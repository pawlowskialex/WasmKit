import Testing
import WAT
import WasmParser

@testable import WasmKit

/// `Function.invoke(_:into:on:)`: the same results, checks and failures as `invoke(_:on:)`, with
/// the arguments and results in buffers the caller owns.
@Suite
struct InvokeIntoBuffersTests {
    static let wat = """
        (module
          (import "env" "hostAdd" (func $hostAdd (param i32 i32) (result i32)))
          (func $add32 (export "add32") (param i32 i32) (result i32) (i32.add (local.get 0) (local.get 1)))
          (elem declare func $add32)
          (func (export "getRef") (result funcref) (ref.func $add32))
          (func (export "mix") (param i32 i64 f32 f64) (result f64 i64 i32 f32)
            (local.get 3) (local.get 1) (local.get 0) (local.get 2))
          (func (export "none"))
          (func (export "passRef") (param funcref) (result funcref) (local.get 0))
          (func (export "lanes") (param v128 i32) (result i32 v128)
            (i32x4.extract_lane 1 (local.get 0)) (i32x4.splat (local.get 1)))
          (func (export "viaHost") (param i32 i32) (result i32) (call $hostAdd (local.get 0) (local.get 1)))
          (func (export "unreachable") (result i32) (unreachable))
          (func (export "div") (param i32 i32) (result i32) (i32.div_s (local.get 0) (local.get 1)))
        )
        """

    struct Fixture {
        let store: Store
        let instance: Instance
        let hostAdd: Function

        init(threadingModel: EngineConfiguration.ThreadingModel) throws {
            store = Store(engine: Engine(configuration: .init(threadingModel: threadingModel)))
            hostAdd = Function(store: store, parameters: [.i32, .i32], results: [.i32]) { _, args in
                [.i32(args[0].i32 &+ args[1].i32)]
            }
            instance = try parseWasm(bytes: wat2wasm(InvokeIntoBuffersTests.wat))
                .instantiate(store: store, imports: ["env": ["hostAdd": hostAdd]])
        }

        func callAsFunction(_ name: String) throws -> Function {
            try #require(instance.exports[function: name])
        }
    }

    static let sentinel = Value.i64(0xDEAD_BEEF)

    @Test(arguments: testedThreadingModels)
    func resultsMatchInvoke(threadingModel: EngineConfiguration.ThreadingModel) throws {
        let fixture = try Fixture(threadingModel: threadingModel)
        var stack = ExecutionStack(engine: fixture.store.engine)
        let v128 = V128Storage(lo: 0x0000_0002_0000_0001, hi: 0x0000_0004_0000_0003).value
        let cases: [(String, [Value])] = [
            ("add32", [.i32(40), .i32(2)]),
            ("add32", [.i32(0xFFFF_FFFF), .i32(1)]),
            ("mix", [.i32(1), .i64(.max), .f32(Float(-3.5).bitPattern), .f64(Double.pi.bitPattern)]),
            ("none", []),
            ("passRef", [.ref(.function(nil))]),
            ("passRef", try fixture("getRef").invoke([], on: &stack)),
            ("lanes", [.v128(v128), .i32(7)]),
            ("viaHost", [.i32(20), .i32(22)]),
        ]
        for (name, arguments) in cases {
            let function = try fixture(name)
            let expected = try function.invoke(arguments, on: &stack)
            #expect(try invokeIntoBuffers(function, arguments, results: expected.count, on: &stack) == expected)
        }
        // The host function itself, called with the buffers as its raw implementation takes them.
        #expect(try invokeIntoBuffers(fixture.hostAdd, [.i32(1), .i32(2)], results: 1, on: &stack) == [.i32(3)])
    }

    @Test(arguments: testedThreadingModels)
    func wrongArgumentsOrResultRoomAreRefusedWithoutRunning(threadingModel: EngineConfiguration.ThreadingModel) throws {
        let store = Store(engine: Engine(configuration: .init(threadingModel: threadingModel)))
        var hostCalls = 0
        let host = Function(store: store, parameters: [.i32], results: [.i32]) { _, args in
            hostCalls += 1
            return args
        }
        let instance = try parseWasm(
            bytes: wat2wasm(
                """
                (module
                  (import "env" "host" (func $host (param i32) (result i32)))
                  (func (export "viaHost") (param i32) (result i32) (call $host (local.get 0)))
                )
                """)
        ).instantiate(store: store, imports: ["env": ["host": host]])
        var stack = ExecutionStack(engine: store.engine)
        for function in [try #require(instance.exports[function: "viaHost"]), host] {
            // Wrong type, too few, too many.
            for arguments: [Value] in [[.i64(1)], [], [.i32(1), .i32(2)]] {
                #expect(throws: Trap.self) {
                    _ = try invokeIntoBuffers(function, arguments, results: 1, on: &stack)
                }
            }
            // Room for too few or too many results.
            for count in [0, 2] {
                #expect(throws: Trap.self) {
                    _ = try invokeIntoBuffers(function, [.i32(1)], results: count, on: &stack)
                }
            }
            #expect(hostCalls == 0)
        }
        #expect(try invokeIntoBuffers(host, [.i32(5)], results: 1, on: &stack) == [.i32(5)])
        #expect(hostCalls == 1)
    }

    @Test(arguments: testedThreadingModels)
    func failedCallsLeaveTheResultsAndTheStack(threadingModel: EngineConfiguration.ThreadingModel) throws {
        let fixture = try Fixture(threadingModel: threadingModel)
        var stack = ExecutionStack(engine: fixture.store.engine)
        // A host function whose result is of the wrong type.
        let badHost = Function(store: fixture.store, parameters: [], results: [.i32]) { _, _ in [.i64(1)] }
        for round in UInt32(0)..<50 {
            #expect(throws: Trap.self) { _ = try invokeIntoBuffers(try fixture("unreachable"), [], results: 1, on: &stack) }
            #expect(throws: Trap.self) {
                _ = try invokeIntoBuffers(try fixture("div"), [.i32(1), .i32(0)], results: 1, on: &stack)
            }
            #expect(throws: Trap.self) { _ = try invokeIntoBuffers(badHost, [], results: 1, on: &stack) }
            #expect(try invokeIntoBuffers(try fixture("add32"), [.i32(round), .i32(1)], results: 1, on: &stack) == [.i32(round + 1)])
        }
    }

    /// Calls `function` through `invoke(_:into:on:)`, with every result slot set to a sentinel
    /// first: a call that throws must leave them all as they were.
    private func invokeIntoBuffers(
        _ function: Function, _ arguments: [Value], results count: Int, on stack: inout ExecutionStack,
        sourceLocation: SourceLocation = #_sourceLocation
    ) throws -> [Value] {
        var results = [Value](repeating: Self.sentinel, count: count)
        do {
            try arguments.withUnsafeBufferPointer { arguments in
                try results.withUnsafeMutableBufferPointer { results in
                    try function.invoke(arguments, into: results, on: &stack)
                }
            }
        } catch {
            #expect(results.allSatisfy { $0 == Self.sentinel }, sourceLocation: sourceLocation)
            throw error
        }
        return results
    }
}
