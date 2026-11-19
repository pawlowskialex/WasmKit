import Testing
import WAT
import WasmParser

@testable import WasmKit

/// A call from the host ends at its root frame's `endOfExecution`, which in the direct-threaded
/// loop halts the handler chain rather than throwing. These check that every way a call can end
/// still reaches the host that made it, with the right results or error, on a stack that stays
/// usable: a normal return, each kind of trap, an uncaught exception, stack exhaustion, and calls
/// nested between host and guest.
@Suite
struct ReturnToHostTests {
    static let wat = """
        (module
          (memory (export "memory") 1)
          (tag $tag (param i32))
          (func (export "add32") (param i32 i32) (result i32) (i32.add (local.get 0) (local.get 1)))
          (func (export "mix") (param i32 i64 f32 f64) (result f64 i64 i32 f32)
            (local.get 3) (local.get 1) (local.get 0) (local.get 2))
          (func (export "none"))
          (func (export "unreachable") (result i32) (unreachable))
          (func (export "div") (param i32 i32) (result i32) (i32.div_s (local.get 0) (local.get 1)))
          (func $recurse (export "recurse") (param i32) (result i32)
            (i32.add (call $recurse (i32.add (local.get 0) (i32.const 1))) (i32.const 1)))
          (func (export "oob") (param i32) (result i32) (i32.load (local.get 0)))
          (func (export "throws") (result i32) (throw $tag (i32.const 7)))
          (func (export "sum") (param i64) (result i64) (local $i i64) (local $acc i64)
            (block $done
              (loop $next
                (br_if $done (i64.ge_u (local.get $i) (local.get 0)))
                (local.set $acc (i64.add (local.get $acc) (local.get $i)))
                (local.set $i (i64.add (local.get $i) (i64.const 1)))
                (br $next)))
            (local.get $acc))
        )
        """

    struct Fixture {
        let store: Store
        let instance: Instance

        init(threadingModel: EngineConfiguration.ThreadingModel, boundsChecking: EngineConfiguration.MemoryBoundsChecking? = nil) throws {
            var configuration = EngineConfiguration(threadingModel: threadingModel)
            if let boundsChecking { configuration.memoryBoundsChecking = boundsChecking }
            store = Store(engine: Engine(configuration: configuration))
            instance = try parseWasm(bytes: wat2wasm(ReturnToHostTests.wat)).instantiate(store: store)
        }

        func callAsFunction(_ name: String) throws -> Function {
            try #require(instance.exports[function: name])
        }
    }

    @Test(arguments: testedThreadingModels)
    func manyCallsOnOneStackReturnTheirResults(threadingModel: EngineConfiguration.ThreadingModel) throws {
        let fixture = try Fixture(threadingModel: threadingModel)
        var stack = ExecutionStack(engine: fixture.store.engine)
        for round in UInt32(0)..<1000 {
            #expect(try fixture("add32").invoke([.i32(round), .i32(3)], on: &stack) == [.i32(round + 3)])
        }
        #expect(
            try fixture("mix").invoke([.i32(1), .i64(2), .f32(Float(3).bitPattern), .f64(Double(4).bitPattern)], on: &stack)
                == [.f64(Double(4).bitPattern), .i64(2), .i32(1), .f32(Float(3).bitPattern)])
        #expect(try fixture("none").invoke([], on: &stack) == [])
        #expect(try fixture("sum").invoke([.i64(100)], on: &stack) == [.i64(4950)])
        // And without a stack of the caller's.
        #expect(try fixture("add32")([.i32(1), .i32(2)]) == [.i32(3)])
    }

    @Test(arguments: testedThreadingModels)
    func everyWayACallEndsLeavesTheStackUsable(threadingModel: EngineConfiguration.ThreadingModel) throws {
        let fixture = try Fixture(threadingModel: threadingModel)
        var stack = ExecutionStack(engine: fixture.store.engine)
        for round in UInt32(0)..<50 {
            expectTrap(.unreachable) { _ = try fixture("unreachable").invoke([], on: &stack) }
            expectTrap(.integerDividedByZero) { _ = try fixture("div").invoke([.i32(1), .i32(0)], on: &stack) }
            expectTrap(.integerOverflow) { _ = try fixture("div").invoke([.i32(0x8000_0000), .i32(0xFFFF_FFFF)], on: &stack) }
            expectTrap(.memoryOutOfBounds) { _ = try fixture("oob").invoke([.i32(65536)], on: &stack) }
            if round % 10 == 0 {
                expectTrap(.callStackExhausted) { _ = try fixture("recurse").invoke([.i32(0)], on: &stack) }
            }
            #expect(throws: (any Error).self) { _ = try fixture("throws").invoke([], on: &stack) }
            // The next call on the same stack runs correctly.
            #expect(try fixture("div").invoke([.i32(9), .i32(3)], on: &stack) == [.i32(3)])
            #expect(try fixture("add32").invoke([.i32(round), .i32(1)], on: &stack) == [.i32(round + 1)])
        }
    }

    #if os(macOS) || os(iOS) || os(Linux)
        /// An access in a guard page traps through the trap guard, then the next call returns
        /// normally.
        @Test(.enabled(if: !Engine.isAddressSanitizerEnabled))
        func guardPageTrapsAlternateWithNormalReturns() throws {
            let fixture = try Fixture(threadingModel: .direct, boundsChecking: .mprotect)
            var stack = ExecutionStack(engine: fixture.store.engine)
            for round in UInt32(0)..<20 {
                expectTrap(.memoryOutOfBounds) { _ = try fixture("oob").invoke([.i32(0x8000_0000)], on: &stack) }
                #expect(try fixture("oob").invoke([.i32(0)], on: &stack) == [.i32(0)])
                #expect(try fixture("add32").invoke([.i32(round), .i32(1)], on: &stack) == [.i32(round + 1)])
            }
        }
    #endif

    /// The host calls the guest, which calls the host, which calls the guest again, several levels
    /// deep: each call ends at its own root frame and returns to the host that made it.
    @Test(arguments: testedThreadingModels)
    func nestedHostAndGuestCallsReturnTheRightResults(threadingModel: EngineConfiguration.ThreadingModel) throws {
        let store = Store(engine: Engine(configuration: .init(threadingModel: threadingModel)))
        var outer: Function?
        var inner: Function?
        var hostCalls = 0
        // host(depth, x) = inner(x) at depth 0, outer(depth - 1, x) + 100 otherwise.
        let host = Function(store: store, parameters: [.i32, .i32], results: [.i32]) { _, args in
            hostCalls += 1
            let depth = args[0].i32
            let x = args[1].i32
            var stack = ExecutionStack(engine: store.engine)
            if depth == 0 {
                return try inner!.invoke([.i32(x)], on: &stack)
            }
            let deeper = try outer!.invoke([.i32(depth - 1), .i32(x)], on: &stack)[0].i32
            return [.i32(deeper &+ 100)]
        }
        let instance = try parseWasm(
            bytes: wat2wasm(
                """
                (module
                  (import "env" "host" (func $host (param i32 i32) (result i32)))
                  ;; outer(depth, x) = host(depth, x) + 1
                  (func (export "outer") (param i32 i32) (result i32)
                    (i32.add (call $host (local.get 0) (local.get 1)) (i32.const 1)))
                  (func (export "inner") (param i32) (result i32) (i32.mul (local.get 0) (i32.const 2)))
                )
                """)
        ).instantiate(store: store, imports: ["env": ["host": host]])
        outer = try #require(instance.exports[function: "outer"])
        inner = try #require(instance.exports[function: "inner"])

        // outer(0, x) = 2x + 1; outer(d, x) = outer(d - 1, x) + 101.
        func expected(_ depth: UInt32, _ x: UInt32) -> UInt32 { 2 * x + 1 + 101 * depth }
        var stack = ExecutionStack(engine: store.engine)
        for depth in UInt32(0)...6 {
            hostCalls = 0
            #expect(try outer!.invoke([.i32(depth), .i32(5)], on: &stack) == [.i32(expected(depth, 5))])
            #expect(hostCalls == Int(depth) + 1)
        }
    }

    /// A guest that traps inside a nested call, and one that traps after a nested call returned
    /// normally.
    @Test(arguments: testedThreadingModels)
    func trapsAroundNestedCalls(threadingModel: EngineConfiguration.ThreadingModel) throws {
        let store = Store(engine: Engine(configuration: .init(threadingModel: threadingModel)))
        var functions: [String: Function] = [:]
        var caughtInside: [Error] = []
        // mode 0: call `double` and return its result.
        // mode 1: call `trap`, catch its trap and return 7.
        // mode 2: call `trap` and let its trap through.
        let host = Function(store: store, parameters: [.i32, .i32], results: [.i32]) { _, args in
            var stack = ExecutionStack(engine: store.engine)
            switch args[0].i32 {
            case 0:
                return try functions["double"]!.invoke([args[1]], on: &stack)
            case 1:
                do {
                    _ = try functions["trap"]!.invoke([], on: &stack)
                } catch {
                    caughtInside.append(error)
                }
                return [.i32(7)]
            default:
                _ = try functions["trap"]!.invoke([], on: &stack)
                return [.i32(0)]
            }
        }
        let instance = try parseWasm(
            bytes: wat2wasm(
                """
                (module
                  (import "env" "host" (func $host (param i32 i32) (result i32)))
                  (func (export "double") (param i32) (result i32) (i32.mul (local.get 0) (i32.const 2)))
                  (func (export "trap") (result i32) (unreachable))
                  (func (export "callHost") (param i32 i32) (result i32)
                    (i32.add (call $host (local.get 0) (local.get 1)) (i32.const 1)))
                  ;; The nested call returns normally; then this frame traps.
                  (func (export "trapAfterNested") (param i32) (result i32)
                    (drop (call $host (i32.const 0) (local.get 0)))
                    (unreachable))
                )
                """)
        ).instantiate(store: store, imports: ["env": ["host": host]])
        for name in ["double", "trap", "callHost", "trapAfterNested"] {
            functions[name] = try #require(instance.exports[function: name])
        }
        let callHost = functions["callHost"]!
        var stack = ExecutionStack(engine: store.engine)

        for _ in 0..<10 {
            #expect(try callHost.invoke([.i32(0), .i32(21)], on: &stack) == [.i32(43)])
            expectTrap(.unreachable) { _ = try functions["trapAfterNested"]!.invoke([.i32(4)], on: &stack) }

            // A trap the host catches doesn't end the outer call.
            caughtInside = []
            #expect(try callHost.invoke([.i32(1), .i32(0)], on: &stack) == [.i32(8)])
            #expect(caughtInside.count == 1)
            #expect((caughtInside.first as? Trap)?.reason.description == TrapReason.unreachable.description)

            // One the host lets through ends it, as the same trap.
            expectTrap(.unreachable) { _ = try callHost.invoke([.i32(2), .i32(0)], on: &stack) }
            #expect(try callHost.invoke([.i32(0), .i32(10)], on: &stack) == [.i32(21)])
        }
    }

    func expectTrap(_ expected: TrapReason, sourceLocation: SourceLocation = #_sourceLocation, _ body: () throws -> Void) {
        do {
            try body()
            Issue.record("expected a trap (\(expected)), but no error was thrown", sourceLocation: sourceLocation)
        } catch let trap as Trap {
            #expect(trap.reason.description == expected.description, sourceLocation: sourceLocation)
        } catch {
            Issue.record("expected a trap (\(expected)), but caught: \(error)", sourceLocation: sourceLocation)
        }
    }
}
