import Testing
import WAT
import WasmParser

@testable import WasmKit

#if canImport(Darwin)
    import Darwin
#elseif canImport(Glibc)
    import Glibc
#elseif canImport(Musl)
    import Musl
#endif

/// `Function.invokeUnchecked(arguments:results:on:)` and the cheaper return to the host behind it
/// (the direct-threaded loop halting at the root frame's `endOfExecution` rather than throwing,
/// and the trap guard's `sigsetjmp` saving no signal mask): what the guest does still fails
/// safely. Traps surface as traps and leave the stack usable, the checked `invoke` still rejects
/// wrong arguments, nested calls between host and guest return the right values, and a fault in a
/// guard page still traps, with the thread's signal mask as it was.
@Suite
struct InvokeUncheckedTests {
    static let wat = """
        (module
          (import "env" "hostAdd" (func $hostAdd (param i32 i32) (result i32)))
          (memory (export "memory") 1)
          (tag $tag (param i32))
          (func $add32 (export "add32") (param i32 i32) (result i32) (i32.add (local.get 0) (local.get 1)))
          (func (export "mix") (param i32 i64 f32 f64) (result f64 i64 i32 f32)
            (local.get 3) (local.get 1) (local.get 0) (local.get 2))
          (func (export "none"))
          (func (export "passRef") (param funcref) (result funcref) (local.get 0))
          (func (export "viaHost") (param i32 i32) (result i32) (call $hostAdd (local.get 0) (local.get 1)))
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
        let hostAdd: Function

        init(threadingModel: EngineConfiguration.ThreadingModel) throws {
            store = Store(engine: Engine(configuration: .init(threadingModel: threadingModel)))
            hostAdd = Function(store: store, parameters: [.i32, .i32], results: [.i32]) { _, args in
                [.i32(args[0].i32 &+ args[1].i32)]
            }
            instance = try parseWasm(bytes: wat2wasm(InvokeUncheckedTests.wat))
                .instantiate(store: store, imports: ["env": ["hostAdd": hostAdd]])
        }

        func callAsFunction(_ name: String) throws -> Function {
            try #require(instance.exports[function: name])
        }
    }

    // MARK: - Results

    @Test(arguments: testedThreadingModels)
    func uncheckedResultsMatchChecked(threadingModel: EngineConfiguration.ThreadingModel) throws {
        let fixture = try Fixture(threadingModel: threadingModel)
        var stack = ExecutionStack(engine: fixture.store.engine)

        #expect(try unchecked(fixture("add32"), [3, 4], results: 1, on: &stack) == [7])
        // i32 arithmetic wraps within 32 bits and the result's high bits are zero.
        #expect(try unchecked(fixture("add32"), [0xFFFF_FFFF, 2], results: 1, on: &stack) == [1])

        // Every scalar type, and more than one result.
        let arguments: [Value] = [.i32(0x8000_0001), .i64(0x1234_5678_9ABC_DEF0), .f32(Float(-1.5).bitPattern), .f64(Double.pi.bitPattern)]
        let checked = try fixture("mix").invoke(arguments, on: &stack)
        let raw = try unchecked(fixture("mix"), arguments.map { UntypedValue($0).storage }, results: 4, on: &stack)
        #expect(raw == checked.map { UntypedValue($0).storage })
        #expect(raw == [Double.pi.bitPattern, 0x1234_5678_9ABC_DEF0, 0x8000_0001, UInt64(Float(-1.5).bitPattern)])

        // No parameters or results: nil buffers are fine.
        try fixture("none").invokeUnchecked(arguments: nil, results: nil, on: &stack)

        // A reference, encoded as the interpreter stores it.
        let add32 = try fixture("add32")
        let reference = UntypedValue(.ref(add32.reference)).storage
        #expect(try unchecked(fixture("passRef"), [reference], results: 1, on: &stack) == [reference])
        let null = UntypedValue(.ref(.function(nil))).storage
        #expect(try unchecked(fixture("passRef"), [null], results: 1, on: &stack) == [null])

        // A guest that calls a host function, and a host function called directly (the checked
        // path inside).
        #expect(try unchecked(fixture("viaHost"), [40, 2], results: 1, on: &stack) == [42])
        #expect(try unchecked(fixture.hostAdd, [40, 2], results: 1, on: &stack) == [42])

        // Many calls on one stack.
        for n in UInt64(0)..<200 {
            #expect(try unchecked(fixture("sum"), [n], results: 1, on: &stack) == [n * (n &- 1) / 2])
        }
    }

    // MARK: - Traps

    @Test(arguments: testedThreadingModels)
    func trapInsideUncheckedSurfacesAndTheStackStaysUsable(threadingModel: EngineConfiguration.ThreadingModel) throws {
        let fixture = try Fixture(threadingModel: threadingModel)
        var stack = ExecutionStack(engine: fixture.store.engine)
        let sentinel: UInt64 = 0xDEAD_BEEF_DEAD_BEEF

        for round in 0..<50 {
            var result: [UInt64] = [sentinel]
            expectTrap(.unreachable) {
                try fixture("unreachable").invokeUnchecked(arguments: nil, results: &result, on: &stack)
            }
            // Nothing is written for a call that trapped.
            #expect(result == [sentinel])

            expectTrap(.integerDividedByZero) {
                _ = try unchecked(fixture("div"), [1, 0], results: 1, on: &stack)
            }
            // A signed overflow traps too.
            expectTrap(.integerOverflow) {
                _ = try unchecked(fixture("div"), [0x8000_0000, 0xFFFF_FFFF], results: 1, on: &stack)
            }
            expectTrap(.memoryOutOfBounds) {
                _ = try unchecked(fixture("oob"), [65536], results: 1, on: &stack)
            }
            if round % 10 == 0 {
                expectTrap(.callStackExhausted) {
                    _ = try unchecked(fixture("recurse"), [0], results: 1, on: &stack)
                }
            }
            // An uncaught exception ends the call with an error too.
            #expect(throws: (any Error).self) {
                _ = try unchecked(fixture("throws"), [], results: 1, on: &stack)
            }

            // The same stack runs the next call correctly, unchecked and checked.
            #expect(try unchecked(fixture("add32"), [UInt64(round), 1], results: 1, on: &stack) == [UInt64(round) + 1])
            #expect(try fixture("add32").invoke([.i32(UInt32(round)), .i32(2)], on: &stack) == [.i32(UInt32(round) + 2)])
            #expect(try unchecked(fixture("sum"), [100], results: 1, on: &stack) == [4950])
        }
    }

    @Test(arguments: testedThreadingModels)
    func trapAfterANormalReturnStillTraps(threadingModel: EngineConfiguration.ThreadingModel) throws {
        let fixture = try Fixture(threadingModel: threadingModel)
        var stack = ExecutionStack(engine: fixture.store.engine)
        // Alternate calls that end at the root frame's halt with calls that trap.
        for _ in 0..<20 {
            #expect(try unchecked(fixture("div"), [9, 3], results: 1, on: &stack) == [3])
            expectTrap(.integerDividedByZero) { _ = try unchecked(fixture("div"), [9, 0], results: 1, on: &stack) }
            #expect(try fixture("div").invoke([.i32(8), .i32(2)], on: &stack) == [.i32(4)])
            expectTrap(.unreachable) { _ = try fixture("unreachable").invoke([], on: &stack) }
        }
    }

    // MARK: - The checked path

    @Test(arguments: testedThreadingModels)
    func checkedInvokeStillRejectsWrongArguments(threadingModel: EngineConfiguration.ThreadingModel) throws {
        let fixture = try Fixture(threadingModel: threadingModel)
        var stack = ExecutionStack(engine: fixture.store.engine)
        // Use the stack unchecked first, so the checked calls below run where unchecked ones did.
        #expect(try unchecked(fixture("add32"), [1, 2], results: 1, on: &stack) == [3])

        let add32 = try fixture("add32")
        let wrongArguments: [[Value]] = [
            [.i64(1), .i32(2)],  // a wrong type
            [.f32(0), .f32(0)],
            [.i32(1)],  // too few
            [],
            [.i32(1), .i32(2), .i32(3)],  // too many
            [.ref(.function(nil)), .i32(2)],
        ]
        for arguments in wrongArguments {
            expectTrap(.message(.parameterTypesMismatch(expected: [.i32, .i32], got: arguments))) {
                try add32.invoke(arguments, on: &stack)
            }
            expectTrap(.message(.parameterTypesMismatch(expected: [.i32, .i32], got: arguments))) {
                try add32.invoke(arguments)
            }
            // A host function checks the same way.
            expectTrap(.message(.parameterTypesMismatch(expected: [.i32, .i32], got: arguments))) {
                try fixture.hostAdd.invoke(arguments, on: &stack)
            }
        }
        #expect(try add32.invoke([.i32(5), .i32(6)], on: &stack) == [.i32(11)])
        #expect(try unchecked(add32, [5, 6], results: 1, on: &stack) == [11])
    }

    @Test
    func v128SignatureIsRefusedRatherThanMisread() throws {
        let features: WasmFeatureSet = [.simd]
        let store = Store(engine: Engine(configuration: .init(features: features)))
        let instance = try parseWasm(
            bytes: wat2wasm(
                """
                (module
                  (func (export "lane") (param v128) (result i32) (i32x4.extract_lane 1 (local.get 0)))
                  (func (export "splat") (param i32) (result v128) (i32x4.splat (local.get 0)))
                )
                """, features: features),
            features: features
        ).instantiate(store: store)
        var stack = ExecutionStack(engine: store.engine)
        var slots: [UInt64] = [1, 2]
        var result: [UInt64] = [0, 0]
        for name in ["lane", "splat"] {
            let function = try #require(instance.exports[function: name])
            #expect(throws: Trap.self) {
                try function.invokeUnchecked(arguments: &slots, results: &result, on: &stack)
            }
        }
        #expect(result == [0, 0])
        // The checked path takes them.
        let splat = try #require(instance.exports[function: "splat"])
        let lane = try #require(instance.exports[function: "lane"])
        #expect(try lane.invoke(splat.invoke([.i32(9)], on: &stack), on: &stack) == [.i32(9)])
    }

    // MARK: - Nested calls

    /// The host calls the guest, which calls the host, which calls the guest again, several levels
    /// deep, alternating unchecked and checked calls: each level's call ends at its own root frame
    /// and returns to the host that made it, with the right value.
    @Test(arguments: testedThreadingModels)
    func nestedHostAndGuestCallsReturnTheRightResults(threadingModel: EngineConfiguration.ThreadingModel) throws {
        let store = Store(engine: Engine(configuration: .init(threadingModel: threadingModel)))
        var outer: Function?
        var inner: Function?
        var hostCalls = 0
        // host(depth, x) = 2x at depth 0, outer(depth - 1, x) + 100 otherwise.
        let host = Function(store: store, parameters: [.i32, .i32], results: [.i32]) { _, args in
            hostCalls += 1
            let depth = args[0].i32
            let x = args[1].i32
            var stack = ExecutionStack(engine: store.engine)
            if depth == 0 {
                return [.i32(UInt32(try unchecked(inner!, [UInt64(x)], results: 1, on: &stack)[0]))]
            }
            let deeper: UInt32
            if depth % 2 == 0 {
                deeper = UInt32(try unchecked(outer!, [UInt64(depth - 1), UInt64(x)], results: 1, on: &stack)[0])
            } else {
                deeper = try outer!.invoke([.i32(depth - 1), .i32(x)], on: &stack)[0].i32
            }
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
        let outerFunction = try #require(instance.exports[function: "outer"])
        let innerFunction = try #require(instance.exports[function: "inner"])
        (outer, inner) = (outerFunction, innerFunction)

        // outer(0, x) = 2x + 1; outer(d, x) = outer(d - 1, x) + 101.
        func expected(_ depth: UInt64, _ x: UInt64) -> UInt64 { 2 * x + 1 + 101 * depth }
        var stack = ExecutionStack(engine: store.engine)
        for depth in UInt64(0)...6 {
            hostCalls = 0
            #expect(try unchecked(outer!, [depth, 5], results: 1, on: &stack) == [expected(depth, 5)])
            #expect(hostCalls == Int(depth) + 1)
            #expect(try outer!.invoke([.i32(UInt32(depth)), .i32(7)], on: &stack) == [.i32(UInt32(expected(depth, 7)))])
        }
    }

    /// A guest that traps inside a nested call, and a guest that traps after a nested call returned
    /// normally, from the host's point of view.
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
                return [.i32(UInt32(try unchecked(functions["double"]!, [UInt64(args[1].i32)], results: 1, on: &stack)[0]))]
            case 1:
                do {
                    _ = try unchecked(functions["trap"]!, [], results: 1, on: &stack)
                } catch {
                    caughtInside.append(error)
                }
                return [.i32(7)]
            default:
                _ = try unchecked(functions["trap"]!, [], results: 1, on: &stack)
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
            let function = try #require(instance.exports[function: name])
            functions[name] = function
        }
        let callHost = functions["callHost"]!
        var stack = ExecutionStack(engine: store.engine)

        for _ in 0..<10 {
            #expect(try unchecked(callHost, [0, 21], results: 1, on: &stack) == [43])

            expectTrap(.unreachable) { _ = try unchecked(functions["trapAfterNested"]!, [4], results: 1, on: &stack) }

            // A trap the host catches doesn't end the outer call.
            caughtInside = []
            #expect(try unchecked(callHost, [1, 0], results: 1, on: &stack) == [8])
            #expect(caughtInside.count == 1)
            #expect((caughtInside.first as? Trap)?.reason.description == TrapReason.unreachable.description)

            // One the host lets through ends it, as the same trap.
            expectTrap(.unreachable) { _ = try unchecked(callHost, [2, 0], results: 1, on: &stack) }
            expectTrap(.unreachable) { _ = try callHost.invoke([.i32(2), .i32(0)], on: &stack) }

            #expect(try callHost.invoke([.i32(0), .i32(10)], on: &stack) == [.i32(21)])
        }
    }

    // MARK: - Guard pages and the signal mask

    #if (os(macOS) || os(Linux)) && (arch(arm64) || arch(x86_64))
        /// A shared memory's accesses are bounds-checked by its guard pages: an access past the
        /// committed pages faults, and the trap guard turns the fault into a trap. Only the
        /// direct-threaded loop runs guest code under the trap guard.
        struct GuardedFixture {
            let store: Store
            let instance: Instance

            init(host: ((Store) -> Function)? = nil) throws {
                let features: WasmFeatureSet = [.threads]
                store = Store(engine: Engine(configuration: .init(threadingModel: .direct, features: features, memoryBoundsChecking: .mprotect)))
                let memory = try WasmKit.Memory(store: store, type: MemoryType(min: 1, max: 2, shared: true))
                let host = host?(store) ?? Function(store: store, parameters: [], results: []) { _, _ in [] }
                instance = try parseWasm(
                    bytes: wat2wasm(
                        """
                        (module
                          (import "env" "mem" (memory 1 2 shared))
                          (import "env" "host" (func $host))
                          (func (export "load") (param i32) (result i32) (i32.load (local.get 0)))
                          (func (export "hostThenLoad") (param i32) (result i32)
                            (call $host) (i32.load (local.get 0)))
                        )
                        """, features: features),
                    features: features
                ).instantiate(store: store, imports: ["env": ["mem": memory, "host": host]])
            }

            func callAsFunction(_ name: String) throws -> Function {
                try #require(instance.exports[function: name])
            }
        }

        static let guardPagesAvailable =
            !Engine.isAddressSanitizerEnabled
            && SharedMemoryStorage.isSupported(
                engineConfiguration: Engine(configuration: .init(features: [.threads], memoryBoundsChecking: .mprotect)).configuration,
                isMemory64: false)

        /// Expects a memory-out-of-bounds trap raised by the trap guard (a fault in a guard page),
        /// not by a software bounds check.
        func expectGuardedTrap(sourceLocation: SourceLocation = #_sourceLocation, _ body: () throws -> Void) {
            do {
                try body()
                Issue.record("expected a trap, but no error was thrown", sourceLocation: sourceLocation)
            } catch let trap as Trap {
                #expect(trap.reason.description == TrapReason.memoryOutOfBounds.description, sourceLocation: sourceLocation)
                // Only the trap guard's path leaves the innermost frame unknown.
                #expect(trap.backtrace != nil, sourceLocation: sourceLocation)
                #expect(trap.backtrace?.innermostSp == nil, sourceLocation: sourceLocation)
            } catch {
                Issue.record("expected a trap, but caught: \(error)", sourceLocation: sourceLocation)
            }
        }

        @Test(.enabled(if: InvokeUncheckedTests.guardPagesAvailable))
        func outOfBoundsAccessTrapsUnderGuardPages() throws {
            let fixture = try GuardedFixture()
            var stack = ExecutionStack(engine: fixture.store.engine)
            let before = currentSignalMask()
            for address: UInt64 in [65536, 65536 * 2 - 4, 0xFFFF_FFF0] {
                expectGuardedTrap { _ = try unchecked(fixture("load"), [address], results: 1, on: &stack) }
                guard maskIsUnchanged(since: before) else { return }
                expectGuardedTrap { _ = try fixture("load").invoke([.i32(UInt32(address))], on: &stack) }
                guard maskIsUnchanged(since: before) else { return }
                // The stack and the memory are fine afterwards.
                let loaded = try unchecked(fixture("load"), [0], results: 1, on: &stack)
                #expect(loaded == [0])
            }
        }

        /// `sigsetjmp(env, 0)` saves no signal mask, so `siglongjmp` from the handler restores none:
        /// the mask after a trap must be the one before it. It is, because the handler runs with
        /// SA_NODEFER and an empty `sa_mask` and so blocks nothing while it runs. Were SIGSEGV left
        /// blocked, the next fault in a guard page could not be delivered: the process would hang
        /// or be killed, which is why each check below comes before the next fault.
        @Test(.enabled(if: InvokeUncheckedTests.guardPagesAvailable))
        func signalMaskIsUnchangedByGuardedTraps() throws {
            let fixture = try GuardedFixture()
            var stack = ExecutionStack(engine: fixture.store.engine)

            try withBlockedSignals([SIGUSR1, SIGUSR2]) {
                let before = currentSignalMask()
                #expect(isBlocked(SIGUSR1, in: before))
                #expect(isBlocked(SIGSEGV, in: before) == false)
                for _ in 0..<20 {
                    expectGuardedTrap { _ = try unchecked(fixture("load"), [65536], results: 1, on: &stack) }
                    guard maskIsUnchanged(since: before) else { return }
                    expectGuardedTrap { _ = try fixture("load").invoke([.i32(65536)], on: &stack) }
                    guard maskIsUnchanged(since: before) else { return }
                }
                let loaded = try unchecked(fixture("load"), [8], results: 1, on: &stack)
                #expect(loaded == [0])
            }
        }

        /// A guarded trap in a call the host makes from inside a guarded call, caught there, then
        /// one in the outer call: each trap guard catches its own fault, the outer one is restored
        /// when the inner call ends, and the mask is unchanged after both.
        @Test(.enabled(if: InvokeUncheckedTests.guardPagesAvailable))
        func nestedGuardedTrapsKeepTheSignalMask() throws {
            var load: Function?
            var innerTraps = 0
            let fixture = try GuardedFixture { store in
                Function(store: store, parameters: [], results: []) { _, _ in
                    var stack = ExecutionStack(engine: store.engine)
                    do {
                        _ = try unchecked(load!, [65536], results: 1, on: &stack)
                    } catch let trap as Trap where trap.reason.description == TrapReason.memoryOutOfBounds.description {
                        innerTraps += 1
                    }
                    return []
                }
            }
            load = try fixture("load")
            var stack = ExecutionStack(engine: fixture.store.engine)

            try withBlockedSignals([SIGUSR1]) {
                let before = currentSignalMask()
                for round in 1...10 {
                    // The inner call traps and the host catches it; the outer call goes on.
                    let loaded = try unchecked(fixture("hostThenLoad"), [0], results: 1, on: &stack)
                    #expect(loaded == [0])
                    guard maskIsUnchanged(since: before) else { return }
                    // The inner call traps; then the outer call does.
                    expectGuardedTrap { _ = try unchecked(fixture("hostThenLoad"), [65536], results: 1, on: &stack) }
                    #expect(innerTraps == 2 * round)
                    guard maskIsUnchanged(since: before) else { return }
                }
            }
        }

        /// Whether this thread's signal mask is still `before`. If it isn't, records the issue and
        /// puts `before` back, so that the test can stop without the next fault hanging the run.
        private func maskIsUnchanged(since before: sigset_t, sourceLocation: SourceLocation = #_sourceLocation) -> Bool {
            let after = currentSignalMask()
            guard signalMasksAreEqual(before, after) else {
                Issue.record(
                    "a guarded trap changed the signal mask (SIGSEGV blocked: \(isBlocked(SIGSEGV, in: after)), SIGBUS blocked: \(isBlocked(SIGBUS, in: after)))",
                    sourceLocation: sourceLocation)
                var before = before
                pthread_sigmask(SIG_SETMASK, &before, nil)
                return false
            }
            return true
        }

        private func currentSignalMask() -> sigset_t {
            var mask = sigset_t()
            sigemptyset(&mask)
            pthread_sigmask(SIG_SETMASK, nil, &mask)
            return mask
        }

        private func signalMasksAreEqual(_ a: sigset_t, _ b: sigset_t) -> Bool {
            withUnsafeBytes(of: a) { a in withUnsafeBytes(of: b) { b in a.elementsEqual(b) } }
        }

        private func isBlocked(_ signal: Int32, in mask: sigset_t) -> Bool {
            var mask = mask
            return sigismember(&mask, signal) == 1
        }

        /// Runs `body` with `signals` blocked on this thread, then puts the mask back.
        private func withBlockedSignals(_ signals: [Int32], _ body: () throws -> Void) throws {
            var block = sigset_t()
            sigemptyset(&block)
            for signal in signals { sigaddset(&block, signal) }
            var original = sigset_t()
            sigemptyset(&original)
            #expect(pthread_sigmask(SIG_BLOCK, &block, &original) == 0)
            defer { pthread_sigmask(SIG_SETMASK, &original, nil) }
            try body()
        }
    #endif

    // MARK: - Helpers

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

/// Calls `function` through `invokeUnchecked` with `arguments`, answering its `results` slots.
private func unchecked(_ function: Function, _ arguments: [UInt64], results: Int, on stack: inout ExecutionStack) throws -> [UInt64] {
    var out = [UInt64](repeating: 0, count: results)
    try arguments.withUnsafeBufferPointer { arguments in
        try out.withUnsafeMutableBufferPointer { out in
            try function.invokeUnchecked(arguments: arguments.baseAddress, results: out.baseAddress, on: &stack)
        }
    }
    return out
}
