import Testing
import WAT
import WasmParser

@_spi(Fuzzing) @testable import WasmKit

/// The API a host uses to link modules together (a dynamic loader placing side modules in a main
/// module's table and memory, or native code sharing a module's memory and table): `Table.count`,
/// `Table.grow(by:value:store:)`, `Table.function(at:store:)`, `Function.reference`,
/// `Instance.function(at:)`, `Memory.grow(by:store:)` and `Memory.unsafeBaseAddress`.
@Suite
struct HostLinkingAPITests {
    /// A module with a `funcref` table of 2 (at most 4) elements and functions that read it.
    static let tableModule = """
        (module
          (type $i2i (func (param i32) (result i32)))
          (table $t (export "table") 2 4 funcref)
          (elem (table $t) (i32.const 0) func $double)
          (func $double (export "double") (type $i2i) (i32.mul (local.get 0) (i32.const 2)))
          (func (export "triple") (type $i2i) (i32.mul (local.get 0) (i32.const 3)))
          (func (export "callAt") (param $slot i32) (param $x i32) (result i32)
            (call_indirect (type $i2i) (local.get $x) (local.get $slot)))
          (func (export "size") (result i32) (table.size $t))
        )
        """

    struct TableFixture {
        let store: Store
        let instance: Instance
        let table: WasmKit.Table

        init(store: Store = Store(engine: Engine())) throws {
            self.store = store
            instance = try parseWasm(bytes: wat2wasm(HostLinkingAPITests.tableModule)).instantiate(store: store)
            table = try #require(instance.exports[table: "table"])
        }

        func function(_ name: String) throws -> Function {
            try #require(instance.exports[function: name])
        }

        func callAt(_ slot: Int, _ x: Int) throws -> [Value] {
            try function("callAt")([.i32(UInt32(slot)), .i32(UInt32(x))])
        }
    }

    // MARK: - Table.count and Table.grow

    @Test
    func tableCountFollowsGrowthByHostAndGuest() throws {
        let fixture = try TableFixture()
        #expect(fixture.table.count == 2)
        #expect(try fixture.function("size")() == [.i32(2)])

        // Without a value the new slots are null.
        let first = try fixture.table.grow(by: 1, store: fixture.store)
        #expect(first == 2)
        #expect(fixture.table.count == 3)
        #expect(fixture.table[2] == .function(nil))
        #expect(fixture.table.function(at: 2, store: fixture.store) == nil)
        // The guest sees the new size, and calling the null slot traps rather than crashing.
        #expect(try fixture.function("size")() == [.i32(3)])
        #expect(throws: Trap.self) { try fixture.callAt(2, 5) }

        // Growing by zero answers the current size and changes nothing.
        #expect(try fixture.table.grow(by: 0, store: fixture.store) == 3)
        #expect(fixture.table.count == 3)
    }

    @Test
    func tableGrowWithInitialValue() throws {
        let fixture = try TableFixture()
        let triple = try fixture.function("triple")

        let first = try fixture.table.grow(by: 2, value: triple.reference, store: fixture.store)
        #expect(first == 2)
        #expect(fixture.table.count == 4)
        for slot in 2..<4 {
            #expect(fixture.table[slot] == triple.reference)
            #expect(fixture.table.function(at: slot, store: fixture.store) == triple)
            // The guest calls through the new slots.
            #expect(try fixture.callAt(slot, 7) == [.i32(21)])
        }
        // The slots that were there are untouched.
        #expect(try fixture.callAt(0, 7) == [.i32(14)])
    }

    @Test
    func tableGrowPastMaximumFailsAndLeavesTheTable() throws {
        let fixture = try TableFixture()
        // The maximum is 4: 2 + 3 is past it.
        #expect(throws: Trap.self) { try fixture.table.grow(by: 3, store: fixture.store) }
        #expect(fixture.table.count == 2)
        // A negative delta is refused rather than shrinking the table.
        #expect(throws: Trap.self) { try fixture.table.grow(by: -1, store: fixture.store) }
        #expect(fixture.table.count == 2)
        // Up to the maximum is fine, and one more is not.
        #expect(try fixture.table.grow(by: 2, store: fixture.store) == 2)
        #expect(throws: Trap.self) { try fixture.table.grow(by: 1, store: fixture.store) }
        #expect(fixture.table.count == 4)
        #expect(try fixture.function("size")() == [.i32(4)])
    }

    @Test
    func tableGrowRefusedByResourceLimiter() throws {
        final class NoTableGrowth: ResourceLimiter {
            func limitMemoryGrowth(to desired: Int) throws -> Bool { true }
            func limitTableGrowth(to desired: Int) throws -> Bool { desired <= 2 }
        }
        let fixture = try TableFixture()
        fixture.store.resourceLimiter = NoTableGrowth()
        #expect(throws: Trap.self) { try fixture.table.grow(by: 1, store: fixture.store) }
        #expect(fixture.table.count == 2)
    }

    @Test
    func tableGrowRejectsAReferenceOfTheWrongKind() throws {
        let fixture = try TableFixture()
        // An extern reference in a funcref table would later be called as a function.
        #expect(throws: Trap.self) { try fixture.table.grow(by: 1, value: .extern(1), store: fixture.store) }
        #expect(fixture.table.count == 2)

        let store = Store(engine: Engine())
        let externTable = try WasmKit.Table(store: store, type: TableType(elementType: .externRef, limits: Limits(min: 0)))
        let function = try fixture.function("double")
        #expect(throws: Trap.self) { try externTable.grow(by: 1, value: function.reference, store: store) }
        #expect(try externTable.grow(by: 1, value: .extern(42), store: store) == 0)
        #expect(externTable[0] == .extern(42))
        // An extern table holds no functions.
        #expect(externTable.function(at: 0, store: store) == nil)
    }

    // MARK: - Table.function(at:store:)

    @Test
    func tableFunctionAtSetNullAndOutOfRangeSlots() throws {
        let fixture = try TableFixture()
        let double = try fixture.function("double")

        // Set by the module's element segment.
        let set = try #require(fixture.table.function(at: 0, store: fixture.store))
        #expect(set == double)
        #expect(set.type == FunctionType(parameters: [.i32], results: [.i32]))
        #expect(try set([.i32(4)]) == [.i32(8)])

        // Null.
        #expect(fixture.table.function(at: 1, store: fixture.store) == nil)

        // Out of range: answered, not read past the table.
        for index in [-1, 2, 3, Int.max, Int.min] {
            #expect(fixture.table.function(at: index, store: fixture.store) == nil)
        }
    }

    @Test
    func tableFunctionAtAnotherStoreAnswersNil() throws {
        let fixture = try TableFixture()
        let otherStore = Store(engine: fixture.store.engine)
        #expect(fixture.table.function(at: 0, store: otherStore) == nil)
    }

    // MARK: - Function.reference

    @Test
    func functionReferenceRoundTripsThroughATable() throws {
        let fixture = try TableFixture()
        let triple = try fixture.function("triple")

        // Through the subscript.
        fixture.table[1] = triple.reference
        let back = try #require(fixture.table.function(at: 1, store: fixture.store))
        #expect(back == triple)
        #expect(back.reference == triple.reference)
        #expect(back.type == triple.type)
        #expect(try fixture.callAt(1, 5) == [.i32(15)])

        // Clearing the slot makes calling it trap.
        fixture.table[1] = .function(nil)
        #expect(fixture.table.function(at: 1, store: fixture.store) == nil)
        #expect(throws: Trap.self) { try fixture.callAt(1, 5) }
    }

    @Test
    func functionReferenceOfAnotherModuleAndOfAHostFunction() throws {
        let store = Store(engine: Engine())
        let main = try TableFixture(store: store)

        // A function of another instance in the same store, as a dynamic loader places a side
        // module's function in the main module's table.
        let side = try parseWasm(
            bytes: wat2wasm(
                """
                (module (func (export "negate") (param i32) (result i32)
                  (i32.sub (i32.const 0) (local.get 0))))
                """)
        ).instantiate(store: store)
        let negate = try #require(side.exports[function: "negate"])
        let slot = try main.table.grow(by: 1, value: negate.reference, store: store)
        #expect(main.table.function(at: slot, store: store) == negate)
        #expect(try main.callAt(slot, 9) == [.i32(UInt32(bitPattern: -9))])

        // A host function.
        let host = Function(store: store, parameters: [.i32], results: [.i32]) { _, args in
            [.i32(args[0].i32 &+ 100)]
        }
        main.table[1] = host.reference
        #expect(main.table.function(at: 1, store: store) == host)
        #expect(try main.callAt(1, 1) == [.i32(101)])

        // A function of the wrong type in the slot traps as call_indirect must.
        let wrongType = Function(store: store, parameters: [.i64], results: []) { _, _ in [] }
        main.table[1] = wrongType.reference
        #expect(throws: Trap.self) { try main.callAt(1, 1) }
    }

    // MARK: - Instance.function(at:)

    @Test
    func instanceFunctionAtValidAndOutOfRangeIndices() throws {
        let store = Store(engine: Engine())
        let imported = Function(store: store, parameters: [.i32], results: [.i32]) { _, args in
            [.i32(args[0].i32 &+ 1)]
        }
        let module = try parseWasm(
            bytes: wat2wasm(
                """
                (module
                  (import "env" "inc" (func $inc (param i32) (result i32)))
                  (func $hidden (param i32) (result i32) (i32.mul (local.get 0) (i32.const 10)))
                  (func (export "shown") (param i32) (result i32) (call $hidden (call $inc (local.get 0))))
                )
                """))
        let instance = try module.instantiate(store: store, imports: ["env": ["inc": imported]])

        // Imports come first in the index space.
        let zero = try #require(instance.function(at: 0))
        #expect(zero == imported)
        #expect(try zero([.i32(1)]) == [.i32(2)])

        // A function that isn't exported.
        let hidden = try #require(instance.function(at: 1))
        #expect(hidden.type == FunctionType(parameters: [.i32], results: [.i32]))
        #expect(try hidden([.i32(4)]) == [.i32(40)])

        // An exported one is the same function as the export.
        let shown = try #require(instance.function(at: 2))
        #expect(shown == instance.exports[function: "shown"])
        #expect(try shown([.i32(4)]) == [.i32(50)])

        for index in [-1, 3, Int.max, Int.min] {
            #expect(instance.function(at: index) == nil)
        }

        // Checked invoke still rejects the wrong arguments for a function found by index.
        #expect(throws: Trap.self) { try hidden([.i64(4)]) }
        #expect(throws: Trap.self) { try hidden([]) }
    }

    // MARK: - Memory.grow

    static let memoryModule = """
        (module
          (memory (export "memory") 1 3)
          (func (export "size") (result i32) (memory.size))
          (func (export "load") (param i32) (result i32) (i32.load (local.get 0)))
          (func (export "store") (param i32 i32) (i32.store (local.get 0) (local.get 1)))
        )
        """

    @Test(arguments: HostLinkingAPITests.boundsCheckingModes)
    func memoryGrowSucceedsAndTheGuestSeesIt(mode: EngineConfiguration.MemoryBoundsChecking) throws {
        let store = Store(engine: Engine(configuration: .init(memoryBoundsChecking: mode)))
        let instance = try parseWasm(bytes: wat2wasm(Self.memoryModule)).instantiate(store: store)
        let memory = try #require(instance.exports[memory: "memory"])
        let load = try #require(instance.exports[function: "load"])
        let storeFunction = try #require(instance.exports[function: "store"])
        let size = try #require(instance.exports[function: "size"])

        try storeFunction([.i32(16), .i32(0xABCD)])
        // An access in the second page traps before growing.
        #expect(throws: Trap.self) { try load([.i32(65536)]) }

        #expect(try memory.grow(by: 1, store: store) == 1)
        #expect(memory.byteCount == 2 * 65536)
        #expect(try size() == [.i32(2)])
        // The old bytes are kept; the new page is zero and accessible.
        #expect(try load([.i32(16)]) == [.i32(0xABCD)])
        #expect(try load([.i32(65536)]) == [.i32(0)])
        try storeFunction([.i32(65536), .i32(7)])
        #expect(try load([.i32(65536)]) == [.i32(7)])

        // Growing by zero answers the current size.
        #expect(try memory.grow(by: 0, store: store) == 2)
        #expect(memory.byteCount == 2 * 65536)
    }

    @Test(arguments: HostLinkingAPITests.boundsCheckingModes)
    func memoryGrowBeyondMaximumFailsAndLeavesTheMemory(mode: EngineConfiguration.MemoryBoundsChecking) throws {
        let store = Store(engine: Engine(configuration: .init(memoryBoundsChecking: mode)))
        let instance = try parseWasm(bytes: wat2wasm(Self.memoryModule)).instantiate(store: store)
        let memory = try #require(instance.exports[memory: "memory"])
        let load = try #require(instance.exports[function: "load"])

        // The maximum is 3 pages.
        #expect(try memory.grow(by: 3, store: store) == -1)
        #expect(memory.byteCount == 65536)
        // A negative count is refused rather than shrinking the memory.
        #expect(try memory.grow(by: -1, store: store) == -1)
        #expect(try memory.grow(by: Int.min, store: store) == -1)
        #expect(memory.byteCount == 65536)
        // Overflowing page counts are refused, not wrapped.
        #expect(try memory.grow(by: Int.max, store: store) == -1)
        #expect(memory.byteCount == 65536)

        #expect(try memory.grow(by: 2, store: store) == 1)
        #expect(try memory.grow(by: 1, store: store) == -1)
        #expect(memory.byteCount == 3 * 65536)
        // Past the end still traps.
        #expect(throws: Trap.self) { try load([.i32(3 * 65536)]) }
    }

    @Test
    func memoryGrowRefusedByResourceLimiter() throws {
        final class NoMemoryGrowth: ResourceLimiter {
            func limitMemoryGrowth(to desired: Int) throws -> Bool { desired <= 65536 }
            func limitTableGrowth(to desired: Int) throws -> Bool { true }
        }
        let store = Store(engine: Engine())
        let instance = try parseWasm(bytes: wat2wasm(Self.memoryModule)).instantiate(store: store)
        let memory = try #require(instance.exports[memory: "memory"])
        store.resourceLimiter = NoMemoryGrowth()
        #expect(try memory.grow(by: 1, store: store) == -1)
        #expect(memory.byteCount == 65536)
    }

    /// A host function that grows the memory while the guest runs: the guest's cached base and
    /// size are refreshed when the host function returns, even where the memory moved.
    @Test(arguments: HostLinkingAPITests.boundsCheckingModes)
    func memoryGrownByAHostFunctionIsSeenByTheRunningGuest(mode: EngineConfiguration.MemoryBoundsChecking) throws {
        let store = Store(engine: Engine(configuration: .init(memoryBoundsChecking: mode)))
        var memory: WasmKit.Memory?
        let grow = Function(store: store, parameters: [], results: [.i32]) { _, _ in
            [.i32(UInt32(bitPattern: Int32(try memory!.grow(by: 1, store: store))))]
        }
        let module = try parseWasm(
            bytes: wat2wasm(
                """
                (module
                  (import "env" "grow" (func $grow (result i32)))
                  (memory (export "memory") 1 2)
                  (func (export "run") (result i32)
                    (i32.store (i32.const 8) (i32.const 1234))
                    (drop (call $grow))
                    (i32.store (i32.const 65540) (i32.const 99))
                    (i32.add (i32.load (i32.const 8)) (i32.load (i32.const 65540))))
                )
                """))
        let instance = try module.instantiate(store: store, imports: ["env": ["grow": grow]])
        let exported = try #require(instance.exports[memory: "memory"])
        memory = exported
        let run = try #require(instance.exports[function: "run"])
        #expect(try run() == [.i32(1333)])
        #expect(memory?.byteCount == 2 * 65536)
    }

    // MARK: - Memory.unsafeBaseAddress

    @Test
    func unsafeBaseAddressOfAMallocBackedMemoryIsNotStableAndMayMove() throws {
        let store = Store(engine: Engine(configuration: .init(memoryBoundsChecking: .software)))
        let instance = try parseWasm(bytes: wat2wasm(Self.memoryModule)).instantiate(store: store)
        let memory = try #require(instance.exports[memory: "memory"])
        let storeFunction = try #require(instance.exports[function: "store"])
        let load = try #require(instance.exports[function: "load"])

        let before = memory.unsafeBaseAddress
        #expect(before.stable == false)
        let base = try #require(before.address)
        // The address is the guest's byte 0, both ways.
        try storeFunction([.i32(32), .i32(0x1122_3344)])
        #expect(base.load(fromByteOffset: 32, as: UInt32.self) == 0x1122_3344)
        base.storeBytes(of: 0x5566_7788, toByteOffset: 64, as: UInt32.self)
        #expect(try load([.i32(64)]) == [.i32(0x5566_7788)])

        #expect(try memory.grow(by: 1, store: store) == 1)
        let after = memory.unsafeBaseAddress
        #expect(after.stable == false)
        let newBase = try #require(after.address)
        // A malloc-backed memory is copied into a new allocation when it grows, made before the old
        // one is freed, so today it always moves: why `stable` is false and the old address must not
        // be used again.
        #expect(newBase != base)
        #expect(newBase.load(fromByteOffset: 32, as: UInt32.self) == 0x1122_3344)
        #expect(newBase.load(fromByteOffset: 64, as: UInt32.self) == 0x5566_7788)
        try storeFunction([.i32(65536), .i32(5)])
        #expect(newBase.load(fromByteOffset: 65536, as: UInt32.self) == 5)
    }

    #if os(macOS) || os(iOS) || os(Linux)
        @Test(.enabled(if: !Engine.isAddressSanitizerEnabled))
        func unsafeBaseAddressOfAReservedMemoryIsStable() throws {
            let store = Store(engine: Engine(configuration: .init(memoryBoundsChecking: .mprotect)))
            let instance = try parseWasm(bytes: wat2wasm(Self.memoryModule)).instantiate(store: store)
            let memory = try #require(instance.exports[memory: "memory"])
            let storeFunction = try #require(instance.exports[function: "store"])

            let before = memory.unsafeBaseAddress
            // `stable` answers what the engine did: it reserved the memory's range.
            #expect(before.stable == (memory.handle.withValue { $0.trapGuardReservationSize } > 0))
            #expect(before.stable)
            let base = try #require(before.address)
            try storeFunction([.i32(32), .i32(0xCAFE)])

            #expect(try memory.grow(by: 2, store: store) == 1)
            let after = memory.unsafeBaseAddress
            #expect(after.stable)
            #expect(after.address == base)
            #expect(base.load(fromByteOffset: 32, as: UInt32.self) == 0xCAFE)
            // The grown pages are usable through the same address.
            try storeFunction([.i32(2 * 65536), .i32(77)])
            #expect(base.load(fromByteOffset: 2 * 65536, as: UInt32.self) == 77)
        }

        @Test(.enabled(if: !Engine.isAddressSanitizerEnabled))
        func unsafeBaseAddressOfAMemory64IsNotStableUnderMprotect() throws {
            // The engine reserves only 32-bit memories; a memory64 is malloc-backed whatever the
            // configuration asks, and `stable` says so.
            let features: WasmFeatureSet = [.memory64]
            let store = Store(engine: Engine(configuration: .init(features: features, memoryBoundsChecking: .mprotect)))
            let module = try parseWasm(
                bytes: wat2wasm("(module (memory (export \"memory\") i64 1 2))", features: features),
                features: features)
            let memory = try #require(try module.instantiate(store: store).exports[memory: "memory"])
            #expect(memory.unsafeBaseAddress.stable == false)
            #expect(memory.unsafeBaseAddress.address != nil)
        }

        @Test(.enabled(if: !Engine.isAddressSanitizerEnabled))
        func unsafeBaseAddressOfASharedMemoryIsStable() throws {
            let features: WasmFeatureSet = [.threads]
            let store = Store(engine: Engine(configuration: .init(features: features)))
            let memory = try WasmKit.Memory(store: store, type: MemoryType(min: 1, max: 4, shared: true))
            let before = memory.unsafeBaseAddress
            #expect(before.stable)
            #expect(try memory.grow(by: 3, store: store) == 1)
            #expect(memory.unsafeBaseAddress.address == before.address)
            #expect(try memory.grow(by: 1, store: store) == -1)
        }
    #endif

    static var boundsCheckingModes: [EngineConfiguration.MemoryBoundsChecking] {
        #if os(macOS) || os(iOS) || os(Linux)
            return Engine.isAddressSanitizerEnabled ? [.software] : [.mprotect, .software]
        #else
            return [.software]
        #endif
    }
}
