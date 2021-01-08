# LC3 VM
A Little Computer 3 Virtual Machine, implemented in Rust

More information about LC3 here:

- https://en.wikipedia.org/wiki/Little_Computer_3
- https://justinmeiners.github.io/lc3-vm/

## Folders structure

    .
    ├── Cargo.lock
    ├── Cargo.toml
    ├── README.md
    └── src
       ├── instructions     - Code of all instructions
       │   ├── mod.rs       - Instructions module file (Opcodes declaration, instructions decoding...)
       │   ├── add.rs       - Code of the `ADD` instruction
       │   ├── ...          - ...
       │   └── trap.rs      - Code of the `TRAP` instructions
       ├── bus.rs           - LC3 Communication Bus code
       ├── cpu.rs           - LC3 CPU code
       ├── display.rs       - LC3 Display code
       ├── keyboard.rs      - LC3 Keyboard code
       ├── main.rs          - Main file
       └── memory.rs        - LC3 Memory code

## Instruction

- Type `cargo build` to build the sources
- Type `cargo run` to run the emulator
