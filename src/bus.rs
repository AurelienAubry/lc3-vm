use crate::memory::Memory;

pub struct Bus {
    mem: Memory,
}

impl Bus {
    pub fn new() -> Self {
        Self { mem: Memory::new() }
    }

    pub fn read_mem_word(&self, address: u16) -> u16 {
        self.mem.read_word(address)
    }

    pub fn write_mem_word(&mut self, address: u16, value: u16) {
        self.mem.write_word(address, value)
    }
}
