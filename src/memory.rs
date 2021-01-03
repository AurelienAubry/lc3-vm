pub const MEMORY_SIZE: usize = u16::MAX as usize;

pub struct Memory {
    pub mem: [u16; MEMORY_SIZE],
}

impl Memory {
    pub fn new() -> Self {
        Self {
            mem: [0; MEMORY_SIZE],
        }
    }

    pub fn read_word(&self, address: u16) -> u16 {
        self.mem[address as usize]
    }

    pub fn write_word(&mut self, address: u16, value: u16) {
        self.mem[address as usize] = value;
    }
}
