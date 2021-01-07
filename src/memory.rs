use crate::keyboard::Keyboard;
use num_derive::FromPrimitive;

pub const MEMORY_SIZE: usize = u16::MAX as usize;

pub struct Memory {
    pub mem: [u16; MEMORY_SIZE],
}

#[derive(FromPrimitive, Debug, PartialEq)]
pub enum MemoryRegister {
    MrKbsr = 0xFE00, /* keyboard status */
    MrKbdr = 0xFE02, /* keyboard data */
}

impl Memory {
    pub fn new() -> Self {
        Self {
            mem: [0; MEMORY_SIZE],
        }
    }

    pub fn read_word(&mut self, address: u16, keyboard: &mut Keyboard) -> u16 {
        if address == MemoryRegister::MrKbsr as u16 {
            match keyboard.poll_char() {
                Some(c) => {
                    self.mem[MemoryRegister::MrKbsr as usize] = 1 << 15;
                    self.mem[MemoryRegister::MrKbdr as usize] = c as u16;
                }
                None => {
                    self.mem[MemoryRegister::MrKbsr as usize] = 0;
                }
            }
        }
        self.mem[address as usize]
    }

    pub fn write_word(&mut self, address: u16, value: u16) {
        self.mem[address as usize] = value;
    }
}
