use crate::display::Display;

use crate::keyboard::Keyboard;
use crate::memory::Memory;
use anyhow::Context;
use anyhow::Result;

pub struct Bus {
    mem: Memory,
    keyboard: Keyboard,
    display: Display,
}

impl Bus {
    pub fn new() -> Result<Self> {
        Ok(Self {
            mem: Memory::new(),
            keyboard: Keyboard::new(),
            display: Display::new().context("Failed to create display")?,
        })
    }

    pub fn read_mem_word(&mut self, address: u16) -> u16 {
        self.mem.read_word(address, &mut self.keyboard)
    }

    pub fn write_mem_word(&mut self, address: u16, value: u16) {
        self.mem.write_word(address, value)
    }

    pub fn load_rom(&mut self, buffer: &[u16]) {
        let origin = swap16(buffer[0]);
        for (i, word) in buffer.iter().enumerate().skip(1) {
            self.mem.write_word(origin + (i as u16), swap16(*word));
        }
    }

    pub fn get_pressed_char(&mut self) -> char {
        self.keyboard.get_char()
    }

    pub fn output_char(&mut self, c: u8) -> Result<()> {
        self.display.output_char(c)
    }
    pub fn output_string(&mut self, string: &[u8]) -> Result<()> {
        self.display.output_string(string)
    }
}

fn swap16(x: u16) -> u16 {
    (x << 8) | (x >> 8)
}
