use crate::memory::Memory;
use anyhow::{Context, Result};
use std::io;
use std::io::{stdout, Write};

use crate::cpu;
use crate::cpu::{Register, CPU};
use crate::display::draw;
use std::os::raw::c_int;
use tui::backend::Backend;
use tui::widgets::ListItem;
use tui::Terminal;

extern "C" {
    fn getchar() -> c_int;
}

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

    pub fn write_stdout(&self, data: &[u8]) -> Result<()> {
        stdout()
            .write_all(&data)
            .context("Failed to write data in stdout")
    }

    pub fn read_char(&self) -> i32 {
        unsafe { getchar() }
    }

    pub fn load_rom(&mut self, buffer: &[u16]) {
        let origin = swap16(buffer[0]);
        for i in 1..buffer.len() {
            self.mem.write_word(origin + (i as u16), swap16(buffer[i]));
        }
    }

    pub fn draw<B: Backend>(&self, terminal: &mut Terminal<B>, cpu: &CPU) {
        let offset: u16 = 10;
        let registers = cpu.get_registers();
        let pc = registers.read_register(Register::PC);

        let mem: Vec<ListItem> = self.mem.mem
            [0.max(pc as i32 - offset as i32) as usize..u16::max_value().min(pc + offset) as usize]
            .iter()
            .enumerate()
            .map(|(i, val)| {
                ListItem::new(format!(
                    "{:#04X} - {:#04X}",
                    i + 0.max(pc as i32 - offset as i32) as usize,
                    val
                ))
            })
            .collect();
        draw(terminal, &mem, offset as usize);
    }
}

fn swap16(x: u16) -> u16 {
    (x << 8) | (x >> 8)
}
