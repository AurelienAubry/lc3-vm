use tui::backend::Backend;
use tui::widgets::ListItem;
use tui::Terminal;

use crate::cpu::{Register, CPU};
use crate::display::draw;
use crate::instructions::decode;
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

    pub fn load_rom(&mut self, buffer: &[u16]) {
        let origin = swap16(buffer[0]);
        for (i, word) in buffer.iter().enumerate().skip(1) {
            self.mem.write_word(origin + (i as u16), swap16(*word));
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
                let instruction = decode(*val).unwrap().to_str();
                ListItem::new(format!(
                    "{:#04X} - {}",
                    i + 0.max(pc as i32 - offset as i32) as usize,
                    instruction
                ))
            })
            .collect();
        draw(terminal, &mem, offset as usize);
    }
}

fn swap16(x: u16) -> u16 {
    (x << 8) | (x >> 8)
}
