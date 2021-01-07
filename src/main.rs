use std::fs::File;
use std::io::Read;

use anyhow::{Context, Result};

use crate::bus::Bus;
use crate::cpu::CPU;

mod bus;
mod cpu;
mod display;
mod instructions;
mod keyboard;
mod memory;

fn main() -> Result<()> {
    let mut file = File::open("res/2048.obj").context("Failed to open program binary file")?;
    let mut buffer = Vec::<u8>::new();

    file.read_to_end(&mut buffer)
        .context("Failed to read program binary")?;

    let u16_buffer: Vec<u16> = buffer
        .chunks_exact(2)
        .into_iter()
        .map(|a| u16::from_ne_bytes([a[0], a[1]]))
        .collect();

    let mut cpu = CPU::new();
    let mut bus = Bus::new().context("Failed to create LC3 Bus")?;

    bus.load_rom(&u16_buffer);

    loop {
        cpu.cycle(&mut bus)?;
    }
}
