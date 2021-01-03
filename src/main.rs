use crate::bus::Bus;
use crate::cpu::CPU;
use crate::display::draw;
use anyhow::{Context, Result};
use rand::Rng;
use std::fs::File;
use std::io::Read;
use std::panic::PanicInfo;
use std::time::Duration;
use std::{io, panic, thread};
use termion::input::MouseTerminal;
use termion::raw::IntoRawMode;
use termion::screen::AlternateScreen;
use tui::backend::TermionBackend;
use tui::widgets::{ListItem, ListState};
use tui::Terminal;

mod bus;
mod cpu;
mod display;
mod memory;

fn panic_hook(info: &PanicInfo<'_>) {
    let location = info.location().unwrap();

    let msg = match info.payload().downcast_ref::<&'static str>() {
        Some(s) => *s,
        None => match info.payload().downcast_ref::<String>() {
            Some(s) => &s[..],
            None => "Box<Any>",
        },
    };

    println!(
        "{}thread '<unnamed>' panicked at '{}', {}\n\r",
        termion::screen::ToMainScreen,
        msg,
        location,
        // stacktrace
    );
}

fn main() -> Result<()> {
    let mut file = File::open("res/2048.obj").context("Failed to open program binary file");
    let mut buffer = Vec::<u8>::new();

    file.read_to_end(&mut buffer)
        .context("Failed to read program binary")?;

    let u16_buffer: Vec<u16> = buffer
        .chunks_exact(2)
        .into_iter()
        .map(|a| u16::from_ne_bytes([a[0], a[1]]))
        .collect();

    let mut cpu = CPU::new();
    let mut bus = Bus::new();
    bus.load_rom(&u16_buffer);

    let stdout = io::stdout().into_raw_mode()?;
    let stdout = MouseTerminal::from(stdout);
    let stdout = AlternateScreen::from(stdout);
    let backend = TermionBackend::new(stdout);
    let mut terminal = Terminal::new(backend).context("Failed to create terminal")?;

    panic::set_hook(Box::new(|info| {
        panic_hook(info);
    }));

    for i in 0..10000 {
        cpu.cycle(&mut bus)?;
        bus.draw(&mut terminal, &cpu);
    }

    Ok(())
}
