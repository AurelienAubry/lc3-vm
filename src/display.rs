use anyhow::Result;
use std::io;
use std::io::{Stdout, Write};
use termion::raw::{IntoRawMode, RawTerminal};

pub struct Display {
    stdout: RawTerminal<Stdout>,
}

impl Display {
    pub fn new() -> Result<Self> {
        let display = Self {
            stdout: io::stdout().into_raw_mode()?,
        };

        Ok(display)
    }

    pub fn output_char(&mut self, c: u8) -> Result<()> {
        self.stdout.write_all(&[c])?;
        Ok(())
    }

    pub fn output_string(&mut self, string: &[u8]) -> Result<()> {
        self.stdout.write_all(string)?;
        Ok(())
    }
}
