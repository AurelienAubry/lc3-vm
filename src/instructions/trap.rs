use crate::bus::Bus;
use crate::cpu::{Register, Registers};
use crate::instructions::Instruction;
use anyhow::{Context, Result};

use num_derive::FromPrimitive;
use num_traits::FromPrimitive;
use std::process::exit;

#[derive(FromPrimitive, Debug, PartialEq)]
pub enum TrapCode {
    /// Get character from keyboard, not echoed onto the terminal
    GetC = 0x20,
    /// Output a character
    Out = 0x21,
    /// Output a word string
    Puts = 0x22,
    /// Get character from keyboard, echoed onto the terminal
    In = 0x23,
    /// Output a byte string
    PutSp = 0x24,
    /// Halt the program
    Halt = 0x25,
}

pub struct Trap {
    trap_vect_8: u16,
}

impl Trap {
    pub fn new(instruction: u16) -> Result<Self> {
        Ok(Self {
            trap_vect_8: instruction & 0xFF,
        })
    }
}

impl Instruction for Trap {
    fn run(&self, registers: &mut Registers, bus: &mut Bus) -> Result<()> {
        registers.write_register(Register::R7, registers.read_register(Register::PC));
        let trapcode: TrapCode = FromPrimitive::from_u16(self.trap_vect_8)
            .with_context(|| format!("Failed to decode trapcode: {}", self.trap_vect_8))?;

        match trapcode {
            TrapCode::GetC => {
                let c = bus.get_pressed_char();
                registers.write_register(Register::R0, c as u16);
            }
            TrapCode::Out => {
                let c = registers.read_register(Register::R0) as u8;
                let mut string = vec![];
                if c == b'\n' {
                    string.push(b'\r');
                }
                string.push(c);
                bus.output_string(&string)
                    .context("Failed to output character")?;
            }
            TrapCode::Puts => {
                let mut address = registers.read_register(Register::R0);
                let mut string = vec![];
                let mut c = bus.read_mem_word(address);
                while c != 0 {
                    if c == ('\n' as u16) {
                        string.push(b'\r');
                    }
                    string.push(c as u8);
                    address += 1;

                    c = bus.read_mem_word(address);
                }
                bus.output_string(&string)
                    .context("Failed to output string")?;
            }
            TrapCode::In => {
                bus.output_string(&[b'>', b'>', b' '])
                    .context("Failed to output prompt")?;
                let c = bus.get_pressed_char() as u8;
                bus.output_char(c as u8)
                    .context("Failed to output character")?;
                registers.write_register(Register::R0, c as u16);
            }
            TrapCode::PutSp => {
                let mut address = registers.read_register(Register::R0);
                let mut string = vec![];
                loop {
                    let c = bus.read_mem_word(address);
                    if c == 0 {
                        break;
                    } else {
                        // First character
                        let char1 = (c & 0xFF) as u8;
                        if char1 == b'\n' {
                            string.push(b'\r');
                        }
                        string.push(char1);

                        // Second characyer
                        let char2 = (c >> 8) as u8;
                        if char2 != 0 {
                            if char2 == b'\n' {
                                string.push(b'\r');
                            }
                            string.push(char2);
                        }

                        address += 1;
                    }
                }

                bus.output_string(&string)
                    .context("Failed to output string")?;
            }

            TrapCode::Halt => exit(1),
        }
        Ok(())
    }

    fn to_str(&self) -> String {
        format!("TRAP {:#04x}", self.trap_vect_8)
    }
}

#[cfg(test)]
mod tests {

    use crate::instructions::decode;

    #[test]
    fn test_run() {
        // TODO
    }

    #[test]
    fn test_to_str() {
        let inst = decode(0b1111_0000_00100000).unwrap();
        assert_eq!(inst.to_str(), "TRAP 0x20");
    }
}
