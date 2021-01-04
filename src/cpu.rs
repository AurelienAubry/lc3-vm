use anyhow::{Context, Result};
use num_derive::FromPrimitive;
use num_traits::FromPrimitive;

use crate::bus::Bus;

use crate::instructions::decode;

pub const REGISTER_COUNT: usize = 10;
pub const PC_START: u16 = 0x3000;

#[derive(FromPrimitive, Debug, PartialEq, Copy, Clone)]
pub enum Register {
    R0 = 0,
    R1,
    R2,
    R3,
    R4,
    R5,
    R6,
    R7,
    PC,
    COND,
}

#[derive(FromPrimitive, Debug, PartialEq)]
pub enum Flag {
    /// `P` Positive flag
    Pos = 1 << 0,
    /// `Z` Zero flag
    Zro = 1 << 1,
    /// `N` Negative flag
    Neg = 1 << 2,
}

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

pub struct Registers {
    reg: [u16; REGISTER_COUNT],
}

impl Registers {
    pub fn new() -> Self {
        let mut registers = Registers {
            reg: [0; REGISTER_COUNT],
        };

        registers.write_register(Register::PC, PC_START);

        registers
    }

    pub fn increment_register(&mut self, register: Register, value: u16) {
        let value = self.read_register(register) as u32 + value as u32;
        self.write_register(register, value as u16);
    }

    pub fn read_register(&self, register: Register) -> u16 {
        self.reg[register as usize]
    }

    pub fn write_register(&mut self, register: Register, value: u16) {
        self.reg[register as usize] = value;
    }

    pub fn update_flags(&mut self, updated_register: Register) {
        let updated_reg_value = self.read_register(updated_register);
        let flag;
        if updated_reg_value == 0 {
            flag = Flag::Zro;
        } else if (updated_reg_value >> 15) == 1 {
            flag = Flag::Neg;
        } else {
            flag = Flag::Pos;
        }
        self.reg[Register::COND as usize] = flag as u16;
    }
}

pub struct CPU {
    reg: Registers,
}

impl CPU {
    pub fn new() -> Self {
        Self {
            reg: Registers::new(),
        }
    }

    pub fn cycle(&mut self, bus: &mut Bus) -> Result<()> {
        let raw_instruction = bus.read_mem_word(self.reg.read_register(Register::PC));
        self.reg.increment_register(Register::PC, 1);
        let instruction = decode(raw_instruction).with_context(|| {
            format!("Failed to decode and run instruction: {}", raw_instruction)
        })?;
        instruction.run(&mut self.reg, bus)?;
        Ok(())
    }

    pub fn get_registers(&self) -> &Registers {
        &self.reg
    }
}

pub fn register_from_u16(x: u16) -> Result<Register> {
    match FromPrimitive::from_u16(x) {
        Some(reg) => Ok(reg),
        None => anyhow::bail!("Failed to cast {} to `Registers`", x),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_register_from_u16() {
        assert_eq!(register_from_u16(0x00).unwrap(), Register::R0);
        assert_eq!(register_from_u16(0x09).unwrap(), Register::COND);

        let err = std::panic::catch_unwind(|| register_from_u16(0xFA).unwrap());
        assert!(err.is_err());
    }

    #[test]
    fn test_update_flags() {
        let mut reg = Registers::new();

        reg.write_register(Register::R0, 0);
        reg.update_flags(Register::R0);
        assert_eq!(reg.read_register(Register::COND), Flag::Zro as u16);

        reg.write_register(Register::R0, 10);
        reg.update_flags(Register::R0);
        assert_eq!(reg.read_register(Register::COND), Flag::Pos as u16);

        reg.write_register(Register::R0, 0b1000_0000_0000_0011);
        reg.update_flags(Register::R0);
        assert_eq!(reg.read_register(Register::COND), Flag::Neg as u16);
    }

    #[test]
    fn test_registers_operations() {
        let mut reg = Registers::new();

        reg.increment_register(Register::R0, 1);
        assert_eq!(reg.read_register(Register::R0), 1);

        reg.increment_register(Register::R0, 10);
        assert_eq!(reg.read_register(Register::R0), 11);

        reg.write_register(Register::R1, 15);
        assert_eq!(reg.read_register(Register::R1), 15);
    }
}
