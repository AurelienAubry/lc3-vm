use crate::bus::Bus;
use crate::instructions::br::Br;
use crate::instructions::{decode, Instruction};
use anyhow::{Context, Result};
use num_derive::FromPrimitive;
use num_traits::FromPrimitive;
use std::io::{self, Write};

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
        Self {
            reg: [0; REGISTER_COUNT],
        }
    }

    pub fn increment_register(&mut self, register: Register, value: u16) {
        let value = self.read_register(register) as u32 + value as u32;
        self.write_register(register, value as u16);
    }

    pub fn read_register(&self, register: Register) -> u16 {
        self.reg[register as usize]
    }

    pub(crate) fn write_register(&mut self, register: Register, value: u16) {
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
    pub(crate) reg: Registers,
}

impl CPU {
    pub fn new() -> Self {
        let mut cpu = CPU {
            reg: Registers::new(),
        };
        cpu.reg.write_register(Register::PC, PC_START);

        cpu
    }

    pub fn cycle(&mut self, bus: &mut Bus) -> Result<()> {
        let raw_instruction = bus.read_mem_word(self.reg.read_register(Register::PC));
        self.reg.increment_register(Register::PC, 1);
        let instruction = decode(raw_instruction).with_context(|| {
            format!("Failed to decode and run instruction: {}", raw_instruction)
        })?;
        self.run(&instruction, bus)?;
        Ok(())
    }

    pub fn run(&mut self, instruction: &Box<dyn Instruction>, bus: &mut Bus) -> Result<()> {
        instruction.run(&mut self.reg, bus);
        Ok(())
    }

    fn i_trap(&mut self, instruction: u16, bus: &mut Bus) -> Result<()> {
        let trap_code = instruction & 0xFF;
        let trap_code: TrapCode = FromPrimitive::from_u16(trap_code)
            .with_context(|| format!("Failed to decode TrapCode: {}", trap_code))?;

        /*match trap_code {
            TrapCode::GetC => self.trap_getc(bus)?,
            TrapCode::Out => {}
            TrapCode::Puts => self.trap_puts(bus)?,
            TrapCode::In => {}
            TrapCode::PutSp => {}
            TrapCode::Halt => {}
        }*/

        Ok(())
    }

    fn trap_getc(&mut self, bus: &Bus) -> Result<()> {
        self.reg
            .write_register(Register::R0, bus.read_char() as u16);

        Ok(())
    }

    fn trap_puts(&self, bus: &Bus) -> Result<()> {
        let mut address = self.reg.read_register(Register::R0);
        let mut char = bus.read_mem_word(address);
        let mut string = vec![];

        while char != 0 {
            string.push(char as u8);
            address += 1;
            char = bus.read_mem_word(address);
        }

        bus.write_stdout(&string)
            .context("Failed to write string in stdout")?;

        Ok(())
    }

    pub fn get_registers(&self) -> &Registers {
        &self.reg
    }
}

fn sign_extend(mut x: u16, bit_count: u16) -> u16 {
    if (x >> (bit_count - 1) & 0x1) == 1 {
        x |= 0xFFFF << bit_count;
    }
    x
}

pub fn register_from_u16(x: u16) -> Result<Register> {
    match FromPrimitive::from_u16(x) {
        Some(reg) => Ok(reg),
        None => anyhow::bail!("Failed to cast {} to `Registers`", x),
    }
}
/*
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sign_extend() {
        let n: u16 = 0b0000_0000_0011_0011;
        assert_eq!(sign_extend(n, 8), 0b0000_0000_0011_0011);
        assert_eq!(sign_extend(n, 6), 0b1111_1111_1111_0011);
    }

    #[test]
    fn test_register_from_u16() {
        assert_eq!(register_from_u16(0x00).unwrap(), Register::R0);
        assert_eq!(register_from_u16(0x09).unwrap(), Register::COND);

        let err = std::panic::catch_unwind(|| register_from_u16(0xFA).unwrap());
        assert!(err.is_err());
    }

    #[test]
    fn test_update_flags() {
        let mut cpu = CPU::new();

        cpu.write_register(Register::R0, 0);
        cpu.update_flags(Register::R0);
        assert_eq!(cpu.read_register(Register::COND), Flag::Zro as u16);

        cpu.write_register(Register::R0, 10);
        cpu.update_flags(Register::R0);
        assert_eq!(cpu.read_register(Register::COND), Flag::Pos as u16);

        cpu.write_register(Register::R0, 0b1000_0000_0000_0011);
        cpu.update_flags(Register::R0);
        assert_eq!(cpu.read_register(Register::COND), Flag::Neg as u16);
    }


    // TODO: find a way to assert TRAP tests

    #[test]
    #[ignore]
    fn test_trap_puts() {
        let mut cpu = CPU::new();
        let mut bus = Bus::new();

        let hello_world: [u16; 12] = [
            0x48, 0x65, 0x6C, 0x6C, 0x6F, 0x20, 0x77, 0x6F, 0x72, 0x6C, 0x64, 0x21,
        ];
        let word_addr = PC_START + 0x32;

        for (i, char) in hello_world.iter().enumerate() {
            bus.write_mem_word(word_addr + (i as u16), *char);
        }

        cpu.write_register(Register::R0, word_addr);
        cpu.trap_puts(&bus);
    }

    #[test]
    fn test_trap_getc() {
        let mut cpu = CPU::new();
        let mut bus = Bus::new();

        cpu.trap_getc(&bus);
    }

    #[test]
    fn test_ret() {
        let mut cpu = CPU::new();

        // Jump to subroutine
        cpu.i_jsr(0b0100_1_00000110010);
        assert_eq!(cpu.read_register(Register::PC), PC_START + 0x32);

        cpu.i_jmp(0b1100_000_111_000000);
        assert_eq!(cpu.read_register(Register::PC), PC_START);
    }

    #[test]
    fn test_registers_operations() {
        let mut cpu = CPU::new();

        cpu.increment_register(Register::R0, 1);
        assert_eq!(cpu.read_register(Register::R0), 1);

        cpu.increment_register(Register::R0, 10);
        assert_eq!(cpu.read_register(Register::R0), 11);

        cpu.write_register(Register::R1, 15);
        assert_eq!(cpu.read_register(Register::R1), 15);
    }

    fn create_and_init_cpu(instructions: &Vec<u16>) -> (CPU, Bus) {
        let mut cpu = CPU::new();
        let mut bus = Bus::new();
        for (i, instruction) in instructions.iter().enumerate() {
            bus.write_mem_word(PC_START + i as u16, *instruction);
        }

        (cpu, bus)
    }
}*/
