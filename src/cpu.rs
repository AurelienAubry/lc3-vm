use crate::bus::Bus;
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
pub enum OpCode {
    /// Branch opcode
    Br = 0,
    /// Add opcode
    Add,
    /// Load opcode
    Ld,
    /// Load opcode
    St,
    /// Jump register opcode
    Jsr,
    /// Bitwise and opcode
    And,
    /// Load register opcode
    Ldr,
    /// Store register opcode
    Str,
    /// Unused opcode
    Rti,
    /// Bitwise not opcode
    Not,
    /// Load indirect opcode
    Ldi,
    /// Store indirect opcode
    Sti,
    /// Jump opcode
    Jmp,
    /// Reserved (unused) opcode
    Res,
    /// Load effective address opcode
    Lea,
    /// Execute trap opcode
    Trap,
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

pub struct CPU {
    reg: [u16; REGISTER_COUNT],
}

impl CPU {
    pub fn new() -> Self {
        let mut cpu = CPU {
            reg: [0; REGISTER_COUNT],
        };
        cpu.write_register(Register::PC, PC_START);

        cpu
    }

    pub fn cycle(&mut self, bus: &mut Bus) -> Result<()> {
        let instruction = bus.read_mem_word(self.read_register(Register::PC));
        self.increment_register(Register::PC, 1);

        self.decode_and_run(instruction, bus)
            .with_context(|| format!("Failed to decode and run instruction: {}", instruction))?;
        Ok(())
    }

    pub fn decode_and_run(&mut self, instruction: u16, bus: &mut Bus) -> Result<()> {
        let opcode = instruction >> 12;
        let opcode: OpCode = FromPrimitive::from_u16(opcode)
            .with_context(|| format!("Failed to decode opcode: {}", opcode))?;

        match opcode {
            OpCode::Br => self.i_br(instruction)?,
            OpCode::Add => self.i_add(instruction)?,
            OpCode::Ld => self.i_ld(instruction, bus)?,
            OpCode::St => self.i_st(instruction, bus)?,
            OpCode::Jsr => self.i_jsr(instruction)?,
            OpCode::And => self.i_and(instruction)?,
            OpCode::Ldr => self.i_ldr(instruction, bus)?,
            OpCode::Str => self.i_str(instruction, bus)?,
            OpCode::Rti => anyhow::bail!("Bad opcode: OpRti"),
            OpCode::Not => self.i_not(instruction)?,
            OpCode::Ldi => self.i_ldi(instruction, bus)?,
            OpCode::Sti => self.i_sti(instruction, bus)?,
            OpCode::Jmp => self.i_jmp(instruction)?,
            OpCode::Res => anyhow::bail!("Bad opcode: OpRes"),
            OpCode::Lea => self.i_lea(instruction)?,
            OpCode::Trap => self.i_trap(instruction, bus)?,
        }
        Ok(())
    }

    fn i_br(&mut self, instruction: u16) -> Result<()> {
        let pc_offset = sign_extend(instruction & 0x1FF, 9);
        let cond_flag = (instruction >> 9) & 0x7;

        let cond_reg = self.read_register(Register::COND);

        if cond_flag & cond_reg != 0 {
            self.increment_register(Register::PC, pc_offset);
        }

        Ok(())
    }

    fn i_add(&mut self, instruction: u16) -> Result<()> {
        let dst_reg: Register = register_from_u16((instruction >> 9) & 0x7)?;
        let sr1_reg = register_from_u16((instruction >> 6) & 0x7)?;
        let imm_flag = (instruction >> 5) & 0x1;

        if imm_flag == 1 {
            let imm = sign_extend(instruction & 0x1F, 5);
            let val: u32 = imm as u32 + self.read_register(sr1_reg) as u32;
            self.write_register(dst_reg, val as u16);
        } else {
            let sr2_reg = register_from_u16(instruction & 0x7)?;
            let val: u32 = self.read_register(sr1_reg) as u32 + self.read_register(sr2_reg) as u32;
            self.write_register(dst_reg, val as u16);
        }

        self.update_flags(dst_reg);

        Ok(())
    }

    fn i_ld(&mut self, instruction: u16, bus: &Bus) -> Result<()> {
        let dst_reg = register_from_u16(instruction >> 9 & 0x7)?;
        let pc_offset = sign_extend(instruction & 0x1FF, 9);
        let addr = self.read_register(Register::PC) as u32 + pc_offset as u32;
        self.write_register(dst_reg, bus.read_mem_word(addr as u16));

        self.update_flags(dst_reg);

        Ok(())
    }

    fn i_st(&mut self, instruction: u16, bus: &mut Bus) -> Result<()> {
        let src_reg = register_from_u16(instruction >> 9 & 0x7)?;
        let pc_offset_9 = sign_extend(instruction & 0x1FF, 9);

        bus.write_mem_word(
            self.read_register(Register::PC) + pc_offset_9,
            self.read_register(src_reg),
        );
        Ok(())
    }

    fn i_jsr(&mut self, instruction: u16) -> Result<()> {
        self.write_register(Register::R7, self.read_register(Register::PC));
        let register_bit = (instruction >> 11) & 0x1;

        if register_bit == 0 {
            // JSRR
            let base_register = register_from_u16((instruction >> 6) & 0x7)?;
            self.write_register(Register::PC, self.read_register(base_register));
        } else {
            // JSR
            let pc_offset = sign_extend(instruction & 0x7FF, 11);
            self.increment_register(Register::PC, pc_offset);
        }

        Ok(())
    }

    fn i_and(&mut self, instruction: u16) -> Result<()> {
        let dst_reg: Register = register_from_u16((instruction >> 9) & 0x7)?;
        let sr1_reg = register_from_u16((instruction >> 6) & 0x7)?;
        let imm_flag = (instruction >> 5) & 0x1;

        if imm_flag == 1 {
            let imm = sign_extend(instruction & 0x1F, 5);
            self.write_register(dst_reg, imm & self.read_register(sr1_reg));
        } else {
            let sr2_reg = register_from_u16(instruction & 0x7)?;
            self.write_register(
                dst_reg,
                self.read_register(sr1_reg) & self.read_register(sr2_reg),
            );
        }

        self.update_flags(dst_reg);

        Ok(())
    }

    fn i_ldr(&mut self, instruction: u16, bus: &Bus) -> Result<()> {
        let dst_reg = register_from_u16((instruction >> 9) & 0x7)?;
        let src_reg = register_from_u16((instruction >> 6) & 0x7)?;
        let offset_6 = sign_extend(instruction & 0x3F, 6);

        let address = self.read_register(src_reg) as u32 + offset_6 as u32;
        self.write_register(dst_reg, bus.read_mem_word(address as u16));

        self.update_flags(dst_reg);

        Ok(())
    }

    fn i_str(&mut self, instruction: u16, bus: &mut Bus) -> Result<()> {
        let src_reg = register_from_u16((instruction >> 9) & 0x7)?;
        let base_reg = register_from_u16((instruction >> 6) & 0x7)?;
        let offset_6 = sign_extend(instruction & 0x3F, 6);

        let addr = self.read_register(base_reg) as u32 + offset_6 as u32;
        bus.write_mem_word(addr as u16, self.read_register(src_reg));

        Ok(())
    }

    fn i_not(&mut self, instruction: u16) -> Result<()> {
        let src_reg = register_from_u16((instruction >> 6) & 0x7)?;
        let dst_reg = register_from_u16((instruction >> 9) & 0x7)?;

        self.write_register(dst_reg, !self.read_register(src_reg));

        self.update_flags(dst_reg);

        Ok(())
    }

    fn i_ldi(&mut self, instruction: u16, bus: &Bus) -> Result<()> {
        let dst_reg = register_from_u16((instruction >> 9) & 0x7)?;
        let pc_offset = sign_extend(instruction & 0x1FF, 9);

        let mem_addr = self.read_register(Register::PC) + pc_offset;
        let real_addr = bus.read_mem_word(bus.read_mem_word(mem_addr));
        self.write_register(dst_reg, real_addr);

        self.update_flags(dst_reg);

        Ok(())
    }

    fn i_sti(&mut self, instruction: u16, bus: &mut Bus) -> Result<()> {
        let src_reg = register_from_u16((instruction >> 9) & 0x7)?;
        let pc_offset_9 = sign_extend(instruction & 0x1FF, 9);

        bus.write_mem_word(
            bus.read_mem_word(self.read_register(Register::PC) + pc_offset_9),
            self.read_register(src_reg),
        );

        Ok(())
    }

    fn i_jmp(&mut self, instruction: u16) -> Result<()> {
        let base_reg = register_from_u16((instruction >> 6) & 0x7)?;

        self.write_register(Register::PC, self.read_register(base_reg));

        Ok(())
    }

    fn i_lea(&mut self, instruction: u16) -> Result<()> {
        let dst_reg = register_from_u16((instruction >> 9) & 0x7)?;
        let pc_offset_9 = sign_extend(instruction & 0x1FF, 9);

        self.write_register(dst_reg, self.read_register(Register::PC) + pc_offset_9);
        self.update_flags(dst_reg);

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
        self.write_register(Register::R0, bus.read_char() as u16);

        Ok(())
    }

    fn trap_puts(&self, bus: &Bus) -> Result<()> {
        let mut address = self.read_register(Register::R0);
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

    fn increment_register(&mut self, register: Register, value: u16) {
        let value = self.read_register(register) as u32 + value as u32;
        self.write_register(register, value as u16);
    }

    fn read_register(&self, register: Register) -> u16 {
        self.reg[register as usize]
    }

    fn write_register(&mut self, register: Register, value: u16) {
        self.reg[register as usize] = value;
    }

    fn update_flags(&mut self, updated_register: Register) {
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

    pub fn get_registers(&self) -> &[u16] {
        &self.reg
    }
}

fn sign_extend(mut x: u16, bit_count: u16) -> u16 {
    if (x >> (bit_count - 1) & 0x1) == 1 {
        x |= 0xFFFF << bit_count;
    }
    x
}

fn register_from_u16(x: u16) -> Result<Register> {
    match FromPrimitive::from_u16(x) {
        Some(reg) => Ok(reg),
        None => anyhow::bail!("Failed to cast {} to `Registers`", x),
    }
}

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

    #[test]
    fn test_i_br() {
        let mut cpu = CPU::new();

        // PC += 3, POS Flag
        cpu.write_register(Register::COND, Flag::Pos as u16);
        cpu.i_br(0b0000_0010_0000_0011).unwrap();
        assert_eq!(cpu.read_register(Register::PC), PC_START + 3);

        // Wrong flag: PC don't changes
        cpu.write_register(Register::COND, Flag::Neg as u16);
        cpu.i_br(0b0000_0010_0000_0011).unwrap();
        assert_eq!(cpu.read_register(Register::PC), PC_START + 3);

        // PC += 5, NEG Flag
        cpu.write_register(Register::PC, PC_START);
        cpu.write_register(Register::COND, Flag::Neg as u16);
        cpu.i_br(0b0000_1000_0000_0101).unwrap();
        assert_eq!(cpu.read_register(Register::PC), PC_START + 5);

        // PC += 7, ZRO Flag
        cpu.write_register(Register::PC, PC_START);
        cpu.write_register(Register::COND, Flag::Zro as u16);
        cpu.i_br(0b0000_0100_0000_0111).unwrap();
        assert_eq!(cpu.read_register(Register::PC), PC_START + 7);
    }

    #[test]
    fn test_i_add() {
        let mut cpu = CPU::new();

        // Registers Mode: 10+5=5
        cpu.write_register(Register::R0, 0x0A);
        cpu.write_register(Register::R1, 0x05);
        cpu.i_add(0b0001_010_000_0_00_001).unwrap();
        assert_eq!(cpu.read_register(Register::R2), 0x0A + 0x05);
        assert_eq!(cpu.read_register(Register::COND), Flag::Pos as u16);

        // Immediate Mode: 10-5=5
        cpu.i_add(0b0001_010_000_1_11011).unwrap();
        assert_eq!(cpu.read_register(Register::R2), 0x05);
        assert_eq!(cpu.read_register(Register::COND), Flag::Pos as u16);
    }

    #[test]
    fn test_i_ld() {
        let mut cpu = CPU::new();
        let mut bus = Bus::new();

        // NEG Flag
        bus.write_mem_word(PC_START + 0x32, 0xABCD);
        cpu.i_ld(0b0010_000_000110010, &bus).unwrap();
        assert_eq!(cpu.read_register(Register::R0), 0xABCD);
        assert_eq!(cpu.read_register(Register::COND), Flag::Neg as u16);

        // POS Flag
        bus.write_mem_word(PC_START + 0x33, 0x0BCD);
        cpu.i_ld(0b0010_000_000110011, &bus).unwrap();
        assert_eq!(cpu.read_register(Register::R0), 0x0BCD);
        assert_eq!(cpu.read_register(Register::COND), Flag::Pos as u16);

        // ZRO Flag
        bus.write_mem_word(PC_START + 0x34, 0x0000);
        cpu.i_ld(0b0010_000_000110100, &bus).unwrap();
        assert_eq!(cpu.read_register(Register::R0), 0x0000);
        assert_eq!(cpu.read_register(Register::COND), Flag::Zro as u16);
    }

    #[test]
    fn test_i_st() {
        let mut cpu = CPU::new();
        let mut bus = Bus::new();

        cpu.write_register(Register::R4, 0xABCD);
        cpu.i_st(0b0011_100_000110010, &mut bus).unwrap();
        assert_eq!(bus.read_mem_word(PC_START + 0x32), 0xABCD);
    }

    #[test]
    fn test_i_jsr() {
        let mut cpu = CPU::new();

        // JSR
        cpu.i_jsr(0b0100_1_00000110010).unwrap();
        assert_eq!(cpu.read_register(Register::PC), PC_START + 0x32);

        // JSRR
        cpu.write_register(Register::PC, PC_START);
        cpu.write_register(Register::R4, 0x64);
        cpu.i_jsr(0b0100_0_00_100_000000).unwrap();
        assert_eq!(cpu.read_register(Register::PC), 0x64);
    }

    #[test]
    fn test_i_and() {
        let mut cpu = CPU::new();

        // Registers Mode
        cpu.write_register(Register::R0, 0xFF);
        cpu.write_register(Register::R1, 0x0F);
        cpu.i_and(0b0101_010_000_0_00_001).unwrap();
        assert_eq!(cpu.read_register(Register::R2), 0x0F & 0xFF);
        assert_eq!(cpu.read_register(Register::COND), Flag::Pos as u16);

        // Immediate Mode
        cpu.i_and(0b0101_011_000_1_01111).unwrap();
        assert_eq!(cpu.read_register(Register::R3), 0xFF & 0x0F);
        assert_eq!(cpu.read_register(Register::COND), Flag::Pos as u16);
    }

    #[test]
    fn test_i_ldr() {
        let mut cpu = CPU::new();
        let mut bus = Bus::new();

        bus.write_mem_word(PC_START + 0x32, 0x0FFF);
        cpu.write_register(Register::R2, PC_START + 0x32 + 0x05);
        cpu.i_ldr(0b0110_100_010_111011, &mut bus).unwrap();
        assert_eq!(cpu.read_register(Register::R4), 0x0FFF);
        assert_eq!(cpu.read_register(Register::COND), Flag::Pos as u16);

        bus.write_mem_word(PC_START + 0x32, 0xFFFF);
        cpu.write_register(Register::R2, PC_START + 0x32 + 0x05);
        cpu.i_ldr(0b0110_100_010_111011, &mut bus).unwrap();
        assert_eq!(cpu.read_register(Register::R4), 0xFFFF);
        assert_eq!(cpu.read_register(Register::COND), Flag::Neg as u16);
    }

    #[test]
    fn test_i_str() {
        let mut cpu = CPU::new();
        let mut bus = Bus::new();

        cpu.write_register(Register::R1, 0x00FF);
        cpu.write_register(Register::R2, 0xABCD);
        cpu.i_str(0b0111_010_001_010100, &mut bus).unwrap();

        assert_eq!(bus.read_mem_word(0x00FF + 0x14), 0xABCD);
    }

    #[test]
    fn test_i_not() {
        let mut cpu = CPU::new();

        // ZRO FLAG
        cpu.write_register(Register::R0, 0b1111_1111_1111_1111);
        cpu.i_not(0b1001_001_000_1_11111);
        assert_eq!(cpu.read_register(Register::R1), 0);
        assert_eq!(cpu.read_register(Register::COND), Flag::Zro as u16);

        // POS FLAG
        cpu.write_register(Register::R0, 0b1000_1111_1111_1111);
        cpu.i_not(0b1001_001_000_1_11111);
        assert_eq!(cpu.read_register(Register::R1), 0b0111_0000_0000_0000);
        assert_eq!(cpu.read_register(Register::COND), Flag::Pos as u16);

        // NEG FLAG
        cpu.write_register(Register::R0, 0b0111_1010_1010_1010);
        cpu.i_not(0b1001_001_000_1_11111);
        assert_eq!(cpu.read_register(Register::R1), 0b1000_0101_0101_0101);
        assert_eq!(cpu.read_register(Register::COND), Flag::Neg as u16);
    }

    #[test]
    fn test_i_ldi() {
        let mut cpu = CPU::new();
        let mut bus = Bus::new();

        bus.write_mem_word(PC_START + 0x32, 0x0FFF);
        bus.write_mem_word(0x0FFF, 0xABCD);
        cpu.i_ldi(0b1010_100_000110010, &mut bus).unwrap();
        assert_eq!(cpu.read_register(Register::R4), 0xABCD);
        assert_eq!(cpu.read_register(Register::COND), Flag::Neg as u16);
    }

    #[test]
    fn test_i_sti() {
        let mut cpu = CPU::new();
        let mut bus = Bus::new();

        bus.write_mem_word(PC_START + 0x32, 0xAFFF);

        cpu.write_register(Register::R2, 0xABCD);
        cpu.i_sti(0b1011_010_000110010, &mut bus).unwrap();

        assert_eq!(bus.read_mem_word(0xAFFF), 0xABCD);
    }

    #[test]
    fn test_i_jmp() {
        let mut cpu = CPU::new();

        cpu.write_register(Register::R2, 0xABCD);
        cpu.i_jmp(0b1100_000_010_000000).unwrap();

        assert_eq!(cpu.read_register(Register::PC), 0xABCD);
    }

    #[test]
    fn test_i_lea() {
        let mut cpu = CPU::new();

        cpu.i_lea(0b1110_010_000110010).unwrap();

        assert_eq!(cpu.read_register(Register::R2), PC_START + 0x32);
        assert_eq!(cpu.read_register(Register::COND), Flag::Pos as u16);
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
}
