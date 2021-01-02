use crate::bus::Bus;
use crate::cpu::Registers::PC;
use anyhow::{Context, Result};
use num_derive::FromPrimitive;
use num_traits::FromPrimitive;

pub const REGISTER_COUNT: usize = 10;
pub const PC_START: u16 = 0x3000;

#[derive(FromPrimitive, Debug, PartialEq, Copy, Clone)]
pub enum Registers {
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
pub enum Flags {
    /// `P` Positive flag
    FL_POS = 1 << 0,
    /// `Z` Zero flag
    FL_ZRO = 1 << 1,
    /// `N` Negative flag
    FL_NEG = 1 << 2,
}

#[derive(FromPrimitive, Debug, PartialEq)]
pub enum OpCodes {
    /// Branch opcode
    OP_BR = 0,
    /// Add opcode
    OP_ADD,
    /// Load opcode
    OP_LD,
    /// Load opcode
    OP_ST,
    /// Jump register opcode
    OP_JSR,
    /// Bitwise and opcode
    OP_AND,
    /// Load register opcode
    OP_LDR,
    /// Store register opcode
    OP_STR,
    /// Unused opcode
    OP_RTI,
    /// Bitwise not opcode
    OP_NOT,
    /// Load indirect opcode
    OP_LDI,
    /// Store indirect opcode
    OP_STI,
    /// Jump opcode
    OP_JMP,
    /// Reserved (unused) opcode
    OP_RES,
    /// Load effective address opcode
    OP_LEA,
    /// Execute trap opcode
    OP_TRAP,
}

pub struct CPU {
    reg: [u16; REGISTER_COUNT],
}

impl CPU {
    pub fn new() -> Self {
        let mut cpu = CPU {
            reg: [0; REGISTER_COUNT],
        };
        cpu.write_register(Registers::PC, PC_START);

        cpu
    }

    pub fn cycle(&mut self, bus: &mut Bus) -> Result<()> {
        let instruction = bus.read_mem_word(self.read_register(Registers::PC));
        self.increment_register(Registers::PC, 1);

        self.decode_and_run(instruction, bus)
            .with_context(|| format!("Failed to decode and run instruction: {}", instruction))?;
        Ok(())
    }

    pub fn decode_and_run(&mut self, instruction: u16, bus: &mut Bus) -> Result<()> {
        let opcode = instruction >> 12;
        let opcode = FromPrimitive::from_u16(opcode)
            .with_context(|| format!("Failed to decode opcode: {}", opcode))?;

        match opcode {
            OpCodes::OP_BR => self.i_br(instruction)?,
            OpCodes::OP_ADD => self.i_add(instruction)?,
            OpCodes::OP_LD => self.i_ld(instruction, bus)?,
            OpCodes::OP_ST => self.i_st(instruction, bus)?,
            OpCodes::OP_JSR => self.i_jsr(instruction)?,
            OpCodes::OP_AND => self.i_and(instruction)?,
            OpCodes::OP_LDR => self.i_ldr(instruction, bus)?,
            OpCodes::OP_STR => self.i_str(instruction, bus)?,
            OpCodes::OP_RTI => anyhow::bail!("Bad opcode: OP_RTI"),
            OpCodes::OP_NOT => self.i_not(instruction)?,
            OpCodes::OP_LDI => self.i_ldi(instruction, bus)?,
            OpCodes::OP_STI => self.i_sti(instruction, bus)?,
            OpCodes::OP_JMP => self.i_jmp(instruction)?,
            OpCodes::OP_RES => anyhow::bail!("Bad opcode: OP_RES"),
            OpCodes::OP_LEA => self.i_lea(instruction)?,
            OpCodes::OP_TRAP => self.i_trap(instruction)?,
        }

        Ok(())
    }

    fn i_br(&mut self, instruction: u16) -> Result<()> {
        let pc_offset = sign_extend(instruction & 0x1FF, 9);
        let cond_flag = (instruction >> 9) & 0x7;

        let cond_reg = self.read_register(Registers::COND);

        if cond_flag & cond_reg != 0 {
            self.increment_register(Registers::PC, pc_offset);
        }

        Ok(())
    }

    fn i_add(&mut self, instruction: u16) -> Result<()> {
        let dst_reg: Registers = register_from_u16((instruction >> 9) & 0x7)?;
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

        self.write_register(
            dst_reg,
            bus.read_mem_word(self.read_register(Registers::PC) + pc_offset),
        );

        self.update_flags(dst_reg);

        Ok(())
    }

    fn i_st(&mut self, instruction: u16, bus: &mut Bus) -> Result<()> {
        let src_reg = register_from_u16(instruction >> 9 & 0x7)?;
        let pc_offset_9 = sign_extend(instruction & 0x1FF, 9);

        bus.write_mem_word(
            self.read_register(Registers::PC) + pc_offset_9,
            self.read_register(src_reg),
        );
        Ok(())
    }

    fn i_jsr(&mut self, instruction: u16) -> Result<()> {
        self.write_register(Registers::R7, self.read_register(Registers::PC));
        let register_bit = (instruction >> 11) & 0x1;

        if register_bit == 0 {
            // JSRR
            let base_register = register_from_u16((instruction >> 6) & 0x7)?;
            self.write_register(Registers::PC, self.read_register(base_register));
        } else {
            // JSR
            let pc_offset = sign_extend(instruction & 0x7FF, 11);
            self.increment_register(Registers::PC, pc_offset);
        }

        Ok(())
    }

    fn i_and(&mut self, instruction: u16) -> Result<()> {
        let dst_reg: Registers = register_from_u16((instruction >> 9) & 0x7)?;
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

        bus.write_mem_word(
            self.read_register(base_reg) + offset_6,
            self.read_register(src_reg),
        );

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

        let mem_addr = self.read_register(Registers::PC) + pc_offset;
        let real_addr = bus.read_mem_word(bus.read_mem_word(mem_addr));
        self.write_register(dst_reg, real_addr);

        self.update_flags(dst_reg);

        Ok(())
    }

    fn i_sti(&mut self, instruction: u16, bus: &mut Bus) -> Result<()> {
        let src_reg = register_from_u16((instruction >> 9) & 0x7)?;
        let pc_offset_9 = sign_extend(instruction & 0x1FF, 9);

        bus.write_mem_word(
            bus.read_mem_word(self.read_register(Registers::PC) + pc_offset_9),
            self.read_register(src_reg),
        );

        Ok(())
    }

    fn i_jmp(&mut self, instruction: u16) -> Result<()> {
        let base_reg = register_from_u16((instruction >> 6) & 0x7)?;

        self.write_register(Registers::PC, self.read_register(base_reg));

        Ok(())
    }

    fn i_lea(&mut self, instruction: u16) -> Result<()> {
        let dst_reg = register_from_u16((instruction >> 9) & 0x7)?;
        let pc_offset_9 = sign_extend(instruction & 0x1FF, 9);

        self.write_register(dst_reg, self.read_register(Registers::PC) + pc_offset_9);
        self.update_flags(dst_reg);

        Ok(())
    }

    fn i_trap(&mut self, instruction: u16) -> Result<()> {
        unimplemented!();

        Ok(())
    }

    fn increment_register(&mut self, register: Registers, value: u16) {
        self.reg[register as usize] += value;
    }

    fn read_register(&self, register: Registers) -> u16 {
        self.reg[register as usize]
    }

    fn write_register(&mut self, register: Registers, value: u16) {
        self.reg[register as usize] = value;
    }

    fn update_flags(&mut self, updated_register: Registers) {
        let updated_reg_value = self.read_register(updated_register);
        let flag;
        if updated_reg_value == 0 {
            flag = Flags::FL_ZRO;
        } else if (updated_reg_value >> 15) == 1 {
            flag = Flags::FL_NEG;
        } else {
            flag = Flags::FL_POS;
        }
        self.reg[Registers::COND as usize] = flag as u16;
    }
}

fn sign_extend(mut x: u16, bit_count: u16) -> u16 {
    if (x >> (bit_count - 1) & 0x1) == 1 {
        x |= 0xFFFF << bit_count;
    }
    x
}

fn register_from_u16(x: u16) -> Result<Registers> {
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
        assert_eq!(register_from_u16(0x00).unwrap(), Registers::R0);
        assert_eq!(register_from_u16(0x09).unwrap(), Registers::COND);

        let err = std::panic::catch_unwind(|| register_from_u16(0xFA).unwrap());
        assert!(err.is_err());
    }

    // TODO: CPU unit tests

    #[test]
    fn test_update_flags() {
        let mut cpu = CPU::new();

        cpu.write_register(Registers::R0, 0);
        cpu.update_flags(Registers::R0);
        assert_eq!(cpu.read_register(Registers::COND), Flags::FL_ZRO as u16);

        cpu.write_register(Registers::R0, 10);
        cpu.update_flags(Registers::R0);
        assert_eq!(cpu.read_register(Registers::COND), Flags::FL_POS as u16);

        cpu.write_register(Registers::R0, 0b1000_0000_0000_0011);
        cpu.update_flags(Registers::R0);
        assert_eq!(cpu.read_register(Registers::COND), Flags::FL_NEG as u16);
    }

    #[test]
    fn test_i_br() {
        let mut cpu = CPU::new();

        // PC += 3, POS Flag
        cpu.write_register(Registers::COND, Flags::FL_POS as u16);
        cpu.i_br(0b0000_0010_0000_0011).unwrap();
        assert_eq!(cpu.read_register(Registers::PC), PC_START + 3);

        // Wrong flag: PC don't changes
        cpu.write_register(Registers::COND, Flags::FL_NEG as u16);
        cpu.i_br(0b0000_0010_0000_0011).unwrap();
        assert_eq!(cpu.read_register(Registers::PC), PC_START + 3);

        // PC += 5, NEG Flag
        cpu.write_register(Registers::PC, PC_START);
        cpu.write_register(Registers::COND, Flags::FL_NEG as u16);
        cpu.i_br(0b0000_1000_0000_0101).unwrap();
        assert_eq!(cpu.read_register(Registers::PC), PC_START + 5);

        // PC += 7, ZRO Flag
        cpu.write_register(Registers::PC, PC_START);
        cpu.write_register(Registers::COND, Flags::FL_ZRO as u16);
        cpu.i_br(0b0000_0100_0000_0111).unwrap();
        assert_eq!(cpu.read_register(Registers::PC), PC_START + 7);
    }

    #[test]
    fn test_i_add() {
        let mut cpu = CPU::new();

        // Registers Mode: 10+5=5
        cpu.write_register(Registers::R0, 0x0A);
        cpu.write_register(Registers::R1, 0x05);
        cpu.i_add(0b0001_010_000_0_00_001).unwrap();
        assert_eq!(cpu.read_register(Registers::R2), 0x0A + 0x05);
        assert_eq!(cpu.read_register(Registers::COND), Flags::FL_POS as u16);

        // Immediate Mode: 10-5=5
        cpu.i_add(0b0001_010_000_1_11011).unwrap();
        assert_eq!(cpu.read_register(Registers::R2), 0x05);
        assert_eq!(cpu.read_register(Registers::COND), Flags::FL_POS as u16);
    }

    #[test]
    fn test_i_ld() {
        let mut cpu = CPU::new();
        let mut bus = Bus::new();

        // NEG Flag
        bus.write_mem_word(PC_START + 0x32, 0xABCD);
        cpu.i_ld(0b0010_000_000110010, &bus).unwrap();
        assert_eq!(cpu.read_register(Registers::R0), 0xABCD);
        assert_eq!(cpu.read_register(Registers::COND), Flags::FL_NEG as u16);

        // POS Flag
        bus.write_mem_word(PC_START + 0x33, 0x0BCD);
        cpu.i_ld(0b0010_000_000110011, &bus).unwrap();
        assert_eq!(cpu.read_register(Registers::R0), 0x0BCD);
        assert_eq!(cpu.read_register(Registers::COND), Flags::FL_POS as u16);

        // ZRO Flag
        bus.write_mem_word(PC_START + 0x34, 0x0000);
        cpu.i_ld(0b0010_000_000110100, &bus).unwrap();
        assert_eq!(cpu.read_register(Registers::R0), 0x0000);
        assert_eq!(cpu.read_register(Registers::COND), Flags::FL_ZRO as u16);
    }

    #[test]
    fn test_i_st() {
        let mut cpu = CPU::new();
        let mut bus = Bus::new();

        cpu.write_register(Registers::R4, 0xABCD);
        cpu.i_st(0b0011_100_000110010, &mut bus).unwrap();
        assert_eq!(bus.read_mem_word(PC_START + 0x32), 0xABCD);
    }

    #[test]
    fn test_i_jsr() {
        let mut cpu = CPU::new();

        // JSR
        cpu.i_jsr(0b0100_1_00000110010).unwrap();
        assert_eq!(cpu.read_register(Registers::PC), PC_START + 0x32);

        // JSRR
        cpu.write_register(Registers::PC, PC_START);
        cpu.write_register(Registers::R4, 0x64);
        cpu.i_jsr(0b0100_0_00_100_000000).unwrap();
        assert_eq!(cpu.read_register(Registers::PC), 0x64);
    }

    #[test]
    fn test_i_and() {
        let mut cpu = CPU::new();

        // Registers Mode
        cpu.write_register(Registers::R0, 0xFF);
        cpu.write_register(Registers::R1, 0x0F);
        cpu.i_and(0b0101_010_000_0_00_001).unwrap();
        assert_eq!(cpu.read_register(Registers::R2), 0x0F & 0xFF);
        assert_eq!(cpu.read_register(Registers::COND), Flags::FL_POS as u16);

        // Immediate Mode
        cpu.i_and(0b0101_011_000_1_01111).unwrap();
        assert_eq!(cpu.read_register(Registers::R3), 0xFF & 0x0F);
        assert_eq!(cpu.read_register(Registers::COND), Flags::FL_POS as u16);
    }

    #[test]
    fn test_i_ldr() {
        let mut cpu = CPU::new();
        let mut bus = Bus::new();

        bus.write_mem_word(PC_START + 0x32, 0x0FFF);
        cpu.write_register(Registers::R2, PC_START + 0x32 + 0x05);
        cpu.i_ldr(0b0110_100_010_111011, &mut bus).unwrap();
        assert_eq!(cpu.read_register(Registers::R4), 0x0FFF);
        assert_eq!(cpu.read_register(Registers::COND), Flags::FL_POS as u16);

        bus.write_mem_word(PC_START + 0x32, 0xFFFF);
        cpu.write_register(Registers::R2, PC_START + 0x32 + 0x05);
        cpu.i_ldr(0b0110_100_010_111011, &mut bus).unwrap();
        assert_eq!(cpu.read_register(Registers::R4), 0xFFFF);
        assert_eq!(cpu.read_register(Registers::COND), Flags::FL_NEG as u16);
    }

    #[test]
    fn test_i_str() {
        let mut cpu = CPU::new();
        let mut bus = Bus::new();

        cpu.write_register(Registers::R1, 0x00FF);
        cpu.write_register(Registers::R2, 0xABCD);
        cpu.i_str(0b0111_010_001_010100, &mut bus).unwrap();

        assert_eq!(bus.read_mem_word(0x00FF + 0x14), 0xABCD);
    }

    #[test]
    fn test_i_not() {
        let mut cpu = CPU::new();

        // ZRO FLAG
        cpu.write_register(Registers::R0, 0b1111_1111_1111_1111);
        cpu.i_not(0b1001_001_000_1_11111);
        assert_eq!(cpu.read_register(Registers::R1), 0);
        assert_eq!(cpu.read_register(Registers::COND), Flags::FL_ZRO as u16);

        // POS FLAG
        cpu.write_register(Registers::R0, 0b1000_1111_1111_1111);
        cpu.i_not(0b1001_001_000_1_11111);
        assert_eq!(cpu.read_register(Registers::R1), 0b0111_0000_0000_0000);
        assert_eq!(cpu.read_register(Registers::COND), Flags::FL_POS as u16);

        // NEG FLAG
        cpu.write_register(Registers::R0, 0b0111_1010_1010_1010);
        cpu.i_not(0b1001_001_000_1_11111);
        assert_eq!(cpu.read_register(Registers::R1), 0b1000_0101_0101_0101);
        assert_eq!(cpu.read_register(Registers::COND), Flags::FL_NEG as u16);
    }

    #[test]
    fn test_i_ldi() {
        let mut cpu = CPU::new();
        let mut bus = Bus::new();

        bus.write_mem_word(PC_START + 0x32, 0x0FFF);
        bus.write_mem_word(0x0FFF, 0xABCD);
        cpu.i_ldi(0b1010_100_000110010, &mut bus).unwrap();
        assert_eq!(cpu.read_register(Registers::R4), 0xABCD);
        assert_eq!(cpu.read_register(Registers::COND), Flags::FL_NEG as u16);
    }

    #[test]
    fn test_i_sti() {
        let mut cpu = CPU::new();
        let mut bus = Bus::new();

        bus.write_mem_word(PC_START + 0x32, 0xAFFF);

        cpu.write_register(Registers::R2, 0xABCD);
        cpu.i_sti(0b1011_010_000110010, &mut bus).unwrap();

        assert_eq!(bus.read_mem_word(0xAFFF), 0xABCD);
    }

    #[test]
    fn test_i_jmp() {
        let mut cpu = CPU::new();

        cpu.write_register(Registers::R2, 0xABCD);
        cpu.i_jmp(0b1100_000_010_000000).unwrap();

        assert_eq!(cpu.read_register(Registers::PC), 0xABCD);
    }

    #[test]
    fn test_i_lea() {
        let mut cpu = CPU::new();

        cpu.i_lea(0b1110_010_000110010).unwrap();

        assert_eq!(cpu.read_register(Registers::R2), PC_START + 0x32);
        assert_eq!(cpu.read_register(Registers::COND), Flags::FL_POS as u16);
    }

    #[test]
    fn test_ret() {
        let mut cpu = CPU::new();

        // Jump to subroutine
        cpu.i_jsr(0b0100_1_00000110010);
        assert_eq!(cpu.read_register(Registers::PC), PC_START + 0x32);

        cpu.i_jmp(0b1100_000_111_000000);
        assert_eq!(cpu.read_register(Registers::PC), PC_START);
    }

    #[test]
    fn test_registers_operations() {
        let mut cpu = CPU::new();

        cpu.increment_register(Registers::R0, 1);
        assert_eq!(cpu.read_register(Registers::R0), 1);

        cpu.increment_register(Registers::R0, 10);
        assert_eq!(cpu.read_register(Registers::R0), 11);

        cpu.write_register(Registers::R1, 15);
        assert_eq!(cpu.read_register(Registers::R1), 15);
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
