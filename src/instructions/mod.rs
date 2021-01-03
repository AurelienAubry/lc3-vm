use crate::cpu::{Registers, CPU};
use anyhow::{Context, Result};

use crate::instructions::add::Add;
use crate::instructions::br::Br;
use num_derive::FromPrimitive;
use num_traits::FromPrimitive;

pub mod add;
pub mod br;

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

pub trait Instruction {
    fn new(instruction: u16) -> Result<Box<dyn Instruction>>
    where
        Self: Sized;
    fn run(&self, registers: &mut Registers) -> Result<()>;
    fn to_str(&self) -> String;
}

fn sign_extend(mut x: u16, bit_count: u16) -> u16 {
    if (x >> (bit_count - 1) & 0x1) == 1 {
        x |= 0xFFFF << bit_count;
    }
    x
}

pub fn decode(raw_instruction: u16) -> Result<Box<dyn Instruction>> {
    let opcode = raw_instruction >> 12;
    let opcode: OpCode = FromPrimitive::from_u16(opcode)
        .with_context(|| format!("Failed to decode opcode: {}", opcode))?;

    let instruction: Result<Box<dyn Instruction>> = match opcode {
        OpCode::Br => Br::new(raw_instruction),
        OpCode::Add => Add::new(raw_instruction),
        _ => anyhow::bail!("Not decoded"),
    };

    instruction
}

pub fn two_complement_to_dec(x: u16, bit_count: u16) -> i16 {
    let max = (1u16 << (bit_count - 1)) - 1;
    let modulo = 1u16 << bit_count;
    if x > max {
        return (x as i16 - modulo as i16) as i16;
    }
    return x as i16;
}
