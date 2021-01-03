use crate::cpu::{Registers, CPU};
use anyhow::{Context, Result};

use crate::bus::Bus;
use crate::instructions::add::Add;
use crate::instructions::and::And;
use crate::instructions::br::Br;
use crate::instructions::jmp::Jmp;
use crate::instructions::jsr::Jsr;
use crate::instructions::ld::Ld;
use crate::instructions::ldi::Ldi;
use crate::instructions::ldr::Ldr;
use crate::instructions::lea::Lea;
use crate::instructions::not::Not;
use crate::instructions::st::St;
use crate::instructions::sti::Sti;
use crate::instructions::str::Str;
use crate::instructions::trap::Trap;
use num_derive::FromPrimitive;
use num_traits::FromPrimitive;

pub mod add;
pub mod and;
pub mod br;
mod jmp;
pub mod jsr;
pub mod ld;
pub mod ldi;
pub mod ldr;
pub mod lea;
pub mod not;
pub mod st;
pub mod sti;
pub mod str;
pub mod trap;

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
    fn run(&self, registers: &mut Registers, bus: &mut Bus) -> Result<()>;
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
        OpCode::Ld => Ld::new(raw_instruction),
        OpCode::St => St::new(raw_instruction),
        OpCode::Jsr => Jsr::new(raw_instruction),
        OpCode::And => And::new(raw_instruction),
        OpCode::Ldr => Ldr::new(raw_instruction),
        OpCode::Str => Str::new(raw_instruction),
        OpCode::Rti => anyhow::bail!("Bad opcode: OpRti"),
        OpCode::Not => Not::new(raw_instruction),
        OpCode::Ldi => Ldi::new(raw_instruction),
        OpCode::Sti => Sti::new(raw_instruction),
        OpCode::Jmp => Jmp::new(raw_instruction),
        OpCode::Res => anyhow::bail!("Bad opcode: OpRes"),
        OpCode::Lea => Lea::new(raw_instruction),
        OpCode::Trap => Trap::new(raw_instruction),
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
