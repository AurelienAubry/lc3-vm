use crate::cpu::{Flag, Register, Registers, CPU};
use crate::instructions::{sign_extend, Instruction};
use anyhow::{Context, Result};

pub struct Br {
    pc_offset: u16,
    cond_flag: u16,
}

impl Instruction for Br {
    fn new(instruction: u16) -> Result<Box<dyn Instruction>> {
        let pc_offset = sign_extend(instruction & 0x1FF, 9);
        let cond_flag = (instruction >> 9) & 0x7;

        Ok(Box::new(Self {
            pc_offset,
            cond_flag,
        }))
    }

    fn run(&self, registers: &mut Registers) -> Result<()> {
        let cond_reg = registers.read_register(Register::COND);
        if self.cond_flag & cond_reg != 0 {
            registers.increment_register(Register::PC, self.pc_offset);
        }

        Ok(())
    }

    fn to_str(&self) -> String {
        let mut op = "BR".to_owned();
        if self.cond_flag & (Flag::Neg as u16) != 0 {
            op.push('n');
        }

        if self.cond_flag & (Flag::Zro as u16) != 0 {
            op.push('z');
        }

        if self.cond_flag & (Flag::Pos as u16) != 0 {
            op.push('p');
        }
        format!("{} {:#06x}", op, self.pc_offset)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bus::Bus;
    use crate::cpu::{Flag, PC_START};
    use crate::instructions::decode;

    #[test]
    fn test_run() {
        let mut cpu = CPU::new();
        let mut bus = Bus::new();
        // PC += 3, POS Flag
        cpu.reg.write_register(Register::COND, Flag::Pos as u16);
        let inst = decode(0b0000_0010_0000_0011).unwrap();
        cpu.run(&inst, &mut bus).unwrap();
        assert_eq!(cpu.reg.read_register(Register::PC), PC_START + 3);

        // Wrong flag: PC don't changes
        cpu.reg.write_register(Register::COND, Flag::Neg as u16);
        let inst = decode(0b0000_0010_0000_0011).unwrap();
        cpu.run(&inst, &mut bus).unwrap();
        assert_eq!(cpu.reg.read_register(Register::PC), PC_START + 3);

        // PC += 5, NEG Flag
        cpu.reg.write_register(Register::PC, PC_START);
        cpu.reg.write_register(Register::COND, Flag::Neg as u16);
        let inst = decode(0b0000_1000_0000_0101).unwrap();
        cpu.run(&inst, &mut bus).unwrap();
        assert_eq!(cpu.reg.read_register(Register::PC), PC_START + 5);

        // PC += 7, ZRO Flag
        cpu.reg.write_register(Register::PC, PC_START);
        cpu.reg.write_register(Register::COND, Flag::Zro as u16);
        let inst = decode(0b0000_0100_0000_0111).unwrap();
        cpu.run(&inst, &mut bus).unwrap();
        assert_eq!(cpu.reg.read_register(Register::PC), PC_START + 7);
    }

    #[test]
    fn test_to_str() {
        let mut br = Br::new(0b0000_111_000000011).unwrap();
        assert_eq!(br.to_str(), "BRnzp 0x0003");

        let mut br = Br::new(0b0000_101_000000011).unwrap();
        assert_eq!(br.to_str(), "BRnp 0x0003");
    }
}
