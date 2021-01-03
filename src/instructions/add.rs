use crate::cpu::{register_from_u16, Flag, Register, Registers, CPU};
use crate::instructions::{sign_extend, two_complement_to_dec, Instruction};
use anyhow::{Context, Result};

pub struct Add {
    dst_reg: Register,
    sr1_reg: Register,
    sr2_reg: Option<Register>,
    imm5: Option<u16>,
    is_imm: bool,
}

impl Instruction for Add {
    fn new(instruction: u16) -> Result<Box<dyn Instruction>> {
        let dst_reg: Register = register_from_u16((instruction >> 9) & 0x7)?;
        let sr1_reg = register_from_u16((instruction >> 6) & 0x7)?;
        let is_imm = ((instruction >> 5) & 0x1) == 1;

        if is_imm {
            Ok(Box::new(Self {
                dst_reg,
                sr1_reg,
                sr2_reg: None,
                imm5: Some(instruction & 0x1F),
                is_imm,
            }))
        } else {
            Ok(Box::new(Self {
                dst_reg,
                sr1_reg,
                sr2_reg: Some(register_from_u16(instruction & 0x7)?),
                imm5: None,
                is_imm,
            }))
        }
    }

    fn run(&self, registers: &mut Registers) -> Result<()> {
        if self.is_imm {
            let val: u32 = sign_extend(self.imm5.context("Failed to read imm5")?, 5) as u32
                + registers.read_register(self.sr1_reg) as u32;
            registers.write_register(self.dst_reg, val as u16);
        } else {
            let val: u32 = registers.read_register(self.sr1_reg) as u32
                + registers.read_register(self.sr2_reg.context("Failed to read sr2 register")?)
                    as u32;
            registers.write_register(self.dst_reg, val as u16);
        }

        registers.update_flags(self.dst_reg);

        Ok(())
    }

    fn to_str(&self) -> String {
        if self.is_imm {
            format!(
                "ADD {:?}, {:?}, #{}",
                self.dst_reg,
                self.sr1_reg,
                two_complement_to_dec(self.imm5.unwrap(), 5)
            )
        } else {
            format!(
                "ADD {:?}, {:?}, {:?}",
                self.dst_reg,
                self.sr1_reg,
                self.sr2_reg.unwrap()
            )
        }
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

        // Registers Mode: 10+5=5
        cpu.reg.write_register(Register::R0, 0x0A);
        cpu.reg.write_register(Register::R1, 0x05);
        let instruction = decode(0b0001_010_000_0_00_001).unwrap();
        cpu.run(&instruction, &mut bus).unwrap();
        assert_eq!(cpu.reg.read_register(Register::R2), 0x0A + 0x05);
        assert_eq!(cpu.reg.read_register(Register::COND), Flag::Pos as u16);

        // Immediate Mode: 10-5=5
        let instruction = decode(0b0001_010_000_1_11011).unwrap();
        cpu.run(&instruction, &mut bus).unwrap();
        assert_eq!(cpu.reg.read_register(Register::R2), 0x05);
        assert_eq!(cpu.reg.read_register(Register::COND), Flag::Pos as u16);
    }

    #[test]
    fn test_to_str() {
        let inst = decode(0b0001_010_000_0_00_001).unwrap();
        assert_eq!(inst.to_str(), "ADD R2, R0, R1");

        let inst = decode(0b0001_010_000_1_11011).unwrap();
        assert_eq!(inst.to_str(), "ADD R2, R0, #-5")
    }
}
