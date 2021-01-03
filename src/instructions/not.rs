use crate::bus::Bus;
use crate::cpu::{register_from_u16, Flag, Register, Registers, CPU};
use crate::instructions::{sign_extend, two_complement_to_dec, Instruction};
use anyhow::{Context, Result};

pub struct Not {
    dst_reg: Register,
    src_reg: Register,
}

impl Instruction for Not {
    fn new(instruction: u16) -> Result<Box<dyn Instruction>> {
        let dst_reg = register_from_u16(instruction >> 9 & 0x7)?;
        let src_reg = register_from_u16(instruction >> 6 & 0x7)?;

        Ok(Box::new(Self { dst_reg, src_reg }))
    }

    fn run(&self, registers: &mut Registers, bus: &mut Bus) -> Result<()> {
        registers.write_register(self.dst_reg, !registers.read_register(self.src_reg));

        registers.update_flags(self.dst_reg);

        Ok(())
    }

    fn to_str(&self) -> String {
        format!("NOT {:?}, {:?}", self.dst_reg, self.src_reg,)
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

        // ZRO FLAG
        cpu.reg.write_register(Register::R0, 0b1111_1111_1111_1111);
        let instruction = decode(0b1001_001_000_1_11111).unwrap();
        cpu.run(&instruction, &mut bus).unwrap();
        assert_eq!(cpu.reg.read_register(Register::R1), 0);
        assert_eq!(cpu.reg.read_register(Register::COND), Flag::Zro as u16);

        // POS FLAG
        cpu.reg.write_register(Register::R0, 0b1000_1111_1111_1111);
        let instruction = decode(0b1001_001_000_1_11111).unwrap();
        cpu.run(&instruction, &mut bus).unwrap();
        assert_eq!(cpu.reg.read_register(Register::R1), 0b0111_0000_0000_0000);
        assert_eq!(cpu.reg.read_register(Register::COND), Flag::Pos as u16);

        // NEG FLAG
        cpu.reg.write_register(Register::R0, 0b0111_1010_1010_1010);
        let instruction = decode(0b1001_001_000_1_11111).unwrap();
        cpu.run(&instruction, &mut bus).unwrap();
        assert_eq!(cpu.reg.read_register(Register::R1), 0b1000_0101_0101_0101);
        assert_eq!(cpu.reg.read_register(Register::COND), Flag::Neg as u16);
    }

    #[test]
    fn test_to_str() {
        let inst = decode(0b1001_001_000_1_11111).unwrap();
        assert_eq!(inst.to_str(), "NOT R1, R0");
    }
}
