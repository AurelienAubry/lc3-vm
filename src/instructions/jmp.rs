use crate::bus::Bus;
use crate::cpu::{register_from_u16, Flag, Register, Registers, CPU};
use crate::instructions::{sign_extend, two_complement_to_dec, Instruction};
use anyhow::{Context, Result};

pub struct Jmp {
    base_reg: Register,
}

impl Instruction for Jmp {
    fn new(instruction: u16) -> Result<Box<dyn Instruction>> {
        let base_reg = register_from_u16(instruction >> 6 & 0x7)?;

        Ok(Box::new(Self { base_reg }))
    }

    fn run(&self, registers: &mut Registers, _bus: &mut Bus) -> Result<()> {
        registers.write_register(Register::PC, registers.read_register(self.base_reg));

        Ok(())
    }

    fn to_str(&self) -> String {
        if self.base_reg == Register::R7 {
            "RET".to_string()
        } else {
            format!("JMP {:?}", self.base_reg)
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

        cpu.reg.write_register(Register::R2, 0xABCD);
        let instruction = decode(0b1100_000_010_000000).unwrap();
        cpu.run(&instruction, &mut bus).unwrap();
        assert_eq!(cpu.reg.read_register(Register::PC), 0xABCD);
    }

    #[test]
    fn test_to_str() {
        let inst = decode(0b1100_000_010_000000).unwrap();
        assert_eq!(inst.to_str(), "JMP R2");

        let inst = decode(0b1100_000_111_000000).unwrap();
        assert_eq!(inst.to_str(), "RET");
    }
}
