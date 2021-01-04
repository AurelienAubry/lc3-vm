use crate::bus::Bus;
use crate::cpu::{register_from_u16, Register, Registers};
use crate::instructions::{sign_extend, two_complement_to_dec, Instruction};
use anyhow::Result;

pub struct Str {
    src_reg: Register,
    base_reg: Register,
    offset_6: u16,
}

impl Instruction for Str {
    fn new(instruction: u16) -> Result<Box<dyn Instruction>> {
        let src_reg = register_from_u16(instruction >> 9 & 0x7)?;
        let base_reg = register_from_u16(instruction >> 6 & 0x7)?;
        let offset_6 = instruction & 0x3F;

        Ok(Box::new(Self {
            src_reg,
            base_reg,
            offset_6,
        }))
    }

    fn run(&self, registers: &mut Registers, bus: &mut Bus) -> Result<()> {
        let addr =
            registers.read_register(self.base_reg) as u32 + sign_extend(self.offset_6, 6) as u32;
        bus.write_mem_word(addr as u16, registers.read_register(self.src_reg));

        Ok(())
    }

    fn to_str(&self) -> String {
        format!(
            "STR {:?}, {:?}, #{}",
            self.src_reg,
            self.base_reg,
            two_complement_to_dec(self.offset_6, 6)
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bus::Bus;

    use crate::instructions::decode;

    #[test]
    fn test_run() {
        let mut reg = Registers::new();
        let mut bus = Bus::new();

        reg.write_register(Register::R1, 0x00FF);
        reg.write_register(Register::R2, 0xABCD);
        let instruction = decode(0b0111_010_001_010100).unwrap();
        instruction.run(&mut reg, &mut bus).unwrap();
        assert_eq!(bus.read_mem_word(0x00FF + 0x14), 0xABCD);
    }

    #[test]
    fn test_to_str() {
        let inst = decode(0b0111_010_001_010100).unwrap();
        assert_eq!(inst.to_str(), "STR R2, R1, #20");
    }
}
