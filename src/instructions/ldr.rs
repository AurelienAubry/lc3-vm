use crate::bus::Bus;
use crate::cpu::{register_from_u16, Register, Registers};
use crate::instructions::{sign_extend, two_complement_to_dec, Instruction};
use anyhow::Result;

pub struct Ldr {
    dst_reg: Register,
    base_reg: Register,
    offset_6: u16,
}

impl Ldr {
    pub fn new(instruction: u16) -> Result<Self> {
        let dst_reg = register_from_u16(instruction >> 9 & 0x7)?;
        let base_reg = register_from_u16(instruction >> 6 & 0x7)?;
        let offset_6 = instruction & 0x3F;

        Ok(Self {
            dst_reg,
            base_reg,
            offset_6,
        })
    }
}

impl Instruction for Ldr {
    fn run(&self, registers: &mut Registers, bus: &mut Bus) -> Result<()> {
        let address =
            registers.read_register(self.base_reg) as u32 + sign_extend(self.offset_6, 6) as u32;
        registers.write_register(self.dst_reg, bus.read_mem_word(address as u16));

        registers.update_flags(self.dst_reg);

        Ok(())
    }

    fn to_str(&self) -> String {
        format!(
            "LDR {:?}, {:?}, #{}",
            self.dst_reg,
            self.base_reg,
            two_complement_to_dec(self.offset_6, 6)
        )
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
        let mut reg = Registers::new();
        let mut bus = Bus::new().unwrap();

        bus.write_mem_word(PC_START + 0x32, 0x0FFF);
        reg.write_register(Register::R2, PC_START + 0x32 + 0x05);
        let instruction = decode(0b0110_100_010_111011).unwrap();
        instruction.run(&mut reg, &mut bus).unwrap();
        assert_eq!(reg.read_register(Register::R4), 0x0FFF);
        assert_eq!(reg.read_register(Register::COND), Flag::Pos as u16);

        bus.write_mem_word(PC_START + 0x32, 0xFFFF);
        reg.write_register(Register::R2, PC_START + 0x32 + 0x05);
        let instruction = decode(0b0110_100_010_111011).unwrap();
        instruction.run(&mut reg, &mut bus).unwrap();
        assert_eq!(reg.read_register(Register::R4), 0xFFFF);
        assert_eq!(reg.read_register(Register::COND), Flag::Neg as u16);
    }

    #[test]
    fn test_to_str() {
        let inst = decode(0b0110_100_010_111011).unwrap();
        assert_eq!(inst.to_str(), "LDR R4, R2, #-5");
    }
}
