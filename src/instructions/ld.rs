use crate::bus::Bus;
use crate::cpu::{register_from_u16, Flag, Register, Registers, CPU};
use crate::instructions::{sign_extend, two_complement_to_dec, Instruction};
use anyhow::{Context, Result};

pub struct Ld {
    dst_reg: Register,
    pc_offset_9: u16,
}

impl Instruction for Ld {
    fn new(instruction: u16) -> Result<Box<dyn Instruction>> {
        let dst_reg = register_from_u16(instruction >> 9 & 0x7)?;
        let pc_offset_9 = instruction & 0x1FF;

        Ok(Box::new(Self {
            dst_reg,
            pc_offset_9,
        }))
    }

    fn run(&self, registers: &mut Registers, bus: &mut Bus) -> Result<()> {
        let addr =
            registers.read_register(Register::PC) as u32 + sign_extend(self.pc_offset_9, 9) as u32;
        registers.write_register(self.dst_reg, bus.read_mem_word(addr as u16));

        registers.update_flags(self.dst_reg);

        Ok(())
    }

    fn to_str(&self) -> String {
        format!(
            "LD {:?}, #{}",
            self.dst_reg,
            two_complement_to_dec(self.pc_offset_9, 9)
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
        let mut cpu = CPU::new();
        let mut bus = Bus::new();

        // NEG Flag
        bus.write_mem_word(PC_START + 0x32, 0xABCD);
        let instruction = decode(0b0010_000_000110010).unwrap();
        cpu.run(&instruction, &mut bus).unwrap();
        assert_eq!(cpu.reg.read_register(Register::R0), 0xABCD);
        assert_eq!(cpu.reg.read_register(Register::COND), Flag::Neg as u16);

        // POS Flag
        bus.write_mem_word(PC_START + 0x33, 0x0BCD);
        let instruction = decode(0b0010_000_000110011).unwrap();
        cpu.run(&instruction, &mut bus).unwrap();
        assert_eq!(cpu.reg.read_register(Register::R0), 0x0BCD);
        assert_eq!(cpu.reg.read_register(Register::COND), Flag::Pos as u16);

        // ZRO Flag
        bus.write_mem_word(PC_START + 0x34, 0x0000);
        let instruction = decode(0b0010_000_000110100).unwrap();
        cpu.run(&instruction, &mut bus).unwrap();
        assert_eq!(cpu.reg.read_register(Register::R0), 0x0000);
        assert_eq!(cpu.reg.read_register(Register::COND), Flag::Zro as u16);
    }

    #[test]
    fn test_to_str() {
        let inst = decode(0b0010_100_000110100).unwrap();
        assert_eq!(inst.to_str(), "LD R4, #52");
    }
}
