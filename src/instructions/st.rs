use crate::bus::Bus;
use crate::cpu::{register_from_u16, Register, Registers};
use crate::instructions::{sign_extend, two_complement_to_dec, Instruction};
use anyhow::Result;

pub struct St {
    src_reg: Register,
    pc_offset_9: u16,
}

impl Instruction for St {
    fn new(instruction: u16) -> Result<Box<dyn Instruction>> {
        let src_reg = register_from_u16(instruction >> 9 & 0x7)?;
        let pc_offset_9 = instruction & 0x1FF;

        Ok(Box::new(Self {
            src_reg,
            pc_offset_9,
        }))
    }

    fn run(&self, registers: &mut Registers, bus: &mut Bus) -> Result<()> {
        bus.write_mem_word(
            registers.read_register(Register::PC) + sign_extend(self.pc_offset_9, 9),
            registers.read_register(self.src_reg),
        );

        Ok(())
    }

    fn to_str(&self) -> String {
        format!(
            "ST {:?}, #{}",
            self.src_reg,
            two_complement_to_dec(self.pc_offset_9, 9)
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bus::Bus;
    use crate::cpu::PC_START;
    use crate::instructions::decode;

    #[test]
    fn test_run() {
        let mut reg = Registers::new();
        let mut bus = Bus::new();

        reg.write_register(Register::R4, 0xABCD);
        let instruction = decode(0b0011_100_000110010).unwrap();
        instruction.run(&mut reg, &mut bus).unwrap();
        assert_eq!(bus.read_mem_word(PC_START + 0x32), 0xABCD);
    }

    #[test]
    fn test_to_str() {
        let inst = decode(0b0010_100_000110100).unwrap();
        assert_eq!(inst.to_str(), "LD R4, #52");
    }
}
