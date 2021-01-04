use crate::bus::Bus;
use crate::cpu::{register_from_u16, Register, Registers};
use crate::instructions::{sign_extend, two_complement_to_dec, Instruction};
use anyhow::{Context, Result};

pub struct Jsr {
    is_jsr: bool,
    pc_offset_11: Option<u16>,
    base_reg: Option<Register>,
}

impl Instruction for Jsr {
    fn new(instruction: u16) -> Result<Box<dyn Instruction>> {
        let is_jsr = ((instruction >> 11) & 0x1) == 1;
        if is_jsr {
            Ok(Box::new(Self {
                is_jsr,
                pc_offset_11: Some(instruction & 0x7FF),
                base_reg: None,
            }))
        } else {
            Ok(Box::new(Self {
                is_jsr,
                pc_offset_11: None,
                base_reg: Some(register_from_u16((instruction >> 6) & 0x7)?),
            }))
        }
    }

    fn run(&self, registers: &mut Registers, _bus: &mut Bus) -> Result<()> {
        registers.write_register(Register::R7, registers.read_register(Register::PC));
        if self.is_jsr {
            registers.increment_register(
                Register::PC,
                sign_extend(self.pc_offset_11.context("Failed to get pc_offset_11")?, 11),
            );
        } else {
            // JSRR
            registers.write_register(
                Register::PC,
                registers.read_register(self.base_reg.context("Failed to get base_reg")?),
            );
        }

        Ok(())
    }

    fn to_str(&self) -> String {
        if self.is_jsr {
            format!(
                "JSR #{}",
                two_complement_to_dec(self.pc_offset_11.unwrap(), 11)
            )
        } else {
            format!("JSRR {:?}", self.base_reg.unwrap())
        }
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

        // JSR
        let instruction = decode(0b0100_1_00000110010).unwrap();
        instruction.run(&mut reg, &mut bus).unwrap();
        assert_eq!(reg.read_register(Register::PC), PC_START + 0x32);

        // JSRR
        reg.write_register(Register::PC, PC_START);
        reg.write_register(Register::R4, 0x64);
        let instruction = decode(0b0100_0_00_100_000000).unwrap();
        instruction.run(&mut reg, &mut bus).unwrap();
        assert_eq!(reg.read_register(Register::PC), 0x64);
    }

    #[test]
    fn test_to_str() {
        let inst = decode(0b0100_1_00000110010).unwrap();
        assert_eq!(inst.to_str(), "JSR #50");

        let inst = decode(0b0100_0_00_100_000000).unwrap();
        assert_eq!(inst.to_str(), "JSRR R4")
    }
}
