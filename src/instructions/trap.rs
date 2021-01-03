use crate::bus::Bus;
use crate::cpu::{register_from_u16, Flag, Register, Registers, CPU};
use crate::instructions::{sign_extend, two_complement_to_dec, Instruction};
use anyhow::{Context, Result};

pub struct Trap {
    trap_vect_8: u16,
}

impl Instruction for Trap {
    fn new(instruction: u16) -> Result<Box<dyn Instruction>> {
        Ok(Box::new(Self {
            trap_vect_8: instruction & 0xFF,
        }))
    }

    fn run(&self, _registers: &mut Registers, _bus: &mut Bus) -> Result<()> {
        // TODO

        Ok(())
    }

    fn to_str(&self) -> String {
        format!("TRAP {:#04x}", self.trap_vect_8)
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
        // TODO
    }

    #[test]
    fn test_to_str() {
        let inst = decode(0b1111_0000_00100000).unwrap();
        assert_eq!(inst.to_str(), "TRAP 0x20");
    }
}
