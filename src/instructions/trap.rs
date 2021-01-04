use crate::bus::Bus;
use crate::cpu::Registers;
use crate::instructions::Instruction;
use anyhow::Result;

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
