use std::io::stdin;
use termion::event::Key;
use termion::input::TermRead;

pub struct Keyboard {}

impl Keyboard {
    pub fn new() -> Self {
        Self {}
    }

    pub fn poll_key(&mut self) -> Option<Key> {
        for k in stdin().keys() {
            match k {
                Ok(key) => return Some(key),
                _ => continue,
            }
        }
        None
    }

    pub fn poll_char(&mut self) -> Option<char> {
        match self.poll_key() {
            Some(Key::Char(c)) => Some(c),
            _ => None,
        }
    }

    pub fn get_char(&mut self) -> char {
        loop {
            match self.poll_char() {
                Some(c) => {
                    return c;
                }
                _ => continue,
            }
        }
    }
}
