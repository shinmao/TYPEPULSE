use core::convert::From;

#[repr(u8)]
#[derive(Debug, Copy, Clone)]
pub enum MsgType {
    Reserved = 0,
    Error = 1,
    System = 2,
    Ack = 3,
}

impl From<u8> for MsgType {
    #[inline]
    fn from(b: u8) -> Self {
        unsafe { std::mem::transmute(b) }
    }
}

// user code
fn main() {
    let msg_type: MsgType = 2u8.into();
    println!("{:?}", msg_type);
}