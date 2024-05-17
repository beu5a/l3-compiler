use crate::L3Value;

pub const ADD    : L3Value =  0;
pub const SUB    : L3Value =  1;
pub const MUL    : L3Value =  2;
pub const DIV    : L3Value =  3;
pub const MOD    : L3Value =  4;
pub const LSL    : L3Value =  5;
pub const LSR    : L3Value =  6;
pub const AND    : L3Value =  7;
pub const OR     : L3Value =  8;
pub const XOR    : L3Value =  9;
pub const JLT    : L3Value = 10;
pub const JLE    : L3Value = 11;
pub const JEQ    : L3Value = 12;
pub const JNE    : L3Value = 13;
pub const JUMP_I : L3Value = 14;
pub const JUMP_D : L3Value = 15;
pub const CALL_I : L3Value = 16;
pub const CALL_D : L3Value = 17;
pub const RET    : L3Value = 18;
pub const HALT   : L3Value = 19;
pub const LDLO   : L3Value = 20;
pub const LDHI   : L3Value = 21;
pub const MOVE   : L3Value = 22;
pub const ARGS   : L3Value = 23;
pub const FRAME  : L3Value = 24;
pub const BALO   : L3Value = 25;
pub const BSIZ   : L3Value = 26;
pub const BTAG   : L3Value = 27;
pub const BGET   : L3Value = 28;
pub const BSET   : L3Value = 29;
pub const IO     : L3Value = 30;
