mod cache;
mod hash;
mod node;
mod prime;
mod ruddy;

pub use ruddy::Ruddy;
use std::io::{Read as IoRead, Result as IoResult, Write as IoWrite};

pub type Bdd = u32;

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BddOpType {
    Not,
    And,
    Or,
    Comp, // Complement: X \ Y
    QuantExist,
    QuantForall,
}

pub trait BddManager {
    fn init(node_num: u32, cache_size: u32, var_num: u32) -> Self;
    fn get_var(&self, var: u16) -> Bdd;
    fn get_nvar(&self, var: u16) -> Bdd;
    fn get_true(&self) -> Bdd;
    fn get_false(&self) -> Bdd;
    fn is_true(&self, bdd: Bdd) -> bool {
        bdd == self.get_true()
    }
    fn is_false(&self, bdd: Bdd) -> bool {
        bdd == self.get_false()
    }
    fn get_node_num(&self) -> u32;
    fn ref_bdd(&mut self, bdd: Bdd) -> Bdd;
    fn deref_bdd(&mut self, bdd: Bdd) -> Bdd;
    fn gc(&mut self) -> usize;
}

pub trait BddOp {
    // propositional logic operations
    fn not(&mut self, bdd: Bdd) -> Bdd;
    fn and(&mut self, lhs: Bdd, rhs: Bdd) -> Bdd;
    fn or(&mut self, lhs: Bdd, rhs: Bdd) -> Bdd;
    fn comp(&mut self, lhs: Bdd, rhs: Bdd) -> Bdd;

    // first-order logic operations
    fn exist(&mut self, bdd: Bdd, cube: Bdd) -> Bdd;
    fn forall(&mut self, bdd: Bdd, cube: Bdd) -> Bdd;
}

pub trait BddIO<W: IoWrite, R: IoRead> {
    fn serialize(&self, bdd: Bdd, writer: &mut W) -> IoResult<()>;
    fn deserialize(&mut self, reader: &mut R) -> IoResult<Bdd>;
}

pub trait PrintSet<W: IoWrite> {
    fn print(&self, bdd: Bdd, writer: &mut W) -> IoResult<()>;
}
