use std::fmt::Write;

pub mod ruddy;

pub type _Bdd = u32;
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
pub struct Bdd(pub _Bdd);

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BddOpType {
    Not,
    And,
    Or,
    // Complement: X \ Y
    Comp,
}

pub trait BddManager {
    fn new() -> Self;
    fn init(&mut self, node_num: u32, cache_size: u32, var_num: u32);
    fn get_var(&self, var: u16) -> Bdd;
    fn get_nvar(&self, var: u16) -> Bdd;
    fn get_true(&self) -> Bdd;
    fn get_false(&self) -> Bdd;
    fn is_true(&self, bdd: &Bdd) -> bool {
        *bdd == self.get_true()
    }
    fn is_false(&self, bdd: &Bdd) -> bool {
        *bdd == self.get_false()
    }
    fn get_node_num(&self) -> u32;
    fn ref_bdd<'a>(&mut self, bdd: &'a Bdd) -> &'a Bdd;
    fn deref_bdd<'a>(&mut self, bdd: &'a Bdd) -> &'a Bdd;
    fn gc(&mut self) -> Option<usize>;
}

pub trait BddOp {
    fn not(&mut self, bdd: &Bdd) -> Bdd;
    fn and(&mut self, lhs: &Bdd, rhs: &Bdd) -> Bdd;
    fn or(&mut self, lhs: &Bdd, rhs: &Bdd) -> Bdd;
    fn comp(&mut self, lhs: &Bdd, rhs: &Bdd) -> Bdd;
}

pub trait BddIO {
    fn read_buffer(&mut self, buffer: &Vec<u8>) -> Option<Bdd>;
    fn write_buffer(&self, bdd: &Bdd, buffer: &mut Vec<u8>) -> Option<usize>;
}

pub trait PrintSet {
    fn print(&self, f: &mut dyn Write, bdd: &Bdd) -> std::fmt::Result;
}
