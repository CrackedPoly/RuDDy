mod cache;
mod hash;
mod node;
mod prime;
mod ruddy;

pub use ruddy::Ruddy;
use std::io::{Read as IoRead, Result as IoResult, Write as IoWrite};

/// BDD type (alias of u32).
/// # Why choose u32?
/// u32 is used in RuDDy to index BDD node in hash table. The reason to choose u32 other than usize
/// or u16 is that u32 is small in bytes while not possibly exceed its max. The maximum memory
/// usage of nodes supported by u32 is 2^32 * (20 + 2) / 2^30 = 88 GB, which is too much for most
/// cases.
pub type Bdd = u32;

/// Supported BDD operations.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BddOpType {
    Not,
    And,
    Or,
    Comp, // Complement: X \ Y
    QuantExist,
    QuantForall,
}

/// BDD manager interface.
pub trait BddManager: BddOp {
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

/// Apply BDD operations.
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

/// Serialize/Deserialize BDD between different instances.
pub trait BddIO<W: IoWrite, R: IoRead> {
    /// Serialize to writer.
    fn serialize(&self, bdd: Bdd, writer: &mut W) -> IoResult<()>;
    /// Deserialize from reader, the returned BDD is reference counted, no need to ref it.
    fn deserialize(&mut self, reader: &mut R) -> IoResult<Bdd>;
}

/// Print BDD in human-understandable format.
pub trait PrintSet<W: IoWrite> {
    // print the BDD in the format of unions of cubes to help debugging. The writer is usually a
    // string or stdout.
    fn print(&self, bdd: Bdd, writer: &mut W) -> IoResult<()>;
}
