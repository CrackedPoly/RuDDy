mod io;
mod node;
mod op;

use self::node::*;
#[allow(unused_imports)]
use crate::bdd::{Bdd, BddIO, BddManager, BddOpType, PrintSet, _Bdd};
use crate::cache::{BinaryCache, Growable, UnaryCache};
use crate::hash::{hash_2, hash_3};
use crate::prime::prime_lte;
use std::fmt::Display;
#[cfg(feature = "op_stat")]
use std::time::UNIX_EPOCH;

macro_rules! mark {
    ($level:expr) => {
        $level |= Self::NODE_MARK;
    };
}
macro_rules! unmark {
    ($level:expr) => {
        $level &= Self::NODE_UNMARK;
    };
}
macro_rules! is_marked {
    ($level:expr) => {
        $level & Self::NODE_MARK != 0
    };
}

pub struct Tobdd {
    nodes: Vec32<NodeStatic>,
    refs: Vec32<NodeRef>,
    links: Vec32<NodeLink>,
    m_stack: Vec<_Bdd>,

    not_cache: UnaryCache,
    and_cache: BinaryCache,
    or_cache: BinaryCache,
    comp_cache: BinaryCache,

    #[cfg(feature = "table_stat")]
    t_stat: TableStat,
    #[cfg(feature = "op_stat")]
    op_stat: OpStat,
    free_node_ptr: u32,     // the linked-list head of free nodes
    free_node_num: u32,     // the number of free nodes
    min_free_node_num: u32, // the minimum number of free nodes
    bucket_size: u32,       // the size of the hash bucket
    node_num: u32,          // the number of nodes
    var_num: u32,           // the number of variables
}

impl Tobdd {
    const FALSE_BDD: Bdd = Bdd(0);
    const _FALSE_BDD: _Bdd = 0;
    const TRUE_BDD: Bdd = Bdd(1);
    const _TRUE_BDD: _Bdd = 1;

    const MIN_REF_CNT: u16 = u16::MIN;
    const MAX_REF_CNT: u16 = u16::MAX;

    // the leftmost bit is used to mark
    const INVALID_LEVEL: u32 = 0x7fff_ffff;
    const MAX_LEVEL: u32 = 0x7fff_fffe;

    const NODE_MARK: u32 = 0x8000_0000;
    const NODE_UNMARK: u32 = 0x7fff_ffff;

    const LIST_END_NODE: u32 = Self::_FALSE_BDD;
    const MIN_FREE_RATIO: u32 = 25; // 1 - .75 (Load Factor)
}

#[cfg(feature = "table_stat")]
#[derive(Default)]
pub struct TableStat {
    pub unique_access: usize,
    pub unique_chain: usize,
    pub unique_hit: usize,
    pub unique_miss: usize,
}

#[cfg(feature = "table_stat")]
impl Display for TableStat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("unique_access: {}, ", self.unique_access))?;
        f.write_fmt(format_args!("unique_chain: {}, ", self.unique_chain))?;
        f.write_fmt(format_args!("unique_hit: {}, ", self.unique_hit))?;
        f.write_fmt(format_args!("unique_miss: {}", self.unique_miss))?;
        Ok(())
    }
}

#[cfg(feature = "op_stat")]
#[derive(Default)]
pub struct OpStat {
    pub not_cnt: usize,
    pub not_time: u128,
    pub and_cnt: usize,
    pub and_time: u128,
    pub or_cnt: usize,
    pub or_time: u128,
    pub comp_cnt: usize,
    pub comp_time: u128,
    pub gc_cnt: usize,
    pub gc_time: u128,
    pub gc_freed: usize,
    pub grow_cnt: usize,
    pub grow_time: u128,
    pub grow_newed: usize,
}

#[cfg(feature = "op_stat")]
impl Display for OpStat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!(
            "NOT: (cnt: {}, time: {} us)\n",
            self.not_cnt, self.not_time
        ))?;
        f.write_fmt(format_args!(
            "AND: (cnt: {}, time: {} us)\n",
            self.and_cnt, self.and_time
        ))?;
        f.write_fmt(format_args!(
            "OR: (cnt: {}, time: {} us)\n",
            self.or_cnt, self.or_time
        ))?;
        f.write_fmt(format_args!(
            "COMP: (cnt: {}, time: {} us)\n",
            self.comp_cnt, self.comp_time
        ))?;
        f.write_fmt(format_args!(
            "GC: (cnt: {}, time: {} us, freed: {})\n",
            self.gc_cnt, self.gc_time, self.gc_freed
        ))?;
        f.write_fmt(format_args!(
            "GROW: (cnt: {}, time: {} us, newed: {})",
            self.grow_cnt, self.grow_time, self.grow_newed
        ))?;
        Ok(())
    }
}

impl Tobdd {
    /// Initialize the BDD nodes, including FALSE, TRUE, variables, and negative variables.
    /// Initialize free node pointer and free node list.
    fn init_nodes(mut self) -> Self {
        // FALSE, TRUE and Variables
        self.refs[Self::_FALSE_BDD].ref_cnt = Self::MAX_REF_CNT;
        self.refs[Self::_TRUE_BDD].ref_cnt = Self::MAX_REF_CNT;
        for i in 0..self.var_num {
            let ix = 2 * (i + 1);
            self.nodes[ix].level = i;
            self.nodes[ix].low = Self::_FALSE_BDD;
            self.nodes[ix].high = Self::_TRUE_BDD;
            self.refs[ix].ref_cnt = Self::MAX_REF_CNT;
            let pos = hash_3!(i, Self::_FALSE_BDD, Self::_TRUE_BDD) % self.bucket_size;
            self.links[ix].next = self.links[pos].hash;
            self.links[pos].hash = ix;

            self.nodes[ix + 1].level = i;
            self.nodes[ix + 1].low = Self::_TRUE_BDD;
            self.nodes[ix + 1].high = Self::_FALSE_BDD;
            self.refs[ix + 1].ref_cnt = Self::MAX_REF_CNT;
            let pos = hash_3!(i, Self::_TRUE_BDD, Self::_FALSE_BDD) % self.bucket_size;
            self.links[ix + 1].next = self.links[pos].hash;
            self.links[pos].hash = ix + 1;
        }
        // the rest is free nodes
        self.free_node_ptr = 2 * (self.var_num + 1);
        self.free_node_num = self.node_num - self.free_node_ptr;
        for i in self.free_node_ptr..self.node_num {
            self.links[i].next = i + 1;
        }
        return self;
    }

    fn make_node(&mut self, level: u32, low: u32, high: u32) -> _Bdd {
        #[cfg(feature = "table_stat")]
        {
            self.t_stat.unique_access += 1;
        }
        // find existing node from the bucket
        let mut pos = hash_3!(level, low, high) % self.bucket_size;
        let mut curr = self.links[pos].hash; // first node in the bucket
        while curr != Self::LIST_END_NODE {
            let _node = &self.nodes[curr];
            if _node.level == level && _node.low == low && _node.high == high {
                #[cfg(feature = "table_stat")]
                {
                    self.t_stat.unique_hit += 1;
                }
                return curr;
            }
            curr = self.links[curr].next;
            #[cfg(feature = "table_stat")]
            {
                self.t_stat.unique_chain += 1;
            }
        }
        #[cfg(feature = "table_stat")]
        {
            self.t_stat.unique_miss += 1;
        }
        // check the necessary of resize
        if self.free_node_num == 1 {
            if None == self.gc() || self.free_node_num < self.min_free_node_num {
                self.resize(self.node_num * 2);
                pos = hash_3!(level, low, high) % self.bucket_size;
            }
        }
        let free_idx = self.get_free_node();
        return self.insert(pos, free_idx, level, low, high);
    }

    fn resize(&mut self, new_size: u32) {
        #[cfg(feature = "op_stat")]
        {
            self.op_stat.grow_cnt += 1;
            self.op_stat.grow_newed -= self.free_node_num as usize;
            self.op_stat.grow_time -= UNIX_EPOCH.elapsed().unwrap().as_micros();
        }
        let old_size = self.node_num;
        self.node_num = new_size;
        self.bucket_size = prime_lte(new_size);
        self.min_free_node_num = Self::MIN_FREE_RATIO * new_size / 100;
        self.free_node_num += new_size - old_size;
        // resize nodes
        let mut new_nodes: Vec32<NodeStatic> = Vec32::new(new_size);
        for _ in 0..new_size {
            new_nodes.push(NodeStatic::default());
        }
        new_nodes.data[0..old_size as usize].copy_from_slice(&self.nodes.data);
        // resize refs
        let mut new_refs: Vec32<NodeRef> = Vec32::new(new_size);
        for _ in 0..new_size {
            new_refs.push(NodeRef::default());
        }
        new_refs.data[0..old_size as usize].copy_from_slice(&self.refs.data);
        // resize links, including rehashing
        let mut new_links: Vec32<NodeLink> = Vec32::new(new_size);
        for _ in 0..new_size {
            new_links.push(NodeLink::default());
        }
        let mut _pos = 0;
        for i in 0..old_size {
            _pos = hash_3!(self.nodes[i].level, self.nodes[i].low, self.nodes[i].high)
                % self.bucket_size;
            new_links[i].next = new_links[_pos].hash;
            new_links[_pos].hash = i;
        }
        _pos = self.free_node_ptr;
        let mut _next_free_pos = self.links[_pos].next;
        while _next_free_pos != old_size {
            new_links[_pos].next = _next_free_pos;
            _pos = _next_free_pos;
            _next_free_pos = self.links[_pos].next;
        }
        new_links[_pos].next = _next_free_pos;
        // _next_free_pos == old_size
        for i in old_size..new_size {
            new_links[i].next = i + 1;
        }
        self.nodes = new_nodes;
        self.refs = new_refs;
        self.links = new_links;
        self.resize_cache();
        #[cfg(feature = "op_stat")]
        {
            self.op_stat.grow_newed += self.free_node_num as usize;
            self.op_stat.grow_time += UNIX_EPOCH.elapsed().unwrap().as_micros();
        }
    }

    /// Build a new node with the given level, low, and high.
    fn get_free_node(&mut self) -> u32 {
        let free = self.free_node_ptr;
        self.free_node_ptr = self.links[free].next;
        self.free_node_num -= 1;
        return free;
    }

    /// Insert a new node at the given hash bucket.
    fn insert(&mut self, bucket_pos: u32, free_pos: u32, level: u32, low: u32, high: u32) -> _Bdd {
        self.links[free_pos].next = self.links[bucket_pos].hash;
        self.links[bucket_pos].hash = free_pos;
        self.nodes[free_pos].level = level;
        self.nodes[free_pos].low = low;
        self.nodes[free_pos].high = high;
        return free_pos;
    }

    fn invalidate_cache(&mut self) {
        self.not_cache.invalidate_all();
        self.and_cache.invalidate_all();
        self.or_cache.invalidate_all();
        self.comp_cache.invalidate_all();
    }

    fn resize_cache(&mut self) {
        self.not_cache.grow(self.not_cache.table_size * 2);
        self.and_cache.grow(self.and_cache.table_size * 2);
        self.or_cache.grow(self.or_cache.table_size * 2);
        self.comp_cache.grow(self.comp_cache.table_size * 2);
    }

    fn mark_node_rec(&mut self, bdd: _Bdd) -> () {
        if bdd <= Self::_TRUE_BDD || is_marked!(self.nodes[bdd].level) {
            return;
        }
        mark!(self.nodes[bdd].level);
        self.mark_node_rec(self.nodes[bdd].low);
        self.mark_node_rec(self.nodes[bdd].high);
    }
}

impl BddManager for Tobdd {
    fn init(node_size: u32, cache_size: u32, var_num: u32) -> Self {
        assert!(var_num <= Self::MAX_LEVEL);
        let mut nodes = Vec32::new(node_size);
        let mut refs = Vec32::new(node_size);
        let mut links = Vec32::new(node_size);
        for _ in 0..node_size {
            nodes.push(NodeStatic::default());
            refs.push(NodeRef::default());
            links.push(NodeLink::default());
        }

        Tobdd {
            nodes,
            refs,
            links,
            m_stack: Vec::with_capacity(16),
            not_cache: UnaryCache::new(cache_size, BddOpType::Not),
            and_cache: BinaryCache::new(cache_size, BddOpType::And),
            or_cache: BinaryCache::new(cache_size, BddOpType::Or),
            comp_cache: BinaryCache::new(cache_size, BddOpType::Comp),
            #[cfg(feature = "table_stat")]
            t_stat: TableStat::default(),
            #[cfg(feature = "op_stat")]
            op_stat: OpStat::default(),
            free_node_ptr: 0,
            free_node_num: 0,
            min_free_node_num: Self::MIN_FREE_RATIO * node_size / 100,
            bucket_size: prime_lte(node_size),
            node_num: node_size,
            var_num,
        }
        .init_nodes()
    }

    fn get_var(&self, var: u16) -> Bdd {
        return Bdd((2 * var + 2) as u32);
    }

    fn get_nvar(&self, var: u16) -> Bdd {
        return Bdd((2 * var + 3) as u32);
    }

    fn get_true(&self) -> Bdd {
        return Self::TRUE_BDD;
    }

    fn get_false(&self) -> Bdd {
        return Self::FALSE_BDD;
    }

    fn get_node_num(&self) -> u32 {
        return self.node_num - self.free_node_num;
    }

    fn ref_bdd(&mut self, bdd: Bdd) -> Bdd {
        if self.refs[bdd.0].ref_cnt != Self::MAX_REF_CNT {
            self.refs[bdd.0].ref_cnt += 1;
        }
        return bdd;
    }

    fn deref_bdd(&mut self, bdd: Bdd) -> Bdd {
        let ref_cnt = self.refs[bdd.0].ref_cnt;
        if ref_cnt > Self::MIN_REF_CNT && ref_cnt < Self::MAX_REF_CNT {
            self.refs[bdd.0].ref_cnt -= 1;
        }
        return bdd;
    }

    fn gc(&mut self) -> Option<usize> {
        #[cfg(feature = "op_stat")]
        {
            self.op_stat.gc_cnt += 1;
            self.op_stat.gc_freed -= self.free_node_num as usize;
            self.op_stat.gc_time -= UNIX_EPOCH.elapsed().unwrap().as_micros();
        }
        let old_free_node_num = self.free_node_num;
        for i in 0..self.m_stack.len() {
            self.mark_node_rec(self.m_stack[i]);
        }
        for n in 0..self.node_num {
            if self.refs[n].ref_cnt > 0 {
                self.mark_node_rec(n);
                self.links[n].hash = Self::LIST_END_NODE;
            }
        }
        // only referenced nodes are marked
        self.free_node_ptr = self.node_num;
        self.free_node_num = 0;
        for n in (2..self.node_num).rev() {
            if is_marked!(self.nodes[n].level) {
                unmark!(self.nodes[n].level);
                let pos = hash_3!(self.nodes[n].level, self.nodes[n].low, self.nodes[n].high)
                    % self.bucket_size;
                self.links[n].next = self.links[pos].hash;
                self.links[pos].hash = n;
            } else {
                self.nodes[n].level = Self::INVALID_LEVEL;
                self.links[n].next = self.free_node_ptr;
                self.free_node_ptr = n;
                self.free_node_num += 1;
            }
        }
        self.invalidate_cache();
        #[cfg(feature = "op_stat")]
        {
            self.op_stat.gc_freed += self.free_node_num as usize;
            self.op_stat.gc_time += UNIX_EPOCH.elapsed().unwrap().as_micros();
        }
        let freed = old_free_node_num - self.free_node_num;
        return if freed > 0 {
            Some(freed as usize)
        } else {
            None
        };
    }
}

impl Display for Tobdd {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Tobdd Debug Information\n")?;
        for i in 0..self.node_num {
            f.write_fmt(format_args!(
                "--------------------------- node: {} ---------------------------\n",
                i
            ))?;
            f.write_fmt(format_args!("{:?}\n", self.nodes[i]))?;
            f.write_fmt(format_args!("{:?}\n", self.refs[i]))?;
            f.write_fmt(format_args!("{:?}\n", self.links[i]))?;
        }

        f.write_fmt(format_args!("free_node_ptr: {:?}\n", self.free_node_ptr))?;
        f.write_fmt(format_args!("free_node_num: {:?}\n", self.free_node_num))?;
        f.write_fmt(format_args!(
            "min_free_nodes_num: {:?}\n",
            self.min_free_node_num
        ))?;
        f.write_fmt(format_args!("bucket_size: {:?}\n", self.bucket_size))?;
        f.write_fmt(format_args!("node_num: {:?}\n", self.node_num))?;
        f.write_fmt(format_args!("var_num: {:?}\n", self.var_num))?;
        #[cfg(feature = "cache_stat")]
        {
            f.write_fmt(format_args!("NOT cache stat: {}\n", self.not_cache.stat))?;
            f.write_fmt(format_args!("AND cache stat: {}\n", self.and_cache.stat))?;
            f.write_fmt(format_args!("OR cache stat: {}\n", self.or_cache.stat))?;
            f.write_fmt(format_args!("COMP cache stat: {}\n", self.comp_cache.stat))?;
        }
        #[cfg(feature = "table_stat")]
        {
            f.write_fmt(format_args!("Table stat: {}\n", self.t_stat))?;
        }
        #[cfg(feature = "op_stat")]
        {
            f.write_fmt(format_args!("Op stat: {}\n", self.op_stat))?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bdd::{tobdd, BddOp};

    #[test]
    fn test_tobdd_resize() {
        const NODE_SIZE: u32 = 10;

        let mut tobdd = Tobdd::init(NODE_SIZE, NODE_SIZE, 3);
        let a = tobdd.get_var(0);
        let b = tobdd.get_var(1);
        let c = tobdd.get_var(2);
        // initially, there are only 2 free nodes (20% < 25%), so the resize will be triggered
        let ab = tobdd.and(a, b);
        tobdd.ref_bdd(ab);
        let bc = tobdd.and(b, c);
        tobdd.ref_bdd(bc);
        let abc = tobdd.and(ab, bc);
        tobdd.ref_bdd(abc);
        assert_eq!(tobdd.node_num, NODE_SIZE * 2);
    }

    #[test]
    fn test_tobdd_gc() {
        const NODE_SIZE: u32 = 10;

        let mut tobdd = Tobdd::init(NODE_SIZE, NODE_SIZE, 3);
        let a = tobdd.get_var(0);
        let b = tobdd.get_var(1);
        let c = tobdd.get_var(2);
        // since ab or bc are not referenced, they will be freed after gc
        tobdd.and(a, b);
        tobdd.and(b, c);
        assert_eq!(tobdd.node_num, NODE_SIZE);
        assert_eq!(tobdd.free_node_num, 1);
    }

    #[test]
    fn test_tobdd_io() {
        const NODE_SIZE: u32 = 10;

        let mut tobdd = Tobdd::init(NODE_SIZE, NODE_SIZE, 3);
        let a = tobdd.get_var(0);
        let b = tobdd.get_var(1);
        let c = tobdd.get_var(2);

        let ab = tobdd.and(a, b);
        tobdd.ref_bdd(ab);
        let bc = tobdd.and(b, c);
        tobdd.ref_bdd(bc);
        let abc = tobdd.and(ab, bc);
        tobdd.ref_bdd(abc);

        let mut buffer = Vec::new();
        let size = tobdd.write_buffer(&abc, &mut buffer).unwrap();
        assert_eq!(size, 4 * 12);
        let mut another = Tobdd::init(NODE_SIZE, NODE_SIZE, 3);
        let another_abc = another.read_buffer(&buffer).unwrap();
        another.ref_bdd(another_abc);
        assert_eq!(another.node_num, NODE_SIZE * 2);
    }

    #[test]
    fn test_tobdd_print_set() {
        const NODE_SIZE: u32 = 10;

        let mut tobdd = Tobdd::init(NODE_SIZE, NODE_SIZE, 3);
        let a = tobdd.get_var(0);
        let b = tobdd.get_var(1);
        let c = tobdd.get_var(2);

        let ab = tobdd.and(a, b);
        tobdd.ref_bdd(ab);
        let bc = tobdd.and(b, c);
        tobdd.ref_bdd(bc);
        let abc = tobdd.or(ab, bc);
        tobdd.ref_bdd(abc);

        let mut buf = String::new();
        tobdd::PrintSet::fmt(&tobdd, &mut buf, &tobdd.get_true()).unwrap();
        assert_eq!(buf, "TRUE\n");
        buf.clear();
        tobdd::PrintSet::fmt(&tobdd, &mut buf, &tobdd.get_false()).unwrap();
        assert_eq!(buf, "FALSE\n");
        buf.clear();
        tobdd::PrintSet::fmt(&tobdd, &mut buf, &abc).unwrap();
        assert_eq!(buf, "011\n11-\n");
    }
}
