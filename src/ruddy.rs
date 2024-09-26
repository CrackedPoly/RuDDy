use crate::{
    cache::{BinaryCache, Growable, UnaryCache},
    hash::{hash_2, hash_3},
    node::*,
    prime::prime_lte,
    Bdd, BddIO, BddManager, BddOp, BddOpType, PrintSet,
};
use nohash::{BuildNoHashHasher, IntMap};
#[allow(unused_imports)]
use std::fmt::{Debug, Display};
use std::{
    io::{Read as IoRead, Result as IoResult, Write as IoWrite},
    mem,
};

#[cfg(feature = "op_stat")]
use cpu_time::ThreadTime;

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

pub struct Ruddy {
    nodes: Vec32<NodeStatic>,
    refs: Vec32<NodeRef>,
    links: Vec32<NodeLink>,
    m_stack: Vec<Bdd>,

    quant_varset: Vec32<bool>,
    quant_apply_op: BddOpType,
    quant_cube: Bdd,
    varset_last: Bdd,

    not_cache: UnaryCache,
    and_cache: BinaryCache,
    or_cache: BinaryCache,
    comp_cache: BinaryCache,
    quant_exist_cache: BinaryCache,
    quant_forall_cache: BinaryCache,

    #[cfg(feature = "table_stat")]
    t_stat: TableStat,
    #[cfg(feature = "op_stat")]
    op_stat: OpStat,
    #[cfg(feature = "op_stat")]
    timer: ThreadTime,

    free_node_ptr: u32,     // the linked-list head of free nodes
    free_node_num: u32,     // the number of free nodes
    min_free_node_num: u32, // the minimum number of free nodes
    bucket_size: u32,       // the size of the hash bucket
    node_num: u32,          // the number of nodes
    var_num: u32,           // the number of variables
}

impl Ruddy {
    pub const FALSE_BDD: Bdd = 0;
    pub const TRUE_BDD: Bdd = 1;

    pub const MIN_REF_CNT: u16 = u16::MIN;
    pub const MAX_REF_CNT: u16 = u16::MAX;

    // the leftmost bit is used to mark
    pub const INVALID_LEVEL: u32 = 0x7fff_ffff;
    pub const MAX_LEVEL: u32 = 0x7fff_fffe;

    pub const NODE_MARK: u32 = 0x8000_0000;
    pub const NODE_UNMARK: u32 = 0x7fff_ffff;

    pub const LIST_END_NODE: u32 = Self::FALSE_BDD;
    pub const MIN_FREE_RATIO: u32 = 25; // 1 - .75 (Load Factor)
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

    pub quant_exist_cnt: usize,
    pub quant_exist_time: u128,

    pub quant_forall_cnt: usize,
    pub quant_forall_time: u128,

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

impl Ruddy {
    fn make_node(&mut self, level: u32, low: u32, high: u32) -> Bdd {
        if low == high {
            return low;
        }
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
            self.gc();
            if self.free_node_num < self.min_free_node_num {
                self.resize(self.node_num * 2);
                pos = hash_3!(level, low, high) % self.bucket_size;
            }
        }
        let free_idx = self.get_free_node();
        self.insert(pos, free_idx, level, low, high)
    }

    fn resize(&mut self, new_size: u32) {
        #[cfg(feature = "op_stat")]
        {
            self.op_stat.grow_cnt += 1;
            self.op_stat.grow_newed -= self.free_node_num as usize;
            self.op_stat.grow_time -= self.timer.elapsed().as_micros();
        }
        let old_size = self.node_num;
        self.node_num = new_size;
        self.bucket_size = prime_lte(new_size);
        self.min_free_node_num = Self::MIN_FREE_RATIO * new_size / 100;
        self.free_node_num += new_size - old_size;
        // resize nodes
        let mut new_nodes: Vec32<NodeStatic> = Vec32::with_capacity(new_size);
        for _ in 0..new_size {
            new_nodes.push(NodeStatic::default());
        }
        new_nodes.data[0..old_size as usize].copy_from_slice(&self.nodes.data);
        // resize refs
        let mut new_refs: Vec32<NodeRef> = Vec32::with_capacity(new_size);
        for _ in 0..new_size {
            new_refs.push(NodeRef::default());
        }
        new_refs.data[0..old_size as usize].copy_from_slice(&self.refs.data);
        // resize links, including rehashing
        let mut new_links: Vec32<NodeLink> = Vec32::with_capacity(new_size);
        for _ in 0..new_size {
            new_links.push(NodeLink::default());
        }
        // connect the new free nodes
        for i in (old_size..new_size).rev() {
            new_links[i].next = i + 1;
        }
        let mut _pos = 0;
        for i in (0..old_size).rev() {
            if self.nodes[i].level == Self::INVALID_LEVEL {
                // the node is free
                new_links[i].next = self.links[i].next;
            } else {
                // the node is occupied
                _pos = hash_3!(self.nodes[i].level, self.nodes[i].low, self.nodes[i].high)
                    % self.bucket_size;
                new_links[i].next = new_links[_pos].hash;
                new_links[_pos].hash = i;
            }
        }
        self.nodes = new_nodes;
        self.refs = new_refs;
        self.links = new_links;
        self.resize_cache();
        #[cfg(feature = "op_stat")]
        {
            self.op_stat.grow_newed += self.free_node_num as usize;
            self.op_stat.grow_time += self.timer.elapsed().as_micros();
        }
    }

    /// Build a new node with the given level, low, and high.
    fn get_free_node(&mut self) -> u32 {
        let free = self.free_node_ptr;
        self.free_node_ptr = self.links[free].next;
        self.free_node_num -= 1;
        free
    }

    fn prepare_varset(&mut self, mut cube: Bdd) {
        assert!(
            cube > Self::TRUE_BDD,
            "Invalid varset, cube should be neither FALSE nor TRUE"
        );
        self.quant_varset.data.fill(false);
        while cube > Self::TRUE_BDD {
            self.varset_last = self.level(cube);
            self.quant_varset[self.varset_last] = true;
            cube = self.high(cube);
        }
    }

    /// Insert a new node at the given hash bucket.
    fn insert(&mut self, bucket_pos: u32, free_pos: u32, level: u32, low: u32, high: u32) -> Bdd {
        self.links[free_pos].next = self.links[bucket_pos].hash;
        self.links[bucket_pos].hash = free_pos;
        self.nodes[free_pos].level = level;
        self.nodes[free_pos].low = low;
        self.nodes[free_pos].high = high;
        free_pos
    }

    fn invalidate_cache(&mut self) {
        self.not_cache.invalidate_all();
        self.and_cache.invalidate_all();
        self.or_cache.invalidate_all();
        self.comp_cache.invalidate_all();
        self.quant_exist_cache.invalidate_all();
        self.quant_forall_cache.invalidate_all();
    }

    fn resize_cache(&mut self) {
        self.not_cache.grow(self.not_cache.table_size * 2);
        self.and_cache.grow(self.and_cache.table_size * 2);
        self.or_cache.grow(self.or_cache.table_size * 2);
        self.comp_cache.grow(self.comp_cache.table_size * 2);
        self.quant_exist_cache
            .grow(self.quant_exist_cache.table_size * 2);
        self.quant_forall_cache
            .grow(self.quant_forall_cache.table_size * 2);
    }

    fn mark_node_rec(&mut self, bdd: Bdd) {
        if bdd <= Self::TRUE_BDD || is_marked!(self.nodes[bdd].level) {
            return;
        }
        mark!(self.nodes[bdd].level);
        self.mark_node_rec(self.nodes[bdd].low);
        self.mark_node_rec(self.nodes[bdd].high);
    }
}

impl BddManager for Ruddy {
    fn init(node_num: u32, cache_size: u32, var_num: u32) -> Ruddy {
        // ensure that the number of variables is within the limit
        assert!(var_num <= Self::MAX_LEVEL);
        // ensure that initial node number is able to accommodate the given
        // number of variables
        let (n_num, c_num) = if (2 * var_num + 2) > node_num {
            let ns = 2 * var_num + 3;
            let cs = ns * cache_size / node_num;
            (ns, cs)
        } else {
            (node_num, cache_size)
        };
        let mut nodes = Vec32::with_capacity(n_num);
        let mut refs = Vec32::with_capacity(n_num);
        let mut links = Vec32::with_capacity(n_num);
        let mut varset = Vec32::with_capacity(var_num);
        for _ in 0..n_num {
            nodes.push(NodeStatic::default());
            refs.push(NodeRef::default());
            links.push(NodeLink::default());
        }

        let bucket_size = prime_lte(n_num);
        // FALSE, TRUE and Variables
        refs[Self::FALSE_BDD].ref_cnt = Self::MAX_REF_CNT;
        refs[Self::TRUE_BDD].ref_cnt = Self::MAX_REF_CNT;
        for i in 0..var_num {
            let ix = 2 * (i + 1);
            nodes[ix].level = i;
            nodes[ix].low = Self::FALSE_BDD;
            nodes[ix].high = Self::TRUE_BDD;
            refs[ix].ref_cnt = Self::MAX_REF_CNT;
            let pos = hash_3!(i, Self::FALSE_BDD, Self::TRUE_BDD) % bucket_size;
            links[ix].next = links[pos].hash;
            links[pos].hash = ix;

            nodes[ix + 1].level = i;
            nodes[ix + 1].low = Self::TRUE_BDD;
            nodes[ix + 1].high = Self::FALSE_BDD;
            refs[ix + 1].ref_cnt = Self::MAX_REF_CNT;
            let pos = hash_3!(i, Self::TRUE_BDD, Self::FALSE_BDD) % bucket_size;
            links[ix + 1].next = links[pos].hash;
            links[pos].hash = ix + 1;

            varset.push(false);
        }
        // the rest is free nodes
        let free_node_ptr = 2 * (var_num + 1);
        let free_node_num = n_num - free_node_ptr;
        for i in free_node_ptr..n_num {
            links[i].next = i + 1;
        }

        Ruddy {
            nodes,
            refs,
            links,
            m_stack: Vec::with_capacity(16),

            quant_varset: varset,
            quant_apply_op: BddOpType::And,
            quant_cube: Self::FALSE_BDD,
            varset_last: Self::FALSE_BDD,

            not_cache: UnaryCache::new(BddOpType::Not, c_num),
            and_cache: BinaryCache::new(BddOpType::And, c_num),
            or_cache: BinaryCache::new(BddOpType::Or, c_num),
            comp_cache: BinaryCache::new(BddOpType::Comp, c_num),
            quant_exist_cache: BinaryCache::new(BddOpType::QuantExist, c_num),
            quant_forall_cache: BinaryCache::new(BddOpType::QuantForall, c_num),

            #[cfg(feature = "table_stat")]
            t_stat: TableStat::default(),
            #[cfg(feature = "op_stat")]
            op_stat: OpStat::default(),
            #[cfg(feature = "op_stat")]
            timer: ThreadTime::now(),

            free_node_ptr,
            free_node_num,
            min_free_node_num: Self::MIN_FREE_RATIO * n_num / 100,
            bucket_size,
            node_num: n_num,
            var_num,
        }
    }

    #[inline]
    fn get_var(&self, var: u16) -> Bdd {
        (2 * var + 2) as u32
    }

    #[inline]
    fn get_nvar(&self, var: u16) -> Bdd {
        (2 * var + 3) as u32
    }

    #[inline]
    fn get_true(&self) -> Bdd {
        Self::TRUE_BDD
    }

    #[inline]
    fn get_false(&self) -> Bdd {
        Self::FALSE_BDD
    }

    #[inline]
    fn get_node_num(&self) -> u32 {
        self.node_num - self.free_node_num
    }

    #[inline]
    fn ref_bdd(&mut self, bdd: Bdd) -> Bdd {
        self.refs[bdd].ref_cnt = self.refs[bdd].ref_cnt.saturating_add(1);
        bdd
    }

    #[inline]
    fn deref_bdd(&mut self, bdd: Bdd) -> Bdd {
        if bdd < 2 * self.var_num + 2 {
            return bdd;
        }
        self.refs[bdd].ref_cnt = self.refs[bdd].ref_cnt.saturating_sub(1);
        bdd
    }

    fn gc(&mut self) -> usize {
        #[cfg(feature = "op_stat")]
        {
            self.op_stat.gc_cnt += 1;
            self.op_stat.gc_freed -= self.free_node_num as usize;
            self.op_stat.gc_time -= self.timer.elapsed().as_micros();
        }
        let old_free_node_num = self.free_node_num;
        for i in 0..self.m_stack.len() {
            self.mark_node_rec(self.m_stack[i]);
        }
        for n in 0..self.node_num {
            // nodes in hash bucket may be freed
            self.links[n].hash = Self::LIST_END_NODE;
            if self.refs[n].ref_cnt > 0 {
                self.mark_node_rec(n);
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
            self.op_stat.gc_time += self.timer.elapsed().as_micros();
        }
        (self.free_node_num - old_free_node_num) as usize
    }
}

impl Ruddy {
    #[inline]
    fn level(&self, bdd: Bdd) -> u32 {
        self.nodes[bdd].level
    }

    #[inline]
    fn low(&self, bdd: Bdd) -> Bdd {
        self.nodes[bdd].low
    }

    #[inline]
    fn high(&self, bdd: Bdd) -> Bdd {
        self.nodes[bdd].high
    }
}

impl Ruddy {
    fn _not_rec(&mut self, bdd: Bdd) -> Bdd {
        if bdd <= Self::TRUE_BDD {
            return bdd ^ 1;
        }
        if let Some(_bdd) = self.not_cache.get(bdd) {
            return _bdd;
        }
        let f_low = self._not_rec(self.low(bdd));
        self.m_stack.push(f_low);
        let f_high = self._not_rec(self.high(bdd));
        self.m_stack.push(f_high);
        let res = self.make_node(
            self.level(bdd),
            self.m_stack[self.m_stack.len() - 2],
            self.m_stack[self.m_stack.len() - 1],
        );
        unsafe {
            self.m_stack.set_len(self.m_stack.len() - 2);
        }
        self.not_cache.put(bdd, res);
        res
    }

    fn _apply_rec(&mut self, lhs: Bdd, rhs: Bdd, op: BddOpType) -> Bdd {
        // even self. is tedious, so avoid it
        macro_rules! level {
            ($bdd:expr) => {
                self.level($bdd)
            };
        }
        macro_rules! low {
            ($bdd:expr) => {
                self.low($bdd)
            };
        }
        macro_rules! high {
            ($bdd:expr) => {
                self.high($bdd)
            };
        }

        let hash = match op {
            BddOpType::And => {
                if lhs == rhs || rhs == Self::TRUE_BDD {
                    return lhs;
                }
                if lhs == Self::FALSE_BDD || rhs == Self::FALSE_BDD {
                    return Self::FALSE_BDD;
                }
                if lhs == Self::TRUE_BDD {
                    return rhs;
                }
                if let Some(bdd) = self.and_cache.get((lhs, rhs)) {
                    return bdd;
                }
                self.and_cache.last_hash
            }
            BddOpType::Or => {
                if lhs == rhs || rhs == Self::FALSE_BDD {
                    return lhs;
                }
                if lhs == Self::TRUE_BDD || rhs == Self::TRUE_BDD {
                    return Self::TRUE_BDD;
                }
                if lhs == Self::FALSE_BDD {
                    return rhs;
                }
                if let Some(bdd) = self.or_cache.get((lhs, rhs)) {
                    return bdd;
                }
                self.or_cache.last_hash
            }
            // lhs \ rhs
            BddOpType::Comp => {
                if lhs == rhs || lhs == Self::FALSE_BDD || rhs == Self::TRUE_BDD {
                    return Self::FALSE_BDD;
                }
                if rhs == Self::FALSE_BDD {
                    return lhs;
                }
                if lhs == Self::TRUE_BDD {
                    return self._not_rec(rhs);
                }
                if let Some(bdd) = self.comp_cache.get((lhs, rhs)) {
                    return bdd;
                }
                self.comp_cache.last_hash
            }
            _ => {
                panic!("Not supported")
            }
        };
        match level!(lhs).cmp(&level!(rhs)) {
            std::cmp::Ordering::Equal => {
                let f_low = self._apply_rec(low!(lhs), low!(rhs), op);
                self.m_stack.push(f_low);
                let f_high = self._apply_rec(high!(lhs), high!(rhs), op);
                self.m_stack.push(f_high);
            }
            std::cmp::Ordering::Less => {
                let f_low = self._apply_rec(low!(lhs), rhs, op);
                self.m_stack.push(f_low);
                let f_high = self._apply_rec(high!(lhs), rhs, op);
                self.m_stack.push(f_high);
            }
            std::cmp::Ordering::Greater => {
                let f_low = self._apply_rec(lhs, low!(rhs), op);
                self.m_stack.push(f_low);
                let f_high = self._apply_rec(lhs, high!(rhs), op);
                self.m_stack.push(f_high);
            }
        }
        let res = self.make_node(
            std::cmp::min(level!(lhs), level!(rhs)),
            self.m_stack[self.m_stack.len() - 2],
            self.m_stack[self.m_stack.len() - 1],
        );
        unsafe {
            self.m_stack.set_len(self.m_stack.len() - 2);
        }
        match op {
            BddOpType::And => self.and_cache.put(hash, (lhs, rhs), res),
            BddOpType::Or => self.or_cache.put(hash, (lhs, rhs), res),
            BddOpType::Comp => self.comp_cache.put(hash, (lhs, rhs), res),
            _ => {
                panic!("Not supported")
            }
        }
        res
    }

    fn _quant_rec(&mut self, bdd: Bdd) -> Bdd {
        let level = self.level(bdd);
        if level > self.varset_last {
            return bdd;
        }
        let hash = {
            let cache: &mut BinaryCache = match self.quant_apply_op {
                BddOpType::Or => &mut self.quant_exist_cache,
                BddOpType::And => &mut self.quant_forall_cache,
                _ => unreachable!("quantification should only use AND or OR"),
            };
            if let Some(res) = cache.get((bdd, self.quant_cube)) {
                return res;
            } else {
                cache.last_hash
            }
        };

        let mut low: Bdd;
        if self.quant_varset[level] {
            low = self.low(bdd);
            let mut high = self.high(bdd);
            if self.level(high) > self.level(low) {
                mem::swap(&mut low, &mut high);
            }
            low = self._quant_rec(low);

            if !((self.quant_apply_op == BddOpType::And && low == Self::FALSE_BDD)
                || (self.quant_apply_op == BddOpType::Or && low == Self::TRUE_BDD))
            {
                self.m_stack.push(low);
                high = self._quant_rec(high);
                self.m_stack.push(high);
                low = self._apply_rec(low, high, self.quant_apply_op);
                unsafe {
                    self.m_stack.set_len(self.m_stack.len() - 2);
                }
            }
        } else {
            low = self._quant_rec(self.low(bdd));
            self.m_stack.push(low);
            let high = self._quant_rec(self.high(bdd));
            self.m_stack.push(high);
            low = self.make_node(level, low, high);
            unsafe {
                self.m_stack.set_len(self.m_stack.len() - 2);
            }
        }

        let cache: &mut BinaryCache = match self.quant_apply_op {
            BddOpType::Or => &mut self.quant_exist_cache,
            BddOpType::And => &mut self.quant_forall_cache,
            _ => unreachable!("quantification should only use AND or OR"),
        };
        cache.put(hash, (bdd, self.quant_cube), low);
        low
    }
}

impl BddOp for Ruddy {
    #[inline]
    fn not(&mut self, bdd: Bdd) -> Bdd {
        #[cfg(feature = "op_stat")]
        {
            self.op_stat.not_cnt += 1;
            self.op_stat.not_time -= self.timer.elapsed().as_micros();
        }
        let ret = self._not_rec(bdd);
        #[cfg(feature = "op_stat")]
        {
            self.op_stat.not_time += self.timer.elapsed().as_micros();
        }
        ret
    }

    #[inline]
    fn and(&mut self, lhs: Bdd, rhs: Bdd) -> Bdd {
        #[cfg(feature = "op_stat")]
        {
            self.op_stat.and_cnt += 1;
            self.op_stat.and_time -= self.timer.elapsed().as_micros();
        }
        let ret = self._apply_rec(lhs, rhs, BddOpType::And);
        #[cfg(feature = "op_stat")]
        {
            self.op_stat.and_time += self.timer.elapsed().as_micros();
        }
        ret
    }

    #[inline]
    fn or(&mut self, lhs: Bdd, rhs: Bdd) -> Bdd {
        #[cfg(feature = "op_stat")]
        {
            self.op_stat.or_cnt += 1;
            self.op_stat.or_time -= self.timer.elapsed().as_micros();
        }
        let ret = self._apply_rec(lhs, rhs, BddOpType::Or);
        #[cfg(feature = "op_stat")]
        {
            self.op_stat.or_time += self.timer.elapsed().as_micros();
        }
        ret
    }

    #[inline]
    fn comp(&mut self, lhs: Bdd, rhs: Bdd) -> Bdd {
        #[cfg(feature = "op_stat")]
        {
            self.op_stat.comp_cnt += 1;
            self.op_stat.comp_time -= self.timer.elapsed().as_micros();
        }
        let ret = self._apply_rec(lhs, rhs, BddOpType::Comp);
        #[cfg(feature = "op_stat")]
        {
            self.op_stat.comp_time += self.timer.elapsed().as_micros();
        }
        ret
    }

    fn exist(&mut self, bdd: Bdd, cube: Bdd) -> Bdd {
        self.quant_apply_op = BddOpType::Or;
        self.quant_cube = cube;
        self.prepare_varset(cube);
        #[cfg(feature = "op_stat")]
        {
            self.op_stat.quant_exist_cnt += 1;
            self.op_stat.quant_exist_time -= self.timer.elapsed().as_micros();
        }
        let ret = self._quant_rec(bdd);
        #[cfg(feature = "op_stat")]
        {
            self.op_stat.quant_exist_time += self.timer.elapsed().as_micros();
        }
        ret
    }

    fn forall(&mut self, bdd: Bdd, cube: Bdd) -> Bdd {
        self.quant_apply_op = BddOpType::And;
        self.quant_cube = cube;
        self.prepare_varset(cube);
        #[cfg(feature = "op_stat")]
        {
            self.op_stat.quant_forall_cnt += 1;
            self.op_stat.quant_forall_time -= self.timer.elapsed().as_micros();
        }
        let ret = self._quant_rec(bdd);
        #[cfg(feature = "op_stat")]
        {
            self.op_stat.quant_forall_time += self.timer.elapsed().as_micros();
        }
        ret
    }
}

impl Debug for Ruddy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "Ruddy Debug Information")?;
        for i in 0..self.node_num {
            f.write_fmt(format_args!(
                "idx: {}, level: {}, low: {}, high: {}, ref: {}, next: {}, hash: {}\n",
                i,
                self.nodes[i].level,
                self.nodes[i].low,
                self.nodes[i].high,
                self.refs[i].ref_cnt,
                self.links[i].next,
                self.links[i].hash
            ))?;
        }

        f.write_fmt(format_args!("free_node_ptr: {:?}\n", self.free_node_ptr))?;
        f.write_fmt(format_args!("free_node_num: {:?}\n", self.free_node_num))?;
        f.write_fmt(format_args!(
            "min_free_nodes_num: {:?}\n",
            self.min_free_node_num
        ))?;
        f.write_fmt(format_args!("bucket size: {:?}\n", self.bucket_size))?;
        f.write_fmt(format_args!(
            "m_stack capacity: {:?}\n",
            self.m_stack.capacity()
        ))?;
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

impl<W: IoWrite, R: IoRead> BddIO<W, R> for Ruddy {
    fn serialize(&self, bdd: Bdd, writer: &mut W) -> IoResult<()> {
        fn write_buffer_rec<W: IoWrite>(ruddy: &Ruddy, bdd: Bdd, writer: &mut W) {
            if bdd > Ruddy::TRUE_BDD {
                // low, high, level traversal
                write_buffer_rec(ruddy, ruddy.nodes[bdd].low, writer);
                write_buffer_rec(ruddy, ruddy.nodes[bdd].high, writer);
                // split u32 into 4 u8
                writer.write_all(&bdd.to_be_bytes()).unwrap();
                writer
                    .write_all(&ruddy.nodes[bdd].level.to_be_bytes())
                    .unwrap();
                writer
                    .write_all(&ruddy.nodes[bdd].low.to_be_bytes())
                    .unwrap();
                writer
                    .write_all(&ruddy.nodes[bdd].high.to_be_bytes())
                    .unwrap();
            }
        }

        write_buffer_rec(self, bdd, writer);
        writer.flush()?;
        Ok(())
    }

    fn deserialize(&mut self, reader: &mut R) -> IoResult<Bdd> {
        let mut map: IntMap<Bdd, Bdd> =
            IntMap::with_capacity_and_hasher(16, BuildNoHashHasher::default());
        map.insert(0, 0);
        map.insert(1, 1);
        #[allow(unused_assignments)]
        let (mut bdd, mut level, mut low, mut high, mut ret) = (0u32, 0u32, 0u32, 0u32, 0u32);
        let mut window = [0u8; 16];
        // merge 4 u8 into 1 u32
        while let Ok(()) = reader.read_exact(&mut window) {
            bdd = u32::from_be_bytes(window[0..4].try_into().unwrap());
            level = u32::from_be_bytes(window[4..8].try_into().unwrap());
            assert!(
                level <= self.var_num,
                "Read Error: local manager does not have Var {level}"
            );
            low = u32::from_be_bytes(window[8..12].try_into().unwrap());
            high = u32::from_be_bytes(window[12..16].try_into().unwrap());

            low = *map.get(&low).unwrap();
            high = *map.get(&high).unwrap();
            ret = self.make_node(level, low, high);
            map.insert(bdd, self.ref_bdd(ret));
        }
        for b in map.values() {
            self.deref_bdd(*b);
        }
        Ok(ret)
    }
}

impl<W: IoWrite> PrintSet<W> for Ruddy {
    fn print(&self, bdd: Bdd, f: &mut W) -> IoResult<()> {
        fn fmt_rec<W: IoWrite>(
            ruddy: &Ruddy,
            f: &mut W,
            chars: &mut Vec<char>,
            _bdd: Bdd,
            curr: u32,
        ) -> IoResult<()> {
            if curr == ruddy.var_num {
                for c in chars.iter().take(ruddy.var_num as usize) {
                    f.write_fmt(format_args!("{}", c))?;
                }
                f.write_fmt(format_args!("\n"))?;
                return Ok(());
            }
            let level = ruddy.nodes[_bdd].level;
            if level > curr || _bdd == 1 {
                chars[curr as usize] = '*';
                fmt_rec(ruddy, f, chars, _bdd, curr + 1)?;
                return Ok(());
            }
            let low = ruddy.nodes[_bdd].low;
            let high = ruddy.nodes[_bdd].high;
            if low != 0 {
                chars[curr as usize] = '0';
                fmt_rec(ruddy, f, chars, low, curr + 1)?;
            }
            if high != 0 {
                chars[curr as usize] = '1';
                fmt_rec(ruddy, f, chars, high, curr + 1)?;
            }
            Ok(())
        }

        if bdd <= Self::TRUE_BDD {
            f.write_fmt(format_args!(
                "{}",
                if bdd == 0 { "FALSE\n" } else { "TRUE\n" }
            ))?;
        } else {
            let mut set_chars: Vec<char> = vec!['-'; self.var_num as usize];
            fmt_rec(self, f, &mut set_chars, bdd, 0)?;
        }
        Ok(())
    }
}
#[cfg(test)]
mod tests {
    use flate2::Compression;
    use std::str::from_utf8;

    use super::*;
    use crate::BddOp;

    #[test]
    fn test_ruddy_and() {
        const NODE_SIZE: u32 = 10;

        let mut manager = Ruddy::init(NODE_SIZE, NODE_SIZE, 3);
        let a = manager.get_nvar(0);
        let b = manager.get_nvar(1);
        let c = manager.get_nvar(2);

        let mut buf = Vec::new();

        let and_ab = manager.and(a, b);
        manager.ref_bdd(and_ab);
        let and_abc = manager.and(and_ab, c);
        manager.ref_bdd(and_abc);

        manager.print(and_abc, &mut buf).unwrap();
        assert_eq!(from_utf8(&buf).unwrap(), "000\n");

        manager.deref_bdd(and_ab);
        manager.deref_bdd(and_abc);
    }

    #[test]
    fn test_ruddy_comp() {
        const NODE_SIZE: u32 = 20;

        let mut manager = Ruddy::init(NODE_SIZE, NODE_SIZE, 3);
        let a = manager.get_var(0);
        let nb = manager.get_nvar(1);
        let _c = manager.get_var(2);

        let mut buf = Vec::new();

        let or_a_nb = manager.and(a, nb);
        manager.ref_bdd(or_a_nb);
        let comp = manager.comp(a, or_a_nb);
        manager.ref_bdd(comp);

        manager.print(comp, &mut buf).unwrap();
        assert_eq!(from_utf8(&buf).unwrap(), "11*\n");

        manager.deref_bdd(or_a_nb);
        manager.deref_bdd(comp);
    }

    #[test]
    fn test_ruddy_resize() {
        const NODE_SIZE: u32 = 10;

        let mut manager = Ruddy::init(NODE_SIZE, NODE_SIZE, 3);
        let a = manager.get_var(0);
        let b = manager.get_var(1);
        let c = manager.get_var(2);
        // initially, there are only 2 free nodes (20% < 25%), so the resize will be triggered
        let ab = manager.and(a, b);
        manager.ref_bdd(ab);
        let bc = manager.and(b, c);
        manager.ref_bdd(bc);
        let abc = manager.and(ab, bc);
        manager.ref_bdd(abc);

        assert_eq!(manager.node_num, NODE_SIZE * 2);

        manager.deref_bdd(ab);
        manager.deref_bdd(bc);
        manager.deref_bdd(abc);
    }

    #[test]
    fn test_ruddy_gc() {
        const NODE_SIZE: u32 = 10;

        let mut manager = Ruddy::init(NODE_SIZE, NODE_SIZE, 3);
        let a = manager.get_var(0);
        let b = manager.get_var(1);
        let c = manager.get_var(2);
        // since ab or bc are not referenced, they will be freed after gc
        manager.and(a, b);
        manager.and(b, c);
        manager.gc();

        assert_eq!(manager.node_num, NODE_SIZE);
        assert_eq!(manager.free_node_num, 2);
    }

    #[test]
    fn test_ruddy_io() {
        const NODE_SIZE: u32 = 10;

        let mut manager = Ruddy::init(NODE_SIZE, NODE_SIZE, 3);
        let a = manager.get_var(0);
        let b = manager.get_var(1);
        let c = manager.get_var(2);

        let ab = manager.and(a, b);
        manager.ref_bdd(ab);
        let bc = manager.and(b, c);
        manager.ref_bdd(bc);
        let abc = manager.and(ab, bc);
        manager.ref_bdd(abc);

        let mut buffer = Vec::new();
        BddIO::<Vec<u8>, &[u8]>::serialize(&manager, abc, &mut buffer).unwrap();

        let mut another_manager = Ruddy::init(NODE_SIZE, NODE_SIZE, 3);
        let another_abc =
            BddIO::<Vec<u8>, &[u8]>::deserialize(&mut another_manager, &mut &buffer[..]).unwrap();
        another_manager.ref_bdd(another_abc);
        assert_eq!(another_manager.node_num, NODE_SIZE * 2);

        manager.deref_bdd(ab);
        manager.deref_bdd(bc);
        manager.deref_bdd(abc);
        another_manager.deref_bdd(another_abc);
    }

    #[test]
    fn test_ruddy_io_compressed() {
        const NODE_SIZE: u32 = 100;
        const CACHE_SIZE: u32 = 10;
        const VAR_NUM: u32 = 32;

        let mut manager = Ruddy::init(NODE_SIZE, CACHE_SIZE, VAR_NUM);
        let mut and_all: Bdd = manager.get_true();
        let mut tmp: Bdd;
        for i in 0..VAR_NUM {
            let var = manager.get_var(i as u16);
            tmp = manager.and(and_all, var);
            manager.ref_bdd(tmp);
            manager.deref_bdd(and_all);
            and_all = tmp;
        }

        let mut encoder = flate2::write::DeflateEncoder::new(Vec::new(), Compression::fast());
        BddIO::<flate2::write::DeflateEncoder<Vec<u8>>, flate2::read::DeflateDecoder<&[u8]>>::serialize(&manager, and_all, &mut encoder).unwrap();
        let buffer = encoder.finish().unwrap();
        manager.deref_bdd(and_all);
        println!("Compressed size: {}", buffer.len());

        let mut another_manager = Ruddy::init(NODE_SIZE, CACHE_SIZE, VAR_NUM);
        let mut decoder = flate2::read::DeflateDecoder::new(&buffer[..]);
        let another_and_all = BddIO::<
            flate2::write::DeflateEncoder<Vec<u8>>,
            flate2::read::DeflateDecoder<&[u8]>,
        >::deserialize(&mut another_manager, &mut decoder)
        .unwrap();

        // print to stdout to make sure the BDD is correct
        // let mut stdout = std::io::stdout();
        // another_manager.print(another_and_all, &mut stdout).unwrap();

        another_manager.deref_bdd(another_and_all);
    }

    #[test]
    fn test_ruddy_io_uncompressed() {
        const NODE_SIZE: u32 = 100;
        const CACHE_SIZE: u32 = 10;
        const VAR_NUM: u32 = 32;

        let mut manager = Ruddy::init(NODE_SIZE, CACHE_SIZE, VAR_NUM);
        let mut and_all: Bdd = manager.get_true();
        let mut tmp: Bdd;
        for i in 0..VAR_NUM {
            let var = manager.get_var(i as u16);
            tmp = manager.and(and_all, var);
            manager.ref_bdd(tmp);
            manager.deref_bdd(and_all);
            and_all = tmp;
        }

        let mut buffer = Vec::new();
        BddIO::<Vec<u8>, &[u8]>::serialize(&manager, and_all, &mut buffer).unwrap();
        manager.deref_bdd(and_all);
        println!("Uncompressed size: {}", buffer.len());

        let mut another_manager = Ruddy::init(NODE_SIZE, CACHE_SIZE, VAR_NUM);
        let another_and_all =
            BddIO::<Vec<u8>, &[u8]>::deserialize(&mut another_manager, &mut &buffer[..]).unwrap();

        // print to stdout to make sure the BDD is correct
        // let mut stdout = std::io::stdout();
        // another_manager.print(another_and_all, &mut stdout).unwrap();

        another_manager.deref_bdd(another_and_all);
    }

    #[test]
    fn test_ruddy_print_set() {
        const NODE_SIZE: u32 = 10;

        let mut manager = Ruddy::init(NODE_SIZE, NODE_SIZE, 3);
        let a = manager.get_var(0);
        let b = manager.get_var(1);
        let c = manager.get_var(2);

        let ab = manager.and(a, b);
        manager.ref_bdd(ab);
        let bc = manager.and(b, c);
        manager.ref_bdd(bc);
        let abc = manager.or(ab, bc);
        manager.ref_bdd(abc);

        let mut buf = Vec::new();

        PrintSet::print(&manager, manager.get_true(), &mut buf).unwrap();
        assert_eq!(from_utf8(&buf).unwrap(), "TRUE\n");
        buf.clear();
        PrintSet::print(&manager, manager.get_false(), &mut buf).unwrap();
        assert_eq!(from_utf8(&buf).unwrap(), "FALSE\n");
        buf.clear();
        PrintSet::print(&manager, abc, &mut buf).unwrap();
        assert_eq!(from_utf8(&buf).unwrap(), "011\n11*\n");

        manager.deref_bdd(ab);
        manager.deref_bdd(bc);
        manager.deref_bdd(abc);
    }

    #[test]
    fn test_ruddy_exist() {
        const NODE_SIZE: u32 = 10;

        let mut manager = Ruddy::init(NODE_SIZE, NODE_SIZE, 3);
        let a = manager.get_var(0);
        let b = manager.get_var(1);
        let c = manager.get_var(2);

        let ab = manager.and(a, b);
        manager.ref_bdd(ab);
        let bc = manager.and(b, c);
        manager.ref_bdd(bc);
        let abc = manager.or(ab, bc);
        manager.ref_bdd(abc);

        let mut buf = Vec::new();

        let exist_a = manager.exist(abc, a);
        PrintSet::print(&manager, exist_a, &mut buf).unwrap();
        assert_eq!(from_utf8(&buf).unwrap(), "*1*\n");
        buf.clear();

        let exist_ab = manager.exist(abc, ab);
        PrintSet::print(&manager, exist_ab, &mut buf).unwrap();
        assert_eq!(from_utf8(&buf).unwrap(), "TRUE\n");
        buf.clear();

        let exist_b = manager.exist(abc, b);
        PrintSet::print(&manager, exist_b, &mut buf).unwrap();
        assert_eq!(from_utf8(&buf).unwrap(), "0*1\n1**\n");
        buf.clear();

        manager.deref_bdd(ab);
        manager.deref_bdd(bc);
        manager.deref_bdd(abc);
    }

    #[test]
    fn test_ruddy_forall() {
        const NODE_SIZE: u32 = 10;

        let mut manager = Ruddy::init(NODE_SIZE, NODE_SIZE, 3);
        let a = manager.get_var(0);
        let b = manager.get_var(1);
        let c = manager.get_var(2);

        let ab = manager.or(a, b);
        manager.ref_bdd(ab);
        let bc = manager.or(b, c);
        manager.ref_bdd(bc);
        let abc = manager.and(ab, bc);
        manager.ref_bdd(abc);

        let mut buf = Vec::new();

        PrintSet::print(&manager, ab, &mut buf).unwrap();
        assert_eq!(from_utf8(&buf).unwrap(), "01*\n1**\n");
        buf.clear();

        let forall_a = manager.forall(ab, a);
        PrintSet::print(&manager, forall_a, &mut buf).unwrap();
        assert_eq!(from_utf8(&buf).unwrap(), "*1*\n");
        buf.clear();

        let forall_c = manager.forall(ab, c);
        PrintSet::print(&manager, forall_c, &mut buf).unwrap();
        assert_eq!(from_utf8(&buf).unwrap(), "01*\n1**\n");
        buf.clear();

        manager.deref_bdd(ab);
        manager.deref_bdd(bc);
        manager.deref_bdd(abc);
    }
}
