use crate::{
    hash::hash_2,
    prime::prime_lte,
    {Bdd, BddOpType},
};

#[cfg(feature = "cache_stat")]
use std::fmt::Display;

#[derive(Clone, Copy)]
struct Unary(Bdd, Bdd);

#[derive(Clone, Copy)]
struct Binary(Bdd, Bdd, Bdd);

pub trait Growable {
    fn grow(&mut self, new_size: u32);
    fn invalidate_all(&mut self);
}

#[allow(dead_code)]
pub struct UnaryCache {
    pub op: BddOpType,
    pub table_size: u32,
    table: Vec<Option<Unary>>,

    #[cfg(feature = "cache_stat")]
    pub stat: CacheStat,
}

#[allow(dead_code)]
pub struct BinaryCache {
    pub op: BddOpType,
    pub table_size: u32,
    pub last_hash: usize,
    table: Vec<Option<Binary>>,

    #[cfg(feature = "cache_stat")]
    pub stat: CacheStat,
}

impl UnaryCache {
    pub fn new(op: BddOpType, table_size: u32) -> Self {
        let actual_size = prime_lte(table_size);
        let mut table = Vec::with_capacity(actual_size as usize);
        for _ in 0..actual_size {
            table.push(None);
        }
        match op {
            BddOpType::Not => Self {
                op,
                table_size: actual_size,
                table,
                #[cfg(feature = "cache_stat")]
                stat: CacheStat::default(),
            },
            _ => panic!("Invalid unary operation"),
        }
    }

    #[inline]
    pub fn get(&mut self, key: Bdd) -> Option<Bdd> {
        let entry = &mut self.table[key as usize % self.table_size as usize];
        if let Some(unary) = entry {
            if unary.0 == key {
                #[cfg(feature = "cache_stat")]
                {
                    self.stat.last_hit += 1;
                }
                return Some(unary.1);
            }
        }
        #[cfg(feature = "cache_stat")]
        {
            self.stat.last_miss += 1;
        }
        None
    }

    #[inline]
    pub fn put(&mut self, key: Bdd, value: Bdd) {
        let entry = &mut self.table[key as usize % self.table_size as usize];
        *entry = Some(Unary(key, value));
    }
}

impl Growable for UnaryCache {
    fn grow(&mut self, new_size: u32) {
        let table_size = prime_lte(new_size);
        let mut table = Vec::with_capacity(table_size as usize);
        for i in 0..self.table_size {
            table.push(self.table[i as usize]);
        }
        for _ in self.table_size..table_size {
            table.push(None);
        }
        self.table = table;
        self.table_size = table_size;
        #[cfg(feature = "cache_stat")]
        {
            self.stat.grow_cnt += 1;
            self.stat.unique_hit += self.stat.last_hit;
            self.stat.unique_miss += self.stat.last_miss;
            self.stat.last_hit = 0;
            self.stat.last_miss = 0;
        }
    }

    fn invalidate_all(&mut self) {
        for i in 0..self.table_size {
            self.table[i as usize] = None;
        }
        #[cfg(feature = "cache_stat")]
        {
            self.stat.clear_cnt += 1;
        }
    }
}

impl BinaryCache {
    pub fn new(op: BddOpType, table_size: u32) -> Self {
        let actual_size = prime_lte(table_size);
        let mut table = Vec::with_capacity(actual_size as usize);
        for _ in 0..actual_size {
            table.push(None);
        }
        match op {
            BddOpType::And
            | BddOpType::Or
            | BddOpType::Comp
            | BddOpType::QuantExist
            | BddOpType::QuantForall => Self {
                op,
                table_size: actual_size,
                last_hash: 0,
                table,
                #[cfg(feature = "cache_stat")]
                stat: CacheStat::default(),
            },
            _ => panic!("Invalid binary operation"),
        }
    }

    #[inline]
    pub fn get(&mut self, key: (Bdd, Bdd)) -> Option<Bdd> {
        let (l, r) = if key.0 <= key.1 {
            (key.0, key.1)
        } else {
            (key.1, key.0)
        };
        self.last_hash = hash_2!(l, r) as usize;
        let entry = &mut self.table[self.last_hash % self.table_size as usize];
        if let Some(binary) = entry {
            if binary.0 == key.0 && binary.1 == key.1 {
                #[cfg(feature = "cache_stat")]
                {
                    self.stat.last_hit += 1;
                }
                return Some(binary.2);
            }
        }
        #[cfg(feature = "cache_stat")]
        {
            self.stat.last_miss += 1;
        }
        None
    }

    #[inline]
    pub fn put(&mut self, hash: usize, key: (Bdd, Bdd), value: Bdd) {
        let (l, r) = if key.0 <= key.1 {
            (key.0, key.1)
        } else {
            (key.1, key.0)
        };
        let entry = &mut self.table[hash % self.table_size as usize];
        *entry = Some(Binary(l, r, value));
    }
}

impl Growable for BinaryCache {
    fn grow(&mut self, new_size: u32) {
        let table_size = prime_lte(new_size);
        let mut table = Vec::with_capacity(table_size as usize);
        for i in 0..self.table_size {
            table.push(self.table[i as usize]);
        }
        for _ in self.table_size..table_size {
            table.push(None);
        }
        self.table = table;
        self.table_size = table_size;
        #[cfg(feature = "cache_stat")]
        {
            self.stat.grow_cnt += 1;
            self.stat.unique_hit += self.stat.last_hit;
            self.stat.unique_miss += self.stat.last_miss;
            self.stat.last_hit = 0;
            self.stat.last_miss = 0;
        }
    }

    fn invalidate_all(&mut self) {
        for i in 0..self.table_size {
            self.table[i as usize] = None;
        }
        #[cfg(feature = "cache_stat")]
        {
            self.stat.clear_cnt += 1;
        }
    }
}

#[cfg(feature = "cache_stat")]
#[derive(Default)]
pub struct CacheStat {
    pub clear_cnt: usize,
    pub grow_cnt: usize,
    pub last_hit: usize, // hit count since last grow
    pub last_miss: usize,
    pub unique_hit: usize, // total hit count
    pub unique_miss: usize,
}

#[cfg(feature = "cache_stat")]
impl Display for CacheStat {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(
            f,
            "unique_hit: {}, unique_miss: {}",
            self.unique_hit, self.unique_miss
        )
    }
}
