use crate::bdd::{BddOpType, _Bdd};
use crate::hash::hash_2;
use crate::prime::prime_lte;
#[cfg(feature = "cache_stat")]
use std::fmt::Display;

#[derive(Clone, Copy)]
struct Unary(_Bdd, _Bdd);
#[derive(Clone, Copy)]
struct Binary(_Bdd, _Bdd, _Bdd);

pub trait Growable {
    fn grow(&mut self, new_size: u32);
    fn invalidate_all(&mut self);
}

#[allow(dead_code)]
pub struct UnaryCache {
    pub op: BddOpType,
    #[cfg(feature = "cache_stat")]
    pub stat: CacheStat,
    table: Vec<Option<Unary>>,
    pub table_size: u32,
}

#[allow(dead_code)]
pub struct BinaryCache {
    pub op: BddOpType,
    #[cfg(feature = "cache_stat")]
    pub stat: CacheStat,
    table: Vec<Option<Binary>>,
    pub table_size: u32,
}

impl UnaryCache {
    pub fn new(op: BddOpType) -> Self {
        match op {
            BddOpType::Not => Self {
                op,
                #[cfg(feature = "cache_stat")]
                stat: CacheStat::default(),
                table: Vec::new(),
                table_size: 0,
            },
            _ => panic!("Invalid unary operation"),
        }
    }

    pub fn init(&mut self, table_size: u32) {
        let table_size = prime_lte(table_size);
        let mut table = Vec::with_capacity(table_size as usize);
        for _ in 0..table_size {
            table.push(None);
        }
        self.table = table;
        self.table_size = table_size;
    }

    #[inline]
    pub fn get(&mut self, key: _Bdd) -> Option<_Bdd> {
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
        return None;
    }

    #[inline]
    pub fn put(&mut self, key: _Bdd, value: _Bdd) {
        let entry = &mut self.table[key as usize % self.table_size as usize];
        *entry = Some(Unary(key, value));
    }
}

impl Growable for UnaryCache {
    fn grow(&mut self, new_size: u32) {
        let table_size = prime_lte(new_size);
        let mut table = Vec::with_capacity(table_size as usize);
        for i in 0..self.table_size {
            table.push(self.table[i as usize].clone());
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
    pub fn new(op: BddOpType) -> Self {
        match op {
            BddOpType::And | BddOpType::Or | BddOpType::Comp => Self {
                op,
                #[cfg(feature = "cache_stat")]
                stat: CacheStat::default(),
                table: Vec::new(),
                table_size: 0,
            },
            _ => panic!("Invalid binary operation"),
        }
    }

    pub fn init(&mut self, table_size: u32) {
        let table_size = prime_lte(table_size);
        let mut table = Vec::with_capacity(table_size as usize);
        for _ in 0..table_size {
            table.push(None);
        }
        self.table = table;
        self.table_size = table_size;
    }

    #[inline]
    pub fn get(&mut self, key: (_Bdd, _Bdd)) -> Option<_Bdd> {
        let (l, r) = if key.0 <= key.1 {
            (key.0, key.1)
        } else {
            (key.1, key.0)
        };
        let entry = &mut self.table[hash_2!(l, r) as usize % self.table_size as usize];
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
        return None;
    }

    #[inline]
    pub fn put(&mut self, key: (_Bdd, _Bdd), value: _Bdd) {
        let (l, r) = if key.0 <= key.1 {
            (key.0, key.1)
        } else {
            (key.1, key.0)
        };
        let entry = &mut self.table[hash_2!(l, r) as usize % self.table_size as usize];
        *entry = Some(Binary(l, r, value));
    }
}

impl Growable for BinaryCache {
    fn grow(&mut self, new_size: u32) {
        let table_size = prime_lte(new_size);
        let mut table = Vec::with_capacity(table_size as usize);
        for i in 0..self.table_size {
            table.push(self.table[i as usize].clone());
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
