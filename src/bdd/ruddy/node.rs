use crate::Ruddy;
use std::ops::{Index, IndexMut};

// NOTE: 8 x u64 = 64 bytes, making a cache line
// Why don't put the NodeStatic, NodeRef, and NodeLink in the same struct?
//     - The NodeStatic contains fields that seldom change, CPU can cache and hit the fields.
//     - To minimize the memory, use AtomicU16 to store the reference count is enough. If the
//       ref_cnt is moved to NodeLink, it doesn't comply with the struct alignment.
#[derive(Debug, Copy, Clone)]
pub struct NodeStatic {
    pub level: u32,
    pub low: u32,
    pub high: u32,
}

impl Default for NodeStatic {
    #[inline]
    fn default() -> Self {
        NodeStatic {
            level: Ruddy::INVALID_LEVEL,
            low: Ruddy::LIST_END_NODE,
            high: Ruddy::LIST_END_NODE,
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct NodeRef {
    pub ref_cnt: u16,
}

impl Default for NodeRef {
    #[inline]
    fn default() -> Self {
        NodeRef {
            ref_cnt: Ruddy::MIN_REF_CNT,
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub struct NodeLink {
    // If a node is occupied, next points to the node with the same hash value.
    // If a node is free, next points to the next free node.
    pub next: u32,
    // hash points to the hash bucket.
    pub hash: u32,
}

impl Default for NodeLink {
    #[inline]
    fn default() -> Self {
        NodeLink {
            next: Ruddy::LIST_END_NODE,
            hash: Ruddy::LIST_END_NODE,
        }
    }
}

/// u32-indexed Vec
pub struct Vec32<T> {
    pub data: Vec<T>,
}

impl<T> Vec32<T> {
    #[inline]
    pub fn new() -> Self {
        Vec32 { data: Vec::new() }
    }

    #[inline]
    pub fn with_capacity(size: u32) -> Self {
        Vec32 {
            data: Vec::with_capacity(size as usize),
        }
    }

    #[inline]
    pub fn push(&mut self, value: T) {
        self.data.push(value);
    }
}

impl<T> Index<u32> for Vec32<T> {
    type Output = T;

    #[inline]
    fn index(&self, index: u32) -> &Self::Output {
        &self.data[index as usize]
    }
}

impl<T> IndexMut<u32> for Vec32<T> {
    #[inline]
    fn index_mut(&mut self, index: u32) -> &mut Self::Output {
        &mut self.data[index as usize]
    }
}
