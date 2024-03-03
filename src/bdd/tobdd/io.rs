use crate::bdd::{BddIO, BddManager, PrintSet, _Bdd};
use crate::{Bdd, Tobdd};
use std::collections::HashMap;
use std::fmt::Write as FmtWrite;
use std::io::Write as IoWrite;

impl BddIO for Tobdd {
    #[allow(unused_assignments)]
    fn read_buffer(&mut self, buffer: &Vec<u8>) -> Option<Bdd> {
        let mut map: HashMap<_Bdd, _Bdd> = HashMap::with_capacity(3 * buffer.len() / 2 / 16);
        map.insert(0, 0);
        map.insert(1, 1);
        let mut dst = [0u8; 4];
        let (mut bdd, mut level, mut low, mut high, mut ret) = (0u32, 0u32, 0u32, 0u32, 0u32);
        // merge 4 u8 into 1 u32
        for i in (0..buffer.len()).step_by(16) {
            dst.copy_from_slice(&buffer[i..i + 4]);
            bdd = u32::from_le_bytes(dst);
            dst.copy_from_slice(&buffer[i + 4..i + 8]);
            level = u32::from_le_bytes(dst);
            assert!(
                level <= self.var_num,
                "Read Error: local manager does not have Var {level}"
            );
            dst.copy_from_slice(&buffer[i + 8..i + 12]);
            low = u32::from_le_bytes(dst);
            dst.copy_from_slice(&buffer[i + 12..i + 16]);
            high = u32::from_le_bytes(dst);

            low = *map.get(&low).unwrap();
            high = *map.get(&high).unwrap();
            ret = self.make_node(level, low, high);
            map.insert(bdd, self.ref_bdd(Bdd(ret)).0);
        }
        for b in map.values() {
            self.deref_bdd(Bdd(*b));
        }
        return Some(Bdd(ret));
    }

    fn write_buffer(&self, bdd: &Bdd, buffer: &mut Vec<u8>) -> Option<usize> {
        fn write_buffer_rec(tobdd: &Tobdd, bdd: &Bdd, buffer: &mut Vec<u8>) {
            if bdd.0 > Tobdd::_TRUE_BDD {
                // low, high, level traversal
                write_buffer_rec(tobdd, &Bdd(tobdd.nodes[bdd.0].low), buffer);
                write_buffer_rec(tobdd, &Bdd(tobdd.nodes[bdd.0].high), buffer);
                // split u32 into 4 u8
                buffer.write_all(&bdd.0.to_le_bytes()).unwrap();
                buffer
                    .write_all(&tobdd.nodes[bdd.0].level.to_le_bytes())
                    .unwrap();
                buffer
                    .write_all(&tobdd.nodes[bdd.0].low.to_le_bytes())
                    .unwrap();
                buffer
                    .write_all(&tobdd.nodes[bdd.0].high.to_le_bytes())
                    .unwrap();
            }
        }

        let bef = buffer.len();
        write_buffer_rec(self, bdd, buffer);
        let aft = buffer.len();
        return if aft > bef { Some(aft - bef) } else { None };
    }
}

impl PrintSet for Tobdd {
    fn fmt(&self, f: &mut String, bdd: &Bdd) -> std::fmt::Result {
        fn fmt_rec(
            tobdd: &Tobdd,
            f: &mut String,
            chars: &mut Vec<char>,
            _bdd: _Bdd,
            curr: u32,
        ) -> std::fmt::Result {
            if curr == tobdd.var_num {
                for i in 0..tobdd.var_num as usize {
                    f.write_char(chars[i])?;
                }
                f.write_str("\n")?;
                return Ok(());
            }
            let level = tobdd.nodes[_bdd].level;
            if level > curr || _bdd == 1 {
                chars[curr as usize] = '-';
                fmt_rec(tobdd, f, chars, _bdd, curr + 1)?;
                return Ok(());
            }
            let low = tobdd.nodes[_bdd].low;
            let high = tobdd.nodes[_bdd].high;
            if low != 0 {
                chars[curr as usize] = '0';
                fmt_rec(tobdd, f, chars, low, curr + 1)?;
            }
            if high != 0 {
                chars[curr as usize] = '1';
                fmt_rec(tobdd, f, chars, high, curr + 1)?;
            }
            Ok(())
        }

        if bdd.0 <= Self::_TRUE_BDD {
            f.write_fmt(format_args!(
                "{}\n",
                if bdd.0 == 0 { "FALSE" } else { "TRUE" }
            ))?;
        } else {
            let mut set_chars: Vec<char> = vec![0 as char; self.var_num as usize];
            fmt_rec(self, f, &mut set_chars, bdd.0, 0)?;
        }
        Ok(())
    }
}
