use crate::bdd::ruddy::Ruddy;
use crate::bdd::{Bdd, BddOp, BddOpType, _Bdd};
#[cfg(feature = "op_stat")]
use std::time::UNIX_EPOCH;

impl Ruddy {
    #[inline]
    fn level(&self, _bdd: _Bdd) -> u32 {
        self.nodes[_bdd].level
    }

    #[inline]
    fn low(&self, _bdd: _Bdd) -> _Bdd {
        self.nodes[_bdd].low
    }

    #[inline]
    fn high(&self, _bdd: _Bdd) -> _Bdd {
        self.nodes[_bdd].high
    }
}

impl Ruddy {
    fn _not_rec(&mut self, _bdd: _Bdd) -> _Bdd {
        if _bdd <= Self::_TRUE_BDD {
            return _bdd ^ 1;
        }
        if let Some(_bdd) = self.not_cache.get(_bdd) {
            return _bdd;
        }
        let f_low = self._not_rec(self.low(_bdd));
        self.m_stack.push(f_low);
        let f_high = self._not_rec(self.high(_bdd));
        self.m_stack.push(f_high);
        let res = self.make_node(
            self.level(_bdd),
            self.m_stack[self.m_stack.len() - 2],
            self.m_stack[self.m_stack.len() - 1],
        );
        unsafe {
            self.m_stack.set_len(self.m_stack.len() - 2);
        }
        self.not_cache.put(_bdd, res);
        return res;
    }

    fn _apply_rec(&mut self, lhs: _Bdd, rhs: _Bdd, op: BddOpType) -> _Bdd {
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

        match op {
            BddOpType::And => {
                if lhs == rhs || rhs == Self::_TRUE_BDD {
                    return lhs;
                }
                if lhs == Self::_FALSE_BDD || rhs == Self::_FALSE_BDD {
                    return Self::_FALSE_BDD;
                }
                if lhs == Self::_TRUE_BDD {
                    return rhs;
                }
                if let Some(_bdd) = self.and_cache.get((lhs, rhs)) {
                    return _bdd;
                }
            }
            BddOpType::Or => {
                if lhs == rhs || rhs == Self::_FALSE_BDD {
                    return lhs;
                }
                if lhs == Self::_TRUE_BDD || rhs == Self::_TRUE_BDD {
                    return Self::_TRUE_BDD;
                }
                if lhs == Self::_FALSE_BDD {
                    return rhs;
                }
                if let Some(_bdd) = self.or_cache.get((lhs, rhs)) {
                    return _bdd;
                }
            }
            // lhs \ rhs
            BddOpType::Comp => {
                if lhs == rhs || lhs == Self::_FALSE_BDD || rhs == Self::_TRUE_BDD {
                    return Self::_FALSE_BDD;
                }
                if rhs == Self::_FALSE_BDD {
                    return lhs;
                }
                if lhs == Self::_TRUE_BDD {
                    return self._not_rec(rhs);
                }
                if let Some(_bdd) = self.comp_cache.get((lhs, rhs)) {
                    return _bdd;
                }
            }
            _ => {
                panic!("Not supported")
            }
        }
        if level!(lhs) == level!(rhs) {
            let f_low = self._apply_rec(low!(lhs), low!(rhs), op);
            self.m_stack.push(f_low);
            let f_high = self._apply_rec(high!(lhs), high!(rhs), op);
            self.m_stack.push(f_high);
        } else if level!(lhs) < level!(rhs) {
            let f_low = self._apply_rec(low!(lhs), rhs, op);
            self.m_stack.push(f_low);
            let f_high = self._apply_rec(high!(lhs), rhs, op);
            self.m_stack.push(f_high);
        } else {
            let f_low = self._apply_rec(lhs, low!(rhs), op);
            self.m_stack.push(f_low);
            let f_high = self._apply_rec(lhs, high!(rhs), op);
            self.m_stack.push(f_high);
        };
        let res = self.make_node(
            std::cmp::min(level!(lhs), level!(rhs)),
            self.m_stack[self.m_stack.len() - 2],
            self.m_stack[self.m_stack.len() - 1],
        );
        unsafe {
            self.m_stack.set_len(self.m_stack.len() - 2);
        }
        match op {
            BddOpType::And => self.and_cache.put((lhs, rhs), res),
            BddOpType::Or => self.or_cache.put((lhs, rhs), res),
            BddOpType::Comp => self.comp_cache.put((lhs, rhs), res),
            _ => {
                panic!("Not supported")
            }
        }
        return res;
    }
}

impl BddOp for Ruddy {
    #[inline]
    fn not(&mut self, bdd: &Bdd) -> Bdd {
        #[cfg(feature = "op_stat")]
        {
            self.op_stat.not_cnt += 1;
            self.op_stat.not_time -= UNIX_EPOCH.elapsed().unwrap().as_micros();
        }
        let ret = Bdd(self._not_rec(bdd.0));
        #[cfg(feature = "op_stat")]
        {
            self.op_stat.not_time += UNIX_EPOCH.elapsed().unwrap().as_micros();
        }
        ret
    }

    #[inline]
    fn and(&mut self, lhs: &Bdd, rhs: &Bdd) -> Bdd {
        #[cfg(feature = "op_stat")]
        {
            self.op_stat.and_cnt += 1;
            self.op_stat.and_time -= UNIX_EPOCH.elapsed().unwrap().as_micros();
        }
        let ret = Bdd(self._apply_rec(lhs.0, rhs.0, BddOpType::And));
        #[cfg(feature = "op_stat")]
        {
            self.op_stat.and_time += UNIX_EPOCH.elapsed().unwrap().as_micros();
        }
        ret
    }

    #[inline]
    fn or(&mut self, lhs: &Bdd, rhs: &Bdd) -> Bdd {
        #[cfg(feature = "op_stat")]
        {
            self.op_stat.or_cnt += 1;
            self.op_stat.or_time -= UNIX_EPOCH.elapsed().unwrap().as_micros();
        }
        let ret = Bdd(self._apply_rec(lhs.0, rhs.0, BddOpType::Or));
        #[cfg(feature = "op_stat")]
        {
            self.op_stat.or_time += UNIX_EPOCH.elapsed().unwrap().as_micros();
        }
        ret
    }

    #[inline]
    fn comp(&mut self, lhs: &Bdd, rhs: &Bdd) -> Bdd {
        #[cfg(feature = "op_stat")]
        {
            self.op_stat.comp_cnt += 1;
            self.op_stat.comp_time -= UNIX_EPOCH.elapsed().unwrap().as_micros();
        }
        let ret = Bdd(self._apply_rec(lhs.0, rhs.0, BddOpType::Comp));
        #[cfg(feature = "op_stat")]
        {
            self.op_stat.comp_time += UNIX_EPOCH.elapsed().unwrap().as_micros();
        }
        ret
    }
}
