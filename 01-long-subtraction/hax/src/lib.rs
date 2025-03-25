/// A 256 bits integer represented with four words
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct LargeInt([u64; 4]);

/// Helper function that implements a borrowing subtraction on u64
fn borrowing_sub_u64(lhs: u64, rhs: u64, borrow: bool) -> (u64, bool) {
    let (res, borrow1) = lhs.overflowing_sub(rhs);
    let (res, borrow2) = res.overflowing_sub(borrow as u64);
    (res, borrow1 || borrow2)
}

#[cfg(hax)]
use hax_lib::{int, Int, ToInt};

#[cfg(hax)]
/// Specifications using hax' math integer type `Int`
mod spec {
    use super::*;

    #[hax_lib::attributes]
    impl LargeInt {
        /// Interprets a large int as a mathematical integer
        pub fn to_int(&self) -> Int {
            self.0[0].to_int()
                + self.0[1].to_int() * Int::pow2(int!(64) * int!(1))
                + self.0[2].to_int() * Int::pow2(int!(64) * int!(2))
                + self.0[3].to_int() * Int::pow2(int!(64) * int!(3))
        }

        /// Transforms a mathematical integer into a large int
        #[hax_lib::requires(x >= int!(0) && x < Int::pow2(int!(64) * int!(4)))]
        pub fn from_int(x: Int) -> Self {
            hax_lib::fstar!("FStar.Math.Lemmas.pow2_plus 64 64");
            hax_lib::fstar!("FStar.Math.Lemmas.pow2_plus (64 + 64) 64");
            hax_lib::fstar!("FStar.Math.Lemmas.pow2_plus (64 + 64 + 64) 64");
            let m = int!(64).pow2();
            let a = x.rem_euclid(m).to_u64();
            let x = x / m;
            let b = x.rem_euclid(m).to_u64();
            let x = x / m;
            let c = x.rem_euclid(m).to_u64();
            let x = x / m;
            Self([a, b, c, x.to_u64()])
        }
    }

    pub fn borrowing_sub_int(lhs: Int, rhs: Int, borrow: bool) -> (Int, bool) {
        let sub = lhs - rhs - (borrow as u8).to_int();
        if sub < int!(0) {
            (Int::pow2(int!(256)) + sub, true)
        } else {
            (sub, false)
        }
    }
}

#[hax_lib::attributes]
impl LargeInt {
    #[cfg(test)]
    fn random() -> Self {
        Self(std::array::from_fn(|_| rand::random()))
    }

    /// In-place borrowing subtraction on large integers
    #[hax_lib::ensures(|out_borrow| {
        use hax_lib::{int, Int, ToInt};
        (future(self).to_int(), out_borrow) == spec::borrowing_sub_int(self.to_int(), rhs.to_int(), out_borrow)
    })]
    pub fn borrowing_sub(&mut self, rhs: Self, borrow: bool) -> bool {
        let (a, borrow) = borrowing_sub_u64(self.0[0], rhs.0[0], borrow);
        let (b, borrow) = borrowing_sub_u64(self.0[1], rhs.0[1], borrow);
        let (c, borrow) = borrowing_sub_u64(self.0[2], rhs.0[2], borrow);
        let (d, borrow) = borrowing_sub_u64(self.0[3], rhs.0[3], borrow);
        self.0[0] = a;
        self.0[1] = b;
        self.0[2] = c;
        self.0[3] = d;
        borrow
    }
}

#[cfg(all(test, hax))]
mod tests {
    use super::*;
    fn lifts() {
        for _ in 0..1000 {
            let x = LargeInt::random();
            let y = LargeInt::from_int(x.to_int());
            assert_eq!(x, y);
        }
    }

    fn sub() {
        for _ in 0..1000 {
            let x = LargeInt::random();
            let y = LargeInt::random();
            let borrow0 = rand::random();
            let mut z = x.clone();
            let borrow1 = z.borrowing_sub(y, borrow0);
            assert_eq!(
                (z.to_int(), borrow1),
                spec::borrowing_sub_int(x.to_int(), y.to_int(), borrow0)
            )
        }
    }
}
