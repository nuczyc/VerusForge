
use vstd::prelude::*;
fn main() {}

verus!{

#[verifier::loop_isolation(false)]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
    ensures
        sum[0] <= N,
{
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            // Invariants for array `a`
            forall |k: int| 0 <= k < i ==> 
                if k % 1 == 0 { a[k as int] == 1 } else { a[k as int] == 0 },
            forall |k: int| i <= k < N ==> old(a)[k as int] == a[k as int],
            a.len() == N as usize,

            // Invariants for variable `i`
            i <= N as usize,
            N > 0,
            decreases(N - i as int),
    {
        if (i % 1 == 0) {
            a.set(i, 1);
        } else {
            a.set(i, 0);
        }
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            // Invariants for sum
            sum.len() == 1,
            i > 0 ==> 0 <= sum[0] <= i as i32,
            // The array `a` is not modified in this loop
            a.len() == N as usize,

            // Invariants for variable `i`
            i <= N as usize,
            N > 0,
            decreases(N - i as int),
    {
        if (i == 0) {
            sum.set(0, 0);
        } else {
            sum.set(0, sum[0] + a[i]);
        }
        i = i + 1;
    }
}
}


// Score: Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: True