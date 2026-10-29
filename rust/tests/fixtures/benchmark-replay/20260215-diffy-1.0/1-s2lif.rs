
use vstd::prelude::*;
fn main() {}
verus! {

#[verifier::loop_isolation(false)]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] == 3 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
        decreases N as usize - i,
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            a.len() == N,
        decreases N as usize - i,
    {
        if (a[i] == 1) {
            a.set(i, a[i] + 2);
        } else {
            assert(a[( i ) as int] > 0); // Ensure no underflow
            a.set(i, a[i] - 1);
        }
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            sum.len() == 1,
            a.len() == N,
            forall |k: int| 0 <= k < a.len() ==> a[k] == 3,
        decreases N as usize - i,
    {
        assert(sum[0] + a[( i ) as int] <= 3 * N); // Ensure no overflow
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
}
}


// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 2
// Safe: True