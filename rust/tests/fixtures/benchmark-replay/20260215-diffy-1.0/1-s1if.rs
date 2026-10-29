
use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
    ensures
        sum[0] == N,
{
    let mut i: usize = 0;
    sum.set(0, 0);

    while (i < N as usize)
    invariant
        // Preconditions
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,

        // Loop invariants
        0 <= i <= N as usize,
        a.len() == N as usize,
        sum.len() == 1,
        forall |k: int| 0 <= k < i ==> a[k] == 1,
        forall |k: int| i <= k < N as usize ==> old(a)[k] == a[k],
    decreases(N as usize - i)
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
    invariant
        // Preconditions
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,

        // Loop invariants
        0 <= i <= N as usize,
        a.len() == N as usize,
        sum.len() == 1,
        forall |k: int| 0 <= k < N as usize ==> a[k] == 1,
        sum[0] == i, // Since all a[k] are 1, adding them results in incrementing sum by 1 each time
    decreases(N as usize - i)
    {
        if (a[i] == 1) {
            sum.set(0, sum[0] + a[i]);
        } else {
            sum.set(0, sum[0] * a[i]);
        }
        i = i + 1;
    }
}
}

// Score: Compilation Error: False, Verified: 3, Errors: 0, Verus Errors: 0
// Safe: True