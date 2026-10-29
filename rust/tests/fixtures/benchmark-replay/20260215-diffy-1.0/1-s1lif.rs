
use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] == 2 * N,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            a.len() == N as usize,
            forall |k: int| 0 <= k < i ==> a[k] == 1,
            forall |k: int| i <= k < N as usize ==> old(a)[k] == a[k],
            N > 0,
            N < 1000,
            decreases(N - i),
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            a.len() == N as usize,
            forall |k: int| 0 <= k < i ==> a[k] == 2,
            forall |k: int| i <= k < N as usize ==> a[k] == 1,
            N > 0,
            N < 1000,
            decreases(N - i),
    {
        if (a[i] == 1) {
            a.set(i, a[i] + 1);
        } else {
            a.set(i, a[i] - 1);
        }
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            a.len() == N as usize,
            sum.len() == 1,
            sum[0] == 2 * i,
            forall |k: int| 0 <= k < N as usize ==> a[k] == 2,
            N > 0,
            N < 1000,
            decreases(N - i),
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
}
}

// Score: Compilation Error: False, Verified: 4, Errors: 0, Verus Errors: 0
// Safe: True