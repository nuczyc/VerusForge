
use vstd::prelude::*;
fn main() {}
verus!{
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(b).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        forall |k:int| 0 <= k < N ==> a[k] == 2 * N + 1,
{
    let mut i: usize = 0;
    sum.set(0, 0);

    while (i < N as usize)
        invariant
            i as int <= N,
            sum.len() == 1,
            a.len() == N as usize,
            b.len() == N as usize,
            forall |k: int| 0 <= k < i ==> a[k] == 1,
            forall |k: int| i <= k < N ==> old(a)[k] == a[k],
            N > 0,
            N < 1000,
            decreases(N as int - i as int)
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i as int <= N,
            sum.len() == 1,
            a.len() == N as usize,
            b.len() == N as usize,
            forall |k: int| 0 <= k < i ==> b[k] == 1,
            forall |k: int| i <= k < N ==> old(b)[k] == b[k],
            N > 0,
            N < 1000,
            decreases(N as int - i as int)
    {
        b.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i as int <= N,
            sum.len() == 1,
            a.len() == N as usize,
            b.len() == N as usize,
            sum[0] == i as int,
            forall |k: int| 0 <= k < N ==> a[k] == 1,
            forall |k: int| 0 <= k < N ==> b[k] == 1,
            N > 0,
            N < 1000,
            decreases(N as int - i as int)
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i as int <= N,
            sum.len() == 1,
            a.len() == N as usize,
            b.len() == N as usize,
            sum[0] == N as int + i as int,
            forall |k: int| 0 <= k < N ==> a[k] == 1,
            forall |k: int| 0 <= k < N ==> b[k] == 1,
            N > 0,
            N < 1000,
            decreases(N as int - i as int)
    {
        sum.set(0, sum[0] + b[i]);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            i as int <= N,
            sum.len() == 1,
            a.len() == N as usize,
            b.len() == N as usize,
            sum[0] == 2 * N as int,
            forall |k: int| 0 <= k < i ==> a[k] == 2 * N as int + 1,
            forall |k: int| i <= k < N ==> a[k] == 1,
            N > 0,
            N < 1000,
            decreases(N as int - i as int)
    {
        a.set(i, a[i] + sum[0]);
        i = i + 1;
    }
}
}

// Score: Compilation Error: False, Verified: 6, Errors: 0, Verus Errors: 0
// Safe: True