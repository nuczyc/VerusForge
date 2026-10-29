
use vstd::prelude::*;
fn main() {}
verus!{

#[verifier::loop_isolation(false)]
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(b).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        forall |k:int| 0 <= k < N ==> a[k] == N + 1,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N as usize)
    invariant
        0 <= i <= N,
        forall |k: int| 0 <= k < i ==> a[k] == 1,
        forall |k: int| i <= k < N ==> old(a)[k] == a[k],
        a.len() == N,
        b.len() == N,
        sum.len() == 1,
        N > 0,
        N < 1000,
        decreases(N as int - i as int),
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
    invariant
        0 <= i <= N,
        forall |k: int| 0 <= k < i ==> b[k] == 1,
        forall |k: int| i <= k < N ==> old(b)[k] == b[k],
        a.len() == N,
        b.len() == N,
        sum.len() == 1,
        N > 0,
        N < 1000,
        decreases(N as int - i as int),
    {
        b.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
    invariant
        0 <= i <= N,
        sum.len() == 1,
        sum[0] == i,  // Each iteration adds 1 from `a[i]`
        a.len() == N,
        b.len() == N,
        N > 0,
        N < 1000,
        decreases(N as int - i as int),
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
    invariant
        0 <= i <= N,
        forall |k: int| 0 <= k < i ==> a[k] == N + 1,
        // The property of a[i] will change, no modifications to invariants are needed.
        forall |k: int| i <= k < N ==> a[k] == 1 || a[k] == b[k] + sum[0],
        sum.len() == 1,
        sum[0] == N as i32,
        a.len() == N,
        b.len() == N,
        N > 0,
        N < 1000,
        decreases(N as int - i as int),
    {
        a.set(i, b[i] + sum[0]);
        i = i + 1;
    }
}
}
// Score: Compilation Error: False, Verified: 1, Errors: 0, Verus Errors: 0
// Safe: True