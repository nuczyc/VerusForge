
use vstd::prelude::*;
fn main() {}

verus! {

proof fn assertion_helper(a: &Vec<i32>, i: int, N: int)
    requires
        forall |k: int| 0 <= k < i ==> a[k] == 3,
        0 <= i < N,
    ensures
        a[i] >= 1
{
    assert(a[i] == 1 || a[i] == 2 || a[i] == 3);
    assert(a[i] >= 1);
}

proof fn propagate_invariant(a: &Vec<i32>, i: int)
    requires
        forall |k: int| 0 <= k < i ==> a[k] == 3,
        a[i] == 3,
        i >= 0,
    ensures
        forall |k: int| 0 <= k < i + 1 ==> a[k] == 3
{
    assert(forall |k: int| 0 <= k < i + 1 ==> a[k] == 3);
}

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
        forall |k: int| 0 <= k < i ==> a[k] == 1,
        a.len() == N,
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
        forall |k: int| 0 <= k < i ==> a[k] == 3,
        a.len() == N,
        sum.len() == 1,
        N > 0,
        N < 1000,
        decreases(N as int - i as int),
    {
        if (a[i] == 1) {
            a.set(i, a[i] + 2);
        } else {
            proof {
                assertion_helper(a, i as int, N as int);
            }
            assert(a[( i ) as int] >= 1);
            a.set(i, a[i] - 1);
        }
        proof {
            propagate_invariant(a, i as int);
        }
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
    invariant
        sum.len() == 1,
        sum[0] == i as i32 * 3,
        a.len() == N,
        N > 0,
        N < 1000,
        decreases(N as int - i as int),
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
    
    assert(sum[0] == 3 * N); 
}
}

// Score: Compilation Error: False, Verified: 1, Errors: 3, Verus Errors: 3
// Safe: True