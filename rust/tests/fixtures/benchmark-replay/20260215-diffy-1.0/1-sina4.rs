
use vstd::prelude::*;
fn main() {}

verus!{

proof fn bound_check(N: i32)
    requires
        N > 0,
        N < 1000,
    ensures
        N + N + 1 < i32::MAX,
{
    // Since N < 1000, we can derive that N + N + 1 < 2001, which is less than i32::MAX
    assert(N < 1000);
}

proof fn upper_bound_check(a_val: i32, sum_val: i32)
    requires
        a_val == 1,
        sum_val >= 0,
        sum_val < 1000,
    ensures
        a_val + sum_val <= i32::MAX,
{
    assert(a_val + sum_val == sum_val + 1);
    assert(sum_val + 1 <= 1001);
    assert(1001 < i32::MAX);
}

proof fn a_values_initialized_to_1(a: &Vec<i32>, N: usize)
    requires
        a.len() == N,
    ensures
        forall |k: usize| 0 <= k < N ==> a[( k ) as int] == 1,
{
    // Since the function myfun sets all elements to 1 in the first loop, we can ensure that post this loop:
    assert forall |k: usize| 0 <= k < a.len() ==> a[(k) as int] == 1 by {
        assert(a[( k ) as int] == 1);
    };
}

#[verifier::loop_isolation(false)]
pub fn myfun(a: &mut Vec<i32>, b: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(b).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        forall |k:int| 0 <= k < N ==> b[k] == N + 2,
{
    sum.set(0, 0);
    let mut i: usize = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            a.len() == N as usize,
            sum.len() == 1,
            forall |k: int| 0 <= k < i ==> a[k] == 1,
            // preconditions
            N > 0,
            old(a).len() == N,
            old(b).len() == N,
            old(sum).len() == 1,
            N < 1000,
            decreases(N - i as i32),
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            a.len() == N as usize,
            sum.len() == 1,
            // Array a is unchanged in this loop
            forall |k: int| 0 <= k < a.len() ==> a[k] == 1,
            sum[0] == i as i32,
            // preconditions
            N > 0,
            old(a).len() == N,
            old(b).len() == N,
            old(sum).len() == 1,
            N < 1000,
            decreases(N - i as i32),
    {
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            a.len() == N as usize,
            sum.len() == 1,
            sum[0] == N as i32,
            forall |k: int| 0 <= k < i ==> a[k] == N + 1,
            // preconditions
            N > 0,
            old(a).len() == N,
            old(b).len() == N,
            old(sum).len() == 1,
            N < 1000,
            decreases(N - i as i32),
    {
        proof {
            a_values_initialized_to_1(a, N as usize);
            assert(a[(i) as int] == 1);
        }

        assert(a[i as int] + sum[0] <= i32::MAX) by {
            upper_bound_check(a[( i ) as int], sum[0]);
        }

        a.set(i, a[i] + sum[0]);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            0 <= i <= N as usize,
            a.len() == N as usize,
            b.len() == N as usize,
            sum.len() == 1,
            sum[0] == N as i32,
            // Array a is unchanged in this loop
            forall |k: int| 0 <= k < N ==> a[k] == N + 1,
            forall |k: int| 0 <= k < i ==> b[k] == N + 2,
            // preconditions
            N > 0,
            old(a).len() == N,
            old(b).len() == N,
            old(sum).len() == 1,
            N < 1000,
            decreases(N - i as i32),
    {
        b.set(i, a[i] + 1);
        i = i + 1;
    }
}
}


// Score: Compilation Error: False, Verified: 3, Errors: 1, Verus Errors: 1
// Safe: True