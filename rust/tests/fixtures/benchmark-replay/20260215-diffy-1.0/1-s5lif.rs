
use vstd::prelude::*;
fn main() {}
verus!{

proof fn lemma_sum_not_overflow(v1: i32, v2: i32, n: i32)
    requires
        (0 <= v1 && v1 <= 6) && (0 <= v2),
        v2 + v1 <= i32::MAX,
    ensures
        v2 + v1 <= i32::MAX
{
    assert(v1 <= 6 <= i32::MAX);
    assert(v2 <= n * 6 <= i32::MAX);
    assert(v1 + v2 <= i32::MAX);
}

#[verifier::loop_isolation(false)]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: i32)
    requires
        N > 0,
        old(a).len() == N,
        old(sum).len() == 1,
        N < 1000,
    ensures
        sum[0] == 6 * N,
{
    let mut i: usize = 0;
    sum.set(0, 0);

    while (i < N as usize)
        invariant
            N > 0,
            N < 1000,
            a.len() == N,
            sum.len() == 1,
            forall |k: int| 0 <= k < i as int ==> a[k] == 1,
        decreases (N as usize - i)
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            N > 0,
            N < 1000,
            a.len() == N,
            sum.len() == 1,
            forall |k: int| 0 <= k < i as int ==> a[k] == 6,
            forall |k: int| i as int <= k < a.len() ==> a[k] == 1,
        decreases (N as usize - i)
    {
        if (a[i] == 1) {
            a.set(i, a[i] + 5);
        } else {
            assert(a[(i) as int] > 1);
            a.set(i, a[i] - 1);
        }
        i = i + 1;
    }

    i = 0;
    while (i < N as usize)
        invariant
            N > 0,
            N < 1000,
            a.len() == N,
            sum.len() == 1,
            forall |k: int| 0 <= k < a.len() ==> a[k] == 6,
        decreases (N as usize - i)
    {
        proof {
            assert(0 <= a[(i) as int] && a[(i) as int] <= 6); // Added by AI
            assert(0 <= sum[0]);
            assert(sum[0] <= N * 6); // Added by AI
            lemma_sum_not_overflow(a[(i) as int], sum[0], N);
        }
        assert(sum[0] + a[(i) as int] <= i32::MAX);
        sum.set(0, sum[0] + a[i]);
        i = i + 1;
    }
}
}

// Score: Compilation Error: False, Verified: 0, Errors: 3, Verus Errors: 3
// Safe: True