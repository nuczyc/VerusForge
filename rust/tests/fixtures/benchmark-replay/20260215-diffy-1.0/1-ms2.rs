
use vstd::prelude::*;
fn main() {}

verus!{

spec fn sum_a_up_to_exclusive(a: &Seq<usize>, n: usize) -> usize
    decreases n
{
    if n == 0 {
        0
    } else {
        ( sum_a_up_to_exclusive(a, ( n - 1 ) as usize) + a[n - 1] ) as usize
    }
}

#[verifier::loop_isolation(false)]
pub fn myfun(a: &mut Vec<usize>, sum: &mut Vec<usize>, N: usize) 
    requires 
        old(a).len() == N,
        old(sum).len() == 1,
        N > 0,
    ensures
        sum[0] <= N,
{
    let mut i: usize = 0;
    while (i < N as usize)
    invariant
        a.len() == N,
        sum.len() == 1,
        N > 0,
        0 <= i && i <= N,
        forall |k: int| 0 <= k < i ==> a[k] == (k % 2),
        decreases(N - i),
    {
        a.set(i, i % 2);
        i = i + 1;
    }

    i = 0;

    while (i < N as usize)
    invariant
        a.len() == N,
        sum.len() == 1,
        N > 0,
        0 <= i && i <= N,
        forall |k: int| 0 <= k < N ==> sum[0] == sum_a_up_to_exclusive(&a@, ( k ) as usize) || sum[0] == sum_a_up_to_exclusive(&a@, ( k ) as usize) + a[k],
        sum[0] >= 0,
        decreases(N - i),
    {
        if (i == 0) {
            sum.set(0, 0);
        } else {
            assert(sum[0] + a[i as int] <= N) by {
                // Since `a` contains 0s and 1s, any sum of selected elements must not exceed total length `N`.
                assert(0 <= a[i as int] <= 1);
                assert(sum[0] <= sum_a_up_to_exclusive(&a@, i) <= N);
                assert(sum[0] + a[i as int] <= N);
            }
            sum.set(0, sum[0] + a[i]);
        }
        i = i + 1;
    }
}
}





// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 2
// Safe: True