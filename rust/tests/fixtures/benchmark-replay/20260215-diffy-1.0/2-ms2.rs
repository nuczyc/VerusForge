use vstd::prelude::*;
fn main() {}

verus! {

proof fn lemma_a_values_upper_bound(a: Seq<usize>, N: usize)
    requires
        a.len() == N,
        forall |i: int| 0 <= i < N ==> a[i] < 2,
    ensures
        forall |i: int| 0 <= i < N ==> a[i] <= N
{
    assert(forall |i: int| 0 <= i < N ==> a[i] < 2);
    assert(forall |i: int| 0 <= i < N ==> a[i] <= 1);
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

    // First loop
    while (i < N as usize)
        invariant
            N > 0,
            a.len() == N,
        decreases (N as int - i as int)
    {
        a.set(i, i % 2);
        i = i + 1;
    }

    i = 0;

    // Second loop
    proof {
        assert(sum.len() == 1);
        lemma_a_values_upper_bound(a@, N); // Invoke the lemma to establish bounds on values
        assert(sum[0] <= N); // Added by AI
    }
    while (i < N as usize)
        invariant
            N > 0,
            a.len() == N,
            sum.len() == 1,
            sum[0] <= N,
        decreases (N as int - i as int)
    {
        if (i == 0) {
            sum.set(0, 0);
        } else {
            proof {
                lemma_a_values_upper_bound(a@, N);
                assert(a[(i) as int] <= N);
            }
            assert(sum[0] + a[(i) as int] <= N);
            sum.set(0, sum[0] + a[i]);
        }
        i = i + 1;
    }
}
}
// Score: Compilation Error: False, Verified: 1, Errors: 2, Verus Errors: 2
// Safe: True