
use vstd::prelude::*;
fn main() {}
verus!{

proof fn sum_invariant_proof(N: usize)
    ensures
        0 < 2 * N
{
    assert(0 < 2 * N); // Asserting that the double of a positive integer is positive
}

#[verifier::loop_isolation(false)]
pub fn myfun(a: &mut Vec<i32>, sum: &mut Vec<i32>, N: usize)
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
    while (i < N)
        invariant
            // Maintain array length property
            a.len() == N,
            sum.len() == 1,
            forall |k: int| 0 <= k < i ==> a[k] == 1,
            N > 0,
            N < 1000,
            decreases(N - i),
    {
        a.set(i, 1);
        i = i + 1;
    }

    i = 0;
    while (i < N)
        invariant
            a.len() == N,
            sum.len() == 1,
            forall |k: int| 0 <= k < i ==> a[k] == 2,
            N > 0,
            N < 1000,
            decreases(N - i),
    {
        if (a[i] == 1) {
            a.set(i, a[i] + 1);
        } else {
            // Assert to prevent underflow
            assert(a[( i ) as int] > i32::MIN); // Ensure underflow doesn't occur
            a.set(i, a[i] - 1);
        }
        i = i + 1;
    }

    i = 0;
    proof {
        sum_invariant_proof(N);
        assert(0 < sum[0] + 2 <= 2 * N); // Initialization of sum[0] and initial step
    }
    proof {
        assert(0 <= sum[0]); // Ensure sum[0] is non-negative at the start
        sum_invariant_proof(N); // Call on the helper proof function
    }
    while (i < N)
        invariant
            a.len() == N,
            sum.len() == 1,
            0 <= a[( i ) as int],
            0 <= sum[0] <= 2 * N,
            forall |k: int| 0 <= k < N ==> a[k] == 2, // Changed to cover every element since `a` is not modified in the loop.
            sum[0] == 2 * i,
            N > 0,
            N < 1000,
            decreases(N - i),
    {
        if (a[i] == 2) {
            sum.set(0, sum[0] + a[i]);
        } else {
            sum.set(0, sum[0] * a[i]);
        }
        i = i + 1;

        proof{
            assert(0 <= a[( i ) as int]); // Added by AI
        }
    }
}
}

// Score: Compilation Error: False, Verified: 0, Errors: 3, Verus Errors: 3
// Safe: True