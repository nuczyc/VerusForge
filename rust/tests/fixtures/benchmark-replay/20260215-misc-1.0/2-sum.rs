
#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

spec fn arith_sum_int(i: nat) -> nat
    decreases i
{
    if i == 0 { 0 } else { i + arith_sum_int((i - 1) as nat) }
}

proof fn lemma_arith_sum_monotonic(i: nat, j: nat)
    requires
        i <= j,
    ensures
        arith_sum_int(i) <= arith_sum_int(j),
    decreases j
{
    if i < j {
        lemma_arith_sum_monotonic(i, (j - 1) as nat);
    }
}

/// Helper function to ensure the arith_sum_int function completes the full iteration
proof fn lemma_arith_sum_full_iteration(i: nat, n: nat)
    requires
        i == n,
    ensures
        arith_sum_int(i) == arith_sum_int(n),
{
    // When i equals n, the arithmetic sum is complete for natural numbers.
}

/// Helper function to show that when loop finishes, i must equal n
proof fn lemma_loop_completion(i: u64, n: u64)
    requires
        !(i < n),
    ensures
        i == n,
{
    // Added by AI: i == n when !(i < n)
    assert(i == n); // Added by AI
}

fn compute_arith_sum(n: u64) -> (sum: u64)
    requires
        arith_sum_int(n as nat) < 10000,
    ensures
        arith_sum_int(n as nat) == sum,
{
    let mut i: u64 = 0;
    let mut sum: u64 = 0;
    while i < n
        invariant 
            arith_sum_int(n as nat) < 10000,
            sum == arith_sum_int(i as nat),
        decreases n - i
    {
        i = i + 1;

        // Assert that the next sum does not exceed arith_sum_int(n) and is within u64 limits
        assert(sum + i <= arith_sum_int(n as nat)) by {
            lemma_arith_sum_monotonic(i as nat, n as nat);
        }

        sum = sum + i;
    }
    proof {
        lemma_loop_completion(i, n);
        assert(i == n);
        lemma_arith_sum_full_iteration(i as nat, n as nat);
        assert(arith_sum_int(i as nat) == arith_sum_int(n as nat));
    }
    sum
}

}

// Score: Compilation Error: False, Verified: 5, Errors: 1, Verus Errors: 1
// Safe: True