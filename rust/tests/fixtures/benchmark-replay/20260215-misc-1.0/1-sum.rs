
#[allow(unused_imports)]
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

spec fn arith_sum_int(i: nat) -> nat
    decreases i
{
    if i == 0 { 0 } else { i + arith_sum_int( (i - 1) as nat) }
}

proof fn lemma_monotonic(i: nat, j: nat)
    requires
        i <= j,
    ensures
        arith_sum_int(i) <= arith_sum_int(j),
    decreases j - i
{
    if i < j {
        lemma_monotonic(i, (j - 1) as nat);
    }
}

proof fn lemma_arith_sum(n: nat, sum: u64)
    requires
        arith_sum_int(n) == sum,
    ensures
        arith_sum_int(n) == sum
{
    // Trivial lemma for connecting with the loop invariant
}

proof fn lemma_invariant_final(n: nat, i: nat, sum: u64)
    requires
        i == n,
        arith_sum_int(i) == sum,
    ensures
        arith_sum_int(n) == sum
{
    // Immediate conclusion from the invariant when i == n
}

proof fn lemma_i_equals_n(i: u64, n: u64)
    requires
        i >= n,
    ensures
        i == n
{
    assert(i == n);
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
            arith_sum_int(i as nat) == sum,
            arith_sum_int(n as nat) < 10000,
            n as nat == i + (n - i),
            arith_sum_int(i as nat) <= arith_sum_int(n as nat),
        decreases n - i,
    {
        assert(arith_sum_int(i as nat + 1) <= arith_sum_int(n as nat)) by {
            lemma_monotonic(i as nat + 1, n as nat);
        }
        assert(sum + (i + 1) <= arith_sum_int(n as nat)) by {
            lemma_monotonic(i as nat, n as nat);
        }
        i = i + 1;
        sum = sum + i;
    }
    proof {
        lemma_i_equals_n(i, n);
        assert(i == n); // Added by AI
        lemma_invariant_final(n as nat, i as nat, sum);
        assert(arith_sum_int(n as nat) == sum);
    }
    sum
}

} // verus!

// Score: Compilation Error: False, Verified: 6, Errors: 1, Verus Errors: 1
// Safe: True