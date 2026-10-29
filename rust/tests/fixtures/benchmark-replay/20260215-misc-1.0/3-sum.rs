
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
    decreases j - i
{
    if i < j {
        lemma_arith_sum_monotonic(i, (j - 1) as nat);
    }
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
        sum == arith_sum_int(i as nat),
        arith_sum_int(n as nat) < 10000,
        i <= n,
    decreases n - i
    {
        i = i + 1;

        assert(sum + i <= arith_sum_int(n as nat)) by {
            lemma_arith_sum_monotonic(i as nat, n as nat);
        };

        sum = sum + i;
    }
    sum
}

} // verus!

// Score: Compilation Error: False, Verified: 4, Errors: 0, Verus Errors: 0
// Safe: True