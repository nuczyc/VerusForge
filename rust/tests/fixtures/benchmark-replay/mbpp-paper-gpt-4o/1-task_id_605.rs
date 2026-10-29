
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

spec fn is_divisible(n: int, divisor: int) -> bool {
    (n % divisor) == 0
}

fn prime_num(n: u64) -> (result: bool)
    requires
        n >= 2,
    ensures
        result == (forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k)),
{
    if n <= 1 {
        return false;
    }
    let mut index = 2;
    while index < n
        invariant
            n >= 2, // n is never modified in the loop
            index >= 2, // Added by AI
            forall|k: int| 2 <= k < index ==> !is_divisible(n as int, k), // Added by AI
        decreases n - index
    {
        if ((n % index) == 0) {
            proof {
                assert(is_divisible(n as int, ( index ) as int));
                assert(exists|k: int| 2 <= k < n && is_divisible(n as int, k)) by {
                    assume(2 <= index < n);
                    assert(is_divisible(n as int, ( index ) as int));
                };
            }
            return false;
        }
        index += 1;
    }
    proof {
        assert(forall|k: int| 2 <= k < n ==> !is_divisible(n as int, k)); // Added by AI
    }
    true
}

}



// Score: Compilation Error: False, Verified: 2, Errors: 0, Verus Errors: 0
// Safe: True