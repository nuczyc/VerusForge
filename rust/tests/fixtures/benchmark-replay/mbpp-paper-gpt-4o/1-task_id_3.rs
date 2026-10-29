
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

spec fn is_divisible(n: int, divisor: int) -> bool {
    (n % divisor) == 0
}

fn is_non_prime(n: u64) -> (result: bool)
    requires
        n >= 2,
    ensures
        result == (exists|k: int| 2 <= k < n && is_divisible(n as int, k)),
{
    if n <= 1 {
        return true;
    }
    let mut index = 2;
    while index < n
        invariant n >= 2,
        decreases (n - index), // Added by AI
    {
        proof {
    assert(0 <= index);  // Establish lower bound
    assert(0 <= index);  // Establish lower bound
    assert(0 <= index);  // Establish lower bound
    assert(0 <= index);  // Establish lower bound
            assert(index != 0); // Added by AI
        }
        if ((n % index) == 0) {
            return true;
        }
        index += 1;
    }
    false
}

}
// Score: Compilation Error: False, Verified: 0, Errors: 3, Verus Errors: 3
// Safe: True