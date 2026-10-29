
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

spec fn is_divisible(n: int, divisor: int) -> bool {
    (n % divisor) == 0
}

proof fn exists_divisor(n: u64, index: u64)
    requires
        n >= 2,
        (n % index) == 0,
        index < n,
        index >= 2,
    ensures
        exists|k: int| 2 <= k <= index && is_divisible(n as int, k)
{
    assert(index as int >= 2);
    assert(is_divisible(n as int, index as int));
    assert(exists|k: int| k == index as int && 2 <= k <= index as int && is_divisible(n as int, k));
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
            n >= 2,
            index >= 2,
            forall |k: int| 2 <= k < index ==> !is_divisible(n as int, k),
        decreases n - index,
    {
        if ((n % index) == 0) {
            proof {
                exists_divisor(n, index);
            }
            return false;
        }
        index += 1;
    }
    true
}

}

// Score: Compilation Error: False, Verified: 3, Errors: 0, Verus Errors: 0
// Safe: True