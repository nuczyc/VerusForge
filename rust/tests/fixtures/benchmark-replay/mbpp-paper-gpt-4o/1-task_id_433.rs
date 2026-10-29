
use vstd::prelude::*;

fn main() {}

verus! {

proof fn is_number_greater_than_element(arr: &Vec<i32>, number: i32, idx: usize)
    requires
        idx < arr.len(),
        forall |i: int| 0 <= i < idx ==> number > arr[i],
        number > arr[( idx ) as int],
    ensures
        forall|k: int| 0 <= k <= idx ==> number > arr[k] 
{
    assert(forall|k: int| 0 <= k <= idx ==> number > arr[k]) by {
        if idx > 0 {
            assert(forall |k: int| 0 <= k < idx ==> number > arr[k]);
        }
        let k = idx;
        assert(number > arr[( k ) as int]);
    }
}

#[verifier::loop_isolation(false)]
fn is_greater(arr: &Vec<i32>, number: i32) -> (result: bool)
    ensures
        result == (forall|i: int| 0 <= i < arr.len() ==> number > arr[i]),
{
    let mut i = 0;
    while i < arr.len()
        invariant
            forall|k: int| 0 <= k < i ==> number > arr[k],
        decreases (arr.len() - i)
    {
        proof {
            assert(i < arr.len()); 
            assert(number > arr[(i) as int] || number <= arr[(i) as int]); 
            if number > arr[(i) as int] {
                is_number_greater_than_element(arr, number, i);
            }
        }
        if number <= arr[i] {
            return false;
        }
        i += 1;
    }
    true
}

}

// Score: Compilation Error: False, Verified: 2, Errors: 0, Verus Errors: 0
// Safe: True