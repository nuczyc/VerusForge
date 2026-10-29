
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn insert_before_each(arr: &Vec<i32>, elem: i32) -> (result: Vec<i32>)
    ensures
        result@.len() == (2 * arr.len()),
        forall|k: int| 0 <= k < arr.len() ==> #[trigger] result[2 * k] == elem,
        forall|k: int| 0 <= k < arr.len() ==> #[trigger] result[2 * k + 1] == arr[k],
{
    let mut result: Vec<i32> = Vec::new();
    let mut index = 0;

    while index < arr.len()
    invariant
        forall|i: int| 0 <= i < index ==> result[2 * i + 1] == arr[i],
        2 * index <= result.len()
    decreases arr.len() - index
    {
        result.push(elem);
        result.push(arr[index]);

        assert(forall|i: nat| 0 <= i < index + 1 ==> result[( 2 * i + 1 ) as int] == arr[( i ) as int]) by {
            assert(forall|i: int| 0 <= i < index ==> result[2 * i + 1] == arr[i]);
            assert(result[2 * index + 1] == arr[( index ) as int]);
        }

        index += 1;
    }

    result
}

}




// Score: Compilation Error: False, Verified: 0, Errors: 2, Verus Errors: 2
// Safe: True