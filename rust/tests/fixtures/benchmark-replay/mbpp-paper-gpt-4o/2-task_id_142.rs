use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

spec fn count_identical(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>) -> int
    decreases s1.len(), s2.len(), s3.len()
{
    if s1.len() == 0 || s2.len() == 0 || s3.len() == 0 {
        0
    } else {
        count_identical(s1.drop_last(), s2.drop_last(), s3.drop_last()) + if (s1.last() == s2.last()
            && s2.last() == s3.last()) {
            1 as int
        } else {
            0 as int
        }
    }
}

fn count_identical_position(arr1: &Vec<i32>, arr2: &Vec<i32>, arr3: &Vec<i32>) -> (count: usize)
    requires
        arr1.len() == arr2.len() && arr2.len() == arr3.len(),
    ensures
        0 <= count <= arr1.len(),
        count_identical(arr1@, arr2@, arr3@) == count,
{
    let mut count = 0;
    let mut index = 0;
    while index < arr1.len()
        invariant
            arr1.len() == arr2.len() && arr2.len() == arr3.len(),
            forall |k:int| 0 <= k < arr1.len() ==> arr1[k] == arr1[k], // The arr1 array is not modified in the loop.
            forall |k:int| 0 <= k < arr2.len() ==> arr2[k] == arr2[k], // The arr2 array is not modified in the loop.
            forall |k:int| 0 <= k < arr3.len() ==> arr3[k] == arr3[k], // The arr3 array is not modified in the loop.
            0 <= count <= index, // Ensure `count` is always within the index limit.
        decreases arr1.len() - index // Added by AI
    {
        if arr1[index] == arr2[index] && arr2[index] == arr3[index] {
            assert(count < arr1.len());  // Ensure `count + 1` will not overflow
            count += 1;
        }
        index += 1;
    }
    proof {
        assert(count_identical(arr1@, arr2@, arr3@) == count); // Added by AI
    }
    count
}

} // verus!

// Score: Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 2
// Safe: True