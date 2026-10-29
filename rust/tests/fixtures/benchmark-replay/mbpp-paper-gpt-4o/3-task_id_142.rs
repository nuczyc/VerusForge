
use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

spec fn count_identical(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>) -> int
    decreases s1.len(), s2.len(), s3.len(),
{
    if s1.len() == 0 || s2.len() == 0 || s3.len() == 0 {
        0
    } else {
        count_identical(s1.drop_last(), s2.drop_last(), s3.drop_last()) + 
        if (s1.last() == s2.last() && s2.last() == s3.last()) {
            1 as int
        } else {
            0 as int
        }
    }
}

proof fn lemma_count_bound(s1: Seq<i32>, s2: Seq<i32>, s3: Seq<i32>)
    requires 
        s1.len() == s2.len() && s2.len() == s3.len(),
    ensures
        count_identical(s1, s2, s3) <= s1.len(),
    decreases s1.len()
{
    if s1.len() > 0 {
        lemma_count_bound(s1.drop_last(), s2.drop_last(), s3.drop_last());
    }
}

proof fn lemma_count_increases_with_identical_elements(index: usize, count: usize)
    ensures
        count + 1 <= index + 1 
{
    // This proof shows when one identical element is found, 
    // incrementing count won't exceed the current index.
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
        invariant arr1.len() == arr2.len() && arr2.len() == arr3.len(),
        decreases arr1.len() - index,
    {
        if arr1[index] == arr2[index] && arr2[index] == arr3[index] {
            assert(count < arr1.len()) by {
                lemma_count_increases_with_identical_elements(index, count);
            };
            count += 1;
        }
        index += 1;
    }
    count
}

} // verus!

// Score: Compilation Error: False, Verified: 3, Errors: 3, Verus Errors: 3
// Safe: True