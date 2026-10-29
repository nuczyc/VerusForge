
use vstd::prelude::*;

fn main() {}

verus! {

proof fn successfully_processed_all_elements(arr: &Vec<Vec<i32>>, index: usize, first_elem_arr: &Vec<i32>)
    requires
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() > 0,
        arr.len() == first_elem_arr.len() + (arr.len() - index),
    ensures
        arr.len() == first_elem_arr.len(),
{
    assert(arr.len() == first_elem_arr.len() + (arr.len() - index)) by {
        assert((arr.len() - index) == 0) by {
            assert_index_reached_len(arr.len(), index);
        };
    }
}

proof fn assert_index_reached_len(arr_len: usize, index: usize)
    requires
        arr_len == index,
    ensures
        index == arr_len,
{
    assert(index == arr_len);
}

#[verifier::loop_isolation(false)]

fn get_first_elements(arr: &Vec<Vec<i32>>) -> (result: Vec<i32>)
    requires
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] arr[i].len() > 0,
    ensures
        arr.len() == result.len(),
        forall|i: int| 0 <= i < arr.len() ==> #[trigger] result[i] == #[trigger] arr[i][0],
{
    let mut first_elem_arr: Vec<i32> = Vec::new();
    let mut index = 0;
    while index < arr.len()
        invariant
            forall|i: int| 0 <= i < arr.len() ==> arr[i].len() > 0,
            arr.len() == first_elem_arr.len() + (arr.len() - index),
            forall|k: int| 0 <= k < index ==> first_elem_arr[k] == arr[k][0],
        decreases
            arr.len() - index,
    {
        let seq = &arr[index];
        first_elem_arr.push(seq[0]);
        index += 1;
    }
    proof {
        successfully_processed_all_elements(arr, index, &first_elem_arr);
        assert(arr.len() == first_elem_arr.len());
        assert(forall|i: int| 0 <= i < arr.len() ==> first_elem_arr[i] == arr[i][0]);
    }
    first_elem_arr
}

}

// Score: Compilation Error: False, Verified: 2, Errors: 2, Verus Errors: 2
// Safe: True