use vstd::prelude::*;

fn main() {}

verus! {

#[verifier::loop_isolation(false)]

fn filter_odd_numbers(arr: &Vec<u32>) -> (odd_list: Vec<u32>)
    ensures
        odd_list@ == arr@.filter(|x: u32| x % 2 != 0),
{
    let mut odd_list: Vec<u32> = Vec::new();
    let input_len = arr.len();

    let mut index = 0;
    while index < arr.len() 
        invariant 
            arr.len() == input_len && index <= arr.len(),
            forall |k: int| 0 <= k < index ==> arr@[k] % 2 != 0 ==> odd_list@.contains(arr@[k]),
            odd_list.len() <= index,
        decreases arr.len() - index,
    {
        if (arr[index] % 2 != 0) {
            odd_list.push(arr[index]);
        }
        proof {
            ensure_odd_numbers_in_odd_list(arr, odd_list@, index);
            assert(forall |k: int| 0 <= k < index + 1 ==> arr@[k] % 2 != 0 ==> odd_list@.contains(arr@[k]));
        }
        index += 1;
    }
    proof {
        assert(odd_list@ == arr@.filter(|x: u32| x % 2 != 0)); // Added by AI
    }
    odd_list
}

proof fn ensure_odd_numbers_in_odd_list(arr: &Vec<u32>, odd_list: Seq<u32>, index: usize)
    ensures forall |k: int| 0 <= k < index + 1 ==> arr@[k] % 2 != 0 ==> odd_list.contains(arr@[k])
{
    assert(forall |k: int| 0 <= k < index ==> arr@[k] % 2 != 0 ==> odd_list.contains(arr@[k]));
    if index < arr.len() {
        if arr[( index ) as int] % 2 != 0 {
            assert(odd_list.contains(arr@[index as int]));
        }
    }
}
} // verus!

// Score: Compilation Error: False, Verified: 0, Errors: 3, Verus Errors: 3
// Safe: True