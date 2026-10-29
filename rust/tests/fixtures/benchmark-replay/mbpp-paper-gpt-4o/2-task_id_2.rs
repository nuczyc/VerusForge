
use vstd::prelude::*;

fn main() {}

verus! {
/*
 This lemma is often useful before a vector-remove call, and it can be useful to prove what element is contained in a vector.
 The parameters to this lemma function should match the executable code after it.
 Do NOT pass `old(..)' to this lemma as parameter.
 Example usage:
    proof{
	lemma_vec_remove(vec@, index);
    }
    vec.remove(index);
 */
proof fn lemma_vec_remove<T>(vec: Seq<T>, i: int)
    requires
        0 <= i < vec.len(),
    ensures
        forall |k: int| 0 <= k < i ==> #[trigger] vec[k] == vec.remove(i)[k],
        forall |k: int| i < k  < vec.len() ==> #[trigger] vec[k] ==  vec.remove(i)[k-1],
{

}

/*
 This lemma is often useful before a vector-push call, and it can be useful to prove what element is contained in a vector.
 Example usage:
    proof{
	lemma_vec_push(vec@, value, vec.len());
    }
    vec.push(value);
 */
proof fn lemma_vec_push<T>(vec: Seq<T>, i: T, l: usize)
    requires
        l == vec.len(),
    ensures
        forall |k: int| 0 <= k < vec.len() ==> #[trigger] vec[k] == vec.push(i)[k],
        vec.push(i).index(l as int) == i,
{
}


#[verifier::loop_isolation(false)]

fn contains(arr: &Vec<i32>, key: i32) -> (result: bool)
    ensures
        result == (exists|i: int| 0 <= i < arr.len() && (arr[i] == key)),
{
    let mut i = 0;
    while i < arr.len() 
    decreases arr.len() - i
    {
        if (arr[i] == key) {
            return true;
        }
        i += 1;
    }
    false
}

proof fn lemma_no_duplicates(arr: Seq<i32>)
    ensures
        forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] != arr[j],
    decreases arr.len()
{
    if arr.len() > 1 {
        let last = arr.last();
        let rest = arr.drop_last();
        assert(!rest.contains(last));
        lemma_no_duplicates(rest);
    }
}

proof fn lemma_shared_elements_correctness(list1: Seq<i32>, list2: Seq<i32>, shared: Seq<i32>)
    ensures
        forall|i: int| 0 <= i < shared.len() ==> (list1.contains(shared[i]) && list2.contains(shared[i])),
    decreases shared.len()
{
    if shared.len() > 0 {
        let last = shared.last();
        let rest = shared.drop_last();
        assert(list1.contains(last));
        assert(list2.contains(last));
        lemma_shared_elements_correctness(list1, list2, rest);
    }
}

fn shared_elements(list1: &Vec<i32>, list2: &Vec<i32>) -> (shared: Vec<i32>)
    ensures
        forall|i: int|
            0 <= i < shared.len() ==> (list1@.contains(#[trigger] shared[i]) && list2@.contains(
                #[trigger] shared[i],
            )),
        forall|i: int, j: int| 0 <= i < j < shared.len() ==> shared[i] != shared[j],
{
    let mut shared = Vec::new();
    let mut index = 0;
    while index < list1.len() 
    decreases list1.len() - index
    {
        if (contains(list2, list1[index]) && !contains(&shared, list1[index])) {
            proof {
                lemma_vec_push(shared@, list1[( index ) as int], shared.len());
            }
            shared.push(list1[index]);
        }
        index += 1
    }
    proof {
        lemma_no_duplicates(shared@);
        lemma_shared_elements_correctness(list1@, list2@, shared@);
        assert(forall|i: int| 0 <= i < shared@.len() ==> list1@.contains(shared@[i]) && list2@.contains(shared@[i]));
    }
    shared
}

} // verus!


// Score: Compilation Error: False, Verified: 4, Errors: 5, Verus Errors: 5
// Safe: True