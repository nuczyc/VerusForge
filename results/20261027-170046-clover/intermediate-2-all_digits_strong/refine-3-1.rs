vstd::prelude::verus! {
    use vstd::prelude::*;

    fn main() {}

    spec fn is_ascii_digit_spec(c: char) -> bool {
        c == '0'|| c == '1'|| c == '2'|| c == '3'|| c == '4'|| c == '5'|| c == '6'|| c == '7'|| c == '8'|| c == '9'
    }

    fn is_ascii_digit(c: char) -> (r: bool)
        ensures
            r == is_ascii_digit_spec(c),
    {
        c == '0'|| c == '1'|| c == '2'|| c == '3'|| c == '4'|| c == '5'|| c == '6'|| c == '7'|| c == '8'|| c == '9'
    }

    spec fn all_digits_spec(s: Seq < char >) -> bool {
        forall | i: nat |#![auto] i < s.len() ==> is_ascii_digit_spec(s[i as int])
    }

    fn all_digits(s: String) -> (result: bool)
        requires
            s.is_ascii(),
        ensures
            all_digits_spec(s @) == result,
    {
        let mut result = true;
        let mut i = 0;
        while i < s.as_str().unicode_len()
            invariant
                true,
                s.is_ascii(),
                i <= s @.len(),
                forall | k: int | 0 <= k < s @.len() ==>#[trigger] s @[k] == s @[k],
                result ==>(forall | k: nat | k < i ==> is_ascii_digit_spec(s @[k as int])),
                i <= s @.len(),
                s @.len() - i >= 0,
                i > 0 ==> (forall | k: nat | k < i ==> is_ascii_digit_spec(s @[k as int])),
            decreases
                s @.len() - i,
        {
            proof {
                assert(i < s @.len());
            }
            if!is_ascii_digit(s.as_str().get_char(i)) {
                proof {}
                return false;
            }
            proof {
                assert(is_ascii_digit_spec(s @[i as int]));
            }
            proof {
                assert(s @.len() -(i + 1) < s @.len() - i);
            }
            proof {
                assert forall | k: nat | k < i + 1 implies is_ascii_digit_spec(s @[k as int]) by {
                    if k < i {} else {
                        assert(k == i);
                        assert(is_ascii_digit_spec(s @[i as int]));
                    }
                }
            }
            proof {
                assert(s @.len() - i - 1 >= 0);
            }
            proof {
                assert(s @.len() -(i + 1) >= 0);
            }
            proof {
                assert(s @.len() -(i + 1) < s @.len() - i);
            }
            i = i + 1;
        }
        proof {
            assert forall | k: nat | k < s @.len() implies is_ascii_digit_spec(s @[k as int]) by {
                assert(k < i || k == i);
            }
        }
        true
    }
}

// Score: Compilation Error: True, Verified: -1, Errors: 999, Verus Errors: 0
// Safe: False
