use vstd::prelude::*;
use vstd::set_lib::*;
use vstd::map_lib::*;

fn main() {}

verus! {

pub proof fn injective_finite_map_implies_dom_len_is_equal_to_values_len<K, V>(m: Map<K, V>)
    requires
        m.dom().finite(),
        m.is_injective(),
    ensures
        m.dom().len() == m.values().len(),
{
}

}
