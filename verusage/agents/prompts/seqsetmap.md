This document is about three categories of knowledge about Seq and Set in Verus:
1) open spec
2) axioms
3) vstd lemma functions.

In Verus, EVERY proof that involves Set or Seq should be based on
1) open spec functions (if that API has an open spec); and 2) axioms.

In other words, the properties implified by these axioms and open specs are the
 ONLY knowledge the prover knows about Set and Seq. You should construct your
proof so that the conclusion can be reached based on
the spec functions and axioms listed below.

In addition, some lemma functions are available in ```vstd::set_lib``` and
```vstd::seq_lib```. You can leverage them in your proof by calling them.
After you insert a call to one of the following lemma functions, please add
```assert``` statements right after to indicate what properties are ensured by
the lemma function.

Note:

1. These axiom functions are already known by Verus; do NOT call them in your proof.

2. If the axiom function has a pre-condition, naturally, the pre-condition has to hold in order
for the corresponding post-condition to hold;

3. Pay attention to the ```#[trigger]``` tag below. An expression that matches the trigger expression
has to appear in your code in order for an axiom to take effect.

4. To prove an exist expression ```assert(exists |i:K| condition(i))```, you should identify a variable
or constant ```j``` to make that condition true and add ```assert(condition(j));``` in the program.

To make use of an ```exist``` expression ```assert(exists |i:K| condition(i))```, you should use ```choose```:
```let k = choose |i:K| condition(i);```.
Verus will then know that ```condition(k)``` is true.




Part 1.a: open spec functions of Set

```
pub open spec fn subset_of(self, s2: Set<A>) -> bool {
        forall|a: A| self.contains(a) ==> s2.contains(a)
}

pub open spec fn filter(self, f: spec_fn(A) -> bool) -> Set<A> {
        self.intersect(Self::new(f))
}

pub open spec fn choose(self) -> A {
    choose|a: A| self.contains(a)
}

pub open spec fn disjoint(self, s2: Self) -> bool {
    forall|a: A| self.contains(a) ==> !s2.contains(a)
}
```

Part 1.b: open spec functions of Seq

```rust
   #[verifier::opaque]
    pub open spec fn filter(self, pred: spec_fn(A) -> bool) -> Self
        decreases self.len(),
    {
        if self.len() == 0 {
            self
        } else {
            let subseq = self.drop_last().filter(pred);
            if pred(self.last()) {
                subseq.push(self.last())
            } else {
                subseq
            }
        }
    }

    pub open spec fn contains(self, needle: A) -> bool {
        exists|i: int| 0 <= i < self.len() && self[i] == needle
    }

    pub open spec fn index_of(self, needle: A) -> int {
        choose|i: int| 0 <= i < self.len() && self[i] == needle
    }

    pub open spec fn drop_last(self) -> Seq<A>
        recommends
            self.len() >= 1,
    {
        self.subrange(0, self.len() as int - 1)
    }


    pub open spec fn drop_first(self) -> Seq<A>
        recommends
            self.len() >= 1,
    {
        self.subrange(1, self.len() as int)
    }

    pub open spec fn no_duplicates(self) -> bool {
        forall|i, j| (0 <= i < self.len() && 0 <= j < self.len() && i != j) ==> self[i] != self[j]
    }

    /// Returns `true` if two sequences are disjoint
    pub open spec fn disjoint(self, other: Self) -> bool {
        forall|i: int, j: int| 0 <= i < self.len() && 0 <= j < other.len() ==> self[i] != other[j]
    }

    /// Converts a sequence into a set
    pub open spec fn to_set(self) -> Set<A> {
        Set::new(|a: A| self.contains(a))
    }

    pub open spec fn remove_value(self, val: A) -> Seq<A> {
        let index = self.index_of_first(val);
        match index {
            Some(i) => self.remove(i),
            None => self,
        }
    }

    pub open spec fn reverse(self) -> Seq<A>
        decreases self.len(),
    {
        if self.len() == 0 {
            Seq::empty()
        } else {
            Seq::new(self.len(), |i: int| self[self.len() - 1 - i])
        }
    }

    pub open spec fn insert(self, i: int, a: A) -> Seq<A>
        recommends
            0 <= i <= self.len(),
    {
        self.subrange(0, i).push(a) + self.subrange(i, self.len() as int)
    }

    pub open spec fn remove(self, i: int) -> Seq<A>
        recommends
            0 <= i < self.len(),
    {
        self.subrange(0, i) + self.subrange(i + 1, self.len() as int)
    }


```


Part 2.a: ALL the axioms about Set
Do NOT call them. These are the knowledge Verus already knows.

```rust
pub broadcast proof fn axiom_set_empty<A>(a: A)
    ensures
        !(#[trigger] Set::empty().contains(a)),

pub broadcast proof fn axiom_set_new<A>(f: spec_fn(A) -> bool, a: A)
    ensures
        #[trigger] Set::new(f).contains(a) == f(a),

pub broadcast proof fn axiom_set_insert_same<A>(s: Set<A>, a: A)
    ensures
        #[trigger] s.insert(a).contains(a),

pub broadcast proof fn axiom_set_insert_different<A>(s: Set<A>, a1: A, a2: A)
    requires
        a1 != a2,
    ensures
        #[trigger] s.insert(a2).contains(a1) == s.contains(a1),

pub broadcast proof fn axiom_set_remove_same<A>(s: Set<A>, a: A)
    ensures
        !(#[trigger] s.remove(a).contains(a)),

pub broadcast proof fn axiom_set_remove_insert<A>(s: Set<A>, a: A)
    requires
        s.contains(a),
    ensures
        (#[trigger] s.remove(a)).insert(a) == s,

/************Set::...()::contains()*********/
pub broadcast proof fn axiom_set_remove_different<A>(s: Set<A>, a1: A, a2: A)
    requires
        a1 != a2,
    ensures
        #[trigger] s.remove(a2).contains(a1) == s.contains(a1),

pub broadcast proof fn axiom_set_union<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        #[trigger] s1.union(s2).contains(a) == (s1.contains(a) || s2.contains(a)),

pub broadcast proof fn axiom_set_intersect<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        #[trigger] s1.intersect(s2).contains(a) == (s1.contains(a) && s2.contains(a)),

pub broadcast proof fn axiom_set_difference<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        #[trigger] s1.difference(s2).contains(a) == (s1.contains(a) && !s2.contains(a)),

pub broadcast proof fn axiom_set_complement<A>(s: Set<A>, a: A)
    ensures
        #[trigger] s.complement().contains(a) == !s.contains(a),

/*************s1==s2*******************/
pub broadcast proof fn axiom_set_ext_equal<A>(s1: Set<A>, s2: Set<A>)
    ensures
        #[trigger] (s1 =~= s2) <==> (forall|a: A| s1.contains(a) == s2.contains(a)),

pub broadcast proof fn axiom_set_ext_equal_deep<A>(s1: Set<A>, s2: Set<A>)
    ensures
        #[trigger] (s1 =~~= s2) <==> s1 =~= s2,

/**********Set::mk_map****************/
pub broadcast axiom fn axiom_mk_map_domain<K, V>(s: Set<K>, f: spec_fn(K) -> V)
    ensures
        #[trigger] s.mk_map(f).dom() == s,

pub broadcast axiom fn axiom_mk_map_index<K, V>(s: Set<K>, f: spec_fn(K) -> V, key: K)
    requires
        s.contains(key),
    ensures
        #[trigger] s.mk_map(f)[key] == f(key),

/******* Set::finite() *****/
pub broadcast proof fn axiom_set_empty_finite<A>()
    ensures
        #[trigger] Set::<A>::empty().finite(),

pub broadcast proof fn lemma_set_subset_finite<A>(s: Set<A>, sub: Set<A>)
    requires
        s.finite(),
        sub.subset_of(s),
    ensures
        #![trigger sub.subset_of(s)]
        sub.finite(),

pub broadcast proof fn axiom_set_insert_finite<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger] s.insert(a).finite(),

pub broadcast proof fn axiom_set_remove_finite<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger] s.remove(a).finite(),

pub broadcast proof fn axiom_set_union_finite<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
        s2.finite(),
    ensures
        #[trigger] s1.union(s2).finite(),

pub broadcast proof fn axiom_set_intersect_finite<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite() || s2.finite(),
    ensures
        #[trigger] s1.intersect(s2).finite(),

pub broadcast proof fn axiom_set_difference_finite<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
    ensures
        #[trigger] s1.difference(s2).finite(),

/******Set::choose, Set::contains************/
pub broadcast proof fn axiom_set_choose_finite<A>(s: Set<A>)
    requires
        !s.finite(),
    ensures
        #[trigger] s.contains(s.choose()),

pub broadcast proof fn axiom_set_choose_len<A>(s: Set<A>)
    requires
        s.finite(),
        #[trigger] s.len() != 0,
    ensures
        #[trigger] s.contains(s.choose()),

/******Set::len***************************/
pub broadcast proof fn axiom_set_empty_len<A>()
    ensures
        #[trigger] Set::<A>::empty().len() == 0,

pub broadcast proof fn axiom_set_insert_len<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger] s.insert(a).len() == s.len() + (if s.contains(a) {
            0int
        } else {
            1
        }),

pub broadcast proof fn axiom_set_remove_len<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        s.len() == #[trigger] s.remove(a).len() + (if s.contains(a) {
            1int
        } else {
            0
        }),

pub broadcast proof fn axiom_set_contains_len<A>(s: Set<A>, a: A)
    requires
        s.finite(),
        #[trigger] s.contains(a),
    ensures
        #[trigger] s.len() != 0,


/********Set::is_empty()**********/
pub broadcast proof fn axiom_is_empty<A>(s: Set<A>)
    requires
        !(#[trigger] s.is_empty()),
    ensures
        exists|a: A| s.contains(a),
{
    admit();  // REVIEW, should this be in `set`, or have a proof?
}

pub broadcast proof fn axiom_is_empty_len0<A>(s: Set<A>)
    ensures
        #[trigger] s.is_empty() <==> (s.finite() && s.len() == 0),
{
}

```

Part 2.b: ALL the axioms about Seq
Do NOT call these axiom functions; Verus already knows them.

```rust

pub broadcast axiom fn axiom_seq_index_decreases<A>(s: Seq<A>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        #[trigger] (decreases_to!(s => s[i])),
;

pub axiom fn axiom_seq_len_decreases<A>(s1: Seq<A>, s2: Seq<A>)
    requires
        s2.len() < s1.len(),
        forall|i2: int|
            0 <= i2 < s2.len() && #[trigger] trigger(s2[i2]) ==> exists|i1: int|
                0 <= i1 < s1.len() && s1[i1] == s2[i2],
    ensures
        decreases_to!(s1 => s2),
;

pub broadcast proof fn axiom_seq_subrange_decreases<A>(s: Seq<A>, i: int, j: int)
    requires
        0 <= i <= j <= s.len(),
        s.subrange(i, j).len() < s.len(),
    ensures
        #[trigger] (decreases_to!(s => s.subrange(i, j))),

pub broadcast axiom fn axiom_seq_empty<A>()
    ensures
        #[trigger] Seq::<A>::empty().len() == 0,
;

pub broadcast axiom fn axiom_seq_new_len<A>(len: nat, f: spec_fn(int) -> A)
    ensures
        #[trigger] Seq::new(len, f).len() == len,
;

pub broadcast axiom fn axiom_seq_new_index<A>(len: nat, f: spec_fn(int) -> A, i: int)
    requires
        0 <= i < len,
    ensures
        #[trigger] Seq::new(len, f)[i] == f(i),
;

pub broadcast axiom fn axiom_seq_push_len<A>(s: Seq<A>, a: A)
    ensures
        #[trigger] s.push(a).len() == s.len() + 1,
;

pub broadcast axiom fn axiom_seq_push_index_same<A>(s: Seq<A>, a: A, i: int)
    requires
        i == s.len(),
    ensures
        #[trigger] s.push(a)[i] == a,
;

pub broadcast axiom fn axiom_seq_push_index_different<A>(s: Seq<A>, a: A, i: int)
    requires
        0 <= i < s.len(),
    ensures
        #[trigger] s.push(a)[i] == s[i],
;

pub broadcast axiom fn axiom_seq_update_len<A>(s: Seq<A>, i: int, a: A)
    requires
        0 <= i < s.len(),
    ensures
        #[trigger] s.update(i, a).len() == s.len(),
;

pub broadcast axiom fn axiom_seq_update_same<A>(s: Seq<A>, i: int, a: A)
    requires
        0 <= i < s.len(),
    ensures
        #[trigger] s.update(i, a)[i] == a,
;

pub broadcast axiom fn axiom_seq_update_different<A>(s: Seq<A>, i1: int, i2: int, a: A)
    requires
        0 <= i1 < s.len(),
        0 <= i2 < s.len(),
        i1 != i2,
    ensures
        #[trigger] s.update(i2, a)[i1] == s[i1],
;

pub broadcast axiom fn axiom_seq_ext_equal<A>(s1: Seq<A>, s2: Seq<A>)
    ensures
        #[trigger] (s1 =~= s2) <==> {
            &&& s1.len() == s2.len()
            &&& forall|i: int| 0 <= i < s1.len() ==> s1[i] == s2[i]
        },
;

pub broadcast axiom fn axiom_seq_ext_equal_deep<A>(s1: Seq<A>, s2: Seq<A>)
    ensures
        #[trigger] (s1 =~~= s2) <==> {
            &&& s1.len() == s2.len()
            &&& forall|i: int| 0 <= i < s1.len() ==> s1[i] =~~= s2[i]
        },
;

pub broadcast axiom fn axiom_seq_subrange_len<A>(s: Seq<A>, j: int, k: int)
    requires
        0 <= j <= k <= s.len(),
    ensures
        #[trigger] s.subrange(j, k).len() == k - j,
;

pub broadcast axiom fn axiom_seq_subrange_index<A>(s: Seq<A>, j: int, k: int, i: int)
    requires
        0 <= j <= k <= s.len(),
        0 <= i < k - j,
    ensures
        #[trigger] s.subrange(j, k)[i] == s[i + j],
;

pub broadcast axiom fn axiom_seq_add_len<A>(s1: Seq<A>, s2: Seq<A>)
    ensures
        #[trigger] s1.add(s2).len() == s1.len() + s2.len(),
;

pub broadcast axiom fn axiom_seq_add_index1<A>(s1: Seq<A>, s2: Seq<A>, i: int)
    requires
        0 <= i < s1.len(),
    ensures
        #[trigger] s1.add(s2)[i] == s1[i],
;

pub broadcast axiom fn axiom_seq_add_index2<A>(s1: Seq<A>, s2: Seq<A>, i: int)
    requires
        s1.len() <= i < s1.len() + s2.len(),
    ensures
        #[trigger] s1.add(s2)[i] == s2[i - s1.len()],
;

pub broadcast proof fn lemma_filter_len(self, pred: spec_fn(A) -> bool)
        ensures
            #[trigger] self.filter(pred).len() <= self.len(),


pub broadcast proof fn lemma_filter_pred(self, pred: spec_fn(A) -> bool, i: int)
        requires
            0 <= i < self.filter(pred).len(),
        ensures
            pred(#[trigger] self.filter(pred)[i]),

pub broadcast proof fn lemma_filter_contains(self, pred: spec_fn(A) -> bool, i: int)
        requires
            0 <= i < self.len() && pred(self[i]),
        ensures
            #[trigger] self.filter(pred).contains(self[i]),

pub broadcast proof fn add_empty_left(a: Self, b: Self)
        requires
            a.len() == 0,
        ensures
            #[trigger] (a + b) == b,

 pub broadcast proof fn add_empty_right(a: Self, b: Self)
        requires
            b.len() == 0,
        ensures
            #[trigger] (a + b) == a,

pub broadcast proof fn push_distributes_over_add(a: Self, b: Self, elt: A)
        ensures
            #[trigger] (a + b).push(elt) == a + b.push(elt),

pub broadcast proof fn filter_distributes_over_add(a: Self, b: Self, pred: spec_fn(A) -> bool)
        ensures
            #[trigger] (a + b).filter(pred) == a.filter(pred) + b.filter(pred),

pub broadcast proof fn seq_to_set_is_finite<A>(seq: Seq<A>)
    ensures
        #[trigger] seq.to_set().finite(),

pub broadcast proof fn lemma_fold_right_split<B>(self, f: spec_fn(A, B) -> B, b: B, k: int)
        requires
            0 <= k <= self.len(),
        ensures
            self.subrange(0, k).fold_right(
                f,
                (#[trigger] self.subrange(k, self.len() as int).fold_right(f, b)),
            ) == self.fold_right(f, b),

pub broadcast proof fn lemma_fold_left_split<B>(self, b: B, f: spec_fn(B, A) -> B, k: int)
        requires
            0 <= k <= self.len(),
        ensures
            self.subrange(k, self.len() as int).fold_left(
                (#[trigger] self.subrange(0, k).fold_left(b, f)),
                f,
            ) == self.fold_left(b, f),
```

Part 3. Lemma functions available in ```vstd::seq_lib```

```rust

impl<A> Seq<A> {
    // The following lemma functions are all methods of Seq.
    // If it has its first parameter as `self', you call it by s.foo(...), with s being a Seq object
    // If it does not have its first parameter named `self`, you call it by Seq::foo(...)

    pub proof fn drop_last_distributes_over_add(a: Self, b: Self)
        requires
            0 < b.len(),
        ensures
            (a + b).drop_last() == a + b.drop_last(),

    pub proof fn insert_ensures(self, pos: int, elt: A)
        requires
            0 <= pos <= self.len(),
        ensures
            self.insert(pos, elt).len() == self.len() + 1,
            forall|i: int| 0 <= i < pos ==> #[trigger] self.insert(pos, elt)[i] == self[i],
            forall|i: int| pos <= i < self.len() ==> self.insert(pos, elt)[i + 1] == self[i],
            self.insert(pos, elt)[pos] == elt,

    pub proof fn remove_ensures(self, i: int)
        requires
            0 <= i < self.len(),
        ensures
            self.remove(i).len() == self.len() - 1,
            forall|index: int| 0 <= index < i ==> #[trigger] self.remove(i)[index] == self[index],
            forall|index: int|
                i <= index < self.len() - 1 ==> #[trigger] self.remove(i)[index] == self[index + 1],

    pub proof fn lemma_multiset_has_no_duplicates(self)
        requires
            self.no_duplicates(),
        ensures
            forall|x: A| self.to_multiset().contains(x) ==> self.to_multiset().count(x) == 1,

    pub proof fn lemma_multiset_has_no_duplicates_conv(self)
        requires
            forall|x: A| self.to_multiset().contains(x) ==> self.to_multiset().count(x) == 1,
        ensures
            self.no_duplicates(),

    pub proof fn unique_seq_to_set(self)
        requires
            self.no_duplicates(),
        ensures
            self.len() == self.to_set().len(),

    pub proof fn lemma_cardinality_of_set(self)
        ensures
            self.to_set().len() <= self.len(),

    pub proof fn lemma_cardinality_of_empty_set_is_0(self)
        ensures
            self.to_set().len() == 0 <==> self.len() == 0,

    pub proof fn lemma_no_dup_set_cardinality(self)
        requires
            self.to_set().len() == self.len(),
        ensures
            self.no_duplicates(),

    pub broadcast proof fn lemma_to_set_map_commutes<B>(self, f: spec_fn(A) -> B)
        ensures
            #[trigger] self.to_set().map(f) =~= self.map_values(f).to_set(),

    pub broadcast proof fn lemma_to_set_insert_commutes(sq: Seq<A>, elt: A)
        requires
        ensures
            #[trigger] (sq + seq![elt]).to_set() =~= sq.to_set().insert(elt),

    pub proof fn lemma_all_neg_filter_empty(self, pred: spec_fn(A) -> bool)
        requires
            self.all(|x: A| !pred(x)),
        ensures
            self.filter(pred).len() == 0,

    pub broadcast proof fn lemma_filter_contains_rev(self, p: spec_fn(A) -> bool, elem: A)
        requires
            #[trigger] self.filter(p).contains(elem),
        ensures
            self.contains(elem),

    pub broadcast proof fn lemma_filter_prepend(self, x: A, p: spec_fn(A) -> bool)
        ensures
            #[trigger] (seq![x] + self).filter(p) == (if p(x) {
                seq![x]
            } else {
                Seq::empty()
            }) + self.filter(p),

    pub proof fn lemma_filter_monotone(self, ys: Seq<A>, p: spec_fn(A) -> bool)
        requires
            self.is_prefix_of(ys),
        ensures
            self.filter(p).is_prefix_of(ys.filter(p)),

    pub proof fn lemma_filter_take_len(self, p: spec_fn(A) -> bool, i: int)
        requires
            0 <= i <= self.len(),
        ensures
            self.filter(p).len() >= self.take(i).filter(p).len(),

    pub broadcast proof fn lemma_filter_len_push(self, p: spec_fn(A) -> bool, elem: A)
        ensures
            #[trigger] self.push(elem).filter(p).len() == self.filter(p).len() + (if p(elem) {
                1int
            } else {
                0int
            }),

    pub broadcast proof fn lemma_take_any_succ(self, p: spec_fn(A) -> bool, i: int)
        requires
            0 <= i < self.len(),
        ensures
            #[trigger] self.take(i + 1).any(p) <==> self.take(i).any(p) || p(self[i]),

    pub broadcast proof fn lemma_push_to_set_commute(self, elem: A)
        ensures
            #[trigger] self.push(elem).to_set() =~= self.to_set().insert(elem),

    pub broadcast proof fn lemma_filter_push(self, elem: A, pred: spec_fn(A) -> bool)
        ensures
            #[trigger] self.push(elem).filter(pred) == if pred(elem) {
                self.filter(pred).push(elem)
            } else {
                self.filter(pred)
            },
}

pub broadcast proof fn seq_to_set_is_finite<A>(seq: Seq<A>)
    ensures
        #[trigger] seq.to_set().finite(),

pub proof fn seq_to_set_distributes_over_add<T>(s1: Seq<T>, s2: Seq<T>)
    ensures
        s1.to_set() + s2.to_set() =~= (s1 + s2).to_set(),

pub broadcast proof fn lemma_seq_concat_contains_all_elements<A>(x: Seq<A>, y: Seq<A>, elt: A)
    ensures
        #[trigger] (x + y).contains(elt) <==> x.contains(elt) || y.contains(elt),

pub broadcast proof fn lemma_seq_contains_after_push<A>(s: Seq<A>, v: A, x: A)
    ensures
        #[trigger] s.push(v).contains(x) <==> v == x || s.contains(x),

pub broadcast proof fn lemma_seq_subrange_elements<A>(s: Seq<A>, start: int, stop: int, x: A)
    requires
        0 <= start <= stop <= s.len(),
    ensures
        #[trigger] s.subrange(start, stop).contains(x) <==> (exists|i: int|
            0 <= start <= i < stop <= s.len() && #[trigger] s[i] == x),

pub broadcast proof fn lemma_seq_take_contains<A>(s: Seq<A>, n: int, x: A)
    requires
        0 <= n <= s.len(),
    ensures
        #[trigger] s.take(n).contains(x) <==> (exists|i: int|
            0 <= i < n <= s.len() && #[trigger] s[i] == x),

pub proof fn subrange_of_matching_take<T>(a: Seq<T>, b: Seq<T>, s: int, e: int, l: int)
    requires
        a.take(l) == b.take(l),
        l <= a.len(),
        l <= b.len(),
        0 <= s <= e <= l,
    ensures
        a.subrange(s, e) == b.subrange(s, e),

pub broadcast proof fn lemma_seq_skip_contains<A>(s: Seq<A>, n: int, x: A)
    requires
        0 <= n <= s.len(),
    ensures
        #[trigger] s.skip(n).contains(x) <==> (exists|i: int|
            0 <= n <= i < s.len() && #[trigger] s[i] == x),
```
