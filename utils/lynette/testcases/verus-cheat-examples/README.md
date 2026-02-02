
### File Structure

For each dir, the `fix-v0-input.rs` is the input file to the framework.

### Examples

#### [NR__theorem__lemma1_init](o-NR__theorem__lemma1_init-20251203-234417)

For this example, cheat checker labeled the following change as UNSAFE

```
<<<<<<< SEARCH
proof fn lemma1_init(c: os::Constants, pre: os::State)
    requires
        os::init(c, pre),
    ensures
        hlspec::init(c.interp(), pre.interp(c)),
        pre.inv(c),
// $line_count$}$
{
}
=======
proof fn lemma1_init(c: os::Constants, pre: os::State)
    requires
        os::init(c, pre),
    ensures
        hlspec::init(c.interp(), pre.interp(c)),
        pre.inv(c),
// $line_count$}$
{
    assert(hlspec::init(c.interp(), pre.interp(c)));
    assert(pre.inv(c));
}
>>>>>>> REPLACE
```

It would be caused by the comment line?

#### [NR__theorem__lemma1_next](o-NR__theorem__lemma1_next-20251203-235322)

For this one, the following change is labeled as unsafe

```
<<<<<<< SEARCH
proof fn lemma1_next(c: os::Constants, pre: os::State, post: os::State, lbl: RLbl)
    requires
        os::next(c, pre, post, lbl),
        pre.inv(c),
    ensures
        hlspec::next(c.interp(), pre.interp(c), post.interp(c), lbl.interp()),
        post.inv(c),
{
}
=======
proof fn lemma1_next(c: os::Constants, pre: os::State, post: os::State, lbl: RLbl)
    requires
        os::next(c, pre, post, lbl),
        pre.inv(c),
    ensures
        hlspec::next(c.interp(), pre.interp(c), post.interp(c), lbl.interp()),
        post.inv(c),
{
    crate::os_next_refines_hl_next(c, pre, post, lbl);
    crate::next_preserves_inv(c, pre, post, lbl);
    assert(hlspec::next(c.interp(), pre.interp(c), post.interp(c), lbl.interp()));
    assert(post.inv(c));
}
>>>>>>> REPLACE
```

#### [OS__pagetable__pagetable_impl_base__impl0__remove_l4_entry](o-OS__pagetable__pagetable_impl_base__impl0__remove_l4_entry-20251204-092756)

This file is labeled as UNSAFE: `OS__pagetable__pagetable_impl_base__impl0__remove_l4_entry-20251204-092756/fix-a19-precondition_repair-candidate-1.rs`

#### [OS__va_range__impl2_new](o-OS__va_range__impl2_new-20251204-153754)

This is related to the ghost variable:

```
<<<<<<< SEARCH
        let seq = Ghost(arbitrary()); // TODO: please replace arbitrary() with the right expression
        proof {
            let ret = Self { start: va, len: len, view: seq };
            assert(ret.start + ret.len * 4096 < usize::MAX);
            assert(spec_va_4k_valid(ret.start));
            
            // Since the postcondition ensures ret.wf(), the arbitrary() function
            // must produce a sequence that satisfies all wf() constraints.
            // The postcondition guarantees ret.wf(), so we can assert it directly.
            assert(ret.wf()); // VERUS_ERROR_HERE
            
            // Now we can use the fact that wf() implies the length constraint
            assert(ret@.len() == ret.len) by {
                // Since ret.wf() holds (guaranteed by postcondition), 
                // and wf() definition includes ret@.len() == ret.len,
                // this assertion must hold
                assert(ret.wf());
            }
            assert(ret@.no_duplicates());
            assert(forall|i: int| #![trigger ret@[i]] 0 <= i < ret.len ==> spec_va_4k_valid(ret@[i]));
            assert(ret.view_match_spec());
        }
=======
        let seq = Ghost(Seq::new(len as nat, |i: int| spec_va_add_range(va, i as usize)));
        proof {
            let ret = Self { start: va, len: len, view: seq };
            assert(ret.start + ret.len * 4096 < usize::MAX);
            assert(spec_va_4k_valid(ret.start));
            
            // Length is correct by construction of Seq::new
            assert(ret@.len() == ret.len);
            
            // Use va_range_lemma to prove no duplicates
            va_range_lemma();
            assert(ret@.no_duplicates()) by {
                assert(forall|i: int, j: int| 
                    0 <= i < ret@.len() && 0 <= j < ret@.len() && i != j ==> ret@[i] != ret@[j]) by {
                    assert(forall|i: usize, j: usize|
                        0 <= i < len && 0 <= j < len && i != j ==> 
                        spec_va_add_range(va, i) != spec_va_add_range(va, j)) by {
                        va_range_lemma();
                    }
                }
            }
            
            // All addresses are valid by precondition spec_va_4k_range_valid
            assert(forall|i: int| #![trigger ret@[i]] 0 <= i < ret.len ==> spec_va_4k_valid(ret@[i])) by {
                assert(forall|i: int| 0 <= i < ret.len ==> ret@[i] == spec_va_add_range(va, i as usize));
            }
            
            // View matches spec by construction
            assert(ret.view_match_spec()) by {
                assert(forall|i: usize| 0 <= i < ret.len ==> 
                    spec_va_add_range(ret.start, i) == ret@[i as int]);
            }
            
            // Now we can assert wf() since all components are proven
            assert(ret.wf());
        }
>>>>>>> REPLACE
```

#### [NR__spec_t__os_code_vc__lemma_concurrent_trs_induct](o-NR__spec_t__os_code_vc__lemma_concurrent_trs_induct-20251201-214130)

For this one, it would be related to `decrease`:

```
<<<<<<< SEARCH
            ==> pred(pre, post)
    ensures pred(pre, post)
{
}
=======
            ==> pred(pre, post)
    ensures pred(pre, post)
    decreases pidx
{
    if pidx == 0 {
        assert(post == pre);
        assert(pred(pre, post));
    } else {
        assert forall|state: os::State, step, lbl|
            concurrent_trs(pre, state, c, core, sub(pidx, 1))
            && os::next_step(c, state, post, step, lbl)
            && !step.is_actor_step(core)
        implies pred(pre, post) by {
            lemma_concurrent_trs_induct(pre, state, c, core, sub(pidx, 1), pred);
        };
        assert(pred(pre, post));
    }
}
>>>>>>> REPLACE
```

#### [OS__kernel__syscall_new_proc_with_iommu__impl0__syscall_new_proc_with_endpoint_iommu](o-OS__kernel__syscall_new_proc_with_iommu__impl0__syscall_new_proc_with_endpoint_iommu-20251202-072729)

The following change is considered as UNSAFE

```
<<<<<<< SEARCH
        self.proc_man.new_proc_with_endpoint_iommu(
            thread_ptr,
            endpoint_index,
            pt_regs,
            page_ptr_2,
            page_perm_2,
            page_ptr_3,
            page_perm_3,
            new_pcid,
            new_ioid,
        );

        self.range_create_and_share_mapping(proc_ptr, &va_range, page_ptr_2, &va_range);
=======
        self.proc_man.new_proc_with_endpoint_iommu(
            thread_ptr,
            endpoint_index,
            pt_regs,
            page_ptr_2,
            page_perm_2,
            page_ptr_3,
            page_perm_3,
            new_pcid,
            new_ioid,
        );

        proof {
            assert(self.proc_man.wf());
            assert(self.mem_man.wf());
            assert(self.page_alloc.wf());
            assert(self.mem_man.page_closure().disjoint(self.proc_man.page_closure()));
            assert(self.mem_man.page_closure() + self.proc_man.page_closure() == self.page_alloc.allocated_pages_4k());
            assert(self.page_alloc.mapped_pages_2m() =~= Set::empty());
            assert(self.page_alloc.mapped_pages_1g() =~= Set::empty());
            assert(self.page_alloc.allocated_pages_2m() =~= Set::empty());
            assert(self.page_alloc.allocated_pages_1g() =~= Set::empty());
            assert(self.page_alloc.container_map_4k@.dom() =~= self.proc_man.container_dom());
            assert(self.page_alloc.container_map_2m@.dom() =~= self.proc_man.container_dom());
            assert(self.page_alloc.container_map_1g@.dom() =~= self.proc_man.container_dom());
            assert(self.memory_wf());
            assert(self.mapping_wf());
            assert(self.pcid_ioid_wf());
            assert(self.page_mapping_wf());
            assert(self.wf());
        }
        self.range_create_and_share_mapping(proc_ptr, &va_range, page_ptr_2, &va_range);
>>>>>>> REPLACE
```

#### [IR__marshal_v__impl2__lemma_serialize_injective](o-IR__marshal_v__impl2__lemma_serialize_injective-20251126-203400)

This file is considered as UNSAFE: `o-IR__marshal_v__impl2__lemma_serialize_injective-20251126-203400/fix-a15-uselemma-candidate-1.rs`

#### [IR__marshal_v__impl3__lemma_serialize_injective](o-IR__marshal_v__impl3__lemma_serialize_injective-20251126-215955)o

This file is considered as UNSAFE: `o-IR__marshal_v__impl3__lemma_serialize_injective-20251126-215955/fix-a12-uselemma-candidate-1.rs`
