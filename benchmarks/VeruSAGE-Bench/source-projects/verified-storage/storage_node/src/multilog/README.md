# Multilog:  A proven-correct multilog using persistent memory

## Overview

A `MultiLogImpl` implements multiple logs that can be atomically
appended to. Each log is stored on its own persistent memory
region. The implementation handles crash consistency, ensuring
that even if the process or machine crashes, the multilog acts
like a multilog across the crashes.

The implementation handles bit corruption on the persistent
memory, but only for the implementation's internal metadata. If
you want to be sure that *data* you wrote to the multilog isn't
corrupted when you read it back out, you should include your own
corruption-detecting information like a CRC. You can be confident
that the implementation read your data from the same place on
persistent memory where it was stored, but the data still might
have gotten corrupted on that memory.

## Using the library

To create a `MultiLogImpl`, you need an object satisfying the
`PersistentMemoryRegions` trait, i.e., one implementing a list of
persistent-memory regions. The reason we take a single
`PersistentMemoryRegions` input rather than multiple
`PersistentMemory` inputs is to do efficient flushes to multiple
persistent memories at once. We anticipate that several persistent
memory regions will be on the same physical memory, and can thus be
efficiently flushed collectively with a single flush call.

To set up persistent memory objects to store an initial empty
multilog, you call `MultiLogImpl::setup`. For instance, here's
code to first create a `PersistentMemoryRegions` out of volatile
memory mocking persistent memory, then to set up a multilog on
them.

```
let mut region_sizes: Vec<u64> = Vec::<u64>::new();
region_sizes.push(4096);
region_sizes.push(1024);
if let Ok(mut pm_regions) =
    VolatileMemoryMockingPersistentMemoryRegions::new_mock_only_for_use_in_testing(region_sizes.as_slice()) {
   if let Ok(capacities, multilog_id) = MultiLogImpl::setup(&mut pm_regions) {
       println!("Multilog {} is set up with per-region capacities {:?}", multilog_id, capacities);
   }
}
```

Remember that such setup is only intended to be run a single time.
Once you've set up a multilog, you shouldn't set it up again as
that will clear its state. The number of logs in the multilog will
match the number of regions that you pass in, since it uses region
#`n` to store log #`n`.

Once you've set up a multilog, you can start using it. A multilog
is only intended to be used by one process at a time. But if the
process or the machine crashes, it's fine to start using it again.
Indeed, that's the whole point: the most interesting verified
property of this code is that the multilog acts consistently like
a multilog even across crashes.

To start using a multilog, run `MultiLogImpl::start`, passing the
persistent-memory regions and the multilog ID, as in the following
example:

```
match MultiLogImpl::start(pm_regions, multilog_id) {
    Ok(mut multilog) => ...,
    Err(e) => ...,
}
```

To use a multilog, you can do five operations: tentatively append,
commit, read, advance head, and get information. Here's a
description of them all:

To tentatively append some data to the end of log #n, use
`MultiLogImpl::tentatively_append`. For example, the following
code tentatively appends [30, 42, 100] to log #0 and then
tentatively appends [30, 42, 100, 152] to log #1:

```
let mut v: Vec<u8> = Vec::<u8>::new();
v.push(30); v.push(42); v.push(100);
if let Ok(pos) = multilog.tentatively_append(0, v.as_slice()) {
    if let Ok((head, tail, capacity)) = multilog.get_head_tail_and_capacity(0) {
        assert(head == 0);
        assert(tail == 0); // it's only tentative, so tail unchanged
    }
}
v.push(152);
multilog.tentatively_append(1, v.as_slice());
```

(That example also shows an example of the get-information call.)
Note that tentatively appending doesn't actually append to the
log, so the tail doesn't go up. It puts the append operation
inside of the current append transaction, which will be aborted if
the machine crashes before you commit the transaction. It will
also be aborted if the process accessing the multilog via a
`MultiLogImpl` crashes. You can tentatively append to one or more
logs before committing.

To atomically commit all tentative appends in the current append
transaction, use `MultiLogImpl::commit`, as in the following
example:

```
if let Ok(_) = multilog.commit() {
    if let Ok((head, tail, capacity)) = multilog.get_head_tail_and_capacity(0) {
        assert(head == 0);
        assert(tail == 3);
    }
    if let Ok((head, tail, capacity)) = multilog.get_head_tail_and_capacity(1) {
        assert(head == 0);
        assert(tail == 4);
    }
}
```

This, unlike `tentatively_append`, advances logs' tails.

Commit is atomic even with respect to crashes, so it logically
does all the tentative appends at once. So even if the machine
crashes in the middle of the commit operation, or if the process
that called `commit` crashes in the middle of the commit
operation, either all tentative appends will happen or none of
them will.

If a crash occurs in the middle of a commit but the tentative
appends aren't performed, those tentative appends are dropped and
a fresh empty append transaction is started. The same happens if
the crash occurs before you call `commit`.

Once you have data committed in the log, you can read it using
`MultiLogImpl::read`, as in the following example:

```
if let Ok((bytes)) = multilog.read(0, 1, 2) {
    assert(bytes.len() == 2);
    assert(pm_regions.constants().impervious_to_corruption ==> bytes[0] == 42);
}
```

Note, as discussed before, that the bytes returned might be
corruptions of the data you appended, since the implementation of
the multilog only checks for corruption of its own internal
metadata. If you want to use the bytes, we suggest including a CRC
and checking that CRC after any read.

If the memory storing the log is getting too full, you'll need to
advance the log's head with `MultiLogImpl::advance_head`.  This
doesn't affect the logical contents of the log or the positions of
bytes in the log, but does restrict you from reading earlier than
the new head. So, for instance, if you advance the head from 0 to
1000, you can still read byte #1042 by reading from position
#1042. You just can't read byte #42 anymore without getting an
error return value.

The advance-head operation is not tentative, so it doesn't need a
commit. By the time the operation returns, it will have
definitively happened, and that head advancement will survive a
subsequent crash.

The advance-head operation is atomic. That is, either the head
advances or it doesn't. Even if there's an intermediate crash, the
multilog will either be in a state where the advance-head happened
or a state where it didn't happen.

Here's an example of a call to `advance_head`:

```
if let Ok(()) = multilog.advance_head(0, 2) {
    if let Ok((head, tail, capacity)) = multilog.get_head_tail_and_capacity(0) {
        assert(head == 2);
        assert(tail == 3);
    }
    if let Ok((bytes)) = multilog.read(0, 2, 1) {
        assert(pm_regions.constants().impervious_to_corruption ==> bytes[0] == 100);
    }
    let e = multilog.read(0, 0, 1);
    assert(e == Result::<Vec<u8>, MultiLogErr>::Err(MultiLogErr::CantReadBeforeHead{head: 2}));
}
```

## Code organization

The code is organized into the following files. Files ending in `_t.rs` are
trusted specifications (e.g., of how persistent memory behaves and of how a
multilog should operate) that must be audited and read to understand the
semantics being proven. Files ending in `_v.rs` are verified and untrusted and
so do not have to be read to have confidence in the correctness of the code.

<!-- * `lib.rs` packages this crate as a library -->
* `multilogspec_t.rs` specifies the correct behavior of an abstract multilog,
  e.g., what should happen during a call to `tentatively_append`
* `multilogimpl_t.rs` implements `MultiLogImpl`, the main type used by
  clients of this library
* `multilogimpl_v.rs` implements `UntrustedMultiLogImpl`, verified for
  correctness and invoked by `MultiLogImpl` methods
* `inv_v.rs` provides invariants of the multilog code and proofs about those
  invariants
* `layout_v.rs` provides constants, functions, and proofs about how the
  multilog implementation lays out its metadata and data in persistent memory
* `append_v.rs` provides helper lemmas used by the multilog code to
  prove that tentative appends are done correctly
* `setup_v.rs` implements subroutines called when the multilog code is
  setting up a collection of persistent memory regions to act as a multilog
* `start_v.rs` implements subroutines called when the multilog code is
  starting up, either immediately after setup or to recover after a crash

## Example

Here's an example of a program that uses a `MultiLogImpl`:

```
fn test_multilog_on_memory_mapped_file() -> Option<()>
{
    // To test the multilog, we use files in the current directory that mock persistent-memory
    // regions. Here we use such regions, one of size 4096 and one of size 1024.
    let mut region_sizes: Vec<u64> = Vec::<u64>::new();
    region_sizes.push(4096);
    region_sizes.push(1024);

    // Create the multipersistent memory out of the two regions.
    let file_name = vstd::string::new_strlit("test_multilog");
    #[cfg(target_os = "windows")]
    let mut pm_regions = FileBackedPersistentMemoryRegions::new(
        &file_name,
        MemoryMappedFileMediaType::SSD,
        region_sizes.as_slice(),
        FileCloseBehavior::TestingSoDeleteOnClose
    ).ok()?;
    #[cfg(target_os = "linux")]
    let mut pm_regions = FileBackedPersistentMemoryRegions::new(
        &file_name,
        region_sizes.as_slice(),
        PersistentMemoryCheck::DontCheckForPersistentMemory,
    ).ok()?;

    // Set up the memory regions to contain a multilog. The capacities will be less
    // than 4096 and 1024 because a few bytes are needed in each region for metadata.
    let (capacities, multilog_id) = MultiLogImpl::setup(&mut pm_regions).ok()?;
    runtime_assert(capacities.len() == 2);
    runtime_assert(capacities[0] <= 4096);
    runtime_assert(capacities[1] <= 1024);

    // Start accessing the multilog.
    let mut multilog = MultiLogImpl::start(pm_regions, multilog_id).ok()?;

    // Tentatively append [30, 42, 100] to log #0 of the multilog.
    let mut v: Vec<u8> = Vec::<u8>::new();
    v.push(30); v.push(42); v.push(100);
    let pos = multilog.tentatively_append(0, v.as_slice()).ok()?;
    runtime_assert(pos == 0);

    // Note that a tentative append doesn't actually advance the tail. That
    // doesn't happen until the next commit.
    let (head, tail, _capacity) = multilog.get_head_tail_and_capacity(0).ok()?;
    runtime_assert(head == 0);
    runtime_assert(tail == 0);

    // Also tentatively append [30, 42, 100, 152] to log #1. This still doesn't
    // commit anything to the log.
    v.push(152);
    let pos = multilog.tentatively_append(1, v.as_slice()).ok()?;
    runtime_assert(pos == 0);

    // Now commit the tentative appends. This causes log #0 to have tail 3
    // and log #1 to have tail 4.
    if multilog.commit().is_err() {
        runtime_assert(false); // can't fail
    }
    match multilog.get_head_tail_and_capacity(0) {
        Ok((head, tail, capacity)) => {
            runtime_assert(head == 0);
            runtime_assert(tail == 3);
        },
        _ => runtime_assert(false) // can't fail
    }
    match multilog.get_head_tail_and_capacity(1) {
        Ok((head, tail, capacity)) => {
            runtime_assert(head == 0);
            runtime_assert(tail == 4);
        },
        _ => runtime_assert(false) // can't fail
    }

    // We read the 2 bytes starting at position 1 of log #0. We should
    // read bytes [42, 100]. This is only guaranteed if the memory
    // wasn't corrupted.
    if let Ok(bytes) = multilog.read(0, 1, 2) {
        runtime_assert(bytes.len() == 2);
        assert(multilog.constants().impervious_to_corruption ==> bytes[0] == 42);
    }

    // We now advance the head of log #0 to position 2. This causes the
    // head to become 2 and the tail stays at 3.
    match multilog.advance_head(0, 2) {
        Ok(()) => runtime_assert(true),
        _ => runtime_assert(false) // can't fail
    }
    match multilog.get_head_tail_and_capacity(0) {
        Ok((head, tail, capacity)) => {
            runtime_assert(head == 2);
            runtime_assert(tail == 3);
        },
        _ => runtime_assert(false) // can't fail
    }

    // If we read from position 2 of log #0, we get the same thing we
    // would have gotten before the advance-head operation.
    if let Ok(bytes) = multilog.read(0, 2, 1) {
        assert(multilog.constants().impervious_to_corruption ==> bytes[0] == 100);
    }

    // But if we try to read from position 0 of log #0, we get an
    // error because we're not allowed to read from before the head.
    match multilog.read(0, 0, 1) {
        Err(MultiLogErr::CantReadBeforeHead{head}) => runtime_assert(head == 2),
        _ => runtime_assert(false) // can't succeed, and can't fail with any other error
    }
    Some(())
}
```
