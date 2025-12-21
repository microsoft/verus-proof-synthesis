# Log:  A proven-correct log using persistent memory

## Overview

A `LogImpl` implements a log that can be atomically appended to.
The log is stored on a persistent memory region. The
implementation handles crash consistency, ensuring that even if
the process or machine crashes, the log acts like a log across
the crashes.

The implementation handles bit corruption on the persistent
memory, but only for the implementation's internal metadata. If
you want to be sure that *data* you wrote to the log isn't
corrupted when you read it back out, you should include your own
corruption-detecting information like a CRC. You can be confident
that the implementation read your data from the same place on
persistent memory where it was stored, but the data still might
have gotten corrupted on that memory.

## Using the library

To create a `LogImpl`, you need an object satisfying the
`PersistentMemoryRegion` trait, i.e., one implementing a
persistent-memory region. To set up a persistent memory object to
store an initial empty multilog, you call `LogImpl::setup`.
For instance, here's code to first create a
`PersistentMemoryRegion` out of volatile memory mocking
persistent memory, then to set up a log on them.

```
let region_size = 1024;
if let Ok(mut pm_region) =
    VolatileMemoryMockingPersistentMemoryRegion::new_mock_only_for_use_in_testing(region_size) {
   if let Ok(capacity, log_id) = LogImpl::setup(&mut pm_region) {
       println!("Log {} is set up with capacity {}", log_id, capacity);
   }
}
```

Remember that such setup is only intended to be run a single time.
Once you've set up a log, you shouldn't set it up again as
that will clear its state.

Once you've set up a log, you can start using it. A log is only
intended to be used by one process at a time. But if the process
or the machine crashes, it's fine to start using it again.
Indeed, that's the whole point: the most interesting verified
property of this code is that the log acts consistently like
a log even across crashes.

To start using a log, run `LogImpl::start`, passing the
persistent-memory region and the log ID, as in the following
example:

```
match LogImpl::start(pm_region, log_id) {
    Ok(mut log) => ...,
    Err(e) => ...,
}
```

To use a log, you can do five operations: tentatively append,
commit, read, advance head, and get information. Here's a
description of them all:

To tentatively append some data to the end of the log, use
`LogImpl::tentatively_append`. For example, the following
code tentatively appends [30, 42, 100] to the log:

```
let mut v: Vec<u8> = Vec::<u8>::new();
v.push(30); v.push(42); v.push(100);
if let Ok(pos) = log.tentatively_append(v.as_slice()) {
    if let Ok((head, tail, capacity)) = log.get_head_tail_and_capacity(0) {
        assert(head == 0);
        assert(tail == 0); // it's only tentative, so tail unchanged
    }
}
```

(That example also shows an example of the get-information call.)
Note that tentatively appending doesn't actually append to the
log, so the tail doesn't go up. It puts the append operation
inside of the current append transaction, which will be aborted
if the machine crashes before you commit the transaction. It will
also be aborted if the process accessing the log via a `LogImpl`
crashes. You can tentatively append to the log multiple times
before committing.

To atomically commit all tentative appends in the current append
transaction, use `LogImpl::commit`, as in the following example:

```
if let Ok(_) = log.commit() {
    if let Ok((head, tail, capacity)) = multilog.get_head_tail_and_capacity() {
        assert(head == 0);
        assert(tail == 3);
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
`LogImpl::read`, as in the following example:

```
if let Ok((bytes)) = log.read(1, 2) {
    assert(bytes.len() == 2);
    assert(pm_region.constants().impervious_to_corruption ==> bytes[0] == 42);
}
```

Note, as discussed before, that the bytes returned might be
corruptions of the data you appended, since the implementation of
the log only checks for corruption of its own internal metadata.
If you want to use the bytes, we suggest including a CRC and
checking that CRC after any read.

If the memory storing the log is getting too full, you'll need to
advance the log's head with `LogImpl::advance_head`. This doesn't
affect the logical contents of the log or the positions of bytes
in the log, but does restrict you from reading earlier than the
new head. So, for instance, if you advance the head from 0 to
1000, you can still read byte #1042 by reading from position #1042.
You just can't read byte #42 anymore without getting an error
return value.

The advance-head operation is not tentative, so it doesn't need a
commit. By the time the operation returns, it will have
definitively happened, and that head advancement will survive a
subsequent crash.

The advance-head operation is atomic. That is, either the head
advances or it doesn't. Even if there's an intermediate crash,
the log will either be in a state where the advance-head happened
or a state where it didn't happen.

Here's an example of a call to `advance_head`:

```
if let Ok(()) = log.advance_head(0, 2) {
    if let Ok((head, tail, capacity)) = log.get_head_tail_and_capacity() {
        assert(head == 2);
        assert(tail == 3);
    }
    if let Ok((bytes)) = log.read(2, 1) {
        assert(pm_region.constants().impervious_to_corruption ==> bytes[0] == 100);
    }
    let e = multilog.read(0, 1);
    assert(e == Result::<Vec<u8>, LogErr>::Err(LogErr::CantReadBeforeHead{head: 2}));
}
```

## Code organization

The code is organized into the following files. Files ending in
`_t.rs` are trusted specifications (e.g., for the semantics of
each log operation) that must be audited and read to understand
the semantics being proven. Files ending in `_v.rs` are verified
and untrusted and so do not have to be read to have confidence in
the correctness of the code.

<!-- * `lib.rs` packages this crate as a library -->
* `logspec_t.rs` specifies the correct behavior of an abstract log,
  e.g., what should happen during a call to `tentatively_append`
* `logimpl_t.rs` implements `LogImpl`, the main type used by
  clients of this library
* `logimpl_v.rs` implements `UntrustedLogImpl`, verified for
  correctness and invoked by `LogImpl` methods
* `inv_v.rs` provides invariants of the log code and proofs about those
  invariants
* `layout_v.rs` provides constants, functions, and proofs about how the
  log implementation lays out its metadata and data in persistent memory
* `append_v.rs` provides helper lemmas used by the log code to
  prove that tentative appends are done correctly
* `setup_v.rs` implements subroutines called when the log code is
  setting up a collection of persistent memory regions to act as a multilog
* `start_v.rs` implements subroutines called when the log code is
  starting up, either immediately after setup or to recover after a crash

## Example

Here's an example of a program that uses a `LogImpl`:

```
fn test_log_on_memory_mapped_file() -> Option<()>
{
    let region_size = 1024;

    // Create the memory out of a single file.
    let file_name = vstd::string::new_strlit("test_log");
    #[cfg(target_os = "windows")]
    let mut pm_region = FileBackedPersistentMemoryRegion::new(
        &file_name, MemoryMappedFileMediaType::SSD,
        region_size,
        FileCloseBehavior::TestingSoDeleteOnClose
    ).ok()?;
    #[cfg(target_os = "linux")]
    let mut pm_region = FileBackedPersistentMemoryRegion::new(
        &file_name,
        region_size,
        PersistentMemoryCheck::DontCheckForPersistentMemory,
    ).ok()?;

    // Set up the memory region to contain a log. The capacity will be less than
    // the file size because a few bytes are needed for metadata.
    let (capacity, log_id) = LogImpl::setup(&mut pm_region).ok()?;
    runtime_assert(capacity <= 1024);

    // Start accessing the log.
    let mut log = LogImpl::start(pm_region, log_id).ok()?;

    // Tentatively append [30, 42, 100] to the log.
    let mut v: Vec<u8> = Vec::<u8>::new();
    v.push(30); v.push(42); v.push(100);
    let pos = log.tentatively_append(v.as_slice()).ok()?;
    runtime_assert(pos == 0);

    // Note that a tentative append doesn't actually advance the tail. That
    // doesn't happen until the next commit.
    let (head, tail, _capacity) = log.get_head_tail_and_capacity().ok()?;
    runtime_assert(head == 0);
    runtime_assert(tail == 0);

    // Now commit the tentative appends. This causes the log to have tail 3.
    if log.commit().is_err() {
        runtime_assert(false); // can't fail
    }
    match log.get_head_tail_and_capacity() {
        Ok((head, tail, capacity)) => {
            runtime_assert(head == 0);
            runtime_assert(tail == 3);
        },
        _ => runtime_assert(false) // can't fail
    }

    // We read the 2 bytes starting at position 1 of the log. We should
    // read bytes [42, 100]. This is only guaranteed if the memory
    // wasn't corrupted.
    if let Ok(bytes) = log.read(1, 2) {
        runtime_assert(bytes.len() == 2);
        assert(log.constants().impervious_to_corruption ==> bytes[0] == 42);
    }

    // We now advance the head of the log to position 2. This causes the
    // head to become 2 and the tail stays at 3.
    match log.advance_head(2) {
        Ok(()) => runtime_assert(true),
        _ => runtime_assert(false) // can't fail
    }
    match log.get_head_tail_and_capacity() {
        Ok((head, tail, capacity)) => {
            runtime_assert(head == 2);
            runtime_assert(tail == 3);
        },
        _ => runtime_assert(false) // can't fail
    }

    // If we read from position 2 of the log, we get the same thing we
    // would have gotten before the advance-head operation.
    if let Ok(bytes) = log.read(2, 1) {
        assert(log.constants().impervious_to_corruption ==> bytes[0] == 100);
    }

    // But if we try to read from position 0, we get an
    // error because we're not allowed to read from before the head.
    match log.read(0, 1) {
        Err(LogErr::CantReadBeforeHead{head}) => runtime_assert(head == 2),
        _ => runtime_assert(false) // can't succeed, and can't fail with any other error
    }
    Some(())
}
```
