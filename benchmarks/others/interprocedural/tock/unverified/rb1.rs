use vstd::prelude::*;
use vstd::view::View;

pub fn main() {}


verus! {
    pub open spec fn ex_saturating_sub_spec(a: int, b: int) -> (ret: nat)
    {
        if (a > b) {
            (a - b) as nat
        } else {
            0
        }
    }

    #[verifier::external_fn_specification]
    pub fn ex_saturating_sub(a: usize, b: usize) -> (ret: usize)
    ensures
        ex_saturating_sub_spec(a as int, b as int) == ret as int
    {
        a.saturating_sub(b)
    }

    pub trait Queue<T> {
        /// Returns true if there are any items in the queue, false otherwise.
        fn has_elements(&self) -> (ret: bool)
            requires
                self.inv()
            ensures
                self.inv()
        ;

        /// Returns true if the queue is full, false otherwise.
        fn is_full(&self) -> (ret: bool)
            requires
                self.inv()
            ensures
                self.inv()
        ;

        /// Returns how many elements are in the queue.
        fn len(&self) -> (ret: usize)
            requires
                self.inv()
            ensures
                self.inv()
        ;

        /// If the queue isn't full, add a new element to the back of the queue.
        /// Returns whether the element was added.
        fn enqueue(&mut self, val: T) -> (ret: bool)
            requires
                old(self).inv()
            ensures
                self.inv()
        ;

        /// Remove the element from the front of the queue.
        fn dequeue(&mut self) -> (ret: Option<T>)
            requires
                old(self).inv()
            ensures
                self.inv()
        ;

        /// Invariant for the queue.
        spec fn inv(&self) -> bool;

        spec fn capacity_spec(&self) -> nat;
    }

    pub struct RingBuffer<T> {
        ring: Vec<T>,
        head: usize,
        tail: usize,
    }

    impl<T: Copy> View for RingBuffer<T> {
        type V = Seq<T>;

        closed spec fn view(&self) -> Self::V {
            let len = if self.tail >= self.head {
                self.tail - self.head
            } else {
                self.ring.len() - self.head + self.tail
            };

            Seq::new(len as nat, |i| {
                let index = (self.head + i) % self.ring.len() as int;
                self.ring[index]
            })
        }
    }

    impl<T: Copy> Queue<T> for RingBuffer<T> {
        closed spec fn inv(&self) -> bool
        {
            &&& self.head < self.ring.len()
            &&& self.tail < self.ring.len()
            &&& self.ring.len() > 1
        }

        closed spec fn capacity_spec(&self) -> nat
        {
            (self.ring.len() - 1) as nat
        }

        fn has_elements(&self) -> (result: bool)
            ensures
                result == (self@.len() != 0),
        {
            self.head != self.tail
        }

        fn is_full(&self) -> (ret: bool)
            ensures
                ret == (self@.len() == self.capacity_spec())
        {
            self.head == ((self.tail + 1) % self.ring.len())
        }

        fn len(&self) -> (ret: usize)
            ensures
                ret == self@.len(),
        {
            if self.tail > self.head {
                self.tail - self.head
            } else if self.tail < self.head {
                (self.ring.len() - self.head) + self.tail
            } else {
                // head equals tail, length is zero
                0
            }
        }

        fn enqueue(&mut self, val: T) -> (succ: bool)
            ensures
                old(self)@.len() == old(self).capacity_spec() <==> !succ, /* Full failed iff. */
                self.capacity_spec() == old(self).capacity_spec(), /* Capacity unchanged */
                succ == (self@.len() == old(self)@.len() + 1), /* Length increment, we need it here to avoid recommendation not met below */
                succ ==> (self@.len() <= self.capacity_spec()), /* No exceeds capacity */
                succ ==> (self@.last() == val), /* Push to last */
                forall |i: int| 0 <= i < old(self)@.len() ==> self@[i] == old(self)@[i], /* Prior unchanged */
        {
            if self.is_full() {
                // Incrementing tail will overwrite head
                false
            } else {
                self.ring.set(self.tail, val);
                self.tail = (self.tail + 1) % self.ring.len();
                true
            }
        }

        fn dequeue(&mut self) -> (ret: Option<T>)
            ensures
                self.capacity_spec() == old(self).capacity_spec(), /* Capacity unchanged */
                old(self)@.len() == 0 <==> ret == None::<T>, /* Empty failed iff. */
                old(self)@.len() > 0 <==> ret != None::<T>, /* Non-empty succ iff. */
                if let Some(val) = ret {
                    &&& self@.len() == old(self)@.len() - 1 /* Succ condition */
                    &&& val == old(self)@.first() /* Return first */
                } else {
                    self@.len() == old(self)@.len() /* Failed condition */
                },
        {
            if self.has_elements() {
                let val = self.ring[self.head];
                self.head = (self.head + 1) % self.ring.len();
                Some(val)
            } else {
                None
            }
        }
    }

    impl<T: Copy> RingBuffer<T> {
        pub fn new(ring: Vec<T>) -> (ret: RingBuffer<T>)
            requires
                ring.len() > 1
            ensures
                ret.capacity_spec() == ring.len() as nat - 1,
                ret@.len() == 0,
                ret.inv(),
        {
            RingBuffer {
                head: 0,
                tail: 0,
                ring,
            }
        }

        /// Returns the number of elements that can be enqueued until the ring buffer is full.
        pub fn available_len(&self) -> (ret: usize)
            requires
                self.inv()
        {
            // The maximum capacity of the queue is ring.len - 1, because head == tail for the empty
            // queue.
            self.ring.len().saturating_sub(1 + Queue::len(self))
        }
    }

    #[verifier::loop_isolation(false)]
    fn test_enqueue_dequeue_generic(len: usize, value: i32, iterations: usize)
        requires
            len < usize::MAX - 1,
            iterations * 2 < usize::MAX,
    {
        let mut ring: Vec<i32> = Vec::new();

        if len == 0 {
            return;
        }

        for i in 0..(len + 1)
        {
            ring.push(0);
        }

        let mut buf = RingBuffer::new(ring);

        for _ in 0..2 * iterations
        {
            let enqueue_res = buf.enqueue(value);
            assert(enqueue_res);

            let buf_len = buf.len();
            assert(buf_len == 1);

            let has_elements = buf.has_elements();
            assert(has_elements);

            let dequeue_res = buf.dequeue();
            assert(dequeue_res =~= Some(value));

            let buf_len = buf.len();
            assert(buf_len == 0);

            let has_elements = buf.has_elements();
            assert(!has_elements);
        }
    }
}