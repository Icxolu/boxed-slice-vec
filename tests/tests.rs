use boxed_slice_vec::CapacityError;
use boxed_slice_vec::FixedVec;
use matches::assert_matches;

#[test]
fn test_simple() {
    use std::ops::Add;

    let mut vec: FixedVec<Vec<i32>> = FixedVec::with_capacity(3);

    vec.push(vec![1, 2, 3, 4]);
    vec.push(vec![10]);
    vec.push(vec![-1, 13, -2]);

    for elt in &vec {
        assert_eq!(elt.iter().fold(0, Add::add), 10);
    }

    let sum_len = vec.into_iter().map(|x| x.len()).fold(0, Add::add);
    assert_eq!(sum_len, 8);
}

#[test]
fn test_capacity_left() {
    let mut vec = FixedVec::<usize>::with_capacity(4);
    assert_eq!(vec.remaining_capacity(), 4);
    vec.push(1);
    assert_eq!(vec.remaining_capacity(), 3);
    vec.push(2);
    assert_eq!(vec.remaining_capacity(), 2);
    vec.push(3);
    assert_eq!(vec.remaining_capacity(), 1);
    vec.push(4);
    assert_eq!(vec.remaining_capacity(), 0);
}

#[test]
fn test_extend_from_slice() {
    let mut vec = FixedVec::<usize>::with_capacity(10);

    vec.try_extend_from_slice(&[1, 2, 3]).unwrap();
    assert_eq!(vec.len(), 3);
    assert_eq!(&vec[..], &[1, 2, 3]);
    assert_eq!(vec.pop(), Some(3));
    assert_eq!(&vec[..], &[1, 2]);
}

#[test]
fn test_extend_from_slice_error() {
    let mut vec = FixedVec::<usize>::with_capacity(10);

    vec.try_extend_from_slice(&[1, 2, 3]).unwrap();
    let res = vec.try_extend_from_slice(&[0; 8]);
    assert_matches!(res, Err(_));

    let mut vec = FixedVec::<usize>::with_capacity(0);
    let res = vec.try_extend_from_slice(&[0; 1]);
    assert_matches!(res, Err(_));
}

#[test]
fn test_u16_index() {
    const N: usize = 4096;
    let mut vec = FixedVec::with_capacity(N);
    for _ in 0..N {
        assert!(vec.try_push(1u8).is_ok());
    }
    assert!(vec.try_push(0).is_err());
    assert_eq!(vec.len(), N);
}

#[test]
fn test_iter() {
    let mut iter = FixedVec::from([1, 2, 3]).into_iter();
    assert_eq!(iter.size_hint(), (3, Some(3)));
    assert_eq!(iter.next_back(), Some(3));
    assert_eq!(iter.next(), Some(1));
    assert_eq!(iter.next_back(), Some(2));
    assert_eq!(iter.size_hint(), (0, Some(0)));
    assert_eq!(iter.next_back(), None);
}

#[test]
fn test_drop() {
    use std::cell::Cell;

    let flag = &Cell::new(0);

    #[derive(Clone)]
    struct Bump<'a>(&'a Cell<i32>);

    impl<'a> Drop for Bump<'a> {
        fn drop(&mut self) {
            let n = self.0.get();
            self.0.set(n + 1);
        }
    }

    {
        let mut array = FixedVec::with_capacity(128);
        array.push(Bump(flag));
        array.push(Bump(flag));
    }
    assert_eq!(flag.get(), 2);

    // test something with the nullable pointer optimization
    flag.set(0);

    {
        let mut array = FixedVec::with_capacity(3);
        array.push(vec![Bump(flag)]);
        array.push(vec![Bump(flag), Bump(flag)]);
        array.push(vec![]);
        let push4 = array.try_push(vec![Bump(flag)]);
        assert_eq!(flag.get(), 0);
        drop(push4);
        assert_eq!(flag.get(), 1);
        drop(array.pop());
        assert_eq!(flag.get(), 1);
        drop(array.pop());
        assert_eq!(flag.get(), 3);
    }

    assert_eq!(flag.get(), 4);

    // test cloning into_iter
    flag.set(0);
    {
        let mut array = FixedVec::with_capacity(3);
        array.push(Bump(flag));
        array.push(Bump(flag));
        array.push(Bump(flag));
        let mut iter = array.into_iter();
        assert_eq!(flag.get(), 0);
        iter.next();
        assert_eq!(flag.get(), 1);
        let clone = iter.clone();
        assert_eq!(flag.get(), 1);
        drop(clone);
        assert_eq!(flag.get(), 3);
        drop(iter);
        assert_eq!(flag.get(), 5);
    }
}

#[test]
fn test_drop_panics() {
    use std::cell::Cell;
    use std::panic::catch_unwind;
    use std::panic::AssertUnwindSafe;

    let flag = &Cell::new(0);

    struct Bump<'a>(&'a Cell<i32>);

    // Panic in the first drop
    impl<'a> Drop for Bump<'a> {
        fn drop(&mut self) {
            let n = self.0.get();
            self.0.set(n + 1);
            if n == 0 {
                panic!("Panic in Bump's drop");
            }
        }
    }
    // check if rust is new enough
    flag.set(0);
    {
        let array = vec![Bump(flag), Bump(flag)];
        let res = catch_unwind(AssertUnwindSafe(|| {
            drop(array);
        }));
        assert!(res.is_err());
    }

    if flag.get() != 2 {
        println!("test_drop_panics: skip, this version of Rust doesn't continue in drop_in_place");
        return;
    }

    flag.set(0);
    {
        let mut array = FixedVec::with_capacity(128);
        array.push(Bump(flag));
        array.push(Bump(flag));
        array.push(Bump(flag));

        let res = catch_unwind(AssertUnwindSafe(|| {
            drop(array);
        }));
        assert!(res.is_err());
    }
    // Check that all the elements drop, even if the first drop panics.
    assert_eq!(flag.get(), 3);

    flag.set(0);
    {
        let mut array = FixedVec::with_capacity(16);
        array.push(Bump(flag));
        array.push(Bump(flag));
        array.push(Bump(flag));
        array.push(Bump(flag));
        array.push(Bump(flag));

        let i = 2;
        let tail_len = array.len() - i;

        let res = catch_unwind(AssertUnwindSafe(|| {
            array.truncate(i);
        }));
        assert!(res.is_err());
        // Check that all the tail elements drop, even if the first drop panics.
        assert_eq!(flag.get(), tail_len as i32);
    }
}

#[test]
fn test_extend() {
    let mut range = 0..10;

    let mut array = FixedVec::with_capacity(5);
    array.extend(range.by_ref().take(5));
    assert_eq!(&array[..], &[0, 1, 2, 3, 4]);
    assert_eq!(range.next(), Some(5));

    array.extend(range.by_ref().take(0));
    assert_eq!(range.next(), Some(6));

    let mut array = FixedVec::with_capacity(10);
    array.extend(0..3);
    assert_eq!(&array[..], &[0, 1, 2]);
    array.extend(3..5);
    assert_eq!(&array[..], &[0, 1, 2, 3, 4]);
}

#[should_panic]
#[test]
fn test_extend_capacity_panic_1() {
    let mut range = 0..10;

    let mut array = FixedVec::with_capacity(5);
    array.extend(range.by_ref());
}

#[should_panic]
#[test]
fn test_extend_capacity_panic_2() {
    let mut range = 0..10;

    let mut array = FixedVec::with_capacity(5);
    array.extend(range.by_ref().take(5));
    assert_eq!(&array[..], &[0, 1, 2, 3, 4]);
    assert_eq!(range.next(), Some(5));
    array.extend(range.by_ref().take(1));
}

#[test]
fn test_is_send_sync() {
    let data = FixedVec::<Vec<i32>>::with_capacity(0);
    &data as &dyn Send;
    &data as &dyn Sync;
}

#[test]
#[should_panic]
fn test_drop_panic() {
    struct DropPanic;

    impl Drop for DropPanic {
        fn drop(&mut self) {
            panic!("drop");
        }
    }

    let mut array = FixedVec::with_capacity(1);
    array.push(DropPanic);
}

#[test]
#[should_panic]
fn test_drop_panic_into_iter() {
    struct DropPanic;

    impl Drop for DropPanic {
        fn drop(&mut self) {
            panic!("drop");
        }
    }

    let mut array = FixedVec::with_capacity(1);
    array.push(DropPanic);
    array.into_iter();
}

#[test]
fn test_insert() {
    let mut v = FixedVec::with_capacity(0);
    assert_matches!(v.try_push(1), Err(_));

    let mut v = FixedVec::with_capacity(3);
    v.insert(0, 0);
    v.insert(1, 1);
    //let ret1 = v.try_insert(3, 3);
    //assert_matches!(ret1, Err(InsertError::OutOfBounds(_)));
    assert_eq!(&v[..], &[0, 1]);
    v.insert(2, 2);
    assert_eq!(&v[..], &[0, 1, 2]);

    let ret2 = v.try_insert(1, 9);
    assert_eq!(&v[..], &[0, 1, 2]);
    assert_matches!(ret2, Err(_));

    let mut v = FixedVec::from([2]);
    assert_matches!(v.try_insert(0, 1), Err(CapacityError { .. }));
    assert_matches!(v.try_insert(1, 1), Err(CapacityError { .. }));
    //assert_matches!(v.try_insert(2, 1), Err(CapacityError { .. }));
}

#[test]
fn array_clone_from() {
    let mut v = FixedVec::with_capacity(4);
    v.push(vec![1, 2]);
    v.push(vec![3, 4, 5]);
    v.push(vec![6]);
    let reference = v.to_vec();
    let mut u = FixedVec::with_capacity(4);
    u.clone_from(&v);
    assert_eq!(&u, &reference[..]);

    let mut t = FixedVec::with_capacity(4);
    t.push(vec![97]);
    t.push(vec![]);
    t.push(vec![5, 6, 2]);
    t.push(vec![2]);
    t.clone_from(&v);
    assert_eq!(&t, &reference[..]);
    t.clear();
    t.clone_from(&v);
    assert_eq!(&t, &reference[..]);
}

#[test]
fn test_insert_at_length() {
    let mut v = FixedVec::with_capacity(8);
    let result1 = v.try_insert(0, "a");
    let result2 = v.try_insert(1, "b");
    assert!(result1.is_ok() && result2.is_ok());
    assert_eq!(&v[..], &["a", "b"]);
}

#[should_panic]
#[test]
fn test_insert_out_of_bounds() {
    let mut v = FixedVec::with_capacity(8);
    let _ = v.try_insert(1, "test");
}

#[test]
fn test_drop_in_insert() {
    use std::cell::Cell;

    let flag = &Cell::new(0);

    struct Bump<'a>(&'a Cell<i32>);

    impl<'a> Drop for Bump<'a> {
        fn drop(&mut self) {
            let n = self.0.get();
            self.0.set(n + 1);
        }
    }

    flag.set(0);

    {
        let mut array = FixedVec::with_capacity(2);
        array.push(Bump(flag));
        array.insert(0, Bump(flag));
        assert_eq!(flag.get(), 0);
        let ret = array.try_insert(1, Bump(flag));
        assert_eq!(flag.get(), 0);
        assert_matches!(ret, Err(_));
        drop(ret);
        assert_eq!(flag.get(), 1);
    }
    assert_eq!(flag.get(), 3);
}

#[test]
fn test_try_remove() {
    let mut v = FixedVec::with_capacity(4);
    let s = String::from;
    v.push(s("a"));
    v.push(s("b"));
    v.push(s("c"));
    v.push(s("d"));

    assert_eq!(v.try_remove(4), None);
    assert_eq!(v.try_remove(1), Some(s("b")));
    assert_eq!(v.try_remove(1), Some(s("c")));
    assert_eq!(v.try_remove(2), None);
    assert_eq!(&v[..], &["a", "d"]);
}

#[test]
fn test_sizes() {
    let v = FixedVec::from([0u8; 1 << 16]);
    assert_eq!(vec![0u8; v.len()], &v[..]);
}

#[test]
fn test_extend_zst() {
    let mut range = 0..10;
    #[derive(Copy, Clone, PartialEq, Debug)]
    struct Z; // Zero sized type

    let mut array = FixedVec::with_capacity(5);
    array.extend(range.by_ref().take(5).map(|_| Z));
    assert_eq!(&array[..], &[Z; 5]);
    assert_eq!(range.next(), Some(5));

    array.extend(range.by_ref().take(0).map(|_| Z));
    assert_eq!(range.next(), Some(6));

    let mut array = FixedVec::with_capacity(10);
    array.extend((0..3).map(|_| Z));
    assert_eq!(&array[..], &[Z; 3]);
    array.extend((3..5).map(|_| Z));
    assert_eq!(&array[..], &[Z; 5]);
    assert_eq!(array.len(), 5);
}

#[test]
fn test_from_vec() {
    let mut array: FixedVec<usize> = vec![0, 1, 2, 3, 4].into();
    assert_eq!(array.pop(), Some(4));
    assert_eq!(array.as_slice(), &[0, 1, 2, 3]);
}
