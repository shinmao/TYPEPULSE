// cargo run --bin typepulse -- --crate-type lib tests/utility/typepulse_paths_discovery.rs
use std::ptr::NonNull;

struct PathsDiscovery;

impl PathsDiscovery {
    fn discover() {
        unsafe {
            // Strong bypasses
            std::ptr::read(12 as *const i32);
            (12 as *const i32).read();

            std::intrinsics::copy(12 as *const i32, 34 as *mut i32, 56);
            std::intrinsics::copy_nonoverlapping(12 as *const i32, 34 as *mut i32, 56);
            std::ptr::copy(12 as *const i32, 34 as *mut i32, 56);
            std::ptr::copy_nonoverlapping(12 as *const i32, 34 as *mut i32, 56);

            vec![12, 34].set_len(5678);
            std::vec::Vec::from_raw_parts(12 as *mut i32, 34, 56);

            // Weak bypasses
            std::mem::transmute::<_, *mut i32>(12 as *const i32);

            (12 as *mut i32).write(34);
            std::ptr::write(12 as *mut i32, 34);

            (12 as *const i32).as_ref();
            (12 as *mut i32).as_mut();

            let mut ptr = NonNull::new(1234 as *mut i32).unwrap();
            ptr.as_ref();
            ptr.as_mut();

            [12, 34].get_unchecked(0);
            [12, 34].get_unchecked_mut(0);

            std::ptr::slice_from_raw_parts(12 as *const i32, 34);
            std::ptr::slice_from_raw_parts_mut(12 as *mut i32, 34);
            std::slice::from_raw_parts(12 as *const i32, 34);
            std::slice::from_raw_parts_mut(12 as *mut i32, 34);

            // Generic function call
            std::intrinsics::drop_in_place(12 as *mut i32);
            std::ptr::drop_in_place(12 as *mut i32);
            (12 as *mut i32).drop_in_place();

            let st = vec![240, 159, 146, 150];
            std::str::from_utf8_unchecked(&st);

            let a: u8 = 1;
            let mut b: u8 = 1;
            std::ptr::read_unaligned(&a as *const u8 as *const u16);
            std::ptr::write_unaligned(&mut b as *mut u8 as *mut u16, 2);

            char::from_u32_unchecked(0x2764);
        }
    }
}