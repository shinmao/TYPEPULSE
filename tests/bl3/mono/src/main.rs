fn test<T>(a: *const T) {
    let b: *const bool = unsafe {
        std::mem::transmute(a)
    };
}

fn main() {
    let a: u8 = 0;
    test(&a as *const u8);
}
