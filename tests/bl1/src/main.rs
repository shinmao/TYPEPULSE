fn risky_cast_III() {
    let a: [u8; 5] = [1; 5];
    println!("{}", unsafe { *(a[1..4].as_ptr() as *mut u32) });
}


fn risky_cast_II(val: *const i32) -> *const i64 {
    val as *const i64
}

fn risky_cast(val: &i32) -> &i64 {
    let t = val as *const i32 as *const i64;
    unsafe { &*t }
}

fn risky_transmute_II<'a>(val: &'a i32, val2: &'a i64) -> &'a i64 {
    let t: &i64 = unsafe { core::mem::transmute(val) };
    val2
}

fn risky_transmute(val: *const i32) -> *const i64{
    let t: *const i64 = unsafe {
        std::mem::transmute(val)
    };
    t
}

fn safe_transmute(val: &i64) -> &i32 {
    unsafe { core::mem::transmute(val) }
}

fn main() {
    let a: i32 = 3;
}
