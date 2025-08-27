#[repr(C)]
#[derive(Copy, Clone)]
#[doc(hidden)]
pub struct TraitObject {
    pub data: *mut (),
    pub vtable: *mut (),
}

trait Person {
    fn weight(&self) -> i16;
}

impl Person {
    pub fn downcast_unchecked<T: Person>(self: Box<Self>) -> Box<T> {
        let trait_obj: TraitObject = std::mem::transmute(self);
        std::mem::transmute(trait_obj.data)
    }
}
