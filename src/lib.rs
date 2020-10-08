use std::any::{TypeId, Any};
use std::collections::HashMap;

#[derive(Debug)]
pub struct TypedMap(pub HashMap<TypeId, Box<dyn Any>>);

impl TypedMap {
    #[inline]
    pub fn new() -> Self {
        Self(HashMap::new())
    }

    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self(HashMap::with_capacity(capacity))
    }

    #[inline]
    pub fn capacity(&self) -> usize {
        self.0.capacity()
    }

    #[inline]
    pub fn insert<V: Any>(&mut self, v: V) -> Option<V> {
        self.0.insert(TypeId::of::<V>(), Box::new(v))
            .map(|x| x.downcast::<V>().ok())
            .and_then(|x| x.map(|y| *y))
    }

    #[inline]
    pub fn get<V: Any>(&self) -> Option<&V> {
        self.0.get(&TypeId::of::<V>())
            .map(|x| x.downcast_ref::<V>())
            .and_then(|x| x)
    }

    pub fn get_mut<V: Any>(&mut self) -> Option<&mut V> {
        self.0.get_mut(&TypeId::of::<V>())
            .map(|x| x.downcast_mut::<V>())
            .and_then(|x| x)
    }

    #[inline]
    pub fn remove<V: Any>(&mut self) -> Option<V> {
        self.0.remove(&TypeId::of::<V>())
            .map(|x| x.downcast::<V>().ok())
            .and_then(|x| x.map(|y| *y))
    }
}