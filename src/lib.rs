use std::any::{TypeId, Any};
use std::collections::{HashMap, hash_map};
use std::collections::hash_map::IterMut;

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
            .map(|x| x.downcast().ok())
            .and_then(|x| x.map(|y| *y))
    }

    #[inline]
    pub fn get<V: Any>(&self) -> Option<&V> {
        self.0.get(&TypeId::of::<V>())
            .map(|x| x.downcast_ref())
            .and_then(|x| x)
    }

    pub fn get_mut<V: Any>(&mut self) -> Option<&mut V> {
        self.0.get_mut(&TypeId::of::<V>())
            .map(|x| x.downcast_mut())
            .and_then(|x| x)
    }

    #[inline]
    pub fn remove<V: Any>(&mut self) -> Option<V> {
        self.0.remove(&TypeId::of::<V>())
            .map(|x| x.downcast().ok())
            .and_then(|x| x.map(|y| *y))
    }

    #[inline]
    pub fn entry<'a, V: Any + 'a>(&mut self) -> Entry<'a, V> {
        match self.0.entry(TypeId::of::<V>()) {
            hash_map::Entry::Occupied(f) => Entry::Occupied(OccupiedEntry { inner: f }),
            hash_map::Entry::Vacant(f) => Entry::Vacant(VacantEntry { inner: f })
        }
    }

    pub fn iter(&self) -> Iter<'_> {
        Iter { inner: self.0.iter() }
    }

    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.0.shrink_to_fit()
    }
}

pub enum Entry<'a, V: 'a> {
    Occupied(OccupiedEntry<'a, V>),
    Vacant(VacantEntry<'a, V>),
}

pub struct OccupiedEntry<'a, V: 'a> {
    inner: hash_map::OccupiedEntry<'a, TypeId, Box<dyn Any>>
}

impl <'a, V: 'a> OccupiedEntry<'a, V> {
    const CAST_EXPECT_MESSAGE: &'static str = "Couldn't downcast to V";

    #[inline]
    pub fn key(&self) -> &TypeId {
        self.inner.key()
    }

    #[inline]
    pub fn insert(&mut self, value: V) -> V {
        self.inner.insert(Box::new(value))
    }

    #[inline]
    pub fn remove(self) -> V {
        *self.inner.remove()
            .downcast()
            .expect(Self::CAST_EXPECT_MESSAGE)
    }

    #[inline]
    pub fn get(&self) -> &V {
        self.inner.get()
            .downcast_ref()
            .expect(Self::CAST_EXPECT_MESSAGE)
    }

    #[inline]
    pub fn get_mut(&mut self) -> &mut V {
        self.inner.get_mut()
            .downcast_mut()
            .expect(Self::CAST_EXPECT_MESSAGE)
    }

    #[inline]
    pub fn into_mut(self) -> &'a mut V {
        self.inner.into_mut()
            .downcast_mut()
            .expect(Self::CAST_EXPECT_MESSAGE)
    }
}

pub struct VacantEntry<'a, V: 'a> {
    inner: hash_map::VacantEntry<'a, TypeId, Box<dyn Any>>
}

impl <'a, V: 'a> VacantEntry<'a, V> {
    #[inline]
    pub fn insert(self, default: V) -> &'a mut V {
        self.inner.insert(Box::new(default))
            .as_mut()
            .downcast_mut()
            .expect("Couldn't downcast to V")
    }

    #[inline]
    pub fn key(&self) -> &TypeId {
        self.inner.key()
    }
}

impl <'a, V: 'a> Entry<'a, V> {
    #[inline]
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default),
        }
    }

    #[inline]
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(default()),
        }
    }

    #[inline]
    pub fn key(&self) -> &TypeId {
        match *self {
            Entry::Occupied(ref entry) => entry.key(),
            Entry::Vacant(ref entry) => entry.key(),
        }
    }

    #[inline]
    pub fn and_modify<F: FnOnce(&mut V)>(self, f: F) -> Self {
        match self {
            Entry::Occupied(mut entry) => {
                f(entry.get_mut());
                Entry::Occupied(entry)
            }
            Entry::Vacant(entry) => Entry::Vacant(entry),
        }
    }
}

impl <'a, V: 'a + Default> Entry<'a, V> {
    #[inline]
    pub fn or_default(self) -> &'a mut V {
        match self {
            Entry::Occupied(entry) => entry.into_mut(),
            Entry::Vacant(entry) => entry.insert(Default::default()),
        }
    }
}

pub struct Iter<'a> {
    inner: hash_map::Iter<'a, TypeId, Box<dyn Any>>
}

impl <'a> Iterator for Iter<'a> {
    type Item = (&'a TypeId, &'a Box<dyn Any>);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner
            .next()
    }
}

impl <'a> IntoIterator for TypedMap {
    type Item = (&'a TypeId, &'a Box<dyn Any>);
    type IntoIter = Iter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}