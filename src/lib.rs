use std::any::{Any, TypeId};
use std::collections::{hash_map, HashMap};
use std::marker::PhantomData;

/// A hetero container implemented with hashmap.
///
/// The hetero container can store any type that implements `Any` in one container.
/// ```
/// use hetero_container::HeteroContainer;
/// use std::any::TypeId;
///
/// let mut container = HeteroContainer::new();
///
/// // Insert difference types.
/// container.insert(10);
/// container.insert("foo");
///
/// assert_eq!(container.get::<i32>(), Some(&10));
/// assert_eq!(container.get::<&str>(), Some(&"foo"));
///
/// // Check for the specific one.
/// if !container.contains::<String>() {
///     println!("We got {} values, but String not found.", container.len());
/// }
///
/// for (type_id, any) in &container {
///     if any.is::<i32>() {
///         println!("i32: {}", any.downcast_ref::<i32>().unwrap())
///     }
/// }
/// ```
///
/// `HeteroContainer` also implements an [`Entry API`](#method.entry), which allows
/// for more complex methods of getting, setting, updating and removing keys and
/// their values:
///
/// ```
/// use hetero_container::HeteroContainer;
///
/// let mut container = HeteroContainer::new();
///
/// container.entry()
///     .or_insert("tom".to_string());
///
/// container.entry()
///     .or_insert_with(|| 128);
///
/// container.entry::<String>()
///     .and_modify(|mut x| x.push_str(" watson"));
/// ```
///
/// If you need to insert multiple values of the same type, please use `HashSet` with type.
/// ```
/// use hetero_container::HeteroContainer;
/// use std::collections::HashSet;
///
/// let mut container = HeteroContainer::new();
///
/// // Insert multiple strings
/// let mut strings = container.entry::<HashSet<String>>()
///     .or_insert(HashSet::new());
///
/// strings.insert("a".to_string());
/// strings.insert("b".to_string());
///
/// assert_eq!(container.get::<HashSet<String>>().map(|x| x.len()), Some(2));
/// ```
#[derive(Debug)]
pub struct HeteroContainer(HashMap<TypeId, Box<dyn Any>>);

impl HeteroContainer {
    /// Creates an empty `HeteroContainer`.
    ///
    /// The hetero container is initially created with a capacity of 0, so it will not allocate until it
    /// is first inserted into.
    ///
    /// # Examples
    /// ```
    /// use hetero_container::HeteroContainer;
    /// let mut container: HeteroContainer = HeteroContainer::new();
    /// ```
    #[inline]
    pub fn new() -> Self {
        Self(HashMap::new())
    }

    /// Creates an empty `HeteroContainer` with the specified capacity.
    ///
    /// The hetero container will be able to hold at least `capacity` elements without
    /// reallocating. If `capacity` is 0, the hetero container will not be allocate.
    ///
    /// # Examples
    /// ```
    /// use hetero_container::HeteroContainer;
    /// let mut container: HeteroContainer = HeteroContainer::with_capacity(10);
    /// ```
    #[inline]
    pub fn with_capacity(capacity: usize) -> Self {
        Self(HashMap::with_capacity(capacity))
    }

    /// Returns the number of elements the container can hold without reallocating.
    ///
    /// This number is a lower bound; the `HeteroContainer` might be able to hold
    /// more, but is guaranteed to be able to hold at least this many.
    ///
    /// # Examples
    /// ```
    /// use hetero_container::HeteroContainer;
    /// let container: HeteroContainer = HeteroContainer::with_capacity(100);
    /// assert!(container.capacity() >= 100);
    /// ```
    #[inline]
    pub fn capacity(&self) -> usize {
        self.0.capacity()
    }

    /// Returns the number of elements in the container.
    ///
    /// # Examples
    /// ```
    /// use hetero_container::HeteroContainer;
    ///
    /// let mut container = HeteroContainer::new();
    /// assert_eq!(container.len(), 0);
    /// container.insert("a");
    /// assert_eq!(container.len(), 1);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Inserts a value with type into the container.
    ///
    /// If the container did not have this value type present, [`None`] is returned.
    ///
    /// if the container did not have this value type presents, the value is updated, and the old
    /// value is returned.
    ///
    /// # Examples
    /// ```
    /// use hetero_container::HeteroContainer;
    ///
    /// let mut container = HeteroContainer::new();
    /// assert_eq!(container.insert(37), None);
    /// assert_eq!(container.is_empty(), false);
    ///
    /// container.insert(42);
    /// assert_eq!(container.insert(56), Some(42));
    /// assert_eq!(container.get::<i32>(), Some(&56))
    /// ```
    #[inline]
    pub fn insert<V: Any>(&mut self, v: V) -> Option<V> {
        self.0.insert(TypeId::of::<V>(), Box::new(v))
            .map(|x| x.downcast().ok())
            .and_then(|x| x.map(|y| *y))
    }

    /// Returns a reference to the value corresponding to the type.
    ///
    /// The type must implements [`Any`].
    ///
    /// # Examples
    /// ```
    /// use hetero_container::HeteroContainer;
    ///
    /// let mut container = HeteroContainer::new();
    /// container.insert(10);
    /// assert_eq!(container.get::<i32>(), Some(&10));
    /// assert_eq!(container.get::<String>(), None);
    /// ```
    #[inline]
    pub fn get<V: Any>(&self) -> Option<&V> {
        self.0.get(&TypeId::of::<V>())
            .map(|x| x.downcast_ref())
            .and_then(|x| x)
    }

    /// Returns a mutable reference to the value corresponding to the type.
    ///
    /// The type must be implements [`Any`].
    ///
    /// # Examples
    /// ```
    /// use hetero_container::HeteroContainer;
    ///
    /// let mut container = HeteroContainer::new();
    /// container.insert("a");
    /// if let Some(x) = container.get_mut::<&str>() {
    ///     *x = "b"
    /// }
    /// assert_eq!(container.get::<&str>(), Some(&"b"));
    /// ```
    pub fn get_mut<V: Any>(&mut self) -> Option<&mut V> {
        self.0.get_mut(&TypeId::of::<V>())
            .map(|x| x.downcast_mut())
            .and_then(|x| x)
    }

    /// Removes a value from the container, returning the value at the type if the type
    /// was previously in the container.
    ///
    /// The type must implements [`Any`].
    ///
    /// # Examples
    /// ```
    /// use hetero_container::HeteroContainer;
    ///
    /// let mut container = HeteroContainer::new();
    /// container.insert(10);
    /// assert_eq!(container.remove::<i32>(), Some(10));
    /// assert_eq!(container.remove::<i32>(), None);
    /// ```
    #[inline]
    pub fn remove<V: Any>(&mut self) -> Option<V> {
        self.0.remove(&TypeId::of::<V>())
            .map(|x| x.downcast().ok())
            .and_then(|x| x.map(|y| *y))
    }

    /// Gets the given type entry in the container for in-place manipulation.
    ///
    /// # Examples
    /// ```
    /// use hetero_container::HeteroContainer;
    ///
    /// let mut container = HeteroContainer::new();
    /// let v = container.entry()
    ///     .or_insert(0);
    ///
    /// *v *= 10;
    /// ```
    #[inline]
    pub fn entry<V: Any>(&mut self) -> Entry<'_, V> {
        match self.0.entry(TypeId::of::<V>()) {
            hash_map::Entry::Occupied(f) => Entry::Occupied(OccupiedEntry { inner: f , _phantom: PhantomData}, PhantomData),
            hash_map::Entry::Vacant(f) => Entry::Vacant(VacantEntry { inner: f, _phantom: PhantomData}, PhantomData),
        }
    }

    /// Returns `true` if the container contains a value for the specified type.
    #[inline]
    pub fn contains<T: Any>(&self) -> bool {
        self.get::<T>().is_some()
    }

    /// Returns `true` if the container contains no elements.
    ///
    /// # Examples
    /// ```
    /// use hetero_container::HeteroContainer;
    ///
    /// let mut a = HeteroContainer::new();
    /// assert!(a.is_empty());
    /// a.insert("a");
    /// assert!(!a.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// An iterator visiting all TypeId-Box<dyn Any> pairs in arbitrary order.
    /// The iterator element type is `(&'a TypeId, &'a Box<dyn Any>)`.
    ///
    /// # Examples
    /// ```
    /// use hetero_container::HeteroContainer;
    ///
    /// let mut container = HeteroContainer::new();
    /// container.insert(10);
    /// container.insert("foo");
    /// container.insert(1.0);
    ///
    /// for (type_id, value) in container.iter() {
    ///     println!("type_id: {:?} value: {:?}", type_id, value)
    /// }
    /// ```
    #[inline]
    pub fn iter(&self) -> Iter<'_> {
        Iter { inner: self.0.iter() }
    }

    /// An iterator visiting all TypeId-Box<dyn Any> pairs in arbitrary order,
    /// with mutable references to the values.
    /// The iterator elements type is `(&'a TypeId, &'a mut Box<dyn Any>)`.
    ///
    /// # Examples
    /// ```
    /// use hetero_container::HeteroContainer;
    ///
    /// let mut container = HeteroContainer::new();
    /// container.insert("a");
    /// container.insert(1);
    /// container.insert(2.0);
    ///
    /// for (_, val) in container.iter_mut() {
    ///     // I cannot find a good example to do here :(
    /// }
    /// ```
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_> {
        IterMut {
            inner: self.0.iter_mut()
        }
    }

    /// Shrinks the capacity of the container as much as possible. It will drop
    /// down as much as possible while maintaining the internal rules
    /// and possibly leaving some space in accordance with the resize policy.
    ///
    /// # Examples
    /// ```
    /// use hetero_container::HeteroContainer;
    ///
    /// let mut container: HeteroContainer = HeteroContainer::with_capacity(100);
    /// container.insert(1);
    /// container.insert("a");
    /// assert!(container.capacity() >= 100);
    /// container.shrink_to_fit();
    /// assert!(container.capacity() >= 2);
    /// ```
    #[inline]
    pub fn shrink_to_fit(&mut self) {
        self.0.shrink_to_fit()
    }
}

/// A view into a single entry in a container, which may either be vacant or occupied.
///
/// The `enum` is constructed from the [`entry`] method on [`HeteroContainer`].
///
/// [`entry`]: struct.HeteroContainer.html#method.entry
#[derive(Debug)]
pub enum Entry<'a, V> {
    /// An occupied entry.
    Occupied(OccupiedEntry<'a, V>, PhantomData<V>),

    /// A vacant entry.
    Vacant(VacantEntry<'a, V>, PhantomData<V>),
}

/// A view into an occupied entry in a `HeteroContainer`.
/// It is part of the [`Entry`] enum.
///
/// [`Entry`]: enum.Entry.html
#[derive(Debug)]
pub struct OccupiedEntry<'a, V> {
    inner: hash_map::OccupiedEntry<'a, TypeId, Box<dyn Any>>,
    _phantom: PhantomData<V>,
}

impl <'a, V: 'static> OccupiedEntry<'a, V> {
    const CAST_EXPECT_MESSAGE: &'static str = "Couldn't downcast to V";

    /// Gets a reference to the key in the container.
    ///
    /// # Examples
    /// ```
    /// use hetero_container::HeteroContainer;
    /// use std::any::TypeId;
    ///
    /// let mut container: HeteroContainer = HeteroContainer::new();
    /// container.entry().or_insert("hello");
    /// assert_eq!(container.entry::<&str>().key(), &TypeId::of::<&str>());
    /// ```
    #[inline]
    pub fn key(&self) -> &TypeId {
        self.inner.key()
    }

    /// Sets the value of the entry with the VacantEntry's type,
    /// and returns a mutable reference to it.
    ///
    /// # Examples
    /// ```
    /// use hetero_container::{HeteroContainer, Entry};
    ///
    /// let mut container: HeteroContainer = HeteroContainer::new();
    ///
    /// if let Entry::Vacant(o, _) = container.entry() {
    ///     o.insert("hello world");
    /// }
    /// assert_eq!(container.get::<&str>(), Some(&"hello world"));
    /// ```
    #[inline]
    pub fn insert(&mut self, value: V) -> V {
        // self.0.insert(TypeId::of::<V>(), Box::new(v))
        //             .map(|x| x.downcast().ok())
        //             .and_then(|x| x.map(|y| *y))
        *self.inner.insert(Box::new(value))
            .downcast()
            .expect(Self::CAST_EXPECT_MESSAGE)
    }

    /// Takes the value out of the entry, and returns it.
    ///
    /// # Examples
    /// ```
    /// use hetero_container::{HeteroContainer, Entry};
    ///
    /// let mut container: HeteroContainer = HeteroContainer::new();
    /// container.entry().or_insert("hello");
    ///
    /// if let Entry::Occupied(o, _) = container.entry::<&str>() {
    ///     assert_eq!(o.remove(), "hello");
    /// }
    ///
    /// assert_eq!(container.contains::<&str>(), false);
    /// ```
    #[inline]
    pub fn remove(self) -> V {
        *self.inner.remove()
            .downcast()
            .expect(Self::CAST_EXPECT_MESSAGE)
    }

    /// Gets a reference to the value in the entry.
    ///
    /// # Examples
    /// ```
    /// use hetero_container::{HeteroContainer, Entry};
    ///
    /// let mut container: HeteroContainer = HeteroContainer::new();
    /// container.entry().or_insert("hello");
    ///
    /// if let Entry::Occupied(o, _) = container.entry::<&str>() {
    ///     assert_eq!(o.get(), &"hello")
    /// }
    /// ```
    #[inline]
    pub fn get(&self) -> &V {
        self.inner.get()
            .downcast_ref()
            .expect(Self::CAST_EXPECT_MESSAGE)
    }

    /// Gets a mutable reference to the value in the entry.
    ///
    /// If you need a reference to the `OccupiedEntry` which may outlive the
    /// destruction of the `Entry` value, see [`into_mut`].
    ///
    /// [`into_mut`]: #method.into_mut
    ///
    /// # Examples
    /// ```
    /// use hetero_container::{HeteroContainer, Entry};
    ///
    /// let mut container: HeteroContainer = HeteroContainer::new();
    /// container.entry().or_insert(12);
    ///
    /// assert_eq!(container.get::<i32>(), Some(&12));
    /// if let Entry::Occupied(mut o, _) = container.entry::<i32>() {
    ///     *o.get_mut() += 10;
    ///     assert_eq!(*o.get(), 22);
    ///
    ///     // We can use the same Entry multiple times.
    ///     *o.get_mut() += 2;
    /// }
    /// ```
    #[inline]
    pub fn get_mut(&mut self) -> &mut V {
        self.inner.get_mut()
            .downcast_mut()
            .expect(Self::CAST_EXPECT_MESSAGE)
    }

    /// Converts the OccupiedEntry into a mutable reference to the value in the entry
    /// with a lifetime bound to the map itself.
    ///
    /// If you need multiple references to the `OccupiedEntry`, see [`get_mut`].
    ///
    /// [`get_mut`]: #method.get_mut
    ///
    /// # Examples
    /// ```
    /// use hetero_container::{HeteroContainer, Entry};
    ///
    /// let mut container: HeteroContainer = HeteroContainer::new();
    /// container.entry().or_insert(12);
    ///
    /// assert_eq!(container.get::<i32>(), Some(&12));
    /// if let Entry::Occupied(o, _) = container.entry::<i32>() {
    ///     *o.into_mut() += 10;
    /// }
    ///
    /// assert_eq!(container.get::<i32>(), Some(&22))
    /// ```
    #[inline]
    pub fn into_mut(self) -> &'a mut V {
        self.inner.into_mut()
            .downcast_mut()
            .expect(Self::CAST_EXPECT_MESSAGE)
    }
}

/// A view into an vacant entry in a `HeteroContainer`.
/// It is part of the [`Entry`] enum.
///
/// [`Entry`]: enum.Entry.html
#[derive(Debug)]
pub struct VacantEntry<'a, V> {
    inner: hash_map::VacantEntry<'a, TypeId, Box<dyn Any>>,
    _phantom: PhantomData<V>
}

impl <'a, V: 'static> VacantEntry<'a, V> {
    const CAST_EXPECT_MESSAGE: &'static str = "Couldn't downcast to V";

    /// Sets the value of the entry with the VacantEntry's type,
    /// and returns a mutable reference to it.
    ///
    /// # Examples
    /// ```
    /// use hetero_container::{HeteroContainer, Entry};
    ///
    /// let mut container: HeteroContainer = HeteroContainer::new();
    ///
    /// if let Entry::Vacant(o, _) = container.entry::<i32>() {
    ///     o.insert(37);
    /// }
    /// assert_eq!(container.get::<i32>(), Some(&37));
    /// ```
    #[inline]
    pub fn insert(self, default: V) -> &'a mut V {
        self.inner.insert(Box::new(default))
            .as_mut()
            .downcast_mut()
            .expect(Self::CAST_EXPECT_MESSAGE)
    }

    /// Gets a reference to the key that would be used when inserting a value
    /// through the `VacantEntry`.
    ///
    /// # Examples
    /// ```
    /// use hetero_container::HeteroContainer;
    /// use std::any::TypeId;
    ///
    /// let mut container: HeteroContainer = HeteroContainer::new();
    /// assert_eq!(container.entry::<i32>().key(), &TypeId::of::<i32>());
    /// ```
    #[inline]
    pub fn key(&self) -> &TypeId {
        self.inner.key()
    }
}

impl <'a, V: 'static> Entry<'a, V> {
    /// Ensures a value is in the entry by inserting the default value if empty, and returns
    /// a mutable reference to the value in the entry.
    ///
    /// # Examples
    /// ```
    /// use hetero_container::HeteroContainer;
    ///
    /// let mut container: HeteroContainer = HeteroContainer::new();
    ///
    /// container.entry().or_insert(3);
    /// assert_eq!(container.get::<i32>(), Some(&3));
    ///
    /// *container.entry().or_insert(10) *= 2;
    /// assert_eq!(container.get::<i32>(), Some(&6));
    /// ```
    #[inline]
    pub fn or_insert(self, default: V) -> &'a mut V {
        match self {
            Entry::Occupied(entry, _) => entry.into_mut(),
            Entry::Vacant(entry, _) => entry.insert(default),
        }
    }

    /// Ensures a value is in the entry by inserting the result of the default function if empty,
    /// and returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    /// ```
    /// use hetero_container::HeteroContainer;
    ///
    /// let mut container = HeteroContainer::new();
    /// let s = "hoho".to_string();
    ///
    /// container.entry::<String>().or_insert_with(|| s);
    ///
    /// assert_eq!(container.get::<String>(), Some(&"hoho".to_string()));
    /// ```
    #[inline]
    pub fn or_insert_with<F: FnOnce() -> V>(self, default: F) -> &'a mut V {
        match self {
            Entry::Occupied(entry, _) => entry.into_mut(),
            Entry::Vacant(entry, _) => entry.insert(default()),
        }
    }

    /// Returns a reference to this entry's key.
    ///
    /// # Examples
    /// ```
    /// use hetero_container::HeteroContainer;
    /// use std::any::TypeId;
    ///
    /// let mut container: HeteroContainer = HeteroContainer::new();
    /// assert_eq!(container.entry::<String>().key(), &TypeId::of::<String>())
    /// ```
    #[inline]
    pub fn key(&self) -> &TypeId {
        match *self {
            Entry::Occupied(ref entry, _) => entry.key(),
            Entry::Vacant(ref entry, _) => entry.key(),
        }
    }

    /// Provides in-place mutable access to an occupied entry before any
    /// potential inserts into the container.
    ///
    /// # Examples
    /// ```
    /// use hetero_container::HeteroContainer;
    ///
    /// let mut container: HeteroContainer = HeteroContainer::new();
    ///
    /// container.entry::<i32>()
    ///     .and_modify(|e| *e += 1)
    ///     .or_insert(42);
    /// assert_eq!(container.get::<i32>(), Some(&42));
    ///
    /// container.entry::<i32>()
    ///     .and_modify(|e| *e += 1)
    ///     .or_insert(42);
    /// assert_eq!(container.get::<i32>(), Some(&43))
    /// ```
    #[inline]
    pub fn and_modify<F: FnOnce(&mut V)>(self, f: F) -> Self {
        match self {
            Entry::Occupied(mut entry, _phantom) => {
                f(entry.get_mut());
                Entry::Occupied(entry, _phantom)
            }
            Entry::Vacant(entry, _phantom) => Entry::Vacant(entry, _phantom),
        }
    }
}

impl <'a, V: 'static + Default> Entry<'a, V> {
    /// Ensures a value is in the entry by inserting the default value if empty,
    /// and returns a mutable reference to the value in the entry.
    ///
    /// # Examples
    /// ```
    /// # fn main() {
    /// use hetero_container::HeteroContainer;
    ///
    /// let mut container: HeteroContainer = HeteroContainer::new();
    /// container.entry::<Option<u32>>().or_default();
    ///
    /// assert_eq!(container.get::<Option<u32>>(), Some(&None))
    /// # }
    /// ```
    #[inline]
    pub fn or_default(self) -> &'a mut V {
        match self {
            Entry::Occupied(entry, _) => entry.into_mut(),
            Entry::Vacant(entry, _) => entry.insert(Default::default()),
        }
    }
}

/// An iterator over the entries of a `HeteroContainer`.
///
/// this `struct` is created by the [`iter`] method on [`HeteroContainer`]. See its
/// documentation for more.
///
/// [`iter`]: struct.HeteroContainer.html#method.iter
/// [`HeteroContainer`]: struct.HeteroContainer.html
#[derive(Debug)]
pub struct Iter<'a> {
    inner: hash_map::Iter<'a, TypeId, Box<dyn Any>>
}

impl Clone for Iter<'_> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone()
        }
    }
}

impl <'a> Iterator for Iter<'a> {
    type Item = (&'a TypeId, &'a Box<dyn Any>);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner
            .next()
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

/// An owning iterator over
impl <'a> IntoIterator for &'a HeteroContainer {
    type Item = (&'a TypeId, &'a Box<dyn Any>);
    type IntoIter = Iter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

/// A mutable iterator over the entries of a `HeteroContainer`.
///
/// This `struct` is created by the [`iter_mut`] method on [`HeteroContainer`]. See its
/// documentation for more.
///
/// [`iter_mut`]: struct.HeteroContainer.html#method.iter_mut
/// [`HeteroContainer`]: struct.HeteroContainer.html
#[derive(Debug)]
pub struct IterMut<'a> {
    inner: hash_map::IterMut<'a, TypeId, Box<dyn Any>>
}

impl <'a> Iterator for IterMut<'a> {
    type Item = (&'a TypeId, &'a mut Box<dyn Any>);

    #[inline]
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl <'a> IntoIterator for &'a mut HeteroContainer {
    type Item = (&'a TypeId, &'a mut Box<dyn Any>);
    type IntoIter = IterMut<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}