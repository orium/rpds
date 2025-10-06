#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Entry<K, V> {
    pub key: K,
    pub value: V,
}

impl<K, V> Entry<K, V> {
    #[must_use]
    pub fn new(key: K, value: V) -> Entry<K, V> {
        Entry { key, value }
    }
}
