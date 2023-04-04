use chrono::{DateTime, Duration, Utc};
use std::collections::HashMap;
use std::collections::VecDeque;
use std::hash::Hash;

/// A Time-to-live (TTL) cache that stores key-value pairs and removes them automatically after a specified duration.
pub struct TtlCache<K, V> {
    cache: HashMap<K, (V, DateTime<Utc>)>,
    ttl: Duration,
}

impl<K, V> TtlCache<K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    /// Creates a new TtlCache with the specified Time-to-live duration.
    ///
    /// # Arguments
    ///
    /// * `ttl` - The Time-to-live duration for cache entries.
    pub fn new(ttl: Duration) -> Self {
        TtlCache {
            cache: HashMap::new(),
            ttl,
        }
    }

    /// Inserts a key-value pair into the cache with the specified TTL.
    ///
    /// # Arguments
    ///
    /// * `key` - The key to store in the cache.
    /// * `value` - The value to store in the cache.
    pub fn insert(&mut self, key: K, value: V) {
        let expires_at = Utc::now() + self.ttl;
        self.cache.insert(key, (value, expires_at));
    }

    /// Retrieves the value associated with the specified key, if it exists and is not expired.
    ///
    /// # Arguments
    ///
    /// * `key` - The key to retrieve from the cache.
    ///
    /// # Returns
    ///
    /// * `Some(value)` if the key is present and not expired, `None` otherwise.
    pub fn get(&mut self, key: &K) -> Option<V> {
        if let Some((value, expires_at)) = self.cache.get(key) {
            if expires_at > &Utc::now() {
                Some(value.clone())
            } else {
                self.cache.remove(key);
                None
            }
        } else {
            None
        }
    }

    /// Removes the entry associated with the specified key, if it exists.
    ///
    /// # Arguments
    ///
    /// * `key` - The key to remove from the cache.
    pub fn remove(&mut self, key: &K) {
        self.cache.remove(key);
    }

    /// Removes all expired entries from the cache.
    pub fn clear_expired(&mut self) {
        let mut now = Utc::now();
        self.cache
            .retain(|_, (_, expires_at)| expires_at > &mut now);
    }
}

/// A simple implementation of a First-In-First-Out (FIFO) cache.
///
/// # Examples
///
/// ```
/// use cache_tools::FIFOCache;
///
/// let mut cache = FIFOCache::new(3);
/// cache.insert(1, "one");
/// cache.insert(2, "two");
/// cache.insert(3, "three");
/// cache.insert(4, "four"); // Evicts the first entry (1, "one").
/// assert_eq!(cache.get(&1), None);
/// assert_eq!(cache.get(&2), Some(&"two"));
/// ```
pub struct FIFOCache<K, V> {
    capacity: usize,
    keys: VecDeque<K>,
    values: HashMap<K, V>,
}

impl<K: Clone + Eq + std::hash::Hash, V> FIFOCache<K, V> {
    /// Creates a new FIFOCache with the specified capacity.
    ///
    /// # Arguments
    ///
    /// * `capacity` - The maximum number of entries the cache can hold.
    pub fn new(capacity: usize) -> Self {
        FIFOCache {
            capacity,
            keys: VecDeque::with_capacity(capacity),
            values: HashMap::new(),
        }
    }

    /// Inserts a key-value pair into the cache. If the cache is full,
    /// the oldest entry will be evicted.
    ///
    /// # Arguments
    ///
    /// * `key` - The key associated with the value.
    /// * `value` - The value to be stored in the cache.
    pub fn insert(&mut self, key: K, value: V) {
        if self.values.len() == self.capacity {
            if let Some(removed_key) = self.keys.pop_front() {
                self.values.remove(&removed_key);
            }
        }
        self.keys.push_back(key.clone());
        self.values.insert(key, value);
    }

    /// Retrieves the value associated with the given key from the cache.
    ///
    /// # Arguments
    ///
    /// * `key` - The key associated with the value.
    ///
    /// # Returns
    ///
    /// An option containing a reference to the value if found, otherwise None.
    pub fn get(&self, key: &K) -> Option<&V> {
        self.values.get(key)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::thread::sleep;

    #[test]
    fn test_ttl_cache() {
        let mut cache = TtlCache::new(Duration::milliseconds(100));
        cache.insert("key1", "value1");
        cache.insert("key2", "value2");

        assert_eq!(cache.get(&"key1"), Some("value1"));
        assert_eq!(cache.get(&"key2"), Some("value2"));

        sleep(std::time::Duration::from_millis(50));
        cache.clear_expired();
        assert_eq!(cache.get(&"key1"), Some("value1"));
        assert_eq!(cache.get(&"key2"), Some("value2"));

        sleep(std::time::Duration::from_millis(60));
        cache.clear_expired();
        assert_eq!(cache.get(&"key1"), None);
        assert_eq!(cache.get(&"key2"), None);
    }

    #[test]
    fn test_fifo_cache() {
        let mut cache = FIFOCache::new(2);

        cache.insert(1, "one");
        cache.insert(2, "two");
        assert_eq!(cache.get(&1), Some(&"one"));
        assert_eq!(cache.get(&2), Some(&"two"));

        cache.insert(3, "three"); // Evicts the first entry (1, "one").
        assert_eq!(cache.get(&1), None);
        assert_eq!(cache.get(&2), Some(&"two"));
        assert_eq!(cache.get(&3), Some(&"three"));
    }
}
