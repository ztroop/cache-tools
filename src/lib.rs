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
    /// * `key` - The key of the entry to be inserted.
    /// * `value` - The value of the entry to be inserted.
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
    cache: HashMap<K, V>,
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
            cache: HashMap::new(),
        }
    }

    /// Inserts a key-value pair into the cache. If the cache is full,
    /// the oldest entry will be evicted.
    ///
    /// # Arguments
    ///
    /// * `key` - The key of the entry to be inserted.
    /// * `value` - The value of the entry to be inserted.
    pub fn insert(&mut self, key: K, value: V) {
        if self.cache.len() == self.capacity {
            if let Some(removed_key) = self.keys.pop_front() {
                self.cache.remove(&removed_key);
            }
        }
        self.keys.push_back(key.clone());
        self.cache.insert(key, value);
    }

    /// Retrieves the value associated with the given key from the cache.
    ///
    /// # Arguments
    ///
    /// * `key` - The key to retrieve from the cache.
    ///
    /// # Returns
    ///
    /// An option containing a reference to the value if found, otherwise None.
    pub fn get(&self, key: &K) -> Option<&V> {
        self.cache.get(key)
    }
}

/// An implementation of an LRU (Least Recently Used) Cache.
///
/// The cache has a maximum capacity and automatically removes
/// the least recently used entry when the capacity is exceeded.
pub struct LRUCache<K, V> {
    capacity: usize,
    cache: HashMap<K, (V, usize)>,
    lru_keys: VecDeque<K>,
}

impl<K: Clone + Eq + std::hash::Hash, V> LRUCache<K, V> {
    /// Creates a new LRUCache with the specified capacity.
    ///
    /// # Arguments
    ///
    /// * `capacity` - The maximum number of entries the cache can hold.
    pub fn new(capacity: usize) -> Self {
        LRUCache {
            capacity,
            cache: HashMap::with_capacity(capacity),
            lru_keys: VecDeque::with_capacity(capacity),
        }
    }

    /// Retrieves the value associated with the given key if it exists, updating the LRU order.
    ///
    /// # Arguments
    ///
    /// * `key` - The key to retrieve from the cache.
    ///
    /// # Returns
    ///
    /// * `Some(&V)` - If the key exists in the cache.
    /// * `None` - If the key is not in the cache.
    pub fn get(&mut self, key: &K) -> Option<&V> {
        if let Some((value, index)) = self.cache.get_mut(key) {
            self.lru_keys.remove(*index);
            self.lru_keys.push_back(key.clone());
            let new_index = self.lru_keys.len() - 1;
            *index = new_index;
            Some(value)
        } else {
            None
        }
    }

    /// Inserts a key-value pair into the cache, removing the least recently used entry if needed.
    ///
    /// # Arguments
    ///
    /// * `key` - The key of the entry to be inserted.
    /// * `value` - The value of the entry to be inserted.
    pub fn insert(&mut self, key: K, value: V) {
        if self.cache.len() >= self.capacity {
            if let Some(removed_key) = self.lru_keys.pop_front() {
                self.cache.remove(&removed_key);
            }
        }

        let index = self.lru_keys.len();
        self.lru_keys.push_back(key.clone());
        self.cache.insert(key, (value, index));
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::thread::sleep;

    #[test]
    fn test_ttl_cache() {
        let mut cache = TtlCache::new(Duration::milliseconds(100));
        cache.insert("key1", 1);
        cache.insert("key2", 2);

        assert_eq!(cache.get(&"key1"), Some(1));
        assert_eq!(cache.get(&"key2"), Some(2));

        sleep(std::time::Duration::from_millis(50));
        cache.clear_expired();
        assert_eq!(cache.get(&"key1"), Some(1));
        assert_eq!(cache.get(&"key2"), Some(2));

        sleep(std::time::Duration::from_millis(60));
        cache.clear_expired();
        assert_eq!(cache.get(&"key1"), None);
        assert_eq!(cache.get(&"key2"), None);
    }

    #[test]
    fn test_fifo_cache() {
        let mut cache = FIFOCache::new(2);

        cache.insert("one", 1);
        cache.insert("two", 2);
        assert_eq!(cache.get(&"one"), Some(&1));
        assert_eq!(cache.get(&"two"), Some(&2));

        cache.insert("three", 3);
        assert_eq!(cache.get(&"one"), None);
        assert_eq!(cache.get(&"two"), Some(&2));
        assert_eq!(cache.get(&"three"), Some(&3));
    }

    #[test]
    fn test_lru_cache() {
        let mut lru_cache = LRUCache::new(3);

        lru_cache.insert("one", 1);
        lru_cache.insert("two", 2);
        lru_cache.insert("three", 3);

        assert_eq!(lru_cache.get(&"two"), Some(&2));

        lru_cache.insert("four", 4);

        assert_eq!(lru_cache.get(&"one"), None);
        assert_eq!(lru_cache.get(&"two"), Some(&2));
        assert_eq!(lru_cache.get(&"three"), Some(&3));
    }
}
