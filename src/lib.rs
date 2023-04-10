use chrono::{DateTime, Duration, Utc};
use std::collections::{BTreeMap, HashMap, VecDeque};
use std::hash::Hash;

/// A Time-to-live (TTL) cache that stores key-value pairs and removes them automatically after a specified duration.
pub struct TTLCache<K, V> {
    cache: HashMap<K, (V, DateTime<Utc>)>,
    ttl: Duration,
}

impl<K, V> TTLCache<K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    /// Creates a new TTLCache with the specified Time-to-live duration.
    ///
    /// # Arguments
    ///
    /// * `ttl` - The Time-to-live duration for cache entries.
    pub fn new(ttl: Duration) -> Self {
        TTLCache {
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
    /// the oldest entry will be removed.
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

/// The LFU cache maintains a fixed size cache of key-value pairs,
/// removing the least frequently used item when the cache is full.
pub struct LFUCache<K: Ord + Eq + Hash, V> {
    capacity: usize,
    cache: HashMap<K, (V, usize)>,
    frequencies: BTreeMap<usize, Vec<K>>,
}

impl<K: Ord + Copy + Clone + Eq + Hash, V> LFUCache<K, V> {
    /// Creates a new LFUCache with the specified capacity.
    ///
    /// # Arguments
    ///
    /// * `capacity` - The maximum number of items the cache can hold.
    pub fn new(capacity: usize) -> Self {
        LFUCache {
            capacity,
            cache: HashMap::with_capacity(capacity),
            frequencies: BTreeMap::new(),
        }
    }

    /// Gets the value associated with the specified key, if present.
    ///
    /// # Arguments
    ///
    /// * `key` - The key to look up in the cache.
    pub fn get(&mut self, key: K) -> Option<&V> {
        if let Some((value, freq)) = self.cache.get_mut(&key) {
            self.frequencies
                .get_mut(freq)
                .unwrap()
                .retain(|k| k != &key);
            *freq += 1;
            self.frequencies
                .entry(*freq)
                .or_insert_with(Vec::new)
                .push(key.clone());
            Some(value)
        } else {
            None
        }
    }

    /// Inserts a key-value pair into the cache.
    ///
    /// If the cache is full, removes the least frequently used item.
    ///
    /// # Arguments
    ///
    /// * `key` - The key to insert.
    /// * `value` - The value to associate with the key.
    pub fn insert(&mut self, key: K, value: V) {
        if self.capacity == 0 {
            return;
        }

        if self.cache.contains_key(&key) {
            let old_val = self.cache.get_mut(&key).unwrap();
            let freq = old_val.1;
            old_val.0 = value;
            old_val.1 += 1;

            let keys = self.frequencies.get_mut(&freq).unwrap();
            let index = keys.iter().position(|k| k == &key).unwrap();
            keys.remove(index);

            let new_freq_keys = self.frequencies.entry(freq + 1).or_insert_with(Vec::new);
            new_freq_keys.push(key);
        } else {
            if self.cache.len() == self.capacity {
                let (min_freq, removed_key) = {
                    let (min_freq, keys) = self.frequencies.iter().next().unwrap();
                    let removed_key = keys.first().unwrap().clone();
                    (min_freq.clone(), removed_key)
                };
                self.cache.remove(&removed_key);
                self.frequencies.get_mut(&min_freq).unwrap().remove(0);
            }
            self.cache.insert(key.clone(), (value, 1));
            self.frequencies.entry(1).or_insert_with(Vec::new).push(key);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::thread::sleep;

    #[test]
    fn test_ttl_cache() {
        let mut cache = TTLCache::new(Duration::milliseconds(100));
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

    #[test]
    fn test_lfu_cache() {
        let mut lfu_cache = LFUCache::new(3);

        lfu_cache.insert("key1", 1);
        lfu_cache.insert("key2", 2);
        lfu_cache.insert("key3", 3);
        assert_eq!(lfu_cache.cache.len(), 3);
        assert_eq!(lfu_cache.frequencies[&1].len(), 3);

        lfu_cache.insert("key1", 11);
        assert_eq!(lfu_cache.cache.len(), 3);
        assert_eq!(lfu_cache.frequencies[&1].len(), 2);
        assert_eq!(lfu_cache.frequencies[&2].len(), 1);
        assert_eq!(lfu_cache.cache["key1"].0, 11);

        lfu_cache.insert("key4", 4);
        assert_eq!(lfu_cache.cache.len(), 3);
        assert_eq!(lfu_cache.cache.contains_key("key2"), false);
        assert_eq!(lfu_cache.frequencies[&1].len(), 2);
    }
}
