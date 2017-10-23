use std::fmt;
use std::result::Result;
use std::marker::PhantomData;

use serde::{Serialize, Serializer, Deserialize, Deserializer};
use serde::ser::SerializeSeq;
use serde::de::{SeqAccess, Visitor};

use {Entry, Slab};

impl<T> Serialize for Slab<T>
where
    T: Serialize,
{
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut s = serializer.serialize_seq(Some(self.len))?;

        s.serialize_element(&self.capacity())?;
        s.serialize_element(&self.len())?;

        for (key, value) in self.iter() {
            s.serialize_element(&(key, value))?;
        }

        s.end()
    }
}

struct SlabVisitor<T>(PhantomData<T>);

impl<T> Default for SlabVisitor<T> {
    fn default() -> Self {
        SlabVisitor(PhantomData)
    }
}

impl<'de, T> Visitor<'de> for SlabVisitor<T>
where
    T: Deserialize<'de>,
{
    type Value = Slab<T>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("slab")
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        let capacity: usize = seq.next_element()?.unwrap();
        let len: usize = seq.next_element()?.unwrap();

        let mut slab = Slab::with_capacity(capacity);

        slab.len = len;
        slab.next = len + 1;

        while let Some((key, value)) = seq.next_element()? {
            for i in slab.entries.len()..key {
                slab.entries.push(Entry::Vacant(slab.next));
                slab.next = i;
            }

            slab.entries.push(Entry::Occupied(value));
        }

        for i in slab.entries.len()..len {
            slab.entries.push(Entry::Vacant(slab.next));
            slab.next = i;
        }

        Ok(slab)
    }
}

impl<'de, T> Deserialize<'de> for Slab<T>
where
    T: Deserialize<'de>,
{
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_seq(SlabVisitor::default())
    }
}

#[cfg(test)]
mod tests {
    use serde_json;

    use super::*;

    #[test]
    fn serialize() {
        let mut slab = Slab::with_capacity(64);

        let foo = slab.insert("foo");
        let bar = slab.insert("bar");
        let hello = slab.insert("hello");

        slab.remove(bar);

        assert_eq!(slab.capacity(), 64);
        assert_eq!(slab.len(), 2);

        let json = serde_json::to_string(&slab).unwrap();

        assert_eq!(json, "[64,2,[0,\"foo\"],[2,\"hello\"]]");

        let s: Slab<String> = serde_json::from_str(&json).unwrap();

        assert_eq!(s.capacity(), slab.capacity());
        assert_eq!(s.len(), slab.len());
        assert_eq!(s.entries.len(), s.entries.len());
        assert_eq!(s[foo], "foo");
        assert_eq!(s.get(bar), None);
        assert_eq!(s[hello], "hello");
    }
}
