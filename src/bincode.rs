use super::{builder::Builder, Slab};
use bincode::de::{BorrowDecoder, Decoder};
use bincode::enc::Encoder;
use bincode::error::{DecodeError, EncodeError};
use bincode::{BorrowDecode, Decode, Encode};

// Since Slab is stored as a map of usize to T, its implementations are quite similar to those of HashMap<usize, T>:
// https://github.com/bincode-org/bincode/blob/v2.0.0-rc.2/src/features/impl_std.rs#L409-L469.

impl<T: Encode> Encode for Slab<T> {
    fn encode<E: Encoder>(&self, encoder: &mut E) -> Result<(), EncodeError> {
        // https://docs.rs/bincode/2.0.0-rc.2/bincode/config/struct.Configuration.html#method.with_fixed_int_encoding
        // With fixed integer encoding, usize is always encoded as a u64,
        // so there's no need to worry about varying sizes of usize.
        self.len().encode(encoder)?;
        for (key, value) in self {
            key.encode(encoder)?;
            value.encode(encoder)?;
        }
        Ok(())
    }
}

impl<T: Decode> Decode for Slab<T> {
    fn decode<D: Decoder>(decoder: &mut D) -> Result<Self, DecodeError> {
        let len = usize::decode(decoder)?;
        decoder.claim_container_read::<(usize, T)>(len)?;

        let mut builder = Builder::with_capacity(len);
        for _ in 0..len {
            // See the documentation on `unclaim_bytes_read` as to why we're doing this here
            decoder.unclaim_bytes_read(core::mem::size_of::<(usize, T)>());

            let key = usize::decode(decoder)?;
            let value = T::decode(decoder)?;
            builder.pair(key, value);
        }
        Ok(builder.build())
    }
}

impl<'de, T: BorrowDecode<'de>> BorrowDecode<'de> for Slab<T> {
    fn borrow_decode<D: BorrowDecoder<'de>>(decoder: &mut D) -> Result<Self, DecodeError> {
        let len = usize::decode(decoder)?;
        decoder.claim_container_read::<(usize, T)>(len)?;

        let mut builder = Builder::with_capacity(len);
        for _ in 0..len {
            // See the documentation on `unclaim_bytes_read` as to why we're doing this here
            decoder.unclaim_bytes_read(core::mem::size_of::<(usize, T)>());

            let key = usize::borrow_decode(decoder)?;
            let value = T::borrow_decode(decoder)?;
            builder.pair(key, value);
        }
        Ok(builder.build())
    }
}
