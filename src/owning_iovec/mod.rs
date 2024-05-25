mod byte_arena;
mod global_deque;
mod implementation;

pub use byte_arena::AnchoredSlice;
pub use byte_arena::ByteArena;
pub use implementation::ConsumingIovec;
pub use implementation::OwningIovec;
pub use implementation::OwningIovecBackref;
pub use implementation::StableIovec;

impl std::io::Read for ConsumingIovec<'_> {
    fn read(&mut self, mut dst: &mut [u8]) -> std::io::Result<usize> {
        let mut written = 0;
        while !dst.is_empty() {
            let Some(slice) = self.front() else {
                break;
            };

            let to_write = slice.len().min(dst.len());
            dst[..to_write].copy_from_slice(&slice[..to_write]);
            self.advance_slices(to_write);
            written += to_write;
            dst = &mut dst[to_write..];
        }

        Ok(written)
    }
}
