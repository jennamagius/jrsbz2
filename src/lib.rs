// Based on reverse engineering performed by Joe Tsai from https://github.com/dsnet/compress/blob/master/doc/bzip2-format.pdf (https://digital-static.net)
// bzip2 is originally by Julian Seward and may be found at https://sourceware.org/bzip2/

mod common;
mod decode;
mod encode;
#[cfg(test)]
mod test;

pub use crate::decode::Decoder;
pub use crate::encode::Encoder;
