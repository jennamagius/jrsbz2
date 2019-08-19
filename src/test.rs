use crate::common::*;
use crate::decode::*;
use crate::encode::*;

static LOGGER_INIT: std::sync::Once = std::sync::Once::new();

fn log_init() {
    LOGGER_INIT.call_once(env_logger::init);
}

#[test]
fn format_decode_test() {
    log_init();
    let data = b"\x42\x5a\x68\x31\x31\x41\x59\x26\x53\x59\x5a\x55\xc4\x1e\x00\x00\x0c\x5f\x80\x20\x00\x40\x84\x00\x00\x80\x20\x40\x00\x2f\x6c\xdc\x80\x20\x00\x48\x4a\x9a\x4c\xd5\x53\xfc\x69\xa5\x53\xff\x55\x3f\x69\x50\x15\x48\x95\x4f\xff\x55\x51\xff\xaa\xa0\xff\xf5\x55\x31\xff\xaa\xa7\xfb\x4b\x34\xc9\xb8\x38\xff\x16\x14\x56\x5a\xe2\x8b\x9d\x50\xb9\x00\x81\x1a\x91\xfa\x25\x4f\x08\x5f\x4b\x5f\x53\x92\x4b\x11\xc5\x22\x92\xd9\x50\x56\x6b\x6f\x9e\x17\x72\x45\x38\x50\x90\x5a\x55\xc4\x1e";
    let mut decoder = Decoder::default();
    let mut result = Vec::new();
    for byte in &data[..] {
        match decoder.push_byte(*byte) {
            Ok(data) => {
                result.extend(data);
            }
            _ => (),
        }
    }
    assert_eq!(&result[..], &b"If Peter Piper picked a peck of pickled peppers, where\'s the peck of pickled peppers Peter Piper picked?????"[..]);
}

#[test]
fn decode_bwt_test() {
    LOGGER_INIT.call_once(env_logger::init);
    let data = b"?fsrrdkkeaddrrffs,es???d\x01     eeiiiieeeehrppkllkppttpphppPPIootwppppPPcccccckk      iipp    eeeeeeeeer'ree  ";
    assert_eq!(&decode_bwt(data, 24).unwrap()[..], &b"If Peter Piper picked a peck of pickled peppers, where\'s the peck of pickled peppers Peter Piper picked????\x01"[..]);
}

#[test]
fn abencode_test() {
    assert_eq!(abencode(1), vec![Symbol::RunA]);
    assert_eq!(abencode(2), vec![Symbol::RunB]);
    assert_eq!(abencode(3), vec![Symbol::RunA, Symbol::RunA]);
    assert_eq!(abencode(4), vec![Symbol::RunB, Symbol::RunA]);
    assert_eq!(abencode(5), vec![Symbol::RunA, Symbol::RunB]);
    assert_eq!(abencode(6), vec![Symbol::RunB, Symbol::RunB]);
    assert_eq!(abencode(7), vec![Symbol::RunA, Symbol::RunA, Symbol::RunA]);
    assert_eq!(abencode(8), vec![Symbol::RunB, Symbol::RunA, Symbol::RunA]);
    assert_eq!(abencode(9), vec![Symbol::RunA, Symbol::RunB, Symbol::RunA]);
    assert_eq!(abencode(10), vec![Symbol::RunB, Symbol::RunB, Symbol::RunA]);
    assert_eq!(abencode(11), vec![Symbol::RunA, Symbol::RunA, Symbol::RunB]);
    assert_eq!(abencode(12), vec![Symbol::RunB, Symbol::RunA, Symbol::RunB]);
    assert_eq!(abencode(13), vec![Symbol::RunA, Symbol::RunB, Symbol::RunB]);
    assert_eq!(abencode(14), vec![Symbol::RunB, Symbol::RunB, Symbol::RunB]);
    assert_eq!(
        abencode(15),
        vec![Symbol::RunA, Symbol::RunA, Symbol::RunA, Symbol::RunA]
    );
    assert_eq!(
        abencode(16),
        vec![Symbol::RunB, Symbol::RunA, Symbol::RunA, Symbol::RunA]
    );
    assert_eq!(
        abencode(17),
        vec![Symbol::RunA, Symbol::RunB, Symbol::RunA, Symbol::RunA]
    );
    assert_eq!(
        abencode(18),
        vec![Symbol::RunB, Symbol::RunB, Symbol::RunA, Symbol::RunA]
    );
    assert_eq!(abencode(30).len(), 4);
    assert_eq!(abencode(31).len(), 5);
    assert_eq!(abencode(62).len(), 5);
    assert_eq!(abencode(63).len(), 6);
    for i in 0..=64 {
        let encoded = abencode(i);
        let decoded = abdecode(&encoded[..]);
        assert_eq!(decoded, i);
    }
}

#[test]
fn rle_test() {
    assert_eq!(&rle_encode(b"AAAAAAABBBBCCCD")[..], b"AAAA\x03BBBB\x00CCCD");
    assert_eq!(&rle_encode(b"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA")[..], b"AAAA\xfbA");
    assert_eq!(&rle_encode(b"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA")[..], b"AAAA\xfbAAAA\x00");
    assert_eq!(&rle_encode(b"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA")[..], b"AAAA\xfbAAAA\x29");
}

#[test]
fn bwt_test() {
    assert_eq!(bwt_encode(&b"banana"[..]), (b"nnbaaa".to_vec(), 3));
}

#[test]
fn mtf_test() {
    let mut data = b"bbyaeeeeeeafeeeybzzzzzzzzzyz".to_vec();
    let _stack = mtf_encode(&mut data);
    assert_eq!(
        &data[..],
        [1, 0, 4, 2, 3, 0, 0, 0, 0, 0, 1, 4, 2, 0, 0, 3, 4, 5, 0, 0, 0, 0, 0, 0, 0, 0, 2, 1]
    );
}

#[test]
fn empty_encode_test() {
    let mut encoder = crate::encode::Encoder::default();
    let file = encoder.finish().unwrap();
    let mut expected = b"BZh9".to_vec();
    expected.extend(crate::common::STREAM_FOOTER_MAGIC);
    expected.extend(b"\x00\x00\x00\x00");
    assert_eq!(&file[..], &expected[..]);
}

#[test]
fn encode_decode_test() {
    log_init();

    let mut examples = [b"a".to_vec(), b"asdf".to_vec()].to_vec();
    let mut all_bytes = Vec::new();
    for i in 0..=255 {
        all_bytes.push(i);
    }
    examples.push(all_bytes);
    examples.push([171, 10, 25, 159, 216, 62, 237, 173, 28, 171].to_vec());
    let mut rng = rand::thread_rng();
    let mut random = vec![0u8; 9000];
    rand::Rng::fill(&mut rng, &mut random[..]);
    examples.push(random);

    for example in examples {
        let data = crate::encode(&example).unwrap();
        let data = crate::decode(&data);
        assert_eq!(&data[..], &example[..]);
    }
}
