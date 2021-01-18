use hacspec_lib::*;

//use cortex_m_semihosting::{dbg, hprintln};
/// "RIOT"
const RIOTBOOT_MAGIC: u32 = 0x544f_4952u32;

/// A generic type for holding intermediate checksum values
type Fletcher = (u32, u32);

pub fn new_fletcher() -> Fletcher {
    (0u32, 0u32)
}

pub fn max_chunk_size() -> usize {
    360
}

fn reduce_u32(x: u32) -> u32 {
    (x & 0xffffu32) + (x >> 16)
}

fn combine(lower: u32, upper: u32) -> u32 {
    lower | (upper << 16)
}

pub fn update_fletcher(f: Fletcher, data: Seq<u16>) -> Fletcher {
    let max_chunk_size = max_chunk_size();
    let (mut a, mut b) = f;

    for i in 0..data.num_chunks(max_chunk_size) {
        let (chunk_len, chunk) = data.get_chunk(i, max_chunk_size);
        let mut intermediate_a = a;
        let mut intermediate_b = b;

        for _j in 0..chunk_len {
            intermediate_a = intermediate_a + chunk[i] as u32;
            intermediate_b = intermediate_b + intermediate_a;
        }

        a = reduce_u32(intermediate_a);
        b = reduce_u32(intermediate_b);
    }

    a = reduce_u32(a);
    b = reduce_u32(b);
    (a, b)
}

/// Returns the current checksum value of the `Fletcher` object
pub fn value(x: Fletcher) -> u32 {
    let (a, b) = x;
    combine(a, b)
}

/// 1. Header magic number (always "RIOT")
/// 2. Integer representing the partition version
/// 3. Address after the allocated space for the header
/// 4. Checksum of riotboot_hdr
type Header = (u32, u32, u32, u32);

fn header_as_u16_slice(_h: &Header) -> Seq<u16> {
    Seq::<u16>::new(1) // TODO: split all u32 into 2 u16 and concatenate
}
pub fn is_valid_header(h: &Header) -> bool {
    let (magic_number, _, _, checksum) = h;
    let magic_number = magic_number.clone();
    let checksum = checksum.clone();
    let mut result = false;
    if magic_number == RIOTBOOT_MAGIC {
        let fletcher = new_fletcher();
        let fletcher = update_fletcher(fletcher, header_as_u16_slice(h));
        let sum = value(fletcher);
        result = sum == checksum;
    }
    result
}

pub fn choose_image(images: Seq<Header>) -> (bool, u32) {
    let mut image = 0u32;
    let mut image_found = false;

    for i in 0..images.len() {
        let header = images[i];
        if is_valid_header(&header) {
            let (_, sequence_number, start_addr, _) = header;
            let change_image = !(image_found && (sequence_number <= image));
            if change_image {
                image = start_addr;
                image_found = true;
            }
        }
    }
    (image_found, image)
}
