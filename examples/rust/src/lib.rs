#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct Hash256 {
    pub parts: [u64; 4],
}

#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct ExoCap {
    pub pa: u32,
    pub id: u32,
    pub rights: u32,
    pub owner: u32,
    pub auth_tag: Hash256,
}

extern "C" {
    pub fn exo_alloc_page() -> ExoCap;
    pub fn exo_send(dest: ExoCap, buf: *const u8, len: u64) -> i32;
    pub fn exo_yield_to(target: ExoCap) -> i32;
}
