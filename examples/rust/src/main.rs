use exo_rust_demo::*;

fn main() {
    unsafe {
        let page = exo_alloc_page();
        let msg = b"hello";
        let _ = exo_send(page, msg.as_ptr(), msg.len() as u64);
        let _ = exo_yield_to(page);
    }
}
