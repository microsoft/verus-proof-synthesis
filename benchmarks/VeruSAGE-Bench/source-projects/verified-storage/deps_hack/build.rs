#[cfg(target_os = "linux")]
extern crate bindgen;

#[cfg(target_os = "linux")]
use std::path::PathBuf;

#[cfg(target_os = "linux")]
fn setup_linux()
{
    println!("cargo:rustc-link-search=libpmemlog1");
    println!("cargo:rustc-link-lib=pmemlog");
    println!("cargo:rustc-link-lib=pmem");

    let bindings = bindgen::Builder::default()
        .header("wrapper.h")
        .generate()
        .expect("Unable to generate bindings");

    let out_path = PathBuf::from("./src/");
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("Couldn't write bindings!");
}

fn main() {
    #[cfg(target_os = "linux")]
    setup_linux();
}
