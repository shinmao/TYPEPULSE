# TypePulse

## Overview
This is the official repository for **TypePulse**, a type confusion bug detection tool for Rust packages. The details of our work can be found in our paper "TypePulse: Detecting Type Confusion Bugs in Rust Programs", which will appear at the 34th USENIX Security Symposium (USENIX Security '25), August 13–15, 2025, at the Seattle, WA, USA.  

Please check this link: https://www.usenix.org/conference/usenixsecurity25/presentation/chen-hung-mao.  

## Environment Setup
We provide a Dockerfile to facilitate users to quickly deploy and use **TypePulse**. The user also can install TypePulse on the local by following the next steps.

### Requirements
**TypePulse** can be installed on a Linux environment (ubuntu >=18.04). It relies on `rustc` to compile Rust packages. In our evaluation, we use rustc nightly-2023-06-02. In addition, we use Python3 to set up environments and prepare data.

### First time to set up environment
Set up the folder and path for **TypePulse**:
```
python3 setup_typepulse_home.py path/to/your/typepulse_home
```
If you don't install Rust development environment:
```bash
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
```
Don't forget to configure the env variables.

Set up `rustc` version, toolchains, and env variables:
```bash
rustup install nightly-2023-06-02
rustup default nightly-2023-06-02         // change to nightly channel which is rustc 1.72.0-nightly
rustup component add rust-src rustc-dev llvm-tools-preview miri

// env var setup
export TYPEPULSE_RUST_CHANNEL=nightly-2023-06-02
export TYPEPULSE_RUNNER_HOME="/home/TypePulse/typepulse-home"
export RUSTFLAGS="-L $HOME/.rustup/toolchains/nightly-2023-06-02-x86_64-unknown-linux-gnu/lib"
export LD_LIBRARY_PATH="${LD_LIBRARY_PATH}:$HOME/.rustup/toolchains/nightly-2023-06-02-x86_64-unknown-linux-gnu/lib"
export RUSTC_SYSROOT="$HOME/.rustup/toolchains/nightly-2023-06-02-x86_64-unknown-linux-gnu/bin/rustc"
```
### install with `install.sh`
```
// $0 is bin
cargo install --path "$(dirname $0)" --force
```
You should be able to see the message that `cargo-typepulse` and `typepulse` are installed.

## Usage Tutorial: Run TypePulse in your package
For example, if the user wants to run TypePulse in [candle-core 0.4.1](https://crates.io/crates/candle-core). 
First, they need to download the package source code:
```bash
curl -L 'https://crates.io/api/v1/crates/candle-core/0.4.1/download' > ./candle-core-0.4.1.tar.gz
tar -xvf candle-core-0.4.1.tar.gz
```

Then, enter into the directory of the package (Same level as `Cargo.toml`) :
```bash
cd candle-core-0.4.1/
```

Next, execute **TypePulse**:
```bash
cargo typepulse -j 16
# -j 16 means that we use 16 processes to speed up the detection, and the user can change the number according to the local environment.
```

The detection report:
```bash
...
2024-04-29 20:37:28.503790 |INFO | [typepulse-progress] BrokenBitPatterns analysis finished
2024-04-29 20:37:28.503798 |INFO | [typepulse-progress] TypePulse finished
Error (BrokenLayout:): Potential broken layout issue in `quantized::ggml_file::from_raw_data`
-> candle-core/src/quantized/ggml_file.rs:120:1: 135:2
fn from_raw_data<T: super::GgmlType + Send + Sync + 'static>(
    raw_data: &[u8],
    size_in_bytes: usize,
    dims: Vec<usize>,
    device: &Device,
) -> Result<super::QTensor> {
    let raw_data_ptr = raw_data.as_ptr();
    let n_blocks = size_in_bytes / std::mem::size_of::<T>();
    let data = unsafe { std::slice::from_raw_parts(raw_data_ptr as *const T, n_blocks) };
    let data: QStorage = match device {
        Device::Cpu => QStorage::Cpu(Box::new(data.to_vec())),
        Device::Metal(metal) => super::metal::load_quantized(metal, data)?,
        Device::Cuda(cuda) => super::cuda::load_quantized(cuda, data)?,
    };
    super::QTensor::new(data, dims)
}
...
```
In addition to `Error`, we also show the bugs at `Warning` level. However, they are not included in our "Positive" cases.


## Troubleshoot
If you run into the following error message:
```
|ERROR| [typepulse-progress] typepulse was built for a different sysroot than the rustc in your current toolchain.
Make sure you use the same toolchain to run typepulse that you used to build it!
```
The reason could be that the crate specified the different toolchain from the one used by TypePulse. In this case, you could change the `channel` specified in `rust-toolchain.toml` to the one we used if there is no breaking change between two rustc versions.  

### Dependencies issues
To override the specified toolchain of project:  
```
rustup override set nightly-2023-06-02-x86_64-unknown-linux-gnu
```

If you run into this `home` issue:
```
error: package `home v0.5.11` cannot be built because it requires rustc 1.81 or newer, while the currently active rustc version is 1.72.0-nightly
```
Considering this command:  
```
cargo update -p home@0.5.11 --precise 0.5.9
```

### Troubleshooting Custom build issues
```
error: failed to run custom build command for openssl-sys v0.9.98

Caused by:
  process didn't exit successfully: /home/crates/sources/scryer-prolog-0.9.4/target/debug/build/openssl-sys-bab20857b695b75c/build-script-main (exit status: 101)
```
Solution:  
```
apt install -y pkg-config libssl-dev
export PKG_CONFIG_PATH=/usr/lib/x86_64-linux-gnu/pkgconfig
```  
Solution can be applied to packages such as: `scryer-prolog`.  

## `-Zdisable-inter` option
In our work, we provide the ablation study to compare the performance of interprocedural analysis. You can also disable it with following cmd option:
```
cargo typepulse -- -Zdisable-inter
```

## Benchmark: Clippy
Run Clippy to compare the performance of TypePulse as described in Table 4.  
```
cargo +nightly-2023-06-02 clippy -- -Aclippy::all -W clippy::cast_ptr_alignment -W clippy::unsound_collection_transmute
```
