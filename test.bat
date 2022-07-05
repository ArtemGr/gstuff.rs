cargo test --all-features
cargo test --features base62
cargo test --features nightly,lines lines:: -- --nocapture --test-threads 1
cargo bench --features nightly,lines lines::
