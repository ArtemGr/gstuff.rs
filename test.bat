cargo test --all-features
cargo test --features base62

cargo test --features nightly,lines lines:: -- --nocapture --test-threads 1
cargo bench --features nightly,lines lines::

cargo test --features nightly,sqlite lines::csq_test:: -- --nocapture --test-threads 1
cargo bench --features nightly,sqlite lines::csq_bench::
