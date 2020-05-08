#!/bin/sh
set -ex
cargo test --all-features
cargo test --features base62
