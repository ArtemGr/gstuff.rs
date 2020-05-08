#!/bin/sh
set -ex
RUSTFLAGS=-Ctarget-cpu=native cargo bench --all-features
