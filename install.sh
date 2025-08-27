#!/bin/bash
RUSTFLAGS="-A warnings" cargo install --path "$(dirname $0)" --force --locked -j 16
