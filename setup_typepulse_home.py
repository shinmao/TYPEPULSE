#!/usr/bin/python3
import os
import subprocess
import sys

from pathlib import Path

if len(sys.argv) < 2:
    print(f"Usage: {sys.argv[0]} <path>", file=sys.stderr)
    exit(1)

typepulse_home_path = Path(sys.argv[1])

# Sanity check
if typepulse_home_path.exists():
    print(f"Error: {typepulse_home_path} already exists", file=sys.stderr)
    exit(1)

# match directory names with the typepulse runner
typepulse_home_path.mkdir()

cargo_home_path = typepulse_home_path / "cargo_home"
cargo_home_path.mkdir()

sccache_home_path = typepulse_home_path / "sccache_home"
sccache_home_path.mkdir()

typepulse_cache_path = typepulse_home_path / "typepulse_cache"
typepulse_cache_path.mkdir()

campaign_path = typepulse_home_path / "campaign"
campaign_path.mkdir()