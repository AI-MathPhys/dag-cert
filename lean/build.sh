#!/bin/sh
# quiet build: errors and warnings only
lake build 2>&1 | grep -E '^(error|warning)|✖|Build completed|sorry' -A6 | grep -vE '^trace|LEAN_PATH' | cut -c1-600 | head -${1:-90}
