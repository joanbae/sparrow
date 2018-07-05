#!/bin/bash

set -e

make
./sparrow $1 -nobar
