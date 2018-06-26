#!/bin/bash

set -e

./sparrow -cfg $1 > a.json
./sparrow_vis a.json
rm a.json
