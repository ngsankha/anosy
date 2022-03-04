#!/bin/bash

set -e

TIMES=20

echo "{}" > expt2.json
python3 e2e.py --times $TIMES --k 1
python3 e2e.py --times $TIMES --k 3
python3 e2e.py --times $TIMES --k 5
python3 e2e.py --times $TIMES --k 7
python3 e2e.py --times $TIMES --k 10
python3 process.py
