#!/bin/bash

set -ex
rm ~/.ghc/x86_64-darwin-8.10.1/environments/qif || true
cabal v2-build
cabal v2-install --lib --package-env=qif
cd ../examples
ghc -package-env qif -fplugin=AnosySynth Birthday.hs
