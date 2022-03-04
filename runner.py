from plumbum import local, FG, TF
from plumbum.cmd import ghc, liquid, rm
import argparse
import time
from parse import parse
import fileinput
import numpy as np
from scipy.stats import iqr
import csv

BENCHMARKS = [
  'Birthday',
  'Ship',
  'Photo',
  'Pizza',
  'Travel'
]

DOM_SIZES = {
  'Birthday': 365 * (1992 - 1956 + 1),
  'Ship': 101 * 501 * 501,
  'Photo': (2010 - 1900 + 1) * 2 * 4,
  'Pizza': 5 * (2002 - 1900 + 1) * (39103178 - 38867884 + 1) * (77058199 - 76825926 + 1),
  'Travel': 200 * (2011 - 1900 + 1) * 6 * 50
}

BENCHMARKS_SRC_PATH = 'benchmarks/'
BENCHMARKS_PATH = 'examples/'
GHC_PKG_ENV = 'anosy'

parser = argparse.ArgumentParser(description='Run Anosy benchmarks')
parser.add_argument('--times', '-t', dest='times', action='store', type=int,
                    default=11, help='number of times to run the benchmark')
parser.add_argument('--smallbench', dest='smallbench', action='store_true', default=False,
                    help='use the small benchmark suite for data collection')

def writeMain(bench, approx):
  mainSrc = '''\
module Main where

import {}Gen
import PowerSet
import Interval

main = do
  print (sizePowerset fst)
  print (sizePowerset snd)
  where
    (fst, snd) = {}Ind
  '''.format(bench, approx)
  with open('Main.hs', 'w') as f:
    f.write(mainSrc)

def mod_directive(approx, k, src, dst):
  with fileinput.input(files=(src)) as f:
    newlines = []
    for line in f:
      if "{-# ANN module (" in line:
        newlines.append('{{-# ANN module ("{}", "query", {} :: Int) #-}}'.format(approx, k))
      else:
        newlines.append(line)
    with open(dst, 'w') as fw:
      fw.write(''.join(newlines))

def collect(args, approx, k, output_csv):
  if args.smallbench:
    curr_benchmarks = ['Ship']
    times = 1
  else:
    curr_benchmarks = BENCHMARKS
    times = args.times
  
  csv_file = [['Benchmark', 'Size True', 'Size False', 'Verif. Time Median', 'Synth. Time Median', 'Verif. Time SIQR', 'Synth. Time SIQR']]

  for bench in curr_benchmarks:
    synth_times = []
    verif_times = []

    mod_directive(approx, k, BENCHMARKS_SRC_PATH + bench + '.hs', BENCHMARKS_PATH + bench + '.hs')
    local.cwd.chdir(BENCHMARKS_PATH)

    for i in range(times):
      start_time = time.time()
      ghc['-package-env', GHC_PKG_ENV, '-fplugin=AnosySynth', bench + '.hs'] & TF(FG=True)
      end_time = time.time()
      synth_times.append(end_time - start_time)
      
      rm['-rf', '.liquid']
      
      start_time = time.time()
      liquid[bench + 'Gen.hs'] & TF(FG=True)
      end_time = time.time()
      verif_times.append(end_time - start_time)
      
      writeMain(bench, approx)
      ghc['Main.hs'] & TF(FG=True)
      out = local["./Main"]()
      trueSize, falseSize = parse("{}\n{}\n", out).fixed

    local.cwd.chdir('..')

    if str(falseSize) == "-1":
      falseSize = DOM_SIZES[bench]

    row = [bench, trueSize, falseSize,
           np.median(verif_times), iqr(verif_times) / 2,
           np.median(synth_times), iqr(synth_times) / 2]
    csv_file.append(row)

  with open(output_csv, 'w') as f:
    csvwriter = csv.writer(f)
    csvwriter.writerows(csv_file)
  # if args.smallbench:
  #   print("Synth. time: {}".format(synth_times[0]))
  #   print("Verif. time: {}".format(verif_times[0]))
  #   print("True Size: {}".format(trueSize))
  #   print("False Size: {}".format(falseSize))

args = parser.parse_args()
collect(args, 'underapprox', 1, 'underapprox1.csv')
collect(args, 'overapprox',  1, 'overapprox1.csv')
collect(args, 'underapprox', 3, 'underapprox3.csv')
collect(args, 'overapprox',  3, 'overapprox3.csv')
