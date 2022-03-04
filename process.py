import json
import csv
import matplotlib
matplotlib.use('agg')
import matplotlib.pyplot as plt
import numpy as np

plt.rcParams["figure.figsize"] = [9,6]

def query_count_plot(filename, count_data):
  plt.figure()
  plt.figure().clear()
  plt.close()
  plt.cla()
  plt.clf()

  fig, ax2 = plt.subplots()
  ubound = 0

  for k, counts in count_data.items():
    ubound = max(ubound, counts[0])
    ax2.plot(range(1, len(counts) + 1), counts, label=str(k))

  ax2.set_yticks(list(range(0, ubound, 2)))
  ax2.set_ylabel('# Instances (different executions)')
  ax2.legend(loc='best', title='k =')
  ax2.set_xlabel('# Authorized declassification queries')
  plt.autoscale()
  # plt.xlim([0.9, 14.1])
  # plt.ylim([0.9, 20.1])
  plt.savefig(filename, bbox_inches='tight')

with open('expt2.json') as f:
  data = json.load(f)

count_data = {}

for k, unders in data.items():
  counts = []

  for under in unders:
    for i in range(len(under)):
      if i > (len(counts) - 1):
        counts.append(1)
      else:
        counts[i] += 1
  
  count_data[k] = counts

# print(count_data)
query_count_plot('fig6.pdf', count_data)
