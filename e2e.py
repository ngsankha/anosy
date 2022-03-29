import argparse
import traceback
from z3 import ForAll, Int, Ints, If, And, Or, Optimize, Not, Implies, set_param, unsat, simplify, Z3_toggle_warning_messages
import random
import json

set_param('opt.priority', 'pareto')
Z3_toggle_warning_messages(False)

def absolute(x):
  return If(x > 0, x, -x)

def nearby(x, y):
  return (absolute(x - 200) + absolute(y - 200) <= 100)

def between_int(x, lower, upper):
  return And(lower <= x, x <= upper)

def between_loc(x, y, lowerx, upperx, lowery, uppery):
  return And(between_int(x, lowerx, upperx), between_int(y, lowery, uppery))

def powerset_size(dom):
  return sum(map(lambda x: (x[1] - x[0] + 1) * (x[3] - x[2] + 1), dom['pos'])) - sum(map(lambda x: (x[1] - x[0] + 1) * (x[3] - x[2] + 1), dom['neg']))

def in_powerset(xmin, xmax, ymin, ymax, pset):
  accum = False
  for item in pset['pos']:
    accum = Or(accum, And(item[0] <= xmin, xmax <= item[1], item[2] <= ymin, ymax <= item[3]))
  for item in pset['neg']:
    accum = And(accum, Not(And(item[0] <= xmin, xmax <= item[1], item[2] <= ymin, ymax <= item[3])))
  return And(xmin <= xmax, ymin <= ymax, accum)

def overapprox_bounds(x, y, pset):
  accum = False
  for item in pset['pos']:
    accum = Or(accum, And(item[0] <= x, x <= item[1], item[2] <= y, y <= item[3]))
  for item in pset['neg']:
    accum = And(accum, Not(And(item[0] <= x, x <= item[1], item[2] <= y, y <= item[3])))
  return accum

def underapprox(prior, response, k):
  powerset = []
  x, y, xmin, xmax, ymin, ymax = Ints('x y xmin xmax ymin ymax')
  s = Optimize()
  s.set("timeout", 10000)
  s.add(in_powerset(xmin, xmax, ymin, ymax, prior))

  s.push()

  for i in range(k):
    if response:  # response = True
      accum = nearby(x, y)
    else:  # response = False
      accum = Not(nearby(x, y))
    # print(powerset)
    for region in powerset:
      lowerx, upperx, lowery, uppery = region
      accum = And(accum, Not(between_loc(x, y, lowerx, upperx, lowery, uppery)))
    
    # underapprox
    s.add(ForAll([x, y], Implies(between_loc(x, y, xmin, xmax, ymin, ymax), accum)))
    s.maximize(xmax - xmin)
    s.maximize(ymax - ymin)
    if s.check() != unsat:
      m = s.model()
      powerset.append([int(str(m.evaluate(xmin))),
                      int(str(m.evaluate(xmax))),
                      int(str(m.evaluate(ymin))),
                      int(str(m.evaluate(ymax)))])
      s.pop()
    else:
      # print('unsat')
      # print(s.unsat_core())
      raise RuntimeError
      # break

  return {'pos': powerset, 'neg': []}

def overapprox(prior):
  # only response = True makes sense here
  bound = None
  powerset = []
  x, y, xmin, xmax, ymin, ymax = Ints('x y xmin xmax ymin ymax')
  s = Optimize()
  s.set("timeout", 10000)
  s.add(in_powerset(xmin, xmax, ymin, ymax, prior))

  s.push()

  for i in range(k):
    if bound is None:
      accum = nearby(x, y)
    else:
      accum = Not(nearby(x, y))
    # print(powerset)
    for region in powerset:
      lowerx, upperx, lowery, uppery = region
      accum = And(accum, Not(between_loc(x, y, lowerx, upperx, lowery, uppery)))

    # overapprox
    if bound is None:
      s.add(ForAll([x, y], Implies(And(accum, overapprox_bounds(x, y, prior)),
        between_loc(x, y, xmin, xmax, ymin, ymax))))
      s.minimize(xmax - xmin)
      s.minimize(ymax - ymin)
    else:
      s.add(ForAll([x, y], Implies(between_loc(x, y, xmin, xmax, ymin, ymax),
        And(accum, overapprox_bounds(x, y, {'pos': [bound], 'neg': []})))))
      s.maximize(xmax - xmin)
      s.maximize(ymax - ymin)
    if s.check() != unsat:
      m = s.model()
      if bound is None:
        bound = [int(str(m.evaluate(xmin))),
                 int(str(m.evaluate(xmax))),
                 int(str(m.evaluate(ymin))),
                 int(str(m.evaluate(ymax)))]
      else:
        powerset.append([int(str(m.evaluate(xmin))),
                         int(str(m.evaluate(xmax))),
                         int(str(m.evaluate(ymin))),
                         int(str(m.evaluate(ymax)))])
      s.pop()
    else:
      # print('unsat')
      # print(s.unsat_core())
      raise RuntimeError
      # break
  
  return {'pos': [bound], 'neg': powerset}

def intersect_one2one(a, b):
  res = [max(int(str(a[0])), int(str(b[0]))), min(int(str(a[1])), int(str(b[1]))), max(int(str(a[2])), int(str(b[2]))), min(int(str(a[3])), int(str(b[3])))]
  if res[0] <= res[1] and res[2] <= res[3]:
    return res
  else:
    return None

def intersect_one2many(a, b):
  return map(lambda d: intersect_one2one(a, d), b)

def intersect_many2many(a, b):
  res = []
  for item in a:
    intersected = list(intersect_one2many(item, b))
    res.extend(intersected)
  return filter(lambda i: i is not None, res)

def intersect(pset1, pset2):
  return {'pos': list(intersect_many2many(pset1['pos'], pset2['pos'])), 'neg': [*pset1['neg'], *pset2['neg']]}

def rand_pos(pos):
  return random.choice(list(map(lambda x: [random.randint(int(str(x[0])), int(str(x[1]))), random.randint(int(str(x[2])), int(str(x[3])))], pos)))

def in_neg(pt, neg):
  return any(map(lambda x: x[0] <= pt[0] and pt[0] <= x[1] and x[2] <= pt[1] and pt[1] <= x[3], neg))

def gen_secret(prior):
  secret = rand_pos(prior['pos'])
  while in_neg(secret, prior['neg']):
    secret = rand_pos(prior['pos'])
  return secret

def gen_query(prior):
  randpt = gen_secret(prior)
  def tmp(x, y):
    return (absolute(x - randpt[0]) + absolute(y - randpt[1]) <= 100)
  return tmp

def policy(post_true, post_false):
  size_true = powerset_size(post_true)
  size_false = powerset_size(post_false)
  if not isinstance(size_true, int):
    size_true = int(str(simplify(size_true)))
  if not isinstance(size_false, int):
    size_false = int(str(simplify(size_false)))
  if size_true >= 100 and size_false >= 100:
    return True
  else:
    return False

results = []

parser = argparse.ArgumentParser(description='Run Anosy Declassifcation benchmarks')
parser.add_argument('--times', '-t', dest='times', action='store', type=int,
                    default=20, help='number of times to run the declassification benchmark')
parser.add_argument('--k', '-k', dest='k', action='store', type=int,
                    default=1, help='size of powersets')

args = parser.parse_args()
k = args.k

with open('expt2.json', 'r') as f:
  data = json.load(f)

for j in range(args.times):
  print("Running instance {}/{} with k={}".format(j + 1, args.times, k))
  random.seed(42 * j + 1)
  prior = {'pos': [[0, 400, 0, 400]], 'neg': []}
  over_prior = prior
  under_prior = prior
  secret = gen_secret(prior)
  print("Secret: {}".format(secret))

  curr_run = []
  curr_run_over = []

  skip_over = True
  skip_under = False

  for i in range(50):
    if isinstance(powerset_size(under_prior), int):
      under_size = powerset_size(under_prior)
    else:
      under_size = simplify(powerset_size(under_prior))
    if isinstance(powerset_size(over_prior), int):
      over_size = powerset_size(over_prior)
    else:
      over_size = simplify(powerset_size(over_prior))

    print("Under: {}, Over: {}".format(under_size, over_size))
    if not skip_under:
      curr_run.append(under_size)
    if not skip_over:
      curr_run_over.append(over_size)

    if not skip_under:
      nearby = gen_query(under_prior)
      try:
        pset_true = intersect(under_prior, underapprox(under_prior, True, k))
        pset_false = intersect(under_prior, underapprox(under_prior, False, k))
      except Exception as e:
        print('========= Policy violation ==========')
        skip_under = True

      if not policy(pset_true, pset_false):
        print('========= Policy violation ==========')
        skip_under = True
      else:
        if str(simplify(nearby(secret[0], secret[1]))) == 'True':
          under_prior = pset_true
        else:
          under_prior = pset_false

    if not skip_over:
      nearby = gen_query(over_prior)
      try:
        pset_true = intersect(over_prior, overapprox(over_prior))
        pset_false = over_prior
      except:
        print('========= Policy violation ==========')
        skip_over = False

      if not policy(pset_true, pset_false):
        print('========= Policy violation ==========')
        skip_over = True
      else:
        if str(simplify(nearby(secret[0], secret[1]))) == 'True':
          over_prior = pset_true
        else:
          over_prior = pset_false
    
    if skip_over and skip_under:
      break
    
    if i == 49:
      print('========= End of Iter ==========')

    # print(underapprox(under_prior, True))
    # try:
    # pset_true = intersect(under_prior, underapprox(under_prior, True))
    # pset_false = intersect(under_prior, underapprox(under_prior, False))
    # except RuntimeError:
    #   imprecise = True
    #   print('========= Imprecise ==========')
    #   break
    
    # print("response: {}".format(simplify(nearby(secret[0], secret[1]))))
    # if str(simplify(nearby(secret[0], secret[1]))) == 'True':
    #   if policy(pset_true):
    #     under_prior = pset_true
    #   else:
    #     print('========= Policy violation ==========')
    #     break
    # else:
    #   if policy(pset_false):
    #     under_prior = pset_false
    #   else:
    #     print('========= Policy violation ==========')
    #     break

    
    # if str(simplify(nearby(secret[0], secret[1]))) == 'True':
    #   if policy(pset_true):
    #     over_prior = pset_true
    #   else:
    #     break
    # else:
    #   if policy(pset_false):
    #     over_prior = pset_false
    #   else:
    #     break
  results.append(curr_run)
    # results_over.append(curr_run_over)
  # print(results)

# k controls precision
# k = 3

print(results)

data[k] = results

with open('expt2.json', 'w') as f:
  json.dump(data, f)
# print("------")
# print(results_over)
