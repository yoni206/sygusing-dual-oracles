from pysmt.smtlib.parser import SmtLibParser
from pysmt.shortcuts import *
import sys
import os

path = sys.argv[1]
proof_size = int(sys.argv[2])
with open(path, "r") as f:
  script_str = f.read()
parser = SmtLibParser()
script = parser.get_script_fname(path)
smtlib_formula = script.get_strict_formula()
assert(smtlib_formula.is_and())
for clause in smtlib_formula.args():
  assert(clause.is_or())
  for l in clause.args():
    assert(l.is_literal())
cnf_formula = [ list(set(clause.args())) for clause in smtlib_formula.args()]
free_vars = smtlib_formula.get_free_variables()

def superset_of_union_minus_pivot(i,j,k,p):
  return And([Implies(Or(indicators[(v,j,polarity)], indicators[(v,k,polarity)]), indicators[(v,i,polarity)]) for v in free_vars for polarity in [True, False] if v != p])

def subset_of_union(i,j,k):
  return And([Implies(indicators[(v,i,polarity)], Or(indicators[(v,j,polarity)], indicators[(v,k,polarity)])) for v in free_vars for polarity in [True, False]])

def is_pivot(j,k,v):
  return Or(And(indicators[(v,j,True)], Not(indicators[(v,j,False)]) ,indicators[(v,k,False)], Not(indicators[(v,k,True)])), And(indicators[(v,j,False)], Not(indicators[(v,j,True)]) ,indicators[(v,k,True)], Not(indicators[(v,k,False)])))

def not_in(i,v):
  return And(Not(indicators[(v,i,True)]), Not(indicators[(v,i,False)]))

def resolvent_of_by(i,j,k,p):
  return And(is_pivot(j,k,p), not_in(i,p), subset_of_union(i,j,k), superset_of_union_minus_pivot(i,j,k,p))

def resolvent_of(i,j,k):
  return Or([resolvent_of_by(i,j,k,v) for v in free_vars])

def resolvent(i):
  return Or([resolvent_of(i,j,k) for j in range(i) for k in range(j)])

def make_literal(polarity, var):
  return var if polarity else Not(var)

def superset_of_original(i, c):
  return And([indicators[(var, i, polarity)] for var in free_vars for polarity in [True, False] if make_literal(polarity, var) in c])

def subset_of_original(i, c):
  return And([Not(indicators[(var, i, polarity)]) for var in free_vars for polarity in [True, False] if make_literal(polarity, var) not in c])

def copy_of(i, c):
  return And(subset_of_original(i, c), superset_of_original(i, c))

def copy_of_original(i):
  return Or([copy_of(i, c) for c in cnf_formula])

def clause_is_justified(i):
  assert(i in range(0, proof_size))
  return Or([copy_of_original(i), resolvent(i)])

def is_proof():
  return And([clause_is_justified(i) for i in range(proof_size)])

def bottom_included():
  return Or([And([Not(indicators[(var, proof_clause_index, polarity)]) for var in free_vars for polarity in [True, False] ]) for proof_clause_index in range(proof_size)])

def is_proof_of_bottom():
  return And(is_proof(), bottom_included())




indicators = {(var, proof_clause_index, polarity) : Symbol(str(var) + "_is_in_clause_" + str(proof_clause_index) + "_of_proof_" + ("positively" if polarity else "negatively"), BOOL) for var in free_vars for proof_clause_index in range(proof_size) for polarity in {True, False}}
result = is_proof_of_bottom()
write_smtlib(result, path + "_dual.smt2")
print("finished computing formula")
solver = Solver("z3")
solver.add_assertion(result)
answer = solver.check_sat()
if answer:
  proof = [[make_literal(polarity, var) for var in free_vars for polarity in [True, False] if solver.get_value(indicators[(var,i,polarity)]).is_true()] for i in range(proof_size) ]
  print("\n".join([str(clause) for clause in proof]))
else:
  print("no proof")
