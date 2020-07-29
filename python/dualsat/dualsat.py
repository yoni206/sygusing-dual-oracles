import sys
import os
from pysat.solvers import *
from pysat.formula import *

def create_definition(var, clauses, current_largest_variable_id):
  ltr = [[-var] + c for c in clauses ]  
  counter = current_largest_variable_id + 1
  num_of_clauses = len(clauses)
  C = {}
  for i in range(0, num_of_clauses):
    C[i] = counter
    counter = counter +1
  rtl = [[var] + [-C[i] for i in range(0, num_of_clauses)]]
  
  clauses_definitions_ltr = [ [[-C[i]] + list(clauses[i])] for i in range(0, num_of_clauses) ]
  clauses_definitions_rtl = [ [ [C[i], -list(clauses[i])[j]] for j in range(0, len(list(clauses[i])))    ] for i in range(0,num_of_clauses) ]
  result = [ltr] + [rtl] + clauses_definitions_ltr + clauses_definitions_rtl
  return counter, result
  
proof_size = 5

path = sys.argv[1]
formula = CNF(from_file=path)

largest_variable_id = formula.nv
number_of_clauses = len(formula.clauses)

#################################
# introduction of new variables #
#################################

# proof[(i,j,k)] is a new variable that says that the old variable j
# occurrs in the ith clause of the proof negatively (if j=0) or
# positively (if j=1).
proof = {}
counter = 1
for i in range(0, proof_size):
  for j in range(1, largest_variable_id + 1):
    for k in range(0,2):
      proof[(i,j,k)] = counter
      counter = counter + 1

# original[i] is a new variable that says that the ith clause of the proof
# occurrs in the original formula
original = {}
for i in range(0, proof_size):
  original[i] = counter
  counter = counter+1

# copy_of[(i,m)] is a new variable that says that the ith clause of the proof
# is the same as the mth clause of the original formula
copy_of = {}
for i in range(0, proof_size):
  for m in range(0, number_of_clauses):
    copy_of[(i,m)] = counter
    counter = counter + 1

# subclause_of[(i,m)] is a new variable that says that the ith clause of the proof
# is a subclause of the mth clause of the original formula 
subclause_of = {}
for i in range(0, proof_size):
  for m in range(0, number_of_clauses):
    subclause_of[(i,m)] = counter
    counter = counter + 1

# superclause_of[(i,m)] is a new variable that says that the ith clause of the proof
# is a superclauseclause of the mth clause of the original formula 
superclause_of = {}
for i in range(0, proof_size):
  for m in range(0, number_of_clauses):
    superclause_of[(i,m)] = counter
    counter = counter + 1

# pos_subclause_of[(i,m)] is a new variable that says that every positive literal
# that occurs in the ith clause of the proof also occurs in the mth clause
# of the original formula
pos_subclause_of = {}
for i in range(0, proof_size):
  for m in range(0, number_of_clauses):
    pos_subclause_of[(i,m)] = counter
    counter = counter + 1
#TODO the problem is with var 52 that says that the 0 clause of the proof is a positive subclause of the 0 clause of the original formula

# neg_subclause_of[(i,m)] is a new variable that says that every negative literal
# that occurs in the ith clause of the proof also occurs in the mth clause
# of the original formula
neg_subclause_of = {}
for i in range(0, proof_size):
  for m in range(0, number_of_clauses):
    neg_subclause_of[(i,m)] = counter
    counter = counter + 1

# pos_superclause_of[(i,m)] is a new variable that says that every positive literal
# that occurs in the mth clause of the original formula also occurs in the itth clause
# of the proof
pos_superclause_of = {}
for i in range(0, proof_size):
  for m in range(0, number_of_clauses):
    pos_superclause_of[(i,m)] = counter
    counter = counter + 1

# neg_superclause_of[(i,m)] is a new variable that says that every negative literal
# that occurs in the mth clause of the original formula also occurs in the itth clause
# of the proof
neg_superclause_of = {}
for i in range(0, proof_size):
  for m in range(0, number_of_clauses):
    neg_superclause_of[(i,m)] = counter
    counter = counter + 1
 
# resolution[i] is a new variable that says that the ith clause of the proof
# is the result of resolving two *previous* clauses in the proof
resolution = {}
for i in range(0, proof_size):
  resolution[i] = counter
  counter = counter+1

# resolvant[(i,j,k)] is a new variable that says that the ith clause of the proof
# is the resolvant of the jth and kth clauses of the proof
resolvant = {}
for i in range(0, proof_size):
  for j in range(0, proof_size):
    for k in range(0, proof_size):
      resolvant[(i,j,k)] = counter
      counter = counter+1

# pivot[(i,j,k,l)] is a new variable that says that the ith clause of the proof
# is the resolvant of the jth and kth clauses of the proof,
# and that the pivot is the original variable l
pivot = {}
for i in range(0, proof_size):
  for j in range(0, proof_size):
    for k in range(0, proof_size):
      for l in range(1, largest_variable_id+1):
        pivot[(i,j,k,l)]=counter
        counter = counter+1

# pivot_superclause_of[(i,j,k,l)] is a new variable that says that every literal
# that occurs in either the jth or kth clauses of the proof that is different
# from l and from ~l, occurs also in the ith clause of the proof
pivot_superclause_of = {}
for i in range(0, proof_size):
  for j in range(0, proof_size):
    for k in range(0, proof_size):
      for l in range(1, largest_variable_id+1):
        pivot_superclause_of[(i,j,k,l)]=counter
        counter = counter+1

# pivot_subclause_of[(i,j,k,l)] is a new variable that says that every literal
# that occurs in ith clause of the proof is also occurs in either the jth or kth clauses of the proof, and is different than l and ~l.
pivot_subclause_of = {}
for i in range(0, proof_size):
  for j in range(0, proof_size):
    for k in range(0, proof_size):
      for l in range(1, largest_variable_id+1):
        pivot_subclause_of[(i,j,k,l)]=counter
        counter = counter+1

# pivot_superclause_of[(i,j,k,l)] is a new variable that says that every positive literal
# that occurs in either the jth or kth clauses of the proof that is different
# from l and ~l, occurs also in the ith clause of the proof
pivot_pos_superclause_of = {}
for i in range(0, proof_size):
  for j in range(0, proof_size):
    for k in range(0, proof_size):
      for l in range(1, largest_variable_id+1):
        pivot_pos_superclause_of[(i,j,k,l)]=counter
        counter = counter+1

# pivot_subclause_of[(i,j,k,l)] is a new variable that says that every positive literal
# that occurs in ith clause of the proof is also occurs in either the jth or kth clauses of the proof, and is different than l and ~l.
pivot_pos_subclause_of = {}
for i in range(0, proof_size):
  for j in range(0, proof_size):
    for k in range(0, proof_size):
      for l in range(1, largest_variable_id+1):
        pivot_pos_subclause_of[(i,j,k,l)]=counter
        counter = counter+1

# pivot_superclause_of[(i,j,k,l)] is a new variable that says that every negative literal
# that occurs in either the jth or kth clauses of the proof that is different
# from l and ~l, occurs also in the ith clause of the proof
pivot_neg_superclause_of = {}
for i in range(0, proof_size):
  for j in range(0, proof_size):
    for k in range(0, proof_size):
      for l in range(1, largest_variable_id+1):
        pivot_neg_superclause_of[(i,j,k,l)]=counter
        counter = counter+1

# pivot_subclause_of[(i,j,k,l)] is a new variable that says that every negative literal
# that occurs in ith clause of the proof is also occurs in either the jth or kth clauses of the proof, and is different than l and ~l.
pivot_neg_subclause_of = {}
for i in range(0, proof_size):
  for j in range(0, proof_size):
    for k in range(0, proof_size):
      for l in range(1, largest_variable_id+1):
        pivot_neg_subclause_of[(i,j,k,l)]=counter
        counter = counter+1

# bottom_at[i] is a new variable that says that the ith clause of the proof
# is empty
bottom_at = {}
for i in range(0, proof_size):
  bottom_at[i] = counter
  counter = counter+1

bottom_proved = counter
counter = counter+1

legal_proof = counter
counter = counter+1

##############################
# Semantics of new variables #
##############################

def_original = {i: [[copy_of[(i,m)] for m in range(0,number_of_clauses)]] for i in range(0, proof_size)}
def_copy_of = {(i,m): [[subclause_of[(i,m)]], [superclause_of[(i,m)]]] for i in range(0,proof_size) for m in range(0, number_of_clauses)}
def_subclause_of = {(i,m): [[pos_subclause_of[(i,m)]], [neg_subclause_of[(i,m)]]] for i in range(0,proof_size) for m in range(0,number_of_clauses)}
def_superclause_of = {(i,m): [[pos_superclause_of[(i,m)]], [neg_superclause_of[(i,m)]]] for i in range(0,proof_size) for m in range(0,number_of_clauses)}

def_pos_subclause_of =   {(i,m): [[-proof[(i,j,1)]] for j in range(1, largest_variable_id+1) if j not in formula.clauses[m] ] for i in range(0, proof_size) for m in range(0, number_of_clauses)}

def_pos_superclause_of = {(i,m): [[proof[(i,j,1)]] for j in range(1, largest_variable_id+1) if j in formula.clauses[m] ] for i in range(0, proof_size) for m in range(0, number_of_clauses)}

def_neg_subclause_of = {(i,m): [[-proof[(i,j,0)]] for j in range(1, largest_variable_id+1) if -j not in formula.clauses[m] ] for i in range(0, proof_size) for m in range(0, number_of_clauses)}
def_neg_superclause_of = {(i,m): [[proof[(i,j,0)]] for j in range(1, largest_variable_id+1) if -j in formula.clauses[m] ] for i in range(0, proof_size) for m in range(0, number_of_clauses)}

def_resolution = {i: [[resolvant[(i,j,k)] for j in range(0, i) for k in range(0,j)]] for i in range(0, proof_size)}
def_resolvant = {(i,j,k): [[pivot[(i,j,k,l)] for l in range(1, largest_variable_id+1) ]] for i in range(0, proof_size) for j in range(0,i) for k in range(0,j)}
def_pivot = {(i,j,k,l): [[pivot_subclause_of[(i,j,k,l)]], [pivot_superclause_of[(i,j,k,l)]]] for i in range(0, proof_size) for j in range(0,i) for k in range(0,j) for l in range(1, largest_variable_id+1)}
def_pivot_superclause_of = {(i,j,k,l): [[pivot_pos_superclause_of[(i,j,k,l)]], [pivot_neg_superclause_of[i,j,k,l]]] for i in range(0, proof_size) for j in range(0,i) for k in range(0,j) for l in range(1, largest_variable_id+1)}
def_pivot_subclause_of = {(i,j,k,l): [[pivot_pos_subclause_of[(i,j,k,l)]], [pivot_neg_subclause_of[i,j,k,l]]] for i in range(0, proof_size) for j in range(0,i) for k in range(0,j) for l in range(1, largest_variable_id+1)}
def_pivot_pos_superclause_of = {(i,j,k,l): [[-proof[(j,m,1)],proof[(i,m,1)]] for m in range(1, largest_variable_id+1) if abs(m) != l] + [[-proof[(k,m,1)],proof[(i,m,1)]] for m in range(1, largest_variable_id+1) if abs(m) != l] for i in range(0, proof_size) for j in range(0,i) for k in range(0,j) for l in range(1, largest_variable_id+1)}
def_pivot_neg_superclause_of = {(i,j,k,l): [[-proof[(j,m,0)],proof[(i,m,0)]] for m in range(1, largest_variable_id+1) if abs(m) != l] + [[-proof[(k,m,0)],proof[(i,m,0)]] for m in range(1, largest_variable_id+1) if abs(m) != l] for i in range(0, proof_size) for j in range(0,i) for k in range(0,j) for l in range(1, largest_variable_id+1)}
def_pivot_pos_subclause_of = {(i,j,k,l): [[proof[(j,m,1)],-proof[(i,m,1)]] for m in range(1, largest_variable_id+1) if abs(m) != l] + [[proof[(k,m,1)],-proof[(i,m,1)]] for m in range(1, largest_variable_id+1) if abs(m) != l] for i in range(0, proof_size) for j in range(0,i) for k in range(0,j) for l in range(1, largest_variable_id+1)}
def_pivot_neg_subclause_of = {(i,j,k,l): [[proof[(j,m,0)],-proof[(i,m,0)]] for m in range(1, largest_variable_id+1) if abs(m) != l] + [[proof[(k,m,0)],-proof[(i,m,0)]] for m in range(1, largest_variable_id+1) if abs(m) != l] for i in range(0, proof_size) for j in range(0,i) for k in range(0,j) for l in range(1, largest_variable_id+1)}

def_bottom_at = {i: [[-proof[(i,j,1)]] for j in range(1, largest_variable_id+1) ] + [[-proof[(i,j,0)]] for j in range(1, largest_variable_id+1) ]  for i in range(0, proof_size)}
def_bottom_proved = [[bottom_at[i] for i in range(0, proof_size)]]

def_legal_proof = [[original[i], resolution[i]] for i in range(0, proof_size)]

definitions = {}
definitions.update({original[i]: def_original[i] for i in range(0, proof_size)})
definitions.update({copy_of[(i,m)]: def_copy_of[(i,m)] for i in range(0,proof_size) for m in range(0,number_of_clauses)})
definitions.update({subclause_of[(i,m)]: def_subclause_of[(i,m)] for i in range(0,proof_size) for m in range(0,number_of_clauses)})
definitions.update({superclause_of[(i,m)]: def_superclause_of[(i,m)] for i in range(0,proof_size) for m in range(0,number_of_clauses)})
definitions.update({pos_subclause_of[(i,m)]: def_pos_subclause_of[(i,m)] for i in range(0,proof_size) for m in range(0,number_of_clauses)})
definitions.update({pos_superclause_of[(i,m)]: def_pos_superclause_of[(i,m)] for i in range(0,proof_size) for m in range(0,number_of_clauses)})
definitions.update({neg_subclause_of[(i,m)]: def_neg_subclause_of[(i,m)] for i in range(0,proof_size) for m in range(0,number_of_clauses)})
definitions.update({neg_superclause_of[(i,m)]: def_neg_superclause_of[(i,m)] for i in range(0,proof_size) for m in range(0,number_of_clauses)})
definitions.update({resolution[i]: def_resolution[i] for i in range(0, proof_size)})
definitions.update({resolvant[(i,j,k)]: def_resolvant[(i,j,k)] for i in range(0, proof_size) for j in range(0,i) for k in range(0,j)})
definitions.update({pivot[(i,j,k,l)]: def_pivot[(i,j,k,l)] for i in range(0, proof_size) for j in range(0,i) for k in range(0,j) for l in range(1, largest_variable_id+1)})
definitions.update({pivot_superclause_of[(i,j,k,l)]: def_pivot_superclause_of[(i,j,k,l)] for i in range(0, proof_size) for j in range(0,i) for k in range(0,j) for l in range(1, largest_variable_id+1)})
definitions.update({pivot_subclause_of[(i,j,k,l)]: def_pivot_subclause_of[(i,j,k,l)] for i in range(0, proof_size) for j in range(0,i) for k in range(0,j) for l in range(1, largest_variable_id+1)})
definitions.update({pivot_pos_superclause_of[(i,j,k,l)]: def_pivot_pos_superclause_of[(i,j,k,l)] for i in range(0, proof_size) for j in range(0,i) for k in range(0,j) for l in range(1, largest_variable_id+1)})
definitions.update({pivot_pos_subclause_of[(i,j,k,l)]: def_pivot_pos_subclause_of[(i,j,k,l)] for i in range(0, proof_size) for j in range(0,i) for k in range(0,j) for l in range(1, largest_variable_id+1)})
definitions.update({pivot_neg_superclause_of[(i,j,k,l)]: def_pivot_neg_superclause_of[(i,j,k,l)] for i in range(0, proof_size) for j in range(0,i) for k in range(0,j) for l in range(1, largest_variable_id+1)})
definitions.update({pivot_neg_subclause_of[(i,j,k,l)]: def_pivot_neg_subclause_of[(i,j,k,l)] for i in range(0, proof_size) for j in range(0,i) for k in range(0,j) for l in range(1, largest_variable_id+1)})
definitions.update({bottom_at[i]: def_bottom_at[i] for i in range(0, proof_size)})
definitions.update({bottom_proved: def_bottom_proved})
definitions.update({legal_proof: def_legal_proof})


formulas = []
for k in definitions:
  counter, definition = create_definition(k, definitions[k], counter)
  formulas.extend(definition)

formulas.append([[bottom_proved]])
formulas.append([[legal_proof]])

s1 = Solver(name='g3')
for f in formulas:
  for c in f:
      s1.add_clause(c)
result = s1.solve()
print(result)
if result:
  m = s1.get_model()
  mm = [(i,j,k) for i in range(0,proof_size) for j in range(1, largest_variable_id) for k in range(0,2) if proof[(i,j,k)] in m]
  print(mm)
