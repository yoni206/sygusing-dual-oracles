from pysmt.smtlib.parser import SmtLibParser
from pysmt.shortcuts import *
import sys
import os
import dualsmt_resolution as dr

def setup(path, proof_size, num_of_extensions):
  proof_size = int(proof_size)
  num_of_extensions = int(num_of_extensions)
  cnf_formula, free_vars = dr.parse_input_formula(path)
  free_vars += [Symbol("__extention_var__" + str(i) + "__") for i in range(num_of_extentions) ]
  indicators = dr.create_new_variables(cnf_formula, free_vars, proof_size)
  extentions = {i: Symbol(str(i) + "_is_extension") for i in range(proof_size)}
  # TODO add cardinality constraints for extentions. otherwise num_of_extentions is meaningless. right?
  return path, proof_size, num_of_extensions, cnf_formula, free_vars, indicators, extentions

def is_er_proof():
    return And([clause_is_justified_in_er_calculus(i) for i in range(proof_size)])

def is_er_proof_of_bottom():
  return And(is_er_proof(), dr.ends_with_bottom())

if __name__ == "__main__":
  # indicators: which variable is found in which clause of the proof and in what polarity
  # extensions: is this a resolution (false) or an extention clause (true)?
  path, proof_size, num_of_extensions, cnf_formula, free_vars, indicators, extensions = setup(sys.argv[1], sys.argv[2], sys.argv[3])
  new_variables = indicators + extensions
  result = is_er_proof_of_bottom()
