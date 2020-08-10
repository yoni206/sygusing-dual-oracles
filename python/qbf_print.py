import sys
from pysmt.oracles import *
from pysmt.printers import *
from pysmt.shortcuts import *
from pysmt.rewritings import *
from pysmt.smtlib.parser import SmtLibParser
from six.moves import cStringIO # Py2-Py3 Compatibility

file_path = sys.argv[1]

def is_pnf(f):
    cur = f
    while cur.is_quantifier():
      cur = cur.args()[0] 
    qfo = QuantifierOracle()
    return qfo.is_qf(cur)
  

def printer(f):
    cur = f
    prefixes = []
    clauses = []
    assert is_pnf(f)
    if not is_pnf(f):
      prenex_f = prenex_normal_form(f)
    else:
      prenex_f = f
    cur = prenex_f
    while cur.is_quantifier():
      prefix = (cur.node_type(), cur.quantifier_vars())
      prefixes.append(prefix)
      cur = cur.args()[0]
    body = cur
    old_vars = body.get_free_variables()
#    body = cnf(body)
    new_vars = body.get_free_variables()        
    coding = {}
    counter = 1
    for new_var in new_vars:
      coding[new_var] = str(counter)
      counter = counter + 1
    

    fresh_vars = [v for v in new_vars if v not in old_vars]
    prefixes.append((op.EXISTS, fresh_vars))
    prefixes.insert(0,(op.EXISTS, prenex_f.get_free_variables()))

    list_of_text_prefixes = []
    for prefix in prefixes:
      variables = [coding[v] for v in prefix[1]]
      if not variables:
          # skip if not binding anything
          continue
      quantifier_letter = "a" if prefix[0] == op.FORALL else "e"
      text_prefix = quantifier_letter + " " + " ".join(variables) + " 0"
      list_of_text_prefixes.append(text_prefix)
    
    assert(body.is_and())
    clauses = list(conjunctive_partition(body))
    textual_clauses = []
    for clause in clauses:
      assert(clause.is_or() or clause.is_literal())
      clause = list(disjunctive_partition(clause))
      textual_clause = ""
      for l in clause:
        assert(l.is_literal())
        if l.is_not():
          textual_literal = "-" + coding[l.args()[0]]
        else:
          textual_literal = coding[l]
        textual_clause += textual_literal + " "
      textual_clauses.append(textual_clause + "0")
    textual_text = "\n".join(list_of_text_prefixes) + "\n" + "\n".join(textual_clauses)
    textual_text = "p cnf " + str(len(new_vars)) + " "  + str(len(textual_clauses)) + "\n" + textual_text 
    print("c " + repr({str(k): int(v) for k, v in coding.items()}))
    print(textual_text)



parser = SmtLibParser()
with open(file_path, "r") as f:
  script = parser.get_script(f)
f = script.get_last_formula()
printer(f)
