from pysmt.printers import *
from pysmt.shortcuts import *
from pysmt.rewritings import *
from pysmt.smtlib.parser import SmtLibParser
from six.moves import cStringIO # Py2-Py3 Compatibility
DEMO_SMTLIB=\
"""
(set-logic ALL)
(set-option :lang smt2)
(set-option :produce-models true)
(define-fun init ((s1 Bool) (s2 Bool)) Bool
  (and (not s1) s2))
(define-fun trans ((s1 Bool) (s2 Bool) (new_s1 Bool) (new_s2 Bool)) Bool
  (and (= new_s1 (or s1 s2))
       (= new_s2 s2))
)
(define-fun safe ((s1 Bool) (s2 Bool)) Bool (not s1))
(declare-const x11 Bool)
(declare-const x12 Bool)
(declare-const x13 Bool)
(declare-const x14 Bool)
(define-fun inv ((s1 Bool) (s2 Bool)) Bool
   (and (safe s1 s2)
        (or
          (and s1 x11)
          (and (not s1) x12)
          (and s2 x13)
          (and (not s2) x14)
        )
))
(assert (forall ((s1 Bool)
                 (s2 Bool))
                 (=> (init s1 s2) (inv s1 s2))))
(assert (forall ((s1 Bool)
                 (s2 Bool)
                 (new_s1 Bool)
                 (new_s2 Bool))
                 (=> (and (inv s1 s2) (trans s1 s2 new_s1 new_s2)) (inv new_s1 new_s2))))
(check-sat)

"""

def printer(f):
    cur = f
    prefixes = []
    clauses = []
    prenex_f = prenex_normal_form(f)
    cur = prenex_f
    while cur.is_quantifier():
      prefix = (cur.node_type(), cur.quantifier_vars())
      prefixes.append(prefix)
      cur = cur.args()[0]
    body = cur
    old_vars = body.get_free_variables()
    body = cnf(body)
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
      quantifier_letter = "a" if prefix[0] == op.FORALL else "e"
      variables = [coding[v] for v in prefix[1]]
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
    print(textual_text)



parser = SmtLibParser()
script = parser.get_script(cStringIO(DEMO_SMTLIB))
f = script.get_last_formula()
printer(f)
