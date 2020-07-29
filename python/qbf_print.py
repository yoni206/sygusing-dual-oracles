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

parser = SmtLibParser()
script = parser.get_script(cStringIO(DEMO_SMTLIB))
f = script.get_last_formula()
printer = QBFPrinter(None, get_env())
printer.printer(f)
