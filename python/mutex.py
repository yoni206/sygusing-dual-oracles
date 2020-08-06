import pycvc4
from pycvc4 import kinds
print(pycvc4.__init__)
slv = pycvc4.Solver()
slv.setOption("lang", "sygus2")
slv.setOption("uf-ho", "true")
slv.setOption("incremental", "false")
slv.setOption("dag-thresh", "0")
slv.setLogic("ALL");
S = slv.mkUninterpretedSort("S")
BOOL = slv.getBooleanSort()
f = slv.mkVar(BOOL, "f")
ux = slv.mkVar(BOOL, "ux")
uy = slv.mkVar(BOOL, "uy")
x = slv.mkVar(S, "x")
y = slv.mkVar(S, "y")
start_bool = slv.mkVar(BOOL, "StartBool")
start_S = slv.mkVar(S, "StartS")
g = slv.mkSygusGrammar({f,ux,uy,x,y}, {start_bool, start_S})
And = slv.mkTerm(kinds.And, start_bool, start_bool)
Or = slv.mkTerm(kinds.Or, start_bool, start_bool)
Not = slv.mkTerm(kinds.Not, start_bool)
Eq = slv.mkTerm(kinds.Equal, start_S, start_S)
Ite = slv.mkTerm(kinds.Ite, start_bool, start_bool, start_bool)
g.addRules(start_bool, {f, ux, uy,And, Not, Eq})
g.addRules(start_S, {x,y})
g.addAnyVariable(start_bool)
g.addAnyConstant(start_bool)
g.addAnyVariable(start_S)
g.addAnyConstant(start_S)
inv_matrix = slv.synthFun("inv_matrix", [f, ux, uy, x, y], BOOL, g)

var_f = slv.mkSygusVar(BOOL, "f")
var_new_f = slv.mkSygusVar(BOOL, "new_f")
fun_sort = slv.mkFunctionSort(S, BOOL)
var_u = slv.mkSygusVar(fun_sort, "u")
var_new_u = slv.mkSygusVar(fun_sort, "new_u")
var_s = slv.mkSygusVar(S, "s")

bound_var_x = slv.mkVar(S, "x")
bound_var_y = slv.mkVar(S, "y")
bvl = slv.mkTerm(kinds.BoundVarList, bound_var_x)

# init => inv
uempty = slv.mkTerm(kinds.Forall, bvl, slv.mkTerm(kinds.Not, slv.mkTerm(kinds.ApplyUf, [var_u, bound_var_x])))
left1 = slv.mkTerm(kinds.And, var_f, uempty)
bound_u_x = slv.mkTerm(kinds.ApplyUf, [var_u, bound_var_x])
bound_u_y = slv.mkTerm(kinds.ApplyUf, [var_u, bound_var_y])
inv_holds = slv.mkTerm(kinds.ApplyUf, [inv_matrix, var_f, bound_u_x, bound_u_y, bound_var_x, bound_var_y])
bvl1 = slv.mkTerm(kinds.BoundVarList, bound_var_x, bound_var_y)
right1 = slv.mkTerm(kinds.Forall, bvl1, inv_holds)
constraint1 = slv.mkTerm(kinds.Implies, left1, right1)
#slv.addSygusConstraint(constraint1)

# inv /\ trans1 => inv'
bound_var_x_2 = slv.mkVar(S, "x_2")
bound_var_y_2 = slv.mkVar(S, "y_2")
bound_u_x_2 = slv.mkTerm(kinds.ApplyUf, [var_u, bound_var_x_2])
bound_u_y_2 = slv.mkTerm(kinds.ApplyUf, [var_u, bound_var_y_2])
inv_holds = slv.mkTerm(kinds.ApplyUf, inv_matrix, var_f, bound_u_x_2, bound_u_y_2, bound_var_x_2, bound_var_y_2)
bvl2 = slv.mkTerm(kinds.BoundVarList, [bound_var_x_2, bound_var_y_2])
inv_holds_universal = slv.mkTerm(kinds.Forall, bvl2, inv_holds)
new_u_x = slv.mkTerm(kinds.ApplyUf, var_new_u, bound_var_x_2)
new_u_y = slv.mkTerm(kinds.ApplyUf, var_new_u, bound_var_y_2)
disjunction = slv.mkTerm(kinds.Or, bound_u_y, slv.mkTerm(kinds.Equal, bound_var_y_2, bound_var_x_2))
bvl3 = slv.mkTerm(kinds.BoundVarList, [bound_var_y_2])
universal_formula = slv.mkTerm(kinds.Forall, bvl3, slv.mkTerm(kinds.Equal, new_u_y, disjunction))
bvl4 = slv.mkTerm(kinds.BoundVarList, [bound_var_y_2])
existential_formula = slv.mkTerm(kinds.Exists, bvl4, universal_formula)
trans1 = slv.mkTerm(kinds.And, var_f, slv.mkTerm(kinds.Not,var_new_f), existential_formula)
left2 = slv.mkTerm(kinds.And, inv_holds_universal, trans1)
inv_holds_new = slv.mkTerm(kinds.ApplyUf, inv_matrix, var_new_f, new_u_x, new_u_y, bound_var_x_2, bound_var_y_2)
bvl5 = slv.mkTerm(kinds.BoundVarList, [bound_var_x_2, bound_var_y_2])
right2 = slv.mkTerm(kinds.Forall, bvl5, inv_holds_new)
constraint2 = slv.mkTerm(kinds.Implies, left2, right2)
slv.addSygusConstraint(slv.mkTerm(kinds.And, constraint1, constraint2))



# inv /\ trans2 => inv'
bvl = slv.mkTerm(kinds.BoundVarList, [bound_var_x])
existential_formula = slv.mkTerm(kinds.Exists, bvl, slv.mkTerm(kinds.And, bound_u_x, universal_formula))
bvl = slv.mkTerm(kinds.BoundVarList, [bound_var_y])
universal_formula = slv.mkTerm(kinds.Forall, bvl, slv.mkTerm(kinds.Equal, new_u_y, slv.mkTerm(kinds.And, bound_u_y, slv.mkTerm(kinds.Distinct, bound_var_y, bound_var_x))))
trans2 = slv.mkTerm(kinds.And, var_new_f, existential_formula)
left = slv.mkTerm(kinds.And, inv_holds_universal, trans2)
# right it as before)
constraint = slv.mkTerm(kinds.Implies, left, right2)
#slv.addSygusConstraint(constraint)

# inv => safe
left = inv_holds_universal
bvl = slv.mkTerm(kinds.BoundVarList, [bound_var_x, bound_var_y])
right = slv.mkTerm(kinds.Forall, bvl, slv.mkTerm(kinds.Implies, slv.mkTerm(kinds.And, bound_u_x, bound_u_y) , slv.mkTerm(kinds.Equal, bound_var_x, bound_var_y)))
constraint = slv.mkTerm(kinds.Implies, left, right)
# #slv.addSygusConstraint(constraint)

# print solutions if available

if (slv.checkSynth().isUnsat()):
  # Output should be equivalent to:
  # (define-fun max ((x Int) (y Int)) Int (ite (<= x y) y x))
  # (define-fun min ((x Int) (y Int)) Int (ite (<= x y) x y))
    print("solution is:")
    slv.printSynthSolution()
else:
    print("no solution!")
