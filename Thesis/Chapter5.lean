import CvxLean

noncomputable section

open CvxLean Minimization Real

namespace Chapter5

namespace MotivatingExample

/-! Section 5.1 -/

def p :=
  optimization (x : ℝ)
    minimize x
    subject to
      c₁ : 1e-3 ≤ x
      c₂ : 1 / sqrt x ≤ exp x

equivalence eqv₁/p₁ : p := by
  -- DCP fails with the following error:
  --    Failure in constraint c₂:
  --    [Trying atom fun x => rexp x for expression rexp x: Expected concave, but atom is convex]
  fail_if_success dcp

def qByHand :=
  optimization (x : ℝ)
    minimize x
    subject to
      c₁ : 1e-3 ≤ x
      c₂ : exp (-x) ≤ sqrt x

equivalence eqv₂/q₁ : qByHand := by
  -- Here, it succeeds.
  dcp

end MotivatingExample

namespace ProofReconstruction

/-! Section 5.5 -/

open MotivatingExample

-- Here, we see the step-by-step construction by hand.

equivalence* eqv/q : p := by
  rw_constr c₂ =>
    rw [div_le_iff (by arith)]
  rw_constr c₂ =>
    rw [mul_comm]
  rw_constr c₂ =>
    rw [← div_le_iff (by arith)]
  rw_constr c₂ =>
    rw [← exp_neg_eq_one_div]

#print q
#check eqv

solve q

#eval eqv.backward_map q.solution -- 0.426303

end ProofReconstruction

namespace PreDCPProcedure

/-! Section 5.6 -/

open MotivatingExample

-- Now, we show how to get to `q` with the `pre_dcp` tactic.

-- Click on `equivalence*` to see what we send to the `egg` sub-process and what we receive.
equivalence* eqv/q : p := by
  pre_dcp

-- NOTE: This is not exactly the same problem we show in the thesis, but it is equivalent and in
-- DCP form.
#print q
#check eqv

solve q

#eval eqv.backward_map q.solution -- 0.426303

end PreDCPProcedure

namespace EvaluationExamples

/-! Section 5.7.1 -/

def gp :=
  optimization (x y z : ℝ)
    minimize 1 / (x / y)
    subject to
      h1 : 0 < x
      h2 : 0 < y
      h3 : 0 < z
      h4 : 2 ≤ x
      h5 : x ≤ 3
      h6 : x ^ 2 + 3 * y / z ≤ 5 * sqrt y
      h7 : x * y = z ^ 2

equivalence* eqv₁/q₁ : gp := by
  change_of_variables! (u) (x ↦ exp u)
  change_of_variables! (v) (y ↦ exp v)
  change_of_variables! (w) (z ↦ exp w)
  pre_dcp

#print q₁
#check eqv₁

solve q₁

#eval eqv₁.backward_map q₁.solution -- (2.000000, 1.930782, 1.965086)

def qcp :=
  optimization (x y : ℝ)
    minimize -y
    subject to
      h1 : 1 ≤ x
      h2 : x ≤ 2
      h3 : 0 ≤ y
      h4 : sqrt ((2 * y) / (x + y)) ≤ 1

equivalence* eqv₂/q₂ : qcp := by
  pre_dcp

#print q₂
#check eqv₂

solve q₂

#eval eqv₂.backward_map q₂.solution -- (2.000000, 2.000000)

end EvaluationExamples

end Chapter5

end
