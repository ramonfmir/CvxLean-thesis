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

end Chapter5

end
