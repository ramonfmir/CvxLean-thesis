import CvxLean

noncomputable section

open CvxLean Minimization Real

namespace Chapter7

section ReachingOutToTheOptimizationCommunity

/-! Section 7.3 -/

def p :=
  optimization (x y : ℝ)
    minimize -2 * x
    subject to
      c₁ : 0 ≤ x
      c₂ : 1 < y
      c₃ : log (y - 1) ≤ 2 * sqrt x + 1
      c₄ : 3 * x + 5 * y ≤ 10

equivalence* eqv/q : p := by
  change_of_variables! (v) (y ↦ v + 1)
  change_of_variables! (w) (v ↦ exp w)
  remove_constr c₂ =>
    field_simp; arith
  rw_constr c₃ into (w ≤ 2 * sqrt x + 1) =>
    field_simp

solve q

#eval eqv.backward_map q.solution

end ReachingOutToTheOptimizationCommunity

end Chapter7

end
