import CvxLean

open Lean

namespace Chapter2

namespace TypeTheory

/-! Section 2.1.2 -/

#check Vector.replicate (α := ℝ)

#check Nat
#check Nat.rec

axiom p : Prop

#check p → p

#check Nat.zero

axiom B : Type
axiom A : Type
axiom b : B

#check fun _a : A ↦ b
#check λ _a : A ↦ b
#check fun _a : A => b
#check λ _a : A => b

axiom B' : A → Type
axiom b' : (a : A) → B' a

#check fun a : A => b' a

universe u
axiom b'' : A → Sort u

#check (a : A) → b'' a
#check ∀ a : A, b'' a

end TypeTheory

namespace TacticsOverview

/-! Section 2.1.3 -/

example : ∀ x : ℕ, x + 0 = x := by
  intros n
  exact (Nat.add_zero n)

open Parser Elab Tactic

#check intros
#check exact
#check assumption
#check apply
#check eqRefl -- this is `rfl` as a tactic, note that `rfl` is also a term defined as `Eq.refl`.
#check Std.Tactic.tacticSymm_ -- Again, `symm` can also be a term, we show the tactic here.
#check Mathlib.Tactic.tacticTrans___ -- Similar issue.
#check congr

example {α β γ : Type*} (f h : α → β) (g : γ → α) (x y : γ) : f (g x) = h (g y) := by
  congr! <;> sorry

#check cases
#check induction
#check constructor

#check tacticHave_
#check tacticShow_
#check evalCalc

#check rewriteSeq
#check Mathlib.Tactic.evalNthRewriteSeq

#check simp

#check Mathlib.Tactic.normNum
#check Mathlib.Tactic.RingNF.ring
#check linarith
#check positivity

#check Conv.conv

end TacticsOverview

namespace Metaprogramming

/-! Section 2.1.4 -/

#check Syntax
#check Expr

#check CoreM
#check MetaM
#check Elab.TermElabM
#check Elab.Command.CommandElabM
#check Elab.Tactic.TacticM

end Metaprogramming

namespace FormalizedMathematics

/-! Section 2.1.5 -/

-- <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Real/Basic.html>
-- <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Exp.html>
-- <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Log/Basic.html>
-- <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Pow/Real.html>
-- <https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Convex/Basic.html>
-- <https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Determinant.html>
-- <https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Basis.html>
-- <https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/NonsingularInverse.html>
-- <https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/PosDef.html>
-- <https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/LDL.html>
-- <https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Matrix/Spectrum.html>

end FormalizedMathematics

noncomputable section

namespace DGP

/-! Section 2.2.3 -/

open CvxLean Minimization Real

def gp :=
  optimization (x y z : ℝ)
    minimize 1 / (x / y)
    subject to
      h₁ : 0 < x
      h₂ : 0 < y
      h₃ : 0 < z
      h₄ : 2 ≤ x
      h₅ : x ≤ 3
      h₆ : x ^ 2 + 3 * y / z ≤ 5 * sqrt y
      h₇ : x * y = z ^ 2

-- Note that we need to help the arithmetic tactics a bit to prove results about feasibility.

lemma sqrt_4_eq : sqrt (4 : ℝ) = 2 := by
  have h : (4 : ℝ) = 2 ^ 2 := by norm_num
  rw [h, rpow_two, sqrt_sq]; norm_num

lemma le_sqrt_8 : 2 ≤ sqrt (8 : ℝ) := by
  rw [le_sqrt] <;> norm_num

lemma le_sqrt_10 : 3 ≤ sqrt (10 : ℝ) := by
  rw [le_sqrt] <;> norm_num

lemma sqrt_30_eq_mul : sqrt (30 : ℝ) = sqrt 3 * sqrt 10 := by
  rw [← sqrt_mul] <;> norm_num

-- Now, we show that points `a` and `b` are feasible.

def a : ℝ × ℝ × ℝ := ⟨2, 4, sqrt 8⟩

lemma feasible_a : gp.feasible a := by
  simp [a, gp, feasible, sqrt_4_eq]; norm_num
  rw [add_comm, ← le_sub_iff_add_le, div_le_iff] <;> norm_num
  let x := sqrt (8 : ℝ)
  show 12 ≤ 6 * x
  have h : 2 ≤ x := le_sqrt_8
  linarith

def b : ℝ × ℝ × ℝ := ⟨3, 10, sqrt 30⟩

lemma feasible_b : gp.feasible b := by
  simp [b, gp, feasible]; norm_num
  rw [sqrt_30_eq_mul, ← le_sub_iff_add_le, ← sub_mul]
  have h₁ : 3 ≤ 5 - sqrt (3 : ℝ) := by
    rw [le_sub_iff_add_le, add_comm, ← le_sub_iff_add_le]
    rw [sqrt_le_iff]; norm_num
  have h₂ : 3 * 3 ≤ (5 - sqrt 3) * sqrt 10 := by
    apply mul_le_mul h₁ (le_sqrt_10) <;> norm_num
    rw [sqrt_le_iff]; norm_num
  refine le_trans ?_ h₂
  norm_num

-- We show that the point in the middle, `c`, does not satisfy `x * y = z ^ 2`. This means that the
-- constraint does not represent a convex set. Also, it implies that the feasible set is not convex.

def c : ℝ × ℝ × ℝ := (a + b) / 2

lemma c_def : c = ⟨2.5, 7, (sqrt 8 + sqrt 30) / 2⟩ := by
  show (a + b) / ⟨(2 : ℝ), (2 : ℝ), (2 : ℝ)⟩ = _
  simp [a, b]; norm_num

lemma not_h₇_c : ¬ (c.1 * c.2.1 = c.2.2 ^ 2) := by
  rw [c_def]; dsimp; norm_num
  rw [eq_div_iff (by norm_num)]; norm_num
  apply ne_of_gt; rw [sq_lt]; split_ands
  . have h₁ : 0 < sqrt 70 := by norm_num
    have h₂ : 0 < sqrt 8 := by norm_num
    have h₃ : 0 < sqrt 30 := by norm_num
    linarith
  . have h₁ : 8.35 < sqrt 70 := by rw [lt_sqrt] <;> norm_num
    have h₂ : sqrt 8 < 2.83 := by rw [sqrt_lt] <;> norm_num
    have h₃ : sqrt 30 < 5.48 := by rw [sqrt_lt] <;> norm_num
    have h₅ : (2.83 : ℝ) + 5.48 < 8.35 := by norm_num
    linarith

lemma not_feasible_c : ¬ gp.feasible c := by
  simp [gp, feasible, -rpow_two]
  intros; exact not_h₇_c

end DGP

end

end Chapter2
