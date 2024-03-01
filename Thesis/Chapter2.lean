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

end Chapter2
