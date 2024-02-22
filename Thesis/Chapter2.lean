import CvxLean

namespace Chapter2

namespace LeansTypeTheory

/-! Section 2.1 -/

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

end LeansTypeTheory

end Chapter2
