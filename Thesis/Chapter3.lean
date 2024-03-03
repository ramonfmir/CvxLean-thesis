import CvxLean

noncomputable section

open CvxLean Minimization Real

namespace Chapter3

namespace CvxLeanOverview

/-! Section 3.2 -/

#check Minimization

#check feasible
#check optimal

#check Solution

def p :=
  optimization (x y : ℝ)
    minimize 40 * x + 30 * y
    subject to
      c₁ : 12 ≤ x + y
      c₂ : 16 ≤ 2 * x + y

example : p =
    Minimization.mk
      (fun p => 40 * p.1 + 30 * p.2)
      (fun p => 12 ≤ p.1 + p.2 ∧ 16 ≤ 2 * p.1 + p.2) :=
  rfl

def pSolution : Solution p :=
  { point := ⟨4, 8⟩,
    isOptimal := by
      split_ands <;> try norm_num
      intros x' y' h_feas; simp [feasible, p] at h_feas ⊢; linarith }

end CvxLeanOverview

namespace Equivalences

/-! Section 3.3 -/

#check Equivalence

#check Equivalence.refl
#check Equivalence.symm
#check Equivalence.trans

#check StrongEquivalence

#check StrongEquivalence.refl
#check StrongEquivalence.symm
#check StrongEquivalence.trans

#check Equivalence.ofStrongEquivalence

open Equivalence

-- These are the proofs of equivalences and strong equivalnces between the three examples involving
-- `x`, `log(x)` and `log(x)^2` in their objective functions.

def pex₁ :=
  optimization (x : ℝ)
    minimize x
    subject to
      h₁ : 1 ≤ x
      h₂ : x ≤ exp 1

def pex₂ :=
  optimization (x : ℝ)
    minimize log x
    subject to
      h₁ : 1 ≤ x
      h₂ : x ≤ exp 1

def pex₃ :=
  optimization (x : ℝ)
    minimize ((log x) ^ 2 : ℝ)
    subject to
      h₁ : 1 ≤ x
      h₂ : x ≤ exp 1

def E₁₂ : pex₁ ≡ pex₂ := Equivalence.map_objFun_log (fun x h => by positivity!)

def E₂₃ : pex₂ ≡ pex₃ := Equivalence.map_objFun_sq (fun x h => by positivity!)

def nS₁₂ : (pex₁ ≡' pex₂) → False :=
  fun ⟨_, psi, _, psi_feasibility, _, psi_optimality⟩ => by
    simp only [pex₁, pex₂, feasible, constraints, objFun] at *
    let y : ℝ := 1
    have h_feas_y : 1 ≤ y ∧ y ≤ exp 1 := by norm_num
    have h_one_le_phiy := (psi_feasibility y h_feas_y).1
    have h_psiy_le_logy := psi_optimality y h_feas_y
    have h_one_le_logy := le_trans h_one_le_phiy h_psiy_le_logy
    simp at h_one_le_logy
    have hc := lt_of_le_of_lt h_one_le_logy (zero_lt_one (α:= ℝ))
    exact lt_irrefl _ hc

def S₂₃ : pex₂ ≡' pex₃ :=
  { phi := fun x => (exp (sqrt (log x)))
    psi := fun x => (exp ((log x) ^ 2))
    phi_feasibility := fun x ⟨h1x, hx2⟩ => by
      simp [pex₂, pex₃, feasible, constraints, objFun] at *
      split_ands
      . exact sqrt_nonneg _
      . rw [sqrt_le_iff]
        split_ands
        . positivity
        . rw [← log_le_log_iff (by linarith) (by positivity)] at hx2
          apply le_trans hx2; field_simp,
    psi_feasibility := fun x ⟨h1x, hxe⟩ => by
      simp [pex₂, pex₃, feasible, constraints, objFun] at *
      split_ands
      . exact sq_nonneg _
      . rw [abs_le]
        have hx : 0 < x := by linarith
        rw [← log_le_log_iff (by norm_num) hx, log_one] at h1x
        rw [← log_le_log_iff hx (exp_pos _), log_exp] at hxe
        split_ands <;> linarith,
    phi_optimality := fun x ⟨h1x, _⟩ => by
      simp [pex₂, pex₃, feasible, constraints, objFun] at *
      have h_logx_nonneg : 0 ≤ log x := log_nonneg h1x
      rw [sq_sqrt h_logx_nonneg],
    psi_optimality := fun x _ => by
      simp [pex₂, pex₃, feasible, constraints, objFun] at * }

def pex₄ := Minimization.mk (fun (x : ℝ) => x) (fun x => 0 ≤ x ∧ x ≤ 1)

def S₄₂ : pex₄ ≡' pex₂ :=
  { phi := fun x => exp x
    psi := fun x => log x
    phi_feasibility := fun x _ => by
      simp [pex₄, pex₂, feasible, constraints, objFun] at *
      split_ands <;> linarith,
    psi_feasibility := fun x h_feas_x => by
      simp [pex₄, pex₂, feasible, constraints, objFun] at *
      have hx : 0 < x := by linarith
      have h_0_eq_log1 : 0 = log 1 := by simp
      have h_1_eq_loge : 1 = log (exp 1) := by simp
      rw [h_1_eq_loge, h_0_eq_log1]
      rwa [log_le_log_iff hx (exp_pos _), log_le_log_iff (by norm_num) hx],
    phi_optimality := fun x _ => by
      simp [pex₄, pex₂, feasible, constraints, objFun] at *,
    psi_optimality := fun x _ => by
      simp [pex₄, pex₂, feasible, constraints, objFun] at *, }

def nS₄₁ : (pex₄ ≡' pex₁) → False := fun h => nS₁₂ <| h.symm.trans S₄₂

-- We introduce the `equivalence` command here.

equivalence eqvₚ/r : CvxLeanOverview.p := by
  -- Direct application of transitivity (users will rarely apply this).
  equivalence_trans
  -- Check goals here.
  -- Close all goals by reflexivity on the first goal.
  equivalence_rfl
  -- Check new goal here.

equivalence eqvₚ'/p' : CvxLeanOverview.p := by
  -- Check initial goal here
  equivalence_step =>
    -- Any tactic, for example, we swap all multiplications.
    simp only [mul_comm]
  -- Check new goal here

#print p'

#check eqvₚ'

equivalence* eqvComp/conicForm :
  optimization (x : ℝ)
    minimize (exp x)
    subject to
      c₁ : 0 ≤ x := by
  -- We have not introduced this yet (see `Chapter4`).
  dcp

#print conicForm

#check eqvComp.psi
#check eqvComp.backward_map

#eval eqvComp.backward_map ⟨1, 0⟩

-- The rest are examples of tactics.

#check instChangeOfVariablesRealExp

equivalence* eqv₁/p₂ :
    optimization (x y : ℝ)
      minimize (x * y)
      subject to
        c₁ : 0 < x
        c₂ : 1 ≤ y := by
  change_of_variables! (u) (x ↦ exp u)
  change_of_variables! (v) (y ↦ exp v)

#print p₂
#check eqv₁

-- Note that the backward map here is non-trivial, due to the change of variables.
#eval eqv₁.backward_map ⟨1, 1⟩

equivalence eqv₂/p₃ : p₂ := by
  conv_obj =>
    rw [← exp_add]
  conv_constr c₂ =>
    simp

#print p₃
#check eqv₂

equivalence eqv₃/p₄ :
    optimization (x : ℝ)
      minimize sqrt (x ^ 2)
      subject to
        c₁ : 0 ≤ x := by
  rw_obj =>
    -- Check goal here.
    rewrite [rpow_two, sqrt_sq c₁]
    -- Check goal here.
    rfl
  rw_constr c₁ =>
    -- Check goal right before `rfl`, which does not change anything.
    rfl
  rw_constr c₁ into (0 ≤ x) =>
    -- This illustrates the usage of `into`.
    -- Check goal right before `rfl`, which does not change anything.
    rfl

#print p₄
#check eqv₃

equivalence eqv₃'/p₄' :
    optimization (x y : ℝ)
      minimize -log (x + y)
      subject to
        c₁ : 2 ≤ x
        c₂ : 3 ≤ y
        c₃ : log (y / x) ≤ 0 := by
  rw_constr c₃ into (log (y / x) ≤ log 1) =>
    simp
  rw_constr c₃ into (y / x ≤ 1) =>
    rw [log_le_log_iff] <;> positivity
  rw_constr c₃ into (y ≤ 1 * x) =>
    rw [div_le_iff] <;> positivity
  rw_constr c₃ into (y ≤ x) =>
    simp

#print p₄'
#check eqv₃'

variable {f : ℝ → ℝ} {cs : ℝ → Prop}

#check map_objFun_log (D := {** ℝ ** x **}) (f := fun x => f x) (cs := fun x => cs x)

#check map_le_constraint_standard_form

#check map_eq_constraint_standard_form

equivalence eqv₄/p₅ :
  optimization (x y z : ℝ)
    minimize (x + y + z)
    subject to
      c₁ : 0 ≤ x
      c₂ : 0 ≤ y
      c₃ : 0 ≤ z := by
  rename_vars [a, b, c]

#print p₅
#check eqv₄

equivalence eqv₅/p₆ : p₅ := by
  rename_constrs [c₁', c₂']

#print p₆
#check eqv₅

equivalence eqv₆/p₇ : p₆ := by
  reorder_constrs [c₃, c₂', c₁']

#print p₇
#check eqv₆

equivalence eqv₇/p₈ :
  optimization (x : ℝ)
    minimize x
    subject to
      c₁ : 1 ≤ x
      c₂ : 0 < exp x := by
  remove_constr c₂ =>
    positivity

#print p₈
#check eqv₇

#check eliminate_eq_constraint_standard_form

#check decompose_constraint

#check add_slack_variable_standard_form

#check epigraph_form

end Equivalences

namespace Reductions

/-! Section 3.4 -/

#check Reduction

#check Reduction.refl
#check Reduction.trans

#check Reduction.ofEquivalence
#check Equivalence.ofReductions

def p :=
  optimization (x y : ℝ)
    minimize (x + y)
    subject to
      c₁ : 1 ≤ x
      c₂ : 1 ≤ y

reduction red/q : p := by
  change_of_variables (u) (x ↦ exp u)
  change_of_variables (v) (y ↦ exp v)

#print q
#check red

reduction* redComp/q' : p := by
  change_of_variables (u) (x ↦ exp u)
  change_of_variables (v) (y ↦ exp v)

#eval redComp.backward_map ⟨1, 1⟩

end Reductions

namespace Relaxations

/-! Section 3.5 -/

#check Relaxation

#check Relaxation.refl
#check Relaxation.trans

#check Relaxation.ofStrongEquivalence
#check StrongEquivalence.ofRelaxations

open Relaxation

def p :=
  optimization (x : ℝ)
    minimize x
    subject to
      c₁ : log x + exp x + sqrt x + x ^ x ≤ 7
      c₂ : 0 ≤ x

relaxation rel/q : p := by
  relaxation_step =>
    exact remove_constraint (cs' := fun x => 0 ≤ x) (hcs := fun x => by rfl)

#print q
#check rel

def p₁ :=
  optimization (x y : ℝ)
    minimize x + y
    subject to
      c₁ : 0 ≤ x
      c₂ : 0 ≤ y

def p₂ :=
  optimization (x : ℝ)
    minimize x
    subject to
      c₁ : 0 ≤ x

def Rx₁₂ : p₁ ≽' p₂ :=
  { phi := fun (x, _) => x,
    phi_feasibility := fun _ ⟨hx, _⟩ => hx,
    phi_optimality := fun _ ⟨_, hy⟩ => by simpa [objFun, p₁, p₂] }

open Real Matrix

lemma trace_mul_transpose_self_eq_quad_of_symm {n} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ)
    (hA : IsSymm A) :
    trace (A * (Vec.toMatrix x * (Vec.toMatrix x)ᵀ)) = vecMul x A ⬝ᵥ x := by
  simp [trace, dotProduct]
  congr; funext i; simp [Matrix.mul_apply, vecMul, dotProduct, Finset.sum_mul]
  congr; funext j; simp [Vec.toMatrix]; rw [hA.apply i j]; ring

def sdr {n} {A C : Matrix (Fin n) (Fin n) ℝ} (hA : IsSymm A) (hC : IsSymm C) (b : ℝ) :
  (optimization (x : Fin n → ℝ)
    minimize (vecMul x C) ⬝ᵥ x
    subject to
      c₁ : (vecMul x A) ⬝ᵥ x ≥ b) ≽'
  (optimization (X : Matrix (Fin n) (Fin n) ℝ)
    minimize trace (C * X)
    subject to
      c₁ : trace (A * X) ≥ b
      c₂ : PosSemidef X) :=
  { phi := fun x => (Vec.toMatrix x) * (Vec.toMatrix x)ᵀ,
    phi_feasibility := fun x h_feas_x => by
      simp [objFun, feasible, constraints, p₁, p₂, Vec.toMatrix] at *
      rw [trace_mul_transpose_self_eq_quad_of_symm A x hA]
      refine ⟨h_feas_x, ?_⟩
      rw [← conjTranspose_eq_transpose]
      exact posSemidef_conjTranspose_mul_self _,
    phi_optimality := fun x h_feas_x => by
      simp [objFun, feasible, constraints, p₁, p₂] at *
      rw [trace_mul_transpose_self_eq_quad_of_symm C x hC] }

end Relaxations

end Chapter3

end
