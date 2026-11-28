/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

-- Modified for Lean Pool.

module

public import LeanPool.ReadL1.Defs
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.NormNum

/-!
# Bounded operators on ℓ¹ from the images of the basis vectors

On ℓ¹ an operator is determined by where it sends the standard basis vectors `δᵢ`, and any
bounded family of images gives an operator: send `x = ∑ xᵢ δᵢ` to `∑ xᵢ uᵢ`. The series converges
because `‖xᵢ uᵢ‖ ≤ C ‖xᵢ‖` and `∑ ‖xᵢ‖ = ‖x‖`, which also gives the norm bound `C`.

Two consequences are used throughout the construction of Read's operator:

* `ReadL1.l1Lift`: an operator from bounded images of the basis vectors, with norm at most the
  bound (`ReadL1.norm_l1Lift_le`);
* `ReadL1.opNorm_le_of_forall_single`: the norm of an operator on ℓ¹ is at most any bound on the
  norms of the images of the basis vectors. (It is in fact equal to their supremum.)

We did not find either in Mathlib at the pinned version (searched `Mathlib/Analysis/Normed/Lp`
and `Mathlib/Analysis/InnerProductSpace/l2Space.lean`, which have `lp.evalCLM` and
`lp.singleContinuousLinearMap` but no operator built from images of the basis vectors).
-/

@[expose] public section

namespace ReadL1

open scoped ENNReal

/-- The space ℓ¹(ℕ, ℂ) of absolutely summable complex sequences, written as in Formal
Conjectures. -/
abbrev L1 : Type := lp (fun _ : ℕ => ℂ) 1

/-- The standard basis vector `δᵢ` of ℓ¹. -/
noncomputable abbrev δ (i : ℕ) : L1 := lp.single 1 i (1 : ℂ)

/-- The coordinates of an element of ℓ¹ are absolutely summable. -/
lemma summable_norm (x : L1) : Summable fun i => ‖x i‖ := by
  simpa using (memℓp_gen_iff (p := 1) (by norm_num)).1 (lp.memℓp x)

/-- The ℓ¹ norm is the sum of the absolute values of the coordinates. -/
lemma norm_eq_tsum (x : L1) : ‖x‖ = ∑' i, ‖x i‖ := by
  simpa using lp.norm_eq_tsum_rpow (p := 1) (by norm_num) x

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

omit [CompleteSpace X] in
/-- The series `∑ xᵢ uᵢ` converges absolutely when the `uᵢ` are bounded. -/
lemma summable_norm_smul {u : ℕ → X} {C : ℝ} (hu : ∀ i, ‖u i‖ ≤ C) (x : L1) :
    Summable fun i => ‖x i • u i‖ :=
  ((summable_norm x).mul_right C).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    fun i ↦ by rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hu i) (norm_nonneg _)

lemma summable_smul {u : ℕ → X} {C : ℝ} (hu : ∀ i, ‖u i‖ ≤ C) (x : L1) :
    Summable fun i => x i • u i :=
  (summable_norm_smul hu x).of_norm

/-- The linear map `x ↦ ∑ xᵢ uᵢ`. -/
noncomputable def l1LiftLinear (u : ℕ → X) (C : ℝ) (hu : ∀ i, ‖u i‖ ≤ C) : L1 →ₗ[ℂ] X where
  toFun x := ∑' i, x i • u i
  map_add' x y := by
    simp only [lp.coeFn_add, Pi.add_apply, add_smul]
    exact (summable_smul hu x).tsum_add (summable_smul hu y)
  map_smul' c x := by
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
    exact (summable_smul hu x).tsum_const_smul c

/-- The bound: `‖∑ xᵢ uᵢ‖ ≤ ∑ ‖xᵢ‖ C = C ‖x‖`. -/
lemma norm_l1LiftLinear_le (u : ℕ → X) (C : ℝ) (hu : ∀ i, ‖u i‖ ≤ C) (x : L1) :
    ‖l1LiftLinear u C hu x‖ ≤ C * ‖x‖ := by
  have hterm : ∀ i, ‖x i • u i‖ ≤ C * ‖x i‖ := fun i ↦ by
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hu i) (norm_nonneg _)
  change ‖∑' i, x i • u i‖ ≤ C * ‖x‖
  calc ‖∑' i, x i • u i‖ ≤ ∑' i, ‖x i • u i‖ := norm_tsum_le_tsum_norm (summable_norm_smul hu x)
    _ ≤ ∑' i, C * ‖x i‖ :=
        Summable.tsum_le_tsum hterm (summable_norm_smul hu x) ((summable_norm x).mul_left C)
    _ = C * ‖x‖ := by rw [tsum_mul_left, norm_eq_tsum]

/-- **The operator on ℓ¹ with prescribed bounded images `uᵢ` of the basis vectors.** -/
noncomputable def l1Lift (u : ℕ → X) (C : ℝ) (hu : ∀ i, ‖u i‖ ≤ C) : L1 →L[ℂ] X :=
  (l1LiftLinear u C hu).mkContinuous C (norm_l1LiftLinear_le u C hu)

lemma l1Lift_apply (u : ℕ → X) (C : ℝ) (hu : ∀ i, ‖u i‖ ≤ C) (x : L1) :
    l1Lift u C hu x = ∑' i, x i • u i := rfl

/-- `l1Lift` sends `δᵢ` to `uᵢ`. -/
@[simp]
lemma l1Lift_single (u : ℕ → X) (C : ℝ) (hu : ∀ i, ‖u i‖ ≤ C) (i : ℕ) :
    l1Lift u C hu (δ i) = u i := by
  rw [l1Lift_apply, tsum_eq_single i]
  · simp
  · intro j hj
    simp [lp.single_apply, hj]

/-- `l1Lift` has norm at most the bound on the images. -/
lemma norm_l1Lift_le (u : ℕ → X) (C : ℝ) (hu : ∀ i, ‖u i‖ ≤ C) : ‖l1Lift u C hu‖ ≤ C :=
  (l1LiftLinear u C hu).mkContinuous_norm_le ((norm_nonneg _).trans (hu 0))
    (norm_l1LiftLinear_le u C hu)

/-- Every operator on ℓ¹ is the lift of its images of the basis vectors. -/
lemma eq_l1Lift (A : L1 →L[ℂ] X) (C : ℝ) (hA : ∀ i, ‖A (δ i)‖ ≤ C) :
    A = l1Lift (fun i ↦ A (δ i)) C hA := by
  refine lp.ext_continuousLinearMap ENNReal.one_ne_top fun i ↦ ?_
  -- Maps out of `ℂ` agree once they agree at `1`, and `1` goes to `δ i`.
  ext
  exact (l1Lift_single _ C hA i).symm

/-- **The norm of an operator on ℓ¹ is at most any bound on the images of the basis vectors.** -/
lemma opNorm_le_of_forall_single (A : L1 →L[ℂ] X) (C : ℝ) (hA : ∀ i, ‖A (δ i)‖ ≤ C) :
    ‖A‖ ≤ C := by
  rw [eq_l1Lift A C hA]
  exact norm_l1Lift_le _ C hA

end ReadL1
