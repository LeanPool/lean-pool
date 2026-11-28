/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

-- Modified for Lean Pool.

module

public import LeanPool.ReadL1.L1Lift
public import LeanPool.ReadL1.Lemma2

/-!
# Read's operator on ℓ¹

Finitely supported sequences sit inside ℓ¹ (`ReadL1.toL1`), with Śliwa's coordinate norm becoming
the ℓ¹ norm (`ReadL1.norm_toL1`). By Lemma 2 the images `T fᵢ` are bounded by `α`, so `l1Lift`
gives an operator on all of ℓ¹ with those images (`ReadL1.readOp`), of norm at most `α`
(`ReadL1.norm_readOp_le`). On finite sequences it agrees with `T₀` (`ReadL1.readOp_toL1`), so it
is still multiplication by `x`.
-/

@[expose] public section

namespace ReadL1

open Finsupp

variable {d : ℕ → ℕ}

/-- A finitely supported sequence, as an element of ℓ¹: `g ↦ ∑ⱼ gⱼ δⱼ`. -/
noncomputable def toL1 : (ℕ →₀ ℂ) →ₗ[ℂ] L1 := linearCombination ℂ δ

lemma toL1_single (j : ℕ) (c : ℂ) : toL1 (single j c) = c • δ j := by
  simp [toL1]

/-- The coordinates of `toL1 g` are those of `g`. -/
lemma toL1_apply (g : ℕ →₀ ℂ) (k : ℕ) : toL1 g k = g k := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g h hg hh => simp [hg, hh]
  | single j c =>
    rw [toL1_single, lp.coeFn_smul, Pi.smul_apply, lp.single_apply, Finsupp.single_apply]
    by_cases hjk : j = k
    · subst hjk; simp
    · simp [hjk, Ne.symm hjk]

/-- **Śliwa's coordinate norm is the ℓ¹ norm.** -/
lemma norm_toL1 (g : ℕ →₀ ℂ) : ‖toL1 g‖ = nrm g := by
  rw [norm_eq_tsum, nrm]
  simp only [toL1_apply]
  exact tsum_eq_sum fun k hk ↦ by simp [Finsupp.notMem_support_iff.1 hk]

/-- The images of the basis vectors are bounded by `α` (Lemma 2). -/
lemma norm_toL1_shiftImage_le (h : GrowthHyp d) (i : ℕ) : ‖toL1 (shiftImage d i)‖ ≤ alpha := by
  rw [norm_toL1]; exact nrm_shiftImage_le h i

/-- **Read's operator on ℓ¹** (Śliwa's variant): `δᵢ ↦ T fᵢ`. -/
noncomputable def readOp (h : GrowthHyp d) : L1 →L[ℂ] L1 :=
  l1Lift (fun i ↦ toL1 (shiftImage d i)) alpha (norm_toL1_shiftImage_le h)

/-- **`‖T‖ ≤ α`** (Śliwa, Lemma 2). -/
theorem norm_readOp_le (h : GrowthHyp d) : ‖readOp h‖ ≤ alpha :=
  norm_l1Lift_le _ _ _

lemma readOp_single (h : GrowthHyp d) (i : ℕ) : readOp h (δ i) = toL1 (shiftImage d i) :=
  l1Lift_single _ _ _ i

/-- On finite sequences, the operator is `T₀`. -/
theorem readOp_toL1 (h : GrowthHyp d) (g : ℕ →₀ ℂ) : readOp h (toL1 g) = toL1 (T₀ d g) := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add g k hg hk => simp only [map_add, hg, hk]
  | single j c =>
    rw [toL1_single, map_smul, readOp_single, T₀_single, map_smul]

end ReadL1
