/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Tactic.NormNum
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import LeanPool.AaronsonAmbainis.RowDefs

/-!
# Linear functionals on `β → ℝ` for a finite index type `β`

* `functional_eq_sum` — `φ v = ∑ b, φ (e_b) * v b`;
* `coeff_nonneg`      — if `φ` is bounded below on the nonnegative orthant, its coefficients
                        `φ (e_b)` are nonnegative.

Both are used in `Dual/Cover.lean`, where they turn the separating functional given by the
Hahn–Banach theorem into a vector `κ ≥ 0` with `φ v = ∑_S κ_S v_S`.
-/

@[expose] public section

namespace AaronsonAmbainis
namespace Dual

open Finset

variable {β : Type*} [Fintype β] [DecidableEq β]

/-- Every vector is the sum of its coordinates times the unit vectors. -/
theorem eq_sum_single (v : β → ℝ) : v = ∑ b, v b • (Pi.single b (1 : ℝ) : β → ℝ) := by
  funext c
  rw [Finset.sum_apply, Finset.sum_eq_single c]
  · simp
  · intro b _ hb
    simp [hb.symm]
  · intro h
    exact absurd (Finset.mem_univ c) h

theorem functional_eq_sum (φ : (β → ℝ) →L[ℝ] ℝ) (v : β → ℝ) :
    φ v = ∑ b, φ (Pi.single b 1) * v b := by
  conv_lhs => rw [eq_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm]

omit [Fintype β] in
theorem coeff_nonneg (φ : (β → ℝ) →L[ℝ] ℝ) (r : ℝ)
    (h : ∀ v : β → ℝ, (∀ b, 0 ≤ v b) → r < φ v) (b : β) :
    0 ≤ φ (Pi.single b 1) := by
  by_contra hneg
  rw [not_le] at hneg
  -- `v = 0` gives `r < 0`
  have hr : r < 0 := by
    have h0 := h 0 (fun _ => le_rfl)
    rwa [map_zero] at h0
  -- `v = (r / φ e_b) • e_b` lies in the orthant and has `φ v = r`
  have hx := h ((r / φ (Pi.single b 1)) • (Pi.single b (1 : ℝ) : β → ℝ)) (fun c => by
    simp only [Pi.smul_apply, smul_eq_mul]
    refine mul_nonneg (div_nonneg_of_nonpos hr.le hneg.le) ?_
    rw [Pi.single_apply]
    split_ifs <;> norm_num)
  rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hneg.ne] at hx
  exact lt_irrefl _ hx

end Dual
end AaronsonAmbainis
