/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Growth/NormalizedProfile.lean`,
by Jeroen Zuiddam, 2026: `ℂ` replaced by a field `K`; no declaration here needs `K`
algebraically closed.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.SixfoldProductBounds
public import Mathlib.Tactic.FieldSimp
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Positivity and rank bounds for the normalized profile

The normalization exponent is positive when the mean singleton-leg exponent
is positive. Under this hypothesis, passing to the profile preserves order,
and a rank bound `r` becomes the bound `r ^ (1 / t)`.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



namespace MatrixMultiplication.AuxiliarySeparation
namespace Character

open MatrixMultiplication.Foundation

variable (χ : Character K)
variable {X Y Z U V W : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype U] [Fintype V] [Fintype W]

theorem symmetrizedProfile_nonneg (t : ℝ) (T : Tensor K X Y Z) :
    0 ≤ χ.symmetrizedProfile t T :=
  Real.rpow_nonneg (χ.sixfoldProduct_nonneg T) _

theorem symmetrizedProfile_pos (t : ℝ) {T : Tensor K X Y Z} (hT : T ≠ 0) :
    0 < χ.symmetrizedProfile t T :=
  Real.rpow_pos_of_pos (χ.sixfoldProduct_pos hT) _

theorem one_le_symmetrizedProfile {t : ℝ} (ht : 0 < t)
    {T : Tensor K X Y Z} (hT : T ≠ 0) : 1 ≤ χ.symmetrizedProfile t T := by
  exact Real.one_le_rpow (χ.one_le_sixfoldProduct hT) (by positivity)

/-- Tensor products become products of normalized profile values. -/
theorem symmetrizedProfile_product (t : ℝ) (T : Tensor K X Y Z)
    (S : Tensor K U V W) :
    χ.symmetrizedProfile t (Tensor.product T S) =
      χ.symmetrizedProfile t T * χ.symmetrizedProfile t S := by
  simp only [symmetrizedProfile, χ.sixfoldProduct_product]
  exact Real.mul_rpow (χ.sixfoldProduct_nonneg T) (χ.sixfoldProduct_nonneg S)

/-- Positive normalization preserves the order of the underlying sixfold products. -/
theorem symmetrizedProfile_le_iff {t : ℝ} (ht : 0 < t)
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    χ.symmetrizedProfile t T ≤ χ.symmetrizedProfile t S ↔
      χ.sixfoldProduct T ≤ χ.sixfoldProduct S := by
  exact Real.rpow_le_rpow_iff (χ.sixfoldProduct_nonneg T)
    (χ.sixfoldProduct_nonneg S) (by positivity)

/-- The symmetrized profile has the rank bound used in Section 5. -/
theorem symmetrizedProfile_le_rank {t : ℝ} (ht : 0 < t)
    {T : Tensor K X Y Z} {r : ℕ} (h : Tensor.RankAtMost T r) :
    χ.symmetrizedProfile t T ≤ (r : ℝ) ^ (1 / t) := by
  calc
    χ.symmetrizedProfile t T ≤ ((r : ℝ) ^ 6) ^ (1 / (6 * t)) :=
      Real.rpow_le_rpow (χ.sixfoldProduct_nonneg T) (χ.sixfoldProduct_le_rank h)
        (by positivity)
    _ = (r : ℝ) ^ (1 / t) := by
      rw [← Real.rpow_natCast (r : ℝ) 6, ← Real.rpow_mul (by positivity)]
      congr 1
      field_simp
      norm_num

/-- A factor `c ^ (6*t)` in the sixfold product becomes `c` in the profile. -/
theorem mul_symmetrizedProfile_le_of_le {t c : ℝ} (ht : 0 < t) (hc : 0 ≤ c)
    (T : Tensor K X Y Z) (S : Tensor K U V W)
    (h : c ^ (6 * t) * χ.sixfoldProduct T ≤ χ.sixfoldProduct S) :
    c * χ.symmetrizedProfile t T ≤ χ.symmetrizedProfile t S := by
  have hp := Real.rpow_le_rpow
    (mul_nonneg (Real.rpow_nonneg hc _) (χ.sixfoldProduct_nonneg T)) h
    (show 0 ≤ 1 / (6 * t) by positivity)
  rw [Real.mul_rpow (Real.rpow_nonneg hc _) (χ.sixfoldProduct_nonneg T),
    one_div, Real.rpow_rpow_inv hc (ne_of_gt (mul_pos (by norm_num) ht))] at hp
  simpa only [symmetrizedProfile, one_div] using hp

end Character
end MatrixMultiplication.AuxiliarySeparation

end MatrixMultiplicationAllFields
