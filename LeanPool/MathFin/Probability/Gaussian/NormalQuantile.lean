/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho, Yang Ye
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Laws.Quantile
public import LeanPool.MathFin.Probability.Gaussian.GaussianCDFDeriv

/-!
# The standard normal quantile function `Φ⁻¹`

`Φ⁻¹` is the quantile function of the standard normal law (`PhiInv`). Mathlib has no inverse of
the normal CDF, so the library's Gaussian risk closed forms (`Risk/Gaussian.lean`) were
written in a quantile parameter `z` with `Φ(z) = α`. Here the parameter becomes a function of the
level.

Because `Φ` is continuous and strictly increasing, the generalized inverse of
`Probability/Laws/Quantile.lean` is a two-sided inverse: `Φ (Φ⁻¹ p) = p` on `(0, 1)` and
`Φ⁻¹ (Φ x) = x` for every `x`. The quantile of a general Gaussian law then follows from
equivariance under the affine map `z ↦ m + σ z` (`quantile_gaussianReal`).

## Main definitions

* `PhiInv`: the standard normal quantile function `Φ⁻¹`, the generalized inverse of `Φ`.

## Main results

* `continuous_Phi`, `strictMono_Phi`, `Phi_mem_Ioo`: `Φ` is continuous, strictly increasing
  and takes values in `(0, 1)`. Its automation: `continuous_Phi` and `measurable_Phi` are
  `fun_prop` lemmas, `Phi_lt_Phi` / `Phi_le_Phi` are `gcongr` lemmas, and `positivity` proves
  `0 < Φ x` (`Phi_pos`, `evalPhi`).
* `Phi_PhiInv`, `PhiInv_Phi`: the two inverse identities.
* `PhiInv_one_sub`: symmetry, `Φ⁻¹(1 − p) = −Φ⁻¹(p)`.
* `PhiInv_nonneg_iff`, `PhiInv_pos_iff`: `Φ⁻¹(p)` has the sign of `p − 1/2`.
* `quantile_gaussianReal`: the `p`-quantile of `N(m, σ²)` is `m + σ Φ⁻¹(p)`.

## References

* [A. J. McNeil, R. Frey and P. Embrechts, *Quantitative Risk Management: Concepts, Techniques and
  Tools*][McNeilFreyEmbrechts], Example 2.11

## Tags

inverse normal CDF, probit function, Gaussian quantile, normal percentile, value-at-risk quantile,
MSC 60E05, MSC 62G30
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

variable {p x : ℝ}

/-- The CDF of the standard normal law is `Φ`. -/
lemma cdf_gaussianReal_zero_one : ⇑(cdf (gaussianReal 0 1)) = Phi := by
  ext x
  rw [cdf_eq_real, Phi_def, measureReal_def]

/-- `Φ` is continuous. -/
@[fun_prop] lemma continuous_Phi : Continuous Phi :=
  continuous_iff_continuousAt.2 fun x ↦ (hasDerivAt_Phi x).continuousAt

/-- `Φ` is measurable. -/
@[fun_prop] lemma measurable_Phi : Measurable Phi := continuous_Phi.measurable

/-- `Φ` is strictly increasing: its derivative, the normal density, is positive. -/
lemma strictMono_Phi : StrictMono Phi :=
  strictMono_of_hasDerivAt_pos hasDerivAt_Phi fun x ↦ gaussianPDFReal_pos 0 1 x one_ne_zero

/-- `Φ` takes values in the open unit interval. -/
lemma Phi_mem_Ioo (x : ℝ) : Phi x ∈ Ioo 0 1 :=
  ⟨(Phi_nonneg (x - 1)).trans_lt (strictMono_Phi (sub_one_lt x)),
    (strictMono_Phi (lt_add_one x)).trans_le (Phi_le_one _)⟩

/-- `Φ` is positive. `positivity` proves it (`evalPhi`). -/
lemma Phi_pos (x : ℝ) : 0 < Phi x := (Phi_mem_Ioo x).1

/-- `Φ` is strictly increasing, in the form `gcongr` uses. -/
@[gcongr] lemma Phi_lt_Phi {x y : ℝ} (h : x < y) : Phi x < Phi y := strictMono_Phi h

/-- `Φ` is increasing, in the form `gcongr` uses. -/
@[gcongr] lemma Phi_le_Phi {x y : ℝ} (h : x ≤ y) : Phi x ≤ Phi y := strictMono_Phi.monotone h

/-- `Φ(0) = 1/2`, by symmetry. -/
lemma Phi_zero : Phi 0 = 1 / 2 := by
  linarith [Phi_add_Phi_neg 0, show Phi (-0) = Phi 0 by rw [neg_zero]]

/-- The **standard normal quantile function** `Φ⁻¹`. -/
noncomputable def PhiInv (p : ℝ) : ℝ :=
  quantile (gaussianReal 0 1) p

/-- The Galois connection for `Φ⁻¹`: `Φ⁻¹(p) ≤ x ↔ p ≤ Φ(x)`. -/
theorem PhiInv_le_iff (hp : p ∈ Ioo 0 1) : PhiInv p ≤ x ↔ p ≤ Phi x := by
  rw [PhiInv, quantile_le_iff hp, cdf_gaussianReal_zero_one]

/-- `x < Φ⁻¹(p) ↔ Φ(x) < p`. -/
theorem lt_PhiInv_iff (hp : p ∈ Ioo 0 1) : x < PhiInv p ↔ Phi x < p := by
  rw [PhiInv, lt_quantile_iff hp, cdf_gaussianReal_zero_one]

/-- `Φ ∘ Φ⁻¹` is the identity on `(0, 1)`. -/
theorem Phi_PhiInv (hp : p ∈ Ioo 0 1) : Phi (PhiInv p) = p := by
  rw [← cdf_gaussianReal_zero_one]
  exact cdf_quantile (by rw [cdf_gaussianReal_zero_one]; exact continuous_Phi) hp

/-- `Φ⁻¹ ∘ Φ` is the identity. -/
theorem PhiInv_Phi (x : ℝ) : PhiInv (Phi x) = x := by
  have h := quantile_cdf (μ := gaussianReal 0 1) (x := x)
    (by rw [cdf_gaussianReal_zero_one]; exact strictMono_Phi)
    (by rw [cdf_gaussianReal_zero_one]; exact Phi_mem_Ioo x)
  rwa [cdf_gaussianReal_zero_one] at h

/-- `Φ⁻¹` is strictly increasing on `(0, 1)`. -/
theorem strictMonoOn_PhiInv : StrictMonoOn PhiInv (Ioo 0 1) := fun _ hp _ hq hpq ↦ by
  rwa [lt_PhiInv_iff hq, Phi_PhiInv hp]

/-- **Symmetry of the normal quantile**: `Φ⁻¹(1 − p) = −Φ⁻¹(p)`. -/
theorem PhiInv_one_sub (hp : p ∈ Ioo 0 1) : PhiInv (1 - p) = -PhiInv p := by
  conv_lhs => rw [← Phi_PhiInv hp, ← Phi_neg, PhiInv_Phi]

/-- The median of the standard normal law is `0`. -/
theorem PhiInv_half : PhiInv (1 / 2) = 0 := by
  rw [← Phi_zero, PhiInv_Phi]

/-- `Φ⁻¹(p) ≥ 0` exactly when `p ≥ 1/2`. -/
theorem PhiInv_nonneg_iff (hp : p ∈ Ioo 0 1) : 0 ≤ PhiInv p ↔ 1 / 2 ≤ p := by
  rw [← strictMono_Phi.le_iff_le, Phi_PhiInv hp, Phi_zero]

/-- `Φ⁻¹(p) > 0` exactly when `p > 1/2`. -/
theorem PhiInv_pos_iff (hp : p ∈ Ioo 0 1) : 0 < PhiInv p ↔ 1 / 2 < p := by
  rw [← strictMono_Phi.lt_iff_lt, Phi_PhiInv hp, Phi_zero]

/-- Every Gaussian law is an affine image of the standard one:
`N(m, v) = (z ↦ √v · z + m)_* N(0, 1)`. -/
lemma gaussianReal_eq_map_standard (m : ℝ) (v : ℝ≥0) :
    gaussianReal m v = (gaussianReal 0 1).map fun z ↦ √(v : ℝ) * z + m := by
  rw [show (fun z : ℝ ↦ √(v : ℝ) * z + m) = (· + m) ∘ (√(v : ℝ) * ·) from rfl,
    ← Measure.map_map (measurable_add_const m) (measurable_const_mul _), gaussianReal_map_const_mul,
    gaussianReal_map_add_const, mul_zero, zero_add, mul_one]
  congr
  ext
  simp

/-- **The quantile of a Gaussian law**: the `p`-quantile of `N(m, v)` is `m + √v · Φ⁻¹(p)`. -/
theorem quantile_gaussianReal (m : ℝ) (v : ℝ≥0) (hp : p ∈ Ioo 0 1) :
    quantile (gaussianReal m v) p = m + √(v : ℝ) * PhiInv p := by
  rw [gaussianReal_eq_map_standard, quantile_map (h := fun z ↦ √(v : ℝ) * z + m)
    ((monotone_id.const_mul (by positivity)).add_const m)
    (by fun_prop : Continuous fun z : ℝ ↦ √(v : ℝ) * z + m).lowerSemicontinuous hp,
        PhiInv, add_comm]

end MathFin

namespace Mathlib.Meta.Positivity
open Lean.Meta Qq

/-- Extension for the `positivity` tactic: the standard normal CDF `Φ` is positive. -/
@[positivity MathFin.Phi _]
meta def evalPhi : PositivityExt where eval {u α} _ pα? e :=
  match pα? with | none => pure .none | some _ => do
  match u, α, e with
  | 0, ~q(ℝ), ~q(MathFin.Phi $a) =>
    assertInstancesCommute
    pure (.positive q(MathFin.Phi_pos $a))
  | _, _, _ => throwError "not Phi"

end Mathlib.Meta.Positivity
