/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.ModelFree.SVI.SigmaZeroDerivatives
public import LeanPool.MathFin.Models.ModelFree.SVI.QuadraticRay

/-! # The zero-scale certificate

Part of the SVI polynomial-sign certificate (#174).

For `σ = 0`, `b ≥ 0`, `ρ² ≤ 1` and `a > 0` the slice is piecewise linear, and `g(k) ≥ 0` for
every `k ≠ m` is equivalent to two quadratics in the variance `w`, one per wing, being nonnegative
on the ray `w ≥ a` (`sigmaZeroCertificate_iff`).

## Main definitions

* `sigmaZeroBranchQuadratic`: the quadratic in the variance `w` whose sign is that of `g` on a
  wing of slope `s` at zero scale.
* `sigmaZeroBranchCondition`: the sign conditions under which that quadratic is nonnegative on
  the ray `w ≥ a`.
* `sigmaZeroCertificate`: the branch condition on both wings.

## Main results

* `sigmaZeroBranchCondition_iff`: `sigmaZeroBranchCondition p s` iff the branch quadratic is
  nonnegative for all `w ≥ p.a`.
* `sigmaZeroBranchCondition_zero`: for `a > 0`, the condition holds for slope `0`.
* `sigmaZeroCertificate_iff`: for `σ = 0`, `b ≥ 0`, `1 - ρ² ≥ 0` and `a > 0`,
  `sigmaZeroCertificate p` iff `durrleman p k ≥ 0` for every `k ≠ m`.

## Tags

zero-scale SVI, piecewise linear smile, Durrleman condition, butterfly arbitrage, MSC 91G20, JEL G13
-/

@[expose] public section

namespace MathFin
namespace SVI

/-- The quadratic in the variance `w` whose sign is that of `g` on a wing of slope `s` at zero
scale. -/
noncomputable def sigmaZeroBranchQuadratic (p : Params) (s w : ℝ) : ℝ :=
  (1-s^2/4)*w^2+(2*(p.a-s*p.m)-s^2)*w+(p.a-s*p.m)^2

/-- The sign conditions under which the branch quadratic is nonnegative on the ray `w ≥ a`
(`sigmaZeroBranchCondition_iff`). -/
noncomputable def sigmaZeroBranchCondition (p : Params) (s : ℝ) : Prop :=
  let u := 1-s^2/4
  let v := 2*(p.a-s*p.m)-s^2
  let z := (p.a-s*p.m)^2
  0 ≤ u ∧ 0 ≤ u*p.a^2+v*p.a+z ∧
    ((u=0 ∧ 0≤v) ∨ (0<u ∧ (0≤v+2*u*p.a ∨ 0≤4*u*z-v^2)))

/-- The zero-scale certificate: the branch condition on both wings. -/
noncomputable def sigmaZeroCertificate (p : Params) : Prop :=
  sigmaZeroBranchCondition p (leftSlope p) ∧ sigmaZeroBranchCondition p (rightSlope p)

theorem sigmaZeroBranchCondition_iff (p : Params) (s : ℝ) :
    sigmaZeroBranchCondition p s ↔
      ∀ w : ℝ, p.a ≤ w → 0 ≤ sigmaZeroBranchQuadratic p s w := by
  exact (quadratic_nonneg_ray_iff p.a (1-s^2/4)
    (2*(p.a-s*p.m)-s^2) ((p.a-s*p.m)^2)).symm

theorem sigmaZeroBranchCondition_zero (p : Params) (ha : 0 < p.a) :
    sigmaZeroBranchCondition p 0 := by
  rw [sigmaZeroBranchCondition_iff]
  intro w hw
  have : 0<w := lt_of_lt_of_le ha hw
  dsimp [sigmaZeroBranchQuadratic]
  norm_num
  positivity

private theorem quadratic_ray_closed_of_open (p : Params) (s : ℝ)
    (h : ∀ w : ℝ, p.a < w → 0 ≤ sigmaZeroBranchQuadratic p s w) :
    ∀w : ℝ, p.a ≤ w → 0 ≤ sigmaZeroBranchQuadratic p s w := by
  have hc : IsClosed {w : ℝ | 0 ≤ sigmaZeroBranchQuadratic p s w} :=
    isClosed_le continuous_const (by unfold sigmaZeroBranchQuadratic; fun_prop)
  have hh : Set.Ioi p.a ⊆ {w : ℝ | 0 ≤ sigmaZeroBranchQuadratic p s w} := h
  have hh' := hc.closure_subset_iff.mpr hh
  rw [closure_Ioi] at hh'
  exact hh'

private theorem sigmaZeroBranch_durrleman (p : Params) (s k : ℝ)
    (hv : variance p k = p.a + s * (k - p.m)) (hp : slope p k = s)
    (hc : curvature p k = 0) (hw : 0 < variance p k) :
    0 ≤ durrleman p k ↔ 0 ≤ sigmaZeroBranchQuadratic p s (variance p k) := by
  have hn := ne_of_gt hw
  have he : 4*(variance p k)^2*durrleman p k =
      sigmaZeroBranchQuadratic p s (variance p k) := by
    unfold durrleman sigmaZeroBranchQuadratic
    rw [hp,hc]
    field_simp
    rw [hv]
    ring
  rw [← he]
  exact (mul_nonneg_iff_of_pos_left (by positivity)).symm

theorem sigmaZeroCertificate_iff (p : Params) (hs : p.sigma = 0)
    (hb : 0 ≤ p.b) (hr : 0 ≤ 1 - p.rho ^ 2) (ha : 0 < p.a) :
    sigmaZeroCertificate p ↔ ∀k : ℝ, k≠p.m → 0≤durrleman p k := by
  have hw : ∀k : ℝ,0<variance p k := (sigmaZero_variance_pos_iff p hs hb hr).mpr ha
  have hl := leftSlope_nonpos p hb hr
  have hr' := rightSlope_nonneg p hb hr
  constructor
  · rintro ⟨hleft,hright⟩ k hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [sigmaZeroBranch_durrleman p (leftSlope p) k
        (sigmaZero_variance_left p hs k h.le) (sigmaZero_slope_left p hs k h)
        (sigmaZero_curvature p hs k) (hw k)]
      exact (sigmaZeroBranchCondition_iff p _).mp hleft _ (sigmaZero_variance_ge p hs hb hr k)
    · rw [sigmaZeroBranch_durrleman p (rightSlope p) k
        (sigmaZero_variance_right p hs k h.le) (sigmaZero_slope_right p hs k h)
        (sigmaZero_curvature p hs k) (hw k)]
      exact (sigmaZeroBranchCondition_iff p _).mp hright _ (sigmaZero_variance_ge p hs hb hr k)
  · intro h
    constructor
    · by_cases hz : leftSlope p = 0
      · rw [hz]; exact sigmaZeroBranchCondition_zero p ha
      rw [sigmaZeroBranchCondition_iff]
      apply quadratic_ray_closed_of_open
      intro w hwa
      let k := p.m+(w-p.a)/leftSlope p
      have hsneg : leftSlope p < 0 := lt_of_le_of_ne hl hz
      have hk : k < p.m := by
        have := div_neg_of_pos_of_neg (sub_pos.mpr hwa) hsneg
        dsimp [k]; linarith
      have hvar : variance p k = w := by
        rw [sigmaZero_variance_left p hs k hk.le]
        dsimp [k]
        field_simp
        ring
      have hh := (sigmaZeroBranch_durrleman p (leftSlope p) k
        (sigmaZero_variance_left p hs k hk.le) (sigmaZero_slope_left p hs k hk)
        (sigmaZero_curvature p hs k) (hw k)).mp (h k (ne_of_lt hk))
      simpa [hvar] using hh
    · by_cases hz : rightSlope p = 0
      · rw [hz]; exact sigmaZeroBranchCondition_zero p ha
      rw [sigmaZeroBranchCondition_iff]
      apply quadratic_ray_closed_of_open
      intro w hwa
      let k := p.m+(w-p.a)/rightSlope p
      have hspos : 0 < rightSlope p := lt_of_le_of_ne hr' (Ne.symm hz)
      have hk : p.m < k := by
        have := div_pos (sub_pos.mpr hwa) hspos
        dsimp [k]; linarith
      have hvar : variance p k = w := by
        rw [sigmaZero_variance_right p hs k hk.le]
        dsimp [k]
        field_simp
        ring
      have hh := (sigmaZeroBranch_durrleman p (rightSlope p) k
        (sigmaZero_variance_right p hs k hk.le) (sigmaZero_slope_right p hs k hk)
        (sigmaZero_curvature p hs k) (hw k)).mp (h k (ne_of_gt hk))
      simpa [hvar] using hh

end SVI
end MathFin
