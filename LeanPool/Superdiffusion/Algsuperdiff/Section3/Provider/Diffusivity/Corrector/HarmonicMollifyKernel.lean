/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.HarmonicBallMeanValue
public import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# HarmonicMollifyKernel

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# A smooth radial mollifying density and the smoothness of its radial potential

`HarmonicSphereProfile` and `HarmonicSphereBump` build, for every *continuous*
annulus-supported density `k` of vanishing radial moment, a compactly supported
`C^2` function `psi` on `Vec (m + 1)` with `Delta psi = k (|. - z|)`.  That
regularity is exactly what Green's second identity needs, but it is one degree
too weak for the *distributional* harmonicity predicate of `HarmonicWeak`, whose
test class is `C^infty`.  This module supplies the missing regularity and the
concrete density that the mollification argument runs on:

* the radial potential of a **smooth** annulus-supported density is itself
  smooth (`contDiff_radialPotential_comp_of_contDiff`), because the radial
  moment gains one derivative from the fundamental theorem of calculus, the
  radial slope divides by `t^m` away from the origin, and the potential gains
  one more derivative; near the origin the profile is constant, which is what
  `contDiff_radial` needs;
* an explicit smooth density `mollifierProfile m delta`, supported in the
  annulus `(delta/2, delta)`, nonnegative, and normalized so that its radial
  moment equals `1` at every radius `>= delta`.

The annulus support -- rather than a density concentrated at the origin -- is
forced by the potential construction: a radial density must vanish near the
centre for its potential to be smooth there.  It costs nothing, because an
annulus density is still an approximate identity as `delta -> 0`.

## Portability

This file depends only on **Mathlib** and on **CoarseGraining**
(`Homogenization.*`) and on other files of this same harmonic/oscillation
layer.  It mentions no object of the manuscript: no model, no cutoff, no shell,
no corrector, no cube.  It is intended to be portable into CoarseGraining by a
single mechanical namespace rename.

## Contents

* `contDiff_radialMoment`, `contDiffOn_radialSlope`, `contDiffOn_radialPotential`
  -- the regularity chain for a smooth density.
* `contDiff_radialPotential_comp_of_contDiff` -- the smooth radial potential.
* `contDiff_comp_euclideanNorm_sub_of_contDiff`,
  `tsupport_comp_euclideanNorm_sub_subset`,
  `hasCompactSupport_comp_euclideanNorm_sub` -- a smooth annulus density read as
  a smooth compactly supported function on `Vec (m + 1)`.
* `unitAnnulusBump`, `annulusProfile`, `mollifierProfile` -- the explicit
  density family, with `radialMoment_mollifierProfile_of_le` normalizing it.

## References

* ABK26, `e.nablaw.oscillations` (the eventual consumer).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport MeasureTheory

noncomputable section

/-! ### Regularity of the radial potential of a smooth density -/

/-- The radial moment of a smooth density is smooth: it is an antiderivative of
`t ↦ t^m * k t`. -/
theorem contDiff_radialMoment {m : ℕ} {k : ℝ → ℝ} (hk : ContDiff ℝ (⊤ : ℕ∞) k) :
    ContDiff ℝ (⊤ : ℕ∞) (radialMoment m k) := by
  have hderiv : deriv (radialMoment m k) = fun t : ℝ => t ^ m * k t := by
    funext t
    exact (hasDerivAt_radialMoment (m := m) hk.continuous t).deriv
  rw [contDiff_infty_iff_deriv, hderiv]
  exact ⟨fun t => (hasDerivAt_radialMoment (m := m) hk.continuous t).differentiableAt,
    (contDiff_id.pow m).mul hk⟩

/-- The radial slope of a smooth density is smooth away from the origin. -/
theorem contDiffOn_radialSlope {m : ℕ} {k : ℝ → ℝ} (hk : ContDiff ℝ (⊤ : ℕ∞) k) :
    ContDiffOn ℝ (⊤ : ℕ∞) (radialSlope m k) (Set.Ioi 0) := by
  have hrw : radialSlope m k = fun t : ℝ => radialMoment m k t / t ^ m := rfl
  rw [hrw]
  exact ContDiffOn.div (contDiff_radialMoment hk).contDiffOn (contDiff_id.pow m).contDiffOn
    fun t ht => pow_ne_zero _ (ne_of_gt ht)

/-- The radial potential of a smooth annulus-supported density is smooth away
from the origin. -/
theorem contDiffOn_radialPotential {m : ℕ} {k : ℝ → ℝ} {a : ℝ} (hk : ContDiff ℝ (⊤ : ℕ∞) k)
    (ha : 0 < a) (hk0 : ∀ s : ℝ, s ≤ a → k s = 0) (b : ℝ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (radialPotential m k b) (Set.Ioi 0) := by
  have hstep : ((⊤ : ℕ∞) : WithTop ℕ∞) = ((⊤ : ℕ∞) : WithTop ℕ∞) + 1 := by norm_num
  rw [hstep, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioi]
  refine ⟨fun s _ => ((hasDerivAt_radialPotential hk.continuous ha hk0 b
      s).differentiableAt).differentiableWithinAt, fun h => absurd h (by simp), ?_⟩
  refine (contDiffOn_radialSlope (m := m) hk).congr fun s _ => ?_
  exact (hasDerivAt_radialPotential hk.continuous ha hk0 b s).deriv

/-- **The smooth radial potential.**  For a smooth density supported in an
annulus `[a, b]` with `a > 0`, the radial potential composed with the Euclidean
gauge is smooth on all of `Vec (m + 1)`, centre included: it is constant on the
ball of radius `a`. -/
theorem contDiff_radialPotential_comp_of_contDiff {m : ℕ} {k : ℝ → ℝ} {a : ℝ}
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (ha : 0 < a) (hk0 : ∀ s : ℝ, s ≤ a → k s = 0) (b : ℝ)
    (z : Vec (m + 1)) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun w : Vec (m + 1) => radialPotential m k b (euclideanNorm (w - z))) :=
  contDiff_radial ha
    (fun _ ht => (contDiffOn_radialPotential hk ha hk0 b).contDiffAt (isOpen_Ioi.mem_nhds ht))
    (fun _ _ htlt => radialPotential_eq_of_le hk.continuous ha hk0 (le_of_lt htlt))

/-! ### A smooth annulus density as a function on the carrier -/

/-- A smooth density vanishing near the origin is smooth as a radial function on
`Vec (m + 1)`. -/
theorem contDiff_comp_euclideanNorm_sub_of_contDiff {m : ℕ} {k : ℝ → ℝ} {a : ℝ}
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (ha : 0 < a) (hk0 : ∀ s : ℝ, s ≤ a → k s = 0)
    (z : Vec (m + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec (m + 1) => k (euclideanNorm (w - z))) :=
  contDiff_radial ha (fun _ _ => hk.contDiffAt)
    (fun _ _ htlt => by rw [hk0 _ htlt.le, hk0 0 ha.le])

/-- A density vanishing outside `[0, b]` gives a radial function supported in the
closed Euclidean ball of radius `b`. -/
theorem tsupport_comp_euclideanNorm_sub_subset {m : ℕ} {k : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hkb : ∀ s : ℝ, b ≤ s → k s = 0) (z : Vec (m + 1)) :
    tsupport (fun w : Vec (m + 1) => k (euclideanNorm (w - z))) ⊆ euclideanClosedBall z b := by
  refine closure_minimal ?_ (isClosed_euclideanClosedBall z b)
  intro w hw
  rw [mem_euclideanClosedBall_iff_euclideanNorm_le hb.le]
  by_contra hnot
  exact hw (hkb _ (le_of_lt (lt_of_not_ge hnot)))

/-- The radial function attached to a density vanishing outside `[0, b]` has
compact support. -/
theorem hasCompactSupport_comp_euclideanNorm_sub {m : ℕ} {k : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (hkb : ∀ s : ℝ, b ≤ s → k s = 0) (z : Vec (m + 1)) :
    HasCompactSupport (fun w : Vec (m + 1) => k (euclideanNorm (w - z))) :=
  IsCompact.of_isClosed_subset (isCompact_euclideanClosedBall z hb.le) isClosed_closure
    (tsupport_comp_euclideanNorm_sub_subset hb hkb z)

/-! ### The explicit smooth annulus density -/

/-- Bump data on the line: inner radius `1/8`, outer radius `1/4`, centre `3/4`. -/
def unitAnnulusBumpData : ContDiffBump ((3 : ℝ) / 4) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- The reference smooth bump on the line, supported in the annulus `(1/2, 1)`
and equal to `1` on `[5/8, 7/8]`. -/
def unitAnnulusBump : ℝ → ℝ := unitAnnulusBumpData

theorem contDiff_unitAnnulusBump : ContDiff ℝ (⊤ : ℕ∞) unitAnnulusBump :=
  unitAnnulusBumpData.contDiff

theorem unitAnnulusBump_nonneg (t : ℝ) : 0 ≤ unitAnnulusBump t :=
  ContDiffBump.nonneg unitAnnulusBumpData (x := t)

theorem support_unitAnnulusBump :
    Function.support unitAnnulusBump = Set.Ioo (1 / 2 : ℝ) 1 := by
  have h : Function.support unitAnnulusBump
      = Metric.ball ((3 : ℝ) / 4) unitAnnulusBumpData.rOut :=
    ContDiffBump.support_eq unitAnnulusBumpData
  rw [h, show unitAnnulusBumpData.rOut = 1 / 4 from rfl, Real.ball_eq_Ioo]
  norm_num

theorem unitAnnulusBump_eq_zero_of_le {t : ℝ} (ht : t ≤ 1 / 2) : unitAnnulusBump t = 0 := by
  by_contra hne
  have hmem : t ∈ Set.Ioo (1 / 2 : ℝ) 1 := by
    rw [← support_unitAnnulusBump]; exact hne
  linarith [hmem.1]

theorem unitAnnulusBump_eq_zero_of_ge {t : ℝ} (ht : 1 ≤ t) : unitAnnulusBump t = 0 := by
  by_contra hne
  have hmem : t ∈ Set.Ioo (1 / 2 : ℝ) 1 := by
    rw [← support_unitAnnulusBump]; exact hne
  linarith [hmem.2]

theorem unitAnnulusBump_eq_one {t : ℝ} (h1 : 5 / 8 ≤ t) (h2 : t ≤ 7 / 8) :
    unitAnnulusBump t = 1 := by
  have hmem : t ∈ Metric.closedBall ((3 : ℝ) / 4) unitAnnulusBumpData.rIn := by
    rw [show unitAnnulusBumpData.rIn = 1 / 8 from rfl, Real.closedBall_eq_Icc]
    constructor <;> [linarith; linarith]
  exact ContDiffBump.one_of_mem_closedBall unitAnnulusBumpData hmem

/-- The smooth annulus density at scale `δ`, supported in `(δ/2, δ)`. -/
def annulusProfile (δ : ℝ) : ℝ → ℝ := fun t => unitAnnulusBump (t / δ)

theorem contDiff_annulusProfile (δ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (annulusProfile δ) :=
  contDiff_unitAnnulusBump.comp (contDiff_id.div_const δ)

theorem continuous_annulusProfile (δ : ℝ) : Continuous (annulusProfile δ) :=
  (contDiff_annulusProfile δ).continuous

theorem annulusProfile_nonneg (δ : ℝ) (t : ℝ) : 0 ≤ annulusProfile δ t :=
  unitAnnulusBump_nonneg _

theorem annulusProfile_eq_zero_of_le {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : t ≤ δ / 2) :
    annulusProfile δ t = 0 :=
  unitAnnulusBump_eq_zero_of_le (by rw [div_le_iff₀ hδ]; linarith)

theorem annulusProfile_eq_zero_of_ge {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : δ ≤ t) :
    annulusProfile δ t = 0 :=
  unitAnnulusBump_eq_zero_of_ge (by rw [le_div_iff₀ hδ]; linarith)

theorem annulusProfile_eq_one {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (h1 : 5 * δ / 8 ≤ t)
    (h2 : t ≤ 7 * δ / 8) : annulusProfile δ t = 1 :=
  unitAnnulusBump_eq_one (by rw [le_div_iff₀ hδ]; linarith) (by rw [div_le_iff₀ hδ]; linarith)

theorem radialMoment_annulusProfile_pos (m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    0 < radialMoment m (annulusProfile δ) δ :=
  radialMoment_pos_of_pos_on (continuous_annulusProfile δ) (annulusProfile_nonneg δ)
    (p := 5 * δ / 8) (q := 7 * δ / 8) (by linarith) (by linarith) (by linarith)
    (fun t h1 h2 => by rw [annulusProfile_eq_one hδ h1.le h2.le]; norm_num)

private theorem radialMoment_div (m : ℕ) (k : ℝ → ℝ) (c t : ℝ) :
    radialMoment m (fun s => k s / c) t = radialMoment m k t / c := by
  simp only [radialMoment, ← mul_div_assoc]
  exact intervalIntegral.integral_div c _

/-- Radial moments are additive, hence subtractive. -/
theorem radialMoment_sub {m : ℕ} {k₁ k₂ : ℝ → ℝ} (hk₁ : Continuous k₁) (hk₂ : Continuous k₂)
    (t : ℝ) :
    radialMoment m (fun s => k₁ s - k₂ s) t = radialMoment m k₁ t - radialMoment m k₂ t := by
  have h := radialMoment_linear (m := m) hk₁ hk₂ 1 (-1) t
  simpa using! h

/-- **The normalized smooth radial density at scale `δ`.**  It is smooth,
nonnegative, supported in the annulus `(δ/2, δ)`, and has radial moment `1`. -/
def mollifierProfile (m : ℕ) (δ : ℝ) : ℝ → ℝ :=
  fun t => annulusProfile δ t / radialMoment m (annulusProfile δ) δ

theorem contDiff_mollifierProfile (m : ℕ) (δ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (mollifierProfile m δ) :=
  (contDiff_annulusProfile δ).div_const _

theorem continuous_mollifierProfile (m : ℕ) (δ : ℝ) : Continuous (mollifierProfile m δ) :=
  (contDiff_mollifierProfile m δ).continuous

theorem mollifierProfile_nonneg {m : ℕ} {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    0 ≤ mollifierProfile m δ t :=
  div_nonneg (annulusProfile_nonneg δ t) (radialMoment_annulusProfile_pos m hδ).le

theorem mollifierProfile_eq_zero_of_le {m : ℕ} {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : t ≤ δ / 2) :
    mollifierProfile m δ t = 0 := by
  simp only [mollifierProfile, annulusProfile_eq_zero_of_le hδ ht, zero_div]

theorem mollifierProfile_eq_zero_of_ge {m : ℕ} {δ : ℝ} (hδ : 0 < δ) {t : ℝ} (ht : δ ≤ t) :
    mollifierProfile m δ t = 0 := by
  simp only [mollifierProfile, annulusProfile_eq_zero_of_ge hδ ht, zero_div]

theorem mollifierProfile_pos_of_mem {m : ℕ} {δ : ℝ} (hδ : 0 < δ) {t : ℝ}
    (h1 : 5 * δ / 8 < t) (h2 : t < 7 * δ / 8) : 0 < mollifierProfile m δ t := by
  simp only [mollifierProfile, annulusProfile_eq_one hδ h1.le h2.le]
  exact one_div_pos.mpr (radialMoment_annulusProfile_pos m hδ)

theorem radialMoment_mollifierProfile (m : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    radialMoment m (mollifierProfile m δ) δ = 1 := by
  have hrw : mollifierProfile m δ
      = fun t => annulusProfile δ t / radialMoment m (annulusProfile δ) δ := rfl
  rw [hrw, radialMoment_div]
  exact div_self (ne_of_gt (radialMoment_annulusProfile_pos m hδ))

/-- The normalization is stable at every radius beyond the support. -/
theorem radialMoment_mollifierProfile_of_le (m : ℕ) {δ b : ℝ} (hδ : 0 < δ) (hb : δ ≤ b) :
    radialMoment m (mollifierProfile m δ) b = 1 := by
  rw [radialMoment_eq_of_ge (m := m) (continuous_mollifierProfile m δ)
    (fun _ hs => mollifierProfile_eq_zero_of_ge hδ hs) hb]
  exact radialMoment_mollifierProfile m hδ

end

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
