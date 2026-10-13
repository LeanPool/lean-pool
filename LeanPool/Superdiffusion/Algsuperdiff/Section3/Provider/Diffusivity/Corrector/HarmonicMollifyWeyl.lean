/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.HarmonicMollifyKernel
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.HarmonicWeak
public import Mathlib.Analysis.Convolution

/-!
# HarmonicMollifyWeyl

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Smooth approximation of a weakly harmonic function (interior Weyl lemma)

`HarmonicWeak` fixes the distributional predicate `IsWeaklyHarmonicOn` and shows
it is consistent with the classical one *for `C^2` functions*.  It cannot
bootstrap: a function that is merely locally integrable and weakly harmonic is
not known there to be smooth, so none of the classical interior estimates apply
to it.  This module removes that obstruction on the interior, by mollification.

## The argument

Write `K_delta` for the normalized smooth radial density of
`HarmonicMollifyKernel`, supported in the Euclidean annulus `(delta/2, delta)`
and of radial moment `1`, and let

```
  (mollify delta u) (x) = ( int u (y) K_delta (|y - x|) dy ) / M_delta ,
```

where `M_delta` is the total mass of the density.

1. **Smoothness.**  The kernel is smooth and compactly supported, so the
   convolution of a locally integrable function with it is smooth
   (`contDiff_mollify`, from Mathlib's `contDiff_convolution_right`).
2. **The mass does not depend on the scale.**  The difference of two normalized
   densities has vanishing radial moment, hence integrates to zero
   (`mollifierMass_eq_of_pos`).
3. **The mollification does not depend on the scale.**  This is the heart of the
   matter.  The difference `K_delta - K_epsilon` is smooth, radial, supported in
   an annulus away from the origin, and of vanishing radial moment; so
   `HarmonicSphereBump` produces a compactly supported radial potential whose
   Laplacian is exactly that difference, and `HarmonicMollifyKernel` upgrades
   that potential to `C^infty`.  Pairing the weak harmonicity of `u` against it
   gives `mollify delta u = mollify epsilon u` at every point whose closed ball
   of radius `max delta epsilon` lies in the harmonicity set
   (`mollify_eq_mollify_of_isWeaklyHarmonicOn`).
4. **Self-adjointness.**  Fubini for the symmetric kernel gives
   `int (mollify delta u) psi = int u (mollify delta psi)`
   (`integral_mollify_mul`).
5. **Passing to the limit.**  For a continuous compactly supported `psi` the
   mollification `mollify delta psi` converges to `psi` uniformly, by the
   concentration estimate of `HarmonicMeanValue` together with uniform
   continuity; all the mollifications live in one fixed compact set.  Combining
   with 3 and 4, the distribution of `u` agrees with that of the *fixed* smooth
   function `mollify r u` on the interior set, and the fundamental lemma of the
   calculus of variations turns this into almost-everywhere equality.

The classical harmonicity of the smooth representative is then read off from
`HarmonicWeak`: it is weakly harmonic because it agrees a.e. with `u`, and it is
`C^2`, so its coordinate Laplacian vanishes pointwise.

The whole Weyl mechanism is packaged in
`exists_contDiff_ae_eq_of_isWeaklyHarmonicOn`, whose statement mentions no
oscillation, no cube and no scale family: it is the reusable part.

## Portability

This file depends only on **Mathlib** and on **CoarseGraining**
(`Homogenization.*`) and on other files of this same harmonic/oscillation
layer.  It mentions no object of the manuscript: no model, no cutoff, no shell,
no corrector, no cube.  It is intended to be portable into CoarseGraining by a
single mechanical namespace rename.

## Divergences and hypotheses

* Local integrability of `u` on the whole carrier is assumed, rather than on the
  harmonicity set only.  This is what makes the convolution meaningful without a
  cut-off bookkeeping layer; a consumer holding an `L^1` function on a bounded
  set extends it by zero.
* The interior set `V` is described by a *uniform* interior radius `r` rather
  than by compact containment.  The two are equivalent for the sets used
  downstream and the uniform radius is what the argument actually consumes.

## Contents

* `mollifierMass`, `mollify` -- the smoothing operator.
* `contDiff_mollify` -- smoothness.
* `mollifierMass_eq_of_pos`, `mollify_eq_mollify_of_isWeaklyHarmonicOn` -- scale
  independence.
* `integral_mollify_mul` -- self-adjointness (Fubini).
* `abs_mollify_sub_le`, `mollify_eq_zero_of_notMem`, `hasCompactSupport_mollify`
  -- concentration and support.
* `exists_contDiff_ae_eq_of_isWeaklyHarmonicOn` -- **the interior Weyl lemma**.

## References

* ABK26, `e.nablaw.oscillations` (the eventual consumer).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport MeasureTheory

noncomputable section

variable {m : ℕ}

/-- The Euclidean gauge dominates the sup norm of the carrier. -/
theorem norm_le_euclideanNorm {d : ℕ} (x : Vec d) : ‖x‖ ≤ euclideanNorm x := by
  rw [pi_norm_le_iff_of_nonneg (euclideanNorm_nonneg x)]
  intro i
  have hle : x i ^ 2 ≤ vecNormSq x := by
    have hsum : vecNormSq x = ∑ j : Fin d, x j * x j := rfl
    rw [hsum, sq]
    exact Finset.single_le_sum (f := fun j : Fin d => x j * x j)
      (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)
  calc ‖x i‖ = Real.sqrt (x i ^ 2) := by rw [Real.sqrt_sq_eq_abs, Real.norm_eq_abs]
    _ ≤ Real.sqrt (vecNormSq x) := Real.sqrt_le_sqrt hle
    _ = euclideanNorm x := rfl

/-- The Euclidean gauge is symmetric in its two arguments. -/
theorem euclideanNorm_sub_comm {d : ℕ} (x y : Vec d) :
    euclideanNorm (x - y) = euclideanNorm (y - x) := by
  have hsq : vecNormSq (x - y) = vecNormSq (y - x) := by
    have h1 : vecNormSq (x - y) = ∑ i : Fin d, (x i - y i) * (x i - y i) := rfl
    have h2 : vecNormSq (y - x) = ∑ i : Fin d, (y i - x i) * (y i - x i) := rfl
    rw [h1, h2]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [euclideanNorm, euclideanNorm, hsq]

/-- The mass of the radial mollifying density at scale `δ`. -/
def mollifierMass (m : ℕ) (δ : ℝ) : ℝ :=
  ∫ x : Vec (m + 1), mollifierProfile m δ (euclideanNorm x) ∂volume

theorem integrable_mollifierProfile_comp {δ : ℝ} (hδ : 0 < δ) (z : Vec (m + 1)) :
    Integrable (fun x : Vec (m + 1) => mollifierProfile m δ (euclideanNorm (x - z))) volume :=
  integrable_radial (continuous_mollifierProfile m δ) hδ
    (fun _ hs => mollifierProfile_eq_zero_of_ge hδ hs) z

theorem integral_mollifierProfile_comp (m : ℕ) (δ : ℝ) (z : Vec (m + 1)) :
    ∫ x : Vec (m + 1), mollifierProfile m δ (euclideanNorm (x - z)) ∂volume
      = mollifierMass m δ :=
  integral_sub_right_eq_self
    (fun w : Vec (m + 1) => mollifierProfile m δ (euclideanNorm w)) z

theorem mollifierMass_pos {δ : ℝ} (hδ : 0 < δ) : 0 < mollifierMass m δ := by
  have h := integral_radial_pos (m := m) (continuous_mollifierProfile m δ)
    (mollifierProfile_nonneg hδ) hδ (fun _ hs => mollifierProfile_eq_zero_of_ge hδ hs)
    (t₀ := 3 * δ / 4) (by linarith)
    (mollifierProfile_pos_of_mem hδ (by linarith) (by linarith)) 0
  rw [integral_mollifierProfile_comp] at h
  exact h

theorem mollifierMass_eq_of_pos {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    mollifierMass m δ = mollifierMass m ε := by
  have hk : Continuous fun s : ℝ => mollifierProfile m δ s - mollifierProfile m ε s :=
    (continuous_mollifierProfile m δ).sub (continuous_mollifierProfile m ε)
  have ha : (0 : ℝ) < min δ ε / 2 := by positivity
  have hb : (0 : ℝ) < max δ ε := lt_of_lt_of_le hδ (le_max_left _ _)
  have hk0 : ∀ s : ℝ, s ≤ min δ ε / 2 →
      mollifierProfile m δ s - mollifierProfile m ε s = 0 := by
    intro s hs
    have h1 : s ≤ δ / 2 := le_trans hs (by have := min_le_left δ ε; linarith)
    have h2 : s ≤ ε / 2 := le_trans hs (by have := min_le_right δ ε; linarith)
    rw [mollifierProfile_eq_zero_of_le hδ h1, mollifierProfile_eq_zero_of_le hε h2, sub_zero]
  have hkb : ∀ s : ℝ, max δ ε ≤ s →
      mollifierProfile m δ s - mollifierProfile m ε s = 0 := by
    intro s hs
    have h1 : δ ≤ s := le_trans (le_max_left δ ε) hs
    have h2 : ε ≤ s := le_trans (le_max_right δ ε) hs
    rw [mollifierProfile_eq_zero_of_ge hδ h1, mollifierProfile_eq_zero_of_ge hε h2, sub_zero]
  have hmom : radialMoment m (fun s => mollifierProfile m δ s - mollifierProfile m ε s)
      (max δ ε) = 0 := by
    rw [radialMoment_sub (continuous_mollifierProfile m δ) (continuous_mollifierProfile m ε),
      radialMoment_mollifierProfile_of_le m hδ (le_max_left _ _),
      radialMoment_mollifierProfile_of_le m hε (le_max_right _ _), sub_self]
  have h0 : ∫ x : Vec (m + 1), (mollifierProfile m δ (euclideanNorm (x - 0))
      - mollifierProfile m ε (euclideanNorm (x - 0))) ∂volume = 0 :=
    integral_radial_eq_zero_of_radialMoment_eq_zero (m := m)
      (k := fun s => mollifierProfile m δ s - mollifierProfile m ε s) hk ha hb hk0 hkb hmom 0
  rw [integral_sub (integrable_mollifierProfile_comp hδ 0)
      (integrable_mollifierProfile_comp hε 0),
    integral_mollifierProfile_comp, integral_mollifierProfile_comp] at h0
  linarith

/-- **The mollification of `u` at scale `δ`**: the average of `u` against the
normalized radial density supported in the Euclidean annulus `(δ/2, δ)`. -/
def mollify (m : ℕ) (δ : ℝ) (u : Vec (m + 1) → ℝ) : Vec (m + 1) → ℝ :=
  fun x => (∫ y, u y * mollifierProfile m δ (euclideanNorm (y - x)) ∂volume) / mollifierMass m δ

theorem contDiff_mollifierKernel {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec (m + 1) => mollifierProfile m δ (euclideanNorm w)) := by
  have h := contDiff_comp_euclideanNorm_sub_of_contDiff (contDiff_mollifierProfile m δ)
    (half_pos hδ) (fun _ hs => mollifierProfile_eq_zero_of_le hδ hs) (0 : Vec (m + 1))
  simpa using h

theorem hasCompactSupport_mollifierKernel {δ : ℝ} (hδ : 0 < δ) :
    HasCompactSupport (fun w : Vec (m + 1) => mollifierProfile m δ (euclideanNorm w)) := by
  have h := hasCompactSupport_comp_euclideanNorm_sub (k := mollifierProfile m δ) hδ
    (fun _ hs => mollifierProfile_eq_zero_of_ge hδ hs) (0 : Vec (m + 1))
  simpa using h

theorem contDiff_mollify {δ : ℝ} (hδ : 0 < δ) {u : Vec (m + 1) → ℝ}
    (hu : LocallyIntegrable u volume) : ContDiff ℝ (⊤ : ℕ∞) (mollify m δ u) := by
  have heq : mollify m δ u = fun x : Vec (m + 1) =>
      convolution u (fun w : Vec (m + 1) => mollifierProfile m δ (euclideanNorm w))
        (ContinuousLinearMap.mul ℝ ℝ) volume x / mollifierMass m δ := by
    funext x
    have hpt : (fun y : Vec (m + 1) => u y * mollifierProfile m δ (euclideanNorm (y - x)))
        = fun y : Vec (m + 1) => u y * mollifierProfile m δ (euclideanNorm (x - y)) :=
      funext fun y => by rw [euclideanNorm_sub_comm]
    show (∫ y, u y * mollifierProfile m δ (euclideanNorm (y - x)) ∂volume) / mollifierMass m δ = _
    rw [hpt, convolution_mul]
  rw [heq]
  exact ((hasCompactSupport_mollifierKernel hδ).contDiff_convolution_right
    (ContinuousLinearMap.mul ℝ ℝ) hu (contDiff_mollifierKernel hδ)).div_const _

theorem integrable_mul_mollifierProfile_comp {δ : ℝ} (hδ : 0 < δ) {u : Vec (m + 1) → ℝ}
    (hu : LocallyIntegrable u volume) (x : Vec (m + 1)) :
    Integrable (fun y : Vec (m + 1) => u y * mollifierProfile m δ (euclideanNorm (y - x)))
      volume := by
  have hg : Continuous fun y : Vec (m + 1) => mollifierProfile m δ (euclideanNorm (y - x)) :=
    continuous_comp_euclideanNorm_sub (continuous_mollifierProfile m δ) x
  have hcs : HasCompactSupport
      fun y : Vec (m + 1) => mollifierProfile m δ (euclideanNorm (y - x)) :=
    hasCompactSupport_comp_euclideanNorm_sub hδ
      (fun _ hs => mollifierProfile_eq_zero_of_ge hδ hs) x
  simpa using hu.integrable_smul_right_of_hasCompactSupport hg hcs

/-- **Mollification of a weakly harmonic function does not depend on the scale.** -/
theorem mollify_eq_mollify_of_isWeaklyHarmonicOn {U : Set (Vec (m + 1))} {u : Vec (m + 1) → ℝ}
    (hu : LocallyIntegrable u volume) (hw : IsWeaklyHarmonicOn U u) {δ ε : ℝ} (hδ : 0 < δ)
    (hε : 0 < ε) {x : Vec (m + 1)} (hball : euclideanClosedBall x (max δ ε) ⊆ U) :
    mollify m δ u x = mollify m ε u x := by
  have hkc : Continuous fun s : ℝ => mollifierProfile m δ s - mollifierProfile m ε s :=
    (continuous_mollifierProfile m δ).sub (continuous_mollifierProfile m ε)
  have hks : ContDiff ℝ (⊤ : ℕ∞) fun s : ℝ => mollifierProfile m δ s - mollifierProfile m ε s :=
    (contDiff_mollifierProfile m δ).sub (contDiff_mollifierProfile m ε)
  have ha : (0 : ℝ) < min δ ε / 2 := by positivity
  have hb : (0 : ℝ) < max δ ε := lt_of_lt_of_le hδ (le_max_left _ _)
  have hk0 : ∀ s : ℝ, s ≤ min δ ε / 2 →
      mollifierProfile m δ s - mollifierProfile m ε s = 0 := by
    intro s hs
    have h1 : s ≤ δ / 2 := le_trans hs (by have := min_le_left δ ε; linarith)
    have h2 : s ≤ ε / 2 := le_trans hs (by have := min_le_right δ ε; linarith)
    rw [mollifierProfile_eq_zero_of_le hδ h1, mollifierProfile_eq_zero_of_le hε h2, sub_zero]
  have hkb : ∀ s : ℝ, max δ ε ≤ s →
      mollifierProfile m δ s - mollifierProfile m ε s = 0 := by
    intro s hs
    rw [mollifierProfile_eq_zero_of_ge hδ (le_trans (le_max_left δ ε) hs),
      mollifierProfile_eq_zero_of_ge hε (le_trans (le_max_right δ ε) hs), sub_zero]
  have hmom : radialMoment m (fun s => mollifierProfile m δ s - mollifierProfile m ε s)
      (max δ ε) = 0 := by
    rw [radialMoment_sub (continuous_mollifierProfile m δ) (continuous_mollifierProfile m ε),
      radialMoment_mollifierProfile_of_le m hδ (le_max_left _ _),
      radialMoment_mollifierProfile_of_le m hε (le_max_right _ _), sub_self]
  have hsupp : tsupport (fun w : Vec (m + 1) =>
      radialPotential m (fun s => mollifierProfile m δ s - mollifierProfile m ε s) (max δ ε)
        (euclideanNorm (w - x))) ⊆ U :=
    (tsupport_radialPotential_comp_subset hkc hb hkb hmom x).trans hball
  have hzero := hw _ (contDiff_radialPotential_comp_of_contDiff hks ha hk0 (max δ ε) x)
    (hasCompactSupport_radialPotential_comp hkc hb hkb hmom x) hsupp
  rw [setIntegral_mul_euclideanCoordLaplacian_eq_integral u hsupp] at hzero
  have hlap : ∀ y : Vec (m + 1), euclideanCoordLaplacian (fun w : Vec (m + 1) =>
      radialPotential m (fun s => mollifierProfile m δ s - mollifierProfile m ε s) (max δ ε)
        (euclideanNorm (w - x))) y
      = mollifierProfile m δ (euclideanNorm (y - x))
        - mollifierProfile m ε (euclideanNorm (y - x)) :=
    fun y => euclideanCoordLaplacian_radialPotential hkc ha hk0 x y
  have hmul : ∀ y : Vec (m + 1), u y * euclideanCoordLaplacian (fun w : Vec (m + 1) =>
      radialPotential m (fun s => mollifierProfile m δ s - mollifierProfile m ε s) (max δ ε)
        (euclideanNorm (w - x))) y
      = u y * mollifierProfile m δ (euclideanNorm (y - x))
        - u y * mollifierProfile m ε (euclideanNorm (y - x)) := by
    intro y
    rw [hlap y]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hmul),
    integral_sub (integrable_mul_mollifierProfile_comp hδ hu x)
      (integrable_mul_mollifierProfile_comp hε hu x)] at hzero
  show (∫ y, u y * mollifierProfile m δ (euclideanNorm (y - x)) ∂volume) / mollifierMass m δ
    = (∫ y, u y * mollifierProfile m ε (euclideanNorm (y - x)) ∂volume) / mollifierMass m ε
  rw [mollifierMass_eq_of_pos hδ hε]
  have : (∫ y, u y * mollifierProfile m δ (euclideanNorm (y - x)) ∂volume)
      = ∫ y, u y * mollifierProfile m ε (euclideanNorm (y - x)) ∂volume := by linarith
  rw [this]

/-- **The mollification is self-adjoint.**  Pairing the mollification of a
locally integrable function against a compactly supported continuous test
function is the same as pairing the function against the mollified test
function.  This is Fubini for the symmetric kernel. -/
theorem integral_mollify_mul {δ : ℝ} (hδ : 0 < δ) {u ψ : Vec (m + 1) → ℝ}
    (hu : LocallyIntegrable u volume) (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, mollify m δ u x * ψ x ∂volume = ∫ y, u y * mollify m δ ψ y ∂volume := by
  obtain ⟨CK, hCK⟩ := (hasCompactSupport_mollifierKernel (m := m) hδ).exists_bound_of_continuous
    (contDiff_mollifierKernel (m := m) hδ).continuous
  have htc : IsCompact (tsupport ψ) := hψc
  obtain ⟨R, hR⟩ := htc.isBounded.subset_closedBall (0 : Vec (m + 1))
  have hbound : ∀ x y : Vec (m + 1),
      ‖u y * mollifierProfile m δ (euclideanNorm (y - x)) * ψ x‖
        ≤ CK * ‖ψ x‖ *
          (Metric.closedBall (0 : Vec (m + 1)) (R + δ)).indicator (fun w => ‖u w‖) y := by
    intro x y
    by_cases hy : y ∈ Metric.closedBall (0 : Vec (m + 1)) (R + δ)
    · rw [Set.indicator_of_mem hy, norm_mul, norm_mul]
      calc ‖u y‖ * ‖mollifierProfile m δ (euclideanNorm (y - x))‖ * ‖ψ x‖
          ≤ ‖u y‖ * CK * ‖ψ x‖ :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hCK (y - x)) (norm_nonneg _)) (norm_nonneg _)
        _ = CK * ‖ψ x‖ * ‖u y‖ := by ring
    · rcases eq_or_ne (ψ x) 0 with hx0 | hx0
      · rw [Set.indicator_of_notMem hy, hx0]
        simp
      · have hxR : ‖x‖ ≤ R := by
          have hmem := hR (subset_tsupport ψ hx0)
          rw [Metric.mem_closedBall, dist_zero_right] at hmem
          exact hmem
        have hyR : R + δ < ‖y‖ := by
          rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
          exact hy
        have hd : δ < ‖y - x‖ := by
          have hsub := norm_sub_norm_le y x
          linarith
        have hz : mollifierProfile m δ (euclideanNorm (y - x)) = 0 :=
          mollifierProfile_eq_zero_of_ge hδ
            (le_of_lt (lt_of_lt_of_le hd (norm_le_euclideanNorm _)))
        rw [Set.indicator_of_notMem hy, hz]
        simp
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun x y : Vec (m + 1) =>
        u y * mollifierProfile m δ (euclideanNorm (y - x)) * ψ x) (volume.prod volume) := by
    have h1 : AEStronglyMeasurable
        (fun z : Vec (m + 1) × Vec (m + 1) => u z.2) (volume.prod volume) :=
      hu.aestronglyMeasurable.comp_snd
    have h2 : AEStronglyMeasurable
        (fun z : Vec (m + 1) × Vec (m + 1) =>
          mollifierProfile m δ (euclideanNorm (z.2 - z.1))) (volume.prod volume) :=
      (((continuous_mollifierProfile m δ).comp
        (continuous_euclideanNorm.comp (continuous_snd.sub continuous_fst)))).aestronglyMeasurable
    have h3 : AEStronglyMeasurable
        (fun z : Vec (m + 1) × Vec (m + 1) => ψ z.1) (volume.prod volume) :=
      (hψ.comp continuous_fst).aestronglyMeasurable
    exact (h1.mul h2).mul h3
  have hInt : Integrable
      (Function.uncurry fun x y : Vec (m + 1) =>
        u y * mollifierProfile m δ (euclideanNorm (y - x)) * ψ x) (volume.prod volume) := by
    refine Integrable.mono' ?_ hmeas (Filter.Eventually.of_forall fun z => hbound z.1 z.2)
    exact Integrable.mul_prod ((hψ.integrable_of_hasCompactSupport hψc).norm.const_mul CK)
      (MeasureTheory.IntegrableOn.integrable_indicator
        ((hu.integrableOn_isCompact (isCompact_closedBall (0 : Vec (m + 1)) (R + δ))).norm)
        measurableSet_closedBall)
  have hswap := integral_integral_swap (μ := (volume : Measure (Vec (m + 1))))
    (ν := (volume : Measure (Vec (m + 1)))) hInt
  have hpt1 : ∀ x : Vec (m + 1), mollify m δ u x * ψ x
      = (∫ y, u y * mollifierProfile m δ (euclideanNorm (y - x)) * ψ x ∂volume)
        / mollifierMass m δ := by
    intro x
    simp only [mollify]
    rw [integral_mul_const]
    ring
  have hpt2 : ∀ y : Vec (m + 1),
      (∫ x, u y * mollifierProfile m δ (euclideanNorm (y - x)) * ψ x ∂volume)
        = u y * ∫ x, ψ x * mollifierProfile m δ (euclideanNorm (x - y)) ∂volume := by
    intro y
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show u y * mollifierProfile m δ (euclideanNorm (y - x)) * ψ x
        = u y * (ψ x * mollifierProfile m δ (euclideanNorm (x - y)))
    rw [euclideanNorm_sub_comm y x]
    ring
  have hpt3 : ∀ y : Vec (m + 1), u y * mollify m δ ψ y
      = u y * (∫ x, ψ x * mollifierProfile m δ (euclideanNorm (x - y)) ∂volume)
        / mollifierMass m δ := by
    intro y
    simp only [mollify]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt1), integral_div, hswap,
    integral_congr_ae (Filter.Eventually.of_forall hpt2),
    integral_congr_ae (Filter.Eventually.of_forall hpt3), integral_div]

/-- **Concentration of the mollification.**  If a continuous function varies by
at most `η` on the closed Euclidean ball of radius `δ` about `y`, then its
mollification at scale `δ` differs from its value at `y` by at most `η`. -/
theorem abs_mollify_sub_le {δ : ℝ} (hδ : 0 < δ) {ψ : Vec (m + 1) → ℝ} (hψ : Continuous ψ)
    {y : Vec (m + 1)} {η : ℝ} (hosc : ∀ x ∈ euclideanClosedBall y δ, |ψ x - ψ y| ≤ η) :
    |mollify m δ ψ y - ψ y| ≤ η := by
  have hM : (0 : ℝ) < mollifierMass m δ := mollifierMass_pos hδ
  have h := abs_integral_mul_radial_sub_le (m := m) hψ (continuous_mollifierProfile m δ)
    (mollifierProfile_nonneg hδ) hδ (fun _ hs => mollifierProfile_eq_zero_of_ge hδ hs) hosc
  rw [integral_mollifierProfile_comp] at h
  have hrw : mollify m δ ψ y - ψ y
      = ((∫ x, ψ x * mollifierProfile m δ (euclideanNorm (x - y)) ∂volume)
          - ψ y * mollifierMass m δ) / mollifierMass m δ := by
    simp only [mollify]
    rw [sub_div, mul_div_assoc, div_self (ne_of_gt hM), mul_one]
  rw [hrw, abs_div, abs_of_pos hM, div_le_iff₀ hM]
  linarith

/-- Outside a slight enlargement of its support the mollification vanishes. -/
theorem mollify_eq_zero_of_notMem {δ R : ℝ} (hδ : 0 < δ) {ψ : Vec (m + 1) → ℝ}
    (hR : tsupport ψ ⊆ Metric.closedBall (0 : Vec (m + 1)) R) {y : Vec (m + 1)}
    (hy : y ∉ Metric.closedBall (0 : Vec (m + 1)) (R + δ)) : mollify m δ ψ y = 0 := by
  have hz : ∀ x : Vec (m + 1), ψ x * mollifierProfile m δ (euclideanNorm (x - y)) = 0 := by
    intro x
    rcases eq_or_ne (ψ x) 0 with hx0 | hx0
    · rw [hx0, zero_mul]
    · have hxR : ‖x‖ ≤ R := by
        have hmem := hR (subset_tsupport ψ hx0)
        rw [Metric.mem_closedBall, dist_zero_right] at hmem
        exact hmem
      have hyR : R + δ < ‖y‖ := by
        rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
        exact hy
      have hd : δ < ‖x - y‖ := by
        rw [norm_sub_rev]
        have hsub := norm_sub_norm_le y x
        linarith
      rw [mollifierProfile_eq_zero_of_ge hδ
        (le_of_lt (lt_of_lt_of_le hd (norm_le_euclideanNorm _))), mul_zero]
  simp only [mollify, hz]
  simp

theorem hasCompactSupport_mollify {δ R : ℝ} (hδ : 0 < δ) {ψ : Vec (m + 1) → ℝ}
    (hR : tsupport ψ ⊆ Metric.closedBall (0 : Vec (m + 1)) R) :
    HasCompactSupport (mollify m δ ψ) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Vec (m + 1)) (R + δ))
    fun _ hy => mollify_eq_zero_of_notMem hδ hR hy

private theorem eq_of_forall_pos_abs_sub_le {A B T : ℝ} (hT : 0 ≤ T)
    (h : ∀ η : ℝ, 0 < η → |A - B| ≤ η * T) : A = B := by
  by_contra hne
  have hpos : 0 < |A - B| := abs_pos.mpr (sub_ne_zero.mpr hne)
  have hη : 0 < |A - B| / (2 * (T + 1)) := by positivity
  have h2 := h _ hη
  have hlt : |A - B| / (2 * (T + 1)) * T < |A - B| := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-- **Interior smoothness of a weakly harmonic function (Weyl's lemma).**

If `u` is locally integrable and weakly harmonic on `U`, and `V` is an open set
all of whose points carry a closed Euclidean ball of a fixed radius `r` inside
`U`, then `u` agrees almost everywhere on `V` with a smooth function whose
coordinate Laplacian vanishes at every point of `V`.

The witness is the mollification `mollify m r u`.  Three facts drive the proof:
the mollification is smooth because the kernel is; it does not depend on the
scale, because the difference of two normalized radial densities has vanishing
radial moment and is therefore the Laplacian of a smooth compactly supported
radial potential, against which the weak harmonicity of `u` pairs to zero; and
the mollification is self-adjoint, so that pairing it against a test function
and letting the scale shrink recovers the pairing of `u` itself. -/
theorem exists_contDiff_ae_eq_of_isWeaklyHarmonicOn {U V : Set (Vec (m + 1))} (hV : IsOpen V)
    {r : ℝ} (hr : 0 < r) (hsub : ∀ x ∈ V, euclideanClosedBall x r ⊆ U)
    {u : Vec (m + 1) → ℝ} (hu : LocallyIntegrable u volume) (hw : IsWeaklyHarmonicOn U u) :
    ∃ v : Vec (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) v ∧
      (∀ᵐ x ∂volume, x ∈ V → v x = u x) ∧ ∀ x ∈ V, euclideanCoordLaplacian v x = 0 := by
  have hself : ∀ x : Vec (m + 1), x ∈ euclideanClosedBall x r := by
    intro x
    rw [mem_euclideanClosedBall_iff_euclideanNorm_le hr.le]
    have hzero : euclideanNorm (x - x) = 0 := by
      simp [euclideanNorm, vecNormSq, vecDot]
    rw [hzero]
    exact hr.le
  have hVU : V ⊆ U := fun x hx => hsub x hx (hself x)
  have hvsmooth : ContDiff ℝ (⊤ : ℕ∞) (mollify m r u) := contDiff_mollify hr hu
  have hvcont : Continuous (mollify m r u) := hvsmooth.continuous
  have hvloc : LocallyIntegrable (mollify m r u) volume := hvcont.locallyIntegrable
  have hconst : ∀ x ∈ V, ∀ δ : ℝ, 0 < δ → δ ≤ r → mollify m δ u x = mollify m r u x := by
    intro x hx δ hδ hδr
    refine mollify_eq_mollify_of_isWeaklyHarmonicOn hu hw hδ hr ?_
    rw [max_eq_right hδr]
    exact hsub x hx
  have hpair : ∀ ψ : Vec (m + 1) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ V → ∫ x, ψ x • (u x - mollify m r u x) ∂volume = 0 := by
    intro ψ hψs hψc hψV
    have hψcont : Continuous ψ := hψs.continuous
    have htc : IsCompact (tsupport ψ) := hψc
    obtain ⟨R, hR⟩ := htc.isBounded.subset_closedBall (0 : Vec (m + 1))
    have huc : UniformContinuous ψ :=
      hψcont.uniformContinuous_of_tendsto_cocompact (HasCompactSupport.is_zero_at_infty hψc)
    have hTint : IntegrableOn (fun y : Vec (m + 1) => ‖u y‖)
        (Metric.closedBall (0 : Vec (m + 1)) (R + r)) volume :=
      (hu.integrableOn_isCompact (isCompact_closedBall (0 : Vec (m + 1)) (R + r))).norm
    have hTnn : (0 : ℝ) ≤ ∫ y in Metric.closedBall (0 : Vec (m + 1)) (R + r), ‖u y‖ ∂volume :=
      integral_nonneg fun _ => norm_nonneg _
    have hIψ : Integrable (fun y : Vec (m + 1) => u y * ψ y) volume := by
      simpa using hu.integrable_smul_right_of_hasCompactSupport hψcont hψc
    have hIv : Integrable (fun y : Vec (m + 1) => mollify m r u y * ψ y) volume := by
      simpa using hvloc.integrable_smul_right_of_hasCompactSupport hψcont hψc
    have hmain : (∫ x, mollify m r u x * ψ x ∂volume) = ∫ y, u y * ψ y ∂volume := by
      refine eq_of_forall_pos_abs_sub_le hTnn ?_
      intro η hη
      obtain ⟨ρ, hρ, hρψ⟩ := Metric.uniformContinuous_iff.mp huc η hη
      have hδ : (0 : ℝ) < min r (ρ / 2) := lt_min hr (by linarith)
      have hδr : min r (ρ / 2) ≤ r := min_le_left _ _
      have hδρ : min r (ρ / 2) < ρ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
      have hstep1 : (∫ x, mollify m r u x * ψ x ∂volume)
          = ∫ x, mollify m (min r (ρ / 2)) u x * ψ x ∂volume := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        show mollify m r u x * ψ x = mollify m (min r (ρ / 2)) u x * ψ x
        rcases eq_or_ne (ψ x) 0 with h0 | h0
        · rw [h0, mul_zero, mul_zero]
        · rw [hconst x (hψV (subset_tsupport ψ h0)) _ hδ hδr]
      have hstep2 := integral_mollify_mul hδ hu hψcont hψc
      have hΨc : Continuous (mollify m (min r (ρ / 2)) ψ) :=
        (contDiff_mollify hδ hψcont.locallyIntegrable).continuous
      have hΨcs : HasCompactSupport (mollify m (min r (ρ / 2)) ψ) :=
        hasCompactSupport_mollify hδ hR
      have hIΨ : Integrable
          (fun y : Vec (m + 1) => u y * mollify m (min r (ρ / 2)) ψ y) volume := by
        simpa using hu.integrable_smul_right_of_hasCompactSupport hΨc hΨcs
      have hdiff : (∫ y, u y * mollify m (min r (ρ / 2)) ψ y ∂volume)
            - ∫ y, u y * ψ y ∂volume
          = ∫ y, u y * (mollify m (min r (ρ / 2)) ψ y - ψ y) ∂volume := by
        rw [← integral_sub hIΨ hIψ]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        ring
      have hbnd : ∀ y : Vec (m + 1),
          ‖u y * (mollify m (min r (ρ / 2)) ψ y - ψ y)‖
            ≤ η * (Metric.closedBall (0 : Vec (m + 1)) (R + r)).indicator
                (fun w => ‖u w‖) y := by
        intro y
        by_cases hy : y ∈ Metric.closedBall (0 : Vec (m + 1)) (R + r)
        · rw [Set.indicator_of_mem hy, norm_mul]
          have hosc : ∀ x ∈ euclideanClosedBall y (min r (ρ / 2)), |ψ x - ψ y| ≤ η := by
            intro x hx
            have hxy : euclideanNorm (x - y) ≤ min r (ρ / 2) :=
              (mem_euclideanClosedBall_iff_euclideanNorm_le hδ.le).mp hx
            have hdist : dist x y < ρ := by
              rw [dist_eq_norm]
              exact lt_of_le_of_lt (le_trans (norm_le_euclideanNorm _) hxy) hδρ
            have hlt := hρψ hdist
            rw [Real.dist_eq] at hlt
            exact hlt.le
          calc ‖u y‖ * ‖mollify m (min r (ρ / 2)) ψ y - ψ y‖ ≤ ‖u y‖ * η :=
                mul_le_mul_of_nonneg_left
                  (by rw [Real.norm_eq_abs]; exact abs_mollify_sub_le hδ hψcont hosc)
                  (norm_nonneg _)
            _ = η * ‖u y‖ := by ring
        · have hy' : y ∉ Metric.closedBall (0 : Vec (m + 1)) (R + min r (ρ / 2)) := fun hmem =>
            hy (Metric.closedBall_subset_closedBall (by linarith) hmem)
          have h1 : mollify m (min r (ρ / 2)) ψ y = 0 := mollify_eq_zero_of_notMem hδ hR hy'
          have h2 : ψ y = 0 := by
            by_contra hne
            exact hy (Metric.closedBall_subset_closedBall (by linarith)
              (hR (subset_tsupport ψ hne)))
          rw [Set.indicator_of_notMem hy, h1, h2, sub_zero, mul_zero, norm_zero, mul_zero]
      have hbndInt : Integrable (fun y : Vec (m + 1) =>
          η * (Metric.closedBall (0 : Vec (m + 1)) (R + r)).indicator
            (fun w => ‖u w‖) y) volume :=
        (MeasureTheory.IntegrableOn.integrable_indicator hTint measurableSet_closedBall).const_mul η
      have hnorm := norm_integral_le_of_norm_le hbndInt (Filter.Eventually.of_forall hbnd)
      have hTeq : (∫ y, η * (Metric.closedBall (0 : Vec (m + 1)) (R + r)).indicator
            (fun w => ‖u w‖) y ∂volume)
          = η * ∫ y in Metric.closedBall (0 : Vec (m + 1)) (R + r), ‖u y‖ ∂volume := by
        rw [integral_const_mul, integral_indicator measurableSet_closedBall]
      calc |(∫ x, mollify m r u x * ψ x ∂volume) - ∫ y, u y * ψ y ∂volume|
          = |∫ y, u y * (mollify m (min r (ρ / 2)) ψ y - ψ y) ∂volume| := by
            rw [hstep1, hstep2, hdiff]
        _ ≤ η * ∫ y in Metric.closedBall (0 : Vec (m + 1)) (R + r), ‖u y‖ ∂volume := by
            rw [← Real.norm_eq_abs]
            exact hnorm.trans (le_of_eq hTeq)
    have hsplit : ∫ x, ψ x • (u x - mollify m r u x) ∂volume
        = (∫ x, u x * ψ x ∂volume) - ∫ x, mollify m r u x * ψ x ∂volume := by
      rw [← integral_sub hIψ hIv]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [smul_eq_mul]
      ring
    rw [hsplit, hmain]
    ring
  have hae : ∀ᵐ x ∂volume, x ∈ V → u x - mollify m r u x = 0 :=
    hV.ae_eq_zero_of_integral_contDiff_smul_eq_zero ((hu.sub hvloc).locallyIntegrableOn V) hpair
  refine ⟨mollify m r u, hvsmooth, ?_, ?_⟩
  · filter_upwards [hae] with x hx hxV
    have hx0 := hx hxV
    linarith
  · have hwv : IsWeaklyHarmonicOn V (mollify m r u) := by
      intro ψ hψs hψc hψV
      have h1 : ∫ y in V, mollify m r u y * euclideanCoordLaplacian ψ y ∂volume
          = ∫ y in V, u y * euclideanCoordLaplacian ψ y ∂volume := by
        refine setIntegral_congr_ae hV.measurableSet ?_
        filter_upwards [hae] with y hy hyV
        have hy0 := hy hyV
        rw [show mollify m r u y = u y by linarith]
      rw [h1]
      exact (hw.mono hVU) ψ hψs hψc hψV
    exact hwv.euclideanCoordLaplacian_eq_zero hV
      (hvsmooth.of_le (WithTop.coe_le_coe.mpr le_top))

end

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
