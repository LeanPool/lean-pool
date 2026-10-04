/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Regularity.CoeffWkInfty
public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Haar.Unique


/-!
# Mollifying a `W^{1,∞}` weight

`EllipticPdes.Regularity.HasWeakDerivOn.mul_contDiff_left` proves the weak-derivative Leibniz
rule for a `C¹` weight, by mollifying the weight and differentiating the mollification
classically. Guo's hypothesis supplies no classical derivative, so that route is closed and the
mollification has to take the weak derivative instead. This file rebuilds the two facts about
mollification the Leibniz rule needs, with continuity of the weight dropped throughout.

* The sup bound survives with measurability alone. `EllipticPdes.Regularity` already had this
  for a continuous weight; continuity entered only through the integrability of the convolution
  integrand, which an essential bound supplies just as well.
* The derivative of the mollification is the mollification of the *weak* derivative. This is
  where the weak hypothesis does the work: the classical proof moves the derivative from the
  kernel back onto the weight by integration by parts, and `HasWeakPartial` is that
  integration-by-parts identity, applied to the reflected kernel `t ↦ ρ (x - t)`, which is a
  legitimate test function. The weak version is shorter than the `C¹` version it replaces.

## Main declarations

* `abs_convolution_le_of_measurable`: a mollification inherits an essential sup bound, at every
  point.
* `partialD_convolution_eq_of_hasWeakPartial`: `∂_ℓ (a ⋆ ρ) = a' ⋆ ρ` when `a'` is the weak
  `ℓ`-derivative of `a`.
-/

@[expose] public section

open MeasureTheory
open scoped Topology ENNReal Convolution

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-- The scalar convolution written as an integral. `convolution_def` states it with the
`lsmul` action; over `ℝ` that action is multiplication. -/
theorem convolution_lsmul_apply (F K : EuclideanSpace ℝ (Fin d) → ℝ)
    (y : EuclideanSpace ℝ (Fin d)) :
    (F ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] K) y
      = ∫ t, F t * K (y - t) ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) := by
  rw [convolution_def]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]

/-! ### Sup bound with no continuity assumed -/

/-- **Sup bound for a mollification of an essentially bounded weight.** If `h` is measurable and
bounded by `M` almost everywhere, and `ρ` is a non-negative continuous compactly supported kernel
of unit mass, then `h ⋆ ρ` is bounded by `M` at every point.

Continuity of `h` is unused. It entered the `C¹` version only to make the integrand
`|h t| · ρ (x - t)` integrable, and domination by `M · ρ (x - t)` does that under an essential
bound alone. -/
theorem abs_convolution_le_of_measurable
    {ρ : EuclideanSpace ℝ (Fin d) → ℝ} (hρ0 : 0 ≤ ρ) (hρc : Continuous ρ)
    (hρcs : HasCompactSupport ρ)
    (hρ1 : ∫ y, ρ y ∂(volume : Measure (EuclideanSpace ℝ (Fin d))) = 1)
    {h : EuclideanSpace ℝ (Fin d) → ℝ} (hhm : Measurable h) {M : ℝ}
    (hM : ∀ᵐ t ∂(volume : Measure (EuclideanSpace ℝ (Fin d))), |h t| ≤ M)
    (x : EuclideanSpace ℝ (Fin d)) :
    |(h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) x| ≤ M := by
  have hshift_c : Continuous (fun t => ρ (x - t)) :=
    hρc.comp (continuous_const.sub continuous_id)
  have hshift_cs : HasCompactSupport (fun t => ρ (x - t)) :=
    hρcs.comp_homeomorph (Homeomorph.subLeft x)
  have hval : (h ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) x
      = ∫ t, h t * ρ (x - t) ∂volume := by
    rw [convolution_def]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hintM : Integrable (fun t => M * ρ (x - t)) volume :=
    (continuous_const.mul hshift_c).integrable_of_hasCompactSupport hshift_cs.mul_left
  have hprod : Integrable (fun t => h t * ρ (x - t)) volume := by
    refine hintM.mono' (hhm.aestronglyMeasurable.mul hshift_c.aestronglyMeasurable) ?_
    filter_upwards [hM] with t ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 (x - t))]
    exact mul_le_mul_of_nonneg_right ht (hρ0 (x - t))
  have habs : Integrable (fun t => |h t| * ρ (x - t)) volume := by
    refine hprod.abs.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [abs_mul, abs_of_nonneg (hρ0 (x - t))]
  rw [hval]
  calc |∫ t, h t * ρ (x - t) ∂volume|
      ≤ ∫ t, |h t * ρ (x - t)| ∂volume := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun t => h t * ρ (x - t))
    _ = ∫ t, |h t| * ρ (x - t) ∂volume := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        simp only [abs_mul, abs_of_nonneg (hρ0 (x - t))]
    _ ≤ ∫ t, M * ρ (x - t) ∂volume := by
        refine integral_mono_ae habs hintM ?_
        filter_upwards [hM] with t ht
        exact mul_le_mul_of_nonneg_right ht (hρ0 (x - t))
    _ = M * ∫ t, ρ (x - t) ∂volume := integral_const_mul M _
    _ = M * 1 := by rw [integral_sub_left_eq_self ρ volume x, hρ1]
    _ = M := mul_one M

/-- **Locality of a mollification.** If the kernel vanishes outside the ball of radius `r` and two
weights agree on the ball of radius `r` about `x`, their mollifications agree at `x`. This is
what lets a globally bounded weight, which lies in no `Lᵖ` on the whole space, be replaced near
a compact set by a truncation that does, without changing the mollification there. -/
theorem convolution_congr_of_eqOn {a b ρ : EuclideanSpace ℝ (Fin d) → ℝ}
    {x : EuclideanSpace ℝ (Fin d)} {r : ℝ}
    (hρsupp : ∀ y : EuclideanSpace ℝ (Fin d), r ≤ ‖y‖ → ρ y = 0)
    (heq : ∀ t : EuclideanSpace ℝ (Fin d), ‖x - t‖ < r → a t = b t) :
    (a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) x
      = (b ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) x := by
  rw [convolution_lsmul_apply, convolution_lsmul_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  change a t * ρ (x - t) = b t * ρ (x - t)
  rcases lt_or_ge ‖x - t‖ r with hlt | hge
  · rw [heq t hlt]
  · rw [hρsupp (x - t) hge, mul_zero, mul_zero]

/-! ### Derivative of a mollification from the weak derivative -/

/-- **Reflected kernel as a test function.** For a smooth compactly supported `ρ`, the map
`t ↦ ρ (x - t)` is smooth with compact support, so `HasWeakPartial` may be applied to it. -/
theorem contDiff_reflect {ρ : EuclideanSpace ℝ (Fin d) → ℝ} (hρcd : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (x : EuclideanSpace ℝ (Fin d)) : ContDiff ℝ (⊤ : ℕ∞) (fun t => ρ (x - t)) :=
  hρcd.comp (contDiff_const.sub contDiff_id)

/-- The classical partial derivative of the reflected kernel is the reflection of the partial
derivative, with a sign: `∂_ℓ (t ↦ ρ (x - t)) = -(∂_ℓ ρ) (x - t)`. -/
theorem partialD_reflect {ρ : EuclideanSpace ℝ (Fin d) → ℝ} (hρcd : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (ℓ : Fin d) (x t : EuclideanSpace ℝ (Fin d)) :
    partialD ℓ (fun s => ρ (x - s)) t = -(partialD ℓ ρ) (x - t) := by
  have hρdiff : Differentiable ℝ ρ := hρcd.differentiable (by simp)
  have hfd : HasFDerivAt (fun s => ρ (x - s))
      ((fderiv ℝ ρ (x - t)).comp (-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin d)))) t :=
    (hρdiff (x - t)).hasFDerivAt.comp t ((hasFDerivAt_id t).const_sub x)
  simp only [partialD]
  rw [hfd.fderiv]
  simp only [ContinuousLinearMap.comp_apply, _root_.neg_apply,
    ContinuousLinearMap.id_apply, map_neg]

/-- **Derivative of a mollified `W^{1,∞}` weight is the mollification of its weak
derivative.** For `a` with weak `ℓ`-derivative `a'` and a smooth compactly supported kernel `ρ`,
`∂_ℓ (a ⋆ ρ) = a' ⋆ ρ`.

The derivative first passes to the kernel, `∂_ℓ (a ⋆ ρ) = a ⋆ ∂_ℓ ρ`, which needs only local
integrability of `a`. Moving it back onto `a` is where the `C¹` proof integrates by parts, and
here it is the hypothesis: `HasWeakPartial` applied to the reflected kernel `t ↦ ρ (x - t)`
states exactly that identity, and `partialD_reflect` supplies the sign. -/
theorem partialD_convolution_eq_of_hasWeakPartial {ℓ : Fin d}
    {a a' : EuclideanSpace ℝ (Fin d) → ℝ} (haLI : LocallyIntegrable a volume)
    (ha : HasWeakPartial ℓ a a')
    {ρ : EuclideanSpace ℝ (Fin d) → ℝ} (hρcd : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hρcs : HasCompactSupport ρ) :
    partialD ℓ (a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ)
      = a' ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ := by
  have hρcd1 : ContDiff ℝ 1 ρ := hρcd.of_le (by exact_mod_cast le_top)
  funext x
  -- Step 1: the derivative passes to the kernel, which needs only local integrability of `a`.
  have hderiv := hρcs.hasFDerivAt_convolution_right
    (L := ContinuousLinearMap.lsmul ℝ ℝ) haLI hρcd1 x
  have step1 : partialD ℓ (a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) x
      = (a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] partialD ℓ ρ) x := by
    have hpd : partialD ℓ (a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) x
        = (fderiv ℝ (a ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ρ) x)
            (EuclideanSpace.single ℓ 1) := rfl
    have hprec := convolution_precompR_apply (𝕜 := ℝ)
      (L := ContinuousLinearMap.lsmul ℝ ℝ) haLI (hρcs.fderiv ℝ)
      (hρcd.continuous_fderiv (by simp)) x (EuclideanSpace.single ℓ 1)
    rw [hpd, hderiv.fderiv, hprec]
    rfl
  rw [step1]
  -- Step 2: the weak derivative moves it back onto `a`, tested against the reflected kernel.
  have hweak := ha (fun s => ρ (x - s)) (contDiff_reflect hρcd x)
    (hρcs.comp_homeomorph (Homeomorph.subLeft x))
  have hlhs : ∫ t, a t * partialD ℓ (fun s => ρ (x - s)) t
      = - ∫ t, a t * (partialD ℓ ρ) (x - t) := by
    rw [← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    change a t * partialD ℓ (fun s => ρ (x - s)) t = -(a t * (partialD ℓ ρ) (x - t))
    rw [partialD_reflect hρcd ℓ x t]
    ring
  rw [hlhs] at hweak
  rw [convolution_lsmul_apply, convolution_lsmul_apply]
  exact neg_injective hweak

end EllipticPdes.Regularity
