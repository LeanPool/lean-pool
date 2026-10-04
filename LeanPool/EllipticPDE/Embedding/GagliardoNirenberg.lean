/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Embedding.Morrey
public import LeanPool.EllipticPDE.Regularity.CutoffTower
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality


/-!
# Sobolev bootstrap from `Lᵖ` to the conjugate exponent

`morrey_ball` needs a gradient in `Lᵖ` with `p > d`, and the interior `H²` estimate delivers one
in `L²`, so the two compose directly only when `d = 1`. The Gagliardo-Nirenberg-Sobolev
inequality closes the gap in low dimension: an `Lᵖ` weak gradient with `1 ≤ p < d` upgrades to
`Lᵖ'` at the Sobolev conjugate `1/p' = 1/p - 1/d`, and Morrey then applies whenever `p' > d`.

## Dimensions the chain reaches

`p' > d` is equivalent to `p > d/2`, and `L²` data on a ball of finite measure is `Lᵖ` data
exactly when `p ≤ 2`, so a single Sobolev step feeds Morrey precisely when the window
`d/2 < p ≤ min 2 d` is inhabited.

* `d = 1`: Morrey applies to the first-order gradient at `p = 2 > 1`, so no bootstrap is needed.
* `d = 2`: `p = 4/3` has conjugate `4 > 2` (`exists_eLpNorm_four_le`).
* `d = 3`: `p = 2` has conjugate `6 > 3` (`exists_eLpNorm_six_le`).
* `d ≥ 4`: the window is empty, since `d/2 ≥ 2`, so one Sobolev step never reaches `p' > d`.

The bootstrap itself holds in every dimension. Only its composition with Morrey out of `L²` data
is limited, and `EllipticPdes.Embedding.memLp_of_gradClosed` lifts that limit by iterating the
step, at the price of a weak derivative per rung.

Mathlib's `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq` asks for `ContDiff ℝ 1` and compact
support, neither of which an `Lᵖ` class with weak derivatives has. Two devices bridge that.

* A smooth cutoff `η` supported in the ball turns a weak gradient on the ball into a compactly
  supported weak gradient on the whole space, with the product-rule term `v ∂ₖη`
  (`hasWeakGradOn_univ_mul_cutoff`).
* Mollification turns that into a smooth compactly supported function whose classical partials
  are the mollified weak gradient (`partialD_convolution_eq_of_hasWeakGradOn` at `Set.univ`),
  whose `Lᵖ` seminorms Young's inequality (`eLpNorm_convolution_le`) keeps bounded uniformly in
  the mollifier radius, and which converges almost everywhere to the original function, so Fatou
  (`MeasureTheory.eLpNorm_le_of_ae_tendsto`) passes the `Lᵖ'` bound to the limit.

## Main declarations

* `HasWeakGradOn.mono`: a weak gradient restricts to a subset.
* `hasWeakGradOn_univ_mul_cutoff`: the product rule against a smooth cutoff.
* `exists_eLpNorm_sobolevConj_le`: the bootstrap in general dimension and at a general exponent
  pair, with a constant independent of the function.
* `exists_eLpNorm_sobolevConj_le_of_le`: the same, fed by data at a higher exponent.
* `exists_eLpNorm_six_le` and `exists_eLpNorm_four_le`: the `d = 3` and `d = 2` specialisations.

## References

Evans, *Partial Differential Equations* (2nd ed.), §5.6.1 Thm 1.
-/

@[expose] public section

open MeasureTheory Set Metric
open scoped NNReal ENNReal Convolution Topology

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Sobolev (partialD tsupport_partialD_subset)

variable {d : ℕ}

/-! ### Restriction of a weak gradient -/

/-- **Restriction of a weak gradient to a subset.** Both integration-by-parts integrals localise to
the support of the test function, which lies in the smaller set, so the identity over the larger
set transfers verbatim. No measurability of either set is needed: each integrand vanishes off
`tsupport φ`, and `setIntegral_eq_integral_of_forall_compl_eq_zero` collapses both set integrals
to the same whole-space integral. -/
theorem HasWeakGradOn.mono {B B' : Set (EuclideanSpace ℝ (Fin d))} (hsub : B' ⊆ B)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (h : HasWeakGradOn B u g) : HasWeakGradOn B' u g := by
  intro φ hφc hφcs hφB' k
  have key := h φ hφc hφcs (hφB'.trans hsub) k
  have hdk : ∀ x ∉ B', u x * partialD k φ x = 0 := by
    intro x hx
    rw [show partialD k φ x = 0 from image_eq_zero_of_notMem_tsupport
      (fun hc => hx (hφB' (tsupport_partialD_subset k φ hc))), mul_zero]
  have hphi : ∀ x ∉ B', g k x * φ x = 0 := by
    intro x hx
    rw [show φ x = 0 from image_eq_zero_of_notMem_tsupport (fun hc => hx (hφB' hc)), mul_zero]
  have hdkB : ∀ x ∉ B, u x * partialD k φ x = 0 := fun x hx => hdk x fun hc => hx (hsub hc)
  have hphiB : ∀ x ∉ B, g k x * φ x = 0 := fun x hx => hphi x fun hc => hx (hsub hc)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hdk,
    setIntegral_eq_integral_of_forall_compl_eq_zero hphi]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hdkB,
    setIntegral_eq_integral_of_forall_compl_eq_zero hphiB] at key
  exact key

/-- **Dependence of a weak gradient on the almost-everywhere classes alone.** Replacing `u` and
`g` by functions agreeing with them almost everywhere on `B` leaves the integration-by-parts
identity untouched. This moves a statement about a restricted `Lp` class onto whichever
representative is convenient, in particular onto the extension by zero, which is shared across
every set. -/
theorem HasWeakGradOn.congr_ae {B : Set (EuclideanSpace ℝ (Fin d))}
    {u u' : EuclideanSpace ℝ (Fin d) → ℝ} {g g' : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (h : HasWeakGradOn B u g) (hu : u =ᵐ[volume.restrict B] u')
    (hg : ∀ k, g k =ᵐ[volume.restrict B] g' k) : HasWeakGradOn B u' g' := by
  intro φ hφc hφcs hφB k
  rw [← integral_congr_ae (hu.mono fun x hx => by simp only; rw [hx] :
      (fun x => u x * partialD k φ x) =ᵐ[volume.restrict B] fun x => u' x * partialD k φ x),
    ← integral_congr_ae ((hg k).mono fun x hx => by simp only; rw [hx] :
      (fun x => g k x * φ x) =ᵐ[volume.restrict B] fun x => g' k x * φ x)]
  exact h φ hφc hφcs hφB k

/-! ### Product rule against a smooth cutoff -/

/-- The product rule for the coordinate partial derivative. -/
theorem partialD_mul {η φ : EuclideanSpace ℝ (Fin d) → ℝ} (k : Fin d)
    {y : EuclideanSpace ℝ (Fin d)} (hη : DifferentiableAt ℝ η y)
    (hφ : DifferentiableAt ℝ φ y) :
    partialD k (fun x => η x * φ x) y = partialD k η y * φ y + η y * partialD k φ y := by
  have hfd : HasFDerivAt (fun x => η x * φ x)
      (η y • fderiv ℝ φ y + φ y • fderiv ℝ η y) y := hη.hasFDerivAt.mul hφ.hasFDerivAt
  rw [partialD, hfd.fderiv]
  simp only [_root_.add_apply, FunLike.coe_smul, Pi.smul_apply,
    smul_eq_mul, partialD]
  ring

/-- **Cutting a weak gradient off.** If `g` is the weak gradient of `u` on `B` and `η` is a
smooth compactly supported function with `tsupport η ⊆ B`, then the extension by zero of `η u`
has a weak gradient on the whole space, namely `η gₖ + u ∂ₖη`. Testing against `φ` reduces to
testing the hypothesis against `η φ`, which is again a test function supported in `B`, and the
product rule supplies the extra term. This is what makes the mollification argument reach a
compactly supported function without a boundary contribution from `∂B`. -/
theorem hasWeakGradOn_univ_mul_cutoff {B : Set (EuclideanSpace ℝ (Fin d))}
    (hB : MeasurableSet B) {η : EuclideanSpace ℝ (Fin d) → ℝ}
    (hηc : ContDiff ℝ (⊤ : ℕ∞) η) (hηcs : HasCompactSupport η) (hηs : tsupport η ⊆ B)
    {u : EuclideanSpace ℝ (Fin d) → ℝ} {g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (hu : IntegrableOn u B volume) (hgi : ∀ k, IntegrableOn (g k) B volume)
    (h : HasWeakGradOn B u g) :
    HasWeakGradOn Set.univ (fun x => η x * B.indicator u x)
      (fun k x => η x * B.indicator (g k) x + partialD k η x * B.indicator u x) := by
  intro φ hφc hφcs _ k
  have hηd : Differentiable ℝ η := hηc.differentiable (by simp)
  have hφd : Differentiable ℝ φ := hφc.differentiable (by simp)
  -- The multipliers are continuous with compact support, hence bounded.
  have hηpc : Continuous (partialD k η) :=
    (hηc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hηpcs : HasCompactSupport (partialD k η) :=
    hηcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))
  have hφpc : Continuous (partialD k φ) :=
    (hφc.continuous_fderiv (by simp)).clm_apply continuous_const
  obtain ⟨Cη, hCη⟩ := hηcs.exists_bound_of_continuous hηc.continuous
  obtain ⟨Cηp, hCηp⟩ := hηpcs.exists_bound_of_continuous hηpc
  obtain ⟨Cφ, hCφ⟩ := hφcs.exists_bound_of_continuous hφc.continuous
  obtain ⟨Cφp, hCφp⟩ :=
    (hφcs.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k (1 : ℝ))).exists_bound_of_continuous hφpc
  -- The hypothesis applied to the test function `η φ`.
  have hψs : tsupport (fun x => η x * φ x) ⊆ B :=
    (closure_mono (Function.support_mul_subset_left η φ)).trans hηs
  have key := h (fun x => η x * φ x) (hηc.mul hφc) hφcs.mul_left hψs k
  have hprod : ∀ x, partialD k (fun z => η z * φ z) x
      = partialD k η x * φ x + η x * partialD k φ x :=
    fun x => partialD_mul k (hηd x) (hφd x)
  -- Integrability of the four products against the bounded smooth multipliers.
  have hi1 : IntegrableOn (fun x => u x * (partialD k η x * φ x)) B volume :=
    hu.mul_bdd ((hηpc.mul hφc.continuous).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        calc ‖partialD k η x * φ x‖ = ‖partialD k η x‖ * ‖φ x‖ := norm_mul _ _
          _ ≤ Cηp * Cφ := mul_le_mul (hCηp x) (hCφ x) (norm_nonneg _)
              ((norm_nonneg _).trans (hCηp x)))
  have hi2 : IntegrableOn (fun x => u x * (η x * partialD k φ x)) B volume :=
    hu.mul_bdd ((hηc.continuous.mul hφpc).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        calc ‖η x * partialD k φ x‖ = ‖η x‖ * ‖partialD k φ x‖ := norm_mul _ _
          _ ≤ Cη * Cφp := mul_le_mul (hCη x) (hCφp x) (norm_nonneg _)
              ((norm_nonneg _).trans (hCη x)))
  have hi3 : IntegrableOn (fun x => (η x * g k x) * φ x) B volume := by
    have := (hgi k).mul_bdd ((hηc.continuous.mul hφc.continuous).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => by
        calc ‖η x * φ x‖ = ‖η x‖ * ‖φ x‖ := norm_mul _ _
          _ ≤ Cη * Cφ := mul_le_mul (hCη x) (hCφ x) (norm_nonneg _)
              ((norm_nonneg _).trans (hCη x)))
    exact this.congr (Filter.Eventually.of_forall fun x => by simp only [Pi.mul_apply]; ring)
  have hi4 : IntegrableOn (fun x => (partialD k η x * u x) * φ x) B volume :=
    hi1.congr (Filter.Eventually.of_forall fun x => by ring)
  -- Split the hypothesis by the product rule.
  have hsplit : (∫ x in B, u x * (partialD k η x * φ x))
      + ∫ x in B, u x * (η x * partialD k φ x)
      = - ∫ x in B, (η x * g k x) * φ x := by
    have hlhs : (∫ x in B, u x * (partialD k η x * φ x))
        + ∫ x in B, u x * (η x * partialD k φ x)
        = ∫ x in B, u x * partialD k (fun z => η z * φ z) x := by
      rw [← integral_add hi1 hi2]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
        simp only [hprod]; ring)
    rw [hlhs, key]
    exact congrArg Neg.neg
      (integral_congr_ae (Filter.Eventually.of_forall fun x => by ring))
  -- Collapse the two whole-space integrals of the goal onto `B`.
  have hzeroL : ∀ x ∉ B, (η x * B.indicator u x) * partialD k φ x = 0 := by
    intro x hx
    rw [Set.indicator_of_notMem hx, mul_zero, zero_mul]
  have hzeroR : ∀ x ∉ B,
      (η x * B.indicator (g k) x + partialD k η x * B.indicator u x) * φ x = 0 := by
    intro x hx
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero, mul_zero, add_zero,
      zero_mul]
  have hL : ∫ x, (η x * B.indicator u x) * partialD k φ x
      = ∫ x in B, u x * (η x * partialD k φ x) := by
    rw [(setIntegral_eq_integral_of_forall_compl_eq_zero hzeroL).symm]
    exact setIntegral_congr_fun hB fun x hx => by
      rw [Set.indicator_of_mem hx]; ring
  have hR : ∫ x, (η x * B.indicator (g k) x + partialD k η x * B.indicator u x) * φ x
      = (∫ x in B, (η x * g k x) * φ x) + ∫ x in B, (partialD k η x * u x) * φ x := by
    rw [(setIntegral_eq_integral_of_forall_compl_eq_zero hzeroR).symm, ← integral_add hi3 hi4]
    exact setIntegral_congr_fun hB fun x hx => by
      rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; ring
  have hswap : ∫ x in B, (partialD k η x * u x) * φ x
      = ∫ x in B, u x * (partialD k η x * φ x) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  rw [Measure.restrict_univ, hL, hR, hswap]
  linarith [hsplit]

/-! ### Bootstrap -/

section Bootstrap

open EllipticPdes.Regularity (exists_isTestFn_one_nhdsSet_of_isCompact)

/-- **Gagliardo-Nirenberg-Sobolev for a compactly supported weak gradient.** A compactly
supported `w` on `ℝᵈ` whose weak gradient `G` lies in `Lᵖ` lies in `Lᵖ'`, where
`1/p' = 1/p - 1/d`, bounded by the gradient alone with a constant depending only on `d` and
`p`.

Mathlib's `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq` asks for `ContDiff ℝ 1`, so a weak
gradient reaches it through a mollification, whose classical partials are the mollified weak
gradient (`partialD_convolution_eq_of_hasWeakGradOn`) and whose `Lᵖ` seminorms Young's
inequality keeps bounded uniformly in the mollifier radius. Fatou passes the bound to the
almost-everywhere limit.

No cutoff enters, so the conclusion is on the whole space and the bound has no `‖w‖_{Lᵖ}`
term. `exists_eLpNorm_sobolevConj_le` is this statement composed with a cutoff, and the cutoff
is what forces the smaller ball and the extra term. -/
theorem exists_eLpNorm_sobolevConj_le_compactSupport (hd : 0 < d)
    {p p' : ℝ≥0} (hp : 1 ≤ p) (hpp' : (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - (d : ℝ)⁻¹) :
    ∃ K : ℝ≥0, ∀ (w : EuclideanSpace ℝ (Fin d) → ℝ)
        (G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      HasCompactSupport w → Integrable w volume → MemLp w p volume →
      (∀ k, MemLp (G k) p volume) → HasWeakGradOn Set.univ w G →
      MemLp w p' volume ∧
        eLpNorm w p' volume ≤ (K : ℝ≥0∞) * ∑ k, eLpNorm (G k) p volume := by
  classical
  have hpR : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp1 : (1 : ℝ≥0∞) ≤ (p : ℝ≥0∞) := by exact_mod_cast hp
  have hpofReal : ENNReal.ofReal (p : ℝ) = (p : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
  set Kg : ℝ≥0 :=
    SNormLESNormFDerivOfEqConst ℝ (volume : Measure (EuclideanSpace ℝ (Fin d))) (p : ℝ)
    with hKgdef
  refine ⟨Kg, fun w G hwcs hwint hwL hGL hwg' => ?_⟩
  have hGL2 : ∀ k, MemLp (G k) (ENNReal.ofReal (p : ℝ)) volume := by
    intro k; rw [hpofReal]; exact hGL k
  set L := ContinuousLinearMap.lsmul ℝ ℝ (E := ℝ) with hLdef
  have hLflip : L.flip = L := by
    refine ContinuousLinearMap.ext fun a => ContinuousLinearMap.ext fun b => ?_
    simp only [hLdef, ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply,
      smul_eq_mul]
    exact mul_comm b a
  let φb : ℕ → ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) := fun n =>
    { rIn := 1 / (n + 1 : ℝ) / 2
      rOut := 1 / (n + 1 : ℝ)
      rIn_pos := half_pos (by positivity)
      rIn_lt_rOut := half_lt_self (by positivity) }
  have hrOut : ∀ n : ℕ, (φb n).rOut = 1 / (n + 1 : ℝ) := fun _ => rfl
  have hrIn : ∀ n : ℕ, (φb n).rIn = 1 / (n + 1 : ℝ) / 2 := fun _ => rfl
  have hφrOut : Filter.Tendsto (fun n => (φb n).rOut) Filter.atTop (𝓝 0) := by
    simp only [hrOut]; exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hφratio : ∀ᶠ n in Filter.atTop, (φb n).rOut ≤ 2 * (φb n).rIn :=
    Filter.Eventually.of_forall fun n => le_of_eq (by rw [hrOut, hrIn]; ring)
  set W : ℕ → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun n => w ⋆[L, volume] (φb n).normed volume with hWdef
  have hρ0 : ∀ n, (0 : EuclideanSpace ℝ (Fin d) → ℝ) ≤ (φb n).normed volume :=
    fun n x => (φb n).nonneg_normed x
  have hρcont : ∀ n, Continuous ((φb n).normed volume) :=
    fun n => ((φb n).contDiff_normed : ContDiff ℝ (⊤ : ℕ∞) _).continuous
  have hρm : ∀ n, AEStronglyMeasurable ((φb n).normed volume) volume :=
    fun n => (hρcont n).aestronglyMeasurable
  have hρ1 : ∀ n, ∫ y, (φb n).normed volume y ∂volume = 1 := fun n => (φb n).integral_normed
  have hwli : LocallyIntegrable w volume := hwint.locallyIntegrable
  have hWsmooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (W n) :=
    fun n => (φb n).hasCompactSupport_normed.contDiff_convolution_right (L := L) hwli
      (φb n).contDiff_normed
  have hWcs : ∀ n, HasCompactSupport (W n) :=
    fun n => HasCompactSupport.convolution (L := L) hwcs (φb n).hasCompactSupport_normed
  have hWpartialCont : ∀ n k, Continuous (partialD k (W n)) :=
    fun n k => ((hWsmooth n).continuous_fderiv (by simp)).clm_apply continuous_const
  -- The classical partials of a mollification are the mollified weak gradient.
  have hpartial : ∀ (n : ℕ) (k : Fin d),
      partialD k (W n) = (G k ⋆[L, volume] (φb n).normed volume) := by
    intro n k
    funext x
    have hbridge := partialD_convolution_eq_of_hasWeakGradOn (B := Set.univ) MeasurableSet.univ
      (u := w) (g := G) (by rwa [IntegrableOn, Measure.restrict_univ]) hwg' (φb n) k
      (x := x) (subset_univ _)
    simpa only [Set.indicator_univ, hWdef] using hbridge
  -- Gagliardo-Nirenberg-Sobolev on each mollification, with Young keeping the bound uniform.
  have hbound : ∀ n, eLpNorm (W n) p' volume ≤ (Kg : ℝ≥0∞) * ∑ k, eLpNorm (G k) p volume := by
    intro n
    have hgns : eLpNorm (W n) p' volume ≤ (Kg : ℝ≥0∞) * eLpNorm (fderiv ℝ (W n)) p volume := by
      have h := MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq (F := ℝ)
        (μ := (volume : Measure (EuclideanSpace ℝ (Fin d)))) (u := W n)
        ((hWsmooth n).of_le (by exact_mod_cast le_top)) (hWcs n) (p := p) (p' := p')
        hp (by rw [finrank_euclideanSpace_fin]; exact hd)
        (by rw [finrank_euclideanSpace_fin]; exact hpp')
      simpa [hKgdef] using h
    have hfd : eLpNorm (fderiv ℝ (W n)) p volume
        ≤ ∑ k, eLpNorm (partialD k (W n)) p volume := by
      calc eLpNorm (fderiv ℝ (W n)) p volume
          = eLpNorm (fun y => ‖fderiv ℝ (W n) y‖) p volume := (eLpNorm_norm _
              ((hWsmooth n).continuous_fderiv (by simp)).aestronglyMeasurable).symm
        _ ≤ eLpNorm (fun y => ∑ k, ‖partialD k (W n) y‖) p volume := by
            refine eLpNorm_mono
              (((hWsmooth n).continuous_fderiv (by simp)).norm.aestronglyMeasurable) fun y => ?_
            rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), Real.norm_eq_abs,
              abs_of_nonneg (Finset.sum_nonneg fun k _ => norm_nonneg _)]
            exact norm_fderiv_le_sum_partialD (W n) y
        _ ≤ ∑ k, eLpNorm (partialD k (W n)) p volume := by
            rw [show (fun y => ∑ k, ‖partialD k (W n) y‖)
                = ∑ k, (fun y => ‖partialD k (W n) y‖) from by funext y; rw [Finset.sum_apply]]
            refine (eLpNorm_sum_le hp1).trans_eq ?_
            exact Finset.sum_congr rfl fun k _ =>
              eLpNorm_norm _ (hWpartialCont n k).aestronglyMeasurable
    have hyoung : ∀ k, eLpNorm (partialD k (W n)) p volume ≤ eLpNorm (G k) p volume := by
      intro k
      rw [hpartial n k]
      have h := eLpNorm_convolution_le (p := (p : ℝ)) hpR (hρ0 n) (hρm n) (hρ1 n) (hGL2 k)
      simpa [hpofReal] using h
    exact hgns.trans (mul_le_mul' le_rfl
      (hfd.trans (Finset.sum_le_sum fun k _ => hyoung k)))
  -- The mollifications converge to `w` almost everywhere, so Fatou passes the bound to `w`.
  have hae : ∀ᵐ x ∂volume, Filter.Tendsto (fun n => W n x) Filter.atTop (𝓝 (w x)) := by
    have hflip : ∀ n : ℕ,
        ((φb n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] w) = W n := by
      intro n
      change ((φb n).normed volume ⋆[L, volume] w) = w ⋆[L, volume] (φb n).normed volume
      conv_lhs => rw [← hLflip]
      exact convolution_flip (L := L)
    have h0 := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
      (μ := volume) (g := w) hφrOut hφratio hwli
    filter_upwards [h0] with x hx
    exact hx.congr fun n => congrFun (hflip n) x
  have hwsix : eLpNorm w p' volume ≤ (Kg : ℝ≥0∞) * ∑ k, eLpNorm (G k) p volume :=
    MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto (Filter.Eventually.of_forall hbound)
      (fun n => (hWsmooth n).continuous.aestronglyMeasurable) hwL.aestronglyMeasurable hae
  refine ⟨?_, hwsix⟩
  exact lt_of_le_of_lt hwsix (ENNReal.mul_lt_top ENNReal.coe_lt_top
    (ENNReal.sum_lt_top.mpr fun k _ => (hGL k).eLpNorm_lt_top))


/-- **From `Lᵖ` to the Sobolev conjugate `Lᵖ'` (Evans, *Partial Differential Equations*
(2nd ed.), §5.6.1 Thm 1).** On a ball `Metric.ball c R` of `ℝᵈ` with `d ≥ 1`, a function `v` with
an `Lᵖ` weak gradient `g` lies in `Lᵖ'` of the smaller ball `Metric.ball c r`, where the exponents
satisfy `1/p' = 1/p - 1/d`, with a bound linear in `‖v‖_{Lᵖ} + ∑ₖ ‖gₖ‖_{Lᵖ}` and a constant
depending only on `d`, `p`, `c`, `r` and `R`.

The inequality itself is Mathlib's `MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq`, which asks
for `ContDiff ℝ 1` and compact support. Two devices transport it to a weak gradient on a ball: a
smooth cutoff supported in `Metric.ball c R` and equal to `1` on `Metric.closedBall c r`, and a
mollification, whose classical partials are the mollified weak gradient and whose `Lᵖ` seminorms
Young's inequality keeps bounded uniformly in the mollifier radius. Fatou passes the resulting
`Lᵖ'` bound to the almost-everywhere limit.

Outside the range `1 ≤ p < d`, which is the range Evans' statement takes, the hypothesis
`1/p' = 1/p - 1/d` says nothing about a Sobolev conjugate. At `p = d` it forces `p' = 0` and
the conclusion degenerates, `eLpNorm` at exponent zero being zero; above `p = d` its right
side is negative while the left is a reciprocal of a nonnegative number, so no `p'` meets it
and the statement is vacuous. -/
theorem exists_eLpNorm_sobolevConj_le (hd : 0 < d) (c : EuclideanSpace ℝ (Fin d))
    {p p' : ℝ≥0} (hp : 1 ≤ p) (hpp' : (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - (d : ℝ)⁻¹)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ K : ℝ≥0, ∀ (v : EuclideanSpace ℝ (Fin d) → ℝ)
        (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      MemLp v p (volume.restrict (Metric.ball c R)) →
      (∀ k, MemLp (g k) p (volume.restrict (Metric.ball c R))) →
      HasWeakGradOn (Metric.ball c R) v g →
      MemLp v p' (volume.restrict (Metric.ball c r)) ∧
        eLpNorm v p' (volume.restrict (Metric.ball c r))
          ≤ (K : ℝ≥0∞) * (eLpNorm v p (volume.restrict (Metric.ball c R))
              + ∑ k, eLpNorm (g k) p (volume.restrict (Metric.ball c R))) := by
  classical
  have hp1 : (1 : ℝ≥0∞) ≤ (p : ℝ≥0∞) := by exact_mod_cast hp
  set B : Set (EuclideanSpace ℝ (Fin d)) := Metric.ball c R with hBdef
  have hBm : MeasurableSet B := measurableSet_ball
  have hR : 0 < R := hr.trans hrR
  have : IsFiniteMeasure (volume.restrict B) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  -- The cutoff, equal to `1` on the inner ball and supported in the outer one.
  obtain ⟨η, hηtest, hη1, hηIcc⟩ := exists_isTestFn_one_nhdsSet_of_isCompact
    (K := Metric.closedBall c r) (U := B) (isCompact_closedBall c r) Metric.isOpen_ball
    (Metric.closedBall_subset_ball hrR)
  obtain ⟨hηc, hηcs, hηs⟩ := hηtest
  have hηone : ∀ x ∈ Metric.closedBall c r, η x = 1 := hη1.self_of_nhdsSet
  have hηnorm : ∀ x, ‖η x‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hηIcc x).1]; exact (hηIcc x).2
  -- A uniform bound on the cutoff's partial derivatives.
  have hfdc : Continuous (fun x => fderiv ℝ η x) := hηc.continuous_fderiv (by simp)
  obtain ⟨M, hM⟩ := (hηcs.fderiv ℝ).exists_bound_of_continuous hfdc
  have hM0 : (0 : ℝ) ≤ M := (norm_nonneg _).trans (hM 0)
  have hMk : ∀ (k : Fin d) (x : EuclideanSpace ℝ (Fin d)), ‖partialD k η x‖ ≤ M := by
    intro k x
    calc ‖partialD k η x‖ ≤ ‖fderiv ℝ η x‖ * ‖EuclideanSpace.single k (1 : ℝ)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ η x‖ := by simp
      _ ≤ M := hM x
  obtain ⟨Kg, hKg⟩ := exists_eLpNorm_sobolevConj_le_compactSupport hd hp hpp'
  set Mn : ℝ≥0 := max 1 (Real.toNNReal ((d : ℝ) * M)) with hMndef
  refine ⟨Kg * Mn, fun v g hv hg hwg => ?_⟩
  -- The cut-off function and its whole-space weak gradient.
  set w : EuclideanSpace ℝ (Fin d) → ℝ := fun x => η x * B.indicator v x with hwdef
  set G : Fin d → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun k x => η x * B.indicator (g k) x + partialD k η x * B.indicator v x with hGdef
  have hvint : IntegrableOn v B volume := hv.integrable hp1
  have hgint : ∀ k, IntegrableOn (g k) B volume := fun k => (hg k).integrable hp1
  have hwg' : HasWeakGradOn Set.univ w G :=
    hasWeakGradOn_univ_mul_cutoff hBm hηc hηcs hηs hvint hgint hwg
  -- `w` is compactly supported and integrable, and both `w` and `G` lie in `L²`.
  have hvB : MemLp (B.indicator v) p volume := (memLp_indicator_iff_restrict hBm).mpr hv
  have hgB : ∀ k, MemLp (B.indicator (g k)) p volume :=
    fun k => (memLp_indicator_iff_restrict hBm).mpr (hg k)
  have hwmeas : AEStronglyMeasurable w volume :=
    hηc.continuous.aestronglyMeasurable.mul hvB.aestronglyMeasurable
  have hwL2 : MemLp w p volume := by
    refine lt_of_le_of_lt (eLpNorm_mono (g := B.indicator v) hwmeas fun x => ?_)
      hvB.eLpNorm_lt_top
    rw [hwdef, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hηnorm x)
  have hwcs : HasCompactSupport w := hηcs.mul_right
  have hwint : Integrable w volume :=
    (hvint.integrable_indicator hBm).bdd_mul hηc.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall hηnorm)
  have hGmeas : ∀ k, AEStronglyMeasurable (G k) volume := fun k =>
    (hηc.continuous.aestronglyMeasurable.mul (hgB k).aestronglyMeasurable).add
      (((hηc.continuous_fderiv (by simp)).clm_apply
        continuous_const).aestronglyMeasurable.mul hvB.aestronglyMeasurable)
  have hGbound : ∀ k, eLpNorm (G k) p volume
      ≤ eLpNorm (g k) p (volume.restrict B)
        + ENNReal.ofReal M * eLpNorm v p (volume.restrict B) := by
    intro k
    have h1 : eLpNorm (fun x => η x * B.indicator (g k) x) p volume
        ≤ eLpNorm (g k) p (volume.restrict B) := by
      refine (eLpNorm_mono (g := B.indicator (g k))
        (hηc.continuous.aestronglyMeasurable.mul (hgB k).aestronglyMeasurable) fun x => ?_).trans_eq
        (eLpNorm_indicator_eq_eLpNorm_restrict hBm)
      rw [Pi.mul_apply, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hηnorm x)
    have h2 : eLpNorm (fun x => partialD k η x * B.indicator v x) p volume
        ≤ ENNReal.ofReal M * eLpNorm v p (volume.restrict B) := by
      have hstep : eLpNorm (fun x => partialD k η x * B.indicator v x) p volume
          ≤ eLpNorm (fun x => M * B.indicator v x) p volume := by
        refine eLpNorm_mono
          (((hηc.continuous_fderiv (by simp)).clm_apply
            continuous_const).aestronglyMeasurable.mul hvB.aestronglyMeasurable) fun x => ?_
        rw [norm_mul, norm_mul, Real.norm_eq_abs M, abs_of_nonneg hM0]
        exact mul_le_mul_of_nonneg_right (hMk k x) (norm_nonneg _)
      refine hstep.trans (le_of_eq ?_)
      rw [show (fun x => M * B.indicator v x) = M • (B.indicator v) from rfl,
        eLpNorm_const_smul, eLpNorm_indicator_eq_eLpNorm_restrict hBm]
      congr 1
      rw [Real.enorm_eq_ofReal hM0]
    exact (eLpNorm_add_le hp1).trans (add_le_add h1 h2)
  have hGLp : ∀ k, MemLp (G k) p volume := by
    intro k
    refine lt_of_le_of_lt (hGbound k) ?_
    exact ENNReal.add_lt_top.mpr ⟨(hg k).eLpNorm_lt_top, ENNReal.mul_lt_top
        ENNReal.ofReal_lt_top hv.eLpNorm_lt_top⟩
  -- The whole-space inequality, applied to the cut-off function.
  have hwsix : eLpNorm w p' volume ≤ (Kg : ℝ≥0∞) * ∑ k, eLpNorm (G k) p volume :=
    (hKg w G hwcs hwint hwL2 hGLp hwg').2
  -- Bound the whole-space gradient terms by the data on the outer ball.
  have hMn1 : (1 : ℝ≥0∞) ≤ (Mn : ℝ≥0∞) := by
    rw [← ENNReal.coe_one]; exact ENNReal.coe_le_coe.mpr (le_max_left _ _)
  have hMnd : (d : ℝ≥0∞) * ENNReal.ofReal M ≤ (Mn : ℝ≥0∞) := by
    have h3 : (d : ℝ≥0∞) * ENNReal.ofReal M = ENNReal.ofReal ((d : ℝ) * M) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
    rw [h3]
    exact ENNReal.coe_le_coe.mpr (le_max_right _ _)
  have hsum : ∑ k, eLpNorm (G k) p volume
      ≤ (Mn : ℝ≥0∞) * (eLpNorm v p (volume.restrict B)
          + ∑ k, eLpNorm (g k) p (volume.restrict B)) := by
    calc ∑ k, eLpNorm (G k) p volume
        ≤ ∑ _k : Fin d, (eLpNorm (g _k) p (volume.restrict B)
            + ENNReal.ofReal M * eLpNorm v p (volume.restrict B)) :=
          Finset.sum_le_sum fun k _ => hGbound k
      _ = (∑ k, eLpNorm (g k) p (volume.restrict B))
            + (d : ℝ≥0∞) * ENNReal.ofReal M * eLpNorm v p (volume.restrict B) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          ring
      _ ≤ (Mn : ℝ≥0∞) * (∑ k, eLpNorm (g k) p (volume.restrict B))
            + (Mn : ℝ≥0∞) * eLpNorm v p (volume.restrict B) := by
          exact add_le_add (le_mul_of_one_le_left' hMn1)
            (mul_le_mul' hMnd le_rfl)
      _ = (Mn : ℝ≥0∞) * (eLpNorm v p (volume.restrict B)
            + ∑ k, eLpNorm (g k) p (volume.restrict B)) := by ring
  -- On the inner ball the cutoff is `1`, so `w` and `v` agree there.
  have heq : ∀ x ∈ Metric.ball c r, w x = v x := by
    intro x hx
    rw [hwdef]
    simp only
    rw [hηone x (Metric.ball_subset_closedBall hx),
      Set.indicator_of_mem (hBdef ▸ Metric.ball_subset_ball hrR.le hx), one_mul]
  have hcongr : eLpNorm v p' (volume.restrict (Metric.ball c r))
      = eLpNorm w p' (volume.restrict (Metric.ball c r)) :=
    (eLpNorm_congr_ae ((ae_restrict_iff' measurableSet_ball).mpr
      (Filter.Eventually.of_forall heq))).symm
  have hfinal : eLpNorm v p' (volume.restrict (Metric.ball c r))
      ≤ ((Kg * Mn : ℝ≥0) : ℝ≥0∞) * (eLpNorm v p (volume.restrict B)
          + ∑ k, eLpNorm (g k) p (volume.restrict B)) := by
    rw [hcongr, ENNReal.coe_mul, mul_assoc]
    exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans
      (hwsix.trans (mul_le_mul' le_rfl hsum))
  refine ⟨?_, hfinal⟩
  refine lt_of_le_of_lt hfinal (ENNReal.mul_lt_top ENNReal.coe_lt_top ?_)
  exact ENNReal.add_lt_top.mpr ⟨hv.eLpNorm_lt_top,
    ENNReal.sum_lt_top.mpr fun k _ => (hg k).eLpNorm_lt_top⟩

/-- **Bootstrap fed by a higher exponent.** The ball has finite measure, so `Lq` data with
`p ≤ q` is `Lᵖ` data, at the price of a factor `|B|^{1/p - 1/q}` which the constant absorbs.
This is the form the dimension-two chain uses: the interior `H²` estimate delivers `L²` data,
while the exponent that reaches Morrey through `1/p' = 1/p - 1/d` is `p = 4/3`. -/
theorem exists_eLpNorm_sobolevConj_le_of_le (hd : 0 < d) (c : EuclideanSpace ℝ (Fin d))
    {p q p' : ℝ≥0} (hp : 1 ≤ p) (hpq : p ≤ q)
    (hpp' : (p' : ℝ)⁻¹ = (p : ℝ)⁻¹ - (d : ℝ)⁻¹)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ K : ℝ≥0, ∀ (v : EuclideanSpace ℝ (Fin d) → ℝ)
        (g : Fin d → EuclideanSpace ℝ (Fin d) → ℝ),
      MemLp v q (volume.restrict (Metric.ball c R)) →
      (∀ k, MemLp (g k) q (volume.restrict (Metric.ball c R))) →
      HasWeakGradOn (Metric.ball c R) v g →
      MemLp v p' (volume.restrict (Metric.ball c r)) ∧
        eLpNorm v p' (volume.restrict (Metric.ball c r))
          ≤ (K : ℝ≥0∞) * (eLpNorm v q (volume.restrict (Metric.ball c R))
              + ∑ k, eLpNorm (g k) q (volume.restrict (Metric.ball c R))) := by
  classical
  have hR : 0 < R := hr.trans hrR
  set B : Set (EuclideanSpace ℝ (Fin d)) := Metric.ball c R with hBdef
  have : IsFiniteMeasure (volume.restrict B) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have hpqE : (p : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by exact_mod_cast hpq
  obtain ⟨K₀, hK₀⟩ := exists_eLpNorm_sobolevConj_le hd c hp hpp' hr hrR
  set A : ℝ≥0∞ := (volume.restrict B) Set.univ
      ^ (1 / (p : ℝ≥0∞).toReal - 1 / (q : ℝ≥0∞).toReal) with hAdef
  have hunivne : (volume.restrict B) Set.univ ≠ 0 := by
    rw [Measure.restrict_apply_univ, hBdef]
    exact (measure_ball_pos volume c hR).ne'
  have hunivtop : (volume.restrict B) Set.univ ≠ ⊤ := by
    rw [Measure.restrict_apply_univ, hBdef]
    exact measure_ball_lt_top.ne
  have hAne : A ≠ ⊤ := ENNReal.rpow_ne_top_of_ne_zero hunivne hunivtop
  refine ⟨K₀ * A.toNNReal, fun v g hv hg hwg => ?_⟩
  obtain ⟨hmem, hbd⟩ :=
    hK₀ v g (hv.mono_exponent hpqE) (fun k => (hg k).mono_exponent hpqE) hwg
  refine ⟨hmem, ?_⟩
  have hcmp : ∀ f : EuclideanSpace ℝ (Fin d) → ℝ,
      AEStronglyMeasurable f (volume.restrict B) →
      eLpNorm f p (volume.restrict B) ≤ eLpNorm f q (volume.restrict B) * A :=
    fun f hf => eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpqE hf
  calc eLpNorm v p' (volume.restrict (Metric.ball c r))
      ≤ (K₀ : ℝ≥0∞) * (eLpNorm v p (volume.restrict B)
          + ∑ k, eLpNorm (g k) p (volume.restrict B)) := hbd
    _ ≤ (K₀ : ℝ≥0∞) * (eLpNorm v q (volume.restrict B) * A
          + ∑ k, eLpNorm (g k) q (volume.restrict B) * A) :=
        mul_le_mul' le_rfl (add_le_add (hcmp v hv.aestronglyMeasurable)
          (Finset.sum_le_sum fun k _ => hcmp (g k) (hg k).aestronglyMeasurable))
    _ = ((K₀ * A.toNNReal : ℝ≥0) : ℝ≥0∞) * (eLpNorm v q (volume.restrict B)
          + ∑ k, eLpNorm (g k) q (volume.restrict B)) := by
        rw [ENNReal.coe_mul, ENNReal.coe_toNNReal hAne, ← Finset.sum_mul, ← add_mul]
        ring

/-- **From `L²` to `L⁶` in dimension three.** The Sobolev conjugate of `2` in dimension `3` is
`2·3/(3-2) = 6`, so a function with an `L²` weak gradient on `Metric.ball c R` lies in `L⁶` of
`Metric.ball c r`. Since `6 > 3`, this single step feeds `morrey_ball`. -/
theorem exists_eLpNorm_six_le (c : EuclideanSpace ℝ (Fin 3)) {r R : ℝ} (hr : 0 < r)
    (hrR : r < R) :
    ∃ K : ℝ≥0, ∀ (v : EuclideanSpace ℝ (Fin 3) → ℝ)
        (g : Fin 3 → EuclideanSpace ℝ (Fin 3) → ℝ),
      MemLp v 2 (volume.restrict (Metric.ball c R)) →
      (∀ k, MemLp (g k) 2 (volume.restrict (Metric.ball c R))) →
      HasWeakGradOn (Metric.ball c R) v g →
      MemLp v 6 (volume.restrict (Metric.ball c r)) ∧
        eLpNorm v 6 (volume.restrict (Metric.ball c r))
          ≤ (K : ℝ≥0∞) * (eLpNorm v 2 (volume.restrict (Metric.ball c R))
              + ∑ k, eLpNorm (g k) 2 (volume.restrict (Metric.ball c R))) := by
  have h := exists_eLpNorm_sobolevConj_le (d := 3) (by norm_num) c (p := 2) (p' := 6)
    (by norm_num) (by push_cast; norm_num) hr hrR
  simpa using h

/-- **From `L²` to `L⁴` in dimension two.** At `d = 2` the Sobolev conjugate of `2` degenerates,
so the step is taken at `p = 4/3`, whose conjugate is `4`. The ball has finite measure, so the
`L²` data of the interior `H²` estimate is `L^{4/3}` data. Since `4 > 2`, the result feeds
`morrey_ball`, with Hölder exponent `1 - 2/4 = 1/2`. -/
theorem exists_eLpNorm_four_le (c : EuclideanSpace ℝ (Fin 2)) {r R : ℝ} (hr : 0 < r)
    (hrR : r < R) :
    ∃ K : ℝ≥0, ∀ (v : EuclideanSpace ℝ (Fin 2) → ℝ)
        (g : Fin 2 → EuclideanSpace ℝ (Fin 2) → ℝ),
      MemLp v 2 (volume.restrict (Metric.ball c R)) →
      (∀ k, MemLp (g k) 2 (volume.restrict (Metric.ball c R))) →
      HasWeakGradOn (Metric.ball c R) v g →
      MemLp v 4 (volume.restrict (Metric.ball c r)) ∧
        eLpNorm v 4 (volume.restrict (Metric.ball c r))
          ≤ (K : ℝ≥0∞) * (eLpNorm v 2 (volume.restrict (Metric.ball c R))
              + ∑ k, eLpNorm (g k) 2 (volume.restrict (Metric.ball c R))) := by
  have h := exists_eLpNorm_sobolevConj_le_of_le (d := 2) (by norm_num) c
    (p := 4 / 3) (q := 2) (p' := 4) (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
    (by rw [← NNReal.coe_le_coe]; push_cast; norm_num) (by push_cast; norm_num) hr hrR
  simpa using h

end Bootstrap

end EllipticPdes.Embedding
