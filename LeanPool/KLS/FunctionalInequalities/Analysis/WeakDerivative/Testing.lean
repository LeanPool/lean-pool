/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.WeakDerivative.Products
public import LeanPool.KLS.FunctionalInequalities.Analysis.WeakDerivative.Approximation
public import LeanPool.KLS.FunctionalInequalities.Analysis.Cutoff.Profile

/-! # Integration against rough weak tests and integrable weak divergence

* `integral_weakDeriv_mul_eq_swap`: the curl identity of two weak derivatives of one scalar
  function persists against compact rough `H¹` tests (Letwin (2.6)).
* `compact_bounded_test_domination`: a common integrable bound for rough bounded tests.
* `integral_flux_eq_neg_forcing_of_bounded_weak_test` and
  `integral_compact_flux_eq_neg_forcing_of_global_bounded_weak_test`: a divergence identity
  `∫ Σᵢ Jᵢ ∂ᵢψ = -∫ F ψ` tested against compact `C¹` functions extends to bounded weak tests.
* `integral_eq_zero_of_integrable_weak_derivative`: a globally integrable weak directional
  derivative of an integrable function has integral zero (Letwin (2.1), Lemma 2.7).

Supporting weak calculus for Letwin arXiv:2607.24164v1 and the
local elliptic estimates of Gilbarg--Trudinger (2001). Each declaration
retains its own support, integrability and dimensional hypotheses.
-/

@[expose] public section

section
open MeasureTheory
open scoped ContDiff

section CompactWeakDerivativeTesting
section
open MeasureTheory Filter Set Metric InnerProductSpace
open scoped Convolution ContDiff ENNReal RealInnerProductSpace Topology
namespace FunctionalInequalities.Analysis

/-! Common-support smooth approximation and compact rough curl testing, used for
Letwin2607.24164v1 (2.6). These are scalar weak-calculus supports; they do not
establish the moment-law evolution, energy comparison, Theorem2.5 or compact8. -/

/-- Compact rough H1 tests preserve the curl identity of two weak derivatives
of the same scalar function. Supporting interface for Letwin2607.24164v1 (2.6). -/
theorem integral_weakDeriv_mul_eq_swap {n : ℕ}
    {f p q η a b : EuclideanSpace ℝ (Fin n) → ℝ}
    {v w : EuclideanSpace ℝ (Fin n)}
    (hp : HasWeakDerivAlong f p v) (hq : HasWeakDerivAlong f q w)
    (hp2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp p 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hq2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp q 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hηv : HasWeakDerivAlong η a v) (hηw : HasWeakDerivAlong η b w)
    (hηc : HasCompactSupport η) (hac : HasCompactSupport a) (hbc : HasCompactSupport b)
    (ha2 : MemLp a 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hb2 : MemLp b 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    (∫ x, p x * b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      ∫ x, q x * a x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  rcases exists_contDiff_compact_weak_deriv_approximation
      hηv hηw hηc hac hbc ha2 hb2 with
    ⟨S, hS, _hηS, haS, hbS, θ, hθ, hconvv, hconvw⟩


  -- Check the localized L2 products used in the test identities.
  have hpS : MemLp (S.indicator p) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (memLp_indicator_iff_restrict hS.measurableSet.nullMeasurableSet).2 (hp2 S hS)

  have hqS : MemLp (S.indicator q) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (memLp_indicator_iff_restrict hS.measurableSet.nullMeasurableSet).2 (hq2 S hS)

  have hθvS (m : ℕ) :
      Function.support (fun x => fderiv ℝ (θ m) x v) ⊆ S :=
    (hθ m).2.2.2.1

  have hθwS (m : ℕ) :
      Function.support (fun x => fderiv ℝ (θ m) x w) ⊆ S :=
    (hθ m).2.2.2.2.1

  have hu_v (m : ℕ) :
      MemLp (fun x => fderiv ℝ (θ m) x v) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (hθ m).2.2.2.2.2.1

  have hu_w (m : ℕ) :
      MemLp (fun x => fderiv ℝ (θ m) x w) 2
        (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (hθ m).2.2.2.2.2.2

  have hsmooth :
      ∀ chi : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ ∞ chi → HasCompactSupport chi →
          (∫ x, p x * fderiv ℝ chi x w
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
            ∫ x, q x * fderiv ℝ chi x v
              ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    intro chi hchi hchic
    have hchi2 : ContDiff ℝ (2 : WithTop ℕ∞) chi :=
      hchi.of_le (WithTop.coe_le_coe.mpr le_top)
    have hfd : ContDiff ℝ 1 (fderiv ℝ chi) :=
      hchi2.fderiv_right (by norm_num)
    have hchi_v : ContDiff ℝ 1 (fun x => fderiv ℝ chi x v) :=
      hfd.clm_apply
        (contDiff_const : ContDiff ℝ 1
          (fun _ : EuclideanSpace ℝ (Fin n) => v))
    have hchi_w : ContDiff ℝ 1 (fun x => fderiv ℝ chi x w) :=
      hfd.clm_apply
        (contDiff_const : ContDiff ℝ 1
          (fun _ : EuclideanSpace ℝ (Fin n) => w))
    have hchi_vc : HasCompactSupport (fun x => fderiv ℝ chi x v) := by
      change HasCompactSupport
        ((fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L v) ∘ fderiv ℝ chi)
      exact (hchic.fderiv ℝ).comp_left (by simp)
    have hchi_wc : HasCompactSupport (fun x => fderiv ℝ chi x w) := by
      change HasCompactSupport
        ((fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L w) ∘ fderiv ℝ chi)
      exact (hchic.fderiv ℝ).comp_left (by simp)
    have hsymm (x : EuclideanSpace ℝ (Fin n)) :
        fderiv ℝ (fun y => fderiv ℝ chi y v) x w =
          fderiv ℝ (fun y => fderiv ℝ chi y w) x v := by
      have hfdx : DifferentiableAt ℝ (fderiv ℝ chi) x :=
        (hfd.differentiable (by simp)).differentiableAt
      have hcv :
          DifferentiableAt ℝ
            (fun _ : EuclideanSpace ℝ (Fin n) => v) x :=
        (differentiable_const v : Differentiable ℝ
          (fun _ : EuclideanSpace ℝ (Fin n) => v)).differentiableAt
      have hcw :
          DifferentiableAt ℝ
            (fun _ : EuclideanSpace ℝ (Fin n) => w) x :=
        (differentiable_const w : Differentiable ℝ
          (fun _ : EuclideanSpace ℝ (Fin n) => w)).differentiableAt
      have hv := fderiv_clm_apply hfdx hcv
      have hw := fderiv_clm_apply hfdx hcw
      have hv' := congrArg
        (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L w) hv
      have hw' := congrArg
        (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L v) hw
      simp only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero, zero_add,
        ContinuousLinearMap.flip_apply] at hv' hw'
      have hs :=
        second_derivative_symmetric
          (fun y => (hchi2.differentiable (by norm_num) y).hasFDerivAt)
          hfdx.hasFDerivAt w v
      calc
        fderiv ℝ (fun y => fderiv ℝ chi y v) x w =
            ((fderiv ℝ (fderiv ℝ chi) x) w) v := hv'
        _ = ((fderiv ℝ (fderiv ℝ chi) x) v) w := hs
        _ = fderiv ℝ (fun y => fderiv ℝ chi y w) x v := hw'.symm

    -- Apply the two weak derivative identities to the smooth tests.
    have ep := hp.2.2 (fun x => fderiv ℝ chi x w) hchi_w hchi_wc
    have eq := hq.2.2 (fun x => fderiv ℝ chi x v) hchi_v hchi_vc
    have hleft :
        (∫ x, f x * fderiv ℝ (fun y => fderiv ℝ chi y w) x v
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∫ x, f x * fderiv ℝ (fun y => fderiv ℝ chi y v) x w
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x =>
        congrArg (fun z : ℝ => f x * z) (hsymm x).symm)
    linarith [ep, eq, hleft]

  have hpair (m : ℕ) :
      (∫ x, S.indicator p x * fderiv ℝ (θ m) x w
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∫ x, S.indicator q x * fderiv ℝ (θ m) x v
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    have hpind :
        (∫ x, S.indicator p x * fderiv ℝ (θ m) x w
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∫ x, p x * fderiv ℝ (θ m) x w
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        by_cases hx : x ∈ S
        · simp only [Set.indicator_of_mem hx]
        · have hd : fderiv ℝ (θ m) x w = 0 := by
            by_contra hd
            exact hx (hθwS m hd)
          simp only [Set.indicator_of_notMem hx, hd, mul_zero])
    have hqind :
        (∫ x, S.indicator q x * fderiv ℝ (θ m) x v
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∫ x, q x * fderiv ℝ (θ m) x v
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        by_cases hx : x ∈ S
        · simp only [Set.indicator_of_mem hx]
        · have hd : fderiv ℝ (θ m) x v = 0 := by
            by_contra hd
            exact hx (hθvS m hd)
          simp only [Set.indicator_of_notMem hx, hd, mul_zero])
    calc
      (∫ x, S.indicator p x * fderiv ℝ (θ m) x w
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          ∫ x, p x * fderiv ℝ (θ m) x w
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := hpind
      _ = ∫ x, q x * fderiv ℝ (θ m) x v
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) :=
        hsmooth (θ m) (hθ m).1 (hθ m).2.1
      _ = ∫ x, S.indicator q x * fderiv ℝ (θ m) x v
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := hqind.symm


  -- Pass to the mollification limits and remove the localization factors.
  have ht_p :
      Tendsto
          (fun m => ∫ x, S.indicator p x * fderiv ℝ (θ m) x w
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
        atTop
        (𝓝 (∫ x, S.indicator p x * b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) :=
    FunctionalInequalities.L2.tendsto_integral_mul_of_eLpNorm_sub
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (a := S.indicator p) (b := b)
      (u := fun m x => fderiv ℝ (θ m) x w)
      hpS hb2 hu_w hconvw

  have ht_q :
      Tendsto
          (fun m => ∫ x, S.indicator q x * fderiv ℝ (θ m) x v
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
        atTop
        (𝓝 (∫ x, S.indicator q x * a x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) :=
    FunctionalInequalities.L2.tendsto_integral_mul_of_eLpNorm_sub
      (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
      (a := S.indicator q) (b := a)
      (u := fun m x => fderiv ℝ (θ m) x v)
      hqS ha2 hu_v hconvv

  have hseq :
      (fun m => ∫ x, S.indicator p x * fderiv ℝ (θ m) x w
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        (fun m => ∫ x, S.indicator q x * fderiv ℝ (θ m) x v
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    funext m
    exact hpair m

  have ht_q' :
      Tendsto
          (fun m => ∫ x, S.indicator p x * fderiv ℝ (θ m) x w
            ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
        atTop
        (𝓝 (∫ x, S.indicator q x * a x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) := by
    rw [hseq]
    exact ht_q

  have hind :
      (∫ x, S.indicator p x * b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∫ x, S.indicator q x * a x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    tendsto_nhds_unique ht_p ht_q'

  have hremove_b :
      (∫ x, S.indicator p x * b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∫ x, p x * b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      by_cases hx : x ∈ S
      · simp only [Set.indicator_of_mem hx]
      · have hbx : b x = 0 := by
          by_contra hbx
          exact hx (hbS hbx)
        simp only [Set.indicator_of_notMem hx, hbx, mul_zero])

  have hremove_a :
      (∫ x, S.indicator q x * a x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∫ x, q x * a x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      by_cases hx : x ∈ S
      · simp only [Set.indicator_of_mem hx]
      · have hax : a x = 0 := by
          by_contra hax
          exact hx (haS hax)
        simp only [Set.indicator_of_notMem hx, hax, mul_zero])

  calc
    (∫ x, p x * b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
        ∫ x, S.indicator p x * b x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := hremove_b.symm
    _ = ∫ x, S.indicator q x * a x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := hind
    _ = ∫ x, q x * a x
          ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := hremove_a

end FunctionalInequalities.Analysis
end
end CompactWeakDerivativeTesting

section BoundedWeakDerivativeTesting
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace FunctionalInequalities.Analysis

/-! Bounded weak-test extension of compact-test divergence identities. -/

/-- A compact-local L1 density admits a common integrable bound for rough bounded tests. -/
theorem compact_bounded_test_domination {n : ℕ}
    {F η : EuclideanSpace ℝ (Fin n) → ℝ} {S : Set (EuclideanSpace ℝ (Fin n))}
    {C : ℝ} (hF : LocallyIntegrable F (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hS : IsCompact S)
    (hη : AEStronglyMeasurable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hsupp : Function.support η ⊆ S) (hbound : ∀ x, ‖η x‖ ≤ C) :
    Integrable (S.indicator fun x => C * ‖F x‖)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∀ x, ‖F x * η x‖ ≤ (S.indicator fun y => C * ‖F y‖) x) ∧
      Integrable (fun x => F x * η x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  have hb : Integrable (S.indicator fun x => C * ‖F x‖)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (integrable_indicator_iff hS.measurableSet).2
      ((hF.integrableOn_isCompact hS).norm.const_mul C)
  have hprod (x : EuclideanSpace ℝ (Fin n)) :
      ‖F x * η x‖ ≤ (S.indicator fun y => C * ‖F y‖) x := by
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, norm_mul]
      calc
        ‖F x‖ * ‖η x‖ ≤ ‖F x‖ * C :=
          mul_le_mul_of_nonneg_left (hbound x) (norm_nonneg _)
        _ = C * ‖F x‖ := mul_comm _ _
    · have hzero : η x = 0 := by
        by_contra hne
        exact hx (hsupp hne)
      rw [Set.indicator_of_notMem hx, hzero, mul_zero, norm_zero]
  exact ⟨hb, hprod, hb.mono' (hF.aestronglyMeasurable.mul hη)
    (Filter.Eventually.of_forall hprod)⟩

/-- Dominated convergence for local L1 forcing and common compact uniformly bounded tests. -/
private theorem tendsto_integral_mul_compact_bounded_tests {n : ℕ}
    {F η : EuclideanSpace ℝ (Fin n) → ℝ}
    {θ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    {S : Set (EuclideanSpace ℝ (Fin n))} {C : ℝ}
    (hF : LocallyIntegrable F (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hS : IsCompact S)
    (hη : AEStronglyMeasurable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hηsupp : Function.support η ⊆ S) (hηbound : ∀ x, ‖η x‖ ≤ C)
    (hθ : ∀ m, AEStronglyMeasurable (θ m)
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hθsupp : ∀ m, Function.support (θ m) ⊆ S)
    (hθbound : ∀ m x, ‖θ m x‖ ≤ C)
    (hAE : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      Tendsto (fun m => θ m x) atTop (𝓝 (η x))) :
    (∀ m, Integrable (fun x => F x * θ m x)
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
    Integrable (fun x => F x * η x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    Tendsto (fun m => ∫ x, F x * θ m x
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop
      (𝓝 (∫ x, F x * η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) := by
  have hlim := compact_bounded_test_domination hF hS hη hηsupp hηbound
  have hseq (m : ℕ) :=
    compact_bounded_test_domination hF hS (hθ m) (hθsupp m) (hθbound m)
  refine ⟨fun m => (hseq m).2.2, hlim.2.2, ?_⟩
  refine tendsto_integral_of_dominated_convergence
    (S.indicator fun x => C * ‖F x‖)
    (fun m => hF.aestronglyMeasurable.mul (hθ m)) hlim.1
    (fun m => Filter.Eventually.of_forall (hseq m).2.1) ?_
  filter_upwards [hAE] with x hx
  exact tendsto_const_nhds.mul hx



/-- Local L2 fluxes can be paired with common compact global L2 test derivatives. -/
private theorem tendsto_integral_mul_of_compact_local_l2 {n : ℕ}
    {J b : EuclideanSpace ℝ (Fin n) → ℝ}
    {v : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : IsCompact S)
    (hJ : ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      MemLp J 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict K))
    (hb : MemLp b 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hv : ∀ m, MemLp (v m) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbS : Function.support b ⊆ S) (hvS : ∀ m, Function.support (v m) ⊆ S)
    (hconv : Tendsto (fun m => eLpNorm (v m - b) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop (𝓝 0)) :
    Integrable (fun x => J x * b x) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∀ m, Integrable (fun x => J x * v m x)
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
    Tendsto (fun m => ∫ x, J x * v m x
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop
      (𝓝 (∫ x, J x * b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) := by
  have hJS : MemLp (S.indicator J) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    (memLp_indicator_iff_restrict hS.measurableSet.nullMeasurableSet).2 (hJ S hS)
  have heqb : (fun x => S.indicator J x * b x) = (fun x => J x * b x) := by
    funext x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
    · have hz : b x = 0 := by
        by_contra hne
        exact hx (hbS hne)
      rw [Set.indicator_of_notMem hx, hz, mul_zero, mul_zero]
  have heqv (m : ℕ) : (fun x => S.indicator J x * v m x) =
      (fun x => J x * v m x) := by
    funext x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
    · have hz : v m x = 0 := by
        by_contra hne
        exact hx (hvS m hne)
      rw [Set.indicator_of_notMem hx, hz, mul_zero, mul_zero]
  have hJb : Integrable (fun x => J x * b x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    rw [← heqb]
    exact hJS.integrable_mul hb
  have hJv (m : ℕ) : Integrable (fun x => J x * v m x)
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    rw [← heqv m]
    exact hJS.integrable_mul (hv m)
  refine ⟨hJb, hJv, ?_⟩
  have ht := FunctionalInequalities.L2.tendsto_integral_mul_of_eLpNorm_sub hJS hb hv hconv
  have hseq : (fun m => ∫ x, S.indicator J x * v m x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      (fun m => ∫ x, J x * v m x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
    funext m
    rw [heqv m]
  rw [hseq, heqb] at ht
  exact ht


private theorem integral_flux_eq_neg_forcing_of_test_limits {n : ℕ}
    {J a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {F η : EuclideanSpace ℝ (Fin n) → ℝ}
    {θ : ℕ → EuclideanSpace ℝ (Fin n) → ℝ}
    {v : ℕ → Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {S : Set (EuclideanSpace ℝ (Fin n))} {C : ℝ}
    (hS : IsCompact S)
    (hJ : ∀ i : Fin n, ∀ K : Set (EuclideanSpace ℝ (Fin n)), IsCompact K →
      MemLp (J i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict K))
    (hF : LocallyIntegrable F (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hη : AEStronglyMeasurable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hηsupp : Function.support η ⊆ S) (hηbound : ∀ x, ‖η x‖ ≤ C)
    (hθ : ∀ m, AEStronglyMeasurable (θ m)
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hθsupp : ∀ m, Function.support (θ m) ⊆ S)
    (hθbound : ∀ m x, ‖θ m x‖ ≤ C)
    (hAE : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))),
      Tendsto (fun m => θ m x) atTop (𝓝 (η x)))
    (ha : ∀ i : Fin n, MemLp (a i) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hasupp : ∀ i : Fin n, Function.support (a i) ⊆ S)
    (hv : ∀ m i, MemLp (v m i) 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hvsupp : ∀ m i, Function.support (v m i) ⊆ S)
    (hconv : ∀ i : Fin n, Tendsto (fun m => eLpNorm (v m i - a i) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop (𝓝 0))
    (hId : ∀ m, (∫ x, ∑ i : Fin n, J i x * v m i x
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, F x * θ m x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) :
    (∀ i : Fin n, Integrable (fun x => J i x * a i x)
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
    Integrable (fun x => F x * η x) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    (∫ x, ∑ i : Fin n, J i x * a i x
      ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, F x * η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  have hforcing := tendsto_integral_mul_compact_bounded_tests
    hF hS hη hηsupp hηbound hθ hθsupp hθbound hAE
  have hflux (i : Fin n) := tendsto_integral_mul_of_compact_local_l2
    hS (hJ i) (ha i) (fun m => hv m i) (hasupp i) (fun m => hvsupp m i) (hconv i)
  refine ⟨fun i => (hflux i).1, hforcing.2.1, ?_⟩
  have hsum := tendsto_finsetSum (Finset.univ : Finset (Fin n))
    (fun i _ => (hflux i).2.2)
  have hL : Tendsto (fun m => ∫ x, ∑ i : Fin n, J i x * v m i x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop
      (𝓝 (∫ x, ∑ i : Fin n, J i x * a i x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) := by
    have hseq (m : ℕ) := integral_finsetSum (Finset.univ : Finset (Fin n))
      (fun i _ => (hflux i).2.1 m)
    have hlim := integral_finsetSum (Finset.univ : Finset (Fin n))
      (fun i _ => (hflux i).1)
    simpa only [← hseq, ← hlim] using hsum
  have hR : Tendsto (fun m => ∫ x, ∑ i : Fin n, J i x * v m i x
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) atTop
      (𝓝 (-(∫ x, F x * η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))))) := by
    simpa only [hId] using hforcing.2.2.neg
  exact tendsto_nhds_unique hL hR


/--
Bounded weak-test extension of a compact-test divergence identity: a compact-local L2 flux `J` and a
locally integrable forcing `F` satisfying `∫ Σᵢ Jᵢ ∂ᵢψ = -∫ F ψ` for every compactly supported C1
`ψ`
satisfy it for a bounded compactly supported locally integrable `η` whose coordinate weak
derivatives are
compactly supported and globally L2, with both sides integrable. Every finite dimension, zero
included. -/
theorem integral_flux_eq_neg_forcing_of_bounded_weak_test {n : ℕ}
    {J a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {F η : EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ}
    (hJ :
      ∀ i : Fin n,
        ∀ S : Set (EuclideanSpace ℝ (Fin n)),
          IsCompact S →
            MemLp (J i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hF : LocallyIntegrable F (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hId :
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ →
          HasCompactSupport ψ →
            (∫ x,
                ∑ i : Fin n,
                  J i x *
                    fderiv ℝ ψ x
                      (EuclideanSpace.basisFun (Fin n) ℝ
                        i) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
              -(∫ x, F x * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))))
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C) (hηc : HasCompactSupport η)
    (hweak : ∀ i : Fin n, HasWeakDerivAlong η (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (hac : ∀ i : Fin n, HasCompactSupport (a i))
    (ha2 : ∀ i : Fin n, MemLp (a i) 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    (∀ i : Fin n,
        Integrable (fun x => J i x * a i x) (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
      Integrable (fun x => F x * η x) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∫ x, ∑ i : Fin n, J i x * a i x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          -(∫ x, F x * η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  obtain ⟨S, hS, hηS, haS, θ, hθ, hconv, hAE⟩ :=
    exists_contDiff_compact_bounded_all_weak_deriv_approximation hη hbound hηc hweak hac ha2
  have hC : 0 ≤ C := (norm_nonneg (η 0)).trans (hbound 0)
  have hη3 (x : EuclideanSpace ℝ (Fin n)) : ‖η x‖ ≤ 3 * C := (hbound x).trans (by linarith)
  exact
    integral_flux_eq_neg_forcing_of_test_limits hS hJ hF hη.aestronglyMeasurable hηS hη3
      (fun m => (hθ m).1.continuous.aestronglyMeasurable) (fun m => (hθ m).2.2.1)
      (fun m => (hθ m).2.2.2.1) hAE ha2 haS (fun m i => ((hθ m).2.2.2.2 i).2)
      (fun m i => ((hθ m).2.2.2.2 i).1) hconv
      (fun m => hId (θ m) ((hθ m).1.of_le (WithTop.coe_le_coe.mpr le_top)) (hθ m).2.1)

end FunctionalInequalities.Analysis
end BoundedWeakDerivativeTesting

section CompactFluxGlobalBoundedWeakTest

open MeasureTheory Filter Set Metric
open scoped ContDiff Topology RealInnerProductSpace

namespace FunctionalInequalities.Analysis

/--
Integration by parts of a compactly supported compact-local L2 flux `J` with locally integrable
forcing `F`
(tested identity against compact C1 tests) against a globally bounded locally integrable weak
function `η` whose
coordinate weak derivatives are L2 on compact sets: both pairings are integrable and `∫ ∑ Jᵢ aᵢ = -∫
F η`. -/
theorem integral_compact_flux_eq_neg_forcing_of_global_bounded_weak_test {n : ℕ}
    {J a : Fin n → EuclideanSpace ℝ (Fin n) → ℝ} {F η : EuclideanSpace ℝ (Fin n) → ℝ} {C : ℝ}
    (hJ :
      ∀ i : Fin n,
        ∀ S : Set (EuclideanSpace ℝ (Fin n)),
          IsCompact S →
            MemLp (J i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hF : LocallyIntegrable F (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hJc : ∀ i : Fin n, HasCompactSupport (J i)) (hFc : HasCompactSupport F)
    (hId :
      ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
        ContDiff ℝ 1 ψ →
          HasCompactSupport ψ →
            (∫ x,
                ∑ i : Fin n,
                  J i x *
                    fderiv ℝ ψ x
                      (EuclideanSpace.basisFun (Fin n) ℝ
                        i) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
              -(∫ x, F x * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))))
    (hη : LocallyIntegrable η (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hbound : ∀ x, ‖η x‖ ≤ C)
    (hweak : ∀ i : Fin n, HasWeakDerivAlong η (a i) (EuclideanSpace.basisFun (Fin n) ℝ i))
    (ha2 :
      ∀ i : Fin n,
        ∀ S : Set (EuclideanSpace ℝ (Fin n)),
          IsCompact S →
            MemLp (a i) 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    (∀ i : Fin n,
        Integrable (fun x => J i x * a i x) (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
      Integrable (fun x => F x * η x) (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
        (∫ x, ∑ i : Fin n, J i x * a i x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
          -(∫ x, F x * η x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by
  classical
  let S := tsupport F ∪ ⋃ i : Fin n, tsupport (J i)
  have hS : IsCompact S := hFc.union (isCompact_iUnion hJc)
  obtain ⟨R, hR, hRS⟩ := hS.isBounded.subset_ball_lt 0 (0 : EuclideanSpace ℝ (Fin n))
  let χ : ContDiffBump (0 : EuclideanSpace ℝ (Fin n)) := ⟨R, R + 1, hR, lt_add_one R⟩
  have hχ1 (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ S) : χ x = 1 :=
    χ.one_of_mem_closedBall (ball_subset_closedBall (hRS hx))
  have hχd (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ S) (i : Fin n) :
    fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x (EuclideanSpace.basisFun (Fin n) ℝ i) = 0 := by
    have he := (χ.eventuallyEq_one_of_mem_ball (hRS hx)).fderiv_eq (𝕜 := ℝ)
    simpa using
      congrArg
        (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L (EuclideanSpace.basisFun (Fin n) ℝ i)) he
  let b := fun i x =>
    χ x * a i x +
      fderiv ℝ (χ : EuclideanSpace ℝ (Fin n) → ℝ) x (EuclideanSpace.basisFun (Fin n) ℝ i) * η x
  have htop : MemLp η (⊤ : ENNReal) (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
    memLp_top_of_bound hη.aestronglyMeasurable C (Filter.Eventually.of_forall hbound)
  have hdata (i : Fin n) :=
    HasWeakDerivAlong.compact_mul_data (hweak i) (ha2 i) (fun T _ => htop.restrict T)
      (χ.contDiff.of_le (WithTop.coe_le_coe.mpr le_top)) χ.hasCompactSupport
  have hηχ :
    LocallyIntegrable (fun x => χ x * η x) (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
    simpa only [mul_comm] using hη.continuous_mul χ.continuous
  have hbχ (x : EuclideanSpace ℝ (Fin n)) : ‖χ x * η x‖ ≤ C := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg χ.nonneg]
    exact
      (mul_le_mul_of_nonneg_right χ.le_one (norm_nonneg _)).trans
        (by simpa only [one_mul] using hbound x)
  obtain ⟨hprod, hforce, hEq⟩ :=
    integral_flux_eq_neg_forcing_of_bounded_weak_test hJ hF hId hηχ hbχ
      χ.hasCompactSupport.mul_right (fun i => (hdata i).1) (fun i => (hdata i).2.2.1)
      (fun i => (hdata i).2.2.2)
  have hJeq (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) : J i x * b i x = J i x * a i x := by
    by_cases hx : J i x = 0
    · simp only [hx, zero_mul]
    · have hxS : x ∈ S := Or.inr (Set.mem_iUnion.mpr ⟨i, subset_tsupport (J i) hx⟩)
      dsimp only [b]
      rw [hχ1 x hxS, hχd x hxS i]
      ring
  have hFeq (x : EuclideanSpace ℝ (Fin n)) : F x * (χ x * η x) = F x * η x := by
    by_cases hx : F x = 0
    · simp only [hx, zero_mul]
    · have hxS : x ∈ S := Or.inl (subset_tsupport F hx)
      rw [hχ1 x hxS, one_mul]
  refine
    ⟨fun i => (hprod i).congr (Filter.Eventually.of_forall (hJeq i)),
      hforce.congr (Filter.Eventually.of_forall hFeq), ?_⟩
  calc
    _ = ∫ x, ∑ i : Fin n, J i x * b i x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => Finset.sum_congr rfl fun i _ => (hJeq i x).symm
    _ = -(∫ x, F x * (χ x * η x) ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := hEq
    _ = _ := congrArg Neg.neg (integral_congr_ae (Filter.Eventually.of_forall hFeq))

end FunctionalInequalities.Analysis

end CompactFluxGlobalBoundedWeakTest

section IntegrableWeakDivergence

open MeasureTheory Filter
open scoped ContDiff Topology
open FunctionalInequalities.Energy.Euclidean.LipschitzApproximation

namespace FunctionalInequalities.Analysis

/-- The integral of a globally integrable weak directional derivative is zero.
This is the cutoff lemma used for Letwin arXiv:2607.24164v1 (2.1)/Lemma2.7. -/
theorem integral_eq_zero_of_integrable_weak_derivative {n : ℕ}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ} {v : EuclideanSpace ℝ (Fin n)}
    (hweak : HasWeakDerivAlong f g v)
    (hf : Integrable f volume) (hg : Integrable g volume) :
    (∫ x, g x ∂volume) = 0 := by
  let E := EuclideanSpace ℝ (Fin n)
  have hscaledNorm (R : ℝ) (x : E) : ‖scaled R x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (scaled_nonneg R x)]
    exact scaled_le_one R x
  have hevent (x : E) : ∀ᶠ k : ℕ in atTop, ‖x‖ < (k : ℝ) + 1 := by
    obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
    apply Filter.eventually_atTop.mpr
    refine ⟨N, fun k hk => ?_⟩
    exact lt_of_le_of_lt (hN.trans (Nat.cast_le.mpr hk)) (lt_add_one _)
  have hcutLim :
      Tendsto
        (fun k : ℕ => ∫ x, scaled ((k : ℝ) + 1) x * g x ∂volume)
        atTop (𝓝 (∫ x, g x ∂volume)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖g x‖)
      (fun k =>
        ((continuous_scaled ((k : ℝ) + 1)).aestronglyMeasurable.mul
          hg.aestronglyMeasurable))
      hg.norm
    · intro k
      filter_upwards [] with x
      change ‖scaled ((k : ℝ) + 1) x * g x‖ ≤ ‖g x‖
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hscaledNorm _ x)
    · filter_upwards [] with x
      have heq :
          (fun k : ℕ => scaled ((k : ℝ) + 1) x * g x) =ᶠ[atTop] fun _ => g x := by
        filter_upwards [hevent x] with k hk
        rw [scaled_eq_one (by positivity) hk.le, one_mul]
      exact tendsto_const_nhds.congr' heq.symm
  obtain ⟨M, hM0, hM⟩ := exists_bound_fderiv_bump (E := E)
  have hcof (k : ℕ) (x : E) :
      ‖fderiv ℝ (scaled ((k : ℝ) + 1)) x v‖ ≤ M * ‖v‖ := by
    have hR : 0 < (k : ℝ) + 1 := by positivity
    have hi : ((k : ℝ) + 1)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by
        have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith)
    have hd : ‖fderiv ℝ (scaled ((k : ℝ) + 1)) x‖ ≤ M :=
      (norm_fderiv_scaled_le hR hM x).trans
        (mul_le_of_le_one_left hM0 hi)
    exact ((fderiv ℝ (scaled ((k : ℝ) + 1)) x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hd (norm_nonneg v))
  have hderivLim :
      Tendsto
        (fun k : ℕ =>
          ∫ x, fderiv ℝ (scaled ((k : ℝ) + 1)) x v * f x ∂volume)
        atTop (𝓝 0) := by
    have ht :
        Tendsto
          (fun k : ℕ =>
            ∫ x, fderiv ℝ (scaled ((k : ℝ) + 1)) x v * f x ∂volume)
          atTop
          (𝓝 (∫ _x : E, (0 : ℝ) ∂volume)) := by
      apply tendsto_integral_of_dominated_convergence
        (fun x => (M * ‖v‖) * ‖f x‖)
        (fun k =>
          (((contDiff_scaled ((k : ℝ) + 1)).continuous_fderiv (by simp)).clm_apply
            continuous_const).aestronglyMeasurable.mul hf.aestronglyMeasurable)
        (hf.norm.const_mul (M * ‖v‖))
      · intro k
        filter_upwards [] with x
        change ‖fderiv ℝ (scaled ((k : ℝ) + 1)) x v * f x‖ ≤
          M * ‖v‖ * ‖f x‖
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hcof k x) (norm_nonneg _)
      · filter_upwards [] with x
        have heq :
            (fun k : ℕ =>
              fderiv ℝ (scaled ((k : ℝ) + 1)) x v * f x) =ᶠ[atTop] fun _ => (0 : ℝ) := by
          filter_upwards [hevent x] with k hk
          rw [fderiv_scaled_eq_zero (by positivity) hk]
          simp only [zero_apply, zero_mul]
        exact tendsto_const_nhds.congr' heq.symm
    simpa only [integral_zero] using ht
  have hidentity (k : ℕ) :
      (∫ x, scaled ((k : ℝ) + 1) x * g x ∂volume) =
        -(∫ x, fderiv ℝ (scaled ((k : ℝ) + 1)) x v * f x ∂volume) := by
    let R : ℝ := (k : ℝ) + 1
    have hR : 0 < R := by
      dsimp only [R]
      positivity
    have hχ : ContDiff ℝ 1 (scaled (E := E) R) :=
      (contDiff_scaled R).of_le (by simp)
    have hw := hweak.2.2 (scaled (E := E) R) hχ (hasCompactSupport_scaled hR)
    have hfd :
        (∫ x, f x * fderiv ℝ (scaled (E := E) R) x v ∂volume) =
          ∫ x, fderiv ℝ (scaled (E := E) R) x v * f x ∂volume := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by ring
    have hgc :
        (∫ x, g x * scaled (E := E) R x ∂volume) =
          ∫ x, scaled (E := E) R x * g x ∂volume := by
      apply integral_congr_ae
      exact ae_of_all _ fun x => by ring
    dsimp only [R] at hfd hgc hw ⊢
    linarith
  have hzero :
      Tendsto
        (fun k : ℕ => ∫ x, scaled ((k : ℝ) + 1) x * g x ∂volume)
        atTop (𝓝 0) := by
    have hneg :
        Tendsto
          (fun k : ℕ =>
            -(∫ x, fderiv ℝ (scaled ((k : ℝ) + 1)) x v * f x ∂volume))
          atTop (𝓝 (-0)) :=
      hderivLim.neg
    simpa only [neg_zero] using
      hneg.congr' (Filter.Eventually.of_forall fun k => (hidentity k).symm)
  exact tendsto_nhds_unique hcutLim hzero

end FunctionalInequalities.Analysis

end IntegrableWeakDivergence
