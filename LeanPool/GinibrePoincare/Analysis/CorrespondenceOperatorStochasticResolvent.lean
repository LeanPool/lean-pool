/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorStochasticResolvent.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorResolvent
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticTransitionResolventIdentification
/-!
# Correspondence operator stochastic resolvent

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperator_stochastic_resolvent_eq`.
-/

@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology ContDiff
namespace GinibrePoincare
noncomputable section
theorem correspondenceOperator_bounded_adjoint_identification
    (n : ℕ) (hn : 0 < n) (f : GinibreFullValueL2 n)
    (u : Configuration n → ℝ) (hu : MemLp u 2 (ginibreMeasure n))
    (A : ℝ) (hA : 0 ≤ A) (hb : ∀ z, ‖u z‖ ≤ A)
    (heq : ∀ θ : Configuration n → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ {z | CollisionFree z} →
      (∫ z, u z*θ z ∂ginibreMeasure n)-(∫ z, u z*ginibrePregenerator n θ z ∂ginibreMeasure n) =
        (∫ z, f z*θ z ∂ginibreMeasure n)) :
    hu.toLp u = correspondenceOperatorValueResolvent n hn f := by
  have hf : MemLp (f : Configuration n → ℝ) 2 (ginibreMeasure n) := Lp.memLp _
  obtain ⟨g, hgm, hlocal, hraw⟩ := ginibreTransitionAnalytic_compact_adjoint_exists_local_gradient n
      hn u f hu hf heq
  have hw : ∀ k (θ : Configuration n → ℝ), ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ {z | CollisionFree z} →
      (∫ z, g z k*θ z) = -(∫ z, u z*fderiv ℝ θ z (ginibreCoordinateDirection k)) := by
    intro k θ hθ hc hs
    calc
      _ = ∫ z, θ z*g z k := by
        apply integral_congr_ae
        exact ae_of_all volume fun z => by dsimp only; exact mul_comm _ _
      _ = -(∫ z, fderiv ℝ θ z (ginibreCoordinateDirection k)*u z) := hraw k θ hθ hc hs
      _ = _ := by
        congr 1
        apply integral_congr_ae
        exact ae_of_all volume fun z => by dsimp only; exact mul_comm _ _
  have hP : ∀ θ : Configuration n → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ {z | CollisionFree z} →
      1*(∫ z, u z*ginibrePregenerator n θ z ∂ginibreMeasure n) =
        1*(∫ z, u z*θ z ∂ginibreMeasure n)-(∫ z, f z*θ z ∂ginibreMeasure n) := by
    intro θ hθ hc hs
    have he := heq θ hθ hc hs
    linear_combination -he
  have hgrad := ginibreLocalWeak_adjoint_to_gradient_equation hn u f g hu hw hlocal 1 1 hP
  have hg : MemLp g 2 (ginibreMeasure n) :=
    ginibreLocalWeak_resolvent_global_gradient_memLp hn u f g
      (ginibre_memLp_locallyIntegrable_collisionFree hn u hu)
      (ginibreLocalWeak_compact_L2_coordinates_locallyIntegrable g hlocal) hw hu hf
      hgm.aestronglyMeasurable hlocal A hA hb 1 (1/(n : ℝ)) (by norm_num) (by positivity) hgrad
  have hdist := ginibreLocalWeak_global_distributional_pair hn u g hu hg hw
  have hcompact : ∀ p ∈ ginibreInteriorSmoothPair n,
      inner ℝ (hu.toLp u) p.1+(1/(n : ℝ))*inner ℝ (hg.toLp g) p.2=inner ℝ f p.1 := by
    intro p hp
    obtain ⟨θ, hθ, hθc, hθs, hpval, hpgrad⟩ := hp
    have huv : inner ℝ (hu.toLp u) p.1 = ∫ z, u z*θ z ∂ginibreMeasure n := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hu.coeFn_toLp, hpval] with z hz hv
      change p.1 z*(hu.toLp u) z = u z*θ z
      rw [hz, hv, mul_comm]
    have hgv : inner ℝ (hg.toLp g) p.2 =
        ∫ z, inner ℝ (g z) (ginibreEuclideanGradient θ z) ∂ginibreMeasure n := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hg.coeFn_toLp, hpgrad] with z hz hv
      change inner ℝ ((hg.toLp g) z) (p.2 z) = _
      rw [hz, hv]
    have hfv : inner ℝ f p.1 = ∫ z, f z*θ z ∂ginibreMeasure n := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hpval] with z hv
      change p.1 z*f z = f z*θ z
      rw [hv, mul_comm]
    rw [huv, hgv, hfv]
    simpa only [one_mul] using hgrad θ hθ hθc hθs
  have h := correspondenceOperatorGenerator_resolvent_unique n hn f (hu.toLp u) (hg.toLp g) hdist
      (by
    intro w h hw
    exact ginibreDistributionalWeakPair_compact_equation_complete hn (hu.toLp u) f (hg.toLp g)
      hcompact w h hw)
  exact h.1

theorem correspondenceOperator_stochastic_resolvent_eq_bounded {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (hα : 0 < (α : ℝ)) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i x t => B i t x) P) (f : GinibreFullValueL2 n)
    (A : ℝ) (hb : ∀ᵐ z ∂ginibreMeasure n, ‖f z‖ ≤ A) :
    ginibreOriginalStochasticL2Resolvent hn α P B hB hiB ((α : ℝ)/(n : ℝ)) f =
      correspondenceOperatorValueResolvent n hn f := by
  let := ginibreMeasure_isProbabilityMeasure hn
  have hc : 0<(α : ℝ)/(n : ℝ) := div_pos hα (Nat.cast_pos.mpr hn)
  obtain ⟨v, hv, hvb, hfv⟩ := ginibreBoundedLp_measurable_version hn f A hb
  obtain ⟨hrm, hrb, hRr⟩ := ginibreOriginalStochasticL2Resolvent_bounded_representative
    hn α P B hB hiB hc f v hfv hv (max A 0) hvb
  let r := fun z => ∫ t in Ioi (0 : ℝ), ((α : ℝ)/(n : ℝ))*Real.exp (-((α : ℝ)/(n : ℝ))*t)*
    ginibreStationaryContinuousTransitionMean α B P v t z
  have hr : MemLp r 2 (ginibreMeasure n) := MemLp.of_bound hrm.aestronglyMeasurable (max A 0)
      (ae_of_all _ hrb)
  have hRp : ginibreOriginalStochasticL2Resolvent hn α P B hB hiB ((α : ℝ)/(n : ℝ)) f=hr.toLp r :=
      by
    apply Lp.ext
    exact hRr.trans hr.coeFn_toLp.symm
  have heq : ∀ θ : Configuration n → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ {z | CollisionFree z} →
      (∫ z, r z*θ z ∂ginibreMeasure n)-(∫ z, r z*ginibrePregenerator n θ z ∂ginibreMeasure n)=
        ∫ z, f z*θ z ∂ginibreMeasure n := by
    intro θ hθ hcθ hs
    have htest : IsGinibreCollisionFreeCompactTest θ := ⟨hθ, hcθ, by
      intro z hz
      exact (collisionFree_iff_not_mem_collisionSet z).mp (hs hz)⟩
    have he := ginibreOriginalStochasticL2Resolvent_compact_adjoint_integral hn α hα P B hB hiB f θ
        htest
    have h1 : (∫ z, ginibreOriginalStochasticL2Resolvent hn α P B hB hiB ((α : ℝ)/(n : ℝ)) f z*θ z
        ∂ginibreMeasure n)=
        ∫ z, r z*θ z ∂ginibreMeasure n := integral_congr_ae (hRr.mono fun z hz => by dsimp only; rw
                                                                                       [hz])
    have h2 : (∫ z, ginibreOriginalStochasticL2Resolvent hn α P B hB hiB ((α : ℝ)/(n : ℝ)) f
        z*ginibrePregenerator n θ z ∂ginibreMeasure n)=
        ∫ z, r z*ginibrePregenerator n θ z ∂ginibreMeasure n := integral_congr_ae (hRr.mono fun z hz
            => by dsimp only; rw [hz])
    exact h1 ▸ h2 ▸ he
  rw [hRp]
  exact correspondenceOperator_bounded_adjoint_identification n hn f r hr (max A 0) (le_max_right _
      _) hrb heq

/-- The original stochastic normalized resolvent equals the unrestricted
ordinary weak-form resolvent on every actual real L² observable. -/
theorem correspondenceOperator_stochastic_resolvent_eq {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (hα : 0 < (α : ℝ)) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i x t => B i t x) P) (f : GinibreFullValueL2 n) :
    ginibreOriginalStochasticL2Resolvent hn α P B hB hiB ((α : ℝ)/(n : ℝ)) f =
      correspondenceOperatorValueResolvent n hn f := by
  have hc : 0<(α : ℝ)/(n : ℝ) := div_pos hα (Nat.cast_pos.mpr hn)
  let R := ginibreOriginalStochasticL2ResolventOperator hn α P B hB hiB ((α : ℝ)/(n : ℝ)) hc
  let S := correspondenceOperatorValueResolvent n hn
  let q (m : ℕ) := (ginibreValueTruncation_memLp n m f (Lp.memLp f)).toLp
    (fun z => sobolevValueTruncation m (f z))
  have ht : Tendsto q atTop (𝓝 f) := ginibreValueTruncation_L2_tendsto n f
  have hh (m : ℕ) : R (q m)=S (q m) := by
    apply correspondenceOperator_stochastic_resolvent_eq_bounded hn α hα P B hB hiB
      (q m) (2*((m : ℝ)+1))
    filter_upwards [(ginibreValueTruncation_memLp n m f (Lp.memLp f)).coeFn_toLp] with z hz
    change q m z = sobolevValueTruncation m (f z) at hz
    rw [hz]
    exact sobolevValueTruncation_bounded m (f z)
  have hRt := R.continuous.tendsto f |>.comp ht
  have hSt : Tendsto (fun m => R (q m)) atTop (𝓝 (S f)) := by
    convert S.continuous.tendsto f |>.comp ht using 1
    funext m
    exact hh m
  exact tendsto_nhds_unique hRt hSt

end
end GinibrePoincare
