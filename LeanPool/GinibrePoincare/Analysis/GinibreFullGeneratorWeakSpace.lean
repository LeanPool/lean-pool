/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreFullGeneratorWeakSpace.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreDistributionalClosure
public import LeanPool.GinibrePoincare.Analysis.GinibreWeakConstants
public import LeanPool.GinibrePoincare.Analysis.GinibreWeakPermutation

/-!
# Ginibre Full Generator Weak Space
-/


@[expose] public section

namespace GinibrePoincare
noncomputable section
open MeasureTheory Filter
open scoped Topology

/-- Real-valued L² classes for the normalized Ginibre measure. -/
abbrev GinibreFullValueL2 (n : ℕ) := Lp ℝ 2 (ginibreMeasure n)
/-- L² vector fields with one real component for each real particle-coordinate direction. -/
abbrev GinibreFullGradientL2 (n : ℕ) :=
  Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n)

/-- Actual ordinary weak derivatives are additive in the full weighted domain. -/
theorem ginibreFullGradient_add {n : ℕ} (hn : 0 < n)
    (u v : GinibreFullValueL2 n) (g h : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g)
    (hv : IsGinibreDistributionalGradient n v h) :
    IsGinibreDistributionalGradient n (u + v) (g + h) := by
  have huv := (ginibre_ae_eq_iff_volume n hn _ _).mp (Lp.coeFn_add u v)
  have hgh := (ginibre_ae_eq_iff_volume n hn _ _).mp (Lp.coeFn_add g h)
  refine ⟨ginibre_memLp_locallyIntegrable_collisionFree hn ((u + v : GinibreFullValueL2 n) :
    Configuration n → ℝ)
    (Lp.memLp (u + v)), ?_, ?_⟩
  · intro k
    let P : EuclideanSpace ℝ (Fin n × Fin 2) →L[ℝ] ℝ :=
      PiLp.proj 2 (fun _ : Fin n × Fin 2 => ℝ) k
    have hm : MemLp (fun z => (g + h : GinibreFullGradientL2 n) z k) 2
        (ginibreMeasure n) := P.comp_memLp (g + h)
    exact ginibre_memLp_locallyIntegrable_collisionFree hn _ hm
  · intro k θ hθ hc hs
    have hdcont : Continuous (fun z => fderiv ℝ θ z (ginibreCoordinateDirection k)) :=
      (hθ.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdcomp := hc.fderiv_apply ℝ (ginibreCoordinateDirection k)
    have hds := (tsupport_fderiv_apply_subset ℝ (ginibreCoordinateDirection k)).trans hs
    have hig := integrable_mul_collisionFree_test _ θ (hu.2.1 k) hθ.continuous hc hs
    have hih := integrable_mul_collisionFree_test _ θ (hv.2.1 k) hθ.continuous hc hs
    have hiu := integrable_mul_collisionFree_test _ _ hu.1 hdcont hdcomp hds
    have hiv := integrable_mul_collisionFree_test _ _ hv.1 hdcont hdcomp hds
    have hl : (∫ z, (g + h : GinibreFullGradientL2 n) z k * θ z) =
        (∫ z, g z k * θ z) + (∫ z, h z k * θ z) := by
      rw [← integral_add hig hih]
      apply integral_congr_ae
      filter_upwards [hgh] with z hz
      rw [hz]
      simp [add_mul]
    have hr : (∫ z, (u + v : GinibreFullValueL2 n) z * fderiv ℝ θ z (ginibreCoordinateDirection
      k)) =
        (∫ z, u z * fderiv ℝ θ z (ginibreCoordinateDirection k)) +
          (∫ z, v z * fderiv ℝ θ z (ginibreCoordinateDirection k)) := by
      rw [← integral_add hiu hiv]
      apply integral_congr_ae
      filter_upwards [huv] with z hz
      rw [hz]
      simp [add_mul]
    rw [hl, hr, hu.2.2 k θ hθ hc hs, hv.2.2 k θ hθ hc hs]
    ring

/-- Actual ordinary weak derivatives commute with real scalar multiplication. -/
theorem ginibreFullGradient_smul {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g) (c : ℝ) :
    IsGinibreDistributionalGradient n (c • u) (c • g) := by
  have hcu := (ginibre_ae_eq_iff_volume n hn _ _).mp (Lp.coeFn_smul c u)
  have hcg := (ginibre_ae_eq_iff_volume n hn _ _).mp (Lp.coeFn_smul c g)
  refine ⟨ginibre_memLp_locallyIntegrable_collisionFree hn ((c • u : GinibreFullValueL2 n) :
    Configuration n → ℝ)
    (Lp.memLp (c • u)), ?_, ?_⟩
  · intro k
    let P : EuclideanSpace ℝ (Fin n × Fin 2) →L[ℝ] ℝ :=
      PiLp.proj 2 (fun _ : Fin n × Fin 2 => ℝ) k
    have hm : MemLp (fun z => (c • g : GinibreFullGradientL2 n) z k) 2
        (ginibreMeasure n) := P.comp_memLp (c • g)
    exact ginibre_memLp_locallyIntegrable_collisionFree hn _ hm
  · intro k θ hθ hc hs
    have hl : (∫ z, (c • g : GinibreFullGradientL2 n) z k * θ z) = c * (∫ z, g z k * θ z) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hcg] with z hz
      rw [hz]
      simp [mul_assoc]
    have hr : (∫ z, (c • u : GinibreFullValueL2 n) z * fderiv ℝ θ z (ginibreCoordinateDirection
      k)) =
        c * (∫ z, u z * fderiv ℝ θ z (ginibreCoordinateDirection k)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [hcu] with z hz
      rw [hz]
      simp [mul_assoc]
    rw [hl, hr, hu.2.2 k θ hθ hc hs]
    ring


/-- The full symmetric weak value-gradient domain, as an actual linear
subspace of the product of the two concrete weighted L² spaces. -/
def ginibreFullWeakSpace (n : ℕ) (hn : 0 < n) :
    Submodule ℝ (GinibreFullValueL2 n × GinibreFullGradientL2 n) where
  carrier := {p | IsGinibreDistributionalGradient n p.1 p.2 ∧ IsGinibreSymmetricWeakPair p}
  zero_mem' := by
    refine ⟨ginibre_weak_gradient_distributional n hn 0 0 (ginibre_zero_weak_gradient n), ?_⟩
    intro σ
    simp
  add_mem' := by
    rintro p q ⟨hp, hps⟩ ⟨hq, hqs⟩
    refine ⟨ginibreFullGradient_add hn p.1 q.1 p.2 q.2 hp hq, ?_⟩
    intro σ
    exact ⟨by simp only [Prod.fst_add, map_add, (hps σ).1, (hqs σ).1],
      by simp only [Prod.snd_add, map_add, (hps σ).2, (hqs σ).2]⟩
  smul_mem' := by
    rintro c p ⟨hp, hps⟩
    refine ⟨ginibreFullGradient_smul hn p.1 p.2 hp c, ?_⟩
    intro σ
    constructor
    · change ginibreRealPermutationL2 σ (c • p.1) = c • p.1
      rw [map_smul, (hps σ).1]
    · change ginibreGradientPermutationL2 σ (c • p.2) = c • p.2
      rw [map_smul, (hps σ).2]

/-- The full symmetric weak value-gradient space is closed in its
product norm. -/
theorem ginibreFullWeakSpace_isClosed (n : ℕ) (hn : 0 < n) :
    IsClosed (ginibreFullWeakSpace n hn : Set (GinibreFullValueL2 n × GinibreFullGradientL2 n)) :=
      by
  change IsClosed ({p | IsGinibreDistributionalGradient n p.1 p.2} ∩
    {p | IsGinibreSymmetricWeakPair p})
  apply (isClosed_ginibre_distributional_gradient_pairs n hn).inter
  simp only [IsGinibreSymmetricWeakPair, Set.ofPred_forall]
  apply isClosed_iInter
  intro σ
  exact (isClosed_eq ((ginibreRealPermutationL2 σ).continuous.comp continuous_fst)
    continuous_fst).inter (isClosed_eq
      ((ginibreGradientPermutationL2 σ).continuous.comp continuous_snd) continuous_snd)

instance ginibreFullWeakSpace_complete (n : ℕ) (hn : 0 < n) :
    CompleteSpace (ginibreFullWeakSpace n hn) :=
  (ginibreFullWeakSpace_isClosed n hn).completeSpace_coe

/-- Centering on actual Ginibre L², bundled as a continuous real-linear map. -/
def ginibreFullCenter (n : ℕ) (hn : 0 < n) : GinibreFullValueL2 n →L[ℝ] GinibreFullValueL2 n :=
  ContinuousLinearMap.id ℝ _ -
    (innerSL ℝ (ginibreRealConstantL2 n hn 1)).smulRight (ginibreRealConstantL2 n hn 1)

theorem ginibreFullCenter_apply (n : ℕ) (hn : 0 < n) (u : GinibreFullValueL2 n) :
    ginibreFullCenter n hn u = u - ginibreRealConstantL2 n hn (ginibreL2Mean n u) := by
  have hmean : inner ℝ (ginibreRealConstantL2 n hn 1) u = ginibreL2Mean n u := by
    rw [L2.inner_def]
    unfold ginibreL2Mean
    apply integral_congr_ae
    filter_upwards [ginibreRealConstantL2_ae n hn 1] with z hz
    simp [hz]
  have hc : ginibreL2Mean n u • ginibreRealConstantL2 n hn 1 =
      ginibreRealConstantL2 n hn (ginibreL2Mean n u) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_smul (ginibreL2Mean n u) (ginibreRealConstantL2 n hn 1),
      ginibreRealConstantL2_ae n hn 1,
      ginibreRealConstantL2_ae n hn (ginibreL2Mean n u)] with z hs hone hconst
    rw [hs]
    change ginibreL2Mean n u * (ginibreRealConstantL2 n hn 1) z = _
    rw [hone, hconst, mul_one]
  simp [ginibreFullCenter, hmean, hc]

/-- Centering preserves the actual symmetric ordinary weak gradient. -/
theorem ginibreFullCenter_weak_pair {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g) (hs : IsGinibreSymmetricWeakPair (u, g)) :
    IsGinibreDistributionalGradient n (ginibreFullCenter n hn u) g ∧
      IsGinibreSymmetricWeakPair (ginibreFullCenter n hn u, g) := by
  let p : ginibreFullWeakSpace n hn := ⟨(u, g), hu, hs⟩
  let c : ginibreFullWeakSpace n hn :=
    ⟨(ginibreRealConstantL2 n hn (ginibreL2Mean n u), 0),
      ginibreRealConstantL2_weak n hn _, ginibreRealConstantL2_symmetric_pair n hn _⟩
  have hp := (p-c).property
  change IsGinibreDistributionalGradient n
    (u - ginibreRealConstantL2 n hn (ginibreL2Mean n u)) (g-0) ∧
    IsGinibreSymmetricWeakPair (u - ginibreRealConstantL2 n hn (ginibreL2Mean n u), g-0) at hp
  simpa only [ginibreFullCenter_apply, sub_zero] using hp

end
end GinibrePoincare
