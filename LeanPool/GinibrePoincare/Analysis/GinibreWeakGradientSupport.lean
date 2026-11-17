/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreWeakGradientSupport.lean.
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

public import LeanPool.GinibrePoincare.Analysis.RadialInteriorWeakSobolevApproximation

/-! # Locality and compact representatives of ordinary weak gradients

The actual weak gradient vanishes almost everywhere outside the topological
support of any value representative. Compact interior values therefore supply
compact interior gradient representatives automatically.
-/


@[expose] public section


open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

/-- An actual ordinary weak gradient vanishes outside the support of the value. -/
theorem ginibre_distributional_gradient_zero_off_support (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ) (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f) :
    ∀ᵐ z ∂ginibreMeasure n, z ∉ tsupport f → g z = 0 := by
  let U := {z : Configuration n | CollisionFree z} ∩ (tsupport f)ᶜ
  have hU : IsOpen U := (isOpen_collisionFree n).inter (isClosed_tsupport f).isOpen_compl
  have hf' := (ginibre_ae_eq_iff_volume n hn _ _).mp hf
  have he (k : Fin n × Fin 2) : ∀ᵐ z ∂(volume : Measure (Configuration n)),
      z ∈ U → g z k = 0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      ((hg.2.1 k).mono_set Set.inter_subset_left)
    intro θ hθ hc hs
    have ht := hg.2.2 k θ hθ hc (hs.trans Set.inter_subset_left)
    have hz : (∫ z, u z * fderiv ℝ θ z (ginibreCoordinateDirection k)) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hf'] with z hz
      rw [hz]
      by_cases hmem : z ∈ tsupport θ
      · have hnot : z ∉ tsupport f := (hs hmem).2
        simp [image_eq_zero_of_notMem_tsupport hnot]
      · rw [fderiv_of_notMem_tsupport ℝ hmem]
        simp
    simpa only [smul_eq_mul, mul_comm, hz, neg_zero] using ht
  have hall := (ae_all_iff).mpr he
  have hcf : ∀ᵐ z ∂(volume : Measure (Configuration n)), CollisionFree z := by
    rw [ae_iff]
    have heq : {z : Configuration n | ¬ CollisionFree z} = collisionSet n := by
      ext z
      simp [collisionFree_iff_not_mem_collisionSet]
    rw [heq]
    exact configurationVolume_collisionSet hn
  obtain ⟨c, hc, hm⟩ := ginibreMeasure_le_finite_smul_volume n hn
  apply (Measure.absolutelyContinuous_of_le_smul hm).ae_le
  filter_upwards [hall, hcf] with z hz hzcf
  intro hznot
  ext k
  exact hz k ⟨hzcf, hznot⟩

/-- Every compact value representative induces a compact weak-gradient
representative with support contained in the value support. -/
theorem ginibre_distributional_gradient_exists_supported_representative
    (n : ℕ) (hn : 0 < n) (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ) (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hc : HasCompactSupport f) :
    ∃ h : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2),
      (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[ginibreMeasure n] h ∧
      HasCompactSupport h ∧ tsupport h ⊆ tsupport f := by
  classical
  let h : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2) := (tsupport f).indicator g
  have hs : tsupport h ⊆ tsupport f := by
    apply closure_minimal ?_ (isClosed_tsupport f)
    intro z hz
    by_contra hnot
    exact hz (by simp [h, hnot])
  refine ⟨h, ?_, hc.of_isClosed_subset (isClosed_tsupport h) hs, hs⟩
  filter_upwards [ginibre_distributional_gradient_zero_off_support n hn u g hg f hf] with z hz
  by_cases hmem : z ∈ tsupport f
  · simp [h, hmem]
  · simp [h, hmem, hz hmem]

/-- Interior compact radial weak values belong to the original smooth radial
completion; compactness and interior support of the gradient are derived. -/
theorem radial_compact_interior_weak_mem_sobolevClosure
    (n : ℕ) (hn : 0 < n) (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ) (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hc : HasCompactSupport f) (hfs : tsupport f ⊆ {z | CollisionFree z})
    (hs : IsSymmetric f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i))) :
    (u, g) ∈ radialSobolevClosure n := by
  obtain ⟨h, hh, hhc, hhs⟩ := ginibre_distributional_gradient_exists_supported_representative
    n hn u g hg f hf hc
  exact radial_interior_weak_mem_sobolevClosure n hn u g hg f h hf hh
    hc hhc hfs (hhs.trans hfs) hs hr

/-- Sharp LSI for interior compact radial weak values, with no separate gradient-support premise. -/
theorem radial_compact_interior_weak_lsi
    (n : ℕ) (hn : 0 < n) (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ) (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hc : HasCompactSupport f) (hfs : tsupport f ⊆ {z | CollisionFree z})
    (hs : IsSymmetric f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i))) :
    Integrable (fun z => u z ^ 2 * Real.log (u z ^ 2)) (ginibreMeasure n) ∧
      ginibreSquareEntropy n u ≤ (1 / (n : ℝ)) * ‖g‖ ^ 2 :=
  radial_sobolev_lsi n hn (u, g)
    (radial_compact_interior_weak_mem_sobolevClosure n hn u g hg f hf hc hfs hs hr)

/-- Actual core approximants exist without a supplied compact gradient representative. -/
theorem radial_compact_interior_weak_exists_core_sequence
    (n : ℕ) (hn : 0 < n) (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ) (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hc : HasCompactSupport f) (hfs : tsupport f ⊆ {z | CollisionFree z})
    (hs : IsSymmetric f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i))) :
    ∃ q : ℕ → Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n),
      (∀ m, q m ∈ radialSobolevCorePairs n) ∧ Tendsto q atTop (𝓝 (u, g)) :=
  mem_closure_iff_seq_limit.mp
    (radial_compact_interior_weak_mem_sobolevClosure n hn u g hg f hf hc hfs hs hr)

end
end GinibrePoincare
