/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreArbitraryWeakPairClosure.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreArbitraryWeakPairApproximation
public import LeanPool.GinibrePoincare.Analysis.GinibreCollisionCutoffSobolevApproximation

/-!
# Ginibre Arbitrary Weak Pair Closure
-/


@[expose] public section

open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

/-- Every value truncation of a weak pair is in the closure of the smooth
collision-free compact value-gradient pairs. -/
theorem ginibreValueTruncation_mem_closure_interiorSmooth {n : ℕ} (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g) (k : ℕ) :
    ((ginibreValueTruncation_memLp n k u (Lp.memLp u)).toLp
        (fun z => sobolevValueTruncation k (u z)),
      (ginibreValueTruncation_vector_memLp n k u (Lp.aestronglyMeasurable u) g
        (Lp.memLp g)).toLp
          (fun z => deriv (sobolevValueTruncation k) (u z) • g z)) ∈
      closure (ginibreInteriorSmoothPair n) := by
  let U := (ginibreValueTruncation_memLp n k u (Lp.memLp u)).toLp
    (fun z => sobolevValueTruncation k (u z))
  let G := (ginibreValueTruncation_vector_memLp n k u (Lp.aestronglyMeasurable u) g
    (Lp.memLp g)).toLp (fun z => deriv (sobolevValueTruncation k) (u z) • g z)
  have hweak := ginibreValueTruncation_distributional n hn k u g hg
  have hspatial (j : ℕ) :
      ginibreWeakSpatialTruncation n hn U G j ∈ closure (ginibreInteriorSmoothPair n) := by
    let f (z : Configuration n) := ginibreSpatialCutoff n j z *
      sobolevValueTruncation k (u z)
    have hf : ((ginibreWeakSpatialTruncation n hn U G j).1 : Configuration n → ℝ)
        =ᵐ[ginibreMeasure n] f := by
      apply (ginibreWeakSpatialTruncation_value_ae n hn U G j).trans
      filter_upwards [(ginibreValueTruncation_memLp n k u (Lp.memLp u)).coeFn_toLp]
        with z hz
      change _ = ginibreSpatialCutoff n j z * sobolevValueTruncation k (u z)
      rw [hz]
    have hfc : HasCompactSupport f := by
      dsimp [f]
      exact (ginibreSpatialCutoff_compact n j).mul_right
    have hA : ∀ z, ‖f z‖ ≤ 2 * ((k : ℝ) + 1) := by
      intro z
      dsimp [f]
      have hχ := ginibreSpatialCutoff_mem_unit n j z
      rw [abs_mul, abs_of_nonneg hχ.1]
      exact (mul_le_of_le_one_left
        (abs_nonneg (sobolevValueTruncation k (u z))) hχ.2).trans (by
          simpa only [Real.norm_eq_abs] using sobolevValueTruncation_bounded k (u z))
    exact ginibreBoundedCompactWeakPair_mem_closure_interiorSmooth hn _ _
      (ginibreWeakSpatialTruncation_distributional n hn U G hweak j) f hf hfc
      (2 * ((k : ℝ) + 1)) (by positivity) hA
  exact isClosed_closure.mem_of_tendsto
    (ginibreWeakSpatialTruncation_tendsto n hn U G) (Eventually.of_forall hspatial)

/-- Every Ginibre distributional weak pair lies in the closure of smooth compact
pairs supported away from collisions. -/
theorem ginibreWeakPair_mem_closure_interiorSmooth {n : ℕ} (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g) :
    (u, g) ∈ closure (ginibreInteriorSmoothPair n) := by
  have htVal := ginibreValueTruncation_L2_tendsto n u
  have htGrad := ginibreValueTruncation_vector_L2_tendsto n u g
  have ht := htVal.prodMk_nhds htGrad
  apply isClosed_closure.mem_of_tendsto ht
  exact Eventually.of_forall (fun k =>
    ginibreValueTruncation_mem_closure_interiorSmooth hn u g hg k)

/-- The Reynolds average of any smooth compact scalar observable is again
smooth, compactly supported, and symmetric. -/
theorem ginibrePermutationAverage_smoothCompact {n : ℕ}
    (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    IsSmoothCompactSymmetric (ginibrePermutationAverage f) := by
  refine ⟨ginibrePermutationAverage_smooth f hf, ?_, ginibrePermutationAverage_symmetric f⟩
  classical
  let e (σ : ParticlePermutation n) : Configuration n ≃L[ℝ] Configuration n :=
    ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin n => ℂ) σ.symm
  have he (σ : ParticlePermutation n) (z : Configuration n) : e σ z = permute σ z := by
    ext i
    simp [e, ContinuousLinearEquiv.piCongrLeft, Equiv.piCongrLeft_apply, permute]
  have hcomp (σ : ParticlePermutation n) :
      HasCompactSupport (fun z => f (permute σ z)) := by
    have hc := hfc.comp_homeomorph (e σ).toHomeomorph
    convert hc using 1
    funext z
    change f (permute σ z) = f (e σ z)
    rw [← he]
  have hsum (s : Finset (ParticlePermutation n)) :
      HasCompactSupport (fun z => ∑ σ ∈ s, f (permute σ z)) := by
    classical
    induction s using Finset.induction_on with
    | empty =>
        apply hasCompactSupport_iff_eventuallyEq.mpr
        exact Eventually.of_forall (fun _ => rfl)
    | @insert σ s hσ ih =>
        have hsum_eq : (fun z => ∑ τ ∈ insert σ s, f (permute τ z)) =
            fun z => f (permute σ z) + ∑ τ ∈ s, f (permute τ z) := by
          funext z
          simp [Finset.sum_insert, hσ]
        rw [hsum_eq]
        exact (hcomp σ).add ih
  have hmul : HasCompactSupport (fun z =>
      (∑ σ : ParticlePermutation n, f (permute σ z)) *
        (Fintype.card (ParticlePermutation n) : ℝ)⁻¹) :=
    (hsum Finset.univ).mul_right
  have heq : (fun z => (Fintype.card (ParticlePermutation n) : ℝ)⁻¹ *
      (∑ σ : ParticlePermutation n, f (permute σ z))) = ginibrePermutationAverage f := by
    funext z
    simp [ginibrePermutationAverage]
  rw [← heq]
  convert hmul using 1
  funext z
  ring

/-- Averaging a smooth compact weak-pair approximation yields an element of the
collision-free core closure. -/
theorem ginibreInteriorSmoothPair_average_mem_coreClosure {n : ℕ} (hn : 0 < n)
    (p : Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hp : p ∈ ginibreInteriorSmoothPair n) :
    (ginibreRealPermutationAverageL2 p.1,
      ginibreGradientPermutationAverageL2 p.2) ∈ closure (ginibreTheoremOneNineCorePairs n) := by
  obtain ⟨f, hf, hfc, hfs, hpv, hpg⟩ := hp
  let F := ginibrePermutationAverage f
  have hF : IsSmoothCompactSymmetric F := by
    simpa [F] using ginibrePermutationAverage_smoothCompact f hf hfc
  let := ginibreMeasure_isProbabilityMeasure hn
  obtain ⟨C, hC⟩ := hF.2.1.exists_bound_of_continuousOn hF.1.continuous.continuousOn
  let A := max C 0
  have hFbound : ∀ z, ‖F z‖ ≤ A := by
    intro z
    by_cases hz : z ∈ tsupport F
    · exact (hC z hz).trans (le_max_left C 0)
    · simp [F, A, image_eq_zero_of_notMem_tsupport hz]
  have hvF : MemLp F 2 (ginibreMeasure n) := by
    apply memLp_of_bounded (a := -A) (b := A) _
      hF.1.continuous.aestronglyMeasurable 2
    exact Eventually.of_forall fun z => abs_le.mp (by
      rw [← Real.norm_eq_abs]
      exact hFbound z)
  have hdF : MemLp (ginibreEuclideanGradient F) 2 (ginibreMeasure n) := by
    have hgradcont := continuous_ginibreEuclideanGradient F hF.1
    have hgradc : HasCompactSupport (ginibreEuclideanGradient F) := by
      apply hF.2.1.of_isClosed_subset (isClosed_tsupport _)
      apply closure_minimal ?_ (isClosed_tsupport F)
      intro z hz
      by_contra hzF
      have hd : fderiv ℝ F z = 0 := fderiv_of_notMem_tsupport ℝ hzF
      apply hz
      ext k
      simp [ginibreEuclideanGradient, hd]
    obtain ⟨D, hD⟩ := hgradc.exists_bound_of_continuousOn hgradcont.continuousOn
    let B := max D 0
    have hb : ∀ z, ‖ginibreEuclideanGradient F z‖ ≤ B := by
      intro z
      by_cases hz : z ∈ tsupport (ginibreEuclideanGradient F)
      · exact (hD z hz).trans (le_max_left D 0)
      · simp [B, image_eq_zero_of_notMem_tsupport hz]
    exact MemLp.of_bound hgradcont.aestronglyMeasurable B
      (Eventually.of_forall hb)
  obtain ⟨q, hq, hqconv⟩ :=
    ginibreCollisionCutoff_smoothPair_core_sequence_of_smoothCompact n hn F hF hvF hdF
  -- The averaged L² pair is exactly the value-gradient pair of `F`.
  have hpvF : (ginibreRealPermutationAverageL2 p.1 : Configuration n → ℝ)
      =ᵐ[ginibreMeasure n] F := by
    classical
  have hterm (σ : ParticlePermutation n) :
        (ginibreRealPermutationL2 σ p.1 : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
          fun z => f (permute σ z) := by
      have hcomp := (ginibre_measurePreserving_permute σ).quasiMeasurePreserving.ae_eq_comp hpv
      filter_upwards [ginibreRealPermutationL2_ae σ p.1, hcomp] with z hz hp
      rw [hz]
      exact hp
    have hsum (s : Finset (ParticlePermutation n)) :
        ((∑ σ ∈ s, ginibreRealPermutationL2 σ p.1 : Lp ℝ 2 (ginibreMeasure n)) :
          Configuration n → ℝ) =ᵐ[ginibreMeasure n]
          fun z => ∑ σ ∈ s, f (permute σ z) := by
      classical
      induction s using Finset.induction_on with
      | empty =>
          filter_upwards [] with z
          simp
      | @insert σ s hσ ih =>
          filter_upwards [Lp.coeFn_add (ginibreRealPermutationL2 σ p.1)
            (∑ τ ∈ s, ginibreRealPermutationL2 τ p.1), hterm σ, ih] with z hadd ht hs
          simp only [Finset.sum_insert hσ]
          calc
            (↑(ginibreRealPermutationL2 σ p.1 +
              ∑ τ ∈ s, ginibreRealPermutationL2 τ p.1) : Configuration n → ℝ) z =
                ((↑(ginibreRealPermutationL2 σ p.1) +
                  ↑(∑ τ ∈ s, ginibreRealPermutationL2 τ p.1)) : Configuration n → ℝ) z := hadd
            _ = f (permute σ z) + ∑ τ ∈ s, f (permute τ z) := by
              change (ginibreRealPermutationL2 σ p.1) z +
                (∑ τ ∈ s, ginibreRealPermutationL2 τ p.1) z = _
              rw [ht, hs]
    unfold ginibreRealPermutationAverageL2
    simp only [smul_apply, sum_apply]
    filter_upwards [Lp.coeFn_smul
      ((Fintype.card (ParticlePermutation n) : ℝ)⁻¹)
      (∑ σ : ParticlePermutation n, ginibreRealPermutationL2 σ p.1),
      hsum Finset.univ] with z hscale hsumz
    change (↑((Fintype.card (ParticlePermutation n) : ℝ)⁻¹ •
      ∑ σ : ParticlePermutation n, ginibreRealPermutationL2 σ p.1) :
        Configuration n → ℝ) z = F z
    rw [hscale]
    change (Fintype.card (ParticlePermutation n) : ℝ)⁻¹ *
      (↑(∑ σ : ParticlePermutation n, ginibreRealPermutationL2 σ p.1) :
        Configuration n → ℝ) z = F z
    rw [hsumz]
    simp [F, ginibrePermutationAverage]
  have hpgF : (ginibreGradientPermutationAverageL2 p.2 :
      Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
      =ᵐ[ginibreMeasure n] ginibreEuclideanGradient F := by
    classical
    have hterm (σ : ParticlePermutation n) :
        (ginibreGradientPermutationL2 σ p.2 :
          Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[ginibreMeasure n]
          fun z => ginibreEuclideanGradient (fun y => f (permute σ y)) z := by
      have hcomp := (ginibre_measurePreserving_permute σ).quasiMeasurePreserving.ae_eq_comp hpg
      filter_upwards [ginibreGradientPermutationL2_ae σ p.2, hcomp] with z hz hp
      rw [hz, ginibreEuclideanGradient_comp_permute σ f hf z]
      congr 1
      ext k
      exact congrArg (fun v : EuclideanSpace ℝ (Fin n × Fin 2) =>
        v (σ.symm k.1, k.2)) hp
    have hsum (s : Finset (ParticlePermutation n)) :
        ((∑ σ ∈ s, ginibreGradientPermutationL2 σ p.2 :
          Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n)) :
          Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[ginibreMeasure n]
          fun z => ∑ σ ∈ s, ginibreEuclideanGradient (fun y => f (permute σ y)) z := by
      classical
      induction s using Finset.induction_on with
      | empty =>
          filter_upwards [] with z
          simp
      | @insert σ s hσ ih =>
          filter_upwards [Lp.coeFn_add (ginibreGradientPermutationL2 σ p.2)
            (∑ τ ∈ s, ginibreGradientPermutationL2 τ p.2), hterm σ, ih] with z hadd ht hs
          simp only [Finset.sum_insert hσ]
          calc
            (↑(ginibreGradientPermutationL2 σ p.2 +
              ∑ τ ∈ s, ginibreGradientPermutationL2 τ p.2) :
                Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) z =
                ((↑(ginibreGradientPermutationL2 σ p.2) +
                  ↑(∑ τ ∈ s, ginibreGradientPermutationL2 τ p.2)) :
                    Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) z := hadd
            _ = _ := by
              change (ginibreGradientPermutationL2 σ p.2) z +
                (∑ τ ∈ s, ginibreGradientPermutationL2 τ p.2) z = _
              rw [ht, hs]
    unfold ginibreGradientPermutationAverageL2
    simp only [smul_apply, sum_apply]
    filter_upwards [Lp.coeFn_smul
      ((Fintype.card (ParticlePermutation n) : ℝ)⁻¹)
      (∑ σ : ParticlePermutation n, ginibreGradientPermutationL2 σ p.2),
      hsum Finset.univ] with z hscale hsumz
    rw [hscale]
    change (Fintype.card (ParticlePermutation n) : ℝ)⁻¹ •
      (↑(∑ σ : ParticlePermutation n, ginibreGradientPermutationL2 σ p.2) :
        Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) z =
      ginibreEuclideanGradient F z
    rw [hsumz]
    simpa [F] using (ginibreEuclideanGradient_permutationAverage f hf z).symm
  have heq : (ginibreRealPermutationAverageL2 p.1,
      ginibreGradientPermutationAverageL2 p.2) =
      (hvF.toLp F, hdF.toLp (ginibreEuclideanGradient F)) := by
    apply Prod.ext
    · apply Lp.ext
      exact hpvF.trans hvF.coeFn_toLp.symm
    · apply Lp.ext
      exact hpgF.trans hdF.coeFn_toLp.symm
  rw [heq]
  exact isClosed_closure.mem_of_tendsto hqconv
    (Eventually.of_forall fun m => subset_closure (hq m))

/-- Every permutation-invariant Ginibre weak pair is approximated in the full
value-gradient L² norm by actual collision-free Theorem 1.9 core pairs. -/
theorem ginibreSymmetricWeakPair_exists_core_sequence {n : ℕ} (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (hs : IsGinibreSymmetricWeakPair (u, g)) :
    ∃ q : ℕ → Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n),
      (∀ m, q m ∈ ginibreTheoremOneNineCorePairs n) ∧
        Tendsto q atTop (𝓝 (u, g)) := by
  have hinner := ginibreWeakPair_mem_closure_interiorSmooth hn u g hg
  obtain ⟨p, hp, hpt⟩ := mem_closure_iff_seq_limit.mp hinner
  let r (m : ℕ) := (ginibreRealPermutationAverageL2 (p m).1,
    ginibreGradientPermutationAverageL2 (p m).2)
  have hmem (m : ℕ) : r m ∈ closure (ginibreTheoremOneNineCorePairs n) := by
    exact ginibreInteriorSmoothPair_average_mem_coreClosure hn (p m) (hp m)
  have hlim : Tendsto r atTop (𝓝 (u, g)) := by
    exact ginibreWeakPair_average_tendsto_of_tendsto p u g hpt hs
  have hclosed : (u, g) ∈ closure (ginibreTheoremOneNineCorePairs n) :=
    isClosed_closure.mem_of_tendsto hlim (Eventually.of_forall hmem)
  exact mem_closure_iff_seq_limit.mp hclosed
end
end GinibrePoincare
