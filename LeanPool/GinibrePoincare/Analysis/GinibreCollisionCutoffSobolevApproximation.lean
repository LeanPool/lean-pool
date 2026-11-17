/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreCollisionCutoffSobolevApproximation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreCollisionCutoffEnergy
public import LeanPool.GinibrePoincare.Analysis.RadialSmoothSobolevApproximation

/-! # Collision-cutoff approximation in the symmetric value-gradient norm -/


@[expose] public section


open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

/-- Smooth compact symmetric value-gradient pairs in the actual Ginibre L² product. -/
def ginibreTheoremOneNineCorePairs (n : ℕ) : Set
    (Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n)) :=
  {p | ∃ f : Configuration n → ℝ, IsTheoremOneNineCore f ∧
    (p.1 : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f ∧
    (p.2 : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[ginibreMeasure n]
      ginibreEuclideanGradient f}

/-- Every globally smooth compact symmetric observable is approximated in both
actual Ginibre L² components by collision-free Theorem 1.9 core pairs. -/
theorem ginibreCollisionCutoff_smoothPair_core_sequence
    (n : ℕ) (hn : 0 < n) (f : Configuration n → ℝ)
    (hf : IsSmoothCompactSymmetric f) (A : ℝ)
    (hA : ∀ z, ‖f z‖ ≤ A)
    (hv : MemLp f 2 (ginibreMeasure n))
    (hd : MemLp (ginibreEuclideanGradient f) 2 (ginibreMeasure n)) :
    ∃ q : ℕ → Lp ℝ 2 (ginibreMeasure n) ×
        Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n),
      (∀ m, q m ∈ ginibreTheoremOneNineCorePairs n) ∧
      Tendsto q atTop (𝓝 (hv.toLp f, hd.toLp (ginibreEuclideanGradient f))) := by
  let hgrad := ginibreEuclideanGradient f
  have hA0 : 0 ≤ A := le_trans (norm_nonneg (f default)) (hA default)
  let value (m : ℕ) := (ginibreCollisionCutoff_L2_mul_memLp n m
    (hv.toLp f) (Lp.memLp (hv.toLp f))).toLp
      (fun z => ginibreCollisionCutoff n m z • (hv.toLp f) z)
  let firstGrad (m : ℕ) := (ginibreCollisionCutoff_L2_mul_memLp n m
    (hd.toLp hgrad) (Lp.memLp (hd.toLp hgrad))).toLp
      (fun z => ginibreCollisionCutoff n m z • (hd.toLp hgrad) z)
  let cutoffGrad (m : ℕ) := (ginibreCollisionCutoff_bounded_gradient_memLp
    n hn f hf.1.continuous.aestronglyMeasurable hf.2.1 A hA m).toLp
      (fun z => f z • ginibreEuclideanGradient (ginibreCollisionCutoff n m) z)
  let q (m : ℕ) := (value m, firstGrad m + cutoffGrad m)
  refine ⟨q, ?_, ?_⟩
  · intro m
    refine ⟨fun z => ginibreCollisionCutoff n m z * f z,
      ginibreCollisionCutoff_mul_core n m f hf, ?_, ?_⟩
    · filter_upwards [(ginibreCollisionCutoff_L2_mul_memLp n m
      (hv.toLp f) (Lp.memLp (hv.toLp f))).coeFn_toLp,
        hv.coeFn_toLp] with z hq hfz
      change (ginibreCollisionCutoff_L2_mul_memLp n m
        (hv.toLp f) (Lp.memLp (hv.toLp f))).toLp
          (fun z => ginibreCollisionCutoff n m z • (hv.toLp f) z) z = _
      rw [hq, hfz]
      simp only [smul_eq_mul]
    · filter_upwards [(ginibreCollisionCutoff_L2_mul_memLp n m
          (hd.toLp hgrad) (Lp.memLp (hd.toLp hgrad))).coeFn_toLp,
        Lp.coeFn_add (firstGrad m) (cutoffGrad m),
        (ginibreCollisionCutoff_bounded_gradient_memLp n hn f
          hf.1.continuous.aestronglyMeasurable hf.2.1 A hA m).coeFn_toLp,
        hd.coeFn_toLp] with z hfirst hadd hcut hgradz
      rw [hadd]
      change firstGrad m z + cutoffGrad m z = ginibreEuclideanGradient
        (fun z => ginibreCollisionCutoff n m z * f z) z
      change firstGrad m z = _ at hfirst
      change cutoffGrad m z = _ at hcut
      rw [hfirst, hcut, hgradz]
      exact (ginibreEuclideanGradient_mul f (ginibreCollisionCutoff n m)
        hf.1 (ginibreCollisionCutoff_smooth n m) z).symm
  · have hvlim := ginibreCollisionCutoff_mul_L2_tendsto n hn (hv.toLp f)
    have hgfirst := ginibreCollisionCutoff_mul_L2_tendsto n hn (hd.toLp hgrad)
    have hgres := ginibreCollisionCutoff_bounded_gradient_L2_tendsto
      n hn f hf.1.continuous.aestronglyMeasurable hf.2.1 A hA0 hA
    have hgsum : Tendsto (fun m => firstGrad m + cutoffGrad m) atTop
        (𝓝 (hd.toLp hgrad)) := by
      simpa [firstGrad, cutoffGrad] using hgfirst.add hgres
    have hpair := hvlim.prodMk_nhds hgsum
    simpa [q, value, firstGrad, cutoffGrad] using hpair

/-- The smooth compact symmetric core pair approximation needs no separate
integrability or boundedness assumptions: compact support supplies them. -/
theorem ginibreCollisionCutoff_smoothPair_core_sequence_of_smoothCompact
    (n : ℕ) (hn : 0 < n) (f : Configuration n → ℝ)
    (hf : IsSmoothCompactSymmetric f)
    (hv : MemLp f 2 (ginibreMeasure n))
    (hd : MemLp (ginibreEuclideanGradient f) 2 (ginibreMeasure n)) :
    ∃ q : ℕ → Lp ℝ 2 (ginibreMeasure n) ×
        Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n),
      (∀ m, q m ∈ ginibreTheoremOneNineCorePairs n) ∧
      Tendsto q atTop (𝓝 (hv.toLp f, hd.toLp (ginibreEuclideanGradient f))) := by
  let := ginibreMeasure_isProbabilityMeasure hn
  obtain ⟨C, hC⟩ := hf.2.1.exists_bound_of_continuousOn hf.1.continuous.continuousOn
  let A := max C 0
  have hA : ∀ z, ‖f z‖ ≤ A := by
    intro z
    by_cases hz : z ∈ tsupport f
    · exact (hC z hz).trans (le_max_left C 0)
    · have hz0 : f z = 0 := image_eq_zero_of_notMem_tsupport hz
      simp [hz0, A]
  exact ginibreCollisionCutoff_smoothPair_core_sequence n hn f hf A hA hv hd

end
end GinibrePoincare
