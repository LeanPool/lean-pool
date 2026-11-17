/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreRadialWeakSobolevApproximation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreWeakSobolevTruncation
public import LeanPool.GinibrePoincare.Analysis.RadialSobolevSpace

/-! # Spatial approximation in the independent radial weak Sobolev space

Radiality means existence of an almost-everywhere representative depending on
the individual squared radii and invariant under particle permutations. No
smoothness or membership in the smooth-core closure enters this definition.
Every such weak-H¹ pair admits compact radial weak-H¹ approximants.
Smooth approximation is a separate, still required step.
-/


@[expose] public section


open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace GinibrePoincare
noncomputable section

def IsGinibreRadialL2Value (n : ℕ) (u : Lp ℝ 2 (ginibreMeasure n)) : Prop :=
  ∃ f : Configuration n → ℝ, IsSymmetric f ∧
    (∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i))) ∧
    (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f

def ginibreRadialWeakSobolevPairs (n : ℕ) : Set
    (Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n)) :=
  {p | IsGinibreDistributionalGradient n p.1 p.2 ∧ IsGinibreRadialL2Value n p.1}

def ginibreCompactRadialWeakSobolevPairs (n : ℕ) : Set
    (Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n)) :=
  {p | IsGinibreDistributionalGradient n p.1 p.2 ∧
    ∃ f : Configuration n → ℝ, HasCompactSupport f ∧ IsSymmetric f ∧
      (∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i))) ∧
      (p.1 : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f}

theorem ginibreCompactRadialWeakSobolevPairs_subset (n : ℕ) :
    ginibreCompactRadialWeakSobolevPairs n ⊆ ginibreRadialWeakSobolevPairs n := by
  rintro p ⟨hg, f, hc, hs, hr, he⟩
  exact ⟨hg, f, hs, hr, he⟩

/-- Actual compact truncations preserve independent symmetry and radiality. -/
theorem ginibreWeakSpatialTruncation_compact_radial (n : ℕ) (hn : 0 < n)
    (p : Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hp : p ∈ ginibreRadialWeakSobolevPairs n) (m : ℕ) :
    ginibreWeakSpatialTruncation n hn p.1 p.2 m ∈ ginibreCompactRadialWeakSobolevPairs n := by
  obtain ⟨hg, f, hs, ⟨F, hF⟩, he⟩ := hp
  refine ⟨ginibreWeakSpatialTruncation_distributional n hn p.1 p.2 hg m,
    (ginibreSpatialCutoff n m) * f, (ginibreSpatialCutoff_compact n m).mul_right, ?_, ?_, ?_⟩
  · intro σ z
    simp only [Pi.mul_apply, ginibreSpatialCutoff_symmetric n m σ z, hs σ z]
  · refine ⟨fun r => sobolevCutoff m (∑ i, r i) * F r, ?_⟩
    intro z
    simp only [Pi.mul_apply, hF, ginibreSpatialCutoff, configurationNormSq]
  · apply (ginibreWeakSpatialTruncation_value_ae n hn p.1 p.2 m).trans
    filter_upwards [he] with z hz
    simp only [hz, Pi.mul_apply]

/-- Compact weak radial pairs approximate every independently defined radial weak pair
simultaneously in value and in its actual gradient. -/
theorem ginibreRadialWeakSobolevPairs_exists_compact_sequence (n : ℕ) (hn : 0 < n)
    (p : Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hp : p ∈ ginibreRadialWeakSobolevPairs n) :
    ∃ q : ℕ → Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n),
      (∀ m, q m ∈ ginibreCompactRadialWeakSobolevPairs n) ∧ Tendsto q atTop (𝓝 p) :=
  ⟨ginibreWeakSpatialTruncation n hn p.1 p.2,
    ginibreWeakSpatialTruncation_compact_radial n hn p hp,
    by simpa only [Prod.mk.eta] using ginibreWeakSpatialTruncation_tendsto n hn p.1 p.2⟩

theorem ginibreRadialWeakSobolevPairs_subset_closure_compact (n : ℕ) (hn : 0 < n) :
    ginibreRadialWeakSobolevPairs n ⊆ closure (ginibreCompactRadialWeakSobolevPairs n) := by
  intro p hp
  obtain ⟨q, hq, ht⟩ := ginibreRadialWeakSobolevPairs_exists_compact_sequence n hn p hp
  exact isClosed_closure.mem_of_tendsto ht
    (Eventually.of_forall (fun m => subset_closure (hq m)))

/-- Spatial compactness causes no loss at the level of the independent weak graph closure. -/
theorem closure_ginibreCompactRadialWeakSobolevPairs (n : ℕ) (hn : 0 < n) :
    closure (ginibreCompactRadialWeakSobolevPairs n) =
      closure (ginibreRadialWeakSobolevPairs n) := by
  apply Set.Subset.antisymm
  · exact closure_mono (ginibreCompactRadialWeakSobolevPairs_subset n)
  · exact closure_minimal (ginibreRadialWeakSobolevPairs_subset_closure_compact n hn)
      isClosed_closure

/-- The original smooth compact radial core lies in the independently defined weak graph. -/
theorem radialSobolevCorePairs_subset_compact_weak (n : ℕ) (hn : 0 < n) :
    radialSobolevCorePairs n ⊆ ginibreCompactRadialWeakSobolevPairs n := by
  intro p hp
  have hg := radialSobolevClosure_distributional_gradient n hn p (subset_closure hp)
  obtain ⟨f, hf, he, _⟩ := hp
  exact ⟨hg, f, hf.1.2.1, hf.1.2.2, hf.2, he⟩

/-- The remaining reverse density problem is precisely the compact weak-to-smooth step.
This equivalence is a reduction; it does not assume or prove that remaining step. -/
theorem radialWeakSobolev_reverse_density_iff_compact (n : ℕ) (hn : 0 < n) :
    ginibreRadialWeakSobolevPairs n ⊆ radialSobolevClosure n ↔
      ginibreCompactRadialWeakSobolevPairs n ⊆ radialSobolevClosure n := by
  constructor
  · intro h
    exact (ginibreCompactRadialWeakSobolevPairs_subset n).trans h
  · intro h
    exact (ginibreRadialWeakSobolevPairs_subset_closure_compact n hn).trans
      (closure_minimal h isClosed_closure)

end
end GinibrePoincare
