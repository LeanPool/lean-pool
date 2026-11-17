/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreArbitraryWeakPairApproximation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreWeightedInteriorMollification
public import LeanPool.GinibrePoincare.Analysis.GinibreCollisionCutoffEnergy
public import LeanPool.GinibrePoincare.Analysis.GinibreWeakGradientSupport

/-! # Arbitrary Ginibre weak pairs: compact interior smoothing and symmetry -/


@[expose] public section


open MeasureTheory Filter
open ContinuousLinearMap
open scoped Topology ContDiff Convolution BigOperators
namespace GinibrePoincare
noncomputable section

/-- The collision-free smooth compact value-gradient pairs, before imposing
particle symmetry. -/
def ginibreInteriorSmoothPair (n : ℕ) : Set
    (Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n)) :=
  {p | ∃ f : Configuration n → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    tsupport f ⊆ {z | CollisionFree z} ∧
    (p.1 : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f ∧
    (p.2 : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[ginibreMeasure n]
      ginibreEuclideanGradient f}

/-- A compact weak pair supported in the collision-free set has smooth compact
approximants whose supports stay in that set. -/
theorem ginibreInteriorWeakPair_exists_smoothSequence {n : ℕ} (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ)
    (h : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hh : (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[ginibreMeasure n] h)
    (hfc : HasCompactSupport f) (hhc : HasCompactSupport h)
    (hfs : tsupport f ⊆ {z | CollisionFree z})
    (hhs : tsupport h ⊆ {z | CollisionFree z}) :
    ∃ q : ℕ → Lp ℝ 2 (ginibreMeasure n) ×
        Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n),
      (∀ m, q m ∈ ginibreInteriorSmoothPair n) ∧
      Tendsto q atTop (𝓝 (u, g)) := by
  obtain ⟨δ, hδ, hδK⟩ := hfc.exists_cthickening_subset_open
    (isOpen_collisionFree n) hfs
  let φ := ginibreInteriorBump n δ hδ
  obtain ⟨v, w, hregular, ht⟩ := ginibre_weighted_interior_mollification n hn u g hg
    f h hf hh hfc hhc hfs hhs φ (ginibreInteriorBump_radius_tendsto n δ hδ)
  refine ⟨fun m => (v m, w m), ?_, ht⟩
  intro m
  refine ⟨(φ m).normed volume ⋆[lsmul ℝ ℝ, volume] f,
    (hregular m).1, (hregular m).2.1, ?_, (hregular m).2.2.1, (hregular m).2.2.2⟩
  have hsupp : Function.support
      ((φ m).normed volume ⋆[lsmul ℝ ℝ, volume] f) ⊆
      Metric.thickening (φ m).rOut (tsupport f) := by
    intro z hz
    have hzsum := (support_convolution_subset
      (L := lsmul ℝ ℝ) (f := (φ m).normed volume) (g := f)) hz
    rcases hzsum with ⟨y, hy, x, hx, rfl⟩
    apply Metric.mem_thickening_iff.mpr
    refine ⟨x, subset_tsupport f hx, ?_⟩
    have hy' : y ∈ Metric.ball 0 (φ m).rOut := by
      rw [(φ m).support_normed_eq] at hy
      exact hy
    simpa [dist_eq_norm, add_sub_cancel_right] using hy'
  have hrδ : (φ m).rOut ≤ δ := by
    dsimp [φ, ginibreInteriorBump]
    have hm : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    rw [div_le_iff₀ hm]
    nlinarith [hδ]
  have htδ : Metric.thickening (φ m).rOut (tsupport f) ⊆
      Metric.cthickening δ (tsupport f) :=
    Metric.thickening_subset_cthickening_of_le hrδ _
  exact (closure_minimal (hsupp.trans htδ) (Metric.isClosed_cthickening)).trans hδK

/-- Bounded compact weak pairs are limits of smooth compact pairs supported
away from collisions, with no radiality condition. -/
theorem ginibreBoundedCompactWeakPair_mem_closure_interiorSmooth {n : ℕ} (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ)
    (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hfc : HasCompactSupport f) (A : ℝ) (hA0 : 0 ≤ A)
    (hA : ∀ z, ‖f z‖ ≤ A) :
    (u, g) ∈ closure (ginibreInteriorSmoothPair n) := by
  let χ (m : ℕ) := ginibreCollisionCutoff n m
  let v (m : ℕ) := (ginibreCollisionCutoff_L2_mul_memLp n m u
    (Lp.memLp u)).toLp (fun z => χ m z • u z)
  let a (m : ℕ) := (ginibreCollisionCutoff_L2_mul_memLp n m g
    (Lp.memLp g)).toLp (fun z => χ m z • g z)
  let b (m : ℕ) := (ginibreCollisionCutoff_bounded_gradient_memLp n hn f
    ((Lp.aestronglyMeasurable u).congr hf) hfc A hA m).toLp
      (fun z => f z • ginibreEuclideanGradient (χ m) z)
  let q (m : ℕ) := (v m, a m + b m)
  have hqdist (m : ℕ) : IsGinibreDistributionalGradient n (q m).1 (q m).2 := by
    apply ginibre_distributional_gradient_mul n hn u g hg (χ m)
      (ginibreCollisionCutoff_smooth n m) (v m) (a m + b m)
    · filter_upwards [(ginibreCollisionCutoff_L2_mul_memLp n m u
        (Lp.memLp u)).coeFn_toLp] with z hz
      simpa [v, χ, smul_eq_mul] using hz
    · filter_upwards [Lp.coeFn_add (a m) (b m),
        (ginibreCollisionCutoff_L2_mul_memLp n m g (Lp.memLp g)).coeFn_toLp,
        (ginibreCollisionCutoff_bounded_gradient_memLp n hn f
          ((Lp.aestronglyMeasurable u).congr hf) hfc A hA m).coeFn_toLp,
        hf] with z hz ha hb hfu
      rw [hz]
      change (a m) z + (b m) z = _
      rw [ha, hb, hfu]
  have hqvalue (m : ℕ) : ((q m).1 : Configuration n → ℝ) =ᵐ[
      ginibreMeasure n] fun z => χ m z * f z := by
    filter_upwards [(ginibreCollisionCutoff_L2_mul_memLp n m u
      (Lp.memLp u)).coeFn_toLp, hf] with z hz hzf
    rw [hz, hzf]
    simp only [smul_eq_mul, χ]
  have hqcompact (m : ℕ) : HasCompactSupport (fun z => χ m z * f z) :=
    hfc.mul_left
  have hqinterior (m : ℕ) : tsupport (fun z => χ m z * f z) ⊆
      {z | CollisionFree z} :=
    (tsupport_mul_subset_left (f := χ m) (g := f)).trans
      (ginibreCollisionCutoff_support_collisionFree n m)
  have hqcore (m : ℕ) : (q m) ∈ closure (ginibreInteriorSmoothPair n) := by
    obtain ⟨h, hh, hhc, hhs⟩ :=
      ginibre_distributional_gradient_exists_supported_representative n hn
        (q m).1 (q m).2 (hqdist m) (fun z => χ m z * f z)
        (hqvalue m) (hqcompact m)
    obtain ⟨s, hs, ht⟩ := ginibreInteriorWeakPair_exists_smoothSequence hn
      (q m).1 (q m).2 (hqdist m) (fun z => χ m z * f z) h (hqvalue m) hh
      (hqcompact m) hhc (hqinterior m) (hhs.trans (hqinterior m))
    exact isClosed_closure.mem_of_tendsto ht
      (Eventually.of_forall (fun j => subset_closure (hs j)))
  have hlimVal : Tendsto (fun m => (q m).1) atTop (𝓝 u) := by
    have hmul := ginibreCollisionCutoff_mul_L2_tendsto n hn u
    have hrep (m : ℕ) : (q m).1 =
        (ginibreCollisionCutoff_L2_mul_memLp n m u (Lp.memLp u)).toLp
          (fun z => χ m z • u z) := rfl
    simp_rw [hrep]
    exact hmul
  have hlimGrad : Tendsto (fun m => (q m).2) atTop (𝓝 g) := by
    have hfirst := ginibreCollisionCutoff_mul_L2_tendsto n hn g
    have hsecond := ginibreCollisionCutoff_bounded_gradient_L2_tendsto n hn f
      ((Lp.aestronglyMeasurable u).congr hf) hfc A hA0 hA
    have hrep (m : ℕ) : (q m).2 =
        (ginibreCollisionCutoff_L2_mul_memLp n m g (Lp.memLp g)).toLp
            (fun z => χ m z • g z) +
          (ginibreCollisionCutoff_bounded_gradient_memLp n hn f
            ((Lp.aestronglyMeasurable u).congr hf) hfc A hA m).toLp
            (fun z => f z • ginibreEuclideanGradient (χ m) z) := by
      rfl
    simp_rw [hrep]
    simpa using hfirst.add hsecond
  exact isClosed_closure.mem_of_tendsto (hlimVal.prodMk_nhds hlimGrad)
    (Eventually.of_forall hqcore)

end
end GinibrePoincare
