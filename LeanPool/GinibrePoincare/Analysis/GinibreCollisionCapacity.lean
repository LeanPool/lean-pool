/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreCollisionCapacity.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreTransitionAnalyticCutoffExhaustion

/-!
# Ginibre collision capacity

Part of the weak Sobolev domains and collision capacity development of the
Ginibre Poincaré formalization.

Main results: `ginibreCapacityCosts_nonempty`, `ginibreCollisionSet_capacity_zero`.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology ContDiff NNReal
namespace GinibrePoincare
noncomputable section

/-- The ordinary real weighted H¹ capacity, with the paper's Dirichlet
normalization. Admissible representatives are at least one on an open
neighborhood of the set, and their gradients are actual weak gradients. -/
def ginibreCapacityCosts (n : ℕ) (C : Set (Configuration n)) : Set ℝ :=
  {r | ∃ (u : Configuration n → ℝ) (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (hu : MemLp u 2 (ginibreMeasure n)) (hg : MemLp g 2 (ginibreMeasure n)),
    IsGinibreDistributionalGradient n (hu.toLp u) (hg.toLp g) ∧
    (∃ U : Set (Configuration n), IsOpen U ∧ C ⊆ U ∧ ∀ z ∈ U, 1≤u z) ∧
    r=(∫ z, u z^2 ∂ginibreMeasure n)+(1/(n : ℝ))*(∫ z, ‖g z‖^2 ∂ginibreMeasure n)}

/-- The weighted `H¹` capacity of `C`: the infimum of the admissible costs
`ginibreCapacityCosts n C`. -/
def ginibreCapacity (n : ℕ) (C : Set (Configuration n)) : ℝ :=
  sInf (ginibreCapacityCosts n C)

theorem ginibreCapacityCosts_nonnegative (n : ℕ) (C : Set (Configuration n))
    {r : ℝ} (hr : r ∈ ginibreCapacityCosts n C) : 0≤r := by
  obtain ⟨u, g, hu, hg, hw, hU, rfl⟩ := hr
  exact add_nonneg (integral_nonneg fun z => sq_nonneg _)
    (mul_nonneg (by positivity) (integral_nonneg fun z => sq_nonneg _))

theorem ginibreCapacityCosts_smooth_mem {n : ℕ} (hn : 0 < n)
    (C : Set (Configuration n)) (u : Configuration n → ℝ)
    (hs : ContDiff ℝ ∞ u) (hu : MemLp u 2 (ginibreMeasure n))
    (hg : MemLp (ginibreEuclideanGradient u) 2 (ginibreMeasure n))
    (hU : ∃ U : Set (Configuration n), IsOpen U ∧ C ⊆ U ∧ ∀ z ∈ U, 1 ≤ u z) :
    (∫ z, u z^2 ∂ginibreMeasure n)+(1/(n : ℝ))*(∫ z, ‖ginibreEuclideanGradient u z‖^2
        ∂ginibreMeasure n)
      ∈ ginibreCapacityCosts n C := by
  exact ⟨u, ginibreEuclideanGradient u, hu, hg,
    ginibre_smooth_distributional_gradient n hn _ _ u hs hu.coeFn_toLp hg.coeFn_toLp, hU, rfl⟩

theorem ginibreEuclideanGradient_one_sub (n : ℕ) (f : Configuration n → ℝ) :
    ginibreEuclideanGradient (fun z => 1-f z)=fun z => -ginibreEuclideanGradient f z := by
  funext z
  ext k
  simp only [ginibreEuclideanGradient_coordinate, fderiv_const_sub, neg_apply, PiLp.neg_apply]

/-- The constant-one weak-H¹ representative is admissible for every set. -/
theorem ginibreCapacityCosts_nonempty {n : ℕ} (hn : 0 < n)
    (C : Set (Configuration n)) : (ginibreCapacityCosts n C).Nonempty := by
  let := ginibreMeasure_isProbabilityMeasure hn
  have hg0 : ginibreEuclideanGradient (fun _ : Configuration n => (1 : ℝ))=fun _ => 0 := by
    funext z
    ext k
    simp [ginibreEuclideanGradient_coordinate]
  have hg : MemLp (ginibreEuclideanGradient (fun _ : Configuration n => (1 : ℝ))) 2 (ginibreMeasure
      n) := by
    rw [hg0]
    exact memLp_const (0 : EuclideanSpace ℝ (Fin n × Fin 2))
  exact ⟨_, ginibreCapacityCosts_smooth_mem hn C (fun _ => (1 : ℝ)) contDiff_const
    (memLp_const 1) hg ⟨univ, isOpen_univ, subset_univ _, fun _ _ => le_rfl⟩⟩

/-- The full collision locus has literal zero weighted H¹ capacity. -/
theorem ginibreCollisionSet_capacity_zero {n : ℕ} (hn : 0 < n) :
    ginibreCapacity n (collisionSet n)=0 := by
  let := ginibreMeasure_isProbabilityMeasure hn
  obtain ⟨η, hcore, hbound, hpoint, henergy⟩ := ginibreTransitionAnalytic_vanishing_energy_cutoffs
      hn
  let u := fun m z => 1-η m z
  have hu (m : ℕ) : MemLp (u m) 2 (ginibreMeasure n) :=
    (memLp_const (1 : ℝ)).sub (ginibreFull_smoothCompact_memLp n hn (η m) (hcore m).1 (hcore
        m).2.1).1
  have hg (m : ℕ) : MemLp (ginibreEuclideanGradient (u m)) 2 (ginibreMeasure n) := by
    rw [ginibreEuclideanGradient_one_sub]
    exact (ginibreFull_smoothCompact_memLp n hn (η m) (hcore m).1 (hcore m).2.1).2.neg
  have hU (m : ℕ) : ∃ U : Set (Configuration n), IsOpen U ∧ collisionSet n⊆U ∧ ∀ z∈U, 1≤u m z := by
    refine ⟨(tsupport (η m))ᶜ, (isClosed_tsupport _).isOpen_compl,?_,?_⟩
    · intro z hz hzs
      exact (hcore m).2.2.1 hzs hz
    · intro z hz
      have he := image_eq_zero_of_notMem_tsupport hz
      simp only [u, he, sub_zero, le_refl]
  let cost := fun m => (∫ z, u m z^2 ∂ginibreMeasure n)+(1/(n : ℝ))*(∫ z, ‖ginibreEuclideanGradient
      (u m) z‖^2 ∂ginibreMeasure n)
  have hc (m : ℕ) : cost m∈ginibreCapacityCosts n (collisionSet n) :=
    ginibreCapacityCosts_smooth_mem hn _ _ (contDiff_const.sub (hcore m).1) (hu m) (hg m) (hU m)
  have hmass : Tendsto (fun m => ∫ z, u m z^2 ∂ginibreMeasure n) atTop (𝓝 0) := by
    have hh := tendsto_integral_of_dominated_convergence (μ := ginibreMeasure n) (F := fun m z => u
        m z^2) (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
      (fun m => (contDiff_const.sub (hcore m).1).continuous.aestronglyMeasurable.pow 2)
      (integrable_const (1 : ℝ)) (fun m => ae_of_all _ fun z => by
        obtain ⟨h0, h1⟩ := hbound m z
        change ‖(1-η m z)^2‖≤1
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        nlinarith) ?_
    · simpa using hh
    · filter_upwards [ginibre_ae_collisionFree n hn] with z hz
      have he := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub (hpoint z
          hz)).pow 2
      simpa only [sub_self, zero_pow (by decide : (2 : ℕ)≠0)] using he
  have hgrad : Tendsto (fun m => ∫ z, ‖ginibreEuclideanGradient (u m) z‖^2 ∂ginibreMeasure n) atTop
      (𝓝 0) := by
    simpa only [u, ginibreEuclideanGradient_one_sub, norm_neg] using henergy
  have ht : Tendsto cost atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using hmass.add (hgrad.const_mul (1/(n : ℝ)))
  have hnonempty : (ginibreCapacityCosts n (collisionSet n)).Nonempty := ⟨cost 0, hc 0⟩
  have hb : BddBelow (ginibreCapacityCosts n (collisionSet n)) :=
    ⟨0, fun r hr => ginibreCapacityCosts_nonnegative n _ hr⟩
  apply le_antisymm
  · exact ge_of_tendsto' ht (fun m => csInf_le hb (hc m))
  · exact le_csInf hnonempty (fun r hr => ginibreCapacityCosts_nonnegative n _ hr)

end
end GinibrePoincare
