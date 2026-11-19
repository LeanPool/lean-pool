/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreEntireProjectionDistance.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreEntireProjectionGeometry

/-!
# Ginibre entire projection distance

Part of the ginibre measure and holomorphic geometry development of the
Ginibre Poincaré formalization.

Main results: `ginibreHolomorphicDistanceSq_eq_projectionNorm`.
-/

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section

theorem continuous_ginibreL2_iff_memLp {n : ℕ} (g : Configuration n → ℂ)
    (hg : Continuous g) : IsGinibreL2 n g ↔ MemLp g 2 (ginibreMeasure n) := by
  rw [memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable]
  simp only [IsGinibreL2, Complex.sq_norm]

theorem ginibreComplexError_eq_L2_norm_sq {n : ℕ}
    (u v : Lp ℂ 2 (ginibreMeasure n)) (f : Configuration n → ℝ)
    (h : Configuration n → ℂ) (hu : (fun z => (f z : ℂ)) =ᵐ[ginibreMeasure n] u)
    (hv : h =ᵐ[ginibreMeasure n] v) :
    ginibreComplexError n f h = ‖u-v‖ ^ 2 := by
  rw [ginibreComplexError, ← integral_norm_sq_eq_L2_norm_sq]
  apply integral_congr_ae
  filter_upwards [hu, hv, Lp.coeFn_sub u v] with z huz hvz hsub
  simp only [Pi.sub_apply] at hsub
  rw [huz, hvz, hsub, Complex.sq_norm]

theorem ginibreEntireRepresentative_mem_symmetric {n : ℕ}
    (u : Lp ℂ 2 (ginibreMeasure n)) (g : Configuration n → ℂ)
    (hg : IsSymmetric g) (heq : g =ᵐ[ginibreMeasure n] u) :
    u ∈ ginibreSymmetricL2 n := by
  intro σ
  apply Lp.ext
  have hp := ginibre_measurePreserving_permute σ
  have hc := Lp.coeFn_compMeasurePreserving u hp
  have heqp := hp.quasiMeasurePreserving.ae_eq_comp heq
  filter_upwards [hc, heq, heqp] with z hcz hez hepz
  change (Lp.compMeasurePreserving (permute σ) hp u) z = u z
  rw [hcz, ← hepz]
  exact (hg σ z).trans hez

/-- The literal infimum of symmetric entire integral errors is attained by
projection onto the paper's actual divisible entire space. -/
theorem ginibreHolomorphicDistanceSq_eq_projectionNorm {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (ginibreMeasure n)) (f : Configuration n → ℝ)
    (hu : (fun z => (f z : ℂ)) =ᵐ[ginibreMeasure n] u) :
    ginibreHolomorphicDistanceSq n f =
      ‖u - (ginibreDivisibleEntireClosedSpace n hn).starProjection u‖ ^ 2 := by
  let H := ginibreDivisibleEntireClosedSpace n hn
  let P := H.starProjection
  have hmem : P u ∈ ginibreDivisibleEntireL2 n hn :=
    Submodule.starProjection_apply_mem H.toSubmodule u
  obtain ⟨v, hv, hvu⟩ := hmem
  obtain ⟨h, hsym, hh⟩ := ginibreDivisibleEntire_exists_symmetricRepresentative hn v hv
  have hrep : h =ᵐ[ginibreMeasure n] P u := hvu ▸ hh.2
  have hml : MemLp h 2 (ginibreMeasure n) := (memLp_congr_ae hrep).mpr (Lp.memLp (P u))
  have hhL2 : IsGinibreL2 n h := (continuous_ginibreL2_iff_memLp h hh.1.continuous).mpr hml
  have herr : ‖u-P u‖ ^ 2 ∈ ginibreHolomorphicErrors n f := by
    refine ⟨h, ⟨hsym, hh.1, hhL2⟩, ?_⟩
    exact (ginibreComplexError_eq_L2_norm_sq u (P u) f h hu hrep).symm
  have hb : BddBelow (ginibreHolomorphicErrors n f) := by
    refine ⟨0, ?_⟩
    rintro r ⟨a, _, rfl⟩
    exact integral_nonneg (fun _ => Complex.normSq_nonneg _)
  apply le_antisymm
  · exact csInf_le hb herr
  · apply le_csInf ⟨_, herr⟩
    rintro r ⟨a, ha, rfl⟩
    have haml := (continuous_ginibreL2_iff_memLp a ha.2.1.continuous).mp ha.2.2
    let w := haml.toLp a
    have hwrep : IsGinibreEntireRepresentative w a := ⟨ha.2.1, haml.coeFn_toLp.symm⟩
    have hws := ginibreEntireRepresentative_mem_symmetric w a ha.1 hwrep.2
    have hwm : w ∈ H := by
      change w ∈ ginibreDivisibleEntireL2 n hn
      rw [ginibreDivisibleEntireL2_eq_holomorphicAmbient]
      exact ginibreSymmetricEntire_mem_holomorphicAmbient hn ⟨w, hws⟩ a hwrep
    rw [ginibreComplexError_eq_L2_norm_sq u w f a hu hwrep.2]
    have ho : inner ℂ (u-P u) (P u-w) = 0 :=
      Submodule.starProjection_inner_eq_zero u (P u-w)
        (H.sub_mem (Submodule.starProjection_apply_mem H.toSubmodule u) hwm)
    have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (u-P u) (P u-w) ho
    have he : (u-P u)+(P u-w) = u-w := by abel
    rw [he] at hpy
    nlinarith [sq_nonneg ‖P u-w‖]

end
end GinibrePoincare
