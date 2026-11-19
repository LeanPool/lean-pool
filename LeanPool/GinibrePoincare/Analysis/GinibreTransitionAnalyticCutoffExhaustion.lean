/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreTransitionAnalyticCutoffExhaustion.lean.
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
public import LeanPool.GinibrePoincare.Analysis.GinibreSpatialCutoffs
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorCoreCompatibility
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorSpectrum
public import LeanPool.GinibrePoincare.Analysis.GinibreMixedGreenIdentity
public import LeanPool.GinibrePoincare.Analysis.GinibreSymmetricWeakPoincare
public import LeanPool.GinibrePoincare.Analysis.GinibreZeroPairCutoff
public import LeanPool.GinibrePoincare.Analysis.RadialInteriorWeakSobolevApproximation
public import LeanPool.GinibrePoincare.Analysis.RadialSmoothSobolevApproximation
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-! Actual smooth compact collision-free exhaustion with vanishing global
Dirichlet energy for the concrete Ginibre probability measure. -/

@[expose] public section
open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

theorem ginibreTransitionAnalytic_vanishing_energy_cutoffs {n : ℕ} (hn : 0 < n) :
    ∃ η : ℕ → Configuration n → ℝ,
      (∀ m, IsTheoremOneNineCore (η m)) ∧
      (∀ m z, 0 ≤ η m z ∧ η m z ≤ 1) ∧
      (∀ z, CollisionFree z → Tendsto (fun m => η m z) atTop (𝓝 1)) ∧
      Tendsto (fun m => ∫ z, ‖ginibreEuclideanGradient (η m) z‖^2 ∂ginibreMeasure n)
        atTop (𝓝 0) := by
  let := ginibreMeasure_isProbabilityMeasure hn
  have hs (m : ℕ) := ginibreSpatialCutoff_smooth n m
  have hbound (m : ℕ) (z : Configuration n) : ‖ginibreSpatialCutoff n m z‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (ginibreSpatialCutoff_mem_unit n m z).1]
    exact (ginibreSpatialCutoff_mem_unit n m z).2
  have hex (m : ℕ) : ∃ k : ℕ, m ≤ k ∧
      (∫ z, ‖ginibreSpatialCutoff n m z • ginibreEuclideanGradient (ginibreCollisionCutoff n k) z‖^2
        ∂ginibreMeasure n) ≤ 1/((m : ℝ)+1) := by
    have hh := ginibreCollisionCutoff_bounded_gradient_energy_tendsto n hn (ginibreSpatialCutoff n
        m)
      (hs m).continuous.aestronglyMeasurable (ginibreSpatialCutoff_compact n m) 1 (by norm_num)
          (hbound m)
    have he := hh.eventually (eventually_lt_nhds (by positivity : (0 : ℝ)<1/((m : ℝ)+1)))
    obtain ⟨k, hk⟩ := (he.and (eventually_ge_atTop m)).exists
    exact ⟨k, hk.2, hk.1.le⟩
  choose k hk henergy using hex
  let η := fun m z => ginibreCollisionCutoff n (k m) z*ginibreSpatialCutoff n m z
  have hcore (m : ℕ) : IsTheoremOneNineCore (η m) :=
    ginibreCollisionCutoff_mul_core n (k m) (ginibreSpatialCutoff n m)
      ⟨hs m, ginibreSpatialCutoff_compact n m, ginibreSpatialCutoff_symmetric n m⟩
  refine ⟨η, hcore,?_,?_,?_⟩
  · intro m z
    obtain ⟨ha, hb⟩ := ginibreCollisionCutoff_mem_unit n (k m) z
    obtain ⟨hc, hd⟩ := ginibreSpatialCutoff_mem_unit n m z
    exact ⟨mul_nonneg ha hc, (mul_le_mul hb hd hc (by norm_num)).trans_eq (one_mul 1)⟩
  · intro z hz
    have hkTop : Tendsto k atTop atTop := tendsto_atTop_mono hk tendsto_id
    have hh := (ginibreCollisionCutoff_eventually_one_gradient_zero n z hz).mono fun m hm => hm.1
    have hc : Tendsto (fun m => ginibreCollisionCutoff n m z) atTop (𝓝 1) :=
      tendsto_const_nhds.congr' (hh.mono fun m hm => hm.symm)
    simpa only [η, one_mul, Function.comp_def] using (hc.comp hkTop).mul
        (ginibreSpatialCutoff_tendsto n z)
  · obtain ⟨C, hC, hgrad⟩ := ginibreSpatialCutoff_gradient_bound
    have hηL (m : ℕ) := (ginibreFull_smoothCompact_memLp n hn (η m) (hcore m).1 (hcore m).2.1).2
    have hBL (m : ℕ) := ginibreCollisionCutoff_bounded_gradient_memLp n hn (ginibreSpatialCutoff n
        m)
      (hs m).continuous.aestronglyMeasurable (ginibreSpatialCutoff_compact n m) 1 (hbound m) (k m)
    have hb (m : ℕ) (z : Configuration n) : ‖ginibreEuclideanGradient (η m) z‖^2 ≤
        2*(C/((m : ℝ)+1))+2*‖ginibreSpatialCutoff n m z •
          ginibreEuclideanGradient (ginibreCollisionCutoff n (k m)) z‖^2 := by
      have he := ginibreEuclideanGradient_mul (ginibreSpatialCutoff n m) (ginibreCollisionCutoff n
          (k m))
        (hs m) (ginibreCollisionCutoff_smooth n (k m)) z
      change ginibreEuclideanGradient (η m) z = _ at he
      have hA : ‖ginibreCollisionCutoff n (k m) z • ginibreEuclideanGradient (ginibreSpatialCutoff n
          m) z‖ ≤
          ‖ginibreEuclideanGradient (ginibreSpatialCutoff n m) z‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ginibreCollisionCutoff_mem_unit n (k m)
            z).1]
        exact mul_le_of_le_one_left (norm_nonneg _) (ginibreCollisionCutoff_mem_unit n (k m) z).2
      have ht : ‖ginibreEuclideanGradient (η m) z‖ ≤
          ‖ginibreEuclideanGradient (ginibreSpatialCutoff n m) z‖+
          ‖ginibreSpatialCutoff n m z • ginibreEuclideanGradient (ginibreCollisionCutoff n (k m)) z‖
              := by
        rw [he]
        exact (norm_add_le _ _).trans (add_le_add hA le_rfl)
      have hg := hgrad n m z
      nlinarith [sq_nonneg (‖ginibreEuclideanGradient (ginibreSpatialCutoff n m) z‖-
        ‖ginibreSpatialCutoff n m z • ginibreEuclideanGradient (ginibreCollisionCutoff n (k m)) z‖),
        norm_nonneg (ginibreEuclideanGradient (η m) z)]
    have hle (m : ℕ) : (∫ z, ‖ginibreEuclideanGradient (η m) z‖^2 ∂ginibreMeasure n) ≤
        2*C/((m : ℝ)+1)+2/((m : ℝ)+1) := by
      have hh := integral_mono (hηL m).norm.integrable_sq
        ((integrable_const (2*(C/((m : ℝ)+1)))).add ((hBL m).norm.integrable_sq.const_mul 2)) (hb m)
      have hi := integral_add (integrable_const (2*(C/((m : ℝ)+1)))) ((hBL
          m).norm.integrable_sq.const_mul 2)
      simp only [Pi.add_apply] at hh hi
      rw [hi, integral_const, integral_const_mul] at hh
      simp only [Measure.real, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul] at hh
      calc
        _ ≤ 2*(C/((m : ℝ)+1))+2*(∫ z, ‖ginibreSpatialCutoff n m z •
            ginibreEuclideanGradient (ginibreCollisionCutoff n (k m)) z‖^2 ∂ginibreMeasure n) := hh
        _ ≤ 2*(C/((m : ℝ)+1))+2*(1/((m : ℝ)+1)) := by gcongr; exact henergy m
        _ = _ := by ring
    apply squeeze_zero (fun m => integral_nonneg fun z => sq_nonneg _) hle
    have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2*C+2)
    convert hh using 1 <;> (try funext m) <;> ring_nf

end
end GinibrePoincare
