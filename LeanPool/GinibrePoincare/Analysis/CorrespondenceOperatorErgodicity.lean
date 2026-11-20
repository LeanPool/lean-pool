/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorErgodicity.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorFixedSpace
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorErgodicClosure
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorRealEvolution
/-!
# Correspondence operator ergodicity

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperatorEvolution_ergodic`.
-/

@[expose] public section
open Set MeasureTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
/-- Actual unrestricted complex L² mean as pairing with the literal constant one. -/
theorem correspondenceOperator_constant_one_inner (n : ℕ) (hn : 0 < n)
    (u : GinibreFullComplexL2 n) :
    inner ℂ (ginibreFullConstant n hn 1).val u=∫z, u z∂ginibreMeasure n := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ginibreFullConstant_ae n hn 1] with z hz
  simp [hz]

theorem correspondenceOperator_constant_inner (n : ℕ) (hn : 0 < n) (a : ℂ) :
    inner ℂ (ginibreFullConstant n hn 1).val (ginibreFullConstant n hn a).val=a := by
  let := ginibreMeasure_isProbabilityMeasure hn
  rw [correspondenceOperator_constant_one_inner]
  rw [integral_congr_ae (ginibreFullConstant_ae n hn a)]
  simp

/-- Every zero-mean unrestricted vector is in the actual resolvent complement
range closure, using the fully proved ordinary weak-gradient fixed space. -/
theorem correspondenceOperator_mean_zero_mem_complement_closure {n : ℕ} (hn : 0 < n)
    (u : GinibreFullComplexL2 n) (hu : inner ℂ (ginibreFullConstant n hn 1).val u = 0) :
    u∈(1-correspondenceOperatorComplexResolvent n hn).range.topologicalClosure := by
  let R := correspondenceOperatorComplexResolvent n hn
  let L : GinibreFullComplexL2 n→L[ℂ] GinibreFullComplexL2 n := 1-R
  have hAdj : L.adjoint=L := by
    have hR : R.adjoint=R := correspondenceOperatorComplexResolvent_isSelfAdjoint n hn
    change ContinuousLinearMap.adjoint (1-R)=1-R
    rw [map_sub, ContinuousLinearMap.adjoint_one, hR]
  have he := L.orthogonal_ker
  rw [hAdj] at he
  change u∈L.range.topologicalClosure
  rw [← he]
  rw [Submodule.mem_orthogonal]
  intro v hv
  have hv0 : v-R v=0 := hv
  have hfixed : R v=v := (sub_eq_zero.mp hv0).symm
  obtain ⟨a, ha⟩ := (correspondenceOperatorComplexResolvent_fixed_iff_constant hn v).mp hfixed
  rw [ha]
  have hconst : (ginibreFullConstant n hn a).val=a • (ginibreFullConstant n hn 1).val := by
    apply Lp.ext
    filter_upwards [ginibreFullConstant_ae n hn a, ginibreFullConstant_ae n hn 1,
      Lp.coeFn_smul a (ginibreFullConstant n hn 1).val] with z hz h1 hs
    rw [hs, hz]
    simp only [Pi.smul_apply, smul_eq_mul, h1, mul_one]
  rw [hconst, inner_smul_left, hu, mul_zero]

/-- The actual unrestricted complex semigroup converges strongly to its concrete
Ginibre mean at all continuous times, without a symmetric-domain restriction. -/
theorem correspondenceOperatorEvolution_ergodic {n : ℕ} (hn : 0 < n)
    (u : GinibreFullComplexL2 n) :
    Tendsto (fun t : ℝ≥0 => correspondenceOperatorEvolution n hn t u) atTop
      (𝓝 (ginibreFullConstant n hn (∫z, u z∂ginibreMeasure n)).val) := by
  let a := ∫z, u z∂ginibreMeasure n
  let c := (ginibreFullConstant n hn a).val
  have hm : inner ℂ (ginibreFullConstant n hn 1).val (u-c)=0 := by
    rw [inner_sub_right, correspondenceOperator_constant_one_inner,
      correspondenceOperator_constant_inner, sub_self]
  have hc := correspondenceOperator_mean_zero_mem_complement_closure hn (u-c) hm
  have hlim := correspondenceOperator_ergodic_complement_closure
    (correspondenceOperatorComplexResolvent n hn)
        (correspondenceOperatorComplexResolvent_isSelfAdjoint n hn)
    (correspondenceOperatorComplexResolvent_spectrum n hn) (u-c) hc
  have hsum := hlim.add (tendsto_const_nhds (x := c))
  simp only [zero_add] at hsum
  apply hsum.congr
  intro t
  change correspondenceOperatorEvolution n hn t (u-c)+c=correspondenceOperatorEvolution n hn t u
  rw [map_sub, correspondenceOperatorEvolution_constant]
  exact sub_add_cancel _ _
end
end GinibrePoincare
