/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreFullSemigroupConservation.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupConstants
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroup
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupEigenvectors
public import LeanPool.GinibrePoincare.Analysis.GinibreConjugationGeometry
public import LeanPool.GinibrePoincare.Analysis.GinibreEqualityWeakVariational
public import LeanPool.GinibrePoincare.Analysis.GinibreZeroPairCutoff
public import LeanPool.GinibrePoincare.Analysis.RadialInteriorWeakSobolevApproximation
public import LeanPool.GinibrePoincare.Analysis.RadialSmoothSobolevApproximation
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-! # Conservation and the exact constant kernel of the full generator -/

@[expose] public section
open MeasureTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- An actual complex equilibrium constant in the full symmetric Hilbert space. -/
def ginibreFullConstant (n : ℕ) (hn : 0 < n) (c : ℂ) : ginibreSymmetricL2 n := by
  let := ginibreMeasure_isProbabilityMeasure hn
  exact ⟨ginibreConstantL2 n hn c, by
    intro σ
    apply Lp.ext
    have ha : (ginibreConstantL2 n hn c : Configuration n → ℂ) =ᵐ[ginibreMeasure n] fun _ => c :=
      Lp.coeFn_const 2 (ginibreMeasure n) c
    have hcomp := (ginibre_measurePreserving_permute
        σ).quasiMeasurePreserving.ae_eq_comp ha
    filter_upwards [Lp.coeFn_compMeasurePreserving (ginibreConstantL2 n hn c)
        (ginibre_measurePreserving_permute σ), hcomp, ha] with z hp hc hu
    change (ginibrePermutationL2 σ (ginibreConstantL2 n hn c)) z =
      (ginibreConstantL2 n hn c) (permute σ z) at hp
    simp only [Function.comp_apply] at hc
    rw [hp, hc, hu]⟩

theorem ginibreFullConstant_ae (n : ℕ) (hn : 0 < n) (c : ℂ) :
    ((ginibreFullConstant n hn c).val : Configuration n → ℂ) =ᵐ[ginibreMeasure n] fun _ => c := by
  let := ginibreMeasure_isProbabilityMeasure hn
  exact Lp.coeFn_const 2 (ginibreMeasure n) c

/-- Real and imaginary parts uniquely determine actual symmetric L² vectors. -/
theorem ginibreFullSymmetric_ext_parts (n : ℕ) (f h : ginibreSymmetricL2 n)
    (hr : ginibreFullSymmetricRe n f = ginibreFullSymmetricRe n h)
    (hi : ginibreFullSymmetricIm n f = ginibreFullSymmetricIm n h) : f = h := by
  apply Subtype.ext
  have hr' : ginibreFullComplexRe n f.val = ginibreFullComplexRe n h.val := congrArg Subtype.val hr
  have hi' : ginibreFullComplexIm n f.val = ginibreFullComplexIm n h.val := congrArg Subtype.val hi
  rw [← ginibreFullComplex_decomposition n f.val, ← ginibreFullComplex_decomposition n h.val,
    hr', hi']

@[simp] theorem ginibreFullConstant_re (n : ℕ) (hn : 0 < n) (c : ℂ) :
    (ginibreFullSymmetricRe n (ginibreFullConstant n hn c)).val = ginibreRealConstantL2 n hn c.re :=
        by
  apply Lp.ext
  filter_upwards [ginibreFullComplexRe_ae n (ginibreFullConstant n hn c).val,
    ginibreFullConstant_ae n hn c, ginibreRealConstantL2_ae n hn c.re] with z hr hc hv
  exact (hr.trans (congrArg Complex.re hc)).trans hv.symm

@[simp] theorem ginibreFullConstant_im (n : ℕ) (hn : 0 < n) (c : ℂ) :
    (ginibreFullSymmetricIm n (ginibreFullConstant n hn c)).val = ginibreRealConstantL2 n hn c.im :=
        by
  apply Lp.ext
  filter_upwards [ginibreFullComplexIm_ae n (ginibreFullConstant n hn c).val,
    ginibreFullConstant_ae n hn c, ginibreRealConstantL2_ae n hn c.im] with z hr hc hv
  exact (hr.trans (congrArg Complex.im hc)).trans hv.symm

/-- The concrete full complex weak resolvent fixes every equilibrium constant. -/
theorem ginibreFullComplexResolvent_constant (n : ℕ) (hn : 0 < n) (c : ℂ) :
    ginibreFullComplexResolvent n hn (ginibreFullConstant n hn c) = ginibreFullConstant n hn c := by
  apply ginibreFullSymmetric_ext_parts
  · rw [ginibreFullComplexResolvent_re]
    apply Subtype.ext
    change ginibreFullValueResolvent n hn (ginibreFullSymmetricRe n (ginibreFullConstant n hn
        c)).val = _
    rw [ginibreFullConstant_re, ginibreFullValueResolvent_constant]
  · rw [ginibreFullComplexResolvent_im]
    apply Subtype.ext
    change ginibreFullValueResolvent n hn (ginibreFullSymmetricIm n (ginibreFullConstant n hn
        c)).val = _
    rw [ginibreFullConstant_im, ginibreFullValueResolvent_constant]

/-- Every equilibrium constant belongs to the actual full generator kernel. -/
theorem ginibreFullGenerator_constant (n : ℕ) (hn : 0 < n) (c : ℂ) :
    (ginibreFullConstant n hn c, 0) ∈ (ginibreFullGenerator n hn).graph := by
  rw [ginibreFullGenerator_graph_iff, sub_zero]
  exact ginibreFullComplexResolvent_constant n hn c

/-- Conservation of every constant by the full-space semigroup. -/
theorem ginibreFullEvolution_constant (n : ℕ) (hn : 0 < n) (t : ℝ≥0) (c : ℂ) :
    ginibreFullEvolution n hn t (ginibreFullConstant n hn c) = ginibreFullConstant n hn c :=
  resolventCfcEvolution_fixes_kernel _ (ginibreFullComplexResolvent_isSelfAdjoint n hn)
    (ginibreFullComplexResolvent_injective n hn) t _ (ginibreFullGenerator_constant n hn c)

/-- The fixed space of the actual complex weak resolvent consists exactly of constants. -/
theorem ginibreFullComplexResolvent_fixed_iff_constant (n : ℕ) (hn : 0 < n)
    (u : ginibreSymmetricL2 n) : ginibreFullComplexResolvent n hn u = u ↔
      ∃ c : ℂ, u = ginibreFullConstant n hn c := by
  constructor
  · intro hu
    have hr := congrArg (ginibreFullSymmetricRe n) hu
    have hi := congrArg (ginibreFullSymmetricIm n) hu
    rw [ginibreFullComplexResolvent_re] at hr
    rw [ginibreFullComplexResolvent_im] at hi
    have hre := (ginibreFullValueResolvent_fixed_iff_constant n hn
      (ginibreFullSymmetricRe n u).val).mp (congrArg Subtype.val hr)
    have him := (ginibreFullValueResolvent_fixed_iff_constant n hn
      (ginibreFullSymmetricIm n u).val).mp (congrArg Subtype.val hi)
    refine ⟨⟨ginibreL2Mean n (ginibreFullSymmetricRe n u).val,
      ginibreL2Mean n (ginibreFullSymmetricIm n u).val⟩, ?_⟩
    apply ginibreFullSymmetric_ext_parts
    · apply Subtype.ext
      rw [ginibreFullConstant_re]
      exact hre
    · apply Subtype.ext
      rw [ginibreFullConstant_im]
      exact him
  · rintro ⟨c, rfl⟩
    exact ginibreFullComplexResolvent_constant n hn c

/-- Exhaustive constant-kernel classification on the actual full generator domain. -/
theorem ginibreFullGenerator_kernel_iff_constant (n : ℕ) (hn : 0 < n)
    (u : ginibreSymmetricL2 n) : (u, 0) ∈ (ginibreFullGenerator n hn).graph ↔
      ∃ c : ℂ, u = ginibreFullConstant n hn c := by
  rw [ginibreFullGenerator_graph_iff, sub_zero, ginibreFullComplexResolvent_fixed_iff_constant]

/-- The equilibrium integral is the full Hilbert pairing with constant one. -/
theorem ginibreFullConstant_one_inner (n : ℕ) (hn : 0 < n) (u : ginibreSymmetricL2 n) :
    inner ℂ (ginibreFullConstant n hn 1) u = ∫ z, u.val z ∂ginibreMeasure n := by
  change inner ℂ (ginibreFullConstant n hn 1).val u.val = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ginibreFullConstant_ae n hn 1] with z hz
  simp [hz]

/-- Conservation of the equilibrium integral for every full-space L² observable. -/
theorem ginibreFullEvolution_integral (n : ℕ) (hn : 0 < n) (t : ℝ≥0)
    (u : ginibreSymmetricL2 n) :
    (∫ z, (ginibreFullEvolution n hn t u).val z ∂ginibreMeasure n) =
      ∫ z, u.val z ∂ginibreMeasure n := by
  rw [← ginibreFullConstant_one_inner n hn, ← ginibreFullConstant_one_inner n hn]
  have hs := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    (ginibreFullEvolution_selfAdjoint n hn t)
  have he := hs (ginibreFullConstant n hn 1) u
  change inner ℂ (ginibreFullEvolution n hn t (ginibreFullConstant n hn 1)) u =
    inner ℂ (ginibreFullConstant n hn 1) (ginibreFullEvolution n hn t u) at he
  rw [ginibreFullEvolution_constant] at he
  exact he.symm

end
end GinibrePoincare
