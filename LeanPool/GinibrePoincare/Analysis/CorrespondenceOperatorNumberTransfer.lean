/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceOperatorNumberTransfer.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceOperatorNumberSquareRoot
public import LeanPool.GinibrePoincare.Analysis.GinibreEqualityWeakDeficit
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorCoreCompatibility
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorSpectrum
public import LeanPool.GinibrePoincare.Analysis.GinibreFullSemigroupConstants
public import LeanPool.GinibrePoincare.Analysis.GinibreMixedGreenIdentity
public import LeanPool.GinibrePoincare.Analysis.GinibreZeroPairCutoff
public import LeanPool.GinibrePoincare.Analysis.RadialInteriorWeakSobolevApproximation
public import LeanPool.GinibrePoincare.Analysis.RadialSmoothSobolevApproximation
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
/-!
# Correspondence operator number transfer

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `correspondenceOperatorNumber_ginibre_shifted_root_deficit`.
-/

@[expose] public section
open MeasureTheory
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
open ComplexHermite

/-- Removing the literal holomorphic projection preserves every actual weak
antiholomorphic derivative. -/
theorem correspondenceOperatorNumber_complement_weak {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n))
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hD : ∀ j, IsGaussianWeakDbar n g (D j) j) :
    (∀j, IsGaussianWeakDbar n (g-gaussianHermiteMode hn 0 g) (D j) j) ∧
      gaussianHermiteMode hn 0 (g-gaussianHermiteMode hn 0 g)=0 ∧
      ‖g‖^2=‖g-gaussianHermiteMode hn 0 g‖^2+‖gaussianHermiteMode hn 0 g‖^2 := by
  have hc (pq : HermiteMultiIndex n) :
      gaussianHermiteCoefficient hn (g-gaussianHermiteMode hn 0 g) pq=
      gaussianHermiteCoefficient hn g pq-
        (if totalAntiDegree pq=0 then gaussianHermiteCoefficient hn g pq else 0) := by
    rw [gaussianHermiteCoefficient_eq_inner, inner_sub_right, inner_basis_gaussianHermiteMode,
      ← gaussianHermiteCoefficient_eq_inner]
  refine ⟨?_,?_,?_⟩
  · intro j
    apply (gaussianWeakDbar_iff_hermiteCoefficient hn _ _ j).mpr
    intro pq
    rw [hc, gaussianWeakDbar_hermiteCoefficient hn g (D j) j (hD j) pq]
    have hd : totalAntiDegree (raiseHermiteIndex j pq)≠0 := by
      have hh := Finset.single_le_sum (fun i _=>Nat.zero_le ((raiseHermiteIndex j pq).2 i))
        (Finset.mem_univ j)
      simp only [raiseHermiteIndex, raiseAt, Function.update_self] at hh
      change (∑i : Fin n, Function.update pq.2 j (pq.2 j+1) i)≠0
      omega
    rw [ite_eq_right hd, sub_zero]
  · apply gaussianHermiteCoefficient_ext hn
    intro pq
    rw [gaussianHermiteCoefficient_eq_inner, inner_basis_gaussianHermiteMode,
      hc]
    by_cases hd : totalAntiDegree pq=0 <;> simp [hd, gaussianHermiteCoefficient_eq_inner]
  · have he := (hasSum_norm_sq_gaussianHermiteCoefficient hn
      (g-gaussianHermiteMode hn 0 g)).add
        (hasSum_norm_sq_gaussianHermiteCoefficient hn (gaussianHermiteMode hn 0 g))
    apply (hasSum_norm_sq_gaussianHermiteCoefficient hn g).unique
    apply he.congr_fun
    intro pq
    rw [hc, gaussianHermiteCoefficient_eq_inner hn (gaussianHermiteMode hn 0 g),
      inner_basis_gaussianHermiteMode]
    by_cases hd : totalAntiDegree pq=0 <;> simp [hd]

/-- Literal formula (6.14), on the entire actual symmetric ordinary weak H¹
domain, with its genuine maximal shifted spectral square-root vector. -/
theorem correspondenceOperatorNumber_ginibre_shifted_root_deficit {n : ℕ} (hn : 0 < n)
    (f : GinibreFullValueL2 n) (G : GinibreFullGradientL2 n)
    (hG : IsGinibreDistributionalGradient n f G) (hSym : IsGinibreSymmetricWeakPair (f, G)) :
    ∃s : Lp ℂ 2 (complexGaussianMeasure n),
      (ginibreFullCenteredTransform n hn f-
          gaussianHermiteMode hn 0 (ginibreFullCenteredTransform n hn f), s)∈
        (correspondenceOperatorNumberSpectral n hn (fun x=>Real.sqrt (x-n))).graph ∧
      ginibreWeakEnergy n G-2*ginibreL2Variance n hn f=
        2*‖ginibreFullHolomorphicRemainder n hn f‖^2+(4/(n : ℝ))*‖s‖^2 := by
  obtain ⟨hc, hsc⟩ := ginibreFullCenter_weak_pair hn f G hG hSym
  let g := ginibreFullCenteredTransform n hn f
  let D : Fin n→Lp ℂ 2 (complexGaussianMeasure n) := fun j=>ginibreFullTransformedDbar n hn j G
  have hD : ∀j, IsGaussianWeakDbar n g (D j) j := by
    intro j
    apply (gaussianWeakDbar_iff_hermiteCoefficient hn _ _ j).mpr
    exact ginibreFullTransformedDbar_weak_coefficient hn (ginibreFullCenter n hn f) G hc hsc j
  obtain ⟨hDu, hu, hNorm⟩ := correspondenceOperatorNumber_complement_weak hn g D hD
  obtain ⟨s, hs, hE⟩ := correspondenceOperatorNumber_shifted_sqrt_paper_energy hn
    (g-gaussianHermiteMode hn 0 g) D hDu hu
  refine ⟨s, hs,?_⟩
  have hQ := ginibreFullTransformedDbar_norm_sum hn G
  have hV : ‖g‖^2=ginibreL2Variance n hn f := by
    dsimp [g, ginibreFullCenteredTransform]
    rw [(normalizedVandermondeL2 n hn).norm_map, ginibreFullCenteredValue_norm_sq]
  have hP := ginibreFullWeak_zero_mode_norm hn f G hG hSym
  have hgeom := ginibreFullWeak_holomorphic_geometry hn f G hG hSym
  change ‖gaussianHermiteMode hn 0 g‖^2=_ at hP
  rw [hV, hP] at hNorm
  change (∑j : Fin n, ‖D j‖^2)=(1/4 : ℝ)*‖G‖^2 at hQ
  unfold ginibreWeakEnergy
  have hnR : (0 : ℝ)<n := by exact_mod_cast hn
  field_simp
  nlinarith [hQ, hE, hNorm, hgeom]
end
end GinibrePoincare
