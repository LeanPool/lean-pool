/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreFullGeneratorPolynomialIdentification.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorPolynomialGradient
public import LeanPool.GinibrePoincare.Analysis.PolynomialGeneratorWeakCore

/-!
# Ginibre full generator polynomial identification

Part of the diffusion operators and analytic semigroups development of the
Ginibre Poincaré formalization.

Main results: `ginibreFullGenerator_polynomial_eigenvector`.
-/

@[expose] public section

noncomputable section
namespace GinibrePoincare
open MeasureTheory
open scoped ContDiff

/-- Actual symmetric full-space class of each Hermite–Laguerre polynomial. -/
def ginibreFullPolynomialEigenvector (n : ℕ) (hn : 2 ≤ n) (i : PolynomialEigenfunctionData n) :
    ginibreSymmetricL2 n :=
  ⟨polynomialEigenfunctionL2 n hn i, by
    intro σ
    apply Lp.ext
    have hp := (ginibre_measurePreserving_permute σ).quasiMeasurePreserving.ae_eq_comp
      (polynomialEigenfunctionL2_coeFn n hn i)
    filter_upwards [Lp.coeFn_compMeasurePreserving (polynomialEigenfunctionL2 n hn i)
        (ginibre_measurePreserving_permute σ),
      hp, polynomialEigenfunctionL2_coeFn n hn i] with z hperm hcomp hz
    rw [show (ginibrePermutationL2 σ (polynomialEigenfunctionL2 n hn i)) z =
      (polynomialEigenfunctionL2 n hn i) (permute σ z) from hperm]
    change (polynomialEigenfunctionL2 n hn i) (permute σ z) = (polynomialEigenfunctionL2 n hn i) z
    change (polynomialEigenfunctionL2 n hn i) (permute σ z) =
      polynomialEigenfunction n i (permute σ z) at hcomp
    rw [hcomp, hz, polynomialEigenfunction_permute]⟩

private theorem projected_graph {n : ℕ} (hn : 2 ≤ n) (i : PolynomialEigenfunctionData n)
    (T : ℂ →L[ℝ] ℝ) (U V : ginibreFullSymmetricValues n)
    (hU : (U.val : Configuration n → ℝ) =ᵐ[ginibreMeasure n] fun z => T (polynomialEigenfunction n i
        z))
    (hV : (V.val : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
      ginibrePregenerator n (fun z => T (polynomialEigenfunction n i z))) :
    (ginibreFullSymmetricOfReal n U, ginibreFullSymmetricOfReal n V) ∈
      (ginibreFullGenerator n (by omega)).graph := by
  have hpoly : polynomialEigenfunction n i =
      sumRadiusPolynomial n (hermiteLaguerrePolynomial n i.a i.b i.m) := by
    funext z
    exact (sumRadiusPolynomial_hermiteLaguerrePolynomial n i.a i.b i.m z).symm
  have hg := ginibreFull_polynomial_projectedGradient_memLp n hn
    (hermiteLaguerrePolynomial n i.a i.b i.m) T
  rw [← hpoly] at hg
  let g := hg.toLp (ginibreEuclideanGradient (fun z => T (polynomialEigenfunction n i z)))
  have hf : ContDiff ℝ ∞ (fun z => T (polynomialEigenfunction n i z)) :=
    T.contDiff.comp (contDiff_polynomialEigenfunction n i)
  have hu := ginibre_smooth_distributional_gradient n (by omega) U.val g _ hf hU hg.coeFn_toLp
  have hs : IsGinibreSymmetricWeakPair (U.val, g) := by
    intro σ
    refine ⟨U.property σ, ?_⟩
    have hp := ginibreDistributionalGradient_permute (by omega : 0 < n) σ U.val g hu
    rw [U.property σ] at hp
    exact ginibre_distributional_gradient_unique n (by omega) U.val _ _ hp hu
  exact ginibreFullGenerator_smooth_graph (by omega) _ hf U V g hu hs hU hV

/-- All genuine polynomial eigenfunctions lie in the actual full weak
symmetric generator, with their concrete differential eigenvalues. -/
theorem ginibreFullGenerator_polynomial_eigenvector (n : ℕ) (hn : 2 ≤ n)
    (i : PolynomialEigenfunctionData n) :
    (ginibreFullPolynomialEigenvector n hn i,
      -(eigenvalue n i.a i.b i.m : ℝ) • ginibreFullPolynomialEigenvector n hn i) ∈
      (ginibreFullGenerator n (by omega)).graph := by
  let u := ginibreFullPolynomialEigenvector n hn i
  let v := -(eigenvalue n i.a i.b i.m : ℝ) • u
  have huf := polynomialEigenfunctionL2_coeFn n hn i
  have he := polynomialEigenfunction_eigenvalue_equation_ae n hn i.a i.b i.m
  rw [ginibreFullGenerator_graph_iff_real_imag]
  constructor
  · have hu : ((ginibreFullSymmetricRe n u).val : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
        fun z => (polynomialEigenfunction n i z).re := by
      filter_upwards [ginibreFullComplexRe_ae n u.val, huf] with z hz hf
      exact hz.trans (congrArg Complex.re hf)
    have hv : ((ginibreFullSymmetricRe n v).val : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
        ginibrePregenerator n (fun z => (polynomialEigenfunction n i z).re) := by
      rw [show ginibreFullSymmetricRe n v = -(eigenvalue n i.a i.b i.m : ℝ) •
        ginibreFullSymmetricRe n u from map_smul _ _ _]
      filter_upwards [Lp.coeFn_smul (-(eigenvalue n i.a i.b i.m : ℝ))
        (ginibreFullSymmetricRe n u).val, hu, he] with z hs hz hg
      simp only [Submodule.coe_smul]
      rw [hs]
      change -(eigenvalue n i.a i.b i.m : ℝ) * _ = _
      rw [hz]
      have h := congrArg Complex.re hg
      simp [complexGinibrePregenerator, eigenvalue] at h ⊢
      linarith
    have hg := projected_graph hn i Complex.reCLM _ _ hu hv
    obtain ⟨g, hw, hs, heq⟩ := (ginibreFullGenerator_real_graph_iff_exists_gradient (by omega) _
        _).mp hg
    exact (ginibreFullGenerator_real_variational_iff (by omega) _ _ g hw hs).mpr heq
  · have hu : ((ginibreFullSymmetricIm n u).val : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
        fun z => (polynomialEigenfunction n i z).im := by
      filter_upwards [ginibreFullComplexIm_ae n u.val, huf] with z hz hf
      exact hz.trans (congrArg Complex.im hf)
    have hv : ((ginibreFullSymmetricIm n v).val : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
        ginibrePregenerator n (fun z => (polynomialEigenfunction n i z).im) := by
      rw [show ginibreFullSymmetricIm n v = -(eigenvalue n i.a i.b i.m : ℝ) •
        ginibreFullSymmetricIm n u from map_smul _ _ _]
      filter_upwards [Lp.coeFn_smul (-(eigenvalue n i.a i.b i.m : ℝ))
        (ginibreFullSymmetricIm n u).val, hu, he] with z hs hz hg
      simp only [Submodule.coe_smul]
      rw [hs]
      change -(eigenvalue n i.a i.b i.m : ℝ) * _ = _
      rw [hz]
      have h := congrArg Complex.im hg
      simp [complexGinibrePregenerator, eigenvalue] at h ⊢
      linarith
    have hg := projected_graph hn i Complex.imCLM _ _ hu hv
    obtain ⟨g, hw, hs, heq⟩ := (ginibreFullGenerator_real_graph_iff_exists_gradient (by omega) _
        _).mp hg
    exact (ginibreFullGenerator_real_variational_iff (by omega) _ _ g hw hs).mpr heq

end GinibrePoincare
