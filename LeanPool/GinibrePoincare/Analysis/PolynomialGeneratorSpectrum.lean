/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/PolynomialGeneratorSpectrum.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorPolynomialCompatibility
public import LeanPool.GinibrePoincare.Analysis.PolynomialSectorHilbertBasis

/-! # Spectrum containment from the concrete polynomial eigenfunctions

The resolvent definition below is the usual bounded, two-sided inverse of
`zeta - L` on the exact domain of an unbounded operator. Mathlib's algebra
spectrum applies to bounded operators and cannot directly be used here.
-/

@[expose] public section
namespace GinibrePoincare
noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- The ordinary bounded resolvent condition for a graph-defined operator. -/
def HasBoundedGraphResolvent (L : H →ₗ.[ℂ] H) (zeta : ℂ) : Prop :=
  ∃ R : H →L[ℂ] H,
    (∀ f, (R f, zeta • R f - f) ∈ L.graph) ∧
    (∀ u v, (u, v) ∈ L.graph → R (zeta • u - v) = u)

/-- Spectrum of an unbounded operator: the complement of its bounded resolvent set. -/
def graphOperatorSpectrum (L : H →ₗ.[ℂ] H) : Set ℂ :=
  {zeta | ¬ HasBoundedGraphResolvent L zeta}

/-- A nonzero eigenvector prevents a bounded two-sided resolvent. -/
theorem eigenpair_mem_graphOperatorSpectrum (L : H →ₗ.[ℂ] H) (zeta : ℂ)
    (u : H) (hu : u ≠ 0) (hg : (u, zeta • u) ∈ L.graph) :
    zeta ∈ graphOperatorSpectrum L := by
  rintro ⟨R, _, hleft⟩
  have h := hleft u (zeta • u) hg
  rw [sub_self, map_zero] at h
  exact hu h.symm

/-- Corollary 1.5, concrete speed `αₙ = n`, for the actual full symmetric
Ginibre generator and `n ≥ 2`. These are full-space spectral points, although
the eigenvectors lie in the closed sum/radius polynomial sector. -/
theorem ginibreFullGenerator_natural_spectrum_containment (n : ℕ) (hn : 2 ≤ n) :
    {zeta : ℂ | ∃ k : ℕ, zeta = -(2 * (k : ℂ))} ⊆
      graphOperatorSpectrum (ginibreFullGenerator n (by omega)) := by
  rintro zeta ⟨k, rfl⟩
  let i : PolynomialEigenfunctionData n := ⟨k, 0, 0⟩
  have hu : ginibreFullPolynomialEigenvector n hn i ≠ 0 := by
    intro hz
    apply polynomialSectorEigenvector_ne_zero n hn i
    apply Subtype.ext
    change polynomialEigenfunctionL2 n hn i = 0
    exact congrArg (fun x : ginibreSymmetricL2 n => x.val) hz
  apply eigenpair_mem_graphOperatorSpectrum _ _ _ hu
  have hg := ginibreFullGenerator_polynomial_eigenvector n hn i
  have he : -(2 * (k : ℂ)) • ginibreFullPolynomialEigenvector n hn i =
      -(eigenvalue n i.a i.b i.m : ℝ) • ginibreFullPolynomialEigenvector n hn i := by
    apply Subtype.ext
    simp [eigenvalue, i, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rw [he]
  exact hg

/-- The actual generator at paper speed `αₙ`: time scaling by `αₙ / n`
of the previously identified full generator at speed `n`. -/
def ginibreFullGeneratorAtSpeed (n : ℕ) (hn : 0 < n) (alpha : ℝ) :
    ginibreSymmetricL2 n →ₗ.[ℂ] ginibreSymmetricL2 n :=
  (alpha / (n : ℝ) : ℂ) • ginibreFullGenerator n hn

/-- Corollary 1.5 spectrum containment for every positive paper speed,
on the full symmetric `L²` space, for `n ≥ 2`. -/
theorem ginibreFullGeneratorAtSpeed_natural_spectrum_containment
    (n : ℕ) (hn : 2 ≤ n) (alpha : ℝ) (_halpha : 0 < alpha) :
    {zeta : ℂ | ∃ k : ℕ, zeta = (-2 * (alpha / (n : ℝ)) * k : ℝ)} ⊆
      graphOperatorSpectrum (ginibreFullGeneratorAtSpeed n (by omega) alpha) := by
  rintro zeta ⟨k, rfl⟩
  let i : PolynomialEigenfunctionData n := ⟨k, 0, 0⟩
  let u := ginibreFullPolynomialEigenvector n hn i
  have hu : u ≠ 0 := by
    intro hz
    apply polynomialSectorEigenvector_ne_zero n hn i
    apply Subtype.ext
    change polynomialEigenfunctionL2 n hn i = 0
    exact congrArg (fun x : ginibreSymmetricL2 n => x.val) hz
  apply eigenpair_mem_graphOperatorSpectrum _ _ u hu
  rw [ginibreFullGeneratorAtSpeed, LinearPMap.smul_graph]
  refine ⟨(u, -(eigenvalue n i.a i.b i.m : ℝ) • u),
    ginibreFullGenerator_polynomial_eigenvector n hn i, ?_⟩
  simp only [LinearMap.prodMap_apply, LinearMap.id_apply, LinearMap.smul_apply]
  congr 1
  apply Subtype.ext
  simp only [Submodule.coe_smul_of_tower]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ), smul_smul, RCLike.ofReal_eq_complex_ofReal]
  congr 1
  simp [i, eigenvalue]
  ring

end
end GinibrePoincare
