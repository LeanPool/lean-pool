/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreEntireProjectionBridge.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GaussianEntireSpaceClosure
public import LeanPool.GinibrePoincare.Analysis.HolomorphicVandermondeL2Closure
public import LeanPool.GinibrePoincare.Analysis.GinibreConjugationGeometry
public import LeanPool.GinibrePoincare.Analysis.GroundStateDbar
public import LeanPool.GinibrePoincare.Analysis.EntireVandermondeFactorization

/-! # Entire Ginibre representatives and the holomorphic projection space

The paper's entire-function space is connected to the existing polynomial
closure through the actual normalized Vandermonde isometry and actual
Gaussian entire representatives, not through an assumed coefficient condition.
-/

@[expose] public section

open MeasureTheory
open scoped ComplexConjugate
namespace GinibrePoincare
noncomputable section
open ComplexHermite

/-- A genuine entire representative of an actual Ginibre L² class. -/
def IsGinibreEntireRepresentative {n : ℕ}
    (u : Lp ℂ 2 (ginibreMeasure n)) (f : Configuration n → ℂ) : Prop :=
  Differentiable ℂ f ∧ f =ᵐ[ginibreMeasure n] u

/-- The actual symmetric Ginibre entire representative space. -/
def ginibreSymmetricEntireL2 (n : ℕ) : Submodule ℂ (ginibreSymmetricL2 n) where
  carrier := {u | ∃ f, IsGinibreEntireRepresentative u.val f}
  zero_mem' := by
    refine ⟨0, differentiable_const 0, ?_⟩
    exact (Lp.coeFn_zero ℂ 2 (ginibreMeasure n)).symm
  add_mem' := by
    rintro u v ⟨f, hf⟩ ⟨g, hg⟩
    refine ⟨fun z => f z + g z, hf.1.add hg.1, ?_⟩
    filter_upwards [hf.2, hg.2, Lp.coeFn_add u.val v.val] with z hfu hgv huv
    change f z + g z = (u.val + v.val) z
    rw [huv]
    exact congrArg₂ (· + ·) hfu hgv
  smul_mem' := by
    rintro c u ⟨f, hf⟩
    refine ⟨fun z => c * f z, hf.1.const_mul c, ?_⟩
    filter_upwards [hf.2, Lp.coeFn_smul c u.val] with z hfu hcu
    change c * f z = (c • u.val) z
    rw [hcu]
    exact congrArg (c * ·) hfu

/-- Multiplication of an actual entire Ginibre representative by the
normalized Vandermonde gives an actual entire Gaussian representative. -/
theorem ginibreEntireRepresentative_normalizedTransform {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (ginibreMeasure n)) (f : Configuration n → ℂ)
    (hf : IsGinibreEntireRepresentative u f) :
    IsGaussianEntireRepresentative (normalizedVandermondeL2 n hn u)
      (fun z => normalizedVandermondeMultiplier n z * f z) := by
  refine ⟨((differentiable_vandermonde n).const_mul _).mul hf.1, ?_⟩
  have hfu := (complexGaussianMeasure_absolutelyContinuous_ginibreMeasure
    (ginibreMassEvaluation n hn)).ae_eq hf.2
  filter_upwards [hfu, normalizedVandermondeL2_coeFn_public n hn u] with z hfu hU
  rw [hU, hfu]

/-- Every actual symmetric entire Ginibre L² representative belongs to the
constructed closed holomorphic polynomial space. -/
theorem ginibreSymmetricEntire_mem_holomorphic {n : ℕ} (hn : 0 < n)
    (u : ginibreSymmetricL2 n) (f : Configuration n → ℂ)
    (hf : IsGinibreEntireRepresentative u.val f) :
    u ∈ ginibreSymmetricHolomorphicPolynomialClosedSpan n hn := by
  let U := vandermondeSymmetricAlternatingEquiv n hn
  have hGrep := ginibreEntireRepresentative_normalizedTransform hn u.val f hf
  have hGzero : (U u).val ∈ hermiteAntiDegreeClosedSpan n hn 0 := by
    have he := gaussianEntireRepresentative_zeroMode_eq hn (U u).val _ hGrep
    rw [gaussianHermiteMode_eq_antiDegreeProjection] at he
    exact Submodule.starProjection_eq_self_iff.mp he
  have hG : U u ∈ gaussianAlternatingZeroModeClosedSpan n hn := by
    change U u ∈ (gaussianAlternatingZeroModeClosedSpan n hn).toSubmodule
    rw [gaussianAlternatingZeroModeClosedSpan_eq_hermiteZeroMode_comap]
    exact hGzero
  have him : U u ∈ (ginibreSymmetricHolomorphicPolynomialClosedSpan n hn).toSubmodule.map
      U.toLinearMap := by
    rw [map_ginibreSymmetricHolomorphicPolynomialClosedSpan]
    exact hG
  obtain ⟨v, hv, heq⟩ := him
  have hvu : v = u := U.injective heq
  exact hvu ▸ hv

/-- The representative-defined entire space is contained in the actual
closed holomorphic polynomial space. -/
theorem ginibreSymmetricEntireL2_le_holomorphic (n : ℕ) (hn : 0 < n) :
    ginibreSymmetricEntireL2 n ≤
      (ginibreSymmetricHolomorphicPolynomialClosedSpan n hn).toSubmodule := by
  rintro u ⟨f, hf⟩
  exact ginibreSymmetricEntire_mem_holomorphic hn u f hf

/-- Ambient-space version used by the literal projection formulas. -/
theorem ginibreSymmetricEntire_mem_holomorphicAmbient {n : ℕ} (hn : 0 < n)
    (u : ginibreSymmetricL2 n) (f : Configuration n → ℂ)
    (hf : IsGinibreEntireRepresentative u.val f) :
    u.val ∈ ginibreHolomorphicAmbientClosedSpan n hn :=
  ⟨u, ginibreSymmetricEntire_mem_holomorphic hn u f hf, rfl⟩

/-- The paper's divisible holomorphic space on symmetric Ginibre L²:
the actual Vandermonde transform has an entire Gaussian representative. -/
def ginibreSymmetricDivisibleEntireL2 (n : ℕ) (hn : 0 < n) :
    Submodule ℂ (ginibreSymmetricL2 n) :=
  (gaussianEntireL2 n).comap ((normalizedVandermondeL2 n hn).toLinearMap.comp
    (ginibreSymmetricL2 n).subtype)

/-- Exact identification of the paper's Vandermonde-defined entire space
with the previously constructed closed polynomial space. This uses the
literal defining condition, without assuming entire divisibility. -/
theorem ginibreSymmetricDivisibleEntireL2_eq_holomorphic (n : ℕ) (hn : 0 < n) :
    ginibreSymmetricDivisibleEntireL2 n hn =
      (ginibreSymmetricHolomorphicPolynomialClosedSpan n hn).toSubmodule := by
  ext u
  let U := vandermondeSymmetricAlternatingEquiv n hn
  change (U u).val ∈ gaussianEntireL2 n ↔
    u ∈ ginibreSymmetricHolomorphicPolynomialClosedSpan n hn
  rw [gaussianEntireL2_eq_zeroModeClosedSpan n hn]
  constructor
  · intro hGzero
    have hG : U u ∈ gaussianAlternatingZeroModeClosedSpan n hn := by
      change U u ∈ (gaussianAlternatingZeroModeClosedSpan n hn).toSubmodule
      rw [gaussianAlternatingZeroModeClosedSpan_eq_hermiteZeroMode_comap]
      exact hGzero
    have him : U u ∈ (ginibreSymmetricHolomorphicPolynomialClosedSpan n hn).toSubmodule.map
        U.toLinearMap := by
      rw [map_ginibreSymmetricHolomorphicPolynomialClosedSpan]
      exact hG
    obtain ⟨v, hv, heq⟩ := him
    have hvu : v = u := U.injective heq
    exact hvu ▸ hv
  · intro hu
    have hG : U u ∈ gaussianAlternatingZeroModeClosedSpan n hn := by
      change U u ∈ (gaussianAlternatingZeroModeClosedSpan n hn).toSubmodule
      rw [← map_ginibreSymmetricHolomorphicPolynomialClosedSpan]
      exact ⟨u, hu, rfl⟩
    exact gaussianAlternatingZeroModeClosedSpan_le_hermiteZeroMode n hn hG

/-- The actual divisible entire-function subspace in ambient Ginibre L². -/
def ginibreDivisibleEntireL2 (n : ℕ) (hn : 0 < n) :
    Submodule ℂ (Lp ℂ 2 (ginibreMeasure n)) :=
  (ginibreSymmetricDivisibleEntireL2 n hn).map (ginibreSymmetricL2 n).subtype

/-- The closed subspace used by every projection theorem is precisely
`H_n^div` as defined by the paper using actual entire Gaussian transforms. -/
theorem ginibreDivisibleEntireL2_eq_holomorphicAmbient (n : ℕ) (hn : 0 < n) :
    ginibreDivisibleEntireL2 n hn = (ginibreHolomorphicAmbientClosedSpan n hn).toSubmodule := by
  rw [ginibreDivisibleEntireL2, ginibreSymmetricDivisibleEntireL2_eq_holomorphic]
  rfl

theorem isClosed_ginibreDivisibleEntireL2 (n : ℕ) (hn : 0 < n) :
    IsClosed (ginibreDivisibleEntireL2 n hn : Set (Lp ℂ 2 (ginibreMeasure n))) := by
  rw [ginibreDivisibleEntireL2_eq_holomorphicAmbient]
  exact (ginibreHolomorphicAmbientClosedSpan n hn).isClosed

/-- Every holomorphic projection has an actual entire Vandermonde
transform, including arbitrary complex symmetric L² inputs. -/
theorem ginibreHolomorphicProjection_mem_divisibleEntire (n : ℕ) (hn : 0 < n)
    (u : Lp ℂ 2 (ginibreMeasure n)) :
    (ginibreHolomorphicAmbientClosedSpan n hn).starProjection u ∈
      ginibreDivisibleEntireL2 n hn := by
  rw [ginibreDivisibleEntireL2_eq_holomorphicAmbient]
  exact Submodule.starProjection_apply_mem _ _

/-- Every actual divisible entire class admits a symmetric entire representative. -/
theorem ginibreDivisibleEntire_exists_symmetricRepresentative {n : ℕ} (hn : 0 < n)
    (u : ginibreSymmetricL2 n) (hu : u ∈ ginibreSymmetricDivisibleEntireL2 n hn) :
    ∃ g, IsSymmetric g ∧ IsGinibreEntireRepresentative u.val g := by
    change normalizedVandermondeL2 n hn u.val ∈ gaussianEntireL2 n at hu
    obtain ⟨f, hf⟩ := hu
    have halt : normalizedVandermondeL2 n hn u.val ∈ gaussianAlternatingL2 n :=
      (vandermondeSymmetricAlternatingEquiv n hn u).property
    obtain ⟨g, hg, hgs, hfac⟩ :=
      gaussianEntireAlternatingRepresentative_vandermonde_factorization hn _ halt f hf
    refine ⟨fun z => (groundStateNormalization n : ℂ) * g z, ?_, hg.const_mul _, ?_⟩
    · intro σ z
      exact congrArg ((groundStateNormalization n : ℂ) * ·) (hgs σ z)
    have heq := (ginibreMeasure_absolutelyContinuous_complexGaussianMeasure n).ae_eq
      (hf.2.trans (normalizedVandermondeL2_coeFn_public n hn u.val))
    have hout : ∀ᵐ z ∂ginibreMeasure n, z ∉ collisionSet n :=
      (ginibreMeasure_absolutelyContinuous_complexGaussianMeasure n).ae_le
        (show ∀ᵐ z ∂complexGaussianMeasure n, z ∉ collisionSet n from by
          rw [ae_iff]
          rw [show {z : Configuration n | ¬z ∉ collisionSet n} = collisionSet n by
              ext z; simp only [Set.mem_ofPred_eq, not_not]]
          exact complexGaussianMeasure_collisionSet n)
    filter_upwards [heq, hout] with z hz hout
    have hv : vandermonde z ≠ 0 := fun hv => hout ((vandermonde_eq_zero_iff z).mp hv)
    rw [hfac z] at hz
    unfold normalizedVandermondeMultiplier at hz
    have ha : (groundStateNormalization n : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (groundStateNormalization_ne_zero_of_pos hn)
    field_simp at hz
    simpa only [mul_comm] using hz

/-- Literal equivalence of the representative and Vandermonde-transform spaces. -/
theorem ginibreSymmetricEntireL2_eq_divisibleEntire (n : ℕ) (hn : 0 < n) :
    ginibreSymmetricEntireL2 n = ginibreSymmetricDivisibleEntireL2 n hn := by
  apply le_antisymm
  · rw [ginibreSymmetricDivisibleEntireL2_eq_holomorphic]
    exact ginibreSymmetricEntireL2_le_holomorphic n hn
  · intro u hu
    obtain ⟨g, _, hg⟩ := ginibreDivisibleEntire_exists_symmetricRepresentative hn u hu
    exact ⟨g, hg⟩

theorem ginibreSymmetricEntireL2_eq_holomorphic (n : ℕ) (hn : 0 < n) :
    ginibreSymmetricEntireL2 n =
      (ginibreSymmetricHolomorphicPolynomialClosedSpan n hn).toSubmodule := by
  rw [ginibreSymmetricEntireL2_eq_divisibleEntire,
    ginibreSymmetricDivisibleEntireL2_eq_holomorphic]

/-- The actual symmetric entire Ginibre L² space is closed. -/
theorem isClosed_ginibreSymmetricEntireL2 (n : ℕ) (hn : 0 < n) :
    IsClosed (ginibreSymmetricEntireL2 n : Set (ginibreSymmetricL2 n)) := by
  rw [ginibreSymmetricEntireL2_eq_holomorphic n hn]
  exact (ginibreSymmetricHolomorphicPolynomialClosedSpan n hn).isClosed

end
end GinibrePoincare

