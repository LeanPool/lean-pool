/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/HolomorphicVandermondeL2Closure.lean.
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

public import LeanPool.GinibrePoincare.Analysis.HolomorphicVandermondeDivision
public import LeanPool.GinibrePoincare.Analysis.HermiteEnergy
public import LeanPool.GinibrePoincare.Analysis.VandermondeL2Inverse

/-! # Closed zero-mode Vandermonde correspondence -/


@[expose] public section


open MeasureTheory

namespace GinibrePoincare
namespace ComplexHermite

noncomputable section

local instance completeSpace_gaussianAlternatingL2 (n : ℕ) :
    CompleteSpace (gaussianAlternatingL2 n) :=
  (isClosed_gaussianAlternatingL2 n).completeSpace_coe

local instance completeSpace_ginibreSymmetricL2 (n : ℕ) :
    CompleteSpace (ginibreSymmetricL2 n) :=
  (isClosed_ginibreSymmetricL2 n).completeSpace_coe

/-- The signed finite average of coordinate permutations on Gaussian `L²`. -/
def gaussianAlternationOperator (n : ℕ) :
    Lp ℂ 2 (complexGaussianMeasure n) →L[ℂ]
      Lp ℂ 2 (complexGaussianMeasure n) :=
  ((Fintype.card (ParticlePermutation n) : ℂ)⁻¹) •
    ∑ σ : ParticlePermutation n,
      (permutationSign σ) •
        (gaussianPermutationL2 σ).toContinuousLinearMap

@[simp] theorem gaussianAlternationOperator_apply (n : ℕ)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) :
    gaussianAlternationOperator n u =
      ((Fintype.card (ParticlePermutation n) : ℂ)⁻¹) •
        ∑ σ : ParticlePermutation n,
          (permutationSign σ) • gaussianPermutationL2 σ u := by
  simp [gaussianAlternationOperator]

private theorem permutationSign_mul_self {n : ℕ}
    (σ : ParticlePermutation n) :
    (permutationSign σ : ℂ) * permutationSign σ = 1 := by
  unfold permutationSign
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
    simp [h]

/-- The signed average fixes every alternating Gaussian vector. -/
theorem gaussianAlternationOperator_eq_self_of_mem {n : ℕ}
    {u : Lp ℂ 2 (complexGaussianMeasure n)}
    (hu : u ∈ gaussianAlternatingL2 n) :
    gaussianAlternationOperator n u = u := by
  change ∀ σ : ParticlePermutation n,
    gaussianPermutationL2 σ u = permutationSign σ • u at hu
  rw [gaussianAlternationOperator_apply]
  simp_rw [hu, smul_smul, permutationSign_mul_self, one_smul]
  rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ]
  simp only [Finset.card_univ]
  have hcard : (Fintype.card (ParticlePermutation n) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [← mul_smul, inv_mul_cancel₀ hcard, one_smul]

/-- Coordinate relabelling simply reindexes both Hermite multi-indices. -/
theorem multivariateNormalized_permute (n : ℕ) (hn : 0 < n)
    (σ : ParticlePermutation n) (p q : Fin n → ℕ) (z : Configuration n) :
    multivariateNormalized n hn p q (permute σ z) =
      multivariateNormalized n hn (p ∘ σ.symm) (q ∘ σ.symm) z := by
  unfold multivariateNormalized
  rw [← Equiv.prod_comp σ.symm]
  apply Finset.prod_congr rfl
  intro i hi
  simp []

/-- The Gaussian permutation operator reindexes Hermite basis vectors. -/
theorem gaussianPermutationL2_hermiteL2Family (n : ℕ) (hn : 0 < n)
    (σ : ParticlePermutation n) (p q : Fin n → ℕ) :
    gaussianPermutationL2 σ (hermiteL2Family n hn (p, q)) =
      hermiteL2Family n hn (p ∘ σ.symm, q ∘ σ.symm) := by
  apply Lp.ext
  have hsourcecomp :=
    (gaussian_measurePreserving_permute σ).quasiMeasurePreserving.ae_eq_comp
      (hermiteL2Family_coeFn n hn (p, q))
  filter_upwards [Lp.coeFn_compMeasurePreserving
      (hermiteL2Family n hn (p, q))
      (gaussian_measurePreserving_permute σ),
    hsourcecomp,
    hermiteL2Family_coeFn n hn (p ∘ σ.symm, q ∘ σ.symm)] with z hcomp hsource htarget
  rw [show (gaussianPermutationL2 σ (hermiteL2Family n hn (p, q))) z =
      hermiteL2Family n hn (p, q) (permute σ z) by exact hcomp]
  change hermiteL2Family n hn (p, q) (permute σ z) =
    multivariateNormalized n hn p q (permute σ z) at hsource
  rw [hsource, htarget, multivariateNormalized_permute]

/-- Every coordinate permutation preserves each finite antiholomorphic-degree
Hermite span. -/
theorem gaussianPermutationL2_mem_hermiteAntiDegreeSpan
    (n : ℕ) (hn : 0 < n) (d : ℕ) (σ : ParticlePermutation n)
    {u : Lp ℂ 2 (complexGaussianMeasure n)}
    (hu : u ∈ hermiteAntiDegreeSpan n hn d) :
    gaussianPermutationL2 σ u ∈ hermiteAntiDegreeSpan n hn d := by
  unfold hermiteAntiDegreeSpan at hu ⊢
  refine Submodule.span_induction
    (p := fun x _ ↦ gaussianPermutationL2 σ x ∈
      Submodule.span ℂ (hermiteL2Family n hn ''
        {pq | totalAntiDegree pq = d}))
    ?_ (by simp) ?_ ?_ hu
  · intro y hy
    obtain ⟨⟨p, q⟩, hpq, rfl⟩ := hy
    rw [gaussianPermutationL2_hermiteL2Family]
    apply Submodule.subset_span
    refine ⟨(p ∘ σ.symm, q ∘ σ.symm), ?_, rfl⟩
    change (∑ i, q (σ.symm i)) = d
    exact (Equiv.sum_comp σ.symm q).trans hpq
  · intro x y hx hy hx' hy'
    rw [map_add]
    exact add_mem hx' hy'
  · intro a x hx hx'
    rw [map_smul]
    exact Submodule.smul_mem _ _ hx'

/-- Consequently the signed finite average preserves every finite
antiholomorphic-degree Hermite span. -/
theorem gaussianAlternationOperator_mem_hermiteAntiDegreeSpan
    (n : ℕ) (hn : 0 < n) (d : ℕ)
    {u : Lp ℂ 2 (complexGaussianMeasure n)}
    (hu : u ∈ hermiteAntiDegreeSpan n hn d) :
    gaussianAlternationOperator n u ∈ hermiteAntiDegreeSpan n hn d := by
  rw [gaussianAlternationOperator_apply]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro σ hσ
  apply Submodule.smul_mem
  exact gaussianPermutationL2_mem_hermiteAntiDegreeSpan n hn d σ hu

/-- Gaussian coordinate pullback is an antihomomorphism of the permutation
group (the outer pullback appears on the left of the product). -/
theorem gaussianPermutationL2_comp_apply {n : ℕ}
    (τ σ : ParticlePermutation n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) :
    gaussianPermutationL2 τ (gaussianPermutationL2 σ u) =
      gaussianPermutationL2 (τ * σ) u := by
  unfold gaussianPermutationL2
  change (Lp.compMeasurePreserving (permute τ)
      (gaussian_measurePreserving_permute τ))
      ((Lp.compMeasurePreserving (permute σ)
        (gaussian_measurePreserving_permute σ)) u) = _
  rw [← Lp.compMeasurePreserving_comp_apply]
  have hfun : permute σ ∘ permute τ = permute (τ * σ) := by
    funext z
    ext i
    simp [permute]
  cases hfun
  rfl

/-- The complex-valued permutation sign is multiplicative. -/
theorem permutationSign_mul {n : ℕ} (τ σ : ParticlePermutation n) :
    permutationSign (τ * σ) = permutationSign τ * permutationSign σ := by
  simp [permutationSign, Equiv.Perm.sign_mul]

/-- The signed average transforms according to the sign character. -/
theorem gaussianPermutationL2_gaussianAlternationOperator {n : ℕ}
    (τ : ParticlePermutation n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) :
    gaussianPermutationL2 τ (gaussianAlternationOperator n u) =
      permutationSign τ • gaussianAlternationOperator n u := by
  rw [gaussianAlternationOperator_apply, map_smul, map_sum]
  simp_rw [map_smul, gaussianPermutationL2_comp_apply]
  have hsum :
      (∑ σ : ParticlePermutation n,
          permutationSign σ • gaussianPermutationL2 (τ * σ) u) =
        permutationSign τ •
          ∑ σ : ParticlePermutation n,
            permutationSign σ • gaussianPermutationL2 σ u := by
    calc
      _ = ∑ σ : ParticlePermutation n,
          permutationSign τ • (permutationSign (τ * σ) •
            gaussianPermutationL2 (τ * σ) u) := by
        apply Finset.sum_congr rfl
        intro σ hσ
        rw [permutationSign_mul, smul_smul]
        have hs := permutationSign_mul_self τ
        rw [← mul_assoc, hs, one_mul]
      _ = permutationSign τ •
          ∑ σ : ParticlePermutation n,
            permutationSign (τ * σ) •
              gaussianPermutationL2 (τ * σ) u := by
        rw [Finset.smul_sum]
      _ = _ := by
        change permutationSign τ •
          ∑ σ, (fun ρ : ParticlePermutation n ↦
            permutationSign ρ • gaussianPermutationL2 ρ u)
              ((Equiv.mulLeft τ) σ) = _
        congr 1
        exact Equiv.sum_comp (Equiv.mulLeft τ)
          (fun ρ : ParticlePermutation n ↦
            permutationSign ρ • gaussianPermutationL2 ρ u)
  rw [hsum, smul_smul]
  module

/-- The image of the signed average is alternating. -/
theorem gaussianAlternationOperator_mem (n : ℕ)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) :
    gaussianAlternationOperator n u ∈ gaussianAlternatingL2 n := by
  intro τ
  exact gaussianPermutationL2_gaussianAlternationOperator τ u

/-- Hence the signed average fixes exactly the alternating Gaussian vectors. -/
theorem gaussianAlternationOperator_eq_self_iff {n : ℕ}
    (u : Lp ℂ 2 (complexGaussianMeasure n)) :
    gaussianAlternationOperator n u = u ↔ u ∈ gaussianAlternatingL2 n := by
  constructor
  · intro h
    rw [← h]
    exact gaussianAlternationOperator_mem n u
  · exact gaussianAlternationOperator_eq_self_of_mem

/-- Alternating Gaussian vectors which are finite linear combinations of
Hermite tensors of antiholomorphic degree zero. -/
def gaussianAlternatingFiniteZeroModeSpan (n : ℕ) (hn : 0 < n) :
    Submodule ℂ (gaussianAlternatingL2 n) :=
  (hermiteAntiDegreeSpan n hn 0).comap
    (gaussianAlternatingL2 n).subtype

/-- The closed alternating part of the degree-zero Hermite span. -/
def gaussianAlternatingZeroModeClosedSpan (n : ℕ) (hn : 0 < n) :
    ClosedSubmodule ℂ (gaussianAlternatingL2 n) where
  toSubmodule := (gaussianAlternatingFiniteZeroModeSpan n hn).topologicalClosure
  isClosed' := (gaussianAlternatingFiniteZeroModeSpan n hn).isClosed_topologicalClosure

/-- Symmetric Ginibre finite holomorphic-polynomial vectors, defined exactly
as inverse normalized-Vandermonde transforms of alternating finite zero-mode
Hermite vectors.  The coefficient-level division theorem identifies these
inverse transforms with symmetric holomorphic polynomial evaluations. -/
def ginibreSymmetricHolomorphicPolynomialSpan (n : ℕ) (hn : 0 < n) :
    Submodule ℂ (ginibreSymmetricL2 n) :=
  (gaussianAlternatingFiniteZeroModeSpan n hn).map
    (vandermondeSymmetricAlternatingEquiv n hn).symm.toLinearMap

/-- Closure of the symmetric holomorphic-polynomial Ginibre vectors. -/
def ginibreSymmetricHolomorphicPolynomialClosedSpan (n : ℕ) (hn : 0 < n) :
    ClosedSubmodule ℂ (ginibreSymmetricL2 n) where
  toSubmodule :=
    (ginibreSymmetricHolomorphicPolynomialSpan n hn).topologicalClosure
  isClosed' :=
    (ginibreSymmetricHolomorphicPolynomialSpan n hn).isClosed_topologicalClosure

theorem map_ginibreSymmetricHolomorphicPolynomialSpan (n : ℕ) (hn : 0 < n) :
    (ginibreSymmetricHolomorphicPolynomialSpan n hn).map
        (vandermondeSymmetricAlternatingEquiv n hn).toLinearMap =
      gaussianAlternatingFiniteZeroModeSpan n hn := by
  ext v
  constructor
  · rintro ⟨u, ⟨w, hw, rfl⟩, rfl⟩
    simpa using hw
  · intro hv
    refine ⟨(vandermondeSymmetricAlternatingEquiv n hn).symm v, ?_, by simp⟩
    exact ⟨v, hv, rfl⟩

/-- The unitary Vandermonde equivalence maps the closure of symmetric
holomorphic polynomial vectors onto the closed alternating zero mode. -/
theorem map_ginibreSymmetricHolomorphicPolynomialClosedSpan
    (n : ℕ) (hn : 0 < n) :
    (ginibreSymmetricHolomorphicPolynomialClosedSpan n hn).toSubmodule.map
        (vandermondeSymmetricAlternatingEquiv n hn).toLinearMap =
      (gaussianAlternatingZeroModeClosedSpan n hn).toSubmodule := by
  apply le_antisymm
  · refine (Submodule.topologicalClosure_map
      (vandermondeSymmetricAlternatingEquiv n hn).toLinearIsometry.toContinuousLinearMap
      (ginibreSymmetricHolomorphicPolynomialSpan n hn)).trans ?_
    change ((ginibreSymmetricHolomorphicPolynomialSpan n hn).map
      (vandermondeSymmetricAlternatingEquiv n hn).toLinearMap).topologicalClosure ≤
        (gaussianAlternatingFiniteZeroModeSpan n hn).topologicalClosure
    rw [map_ginibreSymmetricHolomorphicPolynomialSpan]
  · intro v hv
    change v ∈ (gaussianAlternatingFiniteZeroModeSpan n hn).topologicalClosure at hv
    have hback :
        (vandermondeSymmetricAlternatingEquiv n hn).symm v ∈
          (ginibreSymmetricHolomorphicPolynomialSpan n hn).topologicalClosure := by
      apply (Submodule.topologicalClosure_map
        (vandermondeSymmetricAlternatingEquiv n hn).symm.toLinearIsometry.toContinuousLinearMap
        (gaussianAlternatingFiniteZeroModeSpan n hn))
      exact ⟨v, hv, rfl⟩
    exact ⟨(vandermondeSymmetricAlternatingEquiv n hn).symm v, hback, by simp⟩

/-- In particular, the closed alternating zero mode embeds in the ambient
closed degree-zero Hermite span. -/
theorem gaussianAlternatingZeroModeClosedSpan_le_hermiteZeroMode
    (n : ℕ) (hn : 0 < n) :
    (gaussianAlternatingZeroModeClosedSpan n hn).toSubmodule ≤
      (hermiteAntiDegreeClosedSpan n hn 0).toSubmodule.comap
        (gaussianAlternatingL2 n).subtype := by
  apply Submodule.topologicalClosure_minimal
  · intro v hv
    exact (hermiteAntiDegreeSpan n hn 0).le_topologicalClosure hv
  · exact (hermiteAntiDegreeClosedSpan n hn 0).isClosed.preimage
      (gaussianAlternatingL2 n).subtypeL.continuous

/-- Alternation of finite approximants proves that the closed alternating
zero mode is exactly the intersection of the full closed zero mode with the
alternating Gaussian subspace. -/
theorem gaussianAlternatingZeroModeClosedSpan_eq_hermiteZeroMode_comap
    (n : ℕ) (hn : 0 < n) :
    (gaussianAlternatingZeroModeClosedSpan n hn).toSubmodule =
      (hermiteAntiDegreeClosedSpan n hn 0).toSubmodule.comap
        (gaussianAlternatingL2 n).subtype := by
  apply le_antisymm
  · exact gaussianAlternatingZeroModeClosedSpan_le_hermiteZeroMode n hn
  · intro v hv
    change v.1 ∈ (hermiteAntiDegreeSpan n hn 0).topologicalClosure at hv
    have himage : gaussianAlternationOperator n v.1 ∈
        closure (gaussianAlternationOperator n ''
          (hermiteAntiDegreeSpan n hn 0 :
            Set (Lp ℂ 2 (complexGaussianMeasure n)))) :=
      image_closure_subset_closure_image
        (gaussianAlternationOperator n).continuous ⟨v.1, hv, rfl⟩
    rw [gaussianAlternationOperator_eq_self_of_mem v.2] at himage
    have hsubset :
        gaussianAlternationOperator n ''
            (hermiteAntiDegreeSpan n hn 0 :
              Set (Lp ℂ 2 (complexGaussianMeasure n))) ⊆
          ((fun w : gaussianAlternatingL2 n ↦ w.1) ''
            (gaussianAlternatingFiniteZeroModeSpan n hn :
              Set (gaussianAlternatingL2 n))) := by
      rintro _ ⟨u, hu, rfl⟩
      let w : gaussianAlternatingL2 n :=
        ⟨gaussianAlternationOperator n u,
          gaussianAlternationOperator_mem n u⟩
      refine ⟨w, ?_, rfl⟩
      exact gaussianAlternationOperator_mem_hermiteAntiDegreeSpan n hn 0 hu
    have hclosure := closure_mono hsubset himage
    have hclosedEmbedding : Topology.IsClosedEmbedding
        (fun w : gaussianAlternatingL2 n ↦ w.1) :=
      (isClosed_gaussianAlternatingL2 n).isClosedEmbedding_subtypeVal
    rw [hclosedEmbedding.closure_image_eq] at hclosure
    obtain ⟨w, hw, hwv⟩ := hclosure
    have : w = v := Subtype.ext hwv
    subst w
    exact hw

/-! ## Closed holomorphic projectors -/

/-- Orthogonal projection of symmetric Ginibre `L²` onto the closed
holomorphic-polynomial subspace. -/
def ginibreSymmetricHolomorphicProjection (n : ℕ) (hn : 0 < n) :
    ginibreSymmetricL2 n →L[ℂ] ginibreSymmetricL2 n :=
  (ginibreSymmetricHolomorphicPolynomialClosedSpan n hn).starProjection

/-- Orthogonal projection of alternating Gaussian `L²` onto its closed
degree-zero Hermite subspace. -/
def gaussianAlternatingZeroModeProjection (n : ℕ) (hn : 0 < n) :
    gaussianAlternatingL2 n →L[ℂ] gaussianAlternatingL2 n :=
  ((ginibreSymmetricHolomorphicPolynomialClosedSpan n hn).toSubmodule.map
    ((vandermondeSymmetricAlternatingEquiv n hn).toLinearEquiv :
      ginibreSymmetricL2 n →ₗ[ℂ] gaussianAlternatingL2 n)).starProjection

/-- The Vandermonde unitary intertwines the two closed-subspace
projections. -/
theorem vandermondeEquiv_intertwines_holomorphicProjection
    (n : ℕ) (hn : 0 < n) (u : ginibreSymmetricL2 n) :
    vandermondeSymmetricAlternatingEquiv n hn
        (ginibreSymmetricHolomorphicProjection n hn u) =
      gaussianAlternatingZeroModeProjection n hn
        (vandermondeSymmetricAlternatingEquiv n hn u) := by
  unfold ginibreSymmetricHolomorphicProjection
    gaussianAlternatingZeroModeProjection
  simpa only [LinearIsometryEquiv.symm_apply_apply] using
    (Submodule.starProjection_map_apply
    (vandermondeSymmetricAlternatingEquiv n hn)
    (ginibreSymmetricHolomorphicPolynomialClosedSpan n hn).toSubmodule
    (vandermondeSymmetricAlternatingEquiv n hn u)).symm

/-- The symmetric Ginibre holomorphic component of `u`. -/
def ginibreSymmetricHolomorphicPart (n : ℕ) (hn : 0 < n)
    (u : ginibreSymmetricL2 n) : ginibreSymmetricL2 n :=
  ginibreSymmetricHolomorphicProjection n hn u

/-- The Gaussian degree-zero component obtained from a symmetric Ginibre
vector by the normalized Vandermonde transform. -/
def gaussianZeroModeOfGinibre (n : ℕ) (hn : 0 < n)
    (u : ginibreSymmetricL2 n) : gaussianAlternatingL2 n :=
  gaussianAlternatingZeroModeProjection n hn
    (vandermondeSymmetricAlternatingEquiv n hn u)

/-- For every symmetric Ginibre vector, its projected holomorphic part `h`
has normalized Vandermonde transform equal to its Gaussian zero mode `g₀`. -/
theorem transform_ginibreSymmetricHolomorphicPart_eq_gaussianZeroMode
    (n : ℕ) (hn : 0 < n) (u : ginibreSymmetricL2 n) :
    vandermondeSymmetricAlternatingEquiv n hn
        (ginibreSymmetricHolomorphicPart n hn u) =
      gaussianZeroModeOfGinibre n hn u :=
  vandermondeEquiv_intertwines_holomorphicProjection n hn u

/-- The Gaussian component `g₀` belongs to the ambient degree-zero Hermite
closed span. -/
theorem gaussianZeroModeOfGinibre_mem_hermiteZeroMode
    (n : ℕ) (hn : 0 < n) (u : ginibreSymmetricL2 n) :
    (gaussianZeroModeOfGinibre n hn u).1 ∈
      hermiteAntiDegreeClosedSpan n hn 0 := by
  have hmem : gaussianZeroModeOfGinibre n hn u ∈
      (ginibreSymmetricHolomorphicPolynomialClosedSpan n hn).toSubmodule.map
        ((vandermondeSymmetricAlternatingEquiv n hn).toLinearEquiv :
          ginibreSymmetricL2 n →ₗ[ℂ] gaussianAlternatingL2 n) :=
    Submodule.starProjection_apply_mem _ _
  rw [map_ginibreSymmetricHolomorphicPolynomialClosedSpan n hn] at hmem
  exact gaussianAlternatingZeroModeClosedSpan_le_hermiteZeroMode n hn hmem

end
end ComplexHermite
end GinibrePoincare
