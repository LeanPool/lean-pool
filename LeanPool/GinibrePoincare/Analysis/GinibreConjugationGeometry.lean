/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreConjugationGeometry.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The finite polynomial-alternation bridge also comes from
GinibrePoincare/Analysis/HolomorphicQuotientPhaseFinite.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreL2Norm

public import LeanPool.GinibrePoincare.Analysis.GlobalPhaseAction
public import LeanPool.GinibrePoincare.Analysis.L2RepresentativeBridges

/-! # Conjugation geometry on symmetric Ginibre L² -/


@[expose] public section


open MeasureTheory
open scoped ComplexConjugate ENNReal

namespace GinibrePoincare

noncomputable section

local instance completeSpace_gaussianAlternatingL2' (n : ℕ) :
    CompleteSpace (gaussianAlternatingL2 n) :=
  (isClosed_gaussianAlternatingL2 n).completeSpace_coe

local instance completeSpace_ginibreSymmetricL2' (n : ℕ) :
    CompleteSpace (ginibreSymmetricL2 n) :=
  (isClosed_ginibreSymmetricL2 n).completeSpace_coe

theorem ginibreProbabilityInstance {n : ℕ} (hn : 0 < n) :
    IsProbabilityMeasure (ginibreMeasure n) :=
  ginibreMeasure_isProbabilityMeasure hn

/-- Isometric embedding of scalars as constant Ginibre `L²` functions. -/
def ginibreConstantL2 (n : ℕ) (hn : 0 < n) :
    ℂ →ₗᵢ[ℂ] Lp ℂ 2 (ginibreMeasure n) := by
  letI := ginibreProbabilityInstance hn
  exact {
    toLinearMap := Lp.constₗ 2 (ginibreMeasure n) ℂ
    norm_map' := fun c ↦ by
      change ‖Lp.const 2 (ginibreMeasure n) c‖ = ‖c‖
      rw [Lp.norm_const (2 : ℝ≥0∞) (ginibreMeasure n) c (by norm_num)]
      simp }

/-- Closed subspace of constant Ginibre `L²` functions. -/
def ginibreConstantClosedSubspace (n : ℕ) (hn : 0 < n) :
    ClosedSubmodule ℂ (Lp ℂ 2 (ginibreMeasure n)) where
  toSubmodule := LinearMap.range (ginibreConstantL2 n hn).toLinearMap
  isClosed' := (ginibreConstantL2 n hn).isometry.isUniformInducing.isComplete_range.isClosed

private theorem ginibrePermutationL2_star {n : ℕ}
    (σ : ParticlePermutation n) (u : Lp ℂ 2 (ginibreMeasure n)) :
    ginibrePermutationL2 σ (star u) = star (ginibrePermutationL2 σ u) := by
  apply Lp.ext
  have hstarcomp :=
    (ginibre_measurePreserving_permute σ).quasiMeasurePreserving.ae_eq_comp
      (Lp.coeFn_star u)
  filter_upwards [Lp.coeFn_compMeasurePreserving (star u)
      (ginibre_measurePreserving_permute σ),
    Lp.coeFn_compMeasurePreserving u
      (ginibre_measurePreserving_permute σ),
    hstarcomp,
    Lp.coeFn_star (ginibrePermutationL2 σ u)] with z hleft hright hstar hstarperm
  rw [show (ginibrePermutationL2 σ (star u)) z = (star u) (permute σ z) by
    exact hleft]
  rw [show (star (ginibrePermutationL2 σ u)) z =
    star ((ginibrePermutationL2 σ u) z) by exact hstarperm]
  rw [show (star u) (permute σ z) = star (u (permute σ z)) by
    exact hstar]
  rw [show (ginibrePermutationL2 σ u) z = u (permute σ z) by exact hright]

/-- Pointwise complex conjugation preserves the symmetric Ginibre subspace. -/
def ginibreSymmetricConjugation (n : ℕ) :
    ginibreSymmetricL2 n → ginibreSymmetricL2 n :=
  fun u ↦ ⟨star u.1, by
    intro σ
    rw [ginibrePermutationL2_star, u.2 σ]⟩

/-- Global-phase pullback commutes with value conjugation. -/
theorem ginibreGlobalPhaseL2_star {n : ℕ} (hn : 0 < n)
    (u : ℂ) (hu : ‖u‖ = 1) (h : Lp ℂ 2 (ginibreMeasure n)) :
    ginibreGlobalPhaseL2 hn u hu (star h) =
      star (ginibreGlobalPhaseL2 hn u hu h) := by
  apply Lp.ext
  have hstarcomp :=
    (measurePreserving_globalPhase_ginibreMeasure hn u hu).quasiMeasurePreserving.ae_eq_comp
      (Lp.coeFn_star h)
  filter_upwards [Lp.coeFn_compMeasurePreserving (star h)
      (measurePreserving_globalPhase_ginibreMeasure hn u hu),
    Lp.coeFn_compMeasurePreserving h
      (measurePreserving_globalPhase_ginibreMeasure hn u hu),
    hstarcomp, Lp.coeFn_star (ginibreGlobalPhaseL2 hn u hu h)] with
      z hleft hright hstar hstarphase
  rw [show (ginibreGlobalPhaseL2 hn u hu (star h)) z =
    (star h) (globalPhase u z) by exact hleft]
  rw [show (star (ginibreGlobalPhaseL2 hn u hu h)) z =
    star ((ginibreGlobalPhaseL2 hn u hu h) z) by exact hstarphase]
  rw [show (star h) (globalPhase u z) = star (h (globalPhase u z)) by
    exact hstar]
  rw [show (ginibreGlobalPhaseL2 hn u hu h) z = h (globalPhase u z) by
    exact hright]

/-- Subspace-valued form of phase/conjugation covariance. -/
theorem ginibreGlobalPhaseL2_symmetricConjugation {n : ℕ} (hn : 0 < n)
    (u : ℂ) (hu : ‖u‖ = 1) (h : ginibreSymmetricL2 n) :
    ginibreGlobalPhaseL2 hn u hu (ginibreSymmetricConjugation n h).1 =
      star (ginibreGlobalPhaseL2 hn u hu h.1) :=
  ginibreGlobalPhaseL2_star hn u hu h.1

/-- Value conjugation changes a phase eigenvalue to its complex conjugate. -/
theorem ginibreGlobalPhaseL2_star_eigen {n r : ℕ} (hn : 0 < n)
    (h : Lp ℂ 2 (ginibreMeasure n))
    (hh : ∀ (u : ℂ) (hu : ‖u‖ = 1),
      ginibreGlobalPhaseL2 hn u hu h = u ^ r • h)
    (u : ℂ) (hu : ‖u‖ = 1) :
    ginibreGlobalPhaseL2 hn u hu (star h) = conj (u ^ r) • star h := by
  rw [ginibreGlobalPhaseL2_star, hh u hu]
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (u ^ r • h), Lp.coeFn_star h,
    Lp.coeFn_smul (u ^ r) h,
    Lp.coeFn_smul (conj (u ^ r)) (star h)] with z hl hs hscalar hr
  rw [hl, hr]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hs]
  change conj ((u ^ r • h) z) = conj (u ^ r) * conj (h z)
  rw [hscalar]
  simp

/-- Every strictly positive phase-degree vector is orthogonal to its value
conjugate. -/
theorem inner_star_eq_zero_of_positive_ginibre_phase_degree {n r : ℕ}
    (hn : 0 < n) (hr : 0 < r) (h : Lp ℂ 2 (ginibreMeasure n))
    (hh : ∀ (u : ℂ) (hu : ‖u‖ = 1),
      ginibreGlobalPhaseL2 hn u hu h = u ^ r • h) :
    inner ℂ h (star h) = 0 := by
  have hne : 2 * r ≠ 0 := by omega
  obtain ⟨u, hu, hpow⟩ := exists_unit_phase_pow_ne (2 * r) 0 hne
  have hchar : conj (u ^ r) * conj (u ^ r) ≠ 1 := by
    intro hc
    apply hpow
    have hc' := congrArg conj hc
    simp only [map_pow, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply, map_one] at hc'
    have hp : u ^ (r + r) = 1 := by
      rw [pow_add]
      exact hc'
    simpa only [show 2 * r = r + r by omega, pow_zero] using hp
  exact inner_eq_zero_of_isometry_eigencharacters
    (ginibreGlobalPhaseL2 hn u hu) h (star h) (u ^ r) (conj (u ^ r))
      (hh u hu) (ginibreGlobalPhaseL2_star_eigen hn h hh u hu) hchar

/-- Cross-degree version: two nonnegative holomorphic phase degrees are
orthogonal after conjugating the second whenever their sum is positive. -/
theorem inner_star_eq_zero_of_ginibre_phase_degrees_add_pos {n r s : ℕ}
    (hn : 0 < n) (hrs : 0 < r + s)
    (x y : Lp ℂ 2 (ginibreMeasure n))
    (hx : ∀ (u : ℂ) (hu : ‖u‖ = 1),
      ginibreGlobalPhaseL2 hn u hu x = u ^ r • x)
    (hy : ∀ (u : ℂ) (hu : ‖u‖ = 1),
      ginibreGlobalPhaseL2 hn u hu y = u ^ s • y) :
    inner ℂ x (star y) = 0 := by
  have hne : r + s ≠ 0 := Nat.ne_of_gt hrs
  obtain ⟨u, hu, hpow⟩ := exists_unit_phase_pow_ne (r + s) 0 hne
  have hchar : conj (u ^ r) * conj (u ^ s) ≠ 1 := by
    intro hc
    apply hpow
    have hc' := congrArg conj hc
    simp only [map_pow, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply, map_one] at hc'
    rw [← pow_add] at hc'
    simpa only [pow_zero] using hc'
  exact inner_eq_zero_of_isometry_eigencharacters
    (ginibreGlobalPhaseL2 hn u hu) x (star y) (u ^ r) (conj (u ^ s))
      (hx u hu) (ginibreGlobalPhaseL2_star_eigen hn y hy u hu) hchar

/-- A positive-degree finite homogeneous Vandermonde quotient is orthogonal
to its value conjugate. -/
theorem inner_conjugate_finiteHomogeneousQuotient_eq_zero {n r : ℕ}
    (hn : 0 < n) (hr : 0 < r)
    (S : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℂ)
    (hAlt : finiteZeroHermiteL2 n hn S c ∈ gaussianAlternatingL2 n)
    (Q : ConfigurationPolynomial n)
    (hsum : ∀ z, finiteZeroAntiholomorphicHermiteSum n hn S c z =
      vandermonde z * MvPolynomial.eval z Q)
    (hphase : ∀ (u : ℂ), ‖u‖ = 1 → ∀ z, vandermonde z ≠ 0 →
      MvPolynomial.eval (globalPhase u z) Q =
        u ^ r * MvPolynomial.eval z Q) :
    inner ℂ (finiteHomogeneousQuotientL2 hn S c hAlt).1
      (star (finiteHomogeneousQuotientL2 hn S c hAlt).1) = 0 := by
  apply inner_star_eq_zero_of_positive_ginibre_phase_degree hn hr
  intro u hu
  exact ginibreGlobalPhaseL2_finiteHomogeneousQuotient
    hn S c hAlt Q hsum hphase u hu

/-- The closed common eigenspace of Ginibre global phases with holomorphic
character `u ↦ u^r`.  Defining the closed space by its character makes the
extension from finite homogeneous quotients automatic. -/
def ginibreHolomorphicPhaseDegree (n r : ℕ) (hn : 0 < n) :
    ClosedSubmodule ℂ (Lp ℂ 2 (ginibreMeasure n)) where
  carrier := {h | ∀ (u : ℂ) (hu : ‖u‖ = 1),
    ginibreGlobalPhaseL2 hn u hu h = u ^ r • h}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy u hu
    simp [map_add, hx u hu, hy u hu, smul_add]
  smul_mem' := by
    intro c x hx u hu
    rw [map_smul, hx u hu]
    simp [smul_smul, mul_comm]
  isClosed' := by
    rw [show {h | ∀ (u : ℂ) (hu : ‖u‖ = 1),
        ginibreGlobalPhaseL2 hn u hu h = u ^ r • h} =
      ⋂ (u : ℂ) (hu : ‖u‖ = 1),
        {h | ginibreGlobalPhaseL2 hn u hu h = u ^ r • h} by
      ext h
      simp]
    apply isClosed_iInter
    intro u
    apply isClosed_iInter
    intro hu
    exact isClosed_eq
      (ginibreGlobalPhaseL2 hn u hu).continuous
      (continuous_const_smul (u ^ r))

theorem mem_ginibreHolomorphicPhaseDegree_iff {n r : ℕ} (hn : 0 < n)
    (h : Lp ℂ 2 (ginibreMeasure n)) :
    h ∈ ginibreHolomorphicPhaseDegree n r hn ↔
      ∀ (u : ℂ) (hu : ‖u‖ = 1),
        ginibreGlobalPhaseL2 hn u hu h = u ^ r • h :=
  Iff.rfl

/-- Unequal closed phase-degree spaces are orthogonal. -/
theorem ginibreHolomorphicPhaseDegree_orthogonal {n r s : ℕ}
    (hn : 0 < n) (hrs : r ≠ s) :
    (ginibreHolomorphicPhaseDegree n r hn).toSubmodule ⟂
      (ginibreHolomorphicPhaseDegree n s hn).toSubmodule := by
  intro x hx y hy
  exact inner_eq_zero_of_ginibre_phase_degrees_ne hn hrs.symm y x hy hx

/-- Every vector in a positive closed phase-degree space is orthogonal to
its value conjugate. -/
theorem inner_star_eq_zero_of_mem_positive_phaseDegree {n r : ℕ}
    (hn : 0 < n) (hr : 0 < r) {h : Lp ℂ 2 (ginibreMeasure n)}
    (hh : h ∈ ginibreHolomorphicPhaseDegree n r hn) :
    inner ℂ h (star h) = 0 :=
  inner_star_eq_zero_of_positive_ginibre_phase_degree hn hr h hh

/-- Every finite homogeneous quotient of degree `r` belongs to the closed
degree-`r` character space. -/
theorem finiteHomogeneousQuotientL2_mem_phaseDegree {n r : ℕ}
    (hn : 0 < n) (S : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℂ)
    (hAlt : finiteZeroHermiteL2 n hn S c ∈ gaussianAlternatingL2 n)
    (Q : ConfigurationPolynomial n)
    (hsum : ∀ z, finiteZeroAntiholomorphicHermiteSum n hn S c z =
      vandermonde z * MvPolynomial.eval z Q)
    (hphase : ∀ (u : ℂ), ‖u‖ = 1 → ∀ z, vandermonde z ≠ 0 →
      MvPolynomial.eval (globalPhase u z) Q =
        u ^ r * MvPolynomial.eval z Q) :
    (finiteHomogeneousQuotientL2 hn S c hAlt).1 ∈
      ginibreHolomorphicPhaseDegree n r hn := by
  intro u hu
  exact ginibreGlobalPhaseL2_finiteHomogeneousQuotient
    hn S c hAlt Q hsum hphase u hu

/-- Predicate selecting the genuinely finite homogeneous holomorphic
quotient vectors of degree `r`. -/
def IsFiniteHomogeneousQuotientVector {n : ℕ} (hn : 0 < n) (r : ℕ)
    (h : Lp ℂ 2 (ginibreMeasure n)) : Prop :=
  ∃ (S : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℂ)
      (hAlt : finiteZeroHermiteL2 n hn S c ∈ gaussianAlternatingL2 n)
      (Q : ConfigurationPolynomial n),
    (∀ p ∈ S, totalHolomorphicDegree p = vandermondeDegree n + r) ∧
    IsAlternatingConfigurationPolynomial
      (finiteZeroAntiholomorphicHermitePolynomial n S c) ∧
    finiteZeroAntiholomorphicHermitePolynomial n S c ≠ 0 ∧
    finiteZeroAntiholomorphicHermitePolynomial n S c =
      polynomialVandermonde n * Q ∧
    (∀ z, finiteZeroAntiholomorphicHermiteSum n hn S c z =
      vandermonde z * MvPolynomial.eval z Q) ∧
    (∀ (u : ℂ), ‖u‖ = 1 → ∀ z, vandermonde z ≠ 0 →
      MvPolynomial.eval (globalPhase u z) Q =
        u ^ r * MvPolynomial.eval z Q) ∧
    h = (finiteHomogeneousQuotientL2 hn S c hAlt).1

/-- Closure of the span of finite homogeneous quotients of degree `r`. -/
def ginibreFiniteQuotientDegreeClosedSpan (n r : ℕ) (hn : 0 < n) :
    ClosedSubmodule ℂ (Lp ℂ 2 (ginibreMeasure n)) where
  toSubmodule := (Submodule.span ℂ
    {h | IsFiniteHomogeneousQuotientVector hn r h}).topologicalClosure
  isClosed' := (Submodule.span ℂ
    {h | IsFiniteHomogeneousQuotientVector hn r h}).isClosed_topologicalClosure

theorem ginibreFiniteQuotientDegreeClosedSpan_le_phaseDegree
    (n r : ℕ) (hn : 0 < n) :
    (ginibreFiniteQuotientDegreeClosedSpan n r hn).toSubmodule ≤
      (ginibreHolomorphicPhaseDegree n r hn).toSubmodule := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.2
    intro h hh
    rcases hh with ⟨S, c, hAlt, Q, hdegree, hpolyAlt, hne, hfactor,
      hsum, hphase, rfl⟩
    exact finiteHomogeneousQuotientL2_mem_phaseDegree hn S c hAlt Q hsum hphase
  · exact (ginibreHolomorphicPhaseDegree n r hn).isClosed

theorem ginibreFiniteQuotientDegreeClosedSpan_orthogonal {n r s : ℕ}
    (hn : 0 < n) (hrs : r ≠ s) :
    (ginibreFiniteQuotientDegreeClosedSpan n r hn).toSubmodule ⟂
      (ginibreFiniteQuotientDegreeClosedSpan n s hn).toSubmodule := by
  exact (ginibreHolomorphicPhaseDegree_orthogonal hn hrs).mono
    (ginibreFiniteQuotientDegreeClosedSpan_le_phaseDegree n r hn)
    (ginibreFiniteQuotientDegreeClosedSpan_le_phaseDegree n s hn)

theorem inner_star_eq_zero_of_mem_positive_finiteQuotientDegreeClosure
    {n r : ℕ} (hn : 0 < n) (hr : 0 < r)
    {h : Lp ℂ 2 (ginibreMeasure n)}
    (hh : h ∈ ginibreFiniteQuotientDegreeClosedSpan n r hn) :
    inner ℂ h (star h) = 0 :=
  inner_star_eq_zero_of_mem_positive_phaseDegree hn hr
    (ginibreFiniteQuotientDegreeClosedSpan_le_phaseDegree n r hn hh)

theorem inner_star_eq_zero_of_mem_finiteQuotientDegreeClosures
    {n r s : ℕ} (hn : 0 < n) (hrs : 0 < r + s)
    {x y : Lp ℂ 2 (ginibreMeasure n)}
    (hx : x ∈ ginibreFiniteQuotientDegreeClosedSpan n r hn)
    (hy : y ∈ ginibreFiniteQuotientDegreeClosedSpan n s hn) :
    inner ℂ x (star y) = 0 := by
  exact inner_star_eq_zero_of_ginibre_phase_degrees_add_pos hn hrs x y
    (ginibreFiniteQuotientDegreeClosedSpan_le_phaseDegree n r hn hx)
    (ginibreFiniteQuotientDegreeClosedSpan_le_phaseDegree n s hn hy)

/-- Every bottom-degree finite quotient generator is represented by a
constant function. -/
theorem finite_bottom_quotient_generator_ae_constant {n : ℕ} (hn : 0 < n)
    {h : Lp ℂ 2 (ginibreMeasure n)}
    (hh : IsFiniteHomogeneousQuotientVector hn 0 h) :
    ∃ a : ℂ, h =ᵐ[ginibreMeasure n] fun _ ↦ a := by
  rcases hh with ⟨S, c, hAlt, Q, hdegree, hpolyAlt, hne, hfactor,
    hsum, hphase, rfl⟩
  have hhom : MvPolynomial.IsHomogeneous
      (finiteZeroAntiholomorphicHermitePolynomial n S c)
      (vandermondeDegree n) := by
    apply isHomogeneous_finiteZeroAntiholomorphicHermitePolynomial_of_degree
    intro p hp
    simpa using hdegree p hp
  have hQ := quotient_eq_C_of_bottom_homogeneous_degree hhom hne hfactor
  refine ⟨(groundStateNormalization n : ℂ) * Q.coeff 0, ?_⟩
  filter_upwards [finiteHomogeneousQuotientL2_coeFn hn S c hAlt Q hsum] with z hz
  rw [hz, hQ]
  simp

theorem finite_bottom_quotient_generator_mem_constants {n : ℕ} (hn : 0 < n)
    {h : Lp ℂ 2 (ginibreMeasure n)}
    (hh : IsFiniteHomogeneousQuotientVector hn 0 h) :
    h ∈ ginibreConstantClosedSubspace n hn := by
  obtain ⟨a, ha⟩ := finite_bottom_quotient_generator_ae_constant hn hh
  refine ⟨a, ?_⟩
  apply Lp.ext
  let := ginibreProbabilityInstance hn
  filter_upwards [ha, Lp.coeFn_const (α := Configuration n)
    (μ := ginibreMeasure n) (p := (2 : ℝ≥0∞)) a] with z hz hconst
  change (Lp.const 2 (ginibreMeasure n) a) z = h z
  rw [hconst, hz]
  rfl

theorem ginibreFiniteQuotientDegreeZero_le_constants (n : ℕ) (hn : 0 < n) :
    (ginibreFiniteQuotientDegreeClosedSpan n 0 hn).toSubmodule ≤
      (ginibreConstantClosedSubspace n hn).toSubmodule := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.2
    intro h hh
    exact finite_bottom_quotient_generator_mem_constants hn hh
  · exact (ginibreConstantClosedSubspace n hn).isClosed

theorem ginibreConstantL2_mem_degreeZeroClosure (n : ℕ) (hn : 0 < n) (a : ℂ) :
    ginibreConstantL2 n hn a ∈
      ginibreFiniteQuotientDegreeClosedSpan n 0 hn := by
  by_cases ha : a = 0
  · subst a
    simp
  let k : ℂ := a / (groundStateNormalization n : ℂ)
  let P : ConfigurationPolynomial n :=
    polynomialVandermonde n * MvPolynomial.C k
  let S := holomorphicHermiteSupport P
  let c := holomorphicHermiteCoefficient P
  have hk : k ≠ 0 := div_ne_zero ha (by
    exact_mod_cast groundStateNormalization_ne_zero_of_pos hn)
  have hPalt : IsAlternatingConfigurationPolynomial P := by
    apply isAlternating_polynomialVandermonde_mul
    intro σ
    simp
  have hPne : P ≠ 0 := mul_ne_zero (polynomialVandermonde_ne_zero n)
    (MvPolynomial.C_ne_zero.mpr hk)
  have hPhom : MvPolynomial.IsHomogeneous P (vandermondeDegree n) := by
    unfold P
    simpa using (isHomogeneous_polynomialVandermonde n).mul
      (MvPolynomial.isHomogeneous_C (σ := Fin n) k)
  have hexpand : finiteZeroAntiholomorphicHermitePolynomial n S c = P :=
    finiteZeroAntiholomorphicHermitePolynomial_support_expansion hn P
  have hAltL2 : finiteZeroHermiteL2 n hn S c ∈ gaussianAlternatingL2 n := by
    apply finiteZeroHermiteL2_mem_gaussianAlternating hn
    rwa [hexpand]
  let q := finiteHomogeneousQuotientL2 hn S c hAltL2
  have hsum : ∀ z, finiteZeroAntiholomorphicHermiteSum n hn S c z =
      vandermonde z * MvPolynomial.eval z (MvPolynomial.C k) := by
    intro z
    rw [← eval_finiteZeroAntiholomorphicHermitePolynomial n hn S c z,
      hexpand]
    simp [P, eval_polynomialVandermonde]
  have hqcoe := finiteHomogeneousQuotientL2_coeFn hn S c hAltL2
    (MvPolynomial.C k) hsum
  have hqconst : q.1 = ginibreConstantL2 n hn a := by
    apply Lp.ext
    let := ginibreProbabilityInstance hn
    filter_upwards [hqcoe, Lp.coeFn_const (α := Configuration n)
      (μ := ginibreMeasure n) (p := (2 : ℝ≥0∞)) a] with z hq hc
    change q.1 z = (Lp.const 2 (ginibreMeasure n) a) z
    rw [hq, hc]
    simp only [MvPolynomial.eval_C, Function.const_apply]
    unfold k
    have hgn : (groundStateNormalization n : ℂ) ≠ 0 := by
      exact_mod_cast groundStateNormalization_ne_zero_of_pos hn
    field_simp
  change ginibreConstantL2 n hn a ∈
    (Submodule.span ℂ {h | IsFiniteHomogeneousQuotientVector hn 0 h}).topologicalClosure
  apply subset_closure
  apply Submodule.subset_span
  change IsFiniteHomogeneousQuotientVector hn 0 (ginibreConstantL2 n hn a)
  refine ⟨S, c, hAltL2, MvPolynomial.C k, ?_, ?_, ?_, ?_, hsum, ?_, ?_⟩
  · intro p hp
    simpa using totalHolomorphicDegree_eq_of_mem_holomorphicHermiteSupport hPhom hp
  · rwa [hexpand]
  · rwa [hexpand]
  · rw [hexpand]
  · intro u hu z hz
    simp
  · exact hqconst.symm

theorem ginibreFiniteQuotientDegreeZero_eq_constants (n : ℕ) (hn : 0 < n) :
    ginibreFiniteQuotientDegreeClosedSpan n 0 hn =
      ginibreConstantClosedSubspace n hn := by
  ext h
  constructor
  · intro hh
    exact ginibreFiniteQuotientDegreeZero_le_constants n hn hh
  · rintro ⟨a, rfl⟩
    exact ginibreConstantL2_mem_degreeZeroClosure n hn a

/-- Every nonzero homogeneous component of an alternating polynomial gives
a finite quotient generator in the degree shifted by the Vandermonde
degree. -/
theorem homogeneousComponent_gives_finiteQuotientVector
    {n d : ℕ} (hn : 0 < n) {P : ConfigurationPolynomial n}
    (hAlt : IsAlternatingConfigurationPolynomial P)
    (hcomponent : MvPolynomial.homogeneousComponent d P ≠ 0) :
    ∃ (h : Lp ℂ 2 (ginibreMeasure n)),
      IsFiniteHomogeneousQuotientVector hn (d - vandermondeDegree n) h := by
  let Pd := MvPolynomial.homogeneousComponent d P
  have hPdHom : MvPolynomial.IsHomogeneous Pd d :=
    MvPolynomial.homogeneousComponent_isHomogeneous d P
  have hPdAlt : IsAlternatingConfigurationPolynomial Pd :=
    isAlternating_homogeneousComponent hAlt
  obtain ⟨Q, hQsym, hfactor, hle, hphase⟩ :=
    homogeneous_alternating_polynomial_division hPdHom hPdAlt hcomponent
  let S := holomorphicHermiteSupport Pd
  let c := holomorphicHermiteCoefficient Pd
  have hexpand : finiteZeroAntiholomorphicHermitePolynomial n S c = Pd :=
    finiteZeroAntiholomorphicHermitePolynomial_support_expansion hn Pd
  have hAltL2 : finiteZeroHermiteL2 n hn S c ∈ gaussianAlternatingL2 n := by
    apply finiteZeroHermiteL2_mem_gaussianAlternating hn
    rwa [hexpand]
  let h := (finiteHomogeneousQuotientL2 hn S c hAltL2).1
  refine ⟨h, S, c, hAltL2, Q, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · intro p hp
    rw [Nat.add_sub_of_le hle]
    exact totalHolomorphicDegree_eq_of_mem_holomorphicHermiteSupport hPdHom hp
  · rwa [hexpand]
  · rwa [hexpand]
  · rwa [hexpand]
  · intro z
    rw [← eval_finiteZeroAntiholomorphicHermitePolynomial n hn S c z,
      hexpand, hfactor, map_mul, eval_polynomialVandermonde]
  · exact hphase

/-- Every alternating polynomial is a finite sum of homogeneous alternating
components; every nonzero summand has at least Vandermonde degree and is
therefore covered by the preceding quotient construction. -/
theorem alternating_polynomial_homogeneous_decomposition
    {n : ℕ} (P : ConfigurationPolynomial n)
    (hAlt : IsAlternatingConfigurationPolynomial P) :
    (∑ d ∈ Finset.range (P.totalDegree + 1),
        MvPolynomial.homogeneousComponent d P) = P ∧
      ∀ d, MvPolynomial.homogeneousComponent d P ≠ 0 →
        IsAlternatingConfigurationPolynomial
          (MvPolynomial.homogeneousComponent d P) ∧
        vandermondeDegree n ≤ d := by
  refine ⟨MvPolynomial.sum_homogeneousComponent P, ?_⟩
  intro d hd
  have hhom := MvPolynomial.homogeneousComponent_isHomogeneous d P
  have halt : IsAlternatingConfigurationPolynomial
      (MvPolynomial.homogeneousComponent d P) :=
    isAlternating_homogeneousComponent hAlt
  exact ⟨halt,
    vandermondeDegree_le_of_homogeneous_alternating hhom halt hd⟩

/-- Orbit of a holomorphic multi-index under coordinate permutations. -/
def holomorphicPermutationOrbitIndex {n : ℕ}
    (p : Fin n → ℕ) (σ : ParticlePermutation n) : Fin n → ℕ :=
  p ∘ σ.symm

/-- Fiber-summed coefficients of the signed alternation of one holomorphic
Hermite tensor. -/
def alternatedHolomorphicCoefficient {n : ℕ} (p q : Fin n → ℕ) : ℂ :=
  ((Fintype.card (ParticlePermutation n) : ℂ)⁻¹) *
    ∑ σ ∈ (Finset.univ : Finset (ParticlePermutation n)) with
      holomorphicPermutationOrbitIndex p σ = q, permutationSign σ

/-- The finite orbit of a holomorphic multi-index under particle permutations. -/
def holomorphicPermutationOrbitSupport {n : ℕ} (p : Fin n → ℕ) :
    Finset (Fin n → ℕ) :=
  Finset.univ.image (holomorphicPermutationOrbitIndex p)

/-- Generic fiberwise regrouping of a finite sum of scalar multiples. -/
theorem sum_smul_comp_eq_sum_fiber
    {ι κ 𝕜 M : Type*} [DecidableEq κ] [Semiring 𝕜]
    [AddCommMonoid M] [Module 𝕜 M]
    (s : Finset ι) (g : ι → κ) (w : ι → 𝕜) (v : κ → M) :
    (∑ i ∈ s, w i • v (g i)) =
      ∑ q ∈ s.image g, (∑ i ∈ s with g i = q, w i) • v q := by
  symm
  have hfiber := Finset.sum_fiberwise_of_maps_to
    (s := s) (t := s.image g) (g := g)
    (fun i hi ↦ Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    (fun i ↦ w i • v (g i))
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.sum_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [(Finset.mem_filter.mp hi).2]

/-- Opaque `L²` instantiation of the generic fiber regrouping lemma. -/
theorem finiteZeroHermiteL2_alternatedHolomorphicCoefficient
    (n : ℕ) (hn : 0 < n) (p : Fin n → ℕ) :
    finiteZeroHermiteL2 n hn (holomorphicPermutationOrbitSupport p)
        (alternatedHolomorphicCoefficient p) =
      ComplexHermite.gaussianAlternationOperator n
        (ComplexHermite.hermiteL2Family n hn (p, 0)) := by
  rw [ComplexHermite.gaussianAlternationOperator_apply]
  have hperm : ∀ σ : ParticlePermutation n,
      gaussianPermutationL2 σ (ComplexHermite.hermiteL2Family n hn (p, 0)) =
        ComplexHermite.hermiteL2Family n hn
          (holomorphicPermutationOrbitIndex p σ, 0) := by
    intro σ
    rw [ComplexHermite.gaussianPermutationL2_hermiteL2Family]
    congr 2
  rw [show (∑ σ : ParticlePermutation n,
      permutationSign σ • gaussianPermutationL2 σ
        (ComplexHermite.hermiteL2Family n hn (p, 0))) =
      ∑ σ : ParticlePermutation n, permutationSign σ •
        ComplexHermite.hermiteL2Family n hn
          (holomorphicPermutationOrbitIndex p σ, 0) by
    apply Finset.sum_congr rfl
    intro σ hσ
    rw [hperm]]
  rw [sum_smul_comp_eq_sum_fiber
    (s := (Finset.univ : Finset (ParticlePermutation n)))
    (g := holomorphicPermutationOrbitIndex p)
    (w := permutationSign)
    (v := fun q ↦ ComplexHermite.hermiteL2Family n hn (q, 0))]
  unfold finiteZeroHermiteL2 holomorphicPermutationOrbitSupport
    alternatedHolomorphicCoefficient
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [smul_smul]

theorem totalHolomorphicDegree_orbitIndex {n : ℕ}
    (p : Fin n → ℕ) (σ : ParticlePermutation n) :
    totalHolomorphicDegree (holomorphicPermutationOrbitIndex p σ) =
      totalHolomorphicDegree p := by
  unfold totalHolomorphicDegree holomorphicPermutationOrbitIndex
  exact Equiv.sum_comp σ.symm p

theorem totalHolomorphicDegree_eq_of_mem_orbitSupport {n : ℕ}
    (p q : Fin n → ℕ) (hq : q ∈ holomorphicPermutationOrbitSupport p) :
    totalHolomorphicDegree q = totalHolomorphicDegree p := by
  rcases Finset.mem_image.mp hq with ⟨σ, hσ, rfl⟩
  exact totalHolomorphicDegree_orbitIndex p σ

/-- Alternation of the finite Hermite L² class implies algebraic polynomial alternation. -/
theorem finiteZeroHermiteL2_alternating_polynomial {n : ℕ} (hn : 0 < n)
    (S : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℂ)
    (hAlt : finiteZeroHermiteL2 n hn S c ∈ gaussianAlternatingL2 n) :
    IsAlternatingConfigurationPolynomial (finiteZeroAntiholomorphicHermitePolynomial n S c) := by
  apply (finiteHermiteSum_isAlternating_iff hn S c).1
  intro σ
  have heq : (fun z ↦ finiteZeroAntiholomorphicHermiteSum n hn S c (permute σ z)) =
      fun z ↦ permutationSign σ * finiteZeroAntiholomorphicHermiteSum n hn S c z := by
    apply continuous_eq_of_ae_eq_complexGaussian hn
    · have hc : Continuous (finiteZeroAntiholomorphicHermiteSum n hn S c) := by
        convert MvPolynomial.continuous_eval
          (finiteZeroAntiholomorphicHermitePolynomial n S c) using 1
        funext z
        exact (eval_finiteZeroAntiholomorphicHermitePolynomial n hn S c z).symm
      apply hc.comp
      exact continuous_pi (fun i ↦ continuous_apply (σ i))
    · have hc : Continuous (finiteZeroAntiholomorphicHermiteSum n hn S c) := by
        convert MvPolynomial.continuous_eval
          (finiteZeroAntiholomorphicHermitePolynomial n S c) using 1
        funext z
        exact (eval_finiteZeroAntiholomorphicHermitePolynomial n hn S c z).symm
      exact continuous_const.mul hc
    have hLp := hAlt σ
    have hclass :
        (gaussianPermutationL2 σ (finiteZeroHermiteL2 n hn S c) :
          Configuration n → ℂ) =ᵐ[complexGaussianMeasure n]
        (permutationSign σ • finiteZeroHermiteL2 n hn S c :
          Configuration n → ℂ) := by
      rw [hLp]
      exact Lp.coeFn_smul _ _
    have hcoe := finiteZeroHermiteL2_coeFn n hn S c
    have hcomp := (gaussian_measurePreserving_permute σ).quasiMeasurePreserving.ae_eq_comp hcoe
    filter_upwards [hclass, Lp.coeFn_compMeasurePreserving (finiteZeroHermiteL2 n hn S c)
        (gaussian_measurePreserving_permute σ), hcomp, hcoe] with
        z hpoint hpull hsrc htgt
    rw [show (gaussianPermutationL2 σ (finiteZeroHermiteL2 n hn S c)) z =
      finiteZeroHermiteL2 n hn S c (permute σ z) by exact hpull] at hpoint
    simp only [Pi.smul_apply, smul_eq_mul] at hpoint
    change finiteZeroHermiteL2 n hn S c (permute σ z) =
      finiteZeroAntiholomorphicHermiteSum n hn S c (permute σ z) at hsrc
    change finiteZeroHermiteL2 n hn S c (permute σ z) =
      permutationSign σ * finiteZeroHermiteL2 n hn S c z at hpoint
    rw [hsrc, htgt] at hpoint
    exact hpoint
  exact fun z ↦ congrFun heq z


/-- The orbit-fiber polynomial is algebraically alternating. -/
theorem isAlternating_alternatedHolomorphicPolynomial
    (n : ℕ) (hn : 0 < n) (p : Fin n → ℕ) :
    IsAlternatingConfigurationPolynomial
      (finiteZeroAntiholomorphicHermitePolynomial n
        (holomorphicPermutationOrbitSupport p)
        (alternatedHolomorphicCoefficient p)) := by
  apply finiteZeroHermiteL2_alternating_polynomial hn
    (holomorphicPermutationOrbitSupport p) (alternatedHolomorphicCoefficient p)
  rw [finiteZeroHermiteL2_alternatedHolomorphicCoefficient]
  exact ComplexHermite.gaussianAlternationOperator_mem n _

/-- The inverse Vandermonde image of an alternated holomorphic Hermite basis
vector belongs to its shifted homogeneous quotient closure. -/
theorem inverse_alternatedHermite_mem_degreeClosure
    (n : ℕ) (hn : 0 < n) (p : Fin n → ℕ) :
    ((vandermondeSymmetricAlternatingEquiv n hn).symm
      ⟨ComplexHermite.gaussianAlternationOperator n
          (ComplexHermite.hermiteL2Family n hn (p, 0)),
        ComplexHermite.gaussianAlternationOperator_mem n _⟩).1 ∈
      ginibreFiniteQuotientDegreeClosedSpan n
        (totalHolomorphicDegree p - vandermondeDegree n) hn := by
  let S := holomorphicPermutationOrbitSupport p
  let c := alternatedHolomorphicCoefficient p
  let P := finiteZeroAntiholomorphicHermitePolynomial n S c
  have hvEq : finiteZeroHermiteL2 n hn S c =
      ComplexHermite.gaussianAlternationOperator n
        (ComplexHermite.hermiteL2Family n hn (p, 0)) :=
    finiteZeroHermiteL2_alternatedHolomorphicCoefficient n hn p
  have hAltP : IsAlternatingConfigurationPolynomial P :=
    isAlternating_alternatedHolomorphicPolynomial n hn p
  have hHom : MvPolynomial.IsHomogeneous P (totalHolomorphicDegree p) := by
    apply isHomogeneous_finiteZeroAntiholomorphicHermitePolynomial_of_degree
    intro q hq
    exact totalHolomorphicDegree_eq_of_mem_orbitSupport p q hq
  have hAltL2 : finiteZeroHermiteL2 n hn S c ∈ gaussianAlternatingL2 n := by
    rw [hvEq]
    exact ComplexHermite.gaussianAlternationOperator_mem n _
  let x : gaussianAlternatingL2 n :=
    ⟨ComplexHermite.gaussianAlternationOperator n
      (ComplexHermite.hermiteL2Family n hn (p, 0)),
      ComplexHermite.gaussianAlternationOperator_mem n _⟩
  let y : gaussianAlternatingL2 n := ⟨finiteZeroHermiteL2 n hn S c, hAltL2⟩
  have hxy : x = y := Subtype.ext hvEq.symm
  change ((vandermondeSymmetricAlternatingEquiv n hn).symm x).1 ∈ _
  rw [hxy]
  by_cases hP0 : P = 0
  · have hv0 : finiteZeroHermiteL2 n hn S c = 0 := by
      apply Lp.ext
      filter_upwards [finiteZeroHermiteL2_coeFn n hn S c,
        Lp.coeFn_zero ℂ 2 (complexGaussianMeasure n)] with z hv hz
      rw [hv, ← eval_finiteZeroAntiholomorphicHermitePolynomial n hn S c z]
      change MvPolynomial.eval z P = _
      rw [hP0, map_zero]
      exact hz.symm
    change ((vandermondeSymmetricAlternatingEquiv n hn).symm
      (⟨finiteZeroHermiteL2 n hn S c, hAltL2⟩ : gaussianAlternatingL2 n)).1 ∈ _
    have hy0 : (⟨finiteZeroHermiteL2 n hn S c, hAltL2⟩ :
        gaussianAlternatingL2 n) = 0 := Subtype.ext hv0
    rw [hy0]
    simp
  · obtain ⟨Q, hQ, hfactor, hle, hphase⟩ :=
      homogeneous_alternating_polynomial_division hHom hAltP hP0
    have hsum : ∀ z, finiteZeroAntiholomorphicHermiteSum n hn S c z =
        vandermonde z * MvPolynomial.eval z Q := by
      intro z
      rw [← eval_finiteZeroAntiholomorphicHermitePolynomial n hn S c z]
      change MvPolynomial.eval z P = _
      rw [hfactor, map_mul, eval_polynomialVandermonde]
    change (finiteHomogeneousQuotientL2 hn S c hAltL2).1 ∈ _
    apply subset_closure
    apply Submodule.subset_span
    refine ⟨S, c, hAltL2, Q, ?_, hAltP, hP0, hfactor, hsum, hphase, rfl⟩
    intro q hq
    rw [Nat.add_sub_of_le hle]
    exact totalHolomorphicDegree_eq_of_mem_orbitSupport p q hq

/-- The closed ambient Ginibre space generated by all homogeneous polynomial
quotient degrees. -/
def ginibreFiniteQuotientGradedClosedSpan (n : ℕ) (hn : 0 < n) :
    ClosedSubmodule ℂ (Lp ℂ 2 (ginibreMeasure n)) :=
  ⨆ r : ℕ, ginibreFiniteQuotientDegreeClosedSpan n r hn

theorem inverse_alternatedHermite_mem_gradedClosedSpan
    (n : ℕ) (hn : 0 < n) (p : Fin n → ℕ) :
    ((vandermondeSymmetricAlternatingEquiv n hn).symm
      ⟨ComplexHermite.gaussianAlternationOperator n
          (ComplexHermite.hermiteL2Family n hn (p, 0)),
        ComplexHermite.gaussianAlternationOperator_mem n _⟩).1 ∈
      ginibreFiniteQuotientGradedClosedSpan n hn := by
  exact le_iSup (fun r : ℕ ↦ ginibreFiniteQuotientDegreeClosedSpan n r hn)
    (totalHolomorphicDegree p - vandermondeDegree n)
    (inverse_alternatedHermite_mem_degreeClosure n hn p)

/-- Alternation followed by inverse Vandermonde division, regarded as an
ambient continuous linear map. -/
def alternatedInverseVandermondeL2 (n : ℕ) (hn : 0 < n) :
    Lp ℂ 2 (complexGaussianMeasure n) →L[ℂ] Lp ℂ 2 (ginibreMeasure n) :=
  (ginibreSymmetricL2 n).subtypeL.comp
    ((vandermondeSymmetricAlternatingEquiv n
      hn).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((ComplexHermite.gaussianAlternationOperator n).codRestrict
        (gaussianAlternatingL2 n)
        (ComplexHermite.gaussianAlternationOperator_mem n)))

/-- Every finite Gaussian antiholomorphic-degree-zero vector, after
alternation and inverse Vandermonde division, lies in the graded quotient
closed span. -/
theorem alternatedInverseVandermondeL2_mem_gradedClosedSpan
    (n : ℕ) (hn : 0 < n) (v : Lp ℂ 2 (complexGaussianMeasure n))
    (hv : v ∈ ComplexHermite.hermiteAntiDegreeSpan n hn 0) :
    alternatedInverseVandermondeL2 n hn v ∈
      ginibreFiniteQuotientGradedClosedSpan n hn := by
  refine Submodule.span_induction (p := fun w _ ↦
    alternatedInverseVandermondeL2 n hn w ∈
      ginibreFiniteQuotientGradedClosedSpan n hn) ?basis
      (map_zero (alternatedInverseVandermondeL2 n hn) ▸
        (ginibreFiniteQuotientGradedClosedSpan n hn).zero_mem)
      (fun x y _ _ hx hy ↦ by simpa using
        (ginibreFiniteQuotientGradedClosedSpan n hn).add_mem hx hy)
      (fun a x _ hx ↦ by
        rw [map_smul]
        exact (ginibreFiniteQuotientGradedClosedSpan n hn).smul_mem a hx) hv
  rintro w ⟨pq, hpq, rfl⟩
  rcases pq with ⟨p, q⟩
  have hq : q = 0 := by
    ext i
    have hall := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ ↦ Nat.zero_le (q j))).mp hpq i (Finset.mem_univ i)
    exact hall
  subst q
  have hsub :
      ((ComplexHermite.gaussianAlternationOperator n).codRestrict
          (gaussianAlternatingL2 n)
          (ComplexHermite.gaussianAlternationOperator_mem n))
          (ComplexHermite.hermiteL2Family n hn (p, 0)) =
        (⟨ComplexHermite.gaussianAlternationOperator n
            (ComplexHermite.hermiteL2Family n hn (p, 0)),
          ComplexHermite.gaussianAlternationOperator_mem n _⟩ :
            gaussianAlternatingL2 n) := Subtype.ext rfl
  simp only [alternatedInverseVandermondeL2, ContinuousLinearMap.comp_apply]
  rw [hsub]
  exact inverse_alternatedHermite_mem_gradedClosedSpan n hn p

/-- The established holomorphic polynomial closure is contained in the
closed sum of its homogeneous quotient degrees. -/
theorem ginibreHolomorphicClosedSpan_le_gradedClosedSpan
    (n : ℕ) (hn : 0 < n) (u : ginibreSymmetricL2 n)
    (hu : u ∈ ComplexHermite.ginibreSymmetricHolomorphicPolynomialClosedSpan n hn) :
    u.1 ∈ ginibreFiniteQuotientGradedClosedSpan n hn := by
  change u ∈
    (ComplexHermite.ginibreSymmetricHolomorphicPolynomialSpan n hn).topologicalClosure at hu
  have hle : ComplexHermite.ginibreSymmetricHolomorphicPolynomialSpan n hn ≤
      (ginibreFiniteQuotientGradedClosedSpan n hn).toSubmodule.comap
        (ginibreSymmetricL2 n).subtype := by
    rintro w ⟨v, hv, rfl⟩
    have hfin := alternatedInverseVandermondeL2_mem_gradedClosedSpan n hn v.1 hv
    have hfix : ComplexHermite.gaussianAlternationOperator n v.1 = v.1 :=
      ComplexHermite.gaussianAlternationOperator_eq_self_of_mem v.2
    have heq : alternatedInverseVandermondeL2 n hn v.1 =
        ((vandermondeSymmetricAlternatingEquiv n hn).symm v).1 := by
      have harg :
          ((ComplexHermite.gaussianAlternationOperator n).codRestrict
            (gaussianAlternatingL2 n)
            (ComplexHermite.gaussianAlternationOperator_mem n)) v.1 = v :=
        Subtype.ext hfix
      change (((vandermondeSymmetricAlternatingEquiv n hn).symm
        (((ComplexHermite.gaussianAlternationOperator n).codRestrict
          (gaussianAlternatingL2 n)
          (ComplexHermite.gaussianAlternationOperator_mem n)) v.1))).1 = _
      rw [harg]
    rw [heq] at hfin
    exact hfin
  have hclosed : IsClosed
      ((ginibreFiniteQuotientGradedClosedSpan n hn).toSubmodule.comap
        (ginibreSymmetricL2 n).subtype : Set (ginibreSymmetricL2 n)) :=
    (ginibreFiniteQuotientGradedClosedSpan n hn).isClosed.preimage
      (ginibreSymmetricL2 n).subtypeL.continuous
  exact (Submodule.topologicalClosure_minimal _ hle hclosed) hu

theorem finiteZeroHermiteL2_mem_antiDegreeZeroSpan
    (n : ℕ) (hn : 0 < n) (S : Finset (Fin n → ℕ))
    (c : (Fin n → ℕ) → ℂ) :
    finiteZeroHermiteL2 n hn S c ∈
      ComplexHermite.hermiteAntiDegreeSpan n hn 0 := by
  unfold finiteZeroHermiteL2
  apply Submodule.sum_mem
  intro p hp
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨(p, 0), ?_, rfl⟩
  simp [ComplexHermite.totalAntiDegree]

/-- Each finite homogeneous quotient generator is already one of the
finite holomorphic Ginibre vectors in the original definition. -/
theorem finiteHomogeneousQuotient_mem_holomorphicPolynomialSpan
    {n r : ℕ} (hn : 0 < n) {h : Lp ℂ 2 (ginibreMeasure n)}
    (hh : IsFiniteHomogeneousQuotientVector hn r h) :
    ∃ w : ginibreSymmetricL2 n,
      w ∈ ComplexHermite.ginibreSymmetricHolomorphicPolynomialSpan n hn ∧
        w.1 = h := by
  rcases hh with ⟨S, c, hAlt, Q, hdegree, hpolyAlt, hne, hfactor,
    hsum, hphase, rfl⟩
  let v : gaussianAlternatingL2 n := ⟨finiteZeroHermiteL2 n hn S c, hAlt⟩
  let w : ginibreSymmetricL2 n :=
    (vandermondeSymmetricAlternatingEquiv n hn).symm v
  refine ⟨w, ?_, rfl⟩
  exact ⟨v, finiteZeroHermiteL2_mem_antiDegreeZeroSpan n hn S c, rfl⟩

/-- The original symmetric holomorphic closed span, embedded in ambient
Ginibre `L²`. -/
def ginibreHolomorphicAmbientClosedSpan (n : ℕ) (hn : 0 < n) :
    ClosedSubmodule ℂ (Lp ℂ 2 (ginibreMeasure n)) where
  toSubmodule :=
    (ComplexHermite.ginibreSymmetricHolomorphicPolynomialClosedSpan n hn).toSubmodule.map
      (ginibreSymmetricL2 n).subtype
  isClosed' := by
    have he : Topology.IsClosedEmbedding
      (fun w : ginibreSymmetricL2 n ↦ w.1) :=
      (isClosed_ginibreSymmetricL2 n).isClosedEmbedding_subtypeVal
    change IsClosed ((fun w : ginibreSymmetricL2 n ↦ w.1) ''
      (ComplexHermite.ginibreSymmetricHolomorphicPolynomialClosedSpan n hn :
        Set (ginibreSymmetricL2 n)))
    rw [← he.isClosed_iff_image_isClosed]
    exact (ComplexHermite.ginibreSymmetricHolomorphicPolynomialClosedSpan n hn).isClosed

theorem ginibreFiniteQuotientDegreeClosedSpan_le_holomorphicAmbient
    (n r : ℕ) (hn : 0 < n) :
    ginibreFiniteQuotientDegreeClosedSpan n r hn ≤
      ginibreHolomorphicAmbientClosedSpan n hn := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.2
    intro h hh
    obtain ⟨w, hw, rfl⟩ :=
      finiteHomogeneousQuotient_mem_holomorphicPolynomialSpan hn hh
    refine ⟨w, ?_, rfl⟩
    change w ∈ (ComplexHermite.ginibreSymmetricHolomorphicPolynomialSpan n hn).topologicalClosure
    exact (ComplexHermite.ginibreSymmetricHolomorphicPolynomialSpan n hn).le_topologicalClosure hw
  · exact (ginibreHolomorphicAmbientClosedSpan n hn).isClosed

theorem ginibreGradedClosedSpan_le_holomorphicAmbient
    (n : ℕ) (hn : 0 < n) :
    ginibreFiniteQuotientGradedClosedSpan n hn ≤
      ginibreHolomorphicAmbientClosedSpan n hn := by
  apply iSup_le
  intro r
  exact ginibreFiniteQuotientDegreeClosedSpan_le_holomorphicAmbient n r hn

theorem ginibreHolomorphicAmbientClosedSpan_eq_graded
    (n : ℕ) (hn : 0 < n) :
    ginibreHolomorphicAmbientClosedSpan n hn =
      ginibreFiniteQuotientGradedClosedSpan n hn := by
  apply le_antisymm
  · rintro h ⟨w, hw, rfl⟩
    exact ginibreHolomorphicClosedSpan_le_gradedClosedSpan n hn w hw
  · exact ginibreGradedClosedSpan_le_holomorphicAmbient n hn

/-- Closed sum of the strictly positive homogeneous quotient degrees. -/
def ginibrePositiveQuotientGradedClosedSpan (n : ℕ) (hn : 0 < n) :
    ClosedSubmodule ℂ (Lp ℂ 2 (ginibreMeasure n)) :=
  ⨆ r : {r : ℕ // 0 < r},
    ginibreFiniteQuotientDegreeClosedSpan n r.1 hn

theorem ginibrePositiveQuotientGradedClosedSpan_le_graded
    (n : ℕ) (hn : 0 < n) :
    ginibrePositiveQuotientGradedClosedSpan n hn ≤
      ginibreFiniteQuotientGradedClosedSpan n hn := by
  apply iSup_le
  intro r
  exact le_iSup (fun d : ℕ ↦ ginibreFiniteQuotientDegreeClosedSpan n d hn) r.1

theorem ginibreFiniteQuotientDegreeClosedSpan_le_positive
    (n r : ℕ) (hn : 0 < n) (hr : 0 < r) :
    ginibreFiniteQuotientDegreeClosedSpan n r hn ≤
      ginibrePositiveQuotientGradedClosedSpan n hn := by
  exact le_iSup (fun d : {d : ℕ // 0 < d} ↦
    ginibreFiniteQuotientDegreeClosedSpan n d.1 hn) ⟨r, hr⟩

theorem ginibreGradedClosedSpan_eq_degreeZero_sup_positive
    (n : ℕ) (hn : 0 < n) :
    ginibreFiniteQuotientGradedClosedSpan n hn =
      ginibreFiniteQuotientDegreeClosedSpan n 0 hn ⊔
        ginibrePositiveQuotientGradedClosedSpan n hn := by
  apply le_antisymm
  · apply iSup_le
    intro r
    by_cases hr : r = 0
    · subst r
      exact le_sup_left
    · exact (ginibreFiniteQuotientDegreeClosedSpan_le_positive n r hn
        (Nat.pos_of_ne_zero hr)).trans le_sup_right
  · apply sup_le
    · exact le_iSup (fun d : ℕ ↦
        ginibreFiniteQuotientDegreeClosedSpan n d hn) 0
    · exact ginibrePositiveQuotientGradedClosedSpan_le_graded n hn

/-- Algebraic sum of the closed positive-degree holomorphic quotient sectors. -/
def ginibrePositiveQuotientAlgebraicSpan (n : ℕ) (hn : 0 < n) :
    Submodule ℂ (Lp ℂ 2 (ginibreMeasure n)) :=
  ⨆ r : {r : ℕ // 0 < r},
    (ginibreFiniteQuotientDegreeClosedSpan n r.1 hn).toSubmodule

theorem inner_star_eq_zero_of_mem_positiveQuotientAlgebraicSpan
    {n : ℕ} (hn : 0 < n) {x y : Lp ℂ 2 (ginibreMeasure n)}
    (hx : x ∈ ginibrePositiveQuotientAlgebraicSpan n hn)
    (hy : y ∈ ginibrePositiveQuotientAlgebraicSpan n hn) :
    inner ℂ x (star y) = 0 := by
  refine Submodule.iSup_induction
    (fun r : {r : ℕ // 0 < r} ↦
      (ginibreFiniteQuotientDegreeClosedSpan n r.1 hn).toSubmodule)
    (motive := fun x ↦ inner ℂ x (star y) = 0)
    hx ?_ (by simp) (fun a b ha hb ↦ by rw [inner_add_left, ha, hb, add_zero])
  intro r xr hxr
  refine Submodule.iSup_induction
    (fun s : {s : ℕ // 0 < s} ↦
      (ginibreFiniteQuotientDegreeClosedSpan n s.1 hn).toSubmodule)
    (motive := fun y ↦ inner ℂ xr (star y) = 0)
    hy ?_ (by
      have hz : star (0 : Lp ℂ 2 (ginibreMeasure n)) = 0 := by
        apply norm_eq_zero.mp
        rw [Lp_norm_star, norm_zero]
      rw [hz, inner_zero_right]) (fun a b ha hb ↦ by
      rw [Lp_star_add, inner_add_right, ha, hb, add_zero])
  intro s ys hys
  exact inner_star_eq_zero_of_mem_finiteQuotientDegreeClosures hn
    (Nat.add_pos_left r.2 s.1) hxr hys

private def ginibreLpConjugationIsometry (n : ℕ) :
    Lp ℂ 2 (ginibreMeasure n) →ₗᵢ[ℝ] Lp ℂ 2 (ginibreMeasure n) where
  toLinearMap :=
    { toFun := star
      map_add' := Lp_star_add
      map_smul' := Lp_star_real_smul }
  norm_map' := Lp_norm_star

private theorem inner_star_eq_zero_positiveClosure_left
    {n : ℕ} (hn : 0 < n) {x y : Lp ℂ 2 (ginibreMeasure n)}
    (hx : x ∈ ginibrePositiveQuotientGradedClosedSpan n hn)
    (hy : y ∈ ginibrePositiveQuotientAlgebraicSpan n hn) :
    inner ℂ x (star y) = 0 := by
  rw [ginibrePositiveQuotientGradedClosedSpan, ClosedSubmodule.mem_iSup] at hx
  change x ∈ closure (ginibrePositiveQuotientAlgebraicSpan n hn :
    Set (Lp ℂ 2 (ginibreMeasure n))) at hx
  let Z : Set (Lp ℂ 2 (ginibreMeasure n)) :=
    {x | inner ℂ x (star y) = 0}
  have hZ : IsClosed Z := by
    apply isClosed_eq
    · exact continuous_inner.comp (continuous_id.prodMk continuous_const)
    · exact continuous_const
  exact (closure_minimal (fun z hz ↦
    inner_star_eq_zero_of_mem_positiveQuotientAlgebraicSpan hn hz hy) hZ) hx

theorem inner_star_eq_zero_of_mem_positiveQuotientGradedClosedSpan
    {n : ℕ} (hn : 0 < n) {x y : Lp ℂ 2 (ginibreMeasure n)}
    (hx : x ∈ ginibrePositiveQuotientGradedClosedSpan n hn)
    (hy : y ∈ ginibrePositiveQuotientGradedClosedSpan n hn) :
    inner ℂ x (star y) = 0 := by
  rw [ginibrePositiveQuotientGradedClosedSpan, ClosedSubmodule.mem_iSup] at hy
  change y ∈ closure (ginibrePositiveQuotientAlgebraicSpan n hn :
    Set (Lp ℂ 2 (ginibreMeasure n))) at hy
  let Z : Set (Lp ℂ 2 (ginibreMeasure n)) :=
    {y | inner ℂ x (star y) = 0}
  have hZ : IsClosed Z := by
    apply isClosed_eq
    · exact continuous_inner.comp
        (continuous_const.prodMk (ginibreLpConjugationIsometry n).continuous)
    · exact continuous_const
  exact (closure_minimal (fun z hz ↦
    inner_star_eq_zero_positiveClosure_left hn hx hz) hZ) hy

/-- The complex `L²` representative of a centered real observable is fixed
by pointwise conjugation. -/
theorem star_centeredObservableL2 {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    star (centeredObservableL2 hn f hf) = centeredObservableL2 hn f hf := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (centeredObservableL2 hn f hf),
    centeredObservableL2_coeFn hn f hf] with z hs hc
  rw [hs]
  calc
    star ((centeredObservableL2 hn f hf) z) =
        star (centeredObservable n f z : ℂ) := congrArg star hc
    _ = (centeredObservable n f z : ℂ) := by simp
    _ = (centeredObservableL2 hn f hf) z := hc.symm

theorem integral_centeredObservable_eq_zero {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    ∫ z, centeredObservable n f z ∂ginibreMeasure n = 0 := by
  let := ginibreProbabilityInstance hn
  have hfi : Integrable f (ginibreMeasure n) :=
    hf.1.continuous.integrable_of_hasCompactSupport hf.2.1
  simp only [centeredObservable]
  rw [integral_sub hfi (integrable_const (smoothGinibreMean n f))]
  simp [smoothGinibreMean]

theorem inner_ginibreConstantL2_centeredObservableL2_eq_zero
    {n : ℕ} (hn : 0 < n) (a : ℂ)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    inner ℂ (ginibreConstantL2 n hn a) (centeredObservableL2 hn f hf) = 0 := by
  rw [MeasureTheory.L2.inner_def]
  let := ginibreProbabilityInstance hn
  rw [integral_congr_ae (show
    (fun z ↦ inner ℂ ((ginibreConstantL2 n hn a) z)
      ((centeredObservableL2 hn f hf) z)) =ᵐ[ginibreMeasure n]
      (fun z ↦ (centeredObservable n f z : ℂ) * star a) by
    filter_upwards [Lp.coeFn_const (α := Configuration n)
        (μ := ginibreMeasure n) (p := (2 : ℝ≥0∞)) a,
      centeredObservableL2_coeFn hn f hf] with z ha hc
    change inner ℂ ((Lp.const 2 (ginibreMeasure n) a) z)
      ((centeredObservableL2 hn f hf) z) = _
    rw [ha, hc]
    simp [RCLike.inner_apply])]
  rw [integral_mul_const]
  have hz : ∫ z, (centeredObservable n f z : ℂ) ∂ginibreMeasure n = 0 := by
    rw [integral_complex_ofReal, integral_centeredObservable_eq_zero hn f hf]
    simp
  rw [hz, zero_mul]

theorem inner_eq_zero_of_mem_constants_centeredObservableL2
    {n : ℕ} (hn : 0 < n) {c : Lp ℂ 2 (ginibreMeasure n)}
    (hc : c ∈ ginibreConstantClosedSubspace n hn)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    inner ℂ c (centeredObservableL2 hn f hf) = 0 := by
  rcases hc with ⟨a, rfl⟩
  exact inner_ginibreConstantL2_centeredObservableL2_eq_zero hn a f hf

theorem degreeZero_orthogonal_positiveGraded
    {n : ℕ} (hn : 0 < n) {c p : Lp ℂ 2 (ginibreMeasure n)}
    (hc : c ∈ ginibreFiniteQuotientDegreeClosedSpan n 0 hn)
    (hp : p ∈ ginibrePositiveQuotientGradedClosedSpan n hn) :
    inner ℂ c p = 0 := by
  rw [ginibrePositiveQuotientGradedClosedSpan, ClosedSubmodule.mem_iSup] at hp
  let Z : Set (Lp ℂ 2 (ginibreMeasure n)) := {p | inner ℂ c p = 0}
  have hZ : IsClosed Z := by
    apply isClosed_eq
    · exact continuous_inner.comp (continuous_const.prodMk continuous_id)
    · exact continuous_const
  apply (closure_minimal ?_ hZ) hp
  intro p hp
  refine Submodule.iSup_induction
    (fun r : {r : ℕ // 0 < r} ↦
      (ginibreFiniteQuotientDegreeClosedSpan n r.1 hn).toSubmodule)
    (motive := fun p ↦ p ∈ Z)
    hp ?_ (by
      change inner ℂ c (0 : Lp ℂ 2 (ginibreMeasure n)) = 0
      simp)
      (fun x y hx hy ↦ by
        change inner ℂ c (x + y) = 0
        rw [inner_add_right, hx, hy, add_zero])
  intro r x hx
  change inner ℂ c x = 0
  have hxc := ginibreFiniteQuotientDegreeClosedSpan_orthogonal hn
    (Nat.ne_of_lt r.2) hc x hx
  rw [← inner_conj_symm c x, hxc, map_zero]

theorem eq_zero_of_mem_holomorphic_of_orthogonal_degreeZero_positive
    {n : ℕ} (hn : 0 < n) {d : Lp ℂ 2 (ginibreMeasure n)}
    (hdH : d ∈ ginibreHolomorphicAmbientClosedSpan n hn)
    (hdC : ∀ c ∈ ginibreFiniteQuotientDegreeClosedSpan n 0 hn,
      inner ℂ d c = 0)
    (hdP : ∀ p ∈ ginibrePositiveQuotientGradedClosedSpan n hn,
      inner ℂ d p = 0) : d = 0 := by
  have hdH' : d ∈
      ginibreFiniteQuotientDegreeClosedSpan n 0 hn ⊔
        ginibrePositiveQuotientGradedClosedSpan n hn := by
    rw [ginibreHolomorphicAmbientClosedSpan_eq_graded,
      ginibreGradedClosedSpan_eq_degreeZero_sup_positive] at hdH
    exact hdH
  rw [ClosedSubmodule.mem_sup] at hdH'
  let Z : Set (Lp ℂ 2 (ginibreMeasure n)) := {z | inner ℂ d z = 0}
  have hZ : IsClosed Z := by
    apply isClosed_eq
    · exact continuous_inner.comp (continuous_const.prodMk continuous_id)
    · exact continuous_const
  have hsub :
      {z | z ∈ (ginibreFiniteQuotientDegreeClosedSpan n 0 hn).toSubmodule ⊔
        (ginibrePositiveQuotientGradedClosedSpan n hn).toSubmodule} ⊆ Z := by
    intro z hz
    rcases Submodule.mem_sup.mp hz with ⟨c, hc, p, hp, rfl⟩
    change inner ℂ d (c + p) = 0
    rw [inner_add_right, hdC c hc, hdP p hp, add_zero]
  have hdd : inner ℂ d d = 0 := (closure_minimal hsub hZ) hdH'
  exact inner_self_eq_zero.mp hdd

theorem holomorphicProjection_centeredObservable_mem_positive
    {n : ℕ} (hn : 0 < n) (f : Configuration n → ℝ)
    (hf : IsTheoremOneNineCore f) :
    (ginibreHolomorphicAmbientClosedSpan n hn).starProjection
        (centeredObservableL2 hn f hf) ∈
      ginibrePositiveQuotientGradedClosedSpan n hn := by
  let H := ginibreHolomorphicAmbientClosedSpan n hn
  let P := ginibrePositiveQuotientGradedClosedSpan n hn
  let u := centeredObservableL2 hn f hf
  let h := H.starProjection u
  let q := P.starProjection h
  have hhH : h ∈ H.toSubmodule := by
    exact Submodule.starProjection_apply_mem H.toSubmodule u
  have hqP : q ∈ P.toSubmodule := by
    exact Submodule.starProjection_apply_mem P.toSubmodule h
  have hPH : P ≤ H := by
    dsimp [P, H]
    rw [ginibreHolomorphicAmbientClosedSpan_eq_graded]
    exact ginibrePositiveQuotientGradedClosedSpan_le_graded n hn
  have hqH : q ∈ H := hPH hqP
  have hdH : h - q ∈ H := H.sub_mem hhH hqH
  have hdP : ∀ p ∈ P, inner ℂ (h - q) p = 0 := by
    intro p hp
    exact Submodule.starProjection_inner_eq_zero h p hp
  have hhC : ∀ c ∈ ginibreFiniteQuotientDegreeClosedSpan n 0 hn,
      inner ℂ h c = 0 := by
    intro c hc
    have hcconst : c ∈ ginibreConstantClosedSubspace n hn := by
      rw [← ginibreFiniteQuotientDegreeZero_eq_constants n hn]
      exact hc
    have hcu : inner ℂ c u = 0 :=
      inner_eq_zero_of_mem_constants_centeredObservableL2 hn hcconst f hf
    have huc : inner ℂ u c = 0 := by
      rw [← inner_conj_symm u c, hcu, map_zero]
    have hcH : c ∈ H := by
      dsimp [H]
      rw [ginibreHolomorphicAmbientClosedSpan_eq_graded]
      exact le_iSup (fun d : ℕ ↦
        ginibreFiniteQuotientDegreeClosedSpan n d hn) 0 hc
    have hres : inner ℂ (u - h) c = 0 :=
      Submodule.starProjection_inner_eq_zero u c hcH
    rw [inner_sub_left] at hres
    rw [huc, zero_sub] at hres
    exact neg_eq_zero.mp hres
  have hdC : ∀ c ∈ ginibreFiniteQuotientDegreeClosedSpan n 0 hn,
      inner ℂ (h - q) c = 0 := by
    intro c hc
    have hcq := degreeZero_orthogonal_positiveGraded hn hc hqP
    have hqc : inner ℂ q c = 0 := by
      rw [← inner_conj_symm q c, hcq, map_zero]
    rw [inner_sub_left, hhC c hc, hqc, sub_zero]
  have hd0 := eq_zero_of_mem_holomorphic_of_orthogonal_degreeZero_positive
    hn hdH hdC hdP
  have hhq : h = q := sub_eq_zero.mp hd0
  have : h ∈ P := by rwa [hhq]
  simpa [h, P] using this

theorem inner_holomorphicProjection_star_eq_zero
    {n : ℕ} (hn : 0 < n) (f : Configuration n → ℝ)
    (hf : IsTheoremOneNineCore f) :
    let h := (ginibreHolomorphicAmbientClosedSpan n hn).starProjection
      (centeredObservableL2 hn f hf)
    inner ℂ h (star h) = 0 := by
  dsimp
  apply inner_star_eq_zero_of_mem_positiveQuotientGradedClosedSpan hn
  · exact holomorphicProjection_centeredObservable_mem_positive hn f hf
  · exact holomorphicProjection_centeredObservable_mem_positive hn f hf

private theorem inner_Lp_star_star {n : ℕ}
    (x y : Lp ℂ 2 (ginibreMeasure n)) :
    inner ℂ (star x) (star y) = star (inner ℂ x y) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  rw [integral_congr_ae (show
    (fun z ↦ inner ℂ ((star x) z) ((star y) z)) =ᵐ[ginibreMeasure n]
      (fun z ↦ star (inner ℂ (x z) (y z))) by
    filter_upwards [Lp.coeFn_star x, Lp.coeFn_star y] with z hx hy
    rw [hx, hy]
    simp [RCLike.inner_apply])]
  exact integral_conj

/-- Pythagorean identity for the three-term real/holomorphic geometry once
the three pairwise orthogonality relations have been established. -/
theorem norm_sq_eq_two_mul_norm_sq_add_of_h_star_remainder_orthogonal
    {n : ℕ} (h r : Lp ℂ 2 (ginibreMeasure n))
    (hhs : inner ℂ h (star h) = 0)
    (hhr : inner ℂ h r = 0)
    (hsr : inner ℂ (star h) r = 0) :
    ‖h + star h + r‖ ^ 2 = 2 * ‖h‖ ^ 2 + ‖r‖ ^ 2 := by
  simp only [pow_two]
  have hadd : inner ℂ (h + star h) r = 0 := by
    rw [inner_add_left, hhr, hsr, add_zero]
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hadd]
  rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hhs]
  rw [Lp_norm_star]
  ring

/-- The complete centered holomorphic/conjugate/remainder geometry. -/
theorem centeredHolomorphicRemainderGeometry
    {n : ℕ} (hn : 0 < n) (f : Configuration n → ℝ)
    (hf : IsTheoremOneNineCore f) :
    let u := centeredObservableL2 hn f hf
    let h := (ginibreHolomorphicAmbientClosedSpan n hn).starProjection u
    let r := u - h - star h
    inner ℂ h (star h) = 0 ∧ inner ℂ h r = 0 ∧
      inner ℂ (star h) r = 0 ∧
      smoothGinibreVariance n f = 2 * ‖h‖ ^ 2 + ‖r‖ ^ 2 := by
  dsimp
  let u := centeredObservableL2 hn f hf
  let H := ginibreHolomorphicAmbientClosedSpan n hn
  let h := H.starProjection u
  let r := u - h - star h
  have hhs : inner ℂ h (star h) = 0 := by
    exact inner_holomorphicProjection_star_eq_zero hn f hf
  have hhH : h ∈ H.toSubmodule := by
    exact Submodule.starProjection_apply_mem H.toSubmodule u
  have heh : inner ℂ (u - h) h = 0 :=
    Submodule.starProjection_inner_eq_zero u h hhH
  have hhe : inner ℂ h (u - h) = 0 := by
    rw [← inner_conj_symm h (u - h), heh, map_zero]
  have hhr : inner ℂ h r = 0 := by
    dsimp [r]
    rw [inner_sub_right, hhe, hhs, sub_zero]
  have hstaru : star u = u := star_centeredObservableL2 hn f hf
  have hstarsub : star (u - h) = u - star h := by
    rw [sub_eq_add_neg, Lp_star_add]
    have hneg : star (-h) = -star h := by
      simpa using Lp_star_real_smul (-1) h
    rw [hneg, hstaru]
    simp [sub_eq_add_neg]
  have hse : inner ℂ (star h) (u - star h) = 0 := by
    have hc := inner_Lp_star_star h (u - h)
    rw [hhe, hstarsub] at hc
    simpa using hc
  have hsr : inner ℂ (star h) r = 0 := by
    dsimp [r]
    rw [inner_sub_right, inner_sub_right]
    have hsh : inner ℂ (star h) h = 0 := by
      rw [← inner_conj_symm (star h) h, hhs, map_zero]
    rw [hsh, sub_zero]
    simpa [inner_sub_right] using hse
  refine ⟨hhs, hhr, hsr, ?_⟩
  have hnorm := norm_sq_eq_two_mul_norm_sq_add_of_h_star_remainder_orthogonal
    h r hhs hhr hsr
  have hur : h + star h + r = u := by
    dsimp [r]
    abel
  rw [hur] at hnorm
  rw [← norm_sq_centeredObservableL2 hn f hf]
  exact hnorm

@[simp] theorem ginibreSymmetricConjugation_coe (n : ℕ)
    (u : ginibreSymmetricL2 n) :
    (ginibreSymmetricConjugation n u).1 = star u.1 := rfl

@[simp] theorem ginibreSymmetricConjugation_involutive (n : ℕ)
    (u : ginibreSymmetricL2 n) :
    ginibreSymmetricConjugation n (ginibreSymmetricConjugation n u) = u := by
  apply Subtype.ext
  simp [ginibreSymmetricConjugation]

/-- Pointwise conjugation as a real-linear isometric involution. -/
def ginibreSymmetricConjugationEquiv (n : ℕ) :
    ginibreSymmetricL2 n ≃ₗᵢ[ℝ] ginibreSymmetricL2 n where
  toFun := ginibreSymmetricConjugation n
  invFun := ginibreSymmetricConjugation n
  left_inv := ginibreSymmetricConjugation_involutive n
  right_inv := ginibreSymmetricConjugation_involutive n
  map_add' u v := by
    apply Subtype.ext
    exact Lp_star_add u.1 v.1
  map_smul' r u := by
    apply Subtype.ext
    exact Lp_star_real_smul r u.1
  norm_map' u := by
    change ‖star u.1‖ = ‖u.1‖
    exact Lp_norm_star u.1

@[simp] theorem ginibreSymmetricConjugationEquiv_apply (n : ℕ)
    (u : ginibreSymmetricL2 n) :
    ginibreSymmetricConjugationEquiv n u = ginibreSymmetricConjugation n u :=
  rfl

end
end GinibrePoincare
