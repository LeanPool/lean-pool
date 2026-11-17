/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GlobalPhaseAction.lean.
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
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import LeanPool.GinibrePoincare.Analysis.ComplexGaussianDensity
public import LeanPool.GinibrePoincare.Analysis.MeasureTransport
public import LeanPool.GinibrePoincare.Analysis.VandermondeL2
public import LeanPool.GinibrePoincare.Analysis.VandermondeL2Inverse
public import LeanPool.GinibrePoincare.Analysis.HermiteL2Family
public import LeanPool.GinibrePoincare.Analysis.HermiteEnergy
public import Mathlib.RingTheory.RootsOfUnity.Complex
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! # Global phase rotations -/


@[expose] public section


open scoped BigOperators ComplexConjugate ENNReal
open MeasureTheory

namespace GinibrePoincare

noncomputable section

/-- Simultaneous multiplication of every particle coordinate by a phase. -/
def globalPhase {n : ℕ} (u : ℂ) (z : Configuration n) : Configuration n :=
  fun i ↦ u * z i

@[simp] theorem globalPhase_apply {n : ℕ} (u : ℂ)
    (z : Configuration n) (i : Fin n) : globalPhase u z i = u * z i := rfl

@[simp] theorem globalPhase_one {n : ℕ} (z : Configuration n) :
    globalPhase 1 z = z := by ext; simp

theorem globalPhase_mul {n : ℕ} (u v : ℂ) (z : Configuration n) :
    globalPhase u (globalPhase v z) = globalPhase (u * v) z := by
  ext i
  simp [globalPhase, mul_assoc]

def totalHolomorphicDegree {n : ℕ} (p : Fin n → ℕ) : ℕ := ∑ i, p i

/-- Total degree of the `n`-particle Vandermonde. -/
def vandermondeDegree (n : ℕ) : ℕ := Fintype.card (OrderedParticlePair n)

theorem vandermondeDegree_eq_sum_Ioi_card (n : ℕ) :
    vandermondeDegree n = ∑ i : Fin n, (Finset.Ioi i).card := by
  unfold vandermondeDegree
  rw [Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  exact Fintype.card_coe _

theorem inner_eq_zero_of_isometry_eigencharacters
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →ₗᵢ[ℂ] E) (x y : E) (a b : ℂ)
    (hx : T x = a • x) (hy : T y = b • y)
    (hsep : conj a * b ≠ 1) : inner ℂ x y = 0 := by
  have hinner := T.inner_map_map x y
  rw [hx, hy, inner_smul_left, inner_smul_right] at hinner
  have hmul : (conj a * b - 1) * inner ℂ x y = 0 := by
    calc
      _ = conj a * b * inner ℂ x y - inner ℂ x y := by ring
      _ = 0 := sub_eq_zero.mpr (by simpa [mul_assoc] using hinner)
  exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hsep)

/-- The real `2 × 2` matrix of multiplication by `u`. -/
def complexMultiplicationMatrix (u : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![u.re, -u.im; u.im, u.re]

/-- Its determinant is the squared complex norm. -/
theorem det_complexMultiplicationMatrix (u : ℂ) :
    (complexMultiplicationMatrix u).det = Complex.normSq u := by
  simp [complexMultiplicationMatrix, Matrix.det_fin_two, Complex.normSq_apply]

/-- In real coordinates, the explicit matrix acts as complex
multiplication. -/
theorem toLin_complexMultiplicationMatrix (u z : ℂ) :
    Matrix.toLin' (complexMultiplicationMatrix u)
        (Complex.measurableEquivPi z) =
      Complex.measurableEquivPi (u * z) := by
  funext i
  fin_cases i <;>
    simp only [Matrix.toLin'_apply]
  all_goals simp [complexMultiplicationMatrix, Matrix.mulVec,
      Complex.mul_re, Complex.mul_im] ; ring

/-- Multiplication by a unit complex number preserves planar Lebesgue
measure. -/
theorem measurePreserving_complex_mul_of_norm_one (u : ℂ) (hu : ‖u‖ = 1) :
    MeasurePreserving (fun z : ℂ ↦ u * z) volume volume := by
  have hnormSq : Complex.normSq u = 1 := by
    rw [← Complex.sq_norm, hu]
    norm_num
  have hdet : (complexMultiplicationMatrix u).det ≠ 0 := by
    rw [det_complexMultiplicationMatrix, hnormSq]
    norm_num
  have hmap := Real.map_matrix_volume_pi_eq_smul_volume_pi hdet
  have hmap' : Measure.map (Matrix.toLin' (complexMultiplicationMatrix u)) volume =
      (volume : Measure (Fin 2 → ℝ)) := by
    rw [hmap, det_complexMultiplicationMatrix, hnormSq]
    simp
  have hlinear : MeasurePreserving
      (Matrix.toLin' (complexMultiplicationMatrix u)) volume volume :=
    ⟨(Matrix.toLin' (complexMultiplicationMatrix u)).continuous_of_finiteDimensional.measurable,
      hmap'⟩
  have hcomp := Complex.volume_preserving_equiv_pi.symm.comp
    (hlinear.comp Complex.volume_preserving_equiv_pi)
  have hfun :
      (Complex.measurableEquivPi.symm ∘
        Matrix.toLin' (complexMultiplicationMatrix u) ∘
          Complex.measurableEquivPi) = (fun z : ℂ ↦ u * z) := by
    funext z
    apply Complex.measurableEquivPi.injective
    simp only [Function.comp_apply, MeasurableEquiv.apply_symm_apply]
    exact toLin_complexMultiplicationMatrix u z
  rw [hfun] at hcomp
  exact hcomp

/-- Multiplication by a nonzero complex scalar as a measurable equivalence. -/
def complexMulMeasurableEquiv (u : ℂ) (hu : u ≠ 0) : ℂ ≃ᵐ ℂ where
  toFun z := u * z
  invFun z := u⁻¹ * z
  left_inv z := by field_simp
  right_inv z := by field_simp
  measurable_toFun := (continuous_const.mul continuous_id).measurable
  measurable_invFun := (continuous_const.mul continuous_id).measurable

theorem complexCoordinateGaussianDensity_globalPhase (n : ℕ) (u z : ℂ)
    (hu : ‖u‖ = 1) :
    complexCoordinateGaussianDensity n (u * z) =
      complexCoordinateGaussianDensity n z := by
  unfold complexCoordinateGaussianDensity
  congr 2
  rw [Complex.normSq_mul, ← Complex.sq_norm, hu]
  norm_num

/-- A unit phase preserves one complex Gaussian coordinate law. -/
theorem measurePreserving_complexCoordinateGaussian_mul {n : ℕ} (hn : 0 < n)
    (u : ℂ) (hu : ‖u‖ = 1) :
    MeasurePreserving (fun z : ℂ ↦ u * z)
      (complexCoordinateGaussianProbability n : Measure ℂ)
      (complexCoordinateGaussianProbability n : Measure ℂ) := by
  have hu0 : u ≠ 0 := by
    intro h
    subst u
    simp at hu
  let e := complexMulMeasurableEquiv u hu0
  rw [complexCoordinateGaussianMeasure_eq_withDensity hn]
  refine ⟨e.measurable, ?_⟩
  have hbase : MeasurePreserving e (volume : Measure ℂ) volume := by
    exact measurePreserving_complex_mul_of_norm_one u hu
  have hd : complexCoordinateGaussianDensity n ∘ e =
      complexCoordinateGaussianDensity n := by
    funext z
    exact complexCoordinateGaussianDensity_globalPhase n u z hu
  have hm := MeasurePreserving.map_withDensity_comp e hbase
    (measurable_complexCoordinateGaussianDensity n)
  change Measure.map e
      ((volume : Measure ℂ).withDensity (complexCoordinateGaussianDensity n)) =
    (volume : Measure ℂ).withDensity (complexCoordinateGaussianDensity n)
  simpa only [hd] using hm

/-- A unit global phase preserves the finite product complex Gaussian law. -/
theorem measurePreserving_globalPhase_complexGaussianMeasure {n : ℕ}
    (hn : 0 < n) (u : ℂ) (hu : ‖u‖ = 1) :
    MeasurePreserving (globalPhase u) (complexGaussianMeasure n)
      (complexGaussianMeasure n) := by
  unfold complexGaussianMeasure complexGaussianProbability
  simp only [ProbabilityMeasure.toMeasure_pi]
  exact measurePreserving_pi _ _ fun _ ↦
    measurePreserving_complexCoordinateGaussian_mul hn u hu

theorem vandermonde_globalPhase (n : ℕ) (u : ℂ) (z : Configuration n) :
    vandermonde (globalPhase u z) =
      u ^ (∑ i : Fin n, (Finset.Ioi i).card) * vandermonde z := by
  rw [vandermonde_eq_product, vandermonde_eq_product]
  simp_rw [globalPhase_apply, ← mul_sub]
  simp_rw [Finset.prod_mul_distrib, Finset.prod_const]
  have hp : (∏ i : Fin n, u ^ (Finset.Ioi i).card) =
      u ^ ∑ i : Fin n, (Finset.Ioi i).card := by
    simpa using (Finset.prod_pow_eq_pow_sum Finset.univ
      (fun i : Fin n ↦ (Finset.Ioi i).card) u)
  rw [hp]

theorem vandermondeDensity_globalPhase (n : ℕ) (u : ℂ)
    (hu : ‖u‖ = 1) (z : Configuration n) :
    vandermondeDensity (globalPhase u z) = vandermondeDensity z := by
  unfold vandermondeDensity vandermondeWeight
  rw [vandermonde_globalPhase]
  rw [Complex.normSq_mul]
  have hp : Complex.normSq
      (u ^ ∑ i : Fin n, (Finset.Ioi i).card) = 1 := by
    rw [← Complex.sq_norm, norm_pow, hu]
    norm_num
  rw [hp, one_mul]

/-- Coordinatewise unit multiplication as a measurable equivalence. -/
def globalPhaseMeasurableEquiv {n : ℕ} (u : ℂ) (hu : u ≠ 0) :
    Configuration n ≃ᵐ Configuration n :=
  MeasurableEquiv.piCongrRight (fun _ ↦ complexMulMeasurableEquiv u hu)

@[simp] theorem globalPhaseMeasurableEquiv_apply {n : ℕ} (u : ℂ)
    (hu : u ≠ 0) (z : Configuration n) :
    globalPhaseMeasurableEquiv u hu z = globalPhase u z := rfl

/-- A unit global phase preserves the normalized Ginibre law. -/
theorem measurePreserving_globalPhase_ginibreMeasure {n : ℕ}
    (hn : 0 < n) (u : ℂ) (hu : ‖u‖ = 1) :
    MeasurePreserving (globalPhase u) (ginibreMeasure n) (ginibreMeasure n) := by
  have hu0 : u ≠ 0 := by
    intro h
    subst u
    simp at hu
  let e := globalPhaseMeasurableEquiv (n := n) u hu0
  refine ⟨e.measurable, ?_⟩
  unfold ginibreMeasure rawGinibreMeasure
  have hmeas : Measurable (globalPhase u : Configuration n → Configuration n) := e.measurable
  rw [Measure.map_smul _ hmeas.aemeasurable]
  congr 1
  have hbase : MeasurePreserving e (complexGaussianMeasure n)
      (complexGaussianMeasure n) := by
    exact measurePreserving_globalPhase_complexGaussianMeasure hn u hu
  have hd : vandermondeDensity ∘ e =
      (vandermondeDensity : Configuration n → ℝ≥0∞) := by
    funext z
    exact vandermondeDensity_globalPhase n u hu z
  nth_rw 1 [← hd]
  exact MeasurePreserving.map_withDensity_comp e hbase
    measurable_vandermondeDensity

theorem multivariateNormalized_zero_globalPhase (n : ℕ) (hn : 0 < n)
    (u : ℂ) (p : Fin n → ℕ) (z : Configuration n) :
    ComplexHermite.multivariateNormalized n hn p 0 (globalPhase u z) =
      u ^ totalHolomorphicDegree p *
        ComplexHermite.multivariateNormalized n hn p 0 z := by
  simp only [ComplexHermite.multivariateNormalized_zero_right]
  simp_rw [globalPhase_apply, mul_pow, ← mul_assoc]
  have hu : (∏ i : Fin n, u ^ p i) = u ^ totalHolomorphicDegree p := by
    simpa [totalHolomorphicDegree] using
      (Finset.prod_pow_eq_pow_sum Finset.univ p u)
  simp_rw [mul_assoc]
  simp_rw [show ∀ x : Fin n,
      (ComplexHermite.oneDimNormalization n (p x) : ℂ) *
          (u ^ p x * z x ^ p x) =
        u ^ p x * ((ComplexHermite.oneDimNormalization n (p x) : ℂ) *
          z x ^ p x) by intro x; ring]
  rw [Finset.prod_mul_distrib, hu]

/-- Pullback by a unit global phase on Gaussian `L²`. -/
def gaussianGlobalPhaseL2 {n : ℕ} (hn : 0 < n) (u : ℂ) (hu : ‖u‖ = 1) :
    Lp ℂ 2 (complexGaussianMeasure n) →ₗᵢ[ℂ]
      Lp ℂ 2 (complexGaussianMeasure n) :=
  Lp.compMeasurePreservingₗᵢ ℂ (globalPhase u)
    (measurePreserving_globalPhase_complexGaussianMeasure hn u hu)

/-- Pullback by a unit global phase on Ginibre `L²`. -/
def ginibreGlobalPhaseL2 {n : ℕ} (hn : 0 < n) (u : ℂ) (hu : ‖u‖ = 1) :
    Lp ℂ 2 (ginibreMeasure n) →ₗᵢ[ℂ] Lp ℂ 2 (ginibreMeasure n) :=
  Lp.compMeasurePreservingₗᵢ ℂ (globalPhase u)
    (measurePreserving_globalPhase_ginibreMeasure hn u hu)

/-- A zero-antiholomorphic Hermite mode is an exact eigenvector of global
phase pullback, with eigenvalue its total holomorphic degree character. -/
theorem gaussianGlobalPhaseL2_hermite_zero (n : ℕ) (hn : 0 < n)
    (u : ℂ) (hu : ‖u‖ = 1) (p : Fin n → ℕ) :
    gaussianGlobalPhaseL2 hn u hu
        (ComplexHermite.hermiteL2Family n hn (p, 0)) =
      u ^ totalHolomorphicDegree p •
        ComplexHermite.hermiteL2Family n hn (p, 0) := by
  apply Lp.ext
  have hsourcecomp :=
    (measurePreserving_globalPhase_complexGaussianMeasure hn u hu).quasiMeasurePreserving.ae_eq_comp
      (ComplexHermite.hermiteL2Family_coeFn n hn (p, 0))
  filter_upwards [Lp.coeFn_compMeasurePreserving
      (ComplexHermite.hermiteL2Family n hn (p, 0))
      (measurePreserving_globalPhase_complexGaussianMeasure hn u hu),
    hsourcecomp,
    ComplexHermite.hermiteL2Family_coeFn n hn (p, 0),
    Lp.coeFn_smul (u ^ totalHolomorphicDegree p)
      (ComplexHermite.hermiteL2Family n hn (p, 0))] with z hcomp hsrc htgt hsmul
  rw [show (gaussianGlobalPhaseL2 hn u hu
      (ComplexHermite.hermiteL2Family n hn (p, 0))) z =
      ComplexHermite.hermiteL2Family n hn (p, 0) (globalPhase u z) by
    exact hcomp]
  change ComplexHermite.hermiteL2Family n hn (p, 0) (globalPhase u z) =
    ComplexHermite.multivariateNormalized n hn p 0 (globalPhase u z) at hsrc
  change ComplexHermite.hermiteL2Family n hn (p, 0) z =
    ComplexHermite.multivariateNormalized n hn p 0 z at htgt
  change (u ^ totalHolomorphicDegree p •
      ComplexHermite.hermiteL2Family n hn (p, 0)) z =
    u ^ totalHolomorphicDegree p *
      ComplexHermite.hermiteL2Family n hn (p, 0) z at hsmul
  rw [hsrc, hsmul, htgt, multivariateNormalized_zero_globalPhase]

/-- Algebraic span of zero-antiholomorphic Hermite modes of a fixed total
holomorphic degree. -/
def gaussianHolomorphicDegreeSpan (n : ℕ) (hn : 0 < n) (d : ℕ) :
    Submodule ℂ (Lp ℂ 2 (complexGaussianMeasure n)) :=
  Submodule.span ℂ
    (ComplexHermite.hermiteL2Family n hn ''
      {(p, q) | q = 0 ∧ totalHolomorphicDegree p = d})

/-- Every vector in a fixed homogeneous span has the corresponding exact
phase character. -/
theorem gaussianGlobalPhaseL2_eq_smul_on_degreeSpan
    (n : ℕ) (hn : 0 < n) (d : ℕ) (u : ℂ) (hu : ‖u‖ = 1)
    {x : Lp ℂ 2 (complexGaussianMeasure n)}
    (hx : x ∈ gaussianHolomorphicDegreeSpan n hn d) :
    gaussianGlobalPhaseL2 hn u hu x = u ^ d • x := by
  unfold gaussianHolomorphicDegreeSpan at hx
  refine Submodule.span_induction
    (p := fun x _ ↦ gaussianGlobalPhaseL2 hn u hu x = u ^ d • x)
    ?_ (by simp) ?_ ?_ hx
  · intro x hx
    obtain ⟨⟨p, q⟩, ⟨hq, hp⟩, rfl⟩ := hx
    subst q
    rw [gaussianGlobalPhaseL2_hermite_zero, hp]
  · intro x y hx hy hxi hyi
    rw [map_add, hxi, hyi, smul_add]
  · intro a x hx hxi
    rw [map_smul, hxi]
    simp [smul_smul, mul_comm]

/-- Fixed-degree spans with separated phase characters are orthogonal. -/
theorem inner_eq_zero_of_mem_holomorphicDegreeSpans
    (n : ℕ) (hn : 0 < n) (d e : ℕ) (u : ℂ) (hu : ‖u‖ = 1)
    {x y : Lp ℂ 2 (complexGaussianMeasure n)}
    (hx : x ∈ gaussianHolomorphicDegreeSpan n hn d)
    (hy : y ∈ gaussianHolomorphicDegreeSpan n hn e)
    (hsep : conj (u ^ d) * u ^ e ≠ 1) :
    inner ℂ x y = 0 :=
  inner_eq_zero_of_isometry_eigencharacters
    (gaussianGlobalPhaseL2 hn u hu) x y (u ^ d) (u ^ e)
    (gaussianGlobalPhaseL2_eq_smul_on_degreeSpan n hn d u hu hx)
    (gaussianGlobalPhaseL2_eq_smul_on_degreeSpan n hn e u hu hy) hsep

/-- Two distinct natural exponents are separated by a unit complex phase. -/
theorem exists_unit_phase_pow_ne (d e : ℕ) (hde : d ≠ e) :
    ∃ u : ℂ, ‖u‖ = 1 ∧ u ^ d ≠ u ^ e := by
  let N := max d e + 1
  let u : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)
  have hN : N ≠ 0 := by
    unfold N
    omega
  have hprim : IsPrimitiveRoot u N := by
    exact Complex.isPrimitiveRoot_exp N hN
  refine ⟨u, ?_, ?_⟩
  · unfold u
    rw [Complex.norm_exp]
    simp
  · intro hp
    apply hde
    apply hprim.pow_inj
    · unfold N
      omega
    · unfold N
      omega
    · exact hp

/-- Homogeneous Gaussian holomorphic spans of unequal degrees are
unconditionally orthogonal. -/
theorem inner_eq_zero_of_mem_holomorphicDegreeSpans_of_ne
    (n : ℕ) (hn : 0 < n) {d e : ℕ} (hde : d ≠ e)
    {x y : Lp ℂ 2 (complexGaussianMeasure n)}
    (hx : x ∈ gaussianHolomorphicDegreeSpan n hn d)
    (hy : y ∈ gaussianHolomorphicDegreeSpan n hn e) :
    inner ℂ x y = 0 := by
  obtain ⟨u, hu, hp⟩ := exists_unit_phase_pow_ne d e hde
  apply inner_eq_zero_of_mem_holomorphicDegreeSpans n hn d e u hu hx hy
  intro hchar
  apply hp
  have hnorm : Complex.normSq (u ^ d) = 1 := by
    rw [← Complex.sq_norm, norm_pow, hu]
    norm_num
  calc
    u ^ d = u ^ d * 1 := by ring
    _ = u ^ d * (conj (u ^ d) * u ^ e) := by rw [hchar]
    _ = (u ^ d * conj (u ^ d)) * u ^ e := by ring
    _ = Complex.normSq (u ^ d) * u ^ e := by rw [Complex.mul_conj]
    _ = u ^ e := by simp [hnorm]

/-- Restrict a finite Hermite coefficient vector to zero antiholomorphic
index and a fixed total holomorphic degree. -/
def coefficientsAtHolomorphicDegree {n : ℕ}
    (c : ComplexHermite.HermiteMultiIndex n →₀ ℂ) (d : ℕ) :
    ComplexHermite.HermiteMultiIndex n →₀ ℂ :=
  c.filter fun pq ↦ pq.2 = 0 ∧ totalHolomorphicDegree pq.1 = d

/-- Holomorphic degrees occurring in a finite zero-antiholomorphic
coefficient vector. -/
def activeHolomorphicDegrees {n : ℕ}
    (c : ComplexHermite.HermiteMultiIndex n →₀ ℂ) : Finset ℕ :=
  c.support.image fun pq ↦ totalHolomorphicDegree pq.1

/-- A finite coefficient vector supported at antiholomorphic index zero is
the finite sum of its homogeneous holomorphic-degree pieces. -/
theorem sum_coefficientsAtHolomorphicDegree {n : ℕ}
    (c : ComplexHermite.HermiteMultiIndex n →₀ ℂ)
    (hc : ∀ pq ∈ c.support, pq.2 = 0) :
    ∑ d ∈ activeHolomorphicDegrees c,
        coefficientsAtHolomorphicDegree c d = c := by
  ext pq
  by_cases hpq : pq ∈ c.support
  · have hd : totalHolomorphicDegree pq.1 ∈ activeHolomorphicDegrees c :=
      Finset.mem_image.mpr ⟨pq, hpq, rfl⟩
    change (Finsupp.lapply pq :
      (ComplexHermite.HermiteMultiIndex n →₀ ℂ) →ₗ[ℂ] ℂ)
        (∑ d ∈ activeHolomorphicDegrees c,
          coefficientsAtHolomorphicDegree c d) = c pq
    simp_rw [map_sum, Finsupp.lapply_apply]
    rw [Finset.sum_eq_single
      (totalHolomorphicDegree pq.1)]
    · simp [coefficientsAtHolomorphicDegree, hc pq hpq]
    · intro d hdmem hne
      simp [coefficientsAtHolomorphicDegree, hne.symm]
    · exact fun hnot ↦ (hnot hd).elim
  · have hz : c pq = 0 := by
      simpa [Finsupp.mem_support_iff] using hpq
    change (Finsupp.lapply pq :
      (ComplexHermite.HermiteMultiIndex n →₀ ℂ) →ₗ[ℂ] ℂ)
        (∑ d ∈ activeHolomorphicDegrees c,
          coefficientsAtHolomorphicDegree c d) = c pq
    simp_rw [map_sum, Finsupp.lapply_apply]
    rw [hz]
    apply Finset.sum_eq_zero
    intro d hd
    unfold coefficientsAtHolomorphicDegree
    simp only [Finsupp.filter_apply]
    split <;> simp [hz]

/-- The associated finite Gaussian Hermite vector decomposes into the sum
of its homogeneous holomorphic-degree pieces. -/
theorem finiteHermiteCombination_eq_sum_holomorphicDegrees
    (n : ℕ) (hn : 0 < n)
    (c : ComplexHermite.HermiteMultiIndex n →₀ ℂ)
    (hc : ∀ pq ∈ c.support, pq.2 = 0) :
    ComplexHermite.finiteHermiteCombination n hn c =
      ∑ d ∈ activeHolomorphicDegrees c,
        ComplexHermite.finiteHermiteCombination n hn
          (coefficientsAtHolomorphicDegree c d) := by
  have hcoeff := sum_coefficientsAtHolomorphicDegree c hc
  have h := congrArg (ComplexHermite.finiteHermiteCombination n hn) hcoeff
  simpa [ComplexHermite.finiteHermiteCombination, map_sum] using h.symm

/-- Every homogeneous piece belongs to its corresponding Gaussian
holomorphic-degree span. -/
theorem finiteHermiteCombination_coefficientsAtHolomorphicDegree_mem
    (n : ℕ) (hn : 0 < n)
    (c : ComplexHermite.HermiteMultiIndex n →₀ ℂ) (d : ℕ) :
    ComplexHermite.finiteHermiteCombination n hn
        (coefficientsAtHolomorphicDegree c d) ∈
      gaussianHolomorphicDegreeSpan n hn d := by
  unfold ComplexHermite.finiteHermiteCombination
  rw [Finsupp.linearCombination_apply]
  apply Submodule.sum_mem
  intro pq hpq
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨pq, ?_, rfl⟩
  have hnz := Finsupp.mem_support_iff.mp hpq
  unfold coefficientsAtHolomorphicDegree at hnz
  simp only [Finsupp.filter_apply] at hnz
  split at hnz
  · exact ‹pq.2 = 0 ∧ totalHolomorphicDegree pq.1 = d›
  · simp at hnz

/-- The polynomial representing a zero-antiholomorphic Hermite mode is
homogeneous in Mathlib's algebraic grading. -/
theorem isHomogeneous_holomorphicHermitePolynomial (n : ℕ)
    (p : Fin n → ℕ) :
    MvPolynomial.IsHomogeneous (holomorphicHermitePolynomial n p)
      (totalHolomorphicDegree p) := by
  unfold holomorphicHermitePolynomial totalHolomorphicDegree
  apply MvPolynomial.IsHomogeneous.prod Finset.univ _ p
  intro i hi
  exact (MvPolynomial.isHomogeneous_X_pow i (p i)).C_mul _

/-- The polynomial Vandermonde is homogeneous of its number of linear
factors. -/
theorem isHomogeneous_polynomialVandermonde (n : ℕ) :
    MvPolynomial.IsHomogeneous (polynomialVandermonde n)
      (vandermondeDegree n) := by
  rw [← prod_orderedPairFactor n]
  unfold vandermondeDegree
  simpa using MvPolynomial.IsHomogeneous.prod
    (Finset.univ : Finset (OrderedParticlePair n)) orderedPairFactor
    (fun _ ↦ 1) (fun p hp ↦ by
      unfold orderedPairFactor
      exact (MvPolynomial.isHomogeneous_X _ _).sub
        (MvPolynomial.isHomogeneous_X _ _))

/-- A nonzero homogeneous alternating polynomial cannot have degree below
the Vandermonde degree. -/
theorem vandermondeDegree_le_of_homogeneous_alternating {n d : ℕ}
    {P : ConfigurationPolynomial n}
    (hP : MvPolynomial.IsHomogeneous P d)
    (hAlt : IsAlternatingConfigurationPolynomial P) (hP0 : P ≠ 0) :
    vandermondeDegree n ≤ d := by
  obtain ⟨Q, hQ, hfactor⟩ := alternating_polynomial_vandermonde_division hAlt
  have hQ0 : Q ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hfactor
    exact hP0 hfactor
  have hdegP := hP.totalDegree hP0
  have hdegV := (isHomogeneous_polynomialVandermonde n).totalDegree
    (polynomialVandermonde_ne_zero n)
  rw [hfactor, MvPolynomial.totalDegree_mul_of_isDomain
    (polynomialVandermonde_ne_zero n) hQ0, hdegV] at hdegP
  omega

/-- A holomorphic coordinate monomial transforms by its degree character. -/
theorem eval_monomial_globalPhase {n : ℕ} (u : ℂ)
    (p : Fin n → ℕ) (z : Configuration n) :
    (∏ i, (globalPhase u z i) ^ p i) =
      u ^ totalHolomorphicDegree p * ∏ i, z i ^ p i := by
  simp_rw [globalPhase_apply, mul_pow]
  have hu : (∏ i : Fin n, u ^ p i) = u ^ totalHolomorphicDegree p := by
    simpa [totalHolomorphicDegree] using
      (Finset.prod_pow_eq_pow_sum Finset.univ p u)
  rw [Finset.prod_mul_distrib, hu]

/-- Functional homogeneity of a holomorphic configuration polynomial. -/
def IsHomogeneousConfigurationPolynomial {n : ℕ} (d : ℕ)
    (P : ConfigurationPolynomial n) : Prop :=
  ∀ u : ℂ, ∀ z : Configuration n,
    MvPolynomial.eval (globalPhase u z) P =
      u ^ d * MvPolynomial.eval z P

/-- The monomial of multiexponent `p` is homogeneous of total degree `p`. -/
theorem isHomogeneous_monomial {n : ℕ} (p : Fin n → ℕ) :
    IsHomogeneousConfigurationPolynomial (totalHolomorphicDegree p)
      (∏ i, MvPolynomial.X i ^ p i : ConfigurationPolynomial n) := by
  intro u z
  simp only [map_prod, map_pow, MvPolynomial.eval_X]
  exact eval_monomial_globalPhase u p z

/-- Algebraic homogeneity implies the expected functional scaling law. -/
theorem isHomogeneousConfigurationPolynomial_of_isHomogeneous {n d : ℕ}
    {P : ConfigurationPolynomial n} (hP : MvPolynomial.IsHomogeneous P d) :
    IsHomogeneousConfigurationPolynomial d P := by
  intro u z
  rw [← P.support_sum_monomial_coeff]
  simp only [map_sum, MvPolynomial.eval_monomial, globalPhase_apply,
    mul_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hmdeg : m.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hP (MvPolynomial.mem_support_iff.mp hm)
  simp only [Finsupp.prod, Finset.prod_mul_distrib]
  have hu : (∏ x ∈ m.support, u ^ m x) = u ^ d := by
    rw [Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_apply, hmdeg]
  rw [hu]
  ring

/-- A finite zero-antiholomorphic Hermite polynomial supported in one total
holomorphic degree is homogeneous in that degree. -/
theorem isHomogeneous_finiteZeroAntiholomorphicHermitePolynomial_of_degree
    {n d : ℕ} (S : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℂ)
    (hdegree : ∀ p ∈ S, totalHolomorphicDegree p = d) :
    MvPolynomial.IsHomogeneous
      (finiteZeroAntiholomorphicHermitePolynomial n S c) d := by
  unfold finiteZeroAntiholomorphicHermitePolynomial
  apply MvPolynomial.IsHomogeneous.sum S _ d
  intro p hp
  rw [← hdegree p hp]
  exact (isHomogeneous_holomorphicHermitePolynomial n p).C_mul _

/-- Homogeneous Vandermonde division, including the exact quotient phase
character away from the (irrelevant) collision locus. -/
theorem homogeneous_alternating_polynomial_division {n d : ℕ}
    {P : ConfigurationPolynomial n}
    (hP : MvPolynomial.IsHomogeneous P d)
    (hAlt : IsAlternatingConfigurationPolynomial P) (hP0 : P ≠ 0) :
    ∃ Q : ConfigurationPolynomial n,
      IsSymmetricConfigurationPolynomial Q ∧
      P = polynomialVandermonde n * Q ∧
      vandermondeDegree n ≤ d ∧
      ∀ (u : ℂ), ‖u‖ = 1 → ∀ z : Configuration n,
        vandermonde z ≠ 0 →
        MvPolynomial.eval (globalPhase u z) Q =
          u ^ (d - vandermondeDegree n) * MvPolynomial.eval z Q := by
  obtain ⟨Q, hQ, hfactor⟩ := alternating_polynomial_vandermonde_division hAlt
  have hle := vandermondeDegree_le_of_homogeneous_alternating hP hAlt hP0
  refine ⟨Q, hQ, hfactor, hle, ?_⟩
  intro u hu z hz
  have hu0 : u ≠ 0 := by
    intro h
    simp [h] at hu
  have hscale :=
    isHomogeneousConfigurationPolynomial_of_isHomogeneous hP u z
  rw [hfactor, map_mul, map_mul, eval_polynomialVandermonde,
    eval_polynomialVandermonde, vandermonde_globalPhase] at hscale
  rw [← vandermondeDegree_eq_sum_Ioi_card] at hscale
  have hpow : u ^ d = u ^ vandermondeDegree n *
      u ^ (d - vandermondeDegree n) := by
    rw [← pow_add, Nat.add_sub_of_le hle]
  rw [hpow] at hscale
  have hs : u ^ vandermondeDegree n *
      (vandermonde z * MvPolynomial.eval (globalPhase u z) Q) =
      u ^ vandermondeDegree n *
        (u ^ (d - vandermondeDegree n) *
          (vandermonde z * MvPolynomial.eval z Q)) := by
    simpa only [mul_assoc] using hscale
  have hscale' := mul_left_cancel₀
    (pow_ne_zero (vandermondeDegree n) hu0) hs
  exact mul_left_cancel₀ hz (by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hscale')

/-- The preceding division theorem specialized to a finite, single-degree
zero-antiholomorphic Hermite sum. -/
theorem finite_homogeneous_zeroHermite_division {n d : ℕ}
    (S : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℂ)
    (hdegree : ∀ p ∈ S, totalHolomorphicDegree p = d)
    (hAlt : IsAlternatingConfigurationPolynomial
      (finiteZeroAntiholomorphicHermitePolynomial n S c))
    (hne : finiteZeroAntiholomorphicHermitePolynomial n S c ≠ 0) :
    ∃ Q : ConfigurationPolynomial n,
      IsSymmetricConfigurationPolynomial Q ∧
      finiteZeroAntiholomorphicHermitePolynomial n S c =
        polynomialVandermonde n * Q ∧
      vandermondeDegree n ≤ d ∧
      ∀ (u : ℂ), ‖u‖ = 1 → ∀ z : Configuration n,
        vandermonde z ≠ 0 →
        MvPolynomial.eval (globalPhase u z) Q =
          u ^ (d - vandermondeDegree n) * MvPolynomial.eval z Q :=
  homogeneous_alternating_polynomial_division
    (isHomogeneous_finiteZeroAntiholomorphicHermitePolynomial_of_degree
      S c hdegree) hAlt hne

/-- In the bottom possible alternating degree, the Vandermonde quotient is
constant. -/
theorem quotient_eq_C_of_bottom_homogeneous_degree {n : ℕ}
    {P Q : ConfigurationPolynomial n}
    (hP : MvPolynomial.IsHomogeneous P (vandermondeDegree n))
    (hP0 : P ≠ 0)
    (hfactor : P = polynomialVandermonde n * Q) :
    Q = MvPolynomial.C (Q.coeff 0) := by
  have hQ0 : Q ≠ 0 := by
    intro hQ
    rw [hQ, mul_zero] at hfactor
    exact hP0 hfactor
  have hdegP := hP.totalDegree hP0
  have hdegV := (isHomogeneous_polynomialVandermonde n).totalDegree
    (polynomialVandermonde_ne_zero n)
  have hdegmul := MvPolynomial.totalDegree_mul_of_isDomain
    (polynomialVandermonde_ne_zero n) hQ0
  rw [← hfactor, hdegP, hdegV] at hdegmul
  have hQdeg : MvPolynomial.totalDegree Q = 0 := by omega
  exact MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hQdeg

/-- Product of the one-dimensional normalization constants in a
zero-antiholomorphic tensor Hermite. -/
def holomorphicTensorNormalization (n : ℕ) (p : Fin n → ℕ) : ℂ :=
  ∏ i, (ComplexHermite.oneDimNormalization n (p i) : ℂ)

theorem holomorphicTensorNormalization_ne_zero (n : ℕ) (hn : 0 < n)
    (p : Fin n → ℕ) : holomorphicTensorNormalization n p ≠ 0 := by
  unfold holomorphicTensorNormalization
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact Complex.ofReal_ne_zero.mpr (by
    unfold ComplexHermite.oneDimNormalization
    positivity)

theorem holomorphicHermitePolynomial_eq_normalization_monomial
    (n : ℕ) (p : Fin n → ℕ) :
    holomorphicHermitePolynomial n p =
      MvPolynomial.C (holomorphicTensorNormalization n p) *
        MvPolynomial.monomial
          (Finsupp.equivFunOnFinite.symm p) 1 := by
  unfold holomorphicHermitePolynomial holomorphicTensorNormalization
  rw [← MvPolynomial.prod_X_pow_eq_monomial]
  simp only [map_prod, Finset.prod_mul_distrib]
  rw [show (∏ i : Fin n, MvPolynomial.X i ^ p i) =
      ∏ i ∈ (Finsupp.equivFunOnFinite.symm p).support,
        MvPolynomial.X i ^ (Finsupp.equivFunOnFinite.symm p) i by
    symm
    apply Finset.prod_subset (by simp)
    intro i hi hi'
    have hp0 : p i = 0 := by
      simpa [Finsupp.equivFunOnFinite] using hi'
    simp [hp0]]

/-- Explicit inversion of the normalization on a holomorphic monomial. -/
theorem C_mul_monomial_eq_smul_holomorphicHermitePolynomial
    (n : ℕ) (hn : 0 < n) (p : Fin n → ℕ) (a : ℂ) :
    MvPolynomial.C a *
        MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm p) 1 =
      MvPolynomial.C (a / holomorphicTensorNormalization n p) *
        holomorphicHermitePolynomial n p := by
  rw [holomorphicHermitePolynomial_eq_normalization_monomial]
  have hN := holomorphicTensorNormalization_ne_zero n hn p
  rw [← mul_assoc, ← map_mul]
  field_simp

/-- Hermite coefficient obtained by dividing a polynomial monomial
coefficient by its nonzero tensor normalization. -/
def holomorphicHermiteCoefficient {n : ℕ} (P : ConfigurationPolynomial n)
    (p : Fin n → ℕ) : ℂ :=
  P.coeff (Finsupp.equivFunOnFinite.symm p) /
    holomorphicTensorNormalization n p

/-- The finite support of a configuration polynomial, viewed as ordinary
multi-index functions. -/
def holomorphicHermiteSupport {n : ℕ} (P : ConfigurationPolynomial n) :
    Finset (Fin n → ℕ) :=
  P.support.image Finsupp.equivFunOnFinite

/-- Every configuration polynomial is exactly its coefficientwise finite
zero-antiholomorphic Hermite expansion. -/
theorem finiteZeroAntiholomorphicHermitePolynomial_support_expansion
    {n : ℕ} (hn : 0 < n) (P : ConfigurationPolynomial n) :
    finiteZeroAntiholomorphicHermitePolynomial n
        (holomorphicHermiteSupport P) (holomorphicHermiteCoefficient P) = P := by
  unfold finiteZeroAntiholomorphicHermitePolynomial holomorphicHermiteSupport
    holomorphicHermiteCoefficient
  rw [Finset.sum_image]
  · calc
      _ = ∑ m ∈ P.support, MvPolynomial.monomial m
          (P.coeff m) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [Finsupp.equivFunOnFinite.symm_apply_apply]
        rw [← C_mul_monomial_eq_smul_holomorphicHermitePolynomial n hn]
        simp [MvPolynomial.monomial_eq]
      _ = P := P.support_sum_monomial_coeff
  · intro a ha b hb hab
    exact Finsupp.equivFunOnFinite.injective hab

/-- The explicit support expansion preserves a polynomial's homogeneous
degree coefficient by coefficient. -/
theorem totalHolomorphicDegree_eq_of_mem_holomorphicHermiteSupport
    {n d : ℕ} {P : ConfigurationPolynomial n}
    (hP : MvPolynomial.IsHomogeneous P d)
    {p : Fin n → ℕ} (hp : p ∈ holomorphicHermiteSupport P) :
    totalHolomorphicDegree p = d := by
  rcases Finset.mem_image.mp hp with ⟨m, hm, rfl⟩
  unfold totalHolomorphicDegree
  have hmdeg : m.degree = d := by
    rw [Finsupp.degree_eq_weight_one]
    exact hP (MvPolynomial.mem_support_iff.mp hm)
  simpa [Finsupp.degree_eq_sum] using hmdeg

/-- Consequently every homogeneous polynomial has an exact finite Hermite
expansion supported in that same degree. -/
theorem homogeneous_polynomial_finiteHermite_expansion {n d : ℕ}
    (hn : 0 < n) {P : ConfigurationPolynomial n}
    (hP : MvPolynomial.IsHomogeneous P d) :
    (∀ p ∈ holomorphicHermiteSupport P,
      totalHolomorphicDegree p = d) ∧
    finiteZeroAntiholomorphicHermitePolynomial n
      (holomorphicHermiteSupport P) (holomorphicHermiteCoefficient P) = P := by
  exact ⟨fun _ hp ↦
    totalHolomorphicDegree_eq_of_mem_holomorphicHermiteSupport hP hp,
    finiteZeroAntiholomorphicHermitePolynomial_support_expansion hn P⟩

/-- Alternation is preserved by taking a homogeneous component. -/
theorem isAlternating_homogeneousComponent {n d : ℕ}
    {P : ConfigurationPolynomial n}
    (hP : IsAlternatingConfigurationPolynomial P) :
    IsAlternatingConfigurationPolynomial (MvPolynomial.homogeneousComponent d P) := by
  intro σ
  have h := congrArg (MvPolynomial.homogeneousComponent d) (hP σ)
  unfold permuteConfigurationPolynomial at h ⊢
  change MvPolynomial.homogeneousComponent d (MvPolynomial.rename σ P) = _ at h
  change MvPolynomial.rename σ (MvPolynomial.homogeneousComponent d P) = _
  rw [← MvPolynomial.rename_homogeneousComponent,
    MvPolynomial.homogeneousComponent_C_mul] at h
  exact h

/-- The finite Gaussian `L²` vector represented by a holomorphic Hermite
sum. -/
def finiteZeroHermiteL2 (n : ℕ) (hn : 0 < n)
    (S : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℂ) :
    Lp ℂ 2 (complexGaussianMeasure n) :=
  ∑ p ∈ S, c p • ComplexHermite.hermiteL2Family n hn (p, 0)

theorem finiteZeroHermiteL2_coeFn (n : ℕ) (hn : 0 < n)
    (S : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℂ) :
    finiteZeroHermiteL2 n hn S c =ᵐ[complexGaussianMeasure n]
      finiteZeroAntiholomorphicHermiteSum n hn S c := by
  unfold finiteZeroHermiteL2 finiteZeroAntiholomorphicHermiteSum
  induction S using Finset.induction_on with
  | empty =>
      filter_upwards [Lp.coeFn_zero ℂ 2 (complexGaussianMeasure n)] with z hz
      change (0 : Lp ℂ 2 (complexGaussianMeasure n)) z = 0
      rw [hz]
      exact Pi.zero_apply z
  | @insert p S hp ih =>
      filter_upwards [Lp.coeFn_add
          (c p • ComplexHermite.hermiteL2Family n hn (p, 0))
          (∑ q ∈ S, c q • ComplexHermite.hermiteL2Family n hn (q, 0)),
        Lp.coeFn_smul (c p) (ComplexHermite.hermiteL2Family n hn (p, 0)),
        ComplexHermite.hermiteL2Family_coeFn n hn (p, 0), ih] with
          z hadd hsmul hmode hsum
      simp only [Finset.sum_insert hp]
      rw [hadd]
      simp only [Pi.add_apply]
      rw [hsmul]
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [hmode, hsum]

theorem finiteZeroHermiteL2_mem_gaussianAlternating {n : ℕ} (hn : 0 < n)
    (S : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℂ)
    (hAlt : IsAlternatingConfigurationPolynomial
      (finiteZeroAntiholomorphicHermitePolynomial n S c)) :
    finiteZeroHermiteL2 n hn S c ∈ gaussianAlternatingL2 n := by
  intro σ
  apply Lp.ext
  have hfun := (finiteHermiteSum_isAlternating_iff hn S c).2 hAlt σ
  have hcoe := finiteZeroHermiteL2_coeFn n hn S c
  have hcoecomp := (gaussian_measurePreserving_permute σ).quasiMeasurePreserving.ae_eq_comp hcoe
  filter_upwards [Lp.coeFn_compMeasurePreserving (finiteZeroHermiteL2 n hn S c)
      (gaussian_measurePreserving_permute σ), hcoecomp, hcoe,
    Lp.coeFn_smul (permutationSign σ) (finiteZeroHermiteL2 n hn S c)] with
      z hperm hsrc htgt hsmul
  rw [show (gaussianPermutationL2 σ (finiteZeroHermiteL2 n hn S c)) z =
    finiteZeroHermiteL2 n hn S c (permute σ z) by exact hperm]
  rw [show (permutationSign σ • finiteZeroHermiteL2 n hn S c) z =
    permutationSign σ • finiteZeroHermiteL2 n hn S c z by exact hsmul]
  change finiteZeroHermiteL2 n hn S c (permute σ z) =
    permutationSign σ * finiteZeroHermiteL2 n hn S c z
  change finiteZeroHermiteL2 n hn S c (permute σ z) =
    _ at hsrc
  rw [hsrc, htgt]
  exact hfun z

/-- Public representative formula for inverse Vandermonde multiplication. -/
theorem inverseVandermondeL2_coeFn_public {n : ℕ} (hn : 0 < n)
    (v : Lp ℂ 2 (complexGaussianMeasure n)) :
    inverseVandermondeL2 n hn v =ᵐ[ginibreMeasure n]
      inverseVandermondeFunction n v := by
  unfold inverseVandermondeL2
  dsimp only
  generalize_proofs h1 h2 h3 h4 h5
  exact (h5 v).coeFn_toLp

/-- The symmetric Ginibre quotient vector attached to an alternating finite
holomorphic Hermite sum. -/
def finiteHomogeneousQuotientL2 {n : ℕ} (hn : 0 < n)
    (S : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℂ)
    (hAlt : finiteZeroHermiteL2 n hn S c ∈ gaussianAlternatingL2 n) :
    ginibreSymmetricL2 n :=
  (vandermondeSymmetricAlternatingEquiv n hn).symm
    ⟨finiteZeroHermiteL2 n hn S c, hAlt⟩

theorem finiteHomogeneousQuotientL2_coeFn {n : ℕ} (hn : 0 < n)
    (S : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℂ)
    (hAlt : finiteZeroHermiteL2 n hn S c ∈ gaussianAlternatingL2 n)
    (Q : ConfigurationPolynomial n)
    (hsum : ∀ z, finiteZeroAntiholomorphicHermiteSum n hn S c z =
      vandermonde z * MvPolynomial.eval z Q) :
    (finiteHomogeneousQuotientL2 hn S c hAlt).1 =ᵐ[ginibreMeasure n]
      fun z ↦ (groundStateNormalization n : ℂ) * MvPolynomial.eval z Q := by
  have hcoe := inverseVandermondeL2_coeFn_public hn
    (finiteZeroHermiteL2 n hn S c)
  have hfinite := (ginibreMeasure_absolutelyContinuous_complexGaussianMeasure n).ae_eq
    (finiteZeroHermiteL2_coeFn n hn S c)
  have hcoll : ginibreMeasure n (collisionSet n) = 0 :=
    (ginibreMeasure_absolutelyContinuous_complexGaussianMeasure n)
      (complexGaussianMeasure_collisionSet n)
  have hout : ∀ᵐ z ∂ginibreMeasure n, z ∉ collisionSet n := by
    rw [ae_iff]
    rw [show {z : Configuration n | ¬ z ∉ collisionSet n} = collisionSet n by
      ext z
      simp]
    exact hcoll
  change inverseVandermondeL2 n hn (finiteZeroHermiteL2 n hn S c) =ᵐ[_] _
  filter_upwards [hcoe, hfinite, hout] with z hin hfin hz
  rw [hin]
  unfold inverseVandermondeFunction inverseVandermondeMultiplier
  rw [hfin, hsum z]
  have hv : vandermonde z ≠ 0 :=
    fun h ↦ hz ((vandermonde_eq_zero_iff z).mp h)
  field_simp

theorem ginibreGlobalPhaseL2_finiteHomogeneousQuotient {n d : ℕ}
    (hn : 0 < n) (S : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℂ)
    (hAlt : finiteZeroHermiteL2 n hn S c ∈ gaussianAlternatingL2 n)
    (Q : ConfigurationPolynomial n)
    (hsum : ∀ z, finiteZeroAntiholomorphicHermiteSum n hn S c z =
      vandermonde z * MvPolynomial.eval z Q)
    (hphase : ∀ (u : ℂ), ‖u‖ = 1 → ∀ z, vandermonde z ≠ 0 →
      MvPolynomial.eval (globalPhase u z) Q =
        u ^ d * MvPolynomial.eval z Q)
    (u : ℂ) (hu : ‖u‖ = 1) :
    ginibreGlobalPhaseL2 hn u hu
        (finiteHomogeneousQuotientL2 hn S c hAlt).1 =
      u ^ d • (finiteHomogeneousQuotientL2 hn S c hAlt).1 := by
  let q := finiteHomogeneousQuotientL2 hn S c hAlt
  change ginibreGlobalPhaseL2 hn u hu q.1 = u ^ d • q.1
  apply Lp.ext
  have hq := finiteHomogeneousQuotientL2_coeFn hn S c hAlt Q hsum
  change q.1 =ᵐ[ginibreMeasure n]
    (fun z ↦ (groundStateNormalization n : ℂ) * MvPolynomial.eval z Q) at hq
  have hqcomp :=
    (measurePreserving_globalPhase_ginibreMeasure hn u hu).quasiMeasurePreserving.ae_eq_comp hq
  have hcoll : ginibreMeasure n (collisionSet n) = 0 :=
    (ginibreMeasure_absolutelyContinuous_complexGaussianMeasure n)
      (complexGaussianMeasure_collisionSet n)
  have hout : ∀ᵐ z ∂ginibreMeasure n, z ∉ collisionSet n := by
    rw [ae_iff]
    rw [show {z : Configuration n | ¬ z ∉ collisionSet n} = collisionSet n by
      ext z
      simp]
    exact hcoll
  filter_upwards [Lp.coeFn_compMeasurePreserving q.1
      (measurePreserving_globalPhase_ginibreMeasure hn u hu),
    hqcomp, hq, Lp.coeFn_smul (u ^ d) q.1, hout] with
      z hcomp hsrc htgt hsmul hz
  rw [show (ginibreGlobalPhaseL2 hn u hu q.1) z =
      q.1 (globalPhase u z) by exact hcomp]
  rw [show (u ^ d • q.1) z = u ^ d • q.1 z by exact hsmul]
  change q.1 (globalPhase u z) =
    (groundStateNormalization n : ℂ) *
      MvPolynomial.eval (globalPhase u z) Q at hsrc
  rw [hsrc]
  simp only [smul_eq_mul]
  rw [htgt, hphase u hu z (fun hv ↦ hz ((vandermonde_eq_zero_iff z).mp hv))]
  ring

/-- Ginibre vectors carrying unequal global-phase degrees are orthogonal. -/
theorem inner_eq_zero_of_ginibre_phase_degrees_ne {n d e : ℕ}
    (hn : 0 < n) (hde : d ≠ e)
    (x y : Lp ℂ 2 (ginibreMeasure n))
    (hx : ∀ (u : ℂ) (hu : ‖u‖ = 1),
      ginibreGlobalPhaseL2 hn u hu x = u ^ d • x)
    (hy : ∀ (u : ℂ) (hu : ‖u‖ = 1),
      ginibreGlobalPhaseL2 hn u hu y = u ^ e • y) :
    inner ℂ x y = 0 := by
  obtain ⟨u, hu, hpow⟩ := exists_unit_phase_pow_ne d e hde
  have hchar : conj (u ^ d) * u ^ e ≠ 1 := by
    intro h
    apply hpow
    calc
      u ^ d = u ^ d * 1 := by ring
      _ = u ^ d * (conj (u ^ d) * u ^ e) := by rw [h]
      _ = (u ^ d * conj (u ^ d)) * u ^ e := by ring
      _ = u ^ e := by
        rw [Complex.mul_conj]
        have hud : ‖u ^ d‖ = 1 := by simp [norm_pow, hu]
        rw [← Complex.sq_norm, hud]
        norm_num
  exact inner_eq_zero_of_isometry_eigencharacters
    (ginibreGlobalPhaseL2 hn u hu) x y (u ^ d) (u ^ e)
      (hx u hu) (hy u hu) hchar

end
end GinibrePoincare
