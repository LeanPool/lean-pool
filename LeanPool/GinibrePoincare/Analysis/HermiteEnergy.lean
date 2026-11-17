/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/HermiteEnergy.lean.
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

public import LeanPool.GinibrePoincare.Analysis.HermiteL2Family

/-! # Finite Hermite expansions and antiholomorphic energy -/


@[expose] public section


open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace GinibrePoincare
namespace ComplexHermite

noncomputable section

/-- A finite Hermite coefficient vector synthesized in Gaussian `L²`. -/
def finiteHermiteCombination (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) :
    Lp ℂ 2 (complexGaussianMeasure n) :=
  Finsupp.linearCombination ℂ (hermiteL2Family n hn) c

/-- Parseval's identity for two finite Hermite expansions. -/
theorem inner_finiteHermiteCombination (n : ℕ) (hn : 0 < n)
    (c d : HermiteMultiIndex n →₀ ℂ) :
    inner ℂ (finiteHermiteCombination n hn c)
        (finiteHermiteCombination n hn d) =
      c.sum fun a z => conj z * d a := by
  exact (orthonormal_hermiteL2Family_gaussian n hn).inner_finsupp_eq_sum_left c d

/-- Parseval's norm decomposition for a finite Hermite expansion. -/
theorem norm_sq_finiteHermiteCombination (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) :
    ‖finiteHermiteCombination n hn c‖ ^ 2 =
      c.sum fun _ z => Complex.normSq z := by
  have h := inner_finiteHermiteCombination n hn c c
  rw [inner_self_eq_norm_sq_to_K] at h
  have hr := congrArg Complex.re h
  simpa [Finsupp.sum, map_sum, Complex.mul_re, Complex.sq_norm,
    Complex.normSq_apply, pow_two] using hr

/-- Restriction of a finite coefficient vector to one total
antiholomorphic degree. -/
def coefficientsAtAntiDegree {n : ℕ}
    (c : HermiteMultiIndex n →₀ ℂ) (d : ℕ) :
    HermiteMultiIndex n →₀ ℂ :=
  c.filter fun pq => totalAntiDegree pq = d

/-- Distinct antiholomorphic-degree pieces are orthogonal. -/
theorem antiDegreePieces_inner_eq_zero (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) {d e : ℕ} (hde : d ≠ e) :
    inner ℂ
        (finiteHermiteCombination n hn (coefficientsAtAntiDegree c d))
        (finiteHermiteCombination n hn (coefficientsAtAntiDegree c e)) = 0 := by
  rw [inner_finiteHermiteCombination]
  unfold Finsupp.sum
  apply Finset.sum_eq_zero
  intro pq hpq
  simp only [coefficientsAtAntiDegree, Finsupp.filter_apply]
  by_cases hd : totalAntiDegree pq = d
  · have he : totalAntiDegree pq ≠ e := by simpa [hd] using hde
    simp [hd, hde]
  · simp [hd]

/-- The exact `j`-coordinate lowering of an individual Hermite mode. -/
theorem dbarComponent_hermiteMode (n : ℕ) (hn : 0 < n)
    (pq : HermiteMultiIndex n) (j : Fin n) (z : Configuration n) :
    dbarComponent (multivariateNormalized n hn pq.1 pq.2) j z =
      Real.sqrt (n * pq.2 j : ℕ) *
        multivariateNormalized n hn pq.1 (Function.update pq.2 j (pq.2 j - 1)) z :=
  dbarComponent_multivariateNormalized n hn pq.1 pq.2 j z

/-- Diagonal antiholomorphic energy of a finite coefficient vector.  The
factor `n * totalAntiDegree` is the sum of the squared exact lowering
coefficients over all coordinates. -/
def finiteDbarEnergy {n : ℕ} (c : HermiteMultiIndex n →₀ ℂ) : ℝ :=
  c.sum fun pq z => (n * totalAntiDegree pq : ℕ) * ‖z‖ ^ 2

/-- Coordinate form of the finite antiholomorphic energy diagonalization. -/
theorem finiteDbarEnergy_eq_sum_coordinates {n : ℕ}
    (c : HermiteMultiIndex n →₀ ℂ) :
    finiteDbarEnergy c =
      ∑ j : Fin n, c.sum fun pq z => (n * pq.2 j : ℕ) * ‖z‖ ^ 2 := by
  unfold finiteDbarEnergy totalAntiDegree
  unfold Finsupp.sum
  simp_rw [Nat.cast_mul, Nat.cast_sum, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Joint-index lowering in coordinate `j`. -/
def lowerHermiteIndex {n : ℕ} (j : Fin n) (pq : HermiteMultiIndex n) :
    HermiteMultiIndex n := (pq.1, lowerAt pq.2 j)

/-- Raise the `j`th entry of an antiholomorphic multi-index by one. -/
def raiseAt {n : ℕ} (q : Fin n → ℕ) (j : Fin n) : Fin n → ℕ :=
  Function.update q j (q j + 1)

/-- Joint-index raising in coordinate `j`. -/
def raiseHermiteIndex {n : ℕ} (j : Fin n) (pq : HermiteMultiIndex n) :
    HermiteMultiIndex n := (pq.1, raiseAt pq.2 j)

/-- Raising cancels truncated lowering when the lowered coordinate was
strictly positive. -/
theorem raiseAt_lowerAt {n : ℕ} (q : Fin n → ℕ) (j : Fin n)
    (hq : 0 < q j) :
    raiseAt (lowerAt q j) j = q := by
  funext k
  by_cases hkj : k = j
  · subst k
    simp [raiseAt, lowerAt]
    omega
  · simp [raiseAt, lowerAt, Function.update_of_ne hkj]

/-- The joint-index raising map is a left inverse to lowering on indices
whose `j`th antiholomorphic exponent is positive. -/
theorem raiseHermiteIndex_lowerHermiteIndex {n : ℕ} (j : Fin n)
    (pq : HermiteMultiIndex n) (hq : 0 < pq.2 j) :
    raiseHermiteIndex j (lowerHermiteIndex j pq) = pq := by
  apply Prod.ext
  · rfl
  · exact raiseAt_lowerAt pq.2 j hq

/-- Coordinate lowering is injective after restricting to source indices
with positive `j`th antiholomorphic exponent. -/
theorem lowerHermiteIndex_injective_of_positive {n : ℕ} (j : Fin n)
    {a b : HermiteMultiIndex n} (ha : 0 < a.2 j) (hb : 0 < b.2 j)
    (h : lowerHermiteIndex j a = lowerHermiteIndex j b) : a = b := by
  calc
    a = raiseHermiteIndex j (lowerHermiteIndex j a) :=
      (raiseHermiteIndex_lowerHermiteIndex j a ha).symm
    _ = raiseHermiteIndex j (lowerHermiteIndex j b) := congrArg _ h
    _ = b := raiseHermiteIndex_lowerHermiteIndex j b hb

/-- A mode with zero `j`th antiholomorphic exponent contributes the zero
coefficient to coordinate lowering. -/
theorem loweringCoefficient_eq_zero_of_coordinate_eq_zero
    (n : ℕ) {m : ℕ} (q : Fin m → ℕ) (j : Fin m) (a : ℂ)
    (hq : q j = 0) :
    (Real.sqrt (n * q j : ℕ) : ℂ) * a = 0 := by
  simp [hq]

/-- Collision-safe lowered coefficients.  `Finsupp.sum` adds coefficients
when several source indices lower to the same target index. -/
def loweredCoefficients (n : ℕ)
    (c : HermiteMultiIndex n →₀ ℂ) (j : Fin n) :
    HermiteMultiIndex n →₀ ℂ :=
  c.sum fun pq a => Finsupp.single (lowerHermiteIndex j pq)
    ((Real.sqrt (n * pq.2 j : ℕ) : ℂ) * a)

/-- Evaluation of the aggregated lowered coefficients at the image of a
positive source index. -/
theorem loweredCoefficients_apply_lowerHermiteIndex (n : ℕ)
    (c : HermiteMultiIndex n →₀ ℂ) (j : Fin n)
    (pq : HermiteMultiIndex n) (hq : 0 < pq.2 j) :
    loweredCoefficients n c j (lowerHermiteIndex j pq) =
      (Real.sqrt (n * pq.2 j : ℕ) : ℂ) * c pq := by
  classical
  unfold loweredCoefficients
  rw [Finsupp.sum_apply]
  unfold Finsupp.sum
  by_cases hpq : pq ∈ c.support
  · rw [Finset.sum_eq_single pq]
    · simp
    · intro a ha hane
      dsimp
      rw [Finsupp.single_apply]
      split_ifs with heq
      · by_cases ha0 : a.2 j = 0
        · exact loweringCoefficient_eq_zero_of_coordinate_eq_zero n a.2 j (c a) ha0
        · have hapos : 0 < a.2 j := Nat.pos_of_ne_zero ha0
          exact (hane (lowerHermiteIndex_injective_of_positive j hapos hq heq)).elim
      · rfl
    · exact fun h => (h hpq).elim
  · have hpq0 : c pq = 0 := by simpa using hpq
    rw [hpq0, mul_zero]
    apply Finset.sum_eq_zero
    intro a ha
    dsimp
    rw [Finsupp.single_apply]
    split_ifs with heq
    · by_cases ha0 : a.2 j = 0
      · exact loweringCoefficient_eq_zero_of_coordinate_eq_zero n a.2 j (c a) ha0
      · have hapos : 0 < a.2 j := Nat.pos_of_ne_zero ha0
        have hapq := lowerHermiteIndex_injective_of_positive j hapos hq heq
        subst a
        exact (hpq ha).elim
    · rfl

/-- An index outside the image of positive coordinate lowering has zero
aggregated lowered coefficient. -/
theorem loweredCoefficients_apply_eq_zero_of_offImage (n : ℕ)
    (c : HermiteMultiIndex n →₀ ℂ) (j : Fin n) (b : HermiteMultiIndex n)
    (hoff : ∀ pq : HermiteMultiIndex n,
      pq ∈ c.support → 0 < pq.2 j → lowerHermiteIndex j pq ≠ b) :
    loweredCoefficients n c j b = 0 := by
  classical
  unfold loweredCoefficients
  rw [Finsupp.sum_apply]
  unfold Finsupp.sum
  apply Finset.sum_eq_zero
  intro pq hpq
  dsimp
  rw [Finsupp.single_apply]
  split_ifs with heq
  · by_cases hq0 : pq.2 j = 0
    · exact loweringCoefficient_eq_zero_of_coordinate_eq_zero n pq.2 j (c pq) hq0
    · exact (hoff pq hpq (Nat.pos_of_ne_zero hq0) heq).elim
  · rfl

/-- The support of lowered coefficients is exactly the image of positive
source-support indices. -/
theorem mem_support_loweredCoefficients_iff (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) (j : Fin n) (b : HermiteMultiIndex n) :
    b ∈ (loweredCoefficients n c j).support ↔
      ∃ pq ∈ c.support, 0 < pq.2 j ∧ lowerHermiteIndex j pq = b := by
  classical
  constructor
  · intro hb
    by_contra h
    push Not at h
    have hz := loweredCoefficients_apply_eq_zero_of_offImage n c j b
      (fun pq hpq hp => h pq hpq hp)
    exact (Finsupp.mem_support_iff.mp hb) hz
  · rintro ⟨pq, hpq, hpos, rfl⟩
    rw [Finsupp.mem_support_iff,
      loweredCoefficients_apply_lowerHermiteIndex n c j pq hpos]
    apply mul_ne_zero
    · exact_mod_cast (Real.sqrt_pos.2 (by positivity : (0 : ℝ) < n * pq.2 j)).ne'
    · exact Finsupp.mem_support_iff.mp hpq

/-- Squared coefficient mass after coordinate lowering is the original
coefficient mass weighted by the exact squared lowering coefficient. -/
theorem loweredCoefficients_normSq_sum (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) (j : Fin n) :
    (loweredCoefficients n c j).sum (fun _ a => Complex.normSq a) =
      c.sum fun pq a => (n * pq.2 j : ℕ) * Complex.normSq a := by
  classical
  unfold Finsupp.sum
  have hreindex :
      (∑ pq ∈ c.support.filter (fun pq => 0 < pq.2 j),
        Complex.normSq
          ((Real.sqrt (n * pq.2 j : ℕ) : ℂ) * c pq)) =
      ∑ b ∈ (loweredCoefficients n c j).support,
        Complex.normSq (loweredCoefficients n c j b) := by
    apply Finset.sum_bij
      (fun pq _ => lowerHermiteIndex j pq)
    · intro pq hpq
      rw [mem_support_loweredCoefficients_iff n hn]
      exact ⟨pq, (Finset.mem_filter.mp hpq).1,
        (Finset.mem_filter.mp hpq).2, rfl⟩
    · intro a ha b hb hab
      exact lowerHermiteIndex_injective_of_positive j
        (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2 hab
    · intro b hb
      rw [mem_support_loweredCoefficients_iff n hn] at hb
      obtain ⟨pq, hpq, hpos, rfl⟩ := hb
      exact ⟨pq, Finset.mem_filter.mpr ⟨hpq, hpos⟩, rfl⟩
    · intro pq hpq
      rw [loweredCoefficients_apply_lowerHermiteIndex n c j pq
        (Finset.mem_filter.mp hpq).2]
  rw [← hreindex]
  change (∑ pq ∈ c.support.filter (fun pq => 0 < pq.2 j),
      Complex.normSq ((Real.sqrt (n * pq.2 j : ℕ) : ℂ) * c pq)) =
    ∑ pq ∈ c.support, ((n * pq.2 j : ℕ) : ℝ) * Complex.normSq (c pq)
  rw [show (∑ pq ∈ c.support,
      ((n * pq.2 j : ℕ) : ℝ) * Complex.normSq (c pq)) =
      ∑ pq ∈ c.support.filter (fun pq => 0 < pq.2 j),
        ((n * pq.2 j : ℕ) : ℝ) * Complex.normSq (c pq) by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro pq hpq
    split_ifs with hpos
    · rfl
    · have hz : pq.2 j = 0 := by omega
      simp [hz]]
  apply Finset.sum_congr rfl
  intro pq hpq
  rw [Complex.normSq_mul]
  have hsqrt : Real.sqrt (n * pq.2 j : ℕ) ^ 2 = (n * pq.2 j : ℕ) := by
    rw [sq, Real.mul_self_sqrt]
    positivity
  rw [Complex.normSq_ofReal, ← sq, hsqrt]

/-- Parseval turns the lowered coefficient identity into the exact
coordinatewise Gaussian `L²` norm formula. -/
theorem norm_sq_finiteHermiteCombination_lowered (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) (j : Fin n) :
    ‖finiteHermiteCombination n hn (loweredCoefficients n c j)‖ ^ 2 =
      c.sum fun pq a => (n * pq.2 j : ℕ) * Complex.normSq a := by
  rw [norm_sq_finiteHermiteCombination, loweredCoefficients_normSq_sum n hn]

/-- Total Gaussian `L²` energy of the finitely synthesized coordinate
`dbar` expansions is the diagonal antiholomorphic Hermite energy. -/
theorem sum_norm_sq_lowered_eq_finiteDbarEnergy (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) :
    (∑ j : Fin n,
      ‖finiteHermiteCombination n hn (loweredCoefficients n c j)‖ ^ 2) =
      finiteDbarEnergy c := by
  simp_rw [norm_sq_finiteHermiteCombination_lowered]
  rw [finiteDbarEnergy_eq_sum_coordinates]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finsupp.sum_congr
  intro pq hpq
  rw [Complex.sq_norm]

/-- The underlying pointwise finite Hermite polynomial. -/
def finiteHermiteFunction (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) : Configuration n → ℂ :=
  Finsupp.linearCombination ℂ
    (fun pq => multivariateNormalized n hn pq.1 pq.2) c

/-- The pointwise finite Hermite function represents its synthesized
Gaussian `L²` vector. -/
theorem finiteHermiteCombination_coeFn (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) :
    finiteHermiteCombination n hn c =ᵐ[complexGaussianMeasure n]
      finiteHermiteFunction n hn c := by
  classical
  unfold finiteHermiteCombination finiteHermiteFunction
  simp only [Finsupp.linearCombination_apply]
  have h :
      (∑ pq ∈ c.support,
        fun z => c pq • (hermiteL2Family n hn pq : Configuration n → ℂ) z) =ᵐ[
          complexGaussianMeasure n]
      ∑ pq ∈ c.support,
        fun z => c pq • multivariateNormalized n hn pq.1 pq.2 z := by
    apply eventuallyEq_sum
    intro pq hpq
    exact (hermiteL2Family_coeFn n hn pq).const_smul (c pq)
  have hcoe :
      ((∑ pq ∈ c.support, c pq • hermiteL2Family n hn pq :
          Lp ℂ 2 (complexGaussianMeasure n)) : Configuration n → ℂ) =ᵐ[
        complexGaussianMeasure n]
      ∑ pq ∈ c.support,
        fun z => c pq • (hermiteL2Family n hn pq : Configuration n → ℂ) z := by
    filter_upwards [Lp.coeFn_linearCombination c (hermiteL2Family n hn)] with z hz
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply,
      Pi.smul_apply] using hz
  filter_upwards [hcoe, h] with z hcz hz
  unfold Finsupp.sum
  rw [hcz]
  exact hz

private theorem differentiable_multivariateNormalized_real (n : ℕ) (hn : 0 < n)
    (p q : Fin n → ℕ) :
    Differentiable ℝ (multivariateNormalized n hn p q) := by
  unfold multivariateNormalized
  let f : Fin n → Configuration n → ℂ :=
    fun i z => normalizedEval n hn (p i) (q i) (z i)
  have hf : ∀ i, Differentiable ℝ (f i) := fun i =>
    (differentiable_normalizedEval n hn (p i) (q i)).comp
      (ContinuousLinearMap.proj i : Configuration n →L[ℝ] ℂ).differentiable
  change Differentiable ℝ (fun z => ∏ i ∈ Finset.univ, f i z)
  intro z
  exact (HasFDerivAt.finsetProd (u := Finset.univ) (g := f)
    (fun i _ => (hf i z).hasFDerivAt)).differentiableAt

private theorem dbarComponent_const_mul {n : ℕ} (a : ℂ)
    (f : Configuration n → ℂ) (hf : Differentiable ℝ f)
    (j : Fin n) (z : Configuration n) :
    dbarComponent (fun w => a * f w) j z = a * dbarComponent f j z := by
  unfold dbarComponent
  rw [fderiv_const_mul (hf z)]
  simp only [smul_apply, smul_eq_mul]
  ring

private theorem dbarComponent_finset_sum {n : ℕ} {ι : Type*}
    (s : Finset ι) (f : ι → Configuration n → ℂ)
    (hf : ∀ i ∈ s, Differentiable ℝ (f i)) (j : Fin n) (z : Configuration n) :
    dbarComponent (fun w => ∑ i ∈ s, f i w) j z =
      ∑ i ∈ s, dbarComponent (f i) j z := by
  unfold dbarComponent
  rw [fderiv_fun_sum (fun i hi => hf i hi z)]
  simp only [sum_apply]
  calc
    _ = (∑ i ∈ s, (1 / 2 : ℂ) *
          (fderiv ℝ (f i) z) (realCoordinateDirection j)) +
        ∑ i ∈ s, (1 / 2 : ℂ) * Complex.I *
          (fderiv ℝ (f i) z) (imaginaryCoordinateDirection j) := by
      rw [mul_add, Finset.mul_sum]
      congr 1
      simp_rw [Finset.mul_sum]
      ring_nf
    _ = _ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring

/-- Pointwise `dbar` of a finite Hermite expansion is the expansion synthesized
from the collision-safe lowered coefficients. -/
theorem dbarComponent_finiteHermiteFunction (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) (j : Fin n) (z : Configuration n) :
    dbarComponent (finiteHermiteFunction n hn c) j z =
      finiteHermiteFunction n hn (loweredCoefficients n c j) z := by
  classical
  rw [show finiteHermiteFunction n hn c = fun z =>
      c.sum fun pq a => a * multivariateNormalized n hn pq.1 pq.2 z by
    funext w
    simp [finiteHermiteFunction, Finsupp.linearCombination_apply,
      Finsupp.sum, Finset.sum_apply, smul_eq_mul]]
  unfold Finsupp.sum
  rw [dbarComponent_finset_sum]
  · have hsum :
        (∑ pq ∈ c.support,
          dbarComponent
            (fun w => c pq * multivariateNormalized n hn pq.1 pq.2 w) j z) =
        ∑ pq ∈ c.support, c pq *
          (Real.sqrt (n * pq.2 j : ℕ) *
            multivariateNormalized n hn pq.1 (lowerAt pq.2 j) z) := by
      apply Finset.sum_congr rfl
      intro pq hpq
      rw [dbarComponent_const_mul _ _
        ((differentiable_multivariateNormalized_real n hn pq.1 pq.2))]
      rw [dbarComponent_multivariateNormalized]
    rw [hsum]
    simp only [Nat.cast_mul, Nat.cast_nonneg, Real.sqrt_mul, Complex.ofReal_mul,
      finiteHermiteFunction, loweredCoefficients, lowerHermiteIndex, map_finsuppSum,
      Finsupp.linearCombination_apply, zero_smul, Finsupp.sum_single_index]
    unfold Finsupp.sum
    rw [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro pq hpq
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · intro pq hpq
    exact (differentiable_multivariateNormalized_real n hn pq.1 pq.2).const_mul _

/-- The Gaussian integral of a coordinate `dbar` square is the squared norm
of the collision-safe lowered `L²` synthesis. -/
theorem integral_conj_dbarComponent_finiteHermiteFunction_mul (n : ℕ)
    (hn : 0 < n) (c : HermiteMultiIndex n →₀ ℂ) (j : Fin n) :
    ∫ z, conj (dbarComponent (finiteHermiteFunction n hn c) j z) *
        dbarComponent (finiteHermiteFunction n hn c) j z
      ∂complexGaussianMeasure n =
      (‖finiteHermiteCombination n hn (loweredCoefficients n c j)‖ ^ 2 : ℂ) := by
  let u := finiteHermiteCombination n hn (loweredCoefficients n c j)
  calc
    _ = inner ℂ u u := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards [finiteHermiteCombination_coeFn n hn
        (loweredCoefficients n c j)] with z hz
      rw [hz, ← dbarComponent_finiteHermiteFunction n hn c j z]
      rw [RCLike.inner_apply]
      ring
    _ = _ := inner_self_eq_norm_sq_to_K u

/-- Exact finite Gaussian `dbar` integral energy identity. -/
theorem finiteGaussianDbarIntegralEnergy (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) :
    (∑ j : Fin n,
      ∫ z, conj (dbarComponent (finiteHermiteFunction n hn c) j z) *
          dbarComponent (finiteHermiteFunction n hn c) j z
        ∂complexGaussianMeasure n) =
      (finiteDbarEnergy c : ℂ) := by
  simp_rw [integral_conj_dbarComponent_finiteHermiteFunction_mul]
  exact_mod_cast sum_norm_sq_lowered_eq_finiteDbarEnergy n hn c

end
end ComplexHermite
end GinibrePoincare
