/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/HermiteSecondDbarWeakClosure.lean.
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

public import LeanPool.GinibrePoincare.Analysis.HermiteSecondDbarEnergy
public import LeanPool.GinibrePoincare.Analysis.GaussianDbarDistributionalClosure

/-! # Infinite second-lowering synthesis

The second derivatives of the inverse square root can be synthesized
from the genuine first derivatives of a compact smooth Gaussian function.
Distributional identification is separate from the synthesis.
-/

@[expose] public section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology
namespace GinibrePoincare
noncomputable section
open ComplexHermite

theorem raiseHermiteIndex_injective {n : ℕ} (k : Fin n) :
    Function.Injective (raiseHermiteIndex k) := by
  intro a b he
  apply (raiseHermiteIndexEquivPositive k).injective
  exact Subtype.ext he

/-- The term indexed by `r` in the Hermite expansion of the `j`-th `dbar` derivative of `g`:
`√(n r.2 j)` times the `r`-th Hermite coefficient of `g`, times the normalized Hermite vector
at the lowered index `lowerHermiteIndex j r`. -/
def gaussianHermiteFirstLoweringTerm {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) (j : Fin n)
    (r : HermiteMultiIndex n) : Lp ℂ 2 (complexGaussianMeasure n) :=
  ((Real.sqrt (n * r.2 j : ℕ) : ℂ) * gaussianHermiteCoefficient hn g r) •
    multivariateNormalizedL2 n hn (lowerHermiteIndex j r).1 (lowerHermiteIndex j r).2

/-- The genuine first derivative's Hermite expansion can be indexed by
the original source modes, with zero terms when lowering is impossible. -/
theorem hasSum_gaussianHermiteFirstLoweringTerm {n : ℕ} (hn : 0 < n)
    (g D : Lp ℂ 2 (complexGaussianMeasure n)) (j : Fin n)
    (hcoeff : ∀ pq, gaussianHermiteCoefficient hn D pq =
      (Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) *
        gaussianHermiteCoefficient hn g (raiseHermiteIndex j pq)) :
    HasSum (gaussianHermiteFirstLoweringTerm hn g j) D := by
  let e := raiseHermiteIndexEquivPositive j
  let f : {r : HermiteMultiIndex n // 0 < r.2 j} →
      Lp ℂ 2 (complexGaussianMeasure n) :=
    fun r => gaussianHermiteFirstLoweringTerm hn g j r.1
  have hsSub : HasSum f D := by
    apply (e.hasSum_iff).1
    have hs := (gaussianHermiteHilbertBasis n hn).hasSum_repr D
    apply hs.congr_fun
    intro pq
    have hlow : lowerHermiteIndex j (raiseHermiteIndex j pq) = pq := e.left_inv pq
    symm
    change gaussianHermiteCoefficient hn D pq •
      (gaussianHermiteHilbertBasis n hn) pq =
      gaussianHermiteFirstLoweringTerm hn g j (raiseHermiteIndex j pq)
    rw [hcoeff, gaussianHermiteHilbertBasis_apply]
    simp only [gaussianHermiteFirstLoweringTerm, hlow]
    simp [raiseHermiteIndex, raiseAt]
  let T := gaussianHermiteFirstLoweringTerm hn g j
  have hT : ({r : HermiteMultiIndex n | 0 < r.2 j} : Set _).indicator T = T := by
    funext r
    simp only [Set.indicator, Set.mem_ofPred_eq]
    split_ifs with hr
    · rfl
    · have hz : r.2 j = 0 := Nat.eq_zero_of_not_pos hr
      simp [T, gaussianHermiteFirstLoweringTerm, hz]
  have hsT : Summable T := by
    have hi : Summable (({r : HermiteMultiIndex n | 0 < r.2 j} : Set _).indicator T) :=
      summable_subtype_iff_indicator.mp hsSub.summable
    rwa [hT] at hi
  have he : (∑' r, T r) = D := by
    rw [← hT, ← tsum_subtype {r | 0 < r.2 j} T]
    exact hsSub.tsum_eq
  exact he ▸ hsT.hasSum

/-- The finitely supported truncation of the Hermite coefficients of `g` to the index set `s`. -/
def gaussianHermiteFiniteCoefficients {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) (s : Finset (HermiteMultiIndex n)) :
    HermiteMultiIndex n →₀ ℂ :=
  Finsupp.onFinset s ((s : Set _).indicator (gaussianHermiteCoefficient hn g))
    (by intro pq hp; by_contra h; exact hp (by simp [h]))

theorem finiteDbarComponentL2_eq_sum (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) (j : Fin n) :
    finiteDbarComponentL2 n hn c j = c.sum (fun r a =>
      ((Real.sqrt (n * r.2 j : ℕ) : ℂ) * a) •
        multivariateNormalizedL2 n hn (lowerHermiteIndex j r).1 (lowerHermiteIndex j r).2) := by
  simp [finiteDbarComponentL2, finiteHermiteCombination, loweredCoefficients,
    map_finsuppSum, Finsupp.linearCombination_apply, Finsupp.sum_single_index,
    hermiteL2Family, multivariateNormalizedL2]

theorem gaussianHermiteFiniteCoefficients_value (n : ℕ) (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) (s : Finset (HermiteMultiIndex n)) :
    finiteHermiteCombination n hn (gaussianHermiteFiniteCoefficients hn g s) =
      ∑ r ∈ s, gaussianHermiteCoefficient hn g r •
        (gaussianHermiteHilbertBasis n hn) r := by
  classical
  have hs : (gaussianHermiteFiniteCoefficients hn g s).support ⊆ s := by
    intro r hr
    by_contra h
    exact (Finsupp.mem_support_iff.mp hr) (by
      simp [gaussianHermiteFiniteCoefficients, h])
  simp only [finiteHermiteCombination, Finsupp.linearCombination_apply]
  rw [Finsupp.sum_of_support_subset _ hs _ (by simp)]
  apply Finset.sum_congr rfl
  intro r hr
  simp [gaussianHermiteFiniteCoefficients, hr, gaussianHermiteHilbertBasis_apply,
    hermiteL2Family, multivariateNormalizedL2]

theorem gaussianHermiteFiniteCoefficients_dbar (n : ℕ) (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n)) (s : Finset (HermiteMultiIndex n)) (j : Fin n) :
    finiteDbarComponentL2 n hn (gaussianHermiteFiniteCoefficients hn g s) j =
      ∑ r ∈ s, gaussianHermiteFirstLoweringTerm hn g j r := by
  classical
  have hs : (gaussianHermiteFiniteCoefficients hn g s).support ⊆ s := by
    intro r hr
    by_contra h
    exact (Finsupp.mem_support_iff.mp hr) (by
      simp [gaussianHermiteFiniteCoefficients, h])
  rw [finiteDbarComponentL2_eq_sum, Finsupp.sum_of_support_subset _ hs _ (by simp)]
  apply Finset.sum_congr rfl
  intro r hr
  simp [gaussianHermiteFiniteCoefficients, hr, gaussianHermiteFirstLoweringTerm]

/-- A genuine Gaussian first-derivative coefficient identity yields
simultaneous strong approximation by finite Hermite polynomials. -/
theorem gaussianHermiteFiniteCoefficients_tendsto {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n))
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hcoeff : ∀ j pq, gaussianHermiteCoefficient hn (D j) pq =
      (Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) *
        gaussianHermiteCoefficient hn g (raiseHermiteIndex j pq)) :
    Tendsto (fun s => finiteHermiteCombination n hn (gaussianHermiteFiniteCoefficients hn g s))
      atTop (𝓝 g) ∧
    ∀ j, Tendsto (fun s => finiteDbarComponentL2 n hn (gaussianHermiteFiniteCoefficients hn g s) j)
      atTop (𝓝 (D j)) := by
  constructor
  · simp only [gaussianHermiteFiniteCoefficients_value]
    change HasSum (fun r => gaussianHermiteCoefficient hn g r •
      (gaussianHermiteHilbertBasis n hn) r) g
    simpa only [gaussianHermiteCoefficient] using
      (gaussianHermiteHilbertBasis n hn).hasSum_repr g
  · intro j
    simp only [gaussianHermiteFiniteCoefficients_dbar]
    change HasSum (gaussianHermiteFirstLoweringTerm hn g j) (D j)
    exact hasSum_gaussianHermiteFirstLoweringTerm hn g (D j) j (hcoeff j)

/-- The `ℓ²` vector of Hermite coefficients of `D`, the coefficient at `pq` multiplied by the
inverse square root weight of the total antiholomorphic degree of `raiseHermiteIndex j pq`. -/
def gaussianInverseSquareRootFirstCoefficients {n : ℕ} (hn : 0 < n)
    (D : Lp ℂ 2 (complexGaussianMeasure n)) (j : Fin n) :
    lp (fun _ : HermiteMultiIndex n => ℂ) 2 :=
  ⟨fun pq => (hermiteInverseSquareRootWeight n (totalAntiDegree (raiseHermiteIndex j pq)) : ℂ) *
    gaussianHermiteCoefficient hn D pq,
    (lp.memℓp ((gaussianHermiteHilbertBasis n hn).repr D)).mono' (by
      intro pq
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hermiteInverseSquareRootWeight_nonneg _ _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (hermiteInverseSquareRootWeight_le_one _ _))⟩

/-- The Gaussian `L²` vector whose Hermite coefficients are
`gaussianInverseSquareRootFirstCoefficients hn D j`. -/
def gaussianInverseSquareRootFirstSynthesis {n : ℕ} (hn : 0 < n)
    (D : Lp ℂ 2 (complexGaussianMeasure n)) (j : Fin n) :
    Lp ℂ 2 (complexGaussianMeasure n) :=
  (gaussianHermiteHilbertBasis n hn).repr.symm (gaussianInverseSquareRootFirstCoefficients hn D j)

@[simp] theorem gaussianHermiteCoefficient_firstSynthesis {n : ℕ} (hn : 0 < n)
    (D : Lp ℂ 2 (complexGaussianMeasure n)) (j : Fin n) (pq : HermiteMultiIndex n) :
    gaussianHermiteCoefficient hn (gaussianInverseSquareRootFirstSynthesis hn D j) pq =
      (hermiteInverseSquareRootWeight n (totalAntiDegree (raiseHermiteIndex j pq)) : ℂ) *
        gaussianHermiteCoefficient hn D pq := by
  simp [gaussianHermiteCoefficient, gaussianInverseSquareRootFirstSynthesis,
    gaussianInverseSquareRootFirstCoefficients]

theorem gaussianInverseSquareRootFirstSynthesis_norm_le {n : ℕ} (hn : 0 < n)
    (D : Lp ℂ 2 (complexGaussianMeasure n)) (j : Fin n) :
    ‖gaussianInverseSquareRootFirstSynthesis hn D j‖ ≤ ‖D‖ := by
  rw [gaussianInverseSquareRootFirstSynthesis, LinearIsometryEquiv.norm_map,
    ← (gaussianHermiteHilbertBasis n hn).repr.norm_map D]
  apply lp.norm_mono (by norm_num)
  intro pq
  change ‖(hermiteInverseSquareRootWeight n (totalAntiDegree (raiseHermiteIndex j pq)) : ℂ) *
    gaussianHermiteCoefficient hn D pq‖ ≤ ‖gaussianHermiteCoefficient hn D pq‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (hermiteInverseSquareRootWeight_nonneg _ _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (hermiteInverseSquareRootWeight_le_one _ _)

/-- The map `D ↦ gaussianInverseSquareRootFirstSynthesis hn D j`, bundled as a continuous
complex-linear operator on Gaussian `L²`. -/
def gaussianInverseSquareRootFirstSynthesisCLM {n : ℕ} (hn : 0 < n) (j : Fin n) :
    Lp ℂ 2 (complexGaussianMeasure n) →L[ℂ] Lp ℂ 2 (complexGaussianMeasure n) :=
  LinearMap.mkContinuous
    { toFun := fun D => gaussianInverseSquareRootFirstSynthesis hn D j
      map_add' := by
        intro D E
        apply gaussianHermiteCoefficient_ext hn
        intro pq
        have ha (u v : Lp ℂ 2 (complexGaussianMeasure n)) :
            gaussianHermiteCoefficient hn (u + v) pq =
              gaussianHermiteCoefficient hn u pq + gaussianHermiteCoefficient hn v pq := by
          simp only [gaussianHermiteCoefficient_eq_inner, inner_add_right]
        rw [gaussianHermiteCoefficient_firstSynthesis, ha, ha,
          gaussianHermiteCoefficient_firstSynthesis, gaussianHermiteCoefficient_firstSynthesis,
              mul_add]
      map_smul' := by
        intro a D
        apply gaussianHermiteCoefficient_ext hn
        intro pq
        have ha (u : Lp ℂ 2 (complexGaussianMeasure n)) :
            gaussianHermiteCoefficient hn (a • u) pq = a * gaussianHermiteCoefficient hn u pq := by
          simp only [gaussianHermiteCoefficient_eq_inner, inner_smul_right]
        change gaussianHermiteCoefficient hn (gaussianInverseSquareRootFirstSynthesis hn (a • D) j)
            pq =
          gaussianHermiteCoefficient hn (a • gaussianInverseSquareRootFirstSynthesis hn D j) pq
        rw [gaussianHermiteCoefficient_firstSynthesis, ha, ha,
            gaussianHermiteCoefficient_firstSynthesis]
        ring }
    1 (by intro D; simpa using gaussianInverseSquareRootFirstSynthesis_norm_le hn D j)

theorem gaussianInverseSquareRootFirstSynthesis_finite (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) (j : Fin n) :
    gaussianInverseSquareRootFirstSynthesis hn (finiteDbarComponentL2 n hn c j) j =
      finiteDbarComponentL2 n hn (finiteHermiteInverseSquareRootCoefficients c) j := by
  apply gaussianHermiteCoefficient_ext hn
  intro pq
  rw [gaussianHermiteCoefficient_firstSynthesis,
    gaussianHermiteCoefficient_finiteDbarComponentL2,
    gaussianHermiteCoefficient_finiteDbarComponentL2,
    finiteHermiteInverseSquareRootCoefficients_apply]
  ring

/-- The ratio `√(n (pq.2 k + 1))` times the inverse square root weight of the total
antiholomorphic degree of the index `pq` raised in coordinates `k` and then `j`. -/
def secondHermiteInverseRatio {n : ℕ} (j k : Fin n) (pq : HermiteMultiIndex n) : ℝ :=
  Real.sqrt (n * (pq.2 k + 1) : ℕ) *
    hermiteInverseSquareRootWeight n
      (totalAntiDegree (raiseHermiteIndex j (raiseHermiteIndex k pq)))

theorem secondHermiteInverseRatio_nonneg {n : ℕ} (j k : Fin n)
    (pq : HermiteMultiIndex n) : 0 ≤ secondHermiteInverseRatio j k pq := by
  exact mul_nonneg (Real.sqrt_nonneg _) (hermiteInverseSquareRootWeight_nonneg _ _)

theorem secondHermiteInverseRatio_le_one {n : ℕ} (hn : 0 < n) (j k : Fin n)
    (pq : HermiteMultiIndex n) : secondHermiteInverseRatio j k pq ≤ 1 := by
  let r := raiseHermiteIndex j (raiseHermiteIndex k pq)
  have hk : pq.2 k + 1 ≤ r.2 k := by
    by_cases hjk : k = j
    · subst j; simp [r, raiseHermiteIndex, raiseAt]
    · simp [r, raiseHermiteIndex, raiseAt, Function.update_of_ne hjk]
  have hd : r.2 k ≤ totalAntiDegree r := by
    exact Finset.single_le_sum (fun i _ => Nat.zero_le (r.2 i)) (Finset.mem_univ k)
  have hb : n * (pq.2 k + 1) ≤ n * totalAntiDegree r :=
    Nat.mul_le_mul_left n (hk.trans hd)
  have hp : (0 : ℝ) < (n * totalAntiDegree r : ℕ) := by
    have hnat : 0 < n * totalAntiDegree r :=
      lt_of_lt_of_le (Nat.mul_pos hn (Nat.succ_pos _)) hb
    exact_mod_cast hnat
  unfold secondHermiteInverseRatio hermiteInverseSquareRootWeight
  change Real.sqrt (n * (pq.2 k + 1) : ℕ) * (Real.sqrt (n * totalAntiDegree r : ℕ))⁻¹ ≤ 1
  rw [← div_eq_mul_inv]
  apply (div_le_one (Real.sqrt_pos.mpr hp)).mpr
  exact Real.sqrt_le_sqrt (by exact_mod_cast hb)

/-- These are actual `ℓ²` coefficients, controlled by a genuine first
derivative vector rather than an assumed second derivative. -/
def gaussianInverseSquareRootSecondCoefficients {n : ℕ} (hn : 0 < n)
    (D : Lp ℂ 2 (complexGaussianMeasure n)) (j k : Fin n) :
    lp (fun _ : HermiteMultiIndex n => ℂ) 2 :=
  ⟨fun pq => (secondHermiteInverseRatio j k pq : ℂ) *
    gaussianHermiteCoefficient hn D (raiseHermiteIndex k pq), by
    have hs := (lp.memℓp ((gaussianHermiteHilbertBasis n hn).repr D)).summable
      (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    have hshift : Memℓp
        (fun pq => gaussianHermiteCoefficient hn D (raiseHermiteIndex k pq)) 2 := by
      apply memℓp_gen
      exact hs.comp_injective (raiseHermiteIndex_injective k)
    apply hshift.mono'
    intro pq
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (secondHermiteInverseRatio_nonneg _ _ _)]
    exact mul_le_of_le_one_left (norm_nonneg _) (secondHermiteInverseRatio_le_one hn _ _ _)⟩

/-- Full infinite `L²` synthesis of a second lowered inverse-square-root
vector from a first derivative. -/
def gaussianInverseSquareRootSecondSynthesis {n : ℕ} (hn : 0 < n)
    (D : Lp ℂ 2 (complexGaussianMeasure n)) (j k : Fin n) :
    Lp ℂ 2 (complexGaussianMeasure n) :=
  (gaussianHermiteHilbertBasis n hn).repr.symm
    (gaussianInverseSquareRootSecondCoefficients hn D j k)

theorem gaussianHermiteCoefficient_secondSynthesis {n : ℕ} (hn : 0 < n)
    (D : Lp ℂ 2 (complexGaussianMeasure n)) (j k : Fin n) (pq : HermiteMultiIndex n) :
    gaussianHermiteCoefficient hn (gaussianInverseSquareRootSecondSynthesis hn D j k) pq =
      (secondHermiteInverseRatio j k pq : ℂ) *
        gaussianHermiteCoefficient hn D (raiseHermiteIndex k pq) := by
  simp [gaussianHermiteCoefficient, gaussianInverseSquareRootSecondSynthesis,
    gaussianInverseSquareRootSecondCoefficients]

theorem gaussianInverseSquareRootSecondSynthesis_norm_le {n : ℕ} (hn : 0 < n)
    (D : Lp ℂ 2 (complexGaussianMeasure n)) (j k : Fin n) :
    ‖gaussianInverseSquareRootSecondSynthesis hn D j k‖ ≤ ‖D‖ := by
  have hsD := hasSum_norm_sq_gaussianHermiteCoefficient hn D
  have hsS := hasSum_norm_sq_gaussianHermiteCoefficient hn
    (gaussianInverseSquareRootSecondSynthesis hn D j k)
  have hbound (pq : HermiteMultiIndex n) :
      ‖gaussianHermiteCoefficient hn (gaussianInverseSquareRootSecondSynthesis hn D j k) pq‖ ^ 2 ≤
        ‖gaussianHermiteCoefficient hn D (raiseHermiteIndex k pq)‖ ^ 2 := by
    rw [gaussianHermiteCoefficient_secondSynthesis, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (secondHermiteInverseRatio_nonneg _ _ _)]
    exact pow_le_pow_left₀ (mul_nonneg (secondHermiteInverseRatio_nonneg _ _ _) (norm_nonneg _))
      (mul_le_of_le_one_left (norm_nonneg _) (secondHermiteInverseRatio_le_one hn _ _ _)) 2
  have hsum := hsS.summable.tsum_le_tsum hbound
    (hsD.summable.comp_injective (raiseHermiteIndex_injective k))
  have hcomp := tsum_comp_le_tsum_of_inj hsD.summable (fun pq => sq_nonneg _)
    (raiseHermiteIndex_injective k)
  rw [hsS.tsum_eq] at hsum
  rw [hsD.tsum_eq] at hcomp
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hsum.trans hcomp)

/-- The second synthesis is bounded and linear in the genuine first
derivative, allowing strong graph approximations to pass to the limit. -/
def gaussianInverseSquareRootSecondSynthesisCLM {n : ℕ} (hn : 0 < n) (j k : Fin n) :
    Lp ℂ 2 (complexGaussianMeasure n) →L[ℂ] Lp ℂ 2 (complexGaussianMeasure n) :=
  LinearMap.mkContinuous
    { toFun := fun D => gaussianInverseSquareRootSecondSynthesis hn D j k
      map_add' := by
        intro D E
        apply gaussianHermiteCoefficient_ext hn
        intro pq
        have ha (u v : Lp ℂ 2 (complexGaussianMeasure n)) (r : HermiteMultiIndex n) :
            gaussianHermiteCoefficient hn (u + v) r =
              gaussianHermiteCoefficient hn u r + gaussianHermiteCoefficient hn v r := by
          simp only [gaussianHermiteCoefficient_eq_inner, inner_add_right]
        rw [gaussianHermiteCoefficient_secondSynthesis, ha, ha,
          gaussianHermiteCoefficient_secondSynthesis, gaussianHermiteCoefficient_secondSynthesis,
          mul_add]
      map_smul' := by
        intro a D
        apply gaussianHermiteCoefficient_ext hn
        intro pq
        have ha (u : Lp ℂ 2 (complexGaussianMeasure n)) (r : HermiteMultiIndex n) :
            gaussianHermiteCoefficient hn (a • u) r = a * gaussianHermiteCoefficient hn u r := by
          simp only [gaussianHermiteCoefficient_eq_inner, inner_smul_right]
        change gaussianHermiteCoefficient hn (gaussianInverseSquareRootSecondSynthesis hn (a • D) j
            k) pq =
          gaussianHermiteCoefficient hn (a • gaussianInverseSquareRootSecondSynthesis hn D j k) pq
        rw [gaussianHermiteCoefficient_secondSynthesis, ha, ha,
          gaussianHermiteCoefficient_secondSynthesis]
        ring }
    1 (by intro D; simpa using gaussianInverseSquareRootSecondSynthesis_norm_le hn D j k)

/-- Infinite synthesis agrees exactly with genuine second differentiation
of the finite inverse-square-root polynomial. -/
theorem gaussianInverseSquareRootSecondSynthesis_finite (n : ℕ) (hn : 0 < n)
    (c : HermiteMultiIndex n →₀ ℂ) (j k : Fin n) :
    gaussianInverseSquareRootSecondSynthesis hn (finiteDbarComponentL2 n hn c j) j k =
      finiteHermiteCombination n hn (loweredCoefficients n
        (loweredCoefficients n (finiteHermiteInverseSquareRootCoefficients c) j) k) := by
  apply gaussianHermiteCoefficient_ext hn
  intro pq
  rw [gaussianHermiteCoefficient_secondSynthesis,
    gaussianHermiteCoefficient_finiteDbarComponentL2]
  change _ = gaussianHermiteCoefficient hn (finiteDbarComponentL2 n hn
    (loweredCoefficients n (finiteHermiteInverseSquareRootCoefficients c) j) k) pq
  rw [gaussianHermiteCoefficient_finiteDbarComponentL2]
  have hlow := gaussianHermiteCoefficient_finiteDbarComponentL2 n hn
    (finiteHermiteInverseSquareRootCoefficients c) j (raiseHermiteIndex k pq)
  rw [finiteDbarComponentL2, gaussianHermiteCoefficient_finiteHermiteCombination] at hlow
  rw [hlow, finiteHermiteInverseSquareRootCoefficients_apply]
  simp only [secondHermiteInverseRatio, Complex.ofReal_mul]
  ring

/-- The full inverse square root has genuine weak first and second
Wirtinger derivatives. The input first derivatives need only their
Hermite identities; the outputs belong to the independently defined
compact-test weak graphs. -/
theorem gaussianInverseSquareRoot_weak_derivatives {n : ℕ} (hn : 0 < n)
    (g : Lp ℂ 2 (complexGaussianMeasure n))
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hcoeff : ∀ j pq, gaussianHermiteCoefficient hn (D j) pq =
      (Real.sqrt (n * (pq.2 j + 1) : ℕ) : ℂ) *
        gaussianHermiteCoefficient hn g (raiseHermiteIndex j pq)) :
    (∀ j, IsGaussianWeakDbar n (gaussianHermiteInverseSquareRoot hn g)
      (gaussianInverseSquareRootFirstSynthesis hn (D j) j) j) ∧
    (∀ j k, IsGaussianWeakDbar n (gaussianInverseSquareRootFirstSynthesis hn (D j) j)
      (gaussianInverseSquareRootSecondSynthesis hn (D j) j k) k) := by
  obtain ⟨hg, hD⟩ := gaussianHermiteFiniteCoefficients_tendsto hn g D hcoeff
  let c := gaussianHermiteFiniteCoefficients hn g
  have hv : Tendsto (fun s => gaussianHermiteInverseSquareRoot hn (finiteHermiteCombination n hn (c
      s)))
      atTop (𝓝 (gaussianHermiteInverseSquareRoot hn g)) :=
    (gaussianHermiteInverseSquareRootCLM hn).continuous.continuousAt.tendsto.comp hg
  have hfirst (j : Fin n) : Tendsto
      (fun s => gaussianInverseSquareRootFirstSynthesis hn (finiteDbarComponentL2 n hn (c s) j) j)
      atTop (𝓝 (gaussianInverseSquareRootFirstSynthesis hn (D j) j)) :=
    (gaussianInverseSquareRootFirstSynthesisCLM hn j).continuous.continuousAt.tendsto.comp (hD j)
  constructor
  · intro j
    refine gaussianWeakDbar_of_tendsto j (fun s =>
      (gaussianHermiteInverseSquareRoot hn (finiteHermiteCombination n hn (c s)),
        gaussianInverseSquareRootFirstSynthesis hn (finiteDbarComponentL2 n hn (c s) j) j))
      _ _ ?_ (hv.prodMk_nhds (hfirst j))
    intro s
    rw [gaussianHermiteInverseSquareRoot_finiteHermiteCombination,
      gaussianInverseSquareRootFirstSynthesis_finite]
    exact gaussian_finiteHermite_weak_dbar n hn _ j
  · intro j k
    have hsecond : Tendsto
        (fun s => gaussianInverseSquareRootSecondSynthesis hn (finiteDbarComponentL2 n hn (c s) j) j
            k)
        atTop (𝓝 (gaussianInverseSquareRootSecondSynthesis hn (D j) j k)) :=
      (gaussianInverseSquareRootSecondSynthesisCLM hn j k).continuous.continuousAt.tendsto.comp (hD
          j)
    refine gaussianWeakDbar_of_tendsto k (fun s =>
      (gaussianInverseSquareRootFirstSynthesis hn (finiteDbarComponentL2 n hn (c s) j) j,
        gaussianInverseSquareRootSecondSynthesis hn (finiteDbarComponentL2 n hn (c s) j) j k))
      _ _ ?_ ((hfirst j).prodMk_nhds hsecond)
    intro s
    rw [gaussianInverseSquareRootFirstSynthesis_finite,
      gaussianInverseSquareRootSecondSynthesis_finite]
    exact gaussian_finiteHermite_weak_dbar n hn _ k

/-- The compact smooth Gaussian endpoint discharges the first-derivative
coefficient identities using actual Gaussian integration by parts. -/
theorem gaussianInverseSquareRoot_smoothCompact_weak_derivatives {n : ℕ} (hn : 0 < n)
    (F : Configuration n → ℂ) (hF : ContDiff ℝ 1 F) (hc : HasCompactSupport F) :
    (∀ j, IsGaussianWeakDbar n
      (gaussianHermiteInverseSquareRoot hn (smoothCompactL2 F hF hc))
      (gaussianInverseSquareRootFirstSynthesis hn (smoothDbarComponentL2 F hF hc j) j) j) ∧
    (∀ j k, IsGaussianWeakDbar n
      (gaussianInverseSquareRootFirstSynthesis hn (smoothDbarComponentL2 F hF hc j) j)
      (gaussianInverseSquareRootSecondSynthesis hn (smoothDbarComponentL2 F hF hc j) j k) k) :=
  gaussianInverseSquareRoot_weak_derivatives hn _ _
    (fun j pq => gaussianHermiteCoefficient_smoothDbarComponentL2_raise hn F hF hc j pq)

end
end GinibrePoincare
