/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/PolynomialSectorIncompleteness.lean.
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

public import LeanPool.GinibrePoincare.Analysis.PolynomialSectorHilbertBasis
public import LeanPool.GinibrePoincare.Analysis.GinibreFullGeneratorPolynomialMoments
public import LeanPool.GinibrePoincare.Analysis.GinibreInteriorWeakGradient
public import LeanPool.GinibrePoincare.Analysis.GinibreRelativePhaseInvariance
public import LeanPool.GinibrePoincare.Analysis.FiniteHermiteDeficit
public import LeanPool.GinibrePoincare.Analysis.GinibreDistributionalClosure
public import LeanPool.GinibrePoincare.Analysis.L2RepresentativeBridges
public import LeanPool.GinibrePoincare.Analysis.RadialSobolevClosure
public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported

/-! The genuine centered quadratic excluded by the Hermite–Laguerre sector. -/

@[expose] public section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace GinibrePoincare
noncomputable section

/-- The holomorphic quadratic `∑ j, (z j - S / n) ^ 2` of the recentered configuration, where
`S` is the coordinate sum. -/
def ginibreCenteredQuadratic (n : ℕ) (z : Configuration n) : ℂ :=
  ∑ j, (recenteredConfiguration n z j)^2

theorem ginibreCenteredQuadratic_continuous (n : ℕ) :
    Continuous (ginibreCenteredQuadratic n) := by
  unfold ginibreCenteredQuadratic recenteredConfiguration projectToOrthogonal coordinateSum
  fun_prop

theorem ginibreCenteredQuadratic_norm_le_radius (n : ℕ) (hn : 0 < n)
    (z : Configuration n) : ‖ginibreCenteredQuadratic n z‖ ≤ pairwiseRadius z := by
  have ht : ‖ginibreCenteredQuadratic n z‖ ≤ recenteredSqNorm n z := by
    unfold ginibreCenteredQuadratic recenteredSqNorm configurationNormSq
    have h := norm_sum_le (Finset.univ : Finset (Fin n)) (fun j => (recenteredConfiguration n z
        j)^2)
    simpa only [norm_pow, Complex.normSq_eq_norm_sq] using h
  rw [pairwiseRadius_eq_radialObservable]
  unfold radialObservable
  have hp : 0 ≤ recenteredSqNorm n z := by
    unfold recenteredSqNorm configurationNormSq
    exact Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

theorem ginibreCenteredQuadratic_memLp (n : ℕ) (hn : 2 ≤ n) :
    MemLp (ginibreCenteredQuadratic n) 2 (ginibreMeasure n) := by
  have hc : Continuous (pairwiseRadius : Configuration n → ℝ) := by
    unfold pairwiseRadius
    fun_prop
  have hi : Integrable (fun z : Configuration n => pairwiseRadius z^2) (ginibreMeasure n) := by
    simpa using ginibreFull_polynomial_joint_moment_integrable n hn 0 2
  have hR : MemLp (pairwiseRadius : Configuration n → ℝ) 2 (ginibreMeasure n) := by
    apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
    simpa only [Real.norm_eq_abs, sq_abs] using hi
  exact hR.mono' (ginibreCenteredQuadratic_continuous n).aestronglyMeasurable
    (Filter.Eventually.of_forall (ginibreCenteredQuadratic_norm_le_radius n (by omega)))

theorem ginibreCenteredQuadratic_symmetric (n : ℕ) :
    ∀ σ : Fin n ≃ Fin n, ∀ z, ginibreCenteredQuadratic n (z ∘ σ) = ginibreCenteredQuadratic n z :=
        by
  intro σ z
  have hS : coordinateSum (z ∘ σ) = coordinateSum z := by
    unfold coordinateSum
    exact Equiv.sum_comp σ z
  unfold ginibreCenteredQuadratic recenteredConfiguration projectToOrthogonal
  simp only [hS, Function.comp_apply]
  exact Equiv.sum_comp σ (fun i => (z i-coordinateSum z/(n : ℂ))^2)

theorem ginibreCenteredQuadratic_not_identically_zero {n : ℕ} (hn : 2 ≤ n) :
    ginibreCenteredQuadratic n ≠ 0 := by
  let j : Fin n := ⟨0, by omega⟩
  let k : Fin n := ⟨1, by omega⟩
  have hjk : j ≠ k := by intro h; have := congrArg Fin.val h; simp [j, k] at this
  let z : Configuration n := fun i => if i=j then 1 else if i=k then -1 else 0
  have hS : coordinateSum z = 0 := by
    have he : z = fun i => (if i=j then (1 : ℂ) else 0)-(if i=k then (1 : ℂ) else 0) := by
      funext i
      dsimp [z]
      split_ifs <;> simp_all
    rw [he]
    simp [coordinateSum, Finset.sum_sub_distrib]
  have hQ : ginibreCenteredQuadratic n z = 2 := by
    unfold ginibreCenteredQuadratic
    rw [recentered_eq_self z hS]
    have he (i : Fin n) : (z i)^2 = (if i=j then (1 : ℂ) else 0)+(if i=k then 1 else 0) := by
      dsimp [z]
      split_ifs <;> simp_all
    simp_rw [he]
    norm_num [Finset.sum_add_distrib]
  intro he
  have hh := congrFun he z
  rw [hQ] at hh
  norm_num at hh

/-- The excluded quadratic is a genuinely nonzero interacting L² vector. -/
def ginibreCenteredQuadraticL2 (n : ℕ) (hn : 2 ≤ n) : GinibrePolynomialL2 n :=
  (ginibreCenteredQuadratic_memLp n hn).toLp (ginibreCenteredQuadratic n)

theorem ginibreCenteredQuadraticL2_ne_zero (n : ℕ) (hn : 2 ≤ n) :
    ginibreCenteredQuadraticL2 n hn ≠ 0 := by
  intro h
  have hae : ginibreCenteredQuadratic n =ᵐ[ginibreMeasure n] 0 := by
    have he := (ginibreCenteredQuadratic_memLp n hn).coeFn_toLp
    change ginibreCenteredQuadraticL2 n hn =ᵐ[ginibreMeasure n] ginibreCenteredQuadratic n at he
    rw [h] at he
    exact he.symm.trans (Lp.coeFn_zero _ _ _)
  have hv := (ginibre_ae_eq_iff_volume n (by omega) _ _).mp hae
  have he := ((ginibreCenteredQuadratic_continuous n).ae_eq_iff_eq volume continuous_const).mp hv
  exact ginibreCenteredQuadratic_not_identically_zero hn he

theorem ginibreCenteredQuadratic_integral_orthogonal_of_preserving
    (n : ℕ) (T : Configuration n → Configuration n)
    (hT : MeasurePreserving T (ginibreMeasure n) (ginibreMeasure n))
    (hQ : ∀ z, ginibreCenteredQuadratic n (T z) = -ginibreCenteredQuadratic n z)
    (F : Configuration n → ℂ) (hF : Continuous F) (hFT : ∀ z, F (T z) = F z) :
    (∫ z, conj (ginibreCenteredQuadratic n z)*F z ∂ginibreMeasure n)=0 := by
  let H : Configuration n → ℂ := fun z => conj (ginibreCenteredQuadratic n z)*F z
  have hm : AEStronglyMeasurable H (ginibreMeasure n) :=
    ((Complex.continuous_conj.comp (ginibreCenteredQuadratic_continuous n)).mul
        hF).aestronglyMeasurable
  have he : (∫ z, H (T z) ∂ginibreMeasure n) = ∫ z, H z ∂ginibreMeasure n := by
    have hx := integral_map hT.measurable.aemeasurable (hT.map_eq.symm ▸ hm)
    rw [hT.map_eq] at hx
    exact hx.symm
  have hfun : (fun z => H (T z)) = fun z => -H z := by
    funext z
    dsimp [H]
    rw [hQ, hFT, map_neg, neg_mul]
  rw [hfun, integral_neg] at he
  change ∫ z, H z ∂ginibreMeasure n = 0
  have htwo : (2 : ℂ)*(∫ z, H z ∂ginibreMeasure n)=0 := by linear_combination -he
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

theorem ginibreCenteredQuadraticL2_inner (n : ℕ) (hn : 2 ≤ n)
    (i : PolynomialEigenfunctionData n) :
    inner ℂ (ginibreCenteredQuadraticL2 n hn) (polynomialEigenfunctionL2 n hn i) =
      ∫ z, conj (ginibreCenteredQuadratic n z)*polynomialEigenfunction n i z ∂ginibreMeasure n := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(ginibreCenteredQuadratic_memLp n hn).coeFn_toLp,
    polynomialEigenfunctionL2_coeFn n hn i] with z hz hi
  change (ginibreCenteredQuadraticL2 n hn) z = ginibreCenteredQuadratic n z at hz
  rw [hz, hi, RCLike.inner_apply]
  ring

theorem ginibreCenteredQuadraticL2_orthogonal_of_integrals (n : ℕ) (hn : 2 ≤ n)
    (he : ∀ i : PolynomialEigenfunctionData n,
      (∫ z, conj (ginibreCenteredQuadratic n z)*polynomialEigenfunction n i z ∂ginibreMeasure n)=0)
          :
    ginibreCenteredQuadraticL2 n hn ∈ (closedPolynomialSector n hn)ᗮ := by
  unfold closedPolynomialSector
  rw [Submodule.orthogonal_closure, Submodule.mem_orthogonal']
  intro F hF
  induction hF using Submodule.span_induction with
  | mem F h =>
    obtain ⟨i, rfl⟩ := h
    rw [ginibreCenteredQuadraticL2_inner, he]
  | zero => simp
  | add x y _ _ hx hy => simp [inner_add_right, hx, hy]
  | smul c x _ hx => simp [inner_smul_right, hx]

theorem closedPolynomialSector_ne_top_of_quadratic_orthogonal (n : ℕ) (hn : 2 ≤ n)
    (hQ : ginibreCenteredQuadraticL2 n hn ∈ (closedPolynomialSector n hn)ᗮ) :
    closedPolynomialSector n hn ≠ ⊤ := by
  intro h
  have hh := (Submodule.mem_orthogonal' _ _).mp hQ (ginibreCenteredQuadraticL2 n hn) (h ▸
      Submodule.mem_top)
  exact ginibreCenteredQuadraticL2_ne_zero n hn (inner_self_eq_zero.mp hh)

theorem ginibreCenteredQuadratic_quarterTurn {n : ℕ} (hn : 0 < n)
    (z : Configuration n) :
    ginibreCenteredQuadratic n (ginibreRelativeQuarterTurn n z) = -ginibreCenteredQuadratic n z :=
        by
  unfold ginibreCenteredQuadratic
  rw [recentered_ginibreRelativeQuarterTurn hn]
  simp only [mul_pow, Complex.I_sq, neg_one_mul, Finset.sum_neg_distrib]

/-- The paper's quadratic is genuinely orthogonal to every polynomial in `S`, `conj S`, and `R`. -/
theorem ginibreCenteredQuadratic_orthogonal_polynomial {n : ℕ} (hn : 0 < n)
    (F : Configuration n → ℂ) (hF : IsPolynomialInSConjSR F) :
    (∫ z, conj (ginibreCenteredQuadratic n z) * F z ∂ginibreMeasure n) = 0 := by
  obtain ⟨P, hP⟩ := hF
  have hcont : Continuous F := by
    have he : F = fun z =>
        MvPolynomial.eval ![SObservable z, conj (SObservable z), (RPoly z : ℂ)] P :=
      funext hP
    rw [he]
    apply (MvPolynomial.continuous_eval P).comp
    apply continuous_pi
    intro i
    fin_cases i <;>
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.mk_one, Fin.reduceFinMk,
        SObservable, RPoly, coordinateSum, pairwiseRadius] <;>
      fun_prop
  apply ginibreCenteredQuadratic_integral_orthogonal_of_preserving n
    (ginibreRelativeQuarterTurn n) (measurePreserving_ginibreRelativeQuarterTurn hn)
    (ginibreCenteredQuadratic_quarterTurn hn) F hcont
  intro z
  rw [hP, hP]
  simp only [SObservable, RPoly, coordinateSum_ginibreRelativeQuarterTurn hn,
    pairwiseRadius_ginibreRelativeQuarterTurn]

theorem ginibreCenteredQuadraticL2_orthogonal (n : ℕ) (hn : 2 ≤ n) :
    ginibreCenteredQuadraticL2 n hn ∈ (closedPolynomialSector n hn)ᗮ := by
  apply ginibreCenteredQuadraticL2_orthogonal_of_integrals
  intro i
  exact ginibreCenteredQuadratic_orthogonal_polynomial (by omega) _
    (polynomialEigenfunction_isPolynomial n i)

/-- The Hermite–Laguerre family spans a proper sector, even among symmetric
functions: its nonzero orthogonal witness is the literal symmetric quadratic Q. -/
theorem polynomialSector_incomplete (n : ℕ) (hn : 2 ≤ n) :
    ginibreCenteredQuadraticL2 n hn ≠ 0 ∧
      (∀ σ : Fin n ≃ Fin n, ∀ z, ginibreCenteredQuadratic n (z ∘ σ)=ginibreCenteredQuadratic n z) ∧
      ginibreCenteredQuadraticL2 n hn ∈ (closedPolynomialSector n hn)ᗮ ∧
      closedPolynomialSector n hn ≠ ⊤ := by
  have hQ := ginibreCenteredQuadraticL2_orthogonal n hn
  exact ⟨ginibreCenteredQuadraticL2_ne_zero n hn, ginibreCenteredQuadratic_symmetric n,
    hQ, closedPolynomialSector_ne_top_of_quadratic_orthogonal n hn hQ⟩

end
end GinibrePoincare
