/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSobolevFour
public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingSobolevEmbedding
public import LeanPool.CaffarelliKohnNirenberg.Foundation.SobolevEmbeddingR3
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Whole-space gradient fourth-power bound

The Gagliardo–Nirenberg estimate for smooth compactly supported
functions extends to smooth `H²` functions by whole-space integration
by parts. The `L⁴` membership of the first derivatives supplies the
integrability needed at infinity.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private instance lpsHolderFourFourTwo :
    ENNReal.HolderTriple 4 4 2 := by
  refine ⟨?_⟩
  rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num,
    ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 4),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
    ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num

private instance lpsHolderTwoTwoOne :
    ENNReal.HolderTriple 2 2 1 := by
  refine ⟨?_⟩
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
    ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by norm_num,
    ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 1)]
  norm_num

/-- A smooth whole-space `H²` scalar field with bound `|f| ≤ M`
satisfies the gradient `L⁴` estimate without a support assumption
(`eq:lps-Hm-energy`). -/
theorem lps_gradL4_sq_le_smooth_h2
    (f : Vec3 → ℝ) (M : ℝ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hL2 : ∀ α : List (Fin 3), α.length ≤ 2 →
      MemLp (wordDeriv α f) 2 volume)
    (hM : ∀ x, |f x| ≤ M) :
    Integrable (fun x => (∑ j : Fin 3, spatialDeriv f j x ^ 2) ^ 2) volume ∧
    ∫ x, (∑ j : Fin 3, spatialDeriv f j x ^ 2) ^ 2 ≤
      28 * M ^ 2 * ∫ x, ∑ j : Fin 3, ∑ k : Fin 3,
        spatialDeriv (spatialDeriv f j) k x ^ 2 := by
  let g : Fin 3 → Vec3 → ℝ := fun j => spatialDeriv f j
  have hg : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (g j) :=
    fun j => contDiff_spatialDeriv_smooth hf j
  have hgd : ∀ j, Differentiable ℝ (g j) :=
    fun j => (hg j).differentiable (by simp)
  have hg2 (j : Fin 3) : MemLp (g j) 2 volume := by
    simpa only [g, wordDeriv] using hL2 [j] (by simp)
  have hg4 (j : Fin 3) : MemLp (g j) 4 volume :=
    lps_smooth_first_derivative_memLp_four f hf hL2 j
  have hD2 (j k : Fin 3) : MemLp (spatialDeriv (g j) k) 2 volume := by
    simpa only [g, wordDeriv] using hL2 [j, k] (by simp)
  have hgsq2 (j : Fin 3) : MemLp (fun x => g j x ^ 2) 2 volume := by
    have heq : (g j * g j) = (fun x => g j x ^ 2) := by
      funext x
      simp [Pi.mul_apply, pow_two]
    rw [← heq]
    exact (hg4 j).mul (hg4 j)
  let A : Vec3 → ℝ := fun x => ∑ j : Fin 3, g j x ^ 2
  have hA : ContDiff ℝ (⊤ : ℕ∞) A :=
    ContDiff.sum fun j _ => (hg j).pow 2
  have hA2 : MemLp A 2 volume :=
    memLp_finsetSum Finset.univ (fun j _ => hgsq2 j)
  have hAint : Integrable (fun x => A x ^ 2) volume := hA2.integrable_sq
  let Φ : Fin 3 → Vec3 → ℝ := fun j x => A x * g j x
  have hΦ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (Φ j) :=
    fun j => hA.mul (hg j)
  have hΦd : ∀ j x, spatialDeriv (Φ j) j x =
      (∑ k : Fin 3, 2 * g k x * spatialDeriv (g k) j x) * g j x +
        A x * spatialDeriv (g j) j x := by
    intro j x
    change spatialDeriv (fun y => A y * g j y) j x = _
    rw [spatialDeriv_mul ((hA.differentiable (by simp)) x) ((hgd j) x),
      vorticityGNSmooth_deriv_sum_sq hgd j x]
  have hterm (j k : Fin 3) :
      Integrable (fun x =>
        (2 * g k x * spatialDeriv (g k) j x) * g j x) volume := by
    have hprod : MemLp (fun x => g k x * g j x) 2 volume := by
      have heq : (g k * g j) = (fun x => g k x * g j x) := by
        funext x
        rfl
      rw [← heq]
      exact (hg4 k).mul (hg4 j)
    have hint : Integrable
        (fun x => (g k x * g j x) * spatialDeriv (g k) j x)
        volume := by
      have heq : ((fun x => g k x * g j x) * spatialDeriv (g k) j) =
          (fun x => (g k x * g j x) * spatialDeriv (g k) j x) := by
        funext x
        rfl
      rw [← heq]
      exact hprod.integrable_mul (hD2 k j)
    convert hint.const_mul 2 using 1
    funext x
    ring
  have htermSum (j : Fin 3) :
      Integrable (fun x =>
        (∑ k : Fin 3, 2 * g k x * spatialDeriv (g k) j x) * g j x)
        volume := by
    have hsum := integrable_finsetSum (Finset.univ : Finset (Fin 3))
      (fun k _ => hterm j k)
    convert hsum using 1
    funext x
    rw [Finset.sum_mul]
  have hDΦint (j : Fin 3) :
      Integrable (spatialDeriv (Φ j) j) volume := by
    have hpart : Integrable (fun x => A x * spatialDeriv (g j) j x)
        volume := hA2.integrable_mul (hD2 j j)
    exact (htermSum j).add hpart |>.congr
      (Filter.Eventually.of_forall fun x => (hΦd j x).symm)
  have hΦint (j : Fin 3) : Integrable (Φ j) volume :=
    hA2.integrable_mul (hg2 j)
  have hfΦint (j : Fin 3) :
      Integrable (fun x => f x * spatialDeriv (Φ j) j x) volume :=
    (hDΦint j).bdd_mul hf.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using hM x)
  have hgΦint (j : Fin 3) :
      Integrable (fun x => g j x * Φ j x) volume := by
    have hint := (hgsq2 j).integrable_mul hA2
    convert hint using 1
    funext x
    dsimp [Φ]
    ring
  have hfΦcross (j : Fin 3) :
      Integrable (fun x => f x * Φ j x) volume :=
    (hΦint j).bdd_mul hf.continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using hM x)
  let E : Vec3 → ℝ := fun x => -∑ j : Fin 3,
    f x * spatialDeriv (Φ j) j x
  have hEint : Integrable E volume :=
    (integrable_finsetSum _ fun j _ => hfΦint j).neg
  have hAform (x : Vec3) : A x ^ 2 =
      ∑ j : Fin 3, g j x * Φ j x := by
    simp only [Φ, A, Fin.sum_univ_three]
    ring
  have hX : ∫ x, A x ^ 2 = ∫ x, E x := by
    simp only [hAform, E]
    rw [integral_finsetSum _ fun j _ => hgΦint j, integral_neg,
      integral_finsetSum _ fun j _ => hfΦint j, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (μ := volume) (f := f) (g := Φ j) (v := basisVec j)
      (by simpa only [g, spatialDeriv] using hgΦint j)
      (by simpa only [spatialDeriv] using hfΦint j)
      (hfΦcross j)
      (fun x _ => hf.differentiable (by simp) x)
      (fun x _ => (hΦ j).differentiable (by simp) x)
    have hEq : (∫ x, f x * spatialDeriv (Φ j) j x) =
        -(∫ x, g j x * Φ j x) := by
      simpa only [g, spatialDeriv] using hibp
    rw [hEq, neg_neg]
  let HH : Vec3 → ℝ := fun x => ∑ j : Fin 3, ∑ k : Fin 3,
    spatialDeriv (g j) k x ^ 2
  have hHHint : Integrable HH volume :=
    integrable_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun k _ => (hD2 j k).integrable_sq
  have hEform (x : Vec3) : E x =
      -(f x * ((∑ j : Fin 3, ∑ k : Fin 3,
        2 * g k x * spatialDeriv (g k) j x * g j x) +
          A x * ∑ j : Fin 3, spatialDeriv (g j) j x)) := by
    simp only [E, hΦd, Fin.sum_univ_three]
    ring
  have hpoint (x : Vec3) :
      E x ≤ 3 / 4 * A x ^ 2 + M ^ 2 * (7 * HH x) := by
    rw [hEform]
    simpa only [one_pow, one_mul, mul_one, zero_mul, zero_add,
      mul_zero, add_zero, Fin.sum_univ_three,
      zero_pow (by norm_num : 2 ≠ 0), A, HH] using
      (vorticityGNSmooth_pointwise (F := f x) (M := M) (η := 1)
        (fun _ => 0) (fun j => g j x)
        (fun j k => spatialDeriv (g k) j x) (hM x))
  have hmain : ∫ x, A x ^ 2 ≤
      3 / 4 * (∫ x, A x ^ 2) + M ^ 2 * (7 * ∫ x, HH x) := by
    calc
      ∫ x, A x ^ 2 = ∫ x, E x := hX
      _ ≤ ∫ x, (3 / 4 * A x ^ 2 + M ^ 2 * (7 * HH x)) :=
        integral_mono hEint
          ((hAint.const_mul _).add ((hHHint.const_mul _).const_mul _))
          hpoint
      _ = _ := by
        rw [integral_add (hAint.const_mul _)
          ((hHHint.const_mul _).const_mul _),
          integral_const_mul, integral_const_mul, integral_const_mul]
  refine ⟨hAint, ?_⟩
  change ∫ x, A x ^ 2 ≤ 28 * M ^ 2 * ∫ x, HH x
  linarith only [hmain]

/-- The fourth-power gradient integral of a smooth whole-space `H²`
function is bounded by the square of its ordered `H²` energy
(`eq:lps-Hm-energy`). -/
theorem lps_smooth_h2_gradient_four_energy :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Vec3 → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f →
      (∀ α : List (Fin 3), α.length ≤ 2 →
        MemLp (wordDeriv α f) 2 volume) →
      Integrable (fun x =>
        (∑ j : Fin 3, spatialDeriv f j x ^ 2) ^ 2) volume ∧
      (∫ x, (∑ j : Fin 3, spatialDeriv f j x ^ 2) ^ 2) ≤
        C * sobolevNormSqOn 2 univ (fun α => wordDeriv α f) ^ 2 := by
  obtain ⟨Cs, hCs, hsup⟩ := lps_smooth_h2_uniform_bound
  let C : ℝ := 252 * Cs ^ 2
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro f hf hL2
  let N := sobolevNormSqOn 2 univ (fun α => wordDeriv α f)
  have hN : 0 ≤ N := by
    dsimp [N, sobolevNormSqOn]
    exact Finset.sum_nonneg fun α _ => integral_nonneg fun x => sq_nonneg _
  have h0 : MemLp f 2 volume := by
    simpa only [wordDeriv] using hL2 [] (by simp)
  have h1 (j : Fin 3) : MemLp (spatialDeriv f j) 2 volume := by
    simpa only [wordDeriv] using hL2 [j] (by simp)
  have h2 (j k : Fin 3) :
      MemLp (spatialDeriv (spatialDeriv f j) k) 2 volume := by
    simpa only [wordDeriv] using hL2 [j, k] (by simp)
  have hM (x : Vec3) : |f x| ≤ Cs * Real.sqrt N :=
    hsup f hf h0 h1 h2 x
  obtain ⟨hint, hGN⟩ :=
    lps_gradL4_sq_le_smooth_h2 f (Cs * Real.sqrt N) hf hL2 hM
  have hHHle :
      (∫ x, ∑ j : Fin 3, ∑ k : Fin 3,
        spatialDeriv (spatialDeriv f j) k x ^ 2) ≤ 9 * N := by
    rw [integral_finsetSum _ (fun j _ =>
      integrable_finsetSum _ fun k _ => (h2 j k).integrable_sq)]
    simp_rw [integral_finsetSum _ fun k _ => (h2 _ k).integrable_sq]
    calc
      (∑ j : Fin 3, ∑ k : Fin 3,
        ∫ x, spatialDeriv (spatialDeriv f j) k x ^ 2) ≤
          ∑ _j : Fin 3, ∑ _k : Fin 3, N := by
            exact Finset.sum_le_sum fun j _ =>
              Finset.sum_le_sum fun k _ => by
                simpa only [N, wordDeriv] using
                  lps_wordDeriv_integral_le_sobolev 2 f [j, k] (by simp)
      _ = 9 * N := by simp only [Fin.sum_univ_three]; ring
  refine ⟨hint, ?_⟩
  calc
    (∫ x, (∑ j : Fin 3, spatialDeriv f j x ^ 2) ^ 2) ≤
        28 * (Cs * Real.sqrt N) ^ 2 *
          (∫ x, ∑ j : Fin 3, ∑ k : Fin 3,
            spatialDeriv (spatialDeriv f j) k x ^ 2) := hGN
    _ ≤ 28 * (Cs * Real.sqrt N) ^ 2 * (9 * N) := by gcongr
    _ = C * N ^ 2 := by
      dsimp [C]
      rw [mul_pow, Real.sq_sqrt hN]
      ring

private theorem lps_middle_integral_of_four_bounds
    (a b : Vec3 → ℝ) (C Nf Ng : ℝ)
    (hC : 0 ≤ C) (hNf : 0 ≤ Nf) (hNg : 0 ≤ Ng)
    (ha : MemLp (fun x => a x ^ 2) 2 volume)
    (hb : MemLp (fun x => b x ^ 2) 2 volume)
    (ha4 : (∫ x, a x ^ 4) ≤ C * Nf ^ 2)
    (hb4 : (∫ x, b x ^ 4) ≤ C * Ng ^ 2) :
    Integrable (fun x => (a x * b x) ^ 2) volume ∧
      (∫ x, (a x * b x) ^ 2) ≤ C * Nf * Ng := by
  have hprod : Integrable (fun x => (a x * b x) ^ 2) volume := by
    have heq : ((fun x => a x ^ 2) * (fun x => b x ^ 2)) =
        (fun x => (a x * b x) ^ 2) := by
      funext x
      simp only [Pi.mul_apply]
      ring
    rw [← heq]
    exact ha.integrable_mul hb
  have hpq : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Filter.Eventually.of_forall fun x => sq_nonneg (a x))
    (Filter.Eventually.of_forall fun x => sq_nonneg (b x))
    (by simpa only [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num] using ha)
    (by simpa only [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num] using hb)
  have hfour : (∫ x, (a x * b x) ^ 2) ≤
      Real.sqrt (∫ x, a x ^ 4) * Real.sqrt (∫ x, b x ^ 4) := by
    have heqA : (∫ x, (a x ^ 2) ^ 2) = ∫ x, a x ^ 4 := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    have heqB : (∫ x, (b x ^ 2) ^ 2) = ∫ x, b x ^ 4 := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    simp only [Real.rpow_two] at hholder
    rw [heqA, heqB] at hholder
    have heqL : (∫ x, (a x * b x) ^ 2) =
        ∫ x, a x ^ 2 * b x ^ 2 := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    rw [heqL]
    simpa only [Real.sqrt_eq_rpow] using hholder
  have hroot :
      Real.sqrt (C * Nf ^ 2) * Real.sqrt (C * Ng ^ 2) =
        C * Nf * Ng := by
    rw [Real.sqrt_mul hC, Real.sqrt_mul hC,
      Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
      abs_of_nonneg hNf, abs_of_nonneg hNg]
    calc
      Real.sqrt C * Nf * (Real.sqrt C * Ng) =
          Real.sqrt C ^ 2 * Nf * Ng := by ring
      _ = C * Nf * Ng := by rw [Real.sq_sqrt hC]
  refine ⟨hprod, ?_⟩
  calc
    _ ≤ Real.sqrt (∫ x, a x ^ 4) * Real.sqrt (∫ x, b x ^ 4) := hfour
    _ ≤ Real.sqrt (C * Nf ^ 2) * Real.sqrt (C * Ng ^ 2) := by gcongr
    _ = C * Nf * Ng := hroot

/-- The two-first-derivative Leibniz term in the whole-space `H²`
product estimate has one constant independent of the two fields
(`eq:lps-Hm-energy`). -/
theorem lps_smooth_h2_middle_product_energy :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f g : Vec3 → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f →
      ContDiff ℝ (⊤ : ℕ∞) g →
      (∀ α : List (Fin 3), α.length ≤ 2 →
        MemLp (wordDeriv α f) 2 volume) →
      (∀ α : List (Fin 3), α.length ≤ 2 →
        MemLp (wordDeriv α g) 2 volume) →
      ∀ α β : List (Fin 3), α.length = 1 → β.length = 1 →
        Integrable (fun x =>
          (wordDeriv α f x * wordDeriv β g x) ^ 2) volume ∧
        (∫ x, (wordDeriv α f x * wordDeriv β g x) ^ 2) ≤
          C * sobolevNormSqOn 2 univ (fun γ => wordDeriv γ f) *
            sobolevNormSqOn 2 univ (fun γ => wordDeriv γ g) := by
  obtain ⟨C, hC, hgrad⟩ := lps_smooth_h2_gradient_four_energy
  refine ⟨C, hC, ?_⟩
  intro f g hf hg hfL2 hgL2 α β hα hβ
  obtain ⟨j, rfl⟩ : ∃ j : Fin 3, α = [j] := by
    cases α with
    | nil => simp at hα
    | cons j rest =>
        cases rest with
        | nil => exact ⟨j, rfl⟩
        | cons k rest => simp at hα
  obtain ⟨k, rfl⟩ : ∃ k : Fin 3, β = [k] := by
    cases β with
    | nil => simp at hβ
    | cons k rest =>
        cases rest with
        | nil => exact ⟨k, rfl⟩
        | cons l rest => simp at hβ
  let Nf := sobolevNormSqOn 2 univ (fun γ => wordDeriv γ f)
  let Ng := sobolevNormSqOn 2 univ (fun γ => wordDeriv γ g)
  have hNf : 0 ≤ Nf := by
    dsimp [Nf, sobolevNormSqOn]
    exact Finset.sum_nonneg fun γ _ => integral_nonneg fun x => sq_nonneg _
  have hNg : 0 ≤ Ng := by
    dsimp [Ng, sobolevNormSqOn]
    exact Finset.sum_nonneg fun γ _ => integral_nonneg fun x => sq_nonneg _
  obtain ⟨hAfInt, hAfBound⟩ := hgrad f hf hfL2
  obtain ⟨hAgInt, hAgBound⟩ := hgrad g hg hgL2
  have ha4lp := lps_smooth_first_derivative_memLp_four f hf hfL2 j
  have hb4lp := lps_smooth_first_derivative_memLp_four g hg hgL2 k
  have ha2 : MemLp (fun x => spatialDeriv f j x ^ 2) 2 volume := by
    have heq : (spatialDeriv f j * spatialDeriv f j) =
        (fun x => spatialDeriv f j x ^ 2) := by
      funext x
      simp [Pi.mul_apply, pow_two]
    rw [← heq]
    exact ha4lp.mul ha4lp
  have hb2 : MemLp (fun x => spatialDeriv g k x ^ 2) 2 volume := by
    have heq : (spatialDeriv g k * spatialDeriv g k) =
        (fun x => spatialDeriv g k x ^ 2) := by
      funext x
      simp [Pi.mul_apply, pow_two]
    rw [← heq]
    exact hb4lp.mul hb4lp
  have hcoord (q : Vec3 → ℝ) (h : Fin 3) (hh : ContDiff ℝ (⊤ : ℕ∞) q)
      (hL : ∀ α : List (Fin 3), α.length ≤ 2 →
        MemLp (wordDeriv α q) 2 volume)
      (hInt : Integrable (fun x =>
        (∑ i : Fin 3, spatialDeriv q i x ^ 2) ^ 2) volume)
      (hBound : (∫ x, (∑ i : Fin 3, spatialDeriv q i x ^ 2) ^ 2) ≤
        C * sobolevNormSqOn 2 univ (fun γ => wordDeriv γ q) ^ 2)
      (hL4 : MemLp (spatialDeriv q h) 4 volume) :
      (∫ x, spatialDeriv q h x ^ 4) ≤
        C * sobolevNormSqOn 2 univ (fun γ => wordDeriv γ q) ^ 2 := by
    have hcoordInt : Integrable (fun x => spatialDeriv q h x ^ 4) volume := by
      have hsq : MemLp (fun x => spatialDeriv q h x ^ 2) 2 volume := by
        have heq : (spatialDeriv q h * spatialDeriv q h) =
            (fun x => spatialDeriv q h x ^ 2) := by
          funext x
          simp [Pi.mul_apply, pow_two]
        rw [← heq]
        exact hL4.mul hL4
      convert hsq.integrable_sq using 1
      funext x
      ring
    have hpoint (x : Vec3) : spatialDeriv q h x ^ 4 ≤
        (∑ i : Fin 3, spatialDeriv q i x ^ 2) ^ 2 := by
      have hsingle : spatialDeriv q h x ^ 2 ≤
          ∑ i : Fin 3, spatialDeriv q i x ^ 2 :=
        Finset.single_le_sum
          (fun i _ => sq_nonneg (spatialDeriv q i x))
          (Finset.mem_univ h)
      calc
        spatialDeriv q h x ^ 4 = (spatialDeriv q h x ^ 2) ^ 2 := by ring
        _ ≤ (∑ i : Fin 3, spatialDeriv q i x ^ 2) ^ 2 :=
          pow_le_pow_left₀ (sq_nonneg _) hsingle 2
    exact (integral_mono hcoordInt hInt hpoint).trans hBound
  have ha4 : (∫ x, spatialDeriv f j x ^ 4) ≤ C * Nf ^ 2 :=
    hcoord f j hf hfL2 hAfInt hAfBound ha4lp
  have hb4 : (∫ x, spatialDeriv g k x ^ 4) ≤ C * Ng ^ 2 :=
    hcoord g k hg hgL2 hAgInt hAgBound hb4lp
  simpa only [wordDeriv, Nf, Ng] using
    lps_middle_integral_of_four_bounds
      (spatialDeriv f j) (spatialDeriv g k) C Nf Ng hC hNf hNg
      ha2 hb2 ha4 hb4

end ESS
