/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevBall
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityGNSmooth
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticitySobolevSmooth

/-!
# Smooth Sobolev inequalities on three-dimensional space

The whole-space estimates used in `lem:vorticity-products` of the
Escauriaza–Seregin–Šverák manuscript.
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

private theorem integrable_sq_smooth_compact {g : Vec3 → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    Integrable (fun x => g x ^ 2) volume := by
  have hc : HasCompactSupport (fun x : Vec3 => g x ^ 2) := by
    have hc' : HasCompactSupport (g * g) := hgc.mul_right
    change HasCompactSupport (fun x : Vec3 => g x * g x) at hc'
    simpa only [pow_two] using hc'
  exact (hg.continuous.pow 2).integrable_of_hasCompactSupport hc

/-- A scalar whole-space Gagliardo–Nirenberg estimate for smooth compactly
supported functions. -/
theorem gradL4_sq_le_smooth_scalar
    (f : Vec3 → ℝ) (M : ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (hM : ∀ x, |f x| ≤ M) :
    Integrable (fun x => (∑ j : Fin 3, spatialDeriv f j x ^ 2) ^ 2) volume ∧
      Integrable (fun x => ∑ j : Fin 3, ∑ k : Fin 3,
        spatialDeriv (spatialDeriv f j) k x ^ 2) volume ∧
      ∫ x, (∑ j : Fin 3, spatialDeriv f j x ^ 2) ^ 2 ≤
        28 * M ^ 2 * ∫ x, ∑ j : Fin 3, ∑ k : Fin 3,
          spatialDeriv (spatialDeriv f j) k x ^ 2 := by
  let g : Fin 3 → Vec3 → ℝ := fun j => spatialDeriv f j
  have hg : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (g j) :=
    fun j => contDiff_spatialDeriv_smooth hf j
  have hgc : ∀ j, HasCompactSupport (g j) :=
    fun j => hfc.fderiv_apply (𝕜 := ℝ) (basisVec j)
  have hgd : ∀ j, Differentiable ℝ (g j) :=
    fun j => (hg j).differentiable (by simp)
  let A : Vec3 → ℝ := fun x => ∑ j : Fin 3, g j x ^ 2
  have hA : ContDiff ℝ (⊤ : ℕ∞) A :=
    ContDiff.sum fun j _ => (hg j).pow 2
  let Φ : Fin 3 → Vec3 → ℝ := fun j x => A x * g j x
  have hΦ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (Φ j) :=
    fun j => hA.mul (hg j)
  have hΦc : ∀ j, HasCompactSupport (Φ j) :=
    fun j => (hgc j).mul_left
  have hΦd : ∀ j x, spatialDeriv (Φ j) j x =
      (∑ k : Fin 3, 2 * g k x * spatialDeriv (g k) j x) * g j x +
        A x * spatialDeriv (g j) j x := by
    intro j x
    change spatialDeriv (fun y => A y * g j y) j x = _
    rw [spatialDeriv_mul ((hA.differentiable (by simp)) x) ((hgd j) x),
      vorticityGNSmooth_deriv_sum_sq hgd j x]
  have hΦderivCont : ∀ j, Continuous (spatialDeriv (Φ j) j) :=
    fun j => (contDiff_spatialDeriv_smooth (hΦ j) j).continuous
  have hΦderivc : ∀ j, HasCompactSupport (spatialDeriv (Φ j) j) :=
    fun j => (hΦc j).fderiv_apply (𝕜 := ℝ) (basisVec j)
  have hfΦint : ∀ j, Integrable (fun x => f x * spatialDeriv (Φ j) j x)
      (volume : Measure Vec3) := fun j =>
    (hf.continuous.mul (hΦderivCont j)).integrable_of_hasCompactSupport
      (hΦderivc j).mul_left
  have hgΦint : ∀ j, Integrable (fun x => g j x * Φ j x)
      (volume : Measure Vec3) := fun j =>
    ((hg j).continuous.mul (hΦ j).continuous).integrable_of_hasCompactSupport
      (hΦc j).mul_left
  let E : Vec3 → ℝ := fun x => -∑ j : Fin 3, f x * spatialDeriv (Φ j) j x
  have hEint : Integrable E (volume : Measure Vec3) :=
    (integrable_finsetSum _ fun j _ => hfΦint j).neg
  have hAform : ∀ x, A x ^ 2 = ∑ j : Fin 3, g j x * Φ j x := by
    intro x
    simp only [Φ, A, Fin.sum_univ_three]
    ring
  have hAint : Integrable (fun x => A x ^ 2) (volume : Measure Vec3) := by
    simp only [hAform]
    exact integrable_finsetSum _ fun j _ => hgΦint j
  have hX : ∫ x, A x ^ 2 = ∫ x, E x := by
    simp only [hAform, E]
    rw [integral_finsetSum _ fun j _ => hgΦint j, integral_neg,
      integral_finsetSum _ fun j _ => hfΦint j, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hibp := integral_mul_spatialDeriv_eq_neg_integral_spatialDeriv_mul
      hf (hΦ j) (hΦc j) j
    rw [hibp, neg_neg]
  let HH : Vec3 → ℝ := fun x => ∑ j : Fin 3, ∑ k : Fin 3,
    spatialDeriv (g j) k x ^ 2
  have hHHcont : Continuous HH :=
    continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ =>
      (contDiff_spatialDeriv_smooth (hg j) k).continuous.pow 2
  have hHHc : HasCompactSupport HH := by
    apply hfc.mono'
    intro x hx
    by_contra hxf
    have hxg (j : Fin 3) : x ∉ tsupport (g j) := by
      intro hj
      apply hxf
      exact (tsupport_fderiv_apply_subset ℝ (basisVec j)) hj
    have hz (j k : Fin 3) : spatialDeriv (g j) k x = 0 := by
      simp [spatialDeriv, fderiv_of_notMem_tsupport ℝ (hxg j)]
    exact hx (by simp [HH, hz])
  have hHHint : Integrable HH (volume : Measure Vec3) :=
    hHHcont.integrable_of_hasCompactSupport hHHc
  have hEform : ∀ x, E x =
      -(f x * ((∑ j : Fin 3, ∑ k : Fin 3,
        2 * g k x * spatialDeriv (g k) j x * g j x) +
          A x * ∑ j : Fin 3, spatialDeriv (g j) j x)) := by
    intro x
    simp only [E, hΦd, Fin.sum_univ_three]
    ring
  have hpoint : ∀ x, E x ≤ 3 / 4 * A x ^ 2 + M ^ 2 * (7 * HH x) := by
    intro x
    rw [hEform]
    simpa only [one_pow, one_mul, mul_one, zero_mul, zero_add, mul_zero, add_zero,
      Fin.sum_univ_three, zero_pow (by norm_num : 2 ≠ 0), A, HH] using
      (vorticityGNSmooth_pointwise (F := f x) (M := M) (η := 1)
        (fun _ => 0) (fun j => g j x)
        (fun j k => spatialDeriv (g k) j x) (hM x))
  have hmain : ∫ x, A x ^ 2 ≤
      3 / 4 * (∫ x, A x ^ 2) + M ^ 2 * (7 * ∫ x, HH x) := by
    calc
      ∫ x, A x ^ 2 = ∫ x, E x := hX
      _ ≤ ∫ x, (3 / 4 * A x ^ 2 + M ^ 2 * (7 * HH x)) :=
        integral_mono hEint ((hAint.const_mul _).add ((hHHint.const_mul _).const_mul _))
          hpoint
      _ = _ := by
        rw [integral_add (hAint.const_mul _) ((hHHint.const_mul _).const_mul _),
          integral_const_mul, integral_const_mul, integral_const_mul]
  refine ⟨hAint, hHHint, ?_⟩
  change ∫ x, A x ^ 2 ≤ 28 * M ^ 2 * ∫ x, HH x
  linarith only [hmain]

/-- The order-two Sobolev norm controls every value of a smooth compactly
supported function in three dimensions (`lem:vorticity-products`, ESS). -/
theorem abs_le_sobolevTwo_smooth :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Vec3 → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      ∀ x, |f x| ≤ C * Real.sqrt
        (sobolevNormSqOn 2 univ (fun α => wordDeriv α f)) := by
  obtain ⟨C₀, hC₀, hlocal⟩ := vorticitySobolevSmooth_sup
    (r := (1 : ℝ)) (R := (2 : ℝ)) (by norm_num) (by norm_num)
  refine ⟨Real.sqrt (13 * C₀), Real.sqrt_nonneg _, ?_⟩
  intro f hf hfc x
  let F : Vec3 → ℝ := fun y =>
    f y ^ 2 + ∑ j : Fin 3, spatialDeriv f j y ^ 2 +
      ∑ j : Fin 3, ∑ k : Fin 3, spatialDeriv (spatialDeriv f j) k y ^ 2
  have h0int : Integrable (fun y => f y ^ 2) volume :=
    integrable_sq_smooth_compact hf hfc
  have h1int (j : Fin 3) :
      Integrable (fun y => spatialDeriv f j y ^ 2) volume :=
    integrable_sq_smooth_compact (contDiff_spatialDeriv_smooth hf j)
      (hfc.fderiv_apply (𝕜 := ℝ) (basisVec j))
  have h2int (j k : Fin 3) :
      Integrable (fun y => spatialDeriv (spatialDeriv f j) k y ^ 2) volume :=
    integrable_sq_smooth_compact
      (contDiff_spatialDeriv_smooth (contDiff_spatialDeriv_smooth hf j) k)
      ((hfc.fderiv_apply (𝕜 := ℝ) (basisVec j)).fderiv_apply (𝕜 := ℝ)
        (basisVec k))
  have hsum1int : Integrable (fun y => ∑ j : Fin 3, spatialDeriv f j y ^ 2) volume :=
    integrable_finsetSum _ fun j _ => h1int j
  have hsum2int : Integrable
      (fun y => ∑ j : Fin 3, ∑ k : Fin 3,
        spatialDeriv (spatialDeriv f j) k y ^ 2) volume :=
    integrable_finsetSum _ fun j _ =>
      integrable_finsetSum _ fun k _ => h2int j k
  have hFint : Integrable F volume :=
    (h0int.add hsum1int).add hsum2int
  have hFnn (y : Vec3) : 0 ≤ F y := by
    dsimp [F]
    positivity
  have hball : ∫ y in vec3Ball x 2, F y ≤ ∫ y, F y :=
    setIntegral_le_integral hFint (ae_of_all volume hFnn)
  let N : ℝ := sobolevNormSqOn 2 univ (fun α => wordDeriv α f)
  have hNnn : 0 ≤ N := by
    dsimp [N, sobolevNormSqOn]
    exact Finset.sum_nonneg fun α _ => integral_nonneg fun y => sq_nonneg _
  have hsingle (α : List (Fin 3)) (hα : α.length ≤ 2) :
      ∫ y, wordDeriv α f y ^ 2 ≤ N := by
    dsimp [N, sobolevNormSqOn]
    simp only [Measure.restrict_univ]
    exact Finset.single_le_sum
      (f := fun β : List (Fin 3) => ∫ y, wordDeriv β f y ^ 2)
      (s := sobolevWords 2)
      (fun β _ => integral_nonneg fun y => sq_nonneg (wordDeriv β f y))
      (mem_sobolevWords.mpr hα)
  have h0 : ∫ y, f y ^ 2 ≤ N := hsingle [] (by norm_num)
  have h1 (j : Fin 3) : ∫ y, spatialDeriv f j y ^ 2 ≤ N := by
    simpa only [wordDeriv] using hsingle [j] (by simp)
  have h2 (j k : Fin 3) :
      ∫ y, spatialDeriv (spatialDeriv f j) k y ^ 2 ≤ N := by
    simpa only [wordDeriv] using hsingle [j, k] (by simp)
  have hFbound : ∫ y, F y ≤ 13 * N := by
    have hsum1 : ∑ j : Fin 3, (∫ y, spatialDeriv f j y ^ 2) ≤ 3 * N := by
      calc
        _ ≤ ∑ _j : Fin 3, N := Finset.sum_le_sum fun j _ => h1 j
        _ = 3 * N := by simp
    have hsum2 : ∑ j : Fin 3, ∑ k : Fin 3,
        (∫ y, spatialDeriv (spatialDeriv f j) k y ^ 2) ≤ 9 * N := by
      calc
        _ ≤ ∑ _j : Fin 3, ∑ _k : Fin 3, N :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => h2 j k
        _ = 9 * N := by simp only [Fin.sum_univ_three]; ring
    have houter : ∫ y, F y =
        (∫ y, f y ^ 2 + ∑ j : Fin 3, spatialDeriv f j y ^ 2) +
          ∫ y, ∑ j : Fin 3, ∑ k : Fin 3,
            spatialDeriv (spatialDeriv f j) k y ^ 2 := by
      exact integral_add (h0int.add hsum1int) hsum2int
    have hinner : ∫ y, f y ^ 2 + ∑ j : Fin 3, spatialDeriv f j y ^ 2 =
        (∫ y, f y ^ 2) + ∫ y, ∑ j : Fin 3, spatialDeriv f j y ^ 2 := by
      exact integral_add h0int hsum1int
    rw [houter, hinner,
      integral_finsetSum _ fun j _ => h1int j,
      integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => h2int j k]
    simp_rw [integral_finsetSum _ fun k _ => h2int _ k]
    linarith only [h0, hsum1, hsum2]
  have hx0 : vec3EuclideanNorm (x - x) ≤ (1 : ℝ) := by
    simp [vec3EuclideanNorm]
  have hxbound := hlocal x f hf x hx0
  have hxSq : |f x| ^ 2 ≤ (13 * C₀) * N := by
    calc
      |f x| ^ 2 ≤ C₀ * ∫ y in vec3Ball x 2, F y := hxbound
      _ ≤ C₀ * ∫ y, F y := by gcongr
      _ ≤ C₀ * (13 * N) := by gcongr
      _ = (13 * C₀) * N := by ring
  have hsqrt := Real.sqrt_le_sqrt hxSq
  rw [Real.sqrt_sq_eq_abs, abs_abs] at hsqrt
  rw [Real.sqrt_mul (by positivity : 0 ≤ 13 * C₀)] at hsqrt
  exact hsqrt

end CKN
