/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityCutoff
public import LeanPool.CaffarelliKohnNirenberg.Setting.SobolevGlobalH2Core
public import LeanPool.CaffarelliKohnNirenberg.Setting.SobolevGlobalL6
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm

/-!
# A local sup bound for smooth functions by second derivatives

For a smooth function on space, the value at every point of a closed ball is controlled by the
`L²` norms of the function and of its first and second coordinate derivatives on a larger open
ball. This is the three-dimensional embedding of order two used for the pointwise bounds of
`thm:vorticity-regularity` of the Escauriaza–Seregin–Šverák manuscript: a
cutoff reduces it to the whole-space estimate
CKN.smooth_global_linf_uniform, and the first derivatives of the cutoff product are placed in
`L⁶` by CKN.sobolev_L6_global.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN

/-- An `L²` bound from a pointwise bound of the square by an integrable function. -/
theorem vorticitySobolevSmooth_eLpNorm_le {E : Type*} [NormedAddCommGroup E]
    {h : Vec3 → E} (hh : AEStronglyMeasurable h volume) {B : Vec3 → ℝ}
    (hB : Integrable B volume) (hpt : ∀ y, ‖h y‖ ^ 2 ≤ B y) :
    eLpNorm h 2 volume ≤ ENNReal.ofReal (Real.sqrt (∫ y, B y)) := by
  have hB0' : ∀ y, 0 ≤ B y := fun y => (sq_nonneg _).trans (hpt y)
  have hB0 : 0 ≤ᵐ[volume] B := Eventually.of_forall hB0'
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hh]
  have hlin : ∫⁻ y, ‖h y‖ₑ ^ ((2 : ℝ≥0∞).toReal) ≤ ENNReal.ofReal (∫ y, B y) := by
    rw [ofReal_integral_eq_lintegral_ofReal hB hB0]
    apply lintegral_mono
    intro y
    dsimp only
    rw [← ofReal_norm, ENNReal.toReal_ofNat,
      ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.rpow_two]
    exact hpt y
  calc
    _ ≤ (ENNReal.ofReal (∫ y, B y)) ^ (1 / (2 : ℝ≥0∞).toReal) := by gcongr
    _ = _ := by
      rw [ENNReal.toReal_ofNat, ENNReal.ofReal_rpow_of_nonneg
        (integral_nonneg hB0') (by norm_num), Real.sqrt_eq_rpow]

/-- The real `L²` norm version of `CKN.vorticitySobolevSmooth_eLpNorm_le`. -/
theorem vorticitySobolevSmooth_lpNorm_le {E : Type*} [NormedAddCommGroup E]
    {h : Vec3 → E} (hh : AEStronglyMeasurable h volume) {B : Vec3 → ℝ}
    (hB : Integrable B volume) (hpt : ∀ y, ‖h y‖ ^ 2 ≤ B y) :
    lpNorm h 2 volume ≤ Real.sqrt (∫ y, B y) := by
  have hle := vorticitySobolevSmooth_eLpNorm_le hh hB hpt
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  rwa [ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at hreal

/-- The elementary square bound for four products with bounded first factors. -/
theorem vorticitySobolevSmooth_four_sq {a b c d p q s t M : ℝ}
    (ha : |a| ≤ M) (hb : |b| ≤ M) (hc : |c| ≤ M) (hd : |d| ≤ M) :
    (a * p + b * q + c * s + d * t) ^ 2 ≤
      4 * M ^ 2 * (p ^ 2 + q ^ 2 + s ^ 2 + t ^ 2) := by
  have hsq (x y : ℝ) (hx : |x| ≤ M) : (x * y) ^ 2 ≤ M ^ 2 * y ^ 2 := by
    rw [mul_pow]
    have hx2 : x ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs x]
      exact pow_le_pow_left₀ (abs_nonneg x) hx 2
    exact mul_le_mul_of_nonneg_right hx2 (sq_nonneg y)
  have h1 := hsq a p ha
  have h2 := hsq b q hb
  have h3 := hsq c s hc
  have h4 := hsq d t hd
  have hsum : (a * p + b * q + c * s + d * t) ^ 2 ≤
      4 * ((a * p) ^ 2 + (b * q) ^ 2 + (c * s) ^ 2 + (d * t) ^ 2) := by
    nlinarith only [sq_nonneg (a * p - b * q), sq_nonneg (a * p - c * s),
      sq_nonneg (a * p - d * t), sq_nonneg (b * q - c * s), sq_nonneg (b * q - d * t),
      sq_nonneg (c * s - d * t)]
  nlinarith only [hsum, h1, h2, h3, h4]

/-- Local sup bound of order two: the value of a smooth function at a point of the closed ball
of radius `r` is controlled by the `L²` norms of the function and of its first and second
coordinate derivatives on the open ball of radius `R` (the pointwise embedding used in
`thm:vorticity-regularity` (ESS)). -/
theorem vorticitySobolevSmooth_sup {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x₀ : Vec3) (f : Vec3 → ℝ), ContDiff ℝ (⊤ : ℕ∞) f →
      ∀ x, vec3EuclideanNorm (x - x₀) ≤ r →
        |f x| ^ 2 ≤ C * ∫ y in vec3Ball x₀ R,
          (f y ^ 2 + ∑ j : Fin 3, spatialDeriv f j y ^ 2 +
            ∑ j : Fin 3, ∑ k : Fin 3, spatialDeriv (spatialDeriv f j) k y ^ 2) := by
  obtain ⟨φ₀, hφ₀, hφ₀c, hφ₀supp, hφ₀one, hφ₀nn, hφ₀le⟩ :=
    vorticitySpatialCutoff_exists hr hrR
  obtain ⟨L, hL0, hL1, hL2⟩ := vorticitySmooth_derivative_bounds hφ₀ hφ₀c
  obtain ⟨C₀, hC₀, hlinf⟩ := CKN.smooth_global_linf_uniform
  obtain ⟨C₆, hC₆, hsob⟩ := CKN.sobolev_L6_global
  set M₁ : ℝ := 1 + L with hM₁
  have hM₁pos : 0 ≤ M₁ := by rw [hM₁]; linarith only [hL0]
  set K : ℝ := 24 * M₁ ^ 2 with hK
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hK1 : 1 ≤ K := by
    rw [hK]
    have : 1 ≤ M₁ := by rw [hM₁]; linarith only [hL0]
    nlinarith only [this]
  set A : ℝ := C₀ * (Real.sqrt K + 3 * C₆.toReal * Real.sqrt K) with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  refine ⟨A ^ 2, sq_nonneg A, ?_⟩
  intro x₀ f hf x hx
  -- the translated cutoff and the cutoff product
  let φ : Vec3 → ℝ := fun y => φ₀ (y - x₀)
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hφ₀.comp (contDiff_id.sub contDiff_const)
  have hφc : HasCompactSupport φ := hφ₀c.comp_homeomorph (Homeomorph.subRight x₀)
  let g : Vec3 → ℝ := fun y => φ y * f y
  have hg : ContDiff ℝ (⊤ : ℕ∞) g := hφ.mul hf
  have hgc : HasCompactSupport g := hφc.mul_right
  -- derivatives of the translated cutoff
  have hφd1 (j : Fin 3) (y : Vec3) : spatialDeriv φ j y = spatialDeriv φ₀ j (y - x₀) :=
    vorticitySpatialDeriv_translate φ₀ x₀ y j
  have hφd1fun (j : Fin 3) : spatialDeriv φ j = fun y => spatialDeriv φ₀ j (y - x₀) := by
    funext y
    exact hφd1 j y
  have hφd2 (j k : Fin 3) (y : Vec3) :
      spatialDeriv (spatialDeriv φ j) k y =
        spatialDeriv (spatialDeriv φ₀ j) k (y - x₀) := by
    rw [hφd1fun j]
    exact vorticitySpatialDeriv_translate (spatialDeriv φ₀ j) x₀ y k
  -- vanishing of the cutoff factors outside the outer ball
  have hout (y : Vec3) (hy : y ∉ vec3Ball x₀ R) :
      φ y = 0 ∧ (∀ j, spatialDeriv φ j y = 0) ∧
        (∀ j k, spatialDeriv (spatialDeriv φ j) k y = 0) := by
    have hp : y - x₀ ∉ tsupport φ₀ := by
      intro hmem
      apply hy
      have h0 := hφ₀supp hmem
      simpa [vec3Ball] using h0
    refine ⟨by change φ₀ (y - x₀) = 0; exact image_eq_zero_of_notMem_tsupport hp, ?_, ?_⟩
    · intro j
      rw [hφd1 j y]
      change (fderiv ℝ φ₀ (y - x₀)) (basisVec j) = 0
      rw [fderiv_of_notMem_tsupport ℝ hp]
      simp
    · intro j k
      rw [hφd2 j k y]
      have hp' : y - x₀ ∉ tsupport (spatialDeriv φ₀ j) := fun hmem =>
        hp (tsupport_fderiv_apply_subset ℝ (basisVec j) hmem)
      change (fderiv ℝ (spatialDeriv φ₀ j) (y - x₀)) (basisVec k) = 0
      rw [fderiv_of_notMem_tsupport ℝ hp']
      simp
  -- the local quadratic density and its integrable bound
  let Q : Vec3 → ℝ := fun y => f y ^ 2 + ∑ j : Fin 3, spatialDeriv f j y ^ 2 +
    ∑ j : Fin 3, ∑ k : Fin 3, spatialDeriv (spatialDeriv f j) k y ^ 2
  have hQcont : Continuous Q := by
    have h1 (j : Fin 3) : Continuous (spatialDeriv f j) :=
      (contDiff_spatialDeriv_smooth hf j).continuous
    have h2 (j k : Fin 3) : Continuous (spatialDeriv (spatialDeriv f j) k) :=
      (contDiff_spatialDeriv_smooth (contDiff_spatialDeriv_smooth hf j) k).continuous
    exact ((hf.continuous.pow 2).add (continuous_finsetSum _ fun j _ => (h1 j).pow 2)).add
      (continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun k _ => (h2 j k).pow 2)
  have hQnn (y : Vec3) : 0 ≤ Q y := by positivity
  have hball : MeasurableSet (vec3Ball x₀ R) := (isOpen_vec3Ball x₀ R).measurableSet
  have hQint : IntegrableOn Q (vec3Ball x₀ R) volume := by
    apply (hQcont.continuousOn.integrableOn_compact (isCompact_closedBall x₀ R)).mono_set
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact ((norm_le_vec3EuclideanNorm (y - x₀)).trans (le_of_lt hy))
  let B : Vec3 → ℝ := fun y => K * (vec3Ball x₀ R).indicator Q y
  have hBint : Integrable B volume := (hQint.integrable_indicator hball).const_mul K
  have hBeq : ∫ y, B y = K * ∫ y in vec3Ball x₀ R, Q y := by
    simp only [B]
    rw [integral_const_mul, integral_indicator hball]
  set I : ℝ := ∫ y in vec3Ball x₀ R, Q y with hI
  have hI0 : 0 ≤ I := setIntegral_nonneg hball fun y _ => hQnn y
  -- pointwise bounds
  have hgpt (y : Vec3) : ‖g y‖ ^ 2 ≤ B y := by
    by_cases hy : y ∈ vec3Ball x₀ R
    · simp only [B, Set.indicator_of_mem hy, Real.norm_eq_abs, sq_abs]
      have hφy : φ y ^ 2 ≤ 1 := by
        have h0 := hφ₀nn (y - x₀)
        have h1 := hφ₀le (y - x₀)
        nlinarith only [h0, h1]
      have hfy : f y ^ 2 ≤ Q y := by
        have h1 : 0 ≤ ∑ j : Fin 3, spatialDeriv f j y ^ 2 := by positivity
        have h2 : 0 ≤ ∑ j : Fin 3, ∑ k : Fin 3,
            spatialDeriv (spatialDeriv f j) k y ^ 2 := by positivity
        simp only [Q]
        linarith only [h1, h2]
      calc
        g y ^ 2 = φ y ^ 2 * f y ^ 2 := by simp only [g]; ring
        _ ≤ 1 * f y ^ 2 := mul_le_mul_of_nonneg_right hφy (sq_nonneg _)
        _ ≤ K * Q y := by nlinarith only [hfy, hK1, hQnn y]
    · simp only [B, Set.indicator_of_notMem hy, mul_zero, g, (hout y hy).1, zero_mul, norm_zero]
      norm_num
  -- second derivatives of the cutoff product
  have hg2 (i k : Fin 3) (y : Vec3) :
      spatialDeriv (spatialDeriv g i) k y =
        spatialDeriv (spatialDeriv φ i) k y * f y + spatialDeriv φ i y * spatialDeriv f k y +
          spatialDeriv φ k y * spatialDeriv f i y +
            φ y * spatialDeriv (spatialDeriv f i) k y :=
    spatialSecondDeriv_mul_smooth hφ hf k i y
  have hg2pt (i k : Fin 3) (y : Vec3) :
      spatialDeriv (spatialDeriv g i) k y ^ 2 ≤ (K / 3) * (vec3Ball x₀ R).indicator Q y := by
    rw [hg2 i k y]
    by_cases hy : y ∈ vec3Ball x₀ R
    · rw [Set.indicator_of_mem hy]
      have ha : |spatialDeriv (spatialDeriv φ i) k y| ≤ M₁ := by
        rw [hφd2 i k y, hM₁]
        linarith only [hL2 (y - x₀) i k]
      have hb : |spatialDeriv φ i y| ≤ M₁ := by
        rw [hφd1 i y, hM₁]
        linarith only [hL1 (y - x₀) i]
      have hc : |spatialDeriv φ k y| ≤ M₁ := by
        rw [hφd1 k y, hM₁]
        linarith only [hL1 (y - x₀) k]
      have hd : |φ y| ≤ M₁ := by
        change |φ₀ (y - x₀)| ≤ M₁
        rw [abs_of_nonneg (hφ₀nn (y - x₀)), hM₁]
        linarith only [hφ₀le (y - x₀), hL0]
      have h4 := vorticitySobolevSmooth_four_sq (p := f y) (q := spatialDeriv f k y)
        (s := spatialDeriv f i y) (t := spatialDeriv (spatialDeriv f i) k y) ha hb hc hd
      have hk1 : spatialDeriv f k y ^ 2 ≤ ∑ j : Fin 3, spatialDeriv f j y ^ 2 :=
        Finset.single_le_sum (f := fun j => spatialDeriv f j y ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
      have hi1 : spatialDeriv f i y ^ 2 ≤ ∑ j : Fin 3, spatialDeriv f j y ^ 2 :=
        Finset.single_le_sum (f := fun j => spatialDeriv f j y ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
      have hik1 : spatialDeriv (spatialDeriv f i) k y ^ 2 ≤
          ∑ k' : Fin 3, spatialDeriv (spatialDeriv f i) k' y ^ 2 :=
        Finset.single_le_sum (f := fun k' => spatialDeriv (spatialDeriv f i) k' y ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
      have hik2 : ∑ k' : Fin 3, spatialDeriv (spatialDeriv f i) k' y ^ 2 ≤
          ∑ j : Fin 3, ∑ k' : Fin 3, spatialDeriv (spatialDeriv f j) k' y ^ 2 :=
        Finset.single_le_sum (f := fun j => ∑ k' : Fin 3, spatialDeriv (spatialDeriv f j) k' y ^ 2)
          (fun _ _ => by positivity) (Finset.mem_univ i)
      have hS1 : 0 ≤ ∑ j : Fin 3, spatialDeriv f j y ^ 2 := by positivity
      have hsum : f y ^ 2 + spatialDeriv f k y ^ 2 + spatialDeriv f i y ^ 2 +
          spatialDeriv (spatialDeriv f i) k y ^ 2 ≤ 2 * Q y := by
        have hQy : Q y = f y ^ 2 + ∑ j : Fin 3, spatialDeriv f j y ^ 2 +
            ∑ j : Fin 3, ∑ k : Fin 3, spatialDeriv (spatialDeriv f j) k y ^ 2 := rfl
        linarith only [hk1, hi1, hik1, hik2, hS1, sq_nonneg (f y), hQy,
          sq_nonneg (spatialDeriv (spatialDeriv f i) k y)]
      have hM2 : 0 ≤ 4 * M₁ ^ 2 := by positivity
      calc
        _ ≤ 4 * M₁ ^ 2 * (f y ^ 2 + spatialDeriv f k y ^ 2 + spatialDeriv f i y ^ 2 +
            spatialDeriv (spatialDeriv f i) k y ^ 2) := h4
        _ ≤ 4 * M₁ ^ 2 * (2 * Q y) := mul_le_mul_of_nonneg_left hsum hM2
        _ = K / 3 * Q y := by rw [hK]; ring
    · obtain ⟨h0, h1, h2⟩ := hout y hy
      rw [Set.indicator_of_notMem hy, h0, h1 i, h1 k, h2 i k]
      norm_num
  -- the first derivatives of the cutoff product as whole-space `H¹` functions
  let H : Fin 3 → H1Function (Set.univ : Set Vec3) := fun i =>
    { toFun := spatialDeriv g i
      grad := fun y k => spatialDeriv (spatialDeriv g i) k y
      memL2 := by
        have hc := (contDiff_spatialDeriv_smooth hg i).continuous.memLp_of_hasCompactSupport
          (μ := volume) (p := (2 : ℝ≥0∞)) (hgc.fderiv_apply (𝕜 := ℝ) (basisVec i))
        exact hc.restrict _
      gradMemL2 := by
        intro k
        have hc := (contDiff_spatialDeriv_smooth (contDiff_spatialDeriv_smooth hg i)
          k).continuous.memLp_of_hasCompactSupport (μ := volume) (p := (2 : ℝ≥0∞))
          ((hgc.fderiv_apply (𝕜 := ℝ) (basisVec i)).fderiv_apply (𝕜 := ℝ) (basisVec k))
        exact hc.restrict _
      hasWeakGradient :=
        HasWeakGradientOn.of_contDiff ((contDiff_spatialDeriv_smooth hg i).of_le (by simp)) }
  have hgradmeas (i : Fin 3) : AEStronglyMeasurable (H i).grad volume := by
    have hcont : Continuous (H i).grad := by
      apply continuous_pi
      intro k
      exact (contDiff_spatialDeriv_smooth (contDiff_spatialDeriv_smooth hg i) k).continuous
    exact hcont.aestronglyMeasurable
  have hgradpt (i : Fin 3) (y : Vec3) : ‖(H i).grad y‖ ^ 2 ≤ B y := by
    have hn := norm_le_vec3EuclideanNorm ((H i).grad y)
    have hsq : ‖(H i).grad y‖ ^ 2 ≤
        ∑ k : Fin 3, spatialDeriv (spatialDeriv g i) k y ^ 2 := by
      have h1 : ‖(H i).grad y‖ ^ 2 ≤ vec3EuclideanNorm ((H i).grad y) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hn 2
      have h2 : vec3EuclideanNorm ((H i).grad y) ^ 2 =
          ∑ k : Fin 3, spatialDeriv (spatialDeriv g i) k y ^ 2 := by
        rw [vec3EuclideanNorm, Real.sq_sqrt (by positivity)]
      linarith only [h1, h2]
    have hsum : ∑ k : Fin 3, spatialDeriv (spatialDeriv g i) k y ^ 2 ≤
        ∑ _k : Fin 3, (K / 3) * (vec3Ball x₀ R).indicator Q y :=
      Finset.sum_le_sum fun k _ => hg2pt i k y
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    simp only [B]
    linarith only [hsq, hsum]
  -- the global estimates
  have hgL2 : lpNorm g 2 volume ≤ Real.sqrt (∫ y, B y) :=
    vorticitySobolevSmooth_lpNorm_le hg.continuous.aestronglyMeasurable hBint hgpt
  have hgradL2 (i : Fin 3) : eLpNorm (H i).grad 2 volume ≤
      ENNReal.ofReal (Real.sqrt (∫ y, B y)) :=
    vorticitySobolevSmooth_eLpNorm_le (hgradmeas i) hBint (hgradpt i)
  have hL6 (i : Fin 3) : lpNorm (fun y => (fderiv ℝ g y) (basisVec i)) 6 volume ≤
      C₆.toReal * Real.sqrt (∫ y, B y) := by
    have hs := hsob (H i)
    simp only [lpNormOn, weakGradientLpNormOn, Measure.restrict_univ] at hs
    have hle : eLpNorm (spatialDeriv g i) 6 volume ≤
        C₆ * ENNReal.ofReal (Real.sqrt (∫ y, B y)) :=
      hs.trans (mul_le_mul_of_nonneg_left (hgradL2 i) bot_le)
    have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top hC₆ ENNReal.ofReal_ne_top) hle
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at hreal
    exact hreal
  have hmem6 (i : Fin 3) : MemLp (fun y => (fderiv ℝ g y) (basisVec i))
      (ENNReal.ofReal (6 : ℝ)) volume :=
    (contDiff_spatialDeriv_smooth hg i).continuous.memLp_of_hasCompactSupport
      (hgc.fderiv_apply (𝕜 := ℝ) (basisVec i))
  have hmem2 : MemLp g 2 volume := hg.continuous.memLp_of_hasCompactSupport hgc
  have hmain := hlinf hg hmem2 hmem6 x
  -- the cutoff equals one at the point
  have hgx : g x = f x := by
    simp only [g, φ, hφ₀one (x - x₀) hx, one_mul]
  rw [hgx] at hmain
  have hsumL6 : ∑ i : Fin 3, lpNorm (fun y => (fderiv ℝ g y) (basisVec i)) 6 volume ≤
      3 * (C₆.toReal * Real.sqrt (∫ y, B y)) := by
    calc
      _ ≤ ∑ _i : Fin 3, C₆.toReal * Real.sqrt (∫ y, B y) := Finset.sum_le_sum fun i _ => hL6 i
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; norm_num
  have hsqrtB : Real.sqrt (∫ y, B y) = Real.sqrt K * Real.sqrt I := by
    rw [hBeq, Real.sqrt_mul hK0]
  have hbound : |f x| ≤ A * Real.sqrt I := by
    calc
      |f x| ≤ C₀ * (lpNorm g 2 volume + ∑ i : Fin 3,
          lpNorm (fun y => (fderiv ℝ g y) (basisVec i)) 6 volume) := hmain
      _ ≤ C₀ * (Real.sqrt (∫ y, B y) + 3 * (C₆.toReal * Real.sqrt (∫ y, B y))) := by
        gcongr
      _ = A * Real.sqrt I := by rw [hsqrtB, hA]; ring
  have habs : 0 ≤ |f x| := abs_nonneg _
  have hsq := pow_le_pow_left₀ habs hbound 2
  calc
    |f x| ^ 2 ≤ (A * Real.sqrt I) ^ 2 := hsq
    _ = A ^ 2 * I := by rw [mul_pow, Real.sq_sqrt hI0]

end CKN
