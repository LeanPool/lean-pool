/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityCutoff
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.SmoothIBP
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Local div–curl estimate for smooth fields

For a smooth vector field on a ball, the square integral of its gradient on a smaller ball is
controlled by the square integrals of its divergence, of its antisymmetric derivative and of the
field itself on the larger ball (the smooth case of `lem:local-div-curl` of the
Escauriaza–Seregin–Šverák manuscript). For a compactly
supported smooth field the gradient identity
`∫ |∇W|² = ∫ (div W)² + ½ ∫ Σ (∂ₐW_b - ∂_bWₐ)²` follows from two integrations by parts; a
cutoff localizes it.
-/

public section

open MeasureTheory Set Filter
open CKN CKN.Foundation.Parabolic
open scoped Topology

noncomputable section

namespace CKN

/-- Mixed coordinate derivatives of a smooth function on space commute. -/
theorem vorticityDivCurlSmooth_deriv_comm {f : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a b : Fin 3) (x : Vec3) :
    spatialDeriv (spatialDeriv f b) a x = spatialDeriv (spatialDeriv f a) b x := by
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.contDiffAt.fderiv_right (m := (1 : ℕ∞)) (by simp)).differentiableAt (by simp)
  have key : ∀ c d : Fin 3, spatialDeriv (spatialDeriv f c) d x =
      fderiv ℝ (fderiv ℝ f) x (basisVec d) (basisVec c) := by
    intro c d
    unfold spatialDeriv
    rw [fderiv_clm_apply hfd (differentiableAt_const (c := basisVec c))]
    simp
  rw [key, key]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simp)) _ _

/-- A continuous function vanishing off a compact set is integrable. -/
theorem vorticityDivCurlSmooth_integrable {K : Set Vec3} (hK : IsCompact K)
    {F : Vec3 → ℝ} (hF : Continuous F) (h0 : ∀ x, x ∉ K → F x = 0) :
    Integrable F (volume : Measure Vec3) :=
  hF.integrable_of_hasCompactSupport (HasCompactSupport.intro hK h0)

/-- Symmetry of the cross terms after two integrations by parts. -/
theorem vorticityDivCurlSmooth_cross {W : Fin 3 → Vec3 → ℝ}
    (hW : ∀ b, ContDiff ℝ (⊤ : ℕ∞) (W b)) (hWc : ∀ b, HasCompactSupport (W b))
    (a b : Fin 3) :
    ∫ x, spatialDeriv (W b) a x * spatialDeriv (W a) b x =
      ∫ x, spatialDeriv (W a) a x * spatialDeriv (W b) b x := by
  have h1 := integral_mul_spatialDeriv_eq_neg_integral_spatialDeriv_mul
    (contDiff_spatialDeriv_smooth (hW a) b) (hW b) (hWc b) a
  have h2 := integral_mul_spatialDeriv_eq_neg_integral_spatialDeriv_mul
    (contDiff_spatialDeriv_smooth (hW a) a) (hW b) (hWc b) b
  have hcomm : (fun x => spatialDeriv (spatialDeriv (W a) b) a x * W b x) =
      fun x => spatialDeriv (spatialDeriv (W a) a) b x * W b x := by
    funext x
    rw [vorticityDivCurlSmooth_deriv_comm (hW a) a b x]
  calc
    ∫ x, spatialDeriv (W b) a x * spatialDeriv (W a) b x
        = ∫ x, spatialDeriv (W a) b x * spatialDeriv (W b) a x := by
          congr 1
          funext x
          ring
    _ = -∫ x, spatialDeriv (spatialDeriv (W a) b) a x * W b x := h1
    _ = -∫ x, spatialDeriv (spatialDeriv (W a) a) b x * W b x := by rw [hcomm]
    _ = ∫ x, spatialDeriv (W a) a x * spatialDeriv (W b) b x := h2.symm

/-- The gradient identity for compactly supported smooth fields, in inequality form. -/
theorem vorticityDivCurlSmooth_integral_le {W : Fin 3 → Vec3 → ℝ}
    (hW : ∀ b, ContDiff ℝ (⊤ : ℕ∞) (W b)) (hWc : ∀ b, HasCompactSupport (W b)) :
    ∫ x, ∑ a : Fin 3, ∑ b : Fin 3, spatialDeriv (W b) a x ^ 2 ≤
      ∫ x, ((∑ a : Fin 3, spatialDeriv (W a) a x) ^ 2 +
        ∑ a : Fin 3, ∑ b : Fin 3,
          (spatialDeriv (W b) a x - spatialDeriv (W a) b x) ^ 2) := by
  let K : Set Vec3 := ⋃ b, tsupport (W b)
  have hK : IsCompact K := isCompact_iUnion fun b => hWc b
  have hzero : ∀ x, x ∉ K → ∀ a b, spatialDeriv (W b) a x = 0 := by
    intro x hx a b
    have hxb : x ∉ tsupport (W b) := fun h => hx (mem_iUnion.2 ⟨b, h⟩)
    simp [spatialDeriv, fderiv_of_notMem_tsupport ℝ hxb]
  have hcont : ∀ a b, Continuous (spatialDeriv (W b) a) := fun a b =>
    (contDiff_spatialDeriv_smooth (hW b) a).continuous
  let d : Fin 3 → Fin 3 → Vec3 → ℝ := fun a b => spatialDeriv (W b) a
  have hint : ∀ F : Vec3 → ℝ, Continuous F → (∀ x, (∀ a b, d a b x = 0) → F x = 0) →
      Integrable F (volume : Measure Vec3) := by
    intro F hF h0
    exact vorticityDivCurlSmooth_integrable hK hF fun x hx => h0 x (hzero x hx)
  have hQ : ∀ a b, Integrable (fun x => d a b x * d b a x) (volume : Measure Vec3) :=
    fun a b => hint _ ((hcont a b).mul (hcont b a)) fun x h => by simp [h]
  have hD : ∀ a b, Integrable (fun x => d a a x * d b b x) (volume : Measure Vec3) :=
    fun a b => hint _ ((hcont a a).mul (hcont b b)) fun x h => by simp [h]
  let A : Vec3 → ℝ := fun x => ∑ a : Fin 3, ∑ b : Fin 3, (d a b x - d b a x) ^ 2
  have hAcont : Continuous A :=
    continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
      ((hcont a b).sub (hcont b a)).pow 2
  have hA : Integrable A (volume : Measure Vec3) :=
    hint _ hAcont fun x h => by simp [A, h]
  let Dv : Vec3 → ℝ := fun x => (∑ a : Fin 3, d a a x) ^ 2
  have hDvcont : Continuous Dv :=
    (continuous_finsetSum _ fun a _ => hcont a a).pow 2
  have hDv : Integrable Dv (volume : Measure Vec3) :=
    hint _ hDvcont fun x h => by simp [Dv, h]
  have hQsum : Integrable (fun x => ∑ a : Fin 3, ∑ b : Fin 3, d a b x * d b a x)
      (volume : Measure Vec3) :=
    integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hQ a b
  have hpoint : (fun x => ∑ a : Fin 3, ∑ b : Fin 3, spatialDeriv (W b) a x ^ 2) =
      fun x => (1 / 2 : ℝ) * A x + ∑ a : Fin 3, ∑ b : Fin 3, d a b x * d b a x := by
    funext x
    simp only [A, d, Fin.sum_univ_three]
    ring
  have hDvEq : Dv = fun x => ∑ a : Fin 3, ∑ b : Fin 3, d a a x * d b b x := by
    funext x
    simp only [Dv, Fin.sum_univ_three]
    ring
  have hQint : ∫ x, ∑ a : Fin 3, ∑ b : Fin 3, d a b x * d b a x = ∫ x, Dv x := by
    rw [hDvEq, integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hQ a b,
      integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hD a b]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun b _ => hQ a b, integral_finsetSum _ fun b _ => hD a b]
    refine Finset.sum_congr rfl fun b _ => ?_
    exact vorticityDivCurlSmooth_cross hW hWc a b
  have hAnn : 0 ≤ ∫ x, A x := integral_nonneg fun x => by positivity
  have hRHS : ∫ x, ((∑ a : Fin 3, spatialDeriv (W a) a x) ^ 2 +
      ∑ a : Fin 3, ∑ b : Fin 3,
        (spatialDeriv (W b) a x - spatialDeriv (W a) b x) ^ 2) = (∫ x, Dv x) + ∫ x, A x := by
    rw [← integral_add hDv hA]
  rw [hpoint, integral_add (hA.const_mul _) hQsum, integral_const_mul, hQint, hRHS]
  linarith only [hAnn]

/-- Two-term squares. -/
theorem vorticityDivCurlSmooth_sq_add_le (x y : ℝ) :
    (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by
  nlinarith only [sq_nonneg (x - y)]

/-- Three-term sums of squares. -/
theorem vorticityDivCurlSmooth_sum_sq_le (f : Fin 3 → ℝ) :
    (∑ a : Fin 3, f a) ^ 2 ≤ 3 * ∑ a : Fin 3, f a ^ 2 := by
  simp only [Fin.sum_univ_three]
  nlinarith only [sq_nonneg (f 0 - f 1), sq_nonneg (f 1 - f 2), sq_nonneg (f 0 - f 2)]

/-- A bounded factor. -/
theorem vorticityDivCurlSmooth_mul_sq_le {d v L : ℝ} (hd : |d| ≤ L) :
    (d * v) ^ 2 ≤ L ^ 2 * v ^ 2 := by
  have hd2 : d ^ 2 ≤ L ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg d) hd 2
    rwa [sq_abs] at this
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right hd2 (sq_nonneg v)

/-- The pointwise algebra behind the cutoff step. -/
theorem vorticityDivCurlSmooth_pointwise {p L : ℝ} (d v : Fin 3 → ℝ)
    (g : Fin 3 → Fin 3 → ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hd : ∀ a, |d a| ≤ L) :
    (∑ a : Fin 3, (d a * v a + p * g a a)) ^ 2 +
        ∑ a : Fin 3, ∑ b : Fin 3,
          ((d a * v b + p * g a b) - (d b * v a + p * g b a)) ^ 2 ≤
      (2 + 30 * L ^ 2) * ((∑ a : Fin 3, g a a) ^ 2 +
        ∑ a : Fin 3, ∑ b : Fin 3, (g a b - g b a) ^ 2 + ∑ b : Fin 3, v b ^ 2) := by
  have hp2 : p ^ 2 ≤ 1 := by nlinarith only [hp0, hp1]
  have hL2 : 0 ≤ L ^ 2 := sq_nonneg L
  set S : ℝ := ∑ b : Fin 3, v b ^ 2 with hS
  set G : ℝ := (∑ a : Fin 3, g a a) ^ 2 with hG
  set T : ℝ := ∑ a : Fin 3, ∑ b : Fin 3, (g a b - g b a) ^ 2 with hT
  have hSnn : 0 ≤ S := by positivity
  have hGnn : 0 ≤ G := by positivity
  have hTnn : 0 ≤ T := by positivity
  -- divergence part
  have hdiv : (∑ a : Fin 3, (d a * v a + p * g a a)) ^ 2 ≤ 6 * L ^ 2 * S + 2 * G := by
    have hsplit : ∑ a : Fin 3, (d a * v a + p * g a a) =
        ∑ a : Fin 3, d a * v a + p * ∑ a : Fin 3, g a a := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    rw [hsplit]
    have h1 := vorticityDivCurlSmooth_sq_add_le (∑ a : Fin 3, d a * v a)
      (p * ∑ a : Fin 3, g a a)
    have h2 := vorticityDivCurlSmooth_sum_sq_le (fun a => d a * v a)
    have h3 : ∑ a : Fin 3, (d a * v a) ^ 2 ≤ L ^ 2 * S := by
      rw [hS, Finset.mul_sum]
      exact Finset.sum_le_sum fun a _ => vorticityDivCurlSmooth_mul_sq_le (hd a)
    have h4 : (p * ∑ a : Fin 3, g a a) ^ 2 ≤ G := by
      rw [mul_pow, hG]
      nlinarith only [hp2, hGnn]
    linarith only [h1, h2, h3, h4]
  -- antisymmetric part
  have hterm : ∀ a b : Fin 3,
      ((d a * v b + p * g a b) - (d b * v a + p * g b a)) ^ 2 ≤
        2 * (g a b - g b a) ^ 2 + 4 * L ^ 2 * (v b ^ 2 + v a ^ 2) := by
    intro a b
    have hre : (d a * v b + p * g a b) - (d b * v a + p * g b a) =
        p * (g a b - g b a) + (d a * v b - d b * v a) := by ring
    rw [hre]
    have h1 := vorticityDivCurlSmooth_sq_add_le (p * (g a b - g b a)) (d a * v b - d b * v a)
    have h2 : (p * (g a b - g b a)) ^ 2 ≤ (g a b - g b a) ^ 2 := by
      rw [mul_pow]
      nlinarith only [hp2, sq_nonneg (g a b - g b a)]
    have h3 : (d a * v b - d b * v a) ^ 2 ≤ 2 * (d a * v b) ^ 2 + 2 * (d b * v a) ^ 2 := by
      nlinarith only [sq_nonneg (d a * v b + d b * v a)]
    have h4 := vorticityDivCurlSmooth_mul_sq_le (v := v b) (hd a)
    have h5 := vorticityDivCurlSmooth_mul_sq_le (v := v a) (hd b)
    nlinarith only [h1, h2, h3, h4, h5]
  have hanti : ∑ a : Fin 3, ∑ b : Fin 3,
      ((d a * v b + p * g a b) - (d b * v a + p * g b a)) ^ 2 ≤ 2 * T + 24 * L ^ 2 * S := by
    have hsum := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) =>
      Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) => hterm a b
    refine hsum.trans (le_of_eq ?_)
    simp only [hT, hS, Fin.sum_univ_three]
    ring
  have hfinal : 6 * L ^ 2 * S + 2 * G + (2 * T + 24 * L ^ 2 * S) ≤
      (2 + 30 * L ^ 2) * (G + T + S) := by
    nlinarith only [hL2, hSnn, hGnn, hTnn]
  linarith only [hdiv, hanti, hfinal]

/-- Local div–curl estimate for smooth fields (smooth case of `lem:local-div-curl` (ESS)). -/
theorem vorticityDivCurlSmooth_local {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x₀ : Vec3) (V : Fin 3 → Vec3 → ℝ),
      (∀ b, ContDiff ℝ (⊤ : ℕ∞) (V b)) →
      ∫ x in vec3Ball x₀ r, ∑ a : Fin 3, ∑ b : Fin 3, spatialDeriv (V b) a x ^ 2 ≤
        C * ∫ x in vec3Ball x₀ R,
          ((∑ a : Fin 3, spatialDeriv (V a) a x) ^ 2 +
            ∑ a : Fin 3, ∑ b : Fin 3, (spatialDeriv (V b) a x - spatialDeriv (V a) b x) ^ 2 +
            ∑ b : Fin 3, V b x ^ 2) := by
  obtain ⟨φ₀, hφ₀, hφ₀c, hφ₀supp, hφ₀one, hφ₀nn, hφ₀le⟩ := vorticitySpatialCutoff_exists hr hrR
  obtain ⟨L, _hL, hL1, _hL2⟩ := vorticitySmooth_derivative_bounds hφ₀ hφ₀c
  refine ⟨2 + 30 * L ^ 2, by positivity, ?_⟩
  intro x₀ V hV
  let φ : Vec3 → ℝ := fun x => φ₀ (x - x₀)
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hφ₀.comp (contDiff_id.sub contDiff_const)
  have hφc : HasCompactSupport φ := hφ₀c.comp_homeomorph (Homeomorph.subRight x₀)
  have hφd : ∀ x a, spatialDeriv φ a x = spatialDeriv φ₀ a (x - x₀) := fun x a =>
    vorticitySpatialDeriv_translate φ₀ x₀ x a
  let W : Fin 3 → Vec3 → ℝ := fun b x => φ x * V b x
  have hW : ∀ b, ContDiff ℝ (⊤ : ℕ∞) (W b) := fun b => hφ.mul (hV b)
  have hWc : ∀ b, HasCompactSupport (W b) := fun b => hφc.mul_right
  have hWd : ∀ x a b, spatialDeriv (W b) a x =
      spatialDeriv φ a x * V b x + φ x * spatialDeriv (V b) a x := by
    intro x a b
    exact spatialDeriv_mul (hφ.differentiable (by simp) x) ((hV b).differentiable (by simp) x) a
  have hVderivCont : ∀ a b, Continuous (spatialDeriv (V b) a) := fun a b =>
    (contDiff_spatialDeriv_smooth (hV b) a).continuous
  have hWderivCont : ∀ a b, Continuous (spatialDeriv (W b) a) := fun a b =>
    (contDiff_spatialDeriv_smooth (hW b) a).continuous
  have hBr : MeasurableSet (vec3Ball x₀ r) := (isOpen_vec3Ball x₀ r).measurableSet
  have hBR : MeasurableSet (vec3Ball x₀ R) := (isOpen_vec3Ball x₀ R).measurableSet
  -- inner ball: the cutoff is identically one
  have hinner : ∀ x ∈ vec3Ball x₀ r, ∀ a b, spatialDeriv (W b) a x = spatialDeriv (V b) a x := by
    intro x hx a b
    have hxr : vec3EuclideanNorm (x - x₀) < r := hx
    have hone : φ x = 1 := hφ₀one _ hxr.le
    have hev : φ₀ =ᶠ[𝓝 (x - x₀)] fun _ => (1 : ℝ) := by
      have hopen : IsOpen {z : Vec3 | vec3EuclideanNorm z < r} :=
        isOpen_lt continuous_vec3EuclideanNorm continuous_const
      filter_upwards [hopen.mem_nhds hxr] with z hz
      exact hφ₀one z (le_of_lt hz)
    have hdz : spatialDeriv φ a x = 0 := by
      rw [hφd]
      simp [spatialDeriv, hev.fderiv_eq]
    rw [hWd, hdz, hone]
    ring
  -- global bound
  let PW : Vec3 → ℝ := fun x => ∑ a : Fin 3, ∑ b : Fin 3, spatialDeriv (W b) a x ^ 2
  let K : Set Vec3 := ⋃ b, tsupport (W b)
  have hK : IsCompact K := isCompact_iUnion fun b => hWc b
  have hPWint : Integrable PW (volume : Measure Vec3) := by
    apply vorticityDivCurlSmooth_integrable hK
    · exact continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
        (hWderivCont a b).pow 2
    · intro x hx
      have hz : ∀ a b, spatialDeriv (W b) a x = 0 := by
        intro a b
        have hxb : x ∉ tsupport (W b) := fun h => hx (mem_iUnion.2 ⟨b, h⟩)
        simp [spatialDeriv, fderiv_of_notMem_tsupport ℝ hxb]
      simp [PW, hz]
  have hstep1 : ∫ x in vec3Ball x₀ r, ∑ a : Fin 3, ∑ b : Fin 3, spatialDeriv (V b) a x ^ 2 =
      ∫ x in vec3Ball x₀ r, PW x := by
    refine setIntegral_congr_fun hBr fun x hx => ?_
    simp only [PW, hinner x hx]
  have hstep2 : ∫ x in vec3Ball x₀ r, PW x ≤ ∫ x, PW x :=
    setIntegral_le_integral hPWint (Eventually.of_forall fun x => by positivity)
  have hstep3 := vorticityDivCurlSmooth_integral_le hW hWc
  let IR : Vec3 → ℝ := fun x => (∑ a : Fin 3, spatialDeriv (V a) a x) ^ 2 +
      ∑ a : Fin 3, ∑ b : Fin 3, (spatialDeriv (V b) a x - spatialDeriv (V a) b x) ^ 2 +
      ∑ b : Fin 3, V b x ^ 2
  have hIRcont : Continuous IR := by
    refine ((continuous_finsetSum _ fun a _ => hVderivCont a a).pow 2).add
      (continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
        ((hVderivCont a b).sub (hVderivCont b a)).pow 2) |>.add ?_
    exact continuous_finsetSum _ fun b _ => ((hV b).continuous).pow 2
  have hBRsub : vec3Ball x₀ R ⊆ Metric.closedBall x₀ R := by
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact ((norm_le_vec3EuclideanNorm (y - x₀)).trans (le_of_lt hy))
  have hIRint : IntegrableOn (fun x => (2 + 30 * L ^ 2) * IR x) (vec3Ball x₀ R)
      (volume : Measure Vec3) :=
    ((hIRcont.const_mul _).continuousOn.integrableOn_compact
      (isCompact_closedBall x₀ R)).mono_set hBRsub
  have hpoint : ∀ x, ((∑ a : Fin 3, spatialDeriv (W a) a x) ^ 2 +
      ∑ a : Fin 3, ∑ b : Fin 3, (spatialDeriv (W b) a x - spatialDeriv (W a) b x) ^ 2) ≤
      (vec3Ball x₀ R).indicator (fun x => (2 + 30 * L ^ 2) * IR x) x := by
    intro x
    by_cases hx : x ∈ vec3Ball x₀ R
    · rw [Set.indicator_of_mem hx]
      simp only [hWd]
      exact vorticityDivCurlSmooth_pointwise (fun a => spatialDeriv φ a x) (fun b => V b x)
        (fun a b => spatialDeriv (V b) a x) (hφ₀nn _) (hφ₀le _)
        (fun a => by rw [hφd]; exact hL1 _ a)
    · rw [Set.indicator_of_notMem hx]
      have hy : x - x₀ ∉ tsupport φ₀ := by
        intro h
        apply hx
        have h' := hφ₀supp h
        simpa [vec3Ball] using h'
      have hφ0 : φ x = 0 := show φ₀ (x - x₀) = 0 from image_eq_zero_of_notMem_tsupport hy
      have hdφ : ∀ a, spatialDeriv φ a x = 0 := by
        intro a
        rw [hφd]
        simp [spatialDeriv, fderiv_of_notMem_tsupport ℝ hy]
      simp [hWd, hdφ, hφ0]
  have hstep4 : ∫ x, ((∑ a : Fin 3, spatialDeriv (W a) a x) ^ 2 +
      ∑ a : Fin 3, ∑ b : Fin 3, (spatialDeriv (W b) a x - spatialDeriv (W a) b x) ^ 2) ≤
      ∫ x, (vec3Ball x₀ R).indicator (fun x => (2 + 30 * L ^ 2) * IR x) x :=
    integral_mono_of_nonneg (Eventually.of_forall fun x => by positivity)
      ((integrable_indicator_iff hBR).2 hIRint) (Eventually.of_forall hpoint)
  rw [integral_indicator hBR, integral_const_mul] at hstep4
  rw [hstep1]
  exact hstep2.trans (hstep3.trans hstep4)

end CKN
