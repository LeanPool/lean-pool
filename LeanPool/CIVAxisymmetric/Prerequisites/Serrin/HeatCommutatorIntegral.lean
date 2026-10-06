/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.HeatKernelIntegrals
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import LeanPool.CIVAxisymmetric.Identities.PartialCalculus

/-!
# The integral of the derivative of the cutoff-commutator kernel

Before the time `s`, the spatial derivative of the commutator kernel
`K₀ = Γ (∂ₜχ + Δχ) + 2 ∇Γ · ∇χ` is bounded by `C ρ⁻⁶` and supported in the window, so its integral
is of size `ρ⁻¹`. This is the cutoff term of the pointwise heat bound in the interior estimates
of the proof of `lem:aniso:annulus`.
-/

public section

open MeasureTheory Set
open CKN.Foundation.Parabolic CKN CKN.Foundation.Heat

noncomputable section
namespace CIV



/-- A directional derivative of a smooth function costs one order of its iterated derivative. -/
theorem norm_iteratedFDeriv_fderiv_apply_le {g : Vec3 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (v : Vec3) (n : ℕ) (y : Vec3) :
    ‖iteratedFDeriv ℝ n (fun y' => fderiv ℝ g y' v) y‖ ≤
      ‖v‖ * ‖iteratedFDeriv ℝ (n + 1) g y‖ := by
  set L : (Vec3 →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ v with hL
  have hfun : (fun y' => fderiv ℝ g y' v) = L ∘ fderiv ℝ g := rfl
  have hdg : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ g) :=
    hg.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)
  rw [hfun]
  refine (L.norm_iteratedFDeriv_comp_left hdg.contDiffAt (by exact_mod_cast le_top)).trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  gcongr
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) (fun T => ?_)
  rw [mul_comm]
  exact T.le_opNorm v

/-- Iterated directional derivatives along unit basis vectors are bounded by the iterated
derivative of the same order. -/
theorem abs_dir_deriv_le {B : Vec3 → ℝ} (hB : ContDiff ℝ (⊤ : ℕ∞) B) (y : Vec3) (i l m : Fin 3) :
    |fderiv ℝ B y (basisVec i)| ≤ ‖iteratedFDeriv ℝ 1 B y‖ ∧
    |fderiv ℝ (fun y' => fderiv ℝ B y' (basisVec i)) y (basisVec l)| ≤
      ‖iteratedFDeriv ℝ 2 B y‖ ∧
    |fderiv ℝ (fun y'' => fderiv ℝ (fun y' => fderiv ℝ B y' (basisVec i)) y'' (basisVec l)) y
        (basisVec m)| ≤ ‖iteratedFDeriv ℝ 3 B y‖ := by
  have hsm : ∀ {g : Vec3 → ℝ}, ContDiff ℝ (⊤ : ℕ∞) g → ∀ v : Vec3,
      ContDiff ℝ (⊤ : ℕ∞) (fun y' => fderiv ℝ g y' v) := fun hg v =>
    (hg.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const
  have hb : ∀ j : Fin 3, ‖(basisVec j : Vec3)‖ ≤ 1 := norm_basisVec_le_one
  have h0 : ∀ {g : Vec3 → ℝ}, ContDiff ℝ (⊤ : ℕ∞) g → ∀ j : Fin 3,
      |fderiv ℝ g y (basisVec j)| ≤ ‖iteratedFDeriv ℝ 1 g y‖ := by
    intro g hg j
    have := norm_iteratedFDeriv_fderiv_apply_le hg (basisVec j) 0 y
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    exact this.trans (mul_le_of_le_one_left (norm_nonneg _) (hb j))
  have hstep : ∀ {g : Vec3 → ℝ}, ContDiff ℝ (⊤ : ℕ∞) g → ∀ (j : Fin 3) (n : ℕ),
      ‖iteratedFDeriv ℝ n (fun y' => fderiv ℝ g y' (basisVec j)) y‖ ≤
        ‖iteratedFDeriv ℝ (n + 1) g y‖ := fun hg j n =>
    (norm_iteratedFDeriv_fderiv_apply_le hg (basisVec j) n y).trans
      (mul_le_of_le_one_left (norm_nonneg _) (hb j))
  refine ⟨h0 hB i, ?_, ?_⟩
  · exact (h0 (hsm hB (basisVec i)) l).trans (hstep hB i 1)
  · refine (h0 (hsm (hsm hB (basisVec i)) (basisVec l)) m).trans ?_
    refine (hstep (hsm hB (basisVec i)) l 1).trans ?_
    exact hstep hB i 2

/-- The spatial partial of a separated product `B(y) T(τ)`. -/
theorem spatialPartial_separated {B : Vec3 → ℝ} (hB : Differentiable ℝ B) (T : ℝ → ℝ) (i : Fin 3) :
    (fun z : ParabolicPoint => spatialPartial (fun w : ParabolicPoint => B w.1 * T w.2) i z) =
      fun z => fderiv ℝ B z.1 (basisVec i) * T z.2 := by
  funext z
  unfold spatialPartial
  show fderiv ℝ (fun y : Vec3 => B y * T z.2) z.1 (basisVec i) = _
  rw [fderiv_mul_const (hB z.1)]
  simp only [smul_apply, smul_eq_mul]
  ring

/-- The time partial of a separated product `B(y) T(τ)`. -/
theorem timePartial_separated (B : Vec3 → ℝ) {T : ℝ → ℝ} (hT : Differentiable ℝ T) :
    (fun z : ParabolicPoint => timePartial (fun w : ParabolicPoint => B w.1 * T w.2) z) =
      fun z => B z.1 * deriv T z.2 := by
  funext z
  unfold timePartial
  show fderiv ℝ (fun r : ℝ => B z.1 * T r) z.2 1 = _
  rw [fderiv_const_mul (hT z.2)]
  simp only [smul_apply, smul_eq_mul]
  rfl

/-- The directional derivative vanishes on an open set where the function is constant. -/
theorem fderiv_apply_eq_zero_of_eqOn_const {g : Vec3 → ℝ} {O : Set Vec3} (hO : IsOpen O) {c : ℝ}
    (hg : ∀ y ∈ O, g y = c) (v : Vec3) : ∀ y ∈ O, fderiv ℝ g y v = 0 := by
  intro y hy
  have hev : g =ᶠ[nhds y] fun _ => c :=
    Filter.eventually_of_mem (hO.mem_nhds hy) (fun y' hy' => hg y' hy')
  rw [hev.fderiv_eq]
  simp

/-- The time profile of the backward cutoff. -/
@[expose] def serrinTimeCut (s ρ : ℝ) (r : ℝ) : ℝ := serrinTimeBump ((r - s) / ρ ^ 2)

/-- The backward cutoff is the ball cutoff times the time profile. -/
theorem serrinCutoff_eq_separated (x : Vec3) (s ρ : ℝ) :
    serrinCutoff x s ρ = fun w : ParabolicPoint => serrinBallCutoff x ρ w.1 * serrinTimeCut s ρ
      w.2 :=
  rfl

/-- The time profile is smooth. -/
theorem contDiff_serrinTimeCut (s ρ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (serrinTimeCut s ρ) := by
  unfold serrinTimeCut
  exact contDiff_serrinTimeBump.comp ((contDiff_id.sub contDiff_const).div_const _)

/-- Bounds for the time profile and its derivative, and the vanishing of the derivative after
`s - ρ²/2`. -/
theorem serrinTimeCut_bounds : ∃ C : ℝ, 0 ≤ C ∧ ∀ (s ρ : ℝ), 0 < ρ → ∀ r : ℝ,
    |serrinTimeCut s ρ r| ≤ 1 ∧ |deriv (serrinTimeCut s ρ) r| ≤ C / ρ ^ 2 ∧
      (s - ρ ^ 2 / 2 < r → deriv (serrinTimeCut s ρ) r = 0) := by
  obtain ⟨C, hC⟩ := abs_iteratedDeriv_serrinTimeBump_scaled_le
  refine ⟨max (C 1) 0, le_max_right _ _, fun s ρ hρ r => ⟨?_, ?_, ?_⟩⟩
  · unfold serrinTimeCut serrinTimeBump
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  · have h := hC 1 s ρ hρ r
    rw [iteratedDeriv_one] at h
    refine h.trans ?_
    rw [mul_one]
    exact div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)
  · intro hr
    have hev : serrinTimeCut s ρ =ᶠ[nhds r] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hr] with r' hr'
      exact ((serrinTimeBump_support (s := s) hρ r').1 (le_of_lt hr'))
    rw [hev.deriv_eq]
    simp

/-- Bounds for the ball cutoff and its first three directional derivatives, and their vanishing
on the inner half ball. -/
theorem serrinBallCutoff_dir_bounds : ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Vec3) (ρ : ℝ), 0 < ρ →
    ∀ (y : Vec3) (i l m : Fin 3),
      |serrinBallCutoff x ρ y| ≤ 1 ∧
      |fderiv ℝ (serrinBallCutoff x ρ) y (basisVec i)| ≤ C / ρ ∧
      |fderiv ℝ (fun y' => fderiv ℝ (serrinBallCutoff x ρ) y' (basisVec i)) y (basisVec l)| ≤
        C / ρ ^ 2 ∧
      |fderiv ℝ (fun y'' => fderiv ℝ (fun y' => fderiv ℝ (serrinBallCutoff x ρ) y' (basisVec i))
          y'' (basisVec l)) y (basisVec m)| ≤ C / ρ ^ 3 ∧
      (vec3EuclideanNorm (y - x) < ρ / 2 →
        fderiv ℝ (serrinBallCutoff x ρ) y (basisVec i) = 0 ∧
        fderiv ℝ (fun y' => fderiv ℝ (serrinBallCutoff x ρ) y' (basisVec i)) y (basisVec l) = 0 ∧
        fderiv ℝ (fun y'' => fderiv ℝ (fun y' => fderiv ℝ (serrinBallCutoff x ρ) y' (basisVec i))
          y'' (basisVec l)) y (basisVec m) = 0) := by
  obtain ⟨C, hC⟩ := norm_iteratedFDeriv_serrinBallCutoff_le
  refine ⟨max (C 1) (max (C 2) (max (C 3) 0)), by positivity, fun x ρ hρ y i l m => ?_⟩
  have hB : ContDiff ℝ (⊤ : ℕ∞) (serrinBallCutoff x ρ) := (serrinBallCutoff_support x hρ x).2.2
  obtain ⟨h1, h2, h3⟩ := abs_dir_deriv_le hB y i l m
  have hm1 : C 1 ≤ max (C 1) (max (C 2) (max (C 3) 0)) := le_max_left _ _
  have hm2 : C 2 ≤ max (C 1) (max (C 2) (max (C 3) 0)) :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hm3 : C 3 ≤ max (C 1) (max (C 2) (max (C 3) 0)) :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have := serrinBallCutoff_mem_Icc x ρ y
    rw [abs_of_nonneg this.1]; exact this.2
  · refine h1.trans ((hC 1 x ρ hρ y).trans ?_)
    rw [pow_one]; exact div_le_div_of_nonneg_right hm1 hρ.le
  · exact h2.trans ((hC 2 x ρ hρ y).trans (div_le_div_of_nonneg_right hm2 (by positivity)))
  · exact h3.trans ((hC 3 x ρ hρ y).trans (div_le_div_of_nonneg_right hm3 (by positivity)))
  · intro hy
    set O : Set Vec3 := {y' | vec3EuclideanNorm (y' - x) < ρ / 2} with hO
    have hOo : IsOpen O := by
      have hc : Continuous (fun y' : Vec3 => vec3EuclideanNorm (y' - x)) := by
        unfold vec3EuclideanNorm; fun_prop
      exact isOpen_lt hc continuous_const
    have hB1 : ∀ y' ∈ O, serrinBallCutoff x ρ y' = 1 := fun y' hy' =>
      (serrinBallCutoff_support x hρ y').1 (le_of_lt hy')
    have hd1 := fderiv_apply_eq_zero_of_eqOn_const hOo hB1 (basisVec i)
    have hd2 := fderiv_apply_eq_zero_of_eqOn_const hOo hd1 (basisVec l)
    have hd3 := fderiv_apply_eq_zero_of_eqOn_const hOo hd2 (basisVec m)
    exact ⟨hd1 y hy, hd2 y hy, hd3 y hy⟩

/-- The spatial partial of the translated heat kernel before the pole. -/
theorem spatialPartial_heatKernel_translate (x : Vec3) (s : ℝ) {z : ParabolicPoint} (hz : z.2 < s)
    (i : Fin 3) :
    spatialPartial (fun w : ParabolicPoint => heatKernel (x - w.1) (s - w.2)) i z =
      -heatKernelSpaceDerivative (x - z.1) (s - z.2) i := by
  have ht : 0 < s - z.2 := by linarith only [hz]
  have hdΓ0 := differentiableAt_heatKernel_space ht (x - z.1)
  have hsub : HasFDerivAt (fun y : Vec3 => x - y) (-ContinuousLinearMap.id ℝ Vec3) z.1 := by
    simpa using (hasFDerivAt_const (𝕜 := ℝ) x z.1).sub (hasFDerivAt_id (𝕜 := ℝ) z.1)
  have h := (hdΓ0.hasFDerivAt.comp z.1 hsub).fderiv
  have e : (fun y : Vec3 => heatKernel (x - y) (s - z.2)) =
      (fun w => heatKernel w (s - z.2)) ∘ HSub.hSub x := rfl
  unfold spatialPartial
  show fderiv ℝ (fun y : Vec3 => heatKernel (x - y) (s - z.2)) z.1 (basisVec i) = _
  rw [e, h]
  simp [heatKernel_fderiv_apply_basisVec ht]

/-- The directional derivative of the space derivative of the heat kernel. -/
theorem fderiv_heatKernelSpaceDerivative_apply {t : ℝ} (ht : 0 < t) (y₀ : Vec3) (i l : Fin 3) :
    fderiv ℝ (fun y : Vec3 => heatKernelSpaceDerivative y t i) y₀ (basisVec l) =
      -(basisVec l i) / (2 * t) * heatKernel y₀ t +
        -(y₀ i) / (2 * t) * heatKernelSpaceDerivative y₀ t l := by
  have hfun : (fun y : Vec3 => heatKernelSpaceDerivative y t i) =
      fun y : Vec3 => (-(y i) / (2 * t)) * heatKernel y t := by
    funext y
    rw [heatKernelSpaceDerivative, ite_eq_left ht]
  have hd1 : DifferentiableAt ℝ (fun y : Vec3 => -(y i) / (2 * t)) y₀ := by fun_prop
  have hd2 := differentiableAt_heatKernel_space ht y₀
  rw [hfun, fderiv_fun_mul hd1 hd2]
  simp only [add_apply, smul_apply, smul_eq_mul]
  rw [heatKernel_fderiv_apply_basisVec ht]
  have hproj : fderiv ℝ (fun y : Vec3 => -(y i) / (2 * t)) y₀ (basisVec l) =
      -(basisVec l i) / (2 * t) := by
    have hlin : HasFDerivAt (fun y : Vec3 => -(y i) / (2 * t))
        ((-(1 / (2 * t))) • (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)) y₀ := by
      have := ((ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ).hasFDerivAt (x := y₀)).const_smul
        (-(1 / (2 * t)))
      convert this using 1
      funext y
      simp only [Pi.smul_apply, smul_eq_mul, ContinuousLinearMap.proj_apply]
      ring
    rw [hlin.fderiv]
    simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.proj_apply]
    ring
  rw [hproj]
  ring

/-- In the region of the window away from the pole, the heat kernel and its first two spatial
derivatives have the parabolic sizes `ρ⁻³`, `ρ⁻⁴`, `ρ⁻⁵`. -/
theorem heatKernel_window_bounds : ∃ C : ℝ, 0 ≤ C ∧ ∀ (ρ : ℝ), 0 < ρ → ∀ (y : Vec3) (t : ℝ),
    0 < t → t ≤ ρ ^ 2 → vec3EuclideanNorm y ≤ ρ →
    (ρ / 2 ≤ vec3EuclideanNorm y ∨ ρ ^ 2 / 2 ≤ t) →
    heatKernel y t ≤ C / ρ ^ 3 ∧ (∀ i, |heatKernelSpaceDerivative y t i| ≤ C / ρ ^ 4) ∧
      ∀ i l, |fderiv ℝ (fun y' : Vec3 => heatKernelSpaceDerivative y' t i) y (basisVec l)| ≤
        C / ρ ^ 5 := by
  refine ⟨400000000000, by norm_num, fun ρ hρ y t ht htρ hyρ hreg => ?_⟩
  set r : ℝ := vec3EuclideanNorm y with hr
  have hr0 : 0 ≤ r := vec3EuclideanNorm_nonneg y
  have hrho : ρ / 2 ≤ rhoTwo y t := by
    unfold rhoTwo
    rcases hreg with h | h
    · have := Real.sqrt_nonneg t
      linarith only [h, this]
    · have hs : ρ / 2 ≤ Real.sqrt t := by
        rw [Real.le_sqrt (by positivity) ht.le]
        nlinarith only [h, hρ]
      linarith only [hs, hr0]
  have hrpos : 0 < ρ / 2 := by positivity
  have hΓ0 : 0 ≤ heatKernel y t := heatKernel_nonneg y t
  have hΓ : heatKernel y t ≤ 8000 / ρ ^ 3 := by
    refine (heatKernel_le_rho_inv_cube ht).trans ?_
    rw [div_le_div_iff₀ (pow_pos (hrpos.trans_le hrho) 3) (by positivity)]
    have := pow_le_pow_left₀ hrpos.le hrho 3
    nlinarith only [this]
  have hD : ∀ i, |heatKernelSpaceDerivative y t i| ≤ 4800000 / ρ ^ 4 := by
    intro i
    refine (heatKernelSpaceDerivative_abs_le_rho_inv_four ht i).trans ?_
    rw [div_le_div_iff₀ (pow_pos (hrpos.trans_le hrho) 4) (by positivity)]
    have := pow_le_pow_left₀ hrpos.le hrho 4
    nlinarith only [this]
  -- the second derivative
  have hcomp : ∀ k : Fin 3, |y k| ≤ r := fun k => abs_apply_le_vec3EuclideanNorm y k
  have hsec : ∀ i l, |fderiv ℝ (fun y' : Vec3 => heatKernelSpaceDerivative y' t i) y (basisVec l)| ≤
      heatKernel y t / (2 * t) + r ^ 2 / (4 * t ^ 2) * heatKernel y t := by
    intro i l
    rw [fderiv_heatKernelSpaceDerivative_apply ht y i l]
    have hDl : heatKernelSpaceDerivative y t l = -(y l) / (2 * t) * heatKernel y t := by
      rw [heatKernelSpaceDerivative, ite_eq_left ht]
    rw [hDl]
    have hb : |(basisVec l : Vec3) i| ≤ 1 := by
      rw [basisVec_apply]; split_ifs <;> simp
    have hyi := hcomp i
    have hyl := hcomp l
    have h2t : 0 < 2 * t := by positivity
    calc |-(basisVec l i) / (2 * t) * heatKernel y t + -(y i) / (2 * t) * (-(y l) / (2 * t) *
          heatKernel y t)|
        ≤ |(basisVec l : Vec3) i| / (2 * t) * heatKernel y t +
            |y i| * |y l| / (4 * t ^ 2) * heatKernel y t := by
          refine (abs_add_le _ _).trans (le_of_eq ?_)
          rw [abs_mul, abs_mul, abs_mul, abs_div, abs_div, abs_div, abs_neg, abs_neg, abs_neg,
            abs_of_pos h2t, abs_of_nonneg hΓ0]
          field_simp
          ring
      _ ≤ 1 / (2 * t) * heatKernel y t + r * r / (4 * t ^ 2) * heatKernel y t := by
          gcongr
      _ = heatKernel y t / (2 * t) + r ^ 2 / (4 * t ^ 2) * heatKernel y t := by ring
  refine ⟨hΓ.trans (div_le_div_of_nonneg_right (by norm_num) (by positivity)),
    fun i => (hD i).trans (div_le_div_of_nonneg_right (by norm_num) (by positivity)),
    fun i l => (hsec i l).trans ?_⟩
  rcases le_or_gt (ρ ^ 2 / 48) t with hbig | hsmall
  · -- times comparable to `ρ²`
    have h1 : heatKernel y t / (2 * t) ≤ 24 / ρ ^ 2 * heatKernel y t := by
      rw [div_le_iff₀ (by positivity)]
      have : 24 / ρ ^ 2 * (2 * t) ≥ 1 := by
        rw [ge_iff_le, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        nlinarith only [hbig]
      nlinarith only [this, hΓ0]
    have h2 : r ^ 2 / (4 * t ^ 2) ≤ 576 / ρ ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hr2 : r ^ 2 ≤ ρ ^ 2 := pow_le_pow_left₀ hr0 hyρ 2
      have ht2 : ρ ^ 4 / 2304 ≤ t ^ 2 := by nlinarith only [hbig, hρ]
      nlinarith only [hr2, ht2, hρ]
    have h3 : heatKernel y t / (2 * t) + r ^ 2 / (4 * t ^ 2) * heatKernel y t ≤
        600 / ρ ^ 2 * heatKernel y t := by
      have := mul_le_mul_of_nonneg_right h2 hΓ0
      have e : 600 / ρ ^ 2 * heatKernel y t =
          24 / ρ ^ 2 * heatKernel y t + 576 / ρ ^ 2 * heatKernel y t := by ring
      linarith only [h1, this, e]
    refine h3.trans ?_
    calc 600 / ρ ^ 2 * heatKernel y t ≤ 600 / ρ ^ 2 * (8000 / ρ ^ 3) := by gcongr
      _ = 4800000 / ρ ^ 5 := by field_simp; ring
      _ ≤ 400000000000 / ρ ^ 5 := div_le_div_of_nonneg_right (by norm_num) (by positivity)
  · -- small times: the Gaussian factor is controlled by the time derivative
    have hyr : ρ / 2 ≤ r := by
      rcases hreg with h | h
      · exact h
      · exfalso; nlinarith only [h, hsmall, hρ]
    have hTD : |heatKernelTimeDerivative y t| ≤ 320000000 / ρ ^ 5 := by
      refine (heatKernelTimeDerivative_le_rho_inv_five ht).trans ?_
      rw [div_le_div_iff₀ (pow_pos (hrpos.trans_le hrho) 5) (by positivity)]
      have := pow_le_pow_left₀ hrpos.le hrho 5
      nlinarith only [this]
    have hTDf : heatKernelTimeDerivative y t =
        heatKernel y t * (r ^ 2 / (4 * t ^ 2) - 3 / (2 * t)) := by
      rw [heatKernelTimeDerivative, ite_eq_left ht, hr, vec3EuclideanNorm_sq]
    set a : ℝ := heatKernel y t / t with ha
    have ha0 : 0 ≤ a := by positivity
    have hq : 3 ≤ r ^ 2 / (4 * t) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith only [hyr, hsmall, hρ, hr0]
    have hkey : r ^ 2 / (4 * t ^ 2) * heatKernel y t = a * (r ^ 2 / (4 * t)) := by
      rw [ha]; field_simp
    have hTDa : heatKernelTimeDerivative y t = a * (r ^ 2 / (4 * t)) - 3 / 2 * a := by
      rw [hTDf, ha]; field_simp
    have haTD : a ≤ 2 / 3 * |heatKernelTimeDerivative y t| := by
      have := le_abs_self (heatKernelTimeDerivative y t)
      nlinarith only [hTDa, hq, ha0, this]
    have hfirst : heatKernel y t / (2 * t) = a / 2 := by rw [ha]; field_simp
    rw [hfirst, hkey]
    have hsum : a / 2 + a * (r ^ 2 / (4 * t)) ≤ 4 * |heatKernelTimeDerivative y t| := by
      have := le_abs_self (heatKernelTimeDerivative y t)
      nlinarith only [hTDa, haTD, this, ha0]
    refine hsum.trans ?_
    calc 4 * |heatKernelTimeDerivative y t| ≤ 4 * (320000000 / ρ ^ 5) := by gcongr
      _ ≤ 400000000000 / ρ ^ 5 := by
        rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right (by norm_num) (by positivity)

/-- The space derivative of the heat kernel is smooth in space at positive times. -/
theorem contDiff_heatKernelSpaceDerivative {t : ℝ} (ht : 0 < t) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => heatKernelSpaceDerivative y t i) := by
  have hfun : (fun y : Vec3 => heatKernelSpaceDerivative y t i) = fun y : Vec3 =>
      -(y i) / (2 * t) * ((4 * Real.pi * t) ^ (-(3 : ℝ) / 2) *
        Real.exp (-(∑ k, y k ^ 2) / (4 * t))) := by
    funext y
    rw [heatKernelSpaceDerivative, ite_eq_left ht, heatKernel_eq_formula_sum ht]
  rw [hfun]
  fun_prop (disch := positivity)

/-- The heat kernel is smooth in space at positive times. -/
theorem contDiff_heatKernel_space {t : ℝ} (ht : 0 < t) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec3 => heatKernel y t) := by
  have hfun : (fun y : Vec3 => heatKernel y t) = fun y : Vec3 =>
      (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) * Real.exp (-(∑ k, y k ^ 2) / (4 * t)) := by
    funext y; exact heatKernel_eq_formula_sum ht
  rw [hfun]
  fun_prop (disch := positivity)

/-- The directional derivative of `y ↦ g (x - y)` is minus the directional derivative of `g`. -/
theorem fderiv_comp_sub_left_apply {g : Vec3 → ℝ} (x y : Vec3) (hg : DifferentiableAt ℝ g (x - y))
    (v : Vec3) : fderiv ℝ (fun y' => g (x - y')) y v = -(fderiv ℝ g (x - y) v) := by
  have hsub : HasFDerivAt (fun y' : Vec3 => x - y') (-ContinuousLinearMap.id ℝ Vec3) y := by
    simpa using (hasFDerivAt_const (𝕜 := ℝ) x y).sub (hasFDerivAt_id (𝕜 := ℝ) y)
  have h := (hg.hasFDerivAt.comp y hsub).fderiv
  have e : (fun y' : Vec3 => g (x - y')) = g ∘ HSub.hSub x := rfl
  rw [e, h]
  simp

/-- The partials of the backward cutoff, in separated form. -/
theorem serrinCutoff_partials (x : Vec3) {s ρ : ℝ} (hρ : 0 < ρ) (i : Fin 3) :
    (fun z : ParabolicPoint => timePartial (serrinCutoff x s ρ) z) =
      (fun z => serrinBallCutoff x ρ z.1 * deriv (serrinTimeCut s ρ) z.2) ∧
    (fun z : ParabolicPoint => spatialPartial (serrinCutoff x s ρ) i z) =
      (fun z => fderiv ℝ (serrinBallCutoff x ρ) z.1 (basisVec i) * serrinTimeCut s ρ z.2) ∧
    (fun z : ParabolicPoint => spatialSecondPartial (serrinCutoff x s ρ) i i z) =
      (fun z => fderiv ℝ (fun y => fderiv ℝ (serrinBallCutoff x ρ) y (basisVec i)) z.1
        (basisVec i) * serrinTimeCut s ρ z.2) := by
  have hB : ContDiff ℝ (⊤ : ℕ∞) (serrinBallCutoff x ρ) := (serrinBallCutoff_support x hρ x).2.2
  have hBd : Differentiable ℝ (serrinBallCutoff x ρ) := hB.differentiable (by simp)
  have hdB : Differentiable ℝ (fun y => fderiv ℝ (serrinBallCutoff x ρ) y (basisVec i)) :=
    ((hB.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply
      contDiff_const).differentiable (by simp)
  have hT : Differentiable ℝ (serrinTimeCut s ρ) :=
    (contDiff_serrinTimeCut s ρ).differentiable (by simp)
  have h2 := spatialPartial_separated hBd (serrinTimeCut s ρ) i
  refine ⟨timePartial_separated _ hT, h2, ?_⟩
  funext z
  unfold spatialSecondPartial
  have e : (fun w : ParabolicPoint => spatialPartial (serrinCutoff x s ρ) i w) =
      fun w : ParabolicPoint => fderiv ℝ (serrinBallCutoff x ρ) w.1 (basisVec i) *
        serrinTimeCut s ρ w.2 := h2
  rw [e]
  exact congrFun (spatialPartial_separated hdB (serrinTimeCut s ρ) i) z

/-- Before the time `s`, the slice of the commutator kernel is an explicit smooth function of
the space variable. -/
theorem spatialPartial_serrinCutoffKernel_eq_fderiv (x : Vec3) {s ρ : ℝ} (hρ : 0 < ρ)
    {z : ParabolicPoint} (hz : z.2 < s) (l : Fin 3) :
    spatialPartial (serrinCutoffKernel x s ρ) l z =
      fderiv ℝ (fun y : Vec3 =>
        heatKernel (x - y) (s - z.2) *
            (serrinBallCutoff x ρ y * deriv (serrinTimeCut s ρ) z.2 +
              (∑ i, fderiv ℝ (fun y' => fderiv ℝ (serrinBallCutoff x ρ) y' (basisVec i)) y
                (basisVec i)) * serrinTimeCut s ρ z.2) +
          2 * ∑ i, (-heatKernelSpaceDerivative (x - y) (s - z.2) i) *
            (fderiv ℝ (serrinBallCutoff x ρ) y (basisVec i) * serrinTimeCut s ρ z.2))
        z.1 (basisVec l) := by
  unfold spatialPartial
  congr 2
  funext y
  have hyz : ((y, z.2) : ParabolicPoint).2 < s := hz
  unfold serrinCutoffKernel
  have hp := fun i => serrinCutoff_partials x (s := s) hρ i
  rw [congrFun (hp 0).1 (y, z.2)]
  simp only [fun i => congrFun (hp i).2.1 (y, z.2), fun i => congrFun (hp i).2.2 (y, z.2),
    fun i => spatialPartial_heatKernel_translate x s hyz i]
  rw [Finset.sum_mul]

/-- Pointwise bound for the spatial derivative of the commutator kernel in the window. -/
theorem abs_spatialPartial_serrinCutoffKernel_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Vec3) (s ρ : ℝ),
    0 < ρ → ∀ z : ParabolicPoint, z.2 < s →
    z ∈ {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s → ∀ l : Fin 3,
      |spatialPartial (serrinCutoffKernel x s ρ) l z| ≤ C / ρ ^ 6 := by
  obtain ⟨Ck, hCk0, hCk⟩ := heatKernel_window_bounds
  obtain ⟨Cb, hCb0, hCb⟩ := serrinBallCutoff_dir_bounds
  obtain ⟨Ct, hCt0, hCt⟩ := serrinTimeCut_bounds
  refine ⟨Ck * (Cb * Ct + Ct + 18 * Cb), by positivity, ?_⟩
  intro x s ρ hρ z hz hw l
  rw [spatialPartial_serrinCutoffKernel_eq_fderiv x hρ hz l]
  set t : ℝ := s - z.2 with htdef
  have ht : 0 < t := by rw [htdef]; linarith only [hz]
  set y₀ : Vec3 := z.1 with hy₀
  set B : Vec3 → ℝ := serrinBallCutoff x ρ with hBdef
  set T : ℝ → ℝ := serrinTimeCut s ρ with hTdef
  have hB : ContDiff ℝ (⊤ : ℕ∞) B := (serrinBallCutoff_support x hρ x).2.2
  have hsm : ∀ {g : Vec3 → ℝ}, ContDiff ℝ (⊤ : ℕ∞) g → ∀ v : Vec3,
      ContDiff ℝ (⊤ : ℕ∞) (fun y' => fderiv ℝ g y' v) := fun hg v =>
    (hg.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const
  have hdiff : ∀ {g : Vec3 → ℝ}, ContDiff ℝ (⊤ : ℕ∞) g → DifferentiableAt ℝ g y₀ :=
    fun hg => (hg.differentiable (by simp)) y₀
  set dB : Fin 3 → Vec3 → ℝ := fun i y => fderiv ℝ B y (basisVec i) with hdB
  set ddB : Fin 3 → Fin 3 → Vec3 → ℝ := fun i j y => fderiv ℝ (dB i) y (basisVec j) with hddB
  have hdBs : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (dB i) := fun i => hsm hB (basisVec i)
  have hddBs : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (ddB i j) := fun i j => hsm (hdBs i) (basisVec j)
  set S : Vec3 → ℝ := fun y => ∑ i, ddB i i y with hSdef
  -- the four families of factors
  set g0 : Vec3 → ℝ := fun y => heatKernel (x - y) t with hg0
  set a : Vec3 → ℝ := fun y => B y * deriv T z.2 + S y * T z.2 with ha
  set h : Fin 3 → Vec3 → ℝ := fun i y => -heatKernelSpaceDerivative (x - y) t i with hh
  set e : Fin 3 → Vec3 → ℝ := fun i y => dB i y * T z.2 with he
  have hΓs := contDiff_heatKernel_space ht
  have hDs := fun i => contDiff_heatKernelSpaceDerivative ht i
  have dg0 : DifferentiableAt ℝ g0 y₀ :=
    ((hΓs.differentiable (by simp)) (x - y₀)).comp y₀ ((differentiable_const _).sub
      differentiable_id y₀)
  have dS : HasFDerivAt S (∑ i, fderiv ℝ (ddB i i) y₀) y₀ :=
    HasFDerivAt.fun_sum (fun i _ => (hdiff (hddBs i i)).hasFDerivAt)
  have da : DifferentiableAt ℝ a y₀ :=
    ((hdiff hB).mul_const _).add (dS.differentiableAt.mul_const _)
  have dh : ∀ i, DifferentiableAt ℝ (h i) y₀ := fun i =>
    (((hDs i).differentiable (by simp)) (x - y₀)).comp y₀ ((differentiable_const _).sub
      differentiable_id y₀) |>.neg
  have de : ∀ i, DifferentiableAt ℝ (e i) y₀ := fun i => (hdiff (hdBs i)).mul_const _
  have hΦ : HasFDerivAt (fun y => g0 y * a y + 2 * ∑ i, h i y * e i y)
      (g0 y₀ • fderiv ℝ a y₀ + a y₀ • fderiv ℝ g0 y₀ +
        (2 : ℝ) • ∑ i, (h i y₀ • fderiv ℝ (e i) y₀ + e i y₀ • fderiv ℝ (h i) y₀)) y₀ :=
    (dg0.hasFDerivAt.mul da.hasFDerivAt).add
      ((HasFDerivAt.fun_sum (fun i _ => (dh i).hasFDerivAt.mul (de i).hasFDerivAt)).const_mul 2)
  change |fderiv ℝ (fun y => g0 y * a y + 2 * ∑ i, h i y * e i y) y₀ (basisVec l)| ≤ _
  rw [hΦ.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, FunLike.coe_sum, Finset.sum_apply]
  -- the directional derivatives of the factors
  have Dg0 : fderiv ℝ g0 y₀ (basisVec l) = -heatKernelSpaceDerivative (x - y₀) t l := by
    rw [hg0, fderiv_comp_sub_left_apply (g := fun w => heatKernel w t) x y₀
      ((hΓs.differentiable (by simp)) (x - y₀)), heatKernel_fderiv_apply_basisVec ht]
  have Dh : ∀ i, fderiv ℝ (h i) y₀ (basisVec l) =
      fderiv ℝ (fun y' => heatKernelSpaceDerivative y' t i) (x - y₀) (basisVec l) := by
    intro i
    rw [hh]
    simp only
    rw [fderiv_fun_neg, neg_apply, fderiv_comp_sub_left_apply
      (g := fun y' => heatKernelSpaceDerivative y' t i) x y₀
      (((hDs i).differentiable (by simp)) (x - y₀)), neg_neg]
  have De : ∀ i, fderiv ℝ (e i) y₀ (basisVec l) = ddB i l y₀ * T z.2 := by
    intro i
    rw [he]
    simp only
    rw [fderiv_mul_const (hdiff (hdBs i)), smul_apply, smul_eq_mul, mul_comm]
  have Da : fderiv ℝ a y₀ (basisVec l) =
      dB l y₀ * deriv T z.2 + (∑ i, fderiv ℝ (ddB i i) y₀ (basisVec l)) * T z.2 := by
    rw [ha]
    rw [fderiv_fun_add ((hdiff hB).mul_const _) (dS.differentiableAt.mul_const _),
      fderiv_mul_const (hdiff hB), fderiv_mul_const dS.differentiableAt, dS.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul, FunLike.coe_sum, Finset.sum_apply, hdB]
    ring
  rw [Dg0, Da]
  simp only [De, Dh]
  -- geometry of the point in the window
  have hYn : vec3EuclideanNorm (x - y₀) = vec3EuclideanNorm (y₀ - x) := by
    rw [← vec3EuclideanNorm_neg, neg_sub]
  have hYρ : vec3EuclideanNorm (x - y₀) ≤ ρ := by rw [hYn]; exact hw.1
  have htρ : t ≤ ρ ^ 2 := by rw [htdef]; linarith only [hw.2.1]
  have hρ6 : 0 ≤ Ck * (Cb * Ct + Ct + 18 * Cb) / ρ ^ 6 := by positivity
  by_cases hreg : ρ / 2 ≤ vec3EuclideanNorm (x - y₀) ∨ ρ ^ 2 / 2 ≤ t
  · obtain ⟨kΓ, kD, kD2⟩ := hCk ρ hρ (x - y₀) t ht htρ hYρ hreg
    have hTb := hCt s ρ hρ z.2
    have hbB := fun i j m => hCb x ρ hρ y₀ i j m
    have hΓ0 : 0 ≤ heatKernel (x - y₀) t := heatKernel_nonneg _ _
    -- bounds for the factors
    have b_g0 : |g0 y₀| ≤ Ck / ρ ^ 3 := by rw [abs_of_nonneg hΓ0]; exact kΓ
    have b_Dg0 : |-heatKernelSpaceDerivative (x - y₀) t l| ≤ Ck / ρ ^ 4 := by
      rw [abs_neg]; exact kD l
    have b_S : |S y₀| ≤ 3 * (Cb / ρ ^ 2) := by
      rw [hSdef]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ i, |ddB i i y₀| ≤ ∑ _i : Fin 3, Cb / ρ ^ 2 :=
            Finset.sum_le_sum (fun i _ => (hbB i i 0).2.2.1)
        _ = 3 * (Cb / ρ ^ 2) := by simp
    have b_a : |a y₀| ≤ (Ct + 3 * Cb) / ρ ^ 2 := by
      rw [ha]
      simp only
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      calc |B y₀| * |deriv T z.2| + |S y₀| * |T z.2| ≤ 1 * (Ct / ρ ^ 2) + 3 * (Cb / ρ ^ 2) * 1 :=
            add_le_add (mul_le_mul (hbB 0 0 0).1 hTb.2.1 (abs_nonneg _) zero_le_one)
              (mul_le_mul b_S hTb.1 (abs_nonneg _) (by positivity))
        _ = (Ct + 3 * Cb) / ρ ^ 2 := by ring
    have b_Da : |dB l y₀ * deriv T z.2 + (∑ i, fderiv ℝ (ddB i i) y₀ (basisVec l)) * T z.2| ≤
        (Cb * Ct + 3 * Cb) / ρ ^ 3 := by
      have hsum : |∑ i, fderiv ℝ (ddB i i) y₀ (basisVec l)| ≤ 3 * (Cb / ρ ^ 3) := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ i, |fderiv ℝ (ddB i i) y₀ (basisVec l)| ≤ ∑ _i : Fin 3, Cb / ρ ^ 3 :=
              Finset.sum_le_sum (fun i _ => (hbB i i l).2.2.2.1)
          _ = 3 * (Cb / ρ ^ 3) := by simp
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul]
      calc |dB l y₀| * |deriv T z.2| + |∑ i, fderiv ℝ (ddB i i) y₀ (basisVec l)| * |T z.2|
          ≤ Cb / ρ * (Ct / ρ ^ 2) + 3 * (Cb / ρ ^ 3) * 1 :=
            add_le_add (mul_le_mul (hbB l 0 0).2.1 hTb.2.1 (abs_nonneg _) (by positivity))
              (mul_le_mul hsum hTb.1 (abs_nonneg _) (by positivity))
        _ = (Cb * Ct + 3 * Cb) / ρ ^ 3 := by field_simp
    have b_i : ∀ i, |h i y₀ * (ddB i l y₀ * T z.2) +
        e i y₀ * fderiv ℝ (fun y' => heatKernelSpaceDerivative y' t i) (x - y₀) (basisVec l)| ≤
        2 * (Ck * Cb) / ρ ^ 6 := by
      intro i
      have b_h : |h i y₀| ≤ Ck / ρ ^ 4 := by rw [hh]; simp only; rw [abs_neg]; exact kD i
      have b_e : |e i y₀| ≤ Cb / ρ := by
        rw [he]; simp only; rw [abs_mul]
        calc |dB i y₀| * |T z.2| ≤ Cb / ρ * 1 :=
              mul_le_mul (hbB i 0 0).2.1 hTb.1 (abs_nonneg _) (by positivity)
          _ = Cb / ρ := mul_one _
      have b_de : |ddB i l y₀ * T z.2| ≤ Cb / ρ ^ 2 := by
        rw [abs_mul]
        calc |ddB i l y₀| * |T z.2| ≤ Cb / ρ ^ 2 * 1 :=
              mul_le_mul (hbB i l 0).2.2.1 hTb.1 (abs_nonneg _) (by positivity)
          _ = Cb / ρ ^ 2 := mul_one _
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul (h i y₀), abs_mul (e i y₀)]
      calc |h i y₀| * |ddB i l y₀ * T z.2| +
            |e i y₀| * |fderiv ℝ (fun y' => heatKernelSpaceDerivative y' t i) (x - y₀) (basisVec l)|
          ≤ Ck / ρ ^ 4 * (Cb / ρ ^ 2) + Cb / ρ * (Ck / ρ ^ 5) :=
            add_le_add (mul_le_mul b_h b_de (abs_nonneg _) (by positivity))
              (mul_le_mul b_e (kD2 i l) (abs_nonneg _) (by positivity))
        _ = 2 * (Ck * Cb) / ρ ^ 6 := by field_simp; ring
    have b_sum : |∑ i, (h i y₀ * (ddB i l y₀ * T z.2) +
        e i y₀ * fderiv ℝ (fun y' => heatKernelSpaceDerivative y' t i) (x - y₀) (basisVec l))| ≤
        3 * (2 * (Ck * Cb) / ρ ^ 6) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc _ ≤ ∑ _i : Fin 3, 2 * (Ck * Cb) / ρ ^ 6 := Finset.sum_le_sum (fun i _ => b_i i)
        _ = 3 * (2 * (Ck * Cb) / ρ ^ 6) := by simp
    refine (abs_add_le _ _).trans ?_
    refine (add_le_add (abs_add_le _ _) le_rfl).trans ?_
    rw [abs_mul, abs_mul, abs_mul, abs_two]
    calc |g0 y₀| * |dB l y₀ * deriv T z.2 + (∑ i, fderiv ℝ (ddB i i) y₀ (basisVec l)) * T z.2| +
          |a y₀| * |-heatKernelSpaceDerivative (x - y₀) t l| +
          2 * |∑ i, (h i y₀ * (ddB i l y₀ * T z.2) +
            e i y₀ * fderiv ℝ (fun y' => heatKernelSpaceDerivative y' t i) (x - y₀) (basisVec l))|
        ≤ Ck / ρ ^ 3 * ((Cb * Ct + 3 * Cb) / ρ ^ 3) + (Ct + 3 * Cb) / ρ ^ 2 * (Ck / ρ ^ 4) +
          2 * (3 * (2 * (Ck * Cb) / ρ ^ 6)) := by
          gcongr
      _ = Ck * (Cb * Ct + Ct + 18 * Cb) / ρ ^ 6 := by field_simp; ring
  · -- inside the inner cylinder every factor carrying a derivative of the cutoff vanishes
    push Not at hreg
    obtain ⟨hin, htin⟩ := hreg
    have hin' : vec3EuclideanNorm (y₀ - x) < ρ / 2 := by rw [← hYn]; exact hin
    have hT' : deriv T z.2 = 0 := (hCt s ρ hρ z.2).2.2 (by rw [htdef] at htin; linarith only [htin])
    have hz3 := fun i j m => ((hCb x ρ hρ y₀ i j m).2.2.2.2 hin')
    have hS0 : S y₀ = 0 := by
      rw [hSdef]; exact Finset.sum_eq_zero (fun i _ => (hz3 i i 0).2.1)
    have ha0 : a y₀ = 0 := by rw [ha]; simp only; rw [hT', hS0]; ring
    have hdd0 : ∑ i, fderiv ℝ (ddB i i) y₀ (basisVec l) = 0 :=
      Finset.sum_eq_zero (fun i _ => (hz3 i i l).2.2)
    have he0 : ∀ i, e i y₀ = 0 := fun i => by
      have h0 : dB i y₀ = 0 := (hz3 i 0 0).1
      rw [he]; show dB i y₀ * T z.2 = 0; rw [h0, zero_mul]
    have hde0 : ∀ i, ddB i l y₀ = 0 := fun i => (hz3 i l 0).2.1
    simp only [ha0, hT', hdd0, he0, hde0, mul_zero, zero_mul, add_zero, Finset.sum_const_zero,
      abs_zero]
    exact hρ6

/-- The commutator kernel is smooth before the time `s`. -/
theorem contDiffOn_serrinCutoffKernel (x : Vec3) {s ρ : ℝ} (hρ : 0 < ρ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => serrinCutoffKernel x s ρ z)
      (spaceTimeSet univ (Iio s)) := by
  have hΓ : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => heatKernel (x - z.1) (s - z.2)) (spaceTimeSet univ (Iio s)) := by
    have hmap : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => ((x - z.1, s - z.2) : Vec3 × ℝ)) := by
      fun_prop
    refine (heatKernel_contDiffOn_pos.of_le (by exact_mod_cast le_top)).comp hmap.contDiffOn ?_
    intro z hz
    exact ⟨mem_univ _, show (0 : ℝ) < s - z.2 by linarith only [show z.2 < s from hz.2]⟩
  have hB : ContDiff ℝ (⊤ : ℕ∞) (serrinBallCutoff x ρ) := (serrinBallCutoff_support x hρ x).2.2
  have hsm : ∀ {g : Vec3 → ℝ}, ContDiff ℝ (⊤ : ℕ∞) g → ∀ v : Vec3,
      ContDiff ℝ (⊤ : ℕ∞) (fun y' => fderiv ℝ g y' v) := fun hg v =>
    (hg.fderiv_right (m := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp)).clm_apply contDiff_const
  have hT := contDiff_serrinTimeCut s ρ
  have hT' : ContDiff ℝ (⊤ : ℕ∞) (deriv (serrinTimeCut s ρ)) := hT.iterate_deriv 1
  have hsep : ∀ {F : Vec3 → ℝ} {G : ℝ → ℝ}, ContDiff ℝ (⊤ : ℕ∞) F → ContDiff ℝ (⊤ : ℕ∞) G →
      ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => F z.1 * G z.2) (spaceTimeSet univ (Iio s)) :=
    fun hF hG => ((hF.comp contDiff_fst).mul (hG.comp contDiff_snd)).contDiffOn
  have hp := fun i => serrinCutoff_partials x (s := s) hρ i
  have htp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => timePartial (serrinCutoff x s ρ) z)
      (spaceTimeSet univ (Iio s)) := by
    have e := (hp 0).1
    exact (hsep hB hT').congr (fun z _ => congrFun e z)
  have hss : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialSecondPartial (serrinCutoff x s ρ) i i z)
      (spaceTimeSet univ (Iio s)) := fun i =>
    (hsep (hsm (hsm hB (basisVec i)) (basisVec i)) hT).congr (fun z _ => congrFun (hp i).2.2 z)
  have hsp : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => spatialPartial (serrinCutoff x s ρ) i z)
      (spaceTimeSet univ (Iio s)) := fun i =>
    (hsep (hsm hB (basisVec i)) hT).congr (fun z _ => congrFun (hp i).2.1 z)
  have hG : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ =>
      spatialPartial (fun w : ParabolicPoint => heatKernel (x - w.1) (s - w.2)) i z)
      (spaceTimeSet univ (Iio s)) := fun i =>
    contDiffOn_spatialPartial_iterate_spaceTimeSet isOpen_univ isOpen_Iio hΓ i 1
  unfold serrinCutoffKernel
  exact (hΓ.mul (htp.add (ContDiffOn.sum (fun i _ => hss i)))).add
    (contDiffOn_const.mul (ContDiffOn.sum (fun i _ => (hG i).mul (hsp i))))

/-- The spatial derivative of the commutator kernel is integrable before the time `s`, with
integral of size `ρ⁻¹`. -/
theorem serrinCutoffKernel_spatialPartial_integral : ∃ C : ℝ, 0 < C ∧ ∀ (x : Vec3) (s ρ : ℝ),
    0 < ρ → ρ ≤ 1 → ∀ l : Fin 3,
      IntegrableOn (fun z => spatialPartial (serrinCutoffKernel x s ρ) l z)
        {z : ParabolicPoint | z.2 < s} ∧
      ∫ z in {z : ParabolicPoint | z.2 < s}, |spatialPartial (serrinCutoffKernel x s ρ) l z| ≤
        C / ρ := by
  obtain ⟨C₀, hC₀, hC₀b⟩ := abs_spatialPartial_serrinCutoffKernel_le
  refine ⟨8 * C₀ + 1, by positivity, fun x s ρ hρ _ l => ?_⟩
  set U : Set (Vec3 × ℝ) := {z | z.2 < s} with hU
  have hUm : MeasurableSet U := measurableSet_lt measurable_snd measurable_const
  set W : Set (Vec3 × ℝ) := {y : Vec3 | vec3EuclideanNorm (y - x) ≤ ρ} ×ˢ Icc (s - ρ ^ 2) s
    with hW
  have hWm : MeasurableSet W := by
    have hc : Continuous (fun y : Vec3 => vec3EuclideanNorm (y - x)) := by
      unfold vec3EuclideanNorm; fun_prop
    exact (measurableSet_le hc.measurable measurable_const).prod measurableSet_Icc
  have hWsub : W ⊆ Metric.closedBall x ρ ×ˢ Icc (s - ρ ^ 2) s := by
    intro z hz
    refine ⟨?_, hz.2⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact (norm_le_vec3EuclideanNorm _).trans hz.1
  have hvolW : volume W ≤ ENNReal.ofReal (8 * ρ ^ 5) := by
    refine (measure_mono hWsub).trans (le_of_eq ?_)
    rw [show (volume : Measure (Vec3 × ℝ)) = (volume : Measure Vec3).prod (volume : Measure ℝ)
      from rfl, Measure.prod_prod, Real.volume_pi_closedBall x hρ.le, Real.volume_Icc,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [Fintype.card_fin]
    ring
  have hWfin : volume W < ⊤ := hvolW.trans_lt ENNReal.ofReal_lt_top
  have hbound : ∀ z ∈ U, |spatialPartial (serrinCutoffKernel x s ρ) l z| ≤
      W.indicator (fun _ => C₀ / ρ ^ 6) z := by
    intro z hz
    by_cases hzW : z ∈ W
    · rw [indicator_of_mem hzW]; exact hC₀b x s ρ hρ z hz hzW l
    · rw [indicator_of_notMem hzW, (spatialPartial_serrinKernels_eq_zero x hρ hz hzW l).2, abs_zero]
  have hmaj : Integrable (W.indicator (fun _ : Vec3 × ℝ => C₀ / ρ ^ 6)) :=
    (integrable_indicator_iff hWm).mpr (integrableOn_const hWfin.ne)
  have hmeas : AEStronglyMeasurable (fun z : Vec3 × ℝ =>
      spatialPartial (serrinCutoffKernel x s ρ) l z) (volume.restrict U) := by
    have hc := (contDiffOn_spatialPartial_iterate_spaceTimeSet isOpen_univ isOpen_Iio
      (contDiffOn_serrinCutoffKernel x (s := s) hρ) l 1).continuousOn
    have hUeq : spaceTimeSet univ (Iio s) = U := by
      ext z; exact ⟨fun h => h.2, fun h => ⟨mem_univ _, h⟩⟩
    rw [hUeq] at hc
    exact hc.aestronglyMeasurable hUm
  have hae : ∀ᵐ z : Vec3 × ℝ ∂(volume.restrict U),
      ‖spatialPartial (serrinCutoffKernel x s ρ) l z‖ ≤ W.indicator (fun _ => C₀ / ρ ^ 6) z :=
    (ae_restrict_iff' hUm).mpr (Filter.Eventually.of_forall (fun z hz => hbound z hz))
  have hint : IntegrableOn (fun z : Vec3 × ℝ => spatialPartial (serrinCutoffKernel x s ρ) l z) U :=
    Integrable.mono' hmaj.integrableOn hmeas hae
  refine ⟨hint, ?_⟩
  have h1 : ∫ z in U, |spatialPartial (serrinCutoffKernel x s ρ) l z| ≤
      ∫ z in U, W.indicator (fun _ => C₀ / ρ ^ 6) z :=
    setIntegral_mono_on hint.abs hmaj.integrableOn hUm hbound
  have h2 : ∫ z in U, W.indicator (fun _ => C₀ / ρ ^ 6) z ≤
      ∫ z, W.indicator (fun _ => C₀ / ρ ^ 6) z :=
    setIntegral_le_integral hmaj (Filter.Eventually.of_forall
      (fun z => indicator_nonneg (fun _ _ => by positivity) z))
  have h3 : ∫ z, W.indicator (fun _ : Vec3 × ℝ => C₀ / ρ ^ 6) z ≤ C₀ / ρ ^ 6 * (8 * ρ ^ 5) := by
    rw [integral_indicator hWm, setIntegral_const, smul_eq_mul, mul_comm]
    gcongr
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hvolW
  have h4 : C₀ / ρ ^ 6 * (8 * ρ ^ 5) ≤ (8 * C₀ + 1) / ρ := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hρ]
    nlinarith only [hρ, hC₀, pow_pos hρ 6]
  exact h1.trans (h2.trans (h3.trans h4))

end CIV
