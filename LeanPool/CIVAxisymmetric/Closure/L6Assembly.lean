/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Closure.EllipticBounds
public import LeanPool.CIVAxisymmetric.Closure.GktSmallness
public import LeanPool.CIVAxisymmetric.Closure.L6FromGradient
public import LeanPool.CIVAxisymmetric.Analysis.SobolevSix
public import LeanPool.CIVAxisymmetric.Analysis.NormCompare

/-!
# The `L⁶` bound and the closure of `lem:aniso:closure`

This file assembles the last two steps of the closure argument `lem:aniso:closure` of
*Regularity of asymptotically axisymmetric solutions to the 3D Navier–Stokes equations with
analytic forcing*, arXiv:2609.20803.

The first step turns the weighted enstrophy bound `Y t + 1 ≤ C' (-t)^(-C_* η)` of
`closure_gronwall_bound` into a spatial `L⁶` bound on a fixed ball,

`‖u(·,t)‖_{L⁶(B(ρ))} ≤ C'' (-t)^(-C_* η / 2)` for `t ∈ (t_η, 0)`.

It combines three ingredients: the elliptic gradient bound
`integral_sq_fderiv_smul_le`, which controls `∫ |∇(χ u)|²` by `2 Y + C`; the Sobolev
inequality `exists_sobolev_six_const`, consumed through `lintegral_pow_six_le_of_eq_on_ball`;
and the enstrophy bound itself.

The Sobolev step is scalar, while the target is the Euclidean norm `vec3EuclideanNorm` of a
vector field.  The bridge is `lintegral_pow_six_euclideanNorm_le_sum_components`: the Euclidean
norm is dominated pointwise by the `ℓ¹` norm of the components
(`vec3EuclideanNorm_le_sum_abs`), and the `L⁶` triangle inequality then splits the ball
integral into the three componentwise ones that the scalar lemma bounds.

A second mismatch is the norm on `Vec3 = Fin 3 → ℝ`, which is the sup norm.  The Sobolev
inequality is phrased with the operator norm `‖fderiv ℝ g x‖` of the differential, whereas the
elliptic bound produces the coordinate sum `∑ⱼ (∂ⱼ g)²`.  Since the dual of the sup norm is the
`ℓ¹` norm, `sq_opNorm_le_three_mul_sum_sq_basisVec` gives `‖fderiv ℝ g x‖² ≤ 3 ∑ⱼ (∂ⱼ g x)²`,
which is what `eLpNorm_fderiv_comp_two_le` integrates.

The second step specialises `η = 1 / (16 C_*)`, so that the `L⁶` decay exponent is
`β = C_* η / 2 = 1/32` and `4β = 1/8 < 1`.  That is exactly the range in which
`gkt_smallness_of_l6_bound` converts the `L⁶` bound into the parabolic smallness hypothesis of
the Gustafson–Kang–Tsai criterion, which is the conclusion `closure_from_enstrophy_bound`.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



/-! ### Two pointwise comparisons on `Vec3` -/

/-- The Euclidean norm of a vector in `Vec3` is at most the sum of the absolute values of its
components. -/
theorem vec3EuclideanNorm_le_sum_abs (v : Vec3) :
    vec3EuclideanNorm v ≤ ∑ i : Fin 3, |v i| := by
  have hsum_nonneg : 0 ≤ ∑ i : Fin 3, |v i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have h01 : 0 ≤ |v 0| * |v 1| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have h02 : 0 ≤ |v 0| * |v 2| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have h12 : 0 ≤ |v 1| * |v 2| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hsq : ∑ i : Fin 3, v i ^ 2 ≤ (∑ i : Fin 3, |v i|) ^ 2 := by
    simp only [Fin.sum_univ_three]
    nlinarith only [h01, h02, h12, sq_abs (v 0), sq_abs (v 1), sq_abs (v 2)]
  calc vec3EuclideanNorm v = Real.sqrt (∑ i : Fin 3, v i ^ 2) := rfl
    _ ≤ Real.sqrt ((∑ i : Fin 3, |v i|) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ∑ i : Fin 3, |v i| := Real.sqrt_sq hsum_nonneg

/-- `Vec3` carries the sup norm, so the dual norm of a linear functional is its `ℓ¹` norm in the
coordinate basis.  Comparing `ℓ¹` with `ℓ²` in three coordinates gives
`‖L‖² ≤ 3 ∑ⱼ (L eⱼ)²`. -/
theorem sq_opNorm_le_three_mul_sum_sq_basisVec (L : Vec3 →L[ℝ] ℝ) :
    ‖L‖ ^ 2 ≤ 3 * ∑ j : Fin 3, (L (basisVec j)) ^ 2 := by
  have hy_nonneg : 0 ≤ ∑ j : Fin 3, |L (basisVec j)| :=
    Finset.sum_nonneg fun j _ => abs_nonneg _
  have hop : ‖L‖ ≤ ∑ j : Fin 3, |L (basisVec j)| := by
    refine L.opNorm_le_bound hy_nonneg fun x => ?_
    have hLx : L x = ∑ j : Fin 3, x j * L (basisVec j) := by
      conv_lhs => rw [← CKN.sum_smul_basisVec x]
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]
    rw [Real.norm_eq_abs, hLx, mul_comm]
    exact abs_sum_mul_le_norm_mul_sqrt x (fun j => L (basisVec j))
  have hsq : (∑ j : Fin 3, |L (basisVec j)|) ^ 2 ≤ 3 * ∑ j : Fin 3, (L (basisVec j)) ^ 2 := by
    simp only [Fin.sum_univ_three]
    nlinarith only [sq_abs (L (basisVec 0)), sq_abs (L (basisVec 1)), sq_abs (L (basisVec 2)),
      sq_nonneg (|L (basisVec 0)| - |L (basisVec 1)|),
      sq_nonneg (|L (basisVec 0)| - |L (basisVec 2)|),
      sq_nonneg (|L (basisVec 1)| - |L (basisVec 2)|)]
  nlinarith only [hop, hsq, norm_nonneg L, hy_nonneg]

/-! ### The scalar-to-vector bridge on a ball -/

/-- The bridge between the scalar `L⁶` estimate `lintegral_pow_six_le_of_eq_on_ball` and the
vector-valued target: on a ball the `L⁶` norm of the Euclidean length of `v` is at most the sum
of the `L⁶` norms of its three components.  Only a continuous representative `w` agreeing with
`v` on the ball is required, which is how the estimate is used: `w = χ • u(·,t)` is globally
smooth while `u(·,t)` is smooth only on an open set. -/
theorem lintegral_pow_six_euclideanNorm_le_sum_components {v w : Vec3 → Vec3} {ρ : ℝ}
    (hw : ∀ i : Fin 3, Continuous fun x : Vec3 => w x i)
    (heq : ∀ x ∈ vec3Ball (0 : Vec3) ρ, w x = v x) :
    (∫⁻ x in vec3Ball 0 ρ, ENNReal.ofReal (vec3EuclideanNorm (v x)) ^ (6 : ℝ)) ^ (1 / 6 : ℝ)
      ≤ ∑ i : Fin 3,
          (∫⁻ x in vec3Ball 0 ρ, ENNReal.ofReal |v x i| ^ (6 : ℝ)) ^ (1 / 6 : ℝ) := by
  have hB : MeasurableSet (vec3Ball (0 : Vec3) ρ) := (isOpen_vec3Ball (0 : Vec3) ρ).measurableSet
  have hnormcont : Continuous fun x : Vec3 => vec3EuclideanNorm (w x) := by
    have hsum : Continuous fun x : Vec3 => ∑ i : Fin 3, w x i ^ 2 :=
      continuous_finsetSum Finset.univ fun i _ => (hw i).pow 2
    exact Real.continuous_sqrt.comp hsum
  have key : ∀ f : Vec3 → ℝ,
      AEStronglyMeasurable f (volume.restrict (vec3Ball (0 : Vec3) ρ)) →
      (∫⁻ x in vec3Ball (0 : Vec3) ρ, ‖f x‖ₑ ^ (6 : ℝ)) ^ (1 / 6 : ℝ)
        = eLpNorm f 6 (volume.restrict (vec3Ball (0 : Vec3) ρ)) := by
    intro f hf
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf]
    norm_num
  have hLHS : (∫⁻ x in vec3Ball (0 : Vec3) ρ, ENNReal.ofReal (vec3EuclideanNorm (v x)) ^ (6 : ℝ))
      = ∫⁻ x in vec3Ball (0 : Vec3) ρ, ‖vec3EuclideanNorm (w x)‖ₑ ^ (6 : ℝ) := by
    refine setLIntegral_congr_fun hB fun x hx => ?_
    rw [Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _), heq x hx]
  have hRHS : ∀ i : Fin 3,
      (∫⁻ x in vec3Ball (0 : Vec3) ρ, ENNReal.ofReal |v x i| ^ (6 : ℝ)) ^ (1 / 6 : ℝ)
        = eLpNorm (fun x : Vec3 => |w x i|) 6 (volume.restrict (vec3Ball (0 : Vec3) ρ)) := by
    intro i
    have hcongr : (∫⁻ x in vec3Ball (0 : Vec3) ρ, ENNReal.ofReal |v x i| ^ (6 : ℝ))
        = ∫⁻ x in vec3Ball (0 : Vec3) ρ, ‖|w x i|‖ₑ ^ (6 : ℝ) := by
      refine setLIntegral_congr_fun hB fun x hx => ?_
      rw [Real.enorm_eq_ofReal (abs_nonneg _), heq x hx]
    rw [hcongr, key _ ((hw i).abs).aestronglyMeasurable]
  rw [hLHS, key _ hnormcont.aestronglyMeasurable]
  simp only [hRHS]
  calc eLpNorm (fun x : Vec3 => vec3EuclideanNorm (w x)) 6
          (volume.restrict (vec3Ball (0 : Vec3) ρ))
      ≤ eLpNorm (∑ i : Fin 3, fun x : Vec3 => |w x i|) 6
          (volume.restrict (vec3Ball (0 : Vec3) ρ)) := by
        refine eLpNorm_mono_real hnormcont.aestronglyMeasurable fun x => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _), Finset.sum_apply]
        exact vec3EuclideanNorm_le_sum_abs (w x)
    _ ≤ ∑ i : Fin 3, eLpNorm (fun x : Vec3 => |w x i|) 6
          (volume.restrict (vec3Ball (0 : Vec3) ρ)) := eLpNorm_sum_le (by norm_num)

/-! ### From the coordinate gradient energy to the Sobolev right-hand side -/

/-- The `L²` norm of the differential of one component of a smooth compactly supported field,
in terms of the coordinate gradient energy that the elliptic bound controls. -/
theorem eLpNorm_fderiv_comp_two_le {w : Vec3 → Vec3} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hws : HasCompactSupport w) (i : Fin 3) :
    eLpNorm (μ := volume) (fderiv ℝ fun x : Vec3 => w x i) 2
      ≤ ENNReal.ofReal ((3 * ∫ x : Vec3, ∑ j : Fin 3,
          (fderiv ℝ (fun y : Vec3 => w y i) x (basisVec j)) ^ 2) ^ (1 / 2 : ℝ)) := by
  have hcont : Continuous (fderiv ℝ fun x : Vec3 => w x i) :=
    (contDiff_comp w hw i).continuous_fderiv (by simp)
  have hInt : Integrable (fun x : Vec3 =>
      ∑ j : Fin 3, (fderiv ℝ (fun y : Vec3 => w y i) x (basisVec j)) ^ 2) :=
    integrable_finsetSum _ fun j _ => integrable_sq_fderiv_comp w hws hw i j
  have hnn : 0 ≤ᵐ[volume] fun x : Vec3 =>
      3 * ∑ j : Fin 3, (fderiv ℝ (fun y : Vec3 => w y i) x (basisVec j)) ^ 2 := by
    filter_upwards with x
    positivity
  have hIge : 0 ≤ ∫ x : Vec3, 3 * ∑ j : Fin 3,
      (fderiv ℝ (fun y : Vec3 => w y i) x (basisVec j)) ^ 2 :=
    integral_nonneg fun x => by positivity
  have hpt : ∀ x : Vec3, ‖fderiv ℝ (fun y : Vec3 => w y i) x‖ₑ ^ (2 : ℝ)
      ≤ ENNReal.ofReal (3 * ∑ j : Fin 3,
          (fderiv ℝ (fun y : Vec3 => w y i) x (basisVec j)) ^ 2) := by
    intro x
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact sq_opNorm_le_three_mul_sum_sq_basisVec _
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    hcont.aestronglyMeasurable]
  have htoReal : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [htoReal]
  calc (∫⁻ x : Vec3, ‖fderiv ℝ (fun y : Vec3 => w y i) x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      ≤ (∫⁻ x : Vec3, ENNReal.ofReal (3 * ∑ j : Fin 3,
          (fderiv ℝ (fun y : Vec3 => w y i) x (basisVec j)) ^ 2)) ^ (1 / 2 : ℝ) :=
        ENNReal.rpow_le_rpow (lintegral_mono hpt) (by norm_num)
    _ = (ENNReal.ofReal (∫ x : Vec3, 3 * ∑ j : Fin 3,
          (fderiv ℝ (fun y : Vec3 => w y i) x (basisVec j)) ^ 2)) ^ (1 / 2 : ℝ) := by
        rw [ofReal_integral_eq_lintegral_ofReal (hInt.const_mul 3) hnn]
    _ = ENNReal.ofReal ((∫ x : Vec3, 3 * ∑ j : Fin 3,
          (fderiv ℝ (fun y : Vec3 => w y i) x (basisVec j)) ^ 2) ^ (1 / 2 : ℝ)) :=
        ENNReal.ofReal_rpow_of_nonneg hIge (by norm_num)
    _ = ENNReal.ofReal ((3 * ∫ x : Vec3, ∑ j : Fin 3,
          (fderiv ℝ (fun y : Vec3 => w y i) x (basisVec j)) ^ 2) ^ (1 / 2 : ℝ)) := by
        rw [integral_const_mul]

/-! ### The `L⁶` bound on a ball from a gradient-energy bound -/

/-- The `L⁶` norm of `v` on a ball, bounded by the gradient energy of a smooth compactly
supported field `w` that agrees with `v` on that ball.  This packages the Sobolev inequality
(through `lintegral_pow_six_le_of_eq_on_ball`), the scalar-to-vector bridge, and the
sup-norm/coordinate comparison of `eLpNorm_fderiv_comp_two_le`. -/
theorem lintegral_pow_six_euclideanNorm_le_of_gradient_bound {C : ℝ} (hC : 0 < C)
    (hsob : ∀ g : Vec3 → ℝ, ContDiff ℝ 1 g → HasCompactSupport g →
      eLpNorm g 6 ≤ ENNReal.ofReal C * eLpNorm (fderiv ℝ g) 2)
    {v w : Vec3 → Vec3} {ρ D : ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hws : HasCompactSupport w)
    (heq : ∀ x ∈ vec3Ball (0 : Vec3) ρ, w x = v x)
    (hD : (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
        (fderiv ℝ (fun y : Vec3 => w y i) x (basisVec j)) ^ 2) ≤ D) :
    (∫⁻ x in vec3Ball 0 ρ, ENNReal.ofReal (vec3EuclideanNorm (v x)) ^ (6 : ℝ)) ^ (1 / 6 : ℝ)
      ≤ ENNReal.ofReal (3 * C * (3 * D) ^ (1 / 2 : ℝ)) := by
  have hIi : ∀ i : Fin 3, Integrable (fun x : Vec3 =>
      ∑ j : Fin 3, (fderiv ℝ (fun y : Vec3 => w y i) x (basisVec j)) ^ 2) :=
    fun i => integrable_finsetSum _ fun j _ => integrable_sq_fderiv_comp w hws hw i j
  have hGi_nonneg : ∀ i : Fin 3, 0 ≤ ∫ x : Vec3, ∑ j : Fin 3,
      (fderiv ℝ (fun y : Vec3 => w y i) x (basisVec j)) ^ 2 :=
    fun i => integral_nonneg fun x => by positivity
  have hsplit : (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
        (fderiv ℝ (fun y : Vec3 => w y i) x (basisVec j)) ^ 2)
      = ∑ i : Fin 3, ∫ x : Vec3, ∑ j : Fin 3,
        (fderiv ℝ (fun y : Vec3 => w y i) x (basisVec j)) ^ 2 :=
    integral_finsetSum Finset.univ fun i _ => hIi i
  have hDnonneg : 0 ≤ D := by
    have h0 : 0 ≤ ∑ i : Fin 3, ∫ x : Vec3, ∑ j : Fin 3,
        (fderiv ℝ (fun y : Vec3 => w y i) x (basisVec j)) ^ 2 :=
      Finset.sum_nonneg fun i _ => hGi_nonneg i
    rw [hsplit] at hD
    linarith only [h0, hD]
  have hGi_le : ∀ i : Fin 3, (∫ x : Vec3, ∑ j : Fin 3,
      (fderiv ℝ (fun y : Vec3 => w y i) x (basisVec j)) ^ 2) ≤ D := by
    intro i
    have hsingle := Finset.single_le_sum
      (f := fun i' : Fin 3 => ∫ x : Vec3, ∑ j : Fin 3,
        (fderiv ℝ (fun y : Vec3 => w y i') x (basisVec j)) ^ 2)
      (fun i' _ => hGi_nonneg i') (Finset.mem_univ i)
    rw [hsplit] at hD
    linarith only [hsingle, hD]
  have hstep : ∀ i : Fin 3,
      (∫⁻ x in vec3Ball (0 : Vec3) ρ, ENNReal.ofReal |v x i| ^ (6 : ℝ)) ^ (1 / 6 : ℝ)
        ≤ ENNReal.ofReal (C * (3 * D) ^ (1 / 2 : ℝ)) := by
    intro i
    have h1 := lintegral_pow_six_le_of_eq_on_ball hC hsob (u := fun x : Vec3 => v x i)
      (g := fun x : Vec3 => w x i) (ρ := ρ) ((contDiff_comp w hw i).of_le (by simp))
      (hasCompactSupport_comp w hws i) (fun x hx => by rw [heq x hx])
    have h2 := eLpNorm_fderiv_comp_two_le hw hws i
    have h3 : ENNReal.ofReal ((3 * ∫ x : Vec3, ∑ j : Fin 3,
          (fderiv ℝ (fun y : Vec3 => w y i) x (basisVec j)) ^ 2) ^ (1 / 2 : ℝ))
        ≤ ENNReal.ofReal ((3 * D) ^ (1 / 2 : ℝ)) :=
      ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow (by positivity) (by linarith only [hGi_le i]) (by norm_num))
    calc (∫⁻ x in vec3Ball (0 : Vec3) ρ, ENNReal.ofReal |v x i| ^ (6 : ℝ)) ^ (1 / 6 : ℝ)
        ≤ ENNReal.ofReal C * eLpNorm (μ := volume) (fderiv ℝ fun x : Vec3 => w x i) 2 := h1
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal ((3 * D) ^ (1 / 2 : ℝ)) :=
          mul_le_mul' le_rfl (h2.trans h3)
      _ = ENNReal.ofReal (C * (3 * D) ^ (1 / 2 : ℝ)) := (ENNReal.ofReal_mul hC.le).symm
  calc (∫⁻ x in vec3Ball (0 : Vec3) ρ,
          ENNReal.ofReal (vec3EuclideanNorm (v x)) ^ (6 : ℝ)) ^ (1 / 6 : ℝ)
      ≤ ∑ i : Fin 3,
          (∫⁻ x in vec3Ball (0 : Vec3) ρ, ENNReal.ofReal |v x i| ^ (6 : ℝ)) ^ (1 / 6 : ℝ) :=
        lintegral_pow_six_euclideanNorm_le_sum_components
          (fun i => continuous_comp w hw i) heq
    _ ≤ ∑ _i : Fin 3, ENNReal.ofReal (C * (3 * D) ^ (1 / 2 : ℝ)) :=
        Finset.sum_le_sum fun i _ => hstep i
    _ = ENNReal.ofReal (3 * C * (3 * D) ^ (1 / 2 : ℝ)) := by
        rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity]
        congr 1
        simp only [Fin.sum_univ_three]
        ring

/-! ### The `L⁶` bound of `lem:aniso:closure` -/

/-- The spatial `L⁶` bound on the ball `B(ρ)`, from the weighted enstrophy bound.

If `χ` is a smooth cutoff supported in the open set `U` on whose time slices `u` is smooth and
divergence free, `χ = 1` on `B(ρ)`, `|u(·,t)| ≤ Mu` wherever `∇χ ≠ 0`, and the enstrophy
`Y t = ∫ χ² |curl u(·,t)|²` satisfies `Y t + 1 ≤ C' (-t)^(-a)` on `(tη, 0)`, then

`‖u(·,t)‖_{L⁶(B(ρ))} ≤ C'' (-t)^(-a/2)` on `(tη, 0)`.

The `(-t)`-exponent is halved because the gradient energy enters through its square root. -/
theorem l6_ball_bound_of_enstrophy_bound
    {u : ParabolicPoint → Vec3} {χ : Vec3 → ℝ} {U : Set Vec3} {ρ Mu tη a C' : ℝ}
    (hU : IsOpen U) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hsupp : tsupport χ ⊆ U) (hχ1 : ∀ x ∈ vec3Ball (0 : Vec3) ρ, χ x = 1)
    (hu : ∀ t ∈ Ioo tη 0, ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => u (x, t)) U)
    (hdiv : ∀ t ∈ Ioo tη 0, ∀ x ∈ U,
      ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => u (y, t) j) x (basisVec j) = 0)
    (hMu : ∀ t ∈ Ioo tη 0, ∀ x : Vec3, gradVec χ x ≠ 0 →
      ∑ i : Fin 3, (u (x, t) i) ^ 2 ≤ Mu ^ 2)
    (hC' : 0 ≤ C')
    (hY : ∀ t ∈ Ioo tη 0,
      (∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, (curlVec (fun y : Vec3 => u (y, t)) x i) ^ 2) + 1
        ≤ C' * (-t) ^ (-a)) :
    ∃ C'' : ℝ, 0 ≤ C'' ∧ ∀ t ∈ Ioo tη 0,
      (∫⁻ x in vec3Ball 0 ρ,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ)) ^ (1 / 6 : ℝ)
        ≤ ENNReal.ofReal (C'' * (-t) ^ (-(a / 2))) := by
  obtain ⟨Cs, hCs_pos, hCs⟩ := exists_sobolev_six_const
  obtain ⟨Cg, hCg⟩ : ∃ c : ℝ, c = 3 * Mu ^ 2 * ∫ x : Vec3, ∑ i : Fin 3, (gradVec χ x i) ^ 2 :=
    ⟨_, rfl⟩
  have hgrad_nonneg : 0 ≤ ∫ x : Vec3, ∑ i : Fin 3, (gradVec χ x i) ^ 2 :=
    integral_nonneg fun x => by positivity
  have hCg_nonneg : 0 ≤ Cg := by
    rw [hCg]
    exact mul_nonneg (by positivity) hgrad_nonneg
  have hK_nonneg : 0 ≤ 3 * ((2 + Cg) * C') := by
    have h1 : (0 : ℝ) ≤ 2 + Cg := by linarith only [hCg_nonneg]
    have h2 : 0 ≤ (2 + Cg) * C' := mul_nonneg h1 hC'
    linarith only [h2]
  refine ⟨3 * Cs * (3 * ((2 + Cg) * C')) ^ (1 / 2 : ℝ),
    mul_nonneg (by linarith only [hCs_pos]) (Real.rpow_nonneg hK_nonneg _), ?_⟩
  intro t ht
  have hneg : 0 < -t := neg_pos.mpr ht.2
  have hQnn : 0 ≤ (-t) ^ (-a) := Real.rpow_nonneg hneg.le _
  have helliptic := integral_sq_fderiv_smul_le χ (fun x : Vec3 => u (x, t)) U Mu hU hχ hχs hsupp
    (hu t ht) (hdiv t ht) (hMu t ht)
  rw [← hCg] at helliptic
  have hYt := hY t ht
  have hY0 : 0 ≤ ∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3,
      (curlVec (fun y : Vec3 => u (y, t)) x i) ^ 2 :=
    integral_nonneg fun x => by positivity
  have hmul := mul_le_mul_of_nonneg_left hYt (by linarith only [hCg_nonneg] : (0 : ℝ) ≤ 2 + Cg)
  have hD : (∫ x : Vec3, ∑ i : Fin 3, ∑ j : Fin 3,
        (fderiv ℝ (fun y : Vec3 => (χ y • u (y, t)) i) x (basisVec j)) ^ 2)
      ≤ (2 + Cg) * C' * (-t) ^ (-a) := by
    linarith only [helliptic, hmul, mul_nonneg hCg_nonneg hY0]
  obtain ⟨hwC, hwS⟩ := contDiff_smul_of_contDiffOn χ (fun x : Vec3 => u (x, t)) U hU hχ hχs hsupp
    (hu t ht)
  have heq : ∀ x ∈ vec3Ball (0 : Vec3) ρ, (fun x : Vec3 => χ x • u (x, t)) x = u (x, t) := by
    intro x hx
    change χ x • u (x, t) = u (x, t)
    rw [hχ1 x hx, one_smul]
  have hmain := lintegral_pow_six_euclideanNorm_le_of_gradient_bound hCs_pos hCs
    (v := fun x : Vec3 => u (x, t)) (w := fun x : Vec3 => χ x • u (x, t)) (ρ := ρ)
    (D := (2 + Cg) * C' * (-t) ^ (-a)) hwC hwS heq hD
  have hrewrite : 3 * Cs * (3 * ((2 + Cg) * C' * (-t) ^ (-a))) ^ (1 / 2 : ℝ)
      = 3 * Cs * (3 * ((2 + Cg) * C')) ^ (1 / 2 : ℝ) * (-t) ^ (-(a / 2)) := by
    have hfact : 3 * ((2 + Cg) * C' * (-t) ^ (-a))
        = 3 * ((2 + Cg) * C') * (-t) ^ (-a) := by ring
    have hexp : ((-t) ^ (-a)) ^ (1 / 2 : ℝ) = (-t) ^ (-(a / 2)) := by
      rw [← Real.rpow_mul hneg.le]
      congr 1
      ring
    rw [hfact, Real.mul_rpow hK_nonneg hQnn, hexp]
    ring
  rw [hrewrite] at hmain
  exact hmain

/-! ### The closure of `lem:aniso:closure` -/

/-- The closure step: with `η = 1 / (16 C_*)` the enstrophy bound of `closure_gronwall_bound`
yields exactly the parabolic smallness hypothesis of the Gustafson–Kang–Tsai criterion
`gktCriterion`.

The exponent bookkeeping is the point.  The enstrophy decays like `(-t)^(-C_* η)`, so the `L⁶`
norm decays like `(-t)^(-β)` with `β = C_* η / 2`.  The `L⁴_t L⁶_x` quantity of the criterion
raises this to the fourth power and integrates in time over `(-r², 0)`, which converges and
carries a positive power of `r` exactly when `4β < 1`.  With `η = 1 / (16 C_*)` one has
`C_* η = 1/16`, hence `β = 1/32` and `4β = 1/8 < 1`. -/
theorem closure_from_enstrophy_bound
    {u : ParabolicPoint → Vec3} {χ : Vec3 → ℝ} {U : Set Vec3} {ρ Mu tη Cstar η C' : ℝ}
    (hU : IsOpen U) (hρ : 0 < ρ) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχs : HasCompactSupport χ)
    (hsupp : tsupport χ ⊆ U) (hχ1 : ∀ x ∈ vec3Ball (0 : Vec3) ρ, χ x = 1)
    (hu : ∀ t ∈ Ioo tη 0, ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => u (x, t)) U)
    (hdiv : ∀ t ∈ Ioo tη 0, ∀ x ∈ U,
      ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => u (y, t) j) x (basisVec j) = 0)
    (hMu : ∀ t ∈ Ioo tη 0, ∀ x : Vec3, gradVec χ x ≠ 0 →
      ∑ i : Fin 3, (u (x, t) i) ^ 2 ≤ Mu ^ 2)
    (htη : tη < 0) (hCstar : 0 < Cstar) (hη : η = 1 / (16 * Cstar)) (hC' : 0 ≤ C')
    (hY : ∀ t ∈ Ioo tη 0,
      (∫ x : Vec3, χ x ^ 2 * ∑ i : Fin 3, (curlVec (fun y : Vec3 => u (y, t)) x i) ^ 2) + 1
        ≤ C' * (-t) ^ (-(Cstar * η))) :
    ∀ ε : ℝ, 0 < ε → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ r : ℝ, 0 < r → r < r₀ →
      ∫⁻ t in Ioo (-(r ^ 2)) 0,
        (∫⁻ x in vec3Ball 0 r, ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (6 : ℝ))
          ^ (2 / 3 : ℝ) ≤ ENNReal.ofReal ε := by
  obtain ⟨C'', hC''_nonneg, hbound⟩ :=
    l6_ball_bound_of_enstrophy_bound hU hχ hχs hsupp hχ1 hu hdiv hMu hC' hY
  have hCstar_ne : Cstar ≠ 0 := ne_of_gt hCstar
  have hprod : Cstar * η = 1 / 16 := by
    rw [hη]
    field_simp
  have hβ : 0 ≤ Cstar * η / 2 ∧ 4 * (Cstar * η / 2) < 1 := by
    rw [hprod]
    constructor <;> norm_num
  exact gkt_smallness_of_l6_bound hρ hC''_nonneg hβ htη hbound

end CIV
