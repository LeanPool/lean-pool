/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.GlobalPotentials
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.HolomorphicDDC
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.SmoothPshHessian
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.BTTruncations
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PshRadialConvolution
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PshRadialRegularization
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.BallRotation
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# General holomorphic pullback of singular potentials

Smooth PSH pullback is proved below from the genuine `ddᶜ` naturality theorem.
The original first-order holomorphicity hypothesis is enough: on each tested
affine disc it becomes a one-variable holomorphic map and is therefore smooth.
The sole remaining analytic input for the extended-real theorem is existence
of pointwise decreasing radial smooth PSH regularizations. The quasi-PSH
consequence then transports an existing local decomposition. Neither statement
preserves nondegeneracy: a holomorphic image may lie entirely in a pole set.
This is not a trace construction.
-/

@[expose] public section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.HolomorphicPullback

open FirstPass
open FirstPass.MongeAmpere

variable {k n : ℕ}

/-- The explicit inner-product radial profile used for PSH regularization.
Unlike `ContDiffBump.toFun`, this definition does not pass through the
unspecified `someContDiffBumpBase`; it fixes the radial inner-product-space
construction itself. -/
noncomputable def explicitRadialRaw (R : ℝ) (hR : 0 < R) (j : ℕ)
    (x : ComplexModel n) : ℝ :=
  (ContDiffBumpBase.ofInnerProductSpace (ComplexModel n)).toFun 2
    ((shrinkingBump (E := ComplexModel n) R hR j).rIn⁻¹ • x)

/-- Successive raw profiles are exact dilates of one fixed radial function. -/
theorem explicitRadialRaw_scale (R : ℝ) (hR : 0 < R) (a b : ℕ)
    (x : ComplexModel n) :
    explicitRadialRaw R hR b x =
      explicitRadialRaw R hR a
        ((((b : ℝ) + 1) / ((a : ℝ) + 1)) • x) := by
  unfold explicitRadialRaw
  congr 1
  rw [smul_smul]
  congr 1
  simp only [shrinkingBump]
  field_simp

/-- The raw radial profile is smooth, directly from the explicit
inner-product-space bump base. -/
theorem explicitRadialRaw_contDiff (R : ℝ) (hR : 0 < R) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (explicitRadialRaw (n := n) R hR j) := by
  let B := ContDiffBumpBase.ofInnerProductSpace (ComplexModel n)
  have hB : ContDiff ℝ (⊤ : ℕ∞) (B.toFun 2) := by
    rw [contDiff_iff_contDiffAt]
    intro x
    have hwithin := B.smooth (2, x) ⟨by norm_num, mem_univ x⟩
    have hunc := hwithin.contDiffAt
      ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨by norm_num, mem_univ x⟩)
    change ContDiffAt ℝ (⊤ : ℕ∞)
      (Function.uncurry B.toFun ∘ fun y : ComplexModel n ↦ ((2 : ℝ), y)) x
    exact hunc.comp x (by fun_prop)
  have hscale : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : ComplexModel n ↦
        (shrinkingBump (E := ComplexModel n) R hR j).rIn⁻¹ • x) := by
    fun_prop
  change ContDiff ℝ (⊤ : ℕ∞) (B.toFun 2 ∘ fun x : ComplexModel n ↦
    (shrinkingBump (E := ComplexModel n) R hR j).rIn⁻¹ • x)
  exact hB.comp hscale

/-- The explicit raw profile takes values in `[0,1]`. -/
theorem explicitRadialRaw_mem_Icc (R : ℝ) (hR : 0 < R) (j : ℕ)
    (x : ComplexModel n) : explicitRadialRaw R hR j x ∈ Set.Icc (0 : ℝ) 1 := by
  exact (ContDiffBumpBase.ofInnerProductSpace (ComplexModel n)).mem_Icc 2 _

theorem explicitRadialRaw_nonneg (R : ℝ) (hR : 0 < R) (j : ℕ)
    (x : ComplexModel n) : 0 ≤ explicitRadialRaw R hR j x :=
   (explicitRadialRaw_mem_Icc R hR j x).1

theorem explicitRadialRaw_le_one (R : ℝ) (hR : 0 < R) (j : ℕ)
    (x : ComplexModel n) : explicitRadialRaw R hR j x ≤ 1 :=
  (explicitRadialRaw_mem_Icc R hR j x).2

/-- The support of the raw profile is exactly the ball with the advertised
outer radius. -/
theorem explicitRadialRaw_support (R : ℝ) (hR : 0 < R) (j : ℕ) :
    Function.support (explicitRadialRaw (n := n) R hR j) =
      ball 0 (R / ((j : ℝ) + 1)) := by
  let φ : ContDiffBump (0 : ComplexModel n) := shrinkingBump R hR j
  ext x
  change (ContDiffBumpBase.ofInnerProductSpace (ComplexModel n)).toFun 2
      (φ.rIn⁻¹ • x) ≠ 0 ↔ x ∈ ball 0 (R / ((j : ℝ) + 1))
  rw [← Function.mem_support,
    (ContDiffBumpBase.ofInnerProductSpace (ComplexModel n)).support 2 (by norm_num)]
  simp only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_of_pos φ.rIn_pos]
  rw [inv_mul_lt_iff₀ φ.rIn_pos]
  have hratio := shrinkingBump_radius_ratio (E := ComplexModel n) R hR j
  change ‖x‖ < φ.rIn * 2 ↔ _
  rw [mul_comm φ.rIn 2, ← hratio]
  rfl

theorem explicitRadialRaw_tsupport (R : ℝ) (hR : 0 < R) (j : ℕ) :
    tsupport (explicitRadialRaw (n := n) R hR j) =
      closedBall 0 (R / ((j : ℝ) + 1)) := by
  rw [tsupport, explicitRadialRaw_support R hR j,
    closure_ball _ (by positivity : R / ((j : ℝ) + 1) ≠ 0)]

theorem explicitRadialRaw_hasCompactSupport (R : ℝ) (hR : 0 < R) (j : ℕ) :
    HasCompactSupport (explicitRadialRaw (n := n) R hR j) := by
  rw [HasCompactSupport, explicitRadialRaw_tsupport R hR j]
  exact isCompact_closedBall _ _

section RadialNormalization

/-- The explicit radial profile normalized against an arbitrary additive Haar
measure on the standard complex model. -/
noncomputable def coordinateRadialKernel
    (ν : Measure (ComplexModel n)) (R : ℝ) (hR : 0 < R) (j : ℕ)
    (x : ComplexModel n) : ℝ :=
  explicitRadialRaw R hR j x /
    ∫ y : ComplexModel n, explicitRadialRaw R hR j y ∂ν

variable (ν : Measure (ComplexModel n)) [ν.IsAddHaarMeasure]

theorem explicitRadialRaw_integrable_haar (R : ℝ) (hR : 0 < R) (j : ℕ) :
    Integrable (explicitRadialRaw (n := n) R hR j) ν :=
  (explicitRadialRaw_contDiff R hR j).continuous.integrable_of_hasCompactSupport
    (explicitRadialRaw_hasCompactSupport R hR j)

theorem explicitRadialRaw_integral_pos_haar (R : ℝ) (hR : 0 < R) (j : ℕ) :
    0 < ∫ x : ComplexModel n, explicitRadialRaw R hR j x ∂ν := by
  refine (integral_pos_iff_support_of_nonneg
    (explicitRadialRaw_nonneg R hR j)
    (explicitRadialRaw_integrable_haar ν R hR j)).mpr ?_
  rw [explicitRadialRaw_support R hR j]
  exact measure_ball_pos ν 0 (by positivity)

omit [ν.IsAddHaarMeasure] in
theorem coordinateRadialKernel_contDiff (R : ℝ) (hR : 0 < R) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateRadialKernel ν R hR j) :=
  (explicitRadialRaw_contDiff R hR j).div_const _

theorem coordinateRadialKernel_nonneg (R : ℝ) (hR : 0 < R) (j : ℕ)
    (x : ComplexModel n) : 0 ≤ coordinateRadialKernel ν R hR j x :=
  div_nonneg (explicitRadialRaw_nonneg R hR j x)
    (explicitRadialRaw_integral_pos_haar ν R hR j).le

theorem coordinateRadialKernel_integral_one (R : ℝ) (hR : 0 < R) (j : ℕ) :
    ∫ x : ComplexModel n, coordinateRadialKernel ν R hR j x ∂ν = 1 := by
  simp_rw [coordinateRadialKernel, div_eq_mul_inv,
    mul_comm (explicitRadialRaw R hR j _), ← smul_eq_mul, integral_smul]
  exact inv_mul_cancel₀ (explicitRadialRaw_integral_pos_haar ν R hR j).ne'

theorem coordinateRadialKernel_support (R : ℝ) (hR : 0 < R) (j : ℕ) :
    Function.support (coordinateRadialKernel ν R hR j) =
      ball 0 (R / ((j : ℝ) + 1)) := by
  have hpos := explicitRadialRaw_integral_pos_haar (n := n) ν R hR j
  change Function.support (fun x : ComplexModel n ↦
    explicitRadialRaw R hR j x /
      ∫ y : ComplexModel n, explicitRadialRaw R hR j y ∂ν) = _
  rw [Function.support_div, Function.support_const hpos.ne', inter_univ,
    explicitRadialRaw_support R hR j]

theorem coordinateRadialKernel_tsupport (R : ℝ) (hR : 0 < R) (j : ℕ) :
    tsupport (coordinateRadialKernel ν R hR j) =
      closedBall 0 (R / ((j : ℝ) + 1)) := by
  rw [tsupport, coordinateRadialKernel_support ν R hR j,
    closure_ball _ (by positivity : R / ((j : ℝ) + 1) ≠ 0)]

theorem coordinateRadialKernel_hasCompactSupport
    (R : ℝ) (hR : 0 < R) (j : ℕ) :
    HasCompactSupport (coordinateRadialKernel ν R hR j) := by
  rw [HasCompactSupport, coordinateRadialKernel_tsupport ν R hR j]
  exact isCompact_closedBall _ _

theorem coordinateRadialKernel_integrable (R : ℝ) (hR : 0 < R) (j : ℕ) :
    Integrable (coordinateRadialKernel ν R hR j) ν :=
  (coordinateRadialKernel_contDiff ν R hR j).continuous.integrable_of_hasCompactSupport
    (coordinateRadialKernel_hasCompactSupport ν R hR j)

theorem explicitRadialRaw_unitary (R : ℝ) (hR : 0 < R) (j : ℕ)
    (a : ℂ) (ha : ‖a‖ = 1) (x : ComplexModel n) :
    explicitRadialRaw R hR j (a • x) = explicitRadialRaw R hR j x := by
  simp [explicitRadialRaw, ContDiffBumpBase.ofInnerProductSpace, norm_smul, ha]

omit [ν.IsAddHaarMeasure] in
theorem coordinateRadialKernel_unitary (R : ℝ) (hR : 0 < R) (j : ℕ)
    (a : ℂ) (ha : ‖a‖ = 1) (x : ComplexModel n) :
    coordinateRadialKernel ν R hR j (a • x) =
      coordinateRadialKernel ν R hR j x := by
  rw [coordinateRadialKernel, coordinateRadialKernel,
    explicitRadialRaw_unitary R hR j a ha x]

theorem coordinateRadialKernel_scale (R : ℝ) (hR : 0 < R) (a b : ℕ)
    (x : ComplexModel n) :
    coordinateRadialKernel ν R hR b x =
      (((b : ℝ) + 1) / ((a : ℝ) + 1)) ^
          Module.finrank ℝ (ComplexModel n) *
        coordinateRadialKernel ν R hR a
          ((((b : ℝ) + 1) / ((a : ℝ) + 1)) • x) := by
  let q : ℝ := ((b : ℝ) + 1) / ((a : ℝ) + 1)
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hqpow : q ^ Module.finrank ℝ (ComplexModel n) ≠ 0 :=
    pow_ne_zero _ hq.ne'
  have hint :
      (∫ y : ComplexModel n, explicitRadialRaw R hR b y ∂ν) =
        (q ^ Module.finrank ℝ (ComplexModel n))⁻¹ *
          ∫ y : ComplexModel n, explicitRadialRaw R hR a y ∂ν := by
    rw [show (fun y : ComplexModel n ↦ explicitRadialRaw R hR b y) =
        fun y ↦ explicitRadialRaw R hR a (q • y) by
      funext y
      exact explicitRadialRaw_scale R hR a b y]
    simpa only [smul_eq_mul] using
      (Measure.integral_comp_smul_of_nonneg ν
        (explicitRadialRaw (n := n) R hR a) q (hR := hq.le))
  rw [coordinateRadialKernel, coordinateRadialKernel,
    explicitRadialRaw_scale R hR a b, hint]
  dsimp [q]
  field_simp [hqpow, (explicitRadialRaw_integral_pos_haar (n := n) ν R hR a).ne']

end RadialNormalization

/-- The explicit radial profile normalized against standard volume. -/
noncomputable def explicitRadialKernel (R : ℝ) (hR : 0 < R) (j : ℕ)
    (x : ComplexModel n) : ℝ :=
  coordinateRadialKernel volume R hR j x

theorem explicitRadialRaw_integrable (R : ℝ) (hR : 0 < R) (j : ℕ) :
    Integrable (explicitRadialRaw (n := n) R hR j) volume :=
  explicitRadialRaw_integrable_haar volume R hR j

theorem explicitRadialRaw_integral_pos (R : ℝ) (hR : 0 < R) (j : ℕ) :
    0 < ∫ x : ComplexModel n, explicitRadialRaw R hR j x :=
  explicitRadialRaw_integral_pos_haar volume R hR j

theorem explicitRadialKernel_contDiff (R : ℝ) (hR : 0 < R) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (explicitRadialKernel (n := n) R hR j) :=
  coordinateRadialKernel_contDiff volume R hR j

theorem explicitRadialKernel_nonneg (R : ℝ) (hR : 0 < R) (j : ℕ)
    (x : ComplexModel n) : 0 ≤ explicitRadialKernel R hR j x :=
  coordinateRadialKernel_nonneg volume R hR j x

theorem explicitRadialKernel_integral_one (R : ℝ) (hR : 0 < R) (j : ℕ) :
    ∫ x : ComplexModel n, explicitRadialKernel R hR j x = 1 :=
  coordinateRadialKernel_integral_one volume R hR j

/-- Successive normalized kernels are exact dilates, including in complex
dimension zero. -/
theorem explicitRadialKernel_scale (R : ℝ) (hR : 0 < R) (a b : ℕ)
    (x : ComplexModel n) :
    explicitRadialKernel R hR b x =
      (((b : ℝ) + 1) / ((a : ℝ) + 1)) ^
          Module.finrank ℝ (ComplexModel n) *
        explicitRadialKernel R hR a
          ((((b : ℝ) + 1) / ((a : ℝ) + 1)) • x) :=
  coordinateRadialKernel_scale volume R hR a b x

theorem explicitRadialKernel_tsupport (R : ℝ) (hR : 0 < R) (j : ℕ) :
    tsupport (explicitRadialKernel (n := n) R hR j) =
      closedBall 0 (R / ((j : ℝ) + 1)) :=
  coordinateRadialKernel_tsupport volume R hR j

theorem explicitRadialKernel_hasCompactSupport (R : ℝ) (hR : 0 < R) (j : ℕ) :
    HasCompactSupport (explicitRadialKernel (n := n) R hR j) :=
  coordinateRadialKernel_hasCompactSupport volume R hR j

/-- The explicit kernel is invariant under scalar unitary rotations.  This is
the radial identity that the abstract `ContDiffBump` API does not expose. -/
theorem explicitRadialKernel_unitary (R : ℝ) (hR : 0 < R) (j : ℕ)
    (a : ℂ) (ha : ‖a‖ = 1) (x : ComplexModel n) :
    explicitRadialKernel R hR j (a • x) =
      explicitRadialKernel R hR j x :=
  coordinateRadialKernel_unitary volume R hR j a ha x

/-- The explicit raw profile is one on its inner closed ball. -/
theorem explicitRadialRaw_eq_one_of_mem_closedBall
    (R : ℝ) (hR : 0 < R) (j : ℕ) (x : ComplexModel n)
    (hx : x ∈ closedBall 0
      (shrinkingBump (E := ComplexModel n) R hR j).rIn) :
    explicitRadialRaw R hR j x = 1 := by
  apply (ContDiffBumpBase.ofInnerProductSpace (ComplexModel n)).eq_one 2 (by norm_num)
  change ‖(shrinkingBump (E := ComplexModel n) R hR j).rIn⁻¹ • x‖ ≤ 1
  rw [norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_pos (shrinkingBump (E := ComplexModel n) R hR j).rIn_pos]
  have hx' : ‖x‖ ≤ (shrinkingBump (E := ComplexModel n) R hR j).rIn := by
    simpa only [mem_closedBall, dist_zero_right] using hx
  simpa only [div_eq_inv_mul] using
    ((div_le_one (shrinkingBump (E := ComplexModel n) R hR j).rIn_pos).2 hx')

/-- The integral of the raw profile dominates the volume of its inner ball. -/
theorem measure_closedBall_le_explicitRadialRaw_integral
    (R : ℝ) (hR : 0 < R) (j : ℕ) :
    volume.real (closedBall (0 : ComplexModel n)
      (shrinkingBump (E := ComplexModel n) R hR j).rIn) ≤
      ∫ x : ComplexModel n, explicitRadialRaw R hR j x := by
  calc
    volume.real (closedBall (0 : ComplexModel n)
        (shrinkingBump (E := ComplexModel n) R hR j).rIn) =
        ∫ _x : ComplexModel n in closedBall 0
          (shrinkingBump (E := ComplexModel n) R hR j).rIn, 1 ∂volume := by simp
    _ = ∫ x : ComplexModel n in closedBall 0
          (shrinkingBump (E := ComplexModel n) R hR j).rIn,
          explicitRadialRaw R hR j x ∂volume :=
      setIntegral_congr_fun measurableSet_closedBall
        (fun x hx ↦ (explicitRadialRaw_eq_one_of_mem_closedBall R hR j x hx).symm)
    _ ≤ ∫ x : ComplexModel n, explicitRadialRaw R hR j x ∂volume :=
      setIntegral_le_integral (explicitRadialRaw_integrable R hR j)
        (Eventually.of_forall (explicitRadialRaw_nonneg R hR j))

/-- The normalized explicit kernel has the scale-invariant bound required by
the Lebesgue differentiation theorem. -/
theorem explicitRadialKernel_le_div_measure_closedBall
    (R : ℝ) (hR : 0 < R) (j : ℕ) (x : ComplexModel n) :
    explicitRadialKernel R hR j x ≤
      2 ^ Module.finrank ℝ (ComplexModel n) /
        volume.real (closedBall (0 : ComplexModel n)
          (shrinkingBump (E := ComplexModel n) R hR j).rOut) := by
  let φ : ContDiffBump (0 : ComplexModel n) := shrinkingBump R hR j
  have htwo : (0 : ℝ) < 2 := by norm_num
  have hmeasure :
      volume.real (closedBall (0 : ComplexModel n) φ.rOut) /
          2 ^ Module.finrank ℝ (ComplexModel n) ≤
        ∫ y : ComplexModel n, explicitRadialRaw R hR j y := by
    apply le_trans _ (measure_closedBall_le_explicitRadialRaw_integral R hR j)
    rw [div_le_iff₀ (pow_pos htwo _),
      Measure.addHaar_real_closedBall' volume _ φ.rIn_pos.le,
      Measure.addHaar_real_closedBall' volume _ φ.rOut_pos.le,
      mul_assoc, mul_comm _ (2 ^ Module.finrank ℝ (ComplexModel n)), ← mul_assoc,
      ← mul_pow, mul_comm _ 2]
    gcongr
    · exact φ.rOut_pos.le
    · exact (shrinkingBump_radius_ratio (E := ComplexModel n) R hR j).le
  have hraw : explicitRadialRaw R hR j x /
        (∫ y : ComplexModel n, explicitRadialRaw R hR j y) ≤
      1 / (∫ y : ComplexModel n, explicitRadialRaw R hR j y) := by
    gcongr
    · exact (explicitRadialRaw_integral_pos R hR j).le
    · exact explicitRadialRaw_le_one R hR j x
  rw [explicitRadialKernel]
  apply hraw.trans
  rw [div_le_div_iff₀ (explicitRadialRaw_integral_pos R hR j), one_mul,
    ← div_le_iff₀' (pow_pos htwo _)]
  · exact hmeasure
  · exact ENNReal.toReal_pos
      (measure_closedBall_pos volume (0 : ComplexModel n) φ.rOut_pos).ne'
      measure_closedBall_lt_top.ne

/-- Translating the explicit kernel translates its support ball. -/
theorem tsupport_explicitRadialKernel_translate_subset
    (R : ℝ) (hR : 0 < R) (j : ℕ) (z : ComplexModel n) :
    tsupport (fun x : ComplexModel n ↦ explicitRadialKernel R hR j (x - z)) ⊆
      closedBall z (shrinkingBump (E := ComplexModel n) R hR j).rOut := by
  apply closure_minimal _ isClosed_closedBall
  intro x hx
  have hx' : x - z ∈ tsupport (explicitRadialKernel (n := n) R hR j) :=
    subset_closure hx
  rw [explicitRadialKernel_tsupport R hR j] at hx'
  simpa only [mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero, shrinkingBump]
    using hx'

theorem explicitRadialKernel_neg (R : ℝ) (hR : 0 < R) (j : ℕ)
    (x : ComplexModel n) :
    explicitRadialKernel R hR j (-x) = explicitRadialKernel R hR j x := by
  simpa using explicitRadialKernel_unitary R hR j (-1 : ℂ) (by norm_num) x

/-- After translating the center, changing from the `b`-th explicit kernel to
the `a`-th kernel is exactly inverse dilation of the sampled density. -/
theorem translationPairing_explicitRadialKernel_scale
    (g : ComplexModel n → ℝ) (R : ℝ) (hR : 0 < R) (a b : ℕ)
    (z : ComplexModel n) :
    translationPairing volume g (explicitRadialKernel R hR b) z =
      ∫ y : ComplexModel n,
        g (z + ((((b : ℝ) + 1) / ((a : ℝ) + 1))⁻¹ • y)) *
          explicitRadialKernel R hR a y ∂volume := by
  let q : ℝ := ((b : ℝ) + 1) / ((a : ℝ) + 1)
  let d : ℕ := Module.finrank ℝ (ComplexModel n)
  have hq : 0 < q := by
    dsimp [q]
    positivity
  have hqpow : q ^ d ≠ 0 := pow_ne_zero _ hq.ne'
  let f : ComplexModel n → ℝ := fun y ↦
    g (z + q⁻¹ • y) * explicitRadialKernel R hR a y
  have hscale := Measure.integral_comp_smul_of_nonneg volume f q (hR := hq.le)
  calc
    translationPairing volume g (explicitRadialKernel R hR b) z =
        ∫ x : ComplexModel n,
          g (z + x) * explicitRadialKernel R hR b x ∂volume := by
      unfold translationPairing
      rw [← integral_add_left_eq_self
        (fun x : ComplexModel n ↦
          g x * explicitRadialKernel R hR b (x - z)) z]
      simp only [add_sub_cancel_left]
    _ = ∫ x : ComplexModel n,
          q ^ d * (g (z + x) * explicitRadialKernel R hR a (q • x)) ∂volume := by
      apply integral_congr_ae
      filter_upwards with x
      rw [explicitRadialKernel_scale R hR a b]
      dsimp [q, d]
      ring
    _ = q ^ d * ∫ x : ComplexModel n,
          g (z + x) * explicitRadialKernel R hR a (q • x) ∂volume := by
      rw [integral_const_mul]
    _ = q ^ d * ∫ x : ComplexModel n, f (q • x) ∂volume := by
      congr 1
      apply integral_congr_ae
      filter_upwards with x
      dsimp [f]
      rw [smul_smul, inv_mul_cancel₀ hq.ne', one_smul]
    _ = q ^ d * ((q ^ d)⁻¹ * ∫ y : ComplexModel n, f y ∂volume) := by
      rw [hscale]
      rfl
    _ = ∫ y : ComplexModel n, f y ∂volume := by
      rw [← mul_assoc, mul_inv_cancel₀ hqpow, one_mul]
    _ = ∫ y : ComplexModel n,
          g (z + ((((b : ℝ) + 1) / ((a : ℝ) + 1))⁻¹ • y)) *
            explicitRadialKernel R hR a y ∂volume := by
      rfl

/-- The circle averages along an affine complex line of a smooth function
plurisubharmonic on a neighborhood of the unit disc are monotone in the
radius. -/
theorem circleAverage_affineLine_mono_of_smooth_pshOn
    {p : ComplexModel n → ℝ}
    (hpSmooth : ContDiff ℝ ∞ p)
    {Ω : Set (ComplexModel n)} (hΩ : IsOpen Ω)
    (hpPsh : PlurisubharmonicOn (fun x ↦ (p x : EReal)) Ω)
    (z y : ComplexModel n)
    (hlineΩ : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • y ∈ Ω)
    {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s ≤ 1) :
    Real.circleAverage (fun ζ : ℂ ↦ p (z + ζ • y)) 0 r ≤
      Real.circleAverage (fun ζ : ℂ ↦ p (z + ζ • y)) 0 s := by
  have hp2 : ContDiff ℝ 2 p := hpSmooth.of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hline : ContDiff ℝ 2 (fun ζ : ℂ ↦ p (z + ζ • y)) :=
    hp2.comp (contDiff_const.add (complexLineLinear y).contDiff)
  have hΔ : ∀ ζ ∈ closedBall (0 : ℂ) 1,
      0 ≤ Laplacian.laplacian (fun w : ℂ ↦ p (z + w • y)) ζ := by
    intro ζ hζ
    apply (laplacian_complexLine_nonneg_iff hp2 z y ζ).mpr
    exact FirstPass.leviForm_nonneg_of_contDiffOn_plurisubharmonicOn
      (U := ⟨Ω, hΩ⟩) hpSmooth.contDiffOn hpPsh
      (hlineΩ ζ (by simpa only [mem_closedBall, dist_zero_right] using hζ)) y
  exact (circleAverage_monotoneOn_of_laplacian_nonneg hline 0 (by norm_num) hΔ)
    ⟨hr, hrs.trans hs⟩ ⟨hr.trans hrs, hs⟩ hrs

/-- The circle averages along every affine complex line of a globally smooth
plurisubharmonic function are monotone in the radius. -/
theorem circleAverage_affineLine_mono_of_smooth_psh
    {p : ComplexModel n → ℝ}
    (hpSmooth : ContDiff ℝ ∞ p)
    (hpPsh : PlurisubharmonicOn (fun x ↦ (p x : EReal)) Set.univ)
    (z y : ComplexModel n) {r s : ℝ}
    (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s ≤ 1) :
    Real.circleAverage (fun ζ : ℂ ↦ p (z + ζ • y)) 0 r ≤
      Real.circleAverage (fun ζ : ℂ ↦ p (z + ζ • y)) 0 s := by
  exact circleAverage_affineLine_mono_of_smooth_pshOn hpSmooth isOpen_univ hpPsh z y
    (fun _ _ ↦ mem_univ _) hr hrs hs

/-- A continuous affine-circle integrand times a continuous compactly
supported density is integrable on one period times the ambient space.  This
is the product-integrability input for the radial Fubini argument. -/
theorem integrable_circleMap_smul_mul_of_continuous_hasCompactSupport
    {p κ : ComplexModel n → ℝ}
    (hp : Continuous p) (hκ : Continuous κ) (hκc : HasCompactSupport κ)
    (z : ComplexModel n) (r : ℝ) :
    Integrable
      (fun q : ℝ × ComplexModel n ↦
        p (z + circleMap 0 r q.1 • q.2) * κ q.2)
      ((volume.restrict (uIoc 0 (2 * Real.pi))).prod volume) := by
  let F : ℝ × ComplexModel n → ℝ := fun q ↦
    p (z + circleMap 0 r q.1 • q.2) * κ q.2
  let K : Set (ℝ × ComplexModel n) :=
    uIcc 0 (2 * Real.pi) ×ˢ tsupport κ
  have hF : Continuous F := by
    dsimp [F]
    fun_prop
  have hK : IsCompact K := isCompact_uIcc.prod hκc
  have hFI : IntegrableOn F K (volume.prod volume) :=
    hF.continuousOn.integrableOn_compact hK
  have hKind : MeasurableSet K := hK.measurableSet
  have hG : Integrable (K.indicator F) (volume.prod volume) :=
    hFI.integrable_indicator hKind
  rw [Measure.restrict_prod_eq_prod_univ]
  refine (hG.mono_measure Measure.restrict_le_self).congr ?_
  filter_upwards [ae_restrict_mem (μ := volume.prod volume)
    (measurableSet_uIoc.prod MeasurableSet.univ)] with q hq
  by_cases hy : q.2 ∈ tsupport κ
  · rw [indicator_of_mem]
    exact ⟨uIoc_subset_uIcc hq.1, hy⟩
  · have hκ0 : κ q.2 = 0 := by
      by_contra hne
      exact hy (subset_closure hne)
    rw [Set.indicator_of_notMem]
    · rw [hκ0, mul_zero]
    · exact fun hqK ↦ hy hqK.2

/-- Averaging a continuous density along affine complex circles and then
against a compactly supported radial kernel equals the radial pairing at the
corresponding real scale. -/
theorem integral_circleAverage_mul_eq_smul
    {p κ : ComplexModel n → ℝ}
    (hp : Continuous p) (hκ : Continuous κ) (hκc : HasCompactSupport κ)
    (hκrad : ∀ (a : ℂ), ‖a‖ = 1 → ∀ y, κ (a • y) = κ y)
    (z : ComplexModel n) (r : ℝ) :
    ∫ y : ComplexModel n,
        Real.circleAverage (fun ζ : ℂ ↦ p (z + ζ • y)) 0 r * κ y ∂volume =
      ∫ y : ComplexModel n, p (z + (r : ℂ) • y) * κ y ∂volume := by
  let F : ℝ → ComplexModel n → ℝ := fun t y ↦
    p (z + circleMap 0 r t • y) * κ y
  let I : ℝ := ∫ y : ComplexModel n,
    p (z + (r : ℂ) • y) * κ y ∂volume
  have hF : Integrable (Function.uncurry F)
      ((volume.restrict (uIoc 0 (2 * Real.pi))).prod volume) := by
    exact integrable_circleMap_smul_mul_of_continuous_hasCompactSupport
      hp hκ hκc z r
  have hinner : ∀ t : ℝ, ∫ y : ComplexModel n, F t y ∂volume = I := by
    intro t
    let a : ℂ := circleMap 0 1 t
    have ha : ‖a‖ = 1 := by
      dsimp [a]
      simp [norm_circleMap_zero]
    have hrot := (measurePreserving_smul_of_norm_eq_one volume a ha).integral_comp
      (complexRotation a ha).toHomeomorph.measurableEmbedding
      (fun y : ComplexModel n ↦ p (z + (r : ℂ) • y) * κ y)
    simp_rw [hκrad a ha] at hrot
    dsimp [F, I]
    simpa [a, circleMap, smul_smul] using hrot
  simp_rw [Real.circleAverage_def]
  change (∫ y : ComplexModel n,
      ((2 * Real.pi)⁻¹ * (∫ t in 0..2 * Real.pi,
        p (z + circleMap 0 r t • y))) * κ y ∂volume) = I
  calc
    (∫ y : ComplexModel n,
        ((2 * Real.pi)⁻¹ * (∫ t in 0..2 * Real.pi,
          p (z + circleMap 0 r t • y))) * κ y ∂volume) =
        (2 * Real.pi)⁻¹ * ∫ y : ComplexModel n,
          (∫ t in 0..2 * Real.pi,
            p (z + circleMap 0 r t • y)) * κ y ∂volume := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      ring
    _ = (2 * Real.pi)⁻¹ * ∫ y : ComplexModel n,
          (∫ t in 0..2 * Real.pi, F t y) ∂volume := by
      congr 1
      apply integral_congr_ae
      filter_upwards with y
      dsimp [F]
      rw [intervalIntegral.integral_mul_const]
    _ = (2 * Real.pi)⁻¹ *
          ∫ t in 0..2 * Real.pi, ∫ y : ComplexModel n, F t y ∂volume := by
      rw [intervalIntegral_integral_swap hF]
    _ = (2 * Real.pi)⁻¹ * ∫ _t in 0..2 * Real.pi, I := by
      congr 1
      apply intervalIntegral.integral_congr
      intro t _
      exact hinner t
    _ = (2 * Real.pi)⁻¹ * ((2 * Real.pi) * I) := by
      rw [intervalIntegral.integral_const]
      ring
    _ = I := by
      field_simp [Real.pi_ne_zero]

/-- For a globally smooth function which is PSH on a neighborhood of every
tested affine unit disc, integration against a nonnegative compactly supported
radial kernel is monotone in the real dilation radius. -/
theorem integral_add_real_smul_mul_mono_of_smooth_pshOn
    {p κ : ComplexModel n → ℝ}
    (hpSmooth : ContDiff ℝ ∞ p)
    {Ω : Set (ComplexModel n)} (hΩ : IsOpen Ω)
    (hpPsh : PlurisubharmonicOn (fun x ↦ (p x : EReal)) Ω)
    (hκ : Continuous κ) (hκc : HasCompactSupport κ)
    (hκnonneg : ∀ y, 0 ≤ κ y)
    (hκrad : ∀ (a : ℂ), ‖a‖ = 1 → ∀ y, κ (a • y) = κ y)
    (z : ComplexModel n)
    (hlineΩ : ∀ y ∈ tsupport κ, ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • y ∈ Ω)
    {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hs : s ≤ 1) :
    (∫ y : ComplexModel n, p (z + (r : ℂ) • y) * κ y ∂volume) ≤
      ∫ y : ComplexModel n, p (z + (s : ℂ) • y) * κ y ∂volume := by
  rw [← integral_circleAverage_mul_eq_smul hpSmooth.continuous hκ hκc hκrad z r,
    ← integral_circleAverage_mul_eq_smul hpSmooth.continuous hκ hκc hκrad z s]
  have hmean_cont (t : ℝ) : Continuous (fun y : ComplexModel n ↦
      Real.circleAverage (fun ζ : ℂ ↦ p (z + ζ • y)) 0 t) := by
    unfold Real.circleAverage
    have hbase : Continuous (fun y : ComplexModel n ↦
        ∫ θ in 0..2 * Real.pi, p (z + circleMap 0 t θ • y)) := by
      apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      fun_prop
    change Continuous ((2 * Real.pi)⁻¹ • fun y : ComplexModel n ↦
      ∫ θ in 0..2 * Real.pi, p (z + circleMap 0 t θ • y))
    exact hbase.const_smul ((2 * Real.pi)⁻¹)
  have hint (t : ℝ) : Integrable (fun y : ComplexModel n ↦
      Real.circleAverage (fun ζ : ℂ ↦ p (z + ζ • y)) 0 t * κ y) volume :=
    ((hmean_cont t).mul hκ).integrable_of_hasCompactSupport hκc.mul_left
  apply integral_mono_ae (hint r) (hint s)
  filter_upwards with y
  by_cases hy : y ∈ tsupport κ
  · exact mul_le_mul_of_nonneg_right
      (circleAverage_affineLine_mono_of_smooth_pshOn hpSmooth hΩ hpPsh z y
        (hlineΩ y hy) hr hrs hs)
      (hκnonneg y)
  · have hκ0 : κ y = 0 := by
      by_contra hne
      exact hy (subset_closure hne)
    simp [hκ0]

/-- Almost-everywhere pointwise convergence survives precomposition by a
nondegenerate real dilation followed by translation.  This is the null-set
transport needed when applying dominated convergence to radial pairings. -/
theorem ae_tendsto_comp_add_real_smul
    {f : ℕ → ComplexModel n → ℝ} {g : ComplexModel n → ℝ}
    (h : ∀ᵐ x ∂volume,
      Tendsto (fun j ↦ f j x) atTop (𝓝 (g x)))
    (z : ComplexModel n) {r : ℝ} (hr : r ≠ 0) :
    ∀ᵐ y ∂volume,
      Tendsto (fun j ↦ f j (z + r • y)) atTop
        (𝓝 (g (z + r • y))) := by
  have hs : QuasiMeasurePreserving
      (fun y : ComplexModel n ↦ r • y) volume volume :=
    Measure.quasiMeasurePreserving_smul volume hr
  have ht : QuasiMeasurePreserving
      (fun y : ComplexModel n ↦ z + y) volume volume :=
    (measurePreserving_add_left volume z).quasiMeasurePreserving
  have haff : QuasiMeasurePreserving
      (fun y : ComplexModel n ↦ z + r • y) volume volume := by
    simpa only [Function.comp_def] using ht.comp hs
  exact haff.ae h

/-- The explicit radial kernels form an approximate identity for every locally
integrable density.  This is the Lebesgue differentiation part of the radial
system and does not use plurisubharmonicity. -/
theorem ae_tendsto_translationPairing_explicitRadialKernel
    {g : ComplexModel n → ℝ} (hg : LocallyIntegrable g volume)
    (R : ℝ) (hR : 0 < R) :
    ∀ᵐ z ∂volume,
      Tendsto (fun j ↦ translationPairing volume g
        (explicitRadialKernel R hR j) z) atTop (𝓝 (g z)) := by
  filter_upwards [(Besicovitch.vitaliFamily volume).ae_tendsto_average_norm_sub hg]
    with z hz
  have hr : Tendsto
      (fun j ↦ (shrinkingBump (E := ComplexModel n) R hR j).rOut)
      atTop (𝓝 0) := tendsto_shrinkingBump_rOut R hR
  have hr' : Tendsto
      (fun j ↦ (shrinkingBump (E := ComplexModel n) R hR j).rOut)
      atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hr, Eventually.of_forall
      (fun j ↦ (shrinkingBump (E := ComplexModel n) R hR j).rOut_pos)⟩
  have havg := (hz.comp (Besicovitch.tendsto_filterAt volume z)).comp hr'
  have hlim : Tendsto
      (fun j ↦ ∫ y : ComplexModel n,
        explicitRadialKernel R hR j (z - y) • g y ∂volume)
      atTop (𝓝 (g z)) := by
    apply tendsto_integral_smul_of_tendsto_average_norm_sub
      (2 ^ Module.finrank ℝ (ComplexModel n)) havg
    · filter_upwards with j
      exact hg.integrableOn_isCompact (isCompact_closedBall z _)
    · apply tendsto_const_nhds.congr
      intro j
      rw [← integral_neg_eq_self]
      simp only [sub_neg_eq_add, integral_add_left_eq_self,
        explicitRadialKernel_integral_one]
    · filter_upwards with j
      intro y hy
      have hy' : z - y ∈ tsupport (explicitRadialKernel (n := n) R hR j) :=
        subset_closure hy
      rw [explicitRadialKernel_tsupport R hR j] at hy'
      simpa only [mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero,
        shrinkingBump, norm_sub_rev] using hy'
    · filter_upwards with j
      intro y
      rw [abs_of_nonneg (explicitRadialKernel_nonneg R hR j (z - y)),
        Measure.addHaar_real_closedBall_center volume z]
      exact explicitRadialKernel_le_div_measure_closedBall R hR j (z - y)
  apply hlim.congr'
  filter_upwards with j
  unfold translationPairing
  apply integral_congr_ae
  filter_upwards with y
  simp only [smul_eq_mul]
  rw [mul_comm]
  congr 1
  rw [← explicitRadialKernel_neg R hR j (y - z), neg_sub]

/-- The sole remaining radial-analysis atom: radial averages of a locally
bounded PSH function decrease when their scale shrinks.  All kernel and
approximate-identity fields are proved separately. -/
theorem antitone_translationPairing_explicitRadialKernel_of_locallyBoundedPsh
    {Ω : Opens (ComplexModel n)} {p : ComplexModel n → ℝ}
    (hp : IsLocallyBoundedPshOn Ω p) {R : ℝ} (hR : 0 < R)
    {N K : Set (ComplexModel n)} (hKΩ : K ⊆ Ω)
    (hball : ∀ x ∈ N, closedBall x R ⊆ K) :
    ∀ z ∈ N, Antitone (fun j ↦ translationPairing volume (K.indicator p)
      (explicitRadialKernel R hR j) z) := by
  intro z hz a b hab
  let q : ℝ := ((b : ℝ) + 1) / ((a : ℝ) + 1)
  let r : ℝ := q⁻¹
  have hqpos : 0 < q := by
    dsimp [q]
    positivity
  have hqone : 1 ≤ q := by
    dsimp [q]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (a : ℝ) + 1)]
    simpa only [one_mul] using
      (show (a : ℝ) + 1 ≤ (b : ℝ) + 1 by exact_mod_cast Nat.add_le_add_right hab 1)
  have hrpos : 0 < r := inv_pos.mpr hqpos
  have hrle : r ≤ 1 := (inv_le_one₀ hqpos).mpr hqone
  have hScompact : IsCompact (closedBall z R) := isCompact_closedBall z R
  have hSΩ : closedBall z R ⊆ Ω := (hball z hz).trans hKΩ
  obtain ⟨U, K₀, f, C, hU, hSU, hUK₀, hK₀, hK₀Ω, hC,
      hfSmooth, _hfDisc, hfPsh, hfBound, hfAE⟩ :=
    FirstPass.MongeAmpere.exists_uniformlyBounded_smoothPsh_aeApproximation_on_compact
      hp hScompact hSΩ
  have hcomplexRealSmul (t : ℝ) (y : ComplexModel n) :
      (t : ℂ) • y = t • y := by
    rfl
  have hpointBall (t : ℝ) (ht : 0 ≤ t) (htone : t ≤ 1)
      {y : ComplexModel n}
      (hy : y ∈ tsupport (explicitRadialKernel (n := n) R hR a)) :
      z + t • y ∈ closedBall z R := by
    have hyR : y ∈ closedBall (0 : ComplexModel n) R := by
      rw [explicitRadialKernel_tsupport R hR a] at hy
      exact (closedBall_subset_closedBall
        (shrinkingBump_rOut_le (E := ComplexModel n) R hR a)) hy
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_nonneg ht]
    have hynorm : ‖y‖ ≤ R := by
      simpa only [mem_closedBall, dist_zero_right] using hyR
    calc
      t * ‖y‖ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right htone (norm_nonneg y)
      _ ≤ R := by simpa only [one_mul] using hynorm
  have hlineU : ∀ y ∈ tsupport (explicitRadialKernel (n := n) R hR a),
      ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • y ∈ U := by
    intro y hy ζ hζ
    apply hSU
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul]
    have hyR := hpointBall 1 zero_le_one le_rfl hy
    have hynorm : ‖y‖ ≤ R := by
      simpa only [one_smul, mem_closedBall, dist_eq_norm, add_sub_cancel_left]
        using hyR
    calc
      ‖ζ‖ * ‖y‖ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right hζ (norm_nonneg y)
      _ ≤ R := by simpa only [one_mul] using hynorm
  have hκcont : Continuous (explicitRadialKernel (n := n) R hR a) :=
    (explicitRadialKernel_contDiff R hR a).continuous
  have hκcompact : HasCompactSupport (explicitRadialKernel (n := n) R hR a) :=
    explicitRadialKernel_hasCompactSupport R hR a
  have hκintegrable : Integrable (explicitRadialKernel (n := n) R hR a) volume :=
    hκcont.integrable_of_hasCompactSupport hκcompact
  have hboundIntegrable : Integrable
      (fun y : ComplexModel n ↦ C * explicitRadialKernel R hR a y) volume :=
    hκintegrable.const_mul C
  have hDCT (t : ℝ) (ht : 0 < t) :
      Tendsto
        (fun j ↦ ∫ y : ComplexModel n,
          f j (z + t • y) * explicitRadialKernel R hR a y ∂volume)
        atTop
        (𝓝 (∫ y : ComplexModel n,
          K₀.indicator p (z + t • y) * explicitRadialKernel R hR a y ∂volume)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun y : ComplexModel n ↦ C * explicitRadialKernel R hR a y)
    · intro j
      exact (((hfSmooth j).continuous.comp (by fun_prop)).mul hκcont).aestronglyMeasurable
    · exact hboundIntegrable
    · intro j
      filter_upwards with y
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (explicitRadialKernel_nonneg R hR a y)]
      exact mul_le_mul_of_nonneg_right (hfBound j (z + t • y))
        (explicitRadialKernel_nonneg R hR a y)
    · filter_upwards [ae_tendsto_comp_add_real_smul hfAE z ht.ne'] with y hy
      exact hy.mul_const (explicitRadialKernel R hR a y)
  have hlocalCut (t : ℝ) (ht : 0 ≤ t) (htone : t ≤ 1) :
      (∫ y : ComplexModel n,
          K₀.indicator p (z + t • y) * explicitRadialKernel R hR a y ∂volume) =
        ∫ y : ComplexModel n,
          p (z + t • y) * explicitRadialKernel R hR a y ∂volume := by
    apply integral_congr_ae
    filter_upwards with y
    by_cases hy : y ∈ tsupport (explicitRadialKernel (n := n) R hR a)
    · rw [indicator_of_mem (hUK₀ (hSU (hpointBall t ht htone hy)))]
    · have hκzero : explicitRadialKernel R hR a y = 0 := by
        by_contra hne
        exact hy (subset_closure hne)
      simp only [hκzero, mul_zero]
  have hcut (t : ℝ) (ht : 0 ≤ t) (htone : t ≤ 1) :
      (∫ y : ComplexModel n,
          K.indicator p (z + t • y) * explicitRadialKernel R hR a y ∂volume) =
        ∫ y : ComplexModel n,
          p (z + t • y) * explicitRadialKernel R hR a y ∂volume := by
    apply integral_congr_ae
    filter_upwards with y
    by_cases hy : y ∈ tsupport (explicitRadialKernel (n := n) R hR a)
    · rw [indicator_of_mem (hball z hz (hpointBall t ht htone hy))]
    · have hκzero : explicitRadialKernel R hR a y = 0 := by
        by_contra hne
        exact hy (subset_closure hne)
      simp only [hκzero, mul_zero]
  have hlimr := hDCT r hrpos
  have hlimone := hDCT 1 one_pos
  rw [hlocalCut r hrpos.le hrle] at hlimr
  rw [hlocalCut 1 zero_le_one le_rfl] at hlimone
  have hmono :
      (∫ y : ComplexModel n,
          p (z + r • y) * explicitRadialKernel R hR a y ∂volume) ≤
        ∫ y : ComplexModel n,
          p (z + (1 : ℝ) • y) * explicitRadialKernel R hR a y ∂volume := by
    apply le_of_tendsto_of_tendsto' hlimr hlimone
    intro j
    have hj := integral_add_real_smul_mul_mono_of_smooth_pshOn
      (hfSmooth j) hU (hfPsh j) hκcont hκcompact
      (explicitRadialKernel_nonneg R hR a)
      (explicitRadialKernel_unitary R hR a) z hlineU hrpos.le hrle le_rfl
    simpa only [hcomplexRealSmul] using hj
  calc
    translationPairing volume (K.indicator p) (explicitRadialKernel R hR b) z =
        ∫ y : ComplexModel n,
          K.indicator p (z + r • y) * explicitRadialKernel R hR a y ∂volume := by
      simpa only [q, r] using
        translationPairing_explicitRadialKernel_scale
          (K.indicator p) R hR a b z
    _ = ∫ y : ComplexModel n,
          p (z + r • y) * explicitRadialKernel R hR a y ∂volume :=
      hcut r hrpos.le hrle
    _ ≤ ∫ y : ComplexModel n,
          p (z + (1 : ℝ) • y) * explicitRadialKernel R hR a y ∂volume := hmono
    _ = ∫ y : ComplexModel n,
          K.indicator p (z + (1 : ℝ) • y) * explicitRadialKernel R hR a y ∂volume :=
      (hcut 1 zero_le_one le_rfl).symm
    _ = translationPairing volume (K.indicator p)
          (explicitRadialKernel R hR a) z := by
      symm
      simpa only [div_self (by positivity : (a : ℝ) + 1 ≠ 0), inv_one,
        one_smul] using
        translationPairing_explicitRadialKernel_scale
          (K.indicator p) R hR a a z

/-- The explicit inner-product kernels, with all structure fields assembled.
The construction uses the preceding monotonicity atom and the proved Lebesgue
differentiation theorem. -/
theorem exists_explicitRadialConvolutionSystem_of_locallyBoundedPsh
    {Ω : Opens (ComplexModel n)} {p : ComplexModel n → ℝ}
    (hp : IsLocallyBoundedPshOn Ω p) {R : ℝ} (hR : 0 < R)
    {N K : Set (ComplexModel n)} (hN : IsOpen N)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hball : ∀ x ∈ N, closedBall x R ⊆ K) :
    ∃ S : RadialConvolutionSystem ⟨N, hN⟩ K p R,
      ∀ j x, S.kernel j x = explicitRadialKernel R hR j x := by
  have hNK : N ⊆ K := by
    intro z hz
    exact hball z hz (mem_closedBall_self hR.le)
  let hpL : LocallyIntegrableOn p Ω volume :=
    locallyIntegrableOn_of_plurisubharmonicOn_real hp.1
  have hg : LocallyIntegrable (K.indicator p) volume :=
    (integrable_indicator_of_locallyIntegrableOn_isCompact hpL hK hKΩ).locallyIntegrable
  have hae : ∀ᵐ z ∂volume.restrict N,
      Tendsto (fun j ↦ translationPairing volume (K.indicator p)
        (explicitRadialKernel R hR j) z) atTop (𝓝 (p z)) := by
    filter_upwards [ae_restrict_of_ae
      (ae_tendsto_translationPairing_explicitRadialKernel hg R hR),
      ae_restrict_mem hN.measurableSet] with z hzlim hzN
    simpa only [indicator_of_mem (hNK hzN)] using hzlim
  let S : RadialConvolutionSystem ⟨N, hN⟩ K p R :=
    { kernel := fun j ↦ explicitRadialKernel R hR j
      kernel_contDiff := fun j ↦ explicitRadialKernel_contDiff R hR j
      kernel_hasCompactSupport := fun j ↦ explicitRadialKernel_hasCompactSupport R hR j
      kernel_nonneg := fun j x ↦ explicitRadialKernel_nonneg R hR j x
      kernel_integral_one := fun j ↦ explicitRadialKernel_integral_one R hR j
      kernel_radial := fun j a ha x ↦ explicitRadialKernel_unitary R hR j a ha x
      kernel_tsupport := fun j ↦ by
        rw [explicitRadialKernel_tsupport R hR j]
      translated_tsupport := fun j z hz ↦ by
        exact (tsupport_explicitRadialKernel_translate_subset R hR j z).trans
          ((closedBall_subset_closedBall
            (shrinkingBump_rOut_le (E := ComplexModel n) R hR j)).trans
              (hball z hz))
      antitone_pairing :=
        antitone_translationPairing_explicitRadialKernel_of_locallyBoundedPsh
          hp hR hKΩ hball
      ae_tendsto_pairing := hae }
  exact ⟨S, fun _ _ ↦ rfl⟩

/-- An explicit radial convolution on a fixed compact neighborhood gives a decreasing
smooth approximation on the inner domain. -/
theorem isDecreasingApproximation_explicitRadialKernel
    {Ω A : Opens (ComplexModel n)} {p : ComplexModel n → ℝ}
    (hp : IsLocallyBoundedPshOn Ω p) {R : ℝ} (hR : 0 < R)
    {N K : Set (ComplexModel n)} (hN : IsOpen N) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hAN : (A : Set (ComplexModel n)) ⊆ N) (hAΩ : (A : Set (ComplexModel n)) ⊆ Ω)
    (hball : ∀ z ∈ N, Metric.closedBall z R ⊆ K) :
    IsDecreasingApproximation A p
      (fun j ↦ translationPairing volume (K.indicator p) (explicitRadialKernel R hR j)) := by
  let hpL : LocallyIntegrableOn p Ω volume :=
    locallyIntegrableOn_of_plurisubharmonicOn_real hp.1
  have hpLevi : HasNonnegativeDistributionalLevi
      (regularDistribution volume p hpL) :=
    hasNonnegativeDistributionalLevi_of_plurisubharmonicOn_real hp.1
  obtain ⟨S, hSkernel⟩ :=
    exists_explicitRadialConvolutionSystem_of_locallyBoundedPsh
      hp hR hN hK hKΩ hball
  let f : ℕ → ComplexModel n → ℝ := fun j ↦
    translationPairing volume (K.indicator p) (S.kernel j)
  have hg : LocallyIntegrable (K.indicator p) volume :=
    (integrable_indicator_of_locallyIntegrableOn_isCompact hpL hK hKΩ).locallyIntegrable
  have hfDisc (j : ℕ) : DiscPshOn (fun x ↦ (f j x : EReal)) N :=
    discPshOn_translationPairing_indicator hpL hpLevi
      (S.kernel_hasCompactSupport j) (S.kernel_contDiff j)
      (S.kernel_nonneg j) hK hKΩ (S.translated_tsupport j)
  have hfPsh (j : ℕ) : PlurisubharmonicOn (fun x ↦ (f j x : EReal)) A :=
    ((hfDisc j).plurisubharmonicOn hN).mono hAN
  have hfSmooth (j : ℕ) : IsSmoothPshOn A (f j) :=
    isSmoothPshOn_of_psh
      (contDiff_translationPairing hg (S.kernel_hasCompactSupport j)
        (S.kernel_contDiff j)).contDiffOn (hfPsh j)
  have hantiN : ∀ x ∈ N, Antitone (fun j ↦ f j x) := by
    intro x hx
    exact S.antitone_pairing x hx
  have hanti : ∀ x ∈ A, Antitone (fun j ↦ f j x) :=
    fun x hx ↦ hantiN x (hAN hx)
  have hae : ∀ᵐ x ∂volume.restrict (A : Set (ComplexModel n)),
      Tendsto (fun j ↦ f j x) atTop (𝓝 (p x)) := by
    have haeN := S.ae_tendsto_pairing
    change ∀ᵐ x ∂volume.restrict N,
      Tendsto (fun j ↦ f j x) atTop (𝓝 (p x)) at haeN
    exact ae_mono (Measure.restrict_mono hAN le_rfl) haeN
  have hpoint : ∀ x ∈ A, Tendsto (fun j ↦ f j x) atTop (𝓝 (p x)) :=
    tendsto_everywhere_of_ae_of_antitone_psh (hp.1.mono hAΩ) hfPsh hanti hae
  have hker : S.kernel = fun j ↦ explicitRadialKernel R hR j :=
    funext fun j ↦ funext (hSkernel j)
  simpa only [f, hker] using (show IsDecreasingApproximation A p f from ⟨hfSmooth, hanti, hpoint⟩)

/-- The radial monotonicity atom, together with the already checked smoothness,
PSH preservation, almost-everywhere convergence, and representative uniqueness,
produces a pointwise decreasing smooth approximation on every relatively
compact inner domain. -/
theorem exists_decreasingMollifierApproximation
    {Ω A : Opens (ComplexModel n)} {p : ComplexModel n → ℝ}
    (hp : IsLocallyBoundedPshOn Ω p) (hA : RelativelyCompactIn A Ω) :
    ∃ f : ℕ → ComplexModel n → ℝ, IsDecreasingApproximation A p f := by
  let _ : ProperSpace (ComplexModel n) := FiniteDimensional.proper ℝ _
  obtain ⟨R, hR, N, K, hN, hclAN, hNK, hK, hKΩ, hball⟩ :=
    exists_open_compact_closedBall_neighborhood hA.1 Ω.isOpen hA.2
  have hAN : (A : Set (ComplexModel n)) ⊆ N := subset_closure.trans hclAN
  have hAΩ : (A : Set (ComplexModel n)) ⊆ Ω := hAN.trans (hNK.trans hKΩ)
  exact ⟨_, isDecreasingApproximation_explicitRadialKernel hp hR hN hK hKΩ hAN hAΩ hball⟩

/-- A smooth real-valued PSH function pulls back by a smooth holomorphic map.
This is the smooth kernel of the general pullback theorem: `smoothDDC_comp`
cancels the second-derivative terms of the map, and the remaining Levi form is
tested on its complex-linear differential. -/
theorem plurisubharmonicOn_coe_comp_of_smooth
    {F : ComplexModel k → ComplexModel n} {p : ComplexModel n → ℝ}
    {U : Set (ComplexModel k)} {V : Set (ComplexModel n)}
    (hU : IsOpen U) (hV : IsOpen V) (hF : ContDiffOn ℂ ∞ F U)
    (hpSmooth : ContDiffOn ℝ ∞ p V) (hFV : MapsTo F U V)
    (hp : PlurisubharmonicOn (fun y => (p y : EReal)) V) :
    PlurisubharmonicOn (fun y => (p (F y) : EReal)) U := by
  let q : ComplexModel k → ℝ := fun y => p (F y)
  have hqSmooth : ContDiffOn ℝ ∞ q U :=
    hpSmooth.comp (hF.restrict_scalars ℝ) hFV
  have hqLevi : ∀ y ∈ U, ∀ v : ComplexModel k, 0 ≤ leviForm q y v := by
    intro y hy v
    rw [show leviForm q y v = leviForm p (F y) (fderiv ℝ F y v) from
      FirstPass.HolomorphicDDC.leviForm_comp hU hV hF hpSmooth hFV hy v]
    exact FirstPass.leviForm_nonneg_of_contDiffOn_plurisubharmonicOn
      (U := ⟨V, hV⟩) hpSmooth hp (hFV hy) _
  exact FirstPass.plurisubharmonicOn_of_contDiffOn_levi_nonneg hU hqSmooth hqLevi

/-- Smooth real-valued PSH targets pull back under the same first-order
holomorphicity hypothesis as the singular theorem.  On each tested affine
disc the map has scalar complex domain, hence is complex smooth by the Cauchy
integral theorem; the preceding smooth Levi calculation then applies after
the canonical identification `ComplexModel 1 ≃L[ℂ] ℂ`. -/
theorem plurisubharmonicOn_coe_comp_holomorphic_of_smooth
    {F : ComplexModel k → ComplexModel n} {p : ComplexModel n → ℝ}
    {U : Set (ComplexModel k)} {V : Set (ComplexModel n)}
    (hU : IsOpen U) (hV : IsOpen V) (hF : DifferentiableOn ℂ F U)
    (hpSmooth : ContDiffOn ℝ ∞ p V) (hFV : MapsTo F U V)
    (hp : PlurisubharmonicOn (fun y => (p y : EReal)) V) :
    PlurisubharmonicOn (fun y => (p (F y) : EReal)) U := by
  have hcont : ContinuousOn (fun y => p (F y)) U :=
    hpSmooth.continuousOn.comp hF.continuousOn hFV
  have hdisc : DiscPshOn (fun y => (p (F y) : EReal)) U := by
    refine ⟨fun _ _ => EReal.coe_ne_top _,
      (continuous_coe_real_ereal.comp_continuousOn hcont).upperSemicontinuousOn,
      ?_⟩
    intro x v r hr hD C hC
    let line : ℂ → ComplexModel k := fun z => x + z • v
    let D : Set ℂ := line ⁻¹' U
    have hline : Differentiable ℂ line := by
      dsimp only [line]
      fun_prop
    have hDopen : IsOpen D := hU.preimage hline.continuous
    let g : ℂ → ComplexModel n := fun z => F (line z)
    have hgDiff : DifferentiableOn ℂ g D := by
      have hmap : MapsTo line D U := fun _ hz => hz
      exact hF.fun_comp hline.differentiableOn hmap
    have hgSmooth : ContDiffOn ℂ ∞ g D := hgDiff.contDiffOn hDopen
    let e : ComplexModel 1 ≃L[ℂ] ℂ :=
      PiLp.equivOfUnique 2 ℂ (fun _ : Fin 1 => ℂ)
    let A : Set (ComplexModel 1) := e ⁻¹' D
    have hAopen : IsOpen A := hDopen.preimage e.continuous
    let G : ComplexModel 1 → ComplexModel n := fun a => g (e a)
    have hGSmooth : ContDiffOn ℂ ∞ G A := by
      exact hgSmooth.comp e.contDiff.contDiffOn (fun _ ha => ha)
    have hGAV : MapsTo G A V := by
      intro a ha
      exact hFV ha
    have hGPsh : PlurisubharmonicOn (fun a => (p (G a) : EReal)) A :=
      plurisubharmonicOn_coe_comp_of_smooth
        hAopen hV hGSmooth hpSmooth hGAV hp
    have hGdisc : DiscPshOn (fun a => (p (G a) : EReal)) A :=
      hGPsh.discPshOn
    let d : ComplexModel 1 := e.symm 1
    have hedge (z : ℂ) : e (z • d) = z := by
      simp [d]
    have hGparam (z : ℂ) : G (0 + z • d) = F (x + z • v) := by
      simp only [G, g, line, zero_add, hedge]
    have hdiscA : affineClosedDisc (0 : ComplexModel 1) d r ⊆ A := by
      intro a ha
      obtain ⟨z, hz, rfl⟩ := ha
      change line (e (0 + z • d)) ∈ U
      rw [show e (0 + z • d) = z by simp [hedge]]
      exact hD ⟨z, hz, rfl⟩
    have hboundA : ∀ a ∈ affineClosedDisc (0 : ComplexModel 1) d r,
        (p (G a) : EReal) ≤ (C : EReal) := by
      intro a ha
      obtain ⟨z, hz, rfl⟩ := ha
      rw [hGparam]
      exact hC _ ⟨z, hz, rfl⟩
    have hsub := hGdisc.submean (0 : ComplexModel 1) d r hr hdiscA C hboundA
    unfold circleDeficit at hsub ⊢
    simp only [hGparam] at hsub
    simpa [G, g, line] using hsub
  exact hdisc.plurisubharmonicOn hU

/-- **Pending singular step.** PSH germs pull back by a holomorphic map.  The
smooth pullback kernel is proved above; the remaining input is pointwise
decreasing radial regularization of an arbitrary nontrivial PSH germ.  The
resulting pullback may be identically negative infinity, including when the
source maps into the pole set. -/
theorem plurisubharmonicAt_comp_holomorphic
    {F : ComplexModel k → ComplexModel n} {u : ComplexModel n → EReal}
    {U : Set (ComplexModel k)} (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    {z : ComplexModel k} (hz : z ∈ U) (hu : PlurisubharmonicAt u (F z)) :
    PlurisubharmonicAt (fun y => u (F y)) z := by
  obtain ⟨V, hV, hFzV, huV⟩ := hu
  let Ω : Opens (ComplexModel n) := ⟨V, hV⟩
  have huΩ : PlurisubharmonicOn u Ω := huV.plurisubharmonicOn hV
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV (F z) hFzV
  let A : Opens (ComplexModel n) := ⟨ball (F z) (r / 2), isOpen_ball⟩
  have hFzA : F z ∈ A := mem_ball_self (by positivity)
  let _ : ProperSpace (ComplexModel n) := FiniteDimensional.proper ℝ _
  have hAcompact : IsCompact (closure (A : Set (ComplexModel n))) := by
    change IsCompact (closure (ball (F z) (r / 2)))
    rw [closure_ball _ (by positivity : r / 2 ≠ 0)]
    exact isCompact_closedBall _ _
  have hAclΩ : closure (A : Set (ComplexModel n)) ⊆ Ω := by
    change closure (ball (F z) (r / 2)) ⊆ V
    rw [closure_ball _ (by positivity : r / 2 ≠ 0)]
    exact (closedBall_subset_ball (by linarith)).trans hball
  have hAΩ : (A : Set (ComplexModel n)) ⊆ Ω := subset_closure.trans hAclΩ
  have hArel : RelativelyCompactIn A Ω := ⟨hAcompact, hAclΩ⟩
  have hex (q : ℕ) : ∃ f : ℕ → ComplexModel n → ℝ,
      IsDecreasingApproximation A (truncationReal u q) f :=
    exists_decreasingMollifierApproximation
      (truncationReal_isLocallyBoundedPshOn huΩ q) hArel
  choose f hf using hex
  let B : Opens (ComplexModel k) :=
    ⟨U ∩ F ⁻¹' (A : Set (ComplexModel n)),
      hF.continuousOn.isOpen_inter_preimage hU A.isOpen⟩
  have hzB : z ∈ B := ⟨hz, hFzA⟩
  have hFB : DifferentiableOn ℂ F B := hF.mono inter_subset_left
  have hFBA : MapsTo F B A := fun _ hy ↦ hy.2
  have hpull (q j : ℕ) :
      PlurisubharmonicOn (fun y ↦ (f q j (F y) : EReal)) B :=
    plurisubharmonicOn_coe_comp_holomorphic_of_smooth
      B.isOpen A.isOpen hFB ((hf q).1 j).1 hFBA ((hf q).1 j).2.1
  have htruncDisc (q : ℕ) :
      DiscPshOn (fun y ↦ (truncationReal u q (F y) : EReal)) B := by
    have hfj (j : ℕ) : DiscPshOn (fun y ↦ (f q j (F y) : EReal)) B :=
      (hpull q j).discPshOn
    have hanti (y : ComplexModel k) (hy : y ∈ B) :
        Antitone (fun j ↦ (f q j (F y) : EReal)) := by
      intro a b hab
      exact EReal.coe_le_coe_iff.mpr ((hf q).2.1 (F y) hy.2 hab)
    apply (DiscPshOn.iInf_of_antitone hfj hanti).congr
    intro y hy
    exact tendsto_nhds_unique (tendsto_atTop_iInf (hanti y hy))
      (EReal.tendsto_coe.mpr ((hf q).2.2 (F y) hy.2))
  have htruncAnti (y : ComplexModel k) (hy : y ∈ B) :
      Antitone (fun q ↦ (truncationReal u q (F y) : EReal)) := by
    intro a b hab
    exact EReal.coe_le_coe_iff.mpr
      (truncationReal_antitone huΩ (hAΩ hy.2) hab)
  apply (DiscPshOn.iInf_of_antitone htruncDisc htruncAnti).plurisubharmonicOn
    B.isOpen z hzB |>.congr
  filter_upwards [B.isOpen.mem_nhds hzB] with y hy
  have hnegReal : Tendsto (fun q : ℕ ↦ -(q : ℝ)) atTop atBot :=
    tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
  have hnegEReal : Tendsto (fun q : ℕ ↦ ((-(q : ℝ) : ℝ) : EReal)) atTop (𝓝 ⊥) :=
    EReal.tendsto_coe_atBot.comp hnegReal
  have ht : Tendsto (fun q ↦ truncation u q (F y)) atTop (𝓝 (u (F y))) := by
    simpa only [truncation, max_eq_left bot_le] using
      (tendsto_const_nhds.max hnegEReal :
        Tendsto (fun q : ℕ ↦ max (u (F y)) ((-(q : ℝ) : ℝ) : EReal))
          atTop (𝓝 (max (u (F y)) ⊥)))
  have htReal : Tendsto (fun q ↦ (truncationReal u q (F y) : EReal))
      atTop (𝓝 (u (F y))) := by
    have heq : (fun q ↦ (truncationReal u q (F y) : EReal)) =
        fun q ↦ truncation u q (F y) := by
      funext q
      exact coe_truncationReal huΩ q (hAΩ hy.2)
    rw [heq]
    exact ht
  exact tendsto_nhds_unique (tendsto_atTop_iInf (htruncAnti y hy)) htReal

/-- The germ theorem gives pullback on any open source domain mapped to a
set where the target potential has PSH germs. -/
theorem plurisubharmonicOn_comp_holomorphic
    {F : ComplexModel k → ComplexModel n} {u : ComplexModel n → EReal}
    {U : Set (ComplexModel k)} {V : Set (ComplexModel n)}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (hFV : MapsTo F U V)
    (hu : PlurisubharmonicOn u V) :
    PlurisubharmonicOn (fun y => u (F y)) U := by
  intro z hz
  exact plurisubharmonicAt_comp_holomorphic hU hF hz (hu (F z) (hFV hz))

/-- Smooth real summands and PSH germs transport separately. This is a raw
quasi-PSH statement, with no conclusion about the finite locus. -/
theorem quasiPlurisubharmonicAt_comp_holomorphic
    {F : ComplexModel k → ComplexModel n} {u : ComplexModel n → EReal}
    {U : Set (ComplexModel k)} (hU : IsOpen U) (hF : ContDiffOn ℂ ∞ F U)
    {z : ComplexModel k} (hz : z ∈ U) (hu : QuasiPlurisubharmonicAt u (F z)) :
    QuasiPlurisubharmonicAt (fun y => u (F y)) z := by
  obtain ⟨p, h, hp, hh, heq⟩ := hu
  have hcont : ContinuousAt F z := hF.continuousOn.continuousAt (hU.mem_nhds hz)
  refine ⟨fun y => p (F y), fun y => h (F y),
    plurisubharmonicAt_comp_holomorphic hU (hF.differentiableOn (by simp)) hz hp,
    ?_, ?_⟩
  · filter_upwards [hcont.eventually hh, hU.mem_nhds hz] with y hhy hy
    exact hhy.comp y (((hF.restrict_scalars ℝ) y hy).contDiffAt (hU.mem_nhds hy))
  exact heq.comp_tendsto hcont

end SGPT.Foundations.Analysis.Pending.HolomorphicPullback
