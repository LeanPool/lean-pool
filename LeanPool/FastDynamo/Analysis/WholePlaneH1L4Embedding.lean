/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.FourierMultiplierSub
public import LeanPool.FastDynamo.Analysis.ComplexForm
public import LeanPool.FastDynamo.Operator.AssociatedForm
public import LeanPool.FastDynamo.Operator.WholePlaneLocal
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality

/-!
# The weak whole-plane `H¹ → L⁴` embedding

The single form perturbation of the paper (`eq:form-small`, in the proof
of `prop:local-seed`) compares the sectorial forms of two velocity coefficients and needs the
difference to be form-small uniformly over the coefficient family.  The estimate used there is
the Hölder argument with exponents `(4,2,4)` or `(4,4,2)`, built on the two-dimensional
embedding `H¹(ℝ²) → L⁴(ℝ²)`.  This module proves that embedding.

The embedding starts from the Schwartz core of `WholePlaneH1Core` and Mathlib's two-dimensional
Gagliardo--Nirenberg--Sobolev inequality, applied to `x ↦ ‖f x‖²`.  The module provides the
scalar core estimate and the scalar embedding `wholePlaneScalarH1ToL4` with its
almost-everywhere representative.
-/

@[expose] public section

/-!
## The weak whole-plane `H¹ → L⁴` embedding

This part starts from the Schwartz core of `WholePlaneH1Core` and the
two-dimensional Gagliardo--Nirenberg--Sobolev inequality in Mathlib.  The
key core estimate is obtained by applying the latter inequality to
`x ↦ ‖f x‖²`.
-/

namespace FastDynamo

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal LineDeriv SchwartzMap

/-- The exponent `4` is in the normed range of Bochner `Lᵖ`.  This is local
because the form-perturbation API already exports the project-wide instance. -/
local instance : Fact (1 ≤ (4 : ENNReal)) := ⟨by norm_num⟩

/-- The operator norm of a linear map out of the Euclidean plane is bounded
by the sum of its two coordinate values. -/
private theorem norm_clm_wholePlane_le_coordinates
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : WholePlane →L[ℝ] F) :
    ‖L‖ ≤ ‖L (wholePlaneBasis 0)‖ + ‖L (wholePlaneBasis 1)‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro x
  have hx : x = x 0 • wholePlaneBasis 0 + x 1 • wholePlaneBasis 1 := by
    ext j
    fin_cases j <;> simp [wholePlaneBasis]
  calc
    ‖L x‖ = ‖L (x 0 • wholePlaneBasis 0 +
        x 1 • wholePlaneBasis 1)‖ := congrArg norm (congrArg L hx)
    _ = ‖x 0 • L (wholePlaneBasis 0) +
        x 1 • L (wholePlaneBasis 1)‖ := by
      rw [map_add, map_smul, map_smul]
    _
        ≤ ‖x 0 • L (wholePlaneBasis 0)‖ +
            ‖x 1 • L (wholePlaneBasis 1)‖ := norm_add_le _ _
    _ = |x 0| * ‖L (wholePlaneBasis 0)‖ +
          |x 1| * ‖L (wholePlaneBasis 1)‖ := by
      simp [norm_smul]
    _ ≤ ‖x‖ * ‖L (wholePlaneBasis 0)‖ +
          ‖x‖ * ‖L (wholePlaneBasis 1)‖ := by
      gcongr
      · simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le x 0)
      · simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le x 1)
    _ = (‖L (wholePlaneBasis 0)‖ + ‖L (wholePlaneBasis 1)‖) * ‖x‖ := by
      ring

/-- A fixed cutoff, equal to one on the unit ball and supported in the ball
of radius two. -/
def unitCutoff : ContDiffBump (0 : WholePlane) where
  rIn := 1
  rOut := 2
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The expanding copy of `unitCutoff` with inner radius `n + 1`. -/
private def expandingCutoff (n : ℕ) : ContDiffBump (0 : WholePlane) where
  rIn := n + 1
  rOut := 2 * (n + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have : (0 : ℝ) < n + 1 := by positivity
    nlinarith

/-- Pointwise identification of the dilated bump: `expandingCutoff n` is the fixed bump
`unitCutoff` evaluated at `x / (n + 1)`. -/
private theorem expandingCutoff_apply (n : ℕ) (x : WholePlane) :
    expandingCutoff n x = unitCutoff (((n + 1 : ℝ)⁻¹) • x) := by
  simp [ContDiffBump.apply, expandingCutoff, unitCutoff,
    div_eq_mul_inv, show (n + 1 : ℝ) ≠ 0 by positivity, smul_smul]

/-- A global derivative bound for the fixed cutoff. -/
theorem exists_unitCutoff_fderiv_bound :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : WholePlane,
      ‖fderiv ℝ (unitCutoff : WholePlane → ℝ) x‖ ≤ B := by
  have hBdd : BddAbove (Set.range fun x : WholePlane =>
      ‖fderiv ℝ (unitCutoff : WholePlane → ℝ) x‖) := by
    exact ((unitCutoff.contDiff : ContDiff ℝ 1
      (unitCutoff : WholePlane → ℝ)).continuous_fderiv one_ne_zero).norm
        |>.bddAbove_range_of_hasCompactSupport
          ((unitCutoff.hasCompactSupport).fderiv ℝ).norm
  rcases hBdd with ⟨B, hB⟩
  refine ⟨max B 0, le_max_right _ _, fun x => ?_⟩
  exact (hB (Set.mem_range_self x)).trans (le_max_left _ _)

/-- A global bound `B` for the differential of `unitCutoff` bounds the differential of every
dilate `expandingCutoff n` as well, uniformly in `n`: the chain rule contributes the factor
`(n + 1)⁻¹ ≤ 1`. -/
private theorem norm_fderiv_expandingCutoff_le
    (B : ℝ) (hB : ∀ x : WholePlane,
      ‖fderiv ℝ (unitCutoff : WholePlane → ℝ) x‖ ≤ B)
    (n : ℕ) (x : WholePlane) :
    ‖fderiv ℝ (expandingCutoff n : WholePlane → ℝ) x‖ ≤ B := by
  have hfun : (expandingCutoff n : WholePlane → ℝ) =
      fun y => unitCutoff (((n + 1 : ℝ)⁻¹) • y) := by
    funext y
    exact expandingCutoff_apply n y
  rw [hfun, fderiv_comp_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (by positivity))]
  have hn : (1 : ℝ) ≤ n + 1 := by
    exact_mod_cast Nat.le_add_left 1 n
  have hinv : (n + 1 : ℝ)⁻¹ ≤ 1 := by
    exact (inv_le_one₀ (by positivity)).2 hn
  calc
    (n + 1 : ℝ)⁻¹ *
        ‖fderiv ℝ (unitCutoff : WholePlane → ℝ)
          ((n + 1 : ℝ)⁻¹ • x)‖
        ≤ 1 * B := by
          exact mul_le_mul
            hinv
            (hB _) (norm_nonneg _) zero_le_one
    _ = B := one_mul B

/-- For a fixed point `x` the dilated bumps converge to `1`, because `x` lies in the inner ball
of radius `n + 1` for all large `n`.  This makes the truncations exhaust the plane. -/
private theorem tendsto_expandingCutoff_apply (x : WholePlane) :
    Tendsto (fun n : ℕ => expandingCutoff n x) atTop (nhds 1) := by
  obtain ⟨N : ℕ, hN⟩ := exists_nat_ge ‖x‖
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  symm
  rw [(expandingCutoff n).one_of_mem_closedBall]
  simpa [expandingCutoff, Metric.mem_closedBall, dist_zero_right] using
    hN.trans (by exact_mod_cast hn.trans (Nat.le_add_right n 1))

/-- The compactly supported cutoff of the norm-square of a Schwartz map. -/
private def cutoffNormSq
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (n : ℕ) (f : SchwartzMap WholePlane F) (x : WholePlane) : ℝ :=
  expandingCutoff n x * ‖f x‖ ^ 2

/-- The truncated squared norm `x ↦ χₙ(x)‖f x‖²` of a Schwartz map is continuously
differentiable. -/
private theorem cutoffNormSq_contDiff
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  (n : ℕ) (f : SchwartzMap WholePlane F) :
    ContDiff ℝ 1 (cutoffNormSq n f) := by
  exact (expandingCutoff n).contDiff.mul
    (((f.smooth ⊤).of_le (by simp)).norm_sq ℝ)

/-- The truncated squared norm is compactly supported, its support lying inside that of the
bump `expandingCutoff n`. -/
private theorem cutoffNormSq_hasCompactSupport
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (n : ℕ) (f : SchwartzMap WholePlane F) :
    HasCompactSupport (cutoffNormSq n f) := by
  exact (expandingCutoff n).hasCompactSupport.mul_right

/-- Chain-rule bound for the squared norm of a Schwartz map:
`‖D(‖f‖²)(x)‖ ≤ 2‖f x‖ · ‖Df(x)‖`. -/
private theorem norm_fderiv_normSq_le
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : SchwartzMap WholePlane F) (x : WholePlane) :
    ‖fderiv ℝ (fun y => ‖f y‖ ^ 2) x‖ ≤
      2 * ‖f x‖ * ‖fderiv ℝ (f : WholePlane → F) x‖ := by
  rw [((f.hasFDerivAt x).norm_sq).fderiv]
  calc
    ‖2 • (innerSL ℝ (f x)).comp (fderiv ℝ (f : WholePlane → F) x)‖
        ≤ 2 * ‖(innerSL ℝ (f x)).comp
            (fderiv ℝ (f : WholePlane → F) x)‖ := by
          exact norm_nsmul_le
    _ ≤ 2 * (‖innerSL ℝ (f x)‖ *
          ‖fderiv ℝ (f : WholePlane → F) x‖) := by
      exact mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.opNorm_comp_le _ _) (by norm_num)
    _ = 2 * ‖f x‖ * ‖fderiv ℝ (f : WholePlane → F) x‖ := by
      rw [innerSL_apply_norm]
      ring

/-- Leibniz bound for the differential of the truncated squared norm: if `B` bounds
`‖D unitCutoff‖` globally then
`‖D(χₙ‖f‖²)(x)‖ ≤ B‖f x‖² + 2‖f x‖ · ‖Df(x)‖`, uniformly in the truncation index `n`. -/
private theorem norm_fderiv_cutoffNormSq_le
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (B : ℝ) (hB : ∀ x : WholePlane,
      ‖fderiv ℝ (unitCutoff : WholePlane → ℝ) x‖ ≤ B)
    (n : ℕ) (f : SchwartzMap WholePlane F) (x : WholePlane) :
    ‖fderiv ℝ (cutoffNormSq n f) x‖ ≤
      B * ‖f x‖ ^ 2 + 2 * ‖f x‖ *
        ‖fderiv ℝ (f : WholePlane → F) x‖ := by
  have hc : HasFDerivAt (expandingCutoff n : WholePlane → ℝ)
      (fderiv ℝ (expandingCutoff n : WholePlane → ℝ) x) x :=
    ((((expandingCutoff n).contDiff : ContDiff ℝ 1
      (expandingCutoff n : WholePlane → ℝ)).differentiable
        (by norm_num)) x).hasFDerivAt
  have hf := (f.hasFDerivAt x).norm_sq
  change ‖fderiv ℝ ((expandingCutoff n : WholePlane → ℝ) *
      fun y => ‖f y‖ ^ 2) x‖ ≤ _
  rw [(hc.mul hf).fderiv, ← hf.fderiv]
  calc
    ‖expandingCutoff n x • fderiv ℝ (fun y => ‖f y‖ ^ 2) x +
        ‖f x‖ ^ 2 • fderiv ℝ (expandingCutoff n : WholePlane → ℝ) x‖
        ≤ ‖expandingCutoff n x • fderiv ℝ (fun y => ‖f y‖ ^ 2) x‖ +
          ‖‖f x‖ ^ 2 • fderiv ℝ (expandingCutoff n : WholePlane → ℝ) x‖ :=
            norm_add_le _ _
    _ = |expandingCutoff n x| *
          ‖fderiv ℝ (fun y => ‖f y‖ ^ 2) x‖ +
        ‖f x‖ ^ 2 *
          ‖fderiv ℝ (expandingCutoff n : WholePlane → ℝ) x‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_pow, abs_norm]
    _ ≤ 1 * (2 * ‖f x‖ * ‖fderiv ℝ (f : WholePlane → F) x‖) +
          ‖f x‖ ^ 2 * B := by
      apply add_le_add
      · apply mul_le_mul
        · simpa [abs_of_nonneg (expandingCutoff n).nonneg] using
            (expandingCutoff n).le_one
        · exact norm_fderiv_normSq_le f x
        · exact norm_nonneg _
        · norm_num
      · exact mul_le_mul_of_nonneg_left
          (norm_fderiv_expandingCutoff_le B hB n x) (sq_nonneg _)
    _ = B * ‖f x‖ ^ 2 + 2 * ‖f x‖ *
          ‖fderiv ℝ (f : WholePlane → F) x‖ := by ring

/-- Integrated form of the previous pointwise bound: by Cauchy–Schwarz the `L¹` norm of
`D(χₙ‖f‖²)` is at most `B‖f‖_{L²}² + 2‖f‖_{L²}‖Df‖_{L²}`, uniformly in `n`.  This is the
input to the Gagliardo–Nirenberg–Sobolev step yielding `H¹(ℝ²) ↪ L⁴(ℝ²)`. -/
private theorem eLpNorm_fderiv_cutoffNormSq_le
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (B : ℝ) (hB0 : 0 ≤ B) (hB : ∀ x : WholePlane,
      ‖fderiv ℝ (unitCutoff : WholePlane → ℝ) x‖ ≤ B)
    (n : ℕ) (f : SchwartzMap WholePlane F) :
    eLpNorm (fderiv ℝ (cutoffNormSq n f)) 1 volume ≤
      ENNReal.ofReal B * eLpNorm f 2 volume ^ 2 +
        2 * eLpNorm f 2 volume *
          eLpNorm (fderiv ℝ (f : WholePlane → F)) 2 volume := by
  let a : WholePlane → ℝ := fun x => B * ‖f x‖ ^ 2
  let b : WholePlane → ℝ := fun x =>
    2 * ‖f x‖ * ‖fderiv ℝ (f : WholePlane → F) x‖
  have ha : AEStronglyMeasurable a volume := by
    apply Continuous.aestronglyMeasurable
    fun_prop
  have hb : AEStronglyMeasurable b volume := by
    apply Continuous.aestronglyMeasurable
    dsimp only [b]
    exact (continuous_const.mul
      ((f.smooth ⊤).continuous.norm)).mul
        (((f.smooth ⊤).continuous_fderiv (by simp)).norm)
  have hmono : eLpNorm (fderiv ℝ (cutoffNormSq n f)) 1 volume ≤
      eLpNorm (a + b) 1 volume := by
    apply eLpNorm_mono_real
      ((cutoffNormSq_contDiff n f).continuous_fderiv (by simp)).aestronglyMeasurable
    intro x
    exact norm_fderiv_cutoffNormSq_le B hB n f x
  have ha_bound : eLpNorm a 1 volume ≤
      ENNReal.ofReal B * eLpNorm f 2 volume ^ 2 := by
    rw [show a = B • fun x => ‖f x‖ ^ 2 by
      funext x; simp [a]]
    rw [eLpNorm_const_smul, Real.eNorm_eq_ofReal hB0]
    have hsquare : eLpNorm (fun x => ‖f x‖ ^ 2) 1 volume =
        eLpNorm f 2 volume ^ 2 := by
      rw [show (fun x => ‖f x‖ ^ (2 : ℕ)) =
          fun x => ‖f x‖ ^ (2 : ℝ) by
        funext x; rw [Real.rpow_two]]
      calc
        eLpNorm (fun x => ‖f x‖ ^ (2 : ℝ)) 1 volume =
            eLpNorm f (1 * ENNReal.ofReal 2) volume ^ (2 : ℝ) :=
              eLpNorm_norm_rpow f f.continuous.aestronglyMeasurable (by norm_num)
        _ = eLpNorm f 2 volume ^ 2 := by
          norm_num [ENNReal.rpow_two]
    rw [hsquare]
  have hb_bound : eLpNorm b 1 volume ≤
      2 * eLpNorm f 2 volume *
        eLpNorm (fderiv ℝ (f : WholePlane → F)) 2 volume := by
    dsimp only [b]
    have hholder := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
      (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)) (r := (1 : ℝ≥0∞))
      (f := (f : WholePlane → F)) (g := fderiv ℝ (f : WholePlane → F))
      (fun z L => (2 : ℝ) * ‖z‖ * ‖L‖) (2 : ℝ≥0)
      ((continuous_const.mul continuous_fst.norm).mul continuous_snd.norm)
      (f.memLp 2 volume).aestronglyMeasurable
      ((f.smooth ⊤).continuous_fderiv (by simp)).aestronglyMeasurable
      (by
        filter_upwards with x
        simp only [Real.norm_eq_abs, abs_mul, abs_norm]
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2)]
        norm_num)
    simpa using hholder
  exact hmono.trans <| (eLpNorm_add_le (by norm_num)).trans <|
    add_le_add ha_bound hb_bound

/-- Ladyzhenskaya's estimate on the Schwartz core, still written in the
squared form naturally produced by applying GNS to `‖f‖²`. -/
private theorem schwartz_ladyzhenskaya_sq
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : SchwartzMap WholePlane F) :
    eLpNorm f 4 volume ^ 2 ≤
      (MeasureTheory.eLpNormLESNormFDerivOneConst
          (volume : Measure WholePlane) 2 : ℝ≥0∞) *
        (ENNReal.ofReal (Classical.choose exists_unitCutoff_fderiv_bound) *
            eLpNorm f 2 volume ^ 2 +
          2 * eLpNorm f 2 volume *
            eLpNorm (fderiv ℝ (f : WholePlane → F)) 2 volume) := by
  let B : ℝ := Classical.choose exists_unitCutoff_fderiv_bound
  have hB0 : 0 ≤ B := (Classical.choose_spec
    exists_unitCutoff_fderiv_bound).1
  have hB : ∀ x : WholePlane,
      ‖fderiv ℝ (unitCutoff : WholePlane → ℝ) x‖ ≤ B :=
    (Classical.choose_spec exists_unitCutoff_fderiv_bound).2
  let C : ℝ≥0∞ :=
    (MeasureTheory.eLpNormLESNormFDerivOneConst
        (volume : Measure WholePlane) 2 : ℝ≥0∞) *
      (ENNReal.ofReal B * eLpNorm f 2 volume ^ 2 +
        2 * eLpNorm f 2 volume *
          eLpNorm (fderiv ℝ (f : WholePlane → F)) 2 volume)
  have hgns (n : ℕ) : eLpNorm (cutoffNormSq n f) 2 volume ≤ C := by
    calc
      eLpNorm (cutoffNormSq n f) 2 volume ≤
          (MeasureTheory.eLpNormLESNormFDerivOneConst
              (volume : Measure WholePlane) 2 : ℝ≥0∞) *
            eLpNorm (fderiv ℝ (cutoffNormSq n f)) 1 volume := by
        apply MeasureTheory.eLpNorm_le_eLpNorm_fderiv_one
          (volume : Measure WholePlane)
          (cutoffNormSq_contDiff n f)
          (cutoffNormSq_hasCompactSupport n f)
        simpa [WholePlane] using NNReal.HolderConjugate.two_two
      _ ≤ C := by
        dsimp only [C]
        gcongr
        exact eLpNorm_fderiv_cutoffNormSq_le B hB0 hB n f
  have hlimit : eLpNorm (fun x => ‖f x‖ ^ 2) 2 volume ≤ C := by
    apply MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto
      (u := atTop) (f := fun n => cutoffNormSq n f)
    · exact Filter.Eventually.of_forall hgns
    · intro n
      exact (cutoffNormSq_contDiff n f).continuous.aestronglyMeasurable
    · exact (f.continuous.norm.pow 2).aestronglyMeasurable
    · filter_upwards with x
      simpa only [cutoffNormSq, one_mul] using
        (tendsto_expandingCutoff_apply x).mul_const (‖f x‖ ^ 2)
  have hsquare : eLpNorm (fun x => ‖f x‖ ^ 2) 2 volume =
      eLpNorm f 4 volume ^ 2 := by
    rw [show (fun x => ‖f x‖ ^ (2 : ℕ)) =
        fun x => ‖f x‖ ^ (2 : ℝ) by
      funext x; rw [Real.rpow_two]]
    calc
      eLpNorm (fun x => ‖f x‖ ^ (2 : ℝ)) 2 volume =
          eLpNorm f (2 * ENNReal.ofReal 2) volume ^ (2 : ℝ) :=
            eLpNorm_norm_rpow f f.continuous.aestronglyMeasurable (by norm_num)
      _ = eLpNorm f 4 volume ^ 2 := by
        norm_num [ENNReal.rpow_two]
  rw [hsquare] at hlimit
  simpa only [B, C] using hlimit

/-- The full Fréchet derivative on the plane is controlled in `L²` by its
two coordinate line derivatives. -/
private theorem eLpNorm_fderiv_le_lineDerivs
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : SchwartzMap WholePlane F) :
    eLpNorm (fderiv ℝ (f : WholePlane → F)) 2 volume ≤
      eLpNorm ((∂_{wholePlaneBasis 0} f : SchwartzMap WholePlane F) :
        WholePlane → F) 2 volume +
        eLpNorm ((∂_{wholePlaneBasis 1} f : SchwartzMap WholePlane F) :
          WholePlane → F) 2 volume := by
  let d₀ : WholePlane → ℝ := fun x => ‖∂_{wholePlaneBasis 0} f x‖
  let d₁ : WholePlane → ℝ := fun x => ‖∂_{wholePlaneBasis 1} f x‖
  calc
    eLpNorm (fderiv ℝ (f : WholePlane → F)) 2 volume ≤
        eLpNorm (d₀ + d₁) 2 volume := by
      apply eLpNorm_mono_real
        ((f.smooth ⊤).continuous_fderiv (by simp)).aestronglyMeasurable
      intro x
      exact norm_clm_wholePlane_le_coordinates
        (fderiv ℝ (f : WholePlane → F) x)
    _ ≤ eLpNorm d₀ 2 volume + eLpNorm d₁ 2 volume := by
      apply eLpNorm_add_le
      norm_num
    _ = eLpNorm ((∂_{wholePlaneBasis 0} f : SchwartzMap WholePlane F) :
          WholePlane → F) 2 volume +
        eLpNorm ((∂_{wholePlaneBasis 1} f : SchwartzMap WholePlane F) :
          WholePlane → F) 2 volume := by
      simp only [d₀, d₁,
        eLpNorm_norm _ ((∂_{wholePlaneBasis 0} f).memLp 2 volume).aestronglyMeasurable,
        eLpNorm_norm _ ((∂_{wholePlaneBasis 1} f).memLp 2 volume).aestronglyMeasurable]

/-- The `L²` seminorm of a Schwartz map is the `ENNReal` coercion of the norm of its `L²`
class; this transfers the Schwartz-level estimates to the completed spaces. -/
private theorem eLpNorm_schwartz_eq_ofReal_norm_toLp
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : SchwartzMap WholePlane F) :
    eLpNorm f 2 volume = ENNReal.ofReal ‖f.toLp 2 volume‖ := by
  rw [SchwartzMap.norm_toLp,
    ENNReal.ofReal_toReal (f.memLp 2 volume).eLpNorm_ne_top]

/-- In `ℝ≥0∞` one has `x ≤ x² + 1`, used to turn the squared Ladyzhenskaya bound into a bound
on the `L⁴` seminorm itself. -/
private theorem ennreal_le_sq_add_one (x : ℝ≥0∞) : x ≤ x ^ 2 + 1 := by
  rcases le_total x 1 with hx | hx
  · exact hx.trans (by simp)
  · calc
      x = x * 1 := by simp
      _ ≤ x * x := by gcongr
      _ = x ^ 2 := by ring
      _ ≤ x ^ 2 + 1 := by simp

/-- A uniform `L⁴` bound for Schwartz approximants of a unit weak `H¹`
field.  It is coarse; normalization below recovers a homogeneous
operator bound. -/
def wholePlaneScalarH1L4UnitBound : ℝ≥0∞ :=
  (MeasureTheory.eLpNormLESNormFDerivOneConst
      (volume : Measure WholePlane) 2 : ℝ≥0∞) *
    (ENNReal.ofReal (Classical.choose exists_unitCutoff_fderiv_bound) * 4 + 16) + 1

/-- The unit-ball `L⁴` bound is finite, hence has a real value usable as an operator-norm
bound. -/
private theorem wholePlaneScalarH1L4UnitBound_ne_top :
    wholePlaneScalarH1L4UnitBound ≠ ∞ := by
  unfold wholePlaneScalarH1L4UnitBound
  finiteness

/-- Unit-ball form of the weak scalar `H¹ → L⁴` estimate. -/
private theorem eLpNorm_four_wholePlaneScalarH1_le_unitBound
    (u : WholePlaneScalarH1) (hu : ‖u‖ ≤ 1) :
    eLpNorm (wholePlaneH1Embedding ℂ u : WholePlane → ℂ) 4 volume ≤
      wholePlaneScalarH1L4UnitBound := by
  obtain ⟨useq, hvalue, hderiv⟩ :=
    exists_schwartz_tendsto_wholePlaneScalarH1 u
  have hvalueNorm : Tendsto (fun n => ‖(useq n).toLp 2 volume‖)
      atTop (nhds ‖wholePlaneH1Embedding ℂ u‖) :=
    tendsto_norm.comp hvalue
  have hvalueLt : ∀ᶠ n in atTop, ‖(useq n).toLp 2 volume‖ < 2 :=
    hvalueNorm.eventually_lt_const <|
      (norm_wholePlaneH1Embedding_le ℂ u).trans hu |>.trans_lt one_lt_two
  have hderivNorm (j : Fin 2) :
      Tendsto (fun n => ‖(∂_{wholePlaneBasis j} (useq n)).toLp 2 volume‖)
        atTop (nhds ‖wholePlaneH1FirstDerivative ℂ j u‖) :=
    tendsto_norm.comp (hderiv j)
  have hderivLt (j : Fin 2) :
      ∀ᶠ n in atTop, ‖(∂_{wholePlaneBasis j} (useq n)).toLp 2 volume‖ < 2 :=
    (hderivNorm j).eventually_lt_const <|
      (norm_wholePlaneH1FirstDerivative_le ℂ u j).trans hu |>.trans_lt one_lt_two
  have hcore : ∀ᶠ n in atTop,
      eLpNorm (useq n) 4 volume ≤ wholePlaneScalarH1L4UnitBound := by
    filter_upwards [hvalueLt, hderivLt 0, hderivLt 1] with n hn hdn₀ hdn₁
    have hf₂ : eLpNorm (useq n) 2 volume ≤ 2 := by
      rw [eLpNorm_schwartz_eq_ofReal_norm_toLp]
      simpa using ENNReal.ofReal_le_ofReal hn.le
    have hd₀ : eLpNorm
        ((∂_{wholePlaneBasis 0} (useq n) : SchwartzMap WholePlane ℂ) :
          WholePlane → ℂ) 2 volume ≤ 2 := by
      rw [eLpNorm_schwartz_eq_ofReal_norm_toLp]
      simpa using ENNReal.ofReal_le_ofReal hdn₀.le
    have hd₁ : eLpNorm
        ((∂_{wholePlaneBasis 1} (useq n) : SchwartzMap WholePlane ℂ) :
          WholePlane → ℂ) 2 volume ≤ 2 := by
      rw [eLpNorm_schwartz_eq_ofReal_norm_toLp]
      simpa using ENNReal.ofReal_le_ofReal hdn₁.le
    have hfderiv :
        eLpNorm (fderiv ℝ (useq n : WholePlane → ℂ)) 2 volume ≤ 4 := by
      calc
        _ ≤ eLpNorm
              ((∂_{wholePlaneBasis 0} (useq n) : SchwartzMap WholePlane ℂ) :
                WholePlane → ℂ) 2 volume +
            eLpNorm
              ((∂_{wholePlaneBasis 1} (useq n) : SchwartzMap WholePlane ℂ) :
                WholePlane → ℂ) 2 volume :=
          eLpNorm_fderiv_le_lineDerivs (useq n)
        _ ≤ 2 + 2 := add_le_add hd₀ hd₁
        _ = 4 := by norm_num
    have hsq := schwartz_ladyzhenskaya_sq (useq n)
    have hpow : eLpNorm (useq n) 2 volume ^ 2 ≤ 4 := by
      exact (pow_le_pow_left' hf₂ 2).trans_eq (by norm_num)
    have hprod : 2 * eLpNorm (useq n) 2 volume *
        eLpNorm (fderiv ℝ (useq n : WholePlane → ℂ)) 2 volume ≤ 16 := by
      calc
        _ ≤ (2 : ℝ≥0∞) * 2 * 4 := by gcongr
        _ = 16 := by norm_num
    have hfirst :
        ENNReal.ofReal (Classical.choose exists_unitCutoff_fderiv_bound) *
            eLpNorm (useq n) 2 volume ^ 2 ≤
          ENNReal.ofReal (Classical.choose exists_unitCutoff_fderiv_bound) * 4 := by
      gcongr
    have hinner :
        ENNReal.ofReal (Classical.choose exists_unitCutoff_fderiv_bound) *
              eLpNorm (useq n) 2 volume ^ 2 +
            2 * eLpNorm (useq n) 2 volume *
              eLpNorm (fderiv ℝ (useq n : WholePlane → ℂ)) 2 volume ≤
          ENNReal.ofReal (Classical.choose exists_unitCutoff_fderiv_bound) * 4 + 16 :=
      add_le_add hfirst hprod
    have hsq' : eLpNorm (useq n) 4 volume ^ 2 ≤
        (MeasureTheory.eLpNormLESNormFDerivOneConst
            (volume : Measure WholePlane) 2 : ℝ≥0∞) *
          (ENNReal.ofReal (Classical.choose exists_unitCutoff_fderiv_bound) * 4 + 16) := by
      apply hsq.trans
      gcongr
    exact (ennreal_le_sq_add_one _).trans <| by
      simpa only [wholePlaneScalarH1L4UnitBound] using add_le_add hsq' le_rfl
  obtain ⟨ns, hns, haelimit⟩ :=
    (MeasureTheory.tendstoInMeasure_of_tendsto_Lp hvalue).exists_seq_tendsto_ae
  apply MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto
    (u := atTop)
    (f := fun i => ((useq (ns i)).toLp 2 volume : WholePlane → ℂ))
  · filter_upwards [hns.tendsto_atTop.eventually hcore] with i hi
    rw [eLpNorm_congr_ae ((useq (ns i)).coeFn_toLp 2 volume)]
    exact hi
  · intro i
    exact Lp.aestronglyMeasurable _
  · exact Lp.aestronglyMeasurable _
  · exact haelimit

/-- Homogeneous `L⁴` seminorm bound obtained by normalizing a nonzero weak
`H¹` field to the unit sphere. -/
theorem eLpNorm_four_wholePlaneScalarH1_le (u : WholePlaneScalarH1) :
    eLpNorm (wholePlaneH1Embedding ℂ u : WholePlane → ℂ) 4 volume ≤
      ENNReal.ofReal ‖u‖ * wholePlaneScalarH1L4UnitBound := by
  by_cases hu : u = 0
  · subst u
    have haeZero :
        (wholePlaneH1Embedding ℂ (0 : WholePlaneScalarH1) : WholePlane → ℂ) =ᵐ[volume]
          (0 : WholePlane → ℂ) := by
      rw [map_zero]
      exact Lp.coeFn_zero ℂ 2 volume
    rw [eLpNorm_congr_ae haeZero]
    simp
  let c : ℂ := ((‖u‖⁻¹ : ℝ) : ℂ)
  let v : WholePlaneScalarH1 := c • u
  have hnormu : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu
  have hnormc : ‖c‖ = ‖u‖⁻¹ := by
    simp [c]
  have hvnorm : ‖v‖ = 1 := by
    simp only [v, norm_smul, hnormc, inv_mul_cancel₀ hnormu]
  have huv : u = ((‖u‖ : ℝ) : ℂ) • v := by
    dsimp only [v]
    rw [smul_smul]
    have hcoeff : ((‖u‖ : ℝ) : ℂ) * c = 1 := by
      dsimp only [c]
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ hnormu]
      exact Complex.ofReal_one
    rw [hcoeff, one_smul]
  have hmap : wholePlaneH1Embedding ℂ u =
      ((‖u‖ : ℝ) : ℂ) • wholePlaneH1Embedding ℂ v := by
    calc
      wholePlaneH1Embedding ℂ u =
          wholePlaneH1Embedding ℂ (((‖u‖ : ℝ) : ℂ) • v) :=
        congrArg (wholePlaneH1Embedding ℂ) huv
      _ = ((‖u‖ : ℝ) : ℂ) • wholePlaneH1Embedding ℂ v :=
        (wholePlaneH1Embedding ℂ).map_smul _ _
  have hae :
      (wholePlaneH1Embedding ℂ u : WholePlane → ℂ) =ᵐ[volume]
        ((‖u‖ : ℝ) : ℂ) •
          (wholePlaneH1Embedding ℂ v : WholePlane → ℂ) := by
    have hae₁ :
        (wholePlaneH1Embedding ℂ u : WholePlane → ℂ) =ᵐ[volume]
          (((‖u‖ : ℝ) : ℂ) • wholePlaneH1Embedding ℂ v :
            WholePlaneL2 ℂ) := by
      exact Filter.Eventually.of_forall fun x => by rw [hmap]
    exact hae₁.trans (Lp.coeFn_smul _ _)
  rw [eLpNorm_congr_ae hae,
    eLpNorm_const_smul]
  simp only [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg u)]
  gcongr
  exact eLpNorm_four_wholePlaneScalarH1_le_unitBound v hvnorm.le

/-- Every weak scalar whole-plane `H¹` field has an `L⁴` representative. -/
theorem wholePlaneScalarH1_memLp_four (u : WholePlaneScalarH1) :
    MemLp (wholePlaneH1Embedding ℂ u : WholePlane → ℂ) 4 volume := by
  rw [memLp_iff]
  exact (eLpNorm_four_wholePlaneScalarH1_le u).trans_lt <| by
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_top_iff_ne_top.mpr wholePlaneScalarH1L4UnitBound_ne_top)

/-- Scalar whole-plane `L⁴`. -/
abbrev WholePlaneScalarL4 := Lp ℂ 4 (volume : Measure WholePlane)

/-- The `ℂ`-linear map sending a weak scalar `H¹(ℝ²)` field to the `L⁴` class of its `L²`
representative.  `wholePlaneScalarH1ToL4` is its continuous packaging; this realizes the
two-dimensional Sobolev embedding used in the proof of `prop:local-seed` for `eq:form-small`. -/
noncomputable def wholePlaneScalarH1ToL4Linear :
    WholePlaneScalarH1 →ₗ[ℂ] WholePlaneScalarL4 where
  toFun u := (wholePlaneScalarH1_memLp_four u).toLp
    (wholePlaneH1Embedding ℂ u : WholePlane → ℂ)
  map_add' u v := by
    let hu := wholePlaneScalarH1_memLp_four u
    let hv := wholePlaneScalarH1_memLp_four v
    let huv := wholePlaneScalarH1_memLp_four (u + v)
    have hmap : wholePlaneH1Embedding ℂ (u + v) =
        wholePlaneH1Embedding ℂ u + wholePlaneH1Embedding ℂ v :=
      (wholePlaneH1Embedding ℂ).map_add u v
    have hae :
        (wholePlaneH1Embedding ℂ (u + v) : WholePlane → ℂ) =ᵐ[volume]
          (wholePlaneH1Embedding ℂ u : WholePlane → ℂ) +
            (wholePlaneH1Embedding ℂ v : WholePlane → ℂ) := by
      have hae₁ :
          (wholePlaneH1Embedding ℂ (u + v) : WholePlane → ℂ) =ᵐ[volume]
            (wholePlaneH1Embedding ℂ u + wholePlaneH1Embedding ℂ v :
              WholePlaneL2 ℂ) := by
        exact Filter.Eventually.of_forall fun x => by rw [hmap]
      exact hae₁.trans (Lp.coeFn_add _ _)
    calc
      huv.toLp (wholePlaneH1Embedding ℂ (u + v) : WholePlane → ℂ) =
          (hu.add hv).toLp
            ((wholePlaneH1Embedding ℂ u : WholePlane → ℂ) +
              (wholePlaneH1Embedding ℂ v : WholePlane → ℂ)) :=
        MemLp.toLp_congr huv (hu.add hv) hae
      _ = hu.toLp (wholePlaneH1Embedding ℂ u : WholePlane → ℂ) +
          hv.toLp (wholePlaneH1Embedding ℂ v : WholePlane → ℂ) :=
        MemLp.toLp_add hu hv
  map_smul' c u := by
    let hu := wholePlaneScalarH1_memLp_four u
    let hcu := wholePlaneScalarH1_memLp_four (c • u)
    have hmap : wholePlaneH1Embedding ℂ (c • u) =
        c • wholePlaneH1Embedding ℂ u :=
      (wholePlaneH1Embedding ℂ).map_smul c u
    have hae :
        (wholePlaneH1Embedding ℂ (c • u) : WholePlane → ℂ) =ᵐ[volume]
          c • (wholePlaneH1Embedding ℂ u : WholePlane → ℂ) := by
      have hae₁ :
          (wholePlaneH1Embedding ℂ (c • u) : WholePlane → ℂ) =ᵐ[volume]
            (c • wholePlaneH1Embedding ℂ u : WholePlaneL2 ℂ) := by
        exact Filter.Eventually.of_forall fun x => by rw [hmap]
      exact hae₁.trans (Lp.coeFn_smul _ _)
    calc
      hcu.toLp (wholePlaneH1Embedding ℂ (c • u) : WholePlane → ℂ) =
          (hu.const_smul c).toLp
            (c • (wholePlaneH1Embedding ℂ u : WholePlane → ℂ)) :=
        MemLp.toLp_congr hcu (hu.const_smul c) hae
      _ = c • hu.toLp (wholePlaneH1Embedding ℂ u : WholePlane → ℂ) :=
        MemLp.toLp_const_smul c hu

/-- The linear map is bounded: `‖u‖_{L⁴} ≤ C‖u‖_{H¹}` with
`C = wholePlaneScalarH1L4UnitBound.toReal`. -/
theorem norm_wholePlaneScalarH1ToL4Linear_le
    (u : WholePlaneScalarH1) :
    ‖wholePlaneScalarH1ToL4Linear u‖ ≤
      wholePlaneScalarH1L4UnitBound.toReal * ‖u‖ := by
  change ‖(wholePlaneScalarH1_memLp_four u).toLp
    (wholePlaneH1Embedding ℂ u : WholePlane → ℂ)‖ ≤ _
  rw [Lp.norm_toLp]
  calc
    (eLpNorm (wholePlaneH1Embedding ℂ u : WholePlane → ℂ) 4 volume).toReal ≤
        (ENNReal.ofReal ‖u‖ * wholePlaneScalarH1L4UnitBound).toReal := by
      apply ENNReal.toReal_mono
      · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          wholePlaneScalarH1L4UnitBound_ne_top
      · exact eLpNorm_four_wholePlaneScalarH1_le u
    _ = wholePlaneScalarH1L4UnitBound.toReal * ‖u‖ := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg u)]
      ring

/-- The actual continuous scalar weak `H¹(ℝ²) → L⁴(ℝ²)` embedding. -/
noncomputable def wholePlaneScalarH1ToL4 :
    WholePlaneScalarH1 →L[ℂ] WholePlaneScalarL4 :=
  LinearMap.mkContinuous wholePlaneScalarH1ToL4Linear
    wholePlaneScalarH1L4UnitBound.toReal
    norm_wholePlaneScalarH1ToL4Linear_le

/-- The `L⁴` representative produced by `wholePlaneScalarH1ToL4` agrees almost everywhere with
the `L²` embedding of the same weak `H¹` field. -/
theorem wholePlaneScalarH1ToL4_coe_ae (u : WholePlaneScalarH1) :
    (wholePlaneScalarH1ToL4 u : WholePlane → ℂ) =ᵐ[volume]
      (wholePlaneH1Embedding ℂ u : WholePlane → ℂ) :=
  MemLp.coeFn_toLp (wholePlaneScalarH1_memLp_four u)

end

end FastDynamo
