/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Corrector.GradientIdentification

/-!
# ApproximationAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: part (i) of `l.approximation.stationary.by.local` on the potential subspace

The three inputs are

* the cutoff estimates of
  `Algsuperdiff/Section3/Provider/Corrector/PotentialApproximation.lean`, run
  against the mollified field `q = mollifyGrad ρ φ`;
* a pointwise Young split `‖a + b‖² ≤ (1 + δ)‖a‖² + (1 + δ⁻¹)‖b‖²` together
  with the stationary transfer `E[⨍_{cu_K}|realize (q − p)|²] = E[|q − p|²]`
  (`integral_setIntegral_normSq_realize`), which converts the estimate for `q`
  into one for `p`; and
* the density of the mollified gradients
  (`exists_mollifyGrad_integral_normSq_sub_le`), which makes `‖q − p‖_{L²(Ω)}`
  as small as one wishes.

No sublinearity and no ergodic-theoretic input is used.
-/

open MeasureTheory
open HCPolySupport

namespace Algsuperdiff.Section3.Provider.Corrector

open Algsuperdiff.Probability.Stationary

noncomputable section

/-! ### Elementary Young inequalities -/

section Young

/-- The scalar Young inequality `2xy ≤ δx² + δ⁻¹y²`. -/
theorem two_mul_le_young {δ x y : ℝ} (hδ : 0 < δ) :
    2 * (x * y) ≤ δ * x ^ 2 + δ⁻¹ * y ^ 2 := by
  have hinv : δ⁻¹ * δ = 1 := inv_mul_cancel₀ hδ.ne'
  have h : 0 ≤ δ⁻¹ * (δ * x - y) ^ 2 :=
    mul_nonneg (inv_nonneg.2 hδ.le) (sq_nonneg (δ * x - y))
  have key : δ⁻¹ * (δ * x - y) ^ 2 = δ * x ^ 2 + δ⁻¹ * y ^ 2 - 2 * (x * y) := by
    have hrw : δ⁻¹ * (δ * x - y) ^ 2
        = δ⁻¹ * δ * (δ * x ^ 2) - 2 * (δ⁻¹ * δ * (x * y)) + δ⁻¹ * y ^ 2 := by ring
    rw [hrw, hinv]
    ring
  linarith only [h, key]

/-- The vector Young inequality `‖a + b‖² ≤ (1 + δ)‖a‖² + (1 + δ⁻¹)‖b‖²`. -/
theorem normSq_add_le_young {E : Type*} [NormedAddCommGroup E] {δ : ℝ} (hδ : 0 < δ)
    (a b : E) : ‖a + b‖ ^ 2 ≤ (1 + δ) * ‖a‖ ^ 2 + (1 + δ⁻¹) * ‖b‖ ^ 2 := by
  have htri : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have hcross := two_mul_le_young (δ := δ) (x := ‖a‖) (y := ‖b‖) hδ
  have hsq : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) htri 2
  have hexp : (‖a‖ + ‖b‖) ^ 2 = ‖a‖ ^ 2 + 2 * (‖a‖ * ‖b‖) + ‖b‖ ^ 2 := by ring
  linarith only [hsq, hexp, hcross]

/-- The algebraic core of the density step: with `δ` and `s` chosen small the
Young split of a nearby field costs less than `η`. -/
theorem young_density_arith {M P s δ η D A e : ℝ} (hM0 : 0 ≤ M) (hMD : M ≤ D)
    (hP0 : 0 ≤ P) (hs0 : 0 < s) (hs1 : s ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1)
    (hsbound : s * (D * (2 * P + 1) + 1) ≤ η / 3)
    (hδbound : δ * (D * (P + 1) ^ 2 + 1) ≤ η / 3)
    (hsδ : s ≤ δ * η / 6)
    (hA : A ≤ (P + s) ^ 2) (he : e ≤ s ^ 2) :
    (1 + δ) * (M * A) + (1 + δ⁻¹) * e ≤ M * P ^ 2 + η := by
  have hD0 : 0 ≤ D := le_trans hM0 hMD
  have hinv : δ⁻¹ * δ = 1 := inv_mul_cancel₀ hδ0.ne'
  have hinvpos : 0 < δ⁻¹ := inv_pos.2 hδ0
  have hδinv1 : (1 : ℝ) ≤ δ⁻¹ := by
    have hstep := mul_le_mul_of_nonneg_left hδ1 hinvpos.le
    linarith only [hinv, hstep]
  have hssq : s ^ 2 ≤ s := by
    calc s ^ 2 = s * s := by ring
      _ ≤ 1 * s := mul_le_mul_of_nonneg_right hs1 hs0.le
      _ = s := one_mul s
  have h1 : (1 + δ) * (M * A) ≤ M * (P + s) ^ 2 + δ * (M * (P + s) ^ 2) := by
    have hMA : M * A ≤ M * (P + s) ^ 2 := mul_le_mul_of_nonneg_left hA hM0
    calc (1 + δ) * (M * A) ≤ (1 + δ) * (M * (P + s) ^ 2) :=
          mul_le_mul_of_nonneg_left hMA (by linarith only [hδ0])
      _ = M * (P + s) ^ 2 + δ * (M * (P + s) ^ 2) := by ring
  have h2 : M * (P + s) ^ 2 ≤ M * P ^ 2 + s * (D * (2 * P + 1)) := by
    have hbring : s * (2 * P + 1) = 2 * P * s + s := by ring
    have hb : 2 * P * s + s ^ 2 ≤ s * (2 * P + 1) := by linarith only [hssq, hbring]
    have hc0 : (0 : ℝ) ≤ s * (2 * P + 1) := mul_nonneg hs0.le (by linarith only [hP0])
    have hstep : M * (2 * P * s + s ^ 2) ≤ s * (D * (2 * P + 1)) := by
      calc M * (2 * P * s + s ^ 2) ≤ M * (s * (2 * P + 1)) :=
            mul_le_mul_of_nonneg_left hb hM0
        _ ≤ D * (s * (2 * P + 1)) := mul_le_mul_of_nonneg_right hMD hc0
        _ = s * (D * (2 * P + 1)) := by ring
    have hexp : M * (P + s) ^ 2 = M * P ^ 2 + M * (2 * P * s + s ^ 2) := by ring
    linarith only [hexp, hstep]
  have h3 : δ * (M * (P + s) ^ 2) ≤ δ * (D * (P + 1) ^ 2) := by
    have hb : (P + s) ^ 2 ≤ (P + 1) ^ 2 :=
      pow_le_pow_left₀ (by linarith only [hP0, hs0.le]) (by linarith only [hs1]) 2
    have : M * (P + s) ^ 2 ≤ D * (P + 1) ^ 2 :=
      mul_le_mul hMD hb (sq_nonneg _) hD0
    exact mul_le_mul_of_nonneg_left this hδ0.le
  have h4 : (1 + δ⁻¹) * e ≤ 2 * δ⁻¹ * s ^ 2 := by
    have hle : (1 : ℝ) + δ⁻¹ ≤ 2 * δ⁻¹ := by linarith only [hδinv1]
    calc (1 + δ⁻¹) * e ≤ (1 + δ⁻¹) * s ^ 2 :=
          mul_le_mul_of_nonneg_left he (by linarith only [hinvpos])
      _ ≤ 2 * δ⁻¹ * s ^ 2 := mul_le_mul_of_nonneg_right hle (sq_nonneg s)
  have h5 : 2 * δ⁻¹ * s ^ 2 ≤ η / 3 := by
    have hs2 : s ^ 2 ≤ δ * η / 6 := le_trans hssq hsδ
    have hstep : 2 * δ⁻¹ * s ^ 2 ≤ 2 * δ⁻¹ * (δ * η / 6) :=
      mul_le_mul_of_nonneg_left hs2 (by linarith only [hinvpos])
    have heq : 2 * δ⁻¹ * (δ * η / 6) = η / 3 := by
      have hrw : 2 * δ⁻¹ * (δ * η / 6) = (δ⁻¹ * δ) * (η / 3) := by ring
      rw [hrw, hinv, one_mul]
    linarith only [hstep, heq]
  have h6 : s * (D * (2 * P + 1)) ≤ η / 3 := by
    have hring : s * (D * (2 * P + 1) + 1) = s * (D * (2 * P + 1)) + s := by ring
    linarith only [hsbound, hring, hs0.le]
  have h7 : δ * (D * (P + 1) ^ 2) ≤ η / 3 := by
    have hring : δ * (D * (P + 1) ^ 2 + 1) = δ * (D * (P + 1) ^ 2) + δ := by ring
    linarith only [hδbound, hring, hδ0.le]
  linarith only [h1, h2, h3, h4, h5, h6, h7]

/-- Crude quadratic absorption over abstract reals: from `a ≤ b + c` with all
three nonnegative, `a ^ 2 ≤ 2 * b ^ 2 + 2 * c ^ 2`.  Extracted so that the
norm-level applications below never enter a nonlinear arithmetic tactic. -/
private theorem sq_le_two_sq_add_two_sq {a b c : ℝ} (ha : 0 ≤ a)
    (h : a ≤ b + c) : a ^ 2 ≤ 2 * b ^ 2 + 2 * c ^ 2 := by
  have hsq : a ^ 2 ≤ (b + c) ^ 2 := pow_le_pow_left₀ ha h 2
  have hexp : (b + c) ^ 2 = 2 * b ^ 2 + 2 * c ^ 2 - (b - c) ^ 2 := by ring
  linarith only [hsq, hexp, sq_nonneg (b - c)]

end Young

/-! ### The local approximant against a different target field -/

section Pointwise

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]

omit [MeasurableSpace Ω] in
/-- The realization of a difference is the difference of the realizations. -/
theorem realize_sub_apply (q p : Ω → HilbertVec d) (ω : Ω) (x : Vec d) :
    realize (fun ω' => q ω' - p ω') ω x = realize q ω x - realize p ω x := rfl

omit [MeasurableSpace Ω] in
/-- The error against a target field `p` splits into the error against the
mollified field `q` and the stationary remainder `q - p`. -/
theorem localGradApprox_sub_realize_split (Q : TriadicCube d) (L : ℕ)
    (φ : Ω → ℝ) (q p : Ω → HilbertVec d) (ω : Ω) (x : Vec d) :
    HilbertVec.ofVec (localGradApprox Q L φ q ω x) - realize p ω x
      = (HilbertVec.ofVec (localGradApprox Q L φ q ω x) - realize q ω x)
        + realize (fun ω' => q ω' - p ω') ω x := by
  rw [realize_sub_apply]
  abel

omit [MeasurableSpace Ω] in
/-- A crude pointwise bound on the local approximation error, valid at every
point of space. -/
theorem norm_localGradApprox_sub_realize_le (Q : TriadicCube d) (L : ℕ)
    (φ : Ω → ℝ) (q : Ω → HilbertVec d) (ω : Ω) (x : Vec d) :
    ‖HilbertVec.ofVec (localGradApprox Q L φ q ω x) - realize q ω x‖
      ≤ ‖realize q ω x‖ + gradBound Q L * ‖realize φ ω x‖ := by
  rw [ofVec_localGradApprox_sub_realize]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [norm_smul]
    have h0 := (approxCutoff Q L).nonneg x
    have h1 := (approxCutoff Q L).le_one x
    have hcut : ‖(approxCutoff Q L).toFun x - 1‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith only [h0, h1]
    calc ‖(approxCutoff Q L).toFun x - 1‖ * ‖realize q ω x‖
        ≤ 1 * ‖realize q ω x‖ := mul_le_mul_of_nonneg_right hcut (norm_nonneg _)
      _ = ‖realize q ω x‖ := one_mul _
  · rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_cutoffHilbertGrad_le Q L x) (norm_nonneg _)

end Pointwise

/-! ### The cube estimate against a different target field -/

section CubeEstimate

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]

/-- For almost every sample the local approximation error is square integrable
on the cube. -/
theorem ae_memLp_localGradApprox_sub (Q : TriadicCube d) (L : ℕ)
    {φ : Ω → ℝ} {q : Ω → HilbertVec d}
    (hφm : StronglyMeasurable φ) (hφ : MemLp φ 2 μ)
    (hqm : StronglyMeasurable q) (hq : MemLp q 2 μ) :
    ∀ᵐ ω ∂μ, MemLp (fun x => HilbertVec.ofVec (localGradApprox Q L φ q ω x) - realize q ω x) 2
      (volume.restrict (cubeSet Q)) := by
  have hQfin : volume (cubeSet Q) ≠ ⊤ := (volume_cubeSet_lt_top Q).ne
  filter_upwards [ae_memLp_two_realize (μ := μ) hQfin hqm hq,
    ae_memLp_two_realize (μ := μ) hQfin hφm hφ] with ω hqω hφω
  refine MemLp.mono' (hqω.norm.add ((hφω.norm).const_mul (gradBound Q L)))
    (stronglyMeasurable_localGradApprox_sub Q L hφm hqm ω).aestronglyMeasurable ?_
  filter_upwards with x
  exact norm_localGradApprox_sub_realize_le Q L φ q ω x

/-- The set integral of the squared local approximation error is integrable in
the sample. -/
theorem integrable_setIntegral_normSq_localGradApprox_sub (Q : TriadicCube d) (L : ℕ)
    {φ : Ω → ℝ} {q : Ω → HilbertVec d}
    (hφm : StronglyMeasurable φ) (hφ : MemLp φ 2 μ)
    (hqm : StronglyMeasurable q) (hq : MemLp q 2 μ) :
    Integrable (fun ω => ∫ x in cubeSet Q,
      ‖HilbertVec.ofVec (localGradApprox Q L φ q ω x) - realize q ω x‖ ^ 2) μ := by
  have hQfin : volume (cubeSet Q) ≠ ⊤ := (volume_cubeSet_lt_top Q).ne
  have hjoint0 : StronglyMeasurable fun z : Ω × Vec d =>
      HilbertVec.ofVec (localGradApprox Q L φ q z.1 z.2) - realize q z.1 z.2 := by
    have hrw : (fun z : Ω × Vec d =>
        HilbertVec.ofVec (localGradApprox Q L φ q z.1 z.2) - realize q z.1 z.2)
        = fun z : Ω × Vec d => ((approxCutoff Q L).toFun z.2 - 1) • realize q z.1 z.2
          + realize φ z.1 z.2 • cutoffHilbertGrad Q L z.2 :=
      funext fun z => ofVec_localGradApprox_sub_realize Q L φ q z.1 z.2
    rw [hrw]
    refine StronglyMeasurable.add ?_ ?_
    · exact ((((approxCutoff Q L).smooth.continuous.sub
        continuous_const).stronglyMeasurable).comp_measurable
        measurable_snd).smul (stronglyMeasurable_uncurry_realize hqm)
    · exact (stronglyMeasurable_uncurry_realize hφm).smul
        (((continuous_cutoffHilbertGrad Q L).stronglyMeasurable).comp_measurable
          measurable_snd)
  have hjoint : StronglyMeasurable fun z : Ω × Vec d =>
      ‖HilbertVec.ofVec (localGradApprox Q L φ q z.1 z.2) - realize q z.1 z.2‖ ^ 2 :=
    hjoint0.norm.pow 2
  have hmeas : StronglyMeasurable fun ω => ∫ x in cubeSet Q,
      ‖HilbertVec.ofVec (localGradApprox Q L φ q ω x) - realize q ω x‖ ^ 2 :=
    hjoint.integral_prod_right'
  have hdom : Integrable (fun ω =>
      2 * (∫ x in cubeSet Q, ‖realize q ω x‖ ^ 2)
        + 2 * gradBound Q L ^ 2 * ∫ x in cubeSet Q, ‖realize φ ω x‖ ^ 2) μ :=
    ((integrable_setIntegral_normSq_realize hQfin hqm hq).const_mul 2).add
      ((integrable_setIntegral_normSq_realize hQfin hφm hφ).const_mul (2 * gradBound Q L ^ 2))
  refine Integrable.mono' hdom hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_memLp_two_realize (μ := μ) hQfin hqm hq,
    ae_memLp_two_realize (μ := μ) hQfin hφm hφ] with ω hqω hφω
  have hqi : Integrable (fun x => ‖realize q ω x‖ ^ 2) (volume.restrict (cubeSet Q)) :=
    (memLp_two_iff_integrable_sq_norm
      (stronglyMeasurable_realize hqm ω).aestronglyMeasurable).1 hqω
  have hφi : Integrable (fun x => ‖realize φ ω x‖ ^ 2) (volume.restrict (cubeSet Q)) :=
    (memLp_two_iff_integrable_sq_norm
      (stronglyMeasurable_realize hφm ω).aestronglyMeasurable).1 hφω
  have hbound : ∫ x in cubeSet Q,
      ‖HilbertVec.ofVec (localGradApprox Q L φ q ω x) - realize q ω x‖ ^ 2
      ≤ ∫ x in cubeSet Q, (2 * ‖realize q ω x‖ ^ 2
        + 2 * gradBound Q L ^ 2 * ‖realize φ ω x‖ ^ 2) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _)
      ((hqi.const_mul 2).add (hφi.const_mul (2 * gradBound Q L ^ 2))) ?_
    filter_upwards with x
    have hle := norm_localGradApprox_sub_realize_le Q L φ q ω x
    have hg0 := gradBound_nonneg Q L
    have hkey := sq_le_two_sq_add_two_sq (norm_nonneg _) hle
    have hring : 2 * (gradBound Q L * ‖realize φ ω x‖) ^ 2
        = 2 * gradBound Q L ^ 2 * ‖realize φ ω x‖ ^ 2 := by ring
    linarith only [hkey, hring]
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x => sq_nonneg _)]
  refine hbound.trans (le_of_eq ?_)
  rw [integral_add (hqi.const_mul 2) (hφi.const_mul (2 * gradBound Q L ^ 2)),
    integral_const_mul, integral_const_mul]

/-- **The Young transfer at a fixed cube.**  The expected squared error of the
local approximant against an arbitrary target field `p` is controlled by its
error against the mollified field `q` plus the stationary distance from `q` to
`p`. -/
theorem integral_setIntegral_normSq_localGradApprox_sub_target_le (Q : TriadicCube d) (L : ℕ)
    {δ : ℝ} (hδ : 0 < δ) {φ : Ω → ℝ} {q p : Ω → HilbertVec d}
    (hφm : StronglyMeasurable φ) (hφ : MemLp φ 2 μ)
    (hqm : StronglyMeasurable q) (hq : MemLp q 2 μ)
    (hpm : StronglyMeasurable p) (hp : MemLp p 2 μ) :
    ∫ ω, (∫ x in cubeSet Q,
        ‖HilbertVec.ofVec (localGradApprox Q L φ q ω x) - realize p ω x‖ ^ 2) ∂μ
      ≤ (1 + δ) * ∫ ω, (∫ x in cubeSet Q,
          ‖HilbertVec.ofVec (localGradApprox Q L φ q ω x) - realize q ω x‖ ^ 2) ∂μ
        + (1 + δ⁻¹) * (cubeVolume Q * ∫ ω, ‖q ω - p ω‖ ^ 2 ∂μ) := by
  have hQfin : volume (cubeSet Q) ≠ ⊤ := (volume_cubeSet_lt_top Q).ne
  have hZm : StronglyMeasurable (fun ω => q ω - p ω) := hqm.sub hpm
  have hZ : MemLp (fun ω => q ω - p ω) 2 μ := hq.sub hp
  have hIq := integrable_setIntegral_normSq_localGradApprox_sub (μ := μ) Q L hφm hφ hqm hq
  have hIr : Integrable (fun ω => ∫ x in cubeSet Q,
      ‖realize (fun ω' => q ω' - p ω') ω x‖ ^ 2) μ :=
    integrable_setIntegral_normSq_realize hQfin hZm hZ
  have hstep : ∫ ω, (∫ x in cubeSet Q,
        ‖HilbertVec.ofVec (localGradApprox Q L φ q ω x) - realize p ω x‖ ^ 2) ∂μ
      ≤ ∫ ω, ((1 + δ) * (∫ x in cubeSet Q,
          ‖HilbertVec.ofVec (localGradApprox Q L φ q ω x) - realize q ω x‖ ^ 2)
        + (1 + δ⁻¹) * ∫ x in cubeSet Q,
          ‖realize (fun ω' => q ω' - p ω') ω x‖ ^ 2) ∂μ := by
    refine integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun ω => integral_nonneg fun x => sq_nonneg _)
      ((hIq.const_mul (1 + δ)).add (hIr.const_mul (1 + δ⁻¹))) ?_
    filter_upwards [ae_memLp_localGradApprox_sub (μ := μ) Q L hφm hφ hqm hq,
      ae_memLp_two_realize (μ := μ) hQfin hZm hZ] with ω hErr hRem
    have hEi : Integrable (fun x =>
        ‖HilbertVec.ofVec (localGradApprox Q L φ q ω x) - realize q ω x‖ ^ 2)
        (volume.restrict (cubeSet Q)) :=
      (memLp_two_iff_integrable_sq_norm hErr.aestronglyMeasurable).1 hErr
    have hRi : Integrable (fun x => ‖realize (fun ω' => q ω' - p ω') ω x‖ ^ 2)
        (volume.restrict (cubeSet Q)) :=
      (memLp_two_iff_integrable_sq_norm
        (stronglyMeasurable_realize hZm ω).aestronglyMeasurable).1 hRem
    have hinner : ∫ x in cubeSet Q,
        ‖HilbertVec.ofVec (localGradApprox Q L φ q ω x) - realize p ω x‖ ^ 2
        ≤ ∫ x in cubeSet Q, ((1 + δ) *
            ‖HilbertVec.ofVec (localGradApprox Q L φ q ω x) - realize q ω x‖ ^ 2
          + (1 + δ⁻¹) * ‖realize (fun ω' => q ω' - p ω') ω x‖ ^ 2) := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _)
        ((hEi.const_mul (1 + δ)).add (hRi.const_mul (1 + δ⁻¹))) ?_
      filter_upwards with x
      rw [localGradApprox_sub_realize_split]
      exact normSq_add_le_young hδ _ _
    refine hinner.trans (le_of_eq ?_)
    rw [integral_add (hEi.const_mul (1 + δ)) (hRi.const_mul (1 + δ⁻¹)),
      integral_const_mul, integral_const_mul]
  refine hstep.trans (le_of_eq ?_)
  rw [integral_add (hIq.const_mul (1 + δ)) (hIr.const_mul (1 + δ⁻¹)),
    integral_const_mul, integral_const_mul,
    integral_setIntegral_normSq_realize hQfin hZm hZ, volume_cubeSet_toReal]

/-- The `L²(Q)`-normalized form of the Young transfer. -/
theorem integral_cubeLpNorm_localGradApprox_sub_target_le (Q : TriadicCube d) (L : ℕ)
    {δ : ℝ} (hδ : 0 < δ) {φ : Ω → ℝ} {q p : Ω → HilbertVec d}
    (hφm : StronglyMeasurable φ) (hφ : MemLp φ 2 μ)
    (hqm : StronglyMeasurable q) (hq : MemLp q 2 μ)
    (hpm : StronglyMeasurable p) (hp : MemLp p 2 μ) :
    ∫ ω, cubeLpNorm Q 2
        (fun x => HilbertVec.ofVec (localGradApprox Q L φ q ω x) - realize p ω x) ^ (2 : ℝ) ∂μ
      ≤ (1 + δ) * ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * (∫ ω, ‖q ω‖ ^ 2 ∂μ)
          + 2 * gradBound Q L ^ 2 * ∫ ω, ‖φ ω‖ ^ 2 ∂μ)
        + (1 + δ⁻¹) * ∫ ω, ‖q ω - p ω‖ ^ 2 ∂μ := by
  have hQfin : volume (cubeSet Q) ≠ ⊤ := (volume_cubeSet_lt_top Q).ne
  have hvolpos := cubeVolume_pos Q
  have hZm : StronglyMeasurable (fun ω => q ω - p ω) := hqm.sub hpm
  have hZ : MemLp (fun ω => q ω - p ω) 2 μ := hq.sub hp
  -- almost sure identification of the normalized norm
  have hrepr : ∀ᵐ ω ∂μ, cubeLpNorm Q 2
      (fun x => HilbertVec.ofVec (localGradApprox Q L φ q ω x) - realize p ω x) ^ (2 : ℝ)
      = (cubeVolume Q)⁻¹ * ∫ x in cubeSet Q,
          ‖HilbertVec.ofVec (localGradApprox Q L φ q ω x) - realize p ω x‖ ^ 2 := by
    filter_upwards [ae_memLp_localGradApprox_sub (μ := μ) Q L hφm hφ hqm hq,
      ae_memLp_two_realize (μ := μ) hQfin hZm hZ] with ω hErr hRem
    have hmem : MemHilbertVectorL2 (cubeSet Q)
        (fun x => HilbertVec.ofVec (localGradApprox Q L φ q ω x) - realize p ω x) := by
      have hsum : MemLp (fun x => (HilbertVec.ofVec (localGradApprox Q L φ q ω x)
          - realize q ω x) + realize (fun ω' => q ω' - p ω') ω x) 2
          (volume.restrict (cubeSet Q)) := hErr.add hRem
      refine hsum.ae_eq ?_
      filter_upwards with x
      exact (localGradApprox_sub_realize_split Q L φ q p ω x).symm
    have h := cubeLpNorm_rpow_eq_cubeAverage_norm_rpow Q 2
      (fun x => HilbertVec.ofVec (localGradApprox Q L φ q ω x) - realize p ω x)
      (by norm_num) (by simp) (memLp_normalizedCubeMeasure_of_memHilbertVectorL2 hmem)
    simpa [cubeAverage, Real.rpow_natCast] using h
  rw [integral_congr_ae hrepr, integral_const_mul]
  have hkey := integral_setIntegral_normSq_localGradApprox_sub_target_le (μ := μ) Q L hδ
    hφm hφ hqm hq hpm hp
  have hbase := integral_setIntegral_normSq_localGradApprox_sub_le (μ := μ) Q L hφm hφ hqm hq
  have hstrip := volume_boundaryStripSet_toReal_le (d := d) Q L
  have hqnn : 0 ≤ ∫ ω, ‖q ω‖ ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  have hφnn : 0 ≤ ∫ ω, ‖φ ω‖ ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  have hZnn : 0 ≤ ∫ ω, ‖q ω - p ω‖ ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  have hinv : (0 : ℝ) < (cubeVolume Q)⁻¹ := inv_pos.2 hvolpos
  have hmul : (volume (boundaryStripSet Q L)).toReal * ∫ ω, ‖q ω‖ ^ 2 ∂μ
      ≤ (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) / 2 * cubeVolume Q * ∫ ω, ‖q ω‖ ^ 2 ∂μ :=
    mul_le_mul_of_nonneg_right hstrip hqnn
  have hcancel : (cubeVolume Q)⁻¹ * cubeVolume Q = 1 := inv_mul_cancel₀ hvolpos.ne'
  have hchain : (cubeVolume Q)⁻¹ * ∫ ω, (∫ x in cubeSet Q,
        ‖HilbertVec.ofVec (localGradApprox Q L φ q ω x) - realize p ω x‖ ^ 2) ∂μ
      ≤ (cubeVolume Q)⁻¹ * ((1 + δ) * (2 * ((volume (boundaryStripSet Q L)).toReal
              * ∫ ω, ‖q ω‖ ^ 2 ∂μ)
            + 2 * gradBound Q L ^ 2 * (cubeVolume Q * ∫ ω, ‖φ ω‖ ^ 2 ∂μ))
          + (1 + δ⁻¹) * (cubeVolume Q * ∫ ω, ‖q ω - p ω‖ ^ 2 ∂μ)) := by
    refine mul_le_mul_of_nonneg_left (hkey.trans ?_) hinv.le
    have hδ1 : (0 : ℝ) < 1 + δ := by linarith only [hδ]
    exact add_le_add (mul_le_mul_of_nonneg_left hbase hδ1.le) le_rfl
  refine hchain.trans ?_
  have hgb := gradBound_nonneg Q L
  have hδ1 : (0 : ℝ) < 1 + δ := by linarith only [hδ]
  have hδ2 : (0 : ℝ) < 1 + δ⁻¹ := add_pos_of_pos_of_nonneg one_pos (inv_pos.mpr hδ).le
  have hexp : (cubeVolume Q)⁻¹ * ((1 + δ) * (2 * ((volume (boundaryStripSet Q L)).toReal
              * ∫ ω, ‖q ω‖ ^ 2 ∂μ)
            + 2 * gradBound Q L ^ 2 * (cubeVolume Q * ∫ ω, ‖φ ω‖ ^ 2 ∂μ))
          + (1 + δ⁻¹) * (cubeVolume Q * ∫ ω, ‖q ω - p ω‖ ^ 2 ∂μ))
      = (1 + δ) * (2 * ((cubeVolume Q)⁻¹ * ((volume (boundaryStripSet Q L)).toReal
              * ∫ ω, ‖q ω‖ ^ 2 ∂μ))
            + 2 * gradBound Q L ^ 2 * ∫ ω, ‖φ ω‖ ^ 2 ∂μ)
          + (1 + δ⁻¹) * ∫ ω, ‖q ω - p ω‖ ^ 2 ∂μ := by
    field_simp
  rw [hexp]
  have hfirst : 2 * ((cubeVolume Q)⁻¹ * ((volume (boundaryStripSet Q L)).toReal
        * ∫ ω, ‖q ω‖ ^ 2 ∂μ))
      ≤ (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * ∫ ω, ‖q ω‖ ^ 2 ∂μ := by
    have h := mul_le_mul_of_nonneg_left hmul hinv.le
    have hrw : (cubeVolume Q)⁻¹ * ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) / 2 * cubeVolume Q
        * ∫ ω, ‖q ω‖ ^ 2 ∂μ)
        = (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) / 2 * ∫ ω, ‖q ω‖ ^ 2 ∂μ := by
      field_simp
    rw [hrw] at h
    linarith only [h]
  have hlast := mul_le_mul_of_nonneg_left
    (add_le_add hfirst (le_refl (2 * gradBound Q L ^ 2 * ∫ ω, ‖φ ω‖ ^ 2 ∂μ))) hδ1.le
  linarith only [hlast]

/-- The squared normalized error against the target `p` is integrable in the sample
— the integrand of the part-(i) display. -/
theorem integrable_cubeLpNorm_localGradApprox_sub_target (Q : TriadicCube d) (L : ℕ)
    {φ : Ω → ℝ} {q p : Ω → HilbertVec d}
    (hφm : StronglyMeasurable φ) (hφ : MemLp φ 2 μ)
    (hqm : StronglyMeasurable q) (hq : MemLp q 2 μ)
    (hpm : StronglyMeasurable p) (hp : MemLp p 2 μ) :
    Integrable (fun ω => cubeLpNorm Q 2
      (fun x => HilbertVec.ofVec (localGradApprox Q L φ q ω x) - realize p ω x)
        ^ (2 : ℝ)) μ := by
  have hQfin : volume (cubeSet Q) ≠ ⊤ := (volume_cubeSet_lt_top Q).ne
  have hZm : StronglyMeasurable (fun ω => q ω - p ω) := hqm.sub hpm
  have hZ : MemLp (fun ω => q ω - p ω) 2 μ := hq.sub hp
  have hIq := integrable_setIntegral_normSq_localGradApprox_sub (μ := μ) Q L hφm hφ hqm hq
  have hIr : Integrable (fun ω => ∫ x in cubeSet Q,
      ‖realize (fun ω' => q ω' - p ω') ω x‖ ^ 2) μ :=
    integrable_setIntegral_normSq_realize hQfin hZm hZ
  -- the p-target set integral is integrable, by domination through the split
  have hjointq : StronglyMeasurable fun z : Ω × Vec d =>
      HilbertVec.ofVec (localGradApprox Q L φ q z.1 z.2) - realize q z.1 z.2 := by
    have hrw : (fun z : Ω × Vec d =>
        HilbertVec.ofVec (localGradApprox Q L φ q z.1 z.2) - realize q z.1 z.2)
        = fun z : Ω × Vec d => ((approxCutoff Q L).toFun z.2 - 1) • realize q z.1 z.2
          + realize φ z.1 z.2 • cutoffHilbertGrad Q L z.2 :=
      funext fun z => ofVec_localGradApprox_sub_realize Q L φ q z.1 z.2
    rw [hrw]
    refine StronglyMeasurable.add ?_ ?_
    · exact ((((approxCutoff Q L).smooth.continuous.sub
        continuous_const).stronglyMeasurable).comp_measurable
        measurable_snd).smul (stronglyMeasurable_uncurry_realize hqm)
    · exact (stronglyMeasurable_uncurry_realize hφm).smul
        (((continuous_cutoffHilbertGrad Q L).stronglyMeasurable).comp_measurable
          measurable_snd)
  have hjointp : StronglyMeasurable fun z : Ω × Vec d =>
      HilbertVec.ofVec (localGradApprox Q L φ q z.1 z.2) - realize p z.1 z.2 := by
    have hrw : (fun z : Ω × Vec d =>
        HilbertVec.ofVec (localGradApprox Q L φ q z.1 z.2) - realize p z.1 z.2)
        = fun z : Ω × Vec d =>
          (HilbertVec.ofVec (localGradApprox Q L φ q z.1 z.2) - realize q z.1 z.2)
            + realize (fun ω' => q ω' - p ω') z.1 z.2 :=
      funext fun z => localGradApprox_sub_realize_split Q L φ q p z.1 z.2
    rw [hrw]
    exact hjointq.add (stronglyMeasurable_uncurry_realize hZm)
  have hmeasp : StronglyMeasurable fun ω => ∫ x in cubeSet Q,
      ‖HilbertVec.ofVec (localGradApprox Q L φ q ω x) - realize p ω x‖ ^ 2 :=
    (hjointp.norm.pow 2).integral_prod_right'
  have hIp : Integrable (fun ω => ∫ x in cubeSet Q,
      ‖HilbertVec.ofVec (localGradApprox Q L φ q ω x) - realize p ω x‖ ^ 2) μ := by
    have hdom : Integrable (fun ω =>
        2 * (∫ x in cubeSet Q,
            ‖HilbertVec.ofVec (localGradApprox Q L φ q ω x) - realize q ω x‖ ^ 2)
          + 2 * ∫ x in cubeSet Q, ‖realize (fun ω' => q ω' - p ω') ω x‖ ^ 2) μ :=
      (hIq.const_mul 2).add (hIr.const_mul 2)
    refine Integrable.mono' hdom hmeasp.aestronglyMeasurable ?_
    filter_upwards [ae_memLp_localGradApprox_sub (μ := μ) Q L hφm hφ hqm hq,
      ae_memLp_two_realize (μ := μ) hQfin hZm hZ] with ω hErr hRem
    have hEi : Integrable (fun x =>
        ‖HilbertVec.ofVec (localGradApprox Q L φ q ω x) - realize q ω x‖ ^ 2)
        (volume.restrict (cubeSet Q)) :=
      (memLp_two_iff_integrable_sq_norm hErr.aestronglyMeasurable).1 hErr
    have hRi : Integrable (fun x => ‖realize (fun ω' => q ω' - p ω') ω x‖ ^ 2)
        (volume.restrict (cubeSet Q)) :=
      (memLp_two_iff_integrable_sq_norm
        (stronglyMeasurable_realize hZm ω).aestronglyMeasurable).1 hRem
    have hbound : ∫ x in cubeSet Q,
        ‖HilbertVec.ofVec (localGradApprox Q L φ q ω x) - realize p ω x‖ ^ 2
        ≤ ∫ x in cubeSet Q,
          (2 * ‖HilbertVec.ofVec (localGradApprox Q L φ q ω x) - realize q ω x‖ ^ 2
            + 2 * ‖realize (fun ω' => q ω' - p ω') ω x‖ ^ 2) := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _)
        ((hEi.const_mul 2).add (hRi.const_mul 2)) ?_
      filter_upwards with x
      rw [localGradApprox_sub_realize_split]
      have := normSq_add_le_young one_pos
        (HilbertVec.ofVec (localGradApprox Q L φ q ω x) - realize q ω x)
        (realize (fun ω' => q ω' - p ω') ω x)
      simpa [inv_one, one_add_one_eq_two] using this
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x => sq_nonneg _)]
    refine hbound.trans (le_of_eq ?_)
    rw [integral_add (hEi.const_mul 2) (hRi.const_mul 2),
      integral_const_mul, integral_const_mul]
  -- transfer along the a.e. identification with the normalized norm
  have hrepr : ∀ᵐ ω ∂μ, cubeLpNorm Q 2
      (fun x => HilbertVec.ofVec (localGradApprox Q L φ q ω x) - realize p ω x) ^ (2 : ℝ)
      = (cubeVolume Q)⁻¹ * ∫ x in cubeSet Q,
          ‖HilbertVec.ofVec (localGradApprox Q L φ q ω x) - realize p ω x‖ ^ 2 := by
    filter_upwards [ae_memLp_localGradApprox_sub (μ := μ) Q L hφm hφ hqm hq,
      ae_memLp_two_realize (μ := μ) hQfin hZm hZ] with ω hErr hRem
    have hmem : MemHilbertVectorL2 (cubeSet Q)
        (fun x => HilbertVec.ofVec (localGradApprox Q L φ q ω x) - realize p ω x) := by
      have hsum : MemLp (fun x => (HilbertVec.ofVec (localGradApprox Q L φ q ω x)
          - realize q ω x) + realize (fun ω' => q ω' - p ω') ω x) 2
          (volume.restrict (cubeSet Q)) := hErr.add hRem
      refine hsum.ae_eq ?_
      filter_upwards with x
      exact (localGradApprox_sub_realize_split Q L φ q p ω x).symm
    have h := cubeLpNorm_rpow_eq_cubeAverage_norm_rpow Q 2
      (fun x => HilbertVec.ofVec (localGradApprox Q L φ q ω x) - realize p ω x)
      (by norm_num) (by simp) (memLp_normalizedCubeMeasure_of_memHilbertVectorL2 hmem)
    simpa [cubeAverage, Real.rpow_natCast] using h
  exact ((hIp.const_mul (cubeVolume Q)⁻¹).congr
    (by filter_upwards [hrepr] with ω h; exact h.symm))

end CubeEstimate

/-! ### Part (i) on the stationary potential subspace -/

section Main

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] [AddAction (Vec d) Ω]
variable {μ : Measure Ω} [SFinite μ]
variable [MeasurableConstVAdd (Vec d) Ω] [MeasurableVAdd₂ (Vec d) Ω]
variable [VAddInvariantMeasure (Vec d) Ω μ]
variable [TopologicalSpace Ω] [R1Space Ω] [BorelSpace Ω] [ContinuousVAdd (Vec d) Ω]
variable [IsLocallyFiniteMeasure μ] [μ.InnerRegularCompactLTTop]

/-- **The approximation family at a prescribed tolerance.**  For every `η > 0`
there is a family of zero-trace potentials on the origin cubes whose expected
normalized error against `p` exceeds the target `d·3^{-L}·E[|p|²]` by at most
`η` plus a term that vanishes as the cube grows. -/
theorem exists_family_bound (L : ℕ) {η : ℝ} (hη : 0 < η)
    {p : Ω → HilbertVec d} (hpm : StronglyMeasurable p) (hp : MemLp p 2 μ)
    (hmem : hp.toLp p ∈ stationaryPotentialSubspace (μ := μ) (d := d)) :
    ∃ (V : ℕ → Ω → (Vec d → Vec d)) (g : ℕ → ℝ),
      (∀ K, 0 ≤ g K) ∧ Filter.Tendsto g Filter.atTop (nhds 0) ∧
      (∀ K : ℕ, ∀ᵐ ω ∂μ,
        IsPotentialZeroTraceOn (openCubeSet (originCube d (K : ℤ))) (V K ω)) ∧
      (∀ K : ℕ, Integrable (fun ω => cubeLpNorm (originCube d (K : ℤ)) 2
          (fun x => HilbertVec.ofVec (V K ω x) - realize p ω x) ^ (2 : ℝ)) μ) ∧
      (∀ K : ℕ, ∫ ω, cubeLpNorm (originCube d (K : ℤ)) 2
          (fun x => HilbertVec.ofVec (V K ω x) - realize p ω x) ^ (2 : ℝ) ∂μ
        ≤ (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * (∫ ω, ‖p ω‖ ^ 2 ∂μ) + η + g K) := by
  classical
  set P : ℝ := ‖hp.toLp p‖ with hPdef
  have hP0 : 0 ≤ P := norm_nonneg _
  have hPsq : ∫ ω, ‖p ω‖ ^ 2 ∂μ = P ^ 2 := integral_normSq_eq_norm_sq_toLp hp
  have hD0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  -- the two smallness parameters
  have hden1 : (0 : ℝ) < (d : ℝ) * (P + 1) ^ 2 + 1 :=
    add_pos_of_nonneg_of_pos (mul_nonneg hD0 (sq_nonneg _)) one_pos
  have hden2 : (0 : ℝ) < (d : ℝ) * (2 * P + 1) + 1 :=
    add_pos_of_nonneg_of_pos (mul_nonneg hD0 (by linarith only [hP0])) one_pos
  have hX1 : (0 : ℝ) < 3 * ((d : ℝ) * (P + 1) ^ 2 + 1) :=
    mul_pos (by norm_num) hden1
  have hX2 : (0 : ℝ) < 3 * ((d : ℝ) * (2 * P + 1) + 1) :=
    mul_pos (by norm_num) hden2
  set δ : ℝ := min 1 (η / (3 * ((d : ℝ) * (P + 1) ^ 2 + 1))) with hδdef
  have hδ0 : 0 < δ := lt_min one_pos (div_pos hη hX1)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδbound : δ * ((d : ℝ) * (P + 1) ^ 2 + 1) ≤ η / 3 := by
    have hle : δ ≤ η / (3 * ((d : ℝ) * (P + 1) ^ 2 + 1)) := min_le_right _ _
    have hne : ((d : ℝ) * (P + 1) ^ 2 + 1) ≠ 0 := ne_of_gt hden1
    calc δ * ((d : ℝ) * (P + 1) ^ 2 + 1)
        ≤ (η / (3 * ((d : ℝ) * (P + 1) ^ 2 + 1))) * ((d : ℝ) * (P + 1) ^ 2 + 1) :=
          mul_le_mul_of_nonneg_right hle hden1.le
      _ = η / 3 := by field_simp
  set s : ℝ := min 1 (min (η / (3 * ((d : ℝ) * (2 * P + 1) + 1))) (δ * η / 6)) with hsdef
  have hs0 : 0 < s :=
    lt_min one_pos (lt_min (div_pos hη hX2) (div_pos (mul_pos hδ0 hη) (by norm_num)))
  have hs1 : s ≤ 1 := min_le_left _ _
  have hsbound : s * ((d : ℝ) * (2 * P + 1) + 1) ≤ η / 3 := by
    have hle : s ≤ η / (3 * ((d : ℝ) * (2 * P + 1) + 1)) :=
      le_trans (min_le_right _ _) (min_le_left _ _)
    have hne : ((d : ℝ) * (2 * P + 1) + 1) ≠ 0 := ne_of_gt hden2
    calc s * ((d : ℝ) * (2 * P + 1) + 1)
        ≤ (η / (3 * ((d : ℝ) * (2 * P + 1) + 1))) * ((d : ℝ) * (2 * P + 1) + 1) :=
          mul_le_mul_of_nonneg_right hle hden2.le
      _ = η / 3 := by field_simp
  have hsδ : s ≤ δ * η / 6 := le_trans (min_le_right _ _) (min_le_right _ _)
  -- the mollified approximant
  obtain ⟨r, hr, φ, hφm, hφ, hclose⟩ :=
    exists_mollifyGrad_integral_normSq_sub_le (μ := μ) hp hmem
      (ε := s ^ 2) (pow_pos hs0 2)
  set ρ : Mollifier d := Mollifier.ofRadius d hr with hρdef
  set ψ : Ω → ℝ := mollify ρ.toFun φ with hψdef
  have hψm : StronglyMeasurable ψ := stronglyMeasurable_mollify ρ.continuous hφm
  have hψ : MemLp ψ 2 μ := memLp_two_mollify ρ.continuous ρ.integrable hφm hφ
  set q : Ω → HilbertVec d := mollifyGrad ρ.toFun φ with hqdef
  have hqm : StronglyMeasurable q := stronglyMeasurable_mollifyGrad ρ.smooth hφm
  have hq : MemLp q 2 μ := memLp_two_mollifyGrad ρ.compactSupport ρ.smooth hφm hφ
  -- the mollified field is close to `p` in `L²(Ω)`
  have he : ∫ ω, ‖q ω - p ω‖ ^ 2 ∂μ ≤ s ^ 2 := hclose
  have hdist : ‖hq.toLp q - hp.toLp p‖ ≤ s := by
    have hEq : ∫ ω, ‖q ω - p ω‖ ^ 2 ∂μ = ‖hq.toLp q - hp.toLp p‖ ^ 2 :=
      integral_normSq_sub_eq_norm_sq hq hp
    have hsq : ‖hq.toLp q - hp.toLp p‖ ^ 2 ≤ s ^ 2 := by linarith only [hEq, he]
    exact le_of_pow_le_pow_left₀ two_ne_zero hs0.le hsq
  have hA : ∫ ω, ‖q ω‖ ^ 2 ∂μ ≤ (P + s) ^ 2 := by
    have hnorm : ‖hq.toLp q‖ ≤ P + s := by
      have hsub := norm_sub_norm_le (hq.toLp q) (hp.toLp p)
      linarith only [hsub, hdist]
    have hEq : ∫ ω, ‖q ω‖ ^ 2 ∂μ = ‖hq.toLp q‖ ^ 2 := integral_normSq_eq_norm_sq_toLp hq
    have hsq : ‖hq.toLp q‖ ^ 2 ≤ (P + s) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    linarith only [hEq, hsq]
  -- the Young transfer
  have hM0 : (0 : ℝ) ≤ (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) :=
    mul_nonneg hD0 (three_zpow_neg_pos L).le
  have hMD : (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) ≤ (d : ℝ) := by
    have h1 := three_zpow_neg_le_one L
    calc (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) ≤ (d : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left h1 hD0
      _ = (d : ℝ) := mul_one _
  have hδ0nn : (0 : ℝ) ≤ 1 + δ := (add_pos_of_pos_of_nonneg one_pos hδ0.le).le
  refine ⟨fun K ω => localGradApprox (originCube d (K : ℤ)) L ψ q ω,
    fun K => (1 + δ) * (2 * gradBound (originCube d (K : ℤ)) L ^ 2 * ∫ ω, ‖ψ ω‖ ^ 2 ∂μ),
    fun K => mul_nonneg hδ0nn
      (mul_nonneg (mul_nonneg zero_le_two (sq_nonneg _))
        (integral_nonneg fun ω => sq_nonneg _)), ?_, ?_,
    fun K => integrable_cubeLpNorm_localGradApprox_sub_target (μ := μ)
      (originCube d (K : ℤ)) L hψm hψ hqm hq hpm hp, ?_⟩
  · have hinvK : Filter.Tendsto (fun K : ℕ => ((3 : ℝ) ^ K)⁻¹) Filter.atTop (nhds 0) := by
      simpa [inv_pow] using
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ (3 : ℝ)⁻¹)
          (by norm_num : (3 : ℝ)⁻¹ < 1)
    have hgrad0 : Filter.Tendsto (fun K : ℕ => gradBound (originCube d (K : ℤ)) L)
        Filter.atTop (nhds 0) := by
      simp only [gradBound_originCube]
      simpa using hinvK.const_mul
        ((d : ℝ) * quantitativeCubeCutoffGradientConst d * 8 * (3 : ℝ) ^ L)
    have := ((((hgrad0.pow 2).const_mul (2 : ℝ)).mul_const
      (∫ ω, ‖ψ ω‖ ^ 2 ∂μ)).const_mul (1 + δ))
    simpa using this
  · intro K
    filter_upwards [ae_smooth_primitive_mollify (μ := μ) ρ.compactSupport ρ.smooth hφm hφ]
      with ω hω
    exact isPotentialZeroTraceOn_localGradApprox _ L hω.1 hω.2
  · intro K
    have hkey := integral_cubeLpNorm_localGradApprox_sub_target_le (μ := μ)
      (originCube d (K : ℤ)) L hδ0 hψm hψ hqm hq hpm hp
    refine hkey.trans ?_
    have harith := young_density_arith (M := (d : ℝ) * (3 : ℝ) ^ (-(L : ℤ))) (P := P)
      (s := s) (δ := δ) (η := η) (D := (d : ℝ)) (A := ∫ ω, ‖q ω‖ ^ 2 ∂μ)
      (e := ∫ ω, ‖q ω - p ω‖ ^ 2 ∂μ) hM0 hMD hP0 hs0 hs1 hδ0 hδ1 hsbound hδbound hsδ hA he
    have hring : (1 + δ) * ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * (∫ ω, ‖q ω‖ ^ 2 ∂μ)
          + 2 * gradBound (originCube d (K : ℤ)) L ^ 2 * ∫ ω, ‖ψ ω‖ ^ 2 ∂μ)
        = (1 + δ) * ((d : ℝ) * (3 : ℝ) ^ (-(L : ℤ)) * (∫ ω, ‖q ω‖ ^ 2 ∂μ))
          + (1 + δ) * (2 * gradBound (originCube d (K : ℤ)) L ^ 2 * ∫ ω, ‖ψ ω‖ ^ 2 ∂μ) := by
      ring
    rw [hPsq]
    linarith only [harith, hring]

end Main


end

end Algsuperdiff.Section3.Provider.Corrector
