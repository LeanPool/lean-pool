/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.Basic
public import Mathlib.MeasureTheory.Measure.Tilted
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.IteratedDerivative
public import LeanPool.KLS.FunctionalInequalities.Analysis.Tensor.Coefficients
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Exponential tilts, tilt averages and the generator identity

Bizeul–Klartag–Lehec (arXiv:2610.05474v1), eqs. (26)–(28) and (48). For a measure `μ` on a real
inner product space `E` and `z ∈ E`, the exponential tilt is `μ_z = μ.tilted ⟪z, ·⟫`, whose
density is `e^{⟪z, x⟫ - Λ_μ(z)}` when `0 < ∫ e^{⟪z, x⟫} dμ < ∞`, and the tilt average of `f` is
`F_f(z) = ∫ f dμ_z`. The Taylor tensors are `T_d f = (1/d!) ∇^d F_f(0)`. For `μ = m.tilted (-V)`
with a `C¹` potential and a compactly supported `C²` function `u`, the generator identity
`F_{-ℒu}(z) = ⟪z, F_{∇u}(z)⟫` holds for every `z`, where `ℒu = Δu - ⟪∇V, ∇u⟫`; Lemma 3.6 follows.

The definitions are total. If `e^{-V}` is not `m`-integrable, `m.tilted (-V)` is the zero measure,
every tilt average vanishes and the identities hold trivially (this also makes the
exponential-moment premise true). The objects are the source's probability tilts exactly when
`m.tilted (-V)` is a probability measure, i.e. when `e^{-V}` is integrable.

`taylorTensor` is a continuous multilinear map. Its `‖·‖` is the multilinear operator norm, not the
source's Hilbert–Schmidt norm of the coefficient array; a coordinate bridge to
`Analysis/Tensor/Coordinate.lean` is needed before tensor estimates of the source are transferred.
-/

@[expose] public section

noncomputable section

open MeasureTheory FunctionalInequalities.Analysis.Tensor
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.Analysis.BakryEmery

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The exponential tilt `μ_z` of `μ` in direction `z`: density `e^{⟪z, x⟫} / ∫ e^{⟪z, y⟫} dμ(y)`
(BKL (26)). -/
def expTilt (μ : Measure E) (z : E) : Measure E :=
  μ.tilted fun x => ⟪z, x⟫

/-- The tilt average `F_f(z) = ∫ f dμ_z` (BKL (27)), for functions with values in a real
normed space. -/
def tiltAverage {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure E) (f : E → F) (z : E) : F :=
  ∫ x, f x ∂(expTilt μ z)

/-- The Taylor tensor `T_d f = (1/d!) ∇^d F_f(0)` (BKL (28)), as a continuous `d`-linear map (its
norm is the operator norm, not the source's Hilbert–Schmidt norm). -/
def taylorTensor {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (μ : Measure E) (f : E → F) (d : ℕ) : ContinuousMultilinearMap ℝ (fun _ : Fin d => E) F :=
  ((d.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ d (tiltAverage μ f) 0

variable (m : Measure E) [m.IsAddHaarMeasure]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The gradient of `V - ⟪z, ·⟫` is `∇V - z`. -/
theorem gradient_sub_inner {V : E → ℝ} (z x : E) (hV : DifferentiableAt ℝ V x) :
    gradient (fun y => V y - ⟪z, y⟫) x = gradient V x - z := by
    have hinner' :
        HasFDerivAt (fun y : E => ⟪z, y⟫)
          (InnerProductSpace.toDual ℝ E z) x := by
      change HasFDerivAt (fun y : E => innerSL ℝ z y) (innerSL ℝ z) x
      exact (innerSL ℝ z).hasFDerivAt
    have hsub' :
        HasFDerivAt (fun y : E => V y - ⟪z, y⟫)
          (InnerProductSpace.toDual ℝ E (gradient V x) -
            InnerProductSpace.toDual ℝ E z) x :=
      ((hasGradientAt_iff_hasFDerivAt).1 hV.hasGradientAt).sub hinner'
    have hsubgrad :
        HasGradientAt (fun y : E => V y - ⟪z, y⟫)
          (gradient V x - z) x := by
      apply (hasGradientAt_iff_hasFDerivAt).2
      simpa [Pi.sub_apply] using hsub'
    exact hsubgrad.gradient

omit [MeasurableSpace E] [BorelSpace E] in
/--
Tilting the potential by a linear function adds a drift: `ℒ_{V - ⟪z,·⟫} f = ℒ_V f + ⟪z, ∇f⟫`. -/
theorem weightedLaplacian_sub_inner {V f : E → ℝ} (z x : E) (hV : DifferentiableAt ℝ V x) :
    weightedLaplacian (fun y => V y - ⟪z, y⟫) f x =
      weightedLaplacian V f x + ⟪z, gradient f x⟫ := by
  rw [weightedLaplacian_apply, weightedLaplacian_apply]
  rw [gradient_sub_inner z x hV]
  rw [inner_sub_left]
  ring

omit [CompleteSpace E] [FiniteDimensional ℝ E] [BorelSpace E] [m.IsAddHaarMeasure] in
/-- The exponential tilt of `m.tilted (-V)` is the tilted law of the potential `V - ⟪z, ·⟫`. -/
theorem expTilt_tilted {V : E → ℝ} (hV : Integrable (fun x => Real.exp ((-V) x)) m) (z : E) :
    expTilt (m.tilted (-V)) z = m.tilted (-fun y => V y - ⟪z, y⟫) := by
    unfold expTilt
    rw [MeasureTheory.tilted_tilted hV]
    congr 1
    funext x
    change -V x + ⟪z, x⟫ = -(V x - ⟪z, x⟫)
    ring

/-- The generator integrates to zero: `∫ ℒ_W f dμ_W = 0` for `μ_W = m.tilted (-W)`, `W ∈ C¹` and a
compactly supported `C²` function `f`. -/
theorem integral_weightedLaplacian_eq_zero {W f : E → ℝ} (hW : ContDiff ℝ 1 W)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∫ x, weightedLaplacian W f x ∂(m.tilted (-W)) = 0 := by
    have h :=
      integral_inner_gradient_tilted m hW hf hfc
        (g := fun _ : E => (1 : ℝ)) contDiff_const
    simp at h
    have h' : -(∫ x, weightedLaplacian W f x ∂(m.tilted (-W))) = 0 := by
      simpa only [integral_neg] using h.symm
    exact neg_eq_zero.mp h'

section TiltIntegrability

omit [m.IsAddHaarMeasure]
/-- The gradient of a compactly supported `C²` function is integrable for every exponential tilt of
`m.tilted (-V)`. -/
theorem integrable_gradient_expTilt {V f : E → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (z : E) : Integrable (gradient f) (expTilt (m.tilted (-V)) z) := by
    have hfd : Continuous (fderiv ℝ f) :=
      hf.continuous_fderiv (by norm_num)
    have hgrad : Continuous (gradient f) := by
      change Continuous
        (fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
      exact (InnerProductSpace.toDual ℝ E).symm.continuous.comp hfd
    have hfd_cs : HasCompactSupport (fderiv ℝ f) :=
      hfc.fderiv (𝕜 := ℝ)
    have hgrad_cs : HasCompactSupport (gradient f) := by
      change HasCompactSupport
        (fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
      exact hfd_cs.comp_left (InnerProductSpace.toDual ℝ E).symm.map_zero
    unfold expTilt
    exact hgrad.integrable_of_hasCompactSupport hgrad_cs

/-- For a `C¹` potential and a compactly supported `C²` function, `ℒ_V f` is integrable for every
exponential tilt of `m.tilted (-W)`. -/
theorem integrable_weightedLaplacian_expTilt {V W f : E → ℝ} (hV : ContDiff ℝ 1 V)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (z : E) :
    Integrable (fun x => weightedLaplacian V f x) (expTilt (m.tilted (-W)) z) := by
  have hc : Continuous (fun x => weightedLaplacian V f x) := continuous_weightedLaplacian hV hf
  have hcs : HasCompactSupport (fun x => weightedLaplacian V f x) := by
    refine hfc.mono' ?_
    intro x hx
    by_contra hnot
    exact hx (weightedLaplacian_eq_zero_of_notMem_tsupport V hnot)
  unfold expTilt
  exact hc.integrable_of_hasCompactSupport hcs

end TiltIntegrability

omit [BorelSpace E] in
/-- The shifted generator identity yields the tilt pairing once its integrability
and zero integral have been established. -/
theorem integral_neg_weightedLaplacian_eq_inner {μ : Measure E} {V f : E → ℝ}
    (hV : ContDiff ℝ 1 V) (z : E) (hgrad : Integrable (gradient f) μ)
    (hL : Integrable (fun x => weightedLaplacian V f x) μ)
    (hzero : (∫ x, weightedLaplacian (fun y => V y - ⟪z, y⟫) f x ∂μ) = 0) :
    (∫ x, -weightedLaplacian V f x ∂μ) = ⟪z, ∫ x, gradient f x ∂μ⟫ := by
  have hinner : Integrable (fun x => ⟪z, gradient f x⟫) μ :=
    (innerSL ℝ z).integrable_comp hgrad
  have hsum : (∫ x, weightedLaplacian V f x ∂μ) +
      (∫ x, ⟪z, gradient f x⟫ ∂μ) = 0 := by
    rw [← integral_add hL hinner]
    calc
      (∫ x, weightedLaplacian V f x + ⟪z, gradient f x⟫ ∂μ) =
          ∫ x, weightedLaplacian (fun y => V y - ⟪z, y⟫) f x ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x =>
          (weightedLaplacian_sub_inner z x (hV.differentiable (by norm_num) x)).symm
      _ = 0 := hzero
  calc
    (∫ x, -weightedLaplacian V f x ∂μ) = -(∫ x, weightedLaplacian V f x ∂μ) := integral_neg _
    _ = ∫ x, ⟪z, gradient f x⟫ ∂μ := by linarith
    _ = ⟪z, ∫ x, gradient f x ∂μ⟫ := integral_inner hgrad z

/-- **BKL (48)** for compactly supported `C²` functions: with `μ = m.tilted (-V)`, `V ∈ C¹`,
`F_{-ℒu}(z) = ⟪z, F_{∇u}(z)⟫` for every `z ∈ E`, where `ℒu = Δu - ⟪∇V, ∇u⟫`. -/
theorem tiltAverage_neg_weightedLaplacian {V f : E → ℝ} (hV : ContDiff ℝ 1 V)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (z : E) :
    tiltAverage (m.tilted (-V)) (fun x => -weightedLaplacian V f x) z =
      ⟪z, tiltAverage (m.tilted (-V)) (gradient f) z⟫ := by
    unfold tiltAverage
    by_cases h : Integrable (fun x => Real.exp ((-V) x)) m
    · let W : E → ℝ := fun y => V y - ⟪z, y⟫
      have hlin : ContDiff ℝ 1 (fun y : E => ⟪z, y⟫) :=
        (innerSL ℝ z).contDiff
      have hW : ContDiff ℝ 1 W := by
        simpa only [W] using hV.sub hlin
      have hz :
          expTilt (m.tilted (-V)) z = m.tilted (-W) := by
        simpa only [W] using expTilt_tilted m h z
      have hgrad :
          Integrable (gradient f) (expTilt (m.tilted (-V)) z) :=
        integrable_gradient_expTilt (m := m) hf hfc z
      have hinner :
          Integrable (fun x => ⟪z, gradient f x⟫)
            (expTilt (m.tilted (-V)) z) :=
        (innerSL ℝ z).integrable_comp hgrad
      have hL :
          Integrable (fun x => weightedLaplacian V f x)
            (expTilt (m.tilted (-V)) z) :=
        integrable_weightedLaplacian_expTilt (m := m) hV hf hfc z
      have hzero :
          (∫ x, weightedLaplacian W f x
            ∂(expTilt (m.tilted (-V)) z)) = 0 := by
        calc
          (∫ x, weightedLaplacian W f x
              ∂(expTilt (m.tilted (-V)) z)) =
              ∫ x, weightedLaplacian W f x ∂(m.tilted (-W)) := by
                rw [hz]
          _ = 0 := integral_weightedLaplacian_eq_zero m hW hf hfc
      exact integral_neg_weightedLaplacian_eq_inner hV z hgrad hL hzero
    · have hzero : m.tilted (-V) = 0 :=
        tilted_of_not_integrable h
      have hz : expTilt (m.tilted (-V)) z = 0 := by
        unfold expTilt
        rw [hzero]
        exact tilted_zero_measure _
      rw [hz]
      simp

open Filter Topology

universe v

private def expD {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E → F) (x : E) : E →L[ℝ] F :=
  (innerSL ℝ x).smulRight (g x)

section NormedSpace

variable {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [CompleteSpace E] in
private theorem expD_meas
    {μ : Measure E} {g : E → F} (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (expD g) μ := by
  exact
    (ContinuousLinearMap.smulRightL ℝ E F).continuous₂.comp_aestronglyMeasurable
      ((innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).continuous.aestronglyMeasurable.prodMk hg)

section ExponentialBounds

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
private theorem expD_bound
    {g : E → F} {M a : ℝ} (_hM : 0 ≤ M)
    (hb : ∀ x, ‖g x‖ ≤ M * Real.exp (a * ‖x‖)) :
    ∀ x, ‖expD g x‖ ≤ M * Real.exp ((a + 1) * ‖x‖) := by
  intro x
  have hx : ‖x‖ ≤ Real.exp ‖x‖ :=
    le_trans (by linarith) (Real.add_one_le_exp ‖x‖)
  calc
    ‖expD g x‖ = ‖x‖ * ‖g x‖ := by
      simp [expD, ContinuousLinearMap.norm_smulRight_apply,
        innerSL_apply_norm]
    _ ≤ Real.exp ‖x‖ * (M * Real.exp (a * ‖x‖)) := by
      gcongr
      exact hb x
    _ = M * Real.exp ((a + 1) * ‖x‖) := by
      rw [add_mul, Real.exp_add, one_mul]
      ring

private theorem exp_smul_bound
    {g : E → F} {M a : ℝ} (_hM : 0 ≤ M)
    (hb : ∀ x, ‖g x‖ ≤ M * Real.exp (a * ‖x‖))
    (z x : E) {R : ℝ} (hz : ‖z‖ ≤ R) :
    ‖Real.exp ⟪z, x⟫ • g x‖ ≤ M * Real.exp ((R + a) * ‖x‖) := by
  calc
    ‖Real.exp ⟪z, x⟫ • g x‖ =
        Real.exp ⟪z, x⟫ * ‖g x‖ := by
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (R * ‖x‖) * (M * Real.exp (a * ‖x‖)) := by
      gcongr
      · exact
          (real_inner_le_norm _ _).trans
            (mul_le_mul_of_nonneg_right hz (norm_nonneg _))
      · exact hb x
    _ = M * Real.exp ((R + a) * ‖x‖) := by
      rw [add_mul, Real.exp_add]
      ring

end ExponentialBounds

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
private theorem exp_smul_int
    (μ : Measure E)
    (hexp : ∀ r : ℝ,
      Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    {g : E → F} (hg : AEStronglyMeasurable g μ)
    {M a : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, ‖g x‖ ≤ M * Real.exp (a * ‖x‖)) (z : E) :
    Integrable (fun x => Real.exp ⟪z, x⟫ • g x) μ := by
  refine ((hexp (‖z‖ + a)).const_mul M).mono' ?_ ?_
  · exact
      (by fun_prop : Continuous (fun x => Real.exp ⟪z, x⟫)).aestronglyMeasurable.smul hg
  · exact ae_of_all μ (fun x => exp_smul_bound hM hb z x le_rfl)

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem exp_smul_hasFDeriv
    (g : E → F) (x z : E) :
    HasFDerivAt (fun w => Real.exp ⟪w, x⟫ • g x)
      (Real.exp ⟪z, x⟫ • expD g x) z := by
  have hl : HasFDerivAt (fun w : E => ⟪w, x⟫) (innerSL ℝ x) z := by
    convert (innerSL ℝ x).hasFDerivAt (x := z) using 1
    ext w
    simpa only [innerSL_apply_apply] using (real_inner_comm w x).symm
  convert hl.exp.smul_const (g x) using 1
  ext y
  simp [expD, ContinuousLinearMap.smulRight_apply, mul_smul]

section ExponentialDifferentiation

omit [CompleteSpace E]
private theorem exp_integral_hasFDeriv
    (μ : Measure E)
    (hexp : ∀ r : ℝ,
      Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    {g : E → F} (hg : AEStronglyMeasurable g μ)
    {M a : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, ‖g x‖ ≤ M * Real.exp (a * ‖x‖)) (z : E) :
    HasFDerivAt (fun w => ∫ x, Real.exp ⟪w, x⟫ • g x ∂μ)
      (∫ x, Real.exp ⟪z, x⟫ • expD g x ∂μ) z := by
  have hbd := expD_bound hM hb
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun w x => Real.exp ⟪w, x⟫ • g x)
    (F' := fun w x => Real.exp ⟪w, x⟫ • expD g x)
    (bound := fun x =>
      M * Real.exp (((‖z‖ + 1) + (a + 1)) * ‖x‖))
    (Metric.ball_mem_nhds z zero_lt_one)
    ?_ (exp_smul_int μ hexp hg hM hb z) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun w =>
      (exp_smul_int μ hexp hg hM hb w).1
  · exact (exp_smul_int μ hexp (expD_meas hg) hM hbd z).1
  · filter_upwards with x w hw
    apply exp_smul_bound hM hbd w x
    have hd : ‖w - z‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hw
    calc
      ‖w‖ ≤ ‖w - z‖ + ‖z‖ := by
        simpa [add_comm] using norm_le_insert' w z
      _ ≤ ‖z‖ + 1 := by linarith
  · exact (hexp _).const_mul M
  · exact ae_of_all μ (fun x w _ => exp_smul_hasFDeriv g x w)

private theorem exp_integral_contDiff_nat
    {F : Type (max u v)}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (μ : Measure E)
    (hexp : ∀ r : ℝ,
      Integrable (fun x => Real.exp (r * ‖x‖)) μ)
    (n : ℕ) {g : E → F} (hg : AEStronglyMeasurable g μ)
    {M a : ℝ} (hM : 0 ≤ M)
    (hb : ∀ x, ‖g x‖ ≤ M * Real.exp (a * ‖x‖)) :
    ContDiff ℝ n (fun z => ∫ x, Real.exp ⟪z, x⟫ • g x ∂μ) := by
  induction n generalizing F M a with
  | zero =>
      exact contDiff_zero.2
        (continuous_iff_continuousAt.2
          (fun z => (exp_integral_hasFDeriv μ hexp hg hM hb z).continuousAt))
  | succ n IH =>
      apply contDiff_succ_iff_hasFDerivAt.2
      refine ⟨(fun z => ∫ x, Real.exp ⟪z, x⟫ • expD g x ∂μ), ?_, ?_⟩
      · exact IH (expD_meas hg) hM (expD_bound hM hb)
      · exact exp_integral_hasFDeriv μ hexp hg hM hb

end ExponentialDifferentiation

section CompleteSpace

variable [CompleteSpace F]

section SmoothTiltIntegrals

omit [CompleteSpace E]
/-- Differentiation under the integral sign for exponential weights: if `μ` has all exponential
moments and `g` grows at most polynomially, `z ↦ ∫ e^{⟪z, x⟫} g(x) dμ(x)` is smooth. -/
theorem contDiff_integral_exp_inner_smul (μ : Measure E)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {g : E → F}
    (hg : AEStronglyMeasurable g μ) {M : ℝ} {k : ℕ} (hgb : ∀ x, ‖g x‖ ≤ M * (1 + ‖x‖) ^ k) :
    ContDiff ℝ ∞ (fun z => ∫ x, Real.exp ⟪z, x⟫ • g x ∂μ) := by
  let L : ULift.{u} F ≃ₗᵢ[ℝ] F := LinearIsometryEquiv.ulift ℝ F
  have hb : ∀ x, ‖g x‖ ≤ |M| * Real.exp ((k : ℝ) * ‖x‖) := by
    intro x
    calc
      ‖g x‖ ≤ M * (1 + ‖x‖) ^ k := hgb x
      _ ≤ |M| * (Real.exp ‖x‖) ^ k := by
        apply mul_le_mul
        · exact le_abs_self M
        · exact pow_le_pow_left₀ (by positivity)
            (by simpa [add_comm] using Real.add_one_le_exp ‖x‖) k
        · positivity
        · positivity
      _ = |M| * Real.exp ((k : ℝ) * ‖x‖) := by
        rw [Real.exp_nat_mul]
  have hgl : AEStronglyMeasurable (fun x => L.symm (g x)) μ :=
    L.symm.toContinuousLinearEquiv.toContinuousLinearMap.continuous.comp_aestronglyMeasurable hg
  have hbl : ∀ x,
      ‖L.symm (g x)‖ ≤ |M| * Real.exp ((k : ℝ) * ‖x‖) := by
    simpa only [L.symm.norm_map] using hb
  have hnat : ∀ n : ℕ, ContDiff ℝ n
      (fun z => ∫ x, Real.exp ⟪z, x⟫ • L.symm (g x) ∂μ) :=
    fun n => exp_integral_contDiff_nat μ hexp n hgl (abs_nonneg M) hbl
  have hs :=
    (contDiff_infty.2 hnat).continuousLinearMap_comp
      L.toContinuousLinearEquiv.toContinuousLinearMap
  have heq :
      (fun z => L (∫ x, Real.exp ⟪z, x⟫ • L.symm (g x) ∂μ)) =
      (fun z => ∫ x, Real.exp ⟪z, x⟫ • g x ∂μ) := by
    funext z
    change L.toContinuousLinearEquiv.toContinuousLinearMap
      (∫ x, Real.exp ⟪z, x⟫ • L.symm (g x) ∂μ) = _
    rw [← L.toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
      (exp_smul_int μ hexp hgl (abs_nonneg M) hbl z)]
    simp
  change ContDiff ℝ ∞
    (fun z => L (∫ x, Real.exp ⟪z, x⟫ • L.symm (g x) ∂μ)) at hs
  rwa [heq] at hs

/-- Tilt averages of bounded measurable functions are smooth for a nonzero measure with all
exponential moments (BKL: "The function `F_f` is smooth"). -/
theorem contDiff_tiltAverage (μ : Measure E) [NeZero μ]
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) μ) {f : E → F}
    (hf : AEStronglyMeasurable f μ) {M : ℝ} (hfb : ∀ x, ‖f x‖ ≤ M) :
    ContDiff ℝ ∞ (tiltAverage μ f) := by
    have hN :
        ContDiff ℝ ∞ (fun z : E => ∫ x, Real.exp ⟪z, x⟫ • f x ∂μ) :=
      contDiff_integral_exp_inner_smul μ hexp hf (M := M) (k := 0) (by
        intro x
        simpa using hfb x)
    have hD' :
        ContDiff ℝ ∞ (fun z : E => ∫ x, Real.exp ⟪z, x⟫ • (1 : ℝ) ∂μ) :=
      contDiff_integral_exp_inner_smul μ hexp
        measurable_const.aestronglyMeasurable (M := 1) (k := 0) (by
          intro x
          simp)
    have hD :
        ContDiff ℝ ∞ (fun z : E => ∫ x, Real.exp ⟪z, x⟫ ∂μ) := by
      simpa using hD'
    have hInt (z : E) :
        Integrable (fun x : E => Real.exp ⟪z, x⟫) μ := by
      have hc : Continuous (fun x : E => ⟪z, x⟫) :=
        continuous_const.inner continuous_id
      have hm :
          AEStronglyMeasurable (fun x : E => Real.exp ⟪z, x⟫) μ :=
        (Real.continuous_exp.comp hc).aestronglyMeasurable
      apply (hexp ‖z‖).mono' hm
      filter_upwards [] with x
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (real_inner_le_norm z x)
    have hpos (z : E) :
        0 < ∫ x, Real.exp ⟪z, x⟫ ∂μ := by
      exact integral_exp_pos (hInt z)
    have hformula (z : E) :
        tiltAverage μ f z =
          (∫ x, Real.exp ⟪z, x⟫ ∂μ)⁻¹ •
            (∫ x, Real.exp ⟪z, x⟫ • f x ∂μ) := by
      rw [tiltAverage, expTilt, MeasureTheory.integral_tilted]
      calc
        (∫ x,
            (Real.exp ⟪z, x⟫ /
                (∫ y, Real.exp ⟪z, y⟫ ∂μ)) • f x ∂μ) =
            ∫ x,
              ((∫ y, Real.exp ⟪z, y⟫ ∂μ)⁻¹ *
                Real.exp ⟪z, x⟫) • f x ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with x
              rw [div_eq_mul_inv]
              congr 1
              exact mul_comm _ _
        _ = ∫ x,
            (∫ y, Real.exp ⟪z, y⟫ ∂μ)⁻¹ •
              (Real.exp ⟪z, x⟫ • f x) ∂μ := by
              apply integral_congr_ae
              filter_upwards [] with x
              simp [smul_smul, mul_comm]
        _ = (∫ y, Real.exp ⟪z, y⟫ ∂μ)⁻¹ •
            (∫ x, Real.exp ⟪z, x⟫ • f x ∂μ) := by
              rw [integral_smul]
    rw [show tiltAverage μ f =
        fun z => (∫ x, Real.exp ⟪z, x⟫ ∂μ)⁻¹ •
          (∫ x, Real.exp ⟪z, x⟫ • f x ∂μ) from funext hformula]
    exact (hD.inv (fun z => (hpos z).ne')).smul hN

end SmoothTiltIntegrals

omit [FiniteDimensional ℝ E] [BorelSpace E] in
omit [CompleteSpace E] in
/-- Lemma 3.6 from the tilt identity: if `F_g(w) = ⟪w, F_G(w)⟫` for every `w` with `F_G` smooth,
then `T_{d+1} g = S_{d+1} T_d G`. This is the tensor part of the proof of
`taylorTensor_neg_weightedLaplacian`, isolated from the smooth compactly supported setting. -/
theorem taylorTensor_succ_of_eq_inner (μ : Measure E) {g : E → ℝ} {G : E → E}
    (hG : ContDiff ℝ ∞ (tiltAverage μ G))
    (hEq : tiltAverage μ g = fun w => ⟪w, tiltAverage μ G w⟫) (d : ℕ) :
    taylorTensor μ g (d + 1) = symmetrizeML (appendInner (taylorTensor μ G d)) := by
  set Φ := tiltAverage μ G with hΦ
  ext h
  simp only [taylorTensor, symmetrizeML, appendInner,
    smul_apply,
    sum_apply,
    ContinuousMultilinearMap.domDomCongr_apply,
    ContinuousMultilinearMap.uncurryRight_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe]
  rw [hEq, ← hΦ]
  rw [iteratedFDeriv_inner_self_apply hG d 0 h]
  simp only [inner_zero_left, zero_add, Function.comp_apply]
  change
    ((d + 1).factorial : ℝ)⁻¹ •
        ∑ k : Fin (d + 1), ⟪h k, (iteratedFDeriv ℝ d Φ 0) (k.removeNth h)⟫ =
      ((d + 1).factorial : ℝ)⁻¹ •
        ∑ σ : Equiv.Perm (Fin (d + 1)),
          ⟪((d.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ d Φ 0) (Fin.init (h ∘ σ)),
            h (σ (Fin.last d))⟫
  have hs : (∑ σ : Equiv.Perm (Fin (d + 1)),
        ⟪(iteratedFDeriv ℝ d Φ 0) (Fin.init (h ∘ σ)), h (σ (Fin.last d))⟫) =
      (d.factorial : ℝ) *
        ∑ k : Fin (d + 1), ⟪(iteratedFDeriv ℝ d Φ 0) (k.removeNth h), h k⟫ := by
    apply sum_perm_inner_init_last
    intro τ v
    exact iteratedFDeriv_comp_perm_of_contDiff hG d 0 v τ
  have hsum : (∑ σ : Equiv.Perm (Fin (d + 1)),
        ⟪((d.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ d Φ 0) (Fin.init (h ∘ σ)),
          h (σ (Fin.last d))⟫) =
      ∑ k : Fin (d + 1), ⟪(iteratedFDeriv ℝ d Φ 0) (k.removeNth h), h k⟫ := by
    simp_rw [smul_apply, real_inner_smul_left]
    rw [← Finset.mul_sum, hs]
    field_simp [Nat.factorial_ne_zero]
  rw [hsum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => real_inner_comm _ _


/-- **BKL Lemma 3.6** for compactly supported `C²` functions, for `μ = m.tilted (-V)` with
`V ∈ C¹` and all exponential moments: `T_{d+1}(-ℒu) = S_{d+1} T_d(∇u)` for every `d`, where the
original index of `T_d(∇u)` is placed after its `d` Taylor indices. For `d = 0` this is (49),
`T_1(-ℒu) = ∫ ∇u dμ` (paired with the argument); for `d ≥ 1` it is (50). -/
theorem taylorTensor_neg_weightedLaplacian {V f : E → ℝ} (hV : ContDiff ℝ 1 V)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V))) (d : ℕ) :
    taylorTensor (m.tilted (-V)) (fun x => -weightedLaplacian V f x) (d + 1) =
      symmetrizeML (appendInner (taylorTensor (m.tilted (-V)) (gradient f) d)) := by
    let μ : Measure E := m.tilted (-V)
    let G : E → E := tiltAverage μ (gradient f)
    have hG : ContDiff ℝ ∞ G := by
      by_cases hi : Integrable (fun x => Real.exp ((-V) x)) m
      · let := isProbabilityMeasure_tilted hi
        have hgrad_cont : Continuous (gradient f) := by
          rw [show gradient f =
              fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x) by
            rfl]
          exact
            (InnerProductSpace.toDual ℝ E).symm.continuous.comp
              (hf.continuous_fderiv (by norm_num))
        have hgrad_compact : HasCompactSupport (gradient f) := by
          rw [show gradient f =
              fun x => (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x) by
            rfl]
          exact
            (hfc.fderiv (𝕜 := ℝ)).comp_left
              (InnerProductSpace.toDual ℝ E).symm.map_zero
        have hnorm_cont : Continuous (fun x => ‖gradient f x‖) :=
          continuous_norm.comp hgrad_cont
        obtain ⟨M, hM⟩ :=
          hnorm_cont.bounded_above_of_compact_support hgrad_compact.norm
        apply contDiff_tiltAverage μ hexp hgrad_cont.aestronglyMeasurable
        · intro x
          simpa using hM x
      · have hμ : m.tilted (-V) = 0 := tilted_of_not_integrable hi
        have hG0 : G = fun _ => (0 : E) := by
          funext x
          simp [G, μ, tiltAverage, expTilt, hμ]
        rw [hG0]
        exact contDiff_const
    have hEq :
        tiltAverage μ (fun x => -weightedLaplacian V f x) =
          fun w => ⟪w, G w⟫ := by
      funext w
      dsimp [G, μ]
      exact tiltAverage_neg_weightedLaplacian m hV hf hfc w
    exact taylorTensor_succ_of_eq_inner μ hG hEq d
omit [CompleteSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
private lemma expTilt_tilted_zero (V : E → ℝ) :
    expTilt (m.tilted (-V)) 0 = m.tilted (-V) := by
  unfold expTilt
  by_cases hV : Integrable (fun x => Real.exp ((-V) x)) m
  · let : IsProbabilityMeasure (m.tilted (-V)) :=
      isProbabilityMeasure_tilted hV
    simp
  · rw [tilted_of_not_integrable hV]
    simp

section TensorEvaluation

omit [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
private lemma symmetrizeML_fin_one_apply
    (Φ : ContinuousMultilinearMap ℝ (fun _ : Fin 1 => E) ℝ) (h : Fin 1 → E) :
    symmetrizeML Φ h = Φ h := by
  classical
  have hp : ∀ σ : Equiv.Perm (Fin 1), σ = 1 := fun σ => Subsingleton.elim _ _
  simp [symmetrizeML, hp]

private lemma inner_comp_apply
    (Ψ : ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) E)
    (a : Fin 0 → E) (x : E) :
    (((innerSL ℝ).compContinuousMultilinearMap Ψ) a) x = ⟪Ψ a, x⟫ := by
  rfl

end TensorEvaluation

omit [FiniteDimensional ℝ E] [BorelSpace E] [CompleteSpace E] in
private lemma taylorTensor_zero_apply
    (μ : Measure E) (g : E → E) (a : Fin 0 → E) :
    taylorTensor μ g 0 a = tiltAverage μ g 0 := by
  simp [taylorTensor]

/-- **BKL (49)** for compactly supported `C²` functions: `T_1(-ℒu)(h) = ⟪∫ ∇u dμ, h⟫`. -/
theorem taylorTensor_one_neg_weightedLaplacian {V f : E → ℝ} (hV : ContDiff ℝ 1 V)
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hexp : ∀ r : ℝ, Integrable (fun x => Real.exp (r * ‖x‖)) (m.tilted (-V))) (h : Fin 1 → E) :
    taylorTensor (m.tilted (-V)) (fun x => -weightedLaplacian V f x) 1 h =
      ⟪∫ x, gradient f x ∂(m.tilted (-V)), h 0⟫ := by
    have H :=
      taylorTensor_neg_weightedLaplacian (m := m) hV hf hfc hexp 0
    have Hh := congrArg (fun T => T h) H
    rw [symmetrizeML_fin_one_apply] at Hh
    simp only [appendInner, ContinuousMultilinearMap.uncurryRight_apply] at Hh
    rw [inner_comp_apply, taylorTensor_zero_apply] at Hh
    simpa [Nat.zero_add, tiltAverage,
      expTilt_tilted_zero (m := m) V] using Hh

omit [CompleteSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
omit [CompleteSpace F] in
/-- Taylor tensors of a function with smooth tilt average are symmetric multilinear maps. -/
theorem taylorTensor_domDomCongr (μ : Measure E) (f : E → F)
    (hF : ContDiff ℝ ∞ (tiltAverage μ f)) (d : ℕ) (σ : Equiv.Perm (Fin d)) :
    (taylorTensor μ f d).domDomCongr σ = taylorTensor μ f d := by
  ext v
  simp only [taylorTensor, ContinuousMultilinearMap.domDomCongr_apply, smul_apply]
  change
    (d.factorial : ℝ)⁻¹ • (iteratedFDeriv ℝ d (tiltAverage μ f) 0) (v ∘ σ) =
      (d.factorial : ℝ)⁻¹ • (iteratedFDeriv ℝ d (tiltAverage μ f) 0) v
  rw [iteratedFDeriv_comp_perm_of_contDiff hF d 0 v σ]

end CompleteSpace

end NormedSpace

omit [CompleteSpace E] [FiniteDimensional ℝ E] [BorelSpace E] in
/-- In coordinates, the Taylor tensors of a real function are symmetric tensors: invariant under
every permutation of their index positions. -/
theorem slotPerm_coordTensor_taylorTensor {n : ℕ} (b : OrthonormalBasis (Fin n) ℝ E) (μ : Measure E)
    (f : E → ℝ) (hF : ContDiff ℝ ∞ (tiltAverage μ f)) (d : ℕ) (σ : Equiv.Perm (Fin d)) :
    slotPerm n d σ (coordTensor b (taylorTensor μ f d)) = coordTensor b (taylorTensor μ f d) := by
    rw [← coordTensor_domDomCongr, taylorTensor_domDomCongr μ f hF d σ]

end FunctionalInequalities.Analysis.BakryEmery
