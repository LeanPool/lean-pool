/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.WholePlaneH1Core
public import LeanPool.FastDynamo.Analysis.WholePlaneLInfTempered

/-!
# Scalar weak Leibniz rule on the whole plane

This module proves the distributional product rule for a bounded scalar
coefficient with bounded weak first derivatives and a scalar weak `H¹` field.
It packages multiplication by such a coefficient as a bounded complex-linear
operator on the complete whole-plane `H¹` graph.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal LineDeriv SchwartzMap

/-- Product rule for the directional derivative of a product of two Schwartz functions:
`∂_m(f·φ) = (∂_m f)·φ + f·(∂_m φ)`. -/
private lemma lineDeriv_smulLeft_schwartz
    (m : WholePlane) (f phi : SchwartzMap WholePlane ℂ) :
    ∂_{m} (SchwartzMap.smulLeftCLM ℂ (f : WholePlane → ℂ) phi) =
      SchwartzMap.smulLeftCLM ℂ ((∂_{m} f : SchwartzMap WholePlane ℂ) :
        WholePlane → ℂ) phi +
      SchwartzMap.smulLeftCLM ℂ (f : WholePlane → ℂ) (∂_{m} phi) := by
  ext x
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  have h := (f.hasFDerivAt x).mul (phi.hasFDerivAt x)
  rw [show SchwartzMap.smulLeftCLM ℂ (f : WholePlane → ℂ) phi =
      fun y => f y * phi y by
    exact SchwartzMap.smulLeftCLM_apply f.hasTemperateGrowth phi]
  change (fderiv ℝ ((f : WholePlane → ℂ) * (phi : WholePlane → ℂ)) x) m = _
  rw [h.fderiv]
  simp only [add_apply]
  rw [SchwartzMap.smulLeftCLM_apply_apply
      (∂_{m} f).hasTemperateGrowth,
    SchwartzMap.smulLeftCLM_apply_apply f.hasTemperateGrowth]
  simp only [smul_eq_mul]
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv,
    SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rw [smul_apply, smul_apply]
  simp only [smul_eq_mul]
  ring

/-- Product rule for multiplication of a tempered distribution by a Schwartz function:
`∂_m(f·T) = (∂_m f)·T + f·(∂_m T)`, obtained by transposing the Schwartz-level rule onto test
functions. -/
private lemma lineDeriv_smulLeft_tempered
    (m : WholePlane) (f : SchwartzMap WholePlane ℂ)
    (T : TemperedDistribution WholePlane ℂ) :
    ∂_{m} (TemperedDistribution.smulLeftCLM ℂ
      (f : WholePlane → ℂ) T) =
      TemperedDistribution.smulLeftCLM ℂ
        ((∂_{m} f : SchwartzMap WholePlane ℂ) : WholePlane → ℂ) T +
      TemperedDistribution.smulLeftCLM ℂ
        (f : WholePlane → ℂ) (∂_{m} T) := by
  ext phi
  simp only [TemperedDistribution.lineDerivOp_apply_apply,
    TemperedDistribution.smulLeftCLM_apply_apply, map_neg, add_apply]
  rw [lineDeriv_smulLeft_schwartz]
  simp

/-- Scalar multiplication on the whole plane. -/
def wholePlaneScalarMulL2 :
    WholePlaneScalarLInf →L[ℂ]
      WholePlaneScalarL2 →L[ℂ] WholePlaneScalarL2 :=
  scalarVectorMulL2 volume

/-- The `L∞`-times-`L²` scalar product is represented almost everywhere by the pointwise product
`x ↦ a x · u x`. -/
theorem wholePlaneScalarMulL2_coe_ae
    (a : WholePlaneScalarLInf) (u : WholePlaneScalarL2) :
    (wholePlaneScalarMulL2 a u : WholePlane → ℂ) =ᵐ[volume]
      fun x => a x * u x := by
  change (scalarVectorMulL2 volume a u : WholePlane → ℂ) =ᵐ[volume]
    fun x => a x * u x
  simpa only [smul_eq_mul] using scalarVectorMulL2_coe_ae volume a u

/-- For a Schwartz factor the `L∞`-times-`L²` product agrees with Mathlib's `L²`-scaling of the
bounded coefficient by the Schwartz function's `L²` class. -/
private lemma wholePlaneScalarMulL2_schwartz_eq_lpSMul
    (a : WholePlaneScalarLInf) (u : SchwartzMap WholePlane ℂ) :
    wholePlaneScalarMulL2 a (u.toLp 2 volume) =
      ((u.toLp 2 volume) • a : WholePlaneScalarL2) := by
  apply Lp.ext
  filter_upwards [wholePlaneScalarMulL2_coe_ae a (u.toLp 2 volume),
    Lp.coeFn_lpSMul (r := 2) (u.toLp 2 volume) a,
    u.coeFn_toLp 2 volume] with x hleft hright hu
  rw [hleft, hright, hu]
  simp only [Pi.mul_apply, smul_eq_mul]
  rw [hu]
  ring

/-- For a Schwartz factor the product's associated tempered distribution is exactly the
Schwartz multiplication of the distribution attached to the bounded coefficient.  This is the
bridge that lets the Schwartz-level product rule act on `L∞` coefficients. -/
private lemma wholePlaneScalarMulL2_schwartz_toTempered
    (a : WholePlaneScalarLInf) (u : SchwartzMap WholePlane ℂ) :
    wholePlaneL2ToTempered ℂ
        (wholePlaneScalarMulL2 a (u.toLp 2 volume)) =
      TemperedDistribution.smulLeftCLM ℂ (u : WholePlane → ℂ)
        (wholePlaneLInfToTempered ℂ a) := by
  rw [wholePlaneScalarMulL2_schwartz_eq_lpSMul]
  exact Lp.toTemperedDistribution_smul_eq
    u.hasTemperateGrowth (u.memLp 2 volume) a

/-- Distributional certificate that `da` is the `j`-th weak derivative of
the bounded coefficient `a`. -/
def HasWholePlaneLInfWeakDerivative (j : Fin 2)
    (a da : WholePlaneScalarLInf) : Prop :=
  ∂_{wholePlaneBasis j} (wholePlaneLInfToTempered ℂ a) =
    wholePlaneLInfToTempered ℂ da

/-- Distributional certificate that `du` is the `j`-th weak derivative of
the `L²` field `u`. -/
def HasWholePlaneL2WeakDerivative (j : Fin 2)
    (u du : WholePlaneScalarL2) : Prop :=
  ∂_{wholePlaneBasis j} (wholePlaneL2ToTempered ℂ u) =
    wholePlaneL2ToTempered ℂ du

/-- The scalar weak Leibniz theorem with a Schwartz second factor.  This is
the core identity needed before the closed-graph/density passage. -/
theorem hasWholePlaneL2WeakDerivative_mul_schwartz
    {j : Fin 2} {a da : WholePlaneScalarLInf}
    (ha : HasWholePlaneLInfWeakDerivative j a da)
    (u : SchwartzMap WholePlane ℂ) :
    HasWholePlaneL2WeakDerivative j
      (wholePlaneScalarMulL2 a (u.toLp 2 volume))
      (wholePlaneScalarMulL2 da (u.toLp 2 volume) +
        wholePlaneScalarMulL2 a ((∂_{wholePlaneBasis j} u).toLp 2 volume)) := by
  unfold HasWholePlaneL2WeakDerivative
  rw [wholePlaneScalarMulL2_schwartz_toTempered]
  rw [lineDeriv_smulLeft_tempered]
  rw [ha]
  rw [map_add]
  rw [wholePlaneScalarMulL2_schwartz_toTempered,
    wholePlaneScalarMulL2_schwartz_toTempered]
  abel

/-- The scalar whole-plane weak derivative graph is closed in `L² × L²`. -/
theorem HasWholePlaneL2WeakDerivative.closed_of_tendsto
    {j : Fin 2} {u du : WholePlaneScalarL2}
    {useq duseq : ℕ → WholePlaneScalarL2}
    (hseq : ∀ n, HasWholePlaneL2WeakDerivative j (useq n) (duseq n))
    (hu : Filter.Tendsto useq Filter.atTop (nhds u))
    (hdu : Filter.Tendsto duseq Filter.atTop (nhds du)) :
    HasWholePlaneL2WeakDerivative j u du := by
  unfold HasWholePlaneL2WeakDerivative at hseq ⊢
  let D := LineDeriv.lineDerivOpCLM ℂ
    (TemperedDistribution WholePlane ℂ) (wholePlaneBasis j)
  have hleft : Filter.Tendsto
      (fun n => D (wholePlaneL2ToTempered ℂ (useq n))) Filter.atTop
      (nhds (D (wholePlaneL2ToTempered ℂ u))) :=
    (D.continuous.tendsto _).comp
      (((wholePlaneL2ToTempered ℂ).continuous.tendsto u).comp hu)
  have hright : Filter.Tendsto
      (fun n => wholePlaneL2ToTempered ℂ (duseq n)) Filter.atTop
      (nhds (wholePlaneL2ToTempered ℂ du)) :=
    ((wholePlaneL2ToTempered ℂ).continuous.tendsto du).comp hdu
  apply tendsto_nhds_unique hleft
  exact hright.congr' (Filter.Eventually.of_forall fun n => (hseq n).symm)

/-- Sequential closed-graph form of the scalar Leibniz rule.  The release
core-density theorem supplies this simultaneous graph approximation for every
scalar whole-plane `H¹` field. -/
theorem hasWholePlaneL2WeakDerivative_mul_of_tendsto_schwartz
    {j : Fin 2} {a da : WholePlaneScalarLInf}
    (ha : HasWholePlaneLInfWeakDerivative j a da)
    {u du : WholePlaneScalarL2}
    (useq : ℕ → SchwartzMap WholePlane ℂ)
    (hu : Filter.Tendsto
      (fun n => (useq n).toLp 2 volume) Filter.atTop (nhds u))
    (hdu : Filter.Tendsto
      (fun n => (∂_{wholePlaneBasis j} (useq n)).toLp 2 volume)
      Filter.atTop (nhds du)) :
    HasWholePlaneL2WeakDerivative j
      (wholePlaneScalarMulL2 a u)
      (wholePlaneScalarMulL2 da u + wholePlaneScalarMulL2 a du) := by
  apply HasWholePlaneL2WeakDerivative.closed_of_tendsto
    (useq := fun n => wholePlaneScalarMulL2 a ((useq n).toLp 2 volume))
    (duseq := fun n =>
      wholePlaneScalarMulL2 da ((useq n).toLp 2 volume) +
        wholePlaneScalarMulL2 a
          ((∂_{wholePlaneBasis j} (useq n)).toLp 2 volume))
  · intro n
    exact hasWholePlaneL2WeakDerivative_mul_schwartz ha (useq n)
  · exact ((wholePlaneScalarMulL2 a).continuous.tendsto u).comp hu
  · exact (((wholePlaneScalarMulL2 da).continuous.tendsto u).comp hu).add
      (((wholePlaneScalarMulL2 a).continuous.tendsto du).comp hdu)

/-- A bounded scalar coefficient together with both of its bounded weak
derivatives.  This is the precise quotient-level `W¹,∞` certificate needed
by the multiplier theorem. -/
structure WholePlaneScalarW1InfCertificate where
  /-- The bounded scalar coefficient. -/
  value : WholePlaneScalarLInf
  /-- Its two bounded weak coordinate derivatives. -/
  deriv : Fin 2 → WholePlaneScalarLInf
  hasWeakDerivative : ∀ j,
    HasWholePlaneLInfWeakDerivative j value (deriv j)

/-- Multiplication by a certified `W¹,∞` coefficient satisfies the weak
Leibniz rule for every scalar whole-plane `H¹` field. -/
theorem hasWholePlaneL2WeakDerivative_mul_h1
    (a : WholePlaneScalarW1InfCertificate)
    (u : WholePlaneScalarH1) (j : Fin 2) :
    HasWholePlaneL2WeakDerivative j
      (wholePlaneScalarMulL2 a.value (wholePlaneH1Embedding ℂ u))
      (wholePlaneScalarMulL2 (a.deriv j) (wholePlaneH1Embedding ℂ u) +
        wholePlaneScalarMulL2 a.value
          (wholePlaneH1FirstDerivative ℂ j u)) := by
  obtain ⟨useq, hu, hdu⟩ :=
    exists_schwartz_tendsto_wholePlaneScalarH1 u
  exact hasWholePlaneL2WeakDerivative_mul_of_tendsto_schwartz
    (a.hasWeakDerivative j) useq hu (hdu j)

/-- The ambient first-order jet obtained by multiplying a scalar `H¹` field
by a certified `W¹,∞` coefficient. -/
def wholePlaneScalarMulH1Ambient
    (a : WholePlaneScalarW1InfCertificate) :
    WholePlaneScalarH1 →L[ℂ] WholePlaneH1Ambient ℂ :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : WholePlaneJet1Index => WholePlaneScalarL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun q => q.elim
      ((wholePlaneScalarMulL2 a.value).comp
        (wholePlaneH1Embedding ℂ))
      (fun j =>
        (wholePlaneScalarMulL2 (a.deriv j)).comp
            (wholePlaneH1Embedding ℂ) +
          (wholePlaneScalarMulL2 a.value).comp
            (wholePlaneH1FirstDerivative ℂ j)))

/-- Value coordinate of the scalar product jet on `H¹`: the `L²` product `a·u`. -/
@[simp] theorem wholePlaneScalarMulH1Ambient_none
    (a : WholePlaneScalarW1InfCertificate) (u : WholePlaneScalarH1) :
    wholePlaneScalarMulH1Ambient a u none =
      wholePlaneScalarMulL2 a.value (wholePlaneH1Embedding ℂ u) := by
  rfl

/-- First-derivative coordinate of the scalar product jet on `H¹`: the Leibniz expression
`(∂_j a)·u + a·(∂_j u)`. -/
@[simp] theorem wholePlaneScalarMulH1Ambient_some
    (a : WholePlaneScalarW1InfCertificate) (u : WholePlaneScalarH1)
    (j : Fin 2) :
    wholePlaneScalarMulH1Ambient a u (some j) =
      wholePlaneScalarMulL2 (a.deriv j) (wholePlaneH1Embedding ℂ u) +
        wholePlaneScalarMulL2 a.value
          (wholePlaneH1FirstDerivative ℂ j u) := by
  rfl

/-- Multiplication by a certified scalar `W¹,∞` coefficient, as a bounded
complex-linear operator on the complete whole-plane weak `H¹` graph. -/
def wholePlaneScalarMulH1
    (a : WholePlaneScalarW1InfCertificate) :
    WholePlaneScalarH1 →L[ℂ] WholePlaneScalarH1 :=
  (wholePlaneScalarMulH1Ambient a).codRestrict
    (wholePlaneH1Graph ℂ) (fun u => by
      rw [mem_wholePlaneH1Graph_iff]
      intro j
      exact hasWholePlaneL2WeakDerivative_mul_h1 a u j)

/-- Multiplication by a certified `W¹,∞` coefficient has physical `L²` field the product
`a·u`. -/
theorem wholePlaneH1Embedding_scalarMulH1
    (a : WholePlaneScalarW1InfCertificate) (u : WholePlaneScalarH1) :
    wholePlaneH1Embedding ℂ (wholePlaneScalarMulH1 a u) =
      wholePlaneScalarMulL2 a.value (wholePlaneH1Embedding ℂ u) := by
  rfl

/-- Multiplication by a certified `W¹,∞` coefficient stores as its `j`-th weak derivative the
Leibniz expression `(∂_j a)·u + a·(∂_j u)`. -/
theorem wholePlaneH1FirstDerivative_scalarMulH1
    (a : WholePlaneScalarW1InfCertificate) (u : WholePlaneScalarH1)
    (j : Fin 2) :
    wholePlaneH1FirstDerivative ℂ j (wholePlaneScalarMulH1 a u) =
      wholePlaneScalarMulL2 (a.deriv j) (wholePlaneH1Embedding ℂ u) +
        wholePlaneScalarMulL2 a.value
          (wholePlaneH1FirstDerivative ℂ j u) := by
  rfl

end

end FastDynamo
