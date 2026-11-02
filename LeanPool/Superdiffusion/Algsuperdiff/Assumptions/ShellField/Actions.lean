/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Assumptions.ShellField.Basic
public import LeanPool.Superdiffusion.Algsuperdiff.Probability.RegCoeffFieldOperations
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Actions

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Exact transformations of regular shell fields

The actions in this module are the literal transformations used in ABK26:
amplitude scaling, real spatial translation, spatial scaling, triadic shell
scaling, negation, and signed-permutation conjugation.  Each transformation
acts on the stored first and second derivatives by the exact chain rule.
-/

namespace Algsuperdiff.Frozen.Assumptions.ShellField

open HCPolySupport
open scoped Matrix.Norms.Elementwise

/-! ## Instance caches for the derivative carriers

The derivative carrier `Vec d →L[ℝ] Mat d` and the Hessian carrier
`Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)` are searched hundreds of times while
elaborating this file.  Caching the recurring classes once at module level
(outside the section, so that every declaration sees them) turns each search
into a single step.  Every cache below is literally the instance Lean would
otherwise rediscover.
-/

-- The `NormedSpace` instance is cached *first*, from the bare `inferInstance`
-- term (the same single-level recipe as the sibling `Basic.lean` fix, whose
-- `NormedAddCommGroup`/`NormedSpace` caches for this exact carrier this file
-- inherits via import).  Every algebraic class below it is then a *direct
-- projection* off this one instance (`.toModule`, `.toDistribMulAction`, …)
-- rather than a second, independent `inferInstance` search.  Two independent
-- blind searches for the same class can land on different (though defeq)
-- instance terms for a `ContinuousLinearMap` carrier in this mathlib version
-- — e.g. a `Module` found by unifying straight from `NormedSpace.toModule`
-- versus one found some other way — and that mismatch is enough to make
-- `compL`/`flip` applications fail with an instance-path diamond even though
-- both sides are propositionally equal.  Projecting everything from one root
-- instance keeps the whole file on a single, consistent path.
noncomputable instance instNormedSpaceDerivCarrier (d : ℕ) :
    NormedSpace ℝ (Vec d →L[ℝ] Mat d) := inferInstance

noncomputable instance instTopDerivCarrier (d : ℕ) :
    TopologicalSpace (Vec d →L[ℝ] Mat d) := inferInstance

noncomputable instance instAddCommMonoidDerivCarrier (d : ℕ) :
    AddCommMonoid (Vec d →L[ℝ] Mat d) := inferInstance

noncomputable instance instModuleDerivCarrier (d : ℕ) :
    Module ℝ (Vec d →L[ℝ] Mat d) :=
  (instNormedSpaceDerivCarrier d).toModule

-- `DistribMulAction` is deliberately a plain `def`, not a registered
-- `instance`: once it is a global instance, blind searches elsewhere for
-- `Module`/`Semiring`-adjacent classes on the *Hessian* carrier (which
-- itself needs `DistribMulAction`/`Module` on this deriv carrier as an
-- internal subgoal) gain an extra candidate to explore and the bare `c • H`
-- notation search for the Hessian type times out at default heartbeats.
-- Kept as a named `def` purely so the explicit `@HasFDerivAt.const_smul`
-- applications below can still pass it in directly.
/-- The distributive scalar action on the shell derivative carrier. -/
@[instance_reducible] noncomputable def instDistribMulActionDerivCarrier (d : ℕ) :
    DistribMulAction ℝ (Vec d →L[ℝ] Mat d) :=
  (instModuleDerivCarrier d).toDistribMulAction

noncomputable instance instMulActionDerivCarrier (d : ℕ) :
    MulAction ℝ (Vec d →L[ℝ] Mat d) :=
  (instModuleDerivCarrier d).toDistribMulAction.toMulAction

noncomputable instance instSMulCommClassDerivCarrier (d : ℕ) :
    SMulCommClass ℝ ℝ (Vec d →L[ℝ] Mat d) :=
  @smulCommClass_self ℝ (Vec d →L[ℝ] Mat d) _ (instMulActionDerivCarrier d)

noncomputable instance instIsBoundedSMulDerivCarrier (d : ℕ) :
    IsBoundedSMul ℝ (Vec d →L[ℝ] Mat d) :=
  NormedSpace.toIsBoundedSMul

noncomputable instance instContinuousConstSMulDerivCarrier (d : ℕ) :
    ContinuousConstSMul ℝ (Vec d →L[ℝ] Mat d) := inferInstance

-- Same recipe one level up: the Hessian's `NormedAddCommGroup`/`NormedSpace`
-- instances are the direct terms `ContinuousLinearMap.toNormedAddCommGroup` /
-- `.toNormedSpace` (needing exactly the `SMulCommClass` cached above), and
-- `Module` is a projection off the cached `NormedSpace`, not a fresh search.
noncomputable instance instNormedAddCommGroupHessianCarrier (d : ℕ) :
    NormedAddCommGroup (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable instance instNormedSpaceHessianCarrier (d : ℕ) :
    NormedSpace ℝ (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :=
  ContinuousLinearMap.toNormedSpace

noncomputable instance instTopHessianCarrier (d : ℕ) :
    TopologicalSpace (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) := inferInstance

noncomputable instance instAddCommMonoidHessianCarrier (d : ℕ) :
    AddCommMonoid (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) := inferInstance

noncomputable instance instModuleHessianCarrier (d : ℕ) :
    Module ℝ (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :=
  (instNormedSpaceHessianCarrier d).toModule

noncomputable instance instSMulCommClassHessianCarrier (d : ℕ) :
    SMulCommClass ℝ ℝ (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :=
  @smulCommClass_self ℝ (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) _
    (instModuleHessianCarrier d).toDistribMulAction.toMulAction

noncomputable instance instIsBoundedSMulHessianCarrier (d : ℕ) :
    IsBoundedSMul ℝ (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :=
  @NormedSpace.toIsBoundedSMul ℝ (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) _
    (instNormedAddCommGroupHessianCarrier d).toSeminormedAddCommGroup
    (instNormedSpaceHessianCarrier d)

-- `ContinuousLinearMap` carries its own native `SMul` instance
-- (`ContinuousLinearMap.instSMul`); deriving this from `instModuleHessianCarrier`
-- via `.toDistribMulAction.toMulAction.toSMul` produces a second, different
-- (though defeq) `SMul` term and the same instance-path diamond as before.
-- Leaving the `SMul` slots as `_` lets blind search land on the native one.
noncomputable instance instContinuousConstSMulHessianCarrier (d : ℕ) :
    ContinuousConstSMul ℝ (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :=
  @ContinuousSMul.continuousConstSMul ℝ (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) _ _ _
    (@IsBoundedSMul.continuousSMul ℝ (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) _ _ _ _ _
      (instIsBoundedSMulHessianCarrier d))

noncomputable instance instSMulHessianEndomorphisms (d : ℕ) :
    SMul ℝ ((Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) →L[ℝ]
      (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d))) :=
  @ContinuousLinearMap.instSMul ℝ ℝ _ _ (RingHom.id ℝ) _ _ _ _ _ _ _ _ ℝ _
    (instSMulCommClassHessianCarrier d) (instContinuousConstSMulHessianCarrier d)

noncomputable instance instNormedSpaceEndoCarrier (d : ℕ) :
    NormedSpace ℝ (Vec d →L[ℝ] Vec d) := inferInstance

noncomputable section

variable {d : ℕ}

/-! ## Amplitude scaling -/

/-- Continuous scalar multiplication of matrix values. -/
def valueScaleMap (c : ℝ) : C(Mat d, Mat d) :=
  ⟨fun M ↦ c • M, continuous_id.const_smul c⟩

/-- Continuous scalar multiplication of first derivatives. -/
def derivScaleMap (c : ℝ) :
    C(Vec d →L[ℝ] Mat d, Vec d →L[ℝ] Mat d) :=
  ⟨fun D ↦ c • D, continuous_id.const_smul c⟩

/-- Continuous scalar multiplication of second derivatives. -/
def secondDerivScaleMap (c : ℝ) :
    C(Vec d →L[ℝ] (Vec d →L[ℝ] Mat d),
      Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :=
  ⟨fun H ↦ c • H, continuous_id.const_smul c⟩

/-- Scale the values and both stored derivatives of an ambient shell. -/
def scaleAmbient (c : ℝ) :
    ShellAmbient d → ShellAmbient d := fun p ↦
  ((valueScaleMap c).comp p.1,
    ((derivScaleMap c).comp p.2.1,
      (secondDerivScaleMap c).comp p.2.2))

private theorem continuous_scaleAmbient (c : ℝ) :
    Continuous (scaleAmbient (d := d) c) :=
  ((ContinuousMap.continuous_postcomp (valueScaleMap c)).comp continuous_fst).prodMk
    (((ContinuousMap.continuous_postcomp (derivScaleMap c)).comp
      continuous_snd.fst).prodMk
        ((ContinuousMap.continuous_postcomp (secondDerivScaleMap c)).comp
          continuous_snd.snd))

/-- Multiply every matrix value by `c`. -/
def scale (c : ℝ) (j : ShellField d) : ShellField d :=
  ⟨scaleAmbient c j.1, by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      simpa only [scaleAmbient, valueScaleMap, derivScaleMap,
        ContinuousMap.comp_apply] using! (j.hasFDerivAt x).const_smul c
    · intro x
      have hderiv : HasFDerivAt (⇑(deriv j)) (secondDeriv j x) x :=
        j.deriv_hasFDerivAt x
      -- `HasFDerivAt.const_smul`'s blind instance search does not resolve
      -- `DistribMulAction`/`SMulCommClass`/`ContinuousConstSMul` for this
      -- project carrier under this mathlib version (it leaves them as
      -- unassigned metavariables no candidate — including our own cache —
      -- can unify against); passing the three cached instances explicitly
      -- sidesteps the search entirely.
      have h :=
        @HasFDerivAt.const_smul ℝ _ (Vec d) _ _ (Vec d →L[ℝ] Mat d) _ _
          _ _ _ ℝ _ (instDistribMulActionDerivCarrier d)
          (instSMulCommClassDerivCarrier d)
          (instContinuousConstSMulDerivCarrier d) hderiv c
      simpa only [scaleAmbient, derivScaleMap, secondDerivScaleMap,
        ContinuousMap.comp_apply, ContinuousMap.coe_mk,
        ContinuousMap.coe_comp, Function.comp_def] using! h
    · intro x i k
      change c * j x i k = -(c * j x k i)
      rw [j.skew_entry x i k]
      ring⟩

@[simp]
theorem scale_apply (c : ℝ) (j : ShellField d) (x : Vec d) :
    scale c j x = c • j x :=
  rfl

@[simp]
theorem scale_deriv (c : ℝ) (j : ShellField d) (x : Vec d) :
    deriv (scale c j) x = c • deriv j x :=
  rfl

@[simp]
theorem scale_secondDeriv (c : ℝ) (j : ShellField d) (x : Vec d) :
    secondDeriv (scale c j) x = c • secondDeriv j x :=
  rfl

theorem continuous_scale (c : ℝ) :
    Continuous (scale (d := d) c) :=
  Continuous.subtype_mk
    ((continuous_scaleAmbient c).comp continuous_subtype_val)
    (fun j ↦ (scale c j).2)

/-! ## Real spatial translations -/

/-- Continuous translation of the spatial argument. -/
def translateMap (z : Vec d) : C(Vec d, Vec d) :=
  ⟨fun x ↦ x + z, continuous_id.add continuous_const⟩

/-- Translate the values and both stored derivatives of an ambient shell. -/
def translateAmbient (z : Vec d) :
    ShellAmbient d → ShellAmbient d := fun p ↦
  (p.1.comp (translateMap z),
    (p.2.1.comp (translateMap z), p.2.2.comp (translateMap z)))

private theorem continuous_translateAmbient (z : Vec d) :
    Continuous (translateAmbient (d := d) z) :=
  ((ContinuousMap.continuous_precomp (translateMap z)).comp continuous_fst).prodMk
    (((ContinuousMap.continuous_precomp (translateMap z)).comp
      continuous_snd.fst).prodMk
        ((ContinuousMap.continuous_precomp (translateMap z)).comp
          continuous_snd.snd))

/-- Real translation in the manuscript convention `j(x + z)`. -/
def translate (z : Vec d) (j : ShellField d) : ShellField d :=
  ⟨translateAmbient z j.1, by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      simpa only [translateAmbient, translateMap, ContinuousMap.comp_apply,
        Function.comp_def] using!
        (j.hasFDerivAt (x + z)).comp x ((hasFDerivAt_id x).add_const z)
    · intro x
      simpa only [translateAmbient, translateMap, ContinuousMap.comp_apply,
        Function.comp_def] using!
        (j.deriv_hasFDerivAt (x + z)).comp x
          ((hasFDerivAt_id x).add_const z)
    · intro x i k
      simpa only [translateAmbient, translateMap, ContinuousMap.comp_apply] using!
        j.skew_entry (x + z) i k⟩

@[simp]
theorem translate_apply (z : Vec d) (j : ShellField d) (x : Vec d) :
    translate z j x = j (x + z) :=
  rfl

@[simp]
theorem translate_deriv (z : Vec d) (j : ShellField d) (x : Vec d) :
    deriv (translate z j) x = deriv j (x + z) :=
  rfl

@[simp]
theorem translate_secondDeriv (z : Vec d) (j : ShellField d) (x : Vec d) :
    secondDeriv (translate z j) x = secondDeriv j (x + z) :=
  rfl

/-- Translation by the zero vector is the identity on shell fields. -/
@[simp]
theorem translate_zero (j : ShellField d) :
    translate (0 : Vec d) j = j :=
  ext fun x => by rw [translate_apply, add_zero]

theorem continuous_translate (z : Vec d) :
    Continuous (translate (d := d) z) :=
  Continuous.subtype_mk
    ((continuous_translateAmbient z).comp continuous_subtype_val)
    (fun j ↦ (translate z j).2)

theorem measurable_translate (z : Vec d) :
    Measurable (translate (d := d) z) :=
  (continuous_translate z).measurable

/-! ## Spatial scaling and triadic shell scaling -/

/-- Continuous dilation of the spatial argument. -/
def spatialMap (r : ℝ) : C(Vec d, Vec d) :=
  ⟨fun x ↦ r • x, continuous_id.const_smul r⟩

/-- The second-derivative chain rule for spatial dilation. -/
def spatialSecondDerivativeMap (r : ℝ) :
    (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) →L[ℝ]
      (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :=
  ((r • ContinuousLinearMap.id ℝ
      (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d))) :
      (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) →L[ℝ]
        (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d))).comp
    ((ContinuousLinearMap.compL ℝ (Vec d) (Vec d)
      (Vec d →L[ℝ] Mat d)).flip
        (r • ContinuousLinearMap.id ℝ (Vec d) : Vec d →L[ℝ] Vec d))

/-- The continuous-map bundle for the second-derivative dilation action. -/
def spatialSecondDerivativeContinuousMap (r : ℝ) :
    C(Vec d →L[ℝ] (Vec d →L[ℝ] Mat d),
      Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :=
  ⟨spatialSecondDerivativeMap r, (spatialSecondDerivativeMap r).continuous⟩

private theorem spatialSecondDerivativeMap_eq_smul (r : ℝ)
    (H : Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :
    spatialSecondDerivativeMap r H = r ^ 2 • H := by
  ext v w i k
  change r * H (r • v) w i k = r ^ 2 * H v w i k
  rw [H.map_smul]
  change r * (r * H v w i k) = r ^ 2 * H v w i k
  ring

/-- Dilate a shell's spatial argument with the corresponding derivative factors. -/
def spatialScaleAmbient (r : ℝ) :
    ShellAmbient d → ShellAmbient d := fun p ↦
  (p.1.comp (spatialMap r),
    ((derivScaleMap r).comp (p.2.1.comp (spatialMap r)),
      (spatialSecondDerivativeContinuousMap r).comp
        (p.2.2.comp (spatialMap r))))

private theorem continuous_spatialScaleAmbient (r : ℝ) :
    Continuous (spatialScaleAmbient (d := d) r) :=
  ((ContinuousMap.continuous_precomp (spatialMap r)).comp continuous_fst).prodMk
    ((((ContinuousMap.continuous_postcomp (derivScaleMap r)).comp
      (ContinuousMap.continuous_precomp (spatialMap r))).comp
        continuous_snd.fst).prodMk
      (((ContinuousMap.continuous_postcomp
        (spatialSecondDerivativeContinuousMap r)).comp
          (ContinuousMap.continuous_precomp (spatialMap r))).comp
            continuous_snd.snd))

/-- Precompose with `x ↦ r • x`; the derivative carries the chain-rule
factor `r`. -/
def spatialScale (r : ℝ) (j : ShellField d) : ShellField d :=
  ⟨spatialScaleAmbient r j.1, by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      have h := (j.hasFDerivAt (r • x)).comp x
        ((hasFDerivAt_id x).const_smul r)
      have heq : (j.deriv (r • x)).comp (r • ContinuousLinearMap.id ℝ (Vec d)) =
          r • j.deriv (r • x) := by
        ext v
        simp only [ContinuousLinearMap.comp_apply, smul_apply,
          ContinuousLinearMap.id_apply, (j.deriv (r • x)).map_smul]
      simpa only [spatialScaleAmbient, spatialMap, derivScaleMap,
        ContinuousMap.comp_apply, ContinuousMap.coe_mk, ContinuousMap.coe_comp,
        Function.comp_def] using! heq ▸ h
    · intro x
      have hinner := (j.deriv_hasFDerivAt (r • x)).comp x
        ((hasFDerivAt_id x).const_smul r)
      have houter := @HasFDerivAt.const_smul ℝ _ (Vec d) _ _
        (Vec d →L[ℝ] Mat d) _ _ _ _ _ ℝ _ (instDistribMulActionDerivCarrier d)
        (instSMulCommClassDerivCarrier d)
        (instContinuousConstSMulDerivCarrier d) hinner r
      simpa only [spatialScaleAmbient, spatialMap, derivScaleMap,
        spatialSecondDerivativeContinuousMap, spatialSecondDerivativeMap,
        ContinuousMap.comp_apply, Function.comp_def] using! houter
    · intro x i k
      simpa only [spatialScaleAmbient, spatialMap, ContinuousMap.comp_apply] using!
        j.skew_entry (r • x) i k⟩

@[simp]
theorem spatialScale_apply (r : ℝ) (j : ShellField d) (x : Vec d) :
    spatialScale r j x = j (r • x) :=
  rfl

@[simp]
theorem spatialScale_deriv (r : ℝ) (j : ShellField d) (x : Vec d) :
    deriv (spatialScale r j) x = r • deriv j (r • x) :=
  rfl

@[simp]
theorem spatialScale_secondDeriv (r : ℝ) (j : ShellField d) (x : Vec d) :
    secondDeriv (spatialScale r j) x =
      r ^ 2 • secondDeriv j (r • x) :=
  spatialSecondDerivativeMap_eq_smul r (secondDeriv j (r • x))

theorem continuous_spatialScale (r : ℝ) :
    Continuous (spatialScale (d := d) r) :=
  Continuous.subtype_mk
    ((continuous_spatialScaleAmbient r).comp continuous_subtype_val)
    (fun j ↦ (spatialScale r j).2)

theorem measurable_spatialScale (r : ℝ) :
    Measurable (spatialScale (d := d) r) :=
  (continuous_spatialScale r).measurable

/-- Combined amplitude and spatial scaling. -/
def rescale (c r : ℝ) (j : ShellField d) : ShellField d :=
  scale c (spatialScale r j)

theorem continuous_rescale (c r : ℝ) :
    Continuous (rescale (d := d) c r) :=
  (continuous_scale c).comp (continuous_spatialScale r)

/-- The literal marginal scaling action `3^(γ k) j(3^(-k) ·)`. -/
def triadicScale (gamma : ℝ) (k : ℤ) (j : ShellField d) : ShellField d :=
  rescale (Real.rpow 3 (gamma * (k : ℝ))) (((3 : ℝ) ^ k)⁻¹) j

@[simp]
theorem triadicScale_apply (gamma : ℝ) (k : ℤ) (j : ShellField d)
    (x : Vec d) :
    triadicScale gamma k j x =
      Real.rpow 3 (gamma * (k : ℝ)) • j ((((3 : ℝ) ^ k)⁻¹) • x) :=
  rfl

theorem continuous_triadicScale (gamma : ℝ) (k : ℤ) :
    Continuous (triadicScale (d := d) gamma k) :=
  continuous_rescale _ _

theorem measurable_triadicScale (gamma : ℝ) (k : ℤ) :
    Measurable (triadicScale (d := d) gamma k) :=
  (continuous_triadicScale gamma k).measurable

/-! ## Negation -/

/-- Value and derivative negation, as required by J3. -/
def negate (j : ShellField d) : ShellField d :=
  scale (-1) j

@[simp]
theorem negate_apply (j : ShellField d) (x : Vec d) :
    negate j x = -j x := by
  simp only [negate, scale_apply, neg_one_smul]

@[simp]
theorem negate_deriv (j : ShellField d) (x : Vec d) :
    deriv (negate j) x = -deriv j x := by
  apply ContinuousLinearMap.ext
  intro v
  ext i k
  change (-1 : ℝ) * deriv j x v i k = -deriv j x v i k
  ring

@[simp]
theorem negate_secondDeriv (j : ShellField d) (x : Vec d) :
    secondDeriv (negate j) x = -secondDeriv j x := by
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  ext i k
  change (-1 : ℝ) * secondDeriv j x v w i k =
    -secondDeriv j x v w i k
  ring

theorem continuous_negate : Continuous (negate (d := d)) :=
  continuous_scale (-1)

theorem measurable_negate : Measurable (negate (d := d)) :=
  continuous_negate.measurable

/-! ## Signed-permutation conjugation -/

/-- Matrix multiplication bundled as a continuous linear map on vectors. -/
def matVecContinuousLinearMap (R : Mat d) : Vec d →L[ℝ] Vec d :=
  ⟨Matrix.toLin' R, (Matrix.toLin' R).continuous_of_finiteDimensional⟩

@[simp]
theorem matVecContinuousLinearMap_apply (R : Mat d) (x : Vec d) :
    matVecContinuousLinearMap R x = matVecMul R x :=
  rfl

/-- The linear map sending a matrix to its conjugate by `R`. -/
def conjugateLinearMap (R : Mat d) : Mat d →ₗ[ℝ] Mat d where
  toFun M := matTranspose R * M * R
  map_add' M N := by
    rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c M := by
    simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

/-- Matrix conjugation bundled as a continuous linear map. -/
def conjugateContinuousLinearMap (R : Mat d) : Mat d →L[ℝ] Mat d :=
  ⟨conjugateLinearMap R,
    (conjugateLinearMap R).continuous_of_finiteDimensional⟩

@[simp]
theorem conjugateContinuousLinearMap_apply (R M : Mat d) :
    conjugateContinuousLinearMap R M = matTranspose R * M * R :=
  rfl

/-- The exact derivative action `D ↦ (M ↦ RᵀMR) ∘ D ∘ (v ↦ Rv)`. -/
def rotateDerivativeMap (R : Mat d) :
    (Vec d →L[ℝ] Mat d) →L[ℝ] (Vec d →L[ℝ] Mat d) :=
  (ContinuousLinearMap.compL ℝ (Vec d) (Mat d) (Mat d)
      (conjugateContinuousLinearMap R)).comp
    ((ContinuousLinearMap.compL ℝ (Vec d) (Vec d) (Mat d)).flip
      (matVecContinuousLinearMap R))

@[simp]
theorem rotateDerivativeMap_apply (R : Mat d)
    (D : Vec d →L[ℝ] Mat d) (v : Vec d) :
    rotateDerivativeMap R D v =
      matTranspose R * D (matVecMul R v) * R :=
  rfl

/-- The exact Hessian action
`H ↦ (v ↦ w ↦ Rᵀ H (Rv) (Rw) R)`. -/
def rotateSecondDerivativeMap (R : Mat d) :
    (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) →L[ℝ]
      (Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :=
  (ContinuousLinearMap.compL ℝ (Vec d)
      (Vec d →L[ℝ] Mat d) (Vec d →L[ℝ] Mat d)
      (rotateDerivativeMap R)).comp
    ((ContinuousLinearMap.compL ℝ (Vec d) (Vec d)
      (Vec d →L[ℝ] Mat d)).flip
        (matVecContinuousLinearMap R : Vec d →L[ℝ] Vec d))

/-- The continuous matrix-value map used by the rotation action. -/
def rotateValueMap (R : Mat d) : C(Mat d, Mat d) :=
  ⟨conjugateContinuousLinearMap R, (conjugateContinuousLinearMap R).continuous⟩

/-- The continuous spatial map used by the rotation action. -/
def rotateDomainMap (R : Mat d) : C(Vec d, Vec d) :=
  ⟨matVecContinuousLinearMap R, (matVecContinuousLinearMap R).continuous⟩

/-- The continuous first-derivative map used by the rotation action. -/
def rotateDerivativeContinuousMap (R : Mat d) :
    C(Vec d →L[ℝ] Mat d, Vec d →L[ℝ] Mat d) :=
  ⟨rotateDerivativeMap R, (rotateDerivativeMap R).continuous⟩

/-- The continuous second-derivative map used by the rotation action. -/
def rotateSecondDerivativeContinuousMap (R : Mat d) :
    C(Vec d →L[ℝ] (Vec d →L[ℝ] Mat d),
      Vec d →L[ℝ] (Vec d →L[ℝ] Mat d)) :=
  ⟨rotateSecondDerivativeMap R, (rotateSecondDerivativeMap R).continuous⟩

/-- Rotate a shell's argument, values and stored derivatives together. -/
def rotateAmbient (R : Mat d) :
    ShellAmbient d → ShellAmbient d := fun p ↦
  ((rotateValueMap R).comp (p.1.comp (rotateDomainMap R)),
    ((rotateDerivativeContinuousMap R).comp
      (p.2.1.comp (rotateDomainMap R)),
      (rotateSecondDerivativeContinuousMap R).comp
        (p.2.2.comp (rotateDomainMap R))))

private theorem continuous_rotateAmbient (R : Mat d) :
    Continuous (rotateAmbient (d := d) R) :=
  ((ContinuousMap.continuous_postcomp (rotateValueMap R)).comp
      ((ContinuousMap.continuous_precomp (rotateDomainMap R)).comp
        continuous_fst)).prodMk
    (((ContinuousMap.continuous_postcomp (rotateDerivativeContinuousMap R)).comp
      ((ContinuousMap.continuous_precomp (rotateDomainMap R)).comp
        continuous_snd.fst)).prodMk
      ((ContinuousMap.continuous_postcomp
          (rotateSecondDerivativeContinuousMap R)).comp
        ((ContinuousMap.continuous_precomp (rotateDomainMap R)).comp
          continuous_snd.snd)))

/-- The signed-permutation action `j(x) ↦ Rᵀ j(Rx) R`. -/
def rotate (R : Mat d) (_hR : IsSignedPermutationMatrix R)
    (j : ShellField d) : ShellField d :=
  ⟨rotateAmbient R j.1, by
    refine ⟨?_, ?_, ?_⟩
    · intro x
      have hinner := (j.hasFDerivAt (matVecMul R x)).comp x
        (matVecContinuousLinearMap R).hasFDerivAt
      have houter :=
        (conjugateContinuousLinearMap R).hasFDerivAt.comp x hinner
      simpa only [rotateAmbient, rotateValueMap, rotateDomainMap,
        rotateDerivativeContinuousMap, ContinuousMap.comp_apply,
        conjugateContinuousLinearMap_apply,
        matVecContinuousLinearMap_apply, rotateDerivativeMap_apply] using! houter
    · intro x
      have hinner := (j.deriv_hasFDerivAt (matVecMul R x)).comp x
        (matVecContinuousLinearMap R).hasFDerivAt
      have houter := (rotateDerivativeMap R).hasFDerivAt.comp x hinner
      simpa only [rotateAmbient, rotateDomainMap,
        rotateDerivativeContinuousMap, rotateSecondDerivativeContinuousMap,
        ContinuousMap.comp_apply, matVecContinuousLinearMap_apply,
        rotateSecondDerivativeMap] using! houter
    · intro x i k
      have hskew : matTranspose (j (matVecMul R x)) =
          -j (matVecMul R x) :=
        j.skew (matVecMul R x)
      have hmatrix :
          matTranspose (matTranspose R * j (matVecMul R x) * R) =
            -(matTranspose R * j (matVecMul R x) * R) := by
        calc
          matTranspose (matTranspose R * j (matVecMul R x) * R) =
              matTranspose R * matTranspose (j (matVecMul R x)) * R := by
                simp only [matTranspose, Matrix.transpose_mul,
                  Matrix.transpose_transpose, Matrix.mul_assoc]
          _ = matTranspose R * (-j (matVecMul R x)) * R := by
                rw [hskew]
          _ = -(matTranspose R * j (matVecMul R x) * R) := by
                rw [Matrix.mul_neg, Matrix.neg_mul]
      exact congrFun (congrFun hmatrix k) i⟩

@[simp]
theorem rotate_apply (R : Mat d) (hR : IsSignedPermutationMatrix R)
    (j : ShellField d) (x : Vec d) :
    rotate R hR j x = matTranspose R * j (matVecMul R x) * R :=
  rfl

theorem continuous_rotate (R : Mat d) (hR : IsSignedPermutationMatrix R) :
    Continuous (rotate (d := d) R hR) :=
  Continuous.subtype_mk
    ((continuous_rotateAmbient R).comp continuous_subtype_val)
    (fun j ↦ (rotate R hR j).2)

theorem measurable_rotate (R : Mat d) (hR : IsSignedPermutationMatrix R) :
    Measurable (rotate (d := d) R hR) :=
  (continuous_rotate R hR).measurable

/-! ## Compatibility with CoarseGraining regular-field operations -/

theorem forgetShell_translate (z : Vec d) (j : ShellField d) :
    forgetShell (translate z j) = translateReg z (forgetShell j) := by
  apply RegCoeffField.ext
  intro x
  rfl

theorem forgetShell_triadicScale (gamma : ℝ) (k : ℤ)
    (j : ShellField d) :
    forgetShell (triadicScale gamma k j) =
      Algsuperdiff.Probability.triadicLayerScaleReg gamma k (forgetShell j) := by
  apply RegCoeffField.ext
  intro x
  rfl

end

end Algsuperdiff.Frozen.Assumptions.ShellField
