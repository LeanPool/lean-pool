/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.DualNormJunk
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorJointLimit
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorTelescope
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteCubeSolutionRestriction
public import LeanPool.HighContrastHomogenization.Support.Ambient.CoefficientFieldHilbert
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.PublicInternalBridges.CoeffField
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.PublicInternalBridges.EndPoints

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorOriginCubeFields

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Corrector fields on integer-scale origin cubes

Projective local gradients restrict canonically to every integer-scale
centered cube. This module packages corrector gradients, full gradients,
coefficient flux defects, local weak norms, and summable error tails without
choosing pointwise representatives.
-/

open scoped BigOperators ENNReal

namespace HCPolySupport
namespace HighContrast

noncomputable section

open MeasureTheory

/-! ## Restriction to integer-scale origin cubes -/

@[expose]
public noncomputable def originCubeL2RestrictLinear {d : ℕ}
    {n m : ℤ} (hnm : n ≤ m) :
    HilbertVectorL2 (openCubeSet (originCube d m)) →ₗ[ℝ]
      HilbertVectorL2 (openCubeSet (originCube d n)) where
  toFun g :=
    ((Lp.memLp g).mono_measure
      (Measure.restrict_mono_set volume
        (openCubeSet_originCube_subset_of_le hnm))).toLp g
  map_add' f g := by
    let hμ : volumeMeasureOn (openCubeSet (originCube d n)) ≤
        volumeMeasureOn (openCubeSet (originCube d m)) :=
      Measure.restrict_mono_set volume
        (openCubeSet_originCube_subset_of_le hnm)
    change
      ((Lp.memLp (f + g)).mono_measure hμ).toLp (f + g) =
        ((Lp.memLp f).mono_measure hμ).toLp f +
          ((Lp.memLp g).mono_measure hμ).toLp g
    exact
      (MemLp.toLp_congr
        ((Lp.memLp (f + g)).mono_measure hμ)
        (((Lp.memLp f).mono_measure hμ).add
          ((Lp.memLp g).mono_measure hμ))
        ((Lp.coeFn_add f g).filter_mono (ae_mono hμ))).trans
      (MemLp.toLp_add
        ((Lp.memLp f).mono_measure hμ) ((Lp.memLp g).mono_measure hμ))
  map_smul' c f := by
    let hμ : volumeMeasureOn (openCubeSet (originCube d n)) ≤
        volumeMeasureOn (openCubeSet (originCube d m)) :=
      Measure.restrict_mono_set volume
        (openCubeSet_originCube_subset_of_le hnm)
    change
      ((Lp.memLp (c • f)).mono_measure hμ).toLp (c • f) =
        c • ((Lp.memLp f).mono_measure hμ).toLp f
    exact
      (MemLp.toLp_congr
        ((Lp.memLp (c • f)).mono_measure hμ)
        (((Lp.memLp f).mono_measure hμ).const_smul c)
        ((Lp.coeFn_smul c f).filter_mono (ae_mono hμ))).trans
      (MemLp.toLp_const_smul c ((Lp.memLp f).mono_measure hμ))

private theorem originCubeL2RestrictLinear_norm_le {d : ℕ}
    {n m : ℤ} (hnm : n ≤ m)
    (g : HilbertVectorL2 (openCubeSet (originCube d m))) :
    ‖originCubeL2RestrictLinear hnm g‖ ≤ ‖g‖ := by
  let hμ : volumeMeasureOn (openCubeSet (originCube d n)) ≤
      volumeMeasureOn (openCubeSet (originCube d m)) :=
    Measure.restrict_mono_set volume
      (openCubeSet_originCube_subset_of_le hnm)
  change ‖((Lp.memLp g).mono_measure hμ).toLp g‖ ≤ ‖g‖
  rw [Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top g) (eLpNorm_mono_measure g hμ)

/-- Restriction of a Hilbert-vector `L²` class between nested centered
integer-scale origin cubes. -/
@[expose]
noncomputable def originCubeL2Restrict {d : ℕ} {n m : ℤ} (hnm : n ≤ m) :
    HilbertVectorL2 (openCubeSet (originCube d m)) →L[ℝ]
      HilbertVectorL2 (openCubeSet (originCube d n)) :=
  LinearMap.mkContinuous (originCubeL2RestrictLinear hnm) 1 fun g => by
    simpa only [one_mul] using originCubeL2RestrictLinear_norm_le hnm g

/-- Integer-cube restriction agrees almost everywhere with the original
local representative. -/
theorem originCubeL2Restrict_coeFn_ae {d : ℕ} {n m : ℤ}
    (hnm : n ≤ m) (g : HilbertVectorL2 (openCubeSet (originCube d m))) :
    originCubeL2Restrict hnm g
      =ᵐ[volumeMeasureOn (openCubeSet (originCube d n))] g := by
  exact MemLp.coeFn_toLp
    ((Lp.memLp g).mono_measure
      (Measure.restrict_mono_set volume
        (openCubeSet_originCube_subset_of_le hnm)))

/-- Restriction from an origin cube to itself is the identity. -/
@[simp] theorem originCubeL2Restrict_refl {d : ℕ} {n : ℤ} :
    originCubeL2Restrict (d := d) (le_refl n) =
      ContinuousLinearMap.id ℝ
        (HilbertVectorL2 (openCubeSet (originCube d n))) := by
  apply ContinuousLinearMap.ext
  intro g
  apply Lp.ext
  exact originCubeL2Restrict_coeFn_ae (le_refl n) g

/-- The canonical natural exhaustion index covering an integer scale. -/
@[expose]
def originCubeCoverGeneration (n : ℤ) : ℕ :=
  n.toNat

/-- Every integer scale is below its canonical natural cover. -/
theorem le_originCubeCoverGeneration (n : ℤ) :
    n ≤ (originCubeCoverGeneration n : ℤ) := by
  simpa only [originCubeCoverGeneration] using Int.self_le_toNat n

namespace LocalGradientCarrier

/-- The component of a projective local gradient on an arbitrary
integer-scale origin cube. -/
@[expose]
noncomputable def originCubeComponent {d : ℕ}
    (G : LocalGradientCarrier d) (n : ℤ) :
    HilbertVectorL2 (openCubeSet (originCube d n)) :=
  originCubeL2Restrict (le_originCubeCoverGeneration n)
    (component G (originCubeCoverGeneration n))

private theorem component_ae_eq_on_originCube {d : ℕ}
    (G : LocalGradientCarrier d) {n : ℤ} {p q : ℕ}
    (hnp : n ≤ (p : ℤ)) (hnq : n ≤ (q : ℤ)) :
    component G p =ᵐ[volumeMeasureOn (openCubeSet (originCube d n))]
      component G q := by
  by_cases hpq : p ≤ q
  · have hrep := localGradientRestrict_coeFn_ae hpq (component G q)
    rw [restrict_component G hpq] at hrep
    exact hrep.filter_mono <| ae_mono <|
      Measure.restrict_mono_set volume
        (openCubeSet_originCube_subset_of_le hnp)
  · have hqp : q ≤ p := Nat.le_of_not_ge hpq
    have hrep := localGradientRestrict_coeFn_ae hqp (component G p)
    rw [restrict_component G hqp] at hrep
    exact hrep.symm.filter_mono <| ae_mono <|
      Measure.restrict_mono_set volume
        (openCubeSet_originCube_subset_of_le hnq)

/-- Restricting from any natural exhaustion component covering the target
gives the canonical integer component. -/
theorem originCubeComponent_eq_restrict_component {d : ℕ}
    (G : LocalGradientCarrier d) {n : ℤ} (q : ℕ)
    (hnq : n ≤ (q : ℤ)) :
    originCubeComponent G n =
      originCubeL2Restrict hnq (component G q) := by
  apply Lp.ext
  exact
    (originCubeL2Restrict_coeFn_ae
      (le_originCubeCoverGeneration n)
      (component G (originCubeCoverGeneration n))).trans
      ((component_ae_eq_on_originCube G
        (le_originCubeCoverGeneration n) hnq).trans
        (originCubeL2Restrict_coeFn_ae hnq (component G q)).symm)

/-- On natural scales the integer component is the original projective
component. -/
@[simp] theorem originCubeComponent_natCast {d : ℕ}
    (G : LocalGradientCarrier d) (n : ℕ) :
    originCubeComponent G (n : ℤ) = component G n := by
  rw [originCubeComponent_eq_restrict_component G n (le_refl (n : ℤ)),
    originCubeL2Restrict_refl]
  rfl

end LocalGradientCarrier

/-! ## Quotient-safe local weak norms -/

private theorem toVec_toHilbertVectorL2OfVecField_ae {d : ℕ}
    {U : Set (Vec d)} {f : Vec d → Vec d} (hf : MemVectorL2 U f) :
    (fun x => (toHilbertVectorL2OfVecField hf x).toVec)
      =ᵐ[volumeMeasureOn U] f := by
  exact (coeFn_toHilbertVectorL2OfVecField hf).mono fun _ hx => by
    simpa only [hilbertifyVecField, HilbertVec.toVec_ofVec] using
      congrArg HilbertVec.toVec hx

/-- The fail-closed dual pairing depends only on the local a.e. class of its
first field. -/
theorem dualPairing_eq_of_ae_eq_on {d : ℕ} {U : Set (Vec d)}
    {F G : Vec d → Vec d}
    (hFG : F =ᵐ[volumeMeasureOn U] G) (psi : Vec d → Vec d) :
    dualPairing U F psi = dualPairing U G psi := by
  have hdot :
      (fun x => vecDot (F x) (psi x))
        =ᵐ[volume.restrict U] fun x => vecDot (G x) (psi x) := by
    simpa only [volumeMeasureOn, Filter.EventuallyEq] using
      hFG.mono fun x hx => by
        exact congrArg (fun v : Vec d => vecDot v (psi x)) hx
  by_cases hF : IntegrableOn (fun x => vecDot (F x) (psi x)) U volume
  · have hG : IntegrableOn (fun x => vecDot (G x) (psi x)) U volume :=
      (integrableOn_congr_fun_ae hdot).mp hF
    rw [dualPairing_eq_ofReal U F psi hF,
      dualPairing_eq_ofReal U G psi hG]
    apply congrArg ENNReal.ofReal
    unfold volumeAverage
    rw [integral_congr_ae hdot]
  · have hG : ¬ IntegrableOn (fun x => vecDot (G x) (psi x)) U volume := by
      exact fun h => hF ((integrableOn_congr_fun_ae hdot).mpr h)
    rw [dualPairing_eq_top_of_not_integrableOn U F psi hF,
      dualPairing_eq_top_of_not_integrableOn U G psi hG]

/-- The normalized `H⁻¹` dual norm depends only on the local a.e. class. -/
theorem negOneNorm_eq_of_ae_eq_on {d : ℕ} {U : Set (Vec d)}
    {F G : Vec d → Vec d} (hFG : F =ᵐ[volumeMeasureOn U] G) :
    negOneNorm U F = negOneNorm U G := by
  unfold negOneNorm
  apply iSup_congr
  intro psi
  exact dualPairing_eq_of_ae_eq_on hFG psi.1

/-- The normalized negative first-order Sobolev norm of a local `L²` class. -/
@[expose]
noncomputable def localNegOneNorm {d : ℕ} (U : Set (Vec d))
    (F : HilbertVectorL2 U) : ℝ≥0∞ :=
  negOneNorm U fun x => (F x).toVec

/-- The local negative first-order Sobolev norm reads the represented raw
field. -/
theorem localNegOneNorm_toHilbertVectorL2OfVecField {d : ℕ}
    {U : Set (Vec d)} {f : Vec d → Vec d} (hf : MemVectorL2 U f) :
    localNegOneNorm U (toHilbertVectorL2OfVecField hf) = negOneNorm U f := by
  unfold localNegOneNorm
  exact negOneNorm_eq_of_ae_eq_on
    (toVec_toHilbertVectorL2OfVecField_ae hf)

/-! ## Corrector gradients and flux defects -/

private instance originCubeFiniteMeasure (d : ℕ) (n : ℤ) :
    IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube d n))) := by
  simpa only [volumeMeasureOn] using
    (isOpenBoundedConvexDomain_openCubeSet
      (originCube d n)).isFiniteMeasure_restrict_volume

private theorem memVectorL2_const_originCube {d : ℕ}
    (e : Vec d) (n : ℤ) :
    MemVectorL2 (openCubeSet (originCube d n)) (fun _ => e) := by
  simpa using
    (MeasureTheory.memLp_const
      (μ := volumeMeasureOn (openCubeSet (originCube d n)))
      (p := (2 : ENNReal)) (c := e))

/-- The local corrector-gradient class at an integer scale. -/
@[expose]
noncomputable def correctorGradientOnOriginCube {d : ℕ}
    (Phi : Vec d → NormalizedLocalH1Carrier d) (e : Vec d) (n : ℤ) :
    HilbertVectorL2 (openCubeSet (originCube d n)) :=
  LocalGradientCarrier.originCubeComponent (Phi e).gradient n

/-- The constant slope as a local Hilbert-vector `L²` class. -/
@[expose]
noncomputable def constantGradientOnOriginCube {d : ℕ}
    (e : Vec d) (n : ℤ) :
    HilbertVectorL2 (openCubeSet (originCube d n)) :=
  toHilbertVectorL2OfVecField (memVectorL2_const_originCube e n)

/-- The full local gradient `e + ∇φ_e`. -/
@[expose]
noncomputable def correctorFullGradientOnOriginCube {d : ℕ}
    (Phi : Vec d → NormalizedLocalH1Carrier d) (e : Vec d) (n : ℤ) :
    HilbertVectorL2 (openCubeSet (originCube d n)) :=
  constantGradientOnOriginCube e n + correctorGradientOnOriginCube Phi e n

/-- A raw representative of the corrector gradient gives the literal full
gradient class. -/
theorem correctorFullGradientOnOriginCube_eq_of_gradient_eq
    {d : ℕ} (Phi : Vec d → NormalizedLocalH1Carrier d)
    (e : Vec d) (n : ℤ) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet (originCube d n)) g)
    (hgrad : correctorGradientOnOriginCube Phi e n =
      toHilbertVectorL2OfVecField hg) :
    correctorFullGradientOnOriginCube Phi e n =
      toHilbertVectorL2OfVecField
        ((memVectorL2_const_originCube e n).add hg) := by
  rw [correctorFullGradientOnOriginCube, constantGradientOnOriginCube,
    hgrad, toHilbertVectorL2OfVecField_add]

/-- The scalar-identity coefficient flux defect `a(e + ∇φ_e) - e` as a
local a.e. class. -/
@[expose]
noncomputable def scalarIdentityCorrectorFluxDefectOnOriginCube
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (Phi : Vec d → NormalizedLocalH1Carrier d) (e : Vec d) (n : ℤ) :
    HilbertVectorL2 (openCubeSet (originCube d n)) :=
  hilbertCoeffOperator
      (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
        (originCube d n) a)
      (correctorFullGradientOnOriginCube Phi e n) -
    constantGradientOnOriginCube e n

/-- The flux-defect class has the literal raw coefficient-field
representative whenever the corrector gradient does. -/
theorem scalarIdentityCorrectorFluxDefectOnOriginCube_toVec_ae
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (Phi : Vec d → NormalizedLocalH1Carrier d) (e : Vec d) (n : ℤ)
    {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet (originCube d n)) g)
    (hgrad : correctorGradientOnOriginCube Phi e n =
      toHilbertVectorL2OfVecField hg) :
    (fun x =>
        (scalarIdentityCorrectorFluxDefectOnOriginCube a Phi e n x).toVec)
      =ᵐ[volumeMeasureOn (openCubeSet (originCube d n))]
      fun x => matVecMul
          (Book.Ch03.publicCoeffField (originCube d n) a x) (e + g x) - e := by
  let hconst := memVectorL2_const_originCube e n
  let hfull : MemVectorL2 (openCubeSet (originCube d n))
      (fun x => e + g x) := by
    have hfun : (fun _ => e) + g = (fun x => e + g x) := by
      funext x
      rfl
    simpa only [hfun] using hconst.add hg
  have hfullClass :
      correctorFullGradientOnOriginCube Phi e n =
        toHilbertVectorL2OfVecField hfull := by
    simpa only [hfull, hconst, Pi.add_apply] using
      correctorFullGradientOnOriginCube_eq_of_gradient_eq Phi e n hg hgrad
  let hEll := Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
    (originCube d n) a
  have hfluxClass :
      scalarIdentityCorrectorFluxDefectOnOriginCube a Phi e n =
        toHilbertVectorL2OfVecField
          ((memVectorL2_matVecMul_of_isEllipticFieldOn hEll hfull).sub hconst) := by
    unfold scalarIdentityCorrectorFluxDefectOnOriginCube
    rw [hfullClass,
      hilbertCoeffOperator_toHilbertVectorL2OfVecField hEll hfull,
      constantGradientOnOriginCube,
      ← toHilbertVectorL2OfVecField_sub]
  rw [hfluxClass]
  exact
    (coeFn_toHilbertVectorL2OfVecField
      ((memVectorL2_matVecMul_of_isEllipticFieldOn hEll hfull).sub hconst)).mono
      fun _ hx => by
        simpa only [hilbertifyVecField, HilbertVec.toVec_ofVec, Pi.sub_apply,
          Pi.add_apply] using congrArg HilbertVec.toVec hx

/-- Compatible public coefficient fields agree almost everywhere on every
smaller centered origin cube. -/
theorem publicCoeffField_originCube_ae_eq_of_le {d : ℕ}
    (a : Book.Ch02.TriadicCoeffFamily d) {n m : ℤ} (hnm : n ≤ m) :
    Book.Ch03.publicCoeffField (originCube d m) a
      =ᵐ[volumeMeasureOn (openCubeSet (originCube d n))]
      Book.Ch03.publicCoeffField (originCube d n) a := by
  have hdesc := originCube_mem_descendantsAtDepth_of_le (d := d) hnm
  exact
    (Book.Ch03.publicCoeffField_ae_eq_descendant_openCubeSet
      (originCube d m) a hdesc).trans
      (Book.Ch03.publicCoeffField_ae_eq_openCubeSet
        (originCube d n) a).symm

/-! ## Infinite weak-error tails -/

end

end HighContrast
end HCPolySupport
