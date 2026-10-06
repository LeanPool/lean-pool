/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorGlobalEquation
public import LeanPool.HighContrastHomogenization.Provider.Regularity.LiouvilleCubeRestriction
public import LeanPool.HighContrastHomogenization.Setup.ResponsePositivity
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.CoeffFamily
public import LeanPool.HighContrastHomogenization.Support.Sobolev.H1.Translation
public import LeanPool.HighContrastHomogenization.Support.Sobolev.PotentialSolenoidalL2Recovery

/-!
# High-contrast homogenization: Provider.Regularity.ObservationCoefficientTransport

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Observation-cube coefficient and equation transport

A physical weak solution is restricted to an inward cube and pulled back by
translation to the origin cube of the same scale.  A representative of the
source coefficient that is elliptic at every point of every ball, with that
ball's own constants, is translated and packaged as a Chapter 3 coefficient
family.
-/

namespace HCPolySupport
namespace HighContrast

open Book Book.Ch03 MeasureTheory

noncomputable section

variable {d : ℕ}

private theorem smoothGrad_comp_subRight_add
    {phi : Vec d → ℝ} (z y : Vec d) :
    smoothGrad (fun x => phi (x - z)) (y + z) = smoothGrad phi y := by
  ext i
  have hderiv :
      fderiv ℝ (fun x : Vec d => phi (x - z)) (y + z) =
        fderiv ℝ phi ((y + z) - z) := by
    simpa using
      (fderiv_comp_sub (𝕜 := ℝ) (f := phi) (x := y + z) z)
  change
    (fderiv ℝ (fun x : Vec d => phi (x - z)) (y + z)) (basisVec i) =
      (fderiv ℝ phi y) (basisVec i)
  rw [hderiv]
  congr 2
  ext j
  simp [sub_eq_add_neg, add_assoc]

/-- Pull a smooth-test weak equation on a translated domain back to the
untranslated domain. -/
theorem IsWeakSolutionOn.untranslate
    {U : Set (Vec d)} {b : CoeffField d} {F : Vec d → Vec d}
    (z : Vec d)
    (h : IsWeakSolutionOn b (translateSet z U) F) :
    IsWeakSolutionOn (translateCoeffField z b) U
      (fun x => F (x + z)) := by
  intro phi hphi
  let psi : Vec d → ℝ := fun x => phi (x - z)
  have hpsi : IsLocalTest (translateSet z U) psi := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [psi] using!
        hphi.contDiff.comp (contDiff_id.sub contDiff_const)
    · show HasCompactSupport (phi ∘ Homeomorph.subRight z)
      simpa only [psi, Function.comp_apply] using
        hphi.hasCompactSupport.comp_homeomorph (Homeomorph.subRight z)
    · intro x hx
      have hx' : x - z ∈ tsupport phi := by
        rw [show psi = phi ∘ Homeomorph.subRight z by rfl,
          tsupport_comp_eq_preimage phi (Homeomorph.subRight z)] at hx
        exact hx
      exact mem_translateSet_iff_sub_mem.mpr (hphi.tsupport_subset hx')
  let p : Vec d → ℝ := fun x =>
    vecDot (smoothGrad psi x) (matVecMul (b x) (F x))
  let q : Vec d → ℝ := fun y =>
    vecDot (smoothGrad phi y)
      (matVecMul ((translateCoeffField z b) y) (F (y + z)))
  have hqp : ∀ y, q y = p (y + z) := by
    intro y
    dsimp only [p, q, psi, translateCoeffField]
    rw [smoothGrad_comp_subRight_add]
    congr 2
  obtain ⟨hpInt, hpZero⟩ := h psi hpsi
  have hpComp : IntegrableOn (fun y => p (y + z)) U := by
    let hmp := measurePreserving_addRight_restrict_translateSet (d := d) z U
    simpa only [Function.comp_apply] using!
      hmp.integrable_comp_of_integrable hpInt
  refine ⟨?_, ?_⟩
  · exact hpComp.congr (_root_.Filter.Eventually.of_forall fun y => (hqp y).symm)
  · change ∫ y in U, q y ∂volume = 0
    calc
      ∫ y in U, q y ∂volume = ∫ y in U, p (y + z) ∂volume :=
        integral_congr_ae (_root_.Filter.Eventually.of_forall hqp)
      _ = ∫ x in translateSet z U, p x ∂volume :=
        setIntegral_comp_addRight_translateSet (d := d) z U p
      _ = 0 := hpZero

private theorem isForcedEquation_zero_of_isWeakSolutionOn'
    {Q : TriadicCube d} {a : CoeffFamily d}
    (u : H1Function (Book.Ch02.cubeDomain Q : Set (Vec d)))
    (hu : IsWeakSolutionOn (a.coeffOn Q).toCoeffField
      (Book.Ch02.cubeDomain Q : Set (Vec d)) u.grad) :
    IsForcedEquation Q a u (0 : Vec d → Vec d) := by
  have hEll : IsAEEllipticFieldOn (a.coeffOn Q).lam (a.coeffOn Q).Lam
      (Book.Ch02.cubeDomain Q : Set (Vec d)) (a.coeffOn Q).toCoeffField :=
    ⟨(Book.Ch02.cubeDomain Q).measurableSet,
      (a.coeffOn Q).aeStronglyMeasurable, (a.coeffOn Q).aeElliptic⟩
  have hflux : MemVectorL2 (Book.Ch02.cubeDomain Q : Set (Vec d))
      (fun x => matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x)) :=
    hEll.memVectorL2_matVecMul u.grad_memVectorL2
  have hsol : IsSolenoidalOn (Book.Ch02.cubeDomain Q : Set (Vec d))
      (fun x => matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x)) := by
    refine IsSolenoidalOn.of_test_of_contDiff_of_memVectorL2 hflux
      (Book.Ch02.cubeDomain Q).isOpen ?_
    intro psi hpsi hsupp hsub
    have hzero := (hu psi ⟨hpsi, hsupp, hsub⟩).2
    have hfun :
        (fun x => vecDot
          (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x))
          (fun i => (fderiv ℝ psi x) (basisVec i))) =
        fun x => vecDot (smoothGrad psi x)
          (matVecMul ((a.coeffOn Q).toCoeffField x) (u.grad x)) := by
      funext x
      rw [vecDot_comm]
      rfl
    rw [hfun]
    exact hzero
  have hweak : IsH1DirichletRhsWeakSolutionOn
      (a.coeffOn Q).toCoeffField
      (Book.Ch02.cubeDomain Q : Set (Vec d)) u (0 : Vec d → Vec d) :=
    IsH1DirichletRhsWeakSolutionOn.of_residual_solenoidal
      hflux MeasureTheory.MemLp.zero (by simpa only [Pi.zero_apply, sub_zero] using hsol)
  simpa only [IsForcedEquation] using! hweak

/-- Restrict a physical weak solution to an inward observation cube, pull it
back to the origin, and package the translated source representative as a
compatible coefficient family. -/
theorem exists_observationCoeffFamily_and_forcedEquation
    {U : Set (Vec d)}
    (aSource : Source.AKL.Field d)
    (haSource : AEUniformlyEllipticField aSource)
    (aPhysical : CoeffField d)
    (haeSource : (⇑aSource : CoeffField d) =ᵐ[volume] aPhysical)
    (u : H1Function U)
    (huPhysical : IsWeakSolutionOn aPhysical U u.grad)
    (center : Vec d) (m : ℤ)
    (hobs : openCubeAtScale center m ⊆ U) :
    ∃ (aObs : CoeffFamily d)
      (uObs : H1Function (openCubeSet (originCube d m))),
      ((aObs.coeffOn (originCube d m)).toCoeffField =ᵐ[
          volumeMeasureOn (openCubeSet (originCube d m))]
        fun x => aPhysical (x + center)) ∧
      (∀ x, uObs.toFun x = u.toFun (x + center)) ∧
      (∀ x, uObs.grad x = u.grad (x + center)) ∧
      IsForcedEquation (originCube d m) aObs uObs
        (0 : Vec d → Vec d) := by
  obtain ⟨f, hfm, hfa, hfp⟩ :=
    exists_locally_pointwise_elliptic_representative haSource
  let fObs : CoeffField d := translateCoeffField center f
  have hfObsMeas : Measurable fObs := by
    exact hfm.comp (continuous_id.add continuous_const).measurable
  have hfObsEll : ∀ R : ℝ, 0 < R → ∃ lam Lam : ℝ, 0 < lam ∧ lam ≤ Lam ∧
      ∀ x ∈ Metric.ball (0 : Vec d) R, IsEllipticMatrix lam Lam (fObs x) := by
    intro R hR
    obtain ⟨lam, Lam, hlam, hle, hell⟩ :=
      hfp (R + ‖center‖) (lt_of_lt_of_le hR (le_add_of_nonneg_right (norm_nonneg _)))
    refine ⟨lam, Lam, hlam, hle, fun x hx => hell (x + center) ?_⟩
    refine mem_ball_zero_iff.2 ?_
    have hxn : ‖x‖ < R := mem_ball_zero_iff.1 hx
    exact lt_of_le_of_lt (norm_add_le _ _) (by linarith only [hxn])
  let aReg : RegCoeffField d :=
    regCoeffFieldOfBallPointwiseElliptic fObs hfObsMeas hfObsEll
  have haReg : Book.Ch04.AELocallyUniformlyEllipticField aReg :=
    aeLocallyUniformlyEllipticField_of_ball_pointwise hfObsMeas hfObsEll
  let aObs : CoeffFamily d :=
    Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField aReg haReg
  have hfaPhysical : f =ᵐ[volume] aPhysical := hfa.symm.trans haeSource
  have hfaPhysicalShift :
      (fun x => f (x + center)) =ᵐ[volume]
        fun x => aPhysical (x + center) := by
    let hmp := measurePreserving_add_right (volume : Measure (Vec d)) center
    exact hmp.quasiMeasurePreserving.tendsto_ae hfaPhysical
  have hcoeff :
      ((aObs.coeffOn (originCube d m)).toCoeffField =ᵐ[
          volumeMeasureOn (openCubeSet (originCube d m))]
        fun x => aPhysical (x + center)) := by
    change fObs =ᵐ[volume.restrict (openCubeSet (originCube d m))]
      fun x => aPhysical (x + center)
    exact ae_restrict_of_ae (by
      simpa only [fObs, translateCoeffField] using! hfaPhysicalShift)
  let Q : TriadicCube d := originCube d m
  have hV : openCubeAtScale center m =
      translateSet center (openCubeSet Q) := by
    rw [openCubeAtScale_eq_translateSet,
      openCubeAtScale_zero_eq_openCubeSet_originCube]
  have htransOpen : IsOpen (translateSet center (openCubeSet Q)) := by
    rw [← hV]
    exact isOpen_openCubeAtScale center m
  have htransSubset : translateSet center (openCubeSet Q) ⊆ U := by
    rw [← hV]
    exact hobs
  let uT : H1Function (translateSet center (openCubeSet Q)) :=
    u.restrict htransOpen htransSubset
  let uObs : H1Function (openCubeSet Q) :=
    H1Function.untranslate center uT
  have hPhysicalV : IsWeakSolutionOn aPhysical
      (translateSet center (openCubeSet Q)) u.grad :=
    IsWeakSolutionOn.mono htransSubset huPhysical
  have hPhysicalF : IsWeakSolutionOn f
      (translateSet center (openCubeSet Q)) u.grad := by
    exact IsWeakSolutionOn.congr_ae
      (ae_restrict_of_ae hfaPhysical.symm) _root_.Filter.EventuallyEq.rfl hPhysicalV
  have hWeakObs : IsWeakSolutionOn fObs (openCubeSet Q) uObs.grad := by
    have hPull := IsWeakSolutionOn.untranslate center hPhysicalF
    simpa only [fObs, uObs, H1Function.untranslate_grad, uT,
      H1Function.restrict] using! hPull
  have hForced : IsForcedEquation Q aObs uObs (0 : Vec d → Vec d) := by
    apply isForcedEquation_zero_of_isWeakSolutionOn' uObs
    simpa only [aObs, aReg,
      Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField_coeffOn_toCoeffField,
      regCoeffFieldOfBallPointwiseElliptic_toFun] using! hWeakObs
  refine ⟨aObs, uObs, ?_, ?_, ?_, ?_⟩
  · simpa only [Q] using hcoeff
  · intro x
    rfl
  · intro x
    rfl
  · simpa only [Q] using hForced

end

end HighContrast
end HCPolySupport
