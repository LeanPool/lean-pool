/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.Representatives
public import LeanPool.HighContrastHomogenization.Support.Deterministic.MultiscaleQuantitiesBasic.Foundation.Geometry

/-!
# CompatibleFamily

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Compatible CoarseGraining families for an origin-cube coefficient

This internal bridge supplies CoarseGraining's family-valued interface from
coefficient data on the origin cube.  The chosen off-root extension remains
confined to the existence proof; the frozen public A chooses only unique real
scalars.
-/

namespace Algsuperdiff.Section24.UnitCubeMultiscale

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- Every coefficient on the origin cube is represented by at least one coherent
CoarseGraining triadic family. -/
theorem exists_compatibleTriadicCoeffFamily
    (a : CoeffOn (cubeDomain (originCube d 0))) :
    ∃ F : TriadicCoeffFamily d,
      CoeffOn.AEEq (F.coeffOn (originCube d 0)) a := by
  classical
  let representative : CoeffField d :=
    HCPolySupport.Internal.Ch02.BookCh02.pointwiseCoeffField
      (cubeDomain (originCube d 0)) a
  have representative_measurable : Measurable (fun x i j => representative x i j) := by
    simpa [representative] using
      HCPolySupport.Internal.Ch02.BookCh02.pointwiseCoeffField_measurable
        (cubeDomain (originCube d 0)) a
  have representative_isElliptic (x : Vec d) :
      IsEllipticMatrix a.lam a.Lam (representative x) := by
    by_cases hx : x ∈
        (HCPolySupport.Internal.Ch02.BookCh02.goodSetData
          (cubeDomain (originCube d 0)) a).set
    · simpa [representative,
        HCPolySupport.Internal.Ch02.BookCh02.pointwiseCoeffField, hx] using
        (HCPolySupport.Internal.Ch02.BookCh02.goodSetData
          (cubeDomain (originCube d 0)) a).elliptic x hx
    · simpa [representative,
        HCPolySupport.Internal.Ch02.BookCh02.pointwiseCoeffField, hx] using
        HCPolySupport.Internal.Ch02.BookCh02.isEllipticMatrix_smul_one
          (d := d) a.lam_pos a.lam_le_Lam
  let F : TriadicCoeffFamily d := {
    coeffOn := fun Q => {
      toCoeffField := representative
      lam := a.lam
      Lam := a.Lam
      lam_pos := a.lam_pos
      lam_le_Lam := a.lam_le_Lam
      aeStronglyMeasurable := by
        intro i j
        have hmeas : Measurable fun x : Vec d =>
            restrictCoeffField (openCubeSet Q) representative x i j := by
          have hite : Measurable fun x : Vec d =>
              if x ∈ openCubeSet Q then representative x i j else 0 :=
            Measurable.ite (measurableSet_openCubeSet Q)
              ((measurable_pi_iff.1
                (measurable_pi_iff.1 representative_measurable i)) j)
              measurable_const
          convert hite using 1
          funext x
          by_cases hx : x ∈ openCubeSet Q <;> simp [restrictCoeffField, hx]
        exact hmeas.aestronglyMeasurable
      aeElliptic := by
        filter_upwards [ae_restrict_mem (measurableSet_openCubeSet Q)] with x _
        exact representative_isElliptic x
      }
    restrictsTo_of_subset := by
      intro Q R _
      exact Filter.EventuallyEq.rfl
    }
  refine ⟨F, ?_⟩
  change representative =ᵐ[volumeMeasureOn (openCubeSet (originCube d 0))]
    a.toCoeffField
  simpa [representative] using
    HCPolySupport.Internal.Ch02.BookCh02.pointwiseCoeffField_ae_eq
      (cubeDomain (originCube d 0)) a

/-- Root a.e. agreement propagates to every descendant used by the root-local
multiscale quantities. -/
theorem coeffOn_aeeq_of_root_aeeq
    (a : CoeffOn (cubeDomain (originCube d 0)))
    (F G : TriadicCoeffFamily d)
    (hF : CoeffOn.AEEq (F.coeffOn (originCube d 0)) a)
    (hG : CoeffOn.AEEq (G.coeffOn (originCube d 0)) a)
    {R : TriadicCube d} {k : ℤ} (hk : k ≤ (originCube d 0).scale)
    (hR : R ∈ descendantsAtScale (originCube d 0) k) :
    CoeffOn.AEEq (F.coeffOn R) (G.coeffOn R) := by
  have hroot : CoeffOn.AEEq
      (F.coeffOn (originCube d 0)) (G.coeffOn (originCube d 0)) :=
    hF.trans hG.symm
  have hsub : openCubeSet R ⊆ openCubeSet (originCube d 0) :=
    openCubeSet_subset_of_mem_descendantsAtScale hk hR
  have hFchild : (F.coeffOn R).toCoeffField
      =ᵐ[volumeMeasureOn (openCubeSet R)]
        (F.coeffOn (originCube d 0)).toCoeffField :=
    F.restrictsTo_of_subset hsub
  have hGchild : (G.coeffOn R).toCoeffField
      =ᵐ[volumeMeasureOn (openCubeSet R)]
        (G.coeffOn (originCube d 0)).toCoeffField :=
    G.restrictsTo_of_subset hsub
  exact (hFchild.trans
    (ae_restrict_of_ae_restrict_of_subset hsub hroot)).trans hGchild.symm

end

end Algsuperdiff.Section24.UnitCubeMultiscale
