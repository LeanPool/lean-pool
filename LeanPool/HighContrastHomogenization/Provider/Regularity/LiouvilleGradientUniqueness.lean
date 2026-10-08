/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.ClosureH1a
public import LeanPool.HighContrastHomogenization.Provider.Regularity.LiouvilleAdditiveConstant
public import LeanPool.HighContrastHomogenization.Provider.Regularity.LiouvilleCubeRestriction

/-!
# High-contrast homogenization: Provider.Regularity.LiouvilleGradientUniqueness

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Weak-gradient uniqueness for the Liouville local class

Reverse Liouville classification identifies scalar representatives almost
everywhere.  This module upgrades such an identity to the corresponding
global gradient identity, using the local integrability supplied by local
uniform ellipticity and `MemH1sLoc`.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set Filter

noncomputable section

private theorem hasWeakPartialDerivOn_ae_eq_of_value_ae
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {i : Fin d} {u v gi hi : Vec d → ℝ}
    (huv : u =ᵐ[volume.restrict U] v)
    (hgiLoc : LocallyIntegrableOn gi U volume)
    (hhiLoc : LocallyIntegrableOn hi U volume)
    (hgi : HasWeakPartialDerivOn U i u gi)
    (hhi : HasWeakPartialDerivOn U i v hi) :
    gi =ᵐ[volume.restrict U] hi := by
  apply HasWeakPartialDerivOn.ae_eq hU hgiLoc hhiLoc hgi
  intro phi hphiSmooth hphiCompact hphiSub
  calc
    ∫ x in U, u x * (fderiv ℝ phi x) (basisVec i) ∂volume =
        ∫ x in U, v x * (fderiv ℝ phi x) (basisVec i) ∂volume :=
      integral_congr_ae (huv.mono fun x hx => by simp only [hx])
    _ = -(∫ x in U, hi x * phi x ∂volume) :=
      hhi phi hphiSmooth hphiCompact hphiSub

/-- Two `MemH1sLoc` pairs for a locally uniformly elliptic coefficient field
whose scalar representatives agree almost everywhere have globally
almost-everywhere equal weak-gradient representatives. -/
theorem gradient_ae_eq_of_memH1sLoc_of_value_ae
    {d : ℕ} [NeZero d] {b : CoeffField d}
    (hb : IsAELocallyUniformlyElliptic b)
    {u v : Vec d → ℝ} {Du Dv : Vec d → Vec d}
    (hu : MemH1sLoc b u Du) (hv : MemH1sLoc b v Dv)
    (huv : u =ᵐ[volume] v) :
    Du =ᵐ[volume] Dv := by
  have hlocal : ∀ q : ℕ,
      Du =ᵐ[volume.restrict (localGradientCube d q)] Dv := by
    intro q
    obtain ⟨R, hR, hcube⟩ :=
      exists_pos_euclideanBall_superset_openCubeSet (originCube d (q : ℤ))
    have hvalueBall : u =ᵐ[volume.restrict (euclideanBall d R)] v :=
      huv.filter_mono (ae_mono Measure.restrict_le_self)
    have hcoord : ∀ i : Fin d,
        (fun x => Du x i) =ᵐ[volume.restrict (euclideanBall d R)]
          fun x => Dv x i := by
      intro i
      exact hasWeakPartialDerivOn_ae_eq_of_value_ae
        (isOpen_euclideanBall d R) hvalueBall
        (integrableOn_grad_of_memH1sLoc_class hb hu hR i).locallyIntegrableOn
        (integrableOn_grad_of_memH1sLoc_class hb hv hR i).locallyIntegrableOn
        ((hu.2 R hR).1 i) ((hv.2 R hR).1 i)
    have hvectorBall : Du =ᵐ[volume.restrict (euclideanBall d R)] Dv := by
      have hall : ∀ᵐ x ∂volume.restrict (euclideanBall d R),
          ∀ i : Fin d, Du x i = Dv x i := ae_all_iff.mpr hcoord
      filter_upwards [hall] with x hx
      funext i
      exact hx i
    exact hvectorBall.filter_mono (ae_mono
      (Measure.restrict_mono_set volume (by
        simpa only [localGradientCube] using hcube)))
  have hcoordGlobal : ∀ i : Fin d,
      (fun x => Du x i) =ᵐ[volume] fun x => Dv x i := by
    intro i
    apply ae_eq_volume_of_forall_localGradientCube_ae_eq
    intro q
    exact (hlocal q).mono fun x hx => congrFun hx i
  have hall : ∀ᵐ x ∂volume, ∀ i : Fin d, Du x i = Dv x i :=
    ae_all_iff.mpr hcoordGlobal
  filter_upwards [hall] with x hx
  funext i
  exact hx i

end

end HighContrast
end HCPolySupport
