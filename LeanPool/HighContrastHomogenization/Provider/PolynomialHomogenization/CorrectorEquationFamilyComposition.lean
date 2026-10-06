/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorGlobalEquation
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorJointGoodTailEquation

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.CorrectorEquationFamilyComposition

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Canonical scalar-reference corrector equation composition

This module composes the available local Cauchy, joint-equation, global
representative, and global-equation results.  It records the complete
same-family conclusion available before affine transport to a physical
coefficient sample.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set Filter

noncomputable section

/-- The canonical global representatives of a normalized local carrier form
a genuine weak-gradient pair on all of Euclidean space. -/
theorem NormalizedLocalH1Carrier.hasWeakGradientOn_globalRepresentatives
    {d : ℕ} (z : NormalizedLocalH1Carrier d) :
    HasWeakGradientOn Set.univ z.globalValueRepresentative
      z.globalGradientRepresentative := by
  intro i φ hφ hcompact _hsub
  obtain ⟨n, hsupport⟩ :=
    exists_localGradientCube_superset_of_isCompact hcompact.isCompact
  have hlocal := (z.localH1Function n).hasWeakGradient
    i φ hφ hcompact hsupport
  let leftGlobal : Vec d → ℝ := fun x =>
    z.globalValueRepresentative x * (fderiv ℝ φ x) (basisVec i)
  let leftLocal : Vec d → ℝ := fun x =>
    (z.localH1Function n).toFun x * (fderiv ℝ φ x) (basisVec i)
  let rightGlobal : Vec d → ℝ := fun x =>
    z.globalGradientRepresentative x i * φ x
  let rightLocal : Vec d → ℝ := fun x =>
    (z.localH1Function n).grad x i * φ x
  have hleft : leftGlobal =ᵐ[volumeMeasureOn (localGradientCube d n)]
      leftLocal := by
    filter_upwards [z.globalValueRepresentative_ae_eq_localH1Function n]
      with x hx
    simp only [leftGlobal, leftLocal, hx]
  have hright : rightGlobal =ᵐ[volumeMeasureOn (localGradientCube d n)]
      rightLocal := by
    filter_upwards [z.globalGradientRepresentative_ae_eq_localH1Gradient n]
      with x hx
    simp only [rightGlobal, rightLocal, hx]
  have hleftZero : ∀ x, x ∉ localGradientCube d n → leftGlobal x = 0 := by
    intro x hx
    have hxnot : x ∉ tsupport φ := fun hx' => hx (hsupport hx')
    have hφeq : φ =ᶠ[nhds x] 0 :=
      (isClosed_tsupport (f := φ)).isOpen_compl.eventually_mem hxnot |>.mono
        (fun y hy => image_eq_zero_of_notMem_tsupport hy)
    simp only [leftGlobal]
    rw [EventuallyEq.fderiv_eq hφeq]
    simp
  have hrightZero : ∀ x, x ∉ localGradientCube d n → rightGlobal x = 0 := by
    intro x hx
    simp only [rightGlobal,
      image_eq_zero_of_notMem_tsupport (fun hx' => hx (hsupport hx')),
      mul_zero]
  change ∫ x in Set.univ, leftGlobal x ∂volume =
    -∫ x in Set.univ, rightGlobal x ∂volume
  rw [setIntegral_univ, setIntegral_univ,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hleftZero,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hrightZero]
  calc
    ∫ x in localGradientCube d n, leftGlobal x ∂volume =
        ∫ x in localGradientCube d n, leftLocal x ∂volume :=
      integral_congr_ae hleft
    _ = -∫ x in localGradientCube d n, rightLocal x ∂volume := hlocal
    _ = -∫ x in localGradientCube d n, rightGlobal x ∂volume := by
      rw [integral_congr_ae hright.symm]

end

end HighContrast
end HCPolySupport
