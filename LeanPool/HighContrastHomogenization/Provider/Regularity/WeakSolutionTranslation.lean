/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorGlobalEquation
public import LeanPool.HighContrastHomogenization.Support.Geometry.Translation

/-!
# High-contrast homogenization: Provider.Regularity.WeakSolutionTranslation

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Translation of global weak solutions

Integer covariance of correctors requires the deterministic fact that a
global weak solution remains a global weak solution after translating both its
coefficient and flux fields.  This file proves that raw PDE transport without
assuming any corrector-family covariance.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

open MeasureTheory

/-- The coordinate gradient commutes with precomposition by a translation. -/
theorem smoothGrad_comp_subRight {d : ℕ} (phi : Vec d → ℝ)
    (z x : Vec d) :
    smoothGrad (fun y => phi (y - z)) x = smoothGrad phi (x - z) := by
  funext i
  exact congrArg (fun L => L (basisVec i))
    (fderiv_comp_sub (𝕜 := ℝ) (f := phi) (x := x) z)

/-- A global weak solution translates with its coefficient field: if `F` is
`b`-harmonic, then `F(· + z)` is `b(· + z)`-harmonic. -/
theorem IsWeakSolutionOn.translateCoeffField_univ {d : ℕ}
    {b : CoeffField d} {F : Vec d → Vec d}
    (h : IsWeakSolutionOn b Set.univ F) (z : Vec d) :
    IsWeakSolutionOn (translateCoeffField z b) Set.univ
      (fun x => F (x + z)) := by
  intro phi hphi
  let psi : Vec d → ℝ := fun y => phi (y - z)
  have hpsi : IsLocalTest Set.univ psi := by
    refine ⟨?_, ?_, fun _ _ => Set.mem_univ _⟩
    · simpa only [psi] using!
        hphi.contDiff.comp (contDiff_id.sub contDiff_const)
    · show HasCompactSupport (phi ∘ Homeomorph.subRight z)
      simpa only [psi, Function.comp_apply] using
        hphi.hasCompactSupport.comp_homeomorph (Homeomorph.subRight z)
  obtain ⟨hint, hzero⟩ := h psi hpsi
  let f : Vec d → ℝ := fun y =>
    vecDot (smoothGrad psi y) (matVecMul (b y) (F y))
  let g : Vec d → ℝ := fun x =>
    vecDot (smoothGrad phi x)
      (matVecMul (translateCoeffField z b x) (F (x + z)))
  have hfg : ∀ x, f (x + z) = g x := by
    intro x
    dsimp only [f, g]
    have hx : (x + z) - z = x := by
      ext i
      simp [sub_eq_add_neg, add_assoc]
    rw [show smoothGrad psi (x + z) = smoothGrad phi x by
      rw [smoothGrad_comp_subRight, hx]]
    rfl
  have hintf : Integrable f volume := by
    simpa only [integrableOn_univ] using hint
  have hintcomp : Integrable (fun x => f (x + z)) volume := by
    exact (measurePreserving_add_right (volume : Measure (Vec d)) z)
      |>.integrable_comp_of_integrable hintf
  refine ⟨?_, ?_⟩
  · rw [integrableOn_univ]
    exact hintcomp.congr (_root_.Filter.Eventually.of_forall hfg)
  · have huniv : translateSet z (Set.univ : Set (Vec d)) = Set.univ := by
      ext y
      constructor
      · intro _
        exact Set.mem_univ y
      · intro _
        exact ⟨y - z, Set.mem_univ _, by
          ext i
          simp [sub_eq_add_neg, add_assoc]⟩
    calc
      ∫ x in Set.univ, g x ∂volume =
          ∫ x in Set.univ, f (x + z) ∂volume := by
        exact integral_congr_ae
          (_root_.Filter.Eventually.of_forall fun x => (hfg x).symm)
      _ = ∫ y in translateSet z (Set.univ : Set (Vec d)), f y ∂volume :=
        setIntegral_comp_addRight_translateSet z Set.univ f
      _ = ∫ y in Set.univ, f y ∂volume := by rw [huniv]
      _ = 0 := by simpa only [f] using hzero

end

end HighContrast
end HCPolySupport
