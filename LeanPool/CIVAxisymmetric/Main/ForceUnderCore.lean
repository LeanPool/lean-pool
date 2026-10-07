/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Setting.Hypotheses
public import LeanPool.CIVAxisymmetric.Main.MainTheorem
public import LeanPool.CIVAxisymmetric.Reduction.ForceUnderCoreRescale
public import LeanPool.CIVAxisymmetric.Reduction.ForceVanishingAnalytic
public import LeanPool.CIVAxisymmetric.Reduction.ForceC2BoundedRescale
public import LeanPool.CIVAxisymmetric.Reduction.AnisotropicBoundsRescale

/-!
# The public statement `CIV.Main.forceUnderCore`

This module proves the statement `CIV.forceUnderCore` (`cor:interior:nonanalytic`). At a singular
point, the force violates `eq:interior:force:analytic` by the contrapositive of `thm:main`, so it
does not vanish on the unit cylinder, since the zero force is analytic. If it vanished on a cylinder
`B(R') × (-δ', 0)`, the Navier–Stokes scaling by `R = min R' δ'` would carry the hypotheses of
`thm:main` with the zero force to the unit cylinder
(`CIV.isSuitableWeakSolution_rescale_unitCylinder`, `CIV.globalEnergyClass_rescale`,
`CIV.axisymmetricCore_rescale`), and `thm:main` would make the origin regular
(`CIV.boundedNearOrigin_of_rescale`).
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV
namespace Main

/-- The public statement of `cor:interior:nonanalytic`: at a singular point, under the other
hypotheses of `thm:main`, the force is not spatially analytic, does not vanish identically on the
unit cylinder, and does not vanish identically on any cylinder `B(R') × (-δ', 0)`. -/
theorem forceUnderCore (q : ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    (henergy : GlobalEnergyClass u Du p)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) unitCylinder)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (h : ℝ) (hh : 0 < h ∧ h < 1 / 2)
    (hMf : ForceC2Bounded f)
    (C : ℝ) (hC : 0 < C) (hbounds : AnisotropicBounds C h (angularMean u))
    (hcore : ∀ t ∈ Ioo (-1 : ℝ) 0, ∃ ρ ∈ Ioo (0 : ℝ) 1,
      IsAxisymmetricOn u (spaceTimeSet (vec3Ball 0 ρ) {t}))
    (hsing : ¬ BoundedNearOrigin u) :
    ¬ ForceSpatiallyAnalytic f ∧ (∃ z ∈ unitCylinder, f z ≠ 0) ∧
      ∀ R' δ' : ℝ, 0 < R' → R' ≤ 1 → 0 < δ' → δ' ≤ 1 →
        ∃ z ∈ spaceTimeSet (vec3Ball 0 R') (Ioo (-δ') 0), f z ≠ 0 := by
  have hna : ¬ ForceSpatiallyAnalytic f := fun hfa =>
    hsing (mainTheorem q u Du p f hsol henergy hu hp hf h hh hMf hfa C hC hbounds hcore).2
  refine ⟨hna, exists_mem_unitCylinder_ne_zero_of_not_forceSpatiallyAnalytic hna, ?_⟩
  intro R' δ' hR' hR'1 hδ' hδ'1
  by_contra hcon
  push Not at hcon
  have hR0 : 0 < min R' δ' := lt_min hR' hδ'
  have hRR' : min R' δ' ≤ R' := min_le_left _ _
  have hRδ' : min R' δ' ≤ δ' := min_le_right _ _
  have hR1 : min R' δ' ≤ 1 := hRR'.trans hR'1
  have hRsq : min R' δ' ^ 2 ≤ δ' := by
    have hmul : min R' δ' * min R' δ' ≤ 1 * δ' := mul_le_mul hR1 hRδ' hR0.le zero_le_one
    rw [sq]
    linarith only [hmul]
  have hRsq1 : min R' δ' ^ 2 ≤ 1 := pow_le_one₀ hR0.le hR1
  have hcl := isClassicalSolutionOn_of_suitable hsol hu hp hf
  have hsubR : spaceTimeSet (vec3Ball 0 (min R' δ')) (Ioo (-1) 0) ⊆ unitCylinder := by
    intro z hz
    refine ⟨?_, hz.2⟩
    have hz1 := hz.1
    simp only [mem_vec3Ball] at hz1 ⊢
    exact lt_of_lt_of_le hz1 hR1
  have hclR := isClassicalSolutionOn_unitCylinder_of_parabolicRescale hR0 (le_refl _) hRsq1
    (hcl.mono hsubR)
  have hzero := rescaleForce_eq_zero_of_vanishing hR0 hRR' hRsq hcon
  have hC' : 0 < min R' δ' ^ (-(2 * h)) * C := mul_pos (Real.rpow_pos_of_pos hR0 _) hC
  have hmain := mainTheorem q _ _ _ _
    (isSuitableWeakSolution_rescale_unitCylinder hR0 hR1 hsol)
    (globalEnergyClass_rescale hR0 hR1 henergy) hclR.1 hclR.2.1 hclR.2.2.1 h hh
    (forceC2Bounded_rescale hR0 hR1 hMf) (forceSpatiallyAnalytic_of_eqOn_unitCylinder_zero hzero)
    _ hC' (anisotropicBounds_angularMean_rescale hC.le hh.1.le hR0 hR1 hbounds)
    (axisymmetricCore_rescale hR0 hR1 hcore)
  exact hsing (boundedNearOrigin_of_rescale hR0 hmain.2)

end Main
end CIV
