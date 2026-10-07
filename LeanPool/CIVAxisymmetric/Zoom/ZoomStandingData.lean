/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Regularity.RegularSphereFull
public import LeanPool.CIVAxisymmetric.Closure.CirculationBound
public import LeanPool.CIVAxisymmetric.Reduction.AveragedClassical
public import LeanPool.CIVAxisymmetric.Reduction.AveragedForceBound
public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.ClassicalBridge

/-!
# Standing data of the zoom argument of `prop:aniso:small`

Under the hypotheses of `thm:aniso:main` the proof of `prop:aniso:small` works with the
angle-averaged pressure and force (Section `sec:aniso:identities`: "averaging over rotations
... we may take `π` and `f` axisymmetric"), and with the circulation bound
`eq:aniso:zoom:circulation` on a window `B(R_*) × (t_*, 0)` with `ρ < R_* < 1`, which
`lem:aniso:annulus` supplies. This module packages both.

The averaged pair enters only through its classical equations
(`CIV.isClassicalSolutionOn_angularMean`); the regular annulus is obtained from the original
suitable solution (`CIV.exists_annulus_bound_of_timeZeroSingularSetNull`), and the circulation
bound from the maximum principle for the circulation equation of the averaged classical system
(`CIV.forall_Rstar_exists_circulation_bound_ball_of_annulus_bound`), whose force is the
axisymmetric angular mean.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- The standing data of the zoom argument in the proof of `prop:aniso:small`: the classical
equations with the angle-averaged pressure and force, the axisymmetry and `C²` bound of the
averaged force, and the circulation bound `eq:aniso:zoom:circulation` on `B(R_*) × (t_*, 0)`
for some `ρ < R_* < 1`. -/
theorem exists_zoom_standing_data (q : ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    (henergy : GlobalEnergyClass u Du p)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) unitCylinder)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (hMf : ForceC2Bounded f)
    {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) :
    IsClassicalSolutionOn u (angularMeanScalar p) (angularMean f) unitCylinder ∧
      IsAxisymmetricOn (angularMean f) unitCylinder ∧ ForceC2Bounded (angularMean f) ∧
      ∃ Rstar tstar CΓ : ℝ, ρ < Rstar ∧ Rstar < 1 ∧ tstar ∈ Ioo (-1 : ℝ) 0 ∧ 0 ≤ CΓ ∧
        ∀ x ∈ vec3Ball (0 : Vec3) Rstar, ∀ t ∈ Ioo tstar (0 : ℝ),
          |circulation u (x, t)| ≤ CΓ := by
  have hclassical : IsClassicalSolutionOn u p f unitCylinder :=
    isClassicalSolutionOn_of_suitable hsol hu hp hf
  have havg : IsClassicalSolutionOn u (angularMeanScalar p) (angularMean f) unitCylinder :=
    isClassicalSolutionOn_angularMean u p f hclassical haxi
  have hfaxi : IsAxisymmetricOn (angularMean f) unitCylinder :=
    isAxisymmetricOn_angularMean_force f
  have hMf' : ForceC2Bounded (angularMean f) := forceC2Bounded_angularMean hf hMf
  refine ⟨havg, hfaxi, hMf', ?_⟩
  obtain ⟨R₀, hρR₀, hR₀1⟩ := exists_between hρ.2
  obtain ⟨Rlo, Rhi, t₀, M, hρlo, hlohi, hhiR₀, ht₀, hbdd⟩ :=
    exists_annulus_bound_of_timeZeroSingularSetNull q u Du p f hsol henergy hu hp hf hMf ρ R₀
      hρ.1.le hρR₀ hR₀1
  obtain ⟨Mf, hMfb⟩ := exists_bound_force_swirl_of_forceC2Bounded (angularMean f) hMf'
  have hRlo0 : 0 ≤ Rlo := le_trans hρ.1.le hρlo.le
  have hRhi1 : Rhi < 1 := lt_trans hhiR₀ hR₀1
  have hcirc := forall_Rstar_exists_circulation_bound_ball_of_annulus_bound u
    (angularMeanScalar p) (angularMean f) havg haxi hfaxi Mf hMfb Rlo Rhi t₀ M hRlo0 hRhi1 ht₀
    hbdd
  set Rstar : ℝ := (Rlo + Rhi) / 2 with hRstar
  have hmem : Rstar ∈ Ioo Rlo Rhi := ⟨by linarith only [hlohi, hRstar], by linarith only [hlohi,
    hRstar]⟩
  obtain ⟨CΓ, hCΓ⟩ := hcirc Rstar hmem
  refine ⟨Rstar, t₀, max CΓ 0, by linarith only [hρlo, hmem.1], by linarith only [hmem.2, hRhi1],
    ht₀, le_max_right _ _, fun x hx t ht => (hCΓ t ht x hx).trans (le_max_left _ _)⟩

end CIV
