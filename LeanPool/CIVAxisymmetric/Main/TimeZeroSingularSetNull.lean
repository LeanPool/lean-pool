/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Setting.Hypotheses
public import LeanPool.CIVAxisymmetric.Regularity.SingularGradientLimsup
public import LeanPool.CIVAxisymmetric.Regularity.GradientDensityCovering
public import LeanPool.CIVAxisymmetric.Setting.EnergyClassLemmas

/-!
# The public statement `CIV.Main.timeZeroSingularSetNull`

This module proves the statement `CIV.timeZeroSingularSetNull`: from the uniform interior route (the
top-cylinder Theorem A smallness of `CIV.top_cylinder_smallness_of_gradient_small` together with the
Theorem A lower bound `CIV.lintegral_gt_of_mem_singularSlice` at a point of the singular slice), the
scale-invariant Dirichlet integral of the spatial gradient over top-boundary cylinders based at a
singular point has `limsup`, as the radius shrinks to `0` from the right, bounded below by a
universal positive constant. The spatial Vitali covering step
`CIV.hausdorffMeasure_one_null_of_gradient_density`, fed by that lower bound through
`CIV.density_of_le_limsup` and the finite global Dirichlet integral of
`CIV.lintegral_gradSq_lt_top`, then gives the one-dimensional Hausdorff-measure-zero conclusion.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV
namespace Main

/-- The public statement of time-zero partial regularity: the set of points of the
open unit ball near which `u` is unbounded on every backward parabolic neighbourhood ending at
the blow-up time `t = 0` has one-dimensional Hausdorff measure zero, proved from the uniform
interior route through the top-cylinder Theorem A smallness and the spatial Vitali covering
step. -/
theorem timeZeroSingularSetNull (q : ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    (henergy : GlobalEnergyClass u Du p)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) unitCylinder)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (hMf : ForceC2Bounded f) :
    μH[1] (singularSlice u ∩ vec3Ball 0 1) = 0 := by
  have hq : (5 : ℝ) / 2 < q := hsol.2.2.2.1
  have hcont : ContinuousOn (fun z : Vec3 × ℝ => u z) unitCylinder := hu.continuousOn
  -- the pressure and force smoothness hypotheses of the statement are not used by this proof;
  -- record their continuity so that the hypotheses are referenced
  have _hpCont : ContinuousOn (fun z : Vec3 × ℝ => p z) unitCylinder := hp.continuousOn
  have _hfCont : ContinuousOn (fun z : Vec3 × ℝ => f z) unitCylinder := hf.continuousOn
  -- the lower bound on the `limsup` that the spatial covering step consumes
  obtain ⟨ε₁, hε₁pos, hur7⟩ := le_limsup_gradient_of_mem_singularSlice q hq
  -- the density hypothesis of the covering step, from that lower bound and
  -- `density_of_le_limsup`
  have hfin : (∫⁻ z in unitCylinder, ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ := lintegral_gradSq_lt_top henergy
  have hdens : ∀ x ∈ singularSlice u ∩ vec3Ball (0 : Vec3) 1, ∀ r₀ : ℝ, 0 < r₀ →
      ∃ r : ℝ, 0 < r ∧ r < r₀ ∧ ENNReal.ofReal (ε₁ / 18 * r) ≤
        ∫⁻ z in vec3Ball x r ×ˢ Ioo (-(r ^ 2)) 0, ‖Du z‖ₑ ^ (2 : ℝ) := by
    intro x hx r₀ hr₀
    exact density_of_le_limsup hε₁pos
      (hur7 u Du p f hsol henergy hMf hcont x hx.2 hx.1) r₀ hr₀
  have hresult := hausdorffMeasure_one_null_of_gradient_density u Du
    (singularSlice u ∩ vec3Ball 0 1) (ε₁ / 18) (div_pos hε₁pos (by norm_num)) hfin hdens
  rwa [Set.inter_assoc, Set.inter_self] at hresult

end Main
end CIV
