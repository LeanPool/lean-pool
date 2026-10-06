/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Reduction.SmoothPressureGauge
public import LeanPool.CIVAxisymmetric.Main.ClosureLemma
public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.ClassicalBridge
public import LeanPool.CIVAxisymmetric.Reduction.AveragedClassical
public import LeanPool.CIVAxisymmetric.Reduction.AveragedSuitable
public import LeanPool.CIVAxisymmetric.Reduction.AveragedForceBound

/-!
# The rotation-averaged system and the regularity of axisymmetric solutions

For an axisymmetric suitable weak solution on `Q`, smooth there, averaging the momentum
equation over the rotations about the axis leaves the velocity terms unchanged and replaces the
pressure and the force by their angular means `π_bar` and `f_bar = 𝒫 f` (proof of `thm:main`). The pair
`(u, π_bar)` is again suitable with the axisymmetric force `f_bar`: the classical equations give
`∇π_bar - ∇π = f_bar - f` on `Q`, so this is a smooth change of gauge. The closure lemma
`lem:aniso:closure` applied to the averaged triple then gives regularity at the origin from the
smallness `eq:aniso:closure:small` at one radius, with no symmetry assumed on the force; this is
the proof of `thm:aniso:main` from `prop:aniso:small`.
-/

public section

open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace CIV

/-- The averaged system is suitable: for an axisymmetric suitable weak solution on `Q` whose
velocity, pressure and force are smooth there, `(u, π_bar)` is a suitable weak solution with the
force `𝒫 f`, with the same weak gradient. -/
theorem isSuitableWeakSolution_angularMean {q : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) unitCylinder)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) :
    IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du (angularMeanScalar p)
      (angularMean f) := by
  have hcl := isClassicalSolutionOn_of_suitable hsol hu hp hf
  have hclb := isClassicalSolutionOn_angularMean u p f hcl haxi
  refine isSuitableWeakSolution_of_pressureGauge hsol hu hp hf hclb.2.1 hclb.2.2.1
    hcl.2.2.2.2 ?_
  intro z hz i
  have h1 := hcl.2.2.2.1 z hz i
  have h2 := hclb.2.2.2.1 z hz i
  linarith only [h1, h2]

/-- `thm:aniso:main` from the smallness at one radius: an axisymmetric suitable weak solution on
`Q`, smooth there, with a force satisfying `eq:interior:force:c-two` (no symmetry of the force is
assumed) and `lim_{t↑0} (-t) G_{ρ₀}(t) = 0` for some `ρ₀ ∈ (0, 1)`, is regular at the origin.
The closure lemma is applied to the averaged triple `(u, π_bar, 𝒫 f)`. -/
theorem boundedNearOrigin_of_meridionalSmallness_averaged (q : ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (hsol : CKN.IsSuitableWeakSolution (vec3Ball 0 1) (Ioo (-1) 0) q u Du p f)
    (henergy : GlobalEnergyClass u Du p)
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z) unitCylinder)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => p z) unitCylinder)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => f z) unitCylinder)
    (haxi : IsAxisymmetricOn u unitCylinder) (hMf : ForceC2Bounded f)
    (ρ₀ : ℝ) (hρ₀ : ρ₀ ∈ Ioo (0 : ℝ) 1) (hsmall : MeridionalSmallness ρ₀ u) :
    BoundedNearOrigin u :=
  CIV.Main.closureLemma q u Du (angularMeanScalar p) (angularMean f)
    (isSuitableWeakSolution_angularMean hsol hu hp hf haxi)
    (globalEnergyClass_angularMeanScalar u Du p henergy) hu
    (contDiffOn_angularMeanScalar (⊤ : ℕ∞) hp) (contDiffOn_angularMean_smooth hf) haxi
    (isAxisymmetricOn_angularMean_force f) (forceC2Bounded_angularMean hf hMf) ρ₀ hρ₀ hsmall

end CIV
