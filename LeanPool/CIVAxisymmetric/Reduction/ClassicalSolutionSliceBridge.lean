/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Reduction.AnalyticOfBounds
public import LeanPool.CIVAxisymmetric.Statements.IsClassicalSolutionOn
public import LeanPool.CIVAxisymmetric.Statements.UnitCylinder

public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Classical solution slices on the unit cylinder

These lemmas extract the smoothness and divergence-free hypotheses of
`IsClassicalSolutionOn` on time slices inside the unit cylinder, producing the
ball-restricted hypotheses that the closure-lemma assembly's Sobolev and elliptic
steps consume.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN


noncomputable section



namespace CIV

/-- Reading the divergence-free clause of `IsClassicalSolutionOn` off as a time-sliced,
ball-restricted hypothesis: for every `t ∈ (tη, 0)` and `x ∈ U` the point `(x, t)` lies in the
cylinder, so `∑ j, spatialPartial (fun w => u w j) j (x, t) = 0` holds. -/
theorem hdiv_of_isClassicalSolutionOn {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} {U : Set Vec3} {tη : ℝ}
    (hsol : IsClassicalSolutionOn u p f unitCylinder)
    (hUt : ∀ t ∈ Ioo tη (0 : ℝ), ∀ x ∈ U, ((x, t) : ParabolicPoint) ∈ unitCylinder) :
    ∀ t ∈ Ioo tη (0 : ℝ), ∀ x ∈ U,
      ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => u (y, t) j) x (basisVec j) = 0 := by
  intro t ht x hx
  have hz := hUt t ht x hx
  have hkey := hsol.2.2.2.2 (x, t) hz
  simpa only [CKN.spatialPartial] using hkey

/-- Specialising `hdiv_of_isClassicalSolutionOn` to the unit cylinder: any `Rstar ≤ 1` gives a
ball `B(0, Rstar)` that is contained in `B(0, 1)`, so the pair `(x, t)` stays in the unit
cylinder whenever `t ∈ (-1, 0)` and `x ∈ B(0, Rstar)`. -/
theorem hdiv_of_isClassicalSolutionOn_vec3Ball {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} {Rstar : ℝ} (hRstar : Rstar ≤ 1)
    (hsol : IsClassicalSolutionOn u p f unitCylinder) :
    ∀ t ∈ Ioo (-1 : ℝ) (0 : ℝ), ∀ x ∈ vec3Ball (0 : Vec3) Rstar,
      ∑ j : Fin 3, fderiv ℝ (fun y : Vec3 => u (y, t) j) x (basisVec j) = 0 := by
  refine hdiv_of_isClassicalSolutionOn hsol (fun t ht x hx => ⟨vec3Ball_mono hRstar hx, ht⟩)

/-- Reading the smoothness clause of `IsClassicalSolutionOn` off as a time-sliced, ball-restricted
hypothesis: `hsol.1` gives `ContDiffOn` on `unitCylinder = B(1) × (-1, 0)`.  Restricting to
`B(Rstar) × (-1, 0)` and then slicing at `t ∈ (-1, 0)` yields `ContDiffOn ℝ (⊤ : ℕ∞)` of
each component of `u(·, t)` on `B(Rstar, 0)`. -/
theorem hu_of_isClassicalSolutionOn_vec3Ball {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3} {Rstar : ℝ} (hRstar : Rstar ≤ 1)
    (hsol : IsClassicalSolutionOn u p f unitCylinder) :
    ∀ t ∈ Ioo (-1 : ℝ) (0 : ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) (fun x : Vec3 => u (x, t)) (vec3Ball (0 : Vec3) Rstar) := by
  intro t ht
  have hu' : ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec3 × ℝ => u z)
      (spaceTimeSet (vec3Ball 0 Rstar) (Ioo (-1 : ℝ) 0)) :=
    hsol.1.mono (Set.prod_mono (vec3Ball_mono hRstar) subset_rfl)
  exact contDiffOn_pi.2 fun i => contDiffOn_slice_component ht hu' i

end CIV
