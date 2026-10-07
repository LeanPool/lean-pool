/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Reduction.AveragedClassical
public import LeanPool.CIVAxisymmetric.Statements.AnisotropicBounds

/-!
# Congruence of iterated derivatives for axisymmetric fields

If a vector field is axisymmetric on the unit cylinder, then its angular mean agrees
with the field itself there, and consequently every iterated spatial partial derivative
of each component of the angular mean agrees with the same derivative of the original
field — and the anisotropic `ℒ²` bounds transfer from the angular mean to the field.
-/

public section

open Set
open CKN.Foundation.Parabolic CKN

noncomputable section
namespace CIV



/-- Two scalar fields that agree on the unit cylinder have equal iterated spatial partial
derivatives in a fixed direction, at every point of the unit cylinder. -/
theorem spatialPartial_iterate_congr_of_eqOn {g h : ParabolicPoint → ℝ}
    (heq : Set.EqOn g h unitCylinder) (i : Fin 3) (n : ℕ) :
    Set.EqOn ((fun k => spatialPartial k i)^[n] g) ((fun k => spatialPartial k i)^[n] h)
      unitCylinder := by
  induction n with
  | zero => simpa using heq
  | succ k ih =>
    simp only [Function.iterate_succ', Function.comp_apply]
    intro z hz
    exact spatialPartial_congr_of_eqOn ih hz i

/-- For an axisymmetric field, every multi-index spatial partial derivative of a component
of its angular mean agrees with the same derivative of the field itself, at every point of
the unit cylinder — the angular mean does not move a field that is already axisymmetric
there. -/
theorem multiPartial_congr_of_isAxisymmetricOn {u : ParabolicPoint → Vec3}
    (haxi : IsAxisymmetricOn u unitCylinder) (i : Fin 3) (α : Fin 3 → ℕ)
    {z : ParabolicPoint} (hz : z ∈ unitCylinder) :
    multiPartial (fun w => angularMean u w i) α z = multiPartial (fun w => u w i) α z := by
  have heq0 : Set.EqOn (fun w => angularMean u w i) (fun w => u w i) unitCylinder :=
    fun w hw => congrFun (haxi w hw) i
  have heq2 := spatialPartial_iterate_congr_of_eqOn heq0 2 (α 2)
  have heq1 := spatialPartial_iterate_congr_of_eqOn heq2 1 (α 1)
  have heq0' := spatialPartial_iterate_congr_of_eqOn heq1 0 (α 0)
  exact heq0' hz

/-- The meridional-plane specialization of the previous theorem: for an axisymmetric field,
iterated meridional partial derivatives of the angular mean of a component agree with the
same derivatives of the component itself. -/
theorem meridionalPartial_congr_of_isAxisymmetricOn {u : ParabolicPoint → Vec3}
    (haxi : IsAxisymmetricOn u unitCylinder) (i : Fin 3) (a b : ℕ)
    {z : ParabolicPoint} (hz : z ∈ unitCylinder) :
    meridionalPartial (fun w => angularMean u w i) a b z
      = meridionalPartial (fun w => u w i) a b z := by
  have heq0 : Set.EqOn (fun w => angularMean u w i) (fun w => u w i) unitCylinder :=
    fun w hw => congrFun (haxi w hw) i
  have heq2 := spatialPartial_iterate_congr_of_eqOn heq0 2 b
  have heq0' := spatialPartial_iterate_congr_of_eqOn heq2 0 a
  exact heq0' hz

/-- The anisotropic `ℒ²` bounds transfer from the angular mean of an axisymmetric field
to the field itself — used to convert `thm:main`'s hypothesis `AnisotropicBounds C h
(angularMean u)`
into the hypothesis `AnisotropicBounds C h u` that `thm:aniso:main` needs, once `u` is known to
be axisymmetric on the unit cylinder. -/
theorem anisotropicBounds_of_isAxisymmetricOn {C h : ℝ} {u : ParabolicPoint → Vec3}
    (haxi : IsAxisymmetricOn u unitCylinder)
    (hbounds : AnisotropicBounds C h (angularMean u)) :
    AnisotropicBounds C h u := by
  intro a b hab x₁ x₃ t hz
  obtain ⟨h1, h2⟩ := hbounds a b hab x₁ x₃ t hz
  refine ⟨?_, ?_⟩
  · rwa [meridionalPartial_congr_of_isAxisymmetricOn haxi 0 a b hz] at h1
  · rwa [meridionalPartial_congr_of_isAxisymmetricOn haxi 2 a b hz,
      meridionalPartial_congr_of_isAxisymmetricOn haxi 1 a b hz] at h2

end CIV
