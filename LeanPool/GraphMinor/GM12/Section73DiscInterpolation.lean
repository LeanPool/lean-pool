/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.Surface.Disc

/-!
# Interpolating maps with values in a closed disc

For the inside comparison in XII (7.3), Claim (1), page 262,
interpolate the supported collapse with the identity inside its
supporting disc. A disc coordinate identifies the disc with a
convex set. Straight-line interpolation in this coordinate stays
in the disc and fixes any point where the two maps agree.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- Two maps into a closed disc interpolate inside that disc,
fixing points where they agree. This gives the local homotopy
for the supported radial collapse in XII (7.3), Claim (1). -/
theorem exists_disc_interpolation
    {X S : Type*} [TopologicalSpace X] [TopologicalSpace S]
    {D : Set S} (hD : IsClosedDisc D) (f g : C(X, S))
    (hf : range f ⊆ D) (hg : range g ⊆ D) :
    ∃ H : C(unitInterval × X, S), (∀ w, H w ∈ D) ∧
      (∀ x, H (0, x) = f x) ∧ (∀ x, H (1, x) = g x) ∧
      ∀ x, f x = g x → ∀ t, H (t, x) = f x := by
  obtain ⟨e⟩ := hD
  let f₀ : C(X, ClosedUnitDisc) :=
    ⟨fun x => e.symm ⟨f x, hf (mem_range_self x)⟩, by fun_prop⟩
  let f₁ : C(X, ClosedUnitDisc) :=
    ⟨fun x => e.symm ⟨g x, hg (mem_range_self x)⟩, by fun_prop⟩
  let F : C(unitInterval × X, EuclideanPlane) :=
    ⟨fun w => (1 - w.1.val) • (f₀ w.2).val + w.1.val • (f₁ w.2).val, by fun_prop⟩
  have hFD : ∀ w, F w ∈ ClosedUnitDisc := by
    intro w
    exact convex_closedUnitDisc (f₀ w.2).property (f₁ w.2).property
      (sub_nonneg.mpr w.1.property.2) w.1.property.1 (sub_add_cancel 1 w.1.val)
  let H : C(unitInterval × X, S) :=
    ⟨fun w => (e ⟨F w, hFD w⟩).val, by fun_prop⟩
  refine ⟨H, fun w => (e ⟨F w, hFD w⟩).property, ?_, ?_, ?_⟩
  · intro x
    have heq : (⟨F (0, x), hFD (0, x)⟩ : ClosedUnitDisc) = f₀ x := by
      apply Subtype.ext
      simp only [F, ContinuousMap.coe_mk, Icc.coe_zero, sub_zero, one_smul,
        zero_smul, add_zero]
    change (e ⟨F (0, x), hFD (0, x)⟩).val = f x
    rw [heq]
    exact congrArg Subtype.val (e.apply_symm_apply _)
  · intro x
    have heq : (⟨F (1, x), hFD (1, x)⟩ : ClosedUnitDisc) = f₁ x := by
      apply Subtype.ext
      simp only [F, ContinuousMap.coe_mk, Icc.coe_one, sub_self, zero_smul,
        one_smul, zero_add]
    change (e ⟨F (1, x), hFD (1, x)⟩).val = g x
    rw [heq]
    exact congrArg Subtype.val (e.apply_symm_apply _)
  · intro x hfg t
    have heq : f₀ x = f₁ x := congrArg e.symm (Subtype.ext hfg)
    have hFt : (⟨F (t, x), hFD (t, x)⟩ : ClosedUnitDisc) = f₀ x := by
      apply Subtype.ext
      change (1 - t.val) • (f₀ x).val + t.val • (f₁ x).val = (f₀ x).val
      rw [← heq, ← add_smul, sub_add_cancel, one_smul]
    change (e ⟨F (t, x), hFD (t, x)⟩).val = f x
    rw [hFt]
    exact congrArg Subtype.val (e.apply_symm_apply _)

end GraphMinor.GM12
