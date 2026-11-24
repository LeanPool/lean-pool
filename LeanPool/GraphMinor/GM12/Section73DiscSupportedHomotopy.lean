/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73DiscInterpolation
import Mathlib.Topology.ContinuousOn
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# Extending the disc interpolation by the identity

For XII (7.3), Claim (1), page 262, a collapse supported in a
closed disc deforms to the identity without moving any point
outside the disc's interior. Interpolate in disc coordinates,
then paste with the identity on the closed complement of the
interior. The two formulas agree on the boundary.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- A map supported inside a closed disc and preserving that disc
is homotopic to the identity, fixing its boundary and outside.
This controls the boundary deformation for the selected-inside
comparison in XII (7.3), Claim (1), page 262. -/
theorem exists_disc_supported_homotopy
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {D : Set S} (hD : IsClosedDisc D) (f : C(S, S))
    (hmap : ∀ x ∈ D, f x ∈ D) (hfix : ∀ x ∉ interior D, f x = x) :
    ∃ H : C(unitInterval × S, S), (∀ x, H (0, x) = x) ∧
      (∀ x, H (1, x) = f x) ∧
      (∀ t x, x ∉ interior D → H (t, x) = x) ∧
      ∀ t x, x ∈ D → H (t, x) ∈ D := by
  classical
  let ι : C(D, S) := ⟨Subtype.val, continuous_subtype_val⟩
  let fd : C(D, S) := f.comp ι
  obtain ⟨F, hFD, hF₀, hF₁, hFfix⟩ := exists_disc_interpolation hD ι fd
    (by rintro _ ⟨x, rfl⟩; exact x.property)
    (by rintro _ ⟨x, rfl⟩; exact hmap x.val x.property)
  let H : unitInterval × S → S := fun w =>
    if hx : w.2 ∈ D then F (w.1, ⟨w.2, hx⟩) else w.2
  have hHfix : ∀ t x, x ∉ interior D → H (t, x) = x := by
    intro t x hx
    dsimp only [H]
    by_cases hxD : x ∈ D
    · rw [dite_eq_left hxD]
      exact hFfix ⟨x, hxD⟩ (hfix x hx).symm t
    · rw [dite_eq_right hxD]
  have hOn : ContinuousOn H (Prod.snd ⁻¹' D) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    have hc : Continuous (fun w : (Prod.snd ⁻¹' D : Set (unitInterval × S)) =>
        F (w.val.1, ⟨w.val.2, w.property⟩)) := by fun_prop
    apply hc.congr
    intro w
    change F (w.val.1, ⟨w.val.2, w.property⟩) =
      if hx : w.val.2 ∈ D then F (w.val.1, ⟨w.val.2, hx⟩) else w.val.2
    have hwD : w.val.2 ∈ D := w.property
    rw [dite_eq_left hwD]
  have hOff : ContinuousOn H (Prod.snd ⁻¹' (interior D)ᶜ) := by
    apply continuous_snd.continuousOn.congr
    intro w hw
    exact hHfix w.1 w.2 hw
  have hcover : (Prod.snd ⁻¹' D : Set (unitInterval × S)) ∪
      (Prod.snd ⁻¹' (interior D)ᶜ) = univ := by
    apply eq_univ_of_forall
    intro w
    by_cases hw : w.2 ∈ interior D
    · exact Or.inl (show w.2 ∈ D from interior_subset hw)
    · exact Or.inr hw
  have hcont : Continuous H := by
    have hc := hOn.union_of_isClosed hOff
      (hD.isCompact.isClosed.preimage continuous_snd)
      (isOpen_interior.isClosed_compl.preimage continuous_snd)
    rw [hcover] at hc
    exact continuousOn_univ.mp hc
  refine ⟨⟨H, hcont⟩, ?_, ?_, hHfix, ?_⟩
  · intro x
    change H (0, x) = x
    dsimp only [H]
    by_cases hx : x ∈ D
    · rw [dite_eq_left hx]
      exact hF₀ ⟨x, hx⟩
    · rw [dite_eq_right hx]
  · intro x
    change H (1, x) = f x
    dsimp only [H]
    by_cases hx : x ∈ D
    · rw [dite_eq_left hx]
      exact hF₁ ⟨x, hx⟩
    · rw [dite_eq_right hx]
      exact (hfix x (fun hi => hx (interior_subset hi))).symm
  · intro t x hx
    change H (t, x) ∈ D
    dsimp only [H]
    rw [dite_eq_left hx]
    exact hFD _

/-- A supported disc deformation gives a homotopy of any closed
curve to its image. The homotopy stays in any set containing the
curve and the supporting disc. This permits the punctured-surface
comparison of selected insides in XII (7.3), Claim (1). -/
theorem closedCurve_homotopic_of_disc_supported_map
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {D Z : Set S} (hD : IsClosedDisc D) (f : C(S, S))
    (hmap : ∀ x ∈ D, f x ∈ D) (hfix : ∀ x ∉ interior D, f x = x)
    (φ : C(Circle, S)) (hφZ : range φ ⊆ Z) (hDZ : D ⊆ Z) :
    ClosedCurvesHomotopicIn Z φ (f.comp φ) := by
  obtain ⟨H, hH₀, hH₁, hHfix, hHD⟩ := exists_disc_supported_homotopy hD f hmap hfix
  let Ψ : C(Circle × unitInterval, S) := ⟨fun w => H (w.2, φ w.1), by fun_prop⟩
  refine ⟨Ψ, ?_, ?_, ?_⟩
  · intro w
    change H (w.2, φ w.1) ∈ Z
    by_cases hx : φ w.1 ∈ D
    · exact hDZ (hHD w.2 _ hx)
    · rw [hHfix w.2 _ (fun hi => hx (interior_subset hi))]
      exact hφZ (mem_range_self _)
  · intro z
    exact hH₀ (φ z)
  · intro z
    exact hH₁ (φ z)

end GraphMinor.GM12
