/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM07.Section2Base
import LeanPool.GraphMinor.GM07.MinimalNet
import LeanPool.GraphMinor.GM07.Section46FibreCount

/-!
# Endpoint identifications in a seam vertex fibre

The fibre over a seam vertex is joined by the pasted endpoint pairs.
We restrict the defining equivalence relation of the net to this fibre,
then count its points by its pairs. This supplies the finite count used
on page 225 in the proof of VII (4.6).
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface

universe u

/-- Each seam-vertex fibre has at most one more point than its pasted
endpoint pairs, as used in the fibre count of VII (4.6), page 225. -/
theorem Net.fibre_card_le_endpoint_pairs {S : Type u} [TopologicalSpace S]
    (N : Net S) {z : S} (hz : z ∈ N.seamV) :
    (N.φ ⁻¹' {z}).ncard ≤
      Nat.card {p : Fin N.r × Bool //
        N.φ (N.f p.1 (if p.2 then 1 else 0)) = z} + 1 := by
  classical
  let X := N.φ ⁻¹' {z}
  let I := {p : Fin N.r × Bool //
    N.φ (N.f p.1 (if p.2 then 1 else 0)) = z}
  let f : I → X := fun p => ⟨N.f p.1.1 (if p.1.2 then 1 else 0), p.2⟩
  let g : I → X := fun p => ⟨N.g p.1.1 (if p.1.2 then 1 else 0),
    (N.pasting_eq _ _).symm.trans p.2⟩
  have hfin : X.Finite := N.finite_fiber z
  have : Finite X := hfin.to_subtype
  have hne : Nonempty X := by
    obtain ⟨x, hx⟩ := N.quotientMap_φ.surjective z
    exact ⟨⟨x, hx⟩⟩
  have := hne
  let R : N.D → N.D → Prop := fun a b =>
    ∃ (i : Fin N.r) (t : unitInterval), a = N.f i t ∧ b = N.g i t
  let R' : X → X → Prop := fun a b => ∃ i, a = f i ∧ b = g i
  have hlift : ∀ x y, Relation.EqvGen R x y →
      ∀ hx : N.φ x = z, ∀ hy : N.φ y = z,
        Relation.EqvGen R' ⟨x, hx⟩ ⟨y, hy⟩ := by
    intro x y h
    induction h with
    | rel x y h =>
      obtain ⟨i, t, rfl, rfl⟩ := h
      intro hx hy
      have ht : t = 0 ∨ t = 1 := by
        by_cases h0 : t = 0
        · exact .inl h0
        by_cases h1 : t = 1
        · exact .inr h1
        have hti : t ∈ Ioo (0 : unitInterval) 1 := Net.mem_Ioo_of_ne h0 h1
        exact False.elim (N.notMem_seamV_of_mem_Ioo i hti (hx ▸ hz))
      rcases ht with rfl | rfl
      · exact .rel _ _ ⟨⟨(i, false), hx⟩, rfl, rfl⟩
      · exact .rel _ _ ⟨⟨(i, true), hx⟩, rfl, rfl⟩
    | refl x =>
      intro hx hy
      exact .refl _
    | symm x y _ ih =>
      intro hx hy
      exact .symm _ _ (ih hy hx)
    | trans x y z' hxy _ ih₁ ih₂ =>
      intro hx hz'
      have hy : N.φ y = z := ((N.bd_eq_iff x y).mpr hxy).symm.trans hx
      exact .trans _ _ _ (ih₁ hx hy) (ih₂ hy hz')
  have hc : ∀ x y : X, Relation.EqvGen R' x y := by
    intro x y
    exact hlift x y ((N.bd_eq_iff x y).mp (x.2.trans y.2.symm)) x.2 y.2
  exact card_le_pairs_add_one f g hc

end GraphMinor.GM07
