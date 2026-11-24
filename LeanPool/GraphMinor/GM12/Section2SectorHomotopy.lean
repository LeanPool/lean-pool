/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2SectorPatch
public import LeanPool.GraphMinor.GM12.Section2PathHomotopy
import LeanPool.GraphMinor.GM11.Section3

/-!
# Replacing paths in a corner near its vertex

The entry-edge construction on XII page 243 needs to replace an approach
by a path in the same corner. A small patch of a sector disc is simply
connected even when the approach touches its boundary vertex tangentially.
Lift paths to that patch and map the resulting homotopy into the corner
with its vertex added.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- A simply-connected subset of a subspace gives homotopies in that
subspace. The inclusion condition is used to map the homotopy back. -/
theorem paths_homotopic_in_subspace_of_patch {S : Type*} [TopologicalSpace S]
    {X Z : Set S} (hX : IsSimplyConnectedSet X) (hXZ : X ⊆ Z)
    {a b : Z} (p q : Path a b)
    (hp : ∀ t, (p t).val ∈ X) (hq : ∀ t, (q t).val ∈ X) :
    p.Homotopic q := by
  have ha : a.val ∈ X := p.source ▸ hp 0
  have hb : b.val ∈ X := p.target ▸ hp 1
  let pX : Path (⟨a.val, ha⟩ : X) ⟨b.val, hb⟩ := {
    toFun := fun t => ⟨(p t).val, hp t⟩
    continuous_toFun := (continuous_subtype_val.comp p.continuous).subtype_mk _
    source' := by
      apply Subtype.ext
      change (p 0).val = a.val
      exact congrArg Subtype.val p.source
    target' := by
      apply Subtype.ext
      change (p 1).val = b.val
      exact congrArg Subtype.val p.target }
  let qX : Path (⟨a.val, ha⟩ : X) ⟨b.val, hb⟩ := {
    toFun := fun t => ⟨(q t).val, hq t⟩
    continuous_toFun := (continuous_subtype_val.comp q.continuous).subtype_mk _
    source' := by
      apply Subtype.ext
      change (q 0).val = a.val
      exact congrArg Subtype.val q.source
    target' := by
      apply Subtype.ext
      change (q 1).val = b.val
      exact congrArg Subtype.val q.target }
  let inclusion : C(X, Z) := ⟨fun x => ⟨x.val, hXZ x.property⟩,
    continuous_subtype_val.subtype_mk _⟩
  exact (hX.pathsHomotopic pX qX).map inclusion

/-- Two sufficiently short paths in a sector with its boundary vertex
added are homotopic in any subspace containing the sector interior near
that vertex. This is the local replacement step in the entry definition
of Graph Minors XII, page 243. -/
theorem exists_sector_path_replacement {S : Type*} [TopologicalSpace S]
    {D W Z : Set S} (hD : IsClosedDisc D) {v : S} (hv : v ∈ discBd D)
    (hW : IsOpen W) (hvW : v ∈ W)
    (hZ : ((D \ discBd D) ∩ W) ∪ {v} ⊆ Z) :
    ∃ N : Set S, IsOpen N ∧ v ∈ N ∧
      ∀ {a b : Z} (p q : Path a b),
        (∀ t, (p t).val ∈ ((N ∩ D) \ discBd D) ∪ {v}) →
        (∀ t, (q t).val ∈ ((N ∩ D) \ discBd D) ∪ {v}) →
        p.Homotopic q := by
  obtain ⟨N, X, hN, hvN, hvX, hX, hXZ, hNX⟩ :=
    exists_simplyConnected_sector_patch hD hv hW hvW
  refine ⟨N, hN, hvN, ?_⟩
  intro a b p q hp hq
  have hsub : ((N ∩ D) \ discBd D) ∪ {v} ⊆ X := by
    intro x hx
    rcases hx with hx | hx
    · exact hNX hx
    · exact mem_singleton_iff.mp hx ▸ hvX
  exact paths_homotopic_in_subspace_of_patch hX (fun _ hx => hZ (hXZ hx)) p q
    (fun t => hsub (hp t)) (fun t => hsub (hq t))

end GraphMinor.GM12
