/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2PathHomotopy
public import LeanPool.GraphMinor.GM12.Section2SectorHomotopy

/-!
# Closing an entry curve inside its corner

For the omitted entry-edge existence assertion on XII page 243, the
incoming curve and a spoke can be compared in a small corner patch.
Its punctured part joins their nearby points without passing through the
vertex. Simple connectivity then replaces their concatenation by that
joining path. The rest of the spoke already lies in the region.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- A spoke whose initial segment lies in the same simply-connected
corner patch as an incoming path satisfies the homotopy condition of the
entry definition. The punctured patch supplies a replacement path in
the region, and the spoke beyond the patch stays in that region. -/
theorem entry_homotopy_of_patch {Z : Type*} [TopologicalSpace Z]
    {X R : Set Z} {v a b : Z} (hX : IsSimplyConnectedSet X)
    (hpuncture : IsPathConnected (X \ {v})) (hXR : X \ {v} ⊆ R)
    (p : Path a v) (β : Path v b) (hp : ∀ t, p t ∈ X)
    (ha : a ∈ X \ {v}) (s : unitInterval)
    (hs : β s ∈ X \ {v})
    (hβ : ∀ t, (β.subpath 0 s) t ∈ X)
    (htail : ∀ t, (β.subpath s 1) t ∈ R) :
    ∃ ρ : Path a b, (∀ t, ρ t ∈ R) ∧ (p.trans β).Homotopic ρ := by
  let α : Path v (β s) := (β.subpath 0 s).cast β.source.symm rfl
  let τ : Path (β s) b := (β.subpath s 1).cast rfl β.target.symm
  obtain ⟨σ, hσ⟩ := hpuncture.joinedIn a ha (β s) hs
  have hfirst : (p.trans α).Homotopic σ := by
    apply paths_homotopic_of_range_in_simplyConnected hX
    · intro t
      rw [Path.trans_apply]
      split_ifs
      · exact hp _
      · exact hβ _
    · intro t
      exact (hσ t).1
  have hsplit : (α.trans τ).Homotopic β :=
    split_path_homotopic β s α τ (fun _ => rfl) (fun _ => rfl)
  refine ⟨σ.trans τ, ?_, ?_⟩
  · intro t
    rw [Path.trans_apply]
    split_ifs
    · exact hXR (hσ _)
    · exact htail _
  · exact ((Path.Homotopic.refl p).hcomp hsplit.symm).trans
      ((Path.Homotopic.trans_assoc p α τ).symm.trans
        (hfirst.hcomp (Path.Homotopic.refl τ)))

/-- The common-patch criterion with the patch in the surface and paths
in a subspace, as required when that subspace is a region with one
boundary vertex added. -/
theorem entry_homotopy_of_ambient_patch {S : Type*} [TopologicalSpace S]
    {Z X : Set S} {R : Set Z} {v a b : Z}
    (hX : IsSimplyConnectedSet X) (hXZ : X ⊆ Z)
    (hpuncture : IsPathConnected (X \ {v.val}))
    (hXR : ∀ z : Z, z.val ∈ X \ {v.val} → z ∈ R)
    (p : Path a v) (β : Path v b) (hp : ∀ t, (p t).val ∈ X)
    (ha : a.val ∈ X \ {v.val}) (s : unitInterval)
    (hs : (β s).val ∈ X \ {v.val})
    (hβ : ∀ t, ((β.subpath 0 s) t).val ∈ X)
    (htail : ∀ t, (β.subpath s 1) t ∈ R) :
    ∃ ρ : Path a b, (∀ t, ρ t ∈ R) ∧ (p.trans β).Homotopic ρ := by
  let α : Path v (β s) := (β.subpath 0 s).cast β.source.symm rfl
  let τ : Path (β s) b := (β.subpath s 1).cast rfl β.target.symm
  obtain ⟨σ₀, hσ₀⟩ := hpuncture.joinedIn a.val ha (β s).val hs
  let σ : Path a (β s) := {
    toFun := fun t => ⟨σ₀ t, hXZ (hσ₀ t).1⟩
    continuous_toFun := σ₀.continuous.subtype_mk _
    source' := Subtype.ext σ₀.source
    target' := Subtype.ext σ₀.target }
  have hσ : ∀ t, σ t ∈ R := fun t => hXR (σ t) (hσ₀ t)
  have hfirst : (p.trans α).Homotopic σ := by
    apply paths_homotopic_in_subspace_of_patch hX hXZ
    · intro t
      rw [Path.trans_apply]
      split_ifs
      · exact hp _
      · exact hβ _
    · intro t
      exact (hσ₀ t).1
  have hsplit : (α.trans τ).Homotopic β :=
    split_path_homotopic β s α τ (fun _ => rfl) (fun _ => rfl)
  refine ⟨σ.trans τ, ?_, ?_⟩
  · intro t
    rw [Path.trans_apply]
    split_ifs
    · exact hσ _
    · exact htail _
  · exact ((Path.Homotopic.refl p).hcomp hsplit.symm).trans
      ((Path.Homotopic.trans_assoc p α τ).symm.trans
        (hfirst.hcomp (Path.Homotopic.refl τ)))

end GraphMinor.GM12
