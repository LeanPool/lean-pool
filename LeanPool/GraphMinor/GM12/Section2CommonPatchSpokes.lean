/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2PathHomotopy
import LeanPool.GraphMinor.GM12.Section2SectorHomotopy

/-!
# Comparing spokes after different approaches in one patch

In the positive-length restriction step of XII (2.1), pages 243--244,
the simple subcurve may approach a vertex along a different path from
the original curve. If both approaches lie in one corner patch, join
their starting points in the punctured patch. Simple connectedness
makes the two approaches agree after this prefix. Their entry
comparisons then lie in the same simply connected region. Cancelling
the common approach proves that the two spokes are homotopic.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- Entry comparisons for different approaches through the same
simply connected patch make the terminal spokes homotopic. The
puncture is used to join the two starting points inside the region. -/
theorem spokes_homotopic_of_common_patch
    {Z : Type*} [TopologicalSpace Z] {X R : Set Z} {v a b w : Z}
    (hX : IsSimplyConnectedSet X) (hR : IsSimplyConnectedSet R)
    (hpuncture : IsPathConnected (X \ {v})) (hXR : X \ {v} ⊆ R)
    (p : Path a v) (q : Path b v) (α β : Path v w)
    (hpX : ∀ t, p t ∈ X) (hqX : ∀ t, q t ∈ X)
    (ha : a ∈ X \ {v}) (hb : b ∈ X \ {v})
    (ρ : Path a w) (σ : Path b w)
    (hρ : ∀ t, ρ t ∈ R) (hσ : ∀ t, σ t ∈ R)
    (hentry : (p.trans α).Homotopic ρ) (hentry' : (q.trans β).Homotopic σ) :
    α.Homotopic β := by
  obtain ⟨ℓ, hℓ⟩ := hpuncture.joinedIn a ha b hb
  have hpq : p.Homotopic (ℓ.trans q) := by
    apply paths_homotopic_of_range_in_simplyConnected hX p (ℓ.trans q) hpX
    intro t
    rw [Path.trans_apply]
    split_ifs
    · exact (hℓ _).1
    · exact hqX _
  have hsecond : (p.trans β).Homotopic (ℓ.trans σ) :=
    (hpq.hcomp (Path.Homotopic.refl β)).trans
      ((Path.Homotopic.trans_assoc ℓ q β).trans
        ((Path.Homotopic.refl ℓ).hcomp hentry'))
  have hmiddle : ρ.Homotopic (ℓ.trans σ) := by
    apply paths_homotopic_of_range_in_simplyConnected hR ρ (ℓ.trans σ) hρ
    intro t
    rw [Path.trans_apply]
    split_ifs
    · exact hXR (hℓ _)
    · exact hσ _
  exact path_homotopic_cancel_left p α β (hentry.trans (hmiddle.trans hsecond.symm))

/-- The common-patch comparison in an ambient surface, with paths
read in a region together with its boundary vertex. Chart patches
need only be simply connected in the ambient surface. -/
theorem spokes_homotopic_of_common_ambient_patch
    {S : Type*} [TopologicalSpace S] {Z X R : Set S} {v a b w : Z}
    (hX : IsSimplyConnectedSet X) (hR : IsSimplyConnectedSet R)
    (hXZ : X ⊆ Z) (hRZ : R ⊆ Z)
    (hpuncture : IsPathConnected (X \ {v.val})) (hXR : X \ {v.val} ⊆ R)
    (p : Path a v) (q : Path b v) (α β : Path v w)
    (hpX : ∀ t, (p t).val ∈ X) (hqX : ∀ t, (q t).val ∈ X)
    (ha : a.val ∈ X \ {v.val}) (hb : b.val ∈ X \ {v.val})
    (ρ : Path a w) (σ : Path b w)
    (hρ : ∀ t, (ρ t).val ∈ R) (hσ : ∀ t, (σ t).val ∈ R)
    (hentry : (p.trans α).Homotopic ρ) (hentry' : (q.trans β).Homotopic σ) :
    α.Homotopic β := by
  obtain ⟨ℓ₀, hℓ₀⟩ := hpuncture.joinedIn a.val ha b.val hb
  let ℓ : Path a b := {
    toFun := fun t => ⟨ℓ₀ t, hXZ (hℓ₀ t).1⟩
    continuous_toFun := ℓ₀.continuous.subtype_mk _
    source' := Subtype.ext ℓ₀.source
    target' := Subtype.ext ℓ₀.target }
  have hpq : p.Homotopic (ℓ.trans q) := by
    apply paths_homotopic_in_subspace_of_patch hX hXZ p (ℓ.trans q) hpX
    intro t
    rw [Path.trans_apply]
    split_ifs
    · exact (hℓ₀ _).1
    · exact hqX _
  have hsecond : (p.trans β).Homotopic (ℓ.trans σ) :=
    (hpq.hcomp (Path.Homotopic.refl β)).trans
      ((Path.Homotopic.trans_assoc ℓ q β).trans
        ((Path.Homotopic.refl ℓ).hcomp hentry'))
  have hmiddle : ρ.Homotopic (ℓ.trans σ) := by
    apply paths_homotopic_in_subspace_of_patch hR hRZ ρ (ℓ.trans σ) hρ
    intro t
    rw [Path.trans_apply]
    split_ifs
    · exact hXR (hℓ₀ _)
    · exact hσ _
  exact path_homotopic_cancel_left p α β (hentry.trans (hmiddle.trans hsecond.symm))

end GraphMinor.GM12
