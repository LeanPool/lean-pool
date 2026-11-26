/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM16.Section9Zones
import LeanPool.GraphMinor.GM11.Section810
import LeanPool.GraphMinor.GM14.Section3
import LeanPool.GraphMinor.GM15.Section4

/-!
# Zones after clearing a disjoint zone

In the proof of XVI (8.1), each battlefield disc remains a zone while
other discs are cleared. Its boundary and centre survive. Every atom
inside its closure is unchanged, so the upper distance bound follows
from the fact that clearing does not increase distances.
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM14
universe w
variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

omit [ConnectedSpace S] in
/-- An atom of the cleared drawing inside a disjoint closed set was already
an atom of the original drawing. The only new region is the cleared disc. -/
theorem cleared_atom_mem_of_disjoint {H : Drawing S} {d : Set S → Set S → ℕ}
    {γ : ℕ} {z Ω A a : Set S} (hΩ : IsLambdaZoneAround H d γ z Ω)
    (hdis : Disjoint A Ω) (ha : a ∈ (clearedSubdrawing H Ω).A) (haA : a ⊆ A) :
    a ∈ H.A := by
  rcases ha with (⟨v, hv, rfl⟩ | he) | hr
  · exact Or.inl (Or.inl ⟨v, (clearedSubdrawing_isSubdrawing H Ω).1 hv, rfl⟩)
  · exact Or.inl (Or.inr ((clearedSubdrawing_isSubdrawing H Ω).2 he))
  · rcases clearedSubdrawing_region_eq_or_mem_R hΩ hr with heq | hrH
    · obtain ⟨x, hxz⟩ := GraphMinor.GM15.atom_nonempty hΩ.z_mem
      have hx := hΩ.z_subset hxz
      exact False.elim (hdis.notMem_of_mem_left (haA (heq.symm ▸ hx)) hx)
    · exact Or.inr hrH

/-- Graph Minors XVI, proof of (8.1), page 71: a battlefield zone remains
a zone after another disc with disjoint closure is cleared. -/
theorem zone_after_disjoint_clearing {H : Drawing S}
    {T T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d d' : Set S → Set S → ℕ} {θ γ : ℕ} {y z : S} {Λ Ω : Set S}
    (hyH : y ∈ H.V) (hΛ : IsLambdaZoneAround H d γ {y} Λ)
    (hΩ : IsLambdaZoneAround H d γ {z} Ω)
    (hdis : Disjoint (closure Λ) (closure Ω))
    (hClear : IsClearedTangle H T d θ γ Ω T' d') :
    IsLambdaZoneAround (clearedSubdrawing H Ω) d' γ {y} Λ := by
  have hyΛ : y ∈ Λ := hΛ.z_subset (mem_singleton y)
  have hyΩ : y ∉ Ω := fun hy => hdis.notMem_of_mem_left (subset_closure hyΛ) (subset_closure hy)
  have hyNew : y ∈ (clearedSubdrawing H Ω).V :=
    (mem_interSet_V_iff (isClosed_univ.sdiff hΩ.isOpenDisc.1)).mpr ⟨hyH, mem_univ _, hyΩ⟩
  refine ⟨Or.inl (Or.inl ⟨y, hyNew, rfl⟩), hΛ.isOpenDisc, hΛ.z_subset,
    hΛ.isOArc_bd, hΛ.isClosedDisc_closure, ?_, ?_, ?_⟩
  · apply oArc_subset_interSet_U hΛ.isOArc_bd hΛ.bd_subset_U
    intro x hx
    exact ⟨mem_univ _, fun hxΩ => hdis.notMem_of_mem_left hx.1 (subset_closure hxΩ)⟩
  · intro a ha haΛ
    have haH := cleared_atom_mem_of_disjoint hΩ
      (disjoint_left.mpr fun x hxΛ hxΩ => hdis.notMem_of_mem_left hxΛ (subset_closure hxΩ)) ha haΛ
    exact ((hClear.dist_bounds {y} hΛ.z_mem a haH {y}
      (Or.inl (Or.inl ⟨y, hyNew, rfl⟩)) a ha Subset.rfl Subset.rfl).2).trans (hΛ.dist_le a haH haΛ)
  · intro he
    exact hΛ.two_le_of_edge ((clearedSubdrawing_isSubdrawing H Ω).2 he)

omit [ConnectedSpace S] in
/-- Every old atom farther than the radius from the centre survives a
clearing. Choose a point outside the zone closure. The only new atom
that is not an old atom is the cleared region itself. -/
theorem far_atom_mem_cleared {H : Drawing S} {d : Set S → Set S → ℕ}
    {γ : ℕ} {z Ω a : Set S} (hΩ : IsLambdaZoneAround H d γ z Ω)
    (ha : a ∈ H.A) (hfar : γ < d z a) : a ∈ (clearedSubdrawing H Ω).A := by
  have hnot : ¬ a ⊆ closure Ω := fun hsub => (Nat.not_le_of_lt hfar) (hΩ.dist_le a ha hsub)
  obtain ⟨x, hxa, hxΩ⟩ := not_subset.mp hnot
  obtain ⟨a', ha', hxa'⟩ := GraphMinor.GM15.exists_atom_of_point (clearedSubdrawing H Ω) x
  have haH : a' ∈ H.A := by
    rcases ha' with (⟨v, hv, rfl⟩ | he) | hr
    · exact Or.inl (Or.inl ⟨v, (clearedSubdrawing_isSubdrawing H Ω).1 hv, rfl⟩)
    · exact Or.inl (Or.inr ((clearedSubdrawing_isSubdrawing H Ω).2 he))
    · rcases clearedSubdrawing_region_eq_or_mem_R hΩ hr with heq | hrH
      · exact False.elim (hxΩ (subset_closure (heq ▸ hxa')))
      · exact Or.inr hrH
  have heq := GraphMinor.GM15.atom_eq_of_mem ha haH hxa hxa'
  exact heq.symm ▸ ha'

end GraphMinor.GM16
