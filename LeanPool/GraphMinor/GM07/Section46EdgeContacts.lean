/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Rotation
import LeanPool.GraphMinor.Surface.SurfaceGraph
import LeanPool.GraphMinor.GM07.Section2Base

/-!
# Ordered vertex contacts of a parametrized seam edge

The list of contacts used for `W(e)` in VII (4.6), page 225, is finite
in the edge parameter. Its size is at least the number of graph vertices
on the closed edge. The parameter count allows a loop's two ends to be
listed at both ends of the interval.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface GraphMinor.GM11

universe u

/-- The contacts with the finite vertex set of `G` form a finite parameter
set on each seam edge, as used in VII (4.6), page 225. -/
theorem finite_edge_contact_parameters {S : Type u} [TopologicalSpace S]
    {G J : Drawing S} {γ : Set S → unitInterval → S} (hγ : EdgePar J γ)
    {e : Set S} (he : e ∈ J.E) : (γ e ⁻¹' G.V).Finite := by
  let T := γ e ⁻¹' G.V
  have hi : InjOn (γ e) (Ioo 0 1 ∩ T) := (hγ.inj e he).mono inter_subset_left
  have him : ((γ e) '' (Ioo 0 1 ∩ T)).Finite :=
    G.finite_V.subset (by rintro _ ⟨t, ht, rfl⟩; exact ht.2)
  have hfin := (finite_image_iff hi).mp him
  apply (((finite_singleton (1 : unitInterval)).insert 0).union hfin).subset
  intro t ht
  by_cases h0 : t = 0
  · exact .inl (.inl h0)
  by_cases h1 : t = 1
  · exact .inl (.inr h1)
  exact .inr ⟨⟨unitInterval.pos_iff_ne_zero.mpr h0,
    unitInterval.lt_one_iff_ne_one.mpr h1⟩, ht⟩

/-- The parameter list on a long edge contains all the contacts on its
closure. At a loop vertex the two parameter ends may repeat one contact,
as permitted by the ordered list in VII (4.6), page 225. -/
theorem ncard_edge_contacts_le_parameters {S : Type u} [TopologicalSpace S]
    [T2Space S] {G J : Drawing S} {γ : Set S → unitInterval → S}
    (hγ : EdgePar J γ) {e : Set S} (he : e ∈ J.E) :
    (closure e ∩ G.V).ncard ≤ (γ e ⁻¹' G.V).ncard := by
  have hcl : closure e ⊆ γ e '' univ := by
    apply closure_minimal _ ((isCompact_univ.image (hγ.cont e he)).isClosed)
    intro x hx
    obtain ⟨t, ht, rfl⟩ := (congrArg (fun A => x ∈ A) (hγ.image e he)).mpr hx
    exact ⟨t, mem_univ _, rfl⟩
  have hsub : closure e ∩ G.V ⊆ γ e '' (γ e ⁻¹' G.V) := by
    intro x hx
    obtain ⟨t, _, ht⟩ := hcl hx.1
    refine ⟨t, ?_, ht⟩
    change γ e t ∈ G.V
    rw [ht]
    exact hx.2
  have hfin := finite_edge_contact_parameters (G := G) hγ he
  exact (ncard_le_ncard hsub (hfin.image _)).trans (ncard_image_le hfin)

/-- An edge parameter only identifies its two ends. This gives injectivity
on either linking interval used in VII (4.6), page 225. -/
theorem edge_parameter_eq_or_ends {S : Type u} [TopologicalSpace S]
    {J : Drawing S} {γ : Set S → unitInterval → S} (hγ : EdgePar J γ)
    {e : Set S} (he : e ∈ J.E) {s t : unitInterval} (hst : γ e s = γ e t) :
    s = t ∨ s = 0 ∧ t = 1 ∨ s = 1 ∧ t = 0 := by
  have hmid : ∀ r ∈ Ioo (0 : unitInterval) 1, γ e r ∉ J.V := by
    intro r hr
    have hmem : γ e r ∈ e :=
      (congrArg (fun A => γ e r ∈ A) (hγ.image e he)).mp (mem_image_of_mem (γ e) hr)
    exact (he.2.1 hmem).2
  rcases Net.unitInterval_eq_zero_or_one_or_mem_Ioo s with rfl | rfl | hs
  · rcases Net.unitInterval_eq_zero_or_one_or_mem_Ioo t with rfl | rfl | ht
    · exact .inl rfl
    · exact .inr (.inl ⟨rfl, rfl⟩)
    · exact (hmid t ht (hst ▸ hγ.zero e he)).elim
  · rcases Net.unitInterval_eq_zero_or_one_or_mem_Ioo t with rfl | rfl | ht
    · exact .inr (.inr ⟨rfl, rfl⟩)
    · exact .inl rfl
    · exact (hmid t ht (hst ▸ hγ.one e he)).elim
  · rcases Net.unitInterval_eq_zero_or_one_or_mem_Ioo t with rfl | rfl | ht
    · exact (hmid s hs (hst.symm ▸ hγ.zero e he)).elim
    · exact (hmid s hs (hst.symm ▸ hγ.one e he)).elim
    · exact .inl (hγ.inj e he hs ht hst)

end GraphMinor.GM07
