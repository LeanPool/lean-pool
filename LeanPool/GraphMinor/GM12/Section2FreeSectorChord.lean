/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2SectorSpoke
public import LeanPool.GraphMinor.GM11.RadialCorners

/-!
# A parallel spoke obtained from a free entering sector

For the free-neighbourhood case of the omitted entry assertion in XII,
page 243, start a path in the sector interior. It stays in one region
of the union with the radial drawing. That region approaches the hub.
A chord through the region retains the initial sector germ, and radial
maximality gives a spoke and a disc between that spoke and the chord.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 unitInterval

/-- A continuous approach staying off a drawing stays in one region. -/
theorem exists_region_of_approach {S : Type*} [TopologicalSpace S]
    (H : Drawing S) {g : I → S} (hg : Continuous g)
    (hoff : ∀ t, 0 < t → g t ∉ H.U) :
    ∃ p ∈ H.R, ∀ t, 0 < t → g t ∈ p := by
  obtain ⟨p, hp, hg1⟩ := exists_region_of_notMem (hoff 1 one_pos)
  let A : Set S := g '' Ioc (0 : I) 1
  have hA : IsPreconnected A := isPreconnected_Ioc.image g hg.continuousOn
  have hdis : Disjoint A H.U := Set.disjoint_left.mpr fun _ hx hxU => by
    obtain ⟨t, ht, rfl⟩ := hx
    exact hoff t ht.1 hxU
  have hsub : A ⊆ p := subset_region hp hA hdis ⟨1, ⟨one_pos, le_rfl⟩, rfl⟩ hg1
  exact ⟨p, hp, fun t ht => hsub ⟨t, ⟨ht, t.property.2⟩, rfl⟩⟩

/-- A radial-free sector germ gives a chord to the hub and a parallel
radial edge. The chord retains its germ in the prescribed sector. -/
theorem exists_parallel_spoke_at_free_sector {S : Type*} [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] (hS : IsClosedSurface S)
    {Γ K : Drawing S} (hrad : PreRad (.drawing Γ) K)
    (hmax : RadMax (.drawing Γ) K) (hE : Γ.E.Nonempty)
    {γ : Set S → I → S} {v : S} (hv : v ∈ Γ.V)
    {next : halfEdges Γ γ v → halfEdges Γ γ v}
    {ρ P Q : halfEdges Γ γ v → Set S} {W : Set S}
    {τ : halfEdges Γ γ v → I}
    (hsec : IsSectors Γ γ v next ρ P W Q τ) (k : halfEdges Γ γ v)
    {c : S} (hc : c ∈ ρ k) (hcV : c ∈ K.V)
    {O : Set S} (hO : IsOpen O) (hvO : v ∈ O)
    (hfree : Disjoint ((O ∩ Q k) \ Γ.U) K.U) :
    ∃ (e : Set S), e ∈ K.E ∧ closure e ∩ K.V = {v, c} ∧
      ∃ u : I → S, Continuous u ∧ Function.Injective u ∧ u 0 = v ∧ u 1 = c ∧
        (∀ t, t ≠ 0 → t ≠ 1 → u t ∈ ρ k) ∧
        (∃ N : Set S, IsOpen N ∧ v ∈ N ∧
          ∀ t, 0 < t → u t ∈ N → u t ∈ Q k \ discBd (Q k)) ∧
        ∃ Δ : Set S, IsClosedDisc Δ ∧ Δ ⊆ ρ k ∪ {v} ∧
          subBd Δ = closure e ∪ range u := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have : Nonempty S := ⟨v⟩
  have hr := hsec.corners.region k
  obtain ⟨g, hg, _, hg0, hgt⟩ := exists_path_into_disc (hsec.disc k) (hsec.bd k)
    (hO.inter hsec.isOpen) ⟨hvO, hsec.mem⟩
  have hgr : ∀ t, 0 < t → g t ∈ ρ k := by
    intro t ht
    obtain ⟨htW, htQ, htbd⟩ := hgt t ht
    exact hsec.sub k (hsec.inside k ⟨⟨htW.2, htQ⟩, htbd⟩)
  have hgoff : ∀ t, 0 < t → g t ∉ (radialUnion hrad).U := by
    intro t ht
    have hΓ : g t ∉ Γ.U := region_subset hr (hgr t ht)
    have hK : g t ∉ K.U := Set.disjoint_left.mp hfree
      ⟨⟨(hgt t ht).1.1, (hgt t ht).2.1⟩, hΓ⟩
    rintro (h | h)
    · exact hΓ h
    · exact hK h
  obtain ⟨p, hp, hgp⟩ := exists_region_of_approach (radialUnion hrad) hg hgoff
  obtain ⟨r, hr', hpr⟩ := exists_region_of_sub hrad hp
  have hrr : r = ρ k := region_eq_of_mem hr' hr (hpr (hgp 1 one_pos)) (hgr 1 one_pos)
  have hpr' : p ⊆ ρ k := hrr ▸ hpr
  have hcp : c ∈ closure p := hub_mem_closure hrad hS hr hp hpr' hc hcV
  obtain ⟨η, hη⟩ := exists_edgePar (radialUnion hrad)
  have hcH : c ∈ (radialUnion hrad).V := by rw [radialUnion_V]; exact hcV
  obtain ⟨g₂, hg₂, hg₂0, hg₂p⟩ := exists_access hS (radialUnion hrad) hη hcH
    (exists_half_at_hub hrad hS hmax hE hη hr hc hcV) hp hcp
  have hvnot : v ∉ ρ k := fun h => region_subset hr h (Γ.V_subset_U hv)
  have hvc : v ≠ c := fun h => hvnot (h.symm ▸ hc)
  obtain ⟨y, hy⟩ := region_nonempty hp
  have hppath : IsPathConnected p :=
    isPathConnected_of_isOpen hS (region_isOpen hp) (region_isPreconnected hp) ⟨y, hy⟩
  obtain ⟨u, hu, hui, hu0, hu1, hup, N, hN, hvN, hNg⟩ :=
    exists_chord hppath hvc (fun h => hvnot (hpr' h)) hg hg₂ hg0 hg₂0 hgp hg₂p
  have hline : IsLineWithEnds (range u) c v := by
    have h := isLine_range hu hui
    rw [hu0, hu1] at h
    exact GraphMinor.GM11.IsLineWithEnds.symm h
  have hsubp : range u \ {c, v} ⊆ p := by
    rintro _ ⟨⟨t, rfl⟩, ht⟩
    exact hup t (fun h => ht (Or.inr (by rw [h, hu0]; rfl)))
      (fun h => ht (Or.inl (by rw [h, hu1])))
  have hKU : Disjoint (range u \ {c, v}) K.U := Set.disjoint_left.mpr fun x hx hxK =>
    region_subset hp (hsubp hx) (Or.inr hxK)
  obtain ⟨e, he, hcap, Δ, hΔ, hΔr, hbd⟩ :=
    parallel_of_line hrad hmax hS hr hc hcV hv hline hvc.symm (hsubp.trans hpr') hKU
  refine ⟨e, he, hcap, u, hu, hui, hu0, hu1, fun t ht0 ht1 => hpr' (hup t ht0 ht1),
    ⟨N, hN, hvN, ?_⟩, Δ, hΔ, hΔr, hbd⟩
  intro t ht htN
  obtain ⟨s, hs⟩ := hNg t htN
  have hs0 : 0 < s := by
    apply unitInterval.pos_iff_ne_zero.mpr
    intro hs0
    have hut : u t = u 0 := by rw [← hs, hs0, hg0, hu0]
    exact ht.ne' (hui hut)
  exact hs ▸ ⟨(hgt s hs0).2.1, (hgt s hs0).2.2⟩

end GraphMinor.GM12
