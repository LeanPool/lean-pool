/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2ApproachShrink
public import LeanPool.GraphMinor.GM12.Section2FreeSectorChord
public import LeanPool.GraphMinor.GM12.Section2EntryWitness
import LeanPool.GraphMinor.GM12.Section2SpokePaths

/-!
# Existence of an entering spoke in a fixed sector

This proves the geometric existence step of the omitted entry assertion
on XII page 243 for a specified sector of the original drawing. If a
radial half-edge enters the sector, use its full spoke path. Otherwise
construct a chord in the radial-free sector and replace it by its
parallel spoke across the disc supplied by radial maximality.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 unitInterval

/-- A spoke parametrization retains its injectivity and exact edge image
when read in the region with its vertex added. -/
private theorem lift_spoke_comparison {S : Type*} [TopologicalSpace S]
    {r e : Set S} {v c : S} (hc : c ∈ r)
    {x : (r ∪ {v} : Set S)}
    (F : Path x (⟨v, Or.inr rfl⟩ : (r ∪ {v} : Set S)))
    (β : Path v c) (hβi : Function.Injective β)
    (hβe : β '' Ioo (0 : I) 1 = e) (hβr : ∀ t, 0 < t → β t ∈ r) :
    ∃ q : Path (F 1) (⟨c, Or.inl hc⟩ : (r ∪ {v} : Set S)),
      (∀ t, (q t).val = β t) ∧ Function.Injective (fun t => (q t).val) ∧
        (fun t => (q t).val) '' Ioo (0 : I) 1 = e := by
  obtain ⟨q₀, hq₀⟩ := exists_path_in_region_vertex hc β hβr
  let q := q₀.cast F.target rfl
  have hq : ∀ t, (q t).val = β t := hq₀
  refine ⟨q, hq, ?_, ?_⟩
  · intro s t h
    change (q s).val = (q t).val at h
    rw [hq, hq] at h
    exact hβi h
  · have heq : (fun t => (q t).val) = β := funext hq
    rw [heq]
    exact hβe

/-- Existence of an entering spoke for an approach in a fixed sector.
This is the existence part of the omitted lemma in the trace definition
of XII, page 243, with the sector data made explicit. -/
theorem exists_entry_comparison_in_sector {S : Type*} [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] (hS : IsClosedSurface S)
    {Γ K : Drawing S} (hrad : PreRad (.drawing Γ) K)
    (hmax : RadMax (.drawing Γ) K) (hE : Γ.E.Nonempty)
    {γ : Set S → I → S} {v : S} (hv : v ∈ Γ.V)
    {next : halfEdges Γ γ v → halfEdges Γ γ v}
    {ρ P Q : halfEdges Γ γ v → Set S} {W : Set S}
    {τ : halfEdges Γ γ v → I}
    (hsec : IsSectors Γ γ v next ρ P W Q τ)
    (hcover : W \ Γ.U ⊆ ⋃ k, Q k) (k : halfEdges Γ γ v)
    {c : S} (hc : c ∈ ρ k) (hcV : c ∈ K.V)
    {x : (ρ k ∪ {v} : Set S)}
    (F : Path x (⟨v, Or.inr rfl⟩ : (ρ k ∪ {v} : Set S)))
    (hF : ∀ t, t < 1 → (F t).val ∈ ρ k ∩ (Q k \ discBd (Q k))) :
    ∃ e ∈ K.E,
      ∃ q : Path (F 1) (⟨c, Or.inl hc⟩ : (ρ k ∪ {v} : Set S)),
        Function.Injective (fun t => (q t).val) ∧
        (fun t => (q t).val) '' Ioo (0 : I) 1 = e ∧
        ∃ t : I, t < 1 ∧ ∃ ρpath : Path (F t) (⟨c, Or.inl hc⟩ : (ρ k ∪ {v} : Set S)),
          (∀ s, (ρpath s).val ∈ ρ k) ∧ ((F.subpath t 1).trans q).Homotopic ρpath := by
  have : Nonempty S := ⟨v⟩
  obtain ⟨η, hη⟩ := exists_edgePar K
  have hr := hsec.corners.region k
  have hvr : v ∉ ρ k := fun h => region_subset hr h (Γ.V_subset_U hv)
  have hvc : v ≠ c := fun h => hvr (h.symm ▸ hc)
  have hregion : (Q k \ discBd (Q k)) ∩ W ⊆ ρ k := by
    rintro z ⟨⟨hzQ, hzbd⟩, hzW⟩
    exact hsec.sub k (hsec.inside k ⟨⟨hzW, hzQ⟩, hzbd⟩)
  have hoff : ∀ i : halfEdges K η v, ∀ t : I, 0 < t → spoke η i.val t ∉ Γ.U := by
    intro i t ht hΓ
    have he : spoke η i.val t ∈ i.val.1 := spoke_mem_edge hη i.property.1 ht
    have hKV : spoke η i.val t ∈ K.V := radial_V hrad
      (radial_inter hrad ▸ ⟨hΓ, K.closure_subset_U i.property.1 (subset_closure he)⟩)
    exact edge_notMem_V i.property.1 he hKV
  rcases sector_spoke_or_free_neighbourhood hη hv (radial_V hrad hv) hsec hcover hoff k with
    ⟨i, ε, hε, hεQ⟩ | ⟨O, hO, hvO, hfree⟩
  · have hgi : Continuous (spoke η i.val) :=
      (hη.cont i.val.1 i.property.1).comp (continuous_halfPar i.val.2)
    have hgi0 : spoke η i.val 0 = v := by rw [spoke_zero]; exact i.property.2
    obtain ⟨δ, hδ, hδε, hδW⟩ := exists_pos_le hgi hsec.isOpen
      (hgi0.symm ▸ hsec.mem) hε
    have hδr : spoke η i.val δ ∈ ρ k := hregion ⟨hεQ δ hδ hδε, hδW δ le_rfl⟩
    have hcap := spoke_ends_of_halfEdge_point hS hrad hη hv i hr hc hcV hδ hδr
    obtain ⟨β, hβi, hβrange, hβe, hβhalf⟩ :=
      exists_spoke_path_from_halfEdge hη i hvc hcV hcap
    have hce : c ∈ closure i.val.1 := by
      have hm : c ∈ closure i.val.1 ∩ K.V := hcap.symm ▸ (Or.inr rfl)
      exact hm.1
    have hβr := path_positive_in_region β hc hβe
      (spoke_subset_region hS hrad hr i.property.1 hc hcV hce)
    have hgerm : ∃ ζ : I, 0 < ζ ∧ ∀ t, 0 < t → t ≤ ζ → β t ∈ Q k \ discBd (Q k) := by
      refine ⟨halfT ε, halfT_pos hε, ?_⟩
      intro t ht htε
      obtain ⟨s, hsε, hst⟩ := exists_halfT_eq htε
      have hs : 0 < s := by
        apply unitInterval.pos_iff_ne_zero.mpr
        intro hs0
        have ht0 : t = 0 := by
          rw [hs0] at hst
          have hz : halfT 0 = 0 := Subtype.ext (by simp [halfT])
          exact hst.symm.trans hz
        exact ht.ne' ht0
      rw [← hst, ← hβhalf]
      exact hεQ s hs hsε
    obtain ⟨q, hq, t, ht, ρpath, hρpath, hhom⟩ := entry_comparison_from_surface_germ hc F β
      (hsec.disc k) (hsec.bd k) hsec.isOpen hsec.mem hregion hvr hF hβr hgerm
    refine ⟨i.val.1, i.property.1, q, ?_, ?_, t, ht, ρpath, hρpath, hhom⟩
    · intro s t h
      change (q s).val = (q t).val at h
      rw [hq, hq] at h
      exact hβi h
    · rw [show (fun t => (q t).val) = β from funext hq]
      exact hβe
  · obtain ⟨e, he, hcap, u, hu, hui, hu0, hu1, hur, ⟨N, hN, hvN, hNgerm⟩, Δ, hΔ, hΔr, hbd⟩ :=
      exists_parallel_spoke_at_free_sector hS hrad hmax hE hv hsec k hc hcV hO hvO hfree
    let β : Path v c := ⟨⟨u, hu⟩, hu0, hu1⟩
    have hβr : ∀ t, 0 < t → β t ∈ ρ k := by
      intro t ht
      by_cases ht1 : t = 1
      · rw [ht1, β.target]; exact hc
      · exact hur t ht.ne' ht1
    obtain ⟨ε, hε, _, hεN⟩ := exists_pos_le hu hN (hu0.symm ▸ hvN) (a := 1) one_pos
    have hgerm : ∃ ζ : I, 0 < ζ ∧ ∀ t, 0 < t → t ≤ ζ → β t ∈ Q k \ discBd (Q k) :=
      ⟨ε, hε, fun t ht htε => hNgerm t ht (hεN t htε)⟩
    obtain ⟨q, hq, t, ht, ρpath, hρpath, hhom⟩ := entry_comparison_from_surface_germ hc F β
      (hsec.disc k) (hsec.bd k) hsec.isOpen hsec.mem hregion hvr hF hβr hgerm
    obtain ⟨b, hb⟩ := exists_end_eq hη he (radial_V hrad hv) (by
      have hm : v ∈ closure e ∩ K.V := hcap.symm ▸ (Or.inl rfl)
      exact hm.1)
    let i : halfEdges K η v := ⟨(e, b), he, hb⟩
    obtain ⟨β', hβ'i, hβ'range, hβ'e, _⟩ := exists_spoke_path_from_halfEdge hη i hvc hcV hcap
    have hce : c ∈ closure e := by
      have hm : c ∈ closure e ∩ K.V := hcap.symm ▸ (Or.inr rfl)
      exact hm.1
    have hβ'r := path_positive_in_region β' hc hβ'e (spoke_subset_region hS hrad hr he hc hcV hce)
    obtain ⟨q', hq', hq'i, hq'e⟩ := lift_spoke_comparison hc F β' hβ'i hβ'e hβ'r
    have hΔsub : closure e ∪ range u ⊆ Δ := by
      rw [← hbd]
      rw [subBd_eq_frontier]
      exact frontier_subset_iff_isClosed.mpr hΔ.isClosed
    have hqΔ : ∀ s, (q s).val ∈ Δ := fun s => hΔsub (Or.inr (hq s ▸ mem_range_self s))
    have hq'Δ : ∀ s, (q' s).val ∈ Δ := by
      intro s
      apply hΔsub
      left
      rw [hq' s]
      exact hβ'range ▸ mem_range_self s
    have hfinal := entry_comparison_replace_in_disc hΔ hΔr (F.subpath t 1) q q' ρpath hqΔ hq'Δ hhom
    exact ⟨e, he, q', hq'i, hq'e, t, ht, ρpath, hρpath, hfinal⟩

end GraphMinor.GM12
