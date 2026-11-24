/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Section7
public import LeanPool.GraphMinor.GM11.EdgeSides
public import LeanPool.GraphMinor.GM11.Regions
public import LeanPool.GraphMinor.GM11.Section4c
public import LeanPool.GraphMinor.Surface.InvarianceOfDomain
public import LeanPool.GraphMinor.Surface.DiscArcs

/-!
# The frontier of a `Γ`-nice set

A `Γ`-nice set is a union of vertices, edges and regions of `Γ`, and so an edge or a region lies
inside it
or misses it. `frontier_interSet` says that the frontier of a closed `Γ`-nice set is the point set
of the
drawing `Γ ∩ bd(X)`.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] {Γ : Drawing S} {X : Set S}

omit [T2Space S] in
/-- An atom of `Γ` lies inside a `Γ`-nice set or misses it. -/
theorem nice_atom (hX : IsGammaNice Γ X) {a : Set S} (ha : a ∈ Γ.A) (hne :
  (a ∩ X).Nonempty) : a ⊆ X := by
  obtain ⟨𝒜, h𝒜, rfl⟩ := hX
  obtain ⟨z, hza, hzX⟩ := hne
  obtain ⟨b, hb, hzb⟩ := mem_sUnion.mp hzX
  have hab : a = b := by
    have hdis : ∀ {c d : Set S}, c ∈ Γ.A → d ∈ Γ.A → z ∈ c → z ∈ d → c = d := by
      rintro c d ((⟨v, hv, rfl⟩ | hc) | hc) ((⟨w, hw, rfl⟩ | hd) | hd) hzc hzd
      · have h₁ : z = v := hzc
        have h₂ : z = w := hzd
        subst h₁
        subst h₂
        rfl
      · exact ((hd.2.1 hzd).2 (mem_singleton_iff.mp hzc ▸ hv)).elim
      · exact (region_subset hd hzd (Γ.V_subset_U (mem_singleton_iff.mp hzc ▸ hv))).elim
      · exact ((hc.2.1 hzc).2 (mem_singleton_iff.mp hzd ▸ hw)).elim
      · exact Γ.edge_eq_of_mem hc hd hzc hzd
      · exact (region_subset hd hzd (hc.2.1 hzc).1).elim
      · exact (region_subset hc hzc (Γ.V_subset_U (mem_singleton_iff.mp hzd ▸ hw))).elim
      · exact (region_subset hc hzc (hd.2.1 hzd).1).elim
      · exact region_eq_of_mem hc hd hzc hzd
    exact hdis ha (h𝒜 hb) hza hzb
  subst hab
  exact fun x hx => mem_sUnion.mpr ⟨a, hb, hx⟩

omit [T2Space S] in
theorem nice_edge (hX : IsGammaNice Γ X) {e : Set S} (he : e ∈ Γ.E) (hne :
  (e ∩ X).Nonempty) : e ⊆ X :=
  nice_atom hX (Or.inl (Or.inr he)) hne

omit [T2Space S] in
theorem nice_region (hX : IsGammaNice Γ X) {r : Set S} (hr : r ∈ Γ.R) (hne :
  (r ∩ X).Nonempty) : r ⊆ X :=
  nice_atom hX (Or.inr hr) hne

/-- An edge in a closed `Γ`-nice set with a point on its frontier lies on its frontier. -/
theorem edge_subset_frontier (hS : IsClosedSurface S) (hXc : IsClosed X)
    (hXn : IsGammaNice Γ X) {e : Set S} (he : e ∈ Γ.E) {y : S} (hye : y ∈ e)
      (hy : y ∈ frontier X) : e ⊆ frontier X := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨W, A₁, A₂, hW, hyW, -, hcov, c₁, c₂, d₁, d₂, h₁, h₂⟩ :=
    exists_edge_sides hS Γ he hye
  have hyc : y ∈ closure Xᶜ := by
    rw [closure_compl]
    exact hy.2
  have hyX : y ∈ closure X := hy.1
  obtain ⟨w, hwW, hwc⟩ := mem_closure_iff.mp hyc W hW hyW
  obtain ⟨z, ⟨hzW, hzc⟩, hzU⟩ := exists_notMem_U (Γ := Γ) hS
    (hW.inter hXc.isOpen_compl) ⟨w, hwW, hwc⟩
  obtain ⟨p, hp, hzp⟩ := exists_region_of_notMem hzU
  have hpX : p ⊆ Xᶜ := fun x hx hxX => hzc (nice_region hXn hp ⟨x, hx, hxX⟩ hzp)
  have hinc : (e ∩ closure p).Nonempty := by
    have hmem : z ∈ W \ Γ.U := ⟨hzW, hzU⟩
    rcases hcov hmem with h | h
    · exact ⟨y, hye, closure_mono (subset_region hp c₁ d₁ h hzp) (h₁ ⟨hye, hyW⟩)⟩
    · exact ⟨y, hye, closure_mono (subset_region hp c₂ d₂ h hzp) (h₂ ⟨hye, hyW⟩)⟩
  have hecl := edge_subset_closure_of_incident hS he hp hinc
  have heX : e ⊆ X := nice_edge hXn he ⟨y, hye, hXc.frontier_subset hy⟩
  intro x hx
  refine ⟨subset_closure (heX hx), ?_⟩
  have := closure_mono hpX (hecl hx)
  rwa [closure_compl] at this

/-- **The frontier of a closed `Γ`-nice set** is the point set of `Γ ∩ bd(X)`. -/
theorem frontier_interSet (hS : IsClosedSurface S) (hXc : IsClosed X)
    (hXn : IsGammaNice Γ X) : (Γ.interSet (frontier X)).U = frontier X := by
  have hlc : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hsE : Γ.interSet (frontier X) = Γ.span (Γ.V ∩ frontier X) {e | e ∈ Γ.E ∧ e ⊆ frontier X}
    := rfl
  have hEs : ∀ e, e ∈ (Γ.interSet (frontier X)).E ↔ e ∈ Γ.E ∧ e ⊆ frontier X := by
    intro e
    rw [hsE, Γ.span_E]
    exact ⟨fun h => h.1, fun h => ⟨h, h.1⟩⟩
  have hfc : IsClosed (frontier X) := isClosed_frontier
  apply subset_antisymm
  · rw [Drawing.U_eq]
    rintro x (hx | hx)
    · rcases hx with ⟨⟨-, hx⟩, -⟩ | hx
      · exact hx
      · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
        exact closure_minimal he.1.2 hfc hxe.1
    · obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hx
      exact closure_minimal ((hEs e).mp he).2 hfc hxe
  · intro y hy
    have hyX : y ∈ X := hXc.frontier_subset hy
    by_cases hyU : y ∈ Γ.U
    · by_cases hyV : y ∈ Γ.V
      · exact (Γ.interSet (frontier X)).V_subset_U (by
          rw [hsE]
          exact Or.inl ⟨⟨hyV, hy⟩, hyV⟩)
      · rw [Γ.U_eq] at hyU
        obtain ⟨e, he, hye⟩ := mem_iUnion₂.mp (hyU.resolve_left hyV)
        have hyee : y ∈ e := (Γ.closure_diff_V he).subset ⟨hye, hyV⟩
        have hsub := edge_subset_frontier hS hXc hXn he hyee hy
        exact (Γ.interSet (frontier X)).closure_subset_U ((hEs e).mpr ⟨he, hsub⟩) hye
    · obtain ⟨p, hp, hyp⟩ := exists_region_of_notMem hyU
      have hpX := nice_region hXn hp ⟨y, hyp, hyX⟩
      exact (hy.2 (interior_maximal hpX (region_isOpen hp) hyp)).elim

end GraphMinor.GM11
