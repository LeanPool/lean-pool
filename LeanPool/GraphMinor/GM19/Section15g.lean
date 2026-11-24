/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section15f
public import LeanPool.GraphMinor.GM19.SkeletonTangle
public import LeanPool.GraphMinor.GM17.Bridge

/-!
# Graph Minors XIX, (15.2): the tangle in `sk(Γ)`

The proof of (15.2) passes from `𝒯` to a tangle `𝒯'` in `sk(Γ)` by (14.1) of Graph Minors XVII. The
paper's `sk(Γ)` has an edge
between any two ends of an edge of `Γ`, and we check this for the boundary of a disc
(`exists_skEdge_of_mem_tilde`). The result used
later is `TangleDatum.isTangle_skTangle`.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10 GraphMinor.GM17 Hypergraph

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}

/-- A circuit with three vertices has an edge between any two of them. -/
theorem exists_edge_of_three_vertices {T : Type} [TopologicalSpace T] {C : Drawing T}
  (hC : C.IsCircuit) (h3 : C.V.ncard = 3) {x y : T} (hx : x ∈ C.V) (hy : y ∈ C.V) (hxy : x ≠ y) :
    ∃ e ∈ C.E, x ∈ closure e ∧ y ∈ closure e := by
  classical
  obtain ⟨u, W, ⟨hnd, hed⟩, hpos, hV, hE⟩ := hC
  have hlink : ∀ {e a b}, C.toGraph.IsLink e a b → e ∈ {e | e ∈ W.edges} → ∃ e ∈ C.E, a ∈ closure e
    ∧ b ∈ closure e := fun {e a b} h he ↦ by
    have hc := h.2.2.2
    have ha : a ∈ closure e ∩ C.V := hc ▸ mem_insert a _
    have hb : b ∈ closure e ∩ C.V := hc ▸ mem_insert_of_mem a rfl
    exact ⟨e, hE ▸ he, ha.1, hb.1⟩
  cases W with
  | nil hv => simp [GraphWalk.length, GraphWalk.edges] at hpos
  | @cons _ a _ e₁ h₁ r₁ =>
    cases r₁ with
    | nil hv =>
      have : C.V = {u} := by
        rw [hV]
        ext z
        simp [GraphWalk.support]
      rw [this, ncard_singleton] at h3
      omega
    | @cons _ b _ e₂ h₂ r₂ =>
      cases r₂ with
      | nil hv =>
        have hsub : C.V ⊆ {u, a} := by
          rw [hV]
          intro z hz
          have hz' : z = u ∨ z = a ∨ z = u := by simpa [GraphWalk.support] using hz
          rcases hz' with rfl | rfl | rfl <;> simp
        have := ncard_le_ncard hsub ((finite_singleton a).insert u)
        have h2 := ncard_insert_le u ({a} : Set T)
        rw [ncard_singleton] at h2
        omega
      | @cons _ c _ e₃ h₃ r₃ =>
        cases r₃ with
        | nil hv =>
          have hmem : ∀ z ∈ C.V, z = u ∨ z = a ∨ z = b := fun z hz ↦ by
            rw [hV] at hz
            have hz' : z = u ∨ z = a ∨ z = b ∨ z = u := by simpa [GraphWalk.support] using hz
            rcases hz' with rfl | rfl | rfl | rfl <;> simp
          have l₁ := hlink h₁ (by simp [GraphWalk.edges])
          have l₂ := hlink h₂ (by simp [GraphWalk.edges])
          have l₃ := hlink h₃ (by simp [GraphWalk.edges])
          have sw : ∀ {p q : T}, (∃ e ∈ C.E, p ∈ closure e ∧ q ∈ closure e)
            → ∃ e ∈ C.E, q ∈ closure e ∧ p ∈ closure e := fun ⟨e, he, h, h'⟩ ↦ ⟨e, he, h', h⟩
          rcases hmem x hx with rfl | rfl | rfl <;> rcases hmem y hy with rfl | rfl | rfl
          · exact absurd rfl hxy
          · exact l₁
          · exact sw l₃
          · exact sw l₁
          · exact absurd rfl hxy
          · exact l₂
          · exact l₃
          · exact sw l₂
          · exact absurd rfl hxy
        | @cons _ d _ e₄ h₄ r₄ =>
          exfalso
          have hne : ∃ d' rest, GraphWalk.support r₄ = d' :: rest := by
            cases r₄ <;> exact ⟨_, _, rfl⟩
          obtain ⟨d', rest, hr⟩ := hne
          have hnd' : [a, b, c, d'].Nodup := by
            have : (a :: b :: c :: d' :: rest).Nodup := by simpa [GraphWalk.support, hr] using hnd
            exact this.sublist (by simp)
          have hsub : (([a, b, c, d'].toFinset : Finset T) : Set T) ⊆ C.V := by
            rw [hV]
            intro z hz
            have hz' : z = a ∨ z = b ∨ z = c ∨ z = d' := by simpa using hz
            have : z ∈ a :: b :: c :: d' :: rest := by
              rcases hz' with rfl | rfl | rfl | rfl <;> simp
            simpa [GraphWalk.support, hr] using Or.inr this
          have := ncard_le_ncard hsub (Set.finite_of_ncard_ne_zero (by omega))
          rw [ncard_coe_finset, List.toFinset_card_of_nodup hnd'] at this
          simp at this
          omega

/-- Two ends of an edge of size 3 are joined by an edge of `sk(Γ)` on the boundary of the disc. -/
theorem Painting.exists_skEdge_of_mem_tilde [ConnectedSpace S] (Γ : Painting S) {c : Set S}
  (hc : c ∈ Γ.E) {x y : S} (hx : x ∈ tilde c) (hy : y ∈ tilde c) (hxy : x ≠ y) :
    ∃ f ∈ arcComponentsIn (Γ.skU \ Γ.V), x ∈ closure f ∧ y ∈ closure f := by
  rcases Γ.size_cases hc with h2 | h3
  · exact ⟨c, Γ.two_mem_sk hc h2, hx.1, hy.1⟩
  obtain ⟨hD, hbd, hfin⟩ := Γ.isDisc_of_three hc h3
  obtain ⟨D₀, hU, hV⟩ := Γ.exists_skDrawing
  have hsub : discBd (closure c) ⊆ D₀.U := fun z hz ↦ by
    rw [hU]
    exact Or.inr (mem_iUnion₂.mpr ⟨c, ⟨hc, h3⟩, hz⟩)
  obtain ⟨C, hC, hCs, hCU⟩ := exists_circuit_of_oArc hD.isOArc_discBd hsub
  have hmem : ∀ z ∈ tilde c, z ∈ C.V := fun z hz ↦
    mem_V_of_mem_U_sub hCs (hCU ▸ hbd hz) (hV ▸ Γ.tilde_subset_V hc hz)
  have hCV : C.V = tilde c := by
    refine Subset.antisymm (fun z hz ↦ ?_) hmem
    have hzF : z ∈ discBd (closure c) := hCU ▸ C.V_subset_U hz
    have hzV : z ∈ Γ.V := hV ▸ hCs.1 hz
    exact ⟨Surface.discBd_subset _ hzF, fun h ↦ Γ.disjoint_V hc h hzV⟩
  obtain ⟨e, he, hxe, hye⟩ :=
    exists_edge_of_three_vertices hC (by rwa [hCV]) (hmem x hx) (hmem y hy) hxy
  have he' : e ∈ D₀.E := hCs.2 he
  refine ⟨e, ?_, hxe, hye⟩
  rw [← hU, ← hV]
  exact he'

omit [T2Space Shat] in
/-- The adjacency of the skeleton of `Γ` is witnessed by an edge of `sk(Γ)` in `Σ̂`. -/
theorem IsSkHat.exists_edge_of_adj [ConnectedSpace S] (hS : IsSurface S) {Γ : Painting S} {H :
  Drawing Shat} (h : IsSkHat cap Γ H) (x y : S) (hadj : Γ.toHypergraph.skeleton.Adj x y) :
    ∃ f ∈ H.toHypergraph.edgeSet, H.toHypergraph.Inc f (cap.emb x) ∧ H.toHypergraph.Inc f
      (cap.emb y) := by
  obtain ⟨hne, e, hx, hy⟩ := hadj
  obtain ⟨he, hxV, hxt⟩ := hx
  obtain ⟨-, hyV, hyt⟩ := hy
  obtain ⟨f, hf, hxf, hyf⟩ := Γ.exists_skEdge_of_mem_tilde he hxt hyt hne
  have hg : cap.emb '' f ∈ H.E := (h.edge_iff hS).mpr ⟨f, hf, rfl⟩
  have hcl : closure (cap.emb '' f) = cap.emb '' closure f := ((cap.isClosedEmbedding
    hS).closure_image_eq f).symm ▸ rfl
  refine ⟨_, hg, ⟨hg, ?_, ?_⟩, hg, ?_, ?_⟩
  · rw [h.hV]
    exact mem_image_of_mem _ hxV
  · rw [hcl]
    exact mem_image_of_mem _ hxf
  · rw [h.hV]
    exact mem_image_of_mem _ hyV
  · rw [hcl]
    exact mem_image_of_mem _ hyf

namespace TangleDatum

/-- The tangle `𝒯'` of the proof of (15.2), with separations of order `< m`. -/
def skTangle (D : TangleDatum cap χ) (H : Drawing Shat) (m : ℕ) : Set (Hypergraph Shat
  (Set Shat) × Hypergraph Shat (Set Shat)) :=
  skeletonTangle cap.emb H.toHypergraph D.𝒯 m

omit [T2Space Shat] in
/-- **`𝒯'` is a tangle in `sk(Γ)`**, by (14.1) of Graph Minors XVII. -/
theorem isTangle_skTangle (D : TangleDatum cap χ) {H : Drawing Shat} (hH : IsSkHat cap D.P.Γ H) {m
  : ℕ} (hm : 1 ≤ m) (h3 : 3 * m < 2 * D.ord + 3) : IsTangle H.toHypergraph m (D.skTangle H m) := by
  have : ConnectedSpace S := χ.connected
  refine isTangle_skeletonTangle cap.isEmbedding.injective hH.hV (hH.exists_edge_of_adj
    χ.isSurface) (fun q hq ↦ D.isTangle.isSeparation hq) ?_
  exact gm17Theorem141 S (Set S) D.P.Γ.toHypergraph D.ord m D.𝒯 hm h3 D.isTangle

end TangleDatum

end GraphMinor.GM19
