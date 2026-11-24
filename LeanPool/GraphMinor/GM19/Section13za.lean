/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section13z

/-!
# Graph Minors XIX, Section 13: from chains to walks of `Γ*`

An `(x, y)`-chain of the part of `sk(Γ)` in `Δ` gives a walk of `Γ*`. Each region in the chain costs
two edges of `Γ*`, and this is where the bound of (13.7) comes from.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM06

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

namespace TangleDatum

variable {D : TangleDatum cap χ} {Δ : Set Shat} {Sk : Drawing Shat} {G : Drawing Δ}

/-- Two vertices on the closure of a region of the part of `sk(Γ)` in `Δ` are at most two steps
apart in `Γ*`. -/
theorem IsSkPart.exists_walk (h : D.IsSkPart Δ Sk G) {R : Set Δ} (hR : R ∈ G.R) {z₁ z₂ : Δ}
  (hz₁ : z₁ ∈ G.V) (hz₂ : z₂ ∈ G.V) (c₁ : z₁ ∈ closure R) (c₂ : z₂ ∈ closure R) :
    ∃ K : GraphWalk D.rad.G.toGraph z₁.1 z₂.1, K.length ≤ 2 := by
  have hS := χ.isSurface
  have hΓ := cap.isClosedEmbedding hS
  obtain ⟨q, hq, hRq⟩ := h.exists_region hR
  have hcl : ∀ {z : Δ}, z ∈ closure R → z.1 ∈ closure q := fun hz ↦
    closure_mono hRq (map_mem_closure continuous_subtype_val hz fun x hx ↦ mem_image_of_mem _ hx)
  rcases z₁ with ⟨x₁, hx₁⟩
  rcases z₂ with ⟨x₂, hx₂⟩
  obtain ⟨a, ha, rfl⟩ := (h.mem_V _).mp hz₁
  obtain ⟨b, hb, rfl⟩ := (h.mem_V _).mp hz₂
  have hca := hcl c₁
  have hcb := hcl c₂
  rcases h.sk.region_cases hS hq with hq' | ⟨c, hc, h3, hsub⟩
  · exact D.exists_walk_of_hatRegion hq' ha hb hca hcb
  have hc' : IsClosed (cap.emb '' closure c) := hΓ.isClosedMap _ isClosed_closure
  have hin : ∀ {a : S}, a ∈ D.P.Γ.V → cap.emb a ∈ closure q → a ∈ tilde c := fun ha hcq ↦ by
    obtain ⟨a', ha', hae⟩ := closure_minimal hsub hc' hcq
    have := hΓ.injective hae
    subst this
    exact ⟨ha', fun hn ↦ D.P.Γ.disjoint_V hc hn ha⟩
  by_cases hab : a = b
  · subst hab
    exact ⟨.nil (D.rad.isPreRadial.2.1 (mem_image_of_mem _ ha)), by simp [GraphWalk.length,
      GraphWalk.edges]⟩
  obtain ⟨f, hf, h₁, h₂⟩ := D.P.Γ.exists_side_of_ends hc h3 (hin ha hca) (hin hb hcb) hab
  obtain ⟨r, hr, hfr⟩ := h.sk.exists_hatRegion_side hS hf h3
  have hclf : ∀ {a : S}, a ∈ closure f → cap.emb a ∈ closure r := fun hm ↦
    closure_minimal hfr isClosed_closure (hΓ.closure_image_eq f ▸ mem_image_of_mem _ hm)
  exact D.exists_walk_of_hatRegion hr ha hb (hclf h₁) (hclf h₂)

omit [T2Space S] [T2Space Shat] in
theorem IsSkPart.region_eq (h : D.IsSkPart Δ Sk G) {R : Set Δ} (hR : R ∈ G.R) {x : Δ}
  (hx : x ∈ R) {w : Shat} (hxw : x.1 ∈ D.rad.regionOf w) :
    ∃ q ∈ Sk.R, Subtype.val '' R ⊆ q ∧ q = D.rad.regionOf w := by
  have hS := χ.isSurface
  obtain ⟨q, hq, hRq⟩ := h.exists_region hR
  refine ⟨q, hq, hRq, ?_⟩
  have hxq := hRq (mem_image_of_mem _ hx)
  have hxU : x.1 ∉ D.P.Γ.hatU cap := connectedComponentIn_subset _ _ hxw
  rcases h.sk.region_cases hS hq with ⟨y, hy, rfl⟩ | ⟨c, hc, h3, hsub⟩
  · exact (connectedComponentIn_eq hxq).trans (connectedComponentIn_eq hxw).symm
  · obtain ⟨p, hp, hpe⟩ := hsub hxq
    exact absurd ⟨p, D.P.Γ.closure_subset_U hc hp, hpe⟩ hxU

omit [T2Space Shat] in
/-- A vertex on the closure of a region of the part of `sk(Γ)` is a neighbour of the centre of the
region of `Γ` that holds it. -/
theorem IsSkPart.exists_center_walk (h : D.IsSkPart Δ Sk G) {R : Set Δ} (hR : R ∈ G.R) {x : Δ}
  (hx : x ∈ R) {w : Shat} (hw : w ∈ D.rad.Rstar) (hxw : x.1 ∈ D.rad.regionOf w) {z : Δ}
    (hz : z ∈ G.V) (c : z ∈ closure R) : ∃ K : GraphWalk D.rad.G.toGraph w z.1, K.length ≤ 1 := by
  obtain ⟨q, -, hRq, rfl⟩ := h.region_eq hR hx hxw
  rcases z with ⟨y, hy⟩
  obtain ⟨v, hv, rfl⟩ := (h.mem_V _).mp hz
  have hc : cap.emb v ∈ closure (D.rad.regionOf w) := closure_mono hRq (map_mem_closure (f
    := Subtype.val) continuous_subtype_val c fun x hx ↦ mem_image_of_mem _ hx)
  obtain ⟨e, hl⟩ := D.exists_link_of_closure hw hv hc
  exact ⟨.cons hl (.nil hl.2.2.1), by simp [GraphWalk.length, GraphWalk.edges]⟩

omit [T2Space Shat] in
omit [T2Space S] in
/-- A region of `Γ` has only one centre. -/
theorem center_unique (D : TangleDatum cap χ) {w w' : Shat} (hw : w ∈ D.rad.Rstar)
  (hw' : w' ∈ D.rad.Rstar) (he : D.rad.regionOf w = D.rad.regionOf w') : w = w' := by
  obtain ⟨hr, hm⟩ := D.rad.regionOf_mem hw
  obtain ⟨-, hm'⟩ := D.rad.regionOf_mem hw'
  exact (D.rad.isPreRadial.2.2.1 _ hr).unique ⟨hm, hw.1⟩ ⟨he ▸ hm', hw'.1⟩


/-- How a point `x` sits on a vertex `z` of `Γ*`: it is `z`, a vertex of `Γ`, with `a = 0`, or it
lies in the region of `Γ` with centre `z`, with `a = 1`. -/
def IsCenteredOn (D : TangleDatum cap χ) (x z : Shat) (a : ℕ) : Prop :=
  (a = 0 ∧ x = z ∧ z ∈ D.P.Γ.hatV cap) ∨ (a = 1 ∧ z ∈ D.rad.Rstar ∧ x ∈ D.rad.regionOf z)

omit [T2Space S] [T2Space Shat] in
theorem notMem_hatV_of_region (D : TangleDatum cap χ) {x w : Shat} (hx : x ∈ D.rad.regionOf w) : x
  ∉ D.P.Γ.hatV cap := fun hn ↦
  (connectedComponentIn_subset _ _ hx) (image_mono D.P.Γ.V_subset hn)

theorem chainLength_inl {T : Type} (v : T) (A : List (ChainTerm T)) : chainLength (Sum.inl v :: A)
  = chainLength A + 1 := rfl

theorem chainLength_inr {T : Type} (R : Set T) (A : List (ChainTerm T)) : chainLength
  (Sum.inr R :: A) = chainLength A := rfl

theorem chainLength_nil {T : Type} : chainLength ([] : List (ChainTerm T)) = 0 := rfl

theorem chain_from_vertex (h : D.IsSkPart Δ Sk G) {y : Δ} {z : Shat} {b : ℕ}
  (hy : D.IsCenteredOn y.1 z b) (A : List (ChainTerm Δ)) (v : Δ) (hc : (Sum.inl v :: A).IsChain
    (ChainTerm.AreIncident G))
    (hv : v ∈ G.V) (hl : ChainTerm.MatchesEnd y ((Sum.inl v :: A).getLast (by simp))) :
    ∃ K : GraphWalk D.rad.G.toGraph v.1 z, K.length + 2 ≤ 2 * chainLength (Sum.inl v :: A) + b := by
  induction hn : A.length using Nat.strong_induction_on generalizing A v with
  | _ n ih =>
  cases A with
  | nil =>
    have hvy : v = y := hl
    subst hvy
    rcases hy with ⟨rfl, hm, hz⟩ | ⟨-, -, hm⟩
    · subst hm
      refine ⟨.nil (D.rad.isPreRadial.2.1 hz), ?_⟩
      rw [chainLength_inl, chainLength_nil]
      simp [GraphWalk.length, GraphWalk.edges]
    · exact absurd ((h.mem_V _).mp hv) (D.notMem_hatV_of_region hm)
  | cons t A =>
    cases t with
    | inl u =>
      rw [List.isChain_cons_cons] at hc
      exact hc.1.elim
    | inr R =>
      rw [List.isChain_cons_cons] at hc
      obtain ⟨⟨-, hR, hvR⟩, hc'⟩ := hc
      cases A with
      | nil =>
        have hyR : y ∈ R := by simpa [ChainTerm.MatchesEnd] using hl
        rcases hy with ⟨-, hm, hz⟩ | ⟨rfl, hw, hm⟩
        · exfalso
          have hyV : y ∈ G.V := (h.mem_V _).mpr (hm ▸ hz)
          obtain ⟨p, hp, rfl⟩ := (mem_R_iff G).mp hR
          exact (connectedComponentIn_subset _ _ hyR).2 (G.V_subset_U hyV)
        · obtain ⟨K, hK⟩ := h.exists_center_walk hR hyR hw hm hv hvR
          refine ⟨K.reverse, ?_⟩
          rw [GraphWalk.length_reverse, chainLength_inl, chainLength_inr, chainLength_nil]
          omega
      | cons t' A' =>
        cases t' with
        | inr R' =>
          rw [List.isChain_cons_cons] at hc'
          exact hc'.1.elim
        | inl u =>
          have hu : u ∈ G.V := by
            rw [List.isChain_cons_cons] at hc'
            exact hc'.1.1
          have huR : u ∈ closure R := by
            rw [List.isChain_cons_cons] at hc'
            exact hc'.1.2.2
          have hc'' := hc'.tail
          have hlt : A'.length < n := by
            simp at hn
            omega
          obtain ⟨K₂, hK₂⟩ := ih A'.length hlt A' u hc'' hu (by simpa using hl) rfl
          obtain ⟨K₁, hK₁⟩ := h.exists_walk hR hv hu hvR huR
          refine ⟨K₁.append K₂, ?_⟩
          rw [GraphWalk.length_append]
          rw [chainLength_inl, chainLength_inr, chainLength_inl]
          rw [chainLength_inl] at hK₂
          omega

/-- An `(x, y)`-chain of the part of `sk(Γ)` in `Δ` gives a walk of `Γ*` between the centres of `x`
and `y`, with two edges for each vertex of the chain, less two, and one more edge at each of
`x, y` that is not a vertex. -/
theorem IsSkPart.chain_walk (h : D.IsSkPart Δ Sk G) {x y : Δ} {z z' : Shat} {a b : ℕ}
  (hx : D.IsCenteredOn x.1 z a) (hy : D.IsCenteredOn y.1 z' b) {A : List (ChainTerm Δ)}
    (hc : IsXYChain G x y A) : ∃ K : GraphWalk D.rad.G.toGraph z z', K.length + 2
      ≤ 2 * chainLength A + a + b := by
  obtain ⟨hne, hval, hch, hh, hl, -⟩ := hc
  cases A with
  | nil => exact absurd rfl hne
  | cons t A =>
    cases t with
    | inl v =>
      have hvx : v = x := by simpa [ChainTerm.MatchesEnd] using hh
      subst hvx
      have hvV : v ∈ G.V := hval _ List.mem_cons_self
      rcases hx with ⟨rfl, hm, hz⟩ | ⟨-, -, hm⟩
      · subst hm
        obtain ⟨K, hK⟩ := chain_from_vertex h hy A v hch hvV hl
        exact ⟨K, by omega⟩
      · exact absurd ((h.mem_V _).mp hvV) (D.notMem_hatV_of_region hm)
    | inr R =>
      have hxR : x ∈ R := by simpa [ChainTerm.MatchesEnd] using hh
      have hRR : R ∈ G.R := hval _ List.mem_cons_self
      have hoff : ∀ {p : Δ}, p ∈ R → p ∉ G.V := fun hp hpV ↦ by
        obtain ⟨y', -, rfl⟩ := (mem_R_iff G).mp hRR
        exact (connectedComponentIn_subset _ _ hp).2 (G.V_subset_U hpV)
      rcases hx with ⟨-, hm, hz⟩ | ⟨rfl, hw, hm⟩
      · exact absurd ((h.mem_V _).mpr (hm ▸ hz)) (hoff hxR)
      cases A with
      | nil =>
        have hyR : y ∈ R := by simpa [ChainTerm.MatchesEnd] using hl
        rcases hy with ⟨-, hm', hz⟩ | ⟨rfl, hw', hm'⟩
        · exact absurd ((h.mem_V _).mpr (hm' ▸ hz)) (hoff hyR)
        · obtain ⟨q, -, hRq, rfl⟩ := h.region_eq hRR hxR hm
          obtain ⟨q', -, hRq', e⟩ := h.region_eq hRR hyR hm'
          have hq : D.rad.regionOf z = D.rad.regionOf z' := by
            have h₁ := hRq (mem_image_of_mem _ hyR)
            exact (connectedComponentIn_eq h₁).trans (connectedComponentIn_eq hm').symm
          have := D.center_unique hw hw' hq
          subst this
          refine ⟨.nil hw.1, ?_⟩
          rw [chainLength_inr, chainLength_nil]
          simp [GraphWalk.length, GraphWalk.edges]
      | cons t A =>
        cases t with
        | inr R' =>
          rw [List.isChain_cons_cons] at hch
          exact hch.1.elim
        | inl v =>
          rw [List.isChain_cons_cons] at hch
          obtain ⟨⟨hv, -, hvR⟩, hch'⟩ := hch
          obtain ⟨K₁, hK₁⟩ := h.exists_center_walk hRR hxR hw hm hv hvR
          obtain ⟨K₂, hK₂⟩ := chain_from_vertex h hy A v hch' hv (by simpa using hl)
          refine ⟨K₁.append K₂, ?_⟩
          rw [GraphWalk.length_append]
          rw [chainLength_inr]
          omega

end TangleDatum

end GraphMinor.GM19
