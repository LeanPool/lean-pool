/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section10m

/-!
# Walks around a distance flaw

Everything on a closed walk of length at most `2n` is close to everything else on it. So, since
`dist(Γ) > ½n + 1`, such a walk
meets one cuff at most.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.GM10

universe w

/-- Two vertices of a closed walk are joined by a part of it of at most half its length. -/
theorem exists_half_walk {α β : Type*} {G : Graph α β} {u x y : α} (Z : GraphWalk G u u)
  (hx : x ∈ Z.support) (hy : y ∈ Z.support) :
    ∃ W : GraphWalk G x y, 2 * W.length ≤ Z.length ∧ (∀ z ∈ W.support, z ∈ Z.support)
      ∧ ∀ e ∈ W.edges, e ∈ Z.edges := by
  obtain ⟨A, B, rfl⟩ := Z.exists_append_of_mem hx
  have hsupp : ∀ z, z ∈ (B.append A).support ↔ z ∈ (A.append B).support := fun z ↦ by
    rw [GraphWalk.mem_support_append, GraphWalk.mem_support_append, or_comm]
  have hed : ∀ e, e ∈ (B.append A).edges ↔ e ∈ (A.append B).edges := fun e ↦ by
    rw [GraphWalk.edges_append, GraphWalk.edges_append, List.mem_append, List.mem_append, or_comm]
  obtain ⟨C, E, hR⟩ := (B.append A).exists_append_of_mem ((hsupp y).2 hy)
  have hlen : (A.append B).length = C.length + E.length := by
    have h₁ := congrArg GraphWalk.length hR
    rw [GraphWalk.length_append, GraphWalk.length_append] at h₁
    rw [GraphWalk.length_append]
    omega
  have hC : (∀ z ∈ C.support, z ∈ (A.append B).support) ∧ ∀ e ∈ C.edges, e ∈ (A.append B).edges
    := by
    refine ⟨fun z hz ↦ (hsupp z).1 ?_, fun e he ↦ (hed e).1 ?_⟩
    · rw [hR]
      exact (GraphWalk.mem_support_append _ _).2 (Or.inl hz)
    · rw [hR, GraphWalk.edges_append]
      exact List.mem_append.2 (Or.inl he)
  have hE : (∀ z ∈ E.support, z ∈ (A.append B).support) ∧ ∀ e ∈ E.edges, e ∈ (A.append B).edges
    := by
    refine ⟨fun z hz ↦ (hsupp z).1 ?_, fun e he ↦ (hed e).1 ?_⟩
    · rw [hR]
      exact (GraphWalk.mem_support_append _ _).2 (Or.inr hz)
    · rw [hR, GraphWalk.edges_append]
      exact List.mem_append.2 (Or.inr he)
  rcases le_total C.length E.length with h | h
  · exact ⟨C, by omega, hC.1, hC.2⟩
  · refine ⟨E.reverse, ?_, fun z hz ↦ hE.1 z ?_, fun e he ↦ hE.2 e ?_⟩
    · rw [GraphWalk.length_reverse]
      omega
    · rw [GraphWalk.support_reverse] at hz
      exact List.mem_reverse.1 hz
    · rw [GraphWalk.edges_reverse] at he
      exact List.mem_reverse.1 he

/-- A simple walk that uses only edges of a walk is no longer than that walk. -/
theorem length_le_of_edges {α β : Type*} {G : Graph α β} {u v u' v' : α} {W : GraphWalk G u v}
    {W' : GraphWalk G u' v'} (hW : W.IsSimple) (h : ∀ e ∈ W.edges, e ∈ W'.edges) : W.length
      ≤ W'.length := by
  classical
  have h₁ : W.edges.toFinset ⊆ W'.edges.toFinset := fun e he ↦ by
    rw [List.mem_toFinset] at he ⊢
    exact h e he
  have h₂ := Finset.card_le_card h₁
  rw [List.toFinset_card_of_nodup hW.edges_nodup] at h₂
  exact h₂.trans (List.toFinset_card_le _)

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {cap : IsCappedSurface S Shat} {β : Type w} {χ : ColourScheme S β}


namespace TangleDatum

variable {D : TangleDatum cap χ}

/-- The drawing of a simple walk has as many edges as the walk is long. -/
theorem ncard_walk_E (G : Drawing Shat) {u v : Shat} {W : GraphWalk G.toGraph u v}
  (hW : W.IsSimple) :
    (walkDrawing G W).E.ncard = W.length := by
  classical
  rw [walkDrawing_E]
  have : {e | e ∈ W.edges} = ↑W.edges.toFinset := by
    ext e
    simp
  rw [this, ncard_coe_finset, List.toFinset_card_of_nodup hW.edges_nodup, GraphWalk.length]

omit [T2Space S] in
/-- A walk between two poles is at least `2 dist(Γ)` long. -/
theorem two_dist_le (D : TangleDatum cap χ) {p₁ p₂ : Shat} (h₁ : p₁ ∈ D.rad.poles)
  (h₂ : p₂ ∈ D.rad.poles) (hne : p₁ ≠ p₂)
    (T : GraphWalk D.rad.G.toGraph p₁ p₂) : 2 * Painting.dist D.rad ≤ (T.length : ℕ∞) := by
  classical
  obtain ⟨T', hTs, -, hTe⟩ := GraphWalk.exists_isSimple T
  have hl := length_le_of_edges hTs hTe
  set R := walkDrawing D.rad.G T' with hR
  have hRp : GM19.Drawing.IsPathOf R D.rad.G p₁ p₂ := ⟨walkDrawing_isSubdrawing _ _,
    walkDrawing_isPathBetween _ hTs⟩
  have hRE : R.E.ncard = T'.length := ncard_walk_E _ hTs
  have hle : Painting.dist D.rad ≤ ((R.E.ncard / 2 : ℕ) : ℕ∞) := sInf_le ⟨R, p₁, p₂, h₁, h₂, hne,
    hRp, rfl⟩
  calc 2 * Painting.dist D.rad ≤ 2 * ((R.E.ncard / 2 : ℕ) : ℕ∞) := by gcongr
    _ = ((2 * (R.E.ncard / 2) : ℕ) : ℕ∞) := by push_cast; rfl
    _ ≤ (T.length : ℕ∞) := by
      have : 2 * (R.E.ncard / 2) ≤ T.length := by omega
      exact_mod_cast this

variable (hS : IsSurface S) (h3 : D.P.Γ.IsInternallyThreeConnected)
include hS h3

/-- A closed walk of length at most `2n` meets one cuff at most, if `dist(Γ) > ½n + 1`. -/
theorem labels_eq {n : ℕ} (hd : ((n + 2 : ℕ) : ℕ∞) < 2 * Painting.dist D.rad) {u : Shat}
  (Z : GraphWalk D.rad.G.toGraph u u)
    (hZ : Z.length ≤ 2 * n) {x y : Shat} (hx : x ∈ Z.support) (hy : y ∈ Z.support) {c d : Set S}
    (hlx : cuffLabel cap x = some c) (hly : cuffLabel cap y = some d) : c = d := by
  classical
  have : ConnectedSpace Shat := cap.connected
  by_contra hcd
  obtain ⟨hc, -⟩ := cuffLabel_some hlx
  obtain ⟨hd', -⟩ := cuffLabel_some hly
  obtain ⟨p₁, hp₁, hm₁, hr₁⟩ := D.rad.exists_pole hS hc
  obtain ⟨p₂, hp₂, hm₂, hr₂⟩ := D.rad.exists_pole hS hd'
  have hpne : p₁ ≠ p₂ := by
    rintro rfl
    exact disjoint_left.1 (cap.cuffDisc_disjoint _ hc _ hd' hcd) (subset_closure hm₁)
      (subset_closure hm₂)
  obtain ⟨W, hW, -, -⟩ := exists_half_walk Z hx hy
  obtain ⟨W₁, hW₁⟩ := exists_walk_to_pole hS D.rad (mem_V_of_mem_support Z hx) hlx hp₁ hr₁ h3
  obtain ⟨W₂, hW₂⟩ := exists_walk_to_pole hS D.rad (mem_V_of_mem_support Z hy) hly hp₂ hr₂ h3
  have hle := D.two_dist_le hp₁ hp₂ hpne ((W₁.append W).append W₂.reverse)
  rw [GraphWalk.length_append, GraphWalk.length_append, GraphWalk.length_reverse] at hle
  have hb : W₁.length + W.length + W₂.length ≤ n + 2 := by omega
  have hb' : ((W₁.length + W.length + W₂.length : ℕ) : ℕ∞) ≤ ((n + 2 : ℕ) : ℕ∞) := by
    exact_mod_cast hb
  exact absurd (hle.trans hb') (not_le.2 hd)

omit h3 in
omit [T2Space S] [T2Space Shat] in
/-- A closed walk with a label on it holds a point of that cuff. -/
theorem exists_touch {u : Shat} (Z : GraphWalk D.rad.G.toGraph u u) (hpos : 0 < Z.length)
    {y : Shat} (hy : y ∈ Z.support) {Θ : Set S}
    (hl : cuffLabel cap y = some Θ) : ∃ v ∈ D.P.Γ.V, v ∈ Θ ∧ cap.emb v ∈ Z.support := by
  by_cases hV : y ∈ D.P.Γ.hatV cap
  · obtain ⟨v, hv, rfl⟩ := hV
    exact ⟨v, hv, (mem_cuff_of_label hS hl).2, hy⟩
  · obtain ⟨hp, hΘ, hreg⟩ := pole_of_label hS D.rad ⟨mem_V_of_mem_support Z hy, hV⟩ hl
    obtain ⟨W, -, hW, -⟩ := exists_half_walk Z hy hy
    obtain ⟨A, B, rfl⟩ := Z.exists_append_of_mem hy
    have hsupp : ∀ z, z ∈ (B.append A).support → z ∈ (A.append B).support := fun z hz ↦ by
      rw [GraphWalk.mem_support_append] at hz ⊢
      exact hz.symm
    have hl' : 0 < (B.append A).length := by
      rw [GraphWalk.length_append] at hpos ⊢
      omega
    generalize hR : B.append A = R at hl' hsupp
    cases R with
    | nil h' => simp [GraphWalk.length, GraphWalk.edges] at hl'
    | @cons _ x _ e h' r =>
      obtain ⟨v, hv, rfl, hset⟩ := D.rad.link_cases h' hp.1
      refine ⟨v, hv, (D.rad.pole_edge hS h'.1 hp hΘ hreg hset).2, hsupp _ ?_⟩
      simp only [GraphWalk.support_cons]
      exact List.mem_cons_of_mem _ r.start_mem_support

end TangleDatum

end GraphMinor.GM19
