/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.RST94.Section4b

/-!
# Section 4 of "Quickly excluding a planar graph": (4.2)

Robertson, Seymour and Thomas, J. Combin. Theory Ser. B 62 (1994), (4.2), pages 337–338, and the
transitivity of residual nodules (page 335).

The paper chooses `Q` and the linkage with `Q ∪ ⋃ 𝒫` minimal. We keep the linkage and choose `Q`
with the fewest edges not on a path of the linkage. What the
proofs of (5.3) use is that `Q` does not leave a path `P` and come back, and this is `NoReturn`.
-/

@[expose] public section

namespace GraphMinor.RST94

open Hypergraph GM10 Set

variable {α β ι : Type*} {G A B : Hypergraph α β} {θ : ℕ} {T : Set (Hypergraph α β × Hypergraph α
  β)}

/-- The paths `P i` form a linkage from `z` to `z'` for `G'` (page 335). -/
abbrev IsLinkage (G G' : Hypergraph α β) (z z' : ι → α) (P : ∀ i, G.skeleton.Walk (z i)
  (z' i)) : Prop :=
  (∀ i, (P i).IsPath) ∧ (∀ i, ∀ x ∈ (P i).support, x ∈ G'.vertexSet → x = z' i) ∧
    Pairwise fun i j => Disjoint {x | x ∈ (P i).support} {x | x ∈ (P j).support}

/-- The walk `w` does not leave `X` and come back: each segment of `w` with both ends in `X` lies in
`X`. This is what the paper's condition that `P ∩ Q` is null or a path
gives, for `X = V(P)`. -/
def NoReturn {K : SimpleGraph α} {s t : α} (X : Set α) (w : K.Walk s t) : Prop :=
  ∀ (a b : α) (w₁ : K.Walk s a) (w₂ : K.Walk a b) (w₃ : K.Walk b t), w = w₁.append (w₂.append w₃)
    → a ∈ X → b ∈ X → ∀ c ∈ w₂.support, c ∈ X

theorem NoReturn.of_cons {K : SimpleGraph α} {X : Set α} {r s t : α} {h : K.Adj r s} {w : K.Walk s
  t} (hw : NoReturn X (SimpleGraph.Walk.cons h w)) :
    NoReturn X w := fun a b w₁ w₂ w₃ he ha hb c hc =>
  hw a b (SimpleGraph.Walk.cons h w₁) w₂ w₃ (by rw [he, SimpleGraph.Walk.cons_append]) ha hb c hc

/-- A walk from `X` to a vertex outside `X` has an edge that leaves `X`. -/
theorem exists_boundary_edge {K : SimpleGraph α} {X : Set α} {a c : α} (w : K.Walk a c)
  (ha : a ∈ X) (hc : c ∉ X) :
    ∃ x y, x ∈ X ∧ y ∉ X ∧ s(x, y) ∈ w.edges := by
  induction w with
  | nil => exact absurd ha hc
  | @cons u v t h p ih =>
    by_cases hv : v ∈ X
    · obtain ⟨x, y, h₁, h₂, h₃⟩ := ih hv hc
      exact ⟨x, y, h₁, h₂, by simp [h₃]⟩
    · exact ⟨u, v, ha, hv, by simp⟩

/-- Rerouting the middle part of a path `Q` along a path `p`: this is the choice of `Q` at the end
of the proof of (4.2) (page 338). The set `F` holds the edges of the linkage. -/
theorem reroute {K : SimpleGraph α} {s t a b f l c : α} (w₁ : K.Walk s a) (w₂ : K.Walk a b)
  (w₃ : K.Walk b t)
    (hQ : (w₁.append (w₂.append w₃)).IsPath) (p : K.Walk f l) (hp : p.IsPath) (ha : a ∈ p.support)
      (hb : b ∈ p.support)
    (hal : a ≠ l) (hbl : b ≠ l) (hc : c ∈ w₂.support) (hcp : c ∉ p.support) {F : Set (Sym2 α)}
      (hpF : ∀ e ∈ p.edges, e ∈ F)
    (hF : ∀ x y, x ∈ p.support → y ∉ p.support → s(x, y) ∉ F) :
    ∃ Q' : K.Walk s t, Q'.IsPath ∧ (∀ v ∈ Q'.support, v ∈ w₁.support ∨ v ∈ w₃.support ∨
      (v ∈ p.support ∧ v ≠ l)) ∧
      (∀ e ∈ Q'.edges, e ∈ F ∨ e ∈ (w₁.append (w₂.append w₃)).edges) ∧
      ∃ e ∈ (w₁.append (w₂.append w₃)).edges, e ∉ F ∧ e ∉ Q'.edges := by
  classical
  let seg := (p.takeUntil a ha).reverse.append (p.takeUntil b hb)
  let Q₀ := (w₁.append seg).append w₃
  have hsegS : ∀ v ∈ seg.support, v ∈ p.support ∧ v ≠ l := by
    intro v hv
    have h₁ : ∀ {y : α} (hy : y ∈ p.support), y ≠ l → v ∈ (p.takeUntil y hy).support
      → v ∈ p.support ∧ v ≠ l := fun hy hne hv' =>
      ⟨p.support_takeUntil_subset_support hy hv', fun e => notMem_takeUntil p hp hy hne (e ▸ hv')⟩
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).1 hv with hv | hv
    · exact h₁ ha hal (by simpa using hv)
    · exact h₁ hb hbl hv
  have hsegE : ∀ e ∈ seg.edges, e ∈ F := by
    intro e he
    rw [SimpleGraph.Walk.edges_append, List.mem_append] at he
    rcases he with he | he
    · rw [SimpleGraph.Walk.edges_reverse, List.mem_reverse] at he
      exact hpF e (p.edges_takeUntil_subset_edges ha he)
    · exact hpF e (p.edges_takeUntil_subset_edges hb he)
  have hQ₀S : ∀ v ∈ Q₀.support, v ∈ w₁.support ∨ v ∈ w₃.support ∨ (v ∈ p.support ∧ v ≠ l) := by
    intro v hv
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).1 hv with hv | hv
    · rcases (SimpleGraph.Walk.mem_support_append_iff _ _).1 hv with hv | hv
      · exact Or.inl hv
      · exact Or.inr (Or.inr (hsegS v hv))
    · exact Or.inr (Or.inl hv)
  have hQ₀E : ∀ e ∈ Q₀.edges, e ∈ w₁.edges ∨ e ∈ F ∨ e ∈ w₃.edges := by
    intro e he
    simp only [Q₀, SimpleGraph.Walk.edges_append, List.mem_append] at he
    rcases he with (he | he) | he
    · exact Or.inl he
    · exact Or.inr (Or.inl (hsegE e (by simpa [SimpleGraph.Walk.edges_append] using he)))
    · exact Or.inr (Or.inr he)
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_boundary_edge (X := {v | v ∈ p.support})
    (w₂.takeUntil c hc) ha hcp
  have hxy₂ : s(x, y) ∈ w₂.edges := w₂.edges_takeUntil_subset_edges hc hxy
  have hnd := hQ.isTrail.edges_nodup
  rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_append, List.nodup_append] at hnd
  have hn₁ : s(x, y) ∉ w₁.edges := fun h => hnd.2.2 _ h _ (List.mem_append_left _ hxy₂) rfl
  have hnd₂ := hnd.2.1
  rw [List.nodup_append] at hnd₂
  have hn₃ : s(x, y) ∉ w₃.edges := fun h => hnd₂.2.2 _ hxy₂ _ h rfl
  refine ⟨Q₀.bypass, Q₀.bypass_isPath, fun v hv => hQ₀S v (Q₀.support_bypass_subset_support hv),
    fun e he => ?_,
    s(x, y), ?_, hF x y hx hy, fun h => ?_⟩
  · rcases hQ₀E e (Q₀.edges_bypass_subset_edges he) with h | h | h
    · exact Or.inr (by simp [SimpleGraph.Walk.edges_append, h])
    · exact Or.inl h
    · exact Or.inr (by simp [SimpleGraph.Walk.edges_append, h])
  · simp [SimpleGraph.Walk.edges_append, hxy₂]
  · rcases hQ₀E _ (Q₀.edges_bypass_subset_edges h) with h' | h' | h'
    · exact hn₁ h'
    · exact hF x y hx hy h'
    · exact hn₃ h'

/-- Residual nodules are transitive (page 335). -/
theorem Residual.trans {z z₁ z₂ : ι → α} {G₁ G₂ : Hypergraph α β} {T₁ T₂ : Set
  (Hypergraph α β × Hypergraph α β)} {θ₁ θ₂ : ℕ}
    (hT : IsTangle G θ T) (h₁ : Residual G T θ z G₁ T₁ θ₁ z₁) (h₂ : Residual G₁ T₁ θ₁ z₁ G₂ T₂ θ₂
      z₂) : Residual G T θ z G₂ T₂ θ₂ z₂ := by
  classical
  obtain ⟨P, hP₁, hP₂, hP₃⟩ := h₁.link
  obtain ⟨Q, hQ₁, hQ₂, hQ₃⟩ := h₂.link
  refine ⟨h₂.nodule, h₂.le.trans h₁.le, fun i hi => h₁.avoid i (h₂.le.vertexSet_subset hi),
    Conformal.trans h₁.le h₂.le hT h₁.nodule.tangle h₂.nodule.tangle h₁.conformal h₂.conformal, ?_⟩
  let R : ∀ i, G.skeleton.Walk (z i) (z₂ i) := fun i => ((P i).append ((Q i).mapLe
    (skeleton_mono h₁.le))).bypass
  have hR : ∀ i t, t ∈ (R i).support → t ∈ (P i).support ∨ t ∈ (Q i).support := fun i t ht => by
    have := ((P i).append ((Q i).mapLe (skeleton_mono h₁.le))).support_bypass_subset_support ht
    rcases (SimpleGraph.Walk.mem_support_append_iff _ _).1 this with h | h
    · exact Or.inl h
    · exact Or.inr (by simpa using h)
  have hPG₁ : ∀ i t, t ∈ (Q i).support → t ∈ G₁.vertexSet := fun i t ht =>
    support_mem (Q i) (h₁.nodule.free.1 (mem_range_self i)) ht
  refine ⟨R, fun i => SimpleGraph.Walk.bypass_isPath _, fun i t ht htG => ?_, fun i j hij
    => disjoint_left.2 fun t ht ht' => ?_⟩
  · rcases hR i t ht with h | h
    · have := hP₂ i t h (h₂.le.vertexSet_subset htG)
      exact absurd (this ▸ htG) (h₂.avoid i)
    · exact hQ₂ i t h htG
  · have hc : ∀ i j, i ≠ j → t ∈ (P i).support → t ∉ (Q j).support := fun i j hij hi hj => by
      have := hP₂ i t hi (hPG₁ j t hj)
      subst this
      exact disjoint_left.1 (hQ₃ hij) (Q i).start_mem_support hj
    rcases hR i t ht with h₁' | h₁' <;> rcases hR j t ht' with h₂' | h₂'
    · exact disjoint_left.1 (hP₃ hij) h₁' h₂'
    · exact hc i j hij h₁' h₂'
    · exact hc j i hij.symm h₂' h₁'
    · exact disjoint_left.1 (hQ₃ hij) h₁' h₂'

/-- **(4.2)** (page 337). `Q` goes from `z i` to `z j`, and the condition on `P ∩ Q` is `NoReturn`.
The paper's bound is for `k ≥ h`. -/
theorem theorem_4_2 [Fintype ι] (hG : G.IsGraph) {z : ι → α} (hN : Nodule G T θ z) {k : ℕ}
  (hh : Fintype.card ι ≤ k)
    (hθ : 18 * (Fintype.card ι + k) + 3 ≤ θ) {i j : ι} (hij : i ≠ j) :
    ∃ (G' : Hypergraph α β) (T' : Set (Hypergraph α β × Hypergraph α β)) (z' : ι → α)
      (P : ∀ i, G.skeleton.Walk (z i) (z' i))
      (Q : G.skeleton.Walk (z i) (z j)), Residual G T θ z G' T' k z' ∧ IsLinkage G G' z z' P
        ∧ Q.IsPath ∧
      (∀ x ∈ Q.support, x ∉ G'.vertexSet) ∧ ∀ l, NoReturn {x | x ∈ (P l).support} Q := by
  classical
  have hcard := Fintype.one_lt_card_iff.2 ⟨i, j, hij⟩
  have hfree2 : IsFreeSet G T θ {z i, z j} := hN.free.subset hN.tangle (by
    rintro x (rfl | rfl) <;> exact mem_range_self _)
  obtain ⟨C, hC, T₁, hT₁, hc⟩ := theorem_3_2 (k := Fintype.card ι + k) hG (by omega) (fun e => hij
    (hN.inj e)) hN.tangle hθ hfree2
  let H := G.deleteVertices {x | x ∈ C.support}
  have hH : H ≤ G := deleteVertices_le _ _
  have hfree0 : IsFreeSet G (inducedTangle G H T₁ (Fintype.card ι + k)) (Fintype.card ι + k)
    (range z) :=
    ⟨hN.free.1, by rw [ncard_range hN.inj]; omega, fun A B hm hX => hN.free.2.2 (hc.2 hm) hX⟩
  obtain ⟨G', T', z', hR₀, hav⟩ := theorem_4_1 _ G hG z hN.inj {x | x ∈ C.support} (conn_support C)
    (fun x hx => support_mem C (hN.free.1 (mem_range_self i)) hx) ⟨i, C.start_mem_support⟩ H _ T₁
      hH (fun x => Iff.rfl)
    (fun f hf hno => ⟨hf, hno⟩) hT₁ (by omega) hfree0 rfl
  rw [Nat.add_sub_cancel_left] at hR₀
  have hR : Residual G T θ z G' T' k z' := {
    nodule := hR₀.nodule
    le := hR₀.le
    avoid := hR₀.avoid
    conformal := ⟨by omega, hR₀.conformal.2.trans hc.2⟩
    link := hR₀.link }
  obtain ⟨P, hP⟩ := hR.link
  obtain ⟨hP₁, hP₂, hP₃⟩ := id hP
  let F : Set (Sym2 α) := {e | ∃ l, e ∈ (P l).edges}
  let μ : G.skeleton.Walk (z i) (z j) → ℕ := fun Q => ({e | e ∈ Q.edges} \ F).ncard
  obtain ⟨Q, ⟨hQ₁, hQ₂⟩, hmin⟩ := exists_min_measure (P := fun Q : G.skeleton.Walk (z i) (z j)
    => Q.IsPath ∧ ∀ x ∈ Q.support, x ∉ G'.vertexSet) μ
    ⟨C, hC, hav⟩
  refine ⟨G', T', z', P, Q, hR, hP, hQ₁, hQ₂, fun l a b w₁ w₂ w₃ he ha hb c hc' => ?_⟩
  by_contra hcX
  have hz' : z' l ∈ G'.vertexSet := hR.nodule.free.1 (mem_range_self l)
  have haQ : a ∈ Q.support := by
    rw [he]
    exact (SimpleGraph.Walk.mem_support_append_iff _ _).2 (Or.inl w₁.end_mem_support)
  have hbQ : b ∈ Q.support := by
    rw [he]
    exact (SimpleGraph.Walk.mem_support_append_iff _ _).2 (Or.inr
      ((SimpleGraph.Walk.mem_support_append_iff _ _).2 (Or.inr w₃.start_mem_support)))
  have hal : a ≠ z' l := fun e => hQ₂ a haQ (e ▸ hz')
  have hbl : b ≠ z' l := fun e => hQ₂ b hbQ (e ▸ hz')
  have hF : ∀ x y, x ∈ (P l).support → y ∉ (P l).support → s(x, y) ∉ F := by
    rintro x y hx hy ⟨m, hm⟩
    by_cases hml : m = l
    · subst hml
      exact hy ((P m).snd_mem_support_of_mem_edges hm)
    · exact disjoint_left.1 (hP₃ hml) ((P m).fst_mem_support_of_mem_edges hm) hx
  have hQ' := hQ₁
  rw [he] at hQ'
  obtain ⟨Q', hQ'₁, hQ'₂, hQ'₃, e, he₁, he₂, he₃⟩ := reroute w₁ w₂ w₃ hQ' (P l)
    (hP₁ l) ha hb hal hbl hc' hcX (F := F)
    (fun e he' => ⟨l, he'⟩) hF
  rw [← he] at hQ'₃ he₁
  have hav' : ∀ x ∈ Q'.support, x ∉ G'.vertexSet := by
    intro x hx hxG
    rcases hQ'₂ x hx with h | h | ⟨h, hne⟩
    · refine hQ₂ x ?_ hxG
      rw [he]
      exact (SimpleGraph.Walk.mem_support_append_iff _ _).2 (Or.inl h)
    · refine hQ₂ x ?_ hxG
      rw [he]
      exact (SimpleGraph.Walk.mem_support_append_iff _ _).2 (Or.inr
        ((SimpleGraph.Walk.mem_support_append_iff _ _).2 (Or.inr h)))
    · exact hne (hP₂ l x h hxG)
  have hle := hmin Q' ⟨hQ'₁, hav'⟩
  have hlt : μ Q' < μ Q := by
    refine ncard_lt_ncard ⟨?_, fun hsub => ?_⟩ (List.finite_toSet _ |>.subset sdiff_subset)
    · rintro f ⟨hf₁, hf₂⟩
      exact ⟨(hQ'₃ f hf₁).resolve_left hf₂, hf₂⟩
    · exact he₃ (hsub ⟨he₁, he₂⟩).1
  omega

end GraphMinor.RST94
