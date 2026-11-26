/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section13za

/-!
# Graph Minors XIX, Section 13: points on the boundary of a sector

We locate each point of `bd(Δ)` on the two paths that make up the boundary of `Δ`, by its position
on the path. Two points that lie on the same side of a pair of positions are not separated
by that pair. This is what the division of (13.7) needs.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM06

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

omit [T2Space Shat] in
theorem GraphWalk.length_support' {G : Drawing Shat} {a b : Shat} (K : GraphWalk G.toGraph a b) :
  K.support.length = K.length + 1 := by
  induction K with
  | nil h => rfl
  | cons h t ih =>
    simp only [GraphWalk.support_cons, List.length_cons, ih]
    simp [GraphWalk.length]

omit [T2Space Shat] in
theorem GraphWalk.vertexAt_eq {G : Drawing Shat} {a b : Shat} (K : GraphWalk G.toGraph a b) {p : ℕ}
    (_ : p ≤ K.length) (h : p < K.support.length := by rw [GraphWalk.length_support']; omega) :
    GraphWalk.vertexAt K p = K.support[p] := by
  simp only [GraphWalk.vertexAt]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

omit [T2Space Shat] in
theorem GraphWalk.exists_vertexAt {G : Drawing Shat} {a b x : Shat} (K : GraphWalk G.toGraph a b)
  (hx : x ∈ K.support) : ∃ p ≤ K.length, x = GraphWalk.vertexAt K p := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have hl := GraphWalk.length_support' K
  exact ⟨i, by omega, (GraphWalk.vertexAt_eq K (by omega) hi).symm⟩

omit [T2Space Shat] in
theorem GraphWalk.vertexAt_mem_left {G : Drawing Shat} {a b c : Shat} (P : GraphWalk G.toGraph a b)
  (Q : GraphWalk G.toGraph b c) {p : ℕ} (hp : p ≤ P.length) :
    GraphWalk.vertexAt (P.append Q) p ∈ P.support := by
  have hl := GraphWalk.length_support' P
  have hl' : p ≤ (P.append Q).length := by rw [GraphWalk.length_append]; omega
  rw [GraphWalk.vertexAt_eq _ hl']
  have hp' : p < P.support.length := by omega
  simp only [GraphWalk.support_append, List.getElem_append_left hp']
  exact List.getElem_mem _

omit [T2Space Shat] in
theorem GraphWalk.vertexAt_mem_right {G : Drawing Shat} {a b c : Shat}
  (P : GraphWalk G.toGraph a b) (Q : GraphWalk G.toGraph b c) {p : ℕ} (hp : P.length ≤ p) (hq : p ≤
    (P.append Q).length) :
    GraphWalk.vertexAt (P.append Q) p ∈ Q.support := by
  by_cases he : p = P.length
  · subst he
    rw [GraphWalk.vertexAt_append]
    exact Q.start_mem_support
  have hl := GraphWalk.length_support' P
  have hlk := GraphWalk.length_support' (P.append Q)
  rw [GraphWalk.vertexAt_eq _ hq]
  simp only [GraphWalk.support_append]
  rw [List.getElem_append_right (by omega)]
  exact List.mem_of_mem_tail (List.getElem_mem _)

omit [T2Space Shat] in
theorem GraphWalk.vertexAt_zero {G : Drawing Shat} {a b : Shat} (K : GraphWalk G.toGraph a b) :
  GraphWalk.vertexAt K 0 = a := by
  cases K <;> simp [GraphWalk.vertexAt, GraphWalk.support]

omit [T2Space Shat] in
theorem GraphWalk.vertexAt_length {G : Drawing Shat} {a b : Shat} (K : GraphWalk G.toGraph a b)
  (h : b ∈ G.V) : GraphWalk.vertexAt K K.length = b := by
  induction K with
  | nil h' => simp [GraphWalk.vertexAt, GraphWalk.support, GraphWalk.length]
  | cons hl t ih =>
    have := ih h
    simpa [GraphWalk.vertexAt, GraphWalk.support, GraphWalk.length] using this

omit [T2Space Shat] in
theorem GraphWalk.vertexAt_inj {G : Drawing Shat} {a b : Shat} (K : GraphWalk G.toGraph a b)
  (hs : K.IsSimple) {p q : ℕ} (hp : p ≤ K.length) (hq : q ≤ K.length)
    (h : GraphWalk.vertexAt K p = GraphWalk.vertexAt K q) : p = q := by
  have hl := GraphWalk.length_support' K
  have hp' : p < K.support.length := by omega
  have hq' : q < K.support.length := by omega
  rw [GraphWalk.vertexAt_eq K hp hp', GraphWalk.vertexAt_eq K hq hq'] at h
  exact (List.Nodup.getElem_inj_iff hs).mp h

omit [T2Space Shat] in
theorem GraphWalk.vertexAt_mem {G : Drawing Shat} {a b : Shat} (K : GraphWalk G.toGraph a b) {p :
  ℕ} (hp : p ≤ K.length) : GraphWalk.vertexAt K p ∈ K.support := by
  have hl := GraphWalk.length_support' K
  have hp' : p < K.support.length := by omega
  rw [GraphWalk.vertexAt_eq K hp hp']
  exact List.getElem_mem _

omit [T2Space Shat] in
/-- The position of an edge is the same in any two splittings. -/
theorem GraphWalk.mem_edges_of_split {G : Drawing Shat} {a b x y c : Shat} {g : Set Shat}
  (K : GraphWalk G.toGraph a b) (P₀ : GraphWalk G.toGraph a x) (hl : G.toGraph.IsLink g x y)
    (Q₀ : GraphWalk G.toGraph y b) (h₀ : K = P₀.append (.cons hl Q₀)) (P : GraphWalk G.toGraph a c)
      (Q : GraphWalk G.toGraph c b) (h : K = P.append Q) :
    (P₀.length < P.length → g ∈ P.edges) ∧ (P.length ≤ P₀.length → g ∈ Q.edges) := by
  have e : P₀.edges ++ g :: Q₀.edges = P.edges ++ Q.edges := by
    have h₁ := congrArg GraphWalk.edges (h₀.symm.trans h)
    simpa [GraphWalk.edges_append] using h₁
  have hk : (P₀.edges ++ g :: Q₀.edges)[P₀.edges.length]? = some g := by simp
  rw [e] at hk
  constructor
  · intro hlt
    have hlt' : P₀.edges.length < P.edges.length := hlt
    rw [List.getElem?_append_left hlt'] at hk
    exact List.mem_of_getElem? hk
  · intro hle
    have hle' : P.edges.length ≤ P₀.edges.length := hle
    rw [List.getElem?_append_right hle'] at hk
    exact List.mem_of_getElem? hk

namespace TangleDatum

/-- Two paths of `Γ*` from a vertex `r` of `R*` to `u`, of the same length, with no other common
vertex. They are the boundary of the sector of (13.7), and the last field says
that no walk of `Γ*` is a short cut, which we prove from the spokes later. -/
structure IsBigon (D : TangleDatum cap χ) {r u : Shat} (B : Bool → GraphWalk D.rad.G.toGraph r u) :
  Prop where
  r_mem : r ∈ D.rad.Rstar
  ne : r ≠ u
  simple : ∀ i, (B i).IsSimple
  len : ∀ i i', (B i).length = (B i').length
  meet : ∀ i i', i ≠ i' → ∀ y, y ∈ (B i).support → y ∈ (B i').support → y = r ∨ y = u
  far : ∀ i i' p q, p ≤ q → q ≤ (B i').length → ∀ K : GraphWalk D.rad.G.toGraph (GraphWalk.vertexAt
    (B i) p) (GraphWalk.vertexAt (B i') q), q - p ≤ K.length

variable {D : TangleDatum cap χ} {r u : Shat} {B : Bool → GraphWalk D.rad.G.toGraph r u}

omit [T2Space S] [T2Space Shat] in
theorem IsBigon.u_mem (_hB : D.IsBigon B) : u ∈ D.rad.G.V := (B true).mem_vertexSet_of_mem_support
  (B true).end_mem_support

omit [T2Space S] in
omit [T2Space Shat] in
/-- A vertex of the bigon has one position. -/
theorem IsBigon.position_unique (hB : D.IsBigon B) {i i' : Bool} {p q : ℕ} (hp : p ≤ (B i).length)
  (hq : q ≤ (B i').length) (h : GraphWalk.vertexAt (B i) p = GraphWalk.vertexAt (B i') q) : p = q
    := by
  by_cases hi : i = i'
  · subst hi
    exact GraphWalk.vertexAt_inj _ (hB.simple i) hp hq h
  have h₁ := GraphWalk.vertexAt_mem (B i) hp
  have h₂ := GraphWalk.vertexAt_mem (B i') hq
  rw [← h] at h₂
  rcases hB.meet i i' hi _ h₁ h₂ with h₃ | h₃
  · have e₁ : p = 0 := GraphWalk.vertexAt_inj _ (hB.simple i) hp (Nat.zero_le _) (h₃.trans
      (GraphWalk.vertexAt_zero _).symm)
    have e₂ : q = 0 := GraphWalk.vertexAt_inj _ (hB.simple i') hq (Nat.zero_le _)
      ((h.symm.trans h₃).trans (GraphWalk.vertexAt_zero _).symm)
    omega
  · have e₁ : p = (B i).length := GraphWalk.vertexAt_inj _ (hB.simple i) hp le_rfl (h₃.trans
      (GraphWalk.vertexAt_length _ hB.u_mem).symm)
    have e₂ : q = (B i').length := GraphWalk.vertexAt_inj _ (hB.simple i') hq le_rfl
      ((h.symm.trans h₃).trans (GraphWalk.vertexAt_length _ hB.u_mem).symm)
    have := hB.len i i'
    omega

omit [T2Space Shat] in
/-- The vertices of `Γ` on the bigon are those in odd position, because `Γ*` is bipartite and `r` is
not a vertex of `Γ`. -/
theorem IsBigon.hatV_iff (hB : D.IsBigon B) (i : Bool) {p : ℕ} (hp : p ≤
  (B i).length) : GraphWalk.vertexAt (B i) p ∈ D.P.Γ.hatV cap ↔ Odd p := by
  obtain ⟨P, Q, -, hl⟩ := GraphWalk.exists_split_at (B i) hp
  have h := D.even_length_walk P
  have hr : r ∉ D.P.Γ.hatV cap := hB.r_mem.2
  rw [hl] at h
  rw [← Nat.not_even_iff_odd, h]
  tauto

/-- Where a point of the boundary of the sector lies, on the walk `K`: at position `q`, in the sense
that any splitting of `K` at another position has the point on the part towards `q`. -/
def IsPlaced (D : TangleDatum cap χ) {a b : Shat} (K : GraphWalk D.rad.G.toGraph a b) (x : Shat)
  (q : ℕ) : Prop :=
  q ≤ K.length ∧ (x = GraphWalk.vertexAt K q ∨ x ∉ D.rad.G.V) ∧ ∀ (c : Shat)
    (P : GraphWalk D.rad.G.toGraph a c) (Q : GraphWalk D.rad.G.toGraph c b), K = P.append Q →
    (q < P.length → x ∈ (walkDrawing D.rad.G P).U) ∧ (P.length < q → x ∈ (walkDrawing D.rad.G Q).U)

omit [T2Space S] in
theorem isPlaced_vertexAt (D : TangleDatum cap χ) {a b : Shat} (K : GraphWalk D.rad.G.toGraph a b)
  {q : ℕ} (hq : q ≤ K.length) : D.IsPlaced K (GraphWalk.vertexAt K q) q := by
  refine ⟨hq, .inl rfl, ?_⟩
  rintro c P Q rfl
  refine ⟨fun h ↦ (mem_walkDrawing_U _ _).mpr (.inl (GraphWalk.vertexAt_mem_left P Q h.le)),
    fun h ↦ (mem_walkDrawing_U _ _).mpr (.inl (GraphWalk.vertexAt_mem_right P Q h.le hq))⟩

omit [T2Space S] in
theorem isPlaced_edge {a b x y z : Shat} {g : Set Shat} (K : GraphWalk D.rad.G.toGraph a b)
  (P₀ : GraphWalk D.rad.G.toGraph a x) (hl : D.rad.G.toGraph.IsLink g x y)
    (Q₀ : GraphWalk D.rad.G.toGraph y b) (h₀ : K = P₀.append (.cons hl Q₀)) (hz : z ∈ g) {q : ℕ}
      (hq : q = P₀.length ∨ q = P₀.length + 1) : D.IsPlaced K z q := by
  have hlen : K.length = P₀.length + Q₀.length + 1 := by
    rw [h₀, GraphWalk.length_append]
    simp only [GraphWalk.length, GraphWalk.edges_cons, List.length_cons]
    omega
  refine ⟨by omega, .inr (hl.1.2.1 hz).2, ?_⟩
  intro c P Q h
  have hm := GraphWalk.mem_edges_of_split K P₀ hl Q₀ h₀ P Q h
  refine ⟨fun hlt ↦ (mem_walkDrawing_U _ _).mpr (.inr ⟨g, hm.1 (by omega), subset_closure hz⟩),
    fun hlt ↦ (mem_walkDrawing_U _ _).mpr (.inr ⟨g, hm.2 (by omega), subset_closure hz⟩)⟩

theorem IsBigon.exists_place_vertex (hB : D.IsBigon B) (i : Bool) {x : Shat} (hs : x ∈
  (B i).support) :
    ∃ q a, D.IsPlaced (B i) x q ∧ D.IsCenteredOn x (GraphWalk.vertexAt (B i) q) a ∧ (a = 0 ↔ Odd q)
      := by
  obtain ⟨q, hq, rfl⟩ := GraphWalk.exists_vertexAt _ hs
  by_cases ho : Odd q
  · exact ⟨q, 0, isPlaced_vertexAt D _ hq, .inl ⟨rfl, rfl, (hB.hatV_iff i hq).mpr ho⟩,
      by simpa using ho⟩
  · have hw : GraphWalk.vertexAt (B i) q ∈ D.rad.Rstar := ⟨(B i).mem_vertexSet_of_mem_support hs,
      fun hn ↦ ho ((hB.hatV_iff i hq).mp hn)⟩
    exact ⟨q, 1, isPlaced_vertexAt D _ hq, .inr ⟨rfl, hw, (D.rad.regionOf_mem hw).2⟩,
      by simpa using ho⟩

/-- Each point of a side of the bigon has a place, with a centre at that position. -/
theorem IsBigon.exists_place (hB : D.IsBigon B) (i : Bool) {x : Shat} (hx : x ∈
  (walkDrawing D.rad.G (B i)).U) :
    ∃ q a, D.IsPlaced (B i) x q ∧ D.IsCenteredOn x (GraphWalk.vertexAt (B i) q) a ∧ (a = 0 ↔ Odd q)
      := by
  rcases (mem_walkDrawing_U _ _).mp hx with hs | ⟨g, hg, hxg⟩
  · exact hB.exists_place_vertex i hs
  obtain ⟨c, d, hl, P₀, Q₀, h₀⟩ := GraphWalk.exists_split_edge (B i) hg
  have hgG : g ∈ D.rad.G.E := hl.1
  by_cases hxG : x ∈ D.rad.G.V
  · have hm : x ∈ closure g ∩ D.rad.G.V := ⟨hxg, hxG⟩
    rw [hl.2.2.2] at hm
    have hs : x ∈ (B i).support := by
      rw [h₀, GraphWalk.mem_support_append]
      rcases hm with rfl | rfl
      · exact .inl P₀.end_mem_support
      · exact .inr (by rw [GraphWalk.support_cons]; simpa using .inr Q₀.start_mem_support)
    exact hB.exists_place_vertex i hs
  have hxg' : x ∈ g := (closure_edge_subset hgG hxg).resolve_right hxG
  have hlen : (B i).length = P₀.length + Q₀.length + 1 := by
    rw [h₀, GraphWalk.length_append]
    simp only [GraphWalk.length, GraphWalk.edges_cons, List.length_cons]
    omega
  have hc : GraphWalk.vertexAt (B i) P₀.length = c := by
    rw [h₀]; exact GraphWalk.vertexAt_append _ _
  have hd : GraphWalk.vertexAt (B i) (P₀.length + 1) = d := by
    have h₁ : (B i) = (P₀.append (.cons hl (.nil hl.2.2.1))).append Q₀ := by
      rw [h₀, GraphMinor.GM19.GraphWalk.append_assoc']; rfl
    have h₂ : (P₀.append (.cons hl (.nil hl.2.2.1))).length = P₀.length + 1 := by
      rw [GraphWalk.length_append]
      simp [GraphWalk.length, GraphWalk.edges]
    rw [← h₂, h₁]
    exact GraphWalk.vertexAt_append _ _
  have hclo : c ∈ closure g ∧ d ∈ closure g := by
    have h₁ : c ∈ closure g ∩ D.rad.G.V := by rw [hl.2.2.2]; exact .inl rfl
    have h₂ : d ∈ closure g ∩ D.rad.G.V := by rw [hl.2.2.2]; exact .inr rfl
    exact ⟨h₁.1, h₂.1⟩
  have hcen : ∀ {q : ℕ} {z : Shat}, q ≤ (B i).length → z ∈ closure g → z ∈ D.rad.G.V → ¬ Odd q
    → GraphWalk.vertexAt (B i) q = z → D.IsCenteredOn x (GraphWalk.vertexAt (B i) q) 1
      := fun {q z} hq hzg hzG ho e ↦ by
    rw [e]
    have hz : z ∈ D.rad.Rstar := ⟨hzG, fun hn ↦ ho ((hB.hatV_iff i hq).mp (by rwa [e]))⟩
    exact .inr ⟨rfl, hz, edge_subset_regionOf D hz hgG hzg hxg'⟩
  by_cases hk : Odd P₀.length
  · have ho : ¬ Odd (P₀.length + 1) := by
      rw [Nat.not_odd_iff_even]
      exact hk.add_one
    exact ⟨P₀.length + 1, 1, isPlaced_edge _ P₀ hl Q₀ h₀ hxg' (.inr rfl),
      hcen (by omega) hclo.2 hl.2.2.1 ho hd, by simpa using ho⟩
  · exact ⟨P₀.length, 1, isPlaced_edge _ P₀ hl Q₀ h₀ hxg' (.inl rfl),
      hcen (by omega) hclo.1 hl.2.1 hk hc, by simpa using hk⟩

end TangleDatum

end GraphMinor.GM19
