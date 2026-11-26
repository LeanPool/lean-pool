/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section13b

/-!
# Graph Minors XIX, Section 13: (13.3)

A spoke and an enclave. The main fact is `IsSpoke.subwalk_in_enclave`: a part of a spoke between two
vertices of an enclave `F`
lies in `F`. Otherwise the spoke has a part between two vertices of `F` that is otherwise disjoint
from `F`, and (8.5) gives a
contradiction.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11

universe w

variable {S Shat : Type} [TopologicalSpace S] [T2Space S] [TopologicalSpace Shat] [T2Space Shat]
  {α : Type w} {cap : IsCappedSurface S Shat} {χ : ColourScheme S α}

/-- The last vertex of a walk in a set. -/
theorem GraphWalk.exists_last_mem {α' β : Type*} {G : Graph α' β} {a b : α'}
  (K : GraphWalk G a b) {X : Set α'}
    (hm : ∃ x ∈ K.support, x ∈ X) : ∃ u ∈ X, ∃ (A : GraphWalk G a u) (B : GraphWalk G u b), K
      = A.append B ∧
      ∀ x ∈ B.support, x ∈ X → x = u := by
  induction K with
  | nil h =>
    obtain ⟨x, hx, hxX⟩ := hm
    simp only [GraphWalk.support_nil, List.mem_singleton] at hx
    subst hx
    refine ⟨x, hxX, .nil h, .nil h, rfl, ?_⟩
    intro y hy _
    simpa using hy
  | @cons a c b e h r ih =>
    by_cases hr : ∃ x ∈ r.support, x ∈ X
    · obtain ⟨u, hu, A, B, rfl, hB⟩ := ih hr
      exact ⟨u, hu, .cons h A, B, rfl, hB⟩
    · obtain ⟨x, hx, hxX⟩ := hm
      rcases List.mem_cons.mp hx with rfl | hx'
      · refine ⟨x, hxX, .nil h.left_mem, .cons h r, rfl, ?_⟩
        intro y hy hyX
        rcases List.mem_cons.mp hy with rfl | hy'
        · rfl
        · exact absurd ⟨y, hy', hyX⟩ hr
      · exact absurd ⟨x, hx', hxX⟩ hr

/-- The ends of an edge of a subdrawing lie in the subdrawing. -/
theorem Drawing.IsLink.mem_V_of_sub {T : Type} [TopologicalSpace T] {F G : Drawing T}
  (hF : F.IsSubdrawing G)
    {e : Set T} {x y : T} (hl : G.toGraph.IsLink e x y) (he : e ∈ F.E) : x ∈ F.V ∧ y ∈ F.V := by
  have hl' := (hF.isLink_iff he).mpr hl
  exact ⟨hl'.left_mem, hl'.right_mem⟩

/-- A walk with all its edges in `F`, starting in `F`, has all its vertices in `F`. -/
theorem support_subset_of_edges {T : Type} [TopologicalSpace T] {F G : Drawing T}
  (hF : F.IsSubdrawing G)
    {a b : T} (M : GraphWalk G.toGraph a b) (ha : a ∈ F.V) (hE : ∀ e ∈ M.edges, e ∈ F.E) : ∀ x ∈
      M.support, x ∈ F.V := by
  induction M with
  | nil h =>
    intro x hx
    simp only [GraphWalk.support_nil, List.mem_singleton] at hx
    exact hx ▸ ha
  | @cons a c b e h r ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact ha
    · exact ih (Drawing.IsLink.mem_V_of_sub hF h (hE e (by simp))).2 (fun f hf ↦ hE f
        (by simp [hf])) x hx'

/-- A simple walk that leaves `F`, and meets `F` at most in its last vertex, uses no edge of `F`. -/
theorem edges_notMem_of_avoid {T : Type} [TopologicalSpace T] {F G : Drawing T}
  (hF : F.IsSubdrawing G)
    {c u : T} (M : GraphWalk G.toGraph c u) (hc : c ∉ F.V) (hs : M.IsSimple)
      (hX : ∀ x ∈ M.support, x ∈ F.V → x = u) :
    ∀ e ∈ M.edges, e ∉ F.E := by
  induction M with
  | nil h => simp
  | @cons c c' u e h r ih =>
    intro f hf hfF
    rcases List.mem_cons.mp hf with rfl | hf'
    · exact hc (Drawing.IsLink.mem_V_of_sub hF h hfF).1
    · by_cases hc' : c' ∈ F.V
      · have h₁ : c' = u := hX c' (by simp [r.start_mem_support]) hc'
        subst h₁
        have := hs.of_cons.length_eq_zero
        have h₂ : r.edges = [] := List.eq_nil_of_length_eq_zero this
        simp [h₂] at hf'
      · exact ih hc' hs.of_cons (fun x hx ↦ hX x (by simp [hx])) f hf' hfF

/-- A walk through an edge splits at the edge. -/
theorem GraphWalk.exists_split_edge {α' β : Type*} {G : Graph α' β} {a b : α'}
  (K : GraphWalk G a b) {e : β}
    (he : e ∈ K.edges) : ∃ (x y : α') (hl : G.IsLink e x y) (A : GraphWalk G a x)
      (B : GraphWalk G y b),
      K = A.append (GraphWalk.cons hl B) :=
  K.split_at_edge he

namespace TangleDatum

variable {D : TangleDatum cap χ} {W : Set Shat} {H F P : Drawing Shat} {v h : Shat}

omit [T2Space S] in
/-- A part of a spoke cannot be replaced by a shorter or lighter walk. -/
theorem IsSpoke.part_bound (hS : D.IsSpoke W H v h P) {a b : Shat} {A : GraphWalk D.rad.G.toGraph v
  a}
    {M L : GraphWalk D.rad.G.toGraph a b} {B : GraphWalk D.rad.G.toGraph b h} (hK : (A.append
      (M.append B)).IsSimple)
    (hE : ∀ e, e ∈ P.E ↔ e ∈ (A.append (M.append B)).edges) :
    M.length ≤ L.length ∧ (L.length = M.length → D.tb.walkWeight M ≤ D.tb.walkWeight L) := by
  classical
  have hc : P.E.ncard = (A.append (M.append B)).length := by
    rw [← ncard_walk_E D.rad.G hK]
    congr 1
    ext e
    rw [hE e, walkDrawing_E]
    rfl
  have hw := D.tb.weightSub_eq_of_simple hK hE
  obtain ⟨b₁, w₁⟩ := hS.walk_bound hS.h_mem (A.append (L.append B))
  simp only [GraphWalk.length_append, D.tb.walkWeight_append] at hc hw b₁ w₁
  refine ⟨by omega, fun heq ↦ ?_⟩
  have := w₁ (by omega)
  linarith

/-- **The step of (13.3).** A part of a spoke between two distinct vertices of an enclave must meet
the enclave somewhere else.
The proof is the one in the paper: (8.5) applied to the part and the two paths of `F` between its
ends. -/
theorem IsSpoke.no_ear (hS : D.IsSpoke W H v h P) (hF : IsEnclave D.tb D.ord D.𝒯 F) {a b : Shat}
    {A : GraphWalk D.rad.G.toGraph v a} {M : GraphWalk D.rad.G.toGraph a b} {B : GraphWalk
      D.rad.G.toGraph b h}
    (hK : (A.append (M.append B)).IsSimple) (hE : ∀ e, e ∈ P.E ↔ e ∈ (A.append (M.append B)).edges)
    (hab : a ≠ b) (ha : a ∈ F.V) (hb : b ∈ F.V) (hMV : ∀ x ∈ M.support, x ∈ F.V → x = a ∨ x = b)
    (hME : ∀ e ∈ M.edges, e ∉ F.E) : False := by
  classical
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨ord', 𝒯', h𝒯', hc, -, Δ, hins, hd⟩ := id hF
  have hS' := χ.isSurface
  have h3 := D.P.fits.internally_three_connected
  have hMs : M.IsSimple := (GraphWalk.IsSimple.of_append (GraphWalk.IsSimple.of_append hK).2).1
  obtain ⟨F₁, F₂, hF₁, hF₂, hs₁, hs₂, hp₁, hp₂, hV₁₂, hE₁₂, hsup⟩ := hc.2.exists_two_paths ha hb hab
  set Q := walkDrawing D.rad.G M with hQ
  have hQE : ∀ e, e ∈ Q.E ↔ e ∈ M.edges := fun e ↦ by rw [hQ, walkDrawing_E]; rfl
  have hQp : Drawing.IsPathOf Q D.rad.G a b := ⟨walkDrawing_isSubdrawing _ _,
    walkDrawing_isPathBetween _ hMs⟩
  have ht : TwoPaths D.rad.G F F₁ F₂ Q a b := by
    refine ⟨hab, hc.1, ⟨hs₁, hF₁⟩, ⟨hs₂, hF₂⟩, ?_, ?_, hV₁₂.le, hE₁₂, hQp, ?_, ?_⟩
    · have := Drawing.sup_V hs₁ hs₂
      rwa [hsup] at this
    · have := Drawing.sup_E hs₁ hs₂
      rwa [hsup] at this
    · rintro x ⟨hxQ, hxF⟩
      have : x ∈ M.support := by simpa [hQ, walkDrawing_V] using hxQ
      exact hMV x this hxF
    · exact disjoint_left.mpr fun e he he' ↦ hME e ((hQE e).mp he) he'
  have hwQ := D.tb.weightSub_eq_of_simple hMs hQE
  have hcQ : Q.E.ncard = M.length := ncard_walk_E D.rad.G hMs
  -- Each of the two paths of `F` is at least as long as `Q`, and heavier if it is equally long.
  have hbound : ∀ {X : Drawing Shat}, Drawing.IsPathOf X F a b → Disjoint Q.E X.E → X.E.Nonempty →
      Q.E.ncard ≤ X.E.ncard ∧ (X.E.ncard = Q.E.ncard → D.tb.weightSub Q < D.tb.weightSub X) := by
    intro X hX hdis hne
    have hXG : Drawing.IsPathOf X D.rad.G a b := ⟨hX.1.trans hc.1, hX.2⟩
    obtain ⟨L, hL, -, hLE⟩ := Drawing.IsPathOf.exists_simple_walk hXG
    have hcL : X.E.ncard = L.length := by
      rw [← ncard_walk_E D.rad.G hL]
      congr 1
      ext e
      rw [hLE e, walkDrawing_E]
      rfl
    obtain ⟨h₁, h₂⟩ := hS.part_bound (L := L) hK hE
    refine ⟨by omega, fun heq ↦ ?_⟩
    have hle := h₂ (by omega)
    have hwL := D.tb.weightSub_eq_of_simple hL hLE
    have hne' := D.tb.weight_ne (X := Q.E) (Y := X.E) (walkDrawing_isSubdrawing _ _).2
      (hX.1.trans hc.1).2 hdis hne
    have hle' : D.tb.weightSub Q ≤ D.tb.weightSub X := by rw [hwQ, hwL]; exact hle
    exact lt_of_le_of_ne hle' hne'
  have hd₁ : Disjoint Q.E F₁.E := disjoint_left.mpr fun e he he' ↦ disjoint_left.mp ht.meet_E he
    (hs₁.2 he')
  have hd₂ : Disjoint Q.E F₂.E := disjoint_left.mpr fun e he he' ↦ disjoint_left.mp ht.meet_E he
    (hs₂.2 he')
  obtain ⟨b₁, w₁⟩ := hbound ht.left hd₁ ht.exists_edge
  obtain ⟨b₂, w₂⟩ := hbound ht.right hd₂ ht.swap.exists_edge
  obtain ⟨-, -, -, -, h₁, h₂⟩ := theorem_8_5_proof hS' h3 D.tb D.isTangle h𝒯' hins hd ht b₁
    (fun e ↦ (w₁ e.symm).le)
  have heq : Q.E.ncard = F₂.E.ncard := by omega
  exact lt_irrefl _ ((w₂ heq.symm).trans (h₂ heq))

/-- **A part of a spoke between two vertices of an enclave lies in the enclave.** The paper uses
this form of (13.3) in (13.6). -/
theorem IsSpoke.subwalk_in_enclave (hS : D.IsSpoke W H v h P) (hF : IsEnclave D.tb D.ord D.𝒯 F) {a
  b : Shat}
    {A : GraphWalk D.rad.G.toGraph v a} (M : GraphWalk D.rad.G.toGraph a b) {B : GraphWalk
      D.rad.G.toGraph b h}
    (hK : (A.append (M.append B)).IsSimple) (hE : ∀ e, e ∈ P.E ↔ e ∈ (A.append (M.append B)).edges)
    (ha : a ∈ F.V) (hb : b ∈ F.V) : ∀ e ∈ M.edges, e ∈ F.E := by
  classical
  obtain ⟨ord', 𝒯', h𝒯', hc, -⟩ := id hF
  induction M with
  | nil h => simp
  | @cons a c b g hl r ih =>
    -- `c` is a vertex of `F`, and `g` is an edge of `F`.
    have hg : g ∈ F.E ∧ c ∈ F.V := by
      have hm : ∃ x ∈ r.support, x ∈ F.V := ⟨b, r.end_mem_support, hb⟩
      obtain ⟨u, huF, r₁, r₂, hr, hfirst⟩ := GraphWalk.exists_first_mem r hm
      subst hr
      have hKs : (A.append ((GraphWalk.cons hl r₁).append (r₂.append B))).IsSimple := by
        have h₁ : A.append ((GraphWalk.cons hl (r₁.append r₂)).append B) =
            A.append ((GraphWalk.cons hl r₁).append (r₂.append B)) := by
          rw [show (GraphWalk.cons hl (r₁.append r₂)) = (GraphWalk.cons hl r₁).append r₂ from rfl,
            GraphWalk.append_assoc']
        rwa [h₁] at hK
      have hE' : ∀ e, e ∈ P.E ↔ e ∈ (A.append ((GraphWalk.cons hl r₁).append (r₂.append B))).edges
        := by
        intro e
        rw [hE e]
        simp [GraphWalk.edges_append]
      have hsimple : (GraphWalk.cons hl r₁).IsSimple :=
        (GraphWalk.IsSimple.of_append (GraphWalk.IsSimple.of_append hKs).2).1
      have hau : a ≠ u := by
        rintro rfl
        exact (List.nodup_cons.mp hsimple).1 r₁.end_mem_support
      have huniq : ∀ x ∈ (GraphWalk.cons hl r₁).support, x ∈ F.V → x = a ∨ x = u := by
        intro x hx hxF
        rcases List.mem_cons.mp hx with rfl | hx'
        · exact .inl rfl
        · exact .inr (hfirst x hx' hxF)
      by_cases hcF : c ∈ F.V
      · have hcu : c = u := hfirst c r₁.start_mem_support hcF
        subst hcu
        refine ⟨?_, hcF⟩
        by_contra hgF
        have hr₁ : r₁.edges = [] := List.eq_nil_of_length_eq_zero hsimple.of_cons.length_eq_zero
        refine (hS.no_ear hF hKs hE' hau ha huF huniq fun e he ↦ ?_).elim
        have : e = g := by simpa [hr₁] using he
        exact this ▸ hgF
      · exfalso
        refine hS.no_ear hF hKs hE' hau ha huF huniq fun e he ↦ ?_
        rcases List.mem_cons.mp he with rfl | he'
        · exact fun hF' ↦ hcF (Drawing.IsLink.mem_V_of_sub hc.1 hl hF').2
        · exact edges_notMem_of_avoid hc.1 r₁ hcF hsimple.of_cons hfirst e he'
    intro e he
    rcases List.mem_cons.mp he with rfl | he'
    · exact hg.1
    · have hA : (A.append (GraphWalk.cons hl (GraphWalk.nil hl.right_mem))).append (r.append B) =
          A.append ((GraphWalk.cons hl r).append B) := by
        rw [GraphWalk.append_assoc']
        rfl
      refine ih (A := A.append (GraphWalk.cons hl (GraphWalk.nil hl.right_mem)))
        (by rw [hA]; exact hK) ?_ hg.2 hb e he'
      intro f
      rw [hA]
      exact hE f

omit [T2Space S] in
/-- From the inside of a circuit, an edge of `Γ*` stays inside. -/
theorem edge_inside_of_mem (D : TangleDatum cap χ) {F : Drawing Shat} (hF : F.IsCircuitOf D.rad.G)
    (hlt : F.E.ncard < 2 * D.rep) {g : Set Shat} {x y : Shat} (hl : D.rad.G.toGraph.IsLink g x y)
    (hx : x ∈ D.ins F \ F.U) : g ⊆ D.ins F ∧ y ∈ D.ins F := by
  have : ConnectedSpace Shat := cap.connected
  have hsl := D.isSlope (by omega)
  obtain ⟨hcl, hfr, hU⟩ := ins_facts_of_length hsl hF.2 hF.1 hlt
  have hint : x ∈ interior (D.ins F) := by
    by_contra hn
    apply hx.2
    rw [← hfr, frontier, hcl.closure_eq]
    exact ⟨hx.1, hn⟩
  have hxg : x ∈ closure g := by
    have : x ∈ closure g ∩ D.rad.G.V := by
      rw [hl.2.2.2]
      exact .inl rfl
    exact this.1
  have hyg : y ∈ closure g := by
    have : y ∈ closure g ∩ D.rad.G.V := by
      rw [hl.2.2.2]
      exact .inr rfl
    exact this.1
  have hsub : g ⊆ D.ins F := by
    rcases edge_subset_or_disjoint_of_length hsl hF.2 hF.1 hlt hl.1 with h | h
    · exact h
    · obtain ⟨p, hp, hpg⟩ := mem_closure_iff.mp hxg _ isOpen_interior hint
      exact absurd (interior_subset hp) (disjoint_left.mp h hpg)
  exact ⟨hsub, closure_minimal hsub hcl hyg⟩

omit [T2Space S] in
/-- A walk from inside a circuit to a point not strictly inside it meets the circuit. -/
theorem walk_meets_circuit (D : TangleDatum cap χ) {F : Drawing Shat} (hF : F.IsCircuitOf D.rad.G)
    (hlt : F.E.ncard < 2 * D.rep) {x z : Shat} (T : GraphWalk D.rad.G.toGraph x z)
      (hx : x ∈ D.ins F)
    (hz : z ∉ D.ins F \ F.U) : ∃ a ∈ T.support, a ∈ F.V := by
  have : ConnectedSpace Shat := cap.connected
  induction T with
  | nil h =>
    rename_i y
    refine ⟨y, by simp, ?_⟩
    by_contra hn
    exact hz ⟨hx, fun hu ↦ hn (mem_V_of_mem_U hF.1 hu h)⟩
  | @cons x c z e h r ih =>
    by_cases hxF : x ∈ F.V
    · exact ⟨x, by simp, hxF⟩
    · have hx' : x ∈ D.ins F \ F.U := ⟨hx, fun hu ↦ hxF (mem_V_of_mem_U hF.1 hu h.left_mem)⟩
      obtain ⟨a, ha, haF⟩ := ih (D.edge_inside_of_mem hF hlt h hx').2 hz
      exact ⟨a, by simp [ha], haF⟩

omit [T2Space S] in
/-- The ends of an edge of a walk lie on the walk, and they are different. -/
theorem exists_ends_of_mem_edges (D : TangleDatum cap χ) {a b : Shat}
  (K : GraphWalk D.rad.G.toGraph a b) {e : Set Shat}
    (he : e ∈ K.edges) : ∃ x y, x ≠ y ∧ x ∈ K.support ∧ y ∈ K.support ∧ closure e ∩ D.rad.G.V
      = {x, y} := by
  have heG : e ∈ D.rad.G.E := TieBreaker.mem_edges_E K he
  obtain ⟨x, hx, y, hy, hcap⟩ := D.rad.isPreRadial.2.2.2.2.1 e heG
  have hl : D.rad.G.toGraph.IsLink e x y := ⟨heG, D.rad.isPreRadial.2.1 hx, hy.1, hcap⟩
  have hl' : D.rad.G.toGraph.IsLink e y x := ⟨heG, hy.1, D.rad.isPreRadial.2.1 hx, by rw [hcap,
    pair_comm]⟩
  have hne : x ≠ y := fun h ↦ hy.2 (h ▸ hx)
  exact ⟨x, y, hne, K.left_mem_support_of_mem_edges he hl, K.left_mem_support_of_mem_edges he hl',
    hcap⟩

/-- A vertex of a spoke with vertices of an enclave on both sides lies in the enclave. -/
theorem IsSpoke.mem_of_between (hS : D.IsSpoke W H v h P) (hF : IsEnclave D.tb D.ord D.𝒯 F) {z :
  Shat}
    {K₁ : GraphWalk D.rad.G.toGraph v z} {K₂ : GraphWalk D.rad.G.toGraph z h} (hK :
      (K₁.append K₂).IsSimple)
    (hE : ∀ e, e ∈ P.E ↔ e ∈ (K₁.append K₂).edges) (h₁ : ∃ a ∈ K₁.support, a ∈ F.V)
      (h₂ : ∃ a ∈ K₂.support, a ∈ F.V) :
    z ∈ F.V := by
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨ord', 𝒯', h𝒯', hc, -⟩ := id hF
  obtain ⟨a, ha, haF⟩ := h₁
  obtain ⟨b, hb, hbF⟩ := h₂
  obtain ⟨A, L₁, rfl⟩ := K₁.exists_append_of_mem ha
  obtain ⟨L₂, B, rfl⟩ := K₂.exists_append_of_mem hb
  have heq : (A.append L₁).append (L₂.append B) = A.append ((L₁.append L₂).append B) := by
    rw [GraphWalk.append_assoc', GraphWalk.append_assoc']
  rw [heq] at hK hE
  have hin := hS.subwalk_in_enclave hF (L₁.append L₂) hK hE haF hbF
  exact support_subset_of_edges hc.1 _ haF hin z
    ((GraphWalk.mem_support_append L₁ L₂).mpr (.inl L₁.end_mem_support))

/-- **Graph Minors XIX, (13.3)** (page 367): "Let $S_v$ be a spoke with inner end $h$, and let $F$
be a $\mathscr{T}$-enclave. If $U(S_v)
\cap ins(F) \ne \emptyset$ then $S_v \cap ins(F)$ is a path, and if $U(S_v) \cap ins(F)
\nsubseteq U(F)$ then one of $v, h \in ins(F) \setminus U(F)$." -/
theorem theorem_13_3_proof (hS : D.IsSpoke W H v h P) (hF : IsEnclave D.tb D.ord D.𝒯 F) :
    ((P.U ∩ D.ins F).Nonempty → ∃ (a b : Shat) (Q : Drawing Shat), Drawing.IsPathOf Q D.rad.G a b ∧
      Q.V = P.V ∩ D.ins F ∧ Q.E = {e ∈ P.E | e ⊆ D.ins F}) ∧
    (¬ P.U ∩ D.ins F ⊆ F.U → v ∈ D.ins F \ F.U ∨ h ∈ D.ins F \ F.U) := by
  classical
  have : ConnectedSpace Shat := cap.connected
  obtain ⟨ord', 𝒯', h𝒯', hc, hlt, -⟩ := id hF
  have hlt' : F.E.ncard < 2 * D.rep := hlt
  have hsl := D.isSlope (by omega)
  obtain ⟨hcl, hfr, hU⟩ := ins_facts_of_length hsl hc.2 hc.1 hlt'
  obtain ⟨K, hK, hV, hE⟩ := Drawing.IsPathOf.exists_simple_walk hS.is_path
  -- A point of `U(S)` inside `ins(F)` gives a vertex of `S` in `ins(F)`, or an edge of `S` with
  -- both ends there.
  have hclosure : ∀ e ∈ P.E, (e ∩ D.ins F).Nonempty → closure e ⊆ D.ins F := by
    intro e he hne
    rcases edge_subset_or_disjoint_of_length hsl hc.2 hc.1 hlt' (hS.is_path.1.2 he) with h' | h'
    · exact closure_minimal h' hcl
    · obtain ⟨x, h₁, h₂⟩ := hne
      exact absurd h₂ (disjoint_left.mp h' h₁)
  constructor
  · rintro ⟨p, hpU, hpi⟩
    -- Some vertex of the spoke is in `ins(F)`.
    have hm : ∃ x ∈ K.support, x ∈ D.ins F := by
      by_cases hpV : p ∈ P.V
      · exact ⟨p, (hV p).mp hpV, hpi⟩
      · obtain ⟨e, he, hpe⟩ := P.exists_edge_of_mem hpU hpV
        obtain ⟨x, y, -, hx, -, hcap⟩ := D.exists_ends_of_mem_edges K ((hE e).mp he)
        have hxc : x ∈ closure e ∩ D.rad.G.V := by rw [hcap]; exact .inl rfl
        exact ⟨x, hx, hclosure e he ⟨p, hpe, hpi⟩ hxc.1⟩
    obtain ⟨u₁, hu₁, A, K', hK', hfirst⟩ := GraphWalk.exists_first_mem K hm
    obtain ⟨u₂, hu₂, M, B, hK'', hlast⟩ := GraphWalk.exists_last_mem K' (X
      := D.ins F) ⟨u₁, K'.start_mem_support, hu₁⟩
    subst hK''
    subst hK'
    have hMs : M.IsSimple := (GraphWalk.IsSimple.of_append (GraphWalk.IsSimple.of_append hK).2).1
    -- The part `M` of the spoke stays in `ins(F)`.
    have hMin : ∀ z ∈ M.support, z ∈ D.ins F := by
      intro z hz
      by_contra hzn
      obtain ⟨M₁, M₂, rfl⟩ := M.exists_append_of_mem hz
      have heq : A.append ((M₁.append M₂).append B) = (A.append M₁).append (M₂.append B) := by
        rw [GraphWalk.append_assoc', GraphWalk.append_assoc']
      obtain ⟨a, ha, haF⟩ := D.walk_meets_circuit hc hlt' M₁ hu₁ fun h' ↦ hzn h'.1
      obtain ⟨b, hb, hbF⟩ := D.walk_meets_circuit hc hlt' M₂.reverse hu₂ fun h' ↦ hzn h'.1
      have hb' : b ∈ (M₂.append B).support :=
        (GraphWalk.mem_support_append M₂ B).mpr (.inl (by simpa [GraphWalk.support_reverse] using
          hb))
      have ha' : a ∈ (A.append M₁).support := (GraphWalk.mem_support_append A M₁).mpr (.inr ha)
      have hzF := hS.mem_of_between hF (K₁ := A.append M₁) (K₂ := M₂.append B) (heq ▸ hK)
        (fun e ↦ by rw [← heq]; exact hE e)
        ⟨a, ha', haF⟩ ⟨b, hb', hbF⟩
      exact hzn (hU (F.V_subset_U hzF))
    refine ⟨u₁, u₂, walkDrawing D.rad.G M, ⟨walkDrawing_isSubdrawing _ _,
      walkDrawing_isPathBetween _ hMs⟩, ?_, ?_⟩
    · ext x
      rw [walkDrawing_V]
      constructor
      · intro hx
        have hx' : x ∈ M.support := hx
        refine ⟨(hV x).mpr ?_, hMin x hx'⟩
        exact (GraphWalk.mem_support_append A _).mpr (.inr ((GraphWalk.mem_support_append M B).mpr
          (.inl hx')))
      · rintro ⟨hxP, hxi⟩
        rcases (GraphWalk.mem_support_append A _).mp ((hV x).mp hxP) with h' | h'
        · rw [hfirst x h' hxi]
          exact M.start_mem_support
        · rcases (GraphWalk.mem_support_append M B).mp h' with h'' | h''
          · exact h''
          · rw [hlast x h'' hxi]
            exact M.end_mem_support
    · ext e
      rw [walkDrawing_E]
      constructor
      · intro he
        have he' : e ∈ M.edges := he
        have heP : e ∈ P.E := (hE e).mpr (by simp [GraphWalk.edges_append, he'])
        refine ⟨heP, ?_⟩
        obtain ⟨x, y, hl, M₁, M₂, rfl⟩ := GraphWalk.exists_split_edge M he'
        have hxm : x ∈ (M₁.append (GraphWalk.cons hl M₂)).support :=
          (GraphWalk.mem_support_append _ _).mpr (.inl M₁.end_mem_support)
        have hym : y ∈ (M₁.append (GraphWalk.cons hl M₂)).support :=
          (GraphWalk.mem_support_append _ _).mpr (.inr (by simp [M₂.start_mem_support]))
        by_cases hxF : x ∈ F.V
        · by_cases hyF : y ∈ F.V
          · have heq : A.append ((M₁.append (GraphWalk.cons hl M₂)).append B) =
                (A.append M₁).append ((GraphWalk.cons hl (GraphWalk.nil hl.right_mem)).append
                  (M₂.append B)) := by
              simp only [GraphWalk.append_assoc']
              rfl
            have hin := hS.subwalk_in_enclave hF (GraphWalk.cons hl (GraphWalk.nil hl.right_mem))
              (heq ▸ hK)
              (fun f ↦ by rw [← heq]; exact hE f) hxF hyF
            have heF := hin e (by simp)
            exact fun q hq ↦ hU (F.closure_subset_U heF (subset_closure hq))
          · have hl' : D.rad.G.toGraph.IsLink e y x := ⟨hl.1, hl.2.2.1, hl.2.1, by rw [hl.2.2.2,
              pair_comm]⟩
            exact (D.edge_inside_of_mem hc hlt' hl' ⟨hMin y hym, fun hu ↦ hyF
              (mem_V_of_mem_U hc.1 hu hl.right_mem)⟩).1
        · exact (D.edge_inside_of_mem hc hlt' hl ⟨hMin x hxm, fun hu ↦ hxF
            (mem_V_of_mem_U hc.1 hu hl.left_mem)⟩).1
      · rintro ⟨heP, hei⟩
        have hcl' : closure e ⊆ D.ins F := closure_minimal hei hcl
        have hK₂ := (hE e).mp heP
        simp only [GraphWalk.edges_append, List.mem_append] at hK₂
        have hends : ∀ {a b : Shat} (T : GraphWalk D.rad.G.toGraph a b), e ∈ T.edges → ∀ {c : Shat},
            (∀ x ∈ T.support, x ∈ D.ins F → x = c) → False := by
          intro a b T he' c hT
          obtain ⟨x, y, hne, hx, hy, hcap⟩ := D.exists_ends_of_mem_edges T he'
          have hxc : x ∈ closure e ∩ D.rad.G.V := by rw [hcap]; exact .inl rfl
          have hyc : y ∈ closure e ∩ D.rad.G.V := by rw [hcap]; exact .inr rfl
          exact hne ((hT x hx (hcl' hxc.1)).trans (hT y hy (hcl' hyc.1)).symm)
        rcases hK₂ with h' | h' | h'
        · exact (hends A h' hfirst).elim
        · exact h'
        · exact (hends B h' hlast).elim
  · intro hn
    by_contra hcon
    push Not at hcon
    have hvY : v ∉ D.ins F \ F.U := hcon.1
    have hhY : h ∉ D.ins F \ F.U := hcon.2
    -- No vertex of the spoke is strictly inside.
    have hnoV : ∀ x ∈ K.support, x ∈ D.ins F \ F.U → False := by
      intro x hx hxY
      obtain ⟨K₁, K₂, rfl⟩ := K.exists_append_of_mem hx
      have h₁ := D.walk_meets_circuit hc hlt' K₁.reverse hxY.1 hvY
      have h₂ := D.walk_meets_circuit hc hlt' K₂ hxY.1 hhY
      obtain ⟨a, ha, haF⟩ := h₁
      have hzF := hS.mem_of_between hF hK hE ⟨a, by simpa [GraphWalk.support_reverse] using ha,
        haF⟩ h₂
      exact hxY.2 (F.V_subset_U hzF)
    obtain ⟨p, ⟨hpU, hpi⟩, hpF⟩ := not_subset.mp hn
    by_cases hpV : p ∈ P.V
    · exact hnoV p ((hV p).mp hpV) ⟨hpi, hpF⟩
    · obtain ⟨e, he, hpe⟩ := P.exists_edge_of_mem hpU hpV
      have hcl' := hclosure e he ⟨p, hpe, hpi⟩
      obtain ⟨x, y, hl, A, B, heq⟩ := GraphWalk.exists_split_edge K ((hE e).mp he)
      have hxK : x ∈ K.support := by
        rw [heq]
        exact (GraphWalk.mem_support_append _ _).mpr (.inl A.end_mem_support)
      have hyK : y ∈ K.support := by
        rw [heq]
        exact (GraphWalk.mem_support_append _ _).mpr (.inr (by simp [B.start_mem_support]))
      have hxc : x ∈ closure e ∩ D.rad.G.V := by rw [hl.2.2.2]; exact .inl rfl
      have hyc : y ∈ closure e ∩ D.rad.G.V := by rw [hl.2.2.2]; exact .inr rfl
      have hxF : x ∈ F.V := by
        by_contra h'
        exact hnoV x hxK ⟨hcl' hxc.1, fun hu ↦ h' (mem_V_of_mem_U hc.1 hu hl.left_mem)⟩
      have hyF : y ∈ F.V := by
        by_contra h'
        exact hnoV y hyK ⟨hcl' hyc.1, fun hu ↦ h' (mem_V_of_mem_U hc.1 hu hl.right_mem)⟩
      have heq₂ : K = A.append ((GraphWalk.cons hl (GraphWalk.nil hl.right_mem)).append B) := heq
      have hin := hS.subwalk_in_enclave hF (GraphWalk.cons hl (GraphWalk.nil hl.right_mem))
        (heq₂ ▸ hK)
        (fun f ↦ by rw [← heq₂]; exact hE f) hxF hyF
      have heF := hin e (by simp)
      exact hpF ((F.closure_subset_U heF) (subset_closure hpe))

end TangleDatum

end GraphMinor.GM19
