/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Section4

/-!
# Graph Minors XI, (4.3)(iii)

This file proves (4.3)(iii): if `Γ'` is non-separable and `C` is a circuit of `Γ'` with `ins(C)`
maximal, then `ins(Γ') = ins(C)`. The paper deduces it from (4.3)(i), and leaves to the reader that
every edge of a non-separable drawing lies on a path with ends in `V(C)`. We prove this in the
classical way: in a non-separable drawing, any edge lies on a common circuit with a fixed edge
(`exists_circuit_through`).
-/

public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S]

/-- Any walk contains a simple walk with the same ends. -/
theorem GraphWalk.exists_isSimple {α : Type u} {β : Type*} {G : Graph α β}
    {u v : α} (W : GraphWalk G u v) :
    ∃ W' : GraphWalk G u v, W'.IsSimple ∧ (∀ x ∈ W'.support, x ∈ W.support) ∧
      ∀ e ∈ W'.edges, e ∈ W.edges := by
  classical
  induction W with
  | nil h => exact ⟨.nil h, by simp [GraphWalk.IsSimple], fun _ h => h, fun _ h => h⟩
  | @cons u v w e h r ih =>
    obtain ⟨R, hR, hs, he⟩ := ih
    by_cases hu : u ∈ R.support
    · obtain ⟨R₁, R₂, rfl⟩ := R.exists_append_of_mem hu
      have hR₂ : R₂.IsSimple := by
        have hn : (R₁.support ++ R₂.support.tail).Nodup := by
          have h' : (R₁.append R₂).support.Nodup := hR
          rwa [GraphWalk.support_append] at h'
        have hd := List.nodup_append.mp hn
        unfold GraphWalk.IsSimple
        rw [R₂.support_eq_cons]
        exact List.nodup_cons.mpr ⟨fun hx => hd.2.2 u R₁.end_mem_support u hx rfl, hd.2.1⟩
      refine ⟨R₂, hR₂, fun x hx => ?_, fun e' he' => ?_⟩
      · exact List.mem_cons_of_mem _ (hs x ((GraphWalk.mem_support_append _ _).mpr (Or.inr hx)))
      · refine List.mem_cons_of_mem _ (he e' ?_)
        rw [GraphWalk.edges_append]
        exact List.mem_append_right _ he'
    · refine ⟨.cons h R, List.nodup_cons.mpr ⟨hu, hR⟩, fun x hx => ?_, fun e' he' => ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · simp
        · exact List.mem_cons_of_mem _ (hs x hx)
      · rcases List.mem_cons.mp he' with rfl | he'
        · simp
        · exact List.mem_cons_of_mem _ (he _ he')

/-- A walk that ends in `A` has a first vertex in `A`. -/
theorem GraphWalk.exists_prefix {α : Type u} {β : Type*} {G : Graph α β} {u v : α}
    (W : GraphWalk G u v) (A : Set α) (hv : v ∈ A) :
    ∃ (z : α) (W' : GraphWalk G u z), z ∈ A ∧ (∀ x ∈ W'.support, x ∈ A → x = z) ∧
      (∀ x ∈ W'.support, x ∈ W.support) ∧ (∀ e ∈ W'.edges, e ∈ W.edges) ∧
      (W.IsSimple → W'.IsSimple) := by
  induction W with
  | nil h =>
    refine ⟨_, .nil h, hv, ?_, fun _ h => h, fun _ h => h, fun h => h⟩
    intro x hx _
    simpa using hx
  | @cons u v w e h r ih =>
    by_cases hu : u ∈ A
    · refine ⟨u, .nil h.left_mem, hu, ?_, ?_, ?_, ?_⟩
      · intro x hx _
        simpa using hx
      · intro x hx
        simp only [GraphWalk.support_nil, List.mem_singleton] at hx
        simp [hx]
      · simp
      · intro _
        simp [GraphWalk.IsSimple]
    · obtain ⟨z, W', hz, h₁, h₂, h₃, h₄⟩ := ih hv
      refine ⟨z, .cons h W', hz, ?_, ?_, ?_, ?_⟩
      · intro x hx hxA
        rcases List.mem_cons.mp hx with rfl | hx
        · exact absurd hxA hu
        · exact h₁ x hx hxA
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · simp
        · exact List.mem_cons_of_mem _ (h₂ x hx)
      · intro e' he'
        rcases List.mem_cons.mp he' with rfl | he'
        · simp
        · exact List.mem_cons_of_mem _ (h₃ _ he')
      · intro hs
        have hs' := List.nodup_cons.mp hs
        exact List.nodup_cons.mpr ⟨fun hx => hs'.1 (h₂ u hx), h₄ hs'.2⟩

/-- The subhypergraph of a hypergraph on a vertex set and an edge set closed under ends. -/
private def restrictHyper {α β : Type*} (G : Hypergraph α β) (V' : Set α) (E' : Set β)
    (hV : V' ⊆ G.vertexSet) (hE : E' ⊆ G.edgeSet) (hends : ∀ e ∈ E', ∀ v, G.Inc e v → v ∈ V') :
    Hypergraph α β where
  vertexSet := V'
  edgeSet := E'
  Inc e v := e ∈ E' ∧ G.Inc e v
  vertex_mem_of_inc _ _ h := hends _ h.1 _ h.2
  edge_mem_of_inc _ _ h := h.1
  vertexSet_finite := G.vertexSet_finite.subset hV
  edgeSet_finite := G.edgeSet_finite.subset hE

private theorem restrictHyper_le {α β : Type*} (G : Hypergraph α β) (V' : Set α) (E' : Set β)
    (hV : V' ⊆ G.vertexSet) (hE : E' ⊆ G.edgeSet) (hends : ∀ e ∈ E', ∀ v, G.Inc e v → v ∈ V') :
    restrictHyper G V' E' hV hE hends ≤ G := by
  refine ⟨hV, hE, fun e he => ?_⟩
  ext v
  exact ⟨fun h => ⟨he, h⟩, fun h => h.2⟩

omit [TopologicalSpace S] in
/-- Two distinct members of `{a, b}` are `a` and `b`. -/
private theorem pair_of_ne {X : Set S} {a b t v : S} (h : X = {a, b}) (ht : t ∈ X) (hv : v ∈ X)
    (hne : t ≠ v) : X = {t, v} := by
  rw [h] at ht hv ⊢
  rcases ht with rfl | ht <;> rcases hv with rfl | hv
  · exact absurd rfl hne
  · rw [mem_singleton_iff.mp hv]
  · rw [mem_singleton_iff.mp ht, pair_comm]
  · rw [mem_singleton_iff.mp ht, mem_singleton_iff.mp hv] at hne
    exact absurd rfl hne

/-- A simple walk that meets `V(D)` only in its last vertex has no edge in `D`. -/
private theorem edge_notMem_of_first {Γ' D : Drawing S} (hDs : D.IsSubdrawing Γ') {y z : S}
    (Q : GraphWalk Γ'.toGraph y z) (hQ : Q.IsSimple)
    (hfirst : ∀ x ∈ Q.support, x ∈ D.V → x = z) {e : Set S} (he : e ∈ Q.edges) : e ∉ D.E := by
  intro heD
  obtain ⟨a, b, W₁, h', W₂, rfl⟩ := exists_split_edge Q he
  have hlD : D.toGraph.IsLink e a b := (hDs.isLink_iff heD).mpr h'
  have haQ : a ∈ (W₁.append (GraphWalk.cons h' W₂)).support :=
    (GraphWalk.mem_support_append _ _).mpr (Or.inl W₁.end_mem_support)
  have hbQ : b ∈ (W₁.append (GraphWalk.cons h' W₂)).support :=
    (GraphWalk.mem_support_append _ _).mpr (Or.inr (by simp [W₂.start_mem_support]))
  have ha := hfirst a haQ hlD.2.1
  have hb := hfirst b hbQ hlD.2.2.1
  have hsplit : ((W₁.support ++ (GraphWalk.cons h' W₂).support.tail).Nodup) := by
    have h'' : (W₁.append (GraphWalk.cons h' W₂)).support.Nodup := hQ
    rwa [GraphWalk.support_append] at h''
  have hd := List.nodup_append.mp hsplit
  exact hd.2.2 a W₁.end_mem_support b W₂.start_mem_support (ha.trans hb.symm)

variable [T2Space S]

/-- The extension step: if `f` shares a vertex with an edge of a circuit `D` through `e₀`, then a
circuit passes through `e₀` and `f`. This uses that `Γ'` has no separation of order one. -/
private theorem circuit_step {Γ' D : Drawing S} (hns : Γ'.IsNonSeparable) (hD : D.IsCircuit)
    (hDs : D.IsSubdrawing Γ') {e₀ g f : Set S} (he₀ : e₀ ∈ D.E) (hg : g ∈ D.E) (hf : f ∈ Γ'.E)
    (hfD : f ∉ D.E) {x : S} (hxg : x ∈ closure g) (hxf : x ∈ closure f) (hxV : x ∈ Γ'.V) :
    ∃ D' : Drawing S, D'.IsCircuit ∧ D'.IsSubdrawing Γ' ∧ e₀ ∈ D'.E ∧ f ∈ D'.E := by
  classical
  have hxD : x ∈ D.V := by
    have : x ∈ closure g ∩ D.V := by rw [hDs.closure_inter_V hg]; exact ⟨hxg, hxV⟩
    exact this.2
  -- The other end `y` of `f`.
  obtain ⟨p, q, hpq⟩ := (Γ'.toGraph.edge_mem_iff_exists_isLink f).mp hf
  obtain ⟨y, hxy⟩ : ∃ y, Γ'.toGraph.IsLink f x y := by
    have hx : x ∈ closure f ∩ Γ'.V := ⟨hxf, hxV⟩
    rw [hpq.2.2.2] at hx
    rcases hx with rfl | hx
    · exact ⟨q, hpq⟩
    · exact ⟨p, by rw [mem_singleton_iff.mp hx]; exact hpq.symm⟩
  set T : Set S := {z | ∃ W : GraphWalk Γ'.toGraph y z, x ∉ W.support} with hT
  have hxT : x ∉ T := fun ⟨W, hW⟩ => hW W.end_mem_support
  have hmeet : ∃ z ∈ T, z ∈ D.V := by
    by_contra hcon
    push Not at hcon
    -- Otherwise the vertices reachable from `y` avoiding `x` give a separation of order one.
    have hyT : y ∈ T ∨ y = x := by
      by_cases h : y = x
      · exact Or.inr h
      · refine Or.inl ⟨.nil hxy.right_mem, ?_⟩
        simpa using fun h' : x = y => h h'.symm
    set EB : Set (Set S) := {h | h ∈ Γ'.E ∧ (h = f ∨ ∃ t ∈ T, t ∈ closure h)} with hEB
    set G := Γ'.toHypergraph with hG
    have hInc : ∀ e v, G.Inc e v ↔ e ∈ Γ'.E ∧ v ∈ Γ'.V ∧ v ∈ closure e := fun _ _ => Iff.rfl
    have hendB : ∀ e ∈ EB, ∀ v, G.Inc e v → v ∈ T ∪ {x} := by
      rintro e ⟨heE, rfl | ⟨t, ⟨W, hW⟩, hte⟩⟩ v hv
      · have hv' : v ∈ closure e ∩ Γ'.V := ⟨hv.2.2, hv.2.1⟩
        rw [hxy.2.2.2] at hv'
        rcases hv' with rfl | hv'
        · exact Or.inr rfl
        · rw [mem_singleton_iff.mp hv']
          rcases hyT with h | h
          · exact Or.inl h
          · exact Or.inr h
      · by_cases hvx : v = x
        · exact Or.inr hvx
        · refine Or.inl ?_
          by_cases hvt : v = t
          · exact hvt ▸ ⟨W, hW⟩
          obtain ⟨a, b, hab⟩ := (Γ'.toGraph.edge_mem_iff_exists_isLink e).mp heE
          have htab : t ∈ closure e ∩ Γ'.V :=
            ⟨hte, W.mem_vertexSet_of_mem_support W.end_mem_support⟩
          have hvab : v ∈ closure e ∩ Γ'.V := ⟨hv.2.2, hv.2.1⟩
          have hlink : Γ'.toGraph.IsLink e t v :=
            ⟨heE, htab.2, hvab.2, pair_of_ne hab.2.2.2 htab hvab (Ne.symm hvt)⟩
          refine ⟨W.append (.cons hlink (.nil hlink.right_mem)), ?_⟩
          intro hmem
          rcases (GraphWalk.mem_support_append _ _).mp hmem with hmem | hmem
          · exact hW hmem
          · simp only [GraphWalk.support_cons, GraphWalk.support_nil, List.mem_cons,
              List.not_mem_nil, or_false] at hmem
            rcases hmem with hmem | hmem
            · exact hW (hmem ▸ W.end_mem_support)
            · exact hvx hmem.symm
    have hEBsub : EB ⊆ G.edgeSet := fun h hh => hh.1
    have hVB : T ∪ {x} ⊆ G.vertexSet := by
      rintro z (⟨W, -⟩ | rfl)
      · exact W.mem_vertexSet_of_mem_support W.end_mem_support
      · exact hxV
    have hendA : ∀ e ∈ G.edgeSet \ EB, ∀ v, G.Inc e v → v ∈ G.vertexSet \ T := by
      rintro e ⟨heE, heB⟩ v hv
      exact ⟨hv.2.1, fun hvT => heB ⟨heE, Or.inr ⟨v, hvT, hv.2.2⟩⟩⟩
    set A := restrictHyper G (G.vertexSet \ T) (G.edgeSet \ EB) sdiff_subset sdiff_subset hendA
      with hA
    set B := restrictHyper G (T ∪ {x}) EB hVB hEBsub hendB with hB
    have hAle : A ≤ G := restrictHyper_le _ _ _ _ _ _
    have hBle : B ≤ G := restrictHyper_le _ _ _ _ _ _
    have hsep : G.IsSeparation A B := by
      refine ⟨hAle, hBle, ?_, ?_⟩
      · refine Hypergraph.ext ?_ ?_ ?_
        · ext v
          constructor
          · rintro (h | h)
            · exact h.1
            · exact hVB h
          · intro h
            by_cases hv : v ∈ T
            · exact Or.inr (Or.inl hv)
            · exact Or.inl ⟨h, hv⟩
        · ext e
          constructor
          · rintro (h | h)
            · exact h.1
            · exact h.1
          · intro h
            by_cases he : e ∈ EB
            · exact Or.inr he
            · exact Or.inl ⟨h, he⟩
        · funext e v
          apply propext
          constructor
          · rintro (h | h)
            · exact h.2
            · exact h.2
          · intro h
            by_cases he : e ∈ EB
            · exact Or.inr ⟨he, h⟩
            · exact Or.inl ⟨⟨G.edge_mem_of_inc h, he⟩, h⟩
      · ext e
        constructor
        · rintro ⟨h₁, h₂⟩
          exact h₁.2 h₂
        · exact fun h => h.elim
    have hord : separationOrder A B = 1 := by
      have : (A ∩ B).vertexSet = {x} := by
        ext v
        constructor
        · rintro ⟨h₁, h₂ | h₂⟩
          · exact absurd h₂ h₁.2
          · exact h₂
        · rintro rfl
          exact ⟨⟨hxV, hxT⟩, Or.inr rfl⟩
      rw [separationOrder, this, ncard_singleton]
    refine hns.2 A B hsep hord ⟨g, hDs.2 hg, ?_⟩ ⟨f, hf, Or.inl rfl⟩
    rintro ⟨-, hgf | ⟨t, ht, htg⟩⟩
    · exact hfD (hgf ▸ hg)
    · have : t ∈ closure g ∩ D.V := by
        rw [hDs.closure_inter_V hg]
        obtain ⟨W, -⟩ := ht
        exact ⟨htg, W.mem_vertexSet_of_mem_support W.end_mem_support⟩
      exact hcon t ht this.2
  obtain ⟨z₀, ⟨W₀, hW₀⟩, hz₀⟩ := hmeet
  obtain ⟨W₁, hW₁, hs₁, -⟩ := GraphWalk.exists_isSimple W₀
  obtain ⟨z, Q, hzD, hfirst, hsQ, heQ, hQs⟩ := GraphWalk.exists_prefix W₁ D.V hz₀
  have hQ : Q.IsSimple := hQs hW₁
  have hxQ : x ∉ Q.support := fun h => hW₀ (hs₁ x (hsQ x h))
  have hzx : x ≠ z := fun h => hxQ (h ▸ Q.end_mem_support)
  have hRs : (GraphWalk.cons hxy Q).IsSimple := List.nodup_cons.mpr ⟨hxQ, hQ⟩
  have hPs := walkDrawing_isSubdrawing Γ' (GraphWalk.cons hxy Q)
  have hPp : (walkDrawing Γ' (GraphWalk.cons hxy Q)).IsPathBetween x z :=
    walkDrawing_isPathBetween Γ' hRs
  have hPV := walkDrawing_V Γ' (GraphWalk.cons hxy Q)
  have hPE := walkDrawing_E Γ' (GraphWalk.cons hxy Q)
  obtain ⟨P₁, P₂, hP₁, hP₂, hP₁s, hP₂s, -, -, hV₁₂, -, hsup⟩ := hD.exists_two_paths hxD hzD hzx
  have hkey : ∀ P' : Drawing S, P'.IsPathBetween x z → P'.IsSubdrawing D → x ∈ P'.V → z ∈ P'.V →
      e₀ ∈ P'.E →
      ∃ D' : Drawing S, D'.IsCircuit ∧ D'.IsSubdrawing Γ' ∧ e₀ ∈ D'.E ∧ f ∈ D'.E := by
    intro P' hP' hP's hxP' hzP' he₀P'
    have hP'' := hP's.trans hDs
    have hV : (walkDrawing Γ' (GraphWalk.cons hxy Q)).V ∩ P'.V = {x, z} := by
      ext v
      constructor
      · rintro ⟨h₁, h₂⟩
        rw [hPV] at h₁
        rcases List.mem_cons.mp h₁ with rfl | h₁
        · exact Or.inl rfl
        · exact Or.inr (hfirst v h₁ (hP's.1 h₂))
      · rintro (rfl | hv)
        · refine ⟨?_, hxP'⟩
          rw [hPV]
          exact GraphWalk.start_mem_support _
        · rw [mem_singleton_iff.mp hv]
          refine ⟨?_, hzP'⟩
          rw [hPV]
          exact GraphWalk.end_mem_support _
    have hE : Disjoint (walkDrawing Γ' (GraphWalk.cons hxy Q)).E P'.E := by
      refine disjoint_left.mpr fun e he heP' => ?_
      rw [hPE] at he
      have heD : e ∈ D.E := hP's.2 heP'
      rcases List.mem_cons.mp he with rfl | he
      · exact hfD heD
      · exact edge_notMem_of_first hDs Q hQ hfirst he heD
    refine ⟨Γ'.sup _ P', Drawing.isCircuit_sup hPp hP' hPs hP'' hzx hV hE,
      Drawing.sup_isSubdrawing _ _ _, ?_, ?_⟩
    · rw [Drawing.sup_E hPs hP'']
      exact Or.inr he₀P'
    · rw [Drawing.sup_E hPs hP'', hPE]
      exact Or.inl (by simp)
  have hxz : x ∈ P₁.V ∩ P₂.V ∧ z ∈ P₁.V ∩ P₂.V := by rw [hV₁₂]; simp
  have he₀' : e₀ ∈ P₁.E ∪ P₂.E := by
    have : e₀ ∈ (D.sup P₁ P₂).E := by rw [hsup]; exact he₀
    rwa [Drawing.sup_E hP₁s hP₂s] at this
  rcases he₀' with h | h
  · exact hkey P₁ hP₁ hP₁s hxz.1.1 hxz.2.1 h
  · exact hkey P₂ hP₂ hP₂s hxz.1.2 hxz.2.2 h

/-- Graph theory of non-separable drawings: every edge lies on a circuit with a fixed edge of a
given circuit. -/
theorem exists_circuit_through {Γ' C : Drawing S} (hns : Γ'.IsNonSeparable) (hC : C.IsCircuit)
    (hCs : C.IsSubdrawing Γ') {e₀ f : Set S} (he₀ : e₀ ∈ C.E) (hf : f ∈ Γ'.E) :
    ∃ D : Drawing S, D.IsCircuit ∧ D.IsSubdrawing Γ' ∧ e₀ ∈ D.E ∧ f ∈ D.E := by
  classical
  set Y : Set S := {v | ∃ D : Drawing S, D.IsCircuit ∧ D.IsSubdrawing Γ' ∧ e₀ ∈ D.E ∧ v ∈ D.V}
    with hY
  -- An edge at a vertex of `Y` lies on a circuit through `e₀`.
  have hstep : ∀ {v : S} {h : Set S}, v ∈ Y → h ∈ Γ'.E → v ∈ closure h →
      ∃ D : Drawing S, D.IsCircuit ∧ D.IsSubdrawing Γ' ∧ e₀ ∈ D.E ∧ h ∈ D.E := by
    rintro v h ⟨D, hD, hDs, he, hv⟩ hh hvh
    by_cases hhD : h ∈ D.E
    · exact ⟨D, hD, hDs, he, hhD⟩
    obtain ⟨W, -, hpos, -, hE⟩ := exists_walk_at hD hv
    cases W with
    | nil _ => simp at hpos
    | @cons _ w _ g hl r =>
      have hg : g ∈ D.E := hl.1
      have hvg : v ∈ closure g := by
        have : v ∈ closure g ∩ D.V := by rw [hl.2.2.2]; simp
        exact this.1
      exact circuit_step hns hD hDs he hg hh hhD hvg hvh (hDs.1 hv)
  -- Walks starting in `Y` stay in `Y`.
  have hwalk : ∀ {a b : S} (W : GraphWalk Γ'.toGraph a b), a ∈ Y → b ∈ Y := by
    intro a b W
    induction W with
    | nil _ => exact id
    | @cons a v b e hl r ih =>
      intro ha
      refine ih ?_
      have hae : a ∈ closure e := by
        have : a ∈ closure e ∩ Γ'.V := by rw [hl.2.2.2]; simp
        exact this.1
      obtain ⟨D, hD, hDs, he, heD⟩ := hstep ha hl.1 hae
      exact ⟨D, hD, hDs, he, ((hDs.isLink_iff heD).mpr hl).2.2.1⟩
  obtain ⟨a, _, hal⟩ := (C.toGraph.edge_mem_iff_exists_isLink e₀).mp he₀
  have haY : a ∈ Y := ⟨C, hC, hCs, he₀, hal.2.1⟩
  obtain ⟨b, c, hbc⟩ := (Γ'.toGraph.edge_mem_iff_exists_isLink f).mp hf
  obtain ⟨W⟩ := hns.1.2 a (hCs.1 hal.2.1) b hbc.2.1
  have hb : b ∈ closure f := by
    have : b ∈ closure f ∩ Γ'.V := by rw [hbc.2.2.2]; simp
    exact this.1
  exact hstep (hwalk W haY) hf hb

/-- Graph Minors XI, (4.3)(iii) (page 79): "if $\Gamma'$ is non-separable then $\text{ins}(\Gamma')
= \text{ins}(C)$". The
hypotheses are those of (4.3): `Γ'` is confined and `ins(C)` is maximal. -/
theorem theorem_4_3_iii {Γ Γ' C : Drawing S} {k : ℕ} {ins : Drawing S → Set S}
    (hs : IsSlope Γ k ins) (hsub : Γ'.IsSubdrawing Γ) (hconf : IsConfined k Γ')
    (hC : C.IsCircuit) (hCs : C.IsSubdrawing Γ')
    (hmax : ∀ C' : Drawing S, C'.IsCircuit → C'.IsSubdrawing Γ' → ins C ⊆ ins C' → ins C' ⊆ ins C)
    (hns : Γ'.IsNonSeparable) : insOf ins Γ' = ins C := by
  have hs' := theorem_4_2_proof hs hsub
  have hCl := hconf C hC hCs
  have hUC := hs'.U_subset_ins hC hCs hCl
  obtain ⟨e₀, he₀⟩ : C.E.Nonempty := by
    obtain ⟨u, W, -, hpos, -, hE⟩ := hC
    cases W with
    | nil _ => simp at hpos
    | @cons _ w _ e h r => exact ⟨e, h.1⟩
  -- Every edge of `Γ'` lies in `ins(C)`.
  have hedge : ∀ f ∈ Γ'.E, closure f ⊆ ins C := by
    intro f hf
    obtain ⟨D, hD, hDs, he₀D, hfD⟩ := exists_circuit_through hns hC hCs he₀ hf
    obtain ⟨a, b, hab⟩ := (D.toGraph.edge_mem_iff_exists_isLink e₀).mp he₀D
    have hlC : C.toGraph.IsLink e₀ a b :=
      (hCs.isLink_iff he₀).mpr ((hDs.isLink_iff he₀D).mp hab)
    by_cases hne : a = b
    · -- `e₀` is a loop, so `D` has no other edge.
      subst hne
      have hE₁ : D.E = {e₀} := IsCircuit.E_eq_of_loop hD he₀D (by simpa using hab.2.2.2)
      have hfe : f = e₀ := by rw [hE₁] at hfD; exact hfD
      subst hfe
      exact (C.closure_subset_U he₀).trans hUC
    · obtain ⟨P, Q, hP, hQ, hPs, hQs, -, -, -, -, hsup⟩ := hD.exists_two_paths hab.2.1 hab.2.2.1 hne
      have hP' : P.U ⊆ ins C := path_U_subset hP (hPs.trans hDs) fun hW =>
        theorem_4_3_i hs hsub hconf hC hCs hmax _ hW hlC.2.1 hlC.2.2.1
      have hQ' : Q.U ⊆ ins C := path_U_subset hQ (hQs.trans hDs) fun hW =>
        theorem_4_3_i hs hsub hconf hC hCs hmax _ hW hlC.2.1 hlC.2.2.1
      have hfPQ : f ∈ P.E ∪ Q.E := by
        have : f ∈ (D.sup P Q).E := by rw [hsup]; exact hfD
        rwa [Drawing.sup_E hPs hQs] at this
      rcases hfPQ with h | h
      · exact (P.closure_subset_U h).trans hP'
      · exact (Q.closure_subset_U h).trans hQ'
  -- Every vertex of `Γ'` lies in `ins(C)`.
  have hvertex : ∀ v ∈ Γ'.V, v ∈ ins C := by
    intro v hv
    obtain ⟨a, hal⟩ : C.V.Nonempty := by
      obtain ⟨u, W, -, -, hV, -⟩ := hC
      exact ⟨u, by rw [hV]; exact W.start_mem_support⟩
    obtain ⟨W⟩ := hns.1.2 v hv a (hCs.1 hal)
    cases W with
    | nil _ => exact hUC (C.V_subset_U hal)
    | @cons _ w _ e h r =>
      refine hedge e h.1 ?_
      have : v ∈ closure e ∩ Γ'.V := by rw [h.2.2.2]; simp
      exact this.1
  have hU : Γ'.U ⊆ ins C := by
    rw [Γ'.U_eq]
    exact union_subset hvertex (iUnion₂_subset hedge)
  apply subset_antisymm
  · refine union_subset hU (iUnion₂_subset ?_)
    rintro C' ⟨hC', hC's⟩
    exact hs'.monotone C' C hC' hC's (hconf C' hC' hC's) hC hCs hCl (hC's.U_subset.trans hU)
  · exact (subset_biUnion_of_mem (u := ins)
      (show C ∈ {C : Drawing S | C.IsCircuit ∧ C.IsSubdrawing Γ'} from ⟨hC, hCs⟩)).trans
      subset_union_right

/-- Graph Minors XI, (4.3) (page 79): "Let $\Gamma'$ be a confined subdrawing of $\Gamma$, and let
$C$ be a circuit of $\Gamma'$ with $\text{ins}(C)$ maximal. Then
(i) $U(P) \subseteq \text{ins}(C)$ for every path $P$ of $\Gamma'$ with both ends in $V(C)$,
(ii) for every edge $e$ of $C$, $\Gamma'$ does not capture the region of $\Gamma$ incident with $e$
not included in $\text{ins}(C)$, and
(iii) if $\Gamma'$ is non-separable then $\text{ins}(\Gamma') = \text{ins}(C)$." -/
theorem theorem_4_3_proof {Γ Γ' C : Drawing S} {k : ℕ} {ins : Drawing S → Set S}
    (hs : IsSlope Γ k ins) (hsub : Γ'.IsSubdrawing Γ) (hconf : IsConfined k Γ')
    (hC : C.IsCircuit) (hCs : C.IsSubdrawing Γ')
    (hmax : ∀ C' : Drawing S, C'.IsCircuit → C'.IsSubdrawing Γ' → ins C ⊆ ins C' → ins C' ⊆ ins C) :
    (∀ (P : Drawing S) (a b : S), P.IsPathBetween a b → P.IsSubdrawing Γ' →
      a ∈ C.V → b ∈ C.V → P.U ⊆ ins C) ∧
    (∀ e r : Set S, e ∈ C.E → (e ∩ closure r).Nonempty → ¬ r ⊆ ins C →
      ¬ Captures ins k Γ' r) ∧
    (Γ'.IsNonSeparable → insOf ins Γ' = ins C) :=
  ⟨fun _ _ _ hP hPs ha hb =>
    path_U_subset hP hPs fun hW => theorem_4_3_i hs hsub hconf hC hCs hmax _ hW ha hb,
   fun _ _ he hinc hnot => theorem_4_3_ii hs hsub hconf hC hCs hmax he hinc hnot,
   theorem_4_3_iii hs hsub hconf hC hCs hmax⟩

end GraphMinor.GM11
