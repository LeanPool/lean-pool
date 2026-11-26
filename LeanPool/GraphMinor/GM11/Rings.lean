/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.EvenCircuit

/-!
# Rings

The proof of (5.4) in Graph Minors XI (pages 82–83) studies the circuits of `N(Z₁)` with `ins(C)`
maximal, called `Z₁`-rings, and a forest `G` that records how they meet. We need only one thing from
`G`: a ring that meets the rest in at most one vertex, statement (1) of the proof, and a second such
ring if there are two rings. We get these without the forest, by choosing a ring and a vertex `v` of
it so that the set of vertices reached from the ring without passing through `v` is smallest.

This file works in a confined subdrawing `N` with a slope. `path_mem_ins` is the form of (4.3)(i)
that the paper uses: a path with both ends in `ins(C)` stays there.
-/

@[expose] public section

namespace GraphMinor.GM11

open Set Topology GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S] [T2Space S] {N : Drawing S} {k : ℕ}
  {ins : Drawing S → Set S}

/-- A *ring* of `N` (Graph Minors XI, proof of (5.4), page 82): "a circuit $C$ of $N(Z_1)$ chosen
with $\operatorname{ins}(C)$ maximal". -/
def IsRing (ins : Drawing S → Set S) (N C : Drawing S) : Prop :=
  C.IsCircuit ∧ C.IsSubdrawing N ∧
    ∀ C' : Drawing S, C'.IsCircuit → C'.IsSubdrawing N → ins C ⊆ ins C' → ins C' ⊆ ins C

omit [T2Space S] in
/-- Above each circuit lies a ring. -/
theorem exists_ring_above (ins : Drawing S → Set S) {D : Drawing S} (hD : D.IsCircuit)
    (hDs : D.IsSubdrawing N) : ∃ C, IsRing ins N C ∧ ins D ⊆ ins C := by
  let 𝓒 : Set (Drawing S) := {C | C.IsCircuit ∧ C.IsSubdrawing N}
  have hfin : 𝓒.Finite := by
    refine Set.Finite.of_finite_image (f := fun C : Drawing S => (C.V, C.E)) ?_ ?_
    · refine (N.finite_V.finite_subsets.prod N.finite_edges.finite_subsets).subset ?_
      rintro _ ⟨C, ⟨-, hs⟩, rfl⟩
      exact ⟨hs.1, hs.2⟩
    · intro C _ D _ h
      exact Drawing.ext_of_V_E (congrArg Prod.fst h) (congrArg Prod.snd h)
  obtain ⟨X, hle, hX⟩ := (hfin.image ins).exists_le_maximal (a := ins D) ⟨D, ⟨hD, hDs⟩, rfl⟩
  obtain ⟨C, ⟨hC, hCs⟩, rfl⟩ := hX.1
  exact ⟨C, ⟨hC, hCs, fun C' hC' hC's h => hX.2 ⟨C', ⟨hC', hC's⟩, rfl⟩ h⟩, hle⟩

/-- What the disc `ins(C)` gives. -/
theorem ins_facts_of_length (hs : IsSlope N k ins) {C : Drawing S} (hC : C.IsCircuit)
    (hCs : C.IsSubdrawing N) (hl : C.length < k) :
    IsClosed (ins C) ∧ frontier (ins C) = C.U ∧ C.U ⊆ ins C := by
  have hcl : IsClosed (ins C) := (hs.isClosedDisc C hC hCs hl).isClosed
  have hfr : frontier (ins C) = C.U := by rw [subBd_eq_frontier', hs.subBd_eq C hC hCs hl]
  exact ⟨hcl, hfr, hs.U_subset_ins hC hCs hl⟩

/-- An edge lies in `ins(C)` or misses it. -/
theorem edge_subset_or_disjoint_of_length (hs : IsSlope N k ins) {C : Drawing S} (hC : C.IsCircuit)
    (hCs : C.IsSubdrawing N) (hl : C.length < k) {f : Set S} (hf : f ∈ N.E) : f ⊆ ins C
      ∨ Disjoint f (ins C) := by
  obtain ⟨hcl, hfr, hU⟩ := ins_facts_of_length hs hC hCs hl
  by_cases hfC : f ∈ C.E
  · exact Or.inl (fun x hx => hU (hfC.2.1 hx).1)
  by_cases hmeet : (f ∩ ins C).Nonempty
  · left
    obtain ⟨x, hxf, hxi⟩ := hmeet
    have hdis : Disjoint f (frontier (ins C)) := by
      rw [hfr]
      refine disjoint_left.mpr fun y hy hyU => hfC ?_
      have hyV : y ∉ C.V := fun h => (hf.2.1 hy).2 (hCs.1 h)
      obtain ⟨g, hg, hyg⟩ := C.exists_edge_of_mem hyU hyV
      rw [N.edge_eq_of_mem hf (hCs.2 hg) hy hyg]
      exact hg
    have hcov : f ⊆ interior (ins C) ∪ (ins C)ᶜ := by
      intro y hy
      by_cases hyi : y ∈ ins C
      · refine Or.inl ?_
        by_contra h
        exact disjoint_left.mp hdis hy ⟨subset_closure hyi, h⟩
      · exact Or.inr hyi
    have hxin : x ∈ interior (ins C) :=
      (hcov hxf).resolve_right fun h => h hxi
    intro y hy
    by_contra hyi
    have hconn : IsPreconnected f :=
      (show IsPathConnected f from hf.2.2.1).isConnected.isPreconnected
    obtain ⟨z, -, hz₁, hz₂⟩ := hconn _ _ isOpen_interior hcl.isOpen_compl hcov ⟨x, hxf, hxin⟩
      ⟨y, hy, hyi⟩
    exact hz₂ (interior_subset hz₁)
  · exact Or.inr (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hmeet))

section Slope

variable (hs : IsSlope N k ins) (hconf : IsConfined k N)
include hs hconf

/-- What the disc `ins(C)` gives. -/
theorem ins_facts {C : Drawing S} (hC : C.IsCircuit) (hCs : C.IsSubdrawing N) :
    IsClosed (ins C) ∧ frontier (ins C) = C.U ∧ C.U ⊆ ins C :=
  ins_facts_of_length hs hC hCs (hconf C hC hCs)

/-- An edge lies in `ins(C)` or misses it. -/
theorem edge_subset_or_disjoint {C : Drawing S} (hC : C.IsCircuit) (hCs : C.IsSubdrawing N)
    {f : Set S} (hf : f ∈ N.E) : f ⊆ ins C ∨ Disjoint f (ins C) :=
  edge_subset_or_disjoint_of_length hs hC hCs (hconf C hC hCs) hf

/-- A vertex in `ins(C)` at the end of an edge outside lies on `C`. -/
theorem mem_V_of_outside_edge {C : Drawing S} (hC : C.IsCircuit) (hCs : C.IsSubdrawing N)
    {f : Set S} (hdis : Disjoint f (ins C)) {x : S} (hxV : x ∈ N.V)
    (hxf : x ∈ closure f) (hxi : x ∈ ins C) : x ∈ C.V := by
  obtain ⟨hcl, hfr, -⟩ := ins_facts hs hconf hC hCs
  have hfrx : x ∈ frontier (ins C) := by
    rw [frontier_eq_closure_inter_closure]
    exact ⟨subset_closure hxi, closure_mono (fun y hy => disjoint_left.mp hdis hy) hxf⟩
  rw [hfr] at hfrx
  by_contra h
  obtain ⟨g, hg, hxg⟩ := C.exists_edge_of_mem hfrx h
  exact ((hCs.2 hg).2.1 hxg).2 hxV

/-- If a walk leaves `ins(C)` and first returns at `z`, it arrives by an edge outside. -/
theorem exists_exit_edge {C : Drawing S} (hC : C.IsCircuit) (hCs : C.IsSubdrawing N) {p z : S}
    (W : GraphWalk N.toGraph p z) (hp : p ∉ ins C) (hz : z ∈ ins C)
    (huniq : ∀ x ∈ W.support, x ∈ ins C → x = z) :
    ∃ f ∈ N.E, z ∈ closure f ∧ Disjoint f (ins C) := by
  induction W with
  | nil h => exact absurd hz hp
  | @cons a y b e hl r ih =>
    have huniq' : ∀ x ∈ r.support, x ∈ ins C → x = b := fun x hx => huniq x
      (List.mem_cons_of_mem _ hx)
    have hedge : e ∈ N.E := hl.1
    have hcase : Disjoint e (ins C) := by
      refine (edge_subset_or_disjoint hs hconf hC hCs hedge).resolve_left fun h => hp ?_
      have ha : a ∈ closure e := by
        have : a ∈ closure e ∩ N.V := by rw [hl.2.2.2]; simp
        exact this.1
      exact (ins_facts hs hconf hC hCs).1.closure_subset_iff.mpr h ha
    by_cases hy : y ∈ ins C
    · have hyb : y = b := huniq' y r.start_mem_support hy
      subst hyb
      have hy' : y ∈ closure e := by
        have : y ∈ closure e ∩ N.V := by rw [hl.2.2.2]; simp
        exact this.1
      exact ⟨e, hedge, hy', hcase⟩
    · exact ih hy hz huniq'

/-- The form of (4.3)(i) that the paper uses: for a ring `C`, a path of `N` with both ends in
`ins(C)`
stays in `ins(C)`. -/
theorem path_mem_ins {C : Drawing S} (hC : IsRing ins N C) {a b : S} (W : GraphWalk N.toGraph a b)
    (hW : W.IsSimple) (ha : a ∈ ins C) (hb : b ∈ ins C) :
    (∀ x ∈ W.support, x ∈ ins C) ∧ ∀ e ∈ W.edges, e ⊆ ins C := by
  obtain ⟨hcirc, hCs, hmax⟩ := hC
  obtain ⟨hcl, hfr, hUC⟩ := ins_facts hs hconf hcirc hCs
  induction W with
  | nil h =>
    refine ⟨fun x hx => ?_, fun e he => absurd he List.not_mem_nil⟩
    rw [GraphWalk.support_nil, List.mem_singleton] at hx
    rw [hx]
    exact ha
  | @cons a v b e hl r ih =>
    have hr : r.IsSimple := GraphWalk.IsSimple.of_cons hW
    have hedge : e ∈ N.E := hl.1
    have hae : a ∈ closure e := by
      have : a ∈ closure e ∩ N.V := by rw [hl.2.2.2]; simp
      exact this.1
    have hve : v ∈ closure e := by
      have : v ∈ closure e ∩ N.V := by rw [hl.2.2.2]; simp
      exact this.1
    rcases edge_subset_or_disjoint hs hconf hcirc hCs hedge with hsub | hdis
    · have hv : v ∈ ins C := hcl.closure_subset_iff.mpr hsub hve
      obtain ⟨h₁, h₂⟩ := ih hr hv hb
      refine ⟨fun x hx => ?_, fun f hf => ?_⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact ha
        · exact h₁ x hx
      · rcases List.mem_cons.mp hf with rfl | hf
        · exact hsub
        · exact h₂ f hf
    · exfalso
      have haC : a ∈ C.V := mem_V_of_outside_edge hs hconf hcirc hCs hdis hl.2.1 hae ha
      obtain ⟨z, W', hzA, huniq, hsup, -, hsimple⟩ := GraphWalk.exists_prefix r (ins C) hb
      have hzC : z ∈ C.V := by
        by_cases hv : v ∈ ins C
        · have hvz : v = z := huniq v W'.start_mem_support hv
          subst hvz
          exact mem_V_of_outside_edge hs hconf hcirc hCs hdis hl.2.2.1 hve hv
        · obtain ⟨f, hf, hzf, hdisf⟩ := exists_exit_edge hs hconf hcirc hCs W' hv hzA huniq
          have hzV : z ∈ N.V := W'.mem_vertexSet_of_mem_support W'.end_mem_support
          exact mem_V_of_outside_edge hs hconf hcirc hCs hdisf hzV hzf hzA
      have hT : (GraphWalk.cons hl W').IsSimple := by
        refine List.nodup_cons.mpr ⟨fun h => ?_, hsimple hr⟩
        exact (List.nodup_cons.mp hW).1 (hsup a h)
      have hU := theorem_4_3_i hs (Drawing.IsSubdrawing.refl N) hconf hcirc hCs hmax
        (GraphWalk.cons hl W') hT haC hzC
      obtain ⟨x, hx⟩ := (show e ∈ N.E from hedge).1
      have hxU : x ∈ (walkDrawing N (GraphWalk.cons hl W')).U :=
        (mem_walkDrawing_U N _).mpr (Or.inr ⟨e, List.mem_cons_self, subset_closure hx⟩)
      exact disjoint_left.mp hdis hx (hU hxU)

/-- If a circuit `D` of `N` has two vertices in `ins(C)` for a ring `C`, then `U(D) ⊆ ins(C)`
(Graph Minors XI, proof of (5.4), page 82). -/
theorem circuit_U_subset {C D : Drawing S} (hC : IsRing ins N C) (hD : D.IsCircuit)
    (hDs : D.IsSubdrawing N) {a b : S} (ha : a ∈ D.V) (hb : b ∈ D.V) (hab : a ≠ b)
    (hai : a ∈ ins C) (hbi : b ∈ ins C) : D.U ⊆ ins C := by
  have hcl := (ins_facts hs hconf hC.1 hC.2.1).1
  obtain ⟨P, Q, hP, hQ, hPs, hQs, -, -, -, -, hsup⟩ := hD.exists_two_paths ha hb hab
  have hkey : ∀ R : Drawing S, R.IsPathBetween a b → R.IsSubdrawing D →
      (∀ x ∈ R.V, x ∈ ins C) ∧ ∀ e ∈ R.E, e ⊆ ins C := by
    rintro R ⟨W, hW, hV, hE⟩ hR
    obtain ⟨W', hs', he'⟩ := (hR.trans hDs).exists_walk_up W
    have hW' : W'.IsSimple := by
      unfold GraphWalk.IsSimple
      rw [hs']
      exact hW
    obtain ⟨h₁, h₂⟩ := path_mem_ins hs hconf hC W' hW' hai hbi
    refine ⟨fun x hx => h₁ x ?_, fun e he => h₂ e ?_⟩
    · rw [hV] at hx
      rw [hs']
      exact hx
    · rw [hE] at he
      rw [he']
      exact he
  obtain ⟨p₁, p₂⟩ := hkey P hP hPs
  obtain ⟨q₁, q₂⟩ := hkey Q hQ hQs
  rw [D.U_eq]
  refine union_subset ?_ (iUnion₂_subset fun e he => hcl.closure_subset_iff.mpr ?_)
  · intro x hx
    rw [← hsup, Drawing.sup_V hPs hQs] at hx
    exact hx.elim (p₁ x) (q₁ x)
  · rw [← hsup, Drawing.sup_E hPs hQs] at he
    exact he.elim (p₂ e) (q₂ e)

/-- Two rings with `U(C') ⊆ ins(C)` are equal. -/
theorem ring_eq_of_U_subset {C C' : Drawing S} (hC : IsRing ins N C) (hC' : IsRing ins N C')
    (hU : C'.U ⊆ ins C) : C' = C := by
  have hle := hs.monotone C' C hC'.1 (hC'.2.1.trans (Drawing.IsSubdrawing.refl N))
    (hconf _ hC'.1 hC'.2.1) hC.1 hC.2.1 (hconf _ hC.1 hC.2.1) hU
  have hge := hC'.2.2 C hC.1 hC.2.1 hle
  have heq : ins C' = ins C := subset_antisymm hle hge
  have hUU : C'.U = C.U := by
    rw [← (ins_facts hs hconf hC'.1 hC'.2.1).2.1, ← (ins_facts hs hconf hC.1 hC.2.1).2.1, heq]
  have hV : ∀ {A B : Drawing S}, A.IsSubdrawing N → B.IsSubdrawing N → A.U = B.U → A.V ⊆ B.V := by
    intro A B hA hB hAB x hx
    by_contra h
    have hxU : x ∈ B.U := hAB ▸ A.V_subset_U hx
    obtain ⟨g, hg, hxg⟩ := B.exists_edge_of_mem hxU h
    exact ((hB.2 hg).2.1 hxg).2 (hA.1 hx)
  have hE : ∀ {A B : Drawing S}, A.IsSubdrawing N → B.IsSubdrawing N → A.U = B.U → A.E ⊆ B.E := by
    intro A B hA hB hAB e he
    obtain ⟨x, hx⟩ := he.1
    have hxU : x ∈ B.U := hAB ▸ (he.2.1 hx).1
    have hxV : x ∉ B.V := fun h => ((hA.2 he).2.1 hx).2 (hB.1 h)
    obtain ⟨g, hg, hxg⟩ := B.exists_edge_of_mem hxU hxV
    rw [N.edge_eq_of_mem (hA.2 he) (hB.2 hg) hx hxg]
    exact hg
  exact Drawing.ext_of_V_E (subset_antisymm (hV hC'.2.1 hC.2.1 hUU) (hV hC.2.1 hC'.2.1 hUU.symm))
    (subset_antisymm (hE hC'.2.1 hC.2.1 hUU) (hE hC.2.1 hC'.2.1 hUU.symm))

/-- Distinct rings share at most one vertex (Graph Minors XI, proof of (5.4), page 82). -/
theorem ring_inter_le_one {C C' : Drawing S} (hC : IsRing ins N C) (hC' : IsRing ins N C')
    (hne : C' ≠ C) {a b : S} (ha : a ∈ C'.V) (hb : b ∈ C'.V) (hai : a ∈ ins C) (hbi : b ∈ ins C) :
    a = b := by
  by_contra hab
  exact hne (ring_eq_of_U_subset hs hconf hC hC' (circuit_U_subset hs hconf hC hC'.1 hC'.2.1 ha hb
    hab
    hai hbi))

/-- If a vertex `w` of a ring `C'` lies in `ins(C)` for another ring `C`, then `w` lies on `C`, and
an
edge of `C'` at `w` lies outside `ins(C)`. -/
theorem ring_vertex_in_ins {C C' : Drawing S} (hC : IsRing ins N C) (hC' : IsRing ins N C')
    (hne : C' ≠ C) {w : S} (hw : w ∈ C'.V) (hwi : w ∈ ins C) :
    w ∈ C.V ∧ ∃ g ∈ C'.E, w ∈ closure g ∧ Disjoint g (ins C) := by
  have hcl := (ins_facts hs hconf hC.1 hC.2.1).1
  obtain ⟨W, ⟨hnd, hed⟩, hpos, hV, hE⟩ := exists_walk_at hC'.1 hw
  cases W with
  | nil h => simp [GraphWalk.length, GraphWalk.edges] at hpos
  | @cons a y b g hl r =>
    have hgN : g ∈ C'.E := by rw [hE]; exact List.mem_cons_self
    have hgN' : g ∈ N.E := hC'.2.1.2 hgN
    have hcap : closure g ∩ C'.V = {w, y} := hl.2.2.2
    have hwg : w ∈ closure g := by
      have : w ∈ closure g ∩ C'.V := by rw [hcap]; simp
      exact this.1
    have hyg : y ∈ closure g ∩ C'.V := by rw [hcap]; simp
    rcases edge_subset_or_disjoint hs hconf hC.1 hC.2.1 hgN' with hsub | hdis
    · exfalso
      have hyi : y ∈ ins C := hcl.closure_subset_iff.mpr hsub hyg.1
      have hwy : w = y := ring_inter_le_one hs hconf hC hC' hne hw hyg.2 hwi hyi
      subst hwy
      -- A loop is the whole of `C'`.
      have hr : r.IsSimple := hnd
      have hlen := GraphWalk.IsSimple.length_eq_zero hr
      have hsup : r.support = [w] := by
        cases r with
        | nil _ => rfl
        | cons _ _ => simp [GraphWalk.length, GraphWalk.edges] at hlen
      have hred : r.edges = [] := by
        cases r with
        | nil _ => rfl
        | cons _ _ => simp [GraphWalk.length, GraphWalk.edges] at hlen
      apply hne
      refine ring_eq_of_U_subset hs hconf hC hC' ?_
      rw [C'.U_eq]
      refine union_subset ?_ (iUnion₂_subset fun e he => ?_)
      · intro x hx
        rw [hV] at hx
        have : x = w := by
          have hsupp : x ∈ w :: r.support := hx
          rw [hsup] at hsupp
          simpa using hsupp
        exact this ▸ hwi
      · rw [hE] at he
        have : e = g := by
          have hee : e ∈ g :: r.edges := he
          rw [hred] at hee
          simpa using hee
        rw [this]
        exact hcl.closure_subset_iff.mpr hsub
    · exact ⟨mem_V_of_outside_edge hs hconf hC.1 hC.2.1 hdis (hC'.2.1.1 hw) hwg hwi,
        g, hgN, hwg, hdis⟩

end Slope

omit [TopologicalSpace S] [T2Space S] in
theorem mem_support_nil {G : Graph S (Set S)} {a x : S} {h : a ∈ G.vertexSet} :
    x ∈ (GraphWalk.nil h).support ↔ x = a := by
  simp [GraphWalk.support_nil]

omit [T2Space S] in
/-- Joining two simple walks that share only the joint gives a simple walk. -/
theorem isSimple_append' {a x b : S} {W₁ : GraphWalk N.toGraph a x} {W₂ : GraphWalk N.toGraph x b}
    (h₁ : W₁.IsSimple) (h₂ : W₂.IsSimple) (hdis : ∀ y ∈ W₁.support, y ∈ W₂.support → y = x) :
    (W₁.append W₂).IsSimple := by
  unfold GraphWalk.IsSimple
  rw [GraphWalk.support_append]
  have h₂' : W₂.support = x :: W₂.support.tail := W₂.support_eq_cons
  have hnd : (x :: W₂.support.tail).Nodup := h₂' ▸ h₂
  refine List.nodup_append.mpr ⟨h₁, (List.nodup_cons.mp hnd).2, ?_⟩
  rintro y hy z hz rfl
  have := hdis y hy (h₂' ▸ List.mem_cons_of_mem _ hz)
  exact (List.nodup_cons.mp hnd).1 (this ▸ hz)

/-- A simple walk inside a subdrawing between two vertices of a circuit. -/
theorem exists_simple_walk_in_circuit {C : Drawing S} (hC : C.IsCircuit) (hCs : C.IsSubdrawing N)
    {a b : S} (ha : a ∈ C.V) (hb : b ∈ C.V) :
    ∃ W : GraphWalk N.toGraph a b, W.IsSimple ∧ ∀ x ∈ W.support, x ∈ C.V := by
  by_cases hab : a = b
  · subst hab
    have h0 : a ∈ N.V := hCs.1 ha
    exact ⟨.nil h0, List.nodup_singleton a, fun x hx => mem_support_nil.mp hx ▸ ha⟩
  obtain ⟨P, -, ⟨W, hW, hV, -⟩, -, hPs, -⟩ := hC.exists_two_paths ha hb hab
  obtain ⟨W', hs', -⟩ := (hPs.trans hCs).exists_walk_up W
  refine ⟨W', ?_, fun x hx => ?_⟩
  · unfold GraphWalk.IsSimple
    rw [hs']
    exact hW
  · rw [hs'] at hx
    exact hPs.1 (hV ▸ hx)

section Slope

variable (hs : IsSlope N k ins) (hconf : IsConfined k N)
include hs hconf

/-- No walk that avoids a common vertex `u` of two distinct rings joins them (Graph Minors XI, proof
of (5.4), page 82: the circuit through both rings that the paper excludes). -/
theorem no_walk_between_rings {C C' : Drawing S} (hC : IsRing ins N C) (hC' : IsRing ins N C')
    (hne : C' ≠ C) {u y x : S} (hu : u ∈ C.V) (hu' : u ∈ C'.V) (hy : y ∈ C.V) (hx : x ∈ C'.V)
    (W : GraphWalk N.toGraph y x) (hW : u ∉ W.support) : False := by
  classical
  have hUC := (ins_facts hs hconf hC.1 hC.2.1).2.2
  have hVin : ∀ {w}, w ∈ C.V → w ∈ ins C := fun h => hUC (C.V_subset_U h)
  obtain ⟨W₁, hW₁, hW₁s, -⟩ := GraphWalk.exists_isSimple W
  obtain ⟨z, W₂, hz, huniq, hsup, -, hsimple⟩ := GraphWalk.exists_prefix W₁ C'.V hx
  have hW₂ := hsimple hW₁
  obtain ⟨Q, hQ, hQV⟩ := exists_simple_walk_in_circuit hC'.1 hC'.2.1 hz hu'
  have hR : (W₂.append Q).IsSimple := isSimple_append' hW₂ hQ fun a ha haQ => huniq a ha (hQV a haQ)
  obtain ⟨h₁, -⟩ := path_mem_ins hs hconf hC _ hR (hVin hy) (hVin hu)
  have hzi : z ∈ ins C := h₁ z ((GraphWalk.mem_support_append _ _).mpr (Or.inl W₂.end_mem_support))
  have hzu : z ≠ u := fun h => hW (hW₁s u (hsup u (h ▸ W₂.end_mem_support)))
  exact hzu (ring_inter_le_one hs hconf hC hC' hne hz hu' hzi (hVin hu))

/-- A vertex `u` of a ring `C` at an edge not in `ins(C)` lies on another ring (Graph Minors XI,
proof of (5.4), page 83). Here every edge of `N` lies on a circuit. -/
theorem exists_other_ring (hcirc : ∀ e ∈ N.E, ∃ D : Drawing S, D.IsCircuit ∧ D.IsSubdrawing N
  ∧ e ∈ D.E)
    {C : Drawing S} (hC : IsRing ins N C) {f : Set S} (hf : f ∈ N.E) (hfC : ¬ f ⊆ ins C) {u : S}
    (hu : u ∈ C.V) (huf : u ∈ closure f) : ∃ C', IsRing ins N C' ∧ C' ≠ C ∧ u ∈ C'.V := by
  obtain ⟨D, hD, hDs, hfD⟩ := hcirc f hf
  obtain ⟨C', hC', hle⟩ := exists_ring_above ins hD hDs
  have hfi : f ⊆ ins C' := fun x hx =>
    hle ((ins_facts hs hconf hD hDs).2.2 (hfD.2.1 hx).1)
  have hne : C' ≠ C := fun h => hfC (h ▸ hfi)
  have hne' : C ≠ C' := fun h => hne h.symm
  have hui : u ∈ ins C' := (ins_facts hs hconf hC'.1 hC'.2.1).1.closure_subset_iff.mpr hfi huf
  exact ⟨C', hC', hne, (ring_vertex_in_ins hs hconf hC' hC hne' hu hui).1⟩

/-- Distinct rings have no common edge (Graph Minors XI, proof of (5.4), page 82). -/
theorem ring_edge_disjoint {C C' : Drawing S} (hC : IsRing ins N C) (hC' : IsRing ins N C')
    (hne : C' ≠ C) : Disjoint C.E C'.E := by
  refine disjoint_left.mpr fun g hg hg' => ?_
  obtain ⟨-, -, hU⟩ := ins_facts hs hconf hC.1 hC.2.1
  have hgi : closure g ⊆ ins C :=
    (ins_facts hs hconf hC.1 hC.2.1).1.closure_subset_iff.mpr fun x hx => hU (hg.2.1 hx).1
  obtain ⟨u, W, -, -, -, hE⟩ := id hC'.1
  have hgW : g ∈ W.edges := by
    rw [hE] at hg'
    exact hg'
  obtain ⟨x, y, -, hl, -, -⟩ := exists_split_edge W hgW
  have hx : x ∈ closure g ∩ C'.V := by rw [hl.2.2.2]; simp
  have hy : y ∈ closure g ∩ C'.V := by rw [hl.2.2.2]; simp
  have hxy : x = y := ring_inter_le_one hs hconf hC hC' hne hx.2 hy.2 (hgi hx.1) (hgi hy.1)
  have hloop : closure g ∩ C'.V = {x} := by
    rw [hl.2.2.2, ← hxy]
    simp
  have hone := IsCircuit.E_eq_of_loop hC'.1 hg' hloop
  obtain ⟨-, g₀, hg₀, -, hdis⟩ := ring_vertex_in_ins hs hconf hC hC' hne hx.2 (hgi hx.1)
  rw [hone] at hg₀
  have hg₀g : g₀ = g := hg₀
  obtain ⟨p, hp⟩ := hg.1
  exact disjoint_left.mp hdis (hg₀g ▸ hp) (hU (hg.2.1 hp).1)

end Slope

/-- The vertices reached from `C` by walks of `N` that avoid `v`. -/
def ringSide (N C : Drawing S) (v : S) : Set S :=
  {x | ∃ y ∈ C.V, ∃ W : GraphWalk N.toGraph y x, v ∉ W.support}

/-- `C` meets the rest of `N` only at `v`: statement (1) of the proof of (5.4) in Graph Minors XI
(page 83), "at most one vertex of $C_1$ is incident with an edge of $N(Z_1)$ not in
$\operatorname{ins}(C_1)$". -/
def IsLeafRing (ins : Drawing S → Set S) (N C : Drawing S) (v : S) : Prop :=
  IsRing ins N C ∧ v ∈ C.V ∧ ∀ u ∈ C.V, u ≠ v → ∀ f ∈ N.E, u ∈ closure f → f ⊆ ins C

section Slope

variable (hs : IsSlope N k ins) (hconf : IsConfined k N)
include hs hconf

/-- The descent: from a ring and a vertex, reach a leaf ring whose side stays in the first side, and
that is the first ring or has a vertex in that side. -/
theorem exists_leaf_ring_below
    (hcirc : ∀ e ∈ N.E, ∃ D : Drawing S, D.IsCircuit ∧ D.IsSubdrawing N ∧ e ∈ D.E)
    {C₀ : Drawing S} (hC₀ : IsRing ins N C₀) {v₀ : S} (hv₀ : v₀ ∈ C₀.V) :
    ∃ C v, IsLeafRing ins N C v ∧ ringSide N C v ⊆ ringSide N C₀ v₀ ∧
      (C = C₀ ∨ ∃ u ∈ C.V, u ∈ ringSide N C₀ v₀) := by
  classical
  have hfin : ∀ C v, (ringSide N C v).Finite := fun C v => N.finite_V.subset <| by
    rintro x ⟨y, -, W, -⟩
    exact W.mem_vertexSet_of_mem_support W.end_mem_support
  induction hn : (ringSide N C₀ v₀).ncard using Nat.strong_induction_on generalizing C₀ v₀ with
  | _ n ih =>
    by_cases hleaf : ∀ u ∈ C₀.V, u ≠ v₀ → ∀ f ∈ N.E, u ∈ closure f → f ⊆ ins C₀
    · exact ⟨C₀, v₀, ⟨hC₀, hv₀, hleaf⟩, subset_rfl, Or.inl rfl⟩
    push Not at hleaf
    obtain ⟨u, hu, huv, f, hf, huf, hfC⟩ := hleaf
    obtain ⟨C', hC', hne, hu'⟩ := exists_other_ring hs hconf hcirc hC₀ hf hfC hu huf
    have hne' : C₀ ≠ C' := fun h => hne h.symm
    have hUC₀ := (ins_facts hs hconf hC₀.1 hC₀.2.1).2.2
    have hUC' := (ins_facts hs hconf hC'.1 hC'.2.1).2.2
    have hv₀C' : v₀ ∉ C'.V := fun h => huv (ring_inter_le_one hs hconf hC₀ hC' hne hu' h
      (hUC₀ (C₀.V_subset_U hu)) (hUC₀ (C₀.V_subset_U hv₀)))
    have huN : u ∈ N.V := hC₀.2.1.1 hu
    have huside : u ∈ ringSide N C₀ v₀ := ⟨u, hu, .nil huN, fun h => huv
      (mem_support_nil.mp h).symm⟩
    have hsub : ringSide N C' u ⊆ ringSide N C₀ v₀ := by
      rintro x ⟨y, hy, W, hW⟩
      have hvW : v₀ ∉ W.support := by
        intro hv
        obtain ⟨W₁, W₂, rfl⟩ := W.exists_append_of_mem hv
        refine no_walk_between_rings hs hconf hC₀ hC' hne hu hu' hv₀ hy W₁.reverse ?_
        rw [GraphWalk.support_reverse, List.mem_reverse]
        exact fun h => hW ((GraphWalk.mem_support_append _ _).mpr (Or.inl h))
      obtain ⟨Q, -, hQV⟩ := exists_simple_walk_in_circuit hC'.1 hC'.2.1 hu' hy
      refine ⟨u, hu, Q.append W, fun h => ?_⟩
      rcases (GraphWalk.mem_support_append _ _).mp h with h | h
      · exact hv₀C' (hQV _ h)
      · exact hvW h
    have hnot : u ∉ ringSide N C' u := by
      rintro ⟨y, -, W, hW⟩
      exact hW W.end_mem_support
    have hlt : (ringSide N C' u).ncard < n := by
      rw [← hn]
      exact Set.ncard_lt_ncard ⟨hsub, fun h => hnot (h huside)⟩ (hfin _ _)
    obtain ⟨C, v, h₁, h₂, h₃⟩ := ih _ hlt hC' hu' rfl
    refine ⟨C, v, h₁, h₂.trans hsub, Or.inr ?_⟩
    rcases h₃ with rfl | ⟨w, hw, hws⟩
    · exact ⟨u, hu', huside⟩
    · exact ⟨w, hw, hsub hws⟩

/-- There is a ring as in statement (1), if `N` has a circuit. -/
theorem exists_leaf_ring
    (hcirc : ∀ e ∈ N.E, ∃ D : Drawing S, D.IsCircuit ∧ D.IsSubdrawing N ∧ e ∈ D.E)
    {D : Drawing S} (hD : D.IsCircuit) (hDs : D.IsSubdrawing N) : ∃ C v, IsLeafRing ins N C v := by
  obtain ⟨C₀, hC₀, -⟩ := exists_ring_above ins hD hDs
  obtain ⟨v, hv⟩ : C₀.V.Nonempty := by
    obtain ⟨u, W, -, -, hV, -⟩ := hC₀.1
    exact ⟨u, hV ▸ W.start_mem_support⟩
  obtain ⟨C, v, h, -, -⟩ := exists_leaf_ring_below hs hconf hcirc hC₀ hv
  exact ⟨C, v, h⟩

/-- A walk from outside `ins(C₁)` to a vertex in `ins(C₁)`, for a leaf ring, passes through its
vertex `v₁`. -/
theorem walk_passes_leaf_vertex {C₁ : Drawing S} {v₁ : S} (hL : IsLeafRing ins N C₁ v₁) {y x : S}
    (W : GraphWalk N.toGraph y x) (hy : y ∉ ins C₁) (hx : x ∈ ins C₁) : v₁ ∈ W.support := by
  classical
  obtain ⟨hC, hv, hleaf⟩ := hL
  obtain ⟨z, W', hz, huniq, hsup, -, -⟩ := GraphWalk.exists_prefix W (ins C₁) hx
  obtain ⟨f, hf, hzf, hdis⟩ := exists_exit_edge hs hconf hC.1 hC.2.1 W' hy hz huniq
  have hzV : z ∈ N.V := W'.mem_vertexSet_of_mem_support W'.end_mem_support
  have hzC := mem_V_of_outside_edge hs hconf hC.1 hC.2.1 hdis hzV hzf hz
  by_cases hzv : z = v₁
  · exact hzv ▸ hsup z W'.end_mem_support
  · exfalso
    obtain ⟨p, hp⟩ := (show f ∈ N.E from hf).1
    exact disjoint_left.mp hdis hp (hleaf z hzC hzv f hf hzf hp)

/-- A second ring as in statement (1): if `C₁` is a leaf ring and `C'` is another ring, there is a
leaf ring other than `C₁`. This is the paper's "the graph $G$ defined before (1) has at least two
vertices of valency $\le 1$" (Graph Minors XI, proof of (5.4), page 84). -/
theorem exists_second_leaf_ring
    (hcirc : ∀ e ∈ N.E, ∃ D : Drawing S, D.IsCircuit ∧ D.IsSubdrawing N ∧ e ∈ D.E)
    {C₁ C' : Drawing S} {v₁ : S} (hL : IsLeafRing ins N C₁ v₁) (hC' : IsRing ins N C')
    (hne : C' ≠ C₁) : ∃ C v, IsLeafRing ins N C v ∧ C ≠ C₁ := by
  classical
  have hC₁ := hL.1
  have hUC₁ := (ins_facts hs hconf hC₁.1 hC₁.2.1).2.2
  have hUC' := (ins_facts hs hconf hC'.1 hC'.2.1).2.2
  have hne' : C₁ ≠ C' := fun h => hne h.symm
  -- It is enough to find a vertex of `C'` whose side misses `V(C₁)`.
  have hgoal : ∀ v ∈ C'.V, Disjoint (ringSide N C' v) C₁.V →
      ∃ C v, IsLeafRing ins N C v ∧ C ≠ C₁ := by
    intro v hv hdis
    obtain ⟨C, w, h₁, -, h₃⟩ := exists_leaf_ring_below hs hconf hcirc hC' hv
    refine ⟨C, w, h₁, ?_⟩
    rintro rfl
    rcases h₃ with h | ⟨u, hu, hus⟩
    · exact hne h.symm
    · exact disjoint_left.mp hdis hus hu
  obtain ⟨c, hc⟩ : C'.V.Nonempty := by
    obtain ⟨u, W, -, -, hV, -⟩ := hC'.1
    exact ⟨u, hV ▸ W.start_mem_support⟩
  by_cases hv₁ : v₁ ∈ C'.V
  · -- The ring `C'` passes through `v₁`.
    refine hgoal v₁ hv₁ (disjoint_left.mpr ?_)
    rintro x ⟨y, hy, W, hW⟩ hx
    have hyv : y ≠ v₁ := fun h => hW (h ▸ W.start_mem_support)
    have hyi : y ∉ ins C₁ := fun h => hyv (ring_inter_le_one hs hconf hC₁ hC' hne hy hv₁ h
      (hUC₁ (C₁.V_subset_U hL.2.1)))
    exact hW (walk_passes_leaf_vertex hs hconf hL W hyi (hUC₁ (C₁.V_subset_U hx)))
  · -- All of `C'` lies outside `ins(C₁)`.
    have hout : ∀ w ∈ C'.V, w ∉ ins C₁ := by
      intro w hw hwi
      obtain ⟨hwC, g, hg, hwg, hdis⟩ := ring_vertex_in_ins hs hconf hC₁ hC' hne hw hwi
      by_cases hwv : w = v₁
      · exact hv₁ (hwv ▸ hw)
      · obtain ⟨p, hp⟩ := (show g ∈ C'.E from hg).1
        exact disjoint_left.mp hdis hp (hL.2.2 w hwC hwv g (hC'.2.1.2 hg) hwg hp)
    have hv₁i : v₁ ∉ ins C' := fun h =>
      hv₁ (ring_vertex_in_ins hs hconf hC' hC₁ hne' hL.2.1 h).1
    by_cases hconn : ∃ y ∈ C'.V, Nonempty (GraphWalk N.toGraph y v₁)
    · obtain ⟨y₀, hy₀, ⟨W₀⟩⟩ := hconn
      obtain ⟨W₀', hW₀', -, -⟩ := GraphWalk.exists_isSimple W₀.reverse
      obtain ⟨v, P, hvC, huniq, -, -, hsimple⟩ := GraphWalk.exists_prefix W₀' C'.V hy₀
      have hP := hsimple hW₀'
      -- Off `v`, the walk `P` from `v₁` stays outside `ins(C')`.
      have hPout : ∀ x ∈ P.support, x ≠ v → x ∉ ins C' := by
        intro x hx hxv hxi
        obtain ⟨P₁, P₂, rfl⟩ := P.exists_append_of_mem hx
        obtain ⟨z, X, hz, hzu, hzs, -, -⟩ := GraphWalk.exists_prefix P₁ (ins C') hxi
        obtain ⟨f, hf, hzf, hdis⟩ := exists_exit_edge hs hconf hC'.1 hC'.2.1 X hv₁i hz hzu
        have hzV : z ∈ N.V := X.mem_vertexSet_of_mem_support X.end_mem_support
        have hzC' := mem_V_of_outside_edge hs hconf hC'.1 hC'.2.1 hdis hzV hzf hz
        have hzv : z = v := huniq z ((GraphWalk.mem_support_append _ _).mpr (Or.inl (hzs z
          X.end_mem_support))) hzC'
        -- `z = v` occurs before the end of `P`, which is impossible in a simple walk unless `x =
        -- v`.
        have hndP : (P₁.append P₂).support.Nodup := hP
        rw [GraphWalk.support_append, P₂.support_eq_cons] at hndP
        have hd := List.nodup_append.mp hndP
        have hvP₂ : v ∈ (x :: P₂.support.tail).tail ∨ v = x := by
          have := P₂.end_mem_support
          rw [P₂.support_eq_cons] at this
          rcases List.mem_cons.mp this with h | h
          · exact Or.inr h
          · exact Or.inl h
        rcases hvP₂ with h | h
        · exact hd.2.2 v (hzv ▸ hzs z X.end_mem_support) v h rfl
        · exact hxv h.symm
      refine hgoal v hvC (disjoint_left.mpr ?_)
      rintro x ⟨y, hy, W, hW⟩ hx
      have hv₁W : v₁ ∈ W.support := walk_passes_leaf_vertex hs hconf hL W (hout y hy)
        (hUC₁ (C₁.V_subset_U hx))
      obtain ⟨Q, R, rfl⟩ := W.exists_append_of_mem hv₁W
      have hvQ : v ∉ Q.support := fun h => hW ((GraphWalk.mem_support_append _ _).mpr (Or.inl h))
      obtain ⟨Q₁, hQ₁, hQ₁s, -⟩ := GraphWalk.exists_isSimple Q
      obtain ⟨s, Q₂, hsA, hsu, hQ₂s, -, hsimple'⟩ :=
        GraphWalk.exists_prefix Q₁ {x | x ∈ P.support} P.start_mem_support
      obtain ⟨P₁, P₂, rfl⟩ := P.exists_append_of_mem hsA
      have hP₂ := (isSimple_of_append hP).2
      have hR : (Q₂.append P₂).IsSimple := isSimple_append' (hsimple' hQ₁) hP₂ fun a ha haP =>
        hsu a ha ((GraphWalk.mem_support_append _ _).mpr (Or.inr haP))
      obtain ⟨h₁, -⟩ := path_mem_ins hs hconf hC' _ hR (hUC' (C'.V_subset_U hy))
        (hUC' (C'.V_subset_U hvC))
      have hsi : s ∈ ins C' := h₁ s ((GraphWalk.mem_support_append _ _).mpr
        (Or.inl Q₂.end_mem_support))
      have hsv : s ≠ v := fun h => hvQ (hQ₁s v (hQ₂s v (h ▸ Q₂.end_mem_support)))
      exact hPout s hsA hsv hsi
    · refine hgoal c hc (disjoint_left.mpr ?_)
      rintro x ⟨y, hy, W, -⟩ hx
      have hv₁W := walk_passes_leaf_vertex hs hconf hL W (hout y hy) (hUC₁ (C₁.V_subset_U hx))
      obtain ⟨Q, -, -⟩ := W.exists_append_of_mem hv₁W
      exact hconn ⟨y, hy, ⟨Q⟩⟩

end Slope

end GraphMinor.GM11
