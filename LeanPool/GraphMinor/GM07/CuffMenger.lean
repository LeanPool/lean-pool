/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CuffSegments
public import LeanPool.GraphMinor.Menger.SimpleGraph

/-!
# The paths `Q_i(C)`

Graph Minors VII, (5.9), page 235: "we may deduce from Menger's theorem, applied to the graph
obtained from $G$ by contracting $N_i(C)$ to a single vertex for each $i$ with $1 \le i \le k(C)$,
that there are $k(C)$ mutually vertex-disjoint paths $Q_1, \dots, Q_{k(C)}$ of $G$, such that for
each $i$, $Q_i$ has one end in $C$, the other in $V(N_i(C))$, and all its other vertices and edges
are inside $U(N(C))$".

Here we take the part of `G` on the vertex set `In` inside `N(C)`, and we add one new vertex for
each `N_i(C)`.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function GraphMinor.Surface GraphMinor.GM11

universe u

variable {S : Type u} [TopologicalSpace S]

/-- The graph on the vertices in `In`, with one new vertex for each set `R i`. -/
def contractGraph (G : Drawing S) (In : Set S) {k : ℕ} (R : Fin k → Set S) : SimpleGraph
  (In ⊕ Fin k) where
  Adj p q := match p, q with
    | .inl a, .inl b => a ≠ b ∧ ∃ e, G.toGraph.IsLink e a.1 b.1
    | .inl a, .inr i => ∃ t ∈ R i, ∃ e, G.toGraph.IsLink e a.1 t
    | .inr i, .inl a => ∃ t ∈ R i, ∃ e, G.toGraph.IsLink e a.1 t
    | .inr _, .inr _ => False
  symm := ⟨fun p q h => by
    rcases p with a | i <;> rcases q with b | j
    · obtain ⟨h1, e, h2⟩ := h
      exact ⟨h1.symm, e, h2.symm⟩
    · exact h
    · exact h
    · exact h⟩
  loopless := ⟨fun p h => by
    rcases p with a | i
    · exact h.1 rfl
    · exact h⟩

variable {G : Drawing S} {In : Set S} {k : ℕ} {R : Fin k → Set S}

/-- A walk of `G` that stays in `In` up to its last vertex gives a walk of the contracted graph. -/
theorem exists_contract_walk {y t : S} (W : GraphWalk G.toGraph y t) (hIn : ∀ z ∈ W.support, z ≠ t
  → z ∈ In) {i : Fin k} (ht : t ∈ R i) (hy : y ∈ In) (hne : y ≠ t) :
    ∃ w : (contractGraph G In R).Walk (.inl ⟨y, hy⟩) (.inr i), ∀ p ∈ w.support, p = .inr i
      ∨ ∃ z, ∃ hz : z ∈ In, p = .inl ⟨z, hz⟩ ∧ z ∈ W.support := by
  classical
  induction W with
  | nil _ => exact absurd rfl hne
  | @cons u' v' w' e' h r ih =>
    have hup : ∀ z ∈ r.support, z ∈ (GraphWalk.cons h r).support := fun z hz
      => List.mem_cons_of_mem _ hz
    by_cases hv : v' = w'
    · subst hv
      have hadj : (contractGraph G In R).Adj (.inl ⟨u', hy⟩) (.inr i) := ⟨v', ht, e', h⟩
      refine ⟨.cons hadj .nil, fun p hp => ?_⟩
      simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · exact .inr ⟨u', hy, rfl, List.mem_cons_self⟩
      · exact .inl rfl
    · have hvIn : v' ∈ In := hIn v' (hup _ r.start_mem_support) hv
      obtain ⟨w₁, hw₁⟩ := ih (fun z hz hzt => hIn z (hup z hz) hzt) ht hvIn hv
      by_cases hu : u' = v'
      · subst hu
        refine ⟨w₁, fun p hp => ?_⟩
        rcases hw₁ p hp with h1 | ⟨z, hz, h1, h2⟩
        · exact .inl h1
        · exact .inr ⟨z, hz, h1, hup z h2⟩
      · have hadj : (contractGraph G In R).Adj (.inl ⟨u', hy⟩) (.inl ⟨v', hvIn⟩) := ⟨fun h1 => hu
          (congrArg Subtype.val h1), e', h⟩
        refine ⟨.cons hadj w₁, fun p hp => ?_⟩
        rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hp
        rcases hp with rfl | hp
        · exact .inr ⟨u', hy, rfl, List.mem_cons_self⟩
        · rcases hw₁ p hp with h1 | ⟨z, hz, h1, h2⟩
          · exact .inl h1
          · exact .inr ⟨z, hz, h1, hup z h2⟩

/-- A path of the contracted graph with only its last vertex new gives a path of `G`. -/
theorem exists_lift_walk (hRoff : ∀ i, Disjoint (R i) In) {p q : In ⊕ Fin k} (w :
  (contractGraph G In R).Walk p q) (hw : w.IsPath) :
    ∀ (y : In) (i : Fin k), p = .inl y → q = .inr i → (∀ j, .inr j ∈ w.support → j = i)
      → ∃ t ∈ R i, ∃ W : GraphWalk G.toGraph y.1 t, W.IsSimple ∧ ∀ z ∈ W.support, z = t
        ∨ ∃ hz : z ∈ In, .inl ⟨z, hz⟩ ∈ w.support := by
  classical
  induction w with
  | nil =>
    intro y i h1 h2
    rw [h1] at h2
    exact absurd h2 (by simp)
  | @cons p' q' r' hadj rest ih =>
    intro y i h1 h2 h3
    subst h1 h2
    have hp := SimpleGraph.Walk.cons_isPath_iff _ _ |>.mp hw
    rcases q' with b | j
    · obtain ⟨hne, e, hl⟩ := hadj
      obtain ⟨t, ht, W, h4, h5⟩ := ih hp.1 b i rfl rfl fun j hj => h3 j (List.mem_cons_of_mem _ hj)
      refine ⟨t, ht, .cons hl W, ?_, fun z hz => ?_⟩
      · change (y.1 :: W.support).Nodup
        refine List.nodup_cons.mpr ⟨fun h6 => ?_, h4⟩
        rcases h5 _ h6 with h7 | ⟨h8, h7⟩
        · exact disjoint_left.mp (hRoff i) ht (h7 ▸ y.2)
        · exact hp.2 h7
      · rw [GraphWalk.support, List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact .inr ⟨y.2, List.mem_cons_self⟩
        · rcases h5 z hz with h6 | ⟨h6, h7⟩
          · exact .inl h6
          · exact .inr ⟨h6, List.mem_cons_of_mem _ h7⟩
    · have hji : j = i := h3 j (List.mem_cons_of_mem _ rest.start_mem_support)
      subst hji
      have hnil : rest = .nil :=
        SimpleGraph.Walk.eq_nil_iff_nil.mpr (SimpleGraph.Walk.isPath_iff_nil.mp hp.1)
      subst hnil
      obtain ⟨t, ht, e, hl⟩ := hadj
      refine ⟨t, ht, .cons hl (.nil hl.right_mem), ?_, fun z hz => ?_⟩
      · change [y.1, t].Nodup
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_false_eq_true,
          List.nodup_nil, and_true]
        exact fun h4 => disjoint_left.mp (hRoff j) ht (h4 ▸ y.2)
      · simp only [GraphWalk.support, List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl
        · exact .inr ⟨y.2, List.mem_cons_self⟩
        · exact .inl rfl

/-- **Menger's theorem for the contracted graph.** If each set of fewer than `k` vertices and new
vertices leaves a walk from `A` to a set `R i`, then there are `k` disjoint paths, the `i`th from
`A` to `R i`, with all vertices but the last in `In`. -/
theorem exists_paths_to_groups (hfin : In.Finite) (hRoff : ∀ i, Disjoint (R i) In)
  (hRdis : ∀ i i', i ≠ i' → Disjoint (R i) (R i')) {A : Set S} (hAIn : A ⊆ In)
    (hconn : ∀ (I : Finset (Fin k)) (V' : Finset S), I.card + V'.card < k → ∃ i, i ∉ I
      ∧ ∃ x ∈ A, ∃ t ∈ R i, x ≠ t ∧ ∃ W : GraphWalk G.toGraph x t, ∀ z ∈ W.support, z ≠ t → z ∈ In
        ∧ z ∉ V') :
    ∃ (x t : Fin k → S) (Q : ∀ i, GraphWalk G.toGraph (x i) (t i)), (∀ i, x i ∈ A ∧ t i ∈ R i ∧
      (Q i).IsSimple ∧ ∀ z ∈ (Q i).support, z = t i ∨ z ∈ In) ∧ ∀ i i', i ≠ i' → Disjoint {z | z ∈
        (Q i).support} {z | z ∈ (Q i').support} := by
  classical
  have : Finite In := hfin.to_subtype
  have hF : Finite (In ⊕ Fin k) := inferInstance
  let K := contractGraph G In R
  let A' : Set (In ⊕ Fin k) := {p | ∃ a : In, a.1 ∈ A ∧ p = .inl a}
  let B' : Set (In ⊕ Fin k) := range .inr
  have hmen : HasDisjointPaths K A' B' k := by
    refine Menger.exists_disjointPaths K A' B' hF k fun S' hS' => ?_
    by_contra hlt
    push Not at hlt
    have hS'f : S'.Finite := toFinite _
    let I : Finset (Fin k) := Finset.univ.filter fun i => .inr i ∈ S'
    let V' : Finset S := (hS'f.toFinset.preimage (fun z : In => (Sum.inl z : In ⊕ Fin k))
      Sum.inl_injective.injOn).image Subtype.val
    have hcard : I.card + V'.card ≤ S'.ncard := by
      let pre := hS'f.toFinset.preimage (fun z : In => (Sum.inl z : In ⊕ Fin k))
        Sum.inl_injective.injOn
      have h1 : V'.card ≤ pre.card := Finset.card_image_le
      have h2 : (I.image Sum.inr ∪ pre.image Sum.inl).card = I.card + pre.card := by
        rw [Finset.card_union_of_disjoint, Finset.card_image_of_injective _ Sum.inr_injective,
          Finset.card_image_of_injective _ Sum.inl_injective]
        · rw [Finset.disjoint_left]
          intro p h3 h4
          obtain ⟨_, -, rfl⟩ := Finset.mem_image.mp h3
          obtain ⟨_, -, h5⟩ := Finset.mem_image.mp h4
          exact absurd h5 (by simp)
      have h3 : (I.image Sum.inr ∪ pre.image Sum.inl) ⊆ hS'f.toFinset := by
        intro p hp
        rcases Finset.mem_union.mp hp with h4 | h4
        · obtain ⟨j, h5, rfl⟩ := Finset.mem_image.mp h4
          exact hS'f.mem_toFinset.mpr (Finset.mem_filter.mp h5).2
        · obtain ⟨z, h5, rfl⟩ := Finset.mem_image.mp h4
          exact Finset.mem_preimage.mp h5
      have h4 := Finset.card_le_card h3
      rw [ncard_eq_toFinset_card S' hS'f]
      omega
    obtain ⟨i, hi, x, hxA, t, ht, hxt, W, hW⟩ := hconn I V' (by omega)
    obtain ⟨w, hw⟩ := exists_contract_walk (G := G) (In := In) (R := R) W (fun z hz hzt =>
      (hW z hz hzt).1) ht (hAIn hxA) hxt
    let P : PathFromTo K A' B' := ⟨_, _, w.bypass, w.bypass_isPath, ⟨⟨x, hAIn hxA⟩, hxA, rfl⟩, ⟨i,
      rfl⟩⟩
    obtain ⟨p, hp, hpS⟩ := hS' P
    rcases hw p (SimpleGraph.Walk.support_bypass_subset_support w hp) with rfl | ⟨z, hz, rfl, hzW⟩
    · exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpS⟩)
    · by_cases hzt : z = t
      · exact disjoint_left.mp (hRoff i) ht (hzt ▸ hz)
      · refine (hW z hzW hzt).2 (Finset.mem_image.mpr ⟨⟨z, hz⟩, ?_, rfl⟩)
        simpa using hpS
  obtain ⟨P, hdis⟩ := hmen
  have hsup : ∀ ι ι', ι ≠ ι' → ∀ p, p ∈ (P ι).walk.support → p ∉ (P ι').walk.support
    := fun ι ι' hne p h1 h2 => disjoint_left.mp (hdis hne) h1 h2
  choose r hr using fun ι => (P ι).last_mem
  have hrinj : Injective r := fun ι ι' he => by
    by_contra hne
    refine hsup ι ι' hne (.inr (r ι)) ?_ ?_
    · rw [hr ι]
      exact (P ι).walk.end_mem_support
    · rw [he, hr ι']
      exact (P ι').walk.end_mem_support
  have hrbij : Bijective r := ⟨hrinj, Finite.injective_iff_surjective.mp hrinj⟩
  let e := Equiv.ofBijective r hrbij
  have hlast : ∀ ι j, .inr j ∈ (P ι).walk.support → j = r ι := fun ι j hj => by
    have h1 : r (e.symm j) = j := e.apply_symm_apply j
    by_cases h2 : ι = e.symm j
    · rw [h2, h1]
    · exfalso
      refine hsup ι _ h2 _ hj ?_
      have h3 : (Sum.inr j : In ⊕ Fin k) = (P (e.symm j)).last := (congrArg Sum.inr h1.symm).trans
        (hr _)
      have h4 : ∀ p, p = (P (e.symm j)).last → p ∈ (P (e.symm j)).walk.support := by
        rintro _ rfl
        exact (P _).walk.end_mem_support
      exact h4 _ h3
  have hlift : ∀ ι, ∃ (a : In) (t : S) (W : GraphWalk G.toGraph a.1 t), a.1 ∈ A ∧ (P ι).first
    = .inl a ∧ t ∈ R (r ι) ∧ W.IsSimple ∧ ∀ z ∈ W.support, z = t ∨ ∃ hz : z ∈ In, .inl ⟨z, hz⟩ ∈
      (P ι).walk.support := fun ι => by
    obtain ⟨a, ha, h1⟩ := (P ι).first_mem
    obtain ⟨t, ht, W, h2, h3⟩ := exists_lift_walk (hRoff := hRoff) (P ι).walk (P ι).isPath a
      (r ι) h1 (hr ι).symm (hlast ι)
    exact ⟨a, t, W, ha, h1, ht, h2, h3⟩
  choose a t W h1 h2 h3 h4 h5 using hlift
  have hre : ∀ i, r (e.symm i) = i := fun i => e.apply_symm_apply i
  refine ⟨fun i => (a (e.symm i)).1, fun i => t (e.symm i), fun i => W (e.symm i),
    fun i => ⟨h1 _, ?_, h4 _, fun z hz => ?_⟩, fun i i' hne => ?_⟩
  · have := h3 (e.symm i)
    rwa [hre] at this
  · rcases h5 _ z hz with h6 | ⟨h6, -⟩
    · exact .inl h6
    · exact .inr h6
  · have hne' : e.symm i ≠ e.symm i' := fun h => hne (e.symm.injective h)
    have ht1 : t (e.symm i) ∈ R i := by
      have := h3 (e.symm i)
      rwa [hre] at this
    have ht2 : t (e.symm i') ∈ R i' := by
      have := h3 (e.symm i')
      rwa [hre] at this
    rw [disjoint_left]
    intro z hz hz'
    rcases h5 _ z hz with h6 | ⟨h6, h7⟩ <;> rcases h5 _ z hz' with h8 | ⟨h8, h9⟩
    · exact disjoint_left.mp (hRdis i i' hne) ht1 (by rw [← h6, h8]; exact ht2)
    · exact disjoint_left.mp (hRoff i) ht1 (h6 ▸ h8)
    · exact disjoint_left.mp (hRoff i') ht2 (h8 ▸ h6)
    · exact hsup _ _ hne' _ h7 h9

variable {T : Type u} [TopologicalSpace T]

/-- Two subdrawings without a common vertex have no common point. -/
theorem disjoint_U_of_disjoint_V {G A B : Drawing S} (hA : A.IsSubdrawing G)
  (hB : B.IsSubdrawing G) (hV : Disjoint A.V B.V) : Disjoint A.U B.U := by
  rw [disjoint_left]
  intro x hxA hxB
  by_cases hxV : x ∈ G.V
  · exact disjoint_left.mp hV (mem_V_of_subdrawing hA hxA hxV) (mem_V_of_subdrawing hB hxB hxV)
  · obtain ⟨e, he, hxe⟩ := A.exists_edge_of_mem hxA fun h => hxV (hA.1 h)
    obtain ⟨e', he', hxe'⟩ := B.exists_edge_of_mem hxB fun h => hxV (hB.1 h)
    have hee : e = e' := arcComponent_eq (hA.2 he) (hB.2 he') hxe hxe'
    subst hee
    have hne : (closure e ∩ A.V).Nonempty := by
      rcases A.edge_cond e he with ⟨u, v, -, h1, -⟩ | ⟨u, h1, -⟩
      · exact ⟨u, h1 ▸ mem_insert _ _⟩
      · exact ⟨u, h1 ▸ mem_singleton _⟩
    obtain ⟨u, hu1, hu2⟩ := hne
    exact disjoint_left.mp hV hu2 (mem_V_of_subdrawing hB (B.closure_subset_U he' hu1) (hA.1 hu2))

section Grid

variable [T2Space S] [T2Space T] {G : Drawing S} {j : S → T} {D₁ Δ₂ : Set T} {r s : ℕ} {P : Fin r
  → Drawing S} {u v : Fin r → S} {B : Fin s → Drawing S} {E : Fin s → Set T}

omit [T2Space T] in
omit [T2Space S] in
theorem IsCuffGrid.disjoint_U (h : IsCuffGrid G j D₁ Δ₂ P u v B E) {l l' : Fin s}
  (hne : l ≠ l') : Disjoint (B l).U (B l').U :=
  disjoint_U_of_disjoint_V (h.circuit l).1 (h.circuit l').1 (h.circuit_disj l l' hne)

omit [T2Space T] in
omit [T2Space S] in
/-- The discs of the grid are strictly nested. -/
theorem IsCuffGrid.subset_diff (h : IsCuffGrid G j D₁ Δ₂ P u v B E) (hman : ∀ x : T,
  IsManifoldPoint x) (hj : Injective j) {l l' : Fin s} (hlt : l < l') : E l ⊆ E l' \ discBd (E l')
    := fun x hx => by
  refine ⟨h.mono l l' hlt.le hx, fun hb => ?_⟩
  obtain ⟨-, -, h1, h2, -⟩ := h.circuit l
  by_cases h3 : x ∈ discBd (E l)
  · rw [h2] at h3
    rw [(h.circuit l').2.2.2.1] at hb
    obtain ⟨y, hy, rfl⟩ := h3
    obtain ⟨y', hy', he⟩ := hb
    exact disjoint_left.mp (h.disjoint_U hlt.ne) hy (hj he ▸ hy')
  · exact (discInt_mono hman h1 (h.mono l l' hlt.le) ⟨hx, h3⟩).2 hb

omit [T2Space T] in
/-- **The subpaths `N_i(C)` of a circuit of the grid.** -/
theorem IsCuffGrid.exists_groups {v' k : ℕ} {P : Fin (v' * k) → Drawing S} {u v : Fin (v' * k) → S}
  (h : IsCuffGrid G j D₁ Δ₂ P u v B E) (hk : 0 < k) (hv : 0 < v') (hvk : 2 ≤ v' * k) (l : Fin s) :
    ∃ R : Fin k → Drawing S, (∀ i, (R i).IsSubdrawing (B l) ∧ ∃ a b, (R i).IsPathBetween a b) ∧
      (∀ i i', i ≠ i' → Disjoint (R i).V (R i').V) ∧ (∀ x ∈ (B l).V, ∃ i, x ∈ (R i).V)
        ∧ ∀ i, ∃ f : Fin v' → Fin (v' * k), Injective f ∧ ∀ t, (P (f t)).V ∩ (B l).V ⊆ (R i).V := by
  classical
  choose Q x y h1 h2 h3 h4 using fun ι => h.inter ι l
  have hsub : ∀ ι, (Q ι).IsSubdrawing (B l) := fun ι => by
    refine ⟨fun z hz => ?_, fun e he => ?_⟩
    · have := h3 ι
      exact (this ▸ hz : z ∈ (P ι).V ∩ (B l).V).2
    · obtain ⟨z, hz⟩ := he.1
      have hzU : z ∈ (B l).U := by
        have := (h2 ι)
        exact (this ▸ (he.2.1 hz).1 : z ∈ (P ι).U ∩ (B l).U).2
      have heG := (h1 ι).2 he
      have hzV : z ∉ (B l).V := fun h5 => (heG.2.1 hz).2 ((h.circuit l).1.1 h5)
      obtain ⟨e', he', hze'⟩ := (B l).exists_edge_of_mem hzU hzV
      exact arcComponent_eq heG ((h.circuit l).1.2 he') hz hze' ▸ he'
  have hdis : ∀ ι ι', ι ≠ ι' → Disjoint (Q ι).V (Q ι').V := fun ι ι' hne => by
    rw [h3, h3]
    exact (h.path_disj ι ι' hne).mono inter_subset_left inter_subset_left
  obtain ⟨R, h5, h6, h7, h8⟩ := exists_circuit_groups (h.circuit l).2.1 hk hv hvk Q hsub (fun ι
    => ⟨x ι, y ι, h4 ι⟩) hdis
  refine ⟨R, h5, h6, h7, fun i => ?_⟩
  obtain ⟨f, hf, hf'⟩ := h8 i
  exact ⟨f, hf, fun t => by
    rw [← h3]
    exact hf' t⟩

end Grid

/-- **Walks that stay inside a disc.** A walk of `G` that starts inside the disc `Δ`, whose boundary
is a circuit of `G`, stays inside until it reaches the circuit. -/
theorem walk_stays_inside [T2Space T] (hman : ∀ x : T, IsManifoldPoint x) {G N :
  Drawing S} (hN : N.IsSubdrawing G) {j : S → T} (hj : Continuous j) (hji : Injective j) {Δ : Set
    T} (hΔ : IsClosedDisc Δ) (hb : discBd Δ = j '' N.U) {y t : S} (W : GraphWalk G.toGraph y t)
      (hs : W.IsSimple) (hoff : ∀ z ∈ W.support, z ≠ t → z ∉ N.V) (hy : j y ∈ discInt Δ) :
    ∀ z ∈ W.support, z = t ∨ j z ∈ discInt Δ := by
  induction W with
  | nil _ =>
    intro z hz
    exact .inl (List.mem_singleton.mp hz)
  | @cons u' v' w' e h r ih =>
    have hheld : j v' ∈ Δ := by
      have hoffU : u' ∉ N.U := fun h1 => hy.2 (hb ▸ mem_image_of_mem j h1)
      have heN : e ∉ N.E := fun h1 => hoffU (N.closure_subset_U h1 ((h.2.2.2 ▸ mem_insert _ _ : u'
        ∈ closure e ∩ G.V).1))
      have hebd : Disjoint (j '' e) (frontier Δ) := by
        rw [disjoint_left]
        rintro _ ⟨x, hx, rfl⟩ hf
        have h1 := frontier_disc_subset hman hΔ hf
        rw [hb] at h1
        obtain ⟨x', hx', he'⟩ := h1
        have hxU : x ∈ N.U := hji he' ▸ hx'
        have hxV : x ∉ N.V := fun h2 => (h.1.2.1 hx).2 (hN.1 h2)
        obtain ⟨e', he'', hxe'⟩ := N.exists_edge_of_mem hxU hxV
        exact heN (arcComponent_eq h.1 (hN.2 he'') hx hxe' ▸ he'')
      have hpre : IsPreconnected (j '' e) := h.1.2.2.1.isConnected.isPreconnected.image _
        hj.continuousOn
      have hcl : u' ∈ closure e := (h.2.2.2 ▸ mem_insert _ _ : u' ∈ closure e ∩ G.V).1
      have hcl' : v' ∈ closure e := (h.2.2.2 ▸ mem_insert_of_mem _ rfl : v' ∈ closure e ∩ G.V).1
      have hmeet : (j '' e ∩ Δ).Nonempty := by
        have h2 : j u' ∈ closure (j '' e) := map_mem_closure hj hcl fun x hx
          => mem_image_of_mem j hx
        obtain ⟨w, hw1, hw2⟩ := mem_closure_iff.mp h2 _ (hΔ.isOpen_discInt hman) hy
        exact ⟨w, hw2, hw1.1⟩
      rcases inside_or_off hpre hΔ.isClosed hebd with h1 | h1
      · exact closure_minimal (h1.trans interior_subset) hΔ.isClosed (map_mem_closure hj hcl' fun x
          hx => mem_image_of_mem j hx)
      · obtain ⟨w, hw1, hw2⟩ := hmeet
        exact absurd hw2 (h1 hw1)
    intro z hz
    rw [GraphWalk.support, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact .inr hy
    · have hnd : r.support.Nodup := (List.nodup_cons.mp hs).2
      by_cases hvt : v' = w'
      · subst hvt
        cases r with
        | nil _ => exact .inl (List.mem_singleton.mp hz)
        | cons h' r' =>
          have h1 : (_ :: r'.support).Nodup := hnd
          exact absurd r'.end_mem_support (List.nodup_cons.mp h1).1
      · have hint : j v' ∈ discInt Δ := by
          refine ⟨hheld, fun hbv => ?_⟩
          rw [hb] at hbv
          obtain ⟨x, hx, he'⟩ := hbv
          have hvU : v' ∈ N.U := hji he' ▸ hx
          exact hoff v' (List.mem_cons_of_mem _ r.start_mem_support) hvt
            (mem_V_of_subdrawing hN hvU h.2.2.1)
        exact ih hnd (fun z' hz' hne => hoff z' (List.mem_cons_of_mem _ hz') hne) hint z hz

/-- Among `n` disjoint sets, a set of fewer than `n` points misses one. -/
theorem exists_avoiding {α : Type*} {n : ℕ} (A : Fin n → Set α) (hA : ∀ i i', i ≠ i' → Disjoint
  (A i) (A i')) (X : Finset α) (hX : X.card < n) : ∃ i, ∀ z ∈ X, z ∉ A i := by
  classical
  by_contra hn
  push Not at hn
  choose f hf hfA using hn
  have hinj : Injective fun i => (⟨f i, hf i⟩ : X) := fun i i' he => by
    by_contra hne
    have h1 : f i = f i' := congrArg Subtype.val he
    exact disjoint_left.mp (hA i i' hne) (hfA i) (h1 ▸ hfA i')
  have h2 := Fintype.card_le_of_injective _ hinj
  simp at h2
  omega

/-- A walk through two vertices holds a walk between them. -/
theorem exists_walk_between {α β : Type*} {K : Graph α β} {a b : α} (W : GraphWalk K a b) {x y : α}
  (hx : x ∈ W.support) (hy : y ∈ W.support) : ∃ W' : GraphWalk K x y, ∀ z ∈ W'.support, z ∈
    W.support := by
  obtain ⟨W₁, W₂, rfl⟩ := W.exists_append_of_mem hx
  rcases (GraphWalk.mem_support_append W₁ W₂).mp hy with h | h
  · obtain ⟨A, B, rfl⟩ := W₁.exists_append_of_mem h
    refine ⟨B.reverse, fun z hz => ?_⟩
    rw [GraphWalk.support_reverse, List.mem_reverse] at hz
    exact (GraphWalk.mem_support_append _ _).mpr (.inl ((GraphWalk.mem_support_append _ _).mpr
      (.inr hz)))
  · obtain ⟨A, B, rfl⟩ := W₂.exists_append_of_mem h
    exact ⟨A, fun z hz => (GraphWalk.mem_support_append _ _).mpr (.inr
      ((GraphWalk.mem_support_append _ _).mpr (.inl hz)))⟩

/-- **The paths from `C` to `B_s(C)`.** "since $G$ is boundary-linked, there exist $k(C)$ mutually
vertex-disjoint paths of $G$, each
between $C$ and $B_s(C)$" (page 235), by the grid theorem with no circuits. -/
theorem IsCuffGrid.exists_link_paths (hS : IsSurface S) [ConnectedSpace S] {C : Set S}
  (hC : C ∈ cuffs S) {D D₁ Δ₂ : Set T} {j : S → T} (hc : IsCappedCuff C T j D)
    (hns : ¬ IsSphere T) {G : Drawing S} (hbl : IsBoundaryLinked G) {r β : ℕ} {P : Fin r
      → Drawing S} {u v : Fin r → S} {B : Fin β → Drawing S} {E : Fin β → Set T}
        (h : IsCuffGrid G j D₁ Δ₂ P u v B E)
    (hDint : ∀ l, D ⊆ discInt (E l)) (hoff : Disjoint Δ₂ (bd T)) {s s' : Fin β} (hss : s < s') :
    ∃ (L : Fin (G.V ∩ C).ncard → Drawing S) (a b : Fin (G.V ∩ C).ncard → S), (∀ i,
      (L i).IsSubdrawing G ∧ a i ∈ C ∧ b i ∈ (B s).V ∧ (L i).IsPathBetween (a i) (b i) ∧ j ''
        (L i).U ⊆ E s' \ discBd (E s')) ∧ ∀ i i', i ≠ i' → Disjoint (L i).V (L i').V := by
  classical
  have hT := hc.isSurface
  have : T2Space T := hT.2.1
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  have hman := hT.2.2
  have hcj : IsClosedEmbedding j := hc.isEmbedding.continuous.isClosedEmbedding
    hc.isEmbedding.injective
  have hji := hc.isEmbedding.injective
  obtain ⟨-, -, hEs, hbds, -, -⟩ := h.circuit s
  obtain ⟨-, -, hEs', -, -, hEsΔ⟩ := h.circuit s'
  obtain ⟨Bs, p1, p2, p3, p4, p5, -⟩ := exists_parallel_disc (h.circuit s).1 hcj hEs hEs'
    (h.subset_diff hman hji hss) hbds
  have hCU : C ⊆ bd S := fun x hx => by
    have : x ∈ ⋃₀ cuffs S := ⟨C, hC, hx⟩
    rwa [sUnion_cuffs] at this
  have hbC : j ⁻¹' discBd D = C := by
    rw [hc.discBd_eq, preimage_image_eq _ hji]
  have hin : D ⊆ Bs \ discBd Bs := fun x hx => by
    have h1 := discInt_mono hman hEs p2 (hDint s hx)
    exact ⟨h1.1, h1.2⟩
  have hr : Bs \ discInt D ⊆ range j := fun x hx => by
    by_contra hxr
    rcases hc.union_eq.ge (mem_univ x) with h1 | h1
    · exact hxr h1
    · refine hx.2 ⟨h1, fun hb => hxr ?_⟩
      rw [hc.discBd_eq] at hb
      exact image_subset_range _ _ hb
  have hn₁ : G.IsNormal (j ⁻¹' discBd D) := by
    rw [hbC]
    rintro x ⟨hx, hU⟩
    exact hbl.1 ⟨hCU hx, hU⟩
  have hint : ∀ x ∈ discBd Bs, IsInteriorPoint x := fun x hx => by
    by_contra hb
    exact disjoint_left.mp hoff (hEsΔ (p3 (Surface.discBd_subset _ hx)).1) hb
  have hi : ∀ B', IsClosedDisc B' → D ⊆ B' → B' ⊆ Bs → G.IsNormal (j ⁻¹' discBd B') →
    (G.V ∩ C).ncard ≤ (G.V ∩ j ⁻¹' discBd B').ncard := fun B' h1 h2 _ h4 =>
    hbl.2 C hC _ h4 (isOArc_preimage_bd hc h1 h2) (surrounds_of_disc hS hC hc hns h1 h2)
  obtain ⟨L, a, b, -, -, g1, g2, -⟩ := exists_disc_grid (s := 0) hman hcj hc.isClosedDisc p1 hin hr
    hn₁ p4 hint hi (fun _ _ _ _ _ _ _ _ _ => Nat.zero_le _)
  refine ⟨L, a, b, fun i => ?_, g2⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := g1 i
  refine ⟨h1, ?_, ?_, h4, ?_⟩
  · have : a i ∈ j ⁻¹' discBd D := h2
    rwa [hbC] at this
  · obtain ⟨W, -, hV, -⟩ := id h4
    have h6 : b i ∈ (L i).V := by
      rw [hV]
      exact W.end_mem_support
    have : b i ∈ G.V ∩ j ⁻¹' discBd Bs := ⟨h1.1 h6, h3⟩
    rwa [p5] at this
  · rintro _ ⟨x, hx, rfl⟩
    have h6 := h5 (mem_image_of_mem j hx)
    exact p3 h6.1

/-- **The paths `Q_i(C)`** of page 235. The circuit `N(C)` is `B l₀` with `l₀ = k(C)`, so the
circuits before it are `k(C)` in number. -/
theorem IsCuffGrid.exists_Q_walks (hS : IsSurface S) [ConnectedSpace S] {C : Set S}
  (hC : C ∈ cuffs S) {D D₁ Δ₂ : Set T} {j : S → T} (hc : IsCappedCuff C T j D)
    (hns : ¬ IsSphere T) {G : Drawing S} (hbl : IsBoundaryLinked G) {v' β : ℕ} {P : Fin (v' *
      (G.V ∩ C).ncard) → Drawing S} {u v : Fin (v' * (G.V ∩ C).ncard) → S} {B : Fin β
        → Drawing S} {E : Fin β → Set T} (h : IsCuffGrid G j D₁ Δ₂ P u v B E)
    (hDint : ∀ l, D ⊆ discInt (E l)) (hoff : Disjoint Δ₂ (bd T)) (hkv : (G.V ∩ C).ncard ≤ v')
      (hkβ : (G.V ∩ C).ncard < β) {R : Fin (G.V ∩ C).ncard → Drawing S} (hR₁ : ∀ i,
        (R i).IsSubdrawing (B ⟨_, hkβ⟩)) (hR₂ : ∀ i i', i ≠ i' → Disjoint (R i).V (R i').V)
    (hR₃ : ∀ i, ∃ f : Fin v' → Fin (v' * (G.V ∩ C).ncard), Injective f ∧ ∀ t, (P (f t)).V ∩
      (B ⟨_, hkβ⟩).V ⊆ (R i).V) :
    ∃ (x t : Fin (G.V ∩ C).ncard → S) (Q : ∀ i, GraphWalk G.toGraph (x i) (t i)),
      (∀ i, x i ∈ G.V ∩ C ∧ t i ∈ (R i).V ∧ (Q i).IsSimple ∧ ∀ z ∈ (Q i).support, z = t i
        ∨ z ∈ G.V ∩ j ⁻¹' discInt (E ⟨_, hkβ⟩)) ∧ ∀ i i', i ≠ i' → Disjoint {z | z ∈
          (Q i).support} {z | z ∈ (Q i').support} := by
  classical
  have hT := hc.isSurface
  have : T2Space T := hT.2.1
  have : T2Space S := hS.2.1
  have hman := hT.2.2
  have hji := hc.isEmbedding.injective
  have hjc := hc.isEmbedding.continuous
  let l₀ : Fin β := ⟨(G.V ∩ C).ncard, hkβ⟩
  obtain ⟨hN, -, hEl, hbl₀, -, -⟩ := h.circuit l₀
  let In : Set S := G.V ∩ j ⁻¹' discInt (E l₀)
  have hbU : ∀ {z}, z ∈ (B l₀).U → j z ∉ discInt (E l₀) := fun {z} hz h1 => h1.2
    (hbl₀ ▸ mem_image_of_mem j hz)
  have hRoff : ∀ i, Disjoint (R i).V In := fun i => disjoint_left.mpr fun z hz h1 => hbU
    ((B l₀).V_subset_U ((hR₁ i).1 hz)) h1.2
  have hAIn : G.V ∩ C ⊆ In := fun z hz => by
    refine ⟨hz.1, hDint l₀ (Surface.discBd_subset _ ?_)⟩
    rw [hc.discBd_eq]
    exact mem_image_of_mem j hz.2
  refine exists_paths_to_groups (G := G) (In := In) (R := fun i => (R i).V)
    (G.finite_V.subset inter_subset_left) hRoff hR₂ hAIn fun I V' hIV => ?_
  have hsmall : V'.card < (G.V ∩ C).ncard := by omega
  -- a circuit before `N(C)` that misses `V'`
  have hltβ : ∀ s : Fin (G.V ∩ C).ncard, s.1 < β := fun s => s.2.trans hkβ
  obtain ⟨s, hs⟩ := exists_avoiding (fun s : Fin (G.V ∩ C).ncard => (B ⟨s.1, hltβ s⟩).V)
    (fun s s' hne => h.circuit_disj _ _ fun he => hne (Fin.ext (Fin.mk.inj_iff.mp he))) V' hsmall
  let s₀ : Fin β := ⟨s.1, hltβ s⟩
  have hs₀ : s₀ < l₀ := s.2
  obtain ⟨L, a, b, hL, hLd⟩ := h.exists_link_paths hS hC hc hns hbl hDint hoff hs₀
  obtain ⟨i₀, hi₀⟩ := exists_avoiding (fun i => (L i).V) hLd V' hsmall
  -- a group not in `I`
  obtain ⟨r, hr⟩ : ∃ r, r ∉ I := by
    by_contra hn
    push Not at hn
    have h1 : I = Finset.univ := Finset.eq_univ_iff_forall.mpr hn
    rw [h1] at hIV
    simp at hIV
  obtain ⟨f, hf, hfR⟩ := hR₃ r
  obtain ⟨t₀, ht₀⟩ := exists_avoiding (fun t => (P (f t)).V) (fun t t' hne
    => h.path_disj _ _ fun he => hne (hf he)) V' (by omega)
  obtain ⟨hL₁, ha, hb, hLp, hLU⟩ := hL i₀
  obtain ⟨W₁, -, hW₁V, -⟩ := id hLp
  obtain ⟨Z₁, hZ₁, -⟩ := hL₁.exists_walk_up W₁
  -- along `B_s(C)`
  obtain ⟨c₀, W₂, -, -, hW₂V, -⟩ := id (h.circuit s₀).2.1
  obtain ⟨Z₂, hZ₂, -⟩ := (h.circuit s₀).1.exists_walk_up W₂
  have hsup₂ : ∀ {z}, z ∈ Z₂.support ↔ z ∈ (B s₀).V := fun {z} => by
    rw [hZ₂, hW₂V]
    rfl
  -- along `P`
  obtain ⟨hP₁, -, -, hPp, -⟩ := h.path (f t₀)
  obtain ⟨W₃, -, hW₃V, -⟩ := id hPp
  obtain ⟨Z₃, hZ₃, -⟩ := hP₁.exists_walk_up W₃
  have hsup₃ : ∀ {z}, z ∈ Z₃.support ↔ z ∈ (P (f t₀)).V := fun {z} => by
    rw [hZ₃, hW₃V]
    rfl
  have hmeet : ∀ l, ∃ z, z ∈ (P (f t₀)).V ∧ z ∈ (B l).V := fun l => by
    obtain ⟨Q, x, y, -, -, h3, W, -, h4, -⟩ := h.inter (f t₀) l
    have h5 : x ∈ Q.V := by
      rw [h4]
      exact W.start_mem_support
    rw [h3] at h5
    exact ⟨x, h5⟩
  obtain ⟨y₁, hy₁P, hy₁B⟩ := hmeet s₀
  obtain ⟨y₂, hy₂P, hy₂B⟩ := hmeet l₀
  obtain ⟨Y₂, hY₂⟩ := exists_walk_between Z₂ (hsup₂.mpr hb) (hsup₂.mpr hy₁B)
  obtain ⟨Y₃, hY₃⟩ := exists_walk_between Z₃ (hsup₃.mpr hy₁P) (hsup₃.mpr hy₂P)
  let Z := Z₁.append (Y₂.append Y₃)
  have hZsup : ∀ {z}, z ∈ Z.support → z ∈ (L i₀).V ∨ z ∈ (B s₀).V ∨ z ∈ (P (f t₀)).V := fun {z} hz
    => by
    rcases (GraphWalk.mem_support_append _ _).mp hz with h1 | h1
    · left
      rw [hZ₁, hW₁V] at *
      exact h1
    · rcases (GraphWalk.mem_support_append _ _).mp h1 with h2 | h2
      · exact .inr (.inl (hsup₂.mp (hY₂ z h2)))
      · exact .inr (.inr (hsup₃.mp (hY₃ z h2)))
  have hZV : ∀ {z}, z ∈ Z.support → z ∈ G.V := fun {z} hz => by
    rcases hZsup hz with h1 | h1 | h1
    · exact hL₁.1 h1
    · exact (h.circuit s₀).1.1 h1
    · exact hP₁.1 h1
  have hZoff : ∀ {z}, z ∈ Z.support → z ∉ V' := fun {z} hz hV => by
    rcases hZsup hz with h1 | h1 | h1
    · exact hi₀ z hV h1
    · exact hs z hV h1
    · exact ht₀ z hV h1
  have hZR : ∀ {z}, z ∈ Z.support → z ∈ (B l₀).V → z ∈ (R r).V := fun {z} hz hzB => by
    rcases hZsup hz with h1 | h1 | h1
    · have h2 := hLU (mem_image_of_mem j ((L i₀).V_subset_U h1))
      refine absurd (?_ : j z ∈ discBd (E l₀)) ?_
      · rw [hbl₀]
        exact mem_image_of_mem j ((B l₀).V_subset_U hzB)
      · exact fun h3 => h2.2 h3
    · exact absurd hzB (disjoint_left.mp (h.circuit_disj s₀ l₀ hs₀.ne) h1)
    · exact hfR t₀ ⟨h1, hzB⟩
  -- the first vertex on `N(C)`
  have hend : y₂ ∈ Z.support := (GraphWalk.mem_support_append _ _).mpr (.inr
    ((GraphWalk.mem_support_append _ _).mpr (.inr Y₃.end_mem_support)))
  obtain ⟨t, htB, W₄, W₅, hsplit, hW₅⟩ := exists_last_hit_split Z.reverse (X := (B l₀).V)
    ⟨y₂, by rwa [GraphWalk.support_reverse, List.mem_reverse], hy₂B⟩
  have hsub₅ : ∀ z ∈ W₅.reverse.support, z ∈ Z.support := fun z hz => by
    rw [GraphWalk.support_reverse, List.mem_reverse] at hz
    have h1 : z ∈ Z.reverse.support := (GraphWalk.mem_support_append W₄ W₅).mpr (.inr hz) |> fun h2
      => by
      rwa [← hsplit] at h2
    rw [GraphWalk.support_reverse, List.mem_reverse] at h1
    exact h1
  obtain ⟨W₆, hW₆s, hW₆, -⟩ := GM09.exists_isSimple_subwalk W₅.reverse
  have hsub₆ : ∀ z ∈ W₆.support, z ∈ Z.support := fun z hz => hsub₅ z (hW₆ z hz)
  have hoffN : ∀ z ∈ W₆.support, z ≠ t → z ∉ (B l₀).V := fun z hz hne hzB => by
    have h1 := hW₆ z hz
    rw [GraphWalk.support_reverse, List.mem_reverse] at h1
    exact hne (hW₅ z h1 hzB)
  have haZ : a i₀ ∈ In := hAIn ⟨hL₁.1 (by rw [hW₁V]; exact W₁.start_mem_support), ha⟩
  have hin := walk_stays_inside hman (h.circuit l₀).1 hjc hji hEl hbl₀ W₆ hW₆s hoffN haZ.2
  have htZ : t ∈ Z.support := hsub₆ t W₆.end_mem_support
  refine ⟨r, hr, a i₀, ⟨hL₁.1 (by rw [hW₁V]; exact W₁.start_mem_support), ha⟩,
    t, hZR htZ htB, fun he => ?_, W₆, fun z hz hzt => ⟨?_, hZoff (hsub₆ z hz)⟩⟩
  · exact disjoint_left.mp (hRoff r) (hZR htZ htB) (he ▸ haZ)
  · exact ⟨hZV (hsub₆ z hz), (hin z hz).resolve_left hzt⟩

end GraphMinor.GM07
