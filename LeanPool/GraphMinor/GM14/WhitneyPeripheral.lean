/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM14.WhitneyFaces
import LeanPool.GraphMinor.GM11.PerimeterPull
import LeanPool.GraphMinor.GM09.Basic
import LeanPool.GraphMinor.GM11.Walks

/-!
# Face boundaries are the peripheral circuits

Let `J` be a drawing in a sphere of a subdivision of a simple 3-connected graph. Call a circuit
`C` of `J` *peripheral* if the edges of `J` outside `C` form one bridge of `C`. We show:

* the boundary of a face of `J` is a peripheral circuit (`peripheral_of_side`);
* a peripheral circuit bounds a disc whose interior misses `J`
  (`exists_free_side_of_peripheral`).

So the set of boundaries of faces depends only on the graph. This is the key to Whitney's theorem.
-/

@[expose] public section

namespace GraphMinor.GM14.Whitney

open Set Topology Graph GraphMinor.GM09 GraphMinor.GM11 GraphMinor.Surface

universe u

variable {S : Type u} [TopologicalSpace S]

section Walks

variable {α β : Type*} {G : Graph α β}

/-- Two simple walks that share only their common end have a simple concatenation. -/
theorem isSimple_append {a b c : α} (W₁ : GraphWalk G a b) (W₂ : GraphWalk G b c)
    (h₁ : W₁.IsSimple) (h₂ : W₂.IsSimple) (hc : ∀ p, p ∈ W₁.support → p ∈ W₂.support → p = b) :
    (W₁.append W₂).IsSimple := by
  induction W₁ with
  | nil _ => exact h₂
  | @cons u v w f hl rest ih =>
    have hnd := List.nodup_cons.mp h₁
    refine List.nodup_cons.mpr ⟨?_, ih W₂ hnd.2 h₂ fun p hp hp' => hc p
      (List.mem_cons_of_mem _ hp) hp'⟩
    rw [GraphWalk.mem_support_append]
    rintro (h' | h')
    · exact hnd.1 h'
    · have hub : u = _ := hc u (List.mem_cons_self) h'
      exact hnd.1 (hub ▸ rest.end_mem_support)

/-- Two walks that form a simple walk share only the middle vertex. -/
theorem append_cap {a b c : α} {W₁ : GraphWalk G a b} {W₂ : GraphWalk G b c}
    (h : (W₁.append W₂).IsSimple) (p : α) (h₁ : p ∈ W₁.support) (h₂ : p ∈ W₂.support) : p = b := by
  have hs : (W₁.support ++ W₂.support.tail).Nodup := by
    have h' : (W₁.append W₂).support.Nodup := h
    rwa [GraphWalk.support_append] at h'
  have hd := List.nodup_append.mp hs
  rw [W₂.support_eq_cons, List.mem_cons] at h₂
  rcases h₂ with h₂ | h₂
  · exact h₂
  · exact (hd.2.2 p h₁ p h₂ rfl).elim

/-- Two walks in a loopless graph that share at most one vertex have no common edge. -/
theorem edge_not_mem_of_cap {a b c d q : α} (hl : ∀ e u, ¬ G.IsLink e u u) {W₁ : GraphWalk G a b}
    {W₂ : GraphWalk G c d} (hc : ∀ p, p ∈ W₁.support → p ∈ W₂.support → p = q) {e : β}
    (he₁ : e ∈ W₁.edges) : e ∉ W₂.edges := by
  intro he₂
  obtain ⟨u, v, huv⟩ : ∃ u v, G.IsLink e u v := by
    induction W₁ with
    | nil _ => simp [GraphWalk.edges] at he₁
    | @cons p r s f hlk rest ih =>
      simp only [GraphWalk.edges, List.mem_cons] at he₁
      rcases he₁ with rfl | h'
      · exact ⟨_, _, hlk⟩
      · exact ih (fun p h₁ h₂ => hc p (List.mem_cons_of_mem _ h₁) h₂) h'
  have h₁ := hc u (inc_mem_support W₁ he₁ ⟨v, huv⟩) (inc_mem_support W₂ he₂ ⟨v, huv⟩)
  have h₂ := hc v (inc_mem_support W₁ he₁ ⟨u, huv.symm⟩) (inc_mem_support W₂ he₂ ⟨u, huv.symm⟩)
  subst h₁
  subst h₂
  exact hl e _ huv

end Walks

section WalkSets

variable [T2Space S] {J : Drawing S}

/-- The point set of the part of `J` on a walk. -/
abbrev wU (J : Drawing S) {a b : S} (W : GraphWalk J.toGraph a b) : Set S := (walkDrawing J W).U

theorem mem_wU_of_support {a b p : S} {W : GraphWalk J.toGraph a b} (hp : p ∈ W.support) :
    p ∈ wU J W :=
  (mem_walkDrawing_U J W).mpr (Or.inl hp)

theorem closure_subset_wU {a b : S} {W : GraphWalk J.toGraph a b} {e : Set S} (he : e ∈ W.edges) :
    closure e ⊆ wU J W :=
  fun _ hp => (mem_walkDrawing_U J W).mpr (Or.inr ⟨e, he, hp⟩)

theorem subset_wU {a b : S} {W : GraphWalk J.toGraph a b} {e : Set S} (he : e ∈ W.edges) :
    e ⊆ wU J W :=
  subset_closure.trans (closure_subset_wU he)

theorem support_of_wU {a b p : S} {W : GraphWalk J.toGraph a b} (hp : p ∈ wU J W)
    (hv : p ∈ J.V) : p ∈ W.support := by
  have := mem_V_of_mem_U (walkDrawing_isSubdrawing J W) hv hp
  rwa [walkDrawing_V] at this

theorem wU_reverse {a b : S} (W : GraphWalk J.toGraph a b) : wU J W.reverse = wU J W := by
  ext p
  rw [mem_walkDrawing_U, mem_walkDrawing_U, GraphWalk.support_reverse, GraphWalk.edges_reverse]
  simp

theorem wU_append {a b c : S} (W₁ : GraphWalk J.toGraph a b) (W₂ : GraphWalk J.toGraph b c) :
    wU J (W₁.append W₂) = wU J W₁ ∪ wU J W₂ := by
  ext p
  simp only [mem_union, mem_walkDrawing_U, GraphWalk.mem_support_append, GraphWalk.edges_append,
    List.mem_append]
  constructor
  · rintro ((h | h) | ⟨e, he | he, hp⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inr ⟨e, he, hp⟩)
    · exact Or.inr (Or.inr ⟨e, he, hp⟩)
  · rintro ((h | ⟨e, he, hp⟩) | (h | ⟨e, he, hp⟩))
    · exact Or.inl (Or.inl h)
    · exact Or.inr ⟨e, Or.inl he, hp⟩
    · exact Or.inl (Or.inr h)
    · exact Or.inr ⟨e, Or.inr he, hp⟩

theorem wU_line {a b : S} {W : GraphWalk J.toGraph a b} (hW : W.IsSimple) (hab : a ≠ b) :
    IsLineWithEnds (wU J W) a b :=
  isLine_of_isPathBetween (walkDrawing_isPathBetween J hW) hab

/-- An edge of `J` that meets the part of `J` on a walk is an edge of the walk. -/
theorem edge_mem_of_meets {a b : S} {W : GraphWalk J.toGraph a b} {e : Set S} (he : e ∈ J.E)
    {p : S} (hpe : p ∈ e) (hp : p ∈ wU J W) : e ∈ W.edges := by
  by_contra hn
  have hdis := edge_disjoint_U (walkDrawing_isSubdrawing J W) he
    (by rw [walkDrawing_E]; exact hn)
  exact Set.disjoint_left.mp hdis hpe hp

/-- Two walks with no common edge meet only in common vertices. -/
theorem wU_inter {a b c d : S} {W : GraphWalk J.toGraph a b} {W' : GraphWalk J.toGraph c d}
    (hE : ∀ e ∈ W.edges, e ∉ W'.edges) :
    wU J W ∩ wU J W' = {p | p ∈ W.support ∧ p ∈ W'.support} := by
  rw [U_inter_of_disjoint (walkDrawing_isSubdrawing J W) (walkDrawing_isSubdrawing J W')
    (by rw [walkDrawing_E, walkDrawing_E, Set.disjoint_left]; exact hE),
    walkDrawing_V, walkDrawing_V]
  rfl

/-- An edge that misses the boundary of a disc is inside the disc or misses it. -/
theorem edge_side (hS : IsClosedSurface S) {D : Set S} (hD : IsClosedDisc D) {e : Set S}
    (he : e ∈ J.E) (hdis : Disjoint e (discBd D)) : e ⊆ D ∨ Disjoint e D :=
  subset_or_disjoint_of_frontier hD.isClosed he.2.2.1.isConnected.isPreconnected
    (by rwa [IsClosedDisc.frontier_eq_discBd hS hD])

end WalkSets

section Free

variable [T2Space S] {J : Drawing S}

/-- A circuit `C` of `J` is *peripheral* if the edges of `J` outside `C` form one bridge. -/
def IsPeripheral (J C : Drawing S) : Prop :=
  ∀ e ∈ J.E \ C.E, ∀ f ∈ J.E \ C.E, f ∈ cls J.toGraph C.V (J.E \ C.E) e

omit [T2Space S] in
theorem free_of_side {C : Drawing S} (hs : C.IsSubdrawing J)
    (hinc : ∀ v ∈ J.V, ∃ e ∈ J.E, J.toGraph.Inc e v) {Δ Δ' : Set S} (hdisj : Δ ∩ Δ' = C.U)
    (hcl : IsClosed Δ) (hM : ∀ e ∈ J.E \ C.E, e ⊆ Δ) : Disjoint (Δ' \ C.U) J.U := by
  rw [Set.disjoint_left]
  rintro p ⟨hp, hpC⟩ hpU
  have hoff : ∀ {e}, e ∈ J.E → e ∉ C.E → p ∈ closure e → False := fun {e} he hn hpe =>
    hpC (hdisj ▸ ⟨closure_minimal (hM e ⟨he, hn⟩) hcl hpe, hp⟩)
  by_cases hpV : p ∈ J.V
  · obtain ⟨e, he, ie⟩ := hinc p hpV
    refine hoff he (fun heC => hpC ?_) (mem_closure_of_inc ie)
    have hm : p ∈ closure e ∩ J.V := ⟨mem_closure_of_inc ie, hpV⟩
    rw [← hs.closure_inter_V heC] at hm
    exact C.V_subset_U hm.2
  · obtain ⟨e, he, hpe⟩ := J.exists_edge_of_mem hpU hpV
    refine hoff he (fun heC => hpC ?_) (subset_closure hpe)
    rw [C.U_eq]
    exact Or.inr (mem_iUnion₂.mpr ⟨e, heC, subset_closure hpe⟩)

omit [T2Space S] in
/-- All edges in a bridge of `C` lie on one side of `C`. -/
theorem cls_side {C : Drawing S} (hs : C.IsSubdrawing J) {Δ Δ' : Set S} (hdisj : Δ ∩ Δ' = C.U)
    (hcl : IsClosed Δ) (hcl' : IsClosed Δ') (hside : ∀ e ∈ J.E \ C.E, e ⊆ Δ ∨ e ⊆ Δ') {e₀ f : Set S}
    (he₀ : e₀ ⊆ Δ) (hf : f ∈ cls J.toGraph C.V (J.E \ C.E) e₀) : f ⊆ Δ := by
  induction hf with
  | refl => exact he₀
  | @tail a b _ hadj ih =>
    obtain ⟨-, hb, w, hw, ia, ib⟩ := hadj
    rcases hside b hb with h' | h'
    · exact h'
    · exfalso
      have hwΔ : w ∈ Δ := closure_minimal ih hcl (mem_closure_of_inc ia)
      have hwΔ' : w ∈ Δ' := closure_minimal h' hcl' (mem_closure_of_inc ib)
      have hwU : w ∈ C.U := hdisj ▸ ⟨hwΔ, hwΔ'⟩
      exact hw (mem_V_of_mem_U hs ia.vertex_mem hwU)

/-- A peripheral circuit bounds a disc whose interior misses `J`. -/
theorem exists_free_side_of_peripheral (hS : IsSphere S) {C : Drawing S} (hC : C.IsCircuit)
    (hs : C.IsSubdrawing J) (hinc : ∀ v ∈ J.V, ∃ e ∈ J.E, J.toGraph.Inc e v)
    (hP : IsPeripheral J C) :
    ∃ D : Set S, IsClosedDisc D ∧ discBd D = C.U ∧ Disjoint (D \ discBd D) J.U := by
  have hcl := (IsSphere.isClosedSurface hS).1
  obtain ⟨Δ₁, Δ₂, -, hd₁, hd₂, hb₁, hb₂, hun, hint, -, -⟩ :=
    sphere_disc S hS C.U (GM11.IsCircuit.isOArc_U hC)
  have hside : ∀ e ∈ J.E \ C.E, e ⊆ Δ₁ ∨ e ⊆ Δ₂ := by
    rintro e ⟨he, hn⟩
    have hdis : Disjoint e (discBd Δ₁) := by
      rw [hb₁]
      exact edge_disjoint_U hs he hn
    rcases edge_side hcl hd₁ he hdis with h' | h'
    · exact Or.inl h'
    · refine Or.inr fun p hp => ?_
      have : p ∈ Δ₁ ∪ Δ₂ := by rw [hun]; exact mem_univ p
      exact this.resolve_left (Set.disjoint_left.mp h' hp)
  have hint' : Δ₂ ∩ Δ₁ = C.U := by rw [inter_comm]; exact hint
  by_cases hM : (J.E \ C.E).Nonempty
  · obtain ⟨e₀, he₀⟩ := hM
    rcases hside e₀ he₀ with h' | h'
    · refine ⟨Δ₂, hd₂, hb₂, ?_⟩
      rw [hb₂]
      exact free_of_side hs hinc hint hd₁.isClosed fun e he =>
        cls_side hs hint hd₁.isClosed hd₂.isClosed hside h' (hP e₀ he₀ e he)
    · refine ⟨Δ₁, hd₁, hb₁, ?_⟩
      rw [hb₁]
      refine free_of_side hs hinc hint' hd₂.isClosed fun e he =>
        cls_side hs hint' hd₂.isClosed hd₁.isClosed (fun a ha => (hside a ha).symm) h'
          (hP e₀ he₀ e he)
  · refine ⟨Δ₂, hd₂, hb₂, ?_⟩
    rw [hb₂]
    exact free_of_side hs hinc hint hd₁.isClosed fun e he => (hM ⟨e, he⟩).elim

end Free

section Main

variable [T2Space S] {J C₀ : Drawing S} {Δ : Set S} {c : Set (Set S)}

/-- The set up for showing that a circuit `C₀` with all of `J` on one side `Δ` is peripheral. Here
`c` is a bridge of `C₀`. -/
structure Env (J C₀ : Drawing S) (Δ : Set S) (c : Set (Set S)) : Prop where
  circ : C₀.IsCircuit
  sub : C₀.IsSubdrawing J
  U : J.U ⊆ Δ
  cE : ∀ e ∈ c, e ∈ J.E ∧ e ∉ C₀.E
  stepc : ∀ e f, e ∈ c → adj J.toGraph C₀.V (J.E \ C₀.E) e f → f ∈ c

/-- A disc `D` cut from `Δ` by a path `T` in the bridge `c`, with boundary `T` and a path `Q` of
`C₀`. It contains an edge `g` that is not in `T`, `Q` or `c`. We show that no such disc exists,
by taking one with the fewest edges. -/
structure Cand (J C₀ : Drawing S) (Δ : Set S) (c : Set (Set S)) (g D D' : Set S) {x y : S}
    (T Q : GraphWalk J.toGraph x y) : Prop where
  ne : x ≠ y
  hT : T.IsSimple
  hQ : Q.IsSimple
  disc : IsClosedDisc D
  closed : IsClosed D'
  union : D ∪ D' = Δ
  inter : D ∩ D' = wU J T
  bd : discBd D = wU J T ∪ wU J Q
  Tc : ∀ e ∈ T.edges, e ∈ c
  QC : ∀ e ∈ Q.edges, e ∈ C₀.E
  Tbd : wU J T ∩ C₀.U = {x, y}
  Qbd : C₀.U ∩ D = wU J Q
  gE : g ∈ J.E
  gD : g ⊆ D
  gT : g ∉ T.edges
  gQ : g ∉ Q.edges
  gc : g ∉ c

/-- The edges strictly inside `D`, with those on `Q` and `T` left out. -/
def MM (J : Drawing S) (D : Set S) {x y : S} (T Q : GraphWalk J.toGraph x y) : Set (Set S) :=
  {e | e ∈ J.E ∧ e ⊆ D ∧ e ∉ T.edges ∧ e ∉ Q.edges}

/-- The vertices on the boundary of `D`. -/
def BB {J : Drawing S} {x y : S} (T Q : GraphWalk J.toGraph x y) : Set S :=
  {p | p ∈ T.support ∨ p ∈ Q.support}

/-- The bridge of `e` inside `D`. -/
abbrev icls (J : Drawing S) (D : Set S) {x y : S} (T Q : GraphWalk J.toGraph x y) (e : Set S) :
    Set (Set S) :=
  cls J.toGraph (BB T Q) (MM J D T Q) e

/-- The bridge of `e` inside `D` meets the walk `W` at a vertex other than its ends. -/
def Att (J : Drawing S) (D : Set S) {x y a b : S} (T Q : GraphWalk J.toGraph x y)
    (W : GraphWalk J.toGraph a b) (e : Set S) : Prop :=
  ∃ f ∈ icls J D T Q e, ∃ z ∈ W.support, z ≠ a ∧ z ≠ b ∧ J.toGraph.Inc f z

namespace Cand

variable {g D D' : Set S} {x y : S} {T Q : GraphWalk J.toGraph x y}

theorem symm (hc : Cand J C₀ Δ c g D D' T Q) : Cand J C₀ Δ c g D D' T.reverse Q.reverse where
  ne := hc.ne.symm
  hT := hc.hT.reverse
  hQ := hc.hQ.reverse
  disc := hc.disc
  closed := hc.closed
  union := hc.union
  inter := by rw [wU_reverse]; exact hc.inter
  bd := by rw [wU_reverse, wU_reverse]; exact hc.bd
  Tc e he := hc.Tc e (by rwa [GraphWalk.edges_reverse, List.mem_reverse] at he)
  QC e he := hc.QC e (by rwa [GraphWalk.edges_reverse, List.mem_reverse] at he)
  Tbd := by rw [wU_reverse, pair_comm]; exact hc.Tbd
  Qbd := by rw [wU_reverse]; exact hc.Qbd
  gE := hc.gE
  gD := hc.gD
  gT := by rw [GraphWalk.edges_reverse, List.mem_reverse]; exact hc.gT
  gQ := by rw [GraphWalk.edges_reverse, List.mem_reverse]; exact hc.gQ
  gc := hc.gc

theorem wT_sub (hc : Cand J C₀ Δ c g D D' T Q) : wU J T ⊆ D :=
  fun _ hp => Surface.discBd_subset D (hc.bd ▸ Or.inl hp)

theorem wQ_sub (hc : Cand J C₀ Δ c g D D' T Q) : wU J Q ⊆ D :=
  fun _ hp => Surface.discBd_subset D (hc.bd ▸ Or.inr hp)

theorem wQ_sub_C (hc : Cand J C₀ Δ c g D D' T Q) : wU J Q ⊆ C₀.U :=
  fun _ hp => (hc.Qbd ▸ hp : _ ∈ C₀.U ∩ D).1

theorem cap (hc : Cand J C₀ Δ c g D D' T Q) (p : S) (h₁ : p ∈ T.support) (h₂ : p ∈ Q.support) :
    p = x ∨ p = y := by
  have : p ∈ wU J T ∩ C₀.U := ⟨mem_wU_of_support h₁, hc.wQ_sub_C (mem_wU_of_support h₂)⟩
  rw [hc.Tbd] at this
  exact this

theorem offE (hc : Cand J C₀ Δ c g D D' T Q) {e : Set S} (he : e ∈ J.E) (hT : e ∉ T.edges)
    (hQ : e ∉ Q.edges) : Disjoint e (discBd D) := by
  rw [hc.bd]
  exact Set.disjoint_union_right.mpr
    ⟨edge_disjoint_U (walkDrawing_isSubdrawing J T) he (by rw [walkDrawing_E]; exact hT),
      edge_disjoint_U (walkDrawing_isSubdrawing J Q) he (by rw [walkDrawing_E]; exact hQ)⟩

/-- An edge at a vertex of `D` off `T` lies in `D`, unless it is an edge of `Q`. -/
theorem mem_MM (hS : IsClosedSurface S) (hE : Env J C₀ Δ c) (hc : Cand J C₀ Δ c g D D' T Q)
    {v : S} {e : Set S} (hvT : v ∉ T.support) (hvD : v ∈ D) (he : e ∈ J.E)
    (hi : J.toGraph.Inc e v) (hQ : e ∉ Q.edges) : e ∈ MM J D T Q := by
  have hT : e ∉ T.edges := fun h' => hvT (inc_mem_support T h' hi)
  refine ⟨he, ?_, hT, hQ⟩
  rcases edge_side hS hc.disc he (hc.offE he hT hQ) with h' | h'
  · exact h'
  · exfalso
    have heD' : e ⊆ D' := by
      intro p hp
      have hpU : p ∈ J.U := (he.2.1 hp).1
      have : p ∈ D ∪ D' := by rw [hc.union]; exact hE.U hpU
      exact this.resolve_left (Set.disjoint_left.mp h' hp)
    have hvD' : v ∈ D' := closure_minimal heD' hc.closed (mem_closure_of_inc hi)
    have hvU : v ∈ wU J T := hc.inter ▸ ⟨hvD, hvD'⟩
    exact hvT (support_of_wU hvU hi.vertex_mem)

theorem MM_not_C (hc : Cand J C₀ Δ c g D D' T Q) {e : Set S} (he : e ∈ MM J D T Q) :
    e ∉ C₀.E := by
  intro heC
  obtain ⟨p, hp⟩ : e.Nonempty := he.1.1
  have hpU : p ∈ C₀.U := by
    rw [C₀.U_eq]
    exact Or.inr (mem_iUnion₂.mpr ⟨e, heC, subset_closure hp⟩)
  exact he.2.2.2 (edge_mem_of_meets he.1 hp (hc.Qbd ▸ ⟨hpU, he.2.1 hp⟩))

theorem off_V (hc : Cand J C₀ Δ c g D D' T Q) {p : S} (hp : p ∉ BB T Q)
    (hpD : p ∈ D) (hpJ : p ∈ J.V) : p ∉ C₀.V := by
  intro hpC
  have hm : p ∈ wU J Q := hc.Qbd ▸ ⟨C₀.V_subset_U hpC, hpD⟩
  exact hp (Or.inr (support_of_wU hm hpJ))

theorem cls_sub (hE : Env J C₀ Δ c) (hc : Cand J C₀ Δ c g D D' T Q) {a b : Set S} (ha : a ∈ c)
    (hb : b ∈ icls J D T Q a) : b ∈ c := by
  induction hb with
  | refl => exact ha
  | @tail p q _ hadj ih =>
    obtain ⟨hp, hq, w, hw, i₁, i₂⟩ := hadj
    have hwD : w ∈ D := closure_minimal hp.2.1 hc.disc.isClosed (mem_closure_of_inc i₁)
    exact hE.stepc p q ih ⟨⟨hp.1, hc.MM_not_C hp⟩, ⟨hq.1, hc.MM_not_C hq⟩, w,
      hc.off_V hw hwD i₁.vertex_mem, i₁, i₂⟩

/-- A bridge inside `D` that meets the inside of `T` belongs to `c`. -/
theorem att_c (hE : Env J C₀ Δ c) (hc : Cand J C₀ Δ c g D D' T Q) {a : Set S}
    (ha : a ∈ MM J D T Q) (hatt : Att J D T Q T a) : a ∈ c := by
  obtain ⟨f, hf, z, hz, hzx, hzy, iz⟩ := hatt
  obtain ⟨t, ht, -, -, -, it, -⟩ := exists_two_edges_at_inner T hc.hT hz hzx hzy
  have htc := hc.Tc t ht
  have hfM : f ∈ MM J D T Q := cls_subset ha hf
  have hzC : z ∉ C₀.V := by
    intro hzC
    have : z ∈ wU J T ∩ C₀.U := ⟨mem_wU_of_support hz, C₀.V_subset_U hzC⟩
    rw [hc.Tbd] at this
    rcases this with h' | h'
    · exact hzx h'
    · exact hzy h'
  have hfc : f ∈ c := hE.stepc t f htc
    ⟨hE.cE t htc, ⟨hfM.1, hc.MM_not_C hfM⟩, z, hzC, it, iz⟩
  exact hc.cls_sub hE hfc (cls_symm hf)

/-- The first end of `T` is a branch vertex, with an edge of `C₀` outside `Q`. -/
theorem start_data {G₀ : Graph S (Set S)} {P : Set S → Graph S (Set S)}
    (h : SubData J.toGraph G₀ P) (hE : Env J C₀ Δ c) (hc : Cand J C₀ Δ c g D D' T Q) :
    x ∈ V(G₀) ∧ (∃ t ∈ T.edges, J.toGraph.Inc t x) ∧
      ∃ k ∈ C₀.E, J.toGraph.Inc k x ∧ k ∉ Q.edges := by
  have hxU : x ∈ wU J T ∩ C₀.U := by rw [hc.Tbd]; exact Or.inl rfl
  have hxV : x ∈ C₀.V := mem_V_of_mem_U hE.sub
    (T.mem_vertexSet_of_mem_support T.start_mem_support) hxU.2
  obtain ⟨k₁, hk₁, k₂, hk₂, hne, i₁, i₂⟩ := circuit_two_edges h hE.circ hE.sub hxV
  obtain ⟨t, ht, it⟩ := exists_edge_at_start T hc.ne
  have htc := hE.cE t (hc.Tc t ht)
  refine ⟨h.mem_V₀_of_three htc.1 (hE.sub.2 hk₁) (hE.sub.2 hk₂) it i₁ i₂
      (fun h' => htc.2 (h' ▸ hk₁)) (fun h' => htc.2 (h' ▸ hk₂)) hne, ⟨t, ht, it⟩, ?_⟩
  by_cases hk : k₁ ∈ Q.edges
  · refine ⟨k₂, hk₂, i₂, fun hk' => hne ?_⟩
    have hconv : ∀ {a}, J.toGraph.Inc a x → J.toGraph.Inc a x := id
    exact eq_of_inc_start Q hc.hQ hk hk' (hconv i₁) (hconv i₂)
  · exact ⟨k₁, hk₁, i₁, hk⟩

/-- If no bridge inside `D` joins the inside of `T` to the inside of `Q`, then the edges on the `Q`
side form a side of a separation with `x` and `y` as its middle. By 3-connectivity that side is a
single path `Q`, which leaves no room for `g`. -/
theorem caseB {G₀ : Graph S (Set S)} {P : Set S → Graph S (Set S)} (hS : IsClosedSurface S)
    (h : SubData J.toGraph G₀ P) (hE : Env J C₀ Δ c) (hc : Cand J C₀ Δ c g D D' T Q)
    (hno : ∀ e ∈ MM J D T Q, Att J D T Q T e → Att J D T Q Q e → False) : False := by
  classical
  set X : Set (Set S) := {e | e ∈ Q.edges} ∪ {e | e ∈ MM J D T Q ∧ ¬ Att J D T Q T e} with hX
  have hedgeJ : ∀ e ∈ Q.edges, e ∈ J.E := fun e he => hE.sub.2 (hc.QC e he)
  have hXE : X ⊆ E(J.toGraph) := by
    rintro e (he | he)
    · exact hedgeJ e he
    · exact he.1.1
  have hgM : g ∈ MM J D T Q := ⟨hc.gE, hc.gD, hc.gT, hc.gQ⟩
  have hgX : g ∈ X := Or.inr ⟨hgM, fun hatt => hc.gc (hc.att_c hE hgM hatt)⟩
  have hbd : bdry J.toGraph X ⊆ {x, y} := by
    rintro v ⟨⟨a, ha, hia⟩, f, ⟨hfE, hfX⟩, hif⟩
    by_contra hvxy
    have hvx : v ≠ x := fun h' => hvxy (Or.inl h')
    have hvy : v ≠ y := fun h' => hvxy (Or.inr h')
    have hfQ : f ∉ Q.edges := fun h' => hfX (Or.inl h')
    have key : f ∈ MM J D T Q → Att J D T Q T f := fun hfM => by
      by_contra hn
      exact hfX (Or.inr ⟨hfM, hn⟩)
    rcases ha with haQ | ⟨haM, hna⟩
    · have hvQ : v ∈ Q.support := inc_mem_support Q haQ hia
      have hvT : v ∉ T.support := fun hvT => (hc.cap v hvT hvQ).elim hvx hvy
      have fM := hc.mem_MM hS hE hvT (hc.wQ_sub (mem_wU_of_support hvQ)) hfE hif hfQ
      exact hno f fM (key fM) ⟨f, mem_cls_self, v, hvQ, hvx, hvy, hif⟩
    · by_cases hvT : v ∈ T.support
      · exact hna ⟨a, mem_cls_self, v, hvT, hvx, hvy, hia⟩
      · have hvD : v ∈ D := closure_minimal haM.2.1 hc.disc.isClosed (mem_closure_of_inc hia)
        have fM := hc.mem_MM hS hE hvT hvD hfE hif hfQ
        have hatt := key fM
        by_cases hvQ : v ∈ Q.support
        · exact hno f fM hatt ⟨f, mem_cls_self, v, hvQ, hvx, hvy, hif⟩
        · have hvB : v ∉ BB T Q := fun h' => h'.elim hvT hvQ
          have hfa : f ∈ icls J D T Q a :=
            Relation.ReflTransGen.single ⟨haM, fM, v, hvB, hia, hif⟩
          obtain ⟨p, hp, r⟩ := hatt
          exact hna ⟨p, cls_trans hfa hp, r⟩
  obtain ⟨hx₀, ⟨t, ht, it⟩, k, hk, ik, hkQ⟩ := hc.start_data h hE
  obtain ⟨hy₀, -⟩ := hc.symm.start_data h hE
  have htc := hE.cE t (hc.Tc t ht)
  have htn : t ∉ X := by
    rintro (h' | h')
    · exact htc.2 (hc.QC t h')
    · exact h'.1.2.2.1 ht
  have hkn : k ∉ X := by
    rintro (h' | h')
    · exact hkQ h'
    · exact hc.MM_not_C h'.1 hk
  have hpair : ({x, y} : Set S).ncard = 2 := Set.ncard_pair hc.ne
  obtain ⟨e, he, heq | heq⟩ := h.sep hXE
    (hbd.trans (by rintro p (rfl | rfl); exacts [hx₀, hy₀]))
    (by rw [← hpair]; exact Set.ncard_le_ncard hbd (Set.toFinite _)) ⟨g, hgX⟩ ⟨t, htc.1, htn⟩
  · have hsub := h.thread_subset he hx₀ hy₀ hc.ne Q hc.hQ fun a ha => by
      rw [← heq]
      exact Or.inl ha
    exact hc.gQ (hsub (heq ▸ hgX))
  · have ht' : t ∈ E(J.toGraph) \ X := ⟨htc.1, htn⟩
    have hk' : k ∈ E(J.toGraph) \ X := ⟨hE.sub.2 hk, hkn⟩
    rw [heq] at ht' hk'
    have := h.eq_of_end he hx₀ ht' hk' it ik
    exact htc.2 (this ▸ hk)

/-- A path `R` in the bridge `c` from the inside of `T` to the inside of `Q` cuts `D` in two. The
part
that holds `g` is a smaller candidate. -/
theorem shrink (hc : Cand J C₀ Δ c g D D' T Q) {z w : S}
    {T₁ : GraphWalk J.toGraph x z} {T₂ : GraphWalk J.toGraph z y}
    {Q₁ : GraphWalk J.toGraph x w} {Q₂ : GraphWalk J.toGraph w y} {R : GraphWalk J.toGraph z w}
    (hTu : wU J T = wU J T₁ ∪ wU J T₂) (hQu : wU J Q = wU J Q₁ ∪ wU J Q₂)
    (hsT₁ : T₁.IsSimple) (hsQ₁ : Q₁.IsSimple) (hsR : R.IsSimple)
    (hT₁ : ∀ p, p ∈ T₁.support → p ∈ T.support) (hT₁e : ∀ e, e ∈ T₁.edges → e ∈ T.edges)
    (hT₂ : ∀ p, p ∈ T₂.support → p ∈ T.support)
    (hQ₁ : ∀ p, p ∈ Q₁.support → p ∈ Q.support) (hQ₁e : ∀ e, e ∈ Q₁.edges → e ∈ Q.edges)
    (hQ₂ : ∀ p, p ∈ Q₂.support → p ∈ Q.support)
    (hTcap : ∀ p, p ∈ T₁.support → p ∈ T₂.support → p = z)
    (hRin : ∀ p ∈ R.support, (p ∉ T.support ∧ p ∉ Q.support) ∨ p = z ∨ p = w)
    (hRc : ∀ e ∈ R.edges, e ∈ c) (hRT : ∀ e ∈ R.edges, e ∉ T.edges)
    (hRQ : ∀ e ∈ R.edges, e ∉ Q.edges)
    (hzy : z ≠ y) (hwx : w ≠ x) (hwT : w ∉ T.support) (hzQ : z ∉ Q.support)
    {E₁ E₂ : Set S} (hE₁ : IsClosedDisc E₁) (hE₂ : IsClosedDisc E₂) (hun : E₁ ∪ E₂ = D)
    (hint : E₁ ∩ E₂ = wU J R) (hb₁ : discBd E₁ = (wU J T₁ ∪ wU J Q₁) ∪ wU J R)
    (hb₂ : discBd E₂ = (wU J T₂ ∪ wU J Q₂) ∪ wU J R) (hg : g ⊆ E₁) :
    Cand J C₀ Δ c g E₁ (E₂ ∪ D') (T₁.append R) Q₁ ∧
      {e | e ∈ J.E ∧ e ⊆ E₁} ⊂ {e | e ∈ J.E ∧ e ⊆ D} := by
  have hsub₁ : E₁ ⊆ D := hun ▸ subset_union_left
  have hb₁' : discBd E₁ ⊆ E₁ := Surface.discBd_subset _
  have hb₂' : discBd E₂ ⊆ E₂ := Surface.discBd_subset _
  have hTinE₁ : wU J T₁ ⊆ E₁ := fun p hp => hb₁' (hb₁ ▸ Or.inl (Or.inl hp))
  have hQinE₁ : wU J Q₁ ⊆ E₁ := fun p hp => hb₁' (hb₁ ▸ Or.inl (Or.inr hp))
  have hTinE₂ : wU J T₂ ⊆ E₂ := fun p hp => hb₂' (hb₂ ▸ Or.inl (Or.inl hp))
  have hQinE₂ : wU J Q₂ ⊆ E₂ := fun p hp => hb₂' (hb₂ ▸ Or.inl (Or.inr hp))
  have hRC : ∀ p, p ∈ wU J R → p ∈ C₀.U → p = w := by
    intro p hp hpC
    have hRD : p ∈ D := hsub₁ (hb₁' (hb₁ ▸ Or.inr hp))
    have hpQ : p ∈ wU J Q := hc.Qbd ▸ ⟨hpC, hRD⟩
    have hm : p ∈ wU J R ∩ wU J Q := ⟨hp, hpQ⟩
    rw [wU_inter hRQ] at hm
    rcases hRin p hm.1 with h' | h' | h'
    · exact (h'.2 hm.2).elim
    · exact (hzQ (h' ▸ hm.2)).elim
    · exact h'
  have hwQ₁ : w ∈ wU J Q₁ := mem_wU_of_support Q₁.end_mem_support
  have hyT₁ : y ∉ wU J T₁ := by
    intro hy
    have hyJ : y ∈ J.V := T.mem_vertexSet_of_mem_support T.end_mem_support
    exact hzy (hTcap y (support_of_wU hy hyJ) T₂.end_mem_support).symm
  refine ⟨?_, ⟨fun e he => ⟨he.1, he.2.trans hsub₁⟩, fun hle => ?_⟩⟩
  · refine ⟨hwx.symm, isSimple_append T₁ R hsT₁ hsR ?_, hsQ₁, hE₁, hE₂.isClosed.union hc.closed,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, hc.gE, hg, ?_, ?_, hc.gc⟩
    · intro p h₁ h₂
      rcases hRin p h₂ with h' | h' | h'
      · exact (h'.1 (hT₁ p h₁)).elim
      · exact h'
      · exact (hwT (h' ▸ hT₁ p h₁)).elim
    · rw [← union_assoc, hun]
      exact hc.union
    · rw [wU_append, inter_union_distrib_left, hint]
      refine Subset.antisymm ?_ ?_
      · rintro p (hp | ⟨hp₁, hp₂⟩)
        · exact Or.inr hp
        · have hpT : p ∈ wU J T := hc.inter ▸ ⟨hsub₁ hp₁, hp₂⟩
          rw [hTu] at hpT
          rcases hpT with h' | h'
          · exact Or.inl h'
          · exact Or.inr (hint ▸ ⟨hp₁, hTinE₂ h'⟩)
      · rintro p (hp | hp)
        · have hpT : p ∈ D ∩ D' := by
            rw [hc.inter, hTu]
            exact Or.inl hp
          exact Or.inr ⟨hTinE₁ hp, hpT.2⟩
        · exact Or.inl hp
    · rw [hb₁, wU_append]
      ext p
      simp only [mem_union]
      tauto
    · intro e he
      rw [GraphWalk.edges_append, List.mem_append] at he
      rcases he with he | he
      · exact hc.Tc e (hT₁e e he)
      · exact hRc e he
    · exact fun e he => hc.QC e (hQ₁e e he)
    · rw [wU_append]
      refine Subset.antisymm ?_ ?_
      · rintro p ⟨hp | hp, hpC⟩
        · have hm : p ∈ wU J T ∩ C₀.U := ⟨hTu ▸ Or.inl hp, hpC⟩
          rw [hc.Tbd] at hm
          rcases hm with h' | h'
          · exact Or.inl h'
          · exact (hyT₁ (h' ▸ hp)).elim
        · exact Or.inr (hRC p hp hpC)
      · rintro p (rfl | rfl)
        · refine ⟨Or.inl (mem_wU_of_support T₁.start_mem_support), ?_⟩
          exact hc.wQ_sub_C (hQu ▸ Or.inl (mem_wU_of_support Q₁.start_mem_support))
        · exact ⟨Or.inr (mem_wU_of_support R.end_mem_support),
            hc.wQ_sub_C (hQu ▸ Or.inl hwQ₁)⟩
    · refine Subset.antisymm ?_ ?_
      · rintro p ⟨hpC, hpE⟩
        have hpQ : p ∈ wU J Q := hc.Qbd ▸ ⟨hpC, hsub₁ hpE⟩
        rw [hQu] at hpQ
        rcases hpQ with h' | h'
        · exact h'
        · have hpR : p ∈ wU J R := hint ▸ ⟨hpE, hQinE₂ h'⟩
          exact (hRC p hpR hpC) ▸ hwQ₁
      · exact fun p hp => ⟨hc.wQ_sub_C (hQu ▸ Or.inl hp), hQinE₁ hp⟩
    · rw [GraphWalk.edges_append, List.mem_append]
      rintro (h' | h')
      · exact hc.gT (hT₁e g h')
      · exact hc.gc (hRc g h')
    · exact fun h' => hc.gQ (hQ₁e g h')
  · obtain ⟨t, ht, -⟩ := exists_edge_at_start T₂ hzy
    have htJ : t ∈ J.E := (walkDrawing_isSubdrawing J T₂).2 (by rw [walkDrawing_E]; exact ht)
    have htE₂ : t ⊆ E₂ := (subset_wU ht).trans hTinE₂
    have htD : t ⊆ D := htE₂.trans (hun ▸ subset_union_right)
    have htE₁ : t ⊆ E₁ := (hle ⟨htJ, htD⟩).2
    obtain ⟨p, hp⟩ : t.Nonempty := htJ.1
    have htR : t ∈ R.edges := edge_mem_of_meets htJ hp (hint ▸ ⟨htE₁ hp, htE₂ hp⟩)
    have htT : t ∈ T.edges := by
      by_contra hn
      have hdis := edge_disjoint_U (walkDrawing_isSubdrawing J T) htJ
        (by rw [walkDrawing_E]; exact hn)
      apply Set.disjoint_left.mp hdis hp
      change p ∈ wU J T
      rw [hTu]
      exact Or.inr (subset_wU ht hp)
    exact hRT t htR htT

omit [T2Space S] in
/-- The support of a walk lies in a closed set that holds its start and its edges. -/
theorem support_subset_of_edges {X : Set S} (hX : IsClosed X) {a b : S}
    (W : GraphWalk J.toGraph a b) (ha : a ∈ X) (hW : ∀ e ∈ W.edges, e ⊆ X) :
    ∀ p ∈ W.support, p ∈ X := by
  induction W with
  | nil _ =>
    intro p hp
    simp only [GraphWalk.support, List.mem_singleton] at hp
    exact hp ▸ ha
  | @cons u v w f hl rest ih =>
    intro p hp
    have hf : f ⊆ X := hW f (by simp [GraphWalk.edges])
    have hv : v ∈ X := closure_minimal hf hX (mem_closure_of_inc ⟨u, hl.symm⟩)
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ha
    · exact ih hv (fun e he => hW e (List.mem_cons_of_mem _ he)) p hp

/-- There is no candidate. The proof takes one with the fewest edges in `D`. -/
theorem false_aux {G₀ : Graph S (Set S)} {P : Set S → Graph S (Set S)} (hS : IsClosedSurface S)
    (h : SubData J.toGraph G₀ P) (hE : Env J C₀ Δ c) :
    ∀ n : ℕ, ∀ (D D' : Set S) (x y : S) (T Q : GraphWalk J.toGraph x y),
      Cand J C₀ Δ c g D D' T Q → {e | e ∈ J.E ∧ e ⊆ D}.ncard = n → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro D D' x y T Q hc hn
    by_cases hex : ∃ e ∈ MM J D T Q, Att J D T Q T e ∧ Att J D T Q Q e
    swap
    · exact hc.caseB hS h hE fun e he h₁ h₂ => hex ⟨e, he, h₁, h₂⟩
    obtain ⟨e, heM, hatT, hatQ⟩ := hex
    have hnl : ∀ (e : Set S) (u : S), ¬ J.toGraph.IsLink e u u := fun e u => fun hl => no_loop h hl
    obtain ⟨f₁, hf₁, z, hzT, hzx, hzy, iz⟩ := hatT
    obtain ⟨f₂, hf₂, w, hwQ, hwx, hwy, iw⟩ := hatQ
    obtain ⟨z', hl⟩ := id iz
    have hf₁M : f₁ ∈ MM J D T Q := cls_subset heM hf₁
    have hf₁c : f₁ ∈ c := hc.att_c hE hf₁M ⟨f₁, mem_cls_self, z, hzT, hzx, hzy, iz⟩
    obtain ⟨W, hWe, hWs⟩ := exists_walk_in_cls hf₁M (mem_cls_self (e := f₁)) hl
      (cls_trans (cls_symm hf₁) hf₂) iw
    obtain ⟨R, hsR, hRs, hRe⟩ := GM09.exists_isSimple_subwalk W
    have hRM : ∀ a ∈ R.edges, a ∈ MM J D T Q := fun a ha => cls_subset hf₁M (hWe a (hRe a ha))
    have hRc : ∀ a ∈ R.edges, a ∈ c := fun a ha => hc.cls_sub hE hf₁c (hWe a (hRe a ha))
    have hRin : ∀ p ∈ R.support, (p ∉ T.support ∧ p ∉ Q.support) ∨ p = z ∨ p = w := by
      intro p hp
      rcases hWs p (hRs p hp) with h' | h'
      · exact Or.inl ⟨fun h₁ => h' (Or.inl h₁), fun h₁ => h' (Or.inr h₁)⟩
      · exact Or.inr h'
    obtain ⟨T₁, T₂, hTa⟩ := T.exists_append_of_mem hzT
    obtain ⟨Q₁, Q₂, hQa⟩ := Q.exists_append_of_mem hwQ
    have hTs := hc.hT
    have hQs := hc.hQ
    rw [hTa] at hTs
    rw [hQa] at hQs
    obtain ⟨hsT₁, hsT₂⟩ := GM09.isSimple_of_append hTs
    obtain ⟨hsQ₁, hsQ₂⟩ := GM09.isSimple_of_append hQs
    have hTcap := append_cap hTs
    have hQcap := append_cap hQs
    have hTm : ∀ p, p ∈ T.support ↔ p ∈ T₁.support ∨ p ∈ T₂.support := fun p => by
      rw [hTa, GraphWalk.mem_support_append]
    have hQm : ∀ p, p ∈ Q.support ↔ p ∈ Q₁.support ∨ p ∈ Q₂.support := fun p => by
      rw [hQa, GraphWalk.mem_support_append]
    have hTe : ∀ a, a ∈ T.edges ↔ a ∈ T₁.edges ∨ a ∈ T₂.edges := fun a => by
      rw [hTa, GraphWalk.edges_append, List.mem_append]
    have hQe : ∀ a, a ∈ Q.edges ↔ a ∈ Q₁.edges ∨ a ∈ Q₂.edges := fun a => by
      rw [hQa, GraphWalk.edges_append, List.mem_append]
    have hTu : wU J T = wU J T₁ ∪ wU J T₂ := by rw [hTa, wU_append]
    have hQu : wU J Q = wU J Q₁ ∪ wU J Q₂ := by rw [hQa, wU_append]
    have hzQ : z ∉ Q.support := fun h' => (hc.cap z hzT h').elim hzx hzy
    have hwT : w ∉ T.support := fun h' => (hc.cap w h' hwQ).elim hwx hwy
    have hzw : z ≠ w := fun h' => hwT (h' ▸ hzT)
    have hTQe : ∀ a ∈ T.edges, a ∉ Q.edges := fun a ha ha' => (hE.cE a (hc.Tc a ha)).2 (hc.QC a ha')
    set A := T₁.reverse.append Q₁ with hA
    set B := T₂.append Q₂.reverse with hB
    have hsA : A.IsSimple := by
      refine isSimple_append _ _ hsT₁.reverse hsQ₁ fun p h₁ h₂ => ?_
      rw [GraphWalk.support_reverse, List.mem_reverse] at h₁
      rcases hc.cap p ((hTm p).mpr (Or.inl h₁)) ((hQm p).mpr (Or.inl h₂)) with h' | h'
      · exact h'
      · subst h'
        exact (hzy (hTcap _ h₁ T₂.end_mem_support).symm).elim
    have hsB : B.IsSimple := by
      refine isSimple_append _ _ hsT₂ hsQ₂.reverse fun p h₁ h₂ => ?_
      rw [GraphWalk.support_reverse, List.mem_reverse] at h₂
      rcases hc.cap p ((hTm p).mpr (Or.inr h₁)) ((hQm p).mpr (Or.inr h₂)) with h' | h'
      · subst h'
        exact (hzx (hTcap _ T₁.start_mem_support h₁).symm).elim
      · exact h'
    have hAu : wU J A = wU J T₁ ∪ wU J Q₁ := by rw [hA, wU_append, wU_reverse]
    have hBu : wU J B = wU J T₂ ∪ wU J Q₂ := by rw [hB, wU_append, wU_reverse]
    have hAs : ∀ p, p ∈ A.support ↔ p ∈ T₁.support ∨ p ∈ Q₁.support := fun p => by
      rw [hA, GraphWalk.mem_support_append, GraphWalk.support_reverse, List.mem_reverse]
    have hBs : ∀ p, p ∈ B.support ↔ p ∈ T₂.support ∨ p ∈ Q₂.support := fun p => by
      rw [hB, GraphWalk.mem_support_append, GraphWalk.support_reverse, List.mem_reverse]
    have hAe : ∀ a, a ∈ A.edges ↔ a ∈ T₁.edges ∨ a ∈ Q₁.edges := fun a => by
      rw [hA, GraphWalk.edges_append, GraphWalk.edges_reverse, List.mem_append, List.mem_reverse]
    have hBe : ∀ a, a ∈ B.edges ↔ a ∈ T₂.edges ∨ a ∈ Q₂.edges := fun a => by
      rw [hB, GraphWalk.edges_append, GraphWalk.edges_reverse, List.mem_append, List.mem_reverse]
    have hABe : ∀ a ∈ A.edges, a ∉ B.edges := by
      intro a ha hb
      rcases (hAe a).mp ha with h₁ | h₁ <;> rcases (hBe a).mp hb with h₂ | h₂
      · exact edge_not_mem_of_cap hnl hTcap h₁ h₂
      · exact hTQe a ((hTe a).mpr (Or.inl h₁)) ((hQe a).mpr (Or.inr h₂))
      · exact hTQe a ((hTe a).mpr (Or.inr h₂)) ((hQe a).mpr (Or.inl h₁))
      · exact edge_not_mem_of_cap hnl hQcap h₁ h₂
    have hAB : wU J A ∩ wU J B = {z, w} := by
      rw [wU_inter hABe]
      refine Subset.antisymm ?_ ?_
      · rintro p ⟨h₁, h₂⟩
        rcases (hAs p).mp h₁ with h₁ | h₁ <;> rcases (hBs p).mp h₂ with h₂ | h₂
        · exact Or.inl (hTcap p h₁ h₂)
        · rcases hc.cap p ((hTm p).mpr (Or.inl h₁)) ((hQm p).mpr (Or.inr h₂)) with rfl | rfl
          · exact (hwx (hQcap _ Q₁.start_mem_support h₂).symm).elim
          · exact (hzy (hTcap _ h₁ T₂.end_mem_support).symm).elim
        · rcases hc.cap p ((hTm p).mpr (Or.inr h₂)) ((hQm p).mpr (Or.inl h₁)) with rfl | rfl
          · exact (hzx (hTcap _ T₁.start_mem_support h₂).symm).elim
          · exact (hwy (hQcap _ h₁ Q₂.end_mem_support).symm).elim
        · exact Or.inr (hQcap p h₁ h₂)
      · rintro p (rfl | rfl)
        · exact ⟨A.start_mem_support, B.start_mem_support⟩
        · exact ⟨A.end_mem_support, B.end_mem_support⟩
    have hRA : ∀ a ∈ R.edges, a ∉ A.edges := fun a ha h' => by
      rcases (hAe a).mp h' with h₁ | h₁
      · exact (hRM a ha).2.2.1 ((hTe a).mpr (Or.inl h₁))
      · exact (hRM a ha).2.2.2 ((hQe a).mpr (Or.inl h₁))
    have hRB : ∀ a ∈ R.edges, a ∉ B.edges := fun a ha h' => by
      rcases (hBe a).mp h' with h₁ | h₁
      · exact (hRM a ha).2.2.1 ((hTe a).mpr (Or.inr h₁))
      · exact (hRM a ha).2.2.2 ((hQe a).mpr (Or.inr h₁))
    have hcapR : ∀ {a b : S} {X : GraphWalk J.toGraph z w}, (∀ p ∈ X.support, p ∈ BB T Q) →
        (∀ e ∈ R.edges, e ∉ X.edges) → wU J R ∩ wU J X = {z, w} := by
      intro _ _ X hX hEd
      rw [wU_inter hEd]
      refine Subset.antisymm ?_ ?_
      · rintro p ⟨h₁, h₂⟩
        rcases hRin p h₁ with h' | h'
        · exact ((hX p h₂).elim h'.1 h'.2).elim
        · exact h'
      · rintro p (rfl | rfl)
        · exact ⟨R.start_mem_support, X.start_mem_support⟩
        · exact ⟨R.end_mem_support, X.end_mem_support⟩
    have hAB' : ∀ p ∈ A.support, p ∈ BB T Q := fun p hp => by
      rcases (hAs p).mp hp with h' | h'
      · exact Or.inl ((hTm p).mpr (Or.inl h'))
      · exact Or.inr ((hQm p).mpr (Or.inl h'))
    have hBB' : ∀ p ∈ B.support, p ∈ BB T Q := fun p hp => by
      rcases (hBs p).mp hp with h' | h'
      · exact Or.inl ((hTm p).mpr (Or.inr h'))
      · exact Or.inr ((hQm p).mpr (Or.inr h'))
    have hbdD : discBd D = wU J A ∪ wU J B := by
      rw [hc.bd, hTu, hQu, hAu, hBu]
      ext p
      simp only [mem_union]
      tauto
    have hRD : wU J R ⊆ D := by
      intro p hp
      rcases (mem_walkDrawing_U J R).mp hp with h' | ⟨a, ha, hpa⟩
      · exact support_subset_of_edges hc.disc.isClosed R
          (hc.wT_sub (mem_wU_of_support hzT)) (fun a ha => (hRM a ha).2.1) p h'
      · exact closure_minimal (hRM a ha).2.1 hc.disc.isClosed hpa
    obtain ⟨E₁, E₂, hE₁, hE₂, hun, hint, hb₁, hb₂⟩ := disc_split hc.disc (wU_line hsR hzw)
      (wU_line hsA hzw) (wU_line hsB hzw) hAB (hcapR (a := z) (b := w) hAB' hRA)
      (hcapR (a := z) (b := w) hBB' hRB) hbdD hRD hzw
    have hgR : g ∉ R.edges := fun h' => hc.gc (hRc g h')
    have hgoff := hc.offE hc.gE hc.gT hc.gQ
    have hgdis : Disjoint g (discBd E₁) := by
      rw [hb₁]
      refine Set.disjoint_union_right.mpr ⟨?_, edge_disjoint_U (walkDrawing_isSubdrawing J R) hc.gE
        (by rw [walkDrawing_E]; exact hgR)⟩
      exact Set.disjoint_of_subset_right (fun p hp => hbdD ▸ Or.inl hp) hgoff
    have hfin : {e | e ∈ J.E ∧ e ⊆ D}.Finite := J.finite_edges.subset fun e he => he.1
    rcases edge_side hS hE₁ hc.gE hgdis with h' | h'
    · obtain ⟨hc', hss⟩ := hc.shrink hTu hQu hsT₁ hsQ₁ hsR
        (fun p hp => (hTm p).mpr (Or.inl hp)) (fun a ha => (hTe a).mpr (Or.inl ha))
        (fun p hp => (hTm p).mpr (Or.inr hp))
        (fun p hp => (hQm p).mpr (Or.inl hp)) (fun a ha => (hQe a).mpr (Or.inl ha))
        (fun p hp => (hQm p).mpr (Or.inr hp)) hTcap hRin hRc (fun a ha => (hRM a ha).2.2.1)
        (fun a ha => (hRM a ha).2.2.2) hzy hwx hwT hzQ hE₁ hE₂ hun hint (by rw [hb₁, hAu])
        (by rw [hb₂, hBu]) h'
      exact ih _ (hn ▸ Set.ncard_lt_ncard hss hfin) _ _ _ _ _ _ hc' rfl
    · have hgE₂ : g ⊆ E₂ := by
        intro p hp
        have : p ∈ E₁ ∪ E₂ := by rw [hun]; exact hc.gD hp
        exact this.resolve_left (Set.disjoint_left.mp h' hp)
      have hrevT : ∀ p, p ∈ T.reverse.support ↔ p ∈ T.support := fun p => by
        rw [GraphWalk.support_reverse, List.mem_reverse]
      have hrevQ : ∀ p, p ∈ Q.reverse.support ↔ p ∈ Q.support := fun p => by
        rw [GraphWalk.support_reverse, List.mem_reverse]
      have hrevTe : ∀ a, a ∈ T.reverse.edges ↔ a ∈ T.edges := fun a => by
        rw [GraphWalk.edges_reverse, List.mem_reverse]
      have hrevQe : ∀ a, a ∈ Q.reverse.edges ↔ a ∈ Q.edges := fun a => by
        rw [GraphWalk.edges_reverse, List.mem_reverse]
      have hms : ∀ {a b : S} {W : GraphWalk J.toGraph a b} {p : S},
          p ∈ W.reverse.support → p ∈ W.support := fun {a b W p} hp => by
        rwa [GraphWalk.support_reverse, List.mem_reverse] at hp
      have hme : ∀ {a b : S} {W : GraphWalk J.toGraph a b} {p : Set S},
          p ∈ W.reverse.edges → p ∈ W.edges := fun {a b W p} hp => by
        rwa [GraphWalk.edges_reverse, List.mem_reverse] at hp
      obtain ⟨hc', hss⟩ := hc.symm.shrink (T₁ := T₂.reverse) (T₂ := T₁.reverse)
        (Q₁ := Q₂.reverse) (Q₂ := Q₁.reverse) (R := R)
        (by rw [wU_reverse, wU_reverse, wU_reverse, hTu, union_comm])
        (by rw [wU_reverse, wU_reverse, wU_reverse, hQu, union_comm])
        hsT₂.reverse hsQ₂.reverse hsR
        (fun p hp => (hrevT p).mpr ((hTm p).mpr (Or.inr (hms hp))))
        (fun a ha => (hrevTe a).mpr ((hTe a).mpr (Or.inr (hme ha))))
        (fun p hp => (hrevT p).mpr ((hTm p).mpr (Or.inl (hms hp))))
        (fun p hp => (hrevQ p).mpr ((hQm p).mpr (Or.inr (hms hp))))
        (fun a ha => (hrevQe a).mpr ((hQe a).mpr (Or.inr (hme ha))))
        (fun p hp => (hrevQ p).mpr ((hQm p).mpr (Or.inl (hms hp))))
        (fun p h₁ h₂ => hTcap p (hms h₂) (hms h₁))
        (fun p hp => by
          rcases hRin p hp with h₁ | h₁
          · exact Or.inl ⟨fun h₂ => h₁.1 ((hrevT p).mp h₂), fun h₂ => h₁.2 ((hrevQ p).mp h₂)⟩
          · exact Or.inr h₁)
        hRc (fun a ha h₂ => (hRM a ha).2.2.1 ((hrevTe a).mp h₂))
        (fun a ha h₂ => (hRM a ha).2.2.2 ((hrevQe a).mp h₂)) hzx hwy
        (fun h₂ => hwT ((hrevT w).mp h₂)) (fun h₂ => hzQ ((hrevQ z).mp h₂)) hE₂ hE₁
        ((union_comm _ _).trans hun) ((inter_comm _ _).trans hint)
        (by rw [hb₂, hBu, wU_reverse, wU_reverse])
        (by rw [hb₁, hAu, wU_reverse, wU_reverse]) hgE₂
      exact ih _ (hn ▸ Set.ncard_lt_ncard hss hfin) _ _ _ _ _ _ hc' rfl

end Cand

/-- A path of `J` from a subdrawing is a walk of `J` with the same point set and edges. -/
theorem exists_walk_of_path {P : Drawing S} {a b : S} (hP : P.IsPathBetween a b)
    (hs : P.IsSubdrawing J) :
    ∃ W : GraphWalk J.toGraph a b, W.IsSimple ∧ wU J W = P.U ∧ (∀ e ∈ W.edges, e ∈ P.E) ∧
      ∀ p ∈ W.support, p ∈ P.V := by
  obtain ⟨W, hW, hV, hE⟩ := hP
  obtain ⟨W', hs', he'⟩ := hs.exists_walk_up W
  have hsim : W'.IsSimple := by unfold GraphWalk.IsSimple; rw [hs']; exact hW
  refine ⟨W', hsim, ?_, ?_, ?_⟩
  · change (walkDrawing J W').U = P.U
    rw [Drawing.U_eq (Γ := walkDrawing J W'), Drawing.U_eq (Γ := P), walkDrawing_V,
      walkDrawing_E, hV,
      hE, hs', he']
  · intro e he
    rw [hE, ← he']
    exact he
  · intro p hp
    rw [hV, ← hs']
    exact hp

/-- The first candidate. -/
theorem start_cand {x y : S} {g E₁ E₂ : Set S}
    {W P₁ : GraphWalk J.toGraph x y} (hxy : x ≠ y) (hsW : W.IsSimple) (hsP : P₁.IsSimple)
    (hE₁ : IsClosedDisc E₁) (hE₂ : IsClosed E₂) (hun : E₁ ∪ E₂ = Δ) (hint : E₁ ∩ E₂ = wU J W)
    (hb₁ : discBd E₁ = wU J W ∪ wU J P₁) (hWc : ∀ e ∈ W.edges, e ∈ c)
    (hP₁ : ∀ e ∈ P₁.edges, e ∈ C₀.E) {X : Set S} (hC : C₀.U = wU J P₁ ∪ X) (hX : X ⊆ E₂)
    (hXcap : ∀ p ∈ X, p ∈ wU J W → p ∈ wU J P₁)
    (hWcap : wU J W ∩ C₀.U = {x, y}) (hgJ : g ∈ J.E) (hgD : g ⊆ E₁) (hgC : g ∉ C₀.E)
    (hgc : g ∉ c) : Cand J C₀ Δ c g E₁ E₂ W P₁ := by
  refine ⟨hxy, hsW, hsP, hE₁, hE₂, hun, hint, hb₁, hWc, hP₁, hWcap, ?_, hgJ, hgD,
    fun h' => hgc (hWc g h'), fun h' => hgC (hP₁ g h'), hgc⟩
  refine Subset.antisymm ?_ ?_
  · rintro p ⟨hpC, hpE⟩
    rw [hC] at hpC
    rcases hpC with h' | h'
    · exact h'
    · exact hXcap p h' (hint ▸ ⟨hpE, hX h'⟩)
  · intro p hp
    refine ⟨hC ▸ Or.inl hp, Surface.discBd_subset _ (hb₁ ▸ Or.inr hp)⟩

/-- **A circuit with all of `J` on one side is peripheral.** Here `Δ` is a closed disc with boundary
the circuit, and it holds all of `J`. -/
theorem peripheral_of_side {G₀ : Graph S (Set S)} {P : Set S → Graph S (Set S)}
    (hS : IsClosedSurface S) (h : SubData J.toGraph G₀ P) (hC : C₀.IsCircuit)
    (hs : C₀.IsSubdrawing J) (hΔ : IsClosedDisc Δ) (hb : discBd Δ = C₀.U) (hU : J.U ⊆ Δ) :
    IsPeripheral J C₀ := by
  classical
  intro e he f hf
  by_contra hn
  set c := cls J.toGraph C₀.V (J.E \ C₀.E) e with hcdef
  have hcsub : c ⊆ J.E \ C₀.E := cls_subset he
  have hEnv : Env J C₀ Δ c := ⟨hC, hs, hU, fun a ha => hcsub ha, fun a b ha hab => cls_step ha hab⟩
  have hCne : C₀.E.Nonempty := by
    obtain ⟨u, W, -, hpos, -, hE⟩ := id hC
    cases W with
    | nil _ => simp [GraphWalk.length] at hpos
    | @cons _ m _ a hl rest =>
      exact ⟨a, by rw [hE]; simp [GraphWalk.edges]⟩
  obtain ⟨x, y, W, hxy, hsW, hx, hy, -, -, hEc, hin⟩ := h.exists_ear (Hv := C₀.V) (Hs := C₀.E)
    hs.2 hCne
    (fun a ha v hv => by
      have hm : v ∈ closure a ∩ J.V := ⟨mem_closure_of_inc hv, hv.vertex_mem⟩
      rw [← hs.closure_inter_V ha] at hm
      exact hm.2)
    (fun v hv a ha han hia => by
      obtain ⟨p, hp, q, hq, hpq, ip, iq⟩ := circuit_two_edges h hC hs hv
      exact h.mem_V₀_of_three (hs.2 hp) (hs.2 hq) ha ip iq hia hpq
        (fun h' => han (h' ▸ hp)) (fun h' => han (h' ▸ hq)))
    he.1 he.2
  obtain ⟨P₁, P₂, hP₁, hP₂, hsP₁, hsP₂, -, -, hPV, hPd, hsup⟩ :=
    Drawing.IsCircuit.exists_two_paths hC hx hy hxy
  obtain ⟨X₁, hX₁s, hX₁U, hX₁E, hX₁V⟩ := exists_walk_of_path hP₁ (hsP₁.trans hs)
  obtain ⟨X₂, hX₂s, hX₂U, hX₂E, hX₂V⟩ := exists_walk_of_path hP₂ (hsP₂.trans hs)
  have hCU : C₀.U = wU J X₁ ∪ wU J X₂ := by
    have := sup_U (J := C₀) hsP₁ hsP₂
    rw [hsup] at this
    rw [this, hX₁U, hX₂U]
  have hc₁₂ : wU J X₁ ∩ wU J X₂ = {x, y} := by
    rw [hX₁U, hX₂U, U_inter_of_disjoint hsP₁ hsP₂ hPd, hPV]
  have hWoff : ∀ a ∈ W.edges, a ∉ C₀.E := fun a ha => (hcsub (hEc a ha)).2
  have hcapX : ∀ {X : GraphWalk J.toGraph x y}, (∀ a ∈ X.edges, a ∈ C₀.E) →
      (∀ p ∈ X.support, p ∈ C₀.V) → wU J W ∩ wU J X = {x, y} := by
    intro X h₁ h₂
    rw [wU_inter fun a ha h' => hWoff a ha (h₁ a h')]
    refine Subset.antisymm ?_ ?_
    · rintro p ⟨hp, hp'⟩
      rcases hin p hp with h' | h'
      · exact (h' (h₂ p hp')).elim
      · exact h'
    · rintro p (rfl | rfl)
      · exact ⟨W.start_mem_support, X.start_mem_support⟩
      · exact ⟨W.end_mem_support, X.end_mem_support⟩
  have hX₁C : ∀ a ∈ X₁.edges, a ∈ C₀.E := fun a ha => hsP₁.2 (hX₁E a ha)
  have hX₂C : ∀ a ∈ X₂.edges, a ∈ C₀.E := fun a ha => hsP₂.2 (hX₂E a ha)
  have hc₁ := hcapX hX₁C fun p hp => hsP₁.1 (hX₁V p hp)
  have hc₂ := hcapX hX₂C fun p hp => hsP₂.1 (hX₂V p hp)
  have hWsub : wU J W ⊆ J.U := (walkDrawing_isSubdrawing J W).U_subset
  obtain ⟨E₁, E₂, hE₁, hE₂, hun, hint, hb₁, hb₂⟩ := disc_split hΔ (wU_line hsW hxy)
    (wU_line hX₁s hxy) (wU_line hX₂s hxy) hc₁₂ hc₁ hc₂ (by rw [hb, hCU]) (hWsub.trans hU) hxy
  have hWcap : wU J W ∩ C₀.U = {x, y} := by
    rw [hCU, inter_union_distrib_left, hc₁, hc₂, union_self]
  have hend : ∀ {X : GraphWalk J.toGraph x y}, ({x, y} : Set S) ⊆ wU J X := by
    rintro X p (rfl | rfl)
    · exact mem_wU_of_support X.start_mem_support
    · exact mem_wU_of_support X.end_mem_support
  have hfW : f ∉ W.edges := fun h' => hn (hEc f h')
  have hfdis : Disjoint f (discBd E₁) := by
    rw [hb₁]
    refine Set.disjoint_union_right.mpr ⟨?_, edge_disjoint_U (walkDrawing_isSubdrawing J W) hf.1
      (by rw [walkDrawing_E]; exact hfW)⟩
    refine Set.disjoint_of_subset_right ?_ (edge_disjoint_U hs hf.1 hf.2)
    exact fun p hp => hCU ▸ Or.inl hp
  have hb₁' : discBd E₁ = wU J W ∪ wU J X₁ := by rw [hb₁, union_comm]
  have hb₂' : discBd E₂ = wU J W ∪ wU J X₂ := by rw [hb₂, union_comm]
  rcases edge_side hS hE₁ hf.1 hfdis with h' | h'
  · have hX₂in : wU J X₂ ⊆ E₂ := fun p hp => Surface.discBd_subset _ (hb₂' ▸ Or.inr hp)
    have hc := start_cand (Δ := Δ) (C₀ := C₀) hxy hsW hX₁s hE₁ hE₂.isClosed hun hint hb₁' hEc hX₁C
      hCU hX₂in
      (fun p h₁ h₂ => by
        have : p ∈ wU J W ∩ wU J X₂ := ⟨h₂, h₁⟩
        rw [hc₂] at this
        exact hend this)
      hWcap hf.1 h' hf.2 hn
    exact Cand.false_aux hS h hEnv _ _ _ _ _ _ _ hc rfl
  · have hfE₂ : f ⊆ E₂ := by
      intro p hp
      have : p ∈ E₁ ∪ E₂ := by rw [hun]; exact hU (hf.1.2.1 hp).1
      exact this.resolve_left (Set.disjoint_left.mp h' hp)
    have hX₁in : wU J X₁ ⊆ E₁ := fun p hp => Surface.discBd_subset _ (hb₁' ▸ Or.inr hp)
    have hc := start_cand (Δ := Δ) (C₀ := C₀) hxy hsW hX₂s hE₂ hE₁.isClosed
      ((union_comm _ _).trans hun)
      ((inter_comm _ _).trans hint) hb₂' hEc hX₂C (by rw [hCU, union_comm]) hX₁in
      (fun p h₁ h₂ => by
        have : p ∈ wU J W ∩ wU J X₁ := ⟨h₂, h₁⟩
        rw [hc₁] at this
        exact hend this)
      hWcap hf.1 hfE₂ hf.2 hn
    exact Cand.false_aux hS h hEnv _ _ _ _ _ _ _ hc rfl

end Main

end GraphMinor.GM14.Whitney
