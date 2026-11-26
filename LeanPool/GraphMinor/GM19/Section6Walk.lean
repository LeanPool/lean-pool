/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section6Sector
public import LeanPool.GraphMinor.GM19.Section6Path
public import LeanPool.GraphMinor.GM11.OArcCircuit

/-!
# A closed walk that is not null-homotopic gives a circuit

Let `G` be a drawing with no loops. A walk in the graph of `G` traces a path in the surface
(`walkP`). If a closed walk of length at most `n` is not null-homotopic, then `G` has a circuit with
at
most `n` edges that is not null-homotopic (`exists_circuit_of_walk`). The proof takes a shortest
such
closed walk. All shorter closed walks are null-homotopic, so we may cut the closed pieces out of it
(`walkP_bypass`), and what remains is one edge and a path, which together form an `O`-arc, unless
the
walk goes along an edge and back.

This is used for `rep(sk(Γ)) ≥ rep(Γ)` in (6.7) of Graph Minors XIX, where a curve is first moved
onto a closed walk of the radial drawing, which need not be a circuit.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology GraphMinor.Surface GraphMinor.GM11

local notation "𝕀" => unitInterval

variable {T : Type} [TopologicalSpace T]

/-- Two paths in a contractible set with the same ends are homotopic. -/
theorem paths_homotopic_of_contractible {Λ : Set T} (hc : ContractibleSpace Λ) {a b : T}
  (p q : Path a b)
    (hp : range p ⊆ Λ) (hq : range q ⊆ Λ) : p.Homotopic q := by
  have ha : a ∈ Λ := hp ⟨0, by simp⟩
  have hb : b ∈ Λ := hp ⟨1, by simp⟩
  let p' : Path (⟨a, ha⟩ : Λ) ⟨b, hb⟩ := ⟨⟨fun t => ⟨p t, hp ⟨t, rfl⟩⟩, by fun_prop⟩, by simp, by
    simp⟩
  let q' : Path (⟨a, ha⟩ : Λ) ⟨b, hb⟩ := ⟨⟨fun t => ⟨q t, hq ⟨t, rfl⟩⟩, by fun_prop⟩, by simp, by
    simp⟩
  have h : p'.Homotopic q' := SimplyConnectedSpace.paths_homotopic _ _
  have h2 := h.map ⟨Subtype.val, continuous_subtype_val⟩
  have e1 : p'.map continuous_subtype_val = p := by
    ext t
    rfl
  have e2 : q'.map continuous_subtype_val = q := by
    ext t
    rfl
  have e3 := h2
  simp only [ContinuousMap.coe_mk] at e3
  rwa [e1, e2] at e3

/-- Two paths in a line with the same ends are homotopic. -/
theorem paths_homotopic_in_line {L : Set T} {u v : T} (hL : IsLineWithEnds L u v) {a b : T}
    (p q : Path a b) (hp : range p ⊆ L) (hq : range q ⊆ L) : p.Homotopic q := by
  obtain ⟨f, -, -⟩ := hL
  have hc : ContractibleSpace 𝕀 := (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by simp⟩
  exact paths_homotopic_of_contractible f.symm.contractibleSpace p q hp hq

variable [T2Space T]

omit [T2Space T] in
/-- A step of a walk: an edge with the two ends, and a path along it. -/
theorem exists_walk_step {G : Drawing T} (hl : LoopFree G) {a b : G.V}
    (h : (G.adj.induce G.V).Adj a b) : ∃ e ∈ G.E, ∃ p : Path a.1 b.1, tilde e = {a.1, b.1} ∧
      IsLineWithEnds (closure e) a b ∧ range p = closure e ∧ Function.Injective p := by
  have h' : G.adj.Adj a.1 b.1 := h
  obtain ⟨hne, -, -, e, he, h1, h2⟩ := h'
  obtain ⟨u, v, huv, hti, hL⟩ := hl e he
  have hti' : tilde e = {a.1, b.1} := by
    rw [hti] at h1 h2 ⊢
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [h1, mem_singleton_iff.mp h2]
    · rw [mem_singleton_iff.mp h1, h2, pair_comm]
    · exact absurd ((mem_singleton_iff.mp h1).trans (mem_singleton_iff.mp h2).symm) hne
  have hLe : IsLineWithEnds (closure e) a b := by
    rw [hti] at h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · rw [h1, mem_singleton_iff.mp h2]; exact hL
    · rw [mem_singleton_iff.mp h1, h2]; exact GraphMinor.GM11.IsLineWithEnds.symm hL
    · exact absurd ((mem_singleton_iff.mp h1).trans (mem_singleton_iff.mp h2).symm) hne
  obtain ⟨f, h0, h1'⟩ := id hLe
  refine ⟨e, he, ⟨⟨fun t => (f t).1, by fun_prop⟩, h0, h1'⟩, hti', hLe, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact (f t).2
    · intro hx
      exact ⟨f.symm ⟨x, hx⟩, by simp⟩
  · intro s t hst
    exact f.injective (Subtype.ext hst)

/-- The edge of a step. -/
noncomputable def stepE {G : Drawing T} (hl : LoopFree G) {a b : G.V}
    (h : (G.adj.induce G.V).Adj a b) : Set T := (exists_walk_step hl h).choose

/-- The path along the edge of a step. -/
noncomputable def stepP {G : Drawing T} (hl : LoopFree G) {a b : G.V}
    (h : (G.adj.induce G.V).Adj a b) : Path a.1 b.1 := (exists_walk_step hl h).choose_spec.2.choose

omit [T2Space T] in
theorem stepE_mem {G : Drawing T} (hl : LoopFree G) {a b : G.V} (h : (G.adj.induce G.V).Adj a b) :
    stepE hl h ∈ G.E := (exists_walk_step hl h).choose_spec.1

omit [T2Space T] in
theorem stepE_tilde {G : Drawing T} (hl : LoopFree G) {a b : G.V} (h : (G.adj.induce G.V).Adj a b) :
    tilde (stepE hl h) = {a.1, b.1} := (exists_walk_step hl h).choose_spec.2.choose_spec.1

omit [T2Space T] in
theorem stepE_line {G : Drawing T} (hl : LoopFree G) {a b : G.V} (h : (G.adj.induce G.V).Adj a b) :
    IsLineWithEnds (closure (stepE hl h)) a b := (exists_walk_step hl
      h).choose_spec.2.choose_spec.2.1

omit [T2Space T] in
theorem stepP_range {G : Drawing T} (hl : LoopFree G) {a b : G.V} (h : (G.adj.induce G.V).Adj a b) :
    range (stepP hl h) = closure (stepE hl h) := (exists_walk_step hl
      h).choose_spec.2.choose_spec.2.2.1

omit [T2Space T] in
theorem stepP_injective {G : Drawing T} (hl : LoopFree G) {a b : G.V}
    (h : (G.adj.induce G.V).Adj a b) : Function.Injective (stepP hl h) :=
  (exists_walk_step hl h).choose_spec.2.choose_spec.2.2.2

/-- The path that a walk traces. -/
noncomputable def walkP {G : Drawing T} (hl : LoopFree G) :
    ∀ {a b : G.V}, (G.adj.induce G.V).Walk a b → Path a.1 b.1
  | _, _, .nil => Path.refl _
  | _, _, .cons h p => (stepP hl h).trans (walkP hl p)

/-- The set of points of a walk. -/
noncomputable def walkU {G : Drawing T} (hl : LoopFree G) :
    ∀ {a b : G.V}, (G.adj.induce G.V).Walk a b → Set T
  | a, _, .nil => {a.1}
  | _, _, .cons h p => closure (stepE hl h) ∪ walkU hl p

/-- The set of edges of a walk. -/
noncomputable def walkE {G : Drawing T} (hl : LoopFree G) :
    ∀ {a b : G.V}, (G.adj.induce G.V).Walk a b → Set (Set T)
  | _, _, .nil => ∅
  | _, _, .cons h p => insert (stepE hl h) (walkE hl p)

variable {G : Drawing T} (hl : LoopFree G)

omit [T2Space T] in
theorem walkE_ncard {a b : G.V} (p : (G.adj.induce G.V).Walk a b) :
    (walkE hl p).Finite ∧ (walkE hl p).ncard ≤ p.length := by
  induction p with
  | nil => simp [walkE]
  | cons h p ih =>
    refine ⟨ih.1.insert _, ?_⟩
    have := ncard_insert_le (stepE hl h) (walkE hl p)
    simp only [walkE, SimpleGraph.Walk.length_cons]
    omega

omit [T2Space T] in
theorem walkP_range {a b : G.V} (p : (G.adj.induce G.V).Walk a b) :
    range (walkP hl p) ⊆ walkU hl p := by
  induction p with
  | nil =>
    rintro _ ⟨t, rfl⟩
    rfl
  | cons h p ih =>
    simp only [walkP, walkU]
    rw [Path.trans_range, stepP_range]
    exact union_subset_union_right _ ih

omit [T2Space T] in
theorem walkU_inter_V {a b : G.V} (p : (G.adj.induce G.V).Walk a b) {x : T} (hx : x ∈ walkU hl p)
    (hxV : x ∈ G.V) : (⟨x, hxV⟩ : G.V) ∈ p.support := by
  induction p with
  | nil =>
    have : x = _ := hx
    subst this
    simp
  | @cons a c b h p ih =>
    rw [SimpleGraph.Walk.support_cons, List.mem_cons]
    rcases hx with hx | hx
    · have hxt : x ∈ tilde (stepE hl h) := by
        rw [tilde_eq_inter_V G (stepE_mem hl h)]
        exact ⟨hx, hxV⟩
      rw [stepE_tilde] at hxt
      rcases hxt with hxt | hxt
      · exact .inl (Subtype.ext hxt)
      · have hc : x = c.1 := hxt
        refine .inr ?_
        have hm : c ∈ p.support := p.start_mem_support
        have : (⟨x, hxV⟩ : G.V) = c := Subtype.ext hc
        rwa [this]
    · exact .inr (ih hx)

omit [T2Space T] in
theorem walkU_edge {a b : G.V} (p : (G.adj.induce G.V).Walk a b) {x : T} (hx : x ∈ walkU hl p)
    (hxV : x ∉ G.V) : ∃ f ∈ walkE hl p, f ∈ G.E ∧ closure f ⊆ walkU hl p ∧ x ∈ closure f := by
  induction p with
  | nil =>
    have : x = _ := hx
    subst this
    exact absurd (Subtype.property _) hxV
  | @cons a c b h p ih =>
    rcases hx with hx | hx
    · exact ⟨_, .inl rfl, stepE_mem hl h, subset_union_left, hx⟩
    · obtain ⟨f, hf, hfE, hsub, hxf⟩ := ih hx
      exact ⟨f, .inr hf, hfE, hsub.trans subset_union_right, hxf⟩

omit [T2Space T] in
theorem walkU_subset_U {a b : G.V} (p : (G.adj.induce G.V).Walk a b) : walkU hl p ⊆ G.U := by
  induction p with
  | nil =>
    rintro _ rfl
    exact G.V_subset_U (Subtype.property _)
  | cons h p ih =>
    exact union_subset (G.closure_subset_U (stepE_mem hl h)) ih

/-- The points of a path of the graph form a line. -/
theorem walkU_line {a b : G.V} (p : (G.adj.induce G.V).Walk a b) :
    p.IsPath → a ≠ b → IsLineWithEnds (walkU hl p) a b := by
  induction p with
  | nil => exact fun _ h => absurd rfl h
  | @cons a c b h p ih =>
    intro hp hab
    rw [SimpleGraph.Walk.cons_isPath_iff] at hp
    have hLe := stepE_line hl h
    by_cases hcb : c = b
    · subst hcb
      have hp0 : p = .nil := by
        cases p with
        | nil => rfl
        | cons h' q =>
          have := hp.1
          simp  at this
      subst hp0
      have hsub : walkU hl (.cons h .nil : (G.adj.induce G.V).Walk a c) = closure (stepE hl h) := by
        apply Subset.antisymm
        · refine union_subset subset_rfl ?_
          rintro _ rfl
          exact hLe.right_mem
        · exact subset_union_left
      rw [hsub]
      exact hLe
    · have hL := ih hp.1 hcb
      have hcap : closure (stepE hl h) ∩ walkU hl p = {c.1} := by
        apply Subset.antisymm
        · rintro x ⟨hxe, hxq⟩
          by_cases hxV : x ∈ G.V
          · have hxt : x ∈ tilde (stepE hl h) := by
              rw [tilde_eq_inter_V G (stepE_mem hl h)]
              exact ⟨hxe, hxV⟩
            rw [stepE_tilde] at hxt
            rcases hxt with hxt | hxt
            · subst hxt
              exact absurd (walkU_inter_V hl p hxq hxV) hp.2
            · exact hxt
          · obtain ⟨f, -, hfE, hsub, hxf⟩ := walkU_edge hl p hxq hxV
            have hef := edge_eq_of_mem G (stepE_mem hl h) hfE hxe hxf hxV
            have ha : a.1 ∈ walkU hl p := hsub (hef ▸ hLe.left_mem)
            exact absurd (walkU_inter_V hl p ha a.2) hp.2
        · rintro _ rfl
          exact ⟨hLe.right_mem, hL.left_mem⟩
      exact IsLineWithEnds.union hLe hL hcap

omit [T2Space T] in
theorem walkP_append {a b c : G.V} (p : (G.adj.induce G.V).Walk a b)
    (q : (G.adj.induce G.V).Walk b c) :
    (walkP hl (p.append q)).Homotopic ((walkP hl p).trans (walkP hl q)) := by
  induction p with
  | nil =>
    exact (Path.Homotopic.refl_trans _).symm
  | cons h p ih =>
    simp only [SimpleGraph.Walk.cons_append, walkP]
    exact ((Path.Homotopic.refl _).hcomp (ih q)).trans (Path.Homotopic.trans_assoc _ _ _).symm

open Classical in
omit [T2Space T] in
/-- If all closed walks shorter than `L` are null-homotopic, then a walk shorter than `L` is
homotopic
to the path of the graph inside it. -/
theorem walkP_bypass {L : ℕ}
    (hnull : ∀ (a : G.V) (w : (G.adj.induce G.V).Walk a a), w.length < L →
      (walkP hl w).Homotopic (Path.refl _)) {a b : G.V} (p : (G.adj.induce G.V).Walk a b)
    (hp : p.length < L) : (walkP hl p).Homotopic (walkP hl p.bypass) := by
  induction p with
  | nil => exact Path.Homotopic.refl _
  | @cons a c b h q ih =>
    have hq : q.length < L := by
      rw [SimpleGraph.Walk.length_cons] at hp
      omega
    have ih' := ih hq
    simp only [SimpleGraph.Walk.bypass]
    split_ifs with hs
    · set r := q.bypass with hr
      have hspec : (r.takeUntil a hs).append (r.dropUntil a hs) = r := r.take_spec hs
      have hlen : (r.takeUntil a hs).length ≤ r.length := r.length_takeUntil_le_length hs
      have hr' : r.length ≤ q.length := SimpleGraph.Walk.length_bypass_le_length q
      have hclosed := hnull a (.cons h (r.takeUntil a hs)) (by
        rw [SimpleGraph.Walk.length_cons]
        rw [SimpleGraph.Walk.length_cons] at hp
        omega)
      simp only [walkP] at hclosed
      have h₁ : (walkP hl r).Homotopic
          ((walkP hl (r.takeUntil a hs)).trans (walkP hl (r.dropUntil a hs))) := by
        have := walkP_append hl (r.takeUntil a hs) (r.dropUntil a hs)
        rwa [hspec] at this
      simp only [walkP]
      refine ((Path.Homotopic.refl _).hcomp (ih'.trans h₁)).trans
        ((Path.Homotopic.trans_assoc _ _ _).symm.trans ?_)
      exact (hclosed.hcomp (Path.Homotopic.refl _)).trans (Path.Homotopic.refl_trans _)
    · simp only [walkP]
      exact (Path.Homotopic.refl _).hcomp ih'


omit [T2Space T] in
/-- A loop through a set is null-homotopic if an `O`-arc equal to that set is. -/
theorem loop_refl_of_null {F : Set T} (hF : IsNullHomotopicOArc F) {w : T} (P : Path w w)
    (hr : range P = F) : P.Homotopic (Path.refl w) := by
  have h : P.toContinuousMap 0 = P.toContinuousMap 1 := by simp
  have hγ : ∀ t, loopLift 1 P.toContinuousMap h (arcParam 1 t) = P t := fun t => by simp
  refine path_refl_of_null P hγ (null_of_param hF _ ?_)
  apply Subset.antisymm
  · rintro _ ⟨z, rfl⟩
    obtain ⟨t, rfl⟩ := arcParam_surjective 1 z
    rw [hγ, ← hr]
    exact mem_range_self t
  · rw [← hr]
    rintro _ ⟨t, rfl⟩
    exact ⟨arcParam 1 t, hγ t⟩

open Classical in
/-- **A closed walk that is not null-homotopic gives a circuit.** See the module docstring. -/
theorem exists_circuit_of_walk [ConnectedSpace T] {n : ℕ} {a : G.V}
    (w : (G.adj.induce G.V).Walk a a) (hlen : w.length ≤ n)
    (hnn : ¬ (walkP hl w).Homotopic (Path.refl _)) :
    ∃ C : Drawing T, C.IsCircuitOf G ∧ ¬ IsNullHomotopicOArc C.U ∧ C.E.ncard ≤ n := by
  have hex : ∃ L, ∃ (a : G.V) (w : (G.adj.induce G.V).Walk a a), w.length = L ∧
      ¬ (walkP hl w).Homotopic (Path.refl _) := ⟨_, a, w, rfl, hnn⟩
  have hLn : Nat.find hex ≤ n := (Nat.find_min' hex ⟨a, w, rfl, hnn⟩).trans hlen
  obtain ⟨a₀, w', hw', hnn'⟩ := Nat.find_spec hex
  set L := Nat.find hex with hLdef
  have hnull : ∀ (b : G.V) (w : (G.adj.induce G.V).Walk b b), w.length < L →
      (walkP hl w).Homotopic (Path.refl _) := by
    intro b w hl'
    by_contra hc
    exact Nat.find_min hex hl' ⟨b, w, rfl, hc⟩
  clear hnn hlen w
  cases w' with
  | nil => exact absurd (Path.Homotopic.refl _) hnn'
  | @cons _ y _ h q =>
    have hqL : q.length < L := by
      rw [← hw', SimpleGraph.Walk.length_cons]
      omega
    have hay : a₀ ≠ y := h.ne
    let r := q.bypass
    have hrp : r.IsPath := q.bypass_isPath
    have hrl : r.length ≤ q.length := SimpleGraph.Walk.length_bypass_le_length q
    have hrq := walkP_bypass hl hnull q hqL
    have hstep : ¬ ((stepP hl h).trans (walkP hl r)).Homotopic (Path.refl _) := fun hc => hnn'
      (((Path.Homotopic.refl _).hcomp hrq).trans hc)
    have hLe := stepE_line hl h
    have hL₂ : IsLineWithEnds (walkU hl r) y a₀ := walkU_line hl r hrp hay.symm
    have heE := stepE_mem hl h
    have hcap : closure (stepE hl h) ∩ walkU hl r ⊆ {a₀.1, y.1} := by
      rintro x ⟨hxe, hxq⟩
      by_cases hxV : x ∈ G.V
      · rw [← stepE_tilde hl h, tilde_eq_inter_V G heE]
        exact ⟨hxe, hxV⟩
      exfalso
      obtain ⟨f, -, hfE, hsub, hxf⟩ := walkU_edge hl r hxq hxV
      have hef := edge_eq_of_mem G heE hfE hxe hxf hxV
      have hsub' : closure (stepE hl h) ⊆ walkU hl r := hef ▸ hsub
      refine hstep (paths_homotopic_in_line hL₂ _ _ ?_ ?_)
      · rw [Path.trans_range, stepP_range]
        exact union_subset hsub' (walkP_range hl r)
      · rintro _ ⟨t, rfl⟩
        exact hL₂.right_mem
    let F : Set T := closure (stepE hl h) ∪ walkU hl r
    have hO : IsOArc F := isOArc_union hLe (GraphMinor.GM11.IsLineWithEnds.symm hL₂) hcap
    have hFU : F ⊆ G.U := union_subset (G.closure_subset_U heE) (walkU_subset_U hl r)
    obtain ⟨f₂, f₀, f₁⟩ := id hL₂
    let q₂ : Path y.1 a₀.1 := ⟨⟨fun t => (f₂ t).1, by fun_prop⟩, f₀, f₁⟩
    have hq₂ : range q₂ = walkU hl r := by
      ext x
      constructor
      · rintro ⟨t, rfl⟩
        exact (f₂ t).2
      · intro hx
        exact ⟨f₂.symm ⟨x, hx⟩, by simp [q₂]⟩
    have hnF : ¬ IsNullHomotopicOArc F := by
      intro hn
      have h₁ := loop_refl_of_null hn ((stepP hl h).trans q₂) (by
        rw [Path.trans_range, stepP_range, hq₂])
      refine hstep (((Path.Homotopic.refl _).hcomp ?_).trans h₁)
      exact paths_homotopic_in_line hL₂ _ _ (walkP_range hl r) hq₂.subset
    obtain ⟨C, hC, hsub, hCU⟩ := exists_circuit_of_oArc hO hFU
    refine ⟨C, ⟨hsub, hC⟩, by rwa [hCU], ?_⟩
    have hEs : C.E ⊆ insert (stepE hl h) (walkE hl r) := by
      intro f hf
      have hfG := hsub.2 hf
      obtain ⟨x, hx⟩ := hfG.1
      have hxC := (hf.2.1 hx).1
      have hxV := (hfG.2.1 hx).2
      rw [hCU] at hxC
      rcases hxC with hxC | hxC
      · exact .inl (edge_eq_of_mem G hfG heE (subset_closure hx) hxC hxV)
      · obtain ⟨f', hf', hfE, -, hxf⟩ := walkU_edge hl r hxC hxV
        rw [edge_eq_of_mem G hfG hfE (subset_closure hx) hxf hxV]
        exact .inr hf'
    obtain ⟨hfin, hcard⟩ := walkE_ncard hl r
    have h₁ := ncard_le_ncard hEs (hfin.insert _)
    have h₂ := ncard_insert_le (stepE hl h) (walkE hl r)
    omega

end GraphMinor.GM19
