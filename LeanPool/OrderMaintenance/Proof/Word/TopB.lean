/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Word.Insert
public import LeanPool.OrderMaintenance.Impl.Caps


/-!
# Theorem W, stage B2: the top structure's write sites

The top structure's operations, as the pure state updates the cost proof computes them
(`copyC`, `wiC`, `sdS`, `dsS`, `fdS`, `insFinS`, the construction steps), keep the stored-value
bound. The classes of `docs/WORD.md` §2:
* **R**: node indices, entries and sides read from the state, sublists (`filter`, `erase`,
  `assocErase`, `replace1`), `NIL`;
* **F**: the two fresh nodes of a drain start (`nodes.size`, `nodes.size + 1`) and the new chunks
  of a split: hypotheses;
* **Lab**: table labels (`roomL`, `evenTable`, the centre), given `β ≤ K`;
* **Sz**: weights (`weight + 2`, the sums of a drain start): hypotheses, discharged in
  `TopStep.lean` from `Timing.wts`;
* **Tag**: chunk tags: hypotheses, discharged from `Shape.tags` (`tag_lt_of_topInv`).
-/


@[expose] public section

namespace OrderMaintenance.Proof.Word

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top
variable {K : Nat}

/-! ### Lists -/

theorem lb_nil {α : Type} {P : α → Prop} : ∀ x ∈ ([] : List α), P x := fun _ h => by cases h

theorem lb_cons {α : Type} {P : α → Prop} {a : α} {l : List α} (ha : P a) (hl : ∀ x ∈ l, P x) :
    ∀ x ∈ a :: l, P x := List.forall_mem_cons.2 ⟨ha, hl⟩

/-- An array written with `setX` holds old entries, the new one, or defaults. -/
theorem mem_setX {α : Type} [Inhabited α] {P : α → Prop} {a : Array α} (h : ∀ x ∈ a, P x) {v : α}
    (hv : P v) (hd : P default) (i : Nat) : ∀ x ∈ a.setX i v, P x := by
  intro x hx
  unfold Array.setX at hx
  split at hx
  · simp only [Array.set!] at hx
    rcases Array.mem_or_eq_of_mem_setIfInBounds hx with hx | hx
    · exact h x hx
    · subst hx; exact hv
  · rcases Array.mem_push.mp hx with hx | hx
    · rcases Array.mem_append.mp hx with hx | hx
      · exact h x hx
      · rw [Array.mem_replicate] at hx; rw [hx.2]; exact hd
    · subst hx; exact hv

theorem lb_append {α : Type} {P : α → Prop} {l l' : List α} (h : ∀ x ∈ l, P x) (h' : ∀ x ∈ l', P x) :
    ∀ x ∈ l ++ l', P x := fun x hx => by
  rcases List.mem_append.mp hx with hx | hx
  · exact h x hx
  · exact h' x hx

theorem lb_filter {α : Type} {P : α → Prop} {l : List α} (h : ∀ x ∈ l, P x) (p : α → Bool) :
    ∀ x ∈ l.filter p, P x := fun x hx => h x (List.mem_of_mem_filter hx)

theorem lb_erase {P : Nat → Prop} {l : List Nat} (h : ∀ x ∈ l, P x) (a : Nat) :
    ∀ x ∈ l.erase a, P x := fun x hx => h x (List.mem_of_mem_erase hx)

theorem lb_replace1 {P : Nat → Prop} {ys : List Nat} (hy : ∀ y ∈ ys, P y) (a : Nat) :
    ∀ (l : List Nat), (∀ x ∈ l, P x) → ∀ x ∈ l.replace1 a ys, P x
  | [], _ => lb_nil
  | b :: t, h => by
    unfold List.replace1
    split
    · exact lb_append hy (fun x hx => h x (List.mem_cons_of_mem _ hx))
    · exact List.forall_mem_cons.2 ⟨h b (by simp),
        lb_replace1 hy a t (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

theorem lb_insertIdx {α : Type} {P : α → Prop} {l : List α} (h : ∀ x ∈ l, P x) {y : α} (hy : P y)
    (i : Nat) : ∀ x ∈ l.insertIdx i y, P x := by
  intro x hx
  by_cases hi : i ≤ l.length
  · rcases (List.mem_insertIdx hi).mp hx with rfl | hx
    · exact hy
    · exact h x hx
  · rw [List.insertIdx_of_length_lt (by omega)] at hx; exact h x hx

theorem lb_assocSet {β : Type} {P : Nat → Prop} {l : List (Nat × β)} (h : ∀ p ∈ l, P p.1) {k : Nat}
    (hk : P k) (v : β) : ∀ p ∈ assocSet l k v, P p.1 := by
  intro p hp
  unfold assocSet at hp
  split at hp
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    split
    · exact hk
    · exact h q hq
  · rcases List.mem_append.mp hp with hp | hp
    · exact h p hp
    · simp only [List.mem_singleton] at hp; subst hp; exact hk

theorem lb_assocErase {β : Type} {P : Nat × β → Prop} {l : List (Nat × β)} (h : ∀ p ∈ l, P p) (k : Nat) :
    ∀ p ∈ assocErase l k, P p := lb_filter h _

/-- The keys of `sidesOf` are entries of the order. -/
theorem sidesOf_keys {P : Nat → Prop} {order : List Nat} (h : ∀ x ∈ order, P x) (b : Nat) :
    ∀ p ∈ sidesOf order b, P p.1 := by
  unfold sidesOf
  suffices ∀ (l : List Nat), (∀ x ∈ l, P x) → ∀ (acc : List (Nat × Side) × Side),
      (∀ p ∈ acc.1, P p.1) → ∀ p ∈ (l.foldl (fun (acc : List (Nat × Side) × Side) e =>
        let sd := if e == b then Side.right else acc.2
        (assocSet acc.1 e sd, sd)) acc).1, P p.1 from this order h _ (fun _ h => by cases h)
  intro l
  induction l with
  | nil => intro _ acc hacc; exact hacc
  | cons e t ih =>
    intro hl acc hacc
    simp only [List.foldl_cons]
    exact ih (fun x hx => hl x (List.mem_cons_of_mem _ hx)) _
      (lb_assocSet hacc (hl e (by simp)) _)

/-- `fixSides` adds keys from its entry list. -/
theorem fixSides_keys {P : Nat → Prop} (ns : Array Node) :
    ∀ (es : List Nat) (side side' : List (Nat × Side)), (∀ x ∈ es, P x) → (∀ p ∈ side, P p.1) →
      fixSides ns es side = some side' → ∀ p ∈ side', P p.1
  | [], side, side', _, hs, h => by
    simp only [fixSides, Option.some.injEq] at h; subst h; exact hs
  | e :: es, side, side', he, hs, h => by
    simp only [fixSides] at h
    split at h
    · split at h
      · exact fixSides_keys ns es _ side' (fun x hx => he x (List.mem_cons_of_mem _ hx))
          (lb_assocSet hs (he e (by simp)) _) h
      · cases h
    · exact fixSides_keys ns es side side' (fun x hx => he x (List.mem_cons_of_mem _ hx)) hs h

/-- The keys of a drain's side list are entries of the ghost's table. -/
theorem drainSide_keys {P : Nat → Prop} {ns : Array Node} {V : Node} {b : Nat}
    {side : List (Nat × Side)} (hV : ∀ x ∈ V.order, P x) (h : drainSide ns V b = some side) :
    ∀ p ∈ side, P p.1 := by
  unfold drainSide at h
  split at h
  · exact fixSides_keys ns _ _ side (lb_filter hV _) (sidesOf_keys hV b) h
  · cases h; exact sidesOf_keys hV b

/-! ### Labels -/

/-- An evenly spaced table: entries from the part, labels below `2^β`. -/
theorem evenTable_lt {β : Nat} {part : List Nat} {P : Nat → Prop} (hp : ∀ x ∈ part, P x) :
    ∀ q ∈ evenTable β part, P q.1 ∧ q.2 < 2 ^ β := by
  intro q hq
  unfold evenTable at hq
  obtain ⟨⟨i, e⟩, hie, rfl⟩ := List.mem_map.mp hq
  have hi : i < part.length := by
    have := List.of_mem_zip hie; simpa using this.1
  have he : e ∈ part := (List.of_mem_zip hie).2
  refine ⟨hp e he, ?_⟩
  dsimp only
  rw [Nat.shiftLeft_eq, one_mul]
  have hq := Nat.div_mul_le_self (2 ^ β) (part.length + 1)
  have hpos : 0 < 2 ^ β := Nat.two_pow_pos β
  generalize 2 ^ β / (part.length + 1) = q at hq ⊢
  generalize 2 ^ β = B at hq hpos ⊢
  have h1 : (i + 1) * q ≤ part.length * q := Nat.mul_le_mul_right _ (by omega)
  have h3 : q * (part.length + 1) = part.length * q + q := by ring
  rcases Nat.eq_zero_or_pos q with h4 | h4
  · subst h4; simpa using hpos
  · omega

theorem getD_label_lt {tab : List (Nat × Nat)} (h : ∀ q ∈ tab, q.1 < 2 ^ K ∧ q.2 < 2 ^ K) (i : Nat) :
    (tab.getD i (0, 0)).2 < 2 ^ K := by
  rw [List.getD_eq_getElem?_getD]
  cases hq : tab[i]? with
  | none => exact pos K
  | some q => exact (h q (List.mem_of_getElem? hq)).2

/-- `roomL` is below `2^K`: it is below its upper neighbour (a label, or `2^β`), or below its
lower one plus one. -/
theorem roomL_lt {β : Nat} (hβ : β ≤ K) {tab : List (Nat × Nat)}
    (h : ∀ q ∈ tab, q.1 < 2 ^ K ∧ q.2 < 2 ^ K) (e : Nat) (b : Bool) : roomL β tab e b < 2 ^ K := by
  unfold roomL
  dsimp only
  generalize (tab.findIdx? (·.1 == e)).getD 0 = i
  have hle := getD_label_lt h i
  have hlo : roomLo (tab.take i) (tab.getD i (0, 0)).2 b ≤ 2 ^ K := by
    unfold roomLo
    split
    · split
      · exact Nat.zero_le _
      · next hne =>
        have := (h _ (List.mem_of_mem_take (List.getLast_mem hne))).2; omega
    · omega
  have hhi : roomHi β (tab.drop (i + 1)) (tab.getD i (0, 0)).2 b ≤ 2 ^ K := by
    unfold roomHi
    split
    · omega
    · split
      · exact shift_lt hβ
      · next hne =>
        have := (h _ (List.mem_of_mem_drop (List.head_mem hne))).2; omega
  have : 0 < 2 ^ K := pos K
  omega

/-! ### Nodes -/

/-- Close a `NodeB` goal for a record update whose new values are bounded. -/
syntax "nodeb" : tactic
macro_rules
  | `(tactic| nodeb) => `(tactic| (
      (try intro _ _)
      simp only [NodeB] at *
      (try casesm* _ ∧ _)
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals (try dsimp only)
      all_goals first | assumption | exact pos _ | exact lb_nil | skip))

theorem allN_modify {a : Array Node} (h : ∀ j, NodeB K (a.getX j)) {f : Node → Node}
    (hf : ∀ X, NodeB K X → NodeB K (f X)) (i : Nat) : ∀ j, NodeB K ((a.modify i f).getX j) :=
  allX_modify h hf i

theorem WB.nodeB {s : Core} (h : WB K s) (i : Nat) : NodeB K (s.nodes.getX i) := h.nodes i
theorem WB.nHeight {s : Core} (h : WB K s) (i : Nat) : (s.nodes.getX i).height < 2 ^ K := (h.nodes i).1
theorem WB.nLivePar {s : Core} (h : WB K s) (i : Nat) : (s.nodes.getX i).livePar < 2 ^ K := (h.nodes i).2.1
theorem WB.nWeight {s : Core} (h : WB K s) (i : Nat) : (s.nodes.getX i).weight < 2 ^ K := (h.nodes i).2.2.1
theorem WB.nFirst {s : Core} (h : WB K s) (i : Nat) : (s.nodes.getX i).first < 2 ^ K := (h.nodes i).2.2.2.1
theorem WB.nLast {s : Core} (h : WB K s) (i : Nat) : (s.nodes.getX i).last < 2 ^ K := (h.nodes i).2.2.2.2.1
theorem WB.nT1 {s : Core} (h : WB K s) (i : Nat) : (s.nodes.getX i).t1 < 2 ^ K := (h.nodes i).2.2.2.2.2.1
theorem WB.nT2 {s : Core} (h : WB K s) (i : Nat) : (s.nodes.getX i).t2 < 2 ^ K := (h.nodes i).2.2.2.2.2.2.1
theorem WB.nOvf {s : Core} (h : WB K s) (i : Nat) : (s.nodes.getX i).overflowOf < 2 ^ K :=
  (h.nodes i).2.2.2.2.2.2.2.1
theorem WB.nChildren {s : Core} (h : WB K s) (i : Nat) : ∀ c ∈ (s.nodes.getX i).children, c < 2 ^ K :=
  (h.nodes i).2.2.2.2.2.2.2.2.1
theorem WB.nTable {s : Core} (h : WB K s) (i : Nat) :
    ∀ p ∈ (s.nodes.getX i).table, p.1 < 2 ^ K ∧ p.2 < 2 ^ K := (h.nodes i).2.2.2.2.2.2.2.2.2.1
theorem WB.nInTables {s : Core} (h : WB K s) (i : Nat) : ∀ t ∈ (s.nodes.getX i).inTables, t < 2 ^ K :=
  (h.nodes i).2.2.2.2.2.2.2.2.2.2.1
theorem WB.nSide {s : Core} (h : WB K s) (i : Nat) : ∀ p ∈ (s.nodes.getX i).side, p.1 < 2 ^ K :=
  (h.nodes i).2.2.2.2.2.2.2.2.2.2.2
theorem WB.nOrder {s : Core} (h : WB K s) (i : Nat) : ∀ e ∈ (s.nodes.getX i).order, e < 2 ^ K := by
  intro e he
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp he
  exact (h.nTable i q hq).1
theorem WB.pathE {s : Core} (h : WB K s) (c j : Nat) : (s.path.getX c).getX j < 2 ^ K := h.path c j
theorem WB.cinE {s : Core} (h : WB K s) (c : Nat) : ∀ t ∈ s.cin.getX c, t < 2 ^ K := h.cin c
theorem WB.lparE {s : Core} (h : WB K s) (c : Nat) : s.lpar.getX c < 2 ^ K := h.lpar c

/-- Updates of the top structure's arrays. -/
theorem WB.withPath {s : Core} (h : WB K s) {p : Array (Array Nat)} (hp : ∀ c, ArrB K (p.getX c)) :
    WB K { s with path := p } := { h with path := hp }
theorem WB.withCin {s : Core} (h : WB K s) {p : Array (List Nat)} (hp : ∀ c, ∀ t ∈ p.getX c, t < 2 ^ K) :
    WB K { s with cin := p } := { h with cin := hp }
theorem WB.withLpar {s : Core} (h : WB K s) {p : Array Nat} (hp : ArrB K p) :
    WB K { s with lpar := p } := { h with lpar := hp }

theorem path_setX {s : Core} (h : WB K s) {c j v : Nat} (hv : v < 2 ^ K) :
    ∀ d, ArrB K ((s.path.setX c ((s.path.getX c).setX j v)).getX d) :=
  allX_setX (p := ArrB K) h.path (arrB_setX (h.path c) hv j) c

/-! ### Tags from the top invariant -/

theorem copyS_tag (t : TS) (j : Job) (l : Nat) : (copyS t j l).tag = t.tag := by
  unfold copyS; dsimp only; split_ifs <;> rfl

theorem copyRest_tag (j : Job) (H : Nat) : ∀ k t l, H + 1 - l = k → (copyRest j H t l).tag = t.tag := by
  intro k
  induction k with
  | zero => intro t l hk; rw [copyRest]; rw [ite_eq_right (by omega)]
  | succ k ih =>
    intro t l hk
    rw [copyRest]
    split
    · rw [ih _ _ (by omega), copyS_tag]
    · rfl

theorem finS_tag (t : TS) (oj : Option Job) : (finS t oj).tag = t.tag := by
  unfold finS
  split
  · split
    · exact copyRest_tag _ _ _ _ _ rfl
    · rfl
  · rfl

theorem finS_P (t : TS) (oj : Option Job) : (finS t oj).P = t.P := by
  unfold finS
  split
  · split
    · exact copyRest_P _ _ _ _ _ rfl
    · rfl
  · rfl

/-- **A chunk's tag spells its path**, so it fits in `H·β` bits (`Shape.tags`, `tagUp_lt`). -/
theorem Shape.tag_lt {t : TS} {cl : List Nat} {ord : Nat → List Nat} (S : Shape t cl ord) {c : Nat}
    (hc : c ∈ cl) : t.tag c < 2 ^ (t.P.H * t.P.beta) := by
  rw [S.tags c hc]
  exact tagUp_lt _ (fun j h1 h2 => S.toShapeT.digit_lt hc h1 h2)

/-- **The tags of a core with the top invariant** fit in `H·β` bits. -/
theorem tag_lt_of_topInv {s : Core} (hT : TopInv s) {c : Nat} (hc1 : 1 ≤ c) (hc : c < s.C.size) :
    (s.C.getX c).tag < 2 ^ (s.P.H * s.P.beta) := by
  obtain ⟨-, cl, ord, dr, n0, -, hC, hI⟩ := hT
  have := Shape.tag_lt hI.shape ((hC c).mpr ⟨hc1, hc⟩)
  rw [finS_tag, finS_P] at this
  exact this

/-! ### Node updates -/

theorem WB.modN {s : Core} (h : WB K s) {f : Node → Node} (hf : ∀ X, NodeB K X → NodeB K (f X))
    (i : Nat) : WB K { s with nodes := s.nodes.modify i f } :=
  h.withNodes (allN_modify h.nodes hf i)

theorem WB.ite {c : Prop} [Decidable c] {s a b : Core} (ha : c → WB K a) (hb : ¬ c → WB K b)
    (e : s = if c then a else b) : WB K s := by
  subst e; split
  · next h => exact ha h
  · next h => exact hb h

/-! ### A copy step -/

theorem wb_copyC {s : Core} (h : WB K s) {j : Job} (hj : JobB K j) (l : Nat) : WB K (copyC s j l) := by
  obtain ⟨hx, hy, hz, -⟩ := hj
  have hv := h.pathE j.x l
  have h1 := h.withPath (path_setX (c := j.y) (j := l) h hv)
  have h2 := h1.withPath (path_setX (c := j.z) (j := l) h1 hv)
  unfold copyC
  dsimp only
  split_ifs
  all_goals first
    | exact h2
    | exact h2.modN (fun X hX => by nodeb) _
    | exact (h2.modN (fun X hX => by nodeb) _).modN (fun X hX => by nodeb) _

/-! ### The walk's weight update (class Sz) -/

theorem wb_wiC {s : Core} (h : WB K s) {v : Nat} (hw : (s.nodes.getX v).weight + 2 < 2 ^ K) :
    WB K (wiC s v) := by
  unfold wiC
  refine h.withNodes (allX_modify_at h.nodes ?_)
  have := h.nodeB v
  nodeb

/-! ### A sweep step (class Tag) -/

theorem dsY_lt {s : Core} (h : WB K s) (v : Nat) : dsY s v < 2 ^ K := by
  unfold dsY; split
  · exact h.nFirst v
  · exact h.nLast v

theorem dsT_lt {s : Core} (h : WB K s) (v : Nat) : dsT s v < 2 ^ K := by
  unfold dsT; split
  · exact h.nT1 v
  · exact h.nT2 v

/-- **A sweep step** moves chunk `dsY` to target `dsT` (R) and writes its new tag (the
hypothesis). -/
theorem wb_dsS {s : Core} (h : WB K s) {v tag : Nat} (htag : tag < 2 ^ K) : WB K (dsS s v tag) := by
  have hy := dsY_lt h v
  have ht := dsT_lt h v
  have hn := h.cNext (dsY s v)
  have hp := h.cPrev (dsY s v)
  have h1 : WB K { s with C := s.C.modify (dsY s v) fun C => { C with tag := tag } } :=
    h.withC (allX_modify h.C (fun X hX => by recb) _)
  have h2 := h1.withPath (path_setX (c := dsY s v) (j := (s.nodes.getX v).height) h1 ht)
  unfold dsS
  dsimp only
  split_ifs
  all_goals first
    | exact (h2.modN (fun X hX => by nodeb) _).modN (fun X hX => by nodeb) _
    | exact ((h2.modN (fun X hX => by nodeb) _).modN (fun X hX => by nodeb) _).modN (fun X hX => by nodeb) _

/-! ### The end of a drain (class R) -/

theorem wb_dropTableS {s : Core} (h : WB K s) (v hh e : Nat) : WB K (dropTableS v hh s e) := by
  unfold dropTableS
  split_ifs
  · exact h.withCin (allX_setX (p := fun l => ∀ t ∈ l, t < 2 ^ K) h.cin (lb_erase (h.cinE e) v) e)
  · exact h
  · refine h.withNodes (allX_modify_at h.nodes ?_)
    have := h.nodeB e
    nodeb
    exact lb_erase ‹_› v
  · exact h

theorem wb_fold_dropTableS (v hh : Nat) : ∀ (l : List Nat) {s : Core}, WB K s →
    WB K (l.foldl (dropTableS v hh) s)
  | [], _, h => h
  | e :: l, _, h => by
    simp only [List.foldl_cons]; exact wb_fold_dropTableS v hh l (wb_dropTableS h v hh e)

theorem wb_dropEntryS {s : Core} (h : WB K s) (v T : Nat) : WB K (dropEntryS v s T) := by
  unfold dropEntryS
  refine h.modN (fun X hX => ?_) T
  nodeb
  · exact lb_assocErase ‹_› v
  · exact lb_assocErase ‹_› v

theorem wb_fold_dropEntryS (v : Nat) : ∀ (l : List Nat) {s : Core}, WB K s →
    WB K (l.foldl (dropEntryS v) s)
  | [], _, h => h
  | e :: l, _, h => by
    simp only [List.foldl_cons]; exact wb_fold_dropEntryS v l (wb_dropEntryS h v e)

theorem wb_releaseS {s : Core} (h : WB K s) (v t : Nat) : WB K (releaseS v s t) := by
  unfold releaseS
  split
  · exact h.modN (fun X hX => by nodeb) t
  · exact h

/-- **The end of a drain**: entries and tables lose the ghost (sublists), its targets are
released, it dies. -/
theorem wb_fdS {s : Core} (h : WB K s) (v : Nat) : WB K (fdS v s) := by
  have h4 : WB K (fd4 v s) :=
    wb_releaseS (wb_releaseS (wb_fold_dropEntryS v _ (wb_fold_dropTableS v _ _ h)) v _) v _
  unfold fdS
  exact h4.modN (fun X hX => by nodeb) v

/-! ### A drain start (classes F, Lab, Sz) -/

theorem nodeB_setTS {X : Node} (hX : NodeB K X) {tab : List (Nat × Nat)} {side : List (Nat × Side)}
    (ht : ∀ q ∈ tab, q.1 < 2 ^ K ∧ q.2 < 2 ^ K) (hs : ∀ q ∈ side, q.1 < 2 ^ K) : NodeB K (setTS tab side X) := by
  unfold setTS; nodeb

theorem aroundT_lt {tab : List (Nat × Nat)} (h : ∀ q ∈ tab, q.1 < 2 ^ K ∧ q.2 < 2 ^ K) {e n1 n2 a b : Nat}
    (h1 : n1 < 2 ^ K) (h2 : n2 < 2 ^ K) (ha : a < 2 ^ K) (hb : b < 2 ^ K) :
    ∀ q ∈ aroundT tab e n1 n2 a b, q.1 < 2 ^ K ∧ q.2 < 2 ^ K := by
  unfold aroundT
  exact lb_insertIdx (P := fun q : Nat × Nat => q.1 < 2 ^ K ∧ q.2 < 2 ^ K)
    (lb_insertIdx (P := fun q : Nat × Nat => q.1 < 2 ^ K ∧ q.2 < 2 ^ K) h ⟨h2, hb⟩ _) ⟨h1, ha⟩ _

theorem sideAround_lt {T : Node} (hT : ∀ q ∈ T.side, q.1 < 2 ^ K) {e n1 n2 : Nat} (h1 : n1 < 2 ^ K)
    (h2 : n2 < 2 ^ K) : ∀ q ∈ sideAround T e n1 n2, q.1 < 2 ^ K := by
  unfold sideAround
  split
  · exact lb_assocSet (P := fun x => x < 2 ^ K) (k := n2) (lb_assocSet (P := fun x => x < 2 ^ K) (k := n1) hT h1 _) h2 _
  · exact hT

/-- Insertions around `e` in a list of tables: the new entries and their labels are bounded. -/
theorem allN_fold_aroundF {s0 : Core} (h0 : WB K s0) {e n1 n2 : Nat} {f : Nat → Nat × Nat}
    (h1 : n1 < 2 ^ K) (h2 : n2 < 2 ^ K) (hf : ∀ T, (f T).1 < 2 ^ K ∧ (f T).2 < 2 ^ K) :
    ∀ (l : List Nat) (ns : Array Node), (∀ j, NodeB K (ns.getX j)) →
      ∀ j, NodeB K ((l.foldl (fun ns T => ns.modify T (aroundF s0 e n1 n2 f T)) ns).getX j)
  | [], _, h => h
  | T :: l, ns, h => by
    simp only [List.foldl_cons]
    refine allN_fold_aroundF h0 h1 h2 hf l _ (allN_modify h (fun X hX => ?_) T)
    unfold aroundF
    exact nodeB_setTS hX (aroundT_lt (h0.nTable T) h1 h2 (hf T).1 (hf T).2) (sideAround_lt (h0.nSide T) h1 h2)

theorem wb_addTableS {s : Core} (h : WB K s) {w : Nat} (hw : w < 2 ^ K) (hh e : Nat) :
    WB K (addTableS hh w e s) := by
  unfold addTableS
  split
  · exact h.withCin (allX_setX (p := fun l => ∀ t ∈ l, t < 2 ^ K) h.cin
      (lb_append (h.cinE e) (lb_cons hw lb_nil)) e)
  · refine h.withNodes (allX_modify_at h.nodes ?_)
    have := h.nodeB e
    nodeb
    exact lb_append ‹_› (lb_cons hw lb_nil)

theorem wb_fold_addTableS {w : Nat} (hw : w < 2 ^ K) (hh : Nat) : ∀ (l : List Nat) {s : Core}, WB K s →
    WB K (l.foldl (fun s e => addTableS hh w e s) s)
  | [], _, h => h
  | e :: l, _, h => by
    simp only [List.foldl_cons]; exact wb_fold_addTableS hw hh l (wb_addTableS h hw hh e)

theorem wb_setParentS {s : Core} (h : WB K s) {w : Nat} (hw : w < 2 ^ K) (hh e : Nat) :
    WB K (setParentS hh w e s) := by
  unfold setParentS
  split
  · exact h.withLpar (arrB_setX h.lpar hw e)
  · exact h.modN (fun X hX => by nodeb) e

theorem wb_fold_setParentS {w : Nat} (hw : w < 2 ^ K) (hh : Nat) : ∀ (l : List Nat) {s : Core}, WB K s →
    WB K (l.foldl (fun s e => setParentS hh w e s) s)
  | [], _, h => h
  | e :: l, _, h => by
    simp only [List.foldl_cons]; exact wb_fold_setParentS hw hh l (wb_setParentS h hw hh e)

section start
variable {t : Core} (h : WB K t) {v : Nat} {side : List (Nat × Side)}
include h

theorem wb_sd1 : WB K (sd1 t v) := by
  have hh := h.nHeight v
  unfold sd1
  exact h.withNodes (allX_push (allX_push h.nodes (by nodeb)) (by nodeb))

theorem wb_sd2 (hN : t.nodes.size + 2 ≤ 2 ^ K) (hβ : t.P.beta ≤ K) : WB K (sd2 t v) := by
  have h1 := wb_sd1 (v := v) h
  unfold sd2
  refine h1.withNodes (allN_fold_aroundF h1 (by omega) (by omega) (fun T => ?_) _ _ h1.nodes)
  unfold sF
  exact ⟨roomL_lt hβ (h.nTable T) v true, roomL_lt hβ (h.nTable T) v false⟩

theorem sEntries_lt : ∀ e ∈ sEntries t v, e < 2 ^ K := lb_filter (h.nOrder v) _

theorem wb_sd4 (hN : t.nodes.size + 2 ≤ 2 ^ K) (hβ : t.P.beta ≤ K) : WB K (sd4 t v side) := by
  have h2 := wb_sd2 (v := v) h hN hβ
  have hT := h.nInTables v
  have hev : ∀ (p : List Nat), (∀ e ∈ p, e < 2 ^ K) →
      ∀ q ∈ evenTable t.P.beta p, q.1 < 2 ^ K ∧ q.2 < 2 ^ K := fun p hp q hq => by
    obtain ⟨a, b⟩ := evenTable_lt hp q hq
    exact ⟨a, lt_pow_mono b hβ⟩
  have hl := hev _ (lb_filter (sEntries_lt h (v := v)) (fun x => lookup side x == some .left))
  have hr := hev _ (lb_filter (sEntries_lt h (v := v)) (fun x => lookup side x == some .right))
  unfold sd4
  exact (h2.modN (fun X hX => by nodeb) _).modN (fun X hX => by nodeb) _

theorem wb_sd6 (hN : t.nodes.size + 2 ≤ 2 ^ K) (hβ : t.P.beta ≤ K) : WB K (sd6 t v side) := by
  unfold sd6
  exact wb_fold_addTableS (by omega) _ _ (wb_fold_addTableS (by omega) _ _ (wb_sd4 h hN hβ))

theorem wb_sd8 (hN : t.nodes.size + 2 ≤ 2 ^ K) (hβ : t.P.beta ≤ K) (hv : v < 2 ^ K)
    (hw : ((sCh1 t v side).map (sWt t v)).sum < 2 ^ K) : WB K (sd8 t v side) := by
  have h6 := wb_fold_setParentS (w := t.nodes.size) (by omega) (sH t v) (sCh1 t v side) (wb_sd6 (v := v) (side := side) h hN hβ)
  have hc := lb_filter (h.nChildren v) (fun x => lookup side x == some .left)
  have hl := h.nLivePar v
  unfold sd8
  exact h6.modN (fun X hX => by nodeb) _

theorem wb_sd10 (hN : t.nodes.size + 2 ≤ 2 ^ K) (hβ : t.P.beta ≤ K) (hv : v < 2 ^ K)
    (hw1 : ((sCh1 t v side).map (sWt t v)).sum < 2 ^ K)
    (hw2 : ((sCh2 t v side).map (sWt t v)).sum < 2 ^ K) : WB K (sd10 t v side) := by
  have h8 := wb_fold_setParentS (w := t.nodes.size + 1) (by omega) (sH t v) (sCh2 t v side)
    (wb_sd8 (side := side) h hN hβ hv hw1)
  have hc := lb_filter (h.nChildren v) (fun x => lookup side x == some .right)
  have hl := h.nLivePar v
  unfold sd10
  exact h8.modN (fun X hX => by nodeb) _

/-- **A drain start**: two fresh nodes (F: `nodes.size + 2 ≤ 2^K`), their tables (Lab:
`evenTable`, `roomL`, given `β ≤ K`), their weights (Sz: the sums, hypotheses), and the side
list (keys from the ghost's table, hypothesis). -/
theorem wb_sdS (hN : t.nodes.size + 2 ≤ 2 ^ K) (hβ : t.P.beta ≤ K) (hv : v < 2 ^ K)
    (hw1 : ((sCh1 t v side).map (sWt t v)).sum < 2 ^ K)
    (hw2 : ((sCh2 t v side).map (sWt t v)).sum < 2 ^ K) (hs : ∀ q ∈ side, q.1 < 2 ^ K) :
    WB K (sdS t v side) := by
  have h10 := wb_sd10 h hN hβ hv hw1 hw2
  have : t.nodes.size < 2 ^ K := by omega
  have : t.nodes.size + 1 < 2 ^ K := by omega
  unfold sdS
  refine (h10.modN (fun X hX => ?_) _).modN (fun X hX => by nodeb) _
  nodeb
  exact lb_replace1 (lb_cons (by omega) (lb_cons (by omega) lb_nil)) v _ ‹_›

end start

end OrderMaintenance.Proof.Word
