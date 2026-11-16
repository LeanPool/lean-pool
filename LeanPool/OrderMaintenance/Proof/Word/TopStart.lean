/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Word.TopStep


/-!
# Theorem W, stage B2: a split's insertion into the top structure

`insertAround x y z` reads labels for the new chunks `y`, `z` around `x` (`insertAroundPrep`,
read-only), writes their tags (Tag), and inserts them into the tables, paths and children of the
top structure (`insertAroundFinish`: R, F for `y`, `z`, Lab for the labels). The tags are bounded by
the top invariant of the state after the split (`tag_lt_of_topInv`), as a hypothesis on the final
state: the finish leaves the chunk records alone, so the final tags of `y`, `z` are the written
ones.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Word

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top
variable {K : Nat} {P0 : Params}

/-! ### Read-only and chunk-preserving runs -/

/-- The state is unchanged. -/
def RO (s s' : Core) : Prop := s' = s

instance : IsPre RO := ⟨fun _ => rfl, fun _ _ _ h1 h2 => h2.trans h1⟩

/-- The chunk records are unchanged. -/
def CS (s s' : Core) : Prop := s'.C = s.C

instance : IsPre CS := ⟨fun _ => rfl, fun _ _ _ h1 h2 => h2.trans h1⟩

theorem ro_roomNextTo (t e : Nat) (b : Bool) : Pres RO (roomNextTo t e b) := by
  unfold roomNextTo; pres [pres_getP, pres_getN _]

theorem ro_insertAroundPrep (x : Nat) : Pres RO (insertAroundPrep x) := by
  unfold insertAroundPrep
  pres [pres_getPath _, ro_roomNextTo _ _ _, pres_getN _, pres_getC _, pres_getLpar _]

theorem ro_guardTag (c t : Nat) : Pres RO (guardTag c t) := by
  unfold guardTag; pres [pres_getC _]

theorem cs_modN (i : Nat) (f : Node → Node) : Pres CS (modN i f) := by
  unfold modN; pres; intro s; rfl

theorem cs_insertAroundFinish (x y z : Nat) (tabs ly lz : List Nat) (lp : Nat) :
    Pres CS (insertAroundFinish x y z tabs ly lz lp) := by
  unfold insertAroundFinish insertAroundIn tableInsert joinChunk setPath setInTables setLpar
  pres [pres_getP, pres_getN _, cs_modN _ _]
  all_goals intro s; rfl

/-- A guarded tag write that succeeds writes the tag. -/
theorem guardedSetTag_ok {s s' : Core} {c t : Nat} {u : PUnit} (h : (guardedSetTag c t).run s = .ok u s') :
    s' = { s with C := s.C.modify c fun C => { C with tag := t } } := by
  unfold guardedSetTag modC at h
  rw [run_bind] at h
  have hg := ro_guardTag c t s
  rcases hr : (guardTag c t).run s with ⟨a, s1⟩ | ⟨e, s1⟩
  · rw [hr] at h hg
    have e1 : s1 = s := hg
    subst e1
    simp only [run_modify] at h
    obtain ⟨-, rfl⟩ := EStateM.Result.ok.inj h
    rfl
  · rw [hr] at h; simp at h

/-! ### Triples -/

theorem NodeB.tab {n : Node} (h : NodeB K n) : ∀ p ∈ n.table, p.1 < 2 ^ K ∧ p.2 < 2 ^ K :=
  h.2.2.2.2.2.2.2.2.2.1
theorem NodeB.sd {n : Node} (h : NodeB K n) : ∀ p ∈ n.side, p.1 < 2 ^ K := h.2.2.2.2.2.2.2.2.2.2.2

theorem half_lt {lo hi B : Nat} (h : ¬ lo ≥ hi) (hB : hi ≤ B) : (lo + hi - 1) / 2 < B := by omega

/-- **A label next to an entry** is below `2^K` (Lab): below its upper neighbour, a label or `2^β`. -/
theorem ht_roomNextTo (hβ : P0.beta ≤ K) (t e : Nat) (b : Bool) :
    HT K P0 (roomNextTo t e b) (· < 2 ^ K) := by
  unfold roomNextTo
  refine HT.getP_bind (HT.bind (HT.getN t) fun T hT => ?_)
  have hl := getD_label_lt hT.tab
  have hb := shift_lt (B := P0.beta) hβ
  cases b
  all_goals
    simp only [Bool.false_eq_true, ite_false, ite_true]
    split
    all_goals first
      | exact HT.guard
      | (refine HT.ite (fun _ => HT.bind HT.guard_false fun _ h => h.elim) (fun hc => HT.pure (half_lt hc ?_))
         first | exact le_of_lt (hl _) | (split <;> first | exact le_of_lt (hl _) | exact hb))

/-- A table insertion: the new entry and its label (hypotheses), the side list (R). -/
theorem ht_tableInsert {t e new : Nat} {before : Bool} {lab : Nat} (hn : new < 2 ^ K) (hl : lab < 2 ^ K) :
    HT K P0 (tableInsert t e new before lab) (fun _ => True) := by
  unfold tableInsert
  refine HT.bind (HT.getN t) fun T hT => ?_
  have key : ∀ (tab : List (Nat × Nat)) (side : List (Nat × Side)),
      (∀ q ∈ tab, q.1 < 2 ^ K ∧ q.2 < 2 ^ K) → (∀ p ∈ side, p.1 < 2 ^ K) →
      HT K P0 (modN t fun n => { n with table := tab, side := side }) (fun _ => True) := by
    intro tab side htab hs
    unfold modN
    exact HT.modify fun s hW hP => ⟨hW.modN (fun X hX => by nodeb) t, hP⟩
  have htab := lb_insertIdx (P := fun q : Nat × Nat => q.1 < 2 ^ K ∧ q.2 < 2 ^ K) hT.tab (y := (new, lab)) ⟨hn, hl⟩
  split
  all_goals first
    | exact HT.guard
    | (dsimp only
       split
       · split
         · exact HT.bind (HT.pure (lb_assocSet (P := fun x => x < 2 ^ K) hT.sd hn _)) fun side hs =>
             key _ side (htab _) hs
         · exact HT.bind HT.guard_false fun _ h => h.elim
       · exact HT.bind (HT.pure hT.sd) fun side hs => key _ side (htab _) hs)

theorem ht_insertAroundIn {v v1 v2 : Nat} {q : Nat × Nat × Nat} (h1 : v1 < 2 ^ K) (h2 : v2 < 2 ^ K)
    (ha : q.2.1 < 2 ^ K) (hb : q.2.2 < 2 ^ K) : HT K P0 (insertAroundIn v v1 v2 q) (fun _ => True) := by
  unfold insertAroundIn
  exact HT.bind (ht_tableInsert h1 ha) fun _ _ => ht_tableInsert h2 hb

theorem ht_joinChunk {tabs : List Nat} {lp c : Nat} (ht : ∀ T ∈ tabs, T < 2 ^ K) (hlp : lp < 2 ^ K) :
    HT K P0 (joinChunk tabs lp c) (fun _ => True) := by
  intro s hW hP
  rw [joinChunk_run]
  refine ⟨⟨?_, hP⟩, trivial⟩
  have h1 : ∀ d, ArrB K ((s.path.setX c (Array.replicate (s.P.H + 1) NIL)).getX d) := by
    refine allX_setX (p := ArrB K) hW.path (fun j => ?_) c
    simp only [Array.getX, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> exact pos K
  have h2 := allX_setX (p := fun l => ∀ t ∈ l, t < 2 ^ K) hW.cin ht c
  have h3 := arrB_setX hW.lpar hlp c
  exact ((hW.withPath h1).withCin h2).withLpar h3

/-- **The rest of a split's insertion** (R, F, Lab): the new chunks `y`, `z` enter the tables
(labels `ly`, `lz`), the paths (`NIL` rows), the tables lists (`tabs`), the live parent and its
children. -/
theorem ht_insertAroundFinish {x y z lp : Nat} {tabs ly lz : List Nat} (hK : 1 ≤ K) (hx : x < 2 ^ K)
    (hy : y < 2 ^ K) (hz : z < 2 ^ K) (ht : ∀ T ∈ tabs, T < 2 ^ K) (hly : ∀ a ∈ ly, a < 2 ^ K)
    (hlz : ∀ a ∈ lz, a < 2 ^ K) (hlp : lp < 2 ^ K) :
    HT K P0 (insertAroundFinish x y z tabs ly lz lp) (JobB K) := by
  unfold insertAroundFinish
  refine HT.bind (HT.forM_list _ fun q hq => ?_) fun _ _ =>
    HT.bind (ht_joinChunk ht hlp) fun _ _ => HT.bind (ht_joinChunk ht hlp) fun _ _ =>
      HT.bind (HT.modify fun s hW hP => ⟨hW.modN (fun X hX => ?_) lp, hP⟩) fun _ _ =>
        HT.pure (jobB_copy hK hx hy hz)
  · obtain ⟨-, hq2⟩ := List.of_mem_zip hq
    obtain ⟨ha, hb⟩ := List.of_mem_zip hq2
    exact ht_insertAroundIn hy hz (hly _ ha) (hlz _ hb)
  · nodeb
    exact lb_replace1 (P := fun c => c < 2 ^ K) (lb_cons hy (lb_cons hx (lb_cons hz lb_nil))) x _ ‹_›

theorem ht_mapM_roomNextTo (hβ : P0.beta ≤ K) (l : List Nat) (e : Nat) (b : Bool) :
    HT K P0 (l.mapM (roomNextTo · e b)) (fun r => ∀ a ∈ r, a < 2 ^ K) :=
  HT.mapM_list l fun T _ => ht_roomNextTo hβ T e b

theorem ht_getLpar (c : Nat) : HT K P0 (getLpar c) (· < 2 ^ K) :=
  fun _ hs hP => ⟨⟨hs, hP⟩, hs.lparE c⟩

/-- **The read-only part of a split's insertion** returns bounded tables, labels and parent. -/
theorem ht_insertAroundPrep (hβ : P0.beta ≤ K) (x : Nat) :
    HT K P0 (insertAroundPrep x) (fun r => (∀ T ∈ r.2.2.1, T < 2 ^ K) ∧ (∀ a ∈ r.2.2.2.1, a < 2 ^ K) ∧
      (∀ a ∈ r.2.2.2.2.1, a < 2 ^ K) ∧ r.2.2.2.2.2 < 2 ^ K) := by
  unfold insertAroundPrep getPath
  refine HT.bind (HT.bind HT.get fun st _ => HT.pure (Q := fun _ => True) trivial) fun _ _ => ?_
  refine HT.bind HT.get fun st hst => ?_
  refine HT.bind (ht_mapM_roomNextTo hβ _ x true) fun ly hly => ?_
  refine HT.bind (ht_mapM_roomNextTo hβ _ x false) fun lz hlz => ?_
  ht [ht_getLpar _]
  all_goals first
    | exact ⟨hst.cinE x, hly, hlz, by assumption⟩

/-- **A split's insertion into the top structure keeps the stored-value bound**, given the new
chunks below `2^K` and the bound of their final tags (which the top invariant after the split
gives). -/
theorem insertAround_wb {t : Core} {x y z : Nat} (hW : WB K t) (hK : 1 ≤ K) (hβ : t.P.beta ≤ K)
    (hx : x < 2 ^ K) (hy : y < 2 ^ K) (hz : z < 2 ^ K) (hyz : y ≠ z) (hys : y < t.C.size)
    (hzs : z < t.C.size) {job : Job} {s2 : Core} (hr : (insertAround x y z).run t = .ok job s2)
    (htag : (s2.C.getX y).tag < 2 ^ K ∧ (s2.C.getX z).tag < 2 ^ K) : WB K s2 ∧ JobB K job := by
  unfold insertAround at hr
  rw [run_bind] at hr
  rcases hp : (insertAroundPrep x).run t with ⟨a, t1⟩ | ⟨e, t1⟩
  · rw [hp] at hr
    have e1 : t1 = t := by have := ro_insertAroundPrep x t; rw [hp] at this; exact this
    subst e1
    obtain ⟨-, hb⟩ := (ht_insertAroundPrep (P0 := t1.P) hβ x).ok hW rfl hp
    obtain ⟨ty, tz, tabs, ly, lz, lp⟩ := a
    dsimp only at hr hb
    rw [run_bind] at hr
    rcases hg1 : (guardedSetTag y ty).run t1 with ⟨u1, t2⟩ | ⟨e, t2⟩
    · rw [hg1] at hr
      have e2 := guardedSetTag_ok hg1
      subst e2
      dsimp only at hr
      rw [run_bind] at hr
      rcases hg2 : (guardedSetTag z tz).run
          { t1 with C := t1.C.modify y fun C => { C with tag := ty } } with ⟨u2, t3⟩ | ⟨e, t3⟩
      · rw [hg2] at hr
        have e3 := guardedSetTag_ok hg2
        subst e3
        dsimp only at hr
        have hCS := cs_insertAroundFinish x y z tabs ly lz lp
          { t1 with C := (t1.C.modify y (fun C => { C with tag := ty })).modify z (fun C => { C with tag := tz }) }
        rw [hr] at hCS
        change s2.C = _ at hCS
        rw [hCS] at htag
        simp only [Array.getX_modify, Array.size_modify', hys, hzs, hyz, Ne.symm hyz, and_true,
          ite_true, ite_false] at htag
        obtain ⟨hty, htz⟩ := htag
        have hW3 : WB K { t1 with C := (t1.C.modify y (fun C => { C with tag := ty })).modify z (fun C => { C with tag := tz }) } :=
          hW.withC (allX_modify (allX_modify hW.C (fun X hX => by recb) _) (fun X hX => by recb) _)
        have := (ht_insertAroundFinish (P0 := t1.P) hK hx hy hz hb.1 hb.2.1 hb.2.2.1 hb.2.2.2).ok hW3 rfl hr
        exact ⟨this.1.1, this.2⟩
      · rw [hg2] at hr; simp at hr
    · rw [hg1] at hr; simp at hr
  · rw [hp] at hr; simp at hr

end OrderMaintenance.Proof.Word

namespace OrderMaintenance.Proof.Word

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top
variable {K : Nat}

/-! ### The construction of the initial chain -/

/-- Room for the construction: heights up to `H + 1`, labels and tags. -/
structure PrepRoom (K : Nat) (P : Params) : Prop where
  top : TopRoom K P
  H1 : 1 ≤ P.H
  b1 : 1 ≤ P.beta
  HK : P.H + 1 < 2 ^ K

theorem WB.withPrep {s : Core} (h : WB K s) {p : Option Prep} (hp : ∀ q, p = some q → PrepB K q) :
    WB K { s with prep := p } := { h with prep := hp }

theorem PrepRoom.center {P : Params} (h : PrepRoom K P) : 1 <<< (P.beta - 1) < 2 ^ K :=
  center_lt h.top.beta (Or.inr h.b1)

theorem PrepRoom.chainTag {P : Params} (h : PrepRoom K P) {m : Nat} (hm : m ≤ P.H) :
    OrderMaintenance.Proof.Top.chainTag P m < 2 ^ K :=
  lt_of_lt_of_le (chainTag_lt h.b1 m)
    (Nat.pow_le_pow_right (by norm_num) (le_trans (Nat.mul_le_mul_right _ hm) h.top.tag))

theorem chainNew_nodeB {P : Params} {pr : Prep} {n : Node} (hn : NodeB K n) (hc : pr.chunk < 2 ^ K)
    (hb : pr.below < 2 ^ K) (hK : 1 < 2 ^ K) (hce : 1 <<< (P.beta - 1) < 2 ^ K) :
    NodeB K (chainNew P pr n) := by
  unfold chainNew
  nodeb
  · exact lb_cons hb lb_nil
  · exact lb_cons (P := fun p : Nat × Nat => p.1 < 2 ^ K ∧ p.2 < 2 ^ K) ⟨hb, hce⟩ lb_nil

theorem prepNext_prepB {P : Params} {pr : Prep} {v : Nat} (hp : PrepB K pr) (hh : pr.h + 1 < 2 ^ K)
    (hv : v < 2 ^ K) (ht : pr.tag ||| ((1 <<< (P.beta - 1)) <<< ((pr.h - 1) * P.beta)) < 2 ^ K) :
    PrepB K (prepNext P pr v) := by
  obtain ⟨hc, -, -, -, hpa⟩ := hp
  refine ⟨hc, hh, hv, ht, ?_⟩
  exact mem_setX (P := (· < 2 ^ K)) hpa hv (pos K) pr.h

/-- **A construction step keeps the stored-value bound** (stage `h` of `Stage`): a chain node
(index `nodes.size = h`, F; its table holds the centre, Lab), the next height and the tag of the
chain so far (`chainTag`, below `2^(hβ)`), or, at the end, the stored path and tag. -/
theorem initStep_wb {P : Params} {h : Nat} {s : Core} (S : Stage P h s) (hW : WB K s)
    (hR : PrepRoom K P) (h1 : 1 ≤ h) (hH : h ≤ P.H + 1) {b : Bool} {s' : Core}
    (hr : initStep.run s = .ok b s') : WB K s' := by
  obtain ⟨pa, hp, hsz, hpa⟩ := S.pr
  have hP := S.P
  have hK1 : 1 < 2 ^ K := by have := hR.HK; omega
  have hce := hR.center
  by_cases e1 : h = 1
  · subst e1
    obtain ⟨hc, hh, hbl, htg, hpp⟩ := hW.prep _ hp
    rw [initStep_first s _ hp rfl (by rw [hP]; exact hR.H1)] at hr
    obtain ⟨-, rfl⟩ := EStateM.Result.ok.inj hr
    clear hr
    have hn0 : ∀ i, NodeB K ((#[default].push ({ height := 1 } : Node)).getX i) :=
      getX_of (nodeB_default K) (fun x hx => by
        simp only [List.push_toArray, List.cons_append, List.nil_append, List.mem_toArray,
          List.mem_cons,
          List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact nodeB_default K
        · nodeb)
    have hn := allX_modify hn0 (fun X hX => chainNew_nodeB (P := s.P) hX hc hbl hK1 (by rw [hP]; exact hce)) 1
    have hpath : ∀ c, ArrB K ((#[] : Array (Array Nat)).getX c) := fun c => by
      simp only [getX_empty]; exact arrB_default K
    have hcin : ∀ c, ∀ t ∈ ((((#[] : Array (List Nat)).setX 1 []).setX 1 [1]).getX c), t < 2 ^ K :=
      allX_setX (p := fun l => ∀ t ∈ l, t < 2 ^ K) (allX_setX (p := fun l => ∀ t ∈ l, t < 2 ^ K)
        (fun c t ht => by simp only [getX_empty] at ht; change t ∈ ([] : List Nat) at ht; cases ht) lb_nil _) (lb_cons (P := (· < 2 ^ K)) hK1 lb_nil) _
    have hlpar : ArrB K ((#[] : Array Nat).setX 1 1) := arrB_setX (arrB_empty K) hK1 _
    have hprep : PrepB K (prepNext s.P
        { chunk := 1, h := 1, below := if 1 = 1 then 1 else 1 - 1, tag := chainTag P (1 - 1), path := pa } 1) := by
      refine prepNext_prepB ⟨hc, hh, hbl, htg, hpp⟩ (by have := hR.HK; have := hR.H1; show 1 + 1 < _; omega)
        hK1 ?_
      rw [hP]
      show chainTag P (1 - 1) ||| ((1 <<< (P.beta - 1)) <<< ((1 - 1) * P.beta)) < 2 ^ K
      have := chainTag_succ hR.b1 (1 - 1)
      unfold center at this
      rw [this]
      exact hR.chainTag hR.H1
    exact (((hW.withNodes hn).withPath hpath).withCin hcin).withLpar hlpar |>.withPrep
      (fun q hq => by cases hq; exact hprep)
  · by_cases eH : h ≤ P.H
    · have hn := S.nsz (by omega)
      rw [ite_eq_right e1] at hp
      obtain ⟨hc, hh, hbl, htg, hpp⟩ := hW.prep _ hp
      dsimp only at hc hh hbl htg hpp
      rw [initStep_mid s _ hp (by simpa using e1) (by rw [hP]; exact eH)] at hr
      obtain ⟨-, rfl⟩ := EStateM.Result.ok.inj hr
      clear hr
      have hsz' : s.nodes.size < 2 ^ K := by rw [hn]; have := hR.HK; omega
      have hnd : ∀ i, NodeB K ((((s.nodes.push { height := h }).modify s.nodes.size
          (chainNew s.P { chunk := 1, h := h, below := h - 1, tag := chainTag P (h - 1), path := pa })).modify
            (h - 1) (fun n => { n with inTables := [s.nodes.size], livePar := s.nodes.size })).getX i) := by
        have hhK : h < 2 ^ K := by have := hR.HK; omega
        have hnew : NodeB K ({ height := h } : Node) := by nodeb
        have a1 := allX_push (p := NodeB K) hW.nodes hnew
        have a2 := allX_modify_at (p := NodeB K) (i := s.nodes.size) a1
          (f := chainNew s.P { chunk := 1, h := h, below := h - 1, tag := chainTag P (h - 1), path := pa })
          (chainNew_nodeB (a1 _) hc (by show h - 1 < 2 ^ K; omega) hK1 (by rw [hP]; exact hce))
        exact allX_modify (p := NodeB K) a2 (fun X hX => by nodeb; exact lb_cons (P := (· < 2 ^ K)) hsz' lb_nil) _
      refine (hW.withNodes hnd).withPrep ?_
      · intro q hq
        cases hq
        refine prepNext_prepB ⟨hc, hh, hbl, htg, hpp⟩ (by have := hR.HK; show h + 1 < _; omega) hsz' ?_
        rw [hP]
        show chainTag P (h - 1) ||| ((1 <<< (P.beta - 1)) <<< ((h - 1) * P.beta)) < 2 ^ K
        have := chainTag_succ hR.b1 (h - 1)
        unfold center at this
        rw [this, show h - 1 + 1 = h by omega]
        exact hR.chainTag eH
    · rw [ite_eq_right e1] at hp
      obtain ⟨hc, hh, hbl, htg, hpp⟩ := hW.prep _ hp
      dsimp only at hc hh hbl htg hpp
      rw [initStep_last s _ hp (by simpa using e1) (by rw [hP]; show P.H < h; omega)] at hr
      obtain ⟨-, rfl⟩ := EStateM.Result.ok.inj hr
      clear hr
      have hpa' : ∀ d, ArrB K ((s.path.setX 1 pa).getX d) := by
        refine allX_setX (p := ArrB K) hW.path (fun j => ?_) _
        simp only [Array.getX, Array.getD_eq_getD_getElem?]
        cases hj : pa[j]? with
        | none => exact pos K
        | some w => exact hpp w (Array.mem_of_getElem? hj)
      have hC' := allX_modify (p := ChunkB K) hW.C (f := fun C => { C with tag := chainTag P (h - 1) })
        (fun X hX => by recb) 1
      exact ((hW.withPath hpa').withC hC').withPrep (p := none) (fun q hq => by cases hq)

/-- The fresh core before its chain is built. -/
theorem wb_prepStart {P : Params} (hP : ParamsB K P) (hL : LabRoom K P) (r : Bool) :
    WB K { initState P with
      prep := some { chunk := 1, below := 1, path := Array.replicate (P.H + 1) NIL }, ready := r } := by
  have hK1 : 1 < 2 ^ K := Nat.one_lt_two_pow (by have := hL.K1; omega)
  have h0 := initState_wB hP hL.Be hL.Bg hL.K1
  refine (h0.withPrep (p := some { chunk := 1, below := 1, path := Array.replicate (P.H + 1) NIL })
    (fun q hq => ?_)).withReady
  cases hq
  refine ⟨hK1, hK1, hK1, pos K, fun v hv => ?_⟩
  rw [Array.mem_replicate] at hv
  rw [hv.2]; exact pos K

/-- The eager construction's loop keeps the stored-value bound. -/
theorem wb_initLoop {P : Params} (hPP : topPP P) (hR : PrepRoom K P) :
    ∀ (l : List Nat) (h : Nat) (s : Core), Stage P h s → WB K s → 1 ≤ h → h ≤ P.H + 1 → ∀ s',
      (forIn l PUnit.unit fun (_ : Nat) (_ : PUnit) => do
          let b ← initStep
          if b = true then pure (ForInStep.done PUnit.unit) else pure (ForInStep.yield PUnit.unit) :
          CM PUnit).run s = .ok () s' → WB K s'
  | [], h, s, _, hW, _, _, s', hr => by
    simp only [List.forIn_nil] at hr
    obtain ⟨-, rfl⟩ := EStateM.Result.ok.inj hr; exact hW
  | x :: t, h, s, S, hW, h1, hH, s', hr => by
    rw [List.forIn_cons, run_bind, run_bind] at hr
    by_cases hh : h ≤ P.H
    · obtain ⟨s1, hr1, S1, -⟩ := stage_next S h1 hh hPP.beta
      have hW1 := initStep_wb S hW hR h1 hH hr1
      rw [hr1] at hr
      simp only [Bool.false_eq_true, ite_false, run_pure] at hr
      exact wb_initLoop hPP hR t (h + 1) s1 S1 hW1 (by omega) (by omega) s' hr
    · have e : h = P.H + 1 := by omega
      subst e
      obtain ⟨s1, hr1, -, -⟩ := stage_last S hR.H1
      have hW1 := initStep_wb S hW hR h1 hH hr1
      rw [hr1] at hr
      simp only [ite_true, run_pure] at hr
      obtain ⟨-, rfl⟩ := EStateM.Result.ok.inj hr; exact hW1

/-- **A fresh core keeps the stored-value bound** (`initCore`, eager or lazy), from bounded
parameters and room for labels, tags and heights. -/
theorem initCore_wb {lazy : Bool} {s s' : Core} (hP : ParamsB K s.P) (hL : LabRoom K s.P)
    (hR : PrepRoom K s.P) (hPP : topPP s.P) (hr : (initCore lazy).run s = .ok () s') : WB K s' := by
  cases lazy with
  | true =>
    rw [initCore_lazy_run] at hr
    obtain ⟨-, rfl⟩ := EStateM.Result.ok.inj hr
    exact wb_prepStart hP hL false
  | false =>
    rw [initCore_eager_eq, run_bind] at hr
    rcases hl : (forIn (List.range (s.P.H + 1)) PUnit.unit fun (_ : Nat) (_ : PUnit) => do
        let b ← initStep
        if b = true then pure (ForInStep.done PUnit.unit) else pure (ForInStep.yield PUnit.unit) :
        CM PUnit).run { initState s.P with
          prep := some { chunk := 1, below := 1, path := Array.replicate (s.P.H + 1) NIL }, ready := true }
        with ⟨u, s1⟩ | ⟨e, s1⟩
    · rw [hl] at hr
      simp only [run_modify] at hr
      obtain ⟨-, rfl⟩ := EStateM.Result.ok.inj hr
      exact (wb_initLoop hPP hR _ 1 _ (stage_one s true) (wb_prepStart hP hL true) le_rfl (by omega) s1 hl).withReady
    · rw [hl] at hr; simp at hr

/-- **A fresh core**, as the wrapper makes it (`newCore`). -/
theorem newCore_wb {P : Params} {lazy : Bool} {c : Core} (hP : ParamsB K P) (hL : LabRoom K P)
    (hR : PrepRoom K P) (hPP : topPP P) (hc : newCore P lazy = .ok c) : WB K c := by
  unfold newCore runCore at hc
  rcases hr : (initCore lazy).run { P := P } with ⟨u, s'⟩ | ⟨e, s'⟩
  · rw [hr] at hc
    cases hc
    exact initCore_wb (s := { P := P }) hP hL hR hPP hr
  · rw [hr] at hc; cases hc

/-- **A preparation step keeps the stored-value bound**, on a core whose chain is being built
(`topPI`) or that is ready. -/
theorem prepareStep_wb {s : Core} (hI : s.ready = true ∨ topPI s) (hW : WB K s) (hR : PrepRoom K s.P)
    {b : Bool} {s' : Core} (hr : prepareStep.run s = .ok b s') : WB K s' := by
  rcases hI with hrd | ⟨-, hrd, h, h1, hH, S⟩
  · unfold prepareStep at hr
    simp only [run_get_bind, hrd, Bool.not_true, Bool.false_eq_true, ite_false, run_pure] at hr
    obtain ⟨-, rfl⟩ := EStateM.Result.ok.inj hr; exact hW
  · have key : ∀ c s1, initStep.run s = .ok c s1 → prepareStep.run s =
        .ok (if c then true else s1.ready) (if c then { s1 with ready := true } else s1) := by
      intro c s1 hi
      unfold prepareStep
      simp only [run_get_bind, hrd, Bool.not_false, ite_true]
      rw [run_bind, hi]
      cases c <;> rfl
    rcases hi : initStep.run s with ⟨c, s1⟩ | ⟨e, s1⟩
    · rw [key c s1 hi] at hr
      obtain ⟨-, rfl⟩ := EStateM.Result.ok.inj hr
      have hW1 := initStep_wb S hW (by rw [← S.P]; exact hR) h1 (by rw [← S.P]; exact hH) hi
      cases c
      · exact hW1
      · exact hW1.withReady
    · exfalso
      unfold prepareStep at hr
      simp only [run_get_bind, hrd, Bool.not_false, ite_true] at hr
      rw [run_bind, hi] at hr
      cases hr

end OrderMaintenance.Proof.Word
