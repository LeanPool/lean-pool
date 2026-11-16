/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.ListErase
public import LeanPool.OrderMaintenance.Impl.StartDrain
public import LeanPool.OrderMaintenance.Proof.Top.RunFinish


/-!
# M6: the end of a drain (`finishDrain`) at Level M

Ghost `v` leaves the tables of its entries (`dropTable`), the tables holding it lose its entry
(`dropEntry`, with `assocErase`), its targets are released and it dies. The state reached is Level
F's `fdS v s` (`finishDrain_run`).
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Proof.Top
open OrderMaintenance.Machine (Reg BinOp UnOp)

local notation "upd" => Machine.State.upd

/-! ### `dropTable` -/

/-- Remove `v` from list `k` of record `e`, if there (locals `e v`). -/
def dropS (k : LK) : Stm := cm{
  r ← ‹findP k›(e, v); n := len k[e]
  if r < n then call ‹eraseIdxP k›(e, r) }

theorem dropS_ok {κ : Caps} {k : LK} {s : Core} {L : Loc} {e v : Nat} (he : L "e" = e) (hv : L
  "v" = v)
    (her : e < κ.lrec k) (hcap : (k.view s e).length ≤ κ.lcap k)
    (hok : (k.view s e).findIdx (·.1 == v) < (k.view s e).length → k.idOk s e ∧ k.recOk s e =
      true) :
    ∃ L' c, evalF κ (dropS k) s L =
      .ok (if (k.view s e).findIdx (·.1 == v) < (k.view s e).length then
        k.put s e ((k.view s e).eraseIdx ((k.view s e).findIdx (·.1 == v))) else s) L' c ∧
      c ≤ 150 + 100 * (k.view s e).length ∧ ∀ r, r ≠ "r" → r ≠ "n" → L' r = L r := by
  set l := k.view s e
  set r := l.findIdx (·.1 == v)
  obtain ⟨Lf, cf, ef, hrf, hcf⟩ := findP_agree κ k s
    (Machine.State.setLocs (fun _ => 0) ["i", "x"] [e, v]) (i := e) (x := v)
    (by simp [Machine.State.setLocs, Machine.State.upd])
    (by simp [Machine.State.setLocs, Machine.State.upd]) her
  replace hcf : cf ≤ 20 + 20 * l.length := hcf
  have e1 := evalF_call_ok (q := findP k) (args := [.var "e", .var "v"]) (ds := ["r"]) (L := L)
    (by simp [evList, Exp.ev, he, hv]) ef
  set L1 := Machine.State.setLocs L ["r"] ((findP k).rets.map Lf)
  have hL1 : ∀ q, q ≠ "r" → L1 q = L q := fun q h => by
    simp [L1, findP, Machine.State.setLocs, Machine.State.upd, h]
  have h1r : L1 "r" = r := by simp [L1, Machine.State.setLocs, Machine.State.upd, findP, hrf]; rfl
  have a2 := evalF_assign_ok (κ := κ) (s := s) (L := L1) (x := "n") (e := .llen k "e") (v :=
    l.length)
    (by simp [Exp.ev, hL1 "e" (by decide), he, her, l])
  set L2 := upd L1 "n" l.length
  have h2 : ∀ q, q ≠ "r" → q ≠ "n" → L2 q = L q := fun q h1 h2 => by
    simp only [L2, Machine.State.upd, ite_eq_right h2]; exact hL1 q h1
  by_cases hf : r < l.length
  · obtain ⟨hid, hr⟩ := hok hf
    obtain ⟨Le, ce, ee, hce⟩ := eraseIdxP_agree κ k s (Machine.State.setLocs (fun _ => 0) ["i",
      "p"] [e, r])
      (i := e) (p := r) (by simp [Machine.State.setLocs, Machine.State.upd])
      (by simp [Machine.State.setLocs,
        Machine.State.upd]) hf hid hr her hcap
    replace hce : ce ≤ 100 + 70 * l.length := hce
    have e3 := evalF_call_ok (q := eraseIdxP k) (args := [.var "e", .var "r"]) (ds := []) (L := L2)
      (by simp [evList, Exp.ev, L2, Machine.State.upd, hL1 "e" (by decide), he,
        h1r]) ee
    rw [ite_eq_left hf]
    refine ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 a2 (evalF_ite_t (v := 1)
      (by simp [Exp.ev, Machine.BinOp.eval, L2,
        Machine.State.upd, h1r, hf]) one_ne_zero e3)), ?_, ?_⟩
    · simp only [Exp.cost, costList, List.map, List.sum_cons, List.sum_nil, List.length_nil,
      List.length_cons] at hcf hce ⊢
      omega
    · intro q h1 h2'; simp only [Machine.State.setLocs, ]; exact h2 q h1 h2'
  · rw [ite_eq_right hf]
    refine ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 a2 (evalF_ite_f
      (by simp [Exp.ev, Machine.BinOp.eval, L2,
        Machine.State.upd, h1r, hf]) evalF_skip)), ?_, h2⟩
    · simp only [Exp.cost, costList, List.map, List.sum_cons, List.sum_nil, List.length_nil,
      List.length_cons] at hcf ⊢
      omega

theorem erase_eq_eraseIdx' (l : List Nat) (a : Nat) : l.erase a = l.eraseIdx (l.findIdx (· == a)) :=
  List.erase_eq_eraseIdx_of_idxOf rfl

theorem findIdx_lt_iff_contains (l : List Nat) (a : Nat) : l.findIdx (· == a) < l.length ↔
  l.contains a = true := by
  rw [List.findIdx_lt_length]; simp

theorem getX_nonempty {α : Type} {a : Array (List α)} {i : Nat} (h : a.getX i ≠ [])
    (hd : (default : List α) = []) : i < a.size := by
  by_contra hc; apply h; unfold Array.getX Array.getD; rw [dite_eq_right hc]; exact hd

/-- `dropS .cin` is `dropTableS` at height 0. -/
theorem dropS_cin_eq (s : Core) (v e : Nat) :
    (if (LK.view s e .cin).findIdx (·.1 == v) < (LK.view s e .cin).length then
      LK.put s e ((LK.view s e .cin).eraseIdx ((LK.view s e .cin).findIdx (·.1 == v))) .cin else
        s) =
    dropTableS v 0 s e := by
  simp only [LK.view, findIdx_pair0', List.length_map, findIdx_lt_iff_contains, dropTableS,
    beq_self_eq_true,
    ite_true]
  split
  · simp only [LK.put, ← List.eraseIdx_map, List.map_map, Function.comp_def, List.map_id',
    erase_eq_eraseIdx']
  · rfl

/-- `dropS .inTab` is `dropTableS` above height 0. -/
theorem dropS_inTab_eq (s : Core) (v e hh : Nat) (hh0 : hh ≠ 0) :
    (if (LK.view s e .inTab).findIdx (·.1 == v) < (LK.view s e .inTab).length then
      LK.put s e ((LK.view s e .inTab).eraseIdx ((LK.view s e .inTab).findIdx (·.1 == v)))
        .inTab else s) =
    dropTableS v hh s e := by
  simp only [LK.view, findIdx_pair0', List.length_map, findIdx_lt_iff_contains, dropTableS,
    show (hh == 0) = false by simpa using hh0, Bool.false_eq_true, ite_false]
  split
  · simp only [LK.put, ← List.eraseIdx_map, List.map_map, Function.comp_def, List.map_id',
    erase_eq_eraseIdx']
  · rfl

/-- Remove one drained-table membership from the entry's containing-table list. -/
def dtBody : Stm := cm{ e := table[v][j].fst; if hh = 0 then ‹dropS .cin› else ‹dropS .inTab› }

theorem dropTableS_cin_len (v hh : Nat) (s : Core) (e e' : Nat) :
    ((dropTableS v hh s e').cin.getX e).length ≤ (s.cin.getX e).length := by
  unfold dropTableS
  split_ifs
  · simp only [getX_setX']; split
    · next h => subst h; exact List.length_erase_le
    · exact le_refl _
  all_goals exact le_refl _

theorem dropTableS_inTab_len (v hh : Nat) (s : Core) (e e' : Nat) :
    ((dropTableS v hh s e').nodes.getX e).inTables.length ≤ (s.nodes.getX e).inTables.length := by
  rw [dropTableS_getX]; split
  · simp [List.length_erase]; split <;> omega
  · exact le_refl _

theorem dropTableS_nodes_size (v hh : Nat) (s : Core) (e : Nat) :
    (dropTableS v hh s e).nodes.size = s.nodes.size := by
  unfold dropTableS; split_ifs <;> simp

theorem foldl_dropTableS_len (v hh : Nat) (e : Nat) : ∀ (l : List Nat) (s : Core),
    ((l.foldl (dropTableS v hh) s).cin.getX e).length ≤ (s.cin.getX e).length ∧
    ((l.foldl (dropTableS v hh) s).nodes.getX e).inTables.length ≤ (s.nodes.getX
      e).inTables.length ∧
    (l.foldl (dropTableS v hh) s).nodes.size = s.nodes.size
  | [], _ => ⟨le_refl _, le_refl _, rfl⟩
  | x :: t, s => by
    simp only [List.foldl_cons]
    obtain ⟨h1, h2, h3⟩ := foldl_dropTableS_len v hh e t (dropTableS v hh s x)
    exact ⟨h1.trans (dropTableS_cin_len v hh s e x), h2.trans (dropTableS_inTab_len v hh s e x),
      h3.trans (dropTableS_nodes_size v hh s x)⟩

theorem dtBody_ok {κ : Caps} {X : Core} {L : Loc} {v hh e j B : Nat} (hv : L "v" = v) (hhh : L
  "hh" = hh)
    (hj : j < (X.nodes.getX v).table.length) (he : ((X.nodes.getX v).table.getD j (0, 0)).1 = e)
    (hvr : v < κ.lrec .table)
    (hcin : hh = 0 → e < κ.lrec .cin ∧ (X.cin.getX e).length ≤ κ.lcap .cin ∧ (X.cin.getX
      e).length ≤ B)
    (hin : hh ≠ 0 → e < κ.lrec .inTab ∧ (X.nodes.getX e).inTables.length ≤ κ.lcap .inTab ∧
      (X.nodes.getX e).inTables.length ≤ B) :
    ∃ L' c, evalF κ dtBody X (upd L "j" j) = .ok (dropTableS v hh X e) L' c ∧ c ≤ 170 + 100 * B ∧
      ∀ r, r ≠ "j" → r ≠ "e" → r ≠ "r" → r ≠ "n" → L' r = L r := by
  have a1 := evalF_assign_ok (κ := κ) (s := X) (L := upd L "j" j) (x := "e") (e := .lrd .table
    false "v" "j") (v := e)
    (by simp [Exp.ev, Machine.State.upd, hv, hvr, LK.view, hj, ← he])
  set L1 := upd (upd L "j" j) "e" e
  have h1e : L1 "e" = e := by simp [L1, Machine.State.upd]
  have h1v : L1 "v" = v := by simp [L1, Machine.State.upd, hv]
  have h1F : ∀ r, r ≠ "j" → r ≠ "e" → L1 r = L r := fun r a b => by simp [L1, Machine.State.upd,
    a, b]
  by_cases hh0 : hh = 0
  · obtain ⟨hec, hcc, hBc⟩ := hcin hh0
    obtain ⟨L2, c2, e2, hc2, hF2⟩ := dropS_ok (κ := κ) (k := .cin) (s := X) (L := L1) (e := e)
      (v := v) h1e h1v hec
      (by simpa [LK.view] using hcc)
      (fun hf => by
        refine ⟨?_, rfl⟩
        simp only [LK.idOk]
        apply getX_nonempty (hd := rfl)
        intro h0; simp [LK.view, h0] at hf)
    rw [dropS_cin_eq] at e2
    rw [hh0]
    refine ⟨L2, _, evalF_seq_ok2 a1 (evalF_ite_t (v := 1)
      (by simp [Exp.ev, Machine.BinOp.eval, L1,
        Machine.State.upd, hhh, hh0]) one_ne_zero e2), ?_,
      fun r a b c d => (hF2 r c d).trans (h1F r a b)⟩
    simp only [LK.view, List.length_map] at hc2; simp only [Exp.cost]; nlinarith
  · obtain ⟨hei, hci, hBi⟩ := hin hh0
    obtain ⟨L2, c2, e2, hc2, hF2⟩ := dropS_ok (κ := κ) (k := .inTab) (s := X) (L := L1) (e := e)
      (v := v) h1e h1v hei
      (by simpa [LK.view] using hci)
      (fun hf => by
        have hlt : e < X.nodes.size := by
          by_contra hc
          have : X.nodes.getX e = default := getX_size_le (by omega)
          simp only [LK.view, this, List.findIdx_map, List.length_map, List.findIdx_lt_length,
              Function.comp_apply, beq_iff_eq, exists_eq_right] at hf
          exact absurd hf (by simp [show (default : Node).inTables = [] from rfl])
        exact ⟨by simp [LK.idOk, LK.recOk, hlt], by simp [LK.recOk, hlt]⟩)
    rw [dropS_inTab_eq X v e hh hh0] at e2
    refine ⟨L2, _, evalF_seq_ok2 a1 (evalF_ite_f
      (by simp [Exp.ev, Machine.BinOp.eval, L1,
        Machine.State.upd, hhh, hh0]) e2), ?_,
      fun r a b c d => (hF2 r c d).trans (h1F r a b)⟩
    simp only [LK.view, List.length_map] at hc2; simp only [Exp.cost]; nlinarith

/-- Remove the drained table from every entry that it contains. -/
def dtLoopS : Stm := cm{ m := len table[v]; for j < m do dtBody }

theorem dtLoopS_ok {κ : Caps} {s : Core} {L : Loc} {v hh B : Nat} (hv : L "v" = v) (hhh : L "hh"
  = hh)
    (hvr : v < κ.lrec .table)
    (hcap : ∀ e ∈ (s.nodes.getX v).order,
      (hh = 0 → e < κ.lrec .cin ∧ (s.cin.getX e).length ≤ κ.lcap .cin ∧ (s.cin.getX e).length ≤ B) ∧
      (hh ≠ 0 → e < κ.lrec .inTab ∧ (s.nodes.getX e).inTables.length ≤ κ.lcap .inTab ∧
        (s.nodes.getX e).inTables.length ≤ B)) :
    ∃ L' c, evalF κ dtLoopS s L = .ok ((s.nodes.getX v).order.foldl (dropTableS v hh) s) L' c ∧
      c ≤ 5 + (s.nodes.getX v).table.length * (171 + 100 * B) ∧
      ∀ r, r ≠ "m" → r ≠ "j" → r ≠ "e" → r ≠ "r" → r ≠ "n" → L' r = L r := by
  set tab := (s.nodes.getX v).table
  set ord := (s.nodes.getX v).order
  have hord : ord = tab.map (·.1) := rfl
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "m") (e := .llen .table "v") (v :=
    tab.length)
    (by simp [Exp.ev, hv, hvr, LK.view, tab])
  set L1 := upd L "m" tab.length
  obtain ⟨S', L', c, he, hc, hS', hF⟩ := evalF_loop (κ := κ) (x := "j") (n := .var "m") (b :=
    dtBody)
    (s := s) (L := L1) (N := tab.length) (by simp [Exp.ev, L1, Machine.State.upd])
    (fun j S L' => S = (ord.take j).foldl (dropTableS v hh) s ∧
      ∀ r, r ≠ "m" → r ≠ "j" → r ≠ "e" → r ≠ "r" → r ≠ "n" → L' r = L r) (170 + 100 * B)
    ⟨by simp, fun r h1 _ _ _ _ => by simp [L1, Machine.State.upd, h1]⟩
    (by
      intro j hj S L2 ⟨hS, hF2⟩
      subst hS
      set X := (ord.take j).foldl (dropTableS v hh) s
      have hjo : j < ord.length := by simp only [hord, List.length_map]; exact hj
      have hXt : (X.nodes.getX v).table = tab := foldl_dropTableS_table v hh _ s v
      have hem : ord[j] ∈ ord := List.getElem_mem hjo
      obtain ⟨hc1, hc2⟩ := hcap _ hem
      obtain ⟨g1, g2, -⟩ := foldl_dropTableS_len v hh ord[j] (ord.take j) s
      replace g1 : (X.cin.getX ord[j]).length ≤ (s.cin.getX ord[j]).length := g1
      replace g2 : (X.nodes.getX ord[j]).inTables.length ≤ (s.nodes.getX ord[j]).inTables.length
        := g2
      obtain ⟨L3, c3, e3, hc3, hF3⟩ := dtBody_ok (κ := κ) (X := X) (L := L2) (v := v) (hh := hh)
        (e := ord[j]) (j := j)
        (B := B) (by rw [hF2 "v" (by decide) (by decide) (by decide) (by decide) (by decide), hv])
        (by rw [hF2 "hh" (by decide) (by decide) (by decide) (by decide) (by decide),
          hhh]) (by rw [hXt]; exact hj)
        (by rw [hXt, List.getD_eq_getElem _ _ hj]; simp [hord]) hvr
        (fun h0 => by obtain ⟨a, b, c⟩ := hc1 h0; exact ⟨a, by omega, by omega⟩)
        (fun h0 => by obtain ⟨a, b, c⟩ := hc2 h0; exact ⟨a, by omega, by omega⟩)
      refine ⟨_, L3, c3, e3, hc3, ?_, fun r a b c d e => (hF3 r b c d e).trans (hF2 r a b c d e)⟩
      simp only [X, List.take_succ_eq_append_getElem hjo, List.foldl_append, List.foldl_cons,
        List.foldl_nil])
  rw [hS', show tab.length = ord.length by simp [hord], List.take_length] at he
  refine ⟨L', _, evalF_seq_ok2 a1 he, ?_, hF⟩
  have e : tab.length * (1 + (170 + 100 * B)) = tab.length * (171 + 100 * B) := by ring
  simp only [Exp.cost] at hc ⊢; omega

/-! ### `dropEntry` -/

/-- Remove the drained node from one enclosing table and its side map. -/
def deBody : Stm := cm{
  T := inTab[v][j].fst
  r ← ‹findP .table›(T, v); n := len table[T]; if r < n then skip else fail
  call ‹filterP .table›(T, v); call ‹filterP .side›(T, v) }

theorem encS_filter (l : List (Nat × Side)) (v : Nat) :
    (encS l).filter (·.1 != v) = encS (assocErase l v) := by
  simp [encS, assocErase, List.filter_map, Function.comp_def]

theorem deStep_eq (S : Core) (v T : Nat) :
    LK.put (LK.put S T ((S.nodes.getX T).table.filter (·.1 != v)) .table) T
      (encS (assocErase (S.nodes.getX T).side v)) .side = dropEntryS v S T := by
  rw [put_side_encS]
  simp only [LK.put, dropEntryS, Array.modify_modify_same]
  congr 1; apply Array.modify_congr_getX; simp [assocErase]

theorem deBody_ok {κ : Caps} {S : Core} {L : Loc} {v T j B : Nat} (hv : L "v" = v)
    (hj : j < (S.nodes.getX v).inTables.length) (hTj : (S.nodes.getX v).inTables[j] = T)
    (hvi : v < κ.lrec .inTab) (hmem : v ∈ (S.nodes.getX T).order)
    (htr : T < κ.lrec .table) (hts : T < κ.lrec .side)
    (hct : (S.nodes.getX T).table.length ≤ κ.lcap .table) (hcs : (S.nodes.getX T).side.length ≤
      κ.lcap .side)
    (hBt : (S.nodes.getX T).table.length ≤ B) (hBs : (S.nodes.getX T).side.length ≤ B) :
    ∃ L' c, evalF κ deBody S (upd L "j" j) = .ok (dropEntryS v S T) L' c ∧ c ≤ 300 + 200 * B ∧
      ∀ r, r ≠ "j" → r ≠ "T" → r ≠ "r" → r ≠ "n" → L' r = L r := by
  have hTn : T < S.nodes.size := by
    by_contra hc
    have : S.nodes.getX T = default := getX_size_le (by omega)
    rw [this] at hmem; exact absurd hmem (by simp [Node.order, show (default : Node).table = []
      from rfl])
  have a1 := evalF_assign_ok (κ := κ) (s := S) (L := upd L "j" j) (x := "T") (e := .lrd .inTab
    false "v" "j") (v := T)
    (by simp [Exp.ev, Machine.State.upd, hv, hvi, LK.view, hj, hTj])
  set L1 := upd (upd L "j" j) "T" T
  have h1T : L1 "T" = T := by simp [L1, Machine.State.upd]
  have h1v : L1 "v" = v := by simp [L1, Machine.State.upd, hv]
  -- the guard
  obtain ⟨Lf, cf, ef, hrf, hcf⟩ := findP_agree κ .table S
    (Machine.State.setLocs (fun _ => 0) ["i", "x"] [T, v]) (i := T) (x := v)
    (by simp [Machine.State.setLocs, Machine.State.upd])
    (by simp [Machine.State.setLocs, Machine.State.upd]) htr
  have e2 := evalF_call_ok (q := findP .table) (args := [.var "T", .var "v"]) (ds := ["r"]) (L
    := L1)
    (by simp [evList, Exp.ev, h1T, h1v]) ef
  set L2 := Machine.State.setLocs L1 ["r"] ((findP .table).rets.map Lf)
  have hL2 : ∀ q, q ≠ "r" → L2 q = L1 q := fun q h => by
    simp [L2, findP, Machine.State.setLocs, Machine.State.upd, h]
  have h2r : L2 "r" = (S.nodes.getX T).table.findIdx (·.1 == v) := by
    simp [L2, Machine.State.setLocs, Machine.State.upd, findP,
      hrf]; rfl
  have hfl : (S.nodes.getX T).table.findIdx (·.1 == v) < (S.nodes.getX T).table.length := by
    rw [List.findIdx_lt_length]
    simp only [Node.order, List.mem_map] at hmem
    obtain ⟨q, hq, rfl⟩ := hmem; exact ⟨q, hq, by simp⟩
  have a3 := evalF_assign_ok (κ := κ) (s := S) (L := L2) (x := "n") (e := .llen .table "T")
    (v := (S.nodes.getX T).table.length) (by simp [Exp.ev, hL2 "T" (by decide), h1T, htr, LK.view])
  set L3 := upd L2 "n" (S.nodes.getX T).table.length
  have e4 : evalF κ (.ite ("r" <ₑ "n") .skip .fail) S L3 = .ok S L3 5 := by
    simp [evalF, Exp.ev, L3, Machine.State.upd, h2r,
      Machine.BinOp.eval, hfl, Exp.cost, Res.addCost]
  have h3T : L3 "T" = T := by simp [L3, Machine.State.upd, hL2, h1T]
  have h3v : L3 "v" = v := by simp [L3, Machine.State.upd, hL2, h1v]
  have hF3 : ∀ r, r ≠ "j" → r ≠ "T" → r ≠ "r" → r ≠ "n" → L3 r = L r := fun r a b c d => by
    simp [L3, Machine.State.upd, d, hL2 r c, L1, a, b]
  -- the table
  obtain ⟨Lt, ct, et, hct'⟩ := filterP_agree κ .table S (Machine.State.setLocs (fun _ => 0)
    ["i", "x"] [T, v])
    (i := T) (x := v) (by simp [Machine.State.setLocs, Machine.State.upd])
    (by simp [Machine.State.setLocs,
      Machine.State.upd]) (by simp [LK.idOk, LK.recOk, hTn])
    (by simp [LK.recOk, hTn]) htr (by simpa [LK.view] using hct)
  have e5 := evalF_call_ok (q := filterP .table) (args := [.var "T", .var "v"]) (ds := []) (L := L3)
    (by simp [evList, Exp.ev, h3T, h3v]) et
  set S1 := LK.put S T ((S.nodes.getX T).table.filter (·.1 != v)) .table
  have hS1T : (S1.nodes.getX T).side = (S.nodes.getX T).side := by
    simp only [S1, LK.put, getX_modify', hTn, and_self, ite_true]
  have hS1n : S1.nodes.size = S.nodes.size := by simp [S1]
  -- the side list
  obtain ⟨Ls, cs, es, hcs'⟩ := filterP_agree κ .side S1 (Machine.State.setLocs (fun _ => 0)
    ["i", "x"] [T, v])
    (i := T) (x := v) (by simp [Machine.State.setLocs, Machine.State.upd])
    (by simp [Machine.State.setLocs,
      Machine.State.upd]) (by simp [LK.idOk, LK.recOk, hS1n, hTn])
    (by simp [LK.recOk, hS1n, hTn]) hts (by simp only [LK.view, hS1T, List.length_map]; exact hcs)
  have hvs : LK.view S1 T .side = encS (S.nodes.getX T).side := by simp [LK.view, hS1T]
  rw [hvs, encS_filter] at es
  rw [hvs] at hcs'
  have e6 := evalF_call_ok (q := filterP .side) (args := [.var "T", .var "v"]) (ds := []) (L :=
    Machine.State.setLocs L3 [] ((filterP .table).rets.map Lt))
    (by simp [evList, Exp.ev, Machine.State.setLocs, h3T, h3v]) es
  rw [deStep_eq S v T] at e6
  refine ⟨_, _, evalF_seq_ok2 a1 (evalF_seq_ok2 e2 (evalF_seq_ok2 a3 (evalF_seq_ok2 e4
    (evalF_seq_ok2 e5 e6)))),
    ?_, ?_⟩
  · replace hcf : cf ≤ 20 + 20 * (S.nodes.getX T).table.length := hcf
    replace hct' : ct ≤ 50 + 90 * (S.nodes.getX T).table.length := hct'
    replace hcs' : cs ≤ 50 + 90 * (S.nodes.getX T).side.length := by simpa [encS] using hcs'
    simp only [Exp.cost, costList, List.map, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    omega
  · intro r a b c d
    simp only [Machine.State.setLocs, ]; exact hF3 r a b c d

/-! ### Frames -/

/-- `dropTableS` changes in-table lists only. -/
theorem dropTableS_node (v hh : Nat) (s : Core) (e u : Nat) :
    ∃ l, (dropTableS v hh s e).nodes.getX u = {
      s.nodes.getX u with
      inTables := l
    } := by
  rw [dropTableS_getX]; split
  · exact ⟨_, rfl⟩
  · exact ⟨(s.nodes.getX u).inTables, rfl⟩

theorem foldl_dropTableS_node (v hh u : Nat) : ∀ (l : List Nat) (s : Core),
    ∃ m, (l.foldl (dropTableS v hh) s).nodes.getX u = {
      s.nodes.getX u with
      inTables := m
    }
  | [], s => ⟨(s.nodes.getX u).inTables, rfl⟩
  | e :: t, s => by
    simp only [List.foldl_cons]
    obtain ⟨m, hm⟩ := foldl_dropTableS_node v hh u t (dropTableS v hh s e)
    obtain ⟨m', hm'⟩ := dropTableS_node v hh s e u
    exact ⟨m, by rw [hm, hm']⟩

theorem foldl_dropTableS_v {v hh : Nat} {s : Core} {l : List Nat} (hv : hh ≠ 0 → v ∉ l) :
    (l.foldl (dropTableS v hh) s).nodes.getX v = s.nodes.getX v := by
  induction l generalizing s with
  | nil => rfl
  | cons e t ih =>
    simp only [List.foldl_cons]
    rw [ih (fun h0 h => hv h0 (List.mem_cons_of_mem _ h)), dropTableS_getX, ite_eq_right]
    intro h; exact hv h.2.1 (by rw [h.1]; exact List.mem_cons_self)

/-- `dropEntryS` changes tables and side lists only. -/
theorem foldl_dropEntryS_node (v u : Nat) : ∀ (l : List Nat) (s : Core),
    ∃ t sd, (l.foldl (dropEntryS v) s).nodes.getX u = {
      s.nodes.getX u with
      table := t
      side := sd
    }
  | [], s => ⟨(s.nodes.getX u).table, (s.nodes.getX u).side, rfl⟩
  | T :: r, s => by
    simp only [List.foldl_cons]
    obtain ⟨t, sd, h⟩ := foldl_dropEntryS_node v u r (dropEntryS v s T)
    rw [h]; unfold dropEntryS; simp only [getX_modify']
    split
    · exact ⟨_, _, rfl⟩
    · exact ⟨_, _, rfl⟩

theorem foldl_dropEntryS_notin {v u : Nat} {s : Core} {l : List Nat} (hu : u ∉ l) :
    (l.foldl (dropEntryS v) s).nodes.getX u = s.nodes.getX u := by
  induction l generalizing s with
  | nil => rfl
  | cons T t ih =>
    simp only [List.foldl_cons]
    rw [ih (fun h => hu (List.mem_cons_of_mem _ h)),
      dropEntryS_other v s T u (fun h => hu (h ▸ List.mem_cons_self))]

theorem foldl_dropEntryS_size (v : Nat) : ∀ (l : List Nat) (s : Core), (l.foldl (dropEntryS v)
  s).nodes.size = s.nodes.size
  | [], _ => rfl
  | T :: r, s => by simp only [List.foldl_cons]; rw [foldl_dropEntryS_size v r]; simp [dropEntryS]

/-! ### The `dropEntry` loop -/

/-- Remove the drained node from all of its enclosing tables. -/
def deLoopS : Stm := cm{ m := len inTab[v]; for j < m do deBody }

theorem deLoopS_ok {κ : Caps} {X : Core} {L : Loc} {v B : Nat} (hv : L "v" = v) (hvi : v <
  κ.lrec .inTab)
    (hnd : (X.nodes.getX v).inTables.Nodup) (hT : ∀ T ∈ (X.nodes.getX v).inTables, v ∈
      (X.nodes.getX T).order)
    (hcap : ∀ T ∈ (X.nodes.getX v).inTables, T < κ.lrec .table ∧ T < κ.lrec .side ∧
      (X.nodes.getX T).table.length ≤ κ.lcap .table ∧ (X.nodes.getX T).side.length ≤ κ.lcap .side ∧
      (X.nodes.getX T).table.length ≤ B ∧ (X.nodes.getX T).side.length ≤ B) :
    ∃ L' c, evalF κ deLoopS X L = .ok ((X.nodes.getX v).inTables.foldl (dropEntryS v) X) L' c ∧
      c ≤ 5 + (X.nodes.getX v).inTables.length * (301 + 200 * B) ∧
      ∀ r, r ≠ "m" → r ≠ "j" → r ≠ "T" → r ≠ "r" → r ≠ "n" → L' r = L r := by
  set tabs := (X.nodes.getX v).inTables
  have a1 := evalF_assign_ok (κ := κ) (s := X) (L := L) (x := "m") (e := .llen .inTab "v") (v :=
    tabs.length)
    (by simp [Exp.ev, hv, hvi, LK.view, tabs])
  set L1 := upd L "m" tabs.length
  obtain ⟨S', L', c, he, hc, hS', hF⟩ := evalF_loop (κ := κ) (x := "j") (n := .var "m") (b :=
    deBody)
    (s := X) (L := L1) (N := tabs.length) (by simp [Exp.ev, L1, Machine.State.upd])
    (fun j S L' => S = (tabs.take j).foldl (dropEntryS v) X ∧
      ∀ r, r ≠ "m" → r ≠ "j" → r ≠ "T" → r ≠ "r" → r ≠ "n" → L' r = L r) (300 + 200 * B)
    ⟨by simp, fun r h1 _ _ _ _ => by simp [L1, Machine.State.upd, h1]⟩
    (by
      intro j hj S L2 ⟨hS, hF2⟩
      subst hS
      set S := (tabs.take j).foldl (dropEntryS v) X
      have hTm : tabs[j] ∈ tabs := List.getElem_mem hj
      have hTn : tabs[j] ∉ tabs.take j := nodup_getElem_notin_take hnd hj
      have hST : S.nodes.getX tabs[j] = X.nodes.getX tabs[j] := foldl_dropEntryS_notin hTn
      have hSv : (S.nodes.getX v).inTables = tabs := by
        obtain ⟨t, sd, h⟩ := foldl_dropEntryS_node v v (tabs.take j) X
        simp only [S, h]; rfl
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hcap _ hTm
      obtain ⟨L3, c3, e3, hc3, hF3⟩ := deBody_ok (κ := κ) (S := S) (L := L2) (v := v) (T :=
        tabs[j]) (j := j)
        (B := B) (by rw [hF2 "v" (by decide) (by decide) (by decide) (by decide) (by decide), hv])
        (by rw [hSv]; exact hj) (by simp only [hSv]) hvi (by rw [hST]; exact hT _ hTm) h1 h2
        (by rw [hST]; exact h3) (by rw [hST]; exact h4) (by rw [hST]; exact h5) (by
          rw [hST]
          exact h6)
      refine ⟨_, L3, c3, e3, hc3, ?_, fun r a b c d e => (hF3 r b c d e).trans (hF2 r a b c d e)⟩
      simp only [S, List.take_succ_eq_append_getElem hj, List.foldl_append, List.foldl_cons,
        List.foldl_nil])
  rw [hS', List.take_length] at he
  refine ⟨L', _, evalF_seq_ok2 a1 he, ?_, hF⟩
  have e : tabs.length * (1 + (300 + 200 * B)) = tabs.length * (301 + 200 * B) := by ring
  simp only [Exp.cost] at hc ⊢; omega

/-! ### `finishDrain` -/

/-- `release v (field f of v)` (locals `v`). -/
def relS (f : NF) : Stm := cm{ tt := N[v].‹f›; if N[tt].overflow = v then N[tt].overflow := 0 }

theorem relS_ok {κ : Caps} {S : Core} {L : Loc} {v t : Nat} {f : NF} (hv : L "v" = v) (hf :
  NF.get (S.nodes.getX v) f = t)
    (hv0 : v ≠ 0) (hvN : v < κ.tbl .N) (htN : t < κ.tbl .N) :
    ∃ c, evalF κ (relS f) S L = .ok (releaseS v S t) (upd L "tt" t) c ∧ c ≤ 20 := by
  have a1 := evalF_assign_ok (κ := κ) (s := S) (L := L) (x := "tt") (e := .rd (.n f) "v") (v := t)
    (by simp [Exp.ev, hv, hvN, Fld.cap, Fld.get, hf])
  set L1 := upd L "tt" t
  by_cases ho : (S.nodes.getX t).overflowOf = v
  · have hts : t < S.nodes.size := by
      by_contra hc
      have : S.nodes.getX t = default := getX_size_le (by omega)
      rw [this] at ho; exact hv0 (by rw [← ho]; rfl)
    have w := evalF_wrN_ok (κ := κ) (s := S) (L := L1) (k := .overflow) (i := .var "tt") (e :=
      (0 : Exp)) (j := t)
      (w := 0) (by simp [Exp.ev, L1, Machine.State.upd]) rfl hts  rfl
    have hr : releaseS v S t = {
      S with
      nodes := S.nodes.modify t (NF.set · 0 .overflow)
    } := by
      simp only [releaseS, ho, beq_self_eq_true, ite_true]; rfl
    rw [← hr] at w
    exact ⟨_, evalF_seq_ok2 a1 (evalF_ite_t (v := 1) (by simp [Exp.ev, Machine.BinOp.eval, L1,
      Machine.State.upd,
      hv, htN, Fld.cap, Fld.get, NF.get, ho]) one_ne_zero w), by simp [Exp.cost]⟩
  · have hr : releaseS v S t = S := by simp only [releaseS]; rw [ite_eq_right (by simpa using ho)]
    rw [hr]
    exact ⟨_, evalF_seq_ok2 a1 (evalF_ite_f (by simp [Exp.ev, Machine.BinOp.eval, L1,
      Machine.State.upd,
      hv, htN, Fld.cap, Fld.get, NF.get, ho]) evalF_skip), by simp [Exp.cost]⟩

theorem releaseS_node (v : Nat) (S : Core) (t u : Nat) :
    ∃ o, (releaseS v S t).nodes.getX u = {
      S.nodes.getX u with
      overflowOf := o
    } := by
  unfold releaseS; split
  · simp only [getX_modify']; split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem releaseS_size (v : Nat) (S : Core) (t : Nat) : (releaseS v S t).nodes.size =
  S.nodes.size := by
  unfold releaseS; split <;> simp

/-- Detach a completed drain, release its targets, and mark its source dead. -/
def finishDrainS : Stm := cm{
  hh := h ∸ 1; dtLoopS; deLoopS; ‹relS .t1›; ‹relS .t2›
  N[v].dead := 1; clear inTab[v] }

theorem finishDrainS_ok {κ : Caps} {s : Core} {L : Loc} {v B : Nat} (hv : L "v" = v)
    (hLh : L "h" = (s.nodes.getX v).height)
    -- Level F (as in `finishDrain_run`)
    (hnd : (s.nodes.getX v).inTables.Nodup) (hT : ∀ T ∈ (s.nodes.getX v).inTables, v ∈
      (s.nodes.getX T).order)
    -- the shape
    (hv0 : v ≠ 0) (hvs : v < s.nodes.size) (hvo : (s.nodes.getX v).height - 1 ≠ 0 → v ∉
      (s.nodes.getX v).order)
    -- capacities
    (hvN : v < κ.tbl .N) (hvr : v < κ.lrec .table) (hvi : v < κ.lrec .inTab)
    (ht1 : (s.nodes.getX v).t1 < κ.tbl .N) (ht2 : (s.nodes.getX v).t2 < κ.tbl .N)
    (hcE : ∀ e ∈ (s.nodes.getX v).order,
      ((s.nodes.getX v).height - 1 = 0 → e < κ.lrec .cin ∧ (s.cin.getX e).length ≤ κ.lcap .cin ∧
        (s.cin.getX e).length ≤ B) ∧
      ((s.nodes.getX v).height - 1 ≠ 0 → e < κ.lrec .inTab ∧ (s.nodes.getX e).inTables.length ≤
        κ.lcap .inTab ∧
        (s.nodes.getX e).inTables.length ≤ B))
    (hcT : ∀ T ∈ (s.nodes.getX v).inTables, T < κ.lrec .table ∧ T < κ.lrec .side ∧
      (s.nodes.getX T).table.length ≤ κ.lcap .table ∧ (s.nodes.getX T).side.length ≤ κ.lcap .side ∧
      (s.nodes.getX T).table.length ≤ B ∧ (s.nodes.getX T).side.length ≤ B) :
    ∃ L' c, evalF κ finishDrainS s L = .ok (fdS v s) L' c ∧
      c ≤ 200 + (s.nodes.getX v).table.length * (171 + 100 * B) +
        (s.nodes.getX v).inTables.length * (301 + 200 * B) ∧
      L' "v" = v := by
  set V := s.nodes.getX v
  set hh := V.height - 1
  have a0 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "hh") (e := .monus "h" 1) (v := hh)
    (Exp.ev_monus κ s L (by simp [Exp.ev, hLh, V]) rfl)
  set L0 := upd L "hh" hh
  obtain ⟨L1, c1, e1, hc1, hF1⟩ := dtLoopS_ok (κ := κ) (s := s) (L := L0) (v := v) (hh := hh) (B
    := B)
    (by simp [L0, Machine.State.upd,
      hv]) (by simp [L0, Machine.State.upd]) hvr hcE
  set X0 := V.order.foldl (dropTableS v hh) s
  have hX0v : X0.nodes.getX v = V := foldl_dropTableS_v hvo
  have hX0T : ∀ T, (X0.nodes.getX T).table = (s.nodes.getX T).table ∧
      (X0.nodes.getX T).side = (s.nodes.getX T).side := fun T => by
    obtain ⟨m, hm⟩ := foldl_dropTableS_node v hh T V.order s
    simp [X0, hm]
  have h1v : L1 "v" = v := by
    rw [hF1 "v" (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [L0,
      Machine.State.upd, hv]
  obtain ⟨L2, c2, e2, hc2, hF2⟩ := deLoopS_ok (κ := κ) (X := X0) (L := L1) (v := v) (B := B) h1v hvi
    (by rw [hX0v]; exact hnd)
    (by rw [hX0v]; intro T hTm; simp only [Node.order, (hX0T T).1]; exact hT T hTm)
    (by rw [hX0v]; intro T hTm; simp only [(hX0T T).1, (hX0T T).2]; exact hcT T hTm)
  rw [hX0v] at e2 hc2
  set X2 := V.inTables.foldl (dropEntryS v) X0
  have hX2 : X2 = fd2 v s := rfl
  have hX2v : ∃ t sd, X2.nodes.getX v = {
    V with
    table := t
    side := sd
  } := by
    obtain ⟨t, sd, h⟩ := foldl_dropEntryS_node v v V.inTables X0
    exact ⟨t, sd, by simp only [X2, h, hX0v]⟩
  obtain ⟨tX, sdX, hX2v⟩ := hX2v
  have h2v : L2 "v" = v := by
    rw [hF2 "v" (by decide) (by decide) (by decide) (by decide) (by decide), h1v]
  -- the releases
  obtain ⟨c3, e3, hc3⟩ := relS_ok (κ := κ) (S := X2) (L := L2) (v := v) (t := V.t1) (f := .t1) h2v
    (by simp [NF.get, hX2v]) hv0 hvN ht1
  set X3 := releaseS v X2 V.t1
  have hX3v : (X3.nodes.getX v).t2 = V.t2 := by
    obtain ⟨o, ho⟩ := releaseS_node v X2 V.t1 v
    simp only [X3, ho, hX2v]
  obtain ⟨c4, e4, hc4⟩ := relS_ok (κ := κ) (S := X3) (L := upd L2 "tt" V.t1) (v := v) (t :=
    V.t2) (f := .t2)
    (by simp [Machine.State.upd, h2v]) (by simp [NF.get, hX3v]) hv0 hvN ht2
  set X4 := releaseS v X3 V.t2
  have hX4 : X4 = fd4 v s := rfl
  have hX4n : X4.nodes.size = s.nodes.size := by
    simp only [X4, X3, X2, releaseS_size, foldl_dropEntryS_size, X0]
    exact (foldl_dropTableS_len v hh 0 V.order s).2.2
  -- death
  set L4 := upd (upd L2 "tt" V.t1) "tt" V.t2
  have h4v : L4 "v" = v := by simp [L4, Machine.State.upd, h2v]
  have w5 := evalF_wrN_ok (κ := κ) (s := X4) (L := L4) (k := .dead) (i := .var "v") (e := (1 :
    Exp)) (j := v) (w := 1)
    (by simp [Exp.ev, h4v]) rfl (by rw [hX4n]; exact hvs)  rfl
  set X5 : Core := {
    X4 with
    nodes := X4.nodes.modify v (NF.set · 1 .dead)
  }
  have e6 : evalF κ (.lclear .inTab "v") X5 L4 = .ok (fdS v s) L4 3 := by
    have hso : LK.set κ X5 v [] .inTab = some (LK.put X5 v [] .inTab) := by
      simp [LK.set, LK.recOk, X5, hX4n, hvs, LK.valid, hvi]
    have hfin : LK.put X5 v [] .inTab = fdS v s := by
      simp only [LK.put, X5, fdS, ← hX4, Array.modify_modify_same, List.map_nil]
      congr 1
    simp [evalF, Exp.ev, h4v, hso, hfin, Exp.cost]
  refine ⟨L4, _, evalF_seq_ok2 a0 (evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3
    (evalF_seq_ok2 e4
    (evalF_seq_ok2 w5 e6))))), ?_, h4v⟩
  simp only [Exp.cost, Exp.monus, Exp.max, Exp.sub_def, Exp.add_def, Exp.mul_def,
    Exp.ofNat_def] at hc1 hc2 ⊢
  replace hc1 : c1 ≤ 5 + V.table.length * (171 + 100 * B) := hc1
  omega

end OrderMaintenance.Impl
