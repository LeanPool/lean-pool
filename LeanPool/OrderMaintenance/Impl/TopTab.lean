/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.Side


/-!
# M6: the tables of the top structure (`roomNextTo`, `tableInsert`)
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg BinOp UnOp)

local notation "upd" => Machine.State.upd

theorem findIdx?_some_iff' {l : List (Nat × Nat)} {x i : Nat} :
    l.findIdx? (·.1 == x) = some i ↔ l.findIdx (·.1 == x) = i ∧ i < l.length := by
  rw [List.findIdx?_eq_some_iff_findIdx_eq, and_comm]

theorem run_modN (t : Nat) (f : Node → Node) (σ : Core) :
    (modN t f).run σ = .ok () { σ with nodes := σ.nodes.modify t f } := rfl

theorem put_table_side (σ : Core) (t : Nat) (tbl : List (Nat × Nat)) (sd : List (Nat × Side)) :
    LK.put (LK.put σ t tbl .table) t (encS sd) .side =
      { σ with nodes := σ.nodes.modify t fun n => { n with table := tbl, side := sd } } := by
  simp [LK.put, Array.modify_modify_same, encS, List.map_map, Function.comp_def, sideOfN_sideN]

theorem put_table (σ : Core) (t : Nat) (tbl : List (Nat × Nat)) :
    LK.put σ t tbl .table =
      { σ with nodes := σ.nodes.modify t fun n => { n with table := tbl, side := (σ.nodes.getX
        t).side } } := by
  simp only [LK.put]
  congr 1
  apply Array.modify_congr_getX
  rfl

/-- `tableInsert t e w before lab` (`bf` = 1 for `before`). -/
def tableInsertP : Proc where
  name := "tableInsert"
  params := ["t", "e", "w", "bf", "lab"]
  rets := []
  body := cm{
    r ← ‹findP .table›(t, e)
    n := len table[t]
    if r < n then skip else fail
    p := r + (1 - bf)
    call ‹insertIdxP .table›(t, p, w, lab)
    if N[t].draining then {
      (f, x) ← ‹lookupP .side›(t, e)
      if f then call ‹assocSetP .side›(t, w, x) else fail } }

theorem getX_size_le {α : Type} [Inhabited α] {a : Array α} {i : Nat} (h : a.size ≤ i) : a.getX
  i = default :=
  OrderMaintenance.Proof.Array.getX_ge a h

/-- **`tableInsertP` runs `tableInsert`.** -/
theorem tableInsertP_agree (κ : Caps) (σ : Core) (L : Loc) {t e w lab : Nat} {before : Bool} (ht
  : L "t" = t)
    (he : L "e" = e) (hw : L "w" = w) (hbf : L "bf" = b2n before) (hl : L "lab" = lab)
    (htr : t < κ.lrec .table) (hts : t < κ.lrec .side) (htN : t < κ.tbl .N)
    (hcapT : (σ.nodes.getX t).table.length + 1 ≤ κ.lcap .table)
    (hcapS : (σ.nodes.getX t).side.length + 1 ≤ κ.lcap .side) {σ' : Core}
    (h : (tableInsert t e w before lab).run σ = .ok () σ') :
    ∃ L' c, evalF κ tableInsertP.body σ L = .ok σ' L' c ∧
      c ≤ 250 + 120 * (σ.nodes.getX t).table.length + 50 * (σ.nodes.getX t).side.length := by
  unfold tableInsert at h
  simp only [getN, bind_pure_comp, pure_bind, bind_map_left, EStateM.run_bind, EStateM.run_get] at h
  set T := σ.nodes.getX t with hT
  have hsome : ∃ i, T.table.findIdx? (·.1 == e) = some i := by
    cases hfi : T.table.findIdx? (·.1 == e) with
    | none => simp [T, hfi, OrderMaintenance.Model.guard] at h
    | some i => exact ⟨i, rfl⟩
  obtain ⟨i, hfi⟩ := hsome
  simp only [hfi] at h
  obtain ⟨hfi1, hil⟩ := findIdx?_some_iff'.mp hfi
  have htsz : t < σ.nodes.size := by
    by_contra hc
    have hd : T = default := getX_size_le (by omega)
    rw [hd, show (default : Node).table = [] from rfl] at hil
    simp at hil
  set tbl' := T.table.insertIdx (if before = true then i else i + 1) (w, lab)
  -- the common prefix: find, guard, position, insertion
  obtain ⟨Lf, cf, ef, hrf, hcf⟩ := findP_agree κ .table σ
    (Machine.State.setLocs (fun _ => 0) ["i", "x"] [t, e]) (i := t) (x := e)
    (by simp [Machine.State.setLocs, Machine.State.upd])
    (by simp [Machine.State.setLocs, Machine.State.upd]) htr
  have e1 := evalF_call_ok (q := findP .table) (args := [.var "t", .var "e"]) (ds := ["r"]) (L := L)
    (by simp [evList, Exp.ev, ht, he]) ef
  set L1 := Machine.State.setLocs L ["r"] ((findP .table).rets.map Lf)
  have hL1 : ∀ r, r ≠ "r" → L1 r = L r := fun r h => by
    simp [L1, findP, Machine.State.setLocs, Machine.State.upd, h]
  have hr1 : L1 "r" = i := by
    simp only [findP, Exp.ofNat_def, List.map_cons, hrf, LK.view, List.map_nil,
        Machine.State.setLocs, Machine.State.upd, ↓reduceIte, L1]; exact hfi1
  have e2 := evalF_assign_ok (κ := κ) (s := σ) (L := L1) (x := "n") (e := .llen .table "t") (v
    := T.table.length)
    (by simp [Exp.ev, hL1 "t" (by decide), ht, htr, LK.view, T])
  set L2 := upd L1 "n" T.table.length
  have e3 := evalF_ite_t (κ := κ) (s := σ) (L := L2) (c := "r" <ₑ "n") (t := .skip) (f := .fail)
    (v := 1)
    (by simp [Exp.ev, Machine.BinOp.eval, L2, Machine.State.upd,
      hr1, T, hil]) one_ne_zero evalF_skip
  set pos := if before = true then i else i + 1
  have hb1 : b2n before ≤ 1 := by cases before <;> simp [b2n]
  have e4 := evalF_assign_ok (κ := κ) (s := σ) (L := L2) (x := "p") (e := "r" + (1 - "bf")) (v
    := pos)
    (by
      have hbf2 : L2 "bf" = b2n before := by
        simp only [Machine.State.upd, String.reduceEq, ↓reduceIte, L2]
        rw [hL1 "bf" (by decide), hbf]
      simp only [Exp.ev,  Exp.sub_def, Exp.ofNat_def, hbf2,
        Machine.BinOp.eval,
        show L2 "r" = i by simp [L2, Machine.State.upd,
          hr1], Option.bind_some, ite_eq_left hb1]
      cases before <;> simp [pos, b2n])
  set L3 := upd L2 "p" pos
  have hL3 : ∀ r, r ≠ "r" → r ≠ "n" → r ≠ "p" → L3 r = L r := fun r h1 h2 h3 => by
    simp only [L3, L2, Machine.State.upd, ite_eq_right h2,
      ite_eq_right h3]; exact hL1 r h1
  obtain ⟨Li, ci, ei, hci⟩ := insertIdxP_agree κ .table σ
    (Machine.State.setLocs (fun _ => 0) ["i", "p", "a", "b"] [t, pos, w, lab]) (i := t) (p :=
      pos) (a := w)
    (b := lab) (by simp [Machine.State.setLocs, Machine.State.upd])
    (by simp [Machine.State.setLocs, Machine.State.upd])
    (by simp [Machine.State.setLocs, Machine.State.upd])
    (by simp [Machine.State.setLocs,
      Machine.State.upd]) (by simp [LK.recOk, htsz]) htr
    (by simp [LK.valid]) (by change pos ≤ T.table.length; simp only [pos]; split <;> omega) (by
      simp only [LK.view]; exact hcapT)
  have e5 := evalF_call_ok (q := insertIdxP .table) (args := [.var "t", .var "p", .var "w", .var
    "lab"]) (ds := [])
    (L := L3) (by
      have h1 : L3 "p" = pos := by simp [L3, Machine.State.upd]
      simp [evList, Exp.ev, hL3 "t" (by decide) (by decide) (by decide), ht,
        hL3 "w" (by decide) (by decide) (by decide), hw, hL3 "lab" (by decide) (by decide) (by
          decide), hl, h1]) ei
  simp only [LK.view] at e5
  set S5 := LK.put σ t tbl' .table
  set L5 := Machine.State.setLocs L3 [] ((insertIdxP .table).rets.map Li)
  have hL5 : ∀ r, r ≠ "r" → r ≠ "n" → r ≠ "p" → L5 r = L r := fun r h1 h2 h3 => hL3 r h1 h2 h3
  have hdr : (S5.nodes.getX t).draining = T.draining := by
    simp only [S5, LK.put, OrderMaintenance.Proof.Top.getX_modify', htsz, and_self, ite_true, T]
  have hview : LK.view S5 t .side = encS T.side := by
    rw [LK.view_put (by simp [LK.recOk, htsz]) (by simp [LK.valid])]; simp [LK.view, T]
  by_cases hd : T.draining = true
  · simp only [hd, ite_true] at h
    have hlk : ∃ sd, lookup T.side e = some sd := by
      cases hl : lookup T.side e with
      | none => simp [hl, OrderMaintenance.Model.guard] at h
      | some sd => exact ⟨sd, rfl⟩
    obtain ⟨sd, hlk⟩ := hlk
    simp only [hlk] at h
    simp only [modN, EStateM.run_modify, EStateM.Result.ok.injEq, true_and] at h
    subst h
    obtain ⟨Lk, ck, ek, hfk, hvk, -, -, hck⟩ := lookupP_agree κ .side S5
      (Machine.State.setLocs (fun _ => 0) ["i", "x"] [t, e]) (i := t) (x := e)
      (by simp [Machine.State.setLocs, Machine.State.upd])
      (by simp [Machine.State.setLocs, Machine.State.upd]) hts
    rw [hview, lookup_encS, hlk] at hfk hvk
    rw [hview] at hck
    have e6 := evalF_call_ok (q := lookupP .side) (args := [.var "t", .var "e"]) (ds := ["f",
      "x"]) (L := L5)
      (by simp [evList, Exp.ev, hL5 "t" (by decide) (by decide) (by decide), ht,
        hL5 "e" (by decide) (by decide) (by decide), he]) ek
    set L6 := Machine.State.setLocs L5 ["f", "x"] ((lookupP .side).rets.map Lk)
    obtain ⟨La, ca, ea, hca⟩ := assocSetP_agree κ .side S5
      (Machine.State.setLocs (fun _ => 0) ["i", "x", "y"] [t, w, sideN sd]) (i := t) (x := w) (y
        := sideN sd)
      (by simp [Machine.State.setLocs, Machine.State.upd])
      (by simp [Machine.State.setLocs, Machine.State.upd])
      (by simp [Machine.State.setLocs, Machine.State.upd])
      (by simp [S5, LK.idOk, LK.recOk, htsz]) (by simp [S5, LK.recOk, htsz]) hts
      (fun a => by simp [LK.valid, sideN_le]) (by
        rw [hview]
        have := length_assocSet_le' (encS T.side) w (sideN sd)
        simp only [encS, List.length_map] at this ⊢; omega)
    rw [hview, assocSet_encS] at ea
    rw [hview] at hca
    have e7 := evalF_call_ok (q := assocSetP .side) (args := [.var "t", .var "w", .var "x"]) (ds
      := [])
      (L := L6) (by
        simp [evList, Exp.ev, L6, lookupP, Machine.State.setLocs,
          Machine.State.upd, hvk,
          hL5 "t" (by decide) (by decide) (by decide), ht, hL5 "w" (by decide) (by decide) (by
            decide), hw]) ea
    rw [put_table_side] at e7
    have e8 := evalF_ite_t (κ := κ) (c := .var "f") (f := .fail) (v := 1)
      (by simp [Exp.ev, L6, lookupP, Machine.State.setLocs,
        Machine.State.upd, hfk]) one_ne_zero e7
    have e9 := evalF_ite_t (κ := κ) (s := S5) (L := L5) (c := .rd (.n .draining) "t") (f :=
      .skip) (v := 1)
      (by simp [Exp.ev, hL5 "t" (by decide) (by decide) (by decide), ht, htN, Fld.cap, Fld.get,
        NF.get, hdr, hd,
        b2n]) one_ne_zero (evalF_seq_ok2 e6 e8)
    refine ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 (evalF_seq_ok2 e4
      (evalF_seq_ok2 e5 e9)))),
      ?_⟩
    simp only [LK.view, List.length_map] at hcf hci hck hca
    simp only [Exp.cost, costList, List.map, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil,
       Exp.sub_def, Exp.ofNat_def] at hcf hci hck hca ⊢
    have : (σ.nodes.getX t).table.length = T.table.length := rfl
    have : (σ.nodes.getX t).side.length = T.side.length := rfl
    omega
  · have hd' : T.draining = false := by simpa using hd
    simp only [hd', Bool.false_eq_true, ite_false] at h
    simp only [modN, EStateM.run_modify, EStateM.Result.ok.injEq, true_and] at h
    subst h
    have e9 := evalF_ite_f (κ := κ) (s := S5) (L := L5) (c := .rd (.n .draining) "t")
      (t := (lookupP .side).call [.var "t", .var "e"] ["f", "x"];;
        .ite "f" ((assocSetP .side).call [.var "t", .var "w", .var "x"] []) .fail)
      (by simp [Exp.ev, hL5 "t" (by decide) (by decide) (by decide), ht, htN, Fld.cap, Fld.get,
        NF.get, hdr, hd',
        b2n]) evalF_skip
    have e9' := e9.trans (congrArg (fun x => Res.ok x L5 _) (put_table σ t tbl'))
    refine ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 (evalF_seq_ok2 e4
      (evalF_seq_ok2 e5 e9')))),
      ?_⟩
    simp only [LK.view] at hcf hci
    simp only [Exp.cost, costList, List.map, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil,
       Exp.sub_def, Exp.ofNat_def] at hcf hci ⊢
    have : (σ.nodes.getX t).table.length = T.table.length := rfl
    omega

theorem Exp.ev_bin' {κ : Caps} {σ : Core} {L : Loc} {op : BinOp} {a b : Exp} {x y : Nat}
    (ha : a.ev κ σ L = some x) (hb : b.ev κ σ L = some y) : (Exp.bin op a b).ev κ σ L = op.eval
      x y := by
  simp [Exp.ev, ha, hb]

/-- The bounds around position `r` of table `t`. -/
def boundsS : Stm := cm{
  if bf then {
    if 0 < r then lo := table[t][r - 1].snd + 1 else lo := 0
    hi := table[t][r].snd }
  else {
    lo := table[t][r].snd + 1
    if r + 1 < n then hi := table[t][r + 1].snd else hi := 1 <<< P.beta } }

/-- `roomNextTo t e before` (`bf` = 1 for `before`): a free label next to `e` in table `t`. -/
def roomP : Proc where
  name := "roomNextTo"
  params := ["t", "e", "bf"]
  rets := ["l"]
  body := cm{
    r ← ‹findP .table›(t, e)
    n := len table[t]
    if r < n then skip else fail
    boundsS
    if hi ≤ lo then fail
    l := (lo + hi - 1) / 2 }

/-- The bounds `roomNextTo` takes: one above the lower neighbour's label, and the upper one. -/
def rLo (tab : List (Nat × Nat)) (i : Nat) (before : Bool) : Nat :=
  if before then (if 0 < i then (tab[i - 1]?.getD (0, 0)).2 + 1 else 0) else (tab[i]?.getD (0,
    0)).2 + 1
/-- The upper label boundary next to an insertion, using `2^β` beyond the final entry. -/
def rHi (tab : List (Nat × Nat)) (i : Nat) (before : Bool) (β : Nat) : Nat :=
  if before then (tab[i]?.getD (0, 0)).2
  else (if i + 1 < tab.length then (tab[i + 1]?.getD (0, 0)).2 else 1 <<< β)

theorem roomNextTo_inv {σ σ' : Core} {t e lab : Nat} {before : Bool}
    (h : (roomNextTo t e before).run σ = .ok lab σ') :
    ∃ i, (σ.nodes.getX t).table.findIdx? (·.1 == e) = some i ∧ σ' = σ ∧
      rLo (σ.nodes.getX t).table i before < rHi (σ.nodes.getX t).table i before σ.P.beta ∧
      lab = (rLo (σ.nodes.getX t).table i before + rHi (σ.nodes.getX t).table i before σ.P.beta
        - 1) / 2 := by
  cases hfi : (σ.nodes.getX t).table.findIdx? (·.1 == e) with
  | none => unfold roomNextTo at h; simp [getN, getP, hfi, OrderMaintenance.Model.guard] at h
  | some i =>
    refine ⟨i, rfl, ?_⟩
    unfold roomNextTo at h
    cases before
    · by_cases hn : i + 1 < (σ.nodes.getX t).table.length
      all_goals
        simp only [getP, bind_pure_comp, getN, Bool.false_eq_true, ↓reduceIte,
            List.getD_eq_getElem?_getD, ge_iff_le, Nat.succ_add_sub_one, bind_map_left,
            EStateM.run_bind, EStateM.run_get, hfi, hn, getElem?_pos, Option.getD_some,
            Proof.run_ite, Proof.run_map_guard, EStateM.run_pure] at h
        split at h
        · simp at h
        · next hg =>
          injection h with h1 h2
          exact ⟨h2.symm, by simp only [rLo, rHi]; simp [hn] at hg ⊢; omega, by simp [rLo, rHi,
            hn, ← h1]⟩
    · by_cases hp : 0 < i
      all_goals
        simp only [getP, bind_pure_comp, getN, ↓reduceIte, gt_iff_lt, List.getD_eq_getElem?_getD,
            ge_iff_le, bind_map_left, EStateM.run_bind, EStateM.run_get, hfi, hp,
            Nat.succ_add_sub_one, Proof.run_ite, Proof.run_map_guard, EStateM.run_pure,
            nonpos_iff_eq_zero, zero_add] at h
        split at h
        · simp at h
        · next hg =>
          injection h with h1 h2
          exact ⟨h2.symm, by simp only [rLo, rHi]; simp [hp] at hg ⊢; omega, by simp [rLo, rHi,
            hp, ← h1]⟩

theorem boundsS_ok {κ : Caps} {σ : Core} {L : Loc} {t i : Nat} {before : Bool} (ht : L "t" = t)
  (hr : L "r" = i)
    (hn : L "n" = (σ.nodes.getX t).table.length) (hbf : L "bf" = b2n before)
    (hi : i < (σ.nodes.getX t).table.length) (htr : t < κ.lrec .table) :
    ∃ L' c, evalF κ boundsS σ L = .ok σ L' c ∧ L' "lo" = rLo (σ.nodes.getX t).table i before ∧
      L' "hi" = rHi (σ.nodes.getX t).table i before σ.P.beta ∧ c ≤ 40 ∧
      ∀ r, r ≠ "lo" → r ≠ "hi" → L' r = L r := by
  set tab := (σ.nodes.getX t).table
  have rd : ∀ (Lx : Loc) (jx : Exp) (y : Nat), Lx "t" = t → jx.ev κ σ Lx = some y → y < tab.length →
      (Exp.lrd .table true "t" jx).ev κ σ Lx = some (tab[y]?.getD (0, 0)).2 := by
    intro Lx jx y h1 h2 h3; simp [Exp.ev, h1, h2, htr, LK.view, h3, tab, List.getD_eq_getElem?_getD]
  cases before
  · -- after: `lo` above `e`, `hi` the next label or the top
    have a1 := evalF_assign_ok (κ := κ) (s := σ) (L := L) (x := "lo") (e := .lrd .table true "t"
      "r" + 1)
      (v := (tab[i]?.getD (0, 0)).2 + 1) (by
        rw [Exp.add_def, Exp.ev_bin' (rd L (.var "r") i ht (by simp [Exp.ev, hr]) hi) rfl]; rfl)
    set L1 := Machine.State.upd L "lo" ((tab[i]?.getD (0, 0)).2 + 1)
    have hL1 : ∀ r, r ≠ "lo" → L1 r = L r := fun r h => by simp [L1, Machine.State.upd, h]
    by_cases hn1 : i + 1 < tab.length
    · have a2 := evalF_assign_ok (κ := κ) (s := σ) (L := L1) (x := "hi") (e := .lrd .table true
        "t" ("r" + 1))
        (v := (tab[i + 1]?.getD (0, 0)).2) (rd L1 ("r" + 1) (i + 1) (by rw [hL1 "t" (by decide),
          ht])
          (by simp [Exp.ev, hL1 "r" (by decide), hr, Machine.BinOp.eval]) hn1)
      refine ⟨_, _, evalF_ite_f (by simp [Exp.ev, hbf, b2n]) (evalF_seq_ok2 a1
        (evalF_ite_t (v := 1) (by simp [Exp.ev, Machine.BinOp.eval, hL1 "r" (by decide), hr,
          hL1 "n" (by decide), hn, hn1, tab]) one_ne_zero a2)), ?_, ?_, ?_, ?_⟩
      · simp [Machine.State.upd, L1, rLo]
      · simp [Machine.State.upd, rHi, hn1]
      · simp [Exp.cost]
      · intro r h1 h2; simp only [Machine.State.upd, ite_eq_right h2]; exact hL1 r h1
    · have a2 := evalF_assign_ok (κ := κ) (s := σ) (L := L1) (x := "hi") (e := .bin .shl 1 (.prm
        .beta))
        (v := 1 <<< σ.P.beta) (by simp [Exp.ev, Machine.BinOp.eval, PF.get, Nat.shiftLeft_eq])
      refine ⟨_, _, evalF_ite_f (by simp [Exp.ev, hbf, b2n]) (evalF_seq_ok2 a1
        (evalF_ite_f (by
          have hn1' : ¬ i + 1 < (σ.nodes.getX t).table.length := hn1
          simp only [Exp.ev, hL1 "r" (by decide), hr, BinOp.eval, Option.bind_some,
              hL1 "n" (by decide), hn, Option.some.injEq, ite_eq_right_iff,
              one_ne_zero, imp_false, not_lt, ge_iff_le]
          change tab.length ≤ i + 1; omega) a2)),
        ?_, ?_, ?_, ?_⟩
      · simp [Machine.State.upd, L1, rLo]
      · simp [Machine.State.upd, rHi, hn1]
      · simp [Exp.cost]
      · intro r h1 h2; simp only [Machine.State.upd, ite_eq_right h2]; exact hL1 r h1
  · -- before: `lo` above the previous label (or 0), `hi` the label of `e`
    have hlo : ∃ c1, evalF κ (.ite (0 <ₑ "r") ("lo" ::= .lrd .table true "t" ("r" - 1) + 1)
      ("lo" ::= 0)) σ L =
        .ok σ (Machine.State.upd L "lo" (rLo tab i true)) c1 ∧ c1 ≤ 20 := by
      by_cases hp : 0 < i
      · have a1 := evalF_assign_ok (κ := κ) (s := σ) (L := L) (x := "lo") (e := .lrd .table true
          "t" ("r" - 1) + 1)
          (v := rLo tab i true) (by
            rw [Exp.add_def, Exp.ev_bin' (rd L ("r" - 1) (i - 1) ht
              (by simp [Exp.ev, hr, Machine.BinOp.eval]; omega) (by omega)) rfl]
            simp [Machine.BinOp.eval, rLo, hp])
        exact ⟨_, evalF_ite_t (v := 1) (by simp [Exp.ev, Machine.BinOp.eval, hr, hp])
          one_ne_zero a1,
          by simp [Exp.cost]⟩
      · have a1 := evalF_assign_ok (κ := κ) (s := σ) (L := L) (x := "lo") (e := (0 : Exp)) (v :=
          rLo tab i true)
          (by simp [Exp.ev, rLo, hp])
        exact ⟨_, evalF_ite_f (by simp [Exp.ev, Machine.BinOp.eval, hr]; omega) a1, by simp
          [Exp.cost]⟩
    obtain ⟨c1, e1, hc1⟩ := hlo
    set L1 := Machine.State.upd L "lo" (rLo tab i true)
    have hL1 : ∀ r, r ≠ "lo" → L1 r = L r := fun r h => by simp [L1, Machine.State.upd, h]
    have a2 := evalF_assign_ok (κ := κ) (s := σ) (L := L1) (x := "hi") (e := .lrd .table true
      "t" "r")
      (v := rHi tab i true σ.P.beta) (by
        rw [rd L1 (.var "r") i (by rw [hL1 "t" (by decide), ht]) (by simp [Exp.ev, hL1 "r" (by
          decide), hr]) hi]
        simp [rHi])
    refine ⟨_, _, evalF_ite_t (v := 1) (by simp [Exp.ev, hbf, b2n]) one_ne_zero (evalF_seq_ok2
      e1 a2), ?_, ?_, ?_,
      ?_⟩
    · simp [Machine.State.upd, L1]
    · simp [Machine.State.upd]
    · simp [Exp.cost] at hc1 ⊢; omega
    · intro r h1 h2; simp only [Machine.State.upd, ite_eq_right h2]; exact hL1 r h1

/-- **`roomP` runs `roomNextTo`.** -/
theorem roomP_agree (κ : Caps) (σ : Core) (L : Loc) {t e : Nat} {before : Bool} (ht : L "t" = t)
    (he : L "e" = e) (hbf : L "bf" = b2n before) (htr : t < κ.lrec .table) {lab : Nat} {σ' : Core}
    (h : (roomNextTo t e before).run σ = .ok lab σ') :
    σ' = σ ∧ ∃ L' c, evalF κ roomP.body σ L = .ok σ L' c ∧ L' "l" = lab ∧
      c ≤ 120 + 20 * (σ.nodes.getX t).table.length := by
  obtain ⟨i, hfi, hs, hlt, rfl⟩ := roomNextTo_inv h
  subst σ'
  refine ⟨rfl, ?_⟩
  obtain ⟨hfi1, hil⟩ := findIdx?_some_iff'.mp hfi
  obtain ⟨Lf, cf, ef, hrf, hcf⟩ := findP_agree κ .table σ
    (Machine.State.setLocs (fun _ => 0) ["i", "x"] [t, e]) (i := t) (x := e)
    (by simp [Machine.State.setLocs, Machine.State.upd])
    (by simp [Machine.State.setLocs, Machine.State.upd]) htr
  have e1 := evalF_call_ok (q := findP .table) (args := [.var "t", .var "e"]) (ds := ["r"]) (L := L)
    (by simp [evList, Exp.ev, ht, he]) ef
  set L1 := Machine.State.setLocs L ["r"] ((findP .table).rets.map Lf)
  have hL1 : ∀ r, r ≠ "r" → L1 r = L r := fun r h => by
    simp [L1, findP, Machine.State.setLocs, Machine.State.upd, h]
  have hr1 : L1 "r" = i := by
    simp only [findP, Exp.ofNat_def, List.map_cons, hrf, LK.view, List.map_nil,
        Machine.State.setLocs, Machine.State.upd, ↓reduceIte, L1]; exact hfi1
  have e2 := evalF_assign_ok (κ := κ) (s := σ) (L := L1) (x := "n") (e := .llen .table "t") (v
    := (σ.nodes.getX t).table.length)
    (by simp [Exp.ev, hL1 "t" (by decide), ht, htr, LK.view])
  set L2 := Machine.State.upd L1 "n" (σ.nodes.getX t).table.length
  have e3 := evalF_ite_t (κ := κ) (s := σ) (L := L2) (c := "r" <ₑ "n") (t := .skip) (f := .fail)
    (v := 1)
    (by simp [Exp.ev, Machine.BinOp.eval, L2, Machine.State.upd,
      hr1, hil]) one_ne_zero evalF_skip
  obtain ⟨L3, c3, e4, hlo, hhi, hc3, hF3⟩ := boundsS_ok (κ := κ) (σ := σ) (L := L2) (t := t) (i
    := i)
    (before := before) (by simp [L2, Machine.State.upd, hL1 "t" (by decide), ht])
    (by simp [L2, Machine.State.upd,
      hr1]) (by simp only [Machine.State.upd, ↓reduceIte, L2])
    (by simp [L2, Machine.State.upd, hL1 "bf" (by decide), hbf]) hil htr
  have e5 := evalF_ite_f (κ := κ) (s := σ) (L := L3) (c := "hi" ≤ₑ "lo") (t := .fail)
    (by simp [Exp.ev, Machine.BinOp.eval, hlo, hhi]; omega) evalF_skip
  have e6 := evalF_assign_ok (κ := κ) (s := σ) (L := L3) (x := "l") (e := ("lo" + "hi" - 1) / 2)
    (v := (rLo (σ.nodes.getX t).table i before + rHi (σ.nodes.getX t).table i before σ.P.beta -
      1) / 2)
    (by simp only [Exp.add_def, Exp.ofNat_def, Exp.sub_def, Exp.div_def, Exp.ev, hlo, hhi,
        BinOp.eval, Option.bind_some]; rw [ite_eq_left (by omega)]; rfl)
  refine ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 (evalF_seq_ok2 e4
    (evalF_seq_ok2 e5 e6)))),
    by simp [Machine.State.upd], ?_⟩
  simp only [LK.view] at hcf
  simp only [Exp.cost, costList, List.map, List.sum_cons, List.sum_nil, List.length_cons,
    List.length_nil,
    Exp.add_def, Exp.sub_def, Exp.div_def, Exp.ofNat_def] at hcf hc3 ⊢
  omega

end OrderMaintenance.Impl
