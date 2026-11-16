/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.ChunkStep
public import LeanPool.OrderMaintenance.Impl.StartDrain
public import LeanPool.OrderMaintenance.Proof.Top.RunIns
public import LeanPool.OrderMaintenance.Proof.Cost.Reserve


/-!
# M6: reservation at Level M (`insertAround`, `splitChunkStart`)

`insertAround x y z` puts the new chunks `y`, `z` around `x` in every table holding `x`. Level F
computes all the labels first, then inserts. The program computes the two labels of a table right
before inserting into it: the tables are distinct, so a table is still untouched when its turn
comes, and the labels agree.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Proof.Top
open OrderMaintenance.Machine (Reg BinOp UnOp)

local notation "upd" => OrderMaintenance.Machine.State.upd

/-! ### The tables holding `x` -/

/-- The labels of `y` and `z` in table `T` (Level F's `ly`, `lz`). -/
def cLab (S0 : Core) (x : Nat) (T : Nat) : Nat × Nat :=
  (roomL S0.P.beta (S0.nodes.getX T).table x true, roomL S0.P.beta (S0.nodes.getX T).table x false)

def cStep (S0 : Core) (x y z : Nat) (ns : Array Node) (T : Nat) : Array Node :=
  ns.modify T (aroundF S0 x y z (cLab S0 x) T)

/-- Level F after the insertions into the first `j` tables holding `x`. -/
def cJ (S0 : Core) (x y z j : Nat) : Core :=
  { S0 with nodes := ((S0.cin.getX x).take j).foldl (cStep S0 x y z) S0.nodes }

theorem cStep_getX (S0 : Core) (x y z : Nat) (ns : Array Node) (T u : Nat) (h : u ≠ T) :
    (cStep S0 x y z ns T).getX u = ns.getX u := by
  simp only [cStep, getX_modify']; rw [ite_eq_right (fun e => h e.1)]

theorem cStep_size (S0 : Core) (x y z : Nat) (ns : Array Node) (T : Nat) :
    (cStep S0 x y z ns T).size = ns.size := by simp [cStep]

theorem cJ_getX_notin {S0 : Core} {x y z j u : Nat} (hu : u ∉ (S0.cin.getX x).take j) :
    (cJ S0 x y z j).nodes.getX u = S0.nodes.getX u := by
  simp only [cJ]; rw [fold_modify_getX_notin (cStep_getX S0 x y z) _ _ hu]

theorem cJ_size (S0 : Core) (x y z j : Nat) : (cJ S0 x y z j).nodes.size = S0.nodes.size := by
  simp only [cJ]; rw [fold_modify_size (cStep_size S0 x y z)]

theorem cJ_zero (S0 : Core) (x y z : Nat) : cJ S0 x y z 0 = S0 := by simp [cJ]

def cinsBody : Stm := cm{
  T := cin[x][j].fst
  a ← roomP(T, x, 1)
  b ← roomP(T, x, 0)
  call tableInsertP(T, x, y, 1, a)
  call tableInsertP(T, x, z, 0, b) }

def cinsS : Stm := cm{ m := len cin[x]; for j < m do cinsBody }

theorem cinsStep_ok {κ : Caps} {S0 : Core} {L : Loc} {x y z j B : Nat}
    (hnd : (S0.cin.getX x).Nodup) (hyx : y ≠ x)
    (hroom : ∀ T ∈ S0.cin.getX x, RoomOK S0 x T) (hj : j < (S0.cin.getX x).length)
    (hLx : L "x" = x) (hLy : L "y" = y) (hLz : L "z" = z) (hxi : x < κ.lrec .cin)
    (hcapT : ∀ T ∈ S0.cin.getX x, T < κ.lrec .table ∧ T < κ.lrec .side ∧ T < κ.tbl .N ∧
      (S0.nodes.getX T).table.length + 2 ≤ κ.lcap .table ∧ (S0.nodes.getX T).side.length + 2 ≤ κ.lcap .side)
    (hB : ∀ T ∈ S0.cin.getX x, (S0.nodes.getX T).table.length ≤ B ∧ (S0.nodes.getX T).side.length ≤ B) :
    ∃ L' c, evalF κ cinsBody (cJ S0 x y z j) (upd L "j" j) = .ok (cJ S0 x y z (j + 1)) L' c ∧
      c ≤ 1000 + 400 * B ∧ ∀ r, r ≠ "j" → r ≠ "T" → r ≠ "a" → r ≠ "b" → L' r = L r := by
  set tabs := S0.cin.getX x
  set T := tabs[j]
  set S := cJ S0 x y z j
  have hTm : T ∈ tabs := List.getElem_mem hj
  have hTn : T ∉ tabs.take j := nodup_getElem_notin_take hnd hj
  have hTN : T < S0.nodes.size := (hroom T hTm).lt
  have hST : S.nodes.getX T = S0.nodes.getX T := cJ_getX_notin hTn
  have hSx : S.cin.getX x = tabs := rfl
  have hroomS : RoomOK S x T := by unfold RoomOK; rw [hST]; exact hroom T hTm
  obtain ⟨hTt, hTs, hTNc, hcT, hcS⟩ := hcapT T hTm
  obtain ⟨hBt, hBs⟩ := hB T hTm
  -- the table
  set L0 := upd L "j" j
  have e1 := evalF_assign_ok (κ := κ) (s := S) (L := L0) (x := "T") (e := .lrd .cin false "x" "j") (v := T) (by
    simp [Exp.ev, L0, OrderMaintenance.Machine.State.upd, hLx, hxi, LK.view, hSx, hj, T])
  set L1 := upd L0 "T" T
  have hL1 : ∀ r, r ≠ "j" → r ≠ "T" → L1 r = L r := fun r h1 h2 => by simp [L1, L0, OrderMaintenance.Machine.State.upd, h1, h2]
  -- the two labels
  set a := roomL S.P.beta (S.nodes.getX T).table x true
  set b := roomL S.P.beta (S.nodes.getX T).table x false
  have hLx' : L1 "x" = x := by rw [hL1 "x" (by decide) (by decide), hLx]
  obtain ⟨-, La, ca, ea, hla, hca⟩ := roomP_agree κ S
    (OrderMaintenance.Machine.State.setLocs (fun _ => 0) ["t", "e", "bf"] [T, x, 1]) (t := T) (e := x) (before := true)
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd])
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd])
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd,
      b2n]) hTt (roomNextTo_run' hroomS true)
  have e2 := evalF_call_ok (q := roomP) (args := [.var "T", .var "x", 1]) (ds := ["a"]) (L := L1)
    (by simp [evList, Exp.ev, L1, L0, OrderMaintenance.Machine.State.upd, hLx]) ea
  set L2 := OrderMaintenance.Machine.State.setLocs L1 ["a"] (roomP.rets.map La)
  obtain ⟨-, Lb, cb, eb, hlb, hcb⟩ := roomP_agree κ S
    (OrderMaintenance.Machine.State.setLocs (fun _ => 0) ["t", "e", "bf"] [T, x, 0]) (t := T) (e := x) (before := false)
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd])
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd])
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd,
      b2n]) hTt (roomNextTo_run' hroomS false)
  have e3 := evalF_call_ok (q := roomP) (args := [.var "T", .var "x", 0]) (ds := ["b"]) (L := L2)
    (by simp [evList, Exp.ev, L2, L1, L0, roomP, OrderMaintenance.Machine.State.setLocs,
      OrderMaintenance.Machine.State.upd, hLx]) eb
  set L3 := OrderMaintenance.Machine.State.setLocs L2 ["b"] (roomP.rets.map Lb)
  have hL3 : ∀ r, r ≠ "j" → r ≠ "T" → r ≠ "a" → r ≠ "b" → L3 r = L r := fun r h1 h2 h3 h4 => by
    simp only [L3, L2, roomP, OrderMaintenance.Machine.State.setLocs, List.map,
      OrderMaintenance.Machine.State.upd, ite_eq_right h3, ite_eq_right h4]
    exact hL1 r h1 h2
  have hL3T : L3 "T" = T := by simp [L3, L2, L1, roomP, OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd]
  have hL3a : L3 "a" = a := by simp [L3, L2, roomP, OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd, hla]; rfl
  have hL3b : L3 "b" = b := by simp [L3, roomP, OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd, hlb]; rfl
  -- the two insertions
  obtain ⟨A, le, Bs, htab, hA, hside, -, -⟩ := hroomS
  have hins := insertAroundIn_run (s := S) (T := T) (a := a) (b := b) (n2 := z) htab hA hyx hside
  have h1' := tableInsert_run (s := S) (t := T) (new := y) htab hA true a hside
  unfold insertAroundIn at hins
  obtain ⟨u, s1, h1, h2⟩ := run_bind_ok hins
  rw [h1'] at h1
  injection h1 with _ hs1
  subst hs1
  set s1 := { S with nodes := S.nodes.modify T (setTS (insTab A Bs x le y a true) (sideAfter (S.nodes.getX T) x y)) }
  have hTS : T < S.nodes.size := by rw [cJ_size]; exact hTN
  have hs1T : s1.nodes.getX T = setTS (insTab A Bs x le y a true) (sideAfter (S.nodes.getX T) x y) (S.nodes.getX T) := by
    simp only [s1, getX_modify', hTS, and_self, ite_true]
  have hlenS : (S.nodes.getX T).table.length = A.length + Bs.length + 1 := by rw [htab]; simp; omega
  obtain ⟨L4', c4, e4', hc4⟩ := tableInsertP_agree κ S
    (OrderMaintenance.Machine.State.setLocs (fun _ => 0) ["t", "e", "w", "bf", "lab"] [T, x, y, 1, a]) (t := T) (e := x)
    (w := y) (before := true) (lab := a)
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd])
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd])
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd])
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd, b2n])
    (by simp [OrderMaintenance.Machine.State.setLocs,
      OrderMaintenance.Machine.State.upd]) hTt hTs hTNc
    (by rw [hST]; omega) (by rw [hST]; omega) h1'
  have e4 := evalF_call_ok (q := tableInsertP) (args := [.var "T", .var "x", .var "y", 1, .var "a"]) (ds := [])
    (L := L3) (by
      simp [evList, Exp.ev, hL3T, hL3a, hL3 "x" (by decide) (by decide) (by decide) (by decide),
        hLx,
        hL3 "y" (by decide) (by decide) (by decide) (by decide), hLy]) e4'
  set L4 := OrderMaintenance.Machine.State.setLocs L3 [] (tableInsertP.rets.map L4')
  have hlen1 : (s1.nodes.getX T).table.length = (S.nodes.getX T).table.length + 1 := by
    rw [hs1T, hlenS]; simp [setTS, insTab]; omega
  have hside1 : (s1.nodes.getX T).side.length ≤ (S.nodes.getX T).side.length + 1 := by
    rw [hs1T]; simp only [setTS, sideAfter]; split
    · exact length_assocSet_le' _ _ _
    · omega
  obtain ⟨L5', c5, e5', hc5⟩ := tableInsertP_agree κ s1
    (OrderMaintenance.Machine.State.setLocs (fun _ => 0) ["t", "e", "w", "bf", "lab"] [T, x, z, 0, b]) (t := T) (e := x)
    (w := z) (before := false) (lab := b)
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd])
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd])
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd])
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd, b2n])
    (by simp [OrderMaintenance.Machine.State.setLocs,
      OrderMaintenance.Machine.State.upd]) hTt hTs hTNc
    (by rw [hlen1, hST]; omega) (by rw [hST] at hside1; omega) h2
  have e5 := evalF_call_ok (q := tableInsertP) (args := [.var "T", .var "x", .var "z", 0, .var "b"]) (ds := [])
    (L := L4) (by
      simp [evList, Exp.ev, L4, OrderMaintenance.Machine.State.setLocs, hL3T, hL3b,
        hL3 "x" (by decide) (by decide) (by decide) (by decide), hLx,
        hL3 "z" (by decide) (by decide) (by decide) (by decide), hLz]) e5'
  have hG : aroundF S0 x y z (cLab S0 x) T =
      setTS (aroundTab A Bs x le y z a b) (sideAround (S.nodes.getX T) x y z) := by
    have ha : a = roomL S0.P.beta (A ++ (x, le) :: Bs) x true := by
      show roomL S.P.beta (S.nodes.getX T).table x true = _; rw [htab]; rfl
    have hb : b = roomL S0.P.beta (A ++ (x, le) :: Bs) x false := by
      show roomL S.P.beta (S.nodes.getX T).table x false = _; rw [htab]; rfl
    unfold aroundF cLab
    rw [← hST, htab, aroundT_eq hA, ha, hb]
  have hfin : { S with nodes := S.nodes.modify T (setTS (aroundTab A Bs x le y z a b)
      (sideAround (S.nodes.getX T) x y z)) } = cJ S0 x y z (j + 1) := by
    have hn : (cJ S0 x y z (j + 1)).nodes = cStep S0 x y z S.nodes T := by
      simp only [cJ, S]; rw [List.take_succ_eq_append_getElem hj, List.foldl_append]; rfl
    rw [show cJ S0 x y z (j + 1) = { S with nodes := (cJ S0 x y z (j + 1)).nodes } from rfl, hn]
    simp only [cStep, hG]
  rw [hfin] at e5
  refine ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 (evalF_seq_ok2 e4 e5))), ?_, ?_⟩
  · rw [hST] at hca hcb hc4
    rw [hlen1, hST] at hc5
    rw [hST] at hside1
    have : (s1.nodes.getX T).side.length ≤ B + 1 := by omega
    simp only [Exp.cost, costList, List.map, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil,
      Exp.ofNat_def] at hca hcb hc4 hc5 ⊢
    omega
  · intro r h1 h2 h3 h4
    simp only [OrderMaintenance.Machine.State.setLocs, tableInsertP, List.map]
    exact hL3 r h1 h2 h3 h4

theorem cinsS_ok {κ : Caps} {S0 : Core} {L : Loc} {x y z B : Nat}
    (hnd : (S0.cin.getX x).Nodup) (hyx : y ≠ x) (hroom : ∀ T ∈ S0.cin.getX x, RoomOK S0 x T)
    (hLx : L "x" = x) (hLy : L "y" = y) (hLz : L "z" = z) (hxi : x < κ.lrec .cin)
    (hcapT : ∀ T ∈ S0.cin.getX x, T < κ.lrec .table ∧ T < κ.lrec .side ∧ T < κ.tbl .N ∧
      (S0.nodes.getX T).table.length + 2 ≤ κ.lcap .table ∧ (S0.nodes.getX T).side.length + 2 ≤ κ.lcap .side)
    (hB : ∀ T ∈ S0.cin.getX x, (S0.nodes.getX T).table.length ≤ B ∧ (S0.nodes.getX T).side.length ≤ B) :
    ∃ L' c, evalF κ cinsS S0 L = .ok (cJ S0 x y z (S0.cin.getX x).length) L' c ∧
      c ≤ 5 + (S0.cin.getX x).length * (1001 + 400 * B) ∧
      ∀ r, r ≠ "m" → r ≠ "j" → r ≠ "T" → r ≠ "a" → r ≠ "b" → L' r = L r := by
  set m := (S0.cin.getX x).length
  have a1 := evalF_assign_ok (κ := κ) (s := S0) (L := L) (x := "m") (e := .llen .cin "x") (v := m)
    (by simp [Exp.ev, hLx, hxi, LK.view, m])
  set L1 := upd L "m" m
  obtain ⟨S', L', c, he, hc, hs', hF⟩ := evalF_loop (κ := κ) (x := "j") (n := .var "m") (b := cinsBody)
    (s := S0) (L := L1) (N := m) (by simp [Exp.ev, L1, OrderMaintenance.Machine.State.upd])
    (fun j S L' => S = cJ S0 x y z j ∧
      ∀ r, r ≠ "m" → r ≠ "j" → r ≠ "T" → r ≠ "a" → r ≠ "b" → L' r = L r) (1000 + 400 * B)
    ⟨by rw [cJ_zero], fun r h1 _ _ _ _ => by simp [L1, OrderMaintenance.Machine.State.upd, h1]⟩
    (by
      intro j hj S1 L2 ⟨hS1, hF2⟩
      subst hS1
      obtain ⟨L3, c3, e3, hc3, hF3⟩ := cinsStep_ok (κ := κ) (L := L2) (B := B) hnd hyx hroom hj
        (by rw [hF2 "x" (by decide) (by decide) (by decide) (by decide) (by decide), hLx])
        (by rw [hF2 "y" (by decide) (by decide) (by decide) (by decide) (by decide), hLy])
        (by rw [hF2 "z" (by decide) (by decide) (by decide) (by decide) (by decide),
          hLz]) hxi hcapT hB
      exact ⟨_, L3, c3, e3, hc3, rfl, fun r h1 h2 h3 h4 h5 => (hF3 r h2 h3 h4 h5).trans (hF2 r h1 h2 h3 h4 h5)⟩)
  rw [hs'] at he
  refine ⟨L', _, evalF_seq_ok2 a1 he, ?_, hF⟩
  simp only [Exp.cost] at hc ⊢
  have e : m * (1 + (1000 + 400 * B)) = m * (1001 + 400 * B) := by ring
  rw [e] at hc; omega

/-! ### `joinChunk` -/

/-- `joinChunk (cin x) lp w` (locals `w x lp`). The list of `w` is cleared first, so that the copy
starts from a row that exists. -/
def joinCS : Stm := cm{ rowReset(w); clear cin[w]; a := x; ‹copyS .cin›; lpar[w] := lp }

theorem joinCS_ok {κ : Caps} {s : Core} {L : Loc} {w x lp : Nat} (hw : L "w" = w) (hx : L "x" = x)
    (hlp : L "lp" = lp) (hwx : w ≠ x) (hwC : w < κ.tbl .C) (hz : rowZero κ s w) (hnp : notPrep s w)
    (hH : s.P.H + 1 ≤ κ.pw) (hwi : w < κ.lrec .cin) (hxi : x < κ.lrec .cin)
    (hcap : (s.cin.getX x).length ≤ κ.lcap .cin) (hwa : w < κ.arr .lpar) :
    ∃ L' c, evalF κ joinCS s L = .ok (joinS s (s.cin.getX x) lp w) L' c ∧
      c ≤ 20 + 40 * (s.cin.getX x).length ∧ ∀ r, r ≠ "a" → r ≠ "n" → r ≠ "j" → L' r = L r := by
  set s1 : Core := { s with path := s.path.setX w (Array.replicate (s.P.H + 1) NIL) }
  have e1 : evalF κ (.rowReset "w") s L = .ok s1 L 1 := by
    simp [evalF, Exp.ev, hw, hwC, hz, hnp, hH, s1]
  set s2 := LK.put s1 w [] .cin
  have e2 : evalF κ (.lclear .cin "w") s1 L = .ok s2 L 3 := by
    simp [evalF, Exp.ev, hw, LK.set, LK.recOk, LK.valid, hwi, s2, Exp.cost]
  have a3 := evalF_assign_ok (κ := κ) (s := s2) (L := L) (x := "a") (e := .var "x") (v := x) (by simp [Exp.ev, hx])
  set L3 := upd L "a" x
  have hv2w : LK.view s2 w .cin = [] := by
    rw [LK.view_put (by rfl) (by rfl)]; simp
  have hv2x : LK.view s2 x .cin = (s.cin.getX x).map fun e => (e, 0) := by
    rw [LK.view_put (by rfl) (by rfl)]; simp [Ne.symm hwx, LK.view, s1]
  have hid : LK.idOk s2 w .cin := by
    simp only [LK.idOk, s2, LK.put, size_setX']; omega
  obtain ⟨L4, c4, e4, hc4, hF4⟩ := copyS_ok (κ := κ) (k := .cin) (s := s2) (L := L3) (a := x) (w := w)
    (by simp [L3,
      OrderMaintenance.Machine.State.upd]) (by simp [L3, OrderMaintenance.Machine.State.upd,
      hw]) hwx hid (by rfl) hxi hwi
    (by rw [hv2w, hv2x]; simpa using hcap)
  rw [hv2w, hv2x, List.nil_append, LK.put_put] at e4
  have h4w : L4 "w" = w := by rw [hF4 "w" (by decide) (by decide)]; simp [L3, OrderMaintenance.Machine.State.upd, hw]
  have h4lp : L4 "lp" = lp := by rw [hF4 "lp" (by decide) (by decide)]; simp [L3, OrderMaintenance.Machine.State.upd, hlp]
  have e5 : evalF κ (.wr (.a .lpar) "w" "lp") (LK.put s1 w ((s.cin.getX x).map fun e => (e, 0)) .cin) L4 =
      .ok (joinS s (s.cin.getX x) lp w) L4 3 := by
    simp [evalF, Exp.ev, h4w, h4lp, Fld.set, hwa, AF.set, AF.get, LK.put, s1, joinS, Exp.cost]
    congr 1; induction s.cin.getX x <;> simp_all
  refine ⟨L4, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 a3 (evalF_seq_ok2 e4 e5))), ?_, ?_⟩
  · rw [hv2x, List.length_map] at hc4; simp only [Exp.cost]; omega
  · intro r h1 h2 h3
    rw [hF4 r h2 h3]; simp [L3, OrderMaintenance.Machine.State.upd, h1]

/-! ### The guarded tag write -/

/-- `guardedSetTag c t`: `t` must lie strictly between the tags of `c`'s neighbours. -/
def gstP : Proc where
  name := "guardedSetTag"
  params := ["c", "t"]
  rets := []
  body := cm{
    cp := C[c].prev
    if cp = 0 then skip else if C[cp].tag < t then skip else fail
    cn := C[c].next
    if cn = 0 then skip else if t < C[cn].tag then skip else fail
    C[c].tag := t }

theorem gstP_agree {κ : Caps} {s : Core} {L : Loc} {c t : Nat} (hc : L "c" = c) (ht : L "t" = t)
    (hcs : c < s.C.size) (hcT : c < κ.tbl .C) (hpT : (s.C.getX c).prev < κ.tbl .C)
    (hnT : (s.C.getX c).next < κ.tbl .C) (h : OrderMaintenance.Proof.TagOK s c t) :
    ∃ L' n, evalF κ gstP.body s L = .ok { s with C := s.C.modify c fun C => { C with tag := t } } L' n ∧
      n ≤ 40 := by
  obtain ⟨hp, hn⟩ := h
  set p := (s.C.getX c).prev
  set q := (s.C.getX c).next
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "cp") (e := .rd (.c .prev) "c") (v := p)
    (by simp [Exp.ev, hc, hcT, Fld.cap, Fld.get, CF.get, p])
  set L1 := upd L "cp" p
  have e2 : ∃ c2, evalF κ (.ite ("cp" =ₑ 0) .skip (.ite (.rd (.c .tag) "cp" <ₑ "t") .skip .fail)) s L1 =
      .ok s L1 c2 ∧ c2 ≤ 10 := by
    by_cases hp0 : p = 0
    · exact ⟨_, evalF_ite_t (v := 1) (by simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval, L1, OrderMaintenance.Machine.State.upd, hp0])
        one_ne_zero evalF_skip, by simp [Exp.cost]⟩
    · have hlt : (s.C.getX p).tag < t := hp (by simpa [NIL] using hp0)
      exact ⟨_, evalF_ite_f (by simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval, L1, OrderMaintenance.Machine.State.upd, hp0])
        (evalF_ite_t (v := 1) (by simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval, L1, OrderMaintenance.Machine.State.upd, hpT, Fld.cap,
          Fld.get, CF.get, ht, hlt]) one_ne_zero evalF_skip), by simp [Exp.cost]⟩
  obtain ⟨c2, e2, hc2⟩ := e2
  have a3 := evalF_assign_ok (κ := κ) (s := s) (L := L1) (x := "cn") (e := .rd (.c .next) "c") (v := q)
    (by simp [Exp.ev, L1, OrderMaintenance.Machine.State.upd, hc, hcT, Fld.cap, Fld.get, CF.get, q])
  set L3 := upd L1 "cn" q
  have e4 : ∃ c4, evalF κ (.ite ("cn" =ₑ 0) .skip (.ite ("t" <ₑ .rd (.c .tag) "cn") .skip .fail)) s L3 =
      .ok s L3 c4 ∧ c4 ≤ 10 := by
    by_cases hq0 : q = 0
    · exact ⟨_, evalF_ite_t (v := 1) (by simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval, L3, OrderMaintenance.Machine.State.upd, hq0])
        one_ne_zero evalF_skip, by simp [Exp.cost]⟩
    · have hlt : t < (s.C.getX q).tag := hn (by simpa [NIL] using hq0)
      exact ⟨_, evalF_ite_f (by simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval, L3, OrderMaintenance.Machine.State.upd, hq0])
        (evalF_ite_t (v := 1) (by simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval, L3, L1, OrderMaintenance.Machine.State.upd, hnT, Fld.cap,
          Fld.get, CF.get, ht, hlt]) one_ne_zero evalF_skip), by simp [Exp.cost]⟩
  obtain ⟨c4, e4, hc4⟩ := e4
  have e5 := evalF_wrC_ok (κ := κ) (s := s) (L := L3) (k := .tag) (i := .var "c") (e := .var "t") (j := c) (w := t)
    (by simp [Exp.ev, L3, L1, OrderMaintenance.Machine.State.upd,
      hc]) (by simp [Exp.ev, L3, L1, OrderMaintenance.Machine.State.upd, ht])
    hcs hcT rfl
  exact ⟨_, _, evalF_seq_ok2 a1 (evalF_seq_ok2 e2 (evalF_seq_ok2 a3 (evalF_seq_ok2 e4 e5))),
    by simp [Exp.cost]; omega⟩

/-! ### The parent's children: `x` becomes `y, x, z` -/

theorem replace1_eq3 (x a b : Nat) : ∀ (l : List Nat), x ∈ l →
    l.replace1 x [a, x, b] = (l.insertIdx (l.findIdx (· == x)) a).insertIdx (l.findIdx (· == x) + 2) b
  | [], h => by simp at h
  | y :: l, h => by
    simp only [List.replace1, List.findIdx_cons]
    by_cases hy : y = x
    · subst hy; simp
    · have hx : x ∈ l := by simp at h; tauto
      simp only [hy, ite_false, beq_iff_eq, cond_false]
      rw [replace1_eq3 x a b l hx]
      simp [List.insertIdx_succ_cons]

def childS : Stm := cm{
  r ← ‹findP .children›(lp, x)
  call ‹insertIdxP .children›(lp, r, y, 0)
  call ‹insertIdxP .children›(lp, r + 2, z, 0) }

theorem map_insertIdx_pair0 (l : List Nat) (i a : Nat) :
    (l.map fun e => (e, 0)).insertIdx i (a, 0) = (l.insertIdx i a).map fun e => (e, 0) := by
  rw [List.map_insertIdx]

theorem childS_ok {κ : Caps} {s : Core} {L : Loc} {lp x y z : Nat} (hlp : L "lp" = lp) (hx : L "x" = x)
    (hy : L "y" = y) (hz : L "z" = z) (hmem : x ∈ (s.nodes.getX lp).children) (hlpn : lp < s.nodes.size)
    (hlr : lp < κ.lrec .children) (hcap : (s.nodes.getX lp).children.length + 2 ≤ κ.lcap .children) :
    ∃ L' c, evalF κ childS s L = .ok { s with nodes := s.nodes.modify lp fun n =>
        { n with children := n.children.replace1 x [y, x, z] } } L' c ∧
      c ≤ 250 + 220 * (s.nodes.getX lp).children.length ∧ ∀ r, r ≠ "r" → L' r = L r := by
  set l := (s.nodes.getX lp).children
  set r := l.findIdx (· == x)
  have hr : r < l.length := List.findIdx_lt_length_of_exists ⟨x, hmem, by simp⟩
  have hview : LK.view s lp .children = l.map fun e => (e, 0) := rfl
  obtain ⟨Lf, cf, ef, hrf, hcf⟩ := findP_agree κ .children s
    (OrderMaintenance.Machine.State.setLocs (fun _ => 0) ["i", "x"] [lp, x]) (i := lp) (x := x)
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd])
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd]) hlr
  rw [hview, findIdx_pair0'] at hrf
  rw [hview, List.length_map] at hcf
  have e1 := evalF_call_ok (q := findP .children) (args := [.var "lp", .var "x"]) (ds := ["r"]) (L := L)
    (by simp [evList, Exp.ev, hlp, hx]) ef
  set L1 := OrderMaintenance.Machine.State.setLocs L ["r"] ((findP .children).rets.map Lf)
  have hL1 : ∀ q, q ≠ "r" → L1 q = L q := fun q h => by
    simp [L1, findP, OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd, h]
  have hL1r : L1 "r" = r := by simp [L1, OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd, findP, hrf]; rfl
  obtain ⟨L2', c2, e2', hc2⟩ := insertIdxP_agree κ .children s
    (OrderMaintenance.Machine.State.setLocs (fun _ => 0) ["i", "p", "a", "b"] [lp, r, y, 0]) (i := lp) (p := r) (a := y) (b := 0)
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd])
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd])
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd])
    (by simp [OrderMaintenance.Machine.State.setLocs,
      OrderMaintenance.Machine.State.upd]) (by simp [LK.recOk, hlpn]) hlr
    (by simp [LK.valid]) (by rw [hview, List.length_map]; omega) (by rw [hview, List.length_map]; omega)
  have e2 := evalF_call_ok (q := insertIdxP .children) (args := [.var "lp", .var "r", .var "y", 0]) (ds := [])
    (L := L1) (by simp [evList, Exp.ev, hL1r, hL1 "lp" (by decide), hlp, hL1 "y" (by decide), hy]) e2'
  rw [hview, map_insertIdx_pair0] at e2
  set s2 := LK.put s lp ((l.insertIdx r y).map fun e => (e, 0)) .children
  have hv2 : LK.view s2 lp .children = (l.insertIdx r y).map fun e => (e, 0) := by
    rw [LK.view_put (by simp [LK.recOk, hlpn]) (by simp [LK.valid])]; simp
  have hlen2 : (l.insertIdx r y).length = l.length + 1 := by
    simp [List.length_insertIdx, show r ≤ l.length by omega]
  obtain ⟨L3', c3, e3', hc3⟩ := insertIdxP_agree κ .children s2
    (OrderMaintenance.Machine.State.setLocs (fun _ => 0) ["i", "p", "a", "b"] [lp, r + 2, z, 0]) (i := lp) (p := r + 2) (a := z)
    (b := 0)
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd])
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd])
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd])
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd])
    (by rw [LK.recOk_put]; simp [LK.recOk, hlpn]) hlr
    (by simp [LK.valid]) (by rw [hv2, List.length_map]; omega) (by rw [hv2, List.length_map]; omega)
  set L2 := OrderMaintenance.Machine.State.setLocs L1 [] ((insertIdxP .children).rets.map L2')
  have e3 := evalF_call_ok (q := insertIdxP .children) (args := [.var "lp", "r" + 2, .var "z", 0]) (ds := [])
    (L := L2) (by
      simp [evList, Exp.ev, L2, OrderMaintenance.Machine.State.setLocs,
        OrderMaintenance.Machine.BinOp.eval, hL1r, hL1 "lp" (by decide), hlp,
        hL1 "z" (by decide), hz]) e3'
  rw [hv2, map_insertIdx_pair0, LK.put_put] at e3
  have hfin : LK.put s lp (((l.insertIdx r y).insertIdx (r + 2) z).map fun e => (e, 0)) .children =
      { s with nodes := s.nodes.modify lp fun n => { n with children := n.children.replace1 x [y, x, z] } } := by
    simp only [LK.put]
    congr 1
    apply Array.modify_congr_getX
    rw [replace1_eq3 x y z l hmem]
    simp [l, r, Function.comp_def]
  rw [hfin] at e3
  refine ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 e3), ?_, ?_⟩
  · rw [hv2, List.length_map, hlen2] at hc3
    rw [hview, List.length_map] at hc2
    simp only [Exp.cost, costList, List.map, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil,
      Exp.ofNat_def] at hc2 hc3 hcf ⊢
    omega
  · intro q hq
    simp only [OrderMaintenance.Machine.State.setLocs, insertIdxP, List.map, L2]
    exact hL1 q hq

/-! ### The reads of `insertAround` -/

/-- The labels and tags `insertAround x y z` reads (locals `x`): the tags `ty`, `tz` and the live
parent `lp`. -/
def iaPrepS : Stm := cm{
  p1 := path(x, 1)
  (f, f1) ← ‹lookupP .table›(p1, x)
  if f then skip else fail
  a ← roomP(p1, x, 1)
  b ← roomP(p1, x, 0)
  tx := C[x].tag
  if tx < f1 then fail
  lp := lpar[x]
  ty := tx ∸ f1 + a
  tz := tx ∸ f1 + b }

theorem rowOf_notPrep {s : Core} {c : Nat} (h : notPrep s c) : rowOf s c = s.path.getX c := by
  unfold rowOf; unfold notPrep at h; split
  · next pr hp => rw [hp] at h; simp only at h; rw [ite_eq_right h]
  · rfl

theorem idx?_mem {l : List Nat} {a i : Nat} (h : l.idx? a = some i) : a ∈ l := by
  unfold List.idx? at h
  rw [List.findIdx?_eq_some_iff_getElem] at h
  obtain ⟨hi, hp, -⟩ := h
  have ha : l[i] = a := by simpa using hp
  exact ha ▸ List.getElem_mem hi

theorem iaPrepS_ok {κ : Caps} {s : Core} {L : Loc} {x f1x i1 : Nat} (hLx : L "x" = x)
    (hroom : ∀ T ∈ s.cin.getX x, RoomOK s x T)
    (hf1 : (s.nodes.getX ((s.path.getX x).getX 1)).lab? x = some f1x)
    (hi1 : (s.cin.getX x).idx? ((s.path.getX x).getX 1) = some i1)
    (htx : f1x ≤ (s.C.getX x).tag) (hnp : notPrep s x) (hxC : x < κ.tbl .C) (hpw : 1 < κ.pw)
    (hxa : x < κ.arr .lpar) (hp1 : (s.path.getX x).getX 1 < κ.lrec .table) :
    ∃ L' c, evalF κ iaPrepS s L = .ok s L' c ∧ L' "ty" = OrderMaintenance.Proof.Top.tagY s x f1x i1 ∧
      L' "tz" = OrderMaintenance.Proof.Top.tagZ s x f1x i1 ∧ L' "lp" = s.lpar.getX x ∧
      c ≤ 400 + 60 * (s.nodes.getX ((s.path.getX x).getX 1)).table.length ∧
      ∀ r, r ≠ "p1" → r ≠ "f" → r ≠ "f1" → r ≠ "a" → r ≠ "b" → r ≠ "tx" → r ≠ "lp" → r ≠ "ty" → r ≠ "tz" →
        L' r = L r := by
  set p1 := (s.path.getX x).getX 1
  have hp1m : p1 ∈ s.cin.getX x := idx?_mem hi1
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "p1") (e := .prd "x" 1) (v := p1)
    (by simp [Exp.ev, hLx, hxC, hpw, rowOf_notPrep hnp, p1])
  set L1 := upd L "p1" p1
  have h1x : L1 "x" = x := by simp [L1, OrderMaintenance.Machine.State.upd, hLx]
  -- the label of `x` in its parent's table
  obtain ⟨Lf, cf, ef, hf, hv, -, -, hcf⟩ := lookupP_agree κ .table s
    (OrderMaintenance.Machine.State.setLocs (fun _ => 0) ["i", "x"] [p1, x]) (i := p1) (x := x)
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd])
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd]) hp1
  have hlk : lookup (LK.view s p1 .table) x = some f1x := hf1
  rw [hlk] at hf hv
  have e2 := evalF_call_ok (q := lookupP .table) (args := [.var "p1", .var "x"]) (ds := ["f", "f1"]) (L := L1)
    (by simp [evList, Exp.ev, L1, OrderMaintenance.Machine.State.upd, hLx]) ef
  set L2 := OrderMaintenance.Machine.State.setLocs L1 ["f", "f1"] ((lookupP .table).rets.map Lf)
  have h2f : L2 "f" = 1 := by simp [L2, lookupP, OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd, hf]
  have h2f1 : L2 "f1" = f1x := by simp [L2, lookupP, OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd, hv]
  have hL2 : ∀ r, r ≠ "f" → r ≠ "f1" → L2 r = L1 r := fun r h1 h2 => by
    simp [L2, lookupP, OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd,
      h1, h2]
  have h2x : L2 "x" = x := by rw [hL2 "x" (by decide) (by decide), h1x]
  have h2p : L2 "p1" = p1 := by rw [hL2 "p1" (by decide) (by decide)]; simp [L1, OrderMaintenance.Machine.State.upd]
  have e3 : evalF κ (.ite "f" .skip .fail) s L2 = .ok s L2 3 := by
    simp [evalF, Exp.ev, h2f, Exp.cost, Res.addCost]
  -- the two labels
  obtain ⟨-, La, ca, ea, hla, hca⟩ := roomP_agree κ s
    (OrderMaintenance.Machine.State.setLocs (fun _ => 0) ["t", "e", "bf"] [p1, x, 1]) (t := p1) (e := x) (before := true)
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd])
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd])
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd,
      b2n]) hp1 (roomNextTo_run' (hroom p1 hp1m) true)
  have e4 := evalF_call_ok (q := roomP) (args := [.var "p1", .var "x", 1]) (ds := ["a"]) (L := L2)
    (by simp [evList, Exp.ev, h2p, h2x]) ea
  set L4 := OrderMaintenance.Machine.State.setLocs L2 ["a"] (roomP.rets.map La)
  have hL4 : ∀ r, r ≠ "a" → L4 r = L2 r := fun r h => by
    simp [L4, roomP, OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd, h]
  obtain ⟨-, Lb, cb, eb, hlb, hcb⟩ := roomP_agree κ s
    (OrderMaintenance.Machine.State.setLocs (fun _ => 0) ["t", "e", "bf"] [p1, x, 0]) (t := p1) (e := x) (before := false)
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd])
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd])
    (by simp [OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd,
      b2n]) hp1 (roomNextTo_run' (hroom p1 hp1m) false)
  have e5 := evalF_call_ok (q := roomP) (args := [.var "p1", .var "x", 0]) (ds := ["b"]) (L := L4)
    (by simp [evList, Exp.ev, hL4 "p1" (by decide), hL4 "x" (by decide), h2p, h2x]) eb
  set L5 := OrderMaintenance.Machine.State.setLocs L4 ["b"] (roomP.rets.map Lb)
  have hL5 : ∀ r, r ≠ "b" → L5 r = L4 r := fun r h => by
    simp [L5, roomP, OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd, h]
  set la := roomL s.P.beta (s.nodes.getX p1).table x true
  set lb := roomL s.P.beta (s.nodes.getX p1).table x false
  have h5a : L5 "a" = la := by rw [hL5 "a" (by decide)]; simp [L4, roomP, OrderMaintenance.Machine.State.setLocs,
    OrderMaintenance.Machine.State.upd, hla]
  have h5b : L5 "b" = lb := by simp [L5, roomP, OrderMaintenance.Machine.State.setLocs, OrderMaintenance.Machine.State.upd, hlb]
  have hL5' : ∀ r, r ≠ "a" → r ≠ "b" → r ≠ "f" → r ≠ "f1" → L5 r = L1 r := fun r h1 h2 h3 h4 => by
    rw [hL5 r h2, hL4 r h1, hL2 r h3 h4]
  have h5x : L5 "x" = x := by rw [hL5' "x" (by decide) (by decide) (by decide) (by decide), h1x]
  have h5f1 : L5 "f1" = f1x := by rw [hL5 "f1" (by decide), hL4 "f1" (by decide), h2f1]
  -- the tag of `x`
  set tx := (s.C.getX x).tag
  have a6 := evalF_assign_ok (κ := κ) (s := s) (L := L5) (x := "tx") (e := .rd (.c .tag) "x") (v := tx)
    (by simp [Exp.ev, h5x, hxC, Fld.cap, Fld.get, CF.get, tx])
  set L6 := upd L5 "tx" tx
  have e7 : evalF κ (.ite ("tx" <ₑ "f1") .fail .skip) s L6 = .ok s L6 5 := by
    have : ¬ tx < f1x := by omega
    simp [evalF, Exp.ev, L6, OrderMaintenance.Machine.State.upd, h5f1,
      OrderMaintenance.Machine.BinOp.eval, this, Exp.cost, Res.addCost]
  have a8 := evalF_assign_ok (κ := κ) (s := s) (L := L6) (x := "lp") (e := .rd (.a .lpar) "x") (v := s.lpar.getX x)
    (by simp [Exp.ev, L6, OrderMaintenance.Machine.State.upd, h5x, hxa, Fld.cap, Fld.get, AF.get])
  set L8 := upd L6 "lp" (s.lpar.getX x)
  have hm : (Exp.monus "tx" "f1").ev κ s L8 = some (tx - f1x) :=
    Exp.ev_monus κ s L8 (by simp [Exp.ev, L8, L6, OrderMaintenance.Machine.State.upd])
      (by simp [Exp.ev, L8, L6, OrderMaintenance.Machine.State.upd, h5f1])
  have a9 := evalF_assign_ok (κ := κ) (s := s) (L := L8) (x := "ty") (e := Exp.monus "tx" "f1" + "a")
    (v := tx - f1x + la) (by simp [Exp.ev, hm, OrderMaintenance.Machine.BinOp.eval, L8, L6, OrderMaintenance.Machine.State.upd, h5a])
  set L9 := upd L8 "ty" (tx - f1x + la)
  have hm' : (Exp.monus "tx" "f1").ev κ s L9 = some (tx - f1x) :=
    Exp.ev_monus κ s L9 (by simp [Exp.ev, L9, L8, L6, OrderMaintenance.Machine.State.upd])
      (by simp [Exp.ev, L9, L8, L6, OrderMaintenance.Machine.State.upd, h5f1])
  have a10 := evalF_assign_ok (κ := κ) (s := s) (L := L9) (x := "tz") (e := Exp.monus "tx" "f1" + "b")
    (v := tx - f1x + lb) (by simp [Exp.ev, hm', OrderMaintenance.Machine.BinOp.eval, L9, L8, L6, OrderMaintenance.Machine.State.upd, h5b])
  have hty : OrderMaintenance.Proof.Top.tagY s x f1x i1 = tx - f1x + la := by
    unfold OrderMaintenance.Proof.Top.tagY; rw [idx?_getD_map hi1]
  have htz : OrderMaintenance.Proof.Top.tagZ s x f1x i1 = tx - f1x + lb := by
    unfold OrderMaintenance.Proof.Top.tagZ; rw [idx?_getD_map hi1]
  refine ⟨_, _, evalF_seq_ok2 a1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 (evalF_seq_ok2 e4 (evalF_seq_ok2 e5
    (evalF_seq_ok2 a6 (evalF_seq_ok2 e7 (evalF_seq_ok2 a8 (evalF_seq_ok2 a9 a10)))))))),
    by simp [L9, OrderMaintenance.Machine.State.upd,
      hty], by simp [OrderMaintenance.Machine.State.upd, htz],
    by simp [L9, L8, OrderMaintenance.Machine.State.upd], ?_, ?_⟩
  · simp only [LK.view] at hcf
    simp only [Exp.cost, costList, List.map, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil,
      Exp.ofNat_def, Exp.monus, Exp.max, Exp.sub_def, Exp.add_def, Exp.mul_def] at hca hcb hcf ⊢
    omega
  · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9
    simp only [L9, L8, L6, OrderMaintenance.Machine.State.upd, ite_eq_right h6, ite_eq_right h7,
      ite_eq_right h8, ite_eq_right h9]
    rw [hL5' r h4 h5 h2 h3]; simp [L1, OrderMaintenance.Machine.State.upd, h1]

/-! ### `insertAround` -/

/-- `insertAround x y z` (locals `x y z`). -/
def insertAroundS : Stm := cm{
  iaPrepS
  call gstP(y, ty)
  call gstP(z, tz)
  cinsS
  w := y; joinCS
  w := z; joinCS
  childS }

theorem fold_cStep_children (S0 : Core) (x y z : Nat) (g : Nat → List Nat) :
    ∀ (l : List Nat) (a : Array Node), (∀ u, (a.getX u).children = g u) →
      ∀ u, ((l.foldl (cStep S0 x y z) a).getX u).children = g u
  | [], _, h, u => h u
  | T :: l, a, h, u => by
    simp only [List.foldl_cons]
    refine fold_cStep_children S0 x y z g l _ (fun u' => ?_) u
    simp only [cStep, getX_modify']
    split
    · next hh => rw [← h u']; simp [aroundF, setTS]
    · exact h u'

theorem cJ_children (S0 : Core) (x y z j u : Nat) :
    ((cJ S0 x y z j).nodes.getX u).children = (S0.nodes.getX u).children :=
  fold_cStep_children S0 x y z (fun u => (S0.nodes.getX u).children) _ _ (fun _ => rfl) u

theorem rowZero_joinS {κ : Caps} {X : Core} {tabs : List Nat} {lp w c : Nat} (hcw : c ≠ w) (h : rowZero κ X c) :
    rowZero κ (joinS X tabs lp w) c := by
  intro j hj
  have := h j hj
  unfold rowOf at this ⊢
  simp only [joinS] at this ⊢
  split
  · next pr hp =>
    rw [hp] at this; simp only at this
    by_cases hc : c = pr.chunk
    · rw [ite_eq_left hc] at this ⊢; exact this
    · rw [ite_eq_right hc] at this ⊢; rw [getX_setX', ite_eq_right hcw]; exact this
  · next hp => rw [hp] at this; simp only at this ⊢; rw [getX_setX', ite_eq_right hcw]; exact this

theorem insertAroundS_ok {κ : Caps} {s : Core} {L : Loc} {x y z f1x i1 B : Nat}
    (hLx : L "x" = x) (hLy : L "y" = y) (hLz : L "z" = z)
    (hroom : ∀ T ∈ s.cin.getX x, RoomOK s x T) (hnd : (s.cin.getX x).Nodup) (hyx : y ≠ x)
    (hf1 : (s.nodes.getX ((s.path.getX x).getX 1)).lab? x = some f1x)
    (hi1 : (s.cin.getX x).idx? ((s.path.getX x).getX 1) = some i1)
    (htx : f1x ≤ (s.C.getX x).tag)
    (hlp : x ∈ (s.nodes.getX (s.lpar.getX x)).children)
    (hgy : OrderMaintenance.Proof.TagOK s y (tagY s x f1x i1))
    (hgz : OrderMaintenance.Proof.TagOK { s with C := s.C.modify y fun C => { C with tag := tagY s x f1x i1 } } z (tagZ s x f1x i1))
    (hzx : z ≠ x) (hyz : y ≠ z)
    (hnpx : notPrep s x) (hnpy : notPrep s y) (hnpz : notPrep s z) (hxC : x < κ.tbl .C) (hpw : 1 < κ.pw)
    (hH : s.P.H + 1 ≤ κ.pw) (hxa : x < κ.arr .lpar) (hya : y < κ.arr .lpar) (hza : z < κ.arr .lpar)
    (hys : y < s.C.size) (hzs : z < s.C.size) (hyC : y < κ.tbl .C) (hzC : z < κ.tbl .C)
    (hyP : (s.C.getX y).prev < κ.tbl .C) (hyN : (s.C.getX y).next < κ.tbl .C)
    (hzP : (s.C.getX z).prev < κ.tbl .C) (hzN : (s.C.getX z).next < κ.tbl .C)
    (hry : rowZero κ s y) (hrz : rowZero κ s z)
    (hxi : x < κ.lrec .cin) (hyi : y < κ.lrec .cin) (hzi : z < κ.lrec .cin)
    (hcin : (s.cin.getX x).length ≤ κ.lcap .cin)
    (hcapT : ∀ T ∈ s.cin.getX x, T < κ.lrec .table ∧ T < κ.lrec .side ∧ T < κ.tbl .N ∧
      (s.nodes.getX T).table.length + 2 ≤ κ.lcap .table ∧ (s.nodes.getX T).side.length + 2 ≤ κ.lcap .side)
    (hB : ∀ T ∈ s.cin.getX x, (s.nodes.getX T).table.length ≤ B ∧ (s.nodes.getX T).side.length ≤ B)
    (hlr : s.lpar.getX x < κ.lrec .children)
    (hccap : (s.nodes.getX (s.lpar.getX x)).children.length + 2 ≤ κ.lcap .children) :
    ∃ L' c, evalF κ insertAroundS s L = .ok (insFinS (tagsS s y z (tagY s x f1x i1) (tagZ s x f1x i1)) x y z
        fun T => (roomL s.P.beta (s.nodes.getX T).table x true, roomL s.P.beta (s.nodes.getX T).table x false)) L' c ∧
      c ≤ 1200 + 60 * B + (s.cin.getX x).length * (1100 + 400 * B) +
        220 * (s.nodes.getX (s.lpar.getX x)).children.length ∧
      L' "x" = x ∧ L' "y" = y ∧ L' "z" = z := by
  set ty := tagY s x f1x i1
  set tz := tagZ s x f1x i1
  set tabs := s.cin.getX x
  set lp := s.lpar.getX x
  have hp1m : (s.path.getX x).getX 1 ∈ tabs := idx?_mem hi1
  -- the reads
  obtain ⟨L1, c1, e1, h1y, h1z, h1lp, hc1, hF1⟩ := iaPrepS_ok (κ := κ) (L := L) hLx hroom hf1 hi1 htx hnpx hxC hpw
    hxa (hcapT _ hp1m).1
  have h1 : ∀ r, r = "x" ∨ r = "y" ∨ r = "z" ∨ r = "w" → L1 r = L r := by
    intro r hr
    apply hF1 <;> rcases hr with rfl | rfl | rfl | rfl <;> decide
  -- the tags
  set sY : Core := { s with C := s.C.modify y fun C => { C with tag := ty } }
  obtain ⟨Lg, cg, eg, hcg⟩ := gstP_agree (κ := κ) (s := s)
    (L := OrderMaintenance.Machine.State.setLocs (fun _ => 0) ["c", "t"] [y, ty]) (c := y) (t := ty)
    (by simp [OrderMaintenance.Machine.State.setLocs,
      OrderMaintenance.Machine.State.upd]) (by simp [OrderMaintenance.Machine.State.setLocs,
      OrderMaintenance.Machine.State.upd])
    hys hyC hyP hyN hgy
  have e2 := evalF_call_ok (q := gstP) (args := [.var "y", .var "ty"]) (ds := []) (L := L1)
    (by simp [evList, Exp.ev, h1 "y" (by simp), hLy, h1y, ty]) eg
  have hzY : sY.C.getX z = s.C.getX z := by simp only [sY, getX_modify']; rw [ite_eq_right (fun h => hyz h.1.symm)]
  obtain ⟨Lg', cg', eg', hcg'⟩ := gstP_agree (κ := κ) (s := sY)
    (L := OrderMaintenance.Machine.State.setLocs (fun _ => 0) ["c", "t"] [z, tz]) (c := z) (t := tz)
    (by simp [OrderMaintenance.Machine.State.setLocs,
      OrderMaintenance.Machine.State.upd]) (by simp [OrderMaintenance.Machine.State.setLocs,
      OrderMaintenance.Machine.State.upd])
    (by simp [sY, hzs]) hzC (by rw [hzY]; exact hzP) (by rw [hzY]; exact hzN) hgz
  set L2 := OrderMaintenance.Machine.State.setLocs L1 [] (gstP.rets.map Lg)
  have e3 := evalF_call_ok (q := gstP) (args := [.var "z", .var "tz"]) (ds := []) (L := L2)
    (by simp [evList, Exp.ev, L2, OrderMaintenance.Machine.State.setLocs, h1 "z" (by simp), hLz,
      h1z, tz]) eg'
  set S0 := tagsS s y z ty tz
  have hS0 : ({ sY with C := sY.C.modify z fun C => { C with tag := tz } } : Core) = S0 := rfl
  rw [hS0] at e3
  set L3 := OrderMaintenance.Machine.State.setLocs L2 [] (gstP.rets.map Lg')
  have h3 : ∀ r, L3 r = L1 r := fun r => rfl
  -- the tables
  obtain ⟨L4, c4, e4, hc4, hF4⟩ := cinsS_ok (κ := κ) (S0 := S0) (L := L3) (x := x) (y := y) (z := z) (B := B)
    hnd hyx hroom (by rw [h3, h1 "x" (by simp), hLx]) (by rw [h3, h1 "y" (by simp), hLy])
    (by rw [h3, h1 "z" (by simp), hLz]) hxi hcapT hB
  set J0 := cJ S0 x y z tabs.length
  have h4 : ∀ r, r = "x" ∨ r = "y" ∨ r = "z" ∨ r = "lp" → L4 r = L1 r := by
    intro r hr
    rw [hF4 r (by rcases hr with rfl | rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl <;> decide), h3]
  -- `y` joins
  have a5 := evalF_assign_ok (κ := κ) (s := J0) (L := L4) (x := "w") (e := .var "y") (v := y)
    (by simp [Exp.ev, h4 "y" (by simp), h1 "y" (by simp), hLy])
  set L5 := upd L4 "w" y
  have h5 : ∀ r, r = "x" ∨ r = "y" ∨ r = "z" ∨ r = "lp" → L5 r = L1 r := by
    intro r hr; simp only [L5, OrderMaintenance.Machine.State.upd]
    rw [ite_eq_right (by rcases hr with rfl | rfl | rfl | rfl <;> decide)]; exact h4 r hr
  obtain ⟨L6, c6, e6, hc6, hF6⟩ := joinCS_ok (κ := κ) (s := J0) (L := L5) (w := y) (x := x) (lp := lp)
    (by simp [L5,
      OrderMaintenance.Machine.State.upd]) (by rw [h5 "x" (by simp), h1 "x" (by simp), hLx])
    (by rw [h5 "lp" (by simp), h1lp]) hyx hyC hry hnpy hH hyi hxi hcin hya
  set J1 := joinS J0 tabs lp y
  have h6 : ∀ r, r = "x" ∨ r = "y" ∨ r = "z" ∨ r = "lp" → L6 r = L1 r := by
    intro r hr
    rw [hF6 r (by rcases hr with rfl | rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl <;> decide)]
    exact h5 r hr
  -- `z` joins
  have a7 := evalF_assign_ok (κ := κ) (s := J1) (L := L6) (x := "w") (e := .var "z") (v := z)
    (by simp [Exp.ev, h6 "z" (by simp), h1 "z" (by simp), hLz])
  set L7 := upd L6 "w" z
  have h7 : ∀ r, r = "x" ∨ r = "y" ∨ r = "z" ∨ r = "lp" → L7 r = L1 r := by
    intro r hr; simp only [L7, OrderMaintenance.Machine.State.upd]
    rw [ite_eq_right (by rcases hr with rfl | rfl | rfl | rfl <;> decide)]; exact h6 r hr
  have hJ1x : J1.cin.getX x = tabs := by simp only [J1, joinS]; rw [getX_setX', ite_eq_right (Ne.symm hyx)]; rfl
  obtain ⟨L8, c8, e8, hc8, hF8⟩ := joinCS_ok (κ := κ) (s := J1) (L := L7) (w := z) (x := x) (lp := lp)
    (by simp [L7,
      OrderMaintenance.Machine.State.upd]) (by rw [h7 "x" (by simp), h1 "x" (by simp), hLx])
    (by rw [h7 "lp" (by simp),
      h1lp]) hzx hzC (rowZero_joinS (Ne.symm hyz) hrz) hnpz (show s.P.H + 1 ≤ κ.pw from hH)
    hzi hxi (by rw [hJ1x]; exact hcin) hza
  rw [hJ1x] at e8 hc8
  set J2 := joinS J1 tabs lp z
  have h8 : ∀ r, r = "x" ∨ r = "y" ∨ r = "z" ∨ r = "lp" → L8 r = L1 r := by
    intro r hr
    rw [hF8 r (by rcases hr with rfl | rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl <;> decide)]
    exact h7 r hr
  -- the parent's children
  have hJ2c : (J2.nodes.getX lp).children = (s.nodes.getX lp).children := cJ_children S0 x y z _ lp
  have hlpn : lp < s.nodes.size := by
    by_contra hc
    have : s.nodes.getX lp = default := by unfold Array.getX Array.getD; rw [dite_eq_right hc]
    rw [this] at hlp; exact (List.not_mem_nil (a := x)) hlp
  obtain ⟨L9, c9, e9, hc9, hF9⟩ := childS_ok (κ := κ) (s := J2) (L := L8) (lp := lp) (x := x) (y := y) (z := z)
    (by rw [h8 "lp" (by simp), h1lp]) (by rw [h8 "x" (by simp), h1 "x" (by simp), hLx])
    (by rw [h8 "y" (by simp), h1 "y" (by simp),
      hLy]) (by rw [h8 "z" (by simp), h1 "z" (by simp), hLz])
    (by rw [hJ2c]; exact hlp) (by simp only [J2, J1, joinS, J0, cJ_size]; exact hlpn) hlr (by rw [hJ2c]; exact hccap)
  rw [hJ2c] at hc9
  have hfin : ({ J2 with nodes := J2.nodes.modify lp fun n => { n with children := n.children.replace1 x [y, x, z] } } :
      Core) = insFinS S0 x y z fun T => (roomL s.P.beta (s.nodes.getX T).table x true,
        roomL s.P.beta (s.nodes.getX T).table x false) := by
    have htk : (S0.cin.getX x).take tabs.length = tabs := List.take_of_length_le (le_refl _)
    simp only [J2, J1, J0, cJ, htk]
    rfl
  rw [hfin] at e9
  refine ⟨L9, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 (evalF_seq_ok2 e4 (evalF_seq_ok2 a5
    (evalF_seq_ok2 e6 (evalF_seq_ok2 a7 (evalF_seq_ok2 e8 e9))))))), ?_, ?_, ?_, ?_⟩
  · have hp1B := (hB _ hp1m).1
    have e : tabs.length * (1100 + 400 * B) = tabs.length * (1001 + 400 * B) + 99 * tabs.length := by ring
    have hc4' : c4 ≤ 5 + tabs.length * (1001 + 400 * B) := hc4
    have hc6' : c6 ≤ 20 + 40 * tabs.length := hc6
    simp only [Exp.cost, costList, List.map, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil]
    omega
  · rw [hF9 "x" (by decide), h8 "x" (by simp), h1 "x" (by simp), hLx]
  · rw [hF9 "y" (by decide), h8 "y" (by simp), h1 "y" (by simp), hLy]
  · rw [hF9 "z" (by decide), h8 "z" (by simp), h1 "z" (by simp), hLz]

/-! ### `linkChunkPair` and `markSplit` -/

/-- Two writes to the same chunk. -/
theorem evalF_wrC2 {κ : Caps} {s : Core} {L : Loc} {k1 k2 : CF} {i e1 e2 : Exp} {j w1 w2 : Nat}
    (hi : ∀ S : Core, i.ev κ S L = some j) (he1 : ∀ S : Core, e1.ev κ S L = some w1)
    (he2 : ∀ S : Core, e2.ev κ S L = some w2) (hj : j < s.C.size) (hc : j < κ.tbl .C)
    (hk1 : k1.ok w1 = true) (hk2 : k2.ok w2 = true) :
    evalF κ (.wcF k1 i e1;; .wcF k2 i e2) s L =
      .ok { s with C := s.C.modify j fun C => CF.set (CF.set C w1 k1) w2 k2 } L
        (1 + i.cost + e1.cost + (1 + i.cost + e2.cost)) := by
  have w1' := evalF_wrC_ok (κ := κ) (s := s) (L := L) (k := k1) (i := i) (e := e1) (j := j) (w := w1) (hi _) (he1 _)
    hj hc hk1
  have w2' := evalF_wrC_ok (κ := κ) (s := { s with C := s.C.modify j (CF.set · w1 k1) }) (L := L) (k := k2) (i := i)
    (e := e2) (j := j) (w := w2) (hi _) (he2 _) (by simp [hj]) hc hk2
  rw [Array.modify_modify_same] at w2'
  simp only [Stm.wcF]; exact evalF_seq_ok2 w1' w2'

theorem ev_var_const {κ : Caps} {L : Loc} {r : Reg} {v : Nat} (h : L r = v) :
    ∀ S : Core, (Exp.var r).ev κ S L = some v := fun _ => by simp [Exp.ev, h]

theorem ev_lit_const {κ : Caps} {L : Loc} (v : Nat) : ∀ S : Core, (Exp.lit v).ev κ S L = some v := fun _ => rfl

def lcpY : Stm := cm{ C[y].prev := xp; C[y].next := x }
def lcpP : Stm := cm{ if xp = 0 then S.firstChunk := y else C[xp].next := y }
def lcpZ : Stm := cm{ C[z].prev := x; C[z].next := xn }
def lcpN : Stm := cm{ if xn = 0 then skip else C[xn].prev := z }
def lcpX : Stm := cm{ C[x].prev := y; C[x].next := z }
/-- `linkChunkPair x y z`: `y`, `z` go before and after `x` in the chunk list (locals `x y z`). -/
def linkChunkPairS : Stm := cm{ xp := C[x].prev; xn := C[x].next; lcpY; lcpP; lcpZ; lcpN; lcpX }

theorem linkChunkPairS_ok {κ : Caps} {s : Core} {L : Loc} {x y z : Nat} (hx : L "x" = x) (hy : L "y" = y)
    (hz : L "z" = z) (hxs : x < s.C.size) (hys : y < s.C.size) (hzs : z < s.C.size) (hC : s.C.size ≤ κ.tbl .C)
    (hp : (s.C.getX x).prev ≠ NIL → (s.C.getX x).prev < s.C.size)
    (hn : (s.C.getX x).next ≠ NIL → (s.C.getX x).next < s.C.size) :
    ∃ L' c, evalF κ linkChunkPairS s L = .ok (linkChunkPair s x y z) L' c ∧ c ≤ 60 ∧
      ∀ r, r ≠ "xp" → r ≠ "xn" → L' r = L r := by
  set p := (s.C.getX x).prev
  set n := (s.C.getX x).next
  have hxT : x < κ.tbl .C := by omega
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "xp") (e := .cF .prev "x") (v := p)
    (by simp [Exp.cF, Exp.ev, hx, hxT, Fld.cap, Fld.get, CF.get, p])
  set L1 := upd L "xp" p
  have a2 := evalF_assign_ok (κ := κ) (s := s) (L := L1) (x := "xn") (e := .cF .next "x") (v := n)
    (by simp [Exp.cF, Exp.ev, L1, OrderMaintenance.Machine.State.upd, hx, hxT, Fld.cap, Fld.get,
      CF.get, n])
  set L2 := upd L1 "xn" n
  have hF2 : ∀ r, r ≠ "xp" → r ≠ "xn" → L2 r = L r := fun r h1 h2 => by simp [L2, L1, OrderMaintenance.Machine.State.upd, h1, h2]
  have h2x : L2 "x" = x := by rw [hF2 "x" (by decide) (by decide), hx]
  have h2y : L2 "y" = y := by rw [hF2 "y" (by decide) (by decide), hy]
  have h2z : L2 "z" = z := by rw [hF2 "z" (by decide) (by decide), hz]
  have h2p : L2 "xp" = p := by simp [L2, L1, OrderMaintenance.Machine.State.upd]
  have h2n : L2 "xn" = n := by simp [L2, OrderMaintenance.Machine.State.upd]
  -- `y`
  set S1 : Core := { s with C := s.C.modify y fun C => { C with prev := p, next := x } }
  have e3 : evalF κ lcpY s L2 = .ok S1 L2 6 := by
    have := evalF_wrC2 (κ := κ) (s := s) (L := L2) (k1 := .prev) (k2 := .next) (i := .var "y") (e1 := .var "xp")
      (e2 := .var "x") (ev_var_const h2y) (ev_var_const h2p) (ev_var_const h2x) hys (by omega) rfl rfl
    exact this
  -- the predecessor of `x`
  set S2 : Core := if p = 0 then { S1 with firstChunk := y } else { S1 with C := S1.C.modify p fun C => { C with next := y } }
  have e4 : ∃ c4, evalF κ lcpP S1 L2 = .ok S2 L2 c4 ∧ c4 ≤ 10 := by
    by_cases hp0 : p = 0
    · have w := evalF_wrS_ok (κ := κ) (s := S1) (L := L2) (k := .firstChunk) (e := .var "y") (w := y)
        (by simp [Exp.ev, h2y]) rfl
      have hS2 : S2 = SF.set S1 y .firstChunk := by simp only [S2, ite_eq_left hp0]; rfl
      rw [← hS2] at w
      exact ⟨_, evalF_ite_t (v := 1) (by simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval, h2p, hp0]) one_ne_zero
        (by simp only [Stm.wsc]; exact w), by simp [Exp.cost]⟩
    · have hps : p < s.C.size := hp hp0
      have w := evalF_wrC_ok (κ := κ) (s := S1) (L := L2) (k := .next) (i := .var "xp") (e := .var "y") (j := p) (w := y)
        (by simp [Exp.ev, h2p]) (by simp [Exp.ev, h2y]) (by simp [S1, hps]) (by omega) rfl
      have hS2 : S2 = { S1 with C := S1.C.modify p (CF.set · y .next) } := by simp only [S2, ite_eq_right hp0]; rfl
      rw [← hS2] at w
      exact ⟨_, evalF_ite_f (by simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval, h2p, hp0]) (by simp only [Stm.wcF]; exact w),
        by simp [Exp.cost]⟩
  obtain ⟨c4, e4, hc4⟩ := e4
  have hS2C : S2.C.size = s.C.size := by simp only [S2, S1]; split <;> simp
  -- `z`
  set S3 : Core := { S2 with C := S2.C.modify z fun C => { C with prev := x, next := n } }
  have e5 : evalF κ lcpZ S2 L2 = .ok S3 L2 6 := by
    have := evalF_wrC2 (κ := κ) (s := S2) (L := L2) (k1 := .prev) (k2 := .next) (i := .var "z") (e1 := .var "x")
      (e2 := .var "xn") (ev_var_const h2z) (ev_var_const h2x) (ev_var_const h2n) (by omega) (by omega) rfl rfl
    exact this
  -- the successor of `x`
  set S4 : Core := if n = 0 then S3 else { S3 with C := S3.C.modify n fun C => { C with prev := z } }
  have e6 : ∃ c6, evalF κ lcpN S3 L2 = .ok S4 L2 c6 ∧ c6 ≤ 10 := by
    by_cases hn0 : n = 0
    · have hS4 : S4 = S3 := by simp only [S4, ite_eq_left hn0]
      rw [hS4]
      exact ⟨_, evalF_ite_t (v := 1) (by simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval, h2n, hn0]) one_ne_zero evalF_skip,
        by simp [Exp.cost]⟩
    · have hns : n < s.C.size := hn hn0
      have w := evalF_wrC_ok (κ := κ) (s := S3) (L := L2) (k := .prev) (i := .var "xn") (e := .var "z") (j := n) (w := z)
        (by simp [Exp.ev, h2n]) (by simp [Exp.ev, h2z]) (by simp [S3, hS2C, hns]) (by omega) rfl
      have hS4 : S4 = { S3 with C := S3.C.modify n (CF.set · z .prev) } := by simp only [S4, ite_eq_right hn0]; rfl
      rw [← hS4] at w
      exact ⟨_, evalF_ite_f (by simp [Exp.ev, OrderMaintenance.Machine.BinOp.eval, h2n, hn0]) (by simp only [Stm.wcF]; exact w),
        by simp [Exp.cost]⟩
  obtain ⟨c6, e6, hc6⟩ := e6
  have hS4C : S4.C.size = s.C.size := by simp only [S4, S3]; split <;> simp [hS2C]
  -- `x`
  have e7 := evalF_wrC2 (κ := κ) (s := S4) (L := L2) (k1 := .prev) (k2 := .next) (i := .var "x") (e1 := .var "y")
      (e2 := .var "z") (ev_var_const h2x) (ev_var_const h2y) (ev_var_const h2z) (by omega) hxT rfl rfl
  have hfin : ({ S4 with C := S4.C.modify x fun C => CF.set (CF.set C y .prev) z .next } : Core) =
      linkChunkPair s x y z := by
    unfold linkChunkPair
    by_cases hp0 : p = 0 <;> by_cases hn0 : n = 0 <;>
      simp [S4, S3, S2, S1, hp0, hn0, p, n, NIL] <;> rfl
  rw [hfin] at e7
  refine ⟨L2, _, evalF_seq_ok2 a1 (evalF_seq_ok2 a2 (evalF_seq_ok2 e3 (evalF_seq_ok2 e4 (evalF_seq_ok2 e5
    (evalF_seq_ok2 e6 e7))))), ?_, hF2⟩
  simp only [Exp.cost, Exp.cF] at hc4 hc6 ⊢; omega

def msX : Stm := cm{ C[x].st := 2; C[x].l := y; C[x].r := z }
def msY : Stm := cm{ C[y].st := 1; C[y].src := x }
def msZ : Stm := cm{ C[z].st := 1; C[z].src := x }
/-- `markSplit x y z job` for the job `insertAround` returns (locals `x y z`). -/
def markSplitS : Stm := cm{ msX; msY; msZ; jobSet(x, y, z, 0, 1, 0, 0, 0) }

theorem markSplitS_ok {κ : Caps} {t : Core} {L : Loc} {x y z : Nat} (hx : L "x" = x) (hy : L "y" = y)
    (hz : L "z" = z) (hxs : x < t.C.size) (hys : y < t.C.size) (hzs : z < t.C.size) (hC : t.C.size ≤ κ.tbl .C) :
    evalF κ markSplitS t L = .ok (OrderMaintenance.Proof.markState t x y z { x := x, y := y, z := z, pc := .copy 1 }) L 57 := by
  have w1 := evalF_wrC_ok (κ := κ) (s := t) (L := L) (k := .st) (i := .var "x") (e := (2 : Exp)) (j := x) (w := 2)
    (by simp [Exp.ev, hx]) rfl hxs (by omega) rfl
  set t0 : Core := { t with C := t.C.modify x (CF.set · 2 .st) }
  have w2 := evalF_wrC2 (κ := κ) (s := t0) (L := L) (k1 := .l) (k2 := .r) (i := .var "x") (e1 := .var "y")
      (e2 := .var "z") (ev_var_const hx) (ev_var_const hy) (ev_var_const hz) (by simp [t0, hxs]) (by omega) rfl rfl
  set t1 : Core := { t with C := t.C.modify x fun C => { C with st := .splitting, l := y, r := z } }
  have h1 : ({ t0 with C := t0.C.modify x fun C => CF.set (CF.set C y .l) z .r } : Core) = t1 := by
    simp only [t0, t1, Array.modify_modify_same]; rfl
  rw [h1] at w2
  have e1 : evalF κ msX t L = .ok t1 L 9 := by
    simp only [msX, Stm.wcF] at w1 w2 ⊢; exact evalF_seq_ok2 w1 w2
  have e2 := evalF_wrC2 (κ := κ) (s := t1) (L := L) (k1 := .st) (k2 := .src) (i := .var "y") (e1 := (1 : Exp))
      (e2 := .var "x") (ev_var_const hy) (ev_lit_const 1) (ev_var_const hx) (by simp [t1, hys]) (by omega) rfl rfl
  set t2 : Core := { t1 with C := t1.C.modify y fun C => { C with st := .overflow, src := x } }
  have e3 := evalF_wrC2 (κ := κ) (s := t2) (L := L) (k1 := .st) (k2 := .src) (i := .var "z") (e1 := (1 : Exp))
      (e2 := .var "x") (ev_var_const hz) (ev_lit_const 1) (ev_var_const hx) (by simp [t2, t1, hzs]) (by omega) rfl rfl
  set t3 : Core := { t2 with C := t2.C.modify z fun C => { C with st := .overflow, src := x } }
  have e4 : evalF κ (.jobSet "x" "y" "z" 0 1 0 0 0) t3 L =
      .ok (OrderMaintenance.Proof.markState t x y z { x := x, y := y, z := z, pc := .copy 1 }) L 36 := by
    simp [evalF, evList, Exp.ev, hx, hy, hz, pcDec, costList, Exp.cost]; rfl
  exact evalF_seq_ok2 e1 (evalF_seq_ok2 (show evalF κ msY t1 L = .ok t2 L _ from e2)
    (evalF_seq_ok2 (show evalF κ msZ t2 L = .ok t3 L _ from e3) e4))

/-! ### `splitChunkStart` -/

/-- What `insertAroundS_ok` needs: the hypotheses of Level F's `insertAround_run`, and the
capacities. -/
structure IAOK (κ : Caps) (s : Core) (x y z f1x i1 B : Nat) : Prop where
  room : ∀ T ∈ s.cin.getX x, RoomOK s x T
  nd : (s.cin.getX x).Nodup
  yx : y ≠ x
  f1 : (s.nodes.getX ((s.path.getX x).getX 1)).lab? x = some f1x
  idx : (s.cin.getX x).idx? ((s.path.getX x).getX 1) = some i1
  tx : f1x ≤ (s.C.getX x).tag
  lp : x ∈ (s.nodes.getX (s.lpar.getX x)).children
  gy : OrderMaintenance.Proof.TagOK s y (tagY s x f1x i1)
  gz : OrderMaintenance.Proof.TagOK { s with C := s.C.modify y fun C => { C with tag := tagY s x f1x i1 } } z (tagZ s x f1x i1)
  zx : z ≠ x
  yz : y ≠ z
  npx : notPrep s x
  npy : notPrep s y
  npz : notPrep s z
  xC : x < κ.tbl .C
  pw : 1 < κ.pw
  H : s.P.H + 1 ≤ κ.pw
  xa : x < κ.arr .lpar
  ya : y < κ.arr .lpar
  za : z < κ.arr .lpar
  ys : y < s.C.size
  zs : z < s.C.size
  yC : y < κ.tbl .C
  zC : z < κ.tbl .C
  yP : (s.C.getX y).prev < κ.tbl .C
  yN : (s.C.getX y).next < κ.tbl .C
  zP : (s.C.getX z).prev < κ.tbl .C
  zN : (s.C.getX z).next < κ.tbl .C
  ry : rowZero κ s y
  rz : rowZero κ s z
  xi : x < κ.lrec .cin
  yi : y < κ.lrec .cin
  zi : z < κ.lrec .cin
  cin : (s.cin.getX x).length ≤ κ.lcap .cin
  capT : ∀ T ∈ s.cin.getX x, T < κ.lrec .table ∧ T < κ.lrec .side ∧ T < κ.tbl .N ∧
    (s.nodes.getX T).table.length + 2 ≤ κ.lcap .table ∧ (s.nodes.getX T).side.length + 2 ≤ κ.lcap .side
  tB : ∀ T ∈ s.cin.getX x, (s.nodes.getX T).table.length ≤ B ∧ (s.nodes.getX T).side.length ≤ B
  lr : s.lpar.getX x < κ.lrec .children
  ccap : (s.nodes.getX (s.lpar.getX x)).children.length + 2 ≤ κ.lcap .children

/-- The state `insertAround x y z` reaches from `s` (Level F's `insertAround_run`). -/
def iaState (s : Core) (x y z f1x i1 : Nat) : Core :=
  insFinS (tagsS s y z (tagY s x f1x i1) (tagZ s x f1x i1)) x y z
    fun T => (roomL s.P.beta (s.nodes.getX T).table x true, roomL s.P.beta (s.nodes.getX T).table x false)

/-- The cost bound of `insertAroundS`. -/
def iaCost (s : Core) (x B : Nat) : Nat :=
  1200 + 60 * B + (s.cin.getX x).length * (1100 + 400 * B) + 220 * (s.nodes.getX (s.lpar.getX x)).children.length

theorem IAOK.run {κ : Caps} {s : Core} {x y z f1x i1 B : Nat} (h : IAOK κ s x y z f1x i1 B) :
    (insertAround x y z).run s = .ok { x := x, y := y, z := z, pc := .copy 1 } (iaState s x y z f1x i1) :=
  insertAround_run h.room h.nd h.yx h.f1 h.idx h.tx h.lp h.gy h.gz

theorem IAOK.agree {κ : Caps} {s : Core} {L : Loc} {x y z f1x i1 B : Nat} (h : IAOK κ s x y z f1x i1 B)
    (hLx : L "x" = x) (hLy : L "y" = y) (hLz : L "z" = z) :
    ∃ L' c, evalF κ insertAroundS s L = .ok (iaState s x y z f1x i1) L' c ∧ c ≤ iaCost s x B ∧
      L' "x" = x ∧ L' "y" = y ∧ L' "z" = z :=
  insertAroundS_ok hLx hLy hLz h.room h.nd h.yx h.f1 h.idx h.tx h.lp h.gy h.gz h.zx h.yz h.npx h.npy h.npz h.xC h.pw
    h.H h.xa h.ya h.za h.ys h.zs h.yC h.zC h.yP h.yN h.zP h.zN h.ry h.rz h.xi h.yi h.zi h.cin h.capT h.tB h.lr h.ccap

/-- `splitChunkStart x` (local `x`; `y`, `z` receive the new chunks). -/
def splitChunkStartS : Stm := cm{
  if x = 0 then fail else if size C ≤ x then fail
  y := new C; z := new C
  linkChunkPairS; insertAroundS; markSplitS }

theorem splitChunkStartS_ok {κ : Caps} {s : Core} {L : Loc} {x f1x i1 B : Nat} (hx : L "x" = x) (hx0 : x ≠ NIL)
    (hxs : x < s.C.size) (hC : s.C.size + 2 ≤ κ.tbl .C)
    (hp : (s.C.getX x).prev ≠ NIL → (s.C.getX x).prev < s.C.size)
    (hn : (s.C.getX x).next ≠ NIL → (s.C.getX x).next < s.C.size)
    (hia : IAOK κ (linkChunkPair (OrderMaintenance.Proof.push2 s) x s.C.size (s.C.size + 1)) x s.C.size (s.C.size + 1) f1x i1 B) :
    ∃ L' c, evalF κ splitChunkStartS s L =
      .ok (OrderMaintenance.Proof.markState (iaState (linkChunkPair (OrderMaintenance.Proof.push2 s) x s.C.size (s.C.size + 1)) x s.C.size
        (s.C.size + 1) f1x i1) x s.C.size (s.C.size + 1) { x := x, y := s.C.size, z := s.C.size + 1, pc := .copy 1 })
        L' c ∧
      c ≤ 150 + iaCost (linkChunkPair (OrderMaintenance.Proof.push2 s) x s.C.size (s.C.size + 1)) x B ∧ L' "x" = x := by
  set y := s.C.size
  set z := s.C.size + 1
  have e1 : evalF κ (.ite ("x" =ₑ 0) .fail (.ite (.size .C ≤ₑ "x") .fail .skip)) s L = .ok s L 10 := by
    have h1 : ¬ x = 0 := hx0
    have h2 : ¬ s.C.size ≤ x := by omega
    simp [evalF, Exp.ev, hx, OrderMaintenance.Machine.BinOp.eval, h1, h2, Tbl.size, Exp.cost,
      Res.addCost]
  have e2 : evalF κ (.push .C "y") s L = .ok (Tbl.push s .C) (upd L "y" y) pushCost := by
    have h : Tbl.size s .C < κ.tbl .C := by simp only [Tbl.size]; omega
    simp only [evalF, ite_eq_left h]; rfl
  have e3 : evalF κ (.push .C "z") (Tbl.push s .C) (upd L "y" y) =
      .ok (OrderMaintenance.Proof.push2 s) (upd (upd L "y" y) "z" z) pushCost := by
    have h : Tbl.size (Tbl.push s .C) .C < κ.tbl .C := by simp only [Tbl.size, Tbl.push, Array.size_push]; omega
    simp only [evalF, ite_eq_left h]
    simp only [Tbl.size, Tbl.push, Array.size_push, z]; rfl
  set L3 := upd (upd L "y" y) "z" z
  have h3x : L3 "x" = x := by simp [L3, OrderMaintenance.Machine.State.upd, hx]
  have h3y : L3 "y" = y := by simp [L3, OrderMaintenance.Machine.State.upd]
  have h3z : L3 "z" = z := by simp [L3, OrderMaintenance.Machine.State.upd]
  have hps : (OrderMaintenance.Proof.push2 s).C.size = s.C.size + 2 := by simp [OrderMaintenance.Proof.push2]
  have hpx : (OrderMaintenance.Proof.push2 s).C.getX x = s.C.getX x := by
    simp only [OrderMaintenance.Proof.push2, getX_push',
      Array.size_push]; rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  obtain ⟨L4, c4, e4, hc4, hF4⟩ := linkChunkPairS_ok (κ := κ) (s := OrderMaintenance.Proof.push2 s) (L := L3) (x := x) (y := y)
    (z := z) h3x h3y h3z (by omega) (by omega) (by omega) (by omega) (by rw [hpx, hps]; intro h; have := hp h; omega)
    (by rw [hpx, hps]; intro h; have := hn h; omega)
  obtain ⟨L5, c5, e5, hc5, h5x, h5y, h5z⟩ := hia.agree (L := L4)
    (by rw [hF4 "x" (by decide) (by decide), h3x]) (by rw [hF4 "y" (by decide) (by decide), h3y])
    (by rw [hF4 "z" (by decide) (by decide), h3z])
  have hsz : (iaState (linkChunkPair (OrderMaintenance.Proof.push2 s) x y z) x y z f1x i1).C.size = s.C.size + 2 := by
    simp only [iaState, insFinS_C, (tagsS_top _ _ _ _ _).2.2.2.2.2, Array.size_modify]
    simp [linkChunkPair, hps]
  have e6 := markSplitS_ok (κ := κ) (t := iaState (linkChunkPair (OrderMaintenance.Proof.push2 s) x y z) x y z f1x i1) (L := L5)
    (x := x) (y := y) (z := z) h5x h5y h5z (by omega) (by omega) (by omega) (by omega)
  refine ⟨L5, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 (evalF_seq_ok2 e4 (evalF_seq_ok2 e5 e6)))),
    ?_, h5x⟩
  simp only [pushCost]; omega

end OrderMaintenance.Impl
