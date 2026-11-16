/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.Cut
public import LeanPool.OrderMaintenance.Impl.TopTab
public import LeanPool.OrderMaintenance.Proof.Top.RunStart


/-!
# M6: `startDrain` at Level M

The program builds the side list of `v` first (in place), so until its last step its state is
Level F's stage with `v`'s side list already set: `φ X = X` with `side v := side`. Every stage after
the side list touches other nodes or other fields, so it commutes with `φ`, and the last step sets
`side v := side` anyway.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Proof.Top
open OrderMaintenance.Machine (Reg BinOp UnOp)

local notation "upd" => Machine.State.upd

/-- Level F's state with `v`'s side list already set. -/
def phiS (v : Nat) (side : List (Nat × Side)) (X : Core) : Core :=
  {
    X with
    nodes := X.nodes.modify v fun n => {
      n with
      side := side
    }
  }

theorem put_side_phi (X : Core) (v : Nat) (side : List (Nat × Side)) :
    LK.put X v (encS side) .side = phiS v side X := put_side_encS X v side

theorem Array.modify_push_lt {α : Type} (a : Array α) (x : α) (f : α → α) {i : Nat} (hi : i <
  a.size) :
    (a.modify i f).push x = (a.push x).modify i f := by
  apply Array.ext
  · simp
  · intro j h1 h2
    simp only [Array.getElem_modify, Array.getElem_push]
    simp only [Array.size_push, Array.size_modify] at h1
    by_cases e : j = a.size
    · subst e; simp [show i ≠ a.size by omega]
    · have : j < a.size := by omega
      simp [this]

/-! ### Steps -/

theorem evalF_pushN_ok {κ : Caps} {s : Core} {L : Loc} {x : Reg} (h : s.nodes.size < κ.tbl .N) :
    evalF κ (.push .N x) s L = .ok {
      s with
      nodes := s.nodes.push default
    } (upd L x s.nodes.size) pushCost := by
  simp [evalF, Tbl.size, Tbl.push, h]

theorem evalF_wrN_ok {κ : Caps} {s : Core} {L : Loc} {k : NF} {i e : Exp} {j w : Nat} (hi : i.ev
  κ s L = some j)
    (he : e.ev κ s L = some w) (hj : j < s.nodes.size) (hk : k.ok w = true) :
    evalF κ (.wr (.n k) i e) s L = .ok {
      s with
      nodes := s.nodes.modify j (NF.set · w k)
    } L (1 + i.cost + e.cost) := by
  simp [evalF, hi, he, Fld.set, hj, hk]

/-! ### Stage 1: the two new nodes -/

/-- Allocate the two drain targets at the source node's height. -/
def newNodesS : Stm := cm{ v1 := new N; N[v1].height := h; v2 := new N; N[v2].height := h }

theorem newNodesS_ok {κ : Caps} {t : Core} {L : Loc} {v : Nat} {side : List (Nat × Side)}
    (hh : L "h" = sH t v) (hv : v < t.nodes.size) (hcap : t.nodes.size + 2 ≤ κ.tbl .N) :
    ∃ L', evalF κ newNodesS (phiS v side t) L = .ok (phiS v side (sd1 t v)) L' (2 * pushCost + 6) ∧
      L' "v1" = t.nodes.size ∧ L' "v2" = t.nodes.size + 1 ∧
      ∀ r, r ≠ "v1" → r ≠ "v2" → L' r = L r := by
  set N := t.nodes.size
  set S0 := phiS v side t
  have hs : S0.nodes.size = N := by simp [S0, phiS, N]
  have e1 := evalF_pushN_ok (κ := κ) (s := S0) (L := L) (x := "v1") (by omega)
  rw [hs] at e1
  set S1 := {
    S0 with
    nodes := S0.nodes.push default
  }
  set L1 := upd L "v1" N
  have e2 := evalF_wrN_ok (κ := κ) (s := S1) (L := L1) (k := .height) (i := .var "v1") (e :=
    .var "h") (j := N)
    (w := sH t v) (by simp [Exp.ev, L1, Machine.State.upd]) (by simp [Exp.ev, L1,
      Machine.State.upd, hh])
    (by simp [S1, hs])  rfl
  set S2 := {
    S1 with
    nodes := S1.nodes.modify N (NF.set · (sH t v) .height)
  }
  have hs2 : S2.nodes.size = N + 1 := by simp [S2, S1, hs]
  have e3 := evalF_pushN_ok (κ := κ) (s := S2) (L := L1) (x := "v2") (by omega)
  rw [hs2] at e3
  set S3 := {
    S2 with
    nodes := S2.nodes.push default
  }
  set L3 := upd L1 "v2" (N + 1)
  have e4 := evalF_wrN_ok (κ := κ) (s := S3) (L := L3) (k := .height) (i := .var "v2") (e :=
    .var "h")
    (j := N + 1) (w := sH t v) (by simp [Exp.ev, L3, Machine.State.upd])
    (by simp [Exp.ev, L3, L1, Machine.State.upd,
      hh]) (by simp [S3, hs2])  rfl
  refine ⟨L3, ?_, by simp [L3, L1, Machine.State.upd], by simp [L3, Machine.State.upd],
    fun r h1 h2 => by simp [L3, L1, Machine.State.upd, h1, h2]⟩
  have hfin : {
    S3 with
    nodes := S3.nodes.modify (N + 1) (NF.set · (sH t v) .height)
  } = phiS v side (sd1 t v) := by
    simp only [S3, S2, S1, S0, phiS, sd1]
    congr 1
    apply Array.ext_getX
    · simp
    · intro j
      have hvN : v ≠ N := by omega
      have hvN1 : v ≠ N + 1 := by omega
      simp only [getX_modify', getX_push', Array.size_push, Array.size_modify]
      rcases (show j = N + 1 ∨ j = N ∨ j < N ∨ N + 1 < j by omega) with rfl | rfl | hj | hj
      · simp [Ne.symm hvN1, N]; rfl
      · simp [Ne.symm hvN, N]; rfl
      · simp [show j ≠ N by omega, show j ≠ N + 1 by omega, N, hv, show v < t.nodes.size + 1 + 1
          by omega]
      · simp [show j ≠ N by omega, show j ≠ N + 1 by omega, show j ≠ v by omega, N]
  rw [← hfin]
  exact (evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 e4))).trans (by
    simp [Exp.cost]
    omega)

/-! ### Stage 2: `v1`, `v2` around `v` in every table holding `v` -/

theorem Array.modify_comm {α : Type} (a : Array α) {i j : Nat} (h : i ≠ j) (f g : α → α) :
    (a.modify i f).modify j g = (a.modify j g).modify i f := by
  apply Array.ext
  · simp
  · intro k h1 h2
    simp only [Array.getElem_modify]
    by_cases e1 : i = k <;> by_cases e2 : j = k <;> simp_all

theorem fold_modify_getX_notin {f : Array Node → Nat → Array Node}
    (hf : ∀ ns T u, u ≠ T → (f ns T).getX u = ns.getX u) {u : Nat} : ∀ (l : List Nat) (a : Array
      Node), u ∉ l →
    (l.foldl f a).getX u = a.getX u
  | [], _, _ => rfl
  | T :: l, a, hu => by
    simp only [List.foldl_cons]
    rw [fold_modify_getX_notin hf l _ (fun h => hu (List.mem_cons_of_mem _ h)),
      hf a T u (fun h => hu (by simp [h]))]

theorem fold_modify_size {f : Array Node → Nat → Array Node} (hf : ∀ ns T, (f ns T).size =
  ns.size) :
    ∀ (l : List Nat) (a : Array Node), (l.foldl f a).size = a.size
  | [], _ => rfl
  | T :: l, a => by simp only [List.foldl_cons]; rw [fold_modify_size hf l, hf]

/-- Level F after the insertions into the first `j` tables. -/
def aroundStep (t : Core) (v : Nat) (ns : Array Node) (T : Nat) : Array Node :=
  ns.modify T (aroundF (sd1 t v) v t.nodes.size (t.nodes.size + 1) (sF t v) T)

/-- The drain-start state after updating the first `j` enclosing tables. -/
def sdJ (t : Core) (v j : Nat) : Core :=
  {
    sd1 t v with
    nodes := ((t.nodes.getX v).inTables.take j).foldl (aroundStep t v) (sd1 t v).nodes
  }

theorem sdJ_all (t : Core) (v : Nat) : sdJ t v (t.nodes.getX v).inTables.length = sd2 t v := by
  simp only [sdJ, sd2, List.take_length]; rfl

theorem sd1_getX (t : Core) (v : Nat) {u : Nat} (hu : u < t.nodes.size) : (sd1 t v).nodes.getX u
  = t.nodes.getX u := by
  simp only [sd1, getX_push',
    Array.size_push]; rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-- Insert both drain targets around the source in one enclosing table. -/
def insBody : Stm := cm{
  T := inTab[v][j].fst
  a ← roomP(T, v, 1)
  b ← roomP(T, v, 0)
  call tableInsertP(T, v, v1, 1, a)
  call tableInsertP(T, v, v2, 0, b) }

/-- Insert both drain targets into every table containing the source. -/
def insS : Stm := cm{ m := len inTab[v]; for j < m do insBody }

theorem nodup_getElem_notin_take {l : List Nat} (hnd : l.Nodup) {j : Nat} (hj : j < l.length) :
    l[j] ∉ l.take j := by
  intro h
  obtain ⟨i, hi, he⟩ := List.getElem_of_mem h
  simp only [List.length_take] at hi
  rw [List.getElem_take] at he
  have := (List.Nodup.getElem_inj_iff hnd).mp he
  omega

theorem aroundStep_getX (t : Core) (v : Nat) (ns : Array Node) (T u : Nat) (h : u ≠ T) :
    (aroundStep t v ns T).getX u = ns.getX u := by
  simp only [aroundStep, getX_modify']; rw [ite_eq_right (fun e => h e.1)]

theorem aroundStep_size (t : Core) (v : Nat) (ns : Array Node) (T : Nat) : (aroundStep t v ns
  T).size = ns.size := by
  simp [aroundStep]

theorem sdJ_getX_notin {t : Core} {v j u : Nat} (hu : u ∉ (t.nodes.getX v).inTables.take j)
    (hlt : u < t.nodes.size) : (sdJ t v j).nodes.getX u = t.nodes.getX u := by
  simp only [sdJ]
  rw [fold_modify_getX_notin (aroundStep_getX t v) _ _ hu, sd1_getX t v hlt]

theorem sdJ_getX_notin' {t : Core} {v j u : Nat} (hu : u ∉ (t.nodes.getX v).inTables.take j) :
    (sdJ t v j).nodes.getX u = (sd1 t v).nodes.getX u := by
  simp only [sdJ]
  rw [fold_modify_getX_notin (aroundStep_getX t v) _ _ hu]

theorem sdJ_size (t : Core) (v j : Nat) : (sdJ t v j).nodes.size = t.nodes.size + 2 := by
  simp only [sdJ]; rw [fold_modify_size (aroundStep_size t v)]; simp [sd1]

theorem sdJ_succ (t : Core) (v j : Nat) (hj : j < (t.nodes.getX v).inTables.length) :
    (sdJ t v (j + 1)).nodes = aroundStep t v (sdJ t v j).nodes (t.nodes.getX v).inTables[j] := by
  simp only [sdJ]
  rw [List.take_succ_eq_append_getElem hj, List.foldl_append]; rfl

theorem phiS_getX_ne {v u : Nat} {side : List (Nat × Side)} {X : Core} (h : u ≠ v) :
    (phiS v side X).nodes.getX u = X.nodes.getX u := by
  simp only [phiS, getX_modify']; rw [ite_eq_right (fun e : u = v ∧ v < X.nodes.size => h e.1)]

theorem phiS_getX_self {v : Nat} {side : List (Nat × Side)} {X : Core} (h : v < X.nodes.size) :
    (phiS v side X).nodes.getX v = {
      X.nodes.getX v with
      side := side
    } := by
  simp only [phiS, getX_modify', h, and_self, ite_true]

theorem insStep_ok {κ : Caps} {t : Core} {L : Loc} {v j B : Nat} {side : List (Nat × Side)}
    (hv : v < t.nodes.size) (hnd : (t.nodes.getX v).inTables.Nodup) (hvT : v ∉ (t.nodes.getX
      v).inTables)
    (hroom : ∀ T ∈ (t.nodes.getX v).inTables, RoomOK t v T) (hj : j < (t.nodes.getX
      v).inTables.length)
    (hLv : L "v" = v) (hLv1 : L "v1" = t.nodes.size) (hLv2 : L "v2" = t.nodes.size + 1)
    (hvi : v < κ.lrec .inTab)
    (hcapT : ∀ T ∈ (t.nodes.getX v).inTables, T < κ.lrec .table ∧ T < κ.lrec .side ∧ T < κ.tbl .N ∧
      (t.nodes.getX T).table.length + 2 ≤ κ.lcap .table ∧ (t.nodes.getX T).side.length + 2 ≤
        κ.lcap .side)
    (hB : ∀ T ∈ (t.nodes.getX v).inTables, (t.nodes.getX T).table.length ≤ B ∧ (t.nodes.getX
      T).side.length ≤ B) :
    ∃ L' c, evalF κ insBody (phiS v side (sdJ t v j)) (upd L "j" j) =
      .ok (phiS v side (sdJ t v (j + 1))) L' c ∧ c ≤ 1000 + 400 * B ∧
      ∀ r, r ≠ "j" → r ≠ "T" → r ≠ "a" → r ≠ "b" → L' r = L r := by
  set N := t.nodes.size
  set tabs := (t.nodes.getX v).inTables
  set T := tabs[j]
  set X := sdJ t v j
  set S := phiS v side X
  have hTm : T ∈ tabs := List.getElem_mem hj
  have hTn : T ∉ tabs.take j := nodup_getElem_notin_take hnd hj
  have hTv : T ≠ v := fun h => hvT (h ▸ hTm)
  have hTN : T < N := (hroom T hTm).lt
  have hvn : v ∉ tabs.take j := fun h => hvT (List.mem_of_mem_take h)
  have hST : S.nodes.getX T = t.nodes.getX T := by
    rw [phiS_getX_ne hTv]; exact sdJ_getX_notin hTn hTN
  have hSv : (S.nodes.getX v).inTables = tabs := by
    rw [phiS_getX_self (by rw [sdJ_size]; omega), sdJ_getX_notin hvn hv]
  have hroomS : RoomOK S v T := by unfold RoomOK; rw [hST]; exact hroom T hTm
  obtain ⟨hTt, hTs, hTNc, hcT, hcS⟩ := hcapT T hTm
  obtain ⟨hBt, hBs⟩ := hB T hTm
  -- the table
  set L0 := upd L "j" j
  have e1 := evalF_assign_ok (κ := κ) (s := S) (L := L0) (x := "T") (e := .lrd .inTab false "v"
    "j") (v := T) (by
    simp [Exp.ev, L0, Machine.State.upd, hLv, hvi, LK.view, hSv, hj, T])
  set L1 := upd L0 "T" T
  have hL1 : ∀ r, r ≠ "j" → r ≠ "T" → L1 r = L r := fun r h1 h2 => by simp [L1, L0,
    Machine.State.upd, h1, h2]
  -- the two labels
  set a := roomL S.P.beta (S.nodes.getX T).table v true
  set b := roomL S.P.beta (S.nodes.getX T).table v false
  obtain ⟨-, La, ca, ea, hla, hca⟩ := roomP_agree κ S
    (Machine.State.setLocs (fun _ => 0) ["t", "e", "bf"] [T, v, 1]) (t := T) (e := v) (before :=
      true)
    (by simp [Machine.State.setLocs, Machine.State.upd])
    (by simp [Machine.State.setLocs, Machine.State.upd])
    (by simp [Machine.State.setLocs, Machine.State.upd,
      b2n]) hTt (roomNextTo_run' hroomS true)
  have e2 := evalF_call_ok (q := roomP) (args := [.var "T", .var "v", 1]) (ds := ["a"]) (L := L1)
    (by simp [evList, Exp.ev, L1, L0, Machine.State.upd, hLv]) ea
  set L2 := Machine.State.setLocs L1 ["a"] (roomP.rets.map La)
  obtain ⟨-, Lb, cb, eb, hlb, hcb⟩ := roomP_agree κ S
    (Machine.State.setLocs (fun _ => 0) ["t", "e", "bf"] [T, v, 0]) (t := T) (e := v) (before :=
      false)
    (by simp [Machine.State.setLocs, Machine.State.upd])
    (by simp [Machine.State.setLocs, Machine.State.upd])
    (by simp [Machine.State.setLocs, Machine.State.upd,
      b2n]) hTt (roomNextTo_run' hroomS false)
  have e3 := evalF_call_ok (q := roomP) (args := [.var "T", .var "v", 0]) (ds := ["b"]) (L := L2)
    (by simp [evList, Exp.ev, L2, L1, L0, roomP, Machine.State.setLocs,
      Machine.State.upd, hLv]) eb
  set L3 := Machine.State.setLocs L2 ["b"] (roomP.rets.map Lb)
  have hL3 : ∀ r, r ≠ "j" → r ≠ "T" → r ≠ "a" → r ≠ "b" → L3 r = L r := fun r h1 h2 h3 h4 => by
    simp only [L3, L2, roomP, Machine.State.setLocs, List.map,
      Machine.State.upd, ite_eq_right h3, ite_eq_right h4]
    exact hL1 r h1 h2
  have hL3T : L3 "T" = T := by simp [L3, L2, L1, roomP, Machine.State.setLocs, Machine.State.upd]
  have hL3a : L3 "a" = a := by
    simp [L3, L2, roomP, Machine.State.setLocs, Machine.State.upd, hla]; rfl
  have hL3b : L3 "b" = b := by simp [L3, roomP, Machine.State.setLocs, Machine.State.upd, hlb]; rfl
  -- the two insertions
  obtain ⟨A, le, Bs, htab, hA, hside, -, -⟩ := hroomS
  have hN1 : N ≠ v := by omega
  have hins := insertAroundIn_run (s := S) (T := T) (a := a) (b := b) (n2 := N + 1) htab hA hN1
    hside
  have h1' := tableInsert_run (s := S) (t := T) (new := N) htab hA true a hside
  unfold insertAroundIn at hins
  obtain ⟨u, s1, h1, h2⟩ := run_bind_ok hins
  rw [h1'] at h1
  injection h1 with _ hs1
  subst hs1
  set s1 := {
    S with
    nodes := S.nodes.modify T (setTS (insTab A Bs v le N a true) (sideAfter (S.nodes.getX T) v N))
  }
  have hTS : T < S.nodes.size := by simp [S, phiS, X, sdJ_size]; omega
  have hs1T : s1.nodes.getX T = setTS (insTab A Bs v le N a true) (sideAfter (S.nodes.getX T) v
    N) (S.nodes.getX T) := by
    simp only [s1, getX_modify', hTS, and_self, ite_true]
  have hlenS : (S.nodes.getX T).table.length = A.length + Bs.length + 1 := by rw [htab]; simp; omega
  obtain ⟨L4', c4, e4', hc4⟩ := tableInsertP_agree κ S
    (Machine.State.setLocs (fun _ => 0) ["t", "e", "w", "bf", "lab"] [T, v, N, 1, a]) (t := T)
      (e := v)
    (w := N) (before := true) (lab := a)
    (by simp [Machine.State.setLocs, Machine.State.upd])
    (by simp [Machine.State.setLocs, Machine.State.upd])
    (by simp [Machine.State.setLocs, Machine.State.upd])
    (by simp [Machine.State.setLocs, Machine.State.upd, b2n])
    (by simp [Machine.State.setLocs,
      Machine.State.upd]) hTt hTs hTNc
    (by rw [hST]; omega) (by rw [hST]; omega) h1'
  have e4 := evalF_call_ok (q := tableInsertP) (args := [.var "T", .var "v", .var "v1", 1, .var
    "a"]) (ds := [])
    (L := L3) (by
      simp [evList, Exp.ev, hL3T, hL3a, hL3 "v" (by decide) (by decide) (by decide) (by decide),
        hLv,
        hL3 "v1" (by decide) (by decide) (by decide) (by decide), hLv1]) e4'
  set L4 := Machine.State.setLocs L3 [] (tableInsertP.rets.map L4')
  have hlen1 : (s1.nodes.getX T).table.length = (S.nodes.getX T).table.length + 1 := by
    rw [hs1T, hlenS]; simp [setTS, insTab]; omega
  have hside1 : (s1.nodes.getX T).side.length ≤ (S.nodes.getX T).side.length + 1 := by
    rw [hs1T]; simp only [setTS, sideAfter]; split
    · exact length_assocSet_le' _ _ _
    · omega
  obtain ⟨L5', c5, e5', hc5⟩ := tableInsertP_agree κ s1
    (Machine.State.setLocs (fun _ => 0) ["t", "e", "w", "bf", "lab"] [T, v, N + 1, 0, b]) (t :=
      T) (e := v)
    (w := N + 1) (before := false) (lab := b)
    (by simp [Machine.State.setLocs, Machine.State.upd])
    (by simp [Machine.State.setLocs, Machine.State.upd])
    (by simp [Machine.State.setLocs, Machine.State.upd])
    (by simp [Machine.State.setLocs, Machine.State.upd, b2n])
    (by simp [Machine.State.setLocs,
      Machine.State.upd]) hTt hTs hTNc
    (by rw [hlen1, hST]; omega) (by rw [hST] at hside1; omega) h2
  have e5 := evalF_call_ok (q := tableInsertP) (args := [.var "T", .var "v", .var "v2", 0, .var
    "b"]) (ds := [])
    (L := L4) (by
      simp [evList, Exp.ev, L4, Machine.State.setLocs, hL3T, hL3b,
        hL3 "v" (by decide) (by decide) (by decide) (by decide), hLv,
        hL3 "v2" (by decide) (by decide) (by decide) (by decide), hLv2]) e5'
  have hG : aroundF (sd1 t v) v N (N + 1) (sF t v) T =
      setTS (aroundTab A Bs v le N (N + 1) a b) (sideAround (S.nodes.getX T) v N (N + 1)) := by
    have ha : a = roomL t.P.beta (A ++ (v, le) :: Bs) v true := by
      change roomL S.P.beta (S.nodes.getX T).table v true = _; rw [htab]; rfl
    have hb : b = roomL t.P.beta (A ++ (v, le) :: Bs) v false := by
      change roomL S.P.beta (S.nodes.getX T).table v false = _; rw [htab]; rfl
    unfold aroundF sF
    rw [sd1_getX t v hTN, ← hST, htab, aroundT_eq hA, ha, hb]
  have hfin : {
    S with
    nodes := S.nodes.modify T (setTS (aroundTab A Bs v le N (N + 1) a b) (sideAround
      (S.nodes.getX T) v N (N + 1)))
  } = phiS v side (sdJ t v (j + 1)) := by
    have hn := sdJ_succ t v j hj
    simp only [aroundStep] at hn
    simp only [S, phiS]
    rw [hn, hG, Array.modify_comm _ hTv]
    rfl
  rw [hfin] at e5
  refine ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 (evalF_seq_ok2 e4 e5))),
    ?_, ?_⟩
  · rw [hST] at hca hcb hc4
    rw [hlen1, hST] at hc5
    rw [hST] at hside1
    have : (s1.nodes.getX T).side.length ≤ B + 1 := by omega
    simp only [Exp.cost, costList, List.map, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at hca hcb hc4 hc5 ⊢
    omega
  · intro r h1 h2 h3 h4
    simp only [Machine.State.setLocs, ]
    exact hL3 r h1 h2 h3 h4

theorem sdJ_zero (t : Core) (v : Nat) : sdJ t v 0 = sd1 t v := by simp [sdJ]

theorem insS_ok {κ : Caps} {t : Core} {L : Loc} {v B : Nat} {side : List (Nat × Side)}
    (hv : v < t.nodes.size) (hnd : (t.nodes.getX v).inTables.Nodup) (hvT : v ∉ (t.nodes.getX
      v).inTables)
    (hroom : ∀ T ∈ (t.nodes.getX v).inTables, RoomOK t v T)
    (hLv : L "v" = v) (hLv1 : L "v1" = t.nodes.size) (hLv2 : L "v2" = t.nodes.size + 1)
    (hvi : v < κ.lrec .inTab)
    (hcapT : ∀ T ∈ (t.nodes.getX v).inTables, T < κ.lrec .table ∧ T < κ.lrec .side ∧ T < κ.tbl .N ∧
      (t.nodes.getX T).table.length + 2 ≤ κ.lcap .table ∧ (t.nodes.getX T).side.length + 2 ≤
        κ.lcap .side)
    (hB : ∀ T ∈ (t.nodes.getX v).inTables, (t.nodes.getX T).table.length ≤ B ∧ (t.nodes.getX
      T).side.length ≤ B) :
    ∃ L' c, evalF κ insS (phiS v side (sd1 t v)) L = .ok (phiS v side (sd2 t v)) L' c ∧
      c ≤ 5 + (t.nodes.getX v).inTables.length * (1001 + 400 * B) ∧
      ∀ r, r ≠ "m" → r ≠ "j" → r ≠ "T" → r ≠ "a" → r ≠ "b" → L' r = L r := by
  set m := (t.nodes.getX v).inTables.length
  have hSv : ((phiS v side (sd1 t v)).nodes.getX v).inTables = (t.nodes.getX v).inTables := by
    rw [phiS_getX_self (by simp [sd1]; omega), sd1_getX t v hv]
  have a1 := evalF_assign_ok (κ := κ) (s := phiS v side (sd1 t v)) (L := L) (x := "m") (e :=
    .llen .inTab "v") (v := m)
    (by simp [Exp.ev, hLv, hvi, LK.view, hSv, m])
  set L1 := upd L "m" m
  obtain ⟨S', L', c, he, hc, hs', hF⟩ := evalF_loop (κ := κ) (x := "j") (n := .var "m") (b :=
    insBody)
    (s := phiS v side (sd1 t v)) (L := L1) (N := m) (by simp [Exp.ev, L1, Machine.State.upd])
    (fun j S L' => S = phiS v side (sdJ t v j) ∧
      ∀ r, r ≠ "m" → r ≠ "j" → r ≠ "T" → r ≠ "a" → r ≠ "b" → L' r = L r) (1000 + 400 * B)
    ⟨by rw [sdJ_zero], fun r h1 _ _ _ _ => by simp [L1, Machine.State.upd, h1]⟩
    (by
      intro j hj S1 L2 ⟨hS1, hF2⟩
      subst hS1
      obtain ⟨L3, c3, e3, hc3, hF3⟩ := insStep_ok (κ := κ) (L := L2) (side := side) (B := B) hv
        hnd hvT hroom hj
        (by rw [hF2 "v" (by decide) (by decide) (by decide) (by decide) (by decide), hLv])
        (by rw [hF2 "v1" (by decide) (by decide) (by decide) (by decide) (by decide), hLv1])
        (by rw [hF2 "v2" (by decide) (by decide) (by decide) (by decide) (by decide),
          hLv2]) hvi hcapT hB
      exact ⟨_, L3, c3, e3, hc3, rfl, fun r h1 h2 h3 h4 h5 => (hF3 r h2 h3 h4 h5).trans (hF2 r
        h1 h2 h3 h4 h5)⟩)
  rw [hs', show m = (t.nodes.getX v).inTables.length from rfl, sdJ_all] at he
  refine ⟨L', _, evalF_seq_ok2 a1 he, ?_, hF⟩
  simp only [Exp.cost] at hc ⊢
  have e : m * (1 + (1000 + 400 * B)) = m * (1001 + 400 * B) := by ring
  rw [e] at hc; omega

/-! ### Stage 3: the tables of `v1`, `v2` -/

/-- `drainEntries`' test for entry `e` of `v`'s table. -/
def entOK (t : Core) (v e : Nat) : Bool :=
  sH t v == 1 || (t.nodes.getX v).children.contains e || (t.nodes.getX e).first != NIL

/-- `q := ` entry `e` is a drain entry on side `sd` (locals `v h e sd`). -/
def selE : Exp := cme{ ((h = 1 || r < m) || N[e].first ≠ 0) && (f && x = sd) }
/-- Decide whether a table entry belongs to the selected side of the drain. -/
def selS : Stm := cm{
  r ← ‹findP .children›(v, e)
  m := len children[v]
  (f, x) ← ‹lookupP .side›(v, e)
  q := ‹selE› }

/-- What `selS` reads agrees with Level F's state `t`. -/
structure ReadOK (St t : Core) (v : Nat) (side : List (Nat × Side)) : Prop where
  tab : (St.nodes.getX v).table = (t.nodes.getX v).table
  kids : (St.nodes.getX v).children = (t.nodes.getX v).children
  side : (St.nodes.getX v).side = side
  first : ∀ e, (St.nodes.getX e).first = (t.nodes.getX e).first

theorem selS_ok {κ : Caps} {St t : Core} {L : Loc} {v e : Nat} {side : List (Nat × Side)} {sd :
  Side}
    (hR : ReadOK St t v side) (hLv : L "v" = v) (hLh : L "h" = sH t v) (hLe : L "e" = e) (hLs :
      L "sd" = sideN sd)
    (hvc : v < κ.lrec .children) (hvs : v < κ.lrec .side) (heN : e < κ.tbl .N) :
    ∃ L' c, evalF κ selS St L = .ok St L' c ∧
      L' "q" = (if entOK t v e = true ∧ lookup side e = some sd then 1 else 0) ∧
      c ≤ 120 + 20 * (t.nodes.getX v).children.length + 20 * side.length ∧
      ∀ r, r ≠ "r" → r ≠ "m" → r ≠ "f" → r ≠ "x" → r ≠ "q" → L' r = L r := by
  have hvC : LK.view St v .children = (t.nodes.getX v).children.map fun e => (e, 0) := by
    simp [LK.view, hR.kids]
  have hvS : LK.view St v .side = encS side := by simp [LK.view, hR.side]
  obtain ⟨Lf, cf, ef, hrf, hcf⟩ := findP_agree κ .children St
    (Machine.State.setLocs (fun _ => 0) ["i", "x"] [v, e]) (i := v) (x := e)
    (by simp [Machine.State.setLocs, Machine.State.upd])
    (by simp [Machine.State.setLocs, Machine.State.upd]) hvc
  have e1 := evalF_call_ok (q := findP .children) (args := [.var "v", .var "e"]) (ds := ["r"])
    (L := L)
    (by simp [evList, Exp.ev, hLv, hLe]) ef
  set L1 := Machine.State.setLocs L ["r"] ((findP .children).rets.map Lf)
  have hL1 : ∀ r, r ≠ "r" → L1 r = L r := fun r h => by
    simp [L1, findP, Machine.State.setLocs, Machine.State.upd, h]
  have e2 := evalF_assign_ok (κ := κ) (s := St) (L := L1) (x := "m") (e := .llen .children "v")
    (v := (t.nodes.getX v).children.length) (by simp [Exp.ev, hL1 "v" (by decide), hLv, hvc, hvC])
  set L2 := upd L1 "m" (t.nodes.getX v).children.length
  obtain ⟨Lk, ck, ek, hfk, hvk, -, -, hck⟩ := lookupP_agree κ .side St
    (Machine.State.setLocs (fun _ => 0) ["i", "x"] [v, e]) (i := v) (x := e)
    (by simp [Machine.State.setLocs, Machine.State.upd])
    (by simp [Machine.State.setLocs, Machine.State.upd]) hvs
  rw [hvS, lookup_encS] at hfk hvk
  rw [hvS] at hck
  have e3 := evalF_call_ok (q := lookupP .side) (args := [.var "v", .var "e"]) (ds := ["f",
    "x"]) (L := L2)
    (by simp [evList, Exp.ev, L2, Machine.State.upd, hL1 "v" (by decide), hLv,
      hL1 "e" (by decide), hLe]) ek
  set L3 := Machine.State.setLocs L2 ["f", "x"] ((lookupP .side).rets.map Lk)
  have hL3 : ∀ r, r ≠ "r" → r ≠ "m" → r ≠ "f" → r ≠ "x" → L3 r = L r := fun r h1 h2 h3 h4 => by
    simp only [L3, L2, lookupP, Machine.State.setLocs, List.map,
      Machine.State.upd, ite_eq_right h2, ite_eq_right h3,
      ite_eq_right h4]
    exact hL1 r h1
  have hq : selE.ev κ St L3 = some (if entOK t v e = true ∧ lookup side e = some sd then 1 else
    0) := by
    have h3r : L3 "r" = ((t.nodes.getX v).children.map fun e => (e, 0)).findIdx (·.1 == e) := by
      simp [L3, L2, L1, lookupP, findP, Machine.State.setLocs,
        Machine.State.upd, hrf, hvC]
    have h3m : L3 "m" = (t.nodes.getX v).children.length := by
      simp [L3, L2, lookupP, Machine.State.setLocs,
        Machine.State.upd]
    have h3f : L3 "f" = if ((lookup side e).map sideN).isSome then 1 else 0 := by
      simp [L3, lookupP, Machine.State.setLocs,
        Machine.State.upd, hfk]
    have h3x : L3 "x" = ((lookup side e).map sideN).getD 0 := by
      simp [L3, lookupP, Machine.State.setLocs,
        Machine.State.upd, hvk]
    have hc := findIdx_pair0 (t.nodes.getX v).children e
    simp only [selE, Exp.ev, h3r, h3m, h3f, h3x,
      hL3 "h" (by decide) (by decide) (by decide) (by decide), hLh,
      hL3 "e" (by decide) (by decide) (by decide) (by decide), hLe,
      hL3 "sd" (by decide) (by decide) (by decide) (by decide), hLs, Option.bind_some, heN,
        Fld.cap, Fld.get,
      NF.get, hR.first, ite_true, Machine.BinOp.eval, Machine.UnOp.eval, Option.map_some,
        Exp.ofNat_def]
    simp only [hc]
    congr 1
    unfold entOK
    cases hl : lookup side e with
    | none => simp
    | some st =>
      cases st <;> cases sd <;> simp [sideN] <;>
        by_cases h1 : sH t v = 1 <;> by_cases h2 : (t.nodes.getX v).children.contains e = true <;>
        by_cases h3 : (t.nodes.getX e).first = 0 <;> simp_all [NIL]
  have e4 := evalF_assign_ok (κ := κ) (s := St) (L := L3) (x := "q") (e := selE) hq
  refine ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 e4)), by simp
    [Machine.State.upd], ?_, ?_⟩
  · simp only [List.length_map] at hcf hck
    simp only [Exp.cost, costList, List.map, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil,
      Exp.ofNat_def, selE] at hcf hck ⊢
    simp only [LK.view, hR.kids, List.length_map] at hcf
    omega
  · intro r h1 h2 h3 h4 h5; simp only [Machine.State.upd, ite_eq_right h5]; exact hL3 r h1 h2 h3 h4

/-- The entries of `v`'s table that go to the new node on side `sd`. -/
def selP (t : Core) (v : Nat) (side : List (Nat × Side)) (sd : Side) (e : Nat) : Bool :=
  entOK t v e && lookup side e == some sd

/-- Filter a node's table entries by the requested drain side. -/
def part (t : Core) (v : Nat) (side : List (Nat × Side)) (sd : Side) : List Nat :=
  ((t.nodes.getX v).table.map (·.1)).filter (selP t v side sd)

theorem sLeft_part (t : Core) (v : Nat) (side : List (Nat × Side)) : sLeft t v side = part t v
  side .left := by
  simp only [sLeft, sEntries, drainEntries, part, List.filter_filter, Node.order]
  congr 1; funext e; simp [selP, entOK, Bool.and_comm]

theorem sRight_part (t : Core) (v : Nat) (side : List (Nat × Side)) : sRight t v side = part t v
  side .right := by
  simp only [sRight, sEntries, drainEntries, part, List.filter_filter, Node.order]
  congr 1; funext e; simp [selP, entOK, Bool.and_comm]

/-- `evenTable` with the spacing `st`. -/
def evT (st : Nat) (l : List Nat) : List (Nat × Nat) := ((List.range l.length).zip l).map fun
  (i, e) => (e, (i + 1) * st)

theorem evenTable_evT (β : Nat) (l : List Nat) : evenTable β l = evT ((1 <<< β) / (l.length +
  1)) l := rfl

theorem evT_append (st : Nat) (l : List Nat) (e : Nat) : evT st (l ++ [e]) = evT st l ++ [(e,
  (l.length + 1) * st)] := by
  simp only [evT, List.length_append, List.length_singleton, List.range_succ]
  rw [List.zip_append (by simp)]
  simp

theorem foldl_count (p : Nat → Bool) (l : List Nat) : ∀ n, n ≤ l.length →
    (List.range n).foldl (fun c j => c + if p (l.getD j 0) then 1 else 0) 0 = ((l.take n).filter
      p).length
  | 0, _ => by simp
  | n + 1, h => by
    rw [List.range_succ, List.foldl_append, foldl_count p l n (by omega),
      List.take_succ_eq_append_getElem (by omega),
      List.filter_append]
    simp only [List.foldl_cons, List.foldl_nil,
      List.getD_eq_getElem _ _ (show n < l.length by omega)]
    by_cases hp : p l[n] = true <;> simp [hp]

theorem ReadOK.put_table {St t : Core} {v w : Nat} {side : List (Nat × Side)} (hR : ReadOK St t
  v side)
    (hw : w ≠ v) (l : List (Nat × Nat)) : ReadOK (LK.put St w l .table) t v side := by
  have hg : ∀ u, u ≠ w → (LK.put St w l .table).nodes.getX u = St.nodes.getX u := by
    intro u hu; simp only [LK.put, getX_modify']; rw [ite_eq_right (fun h => hu h.1)]
  have hf : ∀ u, ((LK.put St w l .table).nodes.getX u).first = (St.nodes.getX u).first := by
    intro u; simp only [LK.put, getX_modify']; split <;> rfl
  exact ⟨by rw [hg v (Ne.symm hw)]; exact hR.tab, by rw [hg v (Ne.symm hw)]; exact hR.kids,
    by rw [hg v (Ne.symm hw)]; exact hR.side, fun u => by rw [hf]; exact hR.first u⟩

/-- Count one table entry when it belongs to the selected drain side. -/
def cntBody : Stm := cm{ e := table[v][j].fst; selS; if q then cnt := cnt + 1 }
/-- Append a selected table entry with its evenly spaced target label. -/
def bldBody : Stm := cm{
  e := table[v][j].fst; selS
  if q then { idx := idx + 1; append table[w] (e, idx * st) } }
/-- **The table of a new node `w`**: the drain entries of side `sd`, evenly labelled. -/
def tabS : Stm := cm{
  nt := len table[v]
  cnt := 0; for j < nt do cntBody
  st := (1 <<< P.beta) / (cnt + 1)
  idx := 0; for j < nt do bldBody }

theorem length_evT (st : Nat) (l : List Nat) : (evT st l).length = l.length := by simp [evT]

/-- Count selected entries, recording the exact counter value and preserved registers. -/
theorem count_selected_entries {κ : Caps} {St t : Core} {L : Loc} {v : Nat}
    {side : List (Nat × Side)} {sd : Side} (hR : ReadOK St t v side)
    (hLv : L "v" = v) (hLh : L "h" = sH t v) (hLs : L "sd" = sideN sd)
    (hvc : v < κ.lrec .children) (hvs : v < κ.lrec .side) (hvt : v < κ.lrec .table)
    (hN : ∀ e ∈ (t.nodes.getX v).table.map (·.1), e < κ.tbl .N) :
    let n := (t.nodes.getX v).table.length
    let L2 := upd (upd L "nt" n) "cnt" 0
    ∃ L3 c3, evalF κ (.loop "j" (.var "nt") cntBody) St L2 = .ok St L3 c3 ∧
      c3 ≤ 1 + (.var "nt" : Exp).cost + n *
        (1 + (140 + 20 * (t.nodes.getX v).children.length + 20 * side.length)) ∧
      (∀ r, r ≠ "cnt" → r ≠ "j" → r ≠ "e" → r ≠ "r" → r ≠ "m" → r ≠ "f" →
        r ≠ "x" → r ≠ "q" → L3 r = L2 r) ∧
      L3 "cnt" = (part t v side sd).length := by
  set o := (t.nodes.getX v).table.map (·.1)
  set n := (t.nodes.getX v).table.length
  set K := (t.nodes.getX v).children.length
  set p := selP t v side sd
  have hon : o.length = n := by simp [o, n]
  have hvT : LK.view St v .table = (t.nodes.getX v).table := by simp [LK.view, hR.tab]
  have hsel : ∀ e, (entOK t v e = true ∧ lookup side e = some sd) ↔ p e = true := by
    intro e; simp [p, selP]
  set L2 := upd (upd L "nt" n) "cnt" 0
  have hL2 : ∀ r, r ≠ "nt" → r ≠ "cnt" → L2 r = L r := fun r h1 h2 => by simp [L2,
    Machine.State.upd, h1, h2]
  obtain ⟨L3, c3, e3, hc3, hF3, ha3⟩ := evalF_loop_pure (κ := κ) (x := "j") (n := .var "nt") (b
    := cntBody)
    (s := St) (L := L2) (N := n) (by simp [Exp.ev, L2, Machine.State.upd])
    (fun L' => ∀ r, r ≠ "cnt" → r ≠ "j" → r ≠ "e" → r ≠ "r" → r ≠ "m" → r ≠ "f" → r ≠ "x" → r ≠
      "q" →
      L' r = L2 r) (fun L' => L' "cnt") (fun c j => c + if p (o.getD j 0) then 1 else 0)
    (140 + 20 * K + 20 * side.length) (fun _ _ _ _ _ _ _ _ _ => rfl)
    (by
      intro j hj L' hF
      have hv' : L' "v" = v := by
        rw [hF "v" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
          decide) (by decide),
          hL2 "v" (by decide) (by decide), hLv]
      have e1 := evalF_assign_ok (κ := κ) (s := St) (L := upd L' "j" j) (x := "e") (e := .lrd
        .table false "v" "j")
        (v := o[j]'(by omega)) (by
          have hj2 : j < (t.nodes.getX v).table.length := hj
          have hoj2 : (t.nodes.getX v).table[j].1 = o[j]'(by omega) := by simp [o]
          simp [Exp.ev, Machine.State.upd, hv', hvt, hvT, hj2, hoj2])
      set L4 := upd (upd L' "j" j) "e" (o[j]'(by omega))
      obtain ⟨L5, c5, e5, hq5, hc5, hF5⟩ := selS_ok (κ := κ) (St := St) (t := t) (L := L4) (v := v)
        (e := o[j]'(by omega)) (side := side) (sd := sd) hR
        (by simp [L4, Machine.State.upd, hv'])
        (by simp only [L4, Machine.State.upd]; simp only [String.reduceEq, ↓reduceIte]
            rw [hF "h" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide)
              (by decide), hL2 "h" (by decide) (by decide), hLh])
        (by simp [L4, Machine.State.upd])
        (by simp only [L4, Machine.State.upd]; simp only [String.reduceEq, ↓reduceIte]
            rw [hF "sd" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide)
              (by decide), hL2 "sd" (by decide) (by decide), hLs])
        hvc hvs (hN _ (List.getElem_mem _))
      have hc5' : L5 "cnt" = L' "cnt" := by
        rw [hF5 "cnt" (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [L4,
          Machine.State.upd]
      have hgetD : o.getD j 0 = o[j]'(by omega) := List.getD_eq_getElem _ _ _
      by_cases hpj : p (o[j]'(by omega)) = true
      · have e6 := evalF_assign_ok (κ := κ) (s := St) (L := L5) (x := "cnt") (e := "cnt" + 1) (v
          := L' "cnt" + 1)
          (by simp [Exp.ev, Machine.BinOp.eval, hc5'])
        refine ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e5 (evalF_ite_t (v := 1)
          (by simp [Exp.ev, hq5, (hsel _).mpr hpj]) one_ne_zero e6)), ?_, ?_, ?_⟩
        · simp [Exp.cost] at hc5 ⊢; omega
        · intro r h1 h2 h3 h4 h5 h6 h7 h8
          simp only [Machine.State.upd, ite_eq_right h1]
          rw [hF5 r h4 h5 h6 h7 h8]; simp only [L4, Machine.State.upd, ite_eq_right h2,
            ite_eq_right h3]
          exact hF r h1 h2 h3 h4 h5 h6 h7 h8
        · rw [hgetD, ite_eq_left hpj]; simp [Machine.State.upd]
      · refine ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e5 (evalF_ite_f
          (by
            simp only [Exp.ev, hq5, Option.some.injEq, ite_eq_right_iff, one_ne_zero,
              imp_false, not_and]
            intro a b
            exact hpj ((hsel _).mp ⟨a, b⟩)) evalF_skip)), ?_, ?_, ?_⟩
        · simp [Exp.cost] at hc5 ⊢; omega
        · intro r h1 h2 h3 h4 h5 h6 h7 h8
          rw [hF5 r h4 h5 h6 h7 h8]; simp only [L4, Machine.State.upd, ite_eq_right h2,
            ite_eq_right h3]
          exact hF r h1 h2 h3 h4 h5 h6 h7 h8
        · rw [hgetD, ite_eq_right hpj, hc5']; rfl)
  have hcnt : L3 "cnt" = (part t v side sd).length := by
    have h0 : L2 "cnt" = 0 := by simp [L2, Machine.State.upd]
    rw [ha3, h0, foldl_count p o n (by omega), ← hon, List.take_length]; rfl
  exact ⟨L3, c3, e3, hc3, hF3, hcnt⟩

theorem tabS_ok {κ : Caps} {St t : Core} {L : Loc} {v w : Nat} {side : List (Nat × Side)} {sd :
  Side}
    (hR : ReadOK St t v side) (hP : St.P = t.P) (hw0 : (St.nodes.getX w).table = []) (hwv : w ≠ v)
    (hws : w < St.nodes.size)
    (hLv : L "v" = v) (hLw : L "w" = w) (hLh : L "h" = sH t v) (hLs : L "sd" = sideN sd)
    (hvc : v < κ.lrec .children) (hvs : v < κ.lrec .side) (hvt : v < κ.lrec .table) (hwt : w <
      κ.lrec .table)
    (hN : ∀ e ∈ (t.nodes.getX v).table.map (·.1), e < κ.tbl .N)
    (hcap : (t.nodes.getX v).table.length ≤ κ.lcap .table) :
    ∃ L' c, evalF κ tabS St L = .ok (LK.put St w (evenTable t.P.beta (part t v side sd)) .table)
      L' c ∧
      c ≤ 20 + (t.nodes.getX v).table.length * (320 + 40 * (t.nodes.getX v).children.length +
        40 * side.length) ∧
      ∀ r, r ≠ "nt" → r ≠ "cnt" → r ≠ "j" → r ≠ "e" → r ≠ "r" → r ≠ "m" → r ≠ "f" → r ≠ "x" → r
        ≠ "q" →
        r ≠ "st" → r ≠ "idx" → L' r = L r := by
  set o := (t.nodes.getX v).table.map (·.1)
  set n := (t.nodes.getX v).table.length
  set K := (t.nodes.getX v).children.length
  set p := selP t v side sd
  have hon : o.length = n := by simp [o, n]
  have hvT : LK.view St v .table = (t.nodes.getX v).table := by simp [LK.view, hR.tab]
  have hsel : ∀ e, (entOK t v e = true ∧ lookup side e = some sd) ↔ p e = true := by
    intro e; simp [p, selP]
  have hoj : ∀ j (hj : j < n), ((t.nodes.getX v).table[j]?.getD (0, 0)).1 = o[j]'(by omega) := by
    intro j hj; simp [o, List.getElem?_eq_getElem hj]
  -- the count
  have a1 := evalF_assign_ok (κ := κ) (s := St) (L := L) (x := "nt") (e := .llen .table "v") (v
    := n)
    (by simp [Exp.ev, hLv, hvt, hvT, n])
  have a2 := evalF_assign_ok (κ := κ) (s := St) (L := upd L "nt" n) (x := "cnt") (e := (0 :
    Exp)) (v := 0) rfl
  set L2 := upd (upd L "nt" n) "cnt" 0
  have hL2 : ∀ r, r ≠ "nt" → r ≠ "cnt" → L2 r = L r := fun r h1 h2 => by simp [L2,
    Machine.State.upd, h1, h2]
  obtain ⟨L3, c3, e3, hc3, hF3, hcnt⟩ :=
    count_selected_entries hR hLv hLh hLs hvc hvs hvt hN
  change c3 ≤ 1 + (.var "nt" : Exp).cost +
    n * (1 + (140 + 20 * K + 20 * side.length)) at hc3
  -- the spacing
  set pl := part t v side sd
  set st := (1 <<< t.P.beta) / (pl.length + 1)
  have a3 := evalF_assign_ok (κ := κ) (s := St) (L := L3) (x := "st") (e := .bin .shl 1 (.prm
    .beta) / ("cnt" + 1))
    (v := st) (by simp [Exp.ev, Machine.BinOp.eval, PF.get, hP, hcnt, st, Nat.shiftLeft_eq])
  have a4 := evalF_assign_ok (κ := κ) (s := St) (L := upd L3 "st" st) (x := "idx") (e := (0 :
    Exp)) (v := 0) rfl
  set L5 := upd (upd L3 "st" st) "idx" 0
  have hL5 : ∀ r, r ≠ "nt" → r ≠ "cnt" → r ≠ "j" → r ≠ "e" → r ≠ "r" → r ≠ "m" → r ≠ "f" → r ≠
    "x" → r ≠ "q" →
      r ≠ "st" → r ≠ "idx" → L5 r = L r := by
    intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    simp only [L5, Machine.State.upd, ite_eq_right h10, ite_eq_right h11]
    rw [hF3 r h2 h3 h4 h5 h6 h7 h8 h9]
    change L2 r = L r
    exact hL2 r h1 h2
  -- the build
  have hwi : LK.table.idOk St w := by simp [LK.idOk, LK.recOk, hws]
  have hput0 : LK.put St w [] .table = St := by
    have := LK.put_view hwi; simp only [LK.view, hw0] at this; exact this
  have hR' : ∀ l, ReadOK (LK.put St w l .table) t v side := fun l => hR.put_table hwv l
  have hvT' : ∀ l, LK.view (LK.put St w l .table) v .table = (t.nodes.getX v).table := by
    intro l; rw [LK.view_put (by simp [LK.recOk, hws]) (by simp [LK.valid])]; simp [Ne.symm hwv,
      hvT]
  have hwT' : ∀ l, LK.view (LK.put St w l .table) w .table = l := by
    intro l; rw [LK.view_put (by simp [LK.recOk, hws]) (by simp [LK.valid])]; simp
  have hlenf : ∀ j, ((o.take j).filter p).length ≤ n := by
    intro j; have := List.length_filter_le p (o.take j); simp at this; omega
  obtain ⟨S6, L6, c6, e6, hc6, hS6, hi6, hF6⟩ := evalF_loop (κ := κ) (x := "j") (n := .var "nt")
    (b := bldBody)
    (s := St) (L := L5) (N := n) (by
      simp only [Exp.ev, Machine.State.upd, String.reduceEq, ↓reduceIte, Option.some.injEq, L5]
      rw [hF3 "nt" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
        decide) (by decide)]
      simp [Machine.State.upd, n])
    (fun j S L' => S = LK.put St w (evT st ((o.take j).filter p)) .table ∧
      L' "idx" = ((o.take j).filter p).length ∧
      ∀ r, r ≠ "j" → r ≠ "e" → r ≠ "r" → r ≠ "m" → r ≠ "f" → r ≠ "x" → r ≠ "q" → r ≠ "idx" → L'
        r = L5 r)
    (170 + 20 * K + 20 * side.length)
    ⟨by simp [evT,
      hput0], by simp [L5, Machine.State.upd], fun _ _ _ _ _ _ _ _ _ => rfl⟩
    (by
      intro j hj S1 L' ⟨hS1, hidx, hF⟩
      subst hS1
      set fj := (o.take j).filter p
      set S1 := LK.put St w (evT st fj) .table
      have hvS1 : LK.view S1 v .table = (t.nodes.getX v).table := hvT' _
      have hwS1 : LK.view S1 w .table = evT st fj := hwT' _
      have hv' : L' "v" = v := by
        rw [hF "v" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
          decide) (by decide),
          hL5 "v" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
            decide) (by decide)
            (by decide) (by decide) (by decide), hLv]
      have hfr : ∀ r, r ≠ "j" → r ≠ "e" → r ≠ "r" → r ≠ "m" → r ≠ "f" → r ≠ "x" → r ≠ "q" → r ≠
        "idx" →
          r ≠ "nt" → r ≠ "cnt" → r ≠ "st" → L' r = L r := by
        intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
        rw [hF r h1 h2 h3 h4 h5 h6 h7 h8, hL5 r h9 h10 h1 h2 h3 h4 h5 h6 h7 h11 h8]
      have e1 := evalF_assign_ok (κ := κ) (s := S1) (L := upd L' "j" j) (x := "e") (e := .lrd
        .table false "v" "j")
        (v := o[j]'(by omega)) (by
          have hj2 : j < (t.nodes.getX v).table.length := hj
          have hoj2 : (t.nodes.getX v).table[j].1 = o[j]'(by omega) := by simp [o]
          simp [Exp.ev, Machine.State.upd, hv', hvt, hvS1, hj2, hoj2])
      set L4 := upd (upd L' "j" j) "e" (o[j]'(by omega))
      obtain ⟨L7, c7, e7, hq7, hc7, hF7⟩ := selS_ok (κ := κ) (St := S1) (t := t) (L := L4) (v := v)
        (e := o[j]'(by omega)) (side := side) (sd := sd) (hR' _)
        (by simp [L4, Machine.State.upd, hv'])
        (by simp only [L4, Machine.State.upd]; simp only [String.reduceEq, ↓reduceIte]
            rw [hfr "h" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide)
              (by decide) (by decide) (by decide) (by decide), hLh])
        (by simp [L4, Machine.State.upd])
        (by simp only [L4, Machine.State.upd]; simp only [String.reduceEq, ↓reduceIte]
            rw [hfr "sd" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide)
              (by decide) (by decide) (by decide) (by decide), hLs])
        hvc hvs (hN _ (List.getElem_mem _))
      have h7i : L7 "idx" = fj.length := by
        rw [hF7 "idx" (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp [L4, Machine.State.upd, hidx]
      have h7w : L7 "w" = w := by
        rw [hF7 "w" (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp only [L4, Machine.State.upd]; simp only [String.reduceEq, ↓reduceIte]
        rw [hfr "w" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
          decide)
          (by decide) (by decide) (by decide) (by decide), hLw]
      have h7e : L7 "e" = o[j]'(by omega) := by
        rw [hF7 "e" (by decide) (by decide) (by decide) (by decide) (by decide)]; simp [L4,
          Machine.State.upd]
      have h7st : L7 "st" = st := by
        rw [hF7 "st" (by decide) (by decide) (by decide) (by decide) (by decide)]
        simp only [L4, Machine.State.upd]; simp only [String.reduceEq, ↓reduceIte]
        rw [hF "st" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
          decide) (by decide)]
        simp [L5, Machine.State.upd]
      have hfr7 : ∀ r, r ≠ "j" → r ≠ "e" → r ≠ "r" → r ≠ "m" → r ≠ "f" → r ≠ "x" → r ≠ "q" → r ≠
        "idx" →
          L7 r = L5 r := by
        intro r h1 h2 h3 h4 h5 h6 h7 h8
        rw [hF7 r h3 h4 h5 h6 h7]; simp only [L4, Machine.State.upd, ite_eq_right h1,
          ite_eq_right h2]
        exact hF r h1 h2 h3 h4 h5 h6 h7 h8
      have htk : (o.take (j + 1)).filter p = fj ++ (if p (o[j]'(by omega)) then [o[j]'(by
        omega)] else []) := by
        rw [List.take_succ_eq_append_getElem (by omega), List.filter_append]
        by_cases hpj : p (o[j]'(by omega)) = true <;> simp [hpj, fj]
      by_cases hpj : p (o[j]'(by omega)) = true
      · have e8 := evalF_assign_ok (κ := κ) (s := S1) (L := L7) (x := "idx") (e := "idx" + 1) (v
          := fj.length + 1)
          (by simp [Exp.ev, Machine.BinOp.eval, h7i])
        set L8 := upd L7 "idx" (fj.length + 1)
        have hfj : fj.length + 1 ≤ n := by
          have := hlenf (j + 1); rw [htk, ite_eq_left hpj] at this; simpa using this
        have hso := LK.set_ok (κ := κ) (s := S1) (i := w)
          (l := evT st fj ++ [(o[j]'(by omega), (fj.length + 1) * st)]) (k := .table)
          (by simp [S1, LK.recOk, hws]) (by simp [LK.valid]) (by simp [length_evT]; omega) hwt
        rw [LK.put_put] at hso
        have e9 : evalF κ (.lgrow .table "w" "e" ("idx" * "st")) S1 L8 =
            .ok (LK.put St w (evT st fj ++ [(o[j]'(by omega), (fj.length + 1) * st)]) .table) L8
              24 := by
          simp only [evalF, Exp.ev, L8, Machine.State.upd, h7w, h7e, h7st,
            Machine.BinOp.eval, Option.bind_some, Exp.cost]
          simp only [show ("w" = "idx") = False by decide, show ("e" = "idx") = False by decide,
            show ("st" = "idx") = False by decide,  ite_true, ite_false,
             ]
          rw [hwS1, hso]
        rw [← evT_append,
          ← (ite_eq_left hpj : (if p (o[j]'(by omega)) then [o[j]'(by omega)] else []) = _),
          ← htk] at e9
        refine ⟨_, _, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e7 (evalF_ite_t (v := 1)
          (by simp [Exp.ev, hq7,
            (hsel _).mpr hpj]) one_ne_zero (evalF_seq_ok2 e8 e9))), ?_, rfl, ?_, ?_⟩
        · simp [Exp.cost] at hc7 ⊢; omega
        · simp only [L8, Machine.State.upd,
          ite_true]; rw [htk, ite_eq_left hpj]; simp
        · intro r h1 h2 h3 h4 h5 h6 h7 h8
          simp only [L8, Machine.State.upd,
            ite_eq_right h8]; exact hfr7 r h1 h2 h3 h4 h5 h6 h7 h8
      · refine ⟨_, _, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e7 (evalF_ite_f
          (by
            simp only [Exp.ev, hq7, Option.some.injEq, ite_eq_right_iff, one_ne_zero,
              imp_false, not_and]
            intro a b
            exact hpj ((hsel _).mp ⟨a, b⟩)) evalF_skip)), ?_, ?_, ?_, ?_⟩
        · simp [Exp.cost] at hc7 ⊢; omega
        · rw [htk, ite_eq_right hpj, List.append_nil]
        · rw [htk, ite_eq_right hpj, List.append_nil, h7i]
        · exact hfr7)
  rw [hS6, ← hon, List.take_length] at e6
  have hfin : evT st (o.filter p) = evenTable t.P.beta pl := by rw [evenTable_evT]; rfl
  rw [hfin] at e6
  refine ⟨L6, _, evalF_seq_ok2 a1 (evalF_seq_ok2 a2 (evalF_seq_ok2 e3 (evalF_seq_ok2 a3
    (evalF_seq_ok2 a4 e6)))),
    ?_, ?_⟩
  · simp only [Exp.cost, Exp.div_def, Exp.add_def, Exp.ofNat_def] at hc3 hc6 ⊢
    have h1 : n * (1 + (140 + 20 * K + 20 * side.length)) + n * (1 + (170 + 20 * K + 20 *
      side.length)) ≤
        n * (320 + 40 * K + 40 * side.length) := by
      have : n * (1 + (140 + 20 * K + 20 * side.length)) + n * (1 + (170 + 20 * K + 20 *
        side.length)) =
          n * (312 + 40 * K + 40 * side.length) := by ring
      rw [this]; exact Nat.mul_le_mul_left _ (by omega)
    omega
  · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    rw [hF6 r h3 h4 h5 h6 h7 h8 h9 h11, hL5 r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11]

theorem aroundStep_first (t : Core) (v : Nat) (ns : Array Node) (T e : Nat) :
    ((aroundStep t v ns T).getX e).first = (ns.getX e).first := by
  simp only [aroundStep, getX_modify']; split <;> rfl

theorem fold_aroundStep_first (t : Core) (v e : Nat) : ∀ (l : List Nat) (ns : Array Node),
    ((l.foldl (aroundStep t v) ns).getX e).first = (ns.getX e).first
  | [], _ => rfl
  | T :: l, ns => by
    simp only [List.foldl_cons]; rw [fold_aroundStep_first t v e l, aroundStep_first]

theorem sd1_first (t : Core) (v e : Nat) : ((sd1 t v).nodes.getX e).first = (t.nodes.getX
  e).first := by
  simp only [sd1, getX_push', Array.size_push]
  split
  · rw [getX_size_le (by omega)]; rfl
  · split
    · rw [getX_size_le (by omega)]; rfl
    · rfl

theorem sd2_first (t : Core) (v e : Nat) : ((sd2 t v).nodes.getX e).first = (t.nodes.getX
  e).first := by
  rw [← sdJ_all]; simp only [sdJ]; rw [fold_aroundStep_first, sd1_first]

theorem sd2_getX_v {t : Core} {v : Nat} (hv : v < t.nodes.size) (hvT : v ∉ (t.nodes.getX
  v).inTables) :
    (sd2 t v).nodes.getX v = t.nodes.getX v := by
  rw [← sdJ_all]; exact sdJ_getX_notin (fun h => hvT (List.mem_of_mem_take h)) hv

theorem sd2_getX_new {t : Core} {v u : Nat} (hroom : ∀ T ∈ (t.nodes.getX v).inTables, RoomOK t v T)
    (hu : t.nodes.size ≤ u) (hu2 : u < t.nodes.size + 2) : (sd2 t v).nodes.getX u = {
      height := sH t v
    } := by
  rw [← sdJ_all]
  rw [sdJ_getX_notin' (fun h => by have := (hroom u (List.mem_of_mem_take h)).lt; omega)]
  simp only [sd1, getX_push', Array.size_push]
  by_cases e : u = t.nodes.size + 1
  · rw [ite_eq_left e]
  · rw [ite_eq_right e, ite_eq_left (by omega)]

theorem ReadOK.of_sd2 {t : Core} {v : Nat} {side : List (Nat × Side)} (hv : v < t.nodes.size)
    (hvT : v ∉ (t.nodes.getX v).inTables) : ReadOK (phiS v side (sd2 t v)) t v side := by
  have hsz : v < (sd2 t v).nodes.size := by rw [← sdJ_all, sdJ_size]; omega
  refine ⟨?_, ?_, ?_, fun e => ?_⟩
  · rw [phiS_getX_self hsz, sd2_getX_v hv hvT]
  · rw [phiS_getX_self hsz, sd2_getX_v hv hvT]
  · rw [phiS_getX_self hsz]
  · by_cases h : e = v
    · subst h; rw [phiS_getX_self hsz, sd2_getX_v hv hvT]
    · rw [phiS_getX_ne h, sd2_first]

theorem ReadOK.put_inTab {St t : Core} {v w : Nat} {side : List (Nat × Side)} (hR : ReadOK St t
  v side)
    (hw : w ≠ v) (l : List (Nat × Nat)) : ReadOK (LK.put St w l .inTab) t v side := by
  have hg : ∀ u, u ≠ w → (LK.put St w l .inTab).nodes.getX u = St.nodes.getX u := by
    intro u hu; simp only [LK.put, getX_modify']; rw [ite_eq_right (fun h => hu h.1)]
  have hf : ∀ u, ((LK.put St w l .inTab).nodes.getX u).first = (St.nodes.getX u).first := by
    intro u; simp only [LK.put, getX_modify']; split <;> rfl
  exact ⟨by rw [hg v (Ne.symm hw)]; exact hR.tab, by rw [hg v (Ne.symm hw)]; exact hR.kids,
    by rw [hg v (Ne.symm hw)]; exact hR.side, fun u => by rw [hf]; exact hR.first u⟩

/-- A new node `w` takes `v`'s tables and its share of `v`'s entries (side `sd`). -/
def newTabS : Stm := cm{ a := v; ‹copyS .inTab›; tabS }

theorem newTabS_ok {κ : Caps} {St t : Core} {L : Loc} {v w : Nat} {side : List (Nat × Side)} {sd
  : Side}
    (hR : ReadOK St t v side) (hP : St.P = t.P) (hw0 : (St.nodes.getX w).table = [])
    (hw1 : (St.nodes.getX w).inTables = []) (hwv : w ≠ v) (hws : w < St.nodes.size)
    (hvi : (St.nodes.getX v).inTables = (t.nodes.getX v).inTables)
    (hLv : L "v" = v) (hLw : L "w" = w) (hLh : L "h" = sH t v) (hLs : L "sd" = sideN sd)
    (hvc : v < κ.lrec .children) (hvs : v < κ.lrec .side) (hvt : v < κ.lrec .table) (hwt : w <
      κ.lrec .table)
    (hvI : v < κ.lrec .inTab) (hwI : w < κ.lrec .inTab)
    (hN : ∀ e ∈ (t.nodes.getX v).table.map (·.1), e < κ.tbl .N)
    (hcap : (t.nodes.getX v).table.length ≤ κ.lcap .table)
    (hcapI : (t.nodes.getX v).inTables.length ≤ κ.lcap .inTab) :
    ∃ L' c, evalF κ newTabS St L = .ok (LK.put (LK.put St w ((t.nodes.getX v).inTables.map fun e
      => (e, 0)) .inTab)
        w (evenTable t.P.beta (part t v side sd)) .table) L' c ∧
      c ≤ 30 + 40 * (t.nodes.getX v).inTables.length + (t.nodes.getX v).table.length *
        (320 + 40 * (t.nodes.getX v).children.length + 40 * side.length) ∧
      ∀ r, r ≠ "a" → r ≠ "n" → r ≠ "j" → r ≠ "nt" → r ≠ "cnt" → r ≠ "e" → r ≠ "r" → r ≠ "m" → r
        ≠ "f" →
        r ≠ "x" → r ≠ "q" → r ≠ "st" → r ≠ "idx" → L' r = L r := by
  have a1 := evalF_assign_ok (κ := κ) (s := St) (L := L) (x := "a") (e := .var "v") (v := v) (by
    simp [Exp.ev, hLv])
  set L1 := upd L "a" v
  have hvw : LK.view St w .inTab = [] := by simp [LK.view, hw1]
  have hvv : LK.view St v .inTab = (t.nodes.getX v).inTables.map fun e => (e, 0) := by
    simp [LK.view, hvi]
  obtain ⟨L2, c2, e2, hc2, hF2⟩ := copyS_ok (κ := κ) (k := .inTab) (s := St) (L := L1) (a := v)
    (w := w)
    (by simp [L1,
      Machine.State.upd]) (by simp [L1, Machine.State.upd,
      hLw]) hwv
    (by simp [LK.idOk, LK.recOk,
      hws]) (by simp [LK.recOk, hws]) hvI hwI (by rw [hvw, hvv]; simpa using hcapI)
  rw [hvw, hvv, List.nil_append] at e2
  rw [hvv] at hc2
  set St1 := LK.put St w ((t.nodes.getX v).inTables.map fun e => (e, 0)) .inTab
  have hgw : St1.nodes.getX w = {
    St.nodes.getX w with
    inTables := (t.nodes.getX v).inTables
  } := by
    simp [St1, LK.put,  hws, Function.comp_def]
  have hfr2 : ∀ r, r ≠ "a" → r ≠ "n" → r ≠ "j" → L2 r = L r := fun r h1 h2 h3 => by
    rw [hF2 r h2 h3]; simp [L1, Machine.State.upd, h1]
  obtain ⟨L3, c3, e3, hc3, hF3⟩ := tabS_ok (κ := κ) (St := St1) (t := t) (L := L2) (v := v) (w
    := w) (side := side)
    (sd := sd) (hR.put_inTab hwv _) (by simp [St1, LK.put, hP]) (by rw [hgw]; exact hw0)
    hwv (by simp [St1, LK.put, hws])
    (by rw [hfr2 "v" (by decide) (by decide) (by decide), hLv])
    (by rw [hfr2 "w" (by decide) (by decide) (by decide), hLw])
    (by rw [hfr2 "h" (by decide) (by decide) (by decide), hLh])
    (by rw [hfr2 "sd" (by decide) (by decide) (by decide), hLs]) hvc hvs hvt hwt hN hcap
  refine ⟨L3, _, evalF_seq_ok2 a1 (evalF_seq_ok2 e2 e3), ?_, ?_⟩
  · simp only [List.length_map, Exp.cost] at hc2 hc3 ⊢; omega
  · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13
    rw [hF3 r h4 h5 h3 h6 h7 h8 h9 h10 h11 h12 h13, hfr2 r h1 h2 h3]

/-- Build the left and right target tables from their selected drain entries. -/
def stage3S : Stm := cm{
  w := v1; sd := 0; newTabS
  w := v2; sd := 1; newTabS }

theorem stage3_state (t : Core) (v : Nat) (side : List (Nat × Side)) (hv : v < t.nodes.size) :
    LK.put (LK.put (LK.put (LK.put (phiS v side (sd2 t v)) t.nodes.size
      ((t.nodes.getX v).inTables.map fun e => (e, 0)) .inTab) t.nodes.size
        (evenTable t.P.beta (part t v side .left)) .table) (t.nodes.size + 1)
      ((t.nodes.getX v).inTables.map fun e => (e, 0)) .inTab) (t.nodes.size + 1)
        (evenTable t.P.beta (part t v side .right)) .table = phiS v side (sd4 t v side) := by
  simp only [LK.put, phiS, sd4, Array.modify_modify_same, ← sLeft_part, ← sRight_part]
  rw [Array.modify_comm _ (show v ≠ t.nodes.size by omega),
    Array.modify_comm _ (show v ≠ t.nodes.size + 1 by omega)]
  simp only [Function.comp_def, List.map_map, List.map_id']

theorem put_getX_ne_t {St : Core} {w u : Nat} {l : List (Nat × Nat)} (h : u ≠ w) :
    (LK.put St w l .table).nodes.getX u = St.nodes.getX u := by
  simp only [LK.put, getX_modify']; rw [ite_eq_right (fun e => h e.1)]

theorem put_getX_ne_i {St : Core} {w u : Nat} {l : List (Nat × Nat)} (h : u ≠ w) :
    (LK.put St w l .inTab).nodes.getX u = St.nodes.getX u := by
  simp only [LK.put, getX_modify']; rw [ite_eq_right (fun e => h e.1)]

theorem stage3S_ok {κ : Caps} {t : Core} {L : Loc} {v : Nat} {side : List (Nat × Side)}
    (hv : v < t.nodes.size) (hvT : v ∉ (t.nodes.getX v).inTables)
    (hroom : ∀ T ∈ (t.nodes.getX v).inTables, RoomOK t v T)
    (hLv : L "v" = v) (hLv1 : L "v1" = t.nodes.size) (hLv2 : L "v2" = t.nodes.size + 1) (hLh : L
      "h" = sH t v)
    (hvc : v < κ.lrec .children) (hvs : v < κ.lrec .side) (hvt : v < κ.lrec .table)
    (hwt : t.nodes.size + 1 < κ.lrec .table) (hvI : v < κ.lrec .inTab) (hwI : t.nodes.size + 1 <
      κ.lrec .inTab)
    (hN : ∀ e ∈ (t.nodes.getX v).table.map (·.1), e < κ.tbl .N)
    (hcap : (t.nodes.getX v).table.length ≤ κ.lcap .table)
    (hcapI : (t.nodes.getX v).inTables.length ≤ κ.lcap .inTab) :
    ∃ L' c, evalF κ stage3S (phiS v side (sd2 t v)) L = .ok (phiS v side (sd4 t v side)) L' c ∧
      c ≤ 70 + 80 * (t.nodes.getX v).inTables.length + 2 * ((t.nodes.getX v).table.length *
        (320 + 40 * (t.nodes.getX v).children.length + 40 * side.length)) ∧
      ∀ r, r ≠ "w" → r ≠ "sd" → r ≠ "a" → r ≠ "n" → r ≠ "j" → r ≠ "nt" → r ≠ "cnt" → r ≠ "e" → r
        ≠ "r" →
        r ≠ "m" → r ≠ "f" → r ≠ "x" → r ≠ "q" → r ≠ "st" → r ≠ "idx" → L' r = L r := by
  set N := t.nodes.size
  set S2 := phiS v side (sd2 t v)
  have hS2sz : S2.nodes.size = N + 2 := by simp [S2, phiS, ← sdJ_all, sdJ_size, N]
  have hNv : N ≠ v := by omega
  have hN1v : N + 1 ≠ v := by omega
  have hS2N : S2.nodes.getX N = {
    height := sH t v
  } := by
    rw [phiS_getX_ne hNv, sd2_getX_new hroom le_rfl (by omega)]
  have hS2N1 : S2.nodes.getX (N + 1) = {
    height := sH t v
  } := by
    rw [phiS_getX_ne hN1v, sd2_getX_new hroom (by omega) (by omega)]
  have hS2v : (S2.nodes.getX v).inTables = (t.nodes.getX v).inTables := by
    rw [phiS_getX_self (by rw [← sdJ_all, sdJ_size]; omega), sd2_getX_v hv hvT]
  have a1 := evalF_assign_ok (κ := κ) (s := S2) (L := L) (x := "w") (e := .var "v1") (v := N)
    (by simp [Exp.ev, hLv1])
  have a2 := evalF_assign_ok (κ := κ) (s := S2) (L := upd L "w" N) (x := "sd") (e := (0 : Exp))
    (v := 0) rfl
  set L2 := upd (upd L "w" N) "sd" 0
  have hL2 : ∀ r, r ≠ "w" → r ≠ "sd" → L2 r = L r := fun r h1 h2 => by simp [L2,
    Machine.State.upd, h1, h2]
  obtain ⟨L3, c3, e3, hc3, hF3⟩ := newTabS_ok (κ := κ) (St := S2) (t := t) (L := L2) (v := v) (w
    := N) (side := side)
    (sd := .left) (ReadOK.of_sd2 hv hvT) rfl (by rw [hS2N]) (by rw [hS2N]) hNv (by omega) hS2v
    (by rw [hL2 "v" (by decide) (by decide),
      hLv]) (by simp [L2, Machine.State.upd])
    (by rw [hL2 "h" (by decide) (by decide),
      hLh]) (by simp [L2, Machine.State.upd, sideN]) hvc hvs hvt
    (by omega) hvI (by omega) hN hcap hcapI
  set X1 := LK.put (LK.put S2 N ((t.nodes.getX v).inTables.map fun e => (e, 0)) .inTab) N
    (evenTable t.P.beta (part t v side .left)) .table
  have hX1N1 : X1.nodes.getX (N + 1) = {
    height := sH t v
  } := by
    rw [put_getX_ne_t (by omega), put_getX_ne_i (by omega), hS2N1]
  have hX1v : (X1.nodes.getX v).inTables = (t.nodes.getX v).inTables := by
    rw [put_getX_ne_t (Ne.symm hNv), put_getX_ne_i (Ne.symm hNv), hS2v]
  have hfr3 : ∀ r, r ≠ "w" → r ≠ "sd" → r ≠ "a" → r ≠ "n" → r ≠ "j" → r ≠ "nt" → r ≠ "cnt" → r ≠
    "e" → r ≠ "r" →
      r ≠ "m" → r ≠ "f" → r ≠ "x" → r ≠ "q" → r ≠ "st" → r ≠ "idx" → L3 r = L r := by
    intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    rw [hF3 r h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15, hL2 r h1 h2]
  have a3 := evalF_assign_ok (κ := κ) (s := X1) (L := L3) (x := "w") (e := .var "v2") (v := N + 1)
    (by simp [Exp.ev,
      hfr3 "v2" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
        decide), hLv2])
  have a4 := evalF_assign_ok (κ := κ) (s := X1) (L := upd L3 "w" (N + 1)) (x := "sd") (e := (1 :
    Exp)) (v := 1) rfl
  set L4 := upd (upd L3 "w" (N + 1)) "sd" 1
  have hL4 : ∀ r, r ≠ "w" → r ≠ "sd" → r ≠ "a" → r ≠ "n" → r ≠ "j" → r ≠ "nt" → r ≠ "cnt" → r ≠
    "e" → r ≠ "r" →
      r ≠ "m" → r ≠ "f" → r ≠ "x" → r ≠ "q" → r ≠ "st" → r ≠ "idx" → L4 r = L r := by
    intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    simp only [L4, Machine.State.upd, ite_eq_right h1, ite_eq_right h2]
    exact hfr3 r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
  obtain ⟨L5, c5, e5, hc5, hF5⟩ := newTabS_ok (κ := κ) (St := X1) (t := t) (L := L4) (v := v) (w
    := N + 1)
    (side := side) (sd := .right) (((ReadOK.of_sd2 hv hvT).put_inTab hNv _).put_table hNv _) (by
      simp [X1, LK.put, S2, phiS]; rfl)
    (by rw [hX1N1]) (by rw [hX1N1]) hN1v (by simp [X1, LK.put, hS2sz]) hX1v
    (by rw [hL4 "v" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hLv])
    (by simp [L4, Machine.State.upd])
    (by rw [hL4 "h" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hLh])
    (by simp [L4, Machine.State.upd, sideN]) hvc hvs hvt hwt hvI hwI hN hcap hcapI
  rw [stage3_state t v side hv] at e5
  refine ⟨L5, _, evalF_seq_ok2 a1 (evalF_seq_ok2 a2 (evalF_seq_ok2 e3 (evalF_seq_ok2 a3
    (evalF_seq_ok2 a4 e5)))),
    ?_, ?_⟩
  · simp only [Exp.cost] at hc3 hc5 ⊢; omega
  · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15
    rw [hF5 r h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15,
      hL4 r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15]

/-! ### Stage 4: the entries learn their new tables -/

/-- Record one newly built table in an entry's containing-table list. -/
def atBody : Stm := cm{
  e := table[w][j].fst
  if h ≤ 1 then append cin[e] (w, 0) else append inTab[e] (w, 0) }
/-- Record the new table membership of every entry in one drain target. -/
def atS : Stm := cm{ nt := len table[w]; for j < nt do atBody }

theorem addTableS_table (h w e : Nat) (s : Core) (u : Nat) :
    ((addTableS h w e s).nodes.getX u).table = (s.nodes.getX u).table := by
  unfold addTableS; split
  · rfl
  · simp only [getX_modify']; split <;> rfl

theorem addTableS_size (h w e : Nat) (s : Core) : (addTableS h w e s).nodes.size = s.nodes.size
  := by
  unfold addTableS; split <;> simp

theorem addTableS_P (h w e : Nat) (s : Core) : (addTableS h w e s).P = s.P := by
  unfold addTableS; split <;> rfl

/-- How long a list of tables can get during the loop. -/
def tabsLen (s : Core) (hh e : Nat) : Nat := if hh = 0 then (s.cin.getX e).length else
  (s.nodes.getX e).inTables.length

theorem tabsLen_addTableS (hh w e u : Nat) (s : Core) :
    tabsLen (addTableS hh w e s) hh u ≤ tabsLen s hh u + 1 := by
  unfold tabsLen addTableS
  by_cases h0 : hh = 0
  · simp only [h0, ite_true]; rw [getX_setX']; split
    · next e' => subst e'; simp
    · omega
  · simp only [h0, ite_false]; rw [getX_modify']; split
    · next e' => obtain ⟨rfl, -⟩ := e'; simp
    · omega

theorem atS_ok {κ : Caps} {St : Core} {L : Loc} {w hh : Nat} {l : List Nat}
    (hLw : L "w" = w) (hLh : L "h" = hh) (hwt : w < κ.lrec .table)
    (hkeys : (St.nodes.getX w).table.map (·.1) = l)
    (hE : ∀ e ∈ l, (hh ≤ 1 → e < κ.lrec .cin) ∧ (1 < hh → e < κ.lrec .inTab ∧ e < St.nodes.size))
    (hcap : ∀ e ∈ l, tabsLen St (hh - 1) e + l.length ≤ (if hh ≤ 1 then κ.lcap .cin else κ.lcap
      .inTab)) :
    ∃ L' c, evalF κ atS St L = .ok (l.foldl (fun s e => addTableS (hh - 1) w e s) St) L' c ∧
      c ≤ 5 + 40 * l.length ∧ ∀ r, r ≠ "nt" → r ≠ "j" → r ≠ "e" → L' r = L r := by
  set F := fun (s : Core) (e : Nat) => addTableS (hh - 1) w e s
  have hfoldT : ∀ (m : List Nat) (s : Core) u, ((m.foldl F s).nodes.getX u).table =
    (s.nodes.getX u).table := by
    intro m; induction m with
    | nil => intro s u; rfl
    | cons e m ih => intro s u; simp only [List.foldl_cons]; rw [ih, addTableS_table]
  have hfoldS : ∀ (m : List Nat) (s : Core), (m.foldl F s).nodes.size = s.nodes.size := by
    intro m; induction m with
    | nil => intro s; rfl
    | cons e m ih => intro s; simp only [List.foldl_cons]; rw [ih, addTableS_size]
  have hln : (St.nodes.getX w).table.length = l.length := by rw [← hkeys, List.length_map]
  have a1 := evalF_assign_ok (κ := κ) (s := St) (L := L) (x := "nt") (e := .llen .table "w") (v
    := l.length)
    (by simp [Exp.ev, hLw, hwt, LK.view, hln])
  obtain ⟨S', L', c, he, hc, hS', hF, -⟩ := evalF_loop (κ := κ) (x := "j") (n := .var "nt") (b
    := atBody)
    (s := St) (L := upd L "nt" l.length) (N := l.length) (by simp [Exp.ev, Machine.State.upd])
    (fun j S L' => S = (l.take j).foldl F St ∧ (∀ r, r ≠ "nt" → r ≠ "j" → r ≠ "e" → L' r = L r) ∧
      ∀ u, tabsLen S (hh - 1) u ≤ tabsLen St (hh - 1) u + j) 33
    ⟨by simp, fun r h1 _ _ => by simp [Machine.State.upd, h1], fun u => by omega⟩
    (by
      intro j hj S L1 ⟨hS, hF1, hlen⟩
      subst hS
      set S := (l.take j).foldl F St
      have hwv : LK.view S w .table = (St.nodes.getX w).table := by simp [LK.view, S, hfoldT]
      have hlj : l[j] ∈ l := List.getElem_mem hj
      have hkj : (St.nodes.getX w).table[j].1 = l[j] := by
        subst hkeys; simp
      set L2 := upd L1 "j" j
      have h2w : L2 "w" = w := by
        simp only [Machine.State.upd, String.reduceEq, ↓reduceIte, L2]
        rw [hF1 "w" (by decide) (by decide) (by decide), hLw]
      have h2h : L2 "h" = hh := by
        simp only [Machine.State.upd, String.reduceEq, ↓reduceIte, L2]
        rw [hF1 "h" (by decide) (by decide) (by decide), hLh]
      have e1 := evalF_assign_ok (κ := κ) (s := S) (L := L2) (x := "e") (e := .lrd .table false
        "w" "j") (v := l[j])
        (by simp [Exp.ev, h2w, hwt, hwv,
          show L2 "j" = j by simp [L2, Machine.State.upd], hln, hj, hkj])
      set L3 := upd L2 "e" l[j]
      have h3w : L3 "w" = w := by simp [L3, Machine.State.upd, h2w]
      have h3h : L3 "h" = hh := by simp [L3, Machine.State.upd, h2h]
      have h3e : L3 "e" = l[j] := by simp [L3, Machine.State.upd]
      have hstep : (l.take (j + 1)).foldl F St = F S l[j] := by
        rw [List.take_succ_eq_append_getElem hj, List.foldl_append]; rfl
      have hlenj := hlen l[j]
      have hcj := hcap l[j] hlj
      by_cases h1 : hh ≤ 1
      · have h0 : hh - 1 = 0 := by omega
        have hcl : (LK.view S l[j] .cin).length + 1 ≤ κ.lcap .cin := by
          simp only [tabsLen, h0, ite_true] at hlenj hcj; rw [ite_eq_left h1] at hcj
          simp [LK.view]; omega
        have hso := LK.set_ok (κ := κ) (s := S) (i := l[j]) (l := LK.view S l[j] .cin ++ [(w,
          0)]) (k := .cin)
          rfl (by simp [LK.valid, LK.view]) (by simpa using hcl) ((hE _ hlj).1 h1)
        have hput : LK.put S l[j] (LK.view S l[j] .cin ++ [(w, 0)]) .cin = F S l[j] := by
          simp [F, addTableS, h0, LK.put, LK.view, Function.comp_def]
        refine ⟨_, L3, _, evalF_seq_ok2 e1 (evalF_ite_t (v := 1) (by simp [Exp.ev,
          Machine.BinOp.eval, h3h, h1])
          one_ne_zero (by simp only [evalF, Exp.ev, h3w, h3e, hso, hput]; rfl)), ?_,
          hstep.symm, (fun r h1 h2 h3 => by
            simp only [L3, L2, Machine.State.upd, ite_eq_right h2, ite_eq_right h3]
            exact hF1 r h1 h2 h3), ?_⟩
        · simp [Exp.cost]
        · intro u; have := tabsLen_addTableS (hh - 1) w l[j] u S; have := hlen u
          change tabsLen (addTableS (hh - 1) w l[j] S) (hh - 1) u ≤ _; omega
      · have h0 : hh - 1 ≠ 0 := by omega
        have hjS : l[j] < S.nodes.size := by rw [hfoldS]; exact ((hE _ hlj).2 (by omega)).2
        have hcl : (LK.view S l[j] .inTab).length + 1 ≤ κ.lcap .inTab := by
          simp only [tabsLen, h0, ite_false] at hlenj hcj; rw [ite_eq_right h1] at hcj
          simp [LK.view]; omega
        have hso := LK.set_ok (κ := κ) (s := S) (i := l[j]) (l := LK.view S l[j] .inTab ++ [(w,
          0)]) (k := .inTab)
          (by simp [LK.recOk,
            hjS]) (by simp [LK.valid, LK.view]) (by simpa using hcl) ((hE _ hlj).2 (by omega)).1
        have hput : LK.put S l[j] (LK.view S l[j] .inTab ++ [(w, 0)]) .inTab = F S l[j] := by
          simp [F, addTableS, h0, LK.put, LK.view, Function.comp_def]
        refine ⟨_, L3, _, evalF_seq_ok2 e1 (evalF_ite_f (by
          simp [Exp.ev, Machine.BinOp.eval, h3h]
          omega)
          (by simp only [evalF, Exp.ev, h3w, h3e, hso, hput]; rfl)), ?_,
          hstep.symm, (fun r h1 h2 h3 => by
            simp only [L3, L2, Machine.State.upd, ite_eq_right h2, ite_eq_right h3]
            exact hF1 r h1 h2 h3), ?_⟩
        · simp [Exp.cost]
        · intro u; have := tabsLen_addTableS (hh - 1) w l[j] u S; have := hlen u
          change tabsLen (addTableS (hh - 1) w l[j] S) (hh - 1) u ≤ _; omega)
  rw [hS', List.take_length] at he
  refine ⟨L', _, evalF_seq_ok2 a1 he, ?_, hF⟩
  simp only [Exp.cost] at hc ⊢; omega

theorem addTableS_phi (hh w e v : Nat) (side : List (Nat × Side)) (X : Core) :
    addTableS hh w e (phiS v side X) = phiS v side (addTableS hh w e X) := by
  unfold addTableS phiS
  split
  · rfl
  · have hg : ((X.nodes.modify v fun n => {
    n with
    side := side
  }).getX e).inTables = (X.nodes.getX e).inTables := by
      rw [getX_modify']; split <;> rfl
    simp only [hg]
    congr 1
    by_cases h : e = v
    · subst h; rw [Array.modify_modify_same, Array.modify_modify_same]; rfl
    · rw [Array.modify_comm _ (Ne.symm h)]

theorem fold_addTableS_phi (hh w v : Nat) (side : List (Nat × Side)) : ∀ (l : List Nat) (X : Core),
    l.foldl (fun s e => addTableS hh w e s) (phiS v side X) = phiS v side (l.foldl (fun s e =>
      addTableS hh w e s) X)
  | [], _ => rfl
  | e :: l, X => by
    simp only [List.foldl_cons]; rw [addTableS_phi, fold_addTableS_phi hh w v side l]

theorem fold_tabsLen (hh w u : Nat) : ∀ (l : List Nat) (s : Core),
    tabsLen (l.foldl (fun s e => addTableS hh w e s) s) hh u ≤ tabsLen s hh u + l.length
  | [], _ => by simp
  | e :: l, s => by
    simp only [List.foldl_cons, List.length_cons]
    have := fold_tabsLen hh w u l (addTableS hh w e s); have := tabsLen_addTableS hh w e u s; omega

theorem fold_addTableS_table (hh w u : Nat) : ∀ (l : List Nat) (s : Core),
    ((l.foldl (fun s e => addTableS hh w e s) s).nodes.getX u).table = (s.nodes.getX u).table
  | [], _ => rfl
  | e :: l, s => by simp only [List.foldl_cons]; rw [fold_addTableS_table hh w u l, addTableS_table]

theorem fold_addTableS_size (hh w : Nat) : ∀ (l : List Nat) (s : Core),
    (l.foldl (fun s e => addTableS hh w e s) s).nodes.size = s.nodes.size
  | [], _ => rfl
  | e :: l, s => by simp only [List.foldl_cons]; rw [fold_addTableS_size hh w l, addTableS_size]

theorem evenTable_keys (β : Nat) (l : List Nat) : (evenTable β l).map (·.1) = l := by
  simp only [evenTable, List.map_map, Function.comp_def]
  rw [show (fun x : Nat × Nat => x.2) = Prod.snd from rfl, List.map_snd_zip (by simp)]

theorem aroundStep_inTables (t : Core) (v : Nat) (ns : Array Node) (T e : Nat) :
    ((aroundStep t v ns T).getX e).inTables = (ns.getX e).inTables := by
  simp only [aroundStep, getX_modify']; split <;> rfl

theorem sd4_inTables {t : Core} {v e : Nat} {side : List (Nat × Side)} (he : e < t.nodes.size) :
    ((phiS v side (sd4 t v side)).nodes.getX e).inTables = (t.nodes.getX e).inTables := by
  have h1 : ((phiS v side (sd4 t v side)).nodes.getX e).inTables = ((sd2 t v).nodes.getX
    e).inTables := by
    simp only [phiS, sd4, getX_modify']
    split_ifs with h1 h2 h3 <;> first | rfl | (exfalso; omega)
  have h2 : ∀ (m : List Nat) (ns : Array Node), ((m.foldl (aroundStep t v) ns).getX e).inTables
    = (ns.getX e).inTables := by
    intro m; induction m with
    | nil => intro ns; rfl
    | cons T m ih => intro ns; simp only [List.foldl_cons]; rw [ih, aroundStep_inTables]
  rw [h1, ← sdJ_all]; simp only [sdJ]; rw [h2, sd1_getX t v he]

theorem sd4_cin (t : Core) (v : Nat) (side : List (Nat × Side)) : (phiS v side (sd4 t v
  side)).cin = t.cin := by
  simp only [phiS, sd4, sd2, sd1]

/-- Register the containing-table memberships of both drain targets. -/
def stage4S : Stm := cm{ w := v1; atS; w := v2; atS }

theorem sd4_table_N (t : Core) (v : Nat) (side : List (Nat × Side)) (hv : v < t.nodes.size) :
    ((phiS v side (sd4 t v side)).nodes.getX t.nodes.size).table = evenTable t.P.beta (sLeft t v
      side) := by
  have hsz : t.nodes.size < (sd2 t v).nodes.size := by rw [← sdJ_all, sdJ_size]; omega
  rw [phiS_getX_ne (by omega)]
  simp only [sd4, getX_modify']
  rw [ite_eq_right (fun h => by omega), ite_eq_left ⟨trivial, hsz⟩]

theorem sd4_table_N1 (t : Core) (v : Nat) (side : List (Nat × Side)) (hv : v < t.nodes.size) :
    ((phiS v side (sd4 t v side)).nodes.getX (t.nodes.size + 1)).table = evenTable t.P.beta
      (sRight t v side) := by
  have hsz : t.nodes.size + 1 < (sd2 t v).nodes.size := by rw [← sdJ_all, sdJ_size]; omega
  rw [phiS_getX_ne (by omega)]
  simp only [sd4, getX_modify']
  split_ifs <;> simp_all

theorem stage4S_ok {κ : Caps} {t : Core} {L : Loc} {v : Nat} {side : List (Nat × Side)}
    (hv : v < t.nodes.size) (hK : 1 < sH t v → ∀ e ∈ (t.nodes.getX v).table.map (·.1), e <
      t.nodes.size)
    (hLv1 : L "v1" = t.nodes.size) (hLv2 : L "v2" = t.nodes.size + 1) (hLh : L "h" = sH t v)
    (hwt : t.nodes.size + 1 < κ.lrec .table)
    (hE : ∀ e ∈ (t.nodes.getX v).table.map (·.1), (sH t v ≤ 1 → e < κ.lrec .cin) ∧ (1 < sH t v →
      e < κ.lrec .inTab))
    (hcap : ∀ e ∈ (t.nodes.getX v).table.map (·.1), tabsLen t (sH t v - 1) e + 2 * (t.nodes.getX
      v).table.length ≤
      (if sH t v ≤ 1 then κ.lcap .cin else κ.lcap .inTab)) :
    ∃ L' c, evalF κ stage4S (phiS v side (sd4 t v side)) L = .ok (phiS v side (sd6 t v side)) L' c ∧
      c ≤ 14 + 80 * (t.nodes.getX v).table.length ∧
      ∀ r, r ≠ "w" → r ≠ "nt" → r ≠ "j" → r ≠ "e" → L' r = L r := by
  set N := t.nodes.size
  set o := (t.nodes.getX v).table.map (·.1)
  set S4 := phiS v side (sd4 t v side)
  have hS4sz : S4.nodes.size = N + 2 := by simp [S4, phiS, sd4, ← sdJ_all, sdJ_size, N]
  have hlo : o.length = (t.nodes.getX v).table.length := by simp [o]
  have hLsub : ∀ e ∈ sLeft t v side, e ∈ o := by
    intro e he; rw [sLeft_part] at he; exact List.mem_of_mem_filter he
  have hRsub : ∀ e ∈ sRight t v side, e ∈ o := by
    intro e he; rw [sRight_part] at he; exact List.mem_of_mem_filter he
  have hLlen : (sLeft t v side).length ≤ o.length := by
    rw [sLeft_part]; exact List.length_filter_le _ _
  have hRlen : (sRight t v side).length ≤ o.length := by
    rw [sRight_part]; exact List.length_filter_le _ _
  have htl : ∀ e ∈ o, tabsLen S4 (sH t v - 1) e = tabsLen t (sH t v - 1) e := by
    intro e he; unfold tabsLen; split
    · rfl
    · next h0 => rw [sd4_inTables (hK (by omega) e he)]
  have a1 := evalF_assign_ok (κ := κ) (s := S4) (L := L) (x := "w") (e := .var "v1") (v := N)
    (by simp [Exp.ev, hLv1])
  obtain ⟨L2, c2, e2, hc2, hF2⟩ := atS_ok (κ := κ) (St := S4) (L := upd L "w" N) (w := N) (hh :=
    sH t v)
    (l := sLeft t v side) (by simp [Machine.State.upd]) (by simp [Machine.State.upd, hLh])
    (by omega) (by rw [sd4_table_N t v side hv, evenTable_keys])
    (fun e he => ⟨(hE e (hLsub e he)).1, fun h1 => ⟨(hE e (hLsub e he)).2 h1, by
      have := hK h1 e (hLsub e he); omega⟩⟩)
    (fun e he => by rw [htl e (hLsub e he)]; have := hcap e (hLsub e he); split at this <;>
      split <;> omega)
  set F1 := (sLeft t v side).foldl (fun s e => addTableS (sH t v - 1) N e s) S4
  have hfr2 : ∀ r, r ≠ "w" → r ≠ "nt" → r ≠ "j" → r ≠ "e" → L2 r = L r := fun r h1 h2 h3 h4 => by
    rw [hF2 r h2 h3 h4]; simp [Machine.State.upd, h1]
  have a3 := evalF_assign_ok (κ := κ) (s := F1) (L := L2) (x := "w") (e := .var "v2") (v := N + 1)
    (by simp [Exp.ev, hfr2 "v2" (by decide) (by decide) (by decide) (by decide), hLv2])
  obtain ⟨L4, c4, e4, hc4, hF4⟩ := atS_ok (κ := κ) (St := F1) (L := upd L2 "w" (N + 1)) (w := N + 1)
    (hh := sH t v) (l := sRight t v side) (by simp [Machine.State.upd])
    (by
      simp only [Machine.State.upd, String.reduceEq, ↓reduceIte]
      rw [hfr2 "h" (by decide) (by decide) (by decide) (by decide), hLh])
     hwt
    (by rw [fold_addTableS_table, sd4_table_N1 t v side hv, evenTable_keys])
    (fun e he => ⟨(hE e (hRsub e he)).1, fun h1 => ⟨(hE e (hRsub e he)).2 h1, by
      rw [fold_addTableS_size]; have := hK h1 e (hRsub e he); omega⟩⟩)
    (fun e he => by
      have h1 : tabsLen F1 (sH t v - 1) e ≤ tabsLen S4 (sH t v - 1) e + (sLeft t v side).length :=
        fold_tabsLen (sH t v - 1) N e (sLeft t v side) S4
      rw [htl e (hRsub e he)] at h1
      have := hcap e (hRsub e he); split at this <;> split <;> omega)
  have hfin : (sRight t v side).foldl (fun s e => addTableS (sH t v - 1) (N + 1) e s) F1 = phiS
    v side (sd6 t v side) := by
    simp only [F1, S4, fold_addTableS_phi]; rfl
  rw [hfin] at e4
  refine ⟨L4, _, evalF_seq_ok2 a1 (evalF_seq_ok2 e2 (evalF_seq_ok2 a3 e4)), ?_, ?_⟩
  · simp only [Exp.cost] at hc2 hc4 ⊢; omega
  · intro r h1 h2 h3 h4
    rw [hF4 r h2 h3 h4]; simp only [Machine.State.upd, ite_eq_right h1]; exact hfr2 r h1 h2 h3 h4

/-! ### Stages 5, 6: the children of `v1`, `v2` -/

/-- Test whether a live child has the currently selected drain side. -/
def chSel : Exp := cme{ f && x = sd }
/-- Set an entry's live parent, using the chunk-parent array at height one. -/
def setParS : Stm := cm{ if h = 1 then lpar[e] := u else N[e].livePar := u }
/-- Transfer one selected child, repair its live parent, and accumulate its weight. -/
def chBody : Stm := cm{
  e := children[v][j].fst
  (f, x) ← ‹lookupP .side›(v, e)
  if ‹chSel› then { setParS; append children[u] (e, 0); wtS; ws := ws + w } }
/-- The children on side `sd`, with their parent and weight updated for the new node `u`. -/
def chS : Stm := cm{
  ws := 0; nk := len children[v]; for j < nk do chBody
  N[u].weight := ws; N[u].livePar := N[v].livePar; N[u].overflow := v }

/-- What `chS` produces (Level F's `sd8` / `sd10` step). -/
def chRes (h u v lp wsum : Nat) (ch : List Nat) (St : Core) : Core :=
  let s7 := ch.foldl (fun s e => setParentS h u e s) St
  {
    s7 with
    nodes := s7.nodes.modify u fun n => {
      n with
      children := ch
      weight := wsum
      livePar := lp
      overflowOf := v
    }
  }

theorem setParentS_getX_ne {h u e x : Nat} {s : Core} (hx : x ≠ e) :
    (setParentS h u e s).nodes.getX x = s.nodes.getX x := by
  unfold setParentS; split
  · rfl
  · simp only [getX_modify']; rw [ite_eq_right (fun h => hx h.1)]

theorem setParentS_fields (h u e x : Nat) (s : Core) :
    ((setParentS h u e s).nodes.getX x).children = (s.nodes.getX x).children ∧
    ((setParentS h u e s).nodes.getX x).side = (s.nodes.getX x).side ∧
    ((setParentS h u e s).nodes.getX x).weight = (s.nodes.getX x).weight := by
  unfold setParentS; split
  · exact ⟨rfl, rfl, rfl⟩
  · simp only [getX_modify']; split <;> exact ⟨rfl, rfl, rfl⟩

theorem fold_setParentS_fields (h u x : Nat) : ∀ (l : List Nat) (s : Core),
    ((l.foldl (fun s e => setParentS h u e s) s).nodes.getX x).children = (s.nodes.getX
      x).children ∧
    ((l.foldl (fun s e => setParentS h u e s) s).nodes.getX x).side = (s.nodes.getX x).side ∧
    ((l.foldl (fun s e => setParentS h u e s) s).nodes.getX x).weight = (s.nodes.getX x).weight
  | [], _ => ⟨rfl, rfl, rfl⟩
  | e :: l, s => by
    simp only [List.foldl_cons]
    obtain ⟨a1, a2, a3⟩ := fold_setParentS_fields h u x l (setParentS h u e s)
    obtain ⟨b1, b2, b3⟩ := setParentS_fields h u e x s
    exact ⟨a1.trans b1, a2.trans b2, a3.trans b3⟩

theorem setParentS_getX_one {u e x : Nat} {s : Core} : (setParentS 1 u e s).nodes.getX x =
  s.nodes.getX x := by
  simp [setParentS]

theorem fold_setParentS_getX_notin {h u x : Nat} : ∀ (l : List Nat) (s : Core), (h = 1 ∨ x ∉ l) →
    (l.foldl (fun s e => setParentS h u e s) s).nodes.getX x = s.nodes.getX x
  | [], _, _ => rfl
  | e :: l, s, hx => by
    simp only [List.foldl_cons]
    rw [fold_setParentS_getX_notin l _ (hx.imp id (fun h' h => h' (List.mem_cons_of_mem _ h)))]
    rcases hx with h1 | hx
    · subst h1; exact setParentS_getX_one
    · exact setParentS_getX_ne (fun h => hx (by simp [h]))

theorem setParentS_size (h u e : Nat) (s : Core) : (setParentS h u e s).nodes.size =
  s.nodes.size := by
  unfold setParentS; split <;> simp

theorem fold_setParentS_size (h u : Nat) : ∀ (l : List Nat) (s : Core),
    (l.foldl (fun s e => setParentS h u e s) s).nodes.size = s.nodes.size
  | [], _ => rfl
  | e :: l, s => by simp only [List.foldl_cons]; rw [fold_setParentS_size h u l, setParentS_size]

/-- Setting a parent commutes with replacing the children of another node. -/
theorem setParentS_put {h u e : Nat} {s : Core} {l : List (Nat × Nat)} (he : h = 1 ∨ e ≠ u) :
    setParentS h u e (LK.put s u l .children) = LK.put (setParentS h u e s) u l .children := by
  unfold setParentS LK.put; split
  · rfl
  · next h1 =>
    simp only
    congr 1
    rw [Array.modify_comm _ (Ne.symm (he.resolve_left h1))]

theorem put_getX_ne_c {St : Core} {w u : Nat} {l : List (Nat × Nat)} (h : u ≠ w) :
    (LK.put St w l .children).nodes.getX u = St.nodes.getX u := by
  simp only [LK.put, getX_modify']; rw [ite_eq_right (fun e => h e.1)]

/-- The child-selection loop, preserving its parent-update and register invariants. -/
theorem child_loop_ok {κ : Caps} {St t : Core} {L : Loc} {v u : Nat}
    {side : List (Nat × Side)} {sd : Side}
    (huk : sH t v ≠ 1 → u ∉ (t.nodes.getX v).children) (hus : u < St.nodes.size)
    (hks : ∀ e ∈ (t.nodes.getX v).children,
      (sH t v ≠ 1 → e < St.nodes.size ∧ e < κ.tbl .N) ∧
      (sH t v = 1 → e < κ.arr .lpar))
    (hLv : L "v" = v) (hLu : L "u" = u) (hLh : L "h" = sH t v) (hLs : L "sd" = sideN sd)
    (hvc : v < κ.lrec .children) (hvs : v < κ.lrec .side) (huc : u < κ.lrec .children)
    (hcap : (t.nodes.getX v).children.length ≤ κ.lcap .children)
    (hput0 : LK.put St u [] .children = St)
    (hfv : ∀ (pre : List Nat) (l : List (Nat × Nat)),
      ((LK.put (pre.foldl (fun s e => setParentS (sH t v) u e s) St) u l .children).nodes.getX
         v).children
        = (t.nodes.getX v).children ∧
      ((LK.put (pre.foldl (fun s e => setParentS (sH t v) u e s) St) u l .children).nodes.getX
         v).side
        = side)
    (hfw : sH t v ≠ 1 → ∀ (pre : List Nat) (l : List (Nat × Nat)) e,
      e ∈ (t.nodes.getX v).children →
      ((LK.put (pre.foldl (fun s e => setParentS (sH t v) u e s) St) u l .children).nodes.getX
         e).weight
        = (t.nodes.getX e).weight)
    (hfs : ∀ (pre : List Nat) (l : List (Nat × Nat)),
      (LK.put (pre.foldl (fun s e => setParentS (sH t v) u e s) St) u l .children).nodes.size
        = St.nodes.size) :
    let kids := (t.nodes.getX v).children
    let sel := fun e => lookup side e == some sd
    let F := fun (s : Core) (e : Nat) => setParentS (sH t v) u e s
    let L2 := upd (upd L "ws" 0) "nk" kids.length
    ∃ S' L' c, evalF κ (.loop "j" (.var "nk") chBody) St L2 = .ok S' L' c ∧
      c ≤ 1 + (.var "nk" : Exp).cost + kids.length * (1 + (130 + 20 * side.length)) ∧
      S' = LK.put ((kids.filter sel).foldl F St) u
        ((kids.filter sel).map fun e => (e, 0)) .children ∧
      L' "ws" = ((kids.filter sel).map (sWt t v)).sum ∧
      ∀ r, r ≠ "j" → r ≠ "e" → r ≠ "f" → r ≠ "x" → r ≠ "w" → r ≠ "ws" → L' r = L2 r := by
  set kids := (t.nodes.getX v).children
  set sel := fun e => lookup side e == some sd
  set F := fun (s : Core) (e : Nat) => setParentS (sH t v) u e s
  set L2 := upd (upd L "ws" 0) "nk" kids.length
  have hL2 : ∀ r, r ≠ "ws" → r ≠ "nk" → L2 r = L r := by
    intro r h1 h2
    simp [L2, Machine.State.upd, h1, h2]
  obtain ⟨S', L', c, he, hc, hS', hws', hF⟩ := evalF_loop (κ := κ) (x := "j") (n := .var "nk")
    (b := chBody)
    (s := St) (L := L2) (N := kids.length) (by simp [Exp.ev, L2, Machine.State.upd])
    (fun j S L' => S = LK.put (((kids.take j).filter sel).foldl F St) u
        (((kids.take j).filter sel).map fun e => (e, 0)) .children ∧
      L' "ws" = (((kids.take j).filter sel).map (sWt t v)).sum ∧
      ∀ r, r ≠ "j" → r ≠ "e" → r ≠ "f" → r ≠ "x" → r ≠ "w" → r ≠ "ws" → L' r = L2 r)
    (130 + 20 * side.length)
    ⟨by simp [hput0], by simp [L2, Machine.State.upd], fun _ _ _ _ _ _ _ => rfl⟩
    (by
      intro j hj S L1 ⟨hS, hws1, hF1⟩
      subst hS
      set pre := (kids.take j).filter sel
      set S := LK.put (pre.foldl F St) u (pre.map fun e => (e, 0)) .children
      have hkj : kids[j] ∈ kids := List.getElem_mem hj
      obtain ⟨hkSN, hkA⟩ := hks _ hkj
      have hfr : ∀ r, r ≠ "j" → r ≠ "e" → r ≠ "f" → r ≠ "x" → r ≠ "w" → r ≠ "ws" → r ≠ "nk" → L1
        r = L r := by
        intro r h1 h2 h3 h4 h5 h6 h7; rw [hF1 r h1 h2 h3 h4 h5 h6, hL2 r h6 h7]
      have hv1 : L1 "v" = v := by
        rw [hfr "v" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
          decide), hLv]
      have hvCS : LK.view S v .children = kids.map fun e => (e, 0) := by
        simp [LK.view, (hfv pre _).1, S]
      have hvSS : LK.view S v .side = encS side := by simp [LK.view, (hfv pre _).2, S]
      have e1 := evalF_assign_ok (κ := κ) (s := S) (L := upd L1 "j" j) (x := "e") (e := .lrd
        .children false "v" "j")
        (v := kids[j]) (by simp [Exp.ev, Machine.State.upd, hv1, hvc, hvCS, hj])
      set L3 := upd (upd L1 "j" j) "e" kids[j]
      obtain ⟨Lk, ck, ek, hfk, hvk', -, -, hck⟩ := lookupP_agree κ .side S
        (Machine.State.setLocs (fun _ => 0) ["i", "x"] [v, kids[j] ]) (i := v) (x := kids[j])
        (by simp [Machine.State.setLocs, Machine.State.upd])
        (by simp [Machine.State.setLocs, Machine.State.upd]) hvs
      rw [hvSS, lookup_encS] at hfk hvk'
      rw [hvSS] at hck
      have e2 := evalF_call_ok (q := lookupP .side) (args := [.var "v", .var "e"]) (ds := ["f",
        "x"]) (L := L3)
        (by simp [evList, Exp.ev, L3, Machine.State.upd, hv1]) ek
      set L4 := Machine.State.setLocs L3 ["f", "x"] ((lookupP .side).rets.map Lk)
      have h4f : L4 "f" = if ((lookup side kids[j]).map sideN).isSome then 1 else 0 := by
        simp [L4, lookupP, Machine.State.setLocs,
          Machine.State.upd, hfk]
      have h4x : L4 "x" = ((lookup side kids[j]).map sideN).getD 0 := by
        simp [L4, lookupP, Machine.State.setLocs,
          Machine.State.upd, hvk']
      have hfr4 : ∀ r, r ≠ "j" → r ≠ "e" → r ≠ "f" → r ≠ "x" → r ≠ "w" → r ≠ "ws" → r ≠ "nk" →
        L4 r = L r := by
        intro r h1 h2 h3 h4 h5 h6 h7
        simp only [L4, L3, lookupP, Machine.State.setLocs, List.map,
          Machine.State.upd, ite_eq_right h1, ite_eq_right h2,
          ite_eq_right h3, ite_eq_right h4]
        exact hfr r h1 h2 h3 h4 h5 h6 h7
      have h4s : L4 "sd" = sideN sd := by
        rw [hfr4 "sd" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide), hLs]
      have htk : (kids.take (j + 1)).filter sel = pre ++ (if sel kids[j] then [kids[j] ] else
        []) := by
        rw [List.take_succ_eq_append_getElem hj, List.filter_append]
        by_cases hs : sel kids[j] = true <;> simp [hs, pre]
      by_cases hs : sel kids[j] = true
      · have hlk : lookup side kids[j] = some sd := by simpa [sel] using hs
        have hsel1 : chSel.ev κ S L4 = some 1 := by
          simp [chSel, Exp.ev, h4f, h4x, h4s, hlk, Machine.BinOp.eval]
        have h4h : L4 "h" = sH t v := by
          rw [hfr4 "h" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide), hLh]
        have h4u : L4 "u" = u := by
          rw [hfr4 "u" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide), hLu]
        have h4e : L4 "e" = kids[j] := by
          simp [L4, L3, lookupP, Machine.State.setLocs, Machine.State.upd]
        have hku : sH t v = 1 ∨ kids[j] ≠ u := by
          by_cases h1 : sH t v = 1
          · exact Or.inl h1
          · exact Or.inr (fun h => huk h1 (by rw [← h]; exact hkj))
        set S5 := setParentS (sH t v) u kids[j] S
        have e5 : ∃ c5, evalF κ setParS S L4 = .ok S5 L4 c5 ∧ c5 ≤ 7 := by
          by_cases h1 : sH t v = 1
          · have ew : evalF κ (.wr (.a .lpar) "e" "u") S L4 = .ok S5 L4 3 := by
              simp only [evalF, Exp.ev, h4e, h4u, Fld.set, hkA h1, ite_true, AF.set, AF.get,
                Exp.cost]
              simp only [S5, setParentS, h1, ite_true]
            exact ⟨_, evalF_ite_t (v := 1) (by simp [Exp.ev, Machine.BinOp.eval, h4h, h1])
              one_ne_zero ew,
              by simp [Exp.cost]⟩
          · have ew := evalF_wrN_ok (κ := κ) (s := S) (L := L4) (k := .livePar) (i := .var "e")
              (e := .var "u")
              (j := kids[j]) (w := u) (by simp [Exp.ev, h4e]) (by simp [Exp.ev, h4u]) (by
                rw [hfs]
                exact (hkSN h1).1)
              rfl
            have hs5 : {
              S with
              nodes := S.nodes.modify kids[j] (NF.set · u .livePar)
            } = S5 := by
              simp only [S5, setParentS, h1, ite_false]; rfl
            rw [hs5] at ew
            exact ⟨_, evalF_ite_f (by simp [Exp.ev, Machine.BinOp.eval, h4h, h1]) ew, by simp
              [Exp.cost]⟩
        obtain ⟨c5, e5, hc5⟩ := e5
        have hS5 : S5 = LK.put ((pre ++ [kids[j] ]).foldl F St) u (pre.map fun e => (e, 0))
          .children := by
          change setParentS (sH t v) u kids[j] (LK.put (pre.foldl F St) u _ .children) = _
          rw [setParentS_put hku, List.foldl_append]; rfl
        set S6 := LK.put ((pre ++ [kids[j] ]).foldl F St) u ((pre ++ [kids[j] ]).map fun e =>
          (e, 0)) .children
        have hpl : pre.length + 1 ≤ kids.length := by
          have := htk; rw [ite_eq_left hs] at this
          have h2 := List.length_filter_le sel (kids.take (j + 1))
          rw [this] at h2; simp at h2; omega
        have e6 : evalF κ (.lgrow .children "u" "e" 0) S5 L4 = .ok S6 L4 22 := by
          have hsz5 : u < (List.foldl F St (pre ++ [kids[j] ])).nodes.size := by
            change u < (List.foldl (fun s e => setParentS (sH t v) u e s) St (pre ++ [kids[j]
              ])).nodes.size
            rw [fold_setParentS_size]; exact hus
          have hrec5 : LK.children.recOk (List.foldl F St (pre ++ [kids[j] ])) u = true := by
            simp only [LK.recOk, decide_eq_true_eq]; exact hsz5
          have hvU : LK.view S5 u .children = pre.map fun e => (e, 0) := by
            rw [hS5, LK.view_put hrec5 (by simp [LK.valid])]; simp
          have hso : LK.set κ S5 u ((pre.map fun e => (e, 0)) ++ [(kids[j], 0)]) .children =
            some S6 := by
            rw [LK.set_ok (by rw [hS5, LK.recOk_put]; exact hrec5) (by simp [LK.valid]) (by
              simp; omega) huc,
              hS5, LK.put_put]
            simp [S6]
          simp only [evalF, Exp.ev, h4u, h4e, hvU, hso, Exp.cost]
        obtain ⟨c7, e7, hc7⟩ := wtS_ok (κ := κ) (s := S6) (L := L4) (h := sH t v) (e := kids[j])
          h4h h4e
          (fun h1 => (hkSN h1).2)
        have hwj : drainWt S6.nodes (sH t v) kids[j] = sWt t v kids[j] := by
          simp only [sWt, drainWt]; split
          · rfl
          · next h1 => exact hfw (by simpa using h1) _ _ _ hkj
        rw [hwj] at e7
        set L7 := upd L4 "w" (sWt t v kids[j])
        have e8 := evalF_assign_ok (κ := κ) (s := S6) (L := L7) (x := "ws") (e := "ws" + "w")
          (v := (pre.map (sWt t v)).sum + sWt t v kids[j])
          (by simp [Exp.ev, Machine.BinOp.eval, L7, L4, L3, lookupP,
            Machine.State.setLocs,
            Machine.State.upd, hws1])
        refine ⟨_, _, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_ite_t hsel1 one_ne_zero
          (evalF_seq_ok2 e5 (evalF_seq_ok2 e6 (evalF_seq_ok2 e7 e8))))), ?_, ?_, ?_, ?_⟩
        · simp only [encS, List.length_map] at hck
          simp only [Exp.cost, costList, chSel, List.map, List.sum_cons, List.sum_nil,
            List.length_cons,
            List.length_nil] at hck hc5 hc7 ⊢
          omega
        · rw [htk, ite_eq_left hs]
        · rw [htk, ite_eq_left hs]; simp [Machine.State.upd]
        · intro r h1 h2 h3 h4 h5 h6
          simp only [L7, Machine.State.upd, ite_eq_right h5, ite_eq_right h6]
          simp only [L4, L3, lookupP, Machine.State.setLocs, List.map,
            Machine.State.upd, ite_eq_right h1,
            ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]
          exact hF1 r h1 h2 h3 h4 h5 h6
      · have hsel0 : chSel.ev κ S L4 = some 0 := by
          have hn : lookup side kids[j] ≠ some sd := by simpa [sel] using hs
          cases hl : lookup side kids[j] with
          | none => simp [chSel, Exp.ev, h4f, h4x, h4s, hl, Machine.BinOp.eval]
          | some st =>
            rw [hl] at hn
            have : sideN st ≠ sideN sd := by cases st <;> cases sd <;> simp_all [sideN]
            simp [chSel, Exp.ev, h4f, h4x, h4s, hl, Machine.BinOp.eval, this]
        refine ⟨_, _, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_ite_f hsel0 evalF_skip)), ?_,
          ?_, ?_, ?_⟩
        · simp only [encS, List.length_map] at hck
          simp only [Exp.cost, costList, chSel, List.map, List.sum_cons, List.sum_nil,
            List.length_cons,
            List.length_nil] at hck ⊢
          omega
        · rw [htk, ite_eq_right hs, List.append_nil]
        · rw [htk, ite_eq_right hs, List.append_nil]
          simp only [L4, L3, lookupP, Machine.State.setLocs, List.map,
            Machine.State.upd]
          simpa using hws1
        · intro r h1 h2 h3 h4 h5 h6
          simp only [L4, L3, lookupP, Machine.State.setLocs, List.map,
            Machine.State.upd, ite_eq_right h1,
            ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]
          exact hF1 r h1 h2 h3 h4 h5 h6)
  rw [List.take_length] at hS' hws'
  exact ⟨S', L', c, he, hc, hS', hws', hF⟩

theorem chS_ok {κ : Caps} {St t : Core} {L : Loc} {v u : Nat} {side : List (Nat × Side)} {sd : Side}
    (hkids : (St.nodes.getX v).children = (t.nodes.getX v).children) (hside : (St.nodes.getX
      v).side = side)
    (hwt : sH t v ≠ 1 → ∀ e ∈ (t.nodes.getX v).children, (St.nodes.getX e).weight =
      (t.nodes.getX e).weight)
    (hlp : (St.nodes.getX v).livePar = (t.nodes.getX v).livePar) (hu0 : (St.nodes.getX
      u).children = [])
    (huv : u ≠ v) (huk : sH t v ≠ 1 → u ∉ (t.nodes.getX v).children)
    (hvk : sH t v ≠ 1 → v ∉ (t.nodes.getX v).children)
    (hus : u < St.nodes.size)
    (hks : ∀ e ∈ (t.nodes.getX v).children, (sH t v ≠ 1 → e < St.nodes.size ∧ e < κ.tbl .N) ∧
      (sH t v = 1 → e < κ.arr .lpar))
    (hLv : L "v" = v) (hLu : L "u" = u) (hLh : L "h" = sH t v) (hLs : L "sd" = sideN sd)
    (hvc : v < κ.lrec .children) (hvs : v < κ.lrec .side) (huc : u < κ.lrec .children)
    (hvN : v < κ.tbl .N) (hcap : (t.nodes.getX v).children.length ≤ κ.lcap
      .children) :
    ∃ L' c, evalF κ chS St L = .ok (chRes (sH t v) u v (t.nodes.getX v).livePar
      ((((t.nodes.getX v).children.filter (lookup side · == some sd)).map (sWt t v)).sum)
      ((t.nodes.getX v).children.filter (lookup side · == some sd)) St) L' c ∧
      c ≤ 30 + (t.nodes.getX v).children.length * (140 + 20 * side.length) ∧
      ∀ r, r ≠ "ws" → r ≠ "nk" → r ≠ "j" → r ≠ "e" → r ≠ "f" → r ≠ "x" → r ≠ "w" → L' r = L r := by
  set kids := (t.nodes.getX v).children
  set sel := fun e => lookup side e == some sd
  set F := fun (s : Core) (e : Nat) => setParentS (sH t v) u e s
  have hvC : LK.view St v .children = kids.map fun e => (e, 0) := by simp [LK.view, hkids, kids]
  have hput0 : LK.put St u [] .children = St := by
    have := LK.put_view (k := .children) (s := St) (i := u) (by simp [LK.idOk, LK.recOk, hus])
    simp only [LK.view, hu0, List.map_nil] at this; exact this
  have a1 := evalF_assign_ok (κ := κ) (s := St) (L := L) (x := "ws") (e := (0 : Exp)) (v := 0) rfl
  have a2 := evalF_assign_ok (κ := κ) (s := St) (L := upd L "ws" 0) (x := "nk") (e := .llen
    .children "v")
    (v := kids.length) (by simp [Exp.ev, Machine.State.upd, hLv, hvc, hvC])
  set L2 := upd (upd L "ws" 0) "nk" kids.length
  have hL2 : ∀ r, r ≠ "ws" → r ≠ "nk" → L2 r = L r := fun r h1 h2 => by simp [L2,
    Machine.State.upd, h1, h2]
  -- states during the loop
  have hfv : ∀ (pre : List Nat) (l : List (Nat × Nat)),
      ((LK.put (pre.foldl F St) u l .children).nodes.getX v).children = kids ∧
      ((LK.put (pre.foldl F St) u l .children).nodes.getX v).side = side := by
    intro pre l
    rw [put_getX_ne_c huv.symm]
    obtain ⟨a, b, -⟩ := fold_setParentS_fields (sH t v) u v pre St
    exact ⟨a.trans hkids, b.trans hside⟩
  have hfw : sH t v ≠ 1 → ∀ (pre : List Nat) (l : List (Nat × Nat)) e, e ∈ kids →
      ((LK.put (pre.foldl F St) u l .children).nodes.getX e).weight = (t.nodes.getX e).weight := by
    intro h1 pre l e he
    rw [put_getX_ne_c (fun h => huk h1 (by rw [← h]; exact he))]
    obtain ⟨-, -, c⟩ := fold_setParentS_fields (sH t v) u e pre St
    exact c.trans (hwt h1 e he)
  have hfs : ∀ (pre : List Nat) (l : List (Nat × Nat)),
      (LK.put (pre.foldl F St) u l .children).nodes.size = St.nodes.size := by
    intro pre l; simp [LK.put, F, fold_setParentS_size]
  obtain ⟨S', L', c, he, hc, hS', hws', hF⟩ :=
    child_loop_ok huk hus hks hLv hLu hLh hLs hvc hvs huc hcap hput0 hfv hfw hfs
  subst hS'
  set ch := kids.filter sel
  set S7 := LK.put (ch.foldl F St) u (ch.map fun e => (e, 0)) .children
  have hS7sz : S7.nodes.size = St.nodes.size := hfs ch _
  have hfr' : ∀ r, r ≠ "ws" → r ≠ "nk" → r ≠ "j" → r ≠ "e" → r ≠ "f" → r ≠ "x" → r ≠ "w" → L' r
    = L r := by
    intro r h1 h2 h3 h4 h5 h6 h7
    rw [hF r h3 h4 h5 h6 h7 h1]
    change L2 r = L r
    exact hL2 r h1 h2
  have hLu' : L' "u" = u := by
    rw [hfr' "u" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      decide), hLu]
  have hLv' : L' "v" = v := by
    rw [hfr' "v" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      decide), hLv]
  have w1 := evalF_wrN_ok (κ := κ) (s := S7) (L := L') (k := .weight) (i := .var "u") (e := .var
    "ws") (j := u)
    (w := (ch.map (sWt t v)).sum) (by simp [Exp.ev, hLu']) (by simp [Exp.ev, hws']) (by
      rw [hS7sz]
      exact hus)  rfl
  set S8 := {
    S7 with
    nodes := S7.nodes.modify u (NF.set · (ch.map (sWt t v)).sum .weight)
  }
  have hvch : sH t v = 1 ∨ v ∉ ch := by
    by_cases h1 : sH t v = 1
    · exact Or.inl h1
    · exact Or.inr (fun h => hvk h1 (List.mem_of_mem_filter h))
  have hS8v : (S8.nodes.getX v).livePar = (t.nodes.getX v).livePar := by
    simp only [S8, getX_modify']; rw [ite_eq_right (fun h => huv h.1.symm)]
    rw [put_getX_ne_c huv.symm, fold_setParentS_getX_notin ch St hvch, hlp]
  have w2 := evalF_wrN_ok (κ := κ) (s := S8) (L := L') (k := .livePar) (i := .var "u") (e := .rd
    (.n .livePar) "v")
    (j := u) (w := (t.nodes.getX v).livePar) (by simp [Exp.ev, hLu'])
    (by simp [Exp.ev, hLv', hvN, Fld.cap, Fld.get, NF.get, hS8v]) (by simp [S8, hS7sz, hus])  rfl
  set S9 := {
    S8 with
    nodes := S8.nodes.modify u (NF.set · (t.nodes.getX v).livePar .livePar)
  }
  have w3 := evalF_wrN_ok (κ := κ) (s := S9) (L := L') (k := .overflow) (i := .var "u") (e :=
    .var "v")
    (j := u) (w := v) (by simp [Exp.ev, hLu']) (by simp [Exp.ev, hLv']) (by simp [S9, S8, hS7sz,
      hus])  rfl
  have hfin : {
    S9 with
    nodes := S9.nodes.modify u (NF.set · v .overflow)
  } =
      chRes (sH t v) u v (t.nodes.getX v).livePar ((ch.map (sWt t v)).sum) ch St := by
    simp only [S9, S8, S7, chRes, LK.put, Array.modify_modify_same]
    congr 2
    funext n
    simp [NF.set, Function.comp_def]
  rw [hfin] at w3
  refine ⟨L', _, evalF_seq_ok2 a1 (evalF_seq_ok2 a2 (evalF_seq_ok2 he (evalF_seq_ok2 w1
    (evalF_seq_ok2 w2 w3)))),
    ?_, hfr'⟩
  simp only [Exp.cost] at hc ⊢
  have e : kids.length * (1 + (130 + 20 * side.length)) =
      kids.length * (131 + 20 * side.length) := by
    ring
  have e2 : kids.length * (131 + 20 * side.length) ≤ kids.length * (140 + 20 * side.length) :=
    Nat.mul_le_mul_left _ (by omega)
  rw [e] at hc; omega

theorem setParentS_phi (h w e v : Nat) (side : List (Nat × Side)) (X : Core) :
    setParentS h w e (phiS v side X) = phiS v side (setParentS h w e X) := by
  unfold setParentS phiS
  split
  · rfl
  · congr 1
    by_cases he : e = v
    · subst he; rw [Array.modify_modify_same, Array.modify_modify_same]; rfl
    · rw [Array.modify_comm _ (Ne.symm he)]

theorem fold_setParentS_phi (h w v : Nat) (side : List (Nat × Side)) : ∀ (l : List Nat) (X : Core),
    l.foldl (fun s e => setParentS h w e s) (phiS v side X) =
      phiS v side (l.foldl (fun s e => setParentS h w e s) X)
  | [], _ => rfl
  | e :: l, X => by
    simp only [List.foldl_cons]; rw [setParentS_phi, fold_setParentS_phi h w v side l]

theorem chRes_phi {h u v' lp ws v : Nat} {ch : List Nat} {side : List (Nat × Side)} {X : Core}
  (huv : u ≠ v) :
    chRes h u v' lp ws ch (phiS v side X) = phiS v side (chRes h u v' lp ws ch X) := by
  unfold chRes
  simp only [fold_setParentS_phi]
  simp only [phiS]
  rw [Array.modify_comm _ (Ne.symm huv)]

/-- Children, weight and live parent. -/
def CWL (a b : Node) : Prop := a.children = b.children ∧ a.weight = b.weight ∧ a.livePar = b.livePar

theorem CWL.trans {a b c : Node} (h1 : CWL a b) (h2 : CWL b c) : CWL a c :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩

theorem CWL.refl (a : Node) : CWL a a := ⟨rfl, rfl, rfl⟩

theorem sd6_CWL (t : Core) (v : Nat) (side : List (Nat × Side)) (x : Nat) :
    CWL ((sd6 t v side).nodes.getX x) ((sd1 t v).nodes.getX x) := by
  have hA : ∀ (l : List Nat) (hh w : Nat) (X : Core),
      CWL ((l.foldl (fun s e => addTableS hh w e s) X).nodes.getX x) (X.nodes.getX x) := by
    intro l; induction l with
    | nil => intro _ _ X; exact CWL.refl _
    | cons e l ih =>
      intro hh w X; simp only [List.foldl_cons]
      refine (ih hh w _).trans ?_
      unfold addTableS; split
      · exact CWL.refl _
      · simp only [getX_modify']; split <;> exact CWL.refl _
  have h4 : CWL ((sd4 t v side).nodes.getX x) ((sd2 t v).nodes.getX x) := by
    simp only [sd4, getX_modify']; split_ifs <;> exact CWL.refl _
  have h2 : ∀ (m : List Nat) (ns : Array Node), CWL ((m.foldl (aroundStep t v) ns).getX x)
    (ns.getX x) := by
    intro m; induction m with
    | nil => intro ns; exact CWL.refl _
    | cons T m ih =>
      intro ns; simp only [List.foldl_cons]
      refine (ih _).trans ?_
      simp only [aroundStep, getX_modify']; split
      · exact ⟨rfl, rfl, rfl⟩
      · exact CWL.refl _
  have h2' : CWL ((sd2 t v).nodes.getX x) ((sd1 t v).nodes.getX x) := by
    rw [← sdJ_all]; simp only [sdJ]; exact h2 _ _
  simp only [sd6]
  exact (hA _ _ _ _).trans ((hA _ _ _ _).trans (h4.trans h2'))

theorem sd1_getX_new' (t : Core) (v : Nat) {u : Nat} (hu : t.nodes.size ≤ u) (hu2 : u <
  t.nodes.size + 2) :
    (sd1 t v).nodes.getX u = {
      height := sH t v
    } := by
  simp only [sd1, getX_push', Array.size_push]
  by_cases e : u = t.nodes.size + 1
  · rw [ite_eq_left e]
  · rw [ite_eq_right e, ite_eq_left (by omega)]

theorem chRes_getX_notin {h u v' lp ws x : Nat} {ch : List Nat} {X : Core} (hx : h = 1 ∨ x ∉ ch)
  (hxu : x ≠ u) :
    (chRes h u v' lp ws ch X).nodes.getX x = X.nodes.getX x := by
  simp only [chRes,
    getX_modify']; rw [ite_eq_right (fun e => hxu e.1), fold_setParentS_getX_notin ch X hx]

theorem chRes_weight {h u v' lp ws x : Nat} {ch : List Nat} {X : Core} (hxu : x ≠ u) :
    ((chRes h u v' lp ws ch X).nodes.getX x).weight = (X.nodes.getX x).weight := by
  simp only [chRes, getX_modify']; rw [ite_eq_right (fun e => hxu e.1)]
  exact (fold_setParentS_fields h u x ch X).2.2

theorem chRes_size {h u v' lp ws : Nat} {ch : List Nat} {X : Core} :
    (chRes h u v' lp ws ch X).nodes.size = X.nodes.size := by
  simp [chRes, fold_setParentS_size]

theorem sd8_eq (t : Core) (v : Nat) (side : List (Nat × Side)) :
    sd8 t v side = chRes (sH t v) t.nodes.size v (t.nodes.getX v).livePar
      (((sCh1 t v side).map (sWt t v)).sum) (sCh1 t v side) (sd6 t v side) := rfl

theorem sd10_eq (t : Core) (v : Nat) (side : List (Nat × Side)) :
    sd10 t v side = chRes (sH t v) (t.nodes.size + 1) v (t.nodes.getX v).livePar
      (((sCh2 t v side).map (sWt t v)).sum) (sCh2 t v side) (sd8 t v side) := rfl

/-- Transfer and weigh the children assigned to each drain target. -/
def stage56S : Stm := cm{
  u := v1; sd := 0; chS
  u := v2; sd := 1; chS }

theorem stage56S_ok {κ : Caps} {t : Core} {L : Loc} {v : Nat} {side : List (Nat × Side)}
    (hv : v < t.nodes.size) (hvk : sH t v ≠ 1 → v ∉ (t.nodes.getX v).children)
    (hks : ∀ e ∈ (t.nodes.getX v).children, (sH t v ≠ 1 → e < t.nodes.size ∧ e < κ.tbl .N) ∧
      (sH t v = 1 → e < κ.arr .lpar))
    (hLv : L "v" = v) (hLv1 : L "v1" = t.nodes.size) (hLv2 : L "v2" = t.nodes.size + 1) (hLh : L
      "h" = sH t v)
    (hvc : v < κ.lrec .children) (hvs : v < κ.lrec .side) (huc : t.nodes.size + 1 < κ.lrec
      .children)
    (hvN : v < κ.tbl .N)
    (hcap : (t.nodes.getX v).children.length ≤ κ.lcap .children) :
    ∃ L' c, evalF κ stage56S (phiS v side (sd6 t v side)) L = .ok (phiS v side (sd10 t v side))
      L' c ∧
      c ≤ 70 + 2 * ((t.nodes.getX v).children.length * (140 + 20 * side.length)) ∧
      ∀ r, r ≠ "u" → r ≠ "sd" → r ≠ "ws" → r ≠ "nk" → r ≠ "j" → r ≠ "e" → r ≠ "f" → r ≠ "x" → r
        ≠ "w" →
        L' r = L r := by
  set N := t.nodes.size
  set kids := (t.nodes.getX v).children
  set S6 := phiS v side (sd6 t v side)
  have hsz6 : (sd6 t v side).nodes.size = N + 2 := by
    have h1 : ∀ (l : List Nat) (hh w : Nat) (X : Core), (l.foldl (fun s e => addTableS hh w e s)
      X).nodes.size = X.nodes.size :=
      fun l hh w X => fold_addTableS_size hh w l X
    simp only [sd6, h1, sd4, Array.size_modify, ← sdJ_all, sdJ_size, N]
  have hS6sz : S6.nodes.size = N + 2 := by simp [S6, phiS, hsz6]
  have hkN : sH t v ≠ 1 → ∀ e ∈ kids, e ≠ N ∧ e ≠ N + 1 ∧ e ≠ v := fun h1 e he =>
    ⟨by have := ((hks e he).1 h1).1; omega, by have := ((hks e he).1 h1).1; omega, fun h => hvk
      h1 (h ▸ he)⟩
  have h6v : CWL ((sd6 t v side).nodes.getX v) (t.nodes.getX v) := by
    rw [← sd1_getX t v hv]; exact sd6_CWL t v side v
  have h6e : sH t v ≠ 1 → ∀ e ∈ kids, ((sd6 t v side).nodes.getX e).weight = (t.nodes.getX
    e).weight := by
    intro h1 e he; rw [← sd1_getX t v ((hks e he).1 h1).1]; exact (sd6_CWL t v side e).2.1
  have h6N : ((sd6 t v side).nodes.getX N).children = [] := by
    rw [(sd6_CWL t v side N).1, sd1_getX_new' t v le_rfl (by omega)]
  have h6N1 : ((sd6 t v side).nodes.getX (N + 1)).children = [] := by
    rw [(sd6_CWL t v side (N + 1)).1, sd1_getX_new' t v (by omega) (by omega)]
  have hvsz6 : v < (sd6 t v side).nodes.size := by omega
  -- v1
  have a1 := evalF_assign_ok (κ := κ) (s := S6) (L := L) (x := "u") (e := .var "v1") (v := N)
    (by simp [Exp.ev, hLv1])
  have a2 := evalF_assign_ok (κ := κ) (s := S6) (L := upd L "u" N) (x := "sd") (e := (0 : Exp))
    (v := 0) rfl
  set L2 := upd (upd L "u" N) "sd" 0
  have hL2 : ∀ r, r ≠ "u" → r ≠ "sd" → L2 r = L r := fun r h1 h2 => by simp [L2,
    Machine.State.upd, h1, h2]
  obtain ⟨L3, c3, e3, hc3, hF3⟩ := chS_ok (κ := κ) (St := S6) (t := t) (L := L2) (v := v) (u :=
    N) (side := side)
    (sd := .left) (by rw [phiS_getX_self hvsz6]; exact h6v.1) (by rw [phiS_getX_self hvsz6])
    (fun h1 e he => by rw [phiS_getX_ne (hkN h1 e he).2.2]; exact h6e h1 e he)
    (by rw [phiS_getX_self hvsz6]; exact h6v.2.2) (by rw [phiS_getX_ne (by omega)]; exact h6N)
      (by omega)
    (fun h1 h => (hkN h1 N h).1 rfl) hvk (by omega)
    (fun e he => ⟨fun h1 => ⟨by have := ((hks e he).1 h1).1; omega, ((hks e he).1 h1).2⟩, (hks e
      he).2⟩)
    (by rw [hL2 "v" (by decide) (by decide),
      hLv]) (by simp [L2, Machine.State.upd])
    (by rw [hL2 "h" (by decide) (by decide),
      hLh]) (by simp [L2, Machine.State.upd, sideN])
    hvc hvs (by omega)  hvN hcap
  rw [chRes_phi (show N ≠ v by omega), ← sd8_eq] at e3
  set S8 := phiS v side (sd8 t v side)
  have hfr3 : ∀ r, r ≠ "u" → r ≠ "sd" → r ≠ "ws" → r ≠ "nk" → r ≠ "j" → r ≠ "e" → r ≠ "f" → r ≠
    "x" → r ≠ "w" →
      L3 r = L r := fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 => by rw [hF3 r h3 h4 h5 h6 h7 h8 h9, hL2 r
        h1 h2]
  -- v2
  have hch1 : ∀ x, (sH t v ≠ 1 → x ∉ kids) → (sH t v = 1 ∨ x ∉ sCh1 t v side) := fun x hx => by
    by_cases h1 : sH t v = 1
    · exact Or.inl h1
    · exact Or.inr (fun h => hx h1 (List.mem_of_mem_filter h))
  have h8v : (sd8 t v side).nodes.getX v = (sd6 t v side).nodes.getX v := by
    rw [sd8_eq, chRes_getX_notin (hch1 v hvk) (by omega)]
  have hsz8 : (sd8 t v side).nodes.size = N + 2 := by rw [sd8_eq, chRes_size, hsz6]
  have hvsz8 : v < (sd8 t v side).nodes.size := by omega
  have a3 := evalF_assign_ok (κ := κ) (s := S8) (L := L3) (x := "u") (e := .var "v2") (v := N + 1)
    (by simp [Exp.ev,
      hfr3 "v2" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide), hLv2])
  have a4 := evalF_assign_ok (κ := κ) (s := S8) (L := upd L3 "u" (N + 1)) (x := "sd") (e := (1 :
    Exp)) (v := 1) rfl
  set L4 := upd (upd L3 "u" (N + 1)) "sd" 1
  have hL4 : ∀ r, r ≠ "u" → r ≠ "sd" → r ≠ "ws" → r ≠ "nk" → r ≠ "j" → r ≠ "e" → r ≠ "f" → r ≠
    "x" → r ≠ "w" →
      L4 r = L r := fun r h1 h2 h3 h4 h5 h6 h7 h8 h9 => by
    simp only [L4, Machine.State.upd, ite_eq_right h1,
      ite_eq_right h2]; exact hfr3 r h1 h2 h3 h4 h5 h6 h7 h8 h9
  obtain ⟨L5, c5, e5, hc5, hF5⟩ := chS_ok (κ := κ) (St := S8) (t := t) (L := L4) (v := v) (u :=
    N + 1)
    (side := side) (sd := .right) (by rw [phiS_getX_self hvsz8, h8v]; exact h6v.1) (by rw
      [phiS_getX_self hvsz8])
    (fun h1 e he => by
      rw [phiS_getX_ne (hkN h1 e he).2.2, sd8_eq, chRes_weight (hkN h1 e he).1]; exact h6e h1 e he)
    (by rw [phiS_getX_self hvsz8, h8v]; exact h6v.2.2)
    (by rw [phiS_getX_ne (by omega), sd8_eq,
      chRes_getX_notin (hch1 _ (fun h1 h => (hkN h1 _ h).2.1 rfl)) (by omega)]
        exact h6N1) (by omega)
    (fun h1 h => (hkN h1 (N + 1) h).2.1 rfl) hvk (by simp [S8, phiS, hsz8])
    (fun e he => ⟨fun h1 => ⟨by simp [S8, phiS, hsz8]; have := ((hks e he).1 h1).1; omega, ((hks
      e he).1 h1).2⟩,
      (hks e he).2⟩)
    (by rw [hL4 "v" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      decide) (by decide)
      (by decide), hLv]) (by simp [L4, Machine.State.upd])
    (by rw [hL4 "h" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      decide) (by decide)
      (by decide), hLh]) (by simp [L4, Machine.State.upd, sideN])
    hvc hvs huc  hvN hcap
  rw [chRes_phi (show N + 1 ≠ v by omega), ← sd10_eq] at e5
  refine ⟨L5, _, evalF_seq_ok2 a1 (evalF_seq_ok2 a2 (evalF_seq_ok2 e3 (evalF_seq_ok2 a3
    (evalF_seq_ok2 a4 e5)))),
    ?_, ?_⟩
  · change _ ≤ 70 + 2 * ((t.nodes.getX v).children.length * (140 + 20 * side.length))
    simp only [Exp.cost] at hc3 hc5 ⊢; omega
  · intro r h1 h2 h3 h4 h5 h6 h7 h8 h9
    rw [hF5 r h3 h4 h5 h6 h7 h8 h9, hL4 r h1 h2 h3 h4 h5 h6 h7 h8 h9]

/-! ### Stage 7: the parent of `v` takes `v1, v2` in place of `v` -/

theorem replace1_eq (x a b : Nat) : ∀ (l : List Nat), x ∈ l →
    l.replace1 x [a, b] = (l.set (l.findIdx (· == x)) a).insertIdx (l.findIdx (· == x) + 1) b
  | [], h => by simp at h
  | y :: l, h => by
    simp only [List.replace1, List.findIdx_cons]
    by_cases hy : y = x
    · simp [hy]
    · have hx : x ∈ l := by simp at h; tauto
      simp only [hy, ite_false, beq_iff_eq,  List.set_cons_succ]
      rw [replace1_eq x a b l hx]
      simp [List.insertIdx_succ_cons]

theorem findIdx_pair0' (l : List Nat) (x : Nat) :
    (l.map fun e => (e, 0)).findIdx (·.1 == x) = l.findIdx (· == x) := by
  rw [List.findIdx_map]; rfl

/-- Replace the source node by its two targets in the live parent's child list. -/
def stage7S : Stm := cm{
  p := N[v].livePar
  r ← ‹findP .children›(p, v)
  children[p][r].fst := v1
  call ‹insertIdxP .children›(p, r + 1, v2, 0) }

/-- Level F after the parent's children (`s11` of `sdS`). -/
def sd11 (t : Core) (v : Nat) (side : List (Nat × Side)) : Core :=
  {
    sd10 t v side with
    nodes := (sd10 t v side).nodes.modify (t.nodes.getX v).livePar fun n => {
      n with
      children := n.children.replace1 v [t.nodes.size, t.nodes.size + 1]
    }
  }

theorem chRes_children (h u v' lp ws x : Nat) (ch : List Nat) (X : Core) (hxu : x ≠ u) :
    ((chRes h u v' lp ws ch X).nodes.getX x).children = (X.nodes.getX x).children := by
  simp only [chRes, getX_modify']; rw [ite_eq_right (fun e => hxu e.1)]
  exact (fold_setParentS_fields h u x ch X).1

theorem chRes_livePar_notin {h u v' lp ws x : Nat} {ch : List Nat} {X : Core} (hx : h = 1 ∨ x ∉
  ch) (hxu : x ≠ u) :
    ((chRes h u v' lp ws ch X).nodes.getX x).livePar = (X.nodes.getX x).livePar := by
  rw [chRes_getX_notin hx hxu]

theorem stage7S_ok {κ : Caps} {t : Core} {L : Loc} {v : Nat} {side : List (Nat × Side)}
    (hv : v < t.nodes.size) (hvk : sH t v ≠ 1 → v ∉ (t.nodes.getX v).children)
    (hp : (t.nodes.getX v).livePar < t.nodes.size) (hpv : (t.nodes.getX v).livePar ≠ v)
    (hpar : v ∈ (t.nodes.getX (t.nodes.getX v).livePar).children)
    (hLv : L "v" = v) (hLv1 : L "v1" = t.nodes.size) (hLv2 : L "v2" = t.nodes.size + 1)
    (hpc : (t.nodes.getX v).livePar < κ.lrec .children) (hvN : v < κ.tbl .N)
    (hcap : (t.nodes.getX (t.nodes.getX v).livePar).children.length + 1 ≤ κ.lcap .children) :
    ∃ L' c, evalF κ stage7S (phiS v side (sd10 t v side)) L = .ok (phiS v side (sd11 t v side))
      L' c ∧
      c ≤ 100 + 111 * (t.nodes.getX (t.nodes.getX v).livePar).children.length ∧
      ∀ r, r ≠ "p" → r ≠ "r" → L' r = L r := by
  set N := t.nodes.size
  set p := (t.nodes.getX v).livePar
  set l := (t.nodes.getX p).children
  set S := phiS v side (sd10 t v side)
  have hsz10 : (sd10 t v side).nodes.size = N + 2 := by
    have h1 : ∀ (l : List Nat) (hh w : Nat) (X : Core), (l.foldl (fun s e => addTableS hh w e s)
      X).nodes.size = X.nodes.size :=
      fun l hh w X => fold_addTableS_size hh w l X
    rw [sd10_eq, chRes_size, sd8_eq, chRes_size]
    simp only [sd6, h1, sd4, Array.size_modify, ← sdJ_all, sdJ_size, N]
  have hvsz : v < (sd10 t v side).nodes.size := by omega
  -- the fields read
  have hpl : (S.nodes.getX p).children = l := by
    rw [phiS_getX_ne hpv, sd10_eq, chRes_children _ _ _ _ _ _ _ _ (by omega), sd8_eq,
      chRes_children _ _ _ _ _ _ _ _ (by omega), (sd6_CWL t v side p).1, sd1_getX t v hp]
  have hvlp : (S.nodes.getX v).livePar = p := by
    have h1 : sH t v = 1 ∨ v ∉ sCh2 t v side := by
      by_cases e : sH t v = 1
      · exact Or.inl e
      · exact Or.inr (fun h => hvk e (List.mem_of_mem_filter h))
    have h2 : sH t v = 1 ∨ v ∉ sCh1 t v side := by
      by_cases e : sH t v = 1
      · exact Or.inl e
      · exact Or.inr (fun h => hvk e (List.mem_of_mem_filter h))
    rw [phiS_getX_self hvsz]
    change ((sd10 t v side).nodes.getX v).livePar = p
    rw [sd10_eq, chRes_livePar_notin h1 (by omega), sd8_eq, chRes_livePar_notin h2 (by omega),
      (sd6_CWL t v side v).2.2, sd1_getX t v hv]
  have hrl : l.findIdx (· == v) < l.length := by
    rw [List.findIdx_lt_length]; exact ⟨v, hpar, by simp⟩
  set r := l.findIdx (· == v)
  have hvC : LK.view S p .children = l.map fun e => (e, 0) := by simp [LK.view, hpl, l]
  -- steps
  have e1 := evalF_assign_ok (κ := κ) (s := S) (L := L) (x := "p") (e := .rd (.n .livePar) "v")
    (v := p)
    (by simp [Exp.ev, hLv, hvN, Fld.cap, Fld.get, NF.get, hvlp])
  set L1 := upd L "p" p
  obtain ⟨Lf, cf, ef, hrf, hcf⟩ := findP_agree κ .children S
    (Machine.State.setLocs (fun _ => 0) ["i", "x"] [p, v]) (i := p) (x := v)
    (by simp [Machine.State.setLocs, Machine.State.upd])
    (by simp [Machine.State.setLocs, Machine.State.upd]) hpc
  rw [hvC, findIdx_pair0'] at hrf
  rw [hvC] at hcf
  have e2 := evalF_call_ok (q := findP .children) (args := [.var "p", .var "v"]) (ds := ["r"])
    (L := L1)
    (by simp [evList, Exp.ev, L1, Machine.State.upd, hLv]) ef
  set L2 := Machine.State.setLocs L1 ["r"] ((findP .children).rets.map Lf)
  have h2r : L2 "r" = r := by simp [L2, findP, Machine.State.setLocs, Machine.State.upd, hrf, r]
  have h2p : L2 "p" = p := by simp [L2, L1, findP, Machine.State.setLocs, Machine.State.upd]
  have hfr2 : ∀ x, x ≠ "p" → x ≠ "r" → L2 x = L x := fun x h1 h2 => by
    simp [L2, L1, findP, Machine.State.setLocs,
      Machine.State.upd, h1, h2]
  set l1 := (l.map fun e => (e, 0)).set r (N, 0)
  have hpS : p < S.nodes.size := by simp [S, phiS, hsz10]; omega
  have hvl1 : LK.children.valid l1 = true :=
    LK.valid_set (by rw [← hvC]; exact LK.valid_view S p .children) (by simp [LK.valid])
  have hso : LK.set κ S p l1 .children = some (LK.put S p l1 .children) :=
    LK.set_ok (by simp [LK.recOk, hpS]) hvl1 (by simp [l1]; omega) hpc
  have hrl' : r < (l.map fun e => (e, 0)).length := by simpa using hrl
  have e3 : evalF κ (.lwr .children false "p" "r" "v1") S L2 = .ok (LK.put S p l1 .children) L2
    7 := by
    have hv1 : L2 "v1" = N := by rw [hfr2 "v1" (by decide) (by decide), hLv1]
    have hg : ((l.map fun e => (e, 0)).getD r (0, 0)).2 = 0 := by
      rw [List.getD_eq_getElem _ _ hrl']; simp
    simp only [evalF, Exp.ev, h2p, h2r, hv1, hvC, ite_eq_left hrl', Bool.false_eq_true, ite_false,
      hg, Exp.cost]
    rw [show ((N, 0) : Nat × Nat) = (N, 0) from rfl, hso]
  set S3 := LK.put S p l1 .children
  have hvS3 : LK.view S3 p .children = l1 := by
    rw [LK.view_put (by simp [LK.recOk, hpS]) hvl1]; simp
  obtain ⟨Li, ci, ei, hci⟩ := insertIdxP_agree κ .children S3
    (Machine.State.setLocs (fun _ => 0) ["i", "p", "a", "b"] [p, r + 1, N + 1, 0]) (i := p) (p
      := r + 1)
    (a := N + 1) (b := 0) (by simp [Machine.State.setLocs, Machine.State.upd])
    (by simp [Machine.State.setLocs, Machine.State.upd])
    (by simp [Machine.State.setLocs, Machine.State.upd])
    (by simp [Machine.State.setLocs,
      Machine.State.upd]) (by simp [S3,  LK.recOk, hpS]) hpc
    (by simp [LK.valid]) (by rw [hvS3]; simp [l1]; omega) (by rw [hvS3]; simp [l1]; omega)
  rw [hvS3, LK.put_put] at ei
  rw [hvS3] at hci
  have e4 := evalF_call_ok (q := insertIdxP .children) (args := [.var "p", "r" + 1, .var "v2",
    0]) (ds := [])
    (L := L2) (by
      have hv2 : L2 "v2" = N + 1 := by rw [hfr2 "v2" (by decide) (by decide), hLv2]
      simp [evList, Exp.ev, h2p, h2r, hv2, Machine.BinOp.eval]) ei
  have hfin : LK.put S p (l1.insertIdx (r + 1) (N + 1, 0)) .children = phiS v side (sd11 t v
    side) := by
    have hl : (l1.insertIdx (r + 1) (N + 1, 0)).map (·.1) = l.replace1 v [N, N + 1] := by
      rw [replace1_eq v N (N + 1) l hpar]
      simp only [l1, r]
      rw [insertIdx_take_drop _ _ _ (by simp; omega), insertIdx_take_drop _ _ _ (by simp; omega)]
      simp [List.map_append, List.map_take, List.map_drop, List.map_set, Function.comp_def]
    have hX : ((sd10 t v side).nodes.getX p).children = l := by
      rw [← phiS_getX_ne (side := side) hpv]; exact hpl
    rw [show S = phiS v side (sd10 t v side) from rfl]
    unfold sd11
    generalize sd10 t v side = X at hX ⊢
    simp only [LK.put, phiS, hl]
    refine congrArg (fun a => ({
      X with
      nodes := a
    } : Core)) ?_
    rw [Array.modify_comm _ hpv.symm]
    refine congrArg (fun a : Array Node => a.modify v fun n => {
      n with
      side := side
    }) ?_
    apply Array.modify_congr_getX
    rw [hX]
  rw [hfin] at e4
  refine ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 e4)), ?_, ?_⟩
  · have hl1 : l1.length = l.length := by simp [l1]
    rw [hl1] at hci
    simp only [List.length_map] at hcf
    simp only [Exp.cost, costList, List.map, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil,
      ] at hcf hci ⊢
    omega
  · intro x h1 h2; simp only [Machine.State.setLocs]; exact hfr2 x h1 h2

/-! ### Stage 8: `v` becomes a ghost -/

/-- Turn the source into a draining ghost and clear its live child list. -/
def stage8S : Stm := cm{
  N[v].draining := 1; N[v].t1 := v1; N[v].t2 := v2; N[v].livePar := 0
  clear children[v] }

/-- What `v` becomes. -/
def ghostF (N : Nat) (side : List (Nat × Side)) (n : Node) : Node :=
  {
    n with
    draining := true
    t1 := N
    t2 := N + 1
    side := side
    livePar := NIL
    children := []
  }

theorem sdS_eq (t : Core) (v : Nat) (side : List (Nat × Side)) :
    sdS t v side = {
      sd11 t v side with
      nodes := (sd11 t v side).nodes.modify v (ghostF t.nodes.size side)
    } := rfl

theorem stage8S_ok {κ : Caps} {t : Core} {L : Loc} {v : Nat} {side : List (Nat × Side)}
    (hvs : v < (sd11 t v side).nodes.size) (hLv : L "v" = v) (hLv1 : L "v1" = t.nodes.size)
    (hLv2 : L "v2" = t.nodes.size + 1) (hvc : v < κ.lrec .children) :
    ∃ c, evalF κ stage8S (phiS v side (sd11 t v side)) L = .ok (sdS t v side) L c ∧ c ≤ 20 := by
  rw [sdS_eq]
  generalize sd11 t v side = X at hvs ⊢
  set N := t.nodes.size
  have hs : ∀ (Y : Core) (f : Node → Node), (Y.nodes.modify v f).size = Y.nodes.size := fun _ _
    => by simp
  have w1 := evalF_wrN_ok (κ := κ) (s := phiS v side X) (L := L) (k := .draining) (i := .var
    "v") (e := (1 : Exp))
    (j := v) (w := 1) (by simp [Exp.ev, hLv]) rfl (by simp [phiS, hvs])  rfl
  set Y1 := {
    phiS v side X with
    nodes := (phiS v side X).nodes.modify v (NF.set · 1 .draining)
  }
  have w2 := evalF_wrN_ok (κ := κ) (s := Y1) (L := L) (k := .t1) (i := .var "v") (e := .var "v1")
    (j := v) (w := N) (by simp [Exp.ev, hLv]) (by simp [Exp.ev, hLv1]) (by simp [Y1, phiS, hvs])
       rfl
  set Y2 := {
    Y1 with
    nodes := Y1.nodes.modify v (NF.set · N .t1)
  }
  have w3 := evalF_wrN_ok (κ := κ) (s := Y2) (L := L) (k := .t2) (i := .var "v") (e := .var "v2")
    (j := v) (w := N + 1) (by simp [Exp.ev, hLv]) (by simp [Exp.ev, hLv2]) (by simp [Y2, Y1,
      phiS, hvs])  rfl
  set Y3 := {
    Y2 with
    nodes := Y2.nodes.modify v (NF.set · (N + 1) .t2)
  }
  have w4 := evalF_wrN_ok (κ := κ) (s := Y3) (L := L) (k := .livePar) (i := .var "v") (e := (0 :
    Exp))
    (j := v) (w := 0) (by simp [Exp.ev, hLv]) rfl (by simp [Y3, Y2, Y1, phiS, hvs])  rfl
  set Y4 := {
    Y3 with
    nodes := Y3.nodes.modify v (NF.set · 0 .livePar)
  }
  have w5 : evalF κ (.lclear .children "v") Y4 L = .ok (LK.put Y4 v [] .children) L 3 := by
    have hso := LK.set_ok (κ := κ) (s := Y4) (i := v) (l := []) (k := .children)
      (by simp [LK.recOk, Y4, Y3, Y2, Y1, phiS, hvs]) (by simp [LK.valid]) (by simp) hvc
    simp [evalF, Exp.ev, hLv, hso, Exp.cost]
  have hfin : LK.put Y4 v [] .children = {
    X with
    nodes := X.nodes.modify v (ghostF N side)
  } := by
    simp only [LK.put, Y4, Y3, Y2, Y1, phiS, Array.modify_modify_same]
    refine congrArg (fun a => ({
      X with
      nodes := a
    } : Core)) ?_
    congr 1
  rw [hfin] at w5
  exact ⟨_, evalF_seq_ok2 w1 (evalF_seq_ok2 w2 (evalF_seq_ok2 w3 (evalF_seq_ok2 w4 w5))), by
    simp [Exp.cost]⟩

/-! ### `startDrain` -/

/-- Detect a nonleaf cut that leaves no child on its left side. -/
def sdCond : Exp := cme{ 1 < h && k = 0 }
/-- Construct a drain's side assignment, targets, tables, links and ghost source. -/
def sdMain : Stm := cm{
  if k < nk then b := children[v][k].fst else b := 0
  drainSideS; newNodesS; insS; stage3S; stage4S; stage56S; stage7S; stage8S }
/-- **`startDrain v`** at Level M (local `v`). -/
def startDrainS : Stm := cm{
  h := N[v].height; nk := len children[v]
  if nk < 2 then skip else { drainCutS; if ‹sdCond› then skip else sdMain } }

/-- The cost bound of `startDrain`, in the lengths of the lists it walks. -/
def sdCost (K T I S B P : Nat) : Nat :=
  2 * pushCost + 1000 + 300 * K + T * (280 + 20 * K + 115 * T) + I * (1001 + 400 * B) + 80 * I +
    2 * (T * (320 + 40 * K + 40 * S)) + 80 * T + 2 * (K * (140 + 20 * S)) + 111 * P

theorem sd10_size (t : Core) (v : Nat) (side : List (Nat × Side)) :
    (sd10 t v side).nodes.size = t.nodes.size + 2 := by
  have h1 : ∀ (l : List Nat) (hh w : Nat) (X : Core), (l.foldl (fun s e => addTableS hh w e s)
    X).nodes.size = X.nodes.size :=
    fun l hh w X => fold_addTableS_size hh w l X
  rw [sd10_eq, chRes_size, sd8_eq, chRes_size]
  simp only [sd6, h1, sd4, Array.size_modify, ← sdJ_all, sdJ_size]

theorem sd11_size (t : Core) (v : Nat) (side : List (Nat × Side)) :
    (sd11 t v side).nodes.size = t.nodes.size + 2 := by simp [sd11, sd10_size]

theorem startDrainS_ok {κ : Caps} {t : Core} {L : Loc} {v B : Nat} {side : List (Nat × Side)}
    -- Level F (as in `startDrain_run`)
    (hk2 : 2 ≤ (sKids t v).length) (hk0 : ¬(sH t v > 1 ∧ sK t v = 0)) (hside : sSideO t v = some
      side)
    (hroom : ∀ T ∈ (t.nodes.getX v).inTables, RoomOK t v T) (hnd : (t.nodes.getX v).inTables.Nodup)
    (hpar : v ∈ (t.nodes.getX (t.nodes.getX v).livePar).children) (hv : v < t.nodes.size)
    -- the shape around `v`
    (hvT : v ∉ (t.nodes.getX v).inTables) (hvk : sH t v ≠ 1 → v ∉ (t.nodes.getX v).children)
    (hK : sH t v - 1 ≠ 0 → ∀ e ∈ (t.nodes.getX v).table.map (·.1), e < t.nodes.size)
    (hKN : ∀ e ∈ (t.nodes.getX v).table.map (·.1), e < κ.tbl .N ∧ (sH t v - 1 = 0 → e < κ.lrec
      .cin))
    (hks : sH t v ≠ 1 → ∀ e ∈ (t.nodes.getX v).children, e < t.nodes.size)
    (hksl : sH t v = 1 → ∀ e ∈ (t.nodes.getX v).children, e < κ.arr .lpar)
    (hp : (t.nodes.getX v).livePar < t.nodes.size) (hpv : (t.nodes.getX v).livePar ≠ v)
    (hB : ∀ T ∈ (t.nodes.getX v).inTables, (t.nodes.getX T).table.length ≤ B ∧ (t.nodes.getX
      T).side.length ≤ B)
    -- capacities
    (hLv : L "v" = v) (hcN : t.nodes.size + 2 ≤ κ.tbl .N)
    (hcrc : t.nodes.size + 2 ≤ κ.lrec .children) (hcrs : t.nodes.size + 2 ≤ κ.lrec .side)
    (hcrt : t.nodes.size + 2 ≤ κ.lrec .table) (hcri : t.nodes.size + 2 ≤ κ.lrec .inTab)
    (hcT : ∀ T ∈ (t.nodes.getX v).inTables,
      (t.nodes.getX T).table.length + 2 ≤ κ.lcap .table ∧ (t.nodes.getX T).side.length + 2 ≤
        κ.lcap .side)
    (hcS : 2 * (t.nodes.getX v).table.length + 1 ≤ κ.lcap .side)
    (hcTv : (t.nodes.getX v).table.length ≤ κ.lcap .table)
    (hcI : (t.nodes.getX v).inTables.length ≤ κ.lcap .inTab)
    (hc4 : ∀ e ∈ (t.nodes.getX v).table.map (·.1), tabsLen t (sH t v - 1) e + 2 * (t.nodes.getX
      v).table.length ≤
      (if sH t v ≤ 1 then κ.lcap .cin else κ.lcap .inTab))
    (hcC : (t.nodes.getX v).children.length ≤ κ.lcap .children)
    (hcP : (t.nodes.getX (t.nodes.getX v).livePar).children.length + 1 ≤ κ.lcap .children) :
    ∃ L' c, evalF κ startDrainS t L = .ok (sdS t v side) L' c ∧
      c ≤ sdCost (t.nodes.getX v).children.length (t.nodes.getX v).table.length
        (t.nodes.getX v).inTables.length side.length B
        (t.nodes.getX (t.nodes.getX v).livePar).children.length := by
  set N := t.nodes.size
  set kids := (t.nodes.getX v).children
  have hvN : v < κ.tbl .N := by omega
  have hvc : v < κ.lrec .children := by omega
  have hvs : v < κ.lrec .side := by omega
  have hvt : v < κ.lrec .table := by omega
  have hvi : v < κ.lrec .inTab := by omega
  have hkN : sH t v ≠ 1 → ∀ e ∈ kids, e < κ.tbl .N := fun h1 e he => by have := hks h1 e he; omega
  have hTN : ∀ e ∈ (t.nodes.getX v).table.map (·.1), e < κ.tbl .N := fun e he => (hKN e he).1
  -- the prefix
  have a1 := evalF_assign_ok (κ := κ) (s := t) (L := L) (x := "h") (e := .rd (.n .height) "v")
    (v := sH t v)
    (by simp [Exp.ev, hLv, hvN, Fld.cap, Fld.get, NF.get, sH])
  have a2 := evalF_assign_ok (κ := κ) (s := t) (L := upd L "h" (sH t v)) (x := "nk") (e := .llen
    .children "v")
    (v := kids.length) (by simp [Exp.ev, Machine.State.upd, hLv, hvc, LK.view, kids])
  set L2 := upd (upd L "h" (sH t v)) "nk" kids.length
  have hk2' : 2 ≤ kids.length := hk2
  have e3 : ("nk" <ₑ 2 : Exp).ev κ t L2 = some 0 := by
    simp [Exp.ev, Machine.BinOp.eval, L2,
      Machine.State.upd]; omega
  obtain ⟨L4, c4, e4, hcc4, hk4, hF4⟩ := drainCutS_ok (κ := κ) (s := t) (L := L2) (v := v) (h :=
    sH t v)
    (by simp [L2, Machine.State.upd,
      hLv]) (by simp [L2, Machine.State.upd]) hvc hkN
  have hk4' : L4 "k" = sK t v := hk4
  have hF4' : ∀ r, r ≠ "n" → r ≠ "j" → r ≠ "e" → r ≠ "w" → r ≠ "t" → r ≠ "b" → r ≠ "c" → r ≠ "d"
    → r ≠ "a" →
      r ≠ "k" → r ≠ "h" → r ≠ "nk" → L4 r = L r := by
    intro r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
    rw [hF4 r h1 h2 h3 h4 h5 h6 h7 h8 h9 h10]; simp [L2, Machine.State.upd, h11, h12]
  have h4h : L4 "h" = sH t v := by
    rw [hF4 "h" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      decide) (by decide)
      (by decide) (by decide)]; simp [L2, Machine.State.upd]
  have h4nk : L4 "nk" = kids.length := by
    rw [hF4 "nk" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      decide) (by decide)
      (by decide) (by decide)]; simp [L2, Machine.State.upd]
  have h4v : L4 "v" = v := by
    rw [hF4' "v" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
      decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), hLv]
  have e5 : sdCond.ev κ t L4 = some 0 := by
    simp only [sdCond, Exp.ev, h4h, hk4', Option.bind_some, Machine.BinOp.eval,
      Exp.ofNat_def]
    by_cases h1 : 1 < sH t v
    · have : sK t v ≠ 0 := fun h => hk0 ⟨h1, h⟩
      simp [h1, this]
    · simp [h1]
  -- the boundary
  have eb : ∃ cb, evalF κ (.ite ("k" <ₑ "nk") ("b" ::= .lrd .children false "v" "k") ("b" ::=
    0)) t L4 =
      .ok t (upd L4 "b" (sB t v)) cb ∧ cb ≤ 15 := by
    by_cases hkl : sK t v < kids.length
    · have a := evalF_assign_ok (κ := κ) (s := t) (L := L4) (x := "b") (e := .lrd .children
        false "v" "k")
        (v := sB t v) (by
          simp [Exp.ev, h4v, hk4', hvc, LK.view, kids, hkl, sB, sKids, List.getD_eq_getElem?_getD])
      exact ⟨_, evalF_ite_t (v := 1) (by simp [Exp.ev, Machine.BinOp.eval, hk4', h4nk, hkl])
        one_ne_zero a,
        by simp [Exp.cost]⟩
    · have a := evalF_assign_ok (κ := κ) (s := t) (L := L4) (x := "b") (e := (0 : Exp)) (v := sB
        t v) (by
          simp only [Exp.ofNat_def, List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_none (by simpa [kids] using hkl)]; rfl)
      exact ⟨_, evalF_ite_f (by simp [Exp.ev, Machine.BinOp.eval, hk4', h4nk]; omega) a, by simp
        [Exp.cost]⟩
  obtain ⟨cb, eb, hcb⟩ := eb
  set L5 := upd L4 "b" (sB t v)
  -- the side list
  obtain ⟨L6, c6, e6, hc6, hF6⟩ := drainSideS_ok (κ := κ) (s := t) (L := L5) (v := v) (b := sB t
    v) (side := side)
    (by simp [L5, Machine.State.upd,
      h4v]) (by simp [L5, Machine.State.upd]) hv hvN hvs hvt hvc hTN hcS hside
  rw [put_side_phi] at e6
  have k6 : ∀ r, r = "v" ∨ r = "h" → L6 r = L4 r := by
    rintro r (rfl | rfl) <;>
      rw [hF6 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
        decide) (by decide)] <;>
      simp [L5, Machine.State.upd]
  -- the new nodes
  obtain ⟨L7, e7, h7v1, h7v2, hF7⟩ := newNodesS_ok (κ := κ) (t := t) (L := L6) (v := v) (side :=
    side)
    (by rw [k6 "h" (Or.inr rfl), h4h]) hv hcN
  have k7 : ∀ r, r = "v" ∨ r = "h" → L7 r = L4 r := by
    rintro r hr; rw [hF7 r (by rcases hr with rfl | rfl <;> decide) (by rcases hr with rfl | rfl
      <;> decide), k6 r hr]
  -- the insertions
  obtain ⟨L8, c8, e8, hc8, hF8⟩ := insS_ok (κ := κ) (t := t) (L := L7) (v := v) (B := B) (side
    := side) hv hnd hvT hroom
    (by rw [k7 "v" (Or.inl rfl), h4v]) h7v1 h7v2 hvi
    (fun T hT => by have := (hroom T hT).lt; exact ⟨by omega, by omega, by omega, (hcT T hT).1,
      (hcT T hT).2⟩) hB
  have k8 : ∀ r, r = "v" ∨ r = "h" ∨ r = "v1" ∨ r = "v2" → L8 r = L7 r := by
    rintro r hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact hF8 _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have h8v : L8 "v" = v := by rw [k8 "v" (Or.inl rfl), k7 "v" (Or.inl rfl), h4v]
  have h8h : L8 "h" = sH t v := by rw [k8 "h" (Or.inr (Or.inl rfl)), k7 "h" (Or.inr rfl), h4h]
  have h8v1 : L8 "v1" = N := by rw [k8 "v1" (Or.inr (Or.inr (Or.inl rfl))), h7v1]
  have h8v2 : L8 "v2" = N + 1 := by rw [k8 "v2" (Or.inr (Or.inr (Or.inr rfl))), h7v2]
  -- the tables of v1, v2
  obtain ⟨L9, c9, e9, hc9, hF9⟩ := stage3S_ok (κ := κ) (t := t) (L := L8) (v := v) (side :=
    side) hv hvT hroom
    h8v h8v1 h8v2 h8h hvc hvs hvt (by omega) hvi (by omega) hTN hcTv hcI
  have k9 : ∀ r, r = "v" ∨ r = "h" ∨ r = "v1" ∨ r = "v2" → L9 r = L8 r := by
    rintro r hr
    rcases hr with rfl | rfl | rfl | rfl <;>
      exact hF9 _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
        decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  -- the entries
  obtain ⟨L10, c10, e10, hc10, hF10⟩ := stage4S_ok (κ := κ) (t := t) (L := L9) (v := v) (side :=
    side) hv
    (fun h1 => hK (by omega))
    (by rw [k9 "v1" (by simp),
      h8v1]) (by rw [k9 "v2" (by simp), h8v2]) (by rw [k9 "h" (by simp), h8h]) (by omega)
    (fun e he => ⟨fun h1 => (hKN e he).2 (by omega), fun h1 => by
      have := hK (by omega) e he
      omega⟩) hc4
  have k10 : ∀ r, r = "v" ∨ r = "h" ∨ r = "v1" ∨ r = "v2" → L10 r = L8 r := by
    rintro r hr
    rw [hF10 r (by rcases hr with rfl | rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl
      | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl |
        rfl <;> decide), k9 r hr]
  -- the children
  obtain ⟨L11, c11, e11, hc11, hF11⟩ := stage56S_ok (κ := κ) (t := t) (L := L10) (v := v) (side
    := side) hv hvk
    (fun e he => ⟨fun h1 => ⟨hks h1 e he, by have := hks h1 e he; omega⟩, fun h1 => hksl h1 e he⟩)
    (by rw [k10 "v" (by simp),
      h8v]) (by rw [k10 "v1" (by simp), h8v1]) (by rw [k10 "v2" (by simp), h8v2])
    (by rw [k10 "h" (by simp), h8h]) hvc hvs (by omega)  hvN hcC
  have k11 : ∀ r, r = "v" ∨ r = "v1" ∨ r = "v2" → L11 r = L8 r := by
    rintro r hr
    rw [hF11 r (by rcases hr with rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl
      <;> decide)
      (by rcases hr with rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl <;> decide)
      (by rcases hr with rfl | rfl | rfl <;> decide), k10 r (by rcases hr with rfl | rfl | rfl
        <;> simp)]
  -- the parent
  obtain ⟨L12, c12, e12, hc12, hF12⟩ := stage7S_ok (κ := κ) (t := t) (L := L11) (v := v) (side
    := side) hv hvk hp hpv
    hpar (by rw [k11 "v" (by simp), h8v]) (by rw [k11 "v1" (by simp), h8v1]) (by rw [k11 "v2"
      (by simp), h8v2])
    (by omega) hvN hcP
  have k12 : ∀ r, r = "v" ∨ r = "v1" ∨ r = "v2" → L12 r = L8 r := by
    rintro r hr
    rw [hF12 r (by rcases hr with rfl | rfl | rfl <;> decide) (by rcases hr with rfl | rfl | rfl
      <;> decide), k11 r hr]
  -- v becomes a ghost
  obtain ⟨c13, e13, hc13⟩ := stage8S_ok (κ := κ) (t := t) (L := L12) (v := v) (side := side)
    (by rw [sd11_size]; omega) (by rw [k12 "v" (by simp), h8v]) (by rw [k12 "v1" (by simp), h8v1])
    (by rw [k12 "v2" (by simp), h8v2])  hvc
  refine ⟨L12, _, evalF_seq_ok2 a1 (evalF_seq_ok2 a2 (evalF_ite_f e3 (evalF_seq_ok2 e4
    (evalF_ite_f e5
    (evalF_seq_ok2 eb (evalF_seq_ok2 e6 (evalF_seq_ok2 e7 (evalF_seq_ok2 e8 (evalF_seq_ok2 e9
      (evalF_seq_ok2 e10
      (evalF_seq_ok2 e11 (evalF_seq_ok2 e12 e13)))))))))))), ?_⟩
  simp only [kids] at hcc4 hc6 hc8 hc9 hc10 hc11 hc12 hc13 hcb ⊢
  simp only [sdCost, Exp.cost, sdCond, Exp.ofNat_def] at hcc4 hc6 hc8 hc9 hc10 hc11 hc12 hc13 hcb ⊢
  omega

/-- `startDrain v` with too few children or an empty cut above height one changes nothing. -/
theorem startDrainS_noop {κ : Caps} {t : Core} {L : Loc} {v : Nat}
    (hno : (sKids t v).length < 2 ∨ (sH t v > 1 ∧ sK t v = 0)) (hv : v < t.nodes.size)
    (hLv : L "v" = v) (hcN : t.nodes.size ≤ κ.tbl .N) (hcrc : t.nodes.size ≤ κ.lrec .children)
    (hks : sH t v ≠ 1 → ∀ e ∈ (t.nodes.getX v).children, e < κ.tbl .N) :
    ∃ L' c, evalF κ startDrainS t L = .ok t L' c ∧ c ≤ 230 + 300 * (t.nodes.getX
      v).children.length := by
  set kids := (t.nodes.getX v).children
  have hvN : v < κ.tbl .N := by omega
  have hvc : v < κ.lrec .children := by omega
  have a1 := evalF_assign_ok (κ := κ) (s := t) (L := L) (x := "h") (e := .rd (.n .height) "v")
    (v := sH t v)
    (by simp [Exp.ev, hLv, hvN, Fld.cap, Fld.get, NF.get, sH])
  have a2 := evalF_assign_ok (κ := κ) (s := t) (L := upd L "h" (sH t v)) (x := "nk") (e := .llen
    .children "v")
    (v := kids.length) (by simp [Exp.ev, Machine.State.upd, hLv, hvc, LK.view, kids])
  set L2 := upd (upd L "h" (sH t v)) "nk" kids.length
  by_cases h2 : kids.length < 2
  · refine ⟨L2, _, evalF_seq_ok2 a1 (evalF_seq_ok2 a2 (evalF_ite_t (v := 1)
      (by simp [Exp.ev, Machine.BinOp.eval, L2,
        Machine.State.upd]; omega) one_ne_zero evalF_skip)), ?_⟩
    simp [Exp.cost]; omega
  · have hk : sH t v > 1 ∧ sK t v = 0 := by
      rcases hno with h | h
      · exact absurd h h2
      · exact h
    have e3 : ("nk" <ₑ 2 : Exp).ev κ t L2 = some 0 := by
      simp [Exp.ev, Machine.BinOp.eval, L2,
        Machine.State.upd]; omega
    obtain ⟨L4, c4, e4, hcc4, hk4, hF4⟩ := drainCutS_ok (κ := κ) (s := t) (L := L2) (v := v) (h
      := sH t v)
      (by simp [L2, Machine.State.upd,
        hLv]) (by simp [L2, Machine.State.upd]) hvc hks
    have hk4' : L4 "k" = sK t v := hk4
    have h4h : L4 "h" = sH t v := by
      rw [hF4 "h" (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by
        decide) (by decide)
        (by decide) (by decide)]; simp [L2, Machine.State.upd]
    have e5 : sdCond.ev κ t L4 = some 1 := by
      simp [sdCond, Exp.ev, h4h, hk4', Machine.BinOp.eval, hk.1, hk.2]
    refine ⟨L4, _, evalF_seq_ok2 a1 (evalF_seq_ok2 a2 (evalF_ite_f e3 (evalF_seq_ok2 e4
      (evalF_ite_t e5 one_ne_zero evalF_skip)))), ?_⟩
    simp only [kids] at hcc4 ⊢
    simp only [Exp.cost, sdCond, Exp.ofNat_def] at hcc4 ⊢
    omega

end OrderMaintenance.Impl
