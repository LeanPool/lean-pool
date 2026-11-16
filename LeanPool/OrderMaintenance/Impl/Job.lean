/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.Reserve
public import LeanPool.OrderMaintenance.Impl.Finish
public import LeanPool.OrderMaintenance.Impl.NoJob
public import LeanPool.OrderMaintenance.Proof.Top.Step


/-!
# M6: the top structure's job at Level M (`jobStep`)

The running job lives in the optional record `resJob`; the program reads its fields into locals
(`jx jy jz` and the program counter `jt ja jb jc jd`, `pcEnc`) and writes the new counter with
`pcSet` (or clears the job). Each case is matched against the Level F run lemma the cost proof
uses.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Proof.Top
open OrderMaintenance.Machine (Reg BinOp UnOp)

local notation "upd" => Machine.State.upd

/-! ### A copy step -/

/-- Copy a reservation path level to both replacement chunks and repair range endpoints. -/
def jcopyS : Stm := cm{
  v := path(jx, ja)
  path(jy, ja) := v; path(jz, ja) := v
  if N[v].first = jx then N[v].first := jy
  if N[v].last = jx then N[v].last := jz
  if ja < P.H then pcSet(0, ja + 1, 0, 0, 0) else pcSet(1, 0, 0, 0, 0) }

theorem getX_default_of_le {α : Type} [Inhabited α] {a : Array α} {i : Nat} (h : a.size ≤ i) :
  a.getX i = default := by
  simp [Array.getX, Array.getD, show ¬i < a.size by omega]

theorem jcopyS_ok {κ : Caps} {s : Core} {L : Loc} {j : Job} {l : Nat} (hjob : s.resJob = some j)
    (hx : L "jx" = j.x) (hy : L "jy" = j.y) (hz : L "jz" = j.z) (hl : L "ja" = l)
    (hx0 : j.x ≠ NIL)
    (hnx : notPrep s j.x) (hny : notPrep s j.y) (hnz : notPrep s j.z)
    (hxC : j.x < κ.tbl .C) (hyC : j.y < κ.tbl .C) (hzC : j.z < κ.tbl .C) (hlw : l < κ.pw)
    (hvN : (s.path.getX j.x).getX l < κ.tbl .N) :
    ∃ L' c, evalF κ jcopyS s L = .ok {
      copyC s j l with
      resJob := some (copyNext s.P j l)
    } L' c
      ∧ c ≤ 100 ∧
      ∀ r, r ≠ "v" → L' r = L r := by
  set v := (s.path.getX j.x).getX l
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "v") (e := .prd "jx" "ja") (v := v)
    (by simp [Exp.ev, hx, hl, hxC, hlw, rowOf_notPrep hnx, v])
  set L1 := upd L "v" v
  have h1 : ∀ r, r ≠ "v" → L1 r = L r := fun r h => by simp [L1, Machine.State.upd, h]
  have h1x : L1 "jx" = j.x := by rw [h1 _ (by decide), hx]
  have h1y : L1 "jy" = j.y := by rw [h1 _ (by decide), hy]
  have h1z : L1 "jz" = j.z := by rw [h1 _ (by decide), hz]
  have h1l : L1 "ja" = l := by rw [h1 _ (by decide), hl]
  have h1v : L1 "v" = v := by simp [L1, Machine.State.upd]
  set s1 : Core := {
    s with
    path := s.path.setX j.y ((s.path.getX j.y).setX l v)
  }
  have e2 : evalF κ (.pwr "jy" "ja" "v") s L1 = .ok s1 L1 10 := by
    simp [evalF, Exp.ev, h1y, h1l, h1v, hyC, hlw, hny, Exp.cost, s1]
  set s2 : Core := {
    s1 with
    path := s1.path.setX j.z ((s1.path.getX j.z).setX l v)
  }
  have e3 : evalF κ (.pwr "jz" "ja" "v") s1 L1 = .ok s2 L1 10 := by
    have : notPrep s1 j.z := hnz
    simp [evalF, Exp.ev, h1z, h1l, h1v, hzC, hlw, this, Exp.cost, s2]
  set V := s.nodes.getX v
  have hs2v : s2.nodes.getX v = V := rfl
  -- `first`
  set s3 : Core := if V.first == j.x then {
    s2 with
    nodes := s2.nodes.modify v fun n => {
      n with
      first := j.y
    }
  } else s2
  have e4 : ∃ c4, evalF κ (.ite (.rd (.n .first) "v" =ₑ "jx") (.wr (.n .first) "v" "jy") .skip)
    s2 L1 =
      .ok s3 L1 c4 ∧ c4 ≤ 12 := by
    by_cases hf : V.first = j.x
    · have hvs : v < s.nodes.size := by
        by_contra hc
        have : V = default := getX_default_of_le (by omega)
        rw [this] at hf; exact hx0 (by
          rw [← hf]
          rfl)
      have w := evalF_wrN_ok (κ := κ) (s := s2) (L := L1) (k := .first) (i := .var "v") (e :=
        .var "jy") (j := v)
        (w := j.y) (by simp [Exp.ev, h1v]) (by simp [Exp.ev, h1y]) hvs  rfl
      have hs3 : s3 = {
        s2 with
        nodes := s2.nodes.modify v (NF.set · j.y .first)
      } := by
        simp only [s3, hf, beq_self_eq_true, ite_true]; rfl
      rw [← hs3] at w
      exact ⟨_, evalF_ite_t (v := 1) (by
        simp [Exp.ev, Machine.BinOp.eval, h1v, h1x, hvN, Fld.cap, Fld.get, NF.get, hs2v, hf])
          one_ne_zero w, by simp [Exp.cost]⟩
    · have hs3 : s3 = s2 := by simp only [s3]; rw [ite_eq_right (by simpa using hf)]
      rw [hs3]
      exact ⟨_, evalF_ite_f (by
        simp [Exp.ev, Machine.BinOp.eval, h1v, h1x, hvN, Fld.cap, Fld.get, NF.get, hs2v, hf])
          evalF_skip, by simp [Exp.cost]⟩
  obtain ⟨c4, e4, hc4⟩ := e4
  have hs3v : (s3.nodes.getX v).last = V.last := by
    simp only [s3]; split
    · simp only [getX_modify']; split <;> rfl
    · rfl
  have hs3n : s3.nodes.size = s.nodes.size := by simp only [s3]; split <;> simp [s2, s1]
  -- `last`
  set s4 : Core := if V.last == j.x then {
    s3 with
    nodes := s3.nodes.modify v fun n => {
      n with
      last := j.z
    }
  } else s3
  have e5 : ∃ c5, evalF κ (.ite (.rd (.n .last) "v" =ₑ "jx") (.wr (.n .last) "v" "jz") .skip) s3
    L1 =
      .ok s4 L1 c5 ∧ c5 ≤ 12 := by
    by_cases hf : V.last = j.x
    · have hvs : v < s.nodes.size := by
        by_contra hc
        have : V = default := getX_default_of_le (by omega)
        rw [this] at hf; exact hx0 (by
          rw [← hf]
          rfl)
      have w := evalF_wrN_ok (κ := κ) (s := s3) (L := L1) (k := .last) (i := .var "v") (e :=
        .var "jz") (j := v)
        (w := j.z) (by simp [Exp.ev, h1v]) (by simp [Exp.ev, h1z]) (by
          rw [hs3n]
          exact hvs)  rfl
      have hs4 : s4 = {
        s3 with
        nodes := s3.nodes.modify v (NF.set · j.z .last)
      } := by
        simp only [s4, hf, beq_self_eq_true, ite_true]; rfl
      rw [← hs4] at w
      exact ⟨_, evalF_ite_t (v := 1) (by
        simp [Exp.ev, Machine.BinOp.eval, h1v, h1x, hvN, Fld.cap, Fld.get, NF.get, hs3v, hf])
          one_ne_zero w, by simp [Exp.cost]⟩
    · have hs4 : s4 = s3 := by simp only [s4]; rw [ite_eq_right (by simpa using hf)]
      rw [hs4]
      exact ⟨_, evalF_ite_f (by
        simp [Exp.ev, Machine.BinOp.eval, h1v, h1x, hvN, Fld.cap, Fld.get, NF.get, hs3v, hf])
          evalF_skip, by simp [Exp.cost]⟩
  obtain ⟨c5, e5, hc5⟩ := e5
  have hs4c : s4 = copyC s j l := rfl
  have hj4 : (copyC s j l).resJob = some j := by
    rw [← hs4c]; simp only [s4, s3]; split <;> split <;> exact hjob
  have hP : (copyC s j l).P = s.P := by rw [← hs4c]; simp only [s4, s3]; split <;> split <;> rfl
  rw [hs4c] at e5
  -- the program counter
  have e6 : ∃ c6, evalF κ (.ite ("ja" <ₑ .prm .H) (.pcSet 0 ("ja" + 1) 0 0 0) (.pcSet 1 0 0 0
    0)) (copyC s j l) L1 =
      .ok {
        copyC s j l with
        resJob := some (copyNext s.P j l)
      } L1 c6 ∧ c6 ≤ 40 := by
    by_cases hH : l < s.P.H
    · have hn : copyNext s.P j l = {
      j with
      pc := .copy (l + 1)
    } := by simp [copyNext, hH]
      rw [hn]
      refine ⟨_, evalF_ite_t (v := 1) (by
        simp [Exp.ev, Machine.BinOp.eval, h1l, PF.get, hP, hH]) one_ne_zero
        (by
          simp [evalF, evList, Exp.ev, hj4, h1l, Machine.BinOp.eval, pcDec]
          rfl), ?_⟩
      simp [costList, Exp.cost]
    · have hn : copyNext s.P j l = {
      j with
      pc := .walk none
    } := by simp [copyNext, hH]
      rw [hn]
      refine ⟨_, evalF_ite_f (by
        simp [Exp.ev, Machine.BinOp.eval, h1l, PF.get, hP, hH])
        (by
          simp [evalF, evList, Exp.ev, hj4, pcDec]
          rfl), ?_⟩
      simp [costList, Exp.cost]
  obtain ⟨c6, e6, hc6⟩ := e6
  refine ⟨L1, _, evalF_seq_ok2 a1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 (evalF_seq_ok2 e4
    (evalF_seq_ok2 e5 e6)))),
    ?_, h1⟩
  simp only [Exp.cost] at hc4 hc5 ⊢; omega

/-! ### A sweep step that moves a chunk (`drainStep`, `drainStep_move`) -/

theorem lor_shift (a c b h : Nat) (hc : c < 2 ^ b) (hh : 1 ≤ h) :
    (a <<< (h * b)) ||| (c <<< ((h - 1) * b)) = a * 2 ^ (h * b) + c * 2 ^ ((h - 1) * b) := by
  have e : h * b = b + (h - 1) * b := by
    obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
    simp; ring
  rw [e, Nat.shiftLeft_add, ← Nat.shiftLeft_or_distrib, ← Nat.shiftLeft_add_eq_or_of_lt hc]
  simp only [Nat.shiftLeft_eq, pow_add]; ring

/-- `r := belowOf h c` (local `h`). -/
def belowS (c r : Reg) : Stm := cm{ if h = 1 then ‹r› := ‹c› else ‹r› := path(‹c›, h - 1) }

theorem belowS_ok {κ : Caps} {s : Core} {L : Loc} {c r : Reg} {h y : Nat} (hh : L "h" = h) (hc :
  L c = y)
    (h1 : 1 ≤ h) (hnp : notPrep s y) (hyC : y < κ.tbl .C) (hw : h - 1 < κ.pw) :
    evalF κ (belowS c r) s L = .ok s (upd L r (if h == 1 then y else (s.path.getX y).getX (h - 1)))
      (if h = 1 then 6 else 16) := by
  by_cases e : h = 1
  · simp [belowS, evalF, Exp.ev, hh, hc, Machine.BinOp.eval, e, Exp.cost,
    Res.addCost]
  · simp [belowS, evalF, Exp.ev, hh, hc, Machine.BinOp.eval, e, Exp.cost,
    Res.addCost, hyC, hw,
      rowOf_notPrep hnp, h1]

/-- Select the left drain target and initialize the moved range's boundary locals. -/
def dsLeftS : Stm := cm{ t := N[v].t1; lf := 1; y := y0; bl := b0 }
/-- Select the right drain target after checking its recorded side assignment. -/
def dsRightS : Stm := cm{
  y := N[v].last; ‹belowS "y" "bl"›
  (f, sd) ← ‹lookupP .side›(v, bl); if f then skip else fail
  if sd = 1 then skip else fail; t := N[v].t2; lf := 0 }
/-- The chunk moved (`y`), its target (`t`), the direction (`lf`) and the entry below (`bl`). -/
def dsPickS : Stm := cm{
  y0 := N[v].first; ‹belowS "y0" "b0"›
  (f, sd) ← ‹lookupP .side›(v, b0); if f then skip else fail
  if sd = 0 then dsLeftS else dsRightS }

theorem dsPickS_ok {κ : Caps} {s : Core} {L : Loc} {v : Nat} (hv : L "v" = v) (hh : L "h" =
  (s.nodes.getX v).height)
    (h1 : 1 ≤ (s.nodes.getX v).height)
    (hside : goesLeft s v ∨
      lookup (s.nodes.getX v).side (belowY s v (s.nodes.getX v).first) = some .right ∧
      lookup (s.nodes.getX v).side (belowY s v (s.nodes.getX v).last) = some .right)
    (hvN : v < κ.tbl .N) (hvs : v < κ.lrec .side)
    (hnf : notPrep s (s.nodes.getX v).first) (hnl : notPrep s (s.nodes.getX v).last)
    (hfC : (s.nodes.getX v).first < κ.tbl .C) (hlC : (s.nodes.getX v).last < κ.tbl .C)
    (hw : (s.nodes.getX v).height - 1 < κ.pw) :
    ∃ L' c, evalF κ dsPickS s L = .ok s L' c ∧ L' "y" = dsY s v ∧ L' "t" = dsT s v ∧
      L' "lf" = b2n (decide (goesLeft s v)) ∧ L' "bl" = belowY s v (dsY s v) ∧
      c ≤ 300 + 80 * (s.nodes.getX v).side.length ∧
      ∀ r, r ≠ "y0" → r ≠ "b0" → r ≠ "f" → r ≠ "sd" → r ≠ "t" → r ≠ "lf" → r ≠ "y" → r ≠ "bl" →
        L' r = L r := by
  set V := s.nodes.getX v
  set h := V.height
  have hvs' : LK.view s v .side = encS V.side := rfl
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "y0") (e := .rd (.n .first) "v")
    (v := V.first)
    (by simp [Exp.ev, hv, hvN, Fld.cap, Fld.get, NF.get, V])
  set L1 := upd L "y0" V.first
  have e2 := belowS_ok (κ := κ) (s := s) (L := L1) (c := "y0") (r := "b0") (h := h)
    (by
      simp [L1, Machine.State.upd, hh]) (by simp [L1, Machine.State.upd]) h1 hnf hfC hw
  set b0 := if h == 1 then V.first else (s.path.getX V.first).getX (h - 1)
  have hb0 : b0 = belowY s v V.first := rfl
  set L2 := upd L1 "b0" b0
  obtain ⟨Lf, cf, ef, hf, hsd, -, -, hcf⟩ := lookupP_agree κ .side s
    (Machine.State.setLocs (fun _ => 0) ["i", "x"] [v, b0]) (i := v) (x := b0)
    (by
      simp [Machine.State.setLocs, Machine.State.upd])
    (by
      simp [Machine.State.setLocs, Machine.State.upd]) hvs
  rw [hvs', lookup_encS, hb0] at hf hsd
  rw [hvs'] at hcf
  have e3 := evalF_call_ok (q := lookupP .side) (args := [.var "v", .var "b0"]) (ds := ["f",
    "sd"]) (L := L2)
    (by
      simp [evList, Exp.ev, L2, L1, Machine.State.upd, hv]) ef
  set L3 := Machine.State.setLocs L2 ["f", "sd"] ((lookupP .side).rets.map Lf)
  have hL3 : ∀ r, r ≠ "f" → r ≠ "sd" → L3 r = L2 r := fun r h1 h2 => by
    simp [L3, lookupP, Machine.State.setLocs, Machine.State.upd,
      h1, h2]
  have h3f : L3 "f" = Lf "f" := by simp [L3, lookupP, Machine.State.setLocs, Machine.State.upd]
  have h3sd : L3 "sd" = Lf "v" := by simp [L3, lookupP, Machine.State.setLocs, Machine.State.upd]
  have h3v : L3 "v" = v := by
    rw [hL3 _ (by decide) (by decide)]; simp [L2, L1, Machine.State.upd, hv]
  have h3h : L3 "h" = h := by
    rw [hL3 _ (by decide) (by decide)]; simp [L2, L1, Machine.State.upd, hh]
  have hlen : (encS V.side).length = V.side.length := by simp [encS]
  rw [hlen] at hcf
  by_cases hl : goesLeft s v
  · have hl' : lookup V.side (belowY s v V.first) = some .left := hl
    rw [hl'] at hf hsd
    simp only [Option.map_some, Option.isSome_some, ite_true, Option.getD_some, sideN] at hf hsd
    have e4 : evalF κ (.ite "f" .skip .fail) s L3 = .ok s L3 3 := by
      simp [evalF, Exp.ev, h3f, hf, Exp.cost, Res.addCost]
    have hy : dsY s v = V.first := by simp [dsY, hl, V]
    have ht : dsT s v = V.t1 := by simp [dsT, hl, V]
    have a5 := evalF_assign_ok (κ := κ) (s := s) (L := L3) (x := "t") (e := .rd (.n .t1) "v") (v
      := V.t1)
      (by simp [Exp.ev, h3v, hvN, Fld.cap, Fld.get, NF.get, V])
    set L5 := upd (upd (upd (upd L3 "t" V.t1) "lf" 1) "y" V.first) "bl" b0
    have e5 : evalF κ dsLeftS s L3 = .ok s L5 9 := by
      have a6 := evalF_assign_ok (κ := κ) (s := s) (L := upd L3 "t" V.t1) (x := "lf") (e := (1 :
        Exp)) (v := 1) rfl
      have a7 := evalF_assign_ok (κ := κ) (s := s) (L := upd (upd L3 "t" V.t1) "lf" 1) (x :=
        "y") (e := .var "y0")
        (v := V.first) (by simp [Exp.ev, Machine.State.upd, hL3, L2, L1])
      have a8 := evalF_assign_ok (κ := κ) (s := s) (L := upd (upd (upd L3 "t" V.t1) "lf" 1) "y"
        V.first) (x := "bl")
        (e := .var "b0") (v := b0) (by simp [Exp.ev, Machine.State.upd, hL3, L2])
      exact evalF_seq_ok2 a5 (evalF_seq_ok2 a6 (evalF_seq_ok2 a7 a8))
    have hc6 : ("sd" =ₑ 0 : Exp).ev κ s L3 = some 1 := by
      simp [Exp.ev, Machine.BinOp.eval, h3sd, hsd]
    refine ⟨L5, _, evalF_seq_ok2 a1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 (evalF_seq_ok2 e4
      (evalF_ite_t hc6 one_ne_zero e5)))), by simp [L5, Machine.State.upd, hy],
      by simp [L5, Machine.State.upd,
        ht], by simp [L5, Machine.State.upd, hl, b2n],
      by simp [L5, Machine.State.upd, hy, hb0], ?_, ?_⟩
    · simp only [Exp.cost, costList, List.map, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at hcf ⊢
      split <;> omega
    · intro r h1 h2 h3 h4 h5 h6 h7 h8
      simp only [L5, Machine.State.upd, ite_eq_right h5, ite_eq_right h6,
        ite_eq_right h7, ite_eq_right h8]
      rw [hL3 r h3 h4]; simp [L2, L1, Machine.State.upd, h1, h2]
  · obtain ⟨hr1, hr2⟩ : lookup V.side (belowY s v V.first) = some .right ∧
        lookup V.side (belowY s v V.last) = some .right := hside.resolve_left hl
    rw [hr1] at hf hsd
    simp only [Option.map_some, Option.isSome_some, ite_true, Option.getD_some, sideN] at hf hsd
    have e4 : evalF κ (.ite "f" .skip .fail) s L3 = .ok s L3 3 := by
      simp [evalF, Exp.ev, h3f, hf, Exp.cost, Res.addCost]
    have hy : dsY s v = V.last := by simp [dsY, hl, V]
    have ht : dsT s v = V.t2 := by simp [dsT, hl, V]
    have hc6 : ("sd" =ₑ 0 : Exp).ev κ s L3 = some 0 := by
      simp [Exp.ev, Machine.BinOp.eval, h3sd, hsd]
    -- the right branch
    have a5 := evalF_assign_ok (κ := κ) (s := s) (L := L3) (x := "y") (e := .rd (.n .last) "v")
      (v := V.last)
      (by simp [Exp.ev, h3v, hvN, Fld.cap, Fld.get, NF.get, V])
    set L5 := upd L3 "y" V.last
    have e6 := belowS_ok (κ := κ) (s := s) (L := L5) (c := "y") (r := "bl") (h := h)
      (by
        simp [L5, Machine.State.upd, h3h]) (by simp [L5, Machine.State.upd]) h1 hnl hlC hw
    set b1 := if h == 1 then V.last else (s.path.getX V.last).getX (h - 1)
    have hb1 : b1 = belowY s v V.last := rfl
    set L6 := upd L5 "bl" b1
    obtain ⟨Lg, cg, eg, hg, hgd, -, -, hcg⟩ := lookupP_agree κ .side s
      (Machine.State.setLocs (fun _ => 0) ["i", "x"] [v, b1]) (i := v) (x := b1)
      (by
        simp [Machine.State.setLocs, Machine.State.upd])
      (by
        simp [Machine.State.setLocs, Machine.State.upd]) hvs
    rw [hvs', lookup_encS, hb1, hr2] at hg hgd
    rw [hvs', hlen] at hcg
    simp only [Option.map_some, Option.isSome_some, ite_true, Option.getD_some, sideN] at hg hgd
    have e7 := evalF_call_ok (q := lookupP .side) (args := [.var "v", .var "bl"]) (ds := ["f",
      "sd"]) (L := L6)
      (by
        simp [evList, Exp.ev, L6, L5, Machine.State.upd, h3v]) eg
    set L7 := Machine.State.setLocs L6 ["f", "sd"] ((lookupP .side).rets.map Lg)
    have hL7 : ∀ r, r ≠ "f" → r ≠ "sd" → L7 r = L6 r := fun r h1 h2 => by
      simp [L7, lookupP, Machine.State.setLocs,
        Machine.State.upd, h1, h2]
    have h7f : L7 "f" = 1 := by simp [L7, lookupP, Machine.State.setLocs, Machine.State.upd, hg]
    have h7sd : L7 "sd" = 1 := by simp [L7, lookupP, Machine.State.setLocs, Machine.State.upd, hgd]
    have h7v : L7 "v" = v := by
      rw [hL7 _ (by decide) (by decide)]; simp [L6, L5, Machine.State.upd, h3v]
    have e8 : evalF κ (.ite "f" .skip .fail) s L7 = .ok s L7 3 := by
      simp [evalF, Exp.ev, h7f, Exp.cost, Res.addCost]
    have e9 : evalF κ (.ite ("sd" =ₑ 1) .skip .fail) s L7 = .ok s L7 5 := by
      simp [evalF, Exp.ev, h7sd, Machine.BinOp.eval, Exp.cost, Res.addCost]
    have a10 := evalF_assign_ok (κ := κ) (s := s) (L := L7) (x := "t") (e := .rd (.n .t2) "v")
      (v := V.t2)
      (by simp [Exp.ev, h7v, hvN, Fld.cap, Fld.get, NF.get, V])
    have a11 := evalF_assign_ok (κ := κ) (s := s) (L := upd L7 "t" V.t2) (x := "lf") (e := (0 :
      Exp)) (v := 0) rfl
    set L8 := upd (upd L7 "t" V.t2) "lf" 0
    have eR : ∃ cR, evalF κ dsRightS s L3 = .ok s L8 cR ∧ cR ≤ 120 + 40 * V.side.length := by
      refine ⟨_, evalF_seq_ok2 a5 (evalF_seq_ok2 e6 (evalF_seq_ok2 e7 (evalF_seq_ok2 e8
        (evalF_seq_ok2 e9
        (evalF_seq_ok2 a10 a11))))), ?_⟩
      simp only [Exp.cost, costList, List.map, List.sum_cons, List.sum_nil, List.length_cons,
        List.length_nil] at hcg ⊢
      split <;> omega
    obtain ⟨cR, eR, hcR⟩ := eR
    refine ⟨L8, _, evalF_seq_ok2 a1 (evalF_seq_ok2 e2 (evalF_seq_ok2 e3 (evalF_seq_ok2 e4
      (evalF_ite_f hc6 eR)))), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [L8, Machine.State.upd, hL7, L6, L5, hy]
    · simp [L8, Machine.State.upd, ht]
    · simp [L8, Machine.State.upd, hl, b2n]
    · simp [L8, Machine.State.upd, hL7, L6, hy, hb1]
    · simp only [Exp.cost, costList, List.map, List.sum_cons, List.sum_nil, List.length_cons,
      List.length_nil] at hcf ⊢
      split <;> omega
    · intro r h1 h2 h3 h4 h5 h6 h7 h8
      simp only [L8, Machine.State.upd, ite_eq_right h5, ite_eq_right h6]
      rw [hL7 r h3 h4]; simp only [L6, L5, Machine.State.upd, ite_eq_right h7, ite_eq_right h8]
      rw [hL3 r h3 h4]; simp [L2, L1, Machine.State.upd, h1, h2]

/-- A table lookup that must succeed: `r := lab? of entry e in table t`. -/
def labS (t e r : Reg) : Stm := (lookupP .table).call [.var t, .var e] ["f", r];; .ite "f" .skip
  .fail

theorem labS_ok {κ : Caps} {s : Core} {L : Loc} {t e r : Reg} {tv ev l : Nat} (hr : r ≠ "f") (ht
  : L t = tv)
    (he : L e = ev) (htr : tv < κ.lrec .table) (hl : (s.nodes.getX tv).lab? ev = some l) :
    ∃ c, evalF κ (labS t e r) s L =
      .ok s (Machine.State.setLocs L ["f", r] [1, l]) c ∧ c ≤ 70 + 20 * (s.nodes.getX
        tv).table.length := by
  obtain ⟨Lf, cf, ef, hf, hv, -, -, hcf⟩ := lookupP_agree κ .table s
    (Machine.State.setLocs (fun _ => 0) ["i", "x"] [tv, ev]) (i := tv) (x := ev)
    (by
      simp [Machine.State.setLocs, Machine.State.upd])
    (by
      simp [Machine.State.setLocs, Machine.State.upd]) htr
  have hlk : lookup (LK.view s tv .table) ev = some l := hl
  rw [hlk] at hf hv
  simp only [Option.isSome_some, ite_true, Option.getD_some] at hf hv
  have e1 := evalF_call_ok (q := lookupP .table) (args := [.var t, .var e]) (ds := ["f", r]) (L
    := L)
    (by simp [evList, Exp.ev, ht, he]) ef
  have hL : Machine.State.setLocs L ["f", r] ((lookupP .table).rets.map Lf) =
      Machine.State.setLocs L ["f", r] [1, l] := by simp [lookupP, hf, hv]
  rw [hL] at e1
  have hf1 : Machine.State.setLocs L ["f", r] [1, l] "f" = 1 := by
    simp [Machine.State.setLocs, Machine.State.upd, Ne.symm hr]
  have e2 : evalF κ (.ite "f" .skip .fail) s (Machine.State.setLocs L ["f", r] [1, l]) =
      .ok s (Machine.State.setLocs L ["f", r] [1, l]) 3 := by
    simp only [evalF, Exp.ev, hf1]; simp [Exp.cost, Res.addCost]
  refine ⟨_, evalF_seq_ok2 e1 e2, ?_⟩
  simp only [LK.view, costList, List.map, List.sum_cons, List.sum_nil, Exp.cost, List.length_cons,
    List.length_nil] at hcf ⊢
  omega

/-- The labels around the move and the tag fields they make (locals `v h y t bl`). -/
def dsLabS : Stm := cm{
  if h < P.H then skip else fail
  pr := path(y, h + 1)
  ‹labS "pr" "t" "pt"›; ‹labS "t" "bl" "tb"›; ‹labS "pr" "v" "pv"›; ‹labS "v" "bl" "vb"›
  e1 := 1 <<< (h * P.beta); e0 := 1 <<< ((h - 1) * P.beta)
  old := pv * e1 + vb * e0; new := pt * e1 + tb * e0 }

theorem dsLabS_ok {κ : Caps} {s : Core} {L : Loc} {v h y t bl pt tb pv vb : Nat}
    (hv : L "v" = v) (hh : L "h" = h) (hy : L "y" = y) (ht : L "t" = t) (hbl : L "bl" = bl)
    (hhH : h < s.P.H) (h1 : 1 ≤ h) (hnp : notPrep s y) (hyC : y < κ.tbl .C) (hw : h + 1 < κ.pw)
    (hpt : (s.nodes.getX ((s.path.getX y).getX (h + 1))).lab? t = some pt)
    (htb : (s.nodes.getX t).lab? bl = some tb)
    (hpv : (s.nodes.getX ((s.path.getX y).getX (h + 1))).lab? v = some pv)
    (hvb : (s.nodes.getX v).lab? bl = some vb)
    (htbB : tb < 2 ^ s.P.beta) (hvbB : vb < 2 ^ s.P.beta)
    (hprr : (s.path.getX y).getX (h + 1) < κ.lrec .table) (htr : t < κ.lrec .table) (hvr : v <
      κ.lrec .table) :
    ∃ L' c, evalF κ dsLabS s L = .ok s L' c ∧
      L' "old" = (pv <<< (h * s.P.beta)) ||| (vb <<< ((h - 1) * s.P.beta)) ∧
      L' "new" = (pt <<< (h * s.P.beta)) ||| (tb <<< ((h - 1) * s.P.beta)) ∧
      c ≤ 400 + 40 * (s.nodes.getX ((s.path.getX y).getX (h + 1))).table.length +
        20 * (s.nodes.getX t).table.length + 20 * (s.nodes.getX v).table.length ∧
      ∀ r, r = "v" ∨ r = "y" ∨ r = "t" ∨ r = "lf" ∨ r = "h" → L' r = L r := by
  set pr := (s.path.getX y).getX (h + 1)
  set β := s.P.beta
  have e1 : evalF κ (.ite ("h" <ₑ .prm .H) .skip .fail) s L = .ok s L 6 := by
    simp [evalF, Exp.ev, hh, Machine.BinOp.eval, PF.get, hhH, Exp.cost,
      Res.addCost]
  have a2 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "pr") (e := .prd "y" ("h" + 1)) (v
    := pr)
    (by
      simp [Exp.ev, hy, hh, Machine.BinOp.eval, hyC, hw, rowOf_notPrep hnp, pr])
  set L2 := upd L "pr" pr
  obtain ⟨c3, e3, hc3⟩ := labS_ok (κ := κ) (s := s) (L := L2) (t := "pr") (e := "t") (r := "pt")
    (by decide)
    (by
      simp [L2, Machine.State.upd]) (by
        simp [L2, Machine.State.upd, ht]) hprr hpt
  set L3 := Machine.State.setLocs L2 ["f", "pt"] [1, pt]
  obtain ⟨c4, e4, hc4⟩ := labS_ok (κ := κ) (s := s) (L := L3) (t := "t") (e := "bl") (r := "tb")
    (by decide)
    (by
      simp [L3, L2, Machine.State.setLocs, Machine.State.upd, ht])
    (by
      simp [L3, L2, Machine.State.setLocs, Machine.State.upd, hbl]) htr htb
  set L4 := Machine.State.setLocs L3 ["f", "tb"] [1, tb]
  obtain ⟨c5, e5, hc5⟩ := labS_ok (κ := κ) (s := s) (L := L4) (t := "pr") (e := "v") (r := "pv")
    (by decide)
    (by
      simp [L4, L3, L2, Machine.State.setLocs, Machine.State.upd])
    (by
      simp [L4, L3, L2, Machine.State.setLocs, Machine.State.upd, hv]) hprr hpv
  set L5 := Machine.State.setLocs L4 ["f", "pv"] [1, pv]
  obtain ⟨c6, e6, hc6⟩ := labS_ok (κ := κ) (s := s) (L := L5) (t := "v") (e := "bl") (r := "vb")
    (by decide)
    (by
      simp [L5, L4, L3, L2, Machine.State.setLocs, Machine.State.upd, hv])
    (by
      simp [L5, L4, L3, L2, Machine.State.setLocs, Machine.State.upd, hbl]) hvr hvb
  set L6 := Machine.State.setLocs L5 ["f", "vb"] [1, vb]
  have hL6 : ∀ r, r ≠ "pr" → r ≠ "f" → r ≠ "pt" → r ≠ "tb" → r ≠ "pv" → r ≠ "vb" → L6 r = L r := by
    intro r h1 h2 h3 h4 h5 h6
    simp [L6, L5, L4, L3, L2, Machine.State.setLocs,
      Machine.State.upd, h1, h2, h3, h4, h5, h6]
  have h6 : L6 "pt" = pt ∧ L6 "tb" = tb ∧ L6 "pv" = pv ∧ L6 "vb" = vb ∧ L6 "h" = h := by
    simp [L6, L5, L4, L3, L2, Machine.State.setLocs,
      Machine.State.upd, hh]
  obtain ⟨h6pt, h6tb, h6pv, h6vb, h6h⟩ := h6
  have a7 := evalF_assign_ok (κ := κ) (s := s) (L := L6) (x := "e1") (e := .bin .shl 1 ("h" *
    .prm .beta))
    (v := 2 ^ (h * β)) (by
      simp [Exp.ev, h6h, Machine.BinOp.eval, PF.get, β])
  set L7 := upd L6 "e1" (2 ^ (h * β))
  have a8 := evalF_assign_ok (κ := κ) (s := s) (L := L7) (x := "e0") (e := .bin .shl 1 (("h" -
    1) * .prm .beta))
    (v := 2 ^ ((h - 1) * β)) (by
      simp [Exp.ev, L7, Machine.State.upd, h6h, Machine.BinOp.eval, PF.get, β, h1])
  set L8 := upd L7 "e0" (2 ^ ((h - 1) * β))
  have a9 := evalF_assign_ok (κ := κ) (s := s) (L := L8) (x := "old") (e := "pv" * "e1" + "vb" *
    "e0")
    (v := pv * 2 ^ (h * β) + vb * 2 ^ ((h - 1) * β))
    (by
      simp [Exp.ev, L8, L7, Machine.State.upd, h6pv, h6vb, Machine.BinOp.eval])
  set L9 := upd L8 "old" (pv * 2 ^ (h * β) + vb * 2 ^ ((h - 1) * β))
  have a10 := evalF_assign_ok (κ := κ) (s := s) (L := L9) (x := "new") (e := "pt" * "e1" + "tb"
    * "e0")
    (v := pt * 2 ^ (h * β) + tb * 2 ^ ((h - 1) * β))
    (by
      simp [Exp.ev, L9, L8, L7, Machine.State.upd, h6pt, h6tb, Machine.BinOp.eval])
  refine ⟨_, _, evalF_seq_ok2 e1 (evalF_seq_ok2 a2 (evalF_seq_ok2 e3 (evalF_seq_ok2 e4
    (evalF_seq_ok2 e5
    (evalF_seq_ok2 e6 (evalF_seq_ok2 a7 (evalF_seq_ok2 a8 (evalF_seq_ok2 a9 a10)))))))), ?_, ?_,
      ?_, ?_⟩
  · simp [L9, Machine.State.upd, lor_shift pv vb β h hvbB h1]
  · simp [Machine.State.upd, lor_shift pt tb β h htbB h1]
  · simp only [Exp.cost, Exp.ofNat_def,
    Exp.sub_def] at hc3 hc4 hc5 hc6 ⊢; omega
  · intro r hr
    have : r ≠ "pr" ∧ r ≠ "f" ∧ r ≠ "pt" ∧ r ≠ "tb" ∧ r ≠ "pv" ∧ r ≠ "vb" ∧ r ≠ "e1" ∧ r ≠ "e0"
      ∧ r ≠ "old" ∧
        r ≠ "new" := by rcases hr with rfl | rfl | rfl | rfl | rfl <;> decide
    obtain ⟨a, b, c, d, e, f, g, i, k, m⟩ := this
    simp only [L9, L8, L7, Machine.State.upd, ite_eq_right g, ite_eq_right i,
      ite_eq_right k, ite_eq_right m]
    exact hL6 r a b c d e f

/-- Two writes to the same node. -/
theorem evalF_wrN2 {κ : Caps} {s : Core} {L : Loc} {k1 k2 : NF} {i e1 e2 : Exp} {j w1 w2 : Nat}
    (hi : ∀ S : Core, i.ev κ S L = some j) (he1 : ∀ S : Core, e1.ev κ S L = some w1)
    (he2 : ∀ S : Core, e2.ev κ S L = some w2) (hj : j < s.nodes.size)
    (hk1 : k1.ok w1 = true) (hk2 : k2.ok w2 = true) :
    evalF κ (.wr (.n k1) i e1;; .wr (.n k2) i e2) s L =
      .ok {
        s with
        nodes := s.nodes.modify j fun n => NF.set (NF.set n w1 k1) w2 k2
      } L
        (1 + i.cost + e1.cost + (1 + i.cost + e2.cost)) := by
  have w1' := evalF_wrN_ok (κ := κ) (s := s) (L := L) (k := k1) (i := i) (e := e1) (j := j) (w
    := w1) (hi _) (he1 _)
    hj  hk1
  have w2' := evalF_wrN_ok (κ := κ) (s := {
    s with
    nodes := s.nodes.modify j (NF.set · w1 k1)
  })
    (L := L) (k := k2)
    (i := i) (e := e2) (j := j) (w := w2) (hi _) (he2 _) (by simp [hj])  hk2
  rw [Array.modify_modify_same] at w2'
  exact evalF_seq_ok2 w1' w2'

/-- Check the moved chunk tag against its neighbours and store it. -/
def dsTagS : Stm := cm{
  ty := C[y].tag; if ty < old then fail
  tg := ty - old + new; call gstP(y, tg) }
/-- Remove the moved chunk from the source node's range endpoints. -/
def dsRangeS : Stm := cm{
  if N[v].first = N[v].last then { N[v].first := 0; N[v].last := 0 }
  else if lf then N[v].first := C[y].next
  else N[v].last := C[y].prev }
/-- Extend the selected drain target's range to include the moved chunk. -/
def dsTgtS : Stm := cm{
  if lf then { if N[t].first = 0 then N[t].first := y; N[t].last := y }
  else { if N[t].last = 0 then N[t].last := y; N[t].first := y } }
/-- The writes of a sweep step that moves chunk `y` to target `t` (locals `v h y t lf old new`). -/
def dsMutS : Stm := cm{ dsTagS; path(y, h) := t; dsRangeS; dsTgtS }

/-- Check and update the selected chunk's tag while framing the other locals. -/
private theorem drainTagS_ok {κ : Caps} {s : Core} {L : Loc} {y old new : Nat}
    (hy : L "y" = y) (hold : L "old" = old) (hnew : L "new" = new)
    (hle : old ≤ (s.C.getX y).tag) (hok : OrderMaintenance.Proof.TagOK s y
      ((s.C.getX y).tag - old + new)) (hys : y < s.C.size) (hyC : y < κ.tbl .C)
    (hyP : (s.C.getX y).prev < κ.tbl .C) (hyN : (s.C.getX y).next < κ.tbl .C) :
    let tag := (s.C.getX y).tag - old + new
    let locals := upd (upd L "ty" (s.C.getX y).tag) "tg" tag
    ∃ c, evalF κ dsTagS s L = .ok { s with C := s.C.modify y (fun C => { C with tag := tag }) }
      locals c ∧ c ≤ 60 ∧ ∀ r, r ≠ "ty" → r ≠ "tg" → locals r = L r := by
  let cy := s.C.getX y
  let tag := cy.tag - old + new
  have hTagBound : old ≤ cy.tag := hle
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "ty") (e := .rd (.c .tag) "y") (v
    := cy.tag)
    (by simp [Exp.ev, hy, hyC, Fld.cap, Fld.get, CF.get, cy])
  set L1 := upd L "ty" cy.tag
  have e2 : evalF κ (.ite ("ty" <ₑ "old") .fail .skip) s L1 = .ok s L1 5 := by
    have : ¬ cy.tag < old := by omega
    simp [evalF, Exp.ev, L1, Machine.State.upd, hold,
      Machine.BinOp.eval, this, Exp.cost, Res.addCost]
  have a3 := evalF_assign_ok (κ := κ) (s := s) (L := L1) (x := "tg") (e := "ty" - "old" + "new")
    (v := tag)
    (by
      simp [Exp.ev, L1, Machine.State.upd, hold, hnew, Machine.BinOp.eval, hTagBound, tag])
  set L3 := upd L1 "tg" tag
  have h3 : ∀ r, r ≠ "ty" → r ≠ "tg" → L3 r = L r := fun r h1 h2 => by simp [L3, L1,
    Machine.State.upd, h1, h2]
  obtain ⟨Lg, cg, eg, hcg⟩ := gstP_agree (κ := κ) (s := s)
    (L := Machine.State.setLocs (fun _ => 0) ["c", "t"] [y, tag]) (c := y) (t := tag)
    (by
      simp [Machine.State.setLocs, Machine.State.upd]) (by
        simp [Machine.State.setLocs, Machine.State.upd])
    hys hyC hyP hyN hok
  have e4 := evalF_call_ok (q := gstP) (args := [.var "y", .var "tg"]) (ds := []) (L := L3)
    (by
      simp [evList, Exp.ev, L3, L1, Machine.State.upd, hy]) eg
  set s1 : Core := {
    s with
    C := s.C.modify y fun C => {
      C with
      tag := tag
    }
  }
  have e14 : ∃ c, evalF κ dsTagS s L = .ok s1 L3 c ∧ c ≤ 60 := by
    refine ⟨_, evalF_seq_ok2 a1 (evalF_seq_ok2 e2 (evalF_seq_ok2 a3 e4)), ?_⟩
    simp [Exp.cost, costList]; omega
  obtain ⟨c14, e14, hc14⟩ := e14
  exact ⟨c14, e14, hc14, h3⟩

/-- Update a draining node's endpoints after removing its selected boundary chunk. -/
private theorem drainRangeS_ok {κ : Caps} {S0 : Core} {L : Loc} {v y : Nat}
    {V : Node} {cy : Chunk} {left : Prop} [Decidable left]
    (hv : L "v" = v) (hy : L "y" = y) (hlf : L "lf" = b2n (decide left))
    (hV : S0.nodes.getX v = V) (hnext : (S0.C.getX y).next = cy.next)
    (hprev : (S0.C.getX y).prev = cy.prev) (hvs : v < S0.nodes.size)
    (hvN : v < κ.tbl .N) (hyC : y < κ.tbl .C) :
    ∃ c, evalF κ dsRangeS S0 L = .ok (if V.first == V.last then
      {
        S0 with
        nodes := S0.nodes.modify v fun n => {
          n with
          first := NIL
          last := NIL
        }
      }
    else if left then {
      S0 with
      nodes := S0.nodes.modify v fun n => {
        n with
        first := cy.next
      }
    }
    else {
      S0 with
      nodes := S0.nodes.modify v fun n => {
        n with
        last := cy.prev
      }
    }) L c ∧ c ≤ 20 := by
  let s3 : Core := if V.first == V.last then
      {
        S0 with
        nodes := S0.nodes.modify v fun n => {
          n with
          first := NIL
          last := NIL
        }
      }
    else if left then {
      S0 with
      nodes := S0.nodes.modify v fun n => {
        n with
        first := cy.next
      }
    }
    else {
      S0 with
      nodes := S0.nodes.modify v fun n => {
        n with
        last := cy.prev
      }
    }
  change ∃ c, evalF κ dsRangeS S0 L = .ok s3 L c ∧ c ≤ 20
  by_cases hfl : V.first = V.last
  · have hfl' : V.first = V.last := hfl
    have w := evalF_wrN2 (κ := κ) (s := S0) (L := L) (k1 := .first) (k2 := .last) (i := .var
      "v") (e1 := (0 : Exp))
      (e2 := (0 : Exp)) (ev_var_const hv) (ev_lit_const 0) (ev_lit_const 0) hvs  rfl rfl
    have hs3 : s3 = {
      S0 with
      nodes := S0.nodes.modify v fun n => NF.set (NF.set n 0 .first) 0 .last
    } := by
      simp only [s3, hfl, beq_self_eq_true, ite_true]; rfl
    rw [← hs3] at w
    exact ⟨_, evalF_ite_t (v := 1) (by
      simp [Exp.ev, Machine.BinOp.eval, hv, hvN, Fld.cap, Fld.get, NF.get, hV, hfl'])
        one_ne_zero w, by simp [Exp.cost]⟩
  · have hfl' : ¬ V.first = V.last := hfl
    have hc : (.rd (.n .first) "v" =ₑ .rd (.n .last) "v" : Exp).ev κ S0 L = some 0 := by
      simp [Exp.ev, Machine.BinOp.eval, hv, hvN, Fld.cap, Fld.get, NF.get,
        hV, hfl']
    by_cases hl : left
    · have w := evalF_wrN_ok (κ := κ) (s := S0) (L := L) (k := .first) (i := .var "v") (e :=
        .rd (.c .next) "y")
        (j := v) (w := cy.next) (by simp [Exp.ev, hv]) (by
          simp [Exp.ev, hy, hyC, Fld.cap, Fld.get, CF.get, hnext])
        hvs  rfl
      have hs3 : s3 = {
        S0 with
        nodes := S0.nodes.modify v (NF.set · cy.next .first)
      } := by
        simp only [s3, ite_eq_right (show ¬ (V.first == V.last) = true by simpa using hfl),
          ite_eq_left hl]; rfl
      rw [← hs3] at w
      exact ⟨_, evalF_ite_f hc (evalF_ite_t (v := 1) (by simp [Exp.ev, hlf, hl, b2n])
        one_ne_zero w),
        by simp [Exp.cost]⟩
    · have w := evalF_wrN_ok (κ := κ) (s := S0) (L := L) (k := .last) (i := .var "v") (e :=
        .rd (.c .prev) "y")
        (j := v) (w := cy.prev) (by simp [Exp.ev, hv]) (by
          simp [Exp.ev, hy, hyC, Fld.cap, Fld.get, CF.get,  hprev])
        hvs  rfl
      have hs3 : s3 = {
        S0 with
        nodes := S0.nodes.modify v (NF.set · cy.prev .last)
      } := by
        simp only [s3, ite_eq_right (show ¬ (V.first == V.last) = true by simpa using hfl),
          ite_eq_right hl]; rfl
      rw [← hs3] at w
      exact ⟨_, evalF_ite_f hc (evalF_ite_f (by simp [Exp.ev, hlf, hl, b2n]) w), by simp
        [Exp.cost]⟩


theorem dsMutS_ok {κ : Caps} {s : Core} {L : Loc} {v old new : Nat}
    (hv : L "v" = v) (hh : L "h" = (s.nodes.getX v).height) (hy : L "y" = dsY s v) (ht : L "t" =
      dsT s v)
    (hlf : L "lf" = b2n (decide (goesLeft s v))) (hold : L "old" = old) (hnew : L "new" = new)
    (hle : old ≤ (s.C.getX (dsY s v)).tag) (hok : OrderMaintenance.Proof.TagOK s (dsY s v)
      ((s.C.getX (dsY s v)).tag - old + new))
    (hys : dsY s v < s.C.size) (hyC : dsY s v < κ.tbl .C)
    (hyP : (s.C.getX (dsY s v)).prev < κ.tbl .C) (hyN : (s.C.getX (dsY s v)).next < κ.tbl .C)
    (hnp : notPrep s (dsY s v)) (hw : (s.nodes.getX v).height < κ.pw)
    (hvs : v < s.nodes.size) (hts : dsT s v < s.nodes.size) (hvN : v < κ.tbl .N) (htN : dsT s v
      < κ.tbl .N)
    (htv : dsT s v ≠ v) :
    ∃ L' c, evalF κ dsMutS s L = .ok (dsS s v ((s.C.getX (dsY s v)).tag - old + new)) L' c ∧ c ≤
      150 ∧
      ∀ r, r ≠ "ty" → r ≠ "tg" → L' r = L r := by
  set y := dsY s v
  set t := dsT s v
  set V := s.nodes.getX v
  set cy := s.C.getX y
  set tag := cy.tag - old + new
  set L1 := upd L "ty" cy.tag
  set L3 := upd L1 "tg" tag
  set s1 : Core := { s with C := s.C.modify y (fun C => { C with tag := tag }) }
  obtain ⟨c14, e14, hc14, h3⟩ := drainTagS_ok hy hold hnew hle hok hys hyC hyP hyN
  change ∀ r, r ≠ "ty" → r ≠ "tg" → L3 r = L r at h3
  have h3v : L3 "v" = v := by rw [h3 _ (by decide) (by decide), hv]
  have h3h : L3 "h" = V.height := by rw [h3 _ (by decide) (by decide), hh]
  have h3y : L3 "y" = y := by rw [h3 _ (by decide) (by decide), hy]
  have h3t : L3 "t" = t := by rw [h3 _ (by decide) (by decide), ht]
  have h3lf : L3 "lf" = b2n (decide (goesLeft s v)) := by rw [h3 _ (by decide) (by decide), hlf]
  -- the path
  set s2 : Core := {
    s1 with
    path := s1.path.setX y ((s1.path.getX y).setX V.height t)
  }
  have e5 : evalF κ (.pwr "y" "h" "t") s1 L3 = .ok s2 L3 10 := by
    have : notPrep s1 y := hnp
    simp [evalF, Exp.ev, h3y, h3h, h3t, hyC, hw, this, Exp.cost, s2]
  have hs2v : s2.nodes = s.nodes := rfl
  have hs2y : s2.C.getX y = {
    cy with
    tag := tag
  } := by
    simp only [s2, s1, getX_modify', hys, and_self, ite_true]; rfl
  -- the range of `v`
  set s3 : Core := if V.first == V.last then
      {
        s2 with
        nodes := s2.nodes.modify v fun n => {
          n with
          first := NIL
          last := NIL
        }
      }
    else if goesLeft s v then {
      s2 with
      nodes := s2.nodes.modify v fun n => {
        n with
        first := cy.next
      }
    }
    else {
      s2 with
      nodes := s2.nodes.modify v fun n => {
        n with
        last := cy.prev
      }
    }
  have e6 : ∃ c6, evalF κ dsRangeS s2 L3 = .ok s3 L3 c6 ∧ c6 ≤ 20 := by
    exact drainRangeS_ok (V := V) (cy := cy) (left := goesLeft s v) h3v h3y h3lf
      (by rw [hs2v]) (by rw [hs2y]) (by rw [hs2y]) (by rw [hs2v]; exact hvs) hvN hyC
  obtain ⟨c6, e6, hc6⟩ := e6
  have hs3t : s3.nodes.getX t = s.nodes.getX t := by
    simp only [s3]; split
    · simp only [getX_modify']; rw [ite_eq_right (fun h => htv h.1)]
    · split <;> simp only [getX_modify'] <;> rw [ite_eq_right (fun h => htv h.1)]
  have hs3n : s3.nodes.size = s.nodes.size := by
    simp only [s3]
    split
    · simp [s2, s1]
    · split <;> simp [s2, s1]
  -- the target
  set T := s.nodes.getX t
  have e7 : ∃ c7, evalF κ dsTgtS s3 L3 = .ok (dsS s v tag) L3 c7 ∧ c7 ≤ 30 := by
    by_cases hl : goesLeft s v
    · set s4 : Core := if T.first == NIL then {
      s3 with
      nodes := s3.nodes.modify t fun n => {
        n with
        first := y
      }
    } else s3
      have hfin : dsS s v tag = {
        s4 with
        nodes := s4.nodes.modify t fun n => {
          n with
          last := y
        }
      } := by
        simp only [dsS, s4, s3, ite_eq_left hl]; rfl
      have e8 : ∃ c8, evalF κ (.ite (.rd (.n .first) "t" =ₑ 0) (.wr (.n .first) "t" "y") .skip)
        s3 L3 = .ok s4 L3 c8 ∧
          c8 ≤ 12 := by
        by_cases hT : T.first = 0
        · have hT' : (s.nodes.getX t).first = 0 := hT
          have w := evalF_wrN_ok (κ := κ) (s := s3) (L := L3) (k := .first) (i := .var "t") (e
            := .var "y")
            (j := t) (w := y) (by simp [Exp.ev, h3t]) (by simp [Exp.ev, h3y]) (by
              rw [hs3n]
              exact hts)  rfl
          have hs4 : s4 = {
            s3 with
            nodes := s3.nodes.modify t (NF.set · y .first)
          } := by
            simp only [s4, show (T.first == NIL) = true from beq_iff_eq.mpr hT, ite_true]; rfl
          rw [← hs4] at w
          exact ⟨_, evalF_ite_t (v := 1) (by
            simp [Exp.ev, Machine.BinOp.eval, h3t, htN, Fld.cap, Fld.get, NF.get, hs3t, hT])
              one_ne_zero w, by simp [Exp.cost]⟩
        · have hT' : ¬ (s.nodes.getX t).first = 0 := hT
          have hs4 : s4 = s3 := by
            simp only [s4, show (T.first == NIL) = false from beq_eq_false_iff_ne.mpr hT,
              Bool.false_eq_true, ite_false]
          rw [hs4]
          exact ⟨_, evalF_ite_f (by
            simp [Exp.ev, Machine.BinOp.eval, h3t, htN, Fld.cap, Fld.get, NF.get, hs3t, hT])
              evalF_skip, by simp [Exp.cost]⟩
      obtain ⟨c8, e8, hc8⟩ := e8
      have hs4n : s4.nodes.size = s.nodes.size := by simp only [s4]; split <;> simp [hs3n]
      have w := evalF_wrN_ok (κ := κ) (s := s4) (L := L3) (k := .last) (i := .var "t") (e :=
        .var "y")
        (j := t) (w := y) (by simp [Exp.ev, h3t]) (by simp [Exp.ev, h3y]) (by
          rw [hs4n]
          exact hts)  rfl
      rw [hfin]
      exact ⟨_, evalF_ite_t (v := 1) (by simp [Exp.ev, h3lf, hl, b2n]) one_ne_zero
        (evalF_seq_ok2 e8 w),
        by simp [Exp.cost]; omega⟩
    · set s4 : Core := if T.last == NIL then {
      s3 with
      nodes := s3.nodes.modify t fun n => {
        n with
        last := y
      }
    } else s3
      have hfin : dsS s v tag = {
        s4 with
        nodes := s4.nodes.modify t fun n => {
          n with
          first := y
        }
      } := by
        simp only [dsS, s4, s3, ite_eq_right hl]; rfl
      have e8 : ∃ c8, evalF κ (.ite (.rd (.n .last) "t" =ₑ 0) (.wr (.n .last) "t" "y") .skip) s3
        L3 = .ok s4 L3 c8 ∧
          c8 ≤ 12 := by
        by_cases hT : T.last = 0
        · have hT' : (s.nodes.getX t).last = 0 := hT
          have w := evalF_wrN_ok (κ := κ) (s := s3) (L := L3) (k := .last) (i := .var "t") (e :=
            .var "y")
            (j := t) (w := y) (by simp [Exp.ev, h3t]) (by simp [Exp.ev, h3y]) (by
              rw [hs3n]
              exact hts)  rfl
          have hs4 : s4 = {
            s3 with
            nodes := s3.nodes.modify t (NF.set · y .last)
          } := by
            simp only [s4, show (T.last == NIL) = true from beq_iff_eq.mpr hT, ite_true]; rfl
          rw [← hs4] at w
          exact ⟨_, evalF_ite_t (v := 1) (by
            simp [Exp.ev, Machine.BinOp.eval, h3t, htN, Fld.cap, Fld.get, NF.get, hs3t, hT])
              one_ne_zero w, by simp [Exp.cost]⟩
        · have hT' : ¬ (s.nodes.getX t).last = 0 := hT
          have hs4 : s4 = s3 := by
            simp only [s4, show (T.last == NIL) = false from beq_eq_false_iff_ne.mpr hT,
              Bool.false_eq_true, ite_false]
          rw [hs4]
          exact ⟨_, evalF_ite_f (by
            simp [Exp.ev, Machine.BinOp.eval, h3t, htN, Fld.cap, Fld.get, NF.get, hs3t, hT])
              evalF_skip, by simp [Exp.cost]⟩
      obtain ⟨c8, e8, hc8⟩ := e8
      have hs4n : s4.nodes.size = s.nodes.size := by simp only [s4]; split <;> simp [hs3n]
      have w := evalF_wrN_ok (κ := κ) (s := s4) (L := L3) (k := .first) (i := .var "t") (e :=
        .var "y")
        (j := t) (w := y) (by simp [Exp.ev, h3t]) (by simp [Exp.ev, h3y]) (by
          rw [hs4n]
          exact hts)  rfl
      rw [hfin]
      exact ⟨_, evalF_ite_f (by simp [Exp.ev, h3lf, hl, b2n]) (evalF_seq_ok2 e8 w), by
        simp [Exp.cost]
        omega⟩
  obtain ⟨c7, e7, hc7⟩ := e7
  exact ⟨L3, _, evalF_seq_ok2 e14 (evalF_seq_ok2 e5 (evalF_seq_ok2 e6 e7)), by omega, h3⟩

/-- A sweep step that moves a chunk (locals `v h`). -/
def dsMoveS : Stm := dsPickS;; dsLabS;; dsMutS

theorem dsMoveS_ok {κ : Caps} {s : Core} {L : Loc} {v pt tb pv vb : Nat}
    (hv : L "v" = v) (hh : L "h" = (s.nodes.getX v).height)
    -- Level F (as in `drainStep_move`)
    (hside : goesLeft s v ∨
      lookup (s.nodes.getX v).side (belowY s v (s.nodes.getX v).first) = some .right ∧
      lookup (s.nodes.getX v).side (belowY s v (s.nodes.getX v).last) = some .right)
    (hsz : (s.nodes.getX v).height + 1 < (s.path.getX (dsY s v)).size)
    (hpt : (s.nodes.getX ((s.path.getX (dsY s v)).getX ((s.nodes.getX v).height + 1))).lab? (dsT
      s v) = some pt)
    (htb : (s.nodes.getX (dsT s v)).lab? (belowY s v (dsY s v)) = some tb)
    (hpv : (s.nodes.getX ((s.path.getX (dsY s v)).getX ((s.nodes.getX v).height + 1))).lab? v =
      some pv)
    (hvb : (s.nodes.getX v).lab? (belowY s v (dsY s v)) = some vb)
    (hold : (pv <<< ((s.nodes.getX v).height * s.P.beta)) |||
        (vb <<< (((s.nodes.getX v).height - 1) * s.P.beta)) ≤ (s.C.getX (dsY s v)).tag)
    (hok : OrderMaintenance.Proof.TagOK s (dsY s v) (dsTag s v pt tb pv vb))
    -- the shape
    (h1 : 1 ≤ (s.nodes.getX v).height) (hpsz : (s.path.getX (dsY s v)).size = s.P.H + 1)
    (htbB : tb < 2 ^ s.P.beta) (hvbB : vb < 2 ^ s.P.beta) (htv : dsT s v ≠ v)
    (hvs : v < s.nodes.size) (hts : dsT s v < s.nodes.size) (hys : dsY s v < s.C.size)
    (hnf : notPrep s (s.nodes.getX v).first) (hnl : notPrep s (s.nodes.getX v).last)
    -- capacities
    (hvN : v < κ.tbl .N) (htN : dsT s v < κ.tbl .N) (hvsd : v < κ.lrec .side) (hvr : v < κ.lrec
      .table)
    (htr : dsT s v < κ.lrec .table)
    (hprr : (s.path.getX (dsY s v)).getX ((s.nodes.getX v).height + 1) < κ.lrec .table)
    (hfC : (s.nodes.getX v).first < κ.tbl .C) (hlC : (s.nodes.getX v).last < κ.tbl .C)
    (hyP : (s.C.getX (dsY s v)).prev < κ.tbl .C) (hyN : (s.C.getX (dsY s v)).next < κ.tbl .C)
    (hw : (s.nodes.getX v).height + 1 < κ.pw) :
    ∃ L' c, evalF κ dsMoveS s L = .ok (dsS s v (dsTag s v pt tb pv vb)) L' c ∧
      c ≤ 1000 + 80 * (s.nodes.getX v).side.length +
        40 * (s.nodes.getX ((s.path.getX (dsY s v)).getX ((s.nodes.getX v).height +
          1))).table.length +
        20 * (s.nodes.getX (dsT s v)).table.length + 20 * (s.nodes.getX v).table.length ∧
      L' "v" = v ∧ L' "h" = (s.nodes.getX v).height := by
  set h := (s.nodes.getX v).height
  have hyE : dsY s v = (s.nodes.getX v).first ∨ dsY s v = (s.nodes.getX v).last := by
    unfold dsY; split <;> simp
  have hnp : notPrep s (dsY s v) := by rcases hyE with e | e <;> rw [e] <;> assumption
  have hyC : dsY s v < κ.tbl .C := by rcases hyE with e | e <;> rw [e] <;> assumption
  obtain ⟨L1, c1, e1, h1y, h1t, h1lf, h1bl, hc1, hF1⟩ := dsPickS_ok (κ := κ) (s := s) (L := L)
    hv hh h1 hside hvN hvsd
    hnf hnl hfC hlC (by omega)
  have hF1' : ∀ r, r = "v" ∨ r = "h" → L1 r = L r := by
    intro r hr; apply hF1 <;> rcases hr with rfl | rfl <;> decide
  obtain ⟨L2, c2, e2, h2o, h2n, hc2, hF2⟩ := dsLabS_ok (κ := κ) (s := s) (L := L1) (v := v) (h := h)
    (y := dsY s v) (t := dsT s v) (bl := belowY s v (dsY s v)) (pt := pt) (tb := tb) (pv := pv)
      (vb := vb)
    (by rw [hF1' "v" (by simp),
      hv]) (by rw [hF1' "h" (by simp), hh]) h1y h1t h1bl (by omega) h1 hnp hyC hw
    hpt htb hpv hvb htbB hvbB hprr htr hvr
  obtain ⟨L3, c3, e3, hc3, hF3⟩ := dsMutS_ok (κ := κ) (s := s) (L := L2) (v := v)
    (old := (pv <<< (h * s.P.beta)) ||| (vb <<< ((h - 1) * s.P.beta)))
    (new := (pt <<< (h * s.P.beta)) ||| (tb <<< ((h - 1) * s.P.beta)))
    (by rw [hF2 "v" (by simp), hF1' "v" (by simp),
      hv]) (by rw [hF2 "h" (by simp), hF1' "h" (by simp), hh])
    (by rw [hF2 "y" (by simp),
      h1y]) (by rw [hF2 "t" (by simp), h1t]) (by rw [hF2 "lf" (by simp), h1lf]) h2o h2n
    hold hok hys hyC hyP hyN hnp (by omega) hvs hts hvN htN htv
  refine ⟨L3, _, evalF_seq_ok2 e1 (evalF_seq_ok2 e2 e3), by omega, ?_, ?_⟩
  · rw [hF3 "v" (by decide) (by decide), hF2 "v" (by simp), hF1' "v" (by simp), hv]
  · rw [hF3 "h" (by decide) (by decide), hF2 "h" (by simp), hF1' "h" (by simp), hh]

/-! ### `drainStep` -/

/-- `ok := drainStep v`. -/
def dsP : Proc where
  name := "drainStep"
  params := ["v"]
  rets := ["ok"]
  body := cm{
    if N[v].dead then ok := 0
    else {
      h := N[v].height
      if N[v].first = 0 then { finishDrainS; ok := 0 } else { dsMoveS; ok := 1 } } }

theorem dsP_dead {κ : Caps} {s : Core} {L : Loc} {v : Nat} (hv : L "v" = v) (hvN : v < κ.tbl .N)
    (hal : (s.nodes.getX v).alive = false) :
    ∃ L' c, evalF κ dsP.body s L = .ok s L' c ∧ L' "ok" = 0 ∧ c ≤ 10 := by
  refine ⟨_, _, evalF_ite_t (v := 1) (by
    simp [Exp.ev, hv, hvN, Fld.cap, Fld.get, NF.get, hal, b2n]) one_ne_zero
    (evalF_assign_ok (v := 0) rfl), by simp [Machine.State.upd], by simp [Exp.cost]⟩

theorem dsP_pre {κ : Caps} {s : Core} {L : Loc} {v : Nat} (hv : L "v" = v) (hvN : v < κ.tbl .N)
    (hal : (s.nodes.getX v).alive = true) {s' : Core} {L' : Loc} {c : Nat}
    (h : evalF κ (.ite (.rd (.n .first) "v" =ₑ 0) (finishDrainS;; "ok" ::= 0) (dsMoveS;; "ok"
      ::= 1)) s
      (upd L "h" (s.nodes.getX v).height) = .ok s' L' c) :
    evalF κ dsP.body s L = .ok s' L' (c + 6) := by
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := L) (x := "h") (e := .rd (.n .height) "v")
    (v := (s.nodes.getX v).height) (by simp [Exp.ev, hv, hvN, Fld.cap, Fld.get, NF.get])
  have := evalF_ite_f (t := ("ok" ::= 0)) (by
    simp [Exp.ev, hv, hvN, Fld.cap, Fld.get, NF.get, hal, b2n] : (Exp.rd (.n .dead) "v").ev κ s
      L = some 0) (evalF_seq_ok2 a1 h)
  convert this using 2
  · rfl
  · simp only [Exp.cost]; omega

theorem dsP_move {κ : Caps} {s : Core} {L : Loc} {v pt tb pv vb : Nat} (hv : L "v" = v)
    (hal : (s.nodes.getX v).alive = true) (hf : (s.nodes.getX v).first ≠ NIL)
    (hside : goesLeft s v ∨
      lookup (s.nodes.getX v).side (belowY s v (s.nodes.getX v).first) = some .right ∧
      lookup (s.nodes.getX v).side (belowY s v (s.nodes.getX v).last) = some .right)
    (hsz : (s.nodes.getX v).height + 1 < (s.path.getX (dsY s v)).size)
    (hpt : (s.nodes.getX ((s.path.getX (dsY s v)).getX ((s.nodes.getX v).height + 1))).lab? (dsT
      s v) = some pt)
    (htb : (s.nodes.getX (dsT s v)).lab? (belowY s v (dsY s v)) = some tb)
    (hpv : (s.nodes.getX ((s.path.getX (dsY s v)).getX ((s.nodes.getX v).height + 1))).lab? v =
      some pv)
    (hvb : (s.nodes.getX v).lab? (belowY s v (dsY s v)) = some vb)
    (hold : (pv <<< ((s.nodes.getX v).height * s.P.beta)) |||
        (vb <<< (((s.nodes.getX v).height - 1) * s.P.beta)) ≤ (s.C.getX (dsY s v)).tag)
    (hok : OrderMaintenance.Proof.TagOK s (dsY s v) (dsTag s v pt tb pv vb))
    (h1 : 1 ≤ (s.nodes.getX v).height) (hpsz : (s.path.getX (dsY s v)).size = s.P.H + 1)
    (htbB : tb < 2 ^ s.P.beta) (hvbB : vb < 2 ^ s.P.beta) (htv : dsT s v ≠ v)
    (hvs : v < s.nodes.size) (hts : dsT s v < s.nodes.size) (hys : dsY s v < s.C.size)
    (hnf : notPrep s (s.nodes.getX v).first) (hnl : notPrep s (s.nodes.getX v).last)
    (hvN : v < κ.tbl .N) (htN : dsT s v < κ.tbl .N) (hvsd : v < κ.lrec .side) (hvr : v < κ.lrec
      .table)
    (htr : dsT s v < κ.lrec .table)
    (hprr : (s.path.getX (dsY s v)).getX ((s.nodes.getX v).height + 1) < κ.lrec .table)
    (hfC : (s.nodes.getX v).first < κ.tbl .C) (hlC : (s.nodes.getX v).last < κ.tbl .C)
    (hyP : (s.C.getX (dsY s v)).prev < κ.tbl .C) (hyN : (s.C.getX (dsY s v)).next < κ.tbl .C)
    (hw : (s.nodes.getX v).height + 1 < κ.pw) :
    ∃ L' c, evalF κ dsP.body s L = .ok (dsS s v (dsTag s v pt tb pv vb)) L' c ∧ L' "ok" = 1 ∧
      c ≤ 1100 + 80 * (s.nodes.getX v).side.length +
        40 * (s.nodes.getX ((s.path.getX (dsY s v)).getX ((s.nodes.getX v).height +
          1))).table.length +
        20 * (s.nodes.getX (dsT s v)).table.length + 20 * (s.nodes.getX v).table.length := by
  obtain ⟨L1, c1, e1, hc1, -, -⟩ := dsMoveS_ok (κ := κ) (s := s) (L := upd L "h" (s.nodes.getX
    v).height)
    (v := v) (by simp [Machine.State.upd, hv]) (by simp [Machine.State.upd]) hside hsz hpt htb
      hpv hvb hold hok
    h1 hpsz htbB hvbB htv hvs hts hys hnf hnl hvN htN hvsd hvr htr hprr hfC hlC hyP hyN hw
  have e2 := evalF_seq_ok2 e1 (evalF_assign_ok (κ := κ) (s := dsS s v (dsTag s v pt tb pv vb))
    (L := L1) (x := "ok")
    (e := (1 : Exp)) (v := 1) rfl)
  have hc : (Exp.rd (.n .first) "v" =ₑ 0 : Exp).ev κ s (upd L "h" (s.nodes.getX v).height) =
    some 0 := by
    have : ¬ (s.nodes.getX v).first = 0 := hf
    simp [Exp.ev, Machine.State.upd, hv, hvN, Fld.cap, Fld.get, NF.get,
      Machine.BinOp.eval, this]
  have e3 := evalF_ite_f (t := finishDrainS;; "ok" ::= 0) hc e2
  exact ⟨_, _, dsP_pre hv hvN hal e3, by simp [Machine.State.upd], by
    simp [Exp.cost] at hc1 ⊢
    omega⟩

theorem dsP_finish {κ : Caps} {s : Core} {L : Loc} {v B : Nat} (hv : L "v" = v)
    (hal : (s.nodes.getX v).alive = true) (hf : (s.nodes.getX v).first = NIL)
    (hnd : (s.nodes.getX v).inTables.Nodup) (hT : ∀ T ∈ (s.nodes.getX v).inTables, v ∈
      (s.nodes.getX T).order)
    (hv0 : v ≠ 0) (hvs : v < s.nodes.size) (hvo : (s.nodes.getX v).height - 1 ≠ 0 → v ∉
      (s.nodes.getX v).order)
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
    ∃ L' c, evalF κ dsP.body s L = .ok (fdS v s) L' c ∧ L' "ok" = 0 ∧
      c ≤ 300 + (s.nodes.getX v).table.length * (171 + 100 * B) +
        (s.nodes.getX v).inTables.length * (301 + 200 * B) := by
  obtain ⟨L1, c1, e1, hc1, -⟩ := finishDrainS_ok (κ := κ) (s := s) (L := upd L "h" (s.nodes.getX
    v).height)
    (v := v) (B := B) (by simp [Machine.State.upd, hv]) (by simp [Machine.State.upd]) hnd hT hv0
      hvs hvo hvN hvr
    hvi ht1 ht2 hcE hcT
  have e2 := evalF_seq_ok2 e1 (evalF_assign_ok (κ := κ) (s := fdS v s) (L := L1) (x := "ok") (e
    := (0 : Exp)) (v := 0) rfl)
  have hc : (Exp.rd (.n .first) "v" =ₑ 0 : Exp).ev κ s (upd L "h" (s.nodes.getX v).height) =
    some 1 := by
    have : (s.nodes.getX v).first = 0 := hf
    simp [Exp.ev, Machine.State.upd, hv, hvN, Fld.cap, Fld.get, NF.get,
      Machine.BinOp.eval, this]
  have e3 := evalF_ite_t (f := dsMoveS;; "ok" ::= 1) hc one_ne_zero e2
  exact ⟨_, _, dsP_pre hv hvN hal e3, by simp [Machine.State.upd], by
    simp [Exp.cost] at hc1 ⊢
    omega⟩

/-! ### The funding loop, the step after a drain start, the walk -/

/-- The program agrees with Level F's `drainStep src` from `S` (within `D` steps). -/
def DSAgree (κ : Caps) (S : Core) (src D : Nat) : Prop :=
  ∀ b S', (drainStep src).run S = .ok b S' →
    ∃ L' c, evalF κ dsP.body S (Machine.State.setLocs (fun _ => 0) ["v"] [src]) = .ok S' L' c ∧
      L' "ok" = b2n b ∧ c ≤ D ∧ S'.resJob = S.resJob

/-- `fundLoop` (locals `ja jb jc jd` = `v up src k`); the job's counter is updated. -/
def fundS : Stm := cm{
  if jd < P.s then {
    dk ← dsP(jc)
    if dk then pcSet(4, ja, jb, jc, jd + 1) else pcSet(2, jb, 0, 0, 0) }
  else pcSet(2, jb, 0, 0, 0) }

theorem fundS_agree {κ : Caps} {S : Core} {L : Loc} {j : Job} {v up src k D : Nat} (hjob :
  S.resJob = some j)
    (ha : L "ja" = v) (hb : L "jb" = up) (hc : L "jc" = src) (hd : L "jd" = k) (hds : DSAgree κ
      S src D)
    {r : Option Job} {S' : Core} (h : (fundLoop j v up src k).run S = .ok r S') :
    ∃ L' c, evalF κ fundS S L = .ok {
      S' with
      resJob := r
    } L' c ∧ c ≤ D + 80 := by
  unfold fundLoop at h
  simp only [OrderMaintenance.Proof.run_getP_bind] at h
  by_cases hk : k < S.P.s
  · rw [ite_eq_left hk] at h
    obtain ⟨b, S1, h1, h2⟩ := run_bind_ok h
    obtain ⟨Ld, cd, ed, hdk, hcd, hj1⟩ := hds b S1 h1
    have e1 := evalF_call_ok (q := dsP) (args := [.var "jc"]) (ds := ["dk"]) (L := L) (by
      simp [evList, Exp.ev, hc]) ed
    set L1 := Machine.State.setLocs L ["dk"] (dsP.rets.map Ld)
    have hL1 : ∀ q, q ≠ "dk" → L1 q = L q := fun q hq => by
      simp [L1, dsP, Machine.State.setLocs, Machine.State.upd, hq]
    have h1dk : L1 "dk" = b2n b := by simp [L1, dsP, Machine.State.setLocs, Machine.State.upd, hdk]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, EStateM.run_pure, EStateM.Result.ok.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      have e2' : evalF κ (.pcSet 2 "jb" 0 0 0) S1 L1 = .ok {
        S1 with
        resJob := some {
          j with
          pc := .walk (some up)
        }
      } L1 21 := by
        simp [evalF, evList, Exp.ev, hj1, hjob, hL1 "jb" (by decide), hb, pcDec, costList, Exp.cost]
      have e2 := evalF_ite_f (c := .var "dk") (t := .pcSet 4 "ja" "jb" "jc" ("jd" + 1)) (by
        simp [Exp.ev, h1dk, b2n]) e2'
      refine ⟨_, _, evalF_ite_t (v := 1) (by
        simp [Exp.ev, hd, Machine.BinOp.eval, PF.get, hk]) one_ne_zero
        (evalF_seq_ok2 e1 e2), ?_⟩
      simp [Exp.cost, costList]; omega
    · simp only [↓reduceIte, EStateM.run_pure, EStateM.Result.ok.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      have e2' : evalF κ (.pcSet 4 "ja" "jb" "jc" ("jd" + 1)) S1 L1 =
          .ok {
            S1 with
            resJob := some {
              j with
              pc := .fund v up src (k + 1)
            }
          } L1 23 := by
        simp [evalF, evList, Exp.ev, hj1, hjob, hL1 "ja" (by decide), hL1 "jb" (by decide),
          hL1 "jc" (by decide),
          hL1 "jd" (by decide), ha, hb, hc, hd, pcDec, Machine.BinOp.eval, costList, Exp.cost]
      have e2 := evalF_ite_t (c := .var "dk") (f := .pcSet 2 "jb" 0 0 0) (v := 1) (by
        simp [Exp.ev, h1dk, b2n]) one_ne_zero e2'
      refine ⟨_, _, evalF_ite_t (v := 1) (by
        simp [Exp.ev, hd, Machine.BinOp.eval, PF.get, hk]) one_ne_zero
        (evalF_seq_ok2 e1 e2), ?_⟩
      simp [Exp.cost, costList]; omega
  · rw [ite_eq_right hk] at h
    simp only [EStateM.run_pure, EStateM.Result.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have e' : evalF κ (.pcSet 2 "jb" 0 0 0) S L = .ok {
      S with
      resJob := some {
        j with
        pc := .walk (some up)
      }
    } L 21 := by
      simp [evalF, evList, Exp.ev, hjob, hb, pcDec, costList, Exp.cost]
    refine ⟨_, _, evalF_ite_f (by
      simp [Exp.ev, hd, Machine.BinOp.eval, PF.get, hk]) e', ?_⟩
    simp [Exp.cost]

/-- `afterDrain` (locals `av au` = `v up`). -/
def afSetS : Stm := cm{ ja := av; jb := au; jc := src; jd := 0 }
/-- Resume a reservation at the parent or at the source of an overflow target. -/
def afterDS : Stm := cm{
  src := N[av].overflow;
   if src = 0 then pcSet(2, au, 0, 0, 0) else { afSetS; fundS } }

theorem afterDS_agree {κ : Caps} {S : Core} {L : Loc} {j : Job} {v up D : Nat} (hjob : S.resJob
  = some j)
    (hv : L "av" = v) (hu : L "au" = up) (hvN : v < κ.tbl .N)
    (hds : (S.nodes.getX v).overflowOf ≠ NIL → DSAgree κ S (S.nodes.getX v).overflowOf D)
    {r : Option Job} {S' : Core} (h : (afterDrain j v up).run S = .ok r S') :
    ∃ L' c, evalF κ afterDS S L = .ok {
      S' with
      resJob := r
    } L' c ∧ c ≤ D + 120 := by
  unfold afterDrain at h
  simp only [run_getN_bind] at h
  set src := (S.nodes.getX v).overflowOf
  have a1 := evalF_assign_ok (κ := κ) (s := S) (L := L) (x := "src") (e := .rd (.n .overflow)
    "av") (v := src)
    (by simp [Exp.ev, hv, hvN, Fld.cap, Fld.get, NF.get, src])
  set L1 := upd L "src" src
  by_cases h0 : src = 0
  · rw [ite_eq_right (by simp [h0, NIL])] at h
    simp only [EStateM.run_pure, EStateM.Result.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have e' : evalF κ (.pcSet 2 "au" 0 0 0) S L1 = .ok {
      S with
      resJob := some {
        j with
        pc := .walk (some up)
      }
    } L1 21 := by
      simp [evalF, evList, Exp.ev, hjob, L1, Machine.State.upd, hu, pcDec,
        costList, Exp.cost]
    refine ⟨_, _, evalF_seq_ok2 a1 (evalF_ite_t (v := 1) (by
      simp [Exp.ev, L1, Machine.State.upd, h0, Machine.BinOp.eval]) one_ne_zero e'), by simp
        [Exp.cost]⟩
  · rw [ite_eq_left (by simpa [NIL] using h0)] at h
    set L2 := upd (upd (upd (upd L1 "ja" v) "jb" up) "jc" src) "jd" 0
    have e2 : evalF κ afSetS S L1 = .ok S L2 8 := by
      have b1 := evalF_assign_ok (κ := κ) (s := S) (L := L1) (x := "ja") (e := .var "av") (v := v)
        (by simp [Exp.ev, L1, Machine.State.upd, hv])
      have b2 := evalF_assign_ok (κ := κ) (s := S) (L := upd L1 "ja" v) (x := "jb") (e := .var
        "au") (v := up)
        (by simp [Exp.ev, L1, Machine.State.upd, hu])
      have b3 := evalF_assign_ok (κ := κ) (s := S) (L := upd (upd L1 "ja" v) "jb" up) (x :=
        "jc") (e := .var "src")
        (v := src) (by simp [Exp.ev, L1, Machine.State.upd])
      have b4 := evalF_assign_ok (κ := κ) (s := S) (L := upd (upd (upd L1 "ja" v) "jb" up) "jc"
        src) (x := "jd")
        (e := (0 : Exp)) (v := 0) rfl
      exact evalF_seq_ok2 b1 (evalF_seq_ok2 b2 (evalF_seq_ok2 b3 b4))
    obtain ⟨L3, c3, e3, hc3⟩ := fundS_agree (κ := κ) (S := S) (L := L2) (j := j) (v := v) (up :=
      up) (src := src) (k := 0)
      (D := D) hjob (by simp [L2, Machine.State.upd]) (by simp [L2, Machine.State.upd])
      (by
        simp [L2, Machine.State.upd]) (by
          simp [L2, Machine.State.upd]) (hds (by simpa [NIL] using h0)) h
    have hc : ("src" =ₑ 0 : Exp).ev κ S L1 = some 0 := by
      simp [Exp.ev, L1, Machine.State.upd, h0, Machine.BinOp.eval]
    have e4 := evalF_ite_f (t := .pcSet 2 "au" 0 0 0) hc (evalF_seq_ok2 e2 e3)
    exact ⟨_, _, evalF_seq_ok2 a1 e4, by simp [Exp.cost]; omega⟩

/-- `startDrain v`. -/
def sdP : Proc where
  name := "startDrain"
  params := ["v"]
  rets := []
  body := startDrainS

/-- The program agrees with Level F's `startDrain v` from `S` (within `D` steps). -/
def SDAgree (κ : Caps) (S : Core) (v D : Nat) : Prop :=
  ∀ S', (startDrain v).run S = .ok () S' →
    ∃ L' c, evalF κ sdP.body S (Machine.State.setLocs (fun _ => 0) ["v"] [v]) = .ok S' L' c ∧ c
      ≤ D ∧
      S'.resJob = S.resJob

/-- `pw := a ^ ht`, in one step: `a` is a power of two, so `a ^ ht = 1 <<< (log₂ a · ht)`. -/
def powS : Stm := cm{ pw := 1 <<< (msb(P.a) * ht) }

theorem powS_ok {κ : Caps} {S : Core} {L : Loc} {h : Nat} (hh : L "ht" = h) (ha : S.P.a = 2 ^
  Nat.log2 S.P.a) :
    ∃ L' c, evalF κ powS S L = .ok S L' c ∧ L' "pw" = S.P.a ^ h ∧ c ≤ 10 ∧
      ∀ r, r ≠ "pw" → r ≠ "i" → L' r = L r := by
  refine ⟨_, _, evalF_assign_ok (v := S.P.a ^ h) ?_, by simp [Machine.State.upd], by simp
    [Exp.cost],
    fun r h1 _ => by simp [Machine.State.upd, h1]⟩
  simp only [Exp.ofNat_def, Exp.mul_def]
  conv_rhs => rw [ha]
  rw [← pow_mul]
  simp [Exp.ev, Machine.BinOp.eval, Machine.UnOp.eval, PF.get, hh]

/-- Detect a nondraining, nonoverflow node above its weight threshold with a live parent. -/
def walkC : Exp := cme{ up ≠ 0 && !dr && ov = 0 && 2 * pw < wt + 2 }
/-- Read the current reservation-walk node and its continuation. -/
def walkRd : Stm := cm{
  up := N[wv].livePar; wt := N[wv].weight; ht := N[wv].height
  dr := N[wv].draining; ov := N[wv].overflow }
/-- `walkBody` at node `wv`. -/
def walkS : Stm := cm{
  if wv = 0 then jobClear
  else {
    walkRd; N[wv].weight := wt + 2; powS
    if ‹walkC› then { call sdP(wv); pcSet(3, wv, up, 0, 0) }
    else { av := wv; au := up; afterDS } } }

theorem walkS_agree {κ : Caps} {S : Core} {L : Loc} {j : Job} {v D1 D2 : Nat} (hjob : S.resJob =
  some j)
    (hv : L "wv" = v) (hvs : v ≠ 0 → v < S.nodes.size) (hvN : v ≠ 0 → v < κ.tbl .N)
    (hsd : v ≠ NIL → ((S.nodes.getX v).livePar != NIL && !(S.nodes.getX v).draining &&
      (S.nodes.getX v).overflowOf == NIL &&
      decide ((S.nodes.getX v).weight + 2 > 2 * S.P.a ^ (S.nodes.getX v).height)) = true →
        SDAgree κ (wiC S v) v D1)
    (hds : v ≠ NIL → (S.nodes.getX v).overflowOf ≠ NIL → DSAgree κ (wiC S v) (S.nodes.getX
      v).overflowOf D2)
    (ha : S.P.a = 2 ^ Nat.log2 S.P.a)
    {r : Option Job} {S' : Core} (h : (walkBody j v).run S = .ok r S') :
    ∃ L' c, evalF κ walkS S L = .ok {
      S' with
      resJob := r
    } L' c ∧ c ≤ D1 + D2 + 250 := by
  unfold walkBody at h
  by_cases h0 : v = 0
  · rw [ite_eq_left (by simp [h0, NIL])] at h
    simp only [EStateM.run_pure, EStateM.Result.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨_, _, evalF_ite_t (v := 1) (by simp [Exp.ev, hv, h0, Machine.BinOp.eval]) one_ne_zero
      (show evalF κ .jobClear S L = .ok {
        S with
        resJob := none
      } L 27 from rfl), by
        simp only [Exp.cost]
        omega⟩
  · rw [ite_eq_right (by simpa [NIL] using h0)] at h
    simp only [OrderMaintenance.Proof.run_getP_bind, run_getN_bind, run_modN_bind] at h
    have hvs' := hvs h0
    have hvN' := hvN h0
    set V := S.nodes.getX v
    -- the reads
    set L5 := upd (upd (upd (upd (upd L "up" V.livePar) "wt" V.weight) "ht" V.height) "dr" (b2n
      V.draining)) "ov"
      V.overflowOf
    have e1 : evalF κ walkRd S L = .ok S L5 15 := by
      have b1 := evalF_assign_ok (κ := κ) (s := S) (L := L) (x := "up") (e := .rd (.n .livePar)
        "wv") (v := V.livePar)
        (by simp [Exp.ev, hv, hvN', Fld.cap, Fld.get, NF.get, V])
      have b2 := evalF_assign_ok (κ := κ) (s := S) (L := upd L "up" V.livePar) (x := "wt") (e :=
        .rd (.n .weight) "wv")
        (v := V.weight) (by
          simp [Exp.ev, Machine.State.upd, hv, hvN', Fld.cap, Fld.get, NF.get, V])
      have b3 := evalF_assign_ok (κ := κ) (s := S) (L := upd (upd L "up" V.livePar) "wt"
        V.weight) (x := "ht")
        (e := .rd (.n .height) "wv") (v := V.height)
        (by
          simp [Exp.ev, Machine.State.upd, hv, hvN', Fld.cap, Fld.get, NF.get, V])
      have b4 := evalF_assign_ok (κ := κ) (s := S) (L := upd (upd (upd L "up" V.livePar) "wt"
        V.weight) "ht" V.height)
        (x := "dr") (e := .rd (.n .draining) "wv") (v := b2n V.draining)
        (by
          simp [Exp.ev, Machine.State.upd, hv, hvN', Fld.cap, Fld.get, NF.get, V])
      have b5 := evalF_assign_ok (κ := κ) (s := S)
        (L := upd (upd (upd (upd L "up" V.livePar) "wt" V.weight) "ht" V.height) "dr" (b2n
          V.draining))
        (x := "ov") (e := .rd (.n .overflow) "wv") (v := V.overflowOf)
        (by
          simp [Exp.ev, Machine.State.upd, hv, hvN', Fld.cap, Fld.get, NF.get, V])
      exact evalF_seq_ok2 b1 (evalF_seq_ok2 b2 (evalF_seq_ok2 b3 (evalF_seq_ok2 b4 b5)))
    have h5 : ∀ r, r ≠ "up" → r ≠ "wt" → r ≠ "ht" → r ≠ "dr" → r ≠ "ov" → L5 r = L r := fun r a
      b c d e => by
      simp [L5, Machine.State.upd, a, b, c, d, e]
    have h5v : L5 "wv" = v := by
      rw [h5 _ (by decide) (by decide) (by decide) (by decide) (by decide), hv]
    -- the weight
    have e2 := evalF_wrN_ok (κ := κ) (s := S) (L := L5) (k := .weight) (i := .var "wv") (e :=
      "wt" + 2) (j := v)
      (w := V.weight + 2) (by simp [Exp.ev, h5v]) (by
        simp [Exp.ev, L5, Machine.State.upd, Machine.BinOp.eval])
      hvs'  rfl
    have hW : ({
      S with
      nodes := S.nodes.modify v (NF.set · (V.weight + 2) .weight)
    } : Core) =
      wiC S v := by
      simp only [wiC]; congr 1; apply Array.modify_congr_getX; rfl
    rw [hW] at e2
    obtain ⟨L6, c6, e6, h6pw, hc6, hF6⟩ := powS_ok (κ := κ) (S := wiC S v) (L := L5) (h := V.height)
      (by simp [L5, Machine.State.upd]) ha
    have h6 : ∀ r, r ≠ "pw" → r ≠ "i" → L6 r = L5 r := hF6
    have hjob' : (wiC S v).resJob = some j := hjob
    by_cases hc : V.livePar != NIL && !V.draining && V.overflowOf == NIL && decide (V.weight + 2
      > 2 * S.P.a ^ V.height)
    · rw [ite_eq_left hc] at h
      obtain ⟨u, S1, h1, h2⟩ := run_bind_ok h
      simp only [EStateM.run_pure, EStateM.Result.ok.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      obtain ⟨Ls, cs, es, hcs, hjs⟩ := hsd (by simpa [NIL] using h0) hc S1 h1
      have e7 := evalF_call_ok (q := sdP) (args := [.var "wv"]) (ds := []) (L := L6)
        (by simp [evList, Exp.ev, h6 "wv" (by decide) (by decide), h5v]) es
      have e8 : evalF κ (.pcSet 3 "wv" "up" 0 0) S1 (Machine.State.setLocs L6 [] (sdP.rets.map
        Ls)) =
          .ok {
            S1 with
            resJob := some {
              j with
              pc := .afterDrain v V.livePar
            }
          } L6 21 := by
        simp [evalF, evList, Exp.ev, hjs, hjob', Machine.State.setLocs,
          h6 "wv" (by decide) (by decide), h5v,
          h6 "up" (by decide) (by decide), L5, Machine.State.upd, pcDec, costList, Exp.cost]
      have hcv : walkC.ev κ (wiC S v) L6 = some 1 := by
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
          beq_iff_eq,
          decide_eq_true_eq] at hc
        obtain ⟨⟨⟨hc1, hc2⟩, hc3⟩, hc4⟩ := hc
        simp only [NIL, walkC, Exp.ofNat_def, Exp.mul_def, Exp.add_def, Exp.ev,
            h6 "up" (by decide) (by decide), b2n, hc2, Bool.false_eq_true, ↓reduceIte,
            hc3, Machine.State.upd, String.reduceEq, BinOp.eval, Option.bind_some,
            Option.map_some, UnOp.eval, ite_eq_right_iff, one_ne_zero, imp_false,
            ite_not, h6 "dr" (by decide) (by decide), h6 "ov" (by decide) (by decide),
            h6pw, h6 "wt" (by decide) (by decide), ne_eq, not_lt, not_le,
            not_false_eq_true, true_and, ite_eq_left_iff, Decidable.not_not,
            Option.some.injEq, not_and, zero_ne_one, not_imp, L5] at hc1 ⊢
        exact ⟨hc1, hc4⟩
      refine ⟨_, _, evalF_ite_f (by simp [Exp.ev, hv, h0, Machine.BinOp.eval]) (evalF_seq_ok2 e1
        (evalF_seq_ok2 e2
        (evalF_seq_ok2 e6 (evalF_ite_t hcv one_ne_zero (evalF_seq_ok2 e7 e8))))), ?_⟩
      simp [Exp.cost, costList, walkC] at hc6 ⊢
      omega
    · rw [ite_eq_right hc] at h
      have hcv : walkC.ev κ (wiC S v) L6 = some 0 := by
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
          beq_iff_eq,
          decide_eq_true_eq, not_and] at hc
        simp only [walkC, Exp.ofNat_def, Exp.mul_def, Exp.add_def, Exp.ev,
            h6 "up" (by decide) (by decide), b2n, Machine.State.upd, String.reduceEq,
            ↓reduceIte, BinOp.eval, Option.bind_some, Option.map_some, UnOp.eval,
            ite_eq_right_iff, one_ne_zero, imp_false, ite_not,
            h6 "dr" (by decide) (by decide), Bool.not_eq_true,
            h6 "ov" (by decide) (by decide), h6pw, h6 "wt" (by decide) (by decide),
            ne_eq, not_lt, not_le, Decidable.not_not, not_and, not_imp,
            Bool.not_eq_false, ite_eq_left_iff, Option.some.injEq, L5]
        intro a b c
        have := hc ⟨⟨a, b⟩, c⟩
        change V.weight + 2 ≤ 2 * S.P.a ^ V.height
        omega
      have hov : ((wiC S v).nodes.getX v).overflowOf = V.overflowOf := by
        simp only [wiC, getX_modify', hvs', and_self, ite_true]; rfl
      set L7 := upd (upd L6 "av" v) "au" V.livePar
      have b1 := evalF_assign_ok (κ := κ) (s := wiC S v) (L := L6) (x := "av") (e := .var "wv")
        (v := v)
        (by simp [Exp.ev, h6 "wv" (by decide) (by decide), h5v])
      have b2 := evalF_assign_ok (κ := κ) (s := wiC S v) (L := upd L6 "av" v) (x := "au") (e :=
        .var "up")
        (v := V.livePar) (by simp [Exp.ev, Machine.State.upd, h6 "up" (by decide) (by decide), L5])
      obtain ⟨L8, c8, e8, hc8⟩ := afterDS_agree (κ := κ) (S := wiC S v) (L := L7) (j := j) (v :=
        v) (up := V.livePar)
        (D := D2) hjob' (by simp [L7, Machine.State.upd]) (by simp [L7, Machine.State.upd]) hvN'
        (fun hne => by rw [hov] at hne ⊢; exact hds (by simpa [NIL] using h0) hne) h
      exact ⟨_, _, evalF_ite_f (by simp [Exp.ev, hv, h0, Machine.BinOp.eval]) (evalF_seq_ok2 e1
        (evalF_seq_ok2 e2
        (evalF_seq_ok2 e6 (evalF_ite_f hcv (evalF_seq_ok2 b1 (evalF_seq_ok2 b2 e8)))))),
        by simp [Exp.cost, walkC] at hc6 ⊢; omega⟩

/-! ### The job step -/

/-- Load the suspended reservation job into the procedure's working locals. -/
def jobRdS : Stm := cm{
  jx := O.jobX; jy := O.jobY; jz := O.jobZ; jt := O.jobT
  ja := O.jobA; jb := O.jobB; jc := O.jobC; jd := O.jobD }

/-- One resumption of the running job; the job's record is updated (or cleared). -/
def jobStepS : Stm := cm{
  jobRdS
  if jt = 0 then jcopyS
  else if jt = 1 then { wv := lpar[jy]; walkS }
  else if jt = 2 then { wv := ja; walkS }
  else if jt = 3 then { av := ja; au := jb; afterDS }
  else fundS }

theorem jobRdS_ok {κ : Caps} {s : Core} {L : Loc} {j : Job} (hjob : s.resJob = some j) :
    ∃ L', evalF κ jobRdS s L = .ok s L' 24 ∧ L' "jx" = j.x ∧ L' "jy" = j.y ∧ L' "jz" = j.z ∧
      L' "jt" = (pcEnc j.pc).1 ∧ L' "ja" = (pcEnc j.pc).2.1 ∧ L' "jb" = (pcEnc j.pc).2.2.1 ∧
      L' "jc" = (pcEnc j.pc).2.2.2.1 ∧ L' "jd" = (pcEnc j.pc).2.2.2.2 := by
  refine ⟨upd (upd (upd (upd (upd (upd (upd (upd L "jx" j.x) "jy" j.y) "jz" j.z) "jt" (pcEnc
    j.pc).1) "ja"
    (pcEnc j.pc).2.1) "jb" (pcEnc j.pc).2.2.1) "jc" (pcEnc j.pc).2.2.2.1) "jd" (pcEnc
      j.pc).2.2.2.2, ?_, ?_⟩
  · simp only [jobRdS]
    refine evalF_seq_ok2 (evalF_assign_ok (v := j.x) (by simp [Exp.ev, OF.get, hjob]))
      (evalF_seq_ok2
      (evalF_assign_ok (v := j.y) (by simp [Exp.ev, OF.get, hjob])) (evalF_seq_ok2
      (evalF_assign_ok (v := j.z) (by simp [Exp.ev, OF.get, hjob])) (evalF_seq_ok2
      (evalF_assign_ok (v := (pcEnc j.pc).1) (by simp [Exp.ev, OF.get, hjob])) (evalF_seq_ok2
      (evalF_assign_ok (v := (pcEnc j.pc).2.1) (by simp [Exp.ev, OF.get, hjob])) (evalF_seq_ok2
      (evalF_assign_ok (v := (pcEnc j.pc).2.2.1) (by simp [Exp.ev, OF.get, hjob])) (evalF_seq_ok2
      (evalF_assign_ok (v := (pcEnc j.pc).2.2.2.1) (by simp [Exp.ev, OF.get, hjob]))
      (evalF_assign_ok (v := (pcEnc j.pc).2.2.2.2) (by simp [Exp.ev, OF.get, hjob]))))))))
  · simp [Machine.State.upd]

theorem jobStep_walkNone {s : Core} {j : Job} (hpc : j.pc = .walk none) :
    (jobStep j).run s = (walkBody j (s.lpar.getX j.y)).run s := by
  unfold jobStep; rw [hpc]; simp only [OrderMaintenance.Proof.run_getP_bind, run_getLpar_bind]

theorem jobStep_walkSome {s : Core} {j : Job} {v : Nat} (hpc : j.pc = .walk (some v)) :
    (jobStep j).run s = (walkBody j v).run s := by
  unfold jobStep; rw [hpc]; simp only [OrderMaintenance.Proof.run_getP_bind]

theorem jobStep_after {s : Core} {j : Job} {v up : Nat} (hpc : j.pc = .afterDrain v up) :
    (jobStep j).run s = (afterDrain j v up).run s := by
  unfold jobStep; rw [hpc]; simp only [OrderMaintenance.Proof.run_getP_bind]

theorem jobStep_fund {s : Core} {j : Job} {v up src k : Nat} (hpc : j.pc = .fund v up src k) :
    (jobStep j).run s = (fundLoop j v up src k).run s := by
  unfold jobStep; rw [hpc]; simp only [OrderMaintenance.Proof.run_getP_bind]

theorem jobStepS_copy {κ : Caps} {s : Core} {L : Loc} {j : Job} {l : Nat} (hjob : s.resJob = some j)
    (hpc : j.pc = .copy l) (hx0 : j.x ≠ NIL)
    (hnx : notPrep s j.x) (hny : notPrep s j.y) (hnz : notPrep s j.z)
    (hxC : j.x < κ.tbl .C) (hyC : j.y < κ.tbl .C) (hzC : j.z < κ.tbl .C) (hlw : l < κ.pw)
    (hvN : (s.path.getX j.x).getX l < κ.tbl .N) :
    ∃ L' c, evalF κ jobStepS s L = .ok {
      copyC s j l with
      resJob := some (copyNext s.P j l)
    } L'
      c ∧ c ≤ 140 := by
  obtain ⟨Lr, er, hx, hy, hz, ht, ha, -, -, -⟩ := jobRdS_ok (κ := κ) (L := L) hjob
  rw [hpc] at ht ha
  obtain ⟨L1, c1, e1, hc1, -⟩ := jcopyS_ok (κ := κ) (L := Lr) hjob hx hy hz ha hx0  hnx hny
    hnz hxC hyC hzC hlw hvN
  refine ⟨_, _, evalF_seq_ok2 er (evalF_ite_t (v := 1) (by
    simp [Exp.ev, ht, pcEnc, Machine.BinOp.eval]) one_ne_zero
    e1), by simp [Exp.cost]; omega⟩

theorem jobStepS_walkNone {κ : Caps} {s : Core} {L : Loc} {j : Job} {D1 D2 : Nat} (hjob :
  s.resJob = some j)
    (hpc : j.pc = .walk none) (hya : j.y < κ.arr .lpar)
    (hvs : s.lpar.getX j.y ≠ 0 → s.lpar.getX j.y < s.nodes.size)
    (hvN : s.lpar.getX j.y ≠ 0 → s.lpar.getX j.y < κ.tbl .N)
    (hsd : s.lpar.getX j.y ≠ NIL → ((s.nodes.getX (s.lpar.getX j.y)).livePar != NIL &&
      !(s.nodes.getX (s.lpar.getX j.y)).draining &&
      (s.nodes.getX (s.lpar.getX j.y)).overflowOf == NIL && decide ((s.nodes.getX (s.lpar.getX
        j.y)).weight + 2 >
        2 * s.P.a ^ (s.nodes.getX (s.lpar.getX j.y)).height)) = true →
      SDAgree κ (wiC s (s.lpar.getX j.y)) (s.lpar.getX j.y) D1)
    (hds : s.lpar.getX j.y ≠ NIL → (s.nodes.getX (s.lpar.getX j.y)).overflowOf ≠ NIL →
      DSAgree κ (wiC s (s.lpar.getX j.y)) (s.nodes.getX (s.lpar.getX j.y)).overflowOf D2)
    (hpow : s.P.a = 2 ^ Nat.log2 s.P.a)
    {r : Option Job} {s' : Core} (h : (jobStep j).run s = .ok r s') :
    ∃ L' c, evalF κ jobStepS s L = .ok {
      s' with
      resJob := r
    } L' c ∧ c ≤ D1 + D2 + 300 := by
  obtain ⟨Lr, er, -, hy, -, ht, -, -, -, -⟩ := jobRdS_ok (κ := κ) (L := L) hjob
  rw [hpc] at ht
  rw [jobStep_walkNone hpc] at h
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := Lr) (x := "wv") (e := .rd (.a .lpar) "jy")
    (v := s.lpar.getX j.y)
    (by simp [Exp.ev, hy, hya, Fld.cap, Fld.get, AF.get])
  obtain ⟨L2, c2, e2, hc2⟩ := walkS_agree (κ := κ) (S := s) (L := upd Lr "wv" (s.lpar.getX j.y))
    (j := j) hjob
    (by simp [Machine.State.upd]) hvs hvN hsd hds hpow h
  refine ⟨_, _, evalF_seq_ok2 er (evalF_ite_f (by simp [Exp.ev, ht, pcEnc, Machine.BinOp.eval])
    (evalF_ite_t (v := 1) (by simp [Exp.ev, ht, pcEnc, Machine.BinOp.eval]) one_ne_zero
      (evalF_seq_ok2 a1 e2))), ?_⟩
  simp [Exp.cost]; omega

theorem jobStepS_walkSome {κ : Caps} {s : Core} {L : Loc} {j : Job} {v D1 D2 : Nat} (hjob :
  s.resJob = some j)
    (hpc : j.pc = .walk (some v)) (hvs : v ≠ 0 → v < s.nodes.size) (hvN : v ≠ 0 → v < κ.tbl .N)
    (hsd : v ≠ NIL → ((s.nodes.getX v).livePar != NIL && !(s.nodes.getX v).draining &&
      (s.nodes.getX v).overflowOf == NIL &&
      decide ((s.nodes.getX v).weight + 2 > 2 * s.P.a ^ (s.nodes.getX v).height)) = true →
        SDAgree κ (wiC s v) v D1)
    (hds : v ≠ NIL → (s.nodes.getX v).overflowOf ≠ NIL → DSAgree κ (wiC s v) (s.nodes.getX
      v).overflowOf D2)
    (hpow : s.P.a = 2 ^ Nat.log2 s.P.a)
    {r : Option Job} {s' : Core} (h : (jobStep j).run s = .ok r s') :
    ∃ L' c, evalF κ jobStepS s L = .ok {
      s' with
      resJob := r
    } L' c ∧ c ≤ D1 + D2 + 300 := by
  obtain ⟨Lr, er, -, -, -, ht, ha, -, -, -⟩ := jobRdS_ok (κ := κ) (L := L) hjob
  rw [hpc] at ht ha
  rw [jobStep_walkSome hpc] at h
  have a1 := evalF_assign_ok (κ := κ) (s := s) (L := Lr) (x := "wv") (e := .var "ja") (v := v)
    (by simp [Exp.ev, ha, pcEnc])
  obtain ⟨L2, c2, e2, hc2⟩ := walkS_agree (κ := κ) (S := s) (L := upd Lr "wv" v) (j := j) hjob
    (by simp [Machine.State.upd]) hvs hvN hsd hds hpow h
  refine ⟨_, _, evalF_seq_ok2 er (evalF_ite_f (by simp [Exp.ev, ht, pcEnc, Machine.BinOp.eval])
    (evalF_ite_f (by simp [Exp.ev, ht, pcEnc, Machine.BinOp.eval])
    (evalF_ite_t (v := 1) (by simp [Exp.ev, ht, pcEnc, Machine.BinOp.eval]) one_ne_zero
      (evalF_seq_ok2 a1 e2)))), ?_⟩
  simp [Exp.cost]; omega

theorem jobStepS_after {κ : Caps} {s : Core} {L : Loc} {j : Job} {v up D : Nat} (hjob : s.resJob
  = some j)
    (hpc : j.pc = .afterDrain v up) (hvN : v < κ.tbl .N)
    (hds : (s.nodes.getX v).overflowOf ≠ NIL → DSAgree κ s (s.nodes.getX v).overflowOf D)
    {r : Option Job} {s' : Core} (h : (jobStep j).run s = .ok r s') :
    ∃ L' c, evalF κ jobStepS s L = .ok {
      s' with
      resJob := r
    } L' c ∧ c ≤ D + 200 := by
  obtain ⟨Lr, er, -, -, -, ht, ha, hb, -, -⟩ := jobRdS_ok (κ := κ) (L := L) hjob
  rw [hpc] at ht ha hb
  rw [jobStep_after hpc] at h
  have b1 := evalF_assign_ok (κ := κ) (s := s) (L := Lr) (x := "av") (e := .var "ja") (v := v)
    (by simp [Exp.ev, ha, pcEnc])
  have b2 := evalF_assign_ok (κ := κ) (s := s) (L := upd Lr "av" v) (x := "au") (e := .var "jb")
    (v := up)
    (by simp [Exp.ev, Machine.State.upd, hb, pcEnc])
  obtain ⟨L2, c2, e2, hc2⟩ := afterDS_agree (κ := κ) (S := s) (L := upd (upd Lr "av" v) "au" up)
    (j := j) hjob
    (by simp [Machine.State.upd]) (by simp [Machine.State.upd]) hvN hds h
  refine ⟨_, _, evalF_seq_ok2 er (evalF_ite_f (by simp [Exp.ev, ht, pcEnc, Machine.BinOp.eval])
    (evalF_ite_f (by simp [Exp.ev, ht, pcEnc, Machine.BinOp.eval])
    (evalF_ite_f (by simp [Exp.ev, ht, pcEnc, Machine.BinOp.eval])
    (evalF_ite_t (v := 1) (by simp [Exp.ev, ht, pcEnc, Machine.BinOp.eval]) one_ne_zero
      (evalF_seq_ok2 b1 (evalF_seq_ok2 b2 e2)))))), ?_⟩
  simp [Exp.cost]; omega

theorem jobStepS_fund {κ : Caps} {s : Core} {L : Loc} {j : Job} {v up src k D : Nat} (hjob :
  s.resJob = some j)
    (hpc : j.pc = .fund v up src k) (hds : DSAgree κ s src D)
    {r : Option Job} {s' : Core} (h : (jobStep j).run s = .ok r s') :
    ∃ L' c, evalF κ jobStepS s L = .ok {
      s' with
      resJob := r
    } L' c ∧ c ≤ D + 150 := by
  obtain ⟨Lr, er, -, -, -, ht, ha, hb, hc, hd⟩ := jobRdS_ok (κ := κ) (L := L) hjob
  rw [hpc] at ht ha hb hc hd
  rw [jobStep_fund hpc] at h
  obtain ⟨L2, c2, e2, hc2⟩ := fundS_agree (κ := κ) (S := s) (L := Lr) (j := j) hjob ha hb hc hd
    hds h
  refine ⟨_, _, evalF_seq_ok2 er (evalF_ite_f (by simp [Exp.ev, ht, pcEnc, Machine.BinOp.eval])
    (evalF_ite_f (by simp [Exp.ev, ht, pcEnc, Machine.BinOp.eval])
    (evalF_ite_f (by simp [Exp.ev, ht, pcEnc, Machine.BinOp.eval])
    (evalF_ite_f (by simp [Exp.ev, ht, pcEnc, Machine.BinOp.eval]) e2)))), ?_⟩
  simp [Exp.cost]; omega

/-! ### The agreements, from the cases -/

theorem dsP_noJob : dsP.body.noJob = true := by decide
theorem sdP_noJob : sdP.body.noJob = true := by decide

theorem drainStep_dead_run {s : Core} {v : Nat} (hal : (s.nodes.getX v).alive = false) :
    (drainStep v).run s = .ok false s := by
  unfold drainStep; simp [  hal]

theorem dsAgree_dead {κ : Caps} {S : Core} {v : Nat} (hvN : v < κ.tbl .N) (hal : (S.nodes.getX
  v).alive = false) :
    DSAgree κ S v 10 := by
  intro b S' h
  rw [drainStep_dead_run hal] at h
  injection h with hb hS; subst hb; subst hS
  obtain ⟨L', c, e, hok, hc⟩ := dsP_dead (κ := κ) (L := Machine.State.setLocs (fun _ => 0) ["v"]
    [v])
    (by
      simp [Machine.State.setLocs, Machine.State.upd]) hvN hal
  exact ⟨L', c, e, by simp [hok, b2n], hc, rfl⟩

theorem dsAgree_move {κ : Caps} {s : Core} {v pt tb pv vb : Nat}
    (hal : (s.nodes.getX v).alive = true) (hf : (s.nodes.getX v).first ≠ NIL)
    (hside : goesLeft s v ∨
      lookup (s.nodes.getX v).side (belowY s v (s.nodes.getX v).first) = some .right ∧
      lookup (s.nodes.getX v).side (belowY s v (s.nodes.getX v).last) = some .right)
    (hsz : (s.nodes.getX v).height + 1 < (s.path.getX (dsY s v)).size)
    (hpt : (s.nodes.getX ((s.path.getX (dsY s v)).getX ((s.nodes.getX v).height + 1))).lab? (dsT
      s v) = some pt)
    (htb : (s.nodes.getX (dsT s v)).lab? (belowY s v (dsY s v)) = some tb)
    (hpv : (s.nodes.getX ((s.path.getX (dsY s v)).getX ((s.nodes.getX v).height + 1))).lab? v =
      some pv)
    (hvb : (s.nodes.getX v).lab? (belowY s v (dsY s v)) = some vb)
    (hold : (pv <<< ((s.nodes.getX v).height * s.P.beta)) |||
        (vb <<< (((s.nodes.getX v).height - 1) * s.P.beta)) ≤ (s.C.getX (dsY s v)).tag)
    (hok : OrderMaintenance.Proof.TagOK s (dsY s v) (dsTag s v pt tb pv vb))
    (h1 : 1 ≤ (s.nodes.getX v).height) (hpsz : (s.path.getX (dsY s v)).size = s.P.H + 1)
    (htbB : tb < 2 ^ s.P.beta) (hvbB : vb < 2 ^ s.P.beta) (htv : dsT s v ≠ v)
    (hvs : v < s.nodes.size) (hts : dsT s v < s.nodes.size) (hys : dsY s v < s.C.size)
    (hnf : notPrep s (s.nodes.getX v).first) (hnl : notPrep s (s.nodes.getX v).last)
    (hvN : v < κ.tbl .N) (htN : dsT s v < κ.tbl .N) (hvsd : v < κ.lrec .side) (hvr : v < κ.lrec
      .table)
    (htr : dsT s v < κ.lrec .table)
    (hprr : (s.path.getX (dsY s v)).getX ((s.nodes.getX v).height + 1) < κ.lrec .table)
    (hfC : (s.nodes.getX v).first < κ.tbl .C) (hlC : (s.nodes.getX v).last < κ.tbl .C)
    (hyP : (s.C.getX (dsY s v)).prev < κ.tbl .C) (hyN : (s.C.getX (dsY s v)).next < κ.tbl .C)
    (hw : (s.nodes.getX v).height + 1 < κ.pw) :
    DSAgree κ s v (1100 + 80 * (s.nodes.getX v).side.length +
        40 * (s.nodes.getX ((s.path.getX (dsY s v)).getX ((s.nodes.getX v).height +
          1))).table.length +
        20 * (s.nodes.getX (dsT s v)).table.length + 20 * (s.nodes.getX v).table.length) := by
  intro b S' h
  rw [drainStep_move hal hf hside hsz hpt htb hpv hvb hold hok] at h
  injection h with hb hS; subst hb; subst hS
  obtain ⟨L', c, e, hok', hc⟩ := dsP_move (κ := κ) (L := Machine.State.setLocs (fun _ => 0)
    ["v"] [v])
    (by
      simp [Machine.State.setLocs, Machine.State.upd]) hal hf hside hsz hpt htb hpv hvb hold hok
        h1 hpsz htbB
    hvbB htv hvs hts hys hnf hnl hvN htN hvsd hvr htr hprr hfC hlC hyP hyN hw
  exact ⟨L', c, e, by simp [hok', b2n], hc, evalF_resJob dsP_noJob e⟩

theorem dsAgree_finish {κ : Caps} {s : Core} {v B : Nat}
    (hal : (s.nodes.getX v).alive = true) (hf : (s.nodes.getX v).first = NIL)
    (hnd : (s.nodes.getX v).inTables.Nodup) (hT : ∀ T ∈ (s.nodes.getX v).inTables, v ∈
      (s.nodes.getX T).order)
    (hv0 : v ≠ 0) (hvs : v < s.nodes.size) (hvo : (s.nodes.getX v).height - 1 ≠ 0 → v ∉
      (s.nodes.getX v).order)
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
    DSAgree κ s v (300 + (s.nodes.getX v).table.length * (171 + 100 * B) +
        (s.nodes.getX v).inTables.length * (301 + 200 * B)) := by
  intro b S' h
  rw [drainStep_finish hal hf hnd hT] at h
  injection h with hb hS; subst hb; subst hS
  obtain ⟨L', c, e, hok', hc⟩ := dsP_finish (κ := κ) (L := Machine.State.setLocs (fun _ => 0)
    ["v"] [v]) (B := B)
    (by
      simp [Machine.State.setLocs, Machine.State.upd]) hal hf hnd hT hv0 hvs hvo hvN hvr hvi ht1
        ht2 hcE hcT
  exact ⟨L', c, e, by simp [hok', b2n], hc, evalF_resJob dsP_noJob e⟩

theorem startDrain_noop_run {t : Core} {v : Nat} (hno : (sKids t v).length < 2 ∨ (sH t v > 1 ∧
  sK t v = 0)) :
    (startDrain v).run t = .ok () t := by
  unfold startDrain
  simp only [OrderMaintenance.Proof.run_getP_bind, run_getN_bind]
  by_cases h2 : (t.nodes.getX v).children.length < 2
  · rw [ite_eq_left h2]; rfl
  · rw [ite_eq_right h2]
    simp only [OrderMaintenance.Proof.run_get_bind]
    have hk : (sH t v > 1 ∧ sK t v = 0) := hno.resolve_left h2
    rw [ite_eq_left (by simpa using hk)]; rfl

theorem sdAgree_noop {κ : Caps} {t : Core} {v : Nat} (hno : (sKids t v).length < 2 ∨ (sH t v > 1
  ∧ sK t v = 0))
    (hv : v < t.nodes.size) (hcN : t.nodes.size ≤ κ.tbl .N) (hcrc : t.nodes.size ≤ κ.lrec .children)
    (hks : sH t v ≠ 1 → ∀ e ∈ (t.nodes.getX v).children, e < κ.tbl .N) :
    SDAgree κ t v (230 + 300 * (t.nodes.getX v).children.length) := by
  intro S' h
  rw [startDrain_noop_run hno] at h
  injection h with _ hS; subst hS
  obtain ⟨L', c, e, hc⟩ := startDrainS_noop (κ := κ) (L := Machine.State.setLocs (fun _ => 0)
    ["v"] [v]) hno hv
    (by
      simp [Machine.State.setLocs, Machine.State.upd]) hcN hcrc hks
  exact ⟨L', c, e, hc, rfl⟩

theorem sdAgree_ok {κ : Caps} {t : Core} {v B : Nat} {side : List (Nat × Side)}
    (hk2 : 2 ≤ (sKids t v).length) (hk0 : ¬(sH t v > 1 ∧ sK t v = 0)) (hside : sSideO t v = some
      side)
    (hroom : ∀ T ∈ (t.nodes.getX v).inTables, RoomOK t v T) (hnd : (t.nodes.getX v).inTables.Nodup)
    (hall : ∀ e ∈ sKids t v, (lookup side e).isSome)
    (hpar : v ∈ (t.nodes.getX (t.nodes.getX v).livePar).children) (hv : v < t.nodes.size)
    (hvT : v ∉ (t.nodes.getX v).inTables) (hvk : sH t v ≠ 1 → v ∉ (t.nodes.getX v).children)
    (hK : sH t v - 1 ≠ 0 → ∀ e ∈ (t.nodes.getX v).table.map (·.1), e < t.nodes.size)
    (hKN : ∀ e ∈ (t.nodes.getX v).table.map (·.1), e < κ.tbl .N ∧ (sH t v - 1 = 0 → e < κ.lrec
      .cin))
    (hks : sH t v ≠ 1 → ∀ e ∈ (t.nodes.getX v).children, e < t.nodes.size)
    (hksl : sH t v = 1 → ∀ e ∈ (t.nodes.getX v).children, e < κ.arr .lpar)
    (hp : (t.nodes.getX v).livePar < t.nodes.size) (hpv : (t.nodes.getX v).livePar ≠ v)
    (hB : ∀ T ∈ (t.nodes.getX v).inTables, (t.nodes.getX T).table.length ≤ B ∧ (t.nodes.getX
      T).side.length ≤ B)
    (hcN : t.nodes.size + 2 ≤ κ.tbl .N)
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
    SDAgree κ t v (sdCost (t.nodes.getX v).children.length (t.nodes.getX v).table.length
        (t.nodes.getX v).inTables.length side.length B
        (t.nodes.getX (t.nodes.getX v).livePar).children.length) := by
  intro S' h
  rw [startDrain_run hk2 hk0 hside hroom hnd hall hpar hv] at h
  injection h with _ hS; subst hS
  obtain ⟨L', c, e, hc⟩ := startDrainS_ok (κ := κ) (L := Machine.State.setLocs (fun _ => 0)
    ["v"] [v]) hk2 hk0
    hside hroom hnd hpar hv hvT hvk hK hKN hks hksl hp hpv hB (by
      simp [Machine.State.setLocs, Machine.State.upd]) hcN
    hcrc hcrs hcrt hcri hcT hcS hcTv hcI hc4 hcC hcP
  exact ⟨L', c, e, hc, evalF_resJob sdP_noJob e⟩

end OrderMaintenance.Impl
