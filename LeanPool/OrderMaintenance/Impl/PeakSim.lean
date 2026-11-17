/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.Sim

public import LeanPool.OrderMaintenance.Impl.Peak


/-!
# Theorem W, option (A), stage A1: the peak of the compiled code

`sim_peak`: if machine state `m` holds core `s` with the same locals, and `evalF κ c s L` ends
normally or with a failed guard, then the compiled run of `c` ends with
`peak = max m.peak (pkF κ c s L)`. Together with `sim` (same outcome, same encoding, same cost),
this is the one-time extension of the simulation theorem that approach (i′) of `docs/WORD.md`
needs: every later peak bound for a core procedure is a bound on `pkF`, a Level F quantity.

Nothing here is used by Theorems A and B; `sim` is unchanged.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg Arr BinOp UnOp State Out exec)

variable {p : Nat} {κ : Caps}

/-- The compiled run ends with peak `q`, when the source run ends `ok` or `fail`. -/
def PAgree : Res → Out → Nat → Prop
  | .ok _ _ _, o, q => o.st.peak = q
  | .fail _ _ _, o, q => o.st.peak = q
  | .bug, _, _ => True

theorem PAgree.addCost {r : Res} {o : Out} {q : Nat} (h : PAgree r o q) (c : Nat) :
    PAgree (r.addCost c) ⟨o.st, c + o.cost, o.status⟩ q := by
  cases r <;> exact h

theorem PAgree.congr {r : Res} {o : Out} {q q' : Nat} (h : PAgree r o q) (e : q = q') : PAgree r
  o q' :=
  e ▸ h

@[simp] theorem st_setLoc_peak (m : State) (x : Reg) (v : Nat) : (m.setLoc x v).peak = m.peak := rfl
@[simp] theorem st_write_peak (m : State) (a : Arr) (j v : Nat) : (m.write a j v).peak = m.peak
  := rfl
@[simp] theorem st_bump_peak (m : State) (v : Nat) : (m.bump v).peak = max m.peak v := rfl
@[simp] theorem st_enter_peak (m : State) (ps : List Reg) (vs : List Nat) : (m.enter ps vs).peak
  = m.peak := rfl
@[simp] theorem st_leave_peak (m : State) (c : Reg → Nat) (r d : List Reg) : (m.leave c r
  d).peak = m.peak := rfl

/-! ### Loops -/

theorem sim_peak_runFor {b : Stm} {x : Reg}
    (ih : ∀ s L m, Enc p κ s m → m.loc = L →
      PAgree (evalF κ b s L) (exec (b.compile p κ) m) (max m.peak (pkF κ b s L))) :
    ∀ n k s L m, Enc p κ s m → m.loc = L →
      PAgree (runForF (evalF κ b) x k n s L) (Machine.runFor (exec (b.compile p κ)) x k n m)
        (max m.peak (pkFor (evalF κ b) (pkF κ b) x k n s L))
  | 0, _, s, L, m, h, hL => by
    simp only [PAgree, runForF, Machine.runFor, pkFor, zero_le, sup_of_le_left]
  | n + 1, k, s, L, m, h, hL => by
    have h0 : Enc p κ s (m.setLoc x k) := h.setLoc x k
    have hL0 : (m.setLoc x k).loc = Machine.State.upd L x k := by simp only [State.setLoc, hL]
    have hs := sim (p := p) b h0 hL0
    have hp := ih s _ _ h0 hL0
    simp only [runForF, Machine.runFor, pkFor, Machine.Out.bind]
    revert hs hp
    generalize evalF κ b s (Machine.State.upd L x k) = r
    generalize exec (b.compile p κ) (m.setLoc x k) = o
    intro hs hp
    cases r with
    | ok s' L' c =>
      obtain ⟨h1, h2, h3, -⟩ := hs
      simp only [Res.addCost, Res.bind, h1]
      have := sim_peak_runFor (x := x) ih n (k + 1) s' L' o.st h2 h3
      revert this
      generalize runForF (evalF κ b) x (k + 1) n s' L' = r2
      generalize Machine.runFor (exec (b.compile p κ)) x (k + 1) n o.st = o2
      intro this
      simp only [PAgree, st_setLoc_peak] at hp
      cases r2 <;> simp only [PAgree] at this ⊢ <;> (rw [this, hp]; omega)
    | fail s' L' c =>
      obtain ⟨h1, -, -, -⟩ := hs
      simp only [Res.addCost, Res.bind, h1, PAgree]
      simp only [PAgree, st_setLoc_peak] at hp
      rw [hp]; omega
    | bug => trivial


theorem Exp.le_pkList {κ : Caps} {s : Core} {L : Loc} {e : Exp} {v : Nat} :
    ∀ {es : List Exp}, e ∈ es → e.ev κ s L = some v → v ≤ pkList κ s L es
  | e' :: es, hm, h => by
    simp only [pkList, List.map_cons, List.foldr_cons]
    rcases List.mem_cons.mp hm with rfl | hm
    · exact le_max_of_le_left (Exp.le_pk h)
    · exact le_max_of_le_right (Exp.le_pkList hm h)

/-! ### The statements with their own compiled form -/

section special
variable {s : Core} {L : Loc} {m : State}

theorem peak_lwr (h : Enc p κ s m) (hL : m.loc = L) (k : LK) (b : Bool) (i j e : Exp) :
    PAgree (evalF κ (.lwr k b i j e) s L) (exec (Stm.compile p κ (.lwr k b i j e)) m)
      (max m.peak (pkF κ (.lwr k b i j e) s L)) := by
  simp only [evalF]
  split
  · next x y v hx hy hv =>
    split
    · next hyl =>
      split
      · next s' hs =>
        obtain ⟨hxr, -⟩ := LK.set_lrec hs
        have hle := (h.llen k x hxr).2
        have hyc : y < κ.lcap k := Nat.lt_of_lt_of_le hyl hle
        have hlt : x * k.stride κ.lcap + y < m.cap (arrL p k b) := by
          rw [h.lcapA]; exact h.stride_lt hxr hyc
        simp only [Stm.compile, exec, Machine.Expr.eval,
          Exp.ev_compile h hL i hx, Exp.ev_compile h hL j hy,
          Exp.ev_compile h hL e hv, Option.bind_some, Machine.BinOp.eval]
        rw [ite_eq_left (by simpa using hlt)]
        simp only [PAgree, pkF, lidxPk, st_write_peak, st_bump_peak,
          Machine.Expr.maxv,
          Exp.maxv_compile h hL i hx, Exp.maxv_compile h hL j hy, Exp.maxv_compile h hL e hv,
            Machine.Expr.eval,
          Exp.ev_compile h hL i hx, Exp.ev_compile h hL j hy, Option.bind_some, Machine.BinOp.eval,
          Option.getD_some, Exp.val_of hx, Exp.val_of hy]
        omega
      · trivial
    · trivial
  · trivial

theorem peak_lgrow (h : Enc p κ s m) (hL : m.loc = L) (k : LK) (i a b : Exp) :
    PAgree (evalF κ (.lgrow k i a b) s L) (exec (Stm.compile p κ (.lgrow k i a b)) m)
      (max m.peak (pkF κ (.lgrow k i a b) s L)) := by
  simp only [evalF]
  split
  · next x va vb hx ha hb =>
    split
    · next s' hs =>
      obtain ⟨hxr, hlc⟩ := LK.set_lrec hs
      rw [List.length_append, List.length_singleton] at hlc
      have hlen := (h.llen k x hxr).1
      generalize hn : (k.view s x).length = n at hlc hlen
      have hlt : x * k.stride κ.lcap + n < κ.lrec k * κ.lcap k := h.stride_lt hxr (by omega)
      -- the compiled index and its peak, on every state holding `s`
      have hix : ∀ m' : State, Enc p κ s m' → m'.loc = L →
          (Machine.Expr.bin .add (.bin .mul (i.compile p κ) (.lit (k.stride κ.lcap)))
            (.load (arrLen p k) (i.compile p κ))).eval m' = some (x * k.stride κ.lcap + n) ∧
          (Machine.Expr.bin .add (.bin .mul (i.compile p κ) (.lit (k.stride κ.lcap)))
            (.load (arrLen p k) (i.compile p κ))).maxv m' =
            max (max (max (max (i.pk κ s L) (k.stride κ.lcap)) (x * k.stride κ.lcap)) (max (i.pk
              κ s L) n))
              (x * k.stride κ.lcap + n) := by
        intro m' h' hL'
        have hl' := (h'.llen k x hxr).1
        rw [hn] at hl'
        constructor
        · simp only [Machine.Expr.eval, Exp.ev_compile h' hL' i hx, BinOp.eval, Option.bind_some,
            h'.lcapN, hxr, ↓reduceIte, hl']
        · simp only [Machine.Expr.maxv, Exp.maxv_compile h' hL' i hx, Machine.Expr.eval,
            Exp.ev_compile h' hL' i hx, BinOp.eval, Option.bind_some, Option.getD_some,
            Nat.max_assoc, h'.lcapN, hxr, ↓reduceIte, hl', le_max_iff, Std.le_refl,
            true_or, or_true, sup_of_le_right, le_add_iff_nonneg_left, zero_le,
            le_add_iff_nonneg_right]
      have hpi : (i.val κ s L) = x := Exp.val_of hx
      simp only [Stm.compile]
      rw [Machine.exec,
        exec_store_ok (hix m h hL).1 (Exp.ev_compile h hL a ha) (by rw [h.lcapA]; exact hlt),
        out_bind_ok]
      have h1 := ((h.bump (Machine.Expr.maxv m (Machine.Expr.bin .add (.bin .mul (i.compile p κ)
          (.lit (k.stride κ.lcap))) (.load (arrLen p k) (i.compile p κ))))).bump (a.compile p κ
            |>.maxv m)
        |>.writeBeyond (b := false) (v := va) hxr (le_of_eq hn) (by omega))
      generalize hm1 : (((m.bump (Machine.Expr.maxv m (Machine.Expr.bin .add (.bin .mul
        (i.compile p κ)
          (.lit (k.stride κ.lcap))) (.load (arrLen p k) (i.compile p κ))))).bump (a.compile p κ
            |>.maxv m)).write
          (arrL p k false) (x * k.stride κ.lcap + n) va) = m1 at h1
      have hL1 : m1.loc = L := by rw [← hm1]; simp only [State.write, State.bump, hL,
          Machine.Expr.maxv, Machine.Expr.eval,
          BinOp.eval, Option.bind_some,
          Nat.max_assoc, le_max_iff, Std.le_refl,
          true_or, or_true, sup_of_le_right]
      have hp1 : m1.peak = max (max m.peak (max (max (max (max (i.pk κ s L) (k.stride κ.lcap))
          (x * k.stride κ.lcap)) (max (i.pk κ s L) n)) (x * k.stride κ.lcap + n))) (a.pk κ s L)
            := by
        rw [← hm1]; simp only [st_write_peak, st_bump_peak, (hix m h hL).2, Exp.maxv_compile h
          hL a ha]
      rw [Machine.exec,
        exec_store_ok (hix m1 h1 hL1).1 (Exp.ev_compile h1 hL1 b hb)
        (by rw [h1.lcapA]; exact hlt), out_bind_ok]
      have h2 := ((h1.bump (Machine.Expr.maxv m1 (Machine.Expr.bin .add (.bin .mul (i.compile p κ)
          (.lit (k.stride κ.lcap))) (.load (arrLen p k) (i.compile p κ))))).bump (b.compile p κ
            |>.maxv m1)
        |>.writeBeyond (b := true) (v := vb) hxr (le_of_eq hn) (by omega))
      generalize hm2 : (((m1.bump (Machine.Expr.maxv m1 (Machine.Expr.bin .add (.bin .mul
        (i.compile p κ)
          (.lit (k.stride κ.lcap))) (.load (arrLen p k) (i.compile p κ))))).bump (b.compile p κ
            |>.maxv m1)).write
          (arrL p k true) (x * k.stride κ.lcap + n) vb) = m2 at h2
      have hL2 : m2.loc = L := by rw [← hm2]; simp only [State.write, State.bump, hL1,
          Machine.Expr.maxv, Machine.Expr.eval,
          BinOp.eval, Option.bind_some,
          Nat.max_assoc, le_max_iff, Std.le_refl,
          true_or, or_true, sup_of_le_right]
      have hp2 : m2.peak = max (max m1.peak (max (max (max (max (i.pk κ s L) (k.stride κ.lcap))
          (x * k.stride κ.lcap)) (max (i.pk κ s L) n)) (x * k.stride κ.lcap + n))) (b.pk κ s L)
            := by
        rw [← hm2]; simp only [st_write_peak, st_bump_peak, (hix m1 h1 hL1).2, Exp.maxv_compile
          h1 hL1 b hb]
      have hl2 := (h2.llen k x hxr).1
      rw [hn] at hl2
      have hn2 : (Machine.Expr.bin .add (.load (arrLen p k) (i.compile p κ)) (.lit 1)).eval m2 =
        some (n + 1) := by
        simp only [Machine.Expr.eval, Exp.ev_compile h2 hL2 i hx, h2.lcapN, Option.bind_some,
            hxr, ↓reduceIte, hl2, BinOp.eval]
      rw [exec_store_ok (Exp.ev_compile h2 hL2 i hx) hn2 (by rw [h2.lcapN]; exact hxr)]
      simp only [PAgree, pkF, st_write_peak, st_bump_peak, hp2, hp1, hpi, hn,
        Machine.Expr.maxv,
        Exp.maxv_compile h2 hL2 i hx, Exp.ev_compile h2 hL2 i hx, Machine.Expr.eval,
          Option.bind_some, h2.lcapN,
        ite_eq_left hxr, hl2, Option.getD_some, Machine.BinOp.eval]
      apply le_antisymm
      all_goals
        simp only [max_le_iff]
        repeat' apply And.intro
      all_goals simp only [le_max_iff, le_refl, true_or, or_true, Nat.le_add_left]
    · trivial
  · trivial

theorem peak_lshrink (h : Enc p κ s m) (hL : m.loc = L) (k : LK) (i : Exp) :
    PAgree (evalF κ (.lshrink k i) s L) (exec (Stm.compile p κ (.lshrink k i)) m)
      (max m.peak (pkF κ (.lshrink k i) s L)) := by
  simp only [evalF]
  split
  · next x hx =>
    split
    · next hne =>
      split
      · next s' hs =>
        obtain ⟨hxr, -⟩ := LK.set_lrec hs
        have hlen := (h.llen k x hxr).1
        have hv : (Machine.Expr.bin .sub (.load (arrLen p k) (i.compile p κ)) (.lit 1)).eval m =
            some ((k.view s x).length - 1) := by
          simp only [Machine.Expr.eval, Exp.ev_compile h hL i hx, h.lcapN, Option.bind_some, hxr,
              ↓reduceIte, hlen, BinOp.eval, ite_eq_left_iff, not_le, Nat.lt_one_iff,
              List.length_eq_zero_iff, reduceCtorEq, imp_false]
          intro e; rw [e] at hne; simp only [List.length_nil, ne_eq, not_true_eq_false] at hne
        simp only [Stm.compile]
        rw [exec_store_ok (Exp.ev_compile h hL i hx) hv (by rw [h.lcapN]; exact hxr)]
        have hpos : 1 ≤ (k.view s x).length := Nat.one_le_iff_ne_zero.mpr hne
        simp only [PAgree, pkF, st_write_peak, st_bump_peak, Machine.Expr.maxv,
          Option.getD_some,
          Exp.maxv_compile h hL i hx, Machine.Expr.eval, Exp.ev_compile h hL i hx,
            Option.bind_some, h.lcapN,
          ite_eq_left hxr, hlen, Exp.val_of hx, Machine.BinOp.eval, ite_eq_left hpos]
        omega
      · trivial
    · trivial
  · trivial

theorem peak_lclear (h : Enc p κ s m) (hL : m.loc = L) (k : LK) (i : Exp) :
    PAgree (evalF κ (.lclear k i) s L) (exec (Stm.compile p κ (.lclear k i)) m)
      (max m.peak (pkF κ (.lclear k i) s L)) := by
  simp only [evalF]
  split
  · next x hx =>
    split
    · next s' hs =>
      obtain ⟨hxr, -⟩ := LK.set_lrec hs
      simp only [Stm.compile]
      rw [exec_store_ok (Exp.ev_compile h hL i hx) (by rfl) (by rw [h.lcapN]; exact hxr)]
      simp only [PAgree, pkF, st_write_peak, st_bump_peak, Machine.Expr.maxv,
        Exp.maxv_compile h hL i hx]
      omega
    · trivial
  · trivial

theorem peak_pwr (h : Enc p κ s m) (hL : m.loc = L) (c j e : Exp) :
    PAgree (evalF κ (.pwr c j e) s L) (exec (Stm.compile p κ (.pwr c j e)) m)
      (max m.peak (pkF κ (.pwr c j e) s L)) := by
  simp only [evalF]
  split
  · next x y v hx hy hv =>
    split
    · next hc =>
      obtain ⟨hxC, hyw, hnp⟩ := hc
      have hlt : x * κ.pw + y < m.cap (arrPath p) := by rw [h.wcap]; exact lt_mul_add hxC hyw
      simp only [Stm.compile, exec, Machine.Expr.eval, Exp.ev_compile h hL c hx,
        Exp.ev_compile h hL j hy,
        Exp.ev_compile h hL e hv, h.rowW_eval, Option.bind_some, Machine.BinOp.eval]
      rw [ite_eq_left (by simpa using hlt)]
      simp only [PAgree, pkF, pidxPk, st_write_peak, st_bump_peak,
        Machine.Expr.maxv,
        Exp.maxv_compile h hL c hx, Exp.maxv_compile h hL j hy, Exp.maxv_compile h hL e hv,
          Machine.Expr.eval,
        Exp.ev_compile h hL c hx, Exp.ev_compile h hL j hy, h.rowW_eval, h.rowW_maxv,
          Option.bind_some,
        Machine.BinOp.eval, Option.getD_some, Exp.val_of hx, Exp.val_of hy]
      omega
    · trivial
  · trivial

theorem peak_rowReset (_h : Enc p κ s m) (_hL : m.loc = L) (c : Exp) :
    PAgree (evalF κ (.rowReset c) s L) (exec (Stm.compile p κ (.rowReset c)) m)
      (max m.peak (pkF κ (.rowReset c) s L)) := by
  simp only [evalF]
  split
  · split
    · simp only [PAgree, Stm.compile, exec, pkF, zero_le, sup_of_le_left]
    · trivial
  · trivial

theorem peak_prepInit (h : Enc p κ s m) (hL : m.loc = L) (c b : Exp) :
    PAgree (evalF κ (.prepInit c b) s L) (exec (Stm.compile p κ (.prepInit c b)) m)
      (max m.peak (pkF κ (.prepInit c b) s L)) := by
  simp only [evalF]
  split
  · next x y hx hy =>
    split
    · next hc =>
        have hargs : Machine.evalList m ([c, b].map (Exp.compile p κ)) = some [x, y] :=
          evList_compile h hL [c, b] (by
            simp only [evList, List.mapM_cons, hx, hy, List.mapM_nil, Option.pure_def,
              Option.bind_eq_bind, Option.bind_some])
        have hmx := maxvList_compile h hL [c, b] (vs := [x, y]) (by
          simp only [evList, List.mapM_cons, hx, hy, List.mapM_nil, Option.pure_def,
            Option.bind_eq_bind, Option.bind_some])
        simp only [List.map_cons, List.map_nil] at hargs hmx
        simp only [Stm.compile, exec, hargs]
        generalize hm0 : (m.bump (Machine.maxvList m [Exp.compile p κ c, Exp.compile p κ
          b])).enter ["c", "b"] [x, y] = m0
        have hc0 : ∀ o, m0.cap (arrO p o) = 1 := by intro o; rw [← hm0]; exact h.ocap o
        have hl0 : m0.loc "c" = x ∧ m0.loc "b" = y := by rw [← hm0]; simp only [State.enter,
            State.bump,
            Machine.maxvList,
            List.map_cons,
            List.map_nil,
            List.foldr_cons,
            List.foldr_nil,
            zero_le,
            sup_of_le_left,
            State.setLocs,
            State.upd,
            String.reduceEq,
            ↓reduceIte,
            and_self]
        have hp0 : m0.peak = max m.peak (pkList κ s L [c, b]) := by rw [← hm0, ← hmx]; rfl
        simp only [st1, exec, Machine.Out.bind, Machine.Expr.eval,
          hc0, hl0, Nat.zero_lt_one, ite_true, st_write_cap, st_write_loc, st_bump_cap, st_bump_loc,
          Machine.Expr.maxv]
        simp only [PAgree, pkF, st_leave_peak, st_write_peak, st_bump_peak, hp0]
        apply le_antisymm
        all_goals
          simp only [max_le_iff]
          repeat' apply And.intro
        all_goals simp only [le_max_iff, le_refl, true_or, or_true, Nat.zero_le, Exp.le_pkList
          (κ := κ) (s := s) (L := L) (es := [c, b]) (by simp) hx, Exp.le_pkList (κ := κ) (s :=
            s) (L := L) (es := [c, b]) (by simp) hy]
    · trivial
  · trivial

theorem peak_prepSet (h : Enc p κ s m) (hL : m.loc = L) (hh b t : Exp) :
    PAgree (evalF κ (.prepSet hh b t) s L) (exec (Stm.compile p κ (.prepSet hh b t)) m)
      (max m.peak (pkF κ (.prepSet hh b t) s L)) := by
  simp only [evalF]
  split
  · next pr vh vb vt hpr hvh hvb hvt =>
      have hargs : Machine.evalList m ([hh, b, t].map (Exp.compile p κ)) = some [vh, vb, vt] :=
        evList_compile h hL [hh, b, t] (by
          simp only [evList, List.mapM_cons, hvh, hvb, hvt, List.mapM_nil, Option.pure_def,
            Option.bind_eq_bind, Option.bind_some])
      have hmx := maxvList_compile h hL [hh, b, t] (vs := [vh, vb, vt]) (by
        simp only [evList, List.mapM_cons, hvh, hvb, hvt, List.mapM_nil, Option.pure_def,
          Option.bind_eq_bind, Option.bind_some])
      simp only [List.map_cons, List.map_nil] at hargs hmx
      simp only [Stm.compile, exec, hargs]
      generalize hm0 : (m.bump (Machine.maxvList m [Exp.compile p κ hh, Exp.compile p κ b,
        Exp.compile p κ t])).enter ["h", "b", "t"] [vh, vb, vt] = m0
      have hc0 : ∀ o, m0.cap (arrO p o) = 1 := by intro o; rw [← hm0]; exact h.ocap o
      have hl0 : m0.loc "h" = vh ∧ m0.loc "b" = vb ∧ m0.loc "t" = vt := by rw [← hm0]; simp only [
          State.enter,
          State.bump,
          Machine.maxvList,
          List.map_cons,
          List.map_nil,
          List.foldr_cons,
          List.foldr_nil,
          zero_le,
          sup_of_le_left,
          State.setLocs,
          State.upd,
          String.reduceEq,
          ↓reduceIte,
          and_self]
      have hp0 : m0.peak = max m.peak (pkList κ s L [hh, b, t]) := by rw [← hm0, ← hmx]; rfl
      simp only [st1, exec, Machine.Out.bind, Machine.Expr.eval,
        hc0, hl0, Nat.zero_lt_one, ite_true, st_write_cap, st_write_loc, st_bump_cap, st_bump_loc,
        Machine.Expr.maxv]
      simp only [PAgree, pkF, st_leave_peak, st_write_peak, st_bump_peak, hp0]
      apply le_antisymm
      all_goals
        simp only [max_le_iff]
        repeat' apply And.intro
      all_goals simp only [le_max_iff, le_refl, true_or, or_true, Nat.zero_le, Exp.le_pkList (κ
        := κ) (s := s) (L := L) (es := [hh, b, t]) (by simp) hvh, Exp.le_pkList (κ := κ) (s :=
          s) (L := L) (es := [hh, b, t]) (by simp) hvb, Exp.le_pkList (κ := κ) (s := s) (L := L)
            (es := [hh, b, t]) (by simp) hvt]
  · trivial

theorem peak_prepPath (h : Enc p κ s m) (hL : m.loc = L) (j e : Exp) :
    PAgree (evalF κ (.prepPath j e) s L) (exec (Stm.compile p κ (.prepPath j e)) m)
      (max m.peak (pkF κ (.prepPath j e) s L)) := by
  simp only [evalF]
  split
  · next pr y v hpr hy hv =>
    split
    · next hyw =>
      have hpc := h.prepC pr hpr
      have hch : m.mem (arrO p .prepChunk) 0 = pr.chunk := by rw [h.omem]; simp only [OF.get,
          hpr]
      have hlt : pr.chunk * κ.pw + y < m.cap (arrPath p) := by rw [h.wcap]; exact lt_mul_add hpc hyw
      simp only [Stm.compile, exec, Machine.Expr.eval, Exp.ev_compile h hL j hy,
        Exp.ev_compile h hL e hv,
        h.rowW_eval, Option.bind_some, Machine.BinOp.eval, h.ocap, Nat.zero_lt_one, ite_true, hch]
      rw [ite_eq_left (by simpa using hlt)]
      simp only [PAgree, pkF, pidxPk, st_write_peak, st_bump_peak,
        Machine.Expr.maxv,
        Exp.maxv_compile h hL j hy, Exp.maxv_compile h hL e hv, Machine.Expr.eval, h.ocap,
          Nat.zero_lt_one,
        ite_true, hch, Exp.ev_compile h hL j hy, h.rowW_eval, h.rowW_maxv, Option.bind_some,
        Machine.BinOp.eval, Option.getD_some, Exp.val_of hy, OF.get, hpr]
      omega
    · trivial
  · trivial

theorem peak_prepCommit (h : Enc p κ s m) (_hL : m.loc = L) :
    PAgree (evalF κ .prepCommit s L) (exec (Stm.compile p κ .prepCommit) m)
      (max m.peak (pkF κ .prepCommit s L)) := by
  simp only [evalF]
  split
  · simp only [PAgree, Stm.compile, st1, exec, Out.bind, Machine.Expr.eval, h.ocap, zero_lt_one,
      ↓reduceIte, State.write, State.bump, Machine.Expr.maxv, zero_le, sup_of_le_left,
      Machine.Expr.cost, Nat.reduceAdd, arr_eq_iff, Slot.opt.injEq, reduceCtorEq, pkF]
  · trivial

theorem peak_jobSet (h : Enc p κ s m) (hL : m.loc = L) (x y z t a b c d : Exp) :
    PAgree (evalF κ (.jobSet x y z t a b c d) s L) (exec (Stm.compile p κ (.jobSet x y z t a b c
      d)) m)
      (max m.peak (pkF κ (.jobSet x y z t a b c d) s L)) := by
  simp only [evalF]
  split
  · next vx vy vz vt va vb vc vd hv =>
    have hv' := hv
    simp only [evList_cons_some] at hv'
    obtain ⟨hvx, hvy, hvz, hvt, hva, hvb, hvc, hvd, -⟩ := hv'
    split
    · next pc hpc =>
        have hargs : Machine.evalList m ([x, y, z, t, a, b, c, d].map (Exp.compile p κ)) = some
          [vx, vy, vz, vt, va, vb, vc, vd] :=
          evList_compile h hL [x, y, z, t, a, b, c, d] (by
            simp only [evList, List.mapM_cons, hvx, hvy, hvz, hvt, hva, hvb, hvc, hvd,
              List.mapM_nil, Option.pure_def, Option.bind_eq_bind, Option.bind_some])
        have hmx := maxvList_compile h hL [x, y, z, t, a, b, c, d] (vs := [vx, vy, vz, vt, va,
          vb, vc, vd]) (by
            simp only [evList, List.mapM_cons, hvx, hvy, hvz, hvt, hva, hvb, hvc, hvd,
              List.mapM_nil, Option.pure_def, Option.bind_eq_bind, Option.bind_some])
        simp only [Stm.compile, exec, hargs]
        generalize hm0 : (m.bump (Machine.maxvList m (List.map (Exp.compile p κ) [x, y, z, t, a,
          b, c, d]))).enter ["x", "y", "z", "t", "a", "b", "c", "d"] [vx, vy, vz, vt, va, vb,
            vc, vd] = m0
        have hc0 : ∀ o, m0.cap (arrO p o) = 1 := by intro o; rw [← hm0]; exact h.ocap o
        have hl0 : m0.loc "x" = vx ∧ m0.loc "y" = vy ∧ m0.loc "z" = vz ∧ m0.loc "t" = vt ∧
            m0.loc "a" = va ∧ m0.loc "b" = vb ∧ m0.loc "c" = vc ∧ m0.loc "d" = vd := by
          rw [← hm0]; simp only [State.enter, State.bump, Machine.maxvList, List.map_cons,
              List.map_nil, List.foldr_cons, List.foldr_nil, zero_le,
              sup_of_le_left, State.setLocs, State.upd, String.reduceEq,
              ↓reduceIte, and_self]
        have hp0 : m0.peak = max m.peak (pkList κ s L [x, y, z, t, a, b, c, d]) := by
          rw [← hm0, ← hmx]; rfl
        simp only [st1, exec, Machine.Out.bind, Machine.Expr.eval,
          hc0, hl0, Nat.zero_lt_one, ite_true, st_write_cap, st_write_loc, st_bump_cap, st_bump_loc,
          Machine.Expr.maxv]
        simp only [PAgree, pkF, st_leave_peak, st_write_peak, st_bump_peak, hp0]
        apply le_antisymm
        all_goals
          simp only [max_le_iff]
          repeat' apply And.intro
        all_goals simp only [le_max_iff, le_refl, true_or, or_true, Nat.zero_le, Exp.le_pkList
          (κ := κ) (s := s) (L := L) (es := [x, y, z, t, a, b, c, d]) (by simp) hvx,
            Exp.le_pkList (κ := κ) (s := s) (L := L) (es := [x, y, z, t, a, b, c, d]) (by simp)
              hvy, Exp.le_pkList (κ := κ) (s := s) (L := L) (es := [x, y, z, t, a, b, c, d]) (by
                simp) hvz, Exp.le_pkList (κ := κ) (s := s) (L := L) (es := [x, y, z, t, a, b, c,
                  d]) (by simp) hvt, Exp.le_pkList (κ := κ) (s := s) (L := L) (es := [x, y, z,
                    t, a, b, c, d]) (by simp) hva, Exp.le_pkList (κ := κ) (s := s) (L := L) (es
                      := [x, y, z, t, a, b, c, d]) (by simp) hvb, Exp.le_pkList (κ := κ) (s :=
                        s) (L := L) (es := [x, y, z, t, a, b, c, d]) (by simp) hvc,
                          Exp.le_pkList (κ := κ) (s := s) (L := L) (es := [x, y, z, t, a, b, c,
                            d]) (by simp) hvd]
    · trivial
  · trivial

theorem peak_jobClear (h : Enc p κ s m) (_hL : m.loc = L) :
    PAgree (evalF κ .jobClear s L) (exec (Stm.compile p κ .jobClear) m)
      (max m.peak (pkF κ .jobClear s L)) := by
  simp only [PAgree, evalF, Stm.compile, st1, exec, Out.bind, Machine.Expr.eval, h.ocap,
      zero_lt_one, ↓reduceIte, State.write, State.bump, Machine.Expr.maxv, zero_le,
      sup_of_le_left, Machine.Expr.cost, Nat.reduceAdd, arr_eq_iff, Slot.opt.injEq,
      reduceCtorEq, pkF]

theorem peak_pcSet (h : Enc p κ s m) (hL : m.loc = L) (t a b c d : Exp) :
    PAgree (evalF κ (.pcSet t a b c d) s L) (exec (Stm.compile p κ (.pcSet t a b c d)) m)
      (max m.peak (pkF κ (.pcSet t a b c d) s L)) := by
  simp only [evalF]
  split
  · next jb vt va vb vc vd hj hv =>
    have hv' := hv
    simp only [evList_cons_some] at hv'
    obtain ⟨hvt, hva, hvb, hvc, hvd, -⟩ := hv'
    split
    · next pc hpc =>
        have hargs : Machine.evalList m ([t, a, b, c, d].map (Exp.compile p κ)) = some [vt, va,
          vb, vc, vd] :=
          evList_compile h hL [t, a, b, c, d] (by
            simp only [evList, List.mapM_cons, hvt, hva, hvb, hvc, hvd, List.mapM_nil,
              Option.pure_def, Option.bind_eq_bind, Option.bind_some])
        have hmx := maxvList_compile h hL [t, a, b, c, d] (vs := [vt, va, vb, vc, vd]) (by
          simp only [evList, List.mapM_cons, hvt, hva, hvb, hvc, hvd, List.mapM_nil,
            Option.pure_def, Option.bind_eq_bind, Option.bind_some])
        simp only [Stm.compile, exec, hargs]
        generalize hm0 : (m.bump (Machine.maxvList m (List.map (Exp.compile p κ) [t, a, b, c,
          d]))).enter ["t", "a", "b", "c", "d"] [vt, va, vb, vc, vd] = m0
        have hc0 : ∀ o, m0.cap (arrO p o) = 1 := by intro o; rw [← hm0]; exact h.ocap o
        have hl0 : m0.loc "t" = vt ∧
            m0.loc "a" = va ∧ m0.loc "b" = vb ∧ m0.loc "c" = vc ∧ m0.loc "d" = vd := by
          rw [← hm0]; simp only [State.enter, State.bump, Machine.maxvList, List.map_cons,
              List.map_nil, List.foldr_cons, List.foldr_nil, zero_le,
              sup_of_le_left, State.setLocs, State.upd, String.reduceEq,
              ↓reduceIte, and_self]
        have hp0 : m0.peak = max m.peak (pkList κ s L [t, a, b, c, d]) := by rw [← hm0, ← hmx]; rfl
        simp only [st1, exec, Machine.Out.bind, Machine.Expr.eval,
          hc0, hl0, Nat.zero_lt_one, ite_true, st_write_cap, st_write_loc, st_bump_cap, st_bump_loc,
          Machine.Expr.maxv]
        simp only [PAgree, pkF, st_leave_peak, st_write_peak, st_bump_peak, hp0]
        apply le_antisymm
        all_goals
          simp only [max_le_iff]
          repeat' apply And.intro
        all_goals simp only [le_max_iff, le_refl, true_or, or_true, Nat.zero_le, Exp.le_pkList
          (κ := κ) (s := s) (L := L) (es := [t, a, b, c, d]) (by simp) hvt, Exp.le_pkList (κ :=
            κ) (s := s) (L := L) (es := [t, a, b, c, d]) (by simp) hva, Exp.le_pkList (κ := κ)
              (s := s) (L := L) (es := [t, a, b, c, d]) (by simp) hvb, Exp.le_pkList (κ := κ) (s
                := s) (L := L) (es := [t, a, b, c, d]) (by simp) hvc, Exp.le_pkList (κ := κ) (s
                  := s) (L := L) (es := [t, a, b, c, d]) (by simp) hvd]
    · trivial
  · trivial

end special

/-! ### The simulation of the peak -/

/-- **The compiled code's peak is `pkF`**: when the source run ends normally or with a failed
guard, the compiled run ends with `peak = max m.peak (pkF κ c s L)`. -/
theorem sim_peak (c : Stm) : ∀ {s : Core} {L : Loc} {m : State}, Enc p κ s m → m.loc = L →
    PAgree (evalF κ c s L) (exec (c.compile p κ) m) (max m.peak (pkF κ c s L)) := by
  induction c with
  | skip => intro s L m h hL; simp only [PAgree, evalF, Stm.compile, exec, pkF, zero_le,
      sup_of_le_left]
  | assign x e =>
    intro s L m h hL
    simp only [evalF]
    cases he : e.ev κ s L with
    | none => trivial
    | some v =>
      simp only [Stm.compile, exec, Exp.ev_compile h hL e he, PAgree, pkF, st_setLoc_peak,
        st_bump_peak,
        Exp.maxv_compile h hL e he]
  | wr f i e =>
    intro s L m h hL
    simp only [evalF]
    cases hi : i.ev κ s L with
    | none => trivial
    | some j =>
      cases he : e.ev κ s L with
      | none => trivial
      | some v =>
        simp only
        cases hs : f.set κ s j v with
        | none => trivial
        | some s' =>
          have hj := Fld.set_lt hs h.sle
          simp only [Stm.compile, exec, Exp.ev_compile h hL i hi, Exp.ev_compile h hL e he]
          rw [ite_eq_left (by simp only [h.cap f]; exact hj)]
          simp only [PAgree, pkF, st_write_peak, st_bump_peak, Exp.maxv_compile h hL i hi,
            Exp.maxv_compile h hL e he]
          omega
  | push t x =>
    intro s L m h hL
    simp only [evalF]
    split
    · simp only [PAgree, Stm.compile, exec, Out.bind, Machine.Expr.eval, h.scap t,
        Nat.lt_one_iff, Option.bind_some, ↓reduceIte, h.smem t, State.setLoc, State.bump,
        Machine.Expr.maxv, Option.getD_some, zero_le, sup_of_le_right, Machine.Expr.cost,
        Nat.reduceAdd, State.upd, BinOp.eval, zero_lt_one, State.write, le_max_iff,
        or_self, sup_of_le_left, sup_le_iff, le_add_iff_nonneg_right,
        le_add_iff_nonneg_left, and_self, Nat.max_assoc, pkF]
    · trivial
  | seq c d ihc ihd =>
    intro s L m h hL
    have hs := sim (p := p) c h hL
    have hp := ihc h hL
    simp only [evalF, Stm.compile, exec, pkF]
    revert hs hp
    generalize evalF κ c s L = r
    generalize exec (c.compile p κ) m = o
    intro hs hp
    cases r with
    | ok s' L' n =>
      obtain ⟨h1, h2, h3, -⟩ := hs
      have hd := ihd h2 h3
      simp only [PAgree] at hp
      simp only [Res.bind, Machine.Out.bind, h1]
      revert hd
      generalize evalF κ d s' L' = r2
      generalize exec (d.compile p κ) o.st = o2
      intro hd
      cases r2 <;> simp only [PAgree, Res.addCost] at hd ⊢ <;> (rw [hd, hp]; omega)
    | fail s' L' n =>
      obtain ⟨h1, -, -, -⟩ := hs
      simp only [Res.bind, Machine.Out.bind, h1]; exact hp
    | bug => trivial
  | ite c t f iht ihf =>
    intro s L m h hL
    simp only [evalF]
    cases hc : c.ev κ s L with
    | none => trivial
    | some v =>
      simp only [Stm.compile, exec, Exp.ev_compile h hL c hc, Machine.Out.bind,
        pkF, Exp.val_of hc]
      by_cases hv : v ≠ 0
      · simp only [ite_eq_left hv]
        rw [← Exp.cost_compile p κ c]
        refine ((iht (L := L) (h.bump ((c.compile p κ).maxv m))
          (by simp only [State.bump, hL])).addCost _).congr ?_
        simp only [st_bump_peak, Exp.maxv_compile h hL c hc]; omega
      · simp only [ite_eq_right hv]
        rw [← Exp.cost_compile p κ c]
        refine ((ihf (L := L) (h.bump ((c.compile p κ).maxv m))
          (by simp only [State.bump, hL])).addCost _).congr ?_
        simp only [st_bump_peak, Exp.maxv_compile h hL c hc]; omega
  | loop x n b ihb =>
    intro s L m h hL
    simp only [evalF]
    cases hn : n.ev κ s L with
    | none => trivial
    | some k =>
      simp only [Stm.compile, exec, Exp.ev_compile h hL n hn, Machine.Out.bind,
        pkF, Exp.val_of hn]
      rw [← Exp.cost_compile p κ n]
      refine ((sim_peak_runFor (x := x) (fun s L m h hL => ihb h hL) k 0 s L _
        (h.bump ((n.compile p κ).maxv m)) (by simp only [State.bump, hL])).addCost _).congr ?_
      simp only [st_bump_peak, Exp.maxv_compile h hL n hn]; omega
  | call nm ps b rs args ds ihb =>
    intro s L m h hL
    simp only [evalF]
    cases ha : evList κ s L args with
    | none => trivial
    | some vs =>
      simp only [Stm.compile, exec, evList_compile h hL args ha, pkF, ha, Option.getD_some]
      have hb := ihb (s := s) (L := Machine.State.setLocs (fun _ => 0) ps vs)
        (m := (m.bump (Machine.maxvList m (args.map (Exp.compile p κ)))).enter ps vs)
        ((h.bump (Machine.maxvList m (args.map (Exp.compile p κ)))).congr rfl rfl) (by simp)
      revert hb
      generalize evalF κ b s (Machine.State.setLocs (fun _ => 0) ps vs) = r
      generalize exec (b.compile p κ) _ = o
      intro hb
      cases r with
      | ok s' L' n =>
        simp only [PAgree, st_enter_peak, st_bump_peak, maxvList_compile h hL args ha] at hb
        cases hst : o.status <;> simp only [PAgree, st_leave_peak] at hb ⊢ <;> (rw [hb]; omega)
      | fail s' L' n =>
        simp only [PAgree, st_enter_peak, st_bump_peak, maxvList_compile h hL args ha] at hb
        cases hst : o.status <;> simp only [PAgree, st_leave_peak] at hb ⊢ <;> (rw [hb]; omega)
      | bug => trivial
  | fail => intro s L m h hL; simp only [PAgree, evalF, Stm.compile, exec, pkF, zero_le,
      sup_of_le_left]
  | bug => intro s L m h hL; trivial
  | «catch» c hd ihc ihh =>
    intro s L m h hL
    have hs := sim (p := p) c h hL
    have hp := ihc h hL
    simp only [evalF, Stm.compile, exec, pkF]
    revert hs hp
    generalize evalF κ c s L = r
    generalize exec (c.compile p κ) m = o
    intro hs hp
    cases r with
    | ok s' L' n =>
      obtain ⟨h1, -, -, -⟩ := hs
      simp only [h1, PAgree] at hp ⊢; exact hp
    | fail s' L' n =>
      obtain ⟨h1, h2, h3, -⟩ := hs
      have hh := ihh h2 h3
      simp only [PAgree] at hp
      simp only [h1]
      revert hh
      generalize evalF κ hd s' L' = r2
      generalize exec (hd.compile p κ) o.st = o2
      intro hh
      cases r2 <;> simp only [PAgree, Res.addCost] at hh ⊢ <;> (rw [hh, hp]; omega)
    | bug => trivial
  | lwr k b i j e => intro s L m h hL; exact peak_lwr h hL k b i j e
  | lgrow k i a b => intro s L m h hL; exact peak_lgrow h hL k i a b
  | lshrink k i => intro s L m h hL; exact peak_lshrink h hL k i
  | lclear k i => intro s L m h hL; exact peak_lclear h hL k i
  | pwr c j e => intro s L m h hL; exact peak_pwr h hL c j e
  | rowReset c => intro s L m h hL; exact peak_rowReset h hL c
  | prepInit c b => intro s L m h hL; exact peak_prepInit h hL c b
  | prepSet hh b t => intro s L m h hL; exact peak_prepSet h hL hh b t
  | prepPath j e => intro s L m h hL; exact peak_prepPath h hL j e
  | prepCommit => intro s L m h hL; exact peak_prepCommit h hL
  | jobSet x y z t a b c d => intro s L m h hL; exact peak_jobSet h hL x y z t a b c d
  | jobClear => intro s L m h hL; exact peak_jobClear h hL
  | pcSet t a b c d => intro s L m h hL; exact peak_pcSet h hL t a b c d

end OrderMaintenance.Impl
