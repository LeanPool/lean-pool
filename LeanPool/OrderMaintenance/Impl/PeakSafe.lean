/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.PeakW


/-!
# Theorem W, option (A), stage A2: statements whose peak follows from their syntax

`Stm.Safe Γ W c` says that every expression of `c` (and of the procedures it calls) has no shift
and a peak width (`Exp.wp`) at most `W`, and that every value `c` stores is no wider than its
destination: `Γ x` for a local `x`, `K` for the core (`KH` for the handle field). Calls are
checked with every local of the callee at width `K`.

**`Stm.safe_run`**: from a state with the invariant `Gd` (an encoding, small stored values
`VB`, and every local `x` below `2^(Γ x)`), a safe statement that does not hit a bug computes
nothing at or above `2^W` (`pkF < 2^W`) and ends, normally or with a failed guard, in a state
with `Gd`. Most core procedures are safe; the others are composed from safe pieces with the
rules of `PeakHP.lean`.

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg BinOp UnOp State)

variable {K KH : Nat} {κ : Caps}

/-- **The invariant of stage A2**: an encoding exists, the stored values are small, and every
local `x` is below `2^(Γ x)`. -/
structure Gd (K KH : Nat) (κ : Caps) (Γ : Reg → Nat) (s : Core) (L : Loc) : Prop where
  enc : EncOK κ s
  vb : VB K KH κ s
  loc : ∀ x, L x < 2 ^ Γ x

/-- An expression without shifts whose peak width is at most `W`. -/
def Exp.OK (Γ : Reg → Nat) (K KH W : Nat) (e : Exp) : Prop := e.noShl = true ∧ e.wq Γ K KH K ≤ W

/-- **A statement whose peak follows from its syntax.** -/
def Stm.Safe (K KH : Nat) (Γ : Reg → Nat) (W : Nat) : Stm → Prop
  | .skip => True
  | .assign x e => e.OK Γ K KH W ∧ e.vw Γ K KH K ≤ Γ x
  | .wr f i e => i.OK Γ K KH W ∧ e.OK Γ K KH W ∧ e.vw Γ K KH K ≤ f.wd K KH
  | .push _ x => K ≤ Γ x
  | .seq c d => c.Safe K KH Γ W ∧ d.Safe K KH Γ W
  | .ite c t f => c.OK Γ K KH W ∧ t.Safe K KH Γ W ∧ f.Safe K KH Γ W
  | .loop x n b => n.OK Γ K KH W ∧ n.vw Γ K KH K ≤ Γ x ∧ b.Safe K KH Γ W
  | .call _ _ b _ args ds =>
    (∀ e ∈ args, e.OK Γ K KH W ∧ e.vw Γ K KH K ≤ K) ∧ b.Safe K KH (fun _ => K) W ∧ ∀ d ∈ ds, K ≤ Γ d
  | .fail => True
  | .bug => True
  | .catch c h => c.Safe K KH Γ W ∧ h.Safe K KH Γ W
  | .lwr _ _ i j e => i.OK Γ K KH W ∧ j.OK Γ K KH W ∧ e.OK Γ K KH W ∧ e.vw Γ K KH K ≤ K
  | .lgrow _ i a b => i.OK Γ K KH W ∧ a.OK Γ K KH W ∧ b.OK Γ K KH W ∧ a.vw Γ K KH K ≤ K ∧ b.vw Γ
    K KH K ≤ K
  | .lshrink _ i => i.OK Γ K KH W
  | .lclear _ i => i.OK Γ K KH W
  | .pwr c j e => c.OK Γ K KH W ∧ j.OK Γ K KH W ∧ e.OK Γ K KH W ∧ e.vw Γ K KH K ≤ K
  | .rowReset _ => True
  | .prepInit c b => c.OK Γ K KH W ∧ b.OK Γ K KH W ∧ c.vw Γ K KH K ≤ K ∧ b.vw Γ K KH K ≤ K
  | .prepSet h b t => ∀ e ∈ [h, b, t], e.OK Γ K KH W ∧ e.vw Γ K KH K ≤ K
  | .prepPath j e => j.OK Γ K KH W ∧ e.OK Γ K KH W ∧ e.vw Γ K KH K ≤ K
  | .prepCommit => True
  | .jobSet x y z t a b c d => ∀ e ∈ [x, y, z, t, a, b, c, d], e.OK Γ K KH W ∧ e.vw Γ K KH K ≤ K
  | .jobClear => True
  | .pcSet t a b c d => ∀ e ∈ [t, a, b, c, d], e.OK Γ K KH W ∧ e.vw Γ K KH K ≤ K

/-! ### Expressions under the invariant -/

section exps
variable {Γ : Reg → Nat} {s : Core} {L : Loc} {W : Nat}

theorem Gd.memW (hG : Gd K KH κ Γ s L) (hC : CapsW K κ) : MemW K KH κ s := hG.vb.memW hG.enc hC

theorem Gd.pk (hG : Gd K KH κ Γ s L) (hC : CapsW K κ) {e : Exp} (he : e.OK Γ K KH W) {v : Nat}
    (hv : e.ev κ s L = some v) : e.pk κ s L < 2 ^ W :=
  lt_of_lt_of_le (Exp.wq_sound (hG.memW hC) hC hG.loc e (Exp.shOK_of_noShl κ s L K e he.1) hv)
    (Nat.pow_le_pow_right (by norm_num) he.2)

theorem Gd.val (hG : Gd K KH κ Γ s L) (hC : CapsW K κ) {e : Exp} (he : e.OK Γ K KH W) {v : Nat}
    (hv : e.ev κ s L = some v) : v < 2 ^ e.vw Γ K KH K :=
  Exp.vw_sound (hG.memW hC) hC hG.loc e (Exp.shOK_of_noShl κ s L K e he.1) hv

theorem Gd.valW (hG : Gd K KH κ Γ s L) (hC : CapsW K κ) {e : Exp} (he : e.OK Γ K KH W) {w : Nat}
    (hw : e.vw Γ K KH K ≤ w) {v : Nat} (hv : e.ev κ s L = some v) : v < 2 ^ w :=
  lt_of_lt_of_le (hG.val hC he hv) (Nat.pow_le_pow_right (by norm_num) hw)

theorem Gd.valN (hG : Gd K KH κ Γ s L) (hC : CapsW K κ) {e : Exp} (he : e.noShl = true) {w : Nat}
    (hw : e.vw Γ K KH K ≤ w) {v : Nat} (hv : e.ev κ s L = some v) : v < 2 ^ w :=
  lt_of_lt_of_le (Exp.vw_sound (hG.memW hC) hC hG.loc e (Exp.shOK_of_noShl κ s L K e he) hv)
    (Nat.pow_le_pow_right (by norm_num) hw)

theorem Gd.pkList (hG : Gd K KH κ Γ s L) (hC : CapsW K κ) {es : List Exp} (h : ∀ e ∈ es, e.OK Γ
  K KH W)
    {vs : List Nat} (hv : evList κ s L es = some vs) : pkList κ s L es < 2 ^ W :=
  pkList_lt' (S := K) (hG.memW hC) hC hG.loc (fun e he => ⟨Exp.shOK_of_noShl κ s L K e (h e
    he).1, (h e he).2⟩) hv

theorem Gd.vals (hG : Gd K KH κ Γ s L) (hC : CapsW K κ) :
    ∀ {es : List Exp}, (∀ e ∈ es, e.OK Γ K KH W ∧ e.vw Γ K KH K ≤ K) →
      ∀ {vs : List Nat}, evList κ s L es = some vs → ∀ v ∈ vs, v < 2 ^ K
  | [], _, vs, hv, v, hm => by
    simp only [evList, List.mapM_nil, Option.pure_def, Option.some.injEq, List.nil_eq] at hv
    subst hv
    cases hm
  | e :: es, h, vs, hv, v, hm => by
    simp only [evList, List.mapM_cons] at hv
    cases he : e.ev κ s L with
    | none => simp only [he, Option.pure_def, Option.bind_eq_bind, Option.bind_none,
        reduceCtorEq] at hv
    | some a =>
      cases hes : es.mapM (·.ev κ s L) with
      | none => simp only [he, hes, Option.pure_def, Option.bind_eq_bind, Option.bind_none,
          Option.bind_fun_none, reduceCtorEq] at hv
      | some ws =>
        simp only [he, hes, Option.pure_def, Option.bind_eq_bind, Option.bind_some,
            Option.some.injEq] at hv
        subst hv
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hG.valW hC (h e (by simp)).1 (h e (by simp)).2 he
        · exact Gd.vals hG hC (es := es) (fun e' he' => h e' (by
          simp only [List.mem_cons, he', or_true])) hes v hm

end exps

/-! ### Locals -/

theorem upd_lt {Γ : Reg → Nat} {L : Loc} (hL : ∀ x, L x < 2 ^ Γ x) {y : Reg} {v : Nat} (hv : v <
  2 ^ Γ y) :
    ∀ x, Machine.State.upd L y v x < 2 ^ Γ x := by
  intro x; unfold Machine.State.upd; split
  · next h => subst h; exact hv
  · exact hL x

theorem setLocs_lt {Γ : Reg → Nat} {K : Nat} :
    ∀ {L : Loc} {xs : List Reg} {vs : List Nat}, (∀ x, L x < 2 ^ Γ x) → (∀ x ∈ xs, K ≤ Γ x) →
      (∀ v ∈ vs, v < 2 ^ K) → ∀ x, Machine.State.setLocs L xs vs x < 2 ^ Γ x
  | L, [], vs, hL, _, _ => by cases vs <;> exact hL
  | L, _ :: _, [], hL, _, _ => hL
  | L, y :: xs, v :: vs, hL, hx, hv => by
    simp only [Machine.State.setLocs]
    refine setLocs_lt (upd_lt hL ?_) (fun x hx' => hx x (by
      simp only [List.mem_cons, hx', or_true])) (fun v hv' => hv v (by
      simp only [List.mem_cons, hv', or_true]))
    exact lt_of_lt_of_le (hv v (by simp)) (Nat.pow_le_pow_right (by norm_num) (hx y (by simp)))

theorem zero_locs (Γ : Reg → Nat) : ∀ x, (fun _ => 0 : Loc) x < 2 ^ Γ x := fun _ =>
  Nat.two_pow_pos _

theorem pow_mono_lt {x a b : Nat} (h : x < 2 ^ a) (hab : a ≤ b) : x < 2 ^ b :=
  lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hab)

/-! ### The theorem -/

section run
variable {Γ : Reg → Nat} {W : Nat}

/-- What `safe_run` proves of a statement at one state. -/
def SafeAt (K KH : Nat) (κ : Caps) (Γ : Reg → Nat) (W : Nat) (c : Stm) (s : Core) (L : Loc) :
  Prop :=
  pkF κ c s L < 2 ^ W ∧ (∀ s' L' n, evalF κ c s L = .ok s' L' n → Gd K KH κ Γ s' L') ∧
    (∀ s' L' n, evalF κ c s L = .fail s' L' n → Gd K KH κ Γ s' L')

theorem lt_pow_of_lt_K (hW : K ≤ W) {x : Nat} (h : x < 2 ^ K) : x < 2 ^ W := pow_mono_lt h hW

/-- The loop of a safe statement. -/
theorem safe_loop {b : Stm} {x : Reg} {N : Nat} (hC : CapsW K κ) (hN : N ≤ 2 ^ Γ x)
    (ih : ∀ s L, Gd K KH κ Γ s L → evalF κ b s L ≠ .bug → SafeAt K KH κ Γ W b s L) :
    ∀ m k s L, Gd K KH κ Γ s L → k + m ≤ N → runForF (evalF κ b) x k m s L ≠ .bug →
      pkFor (evalF κ b) (pkF κ b) x k m s L < 2 ^ W ∧
      (∀ s' L' n, runForF (evalF κ b) x k m s L = .ok s' L' n → Gd K KH κ Γ s' L') ∧
      (∀ s' L' n, runForF (evalF κ b) x k m s L = .fail s' L' n → Gd K KH κ Γ s' L')
  | 0, k, s, L, hG, _, _ => by
    refine ⟨by simp only [pkFor, Nat.ofNat_pos, pow_pos], fun s' L' n h => ?_, fun s' L' n h => ?_⟩
    · simp only [runForF, Res.ok.injEq] at h; obtain ⟨rfl, rfl, -⟩ := h; exact hG
    · simp only [runForF, reduceCtorEq] at h
  | m + 1, k, s, L, hG, hk, hnb => by
    have hG0 : Gd K KH κ Γ s (Machine.State.upd L x k) :=
      ⟨hG.enc, hG.vb, upd_lt hG.loc (by omega)⟩
    simp only [runForF] at hnb ⊢
    simp only [pkFor]
    cases hb : evalF κ b s (Machine.State.upd L x k) with
    | bug => simp only [Res.bind, Res.addCost, hb, ne_eq, not_true_eq_false] at hnb
    | fail s1 L1 n1 =>
      obtain ⟨h1, -, h3⟩ := ih s _ hG0 (by rw [hb]; simp)
      refine ⟨max_lt h1 (by simp), fun s' L' n h => ?_, fun s' L' n h => ?_⟩
      · simp only [Res.bind, Res.addCost, reduceCtorEq] at h
      · simp only [Res.bind, Res.addCost, Res.fail.injEq] at h
        obtain ⟨rfl, rfl, -⟩ := h
        exact h3 _ _ _ hb
    | ok s1 L1 n1 =>
      obtain ⟨h1, h2, -⟩ := ih s _ hG0 (by rw [hb]; simp)
      have hG1 := h2 _ _ _ hb
      have hnb' : runForF (evalF κ b) x (k + 1) m s1 L1 ≠ .bug := by
        intro e; apply hnb; simp only [Res.bind, Res.addCost, hb, e]
      obtain ⟨p1, p2, p3⟩ := safe_loop hC hN ih m (k + 1) s1 L1 hG1 (by omega) hnb'
      refine ⟨max_lt h1 p1, fun s' L' n h => ?_, fun s' L' n h => ?_⟩
      · simp only [ Res.addCost, Res.bind] at h
        revert h; cases hr : runForF (evalF κ b) x (k + 1) m s1 L1 <;> simp only [Res.ok.injEq,
            and_imp,
            reduceCtorEq,
            IsEmpty.forall_iff]
        intro e1 e2 _; subst e1; subst e2; exact p2 _ _ _ hr
      · simp only [ Res.addCost, Res.bind] at h
        revert h; cases hr : runForF (evalF κ b) x (k + 1) m s1 L1 <;> simp only [reduceCtorEq,
            IsEmpty.forall_iff,
            Res.fail.injEq,
            and_imp]
        intro e1 e2 _; subst e1; subst e2; exact p3 _ _ _ hr

theorem two_le_pow (hK : 3 ≤ K) : 2 ≤ 2 ^ K :=
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem rowPk_lt {s : Core} (hE : EncOK κ s) (hC : CapsW K κ) : rowPk s < 2 ^ K := by
  have h1 : s.P.H + 1 < 2 ^ K := by rw [← hE.pwH]; exact hC.pw
  have h16 := hC.sixteen
  simp only [rowPk, PF.idx]
  exact max_lt (max_lt (max_lt (by omega) (by omega)) (by omega)) h1

theorem stride_le (κ : Caps) (k : LK) : k.stride κ.lcap ≤ κ.lcap k := by
  cases k <;> simp only [LK.stride, Std.le_refl, zero_le]

theorem lidx_lt (hC : CapsW K κ) {k : LK} {x y : Nat} (hx : x < κ.lrec k) (hy : y < κ.lcap k) :
    x * k.stride κ.lcap + y < 2 ^ K := by
  cases k with
  | freeG =>
    simp only [LK.stride, mul_zero, zero_add]
    exact lt_of_lt_of_le hy (le_of_lt (hC.lcap _))
  | _ => exact lt_trans (lt_mul_add hx hy) (hC.lst _)

/-- Safety of the `assign` constructor at one state. -/
private theorem safeAt_assign (hC : CapsW K κ)
    (x : Reg)
    (e : Exp)
    {Γ : Reg → Nat} {s : Core} {L : Loc}
    (hS : (Stm.assign x e).Safe K KH Γ W) (hG : Gd K KH κ Γ s L)
    (hnb : evalF κ (Stm.assign x e) s L ≠ .bug) :
    SafeAt K KH κ Γ W (Stm.assign x e) s L := by
  obtain ⟨he, hw⟩ := hS
  cases hv : e.ev κ s L with
  | none => simp only [evalF, hv, ne_eq, not_true_eq_false] at hnb
  | some v =>
    refine ⟨hG.pk hC he hv, fun s' L' n h => ?_, fun _ _ _ h => by
      simp only [evalF, hv, reduceCtorEq] at h⟩
    simp only [evalF, hv, Res.ok.injEq] at h; obtain ⟨rfl, rfl, -⟩ := h
    exact ⟨hG.enc, hG.vb, upd_lt hG.loc (hG.valW hC he hw hv)⟩

/-- Safety of the `wr` constructor at one state. -/
private theorem safeAt_wr (hC : CapsW K κ)
    (f : Fld)
    (i e : Exp)
    {Γ : Reg → Nat} {s : Core} {L : Loc}
    (hS : (Stm.wr f i e).Safe K KH Γ W) (hG : Gd K KH κ Γ s L)
    (hnb : evalF κ (Stm.wr f i e) s L ≠ .bug) :
    SafeAt K KH κ Γ W (Stm.wr f i e) s L := by
  obtain ⟨hi, he, hw⟩ := hS
  cases hiv : i.ev κ s L with
  | none => simp only [evalF, hiv, ne_eq, not_true_eq_false] at hnb
  | some j =>
    cases hv : e.ev κ s L with
    | none => simp only [evalF, hiv, hv, ne_eq, not_true_eq_false] at hnb
    | some v =>
      refine ⟨max_lt (hG.pk hC hi hiv) (hG.pk hC he hv), fun s' L' n h => ?_, fun _ _ _ h => ?_⟩
      · have h' := h
        simp only [evalF, hiv, hv] at h
        split at h
        · next s1 hs1 =>
          simp only [Res.ok.injEq] at h; obtain ⟨rfl, rfl, -⟩ := h
          exact ⟨hG.enc.of_ok h', hG.vb.set hs1 (hG.valW hC he hw hv), hG.loc⟩
        · cases h
      · simp only [evalF, hiv, hv] at h; split at h <;> cases h

/-- Safety of the `push` constructor at one state. -/
private theorem safeAt_push (hC : CapsW K κ) (hW : K ≤ W)
    (t : Tbl)
    (x : Reg)
    {Γ : Reg → Nat} {s : Core} {L : Loc}
    (hS : (Stm.push t x).Safe K KH Γ W) (hG : Gd K KH κ Γ s L)
    (hnb : evalF κ (Stm.push t x) s L ≠ .bug) :
    SafeAt K KH κ Γ W (Stm.push t x) s L := by
  by_cases hlt : t.size s < κ.tbl t
  · refine ⟨?_, fun s' L' n h => ?_, fun _ _ _ h => ?_⟩
    · simp only [pkF]; exact lt_pow_of_lt_K hW (by have := hC.tbl t; omega)
    · have h' := h
      simp only [evalF, ite_eq_left hlt] at h; cases h
      exact ⟨hG.enc.of_ok h', hG.vb.push t,
        upd_lt hG.loc (pow_mono_lt (lt_trans hlt (hC.tbl t)) hS)⟩
    · simp only [evalF, ite_eq_left hlt] at h; cases h
  · simp only [evalF, hlt, ↓reduceIte, ne_eq, not_true_eq_false] at hnb

/-- Safety of the `seq` constructor at one state. -/
private theorem safeAt_seq
    (c d : Stm)
    (ihc : ∀ {Γ : Reg → Nat} {s : Core} {L : Loc},
      c.Safe K KH Γ W → Gd K KH κ Γ s L → evalF κ c s L ≠ .bug →
        SafeAt K KH κ Γ W c s L)
    (ihd : ∀ {Γ : Reg → Nat} {s : Core} {L : Loc},
      d.Safe K KH Γ W → Gd K KH κ Γ s L → evalF κ d s L ≠ .bug →
        SafeAt K KH κ Γ W d s L)
    {Γ : Reg → Nat} {s : Core} {L : Loc}
    (hS : (Stm.seq c d).Safe K KH Γ W) (hG : Gd K KH κ Γ s L)
    (hnb : evalF κ (Stm.seq c d) s L ≠ .bug) :
    SafeAt K KH κ Γ W (Stm.seq c d) s L := by
  obtain ⟨hc, hd⟩ := hS
  cases h1 : evalF κ c s L with
  | bug => simp only [evalF, Res.bind, h1, ne_eq, not_true_eq_false] at hnb
  | fail s1 L1 n1 =>
    obtain ⟨p1, -, p3⟩ := ihc hc hG (by rw [h1]; simp)
    refine ⟨by rw [pkF_seq_fail h1]; exact p1, fun s' L' n h => by
      simp only [evalF, Res.bind, h1, reduceCtorEq] at h,
      fun s' L' n h => ?_⟩
    simp only [evalF, Res.bind, h1, Res.fail.injEq] at h
    obtain ⟨rfl, rfl, -⟩ := h
    exact p3 _ _ _ h1
  | ok s1 L1 n1 =>
    obtain ⟨p1, p2, -⟩ := ihc hc hG (by rw [h1]; simp)
    have hG1 := p2 _ _ _ h1
    have hnb2 : evalF κ d s1 L1 ≠ .bug := by
      intro e; apply hnb; simp only [evalF, Res.bind, h1, Res.addCost, e]
    obtain ⟨q1, q2, q3⟩ := ihd hd hG1 hnb2
    refine ⟨by rw [pkF_seq_ok h1]; exact max_lt p1 q1, fun s' L' n h => ?_, fun s' L' n h => ?_⟩
    · simp only [evalF, h1, Res.bind] at h
      revert h; cases h2 : evalF κ d s1 L1 <;> simp only [Res.addCost, Res.ok.injEq, and_imp,
          reduceCtorEq, IsEmpty.forall_iff]
      intro e1 e2 _; subst e1; subst e2; exact q2 _ _ _ h2
    · simp only [evalF, h1, Res.bind] at h
      revert h; cases h2 : evalF κ d s1 L1 <;> simp only [Res.addCost, reduceCtorEq,
          IsEmpty.forall_iff, Res.fail.injEq,
          and_imp]
      intro e1 e2 _; subst e1; subst e2; exact q3 _ _ _ h2

/-- Safety of the `ite` constructor at one state. -/
private theorem safeAt_ite (hC : CapsW K κ)
    (c : Exp)
    (t f : Stm)
    (iht : ∀ {Γ : Reg → Nat} {s : Core} {L : Loc},
      t.Safe K KH Γ W → Gd K KH κ Γ s L → evalF κ t s L ≠ .bug →
        SafeAt K KH κ Γ W t s L)
    (ihf : ∀ {Γ : Reg → Nat} {s : Core} {L : Loc},
      f.Safe K KH Γ W → Gd K KH κ Γ s L → evalF κ f s L ≠ .bug →
        SafeAt K KH κ Γ W f s L)
    {Γ : Reg → Nat} {s : Core} {L : Loc}
    (hS : (Stm.ite c t f).Safe K KH Γ W) (hG : Gd K KH κ Γ s L)
    (hnb : evalF κ (Stm.ite c t f) s L ≠ .bug) :
    SafeAt K KH κ Γ W (Stm.ite c t f) s L := by
  obtain ⟨hc, ht, hf⟩ := hS
  cases hv : c.ev κ s L with
  | none => simp only [evalF, hv, ne_eq, not_true_eq_false] at hnb
  | some v =>
    unfold SafeAt
    rw [pkF_ite hv]
    by_cases h0 : v ≠ 0
    · have hnb' : evalF κ t s L ≠ .bug := by
        intro e; apply hnb; simp only [evalF, hv, Res.addCost, ne_eq, h0, not_false_eq_true,
            ↓reduceIte, e]
      obtain ⟨p1, p2, p3⟩ := iht ht hG hnb'
      refine ⟨by rw [ite_eq_left h0]; exact max_lt (hG.pk hC hc hv) p1, fun s' L' n h => ?_,
        fun s' L' n h => ?_⟩
      · simp only [evalF, hv, ite_eq_left h0] at h
        revert h; cases h2 : evalF κ t s L <;> simp only [Res.addCost, Res.ok.injEq, and_imp,
            reduceCtorEq, IsEmpty.forall_iff]
        intro e1 e2 _; subst e1; subst e2; exact p2 _ _ _ h2
      · simp only [evalF, hv, ite_eq_left h0] at h
        revert h; cases h2 : evalF κ t s L <;> simp only [Res.addCost, reduceCtorEq,
            IsEmpty.forall_iff, Res.fail.injEq,
            and_imp]
        intro e1 e2 _; subst e1; subst e2; exact p3 _ _ _ h2
    · have hnb' : evalF κ f s L ≠ .bug := by
        intro e; apply hnb; simp only [evalF, hv, Res.addCost, h0, ↓reduceIte, e]
      obtain ⟨p1, p2, p3⟩ := ihf hf hG hnb'
      refine ⟨by rw [ite_eq_right h0]; exact max_lt (hG.pk hC hc hv) p1, fun s' L' n h => ?_,
        fun s' L' n h => ?_⟩
      · simp only [evalF, hv, ite_eq_right h0] at h
        revert h; cases h2 : evalF κ f s L <;> simp only [Res.addCost, Res.ok.injEq, and_imp,
            reduceCtorEq, IsEmpty.forall_iff]
        intro e1 e2 _; subst e1; subst e2; exact p2 _ _ _ h2
      · simp only [evalF, hv, ite_eq_right h0] at h
        revert h; cases h2 : evalF κ f s L <;> simp only [Res.addCost, reduceCtorEq,
            IsEmpty.forall_iff, Res.fail.injEq,
            and_imp]
        intro e1 e2 _; subst e1; subst e2; exact p3 _ _ _ h2

/-- Safety of the `loop` constructor at one state. -/
private theorem safeAt_loop (hC : CapsW K κ)
    (x : Reg)
    (n : Exp)
    (b : Stm)
    (ihb : ∀ {Γ : Reg → Nat} {s : Core} {L : Loc},
      b.Safe K KH Γ W → Gd K KH κ Γ s L → evalF κ b s L ≠ .bug →
        SafeAt K KH κ Γ W b s L)
    {Γ : Reg → Nat} {s : Core} {L : Loc}
    (hS : (Stm.loop x n b).Safe K KH Γ W) (hG : Gd K KH κ Γ s L)
    (hnb : evalF κ (Stm.loop x n b) s L ≠ .bug) :
    SafeAt K KH κ Γ W (Stm.loop x n b) s L := by
  obtain ⟨hn, hw, hb⟩ := hS
  cases hv : n.ev κ s L with
  | none => simp only [evalF, hv, ne_eq, not_true_eq_false] at hnb
  | some N =>
    have hN : N ≤ 2 ^ Γ x := le_of_lt (hG.valW hC hn hw hv)
    have hnb' : runForF (evalF κ b) x 0 N s L ≠ .bug := by
      intro e; apply hnb; simp only [evalF, hv, Res.addCost, e]
    obtain ⟨p1, p2, p3⟩ := safe_loop hC hN (fun s L hG hnb => ihb hb hG hnb) N 0 s L hG (by
      omega) hnb'
    refine ⟨?_, fun s' L' n h => ?_, fun s' L' n h => ?_⟩
    · simp only [pkF, Exp.val_of hv]; exact max_lt (hG.pk hC hn hv) p1
    · simp only [evalF, hv] at h
      revert h; cases h2 : runForF (evalF κ b) x 0 N s L <;> simp only [Res.addCost,
          Res.ok.injEq, and_imp,
          reduceCtorEq,
          IsEmpty.forall_iff]
      intro e1 e2 _; subst e1; subst e2; exact p2 _ _ _ h2
    · simp only [evalF, hv] at h
      revert h; cases h2 : runForF (evalF κ b) x 0 N s L <;> simp only [Res.addCost,
          reduceCtorEq,
          IsEmpty.forall_iff,
          Res.fail.injEq, and_imp]
      intro e1 e2 _; subst e1; subst e2; exact p3 _ _ _ h2

/-- Safety of the `call` constructor at one state. -/
private theorem safeAt_call (hC : CapsW K κ)
    (nm : String)
    (ps : List Reg)
    (b : Stm)
    (rs : List Reg)
    (args : List Exp)
    (ds : List Reg)
    (ihb : ∀ {Γ : Reg → Nat} {s : Core} {L : Loc},
      b.Safe K KH Γ W → Gd K KH κ Γ s L → evalF κ b s L ≠ .bug →
        SafeAt K KH κ Γ W b s L)
    {Γ : Reg → Nat} {s : Core} {L : Loc}
    (hS : (Stm.call nm ps b rs args ds).Safe K KH Γ W) (hG : Gd K KH κ Γ s L)
    (hnb : evalF κ (Stm.call nm ps b rs args ds) s L ≠ .bug) :
    SafeAt K KH κ Γ W (Stm.call nm ps b rs args ds) s L := by
  obtain ⟨ha, hb, hd⟩ := hS
  cases hv : evList κ s L args with
  | none => simp only [evalF, hv, ne_eq, not_true_eq_false] at hnb
  | some vs =>
    have hG0 : Gd K KH κ (fun _ => K) s (Machine.State.setLocs (fun _ => 0) ps vs) :=
      ⟨hG.enc, hG.vb, setLocs_lt (zero_locs _) (fun _ _ => le_refl K) (hG.vals hC ha hv)⟩
    have hnb' : evalF κ b s (Machine.State.setLocs (fun _ => 0) ps vs) ≠ .bug := by
      intro e; apply hnb; simp only [evalF, hv, e]
    obtain ⟨p1, p2, p3⟩ := ihb hb hG0 hnb'
    refine ⟨?_, fun s' L' n h => ?_, fun s' L' n h => ?_⟩
    · simp only [pkF, hv, Option.getD_some]
      exact max_lt (hG.pkList hC (fun e he => (ha e he).1) hv) p1
    · simp only [evalF, hv] at h
      revert h; cases h2 : evalF κ b s (Machine.State.setLocs (fun _ => 0) ps vs) <;> simp only [
          Res.ok.injEq,
          and_imp,
          reduceCtorEq,
          IsEmpty.forall_iff]
      intro e1 e2 _; subst e1; subst e2
      obtain ⟨g1, g2, g3⟩ := p2 _ _ _ h2
      refine ⟨g1, g2, setLocs_lt hG.loc hd ?_⟩
      intro v hv'
      simp only [List.mem_map] at hv'
      obtain ⟨r, -, rfl⟩ := hv'
      exact g3 r
    · simp only [evalF, hv] at h
      revert h; cases h2 : evalF κ b s (Machine.State.setLocs (fun _ => 0) ps vs) <;> simp only [
          reduceCtorEq,
          IsEmpty.forall_iff,
          Res.fail.injEq,
          and_imp]
      intro e1 e2 _; subst e1; subst e2
      obtain ⟨g1, g2, -⟩ := p3 _ _ _ h2
      exact ⟨g1, g2, hG.loc⟩

/-- Safety of the `catch` constructor at one state. -/
private theorem safeAt_catch
    (c h : Stm)
    (ihc : ∀ {Γ : Reg → Nat} {s : Core} {L : Loc},
      c.Safe K KH Γ W → Gd K KH κ Γ s L → evalF κ c s L ≠ .bug →
        SafeAt K KH κ Γ W c s L)
    (ihh : ∀ {Γ : Reg → Nat} {s : Core} {L : Loc},
      h.Safe K KH Γ W → Gd K KH κ Γ s L → evalF κ h s L ≠ .bug →
        SafeAt K KH κ Γ W h s L)
    {Γ : Reg → Nat} {s : Core} {L : Loc}
    (hS : (Stm.«catch» c h).Safe K KH Γ W) (hG : Gd K KH κ Γ s L)
    (hnb : evalF κ (Stm.«catch» c h) s L ≠ .bug) :
    SafeAt K KH κ Γ W (Stm.«catch» c h) s L := by
  obtain ⟨hc, hh⟩ := hS
  cases h1 : evalF κ c s L with
  | bug => simp only [evalF, h1, ne_eq, not_true_eq_false] at hnb
  | ok s1 L1 n1 =>
    obtain ⟨p1, p2, -⟩ := ihc hc hG (by rw [h1]; simp)
    refine ⟨by rw [pkF_catch_ok h1]; exact p1, fun s' L' n e => ?_, fun s' L' n e => by
      simp only [evalF, h1, reduceCtorEq] at e⟩
    simp only [evalF, h1, Res.ok.injEq] at e; obtain ⟨rfl, rfl, -⟩ := e; exact p2 _ _ _ h1
  | fail s1 L1 n1 =>
    obtain ⟨p1, -, p3⟩ := ihc hc hG (by rw [h1]; simp)
    have hG1 := p3 _ _ _ h1
    have hnb2 : evalF κ h s1 L1 ≠ .bug := by
      intro e; apply hnb; simp only [evalF, h1, Res.addCost, e]
    obtain ⟨q1, q2, q3⟩ := ihh hh hG1 hnb2
    refine ⟨by rw [pkF_catch_fail h1]; exact max_lt p1 q1, fun s' L' n e => ?_, fun s' L' n e
      => ?_⟩
    · simp only [evalF, h1] at e
      revert e; cases h2 : evalF κ h s1 L1 <;> simp only [Res.addCost, Res.ok.injEq, and_imp,
          reduceCtorEq, IsEmpty.forall_iff]
      intro e1 e2 _; subst e1; subst e2; exact q2 _ _ _ h2
    · simp only [evalF, h1] at e
      revert e; cases h2 : evalF κ h s1 L1 <;> simp only [Res.addCost, reduceCtorEq,
          IsEmpty.forall_iff, Res.fail.injEq,
          and_imp]
      intro e1 e2 _; subst e1; subst e2; exact q3 _ _ _ h2

/-- Safety of the `lwr` constructor at one state. -/
private theorem safeAt_lwr (hC : CapsW K κ) (hW : K ≤ W)
    (k : LK)
    (b : Bool)
    (i j e : Exp)
    {Γ : Reg → Nat} {s : Core} {L : Loc}
    (hS : (Stm.lwr k b i j e).Safe K KH Γ W) (hG : Gd K KH κ Γ s L)
    (hnb : evalF κ (Stm.lwr k b i j e) s L ≠ .bug) :
    SafeAt K KH κ Γ W (Stm.lwr k b i j e) s L := by
  obtain ⟨hi, hj, he, hw⟩ := hS
  cases hx : i.ev κ s L with
  | none => simp only [evalF, hx, ne_eq, not_true_eq_false] at hnb
  | some x =>
  cases hy : j.ev κ s L with
  | none => simp only [evalF, hx, hy, ne_eq, not_true_eq_false] at hnb
  | some y =>
  cases hv : e.ev κ s L with
  | none => simp only [evalF, hx, hy, hv, ne_eq, not_true_eq_false] at hnb
  | some v =>
  simp only [evalF, hx, hy, hv] at hnb
  split at hnb
  · next hyl =>
    split at hnb
    · next s1 hs1 =>
      obtain ⟨hxr, -⟩ := LK.set_lrec hs1
      have hle := hG.enc.llen k hxr
      have hidx := lidx_lt hC hxr (lt_of_lt_of_le hyl hle)
      have hst := lt_of_le_of_lt (stride_le κ k) (hC.lcap k)
      have hlb := hG.vb.lb k hxr
      have hv' := hG.valW hC he hw hv
      refine ⟨?_, fun s' L' n h => ?_, fun _ _ _ h => ?_⟩
      · simp only [pkF, lidxPk, Exp.val_of hx, Exp.val_of hy]
        have := hG.pk hC hi hx; have := hG.pk hC hj hy; have := hG.pk hC he hv
        have hm : x * k.stride κ.lcap ≤ x * k.stride κ.lcap + y := Nat.le_add_right _ _
        refine max_lt (max_lt (max_lt (max_lt (max_lt ?_ ?_) ?_) ?_) ?_) ?_ <;>
          first | assumption | exact lt_pow_of_lt_K hW (by omega)
      · have h' : evalF κ (.lwr k b i j e) s L = .ok s' L' n := h
        simp only [evalF, hx, hy, hv, ite_eq_left hyl, hs1] at h; cases h
        refine ⟨hG.enc.of_ok h', hG.vb.lset hs1 (hlb.set ?_), hG.loc⟩
        have := hlb.getD hyl
        cases b <;> simp only [ite_true, ite_false, Bool.false_eq_true] <;> exact ⟨by omega,
          by omega⟩
      · simp only [evalF, hx, hy, hv, ite_eq_left hyl, hs1] at h; cases h
    · exact absurd rfl hnb
  · exact absurd rfl hnb

/-- Safety of the `lgrow` constructor at one state. -/
private theorem safeAt_lgrow (hC : CapsW K κ) (hW : K ≤ W)
    (k : LK)
    (i a b : Exp)
    {Γ : Reg → Nat} {s : Core} {L : Loc}
    (hS : (Stm.lgrow k i a b).Safe K KH Γ W) (hG : Gd K KH κ Γ s L)
    (hnb : evalF κ (Stm.lgrow k i a b) s L ≠ .bug) :
    SafeAt K KH κ Γ W (Stm.lgrow k i a b) s L := by
  obtain ⟨hi, ha, hb, hwa, hwb⟩ := hS
  cases hx : i.ev κ s L with
  | none => simp only [evalF, hx, ne_eq, not_true_eq_false] at hnb
  | some x =>
  cases hva : a.ev κ s L with
  | none => simp only [evalF, hx, hva, ne_eq, not_true_eq_false] at hnb
  | some va =>
  cases hvb : b.ev κ s L with
  | none => simp only [evalF, hx, hva, hvb, ne_eq, not_true_eq_false] at hnb
  | some vb =>
  simp only [evalF, hx, hva, hvb] at hnb
  split at hnb
  · next s1 hs1 =>
    obtain ⟨hxr, hlc⟩ := LK.set_lrec hs1
    rw [List.length_append, List.length_singleton] at hlc
    have hidx := lidx_lt hC hxr (by omega : (k.view s x).length < κ.lcap k)
    have hst := lt_of_le_of_lt (stride_le κ k) (hC.lcap k)
    have hl1 : (k.view s x).length + 1 < 2 ^ K := lt_of_le_of_lt hlc (hC.lcap k)
    refine ⟨?_, fun s' L' n h => ?_, fun _ _ _ h => ?_⟩
    · simp only [pkF, Exp.val_of hx]
      have := hG.pk hC hi hx; have := hG.pk hC ha hva; have := hG.pk hC hb hvb
      have hm : x * k.stride κ.lcap ≤ x * k.stride κ.lcap + (k.view s x).length :=
        Nat.le_add_right _ _
      refine max_lt (max_lt (max_lt (max_lt (max_lt (max_lt ?_ ?_) ?_) ?_) ?_) (max_lt ?_ ?_))
        ?_ <;>
        first | assumption | exact lt_pow_of_lt_K hW (by omega)
    · have h' : evalF κ (.lgrow k i a b) s L = .ok s' L' n := h
      simp only [evalF, hx, hva, hvb, hs1] at h; cases h
      exact ⟨hG.enc.of_ok h', hG.vb.lset hs1 ((hG.vb.lb k hxr).append
        ⟨hG.valW hC ha hwa hva, hG.valW hC hb hwb hvb⟩), hG.loc⟩
    · simp only [evalF, hx, hva, hvb, hs1] at h; cases h
  · exact absurd rfl hnb

/-- Safety of the `lshrink` constructor at one state. -/
private theorem safeAt_lshrink (hC : CapsW K κ) (hK : 3 ≤ K) (hW : K ≤ W)
    (k : LK)
    (i : Exp)
    {Γ : Reg → Nat} {s : Core} {L : Loc}
    (hS : (Stm.lshrink k i).Safe K KH Γ W) (hG : Gd K KH κ Γ s L)
    (hnb : evalF κ (Stm.lshrink k i) s L ≠ .bug) :
    SafeAt K KH κ Γ W (Stm.lshrink k i) s L := by
  have h1K : (1 : Nat) < 2 ^ W := lt_of_lt_of_le (by have := two_le_pow hK; omega)
    (Nat.pow_le_pow_right (by norm_num) hW)
  cases hx : i.ev κ s L with
  | none => simp only [evalF, hx, ne_eq, not_true_eq_false] at hnb
  | some x =>
  simp only [evalF, hx] at hnb
  split at hnb
  · next hne =>
    split at hnb
    · next s1 hs1 =>
      obtain ⟨hxr, -⟩ := LK.set_lrec hs1
      have hle := hG.enc.llen k hxr
      refine ⟨?_, fun s' L' n h => ?_, fun _ _ _ h => ?_⟩
      · simp only [pkF, Exp.val_of hx]
        exact max_lt (max_lt (hG.pk hC hS hx) (lt_pow_of_lt_K hW (lt_of_le_of_lt hle (hC.lcap
          k)))) h1K
      · have h' : evalF κ (.lshrink k i) s L = .ok s' L' n := h
        simp only [evalF, hx, ite_eq_left hne, hs1] at h; cases h
        exact ⟨hG.enc.of_ok h', hG.vb.lset hs1 (hG.vb.lb k hxr).dropLast, hG.loc⟩
      · simp only [evalF, hx, ite_eq_left hne, hs1] at h; cases h
    · exact absurd rfl hnb
  · exact absurd rfl hnb

/-- Safety of the `lclear` constructor at one state. -/
private theorem safeAt_lclear (hC : CapsW K κ)
    (k : LK)
    (i : Exp)
    {Γ : Reg → Nat} {s : Core} {L : Loc}
    (hS : (Stm.lclear k i).Safe K KH Γ W) (hG : Gd K KH κ Γ s L)
    (hnb : evalF κ (Stm.lclear k i) s L ≠ .bug) :
    SafeAt K KH κ Γ W (Stm.lclear k i) s L := by
  cases hx : i.ev κ s L with
  | none => simp only [evalF, hx, ne_eq, not_true_eq_false] at hnb
  | some x =>
  simp only [evalF, hx] at hnb
  split at hnb
  · next s1 hs1 =>
    refine ⟨by simp only [pkF]; exact hG.pk hC hS hx, fun s' L' n h => ?_, fun _ _ _ h => ?_⟩
    · have h' : evalF κ (.lclear k i) s L = .ok s' L' n := h
      simp only [evalF, hx, hs1] at h; cases h
      exact ⟨hG.enc.of_ok h', hG.vb.lset hs1 LB.nil, hG.loc⟩
    · simp only [evalF, hx, hs1] at h; cases h
  · exact absurd rfl hnb

/-- Safety of the `pwr` constructor at one state. -/
private theorem safeAt_pwr (hC : CapsW K κ) (hW : K ≤ W)
    (c j e : Exp)
    {Γ : Reg → Nat} {s : Core} {L : Loc}
    (hS : (Stm.pwr c j e).Safe K KH Γ W) (hG : Gd K KH κ Γ s L)
    (hnb : evalF κ (Stm.pwr c j e) s L ≠ .bug) :
    SafeAt K KH κ Γ W (Stm.pwr c j e) s L := by
  obtain ⟨hc, hj, he, hw⟩ := hS
  cases hx : c.ev κ s L with
  | none => simp only [evalF, hx, ne_eq, not_true_eq_false] at hnb
  | some x =>
  cases hy : j.ev κ s L with
  | none => simp only [evalF, hx, hy, ne_eq, not_true_eq_false] at hnb
  | some y =>
  cases hv : e.ev κ s L with
  | none => simp only [evalF, hx, hy, hv, ne_eq, not_true_eq_false] at hnb
  | some v =>
  simp only [evalF, hx, hy, hv] at hnb
  split at hnb
  · next hcond =>
    obtain ⟨hxC, hyp, hnp⟩ := hcond
    refine ⟨?_, fun s' L' n h => ?_, fun _ _ _ h => ?_⟩
    · simp only [pkF, pidxPk, Exp.val_of hx, Exp.val_of hy]
      have := hG.pk hC hc hx; have := hG.pk hC hj hy; have := hG.pk hC he hv
      have hidx : x * κ.pw + y < 2 ^ K := lt_trans (lt_mul_add hxC hyp) hC.path
      have hm : x * κ.pw ≤ x * κ.pw + y := Nat.le_add_right _ _
      have hr := rowPk_lt hG.enc hC
      refine max_lt (max_lt (max_lt (max_lt (max_lt ?_ ?_) ?_) ?_) ?_) ?_ <;>
        first | assumption | exact lt_pow_of_lt_K hW (by omega)
    · have h' : evalF κ (.pwr c j e) s L = .ok s' L' n := h
      simp only [evalF, hx, hy, hv, ite_eq_left (And.intro hxC (And.intro hyp hnp))] at h; cases h
      exact ⟨hG.enc.of_ok h', hG.vb.pwr hnp (hG.valW hC he hw hv), hG.loc⟩
    · simp only [evalF, hx, hy, hv, ite_eq_left (And.intro hxC (And.intro hyp hnp))] at h; cases h
  · exact absurd rfl hnb

/-- Safety of the `rowReset` constructor at one state. -/
private theorem safeAt_rowReset
    (c : Exp)
    {Γ : Reg → Nat} {s : Core} {L : Loc}
    (hG : Gd K KH κ Γ s L)
    (hnb : evalF κ (Stm.rowReset c) s L ≠ .bug) :
    SafeAt K KH κ Γ W (Stm.rowReset c) s L := by
  have h0K : (0 : Nat) < 2 ^ W := Nat.two_pow_pos _
  cases hx : c.ev κ s L with
  | none => simp only [evalF, hx, ne_eq, not_true_eq_false] at hnb
  | some x =>
  simp only [evalF, hx] at hnb
  split at hnb
  · next hcond =>
    refine ⟨by simp only [pkF]; exact h0K, fun s' L' n h => ?_, fun _ _ _ h => ?_⟩
    · have h' : evalF κ (.rowReset c) s L = .ok s' L' n := h
      simp only [evalF, hx, ite_eq_left hcond] at h; cases h
      exact ⟨hG.enc.of_ok h', hG.vb.rowReset hcond.2.2.1, hG.loc⟩
    · simp only [evalF, hx, ite_eq_left hcond] at h; cases h
  · exact absurd rfl hnb

/-- Safety of the `prepInit` constructor at one state. -/
private theorem safeAt_prepInit (hC : CapsW K κ) (hK : 3 ≤ K) (hW : K ≤ W)
    (c b : Exp)
    {Γ : Reg → Nat} {s : Core} {L : Loc}
    (hS : (Stm.prepInit c b).Safe K KH Γ W) (hG : Gd K KH κ Γ s L)
    (hnb : evalF κ (Stm.prepInit c b) s L ≠ .bug) :
    SafeAt K KH κ Γ W (Stm.prepInit c b) s L := by
  have h1K : (1 : Nat) < 2 ^ W := lt_of_lt_of_le (by have := two_le_pow hK; omega)
    (Nat.pow_le_pow_right (by norm_num) hW)
  obtain ⟨hc, hb, hwc, hwb⟩ := hS
  cases hx : c.ev κ s L with
  | none => simp only [evalF, hx, ne_eq, not_true_eq_false] at hnb
  | some x =>
  cases hy : b.ev κ s L with
  | none => simp only [evalF, hx, hy, ne_eq, not_true_eq_false] at hnb
  | some y =>
  simp only [evalF, hx, hy] at hnb
  split at hnb
  · next hcond =>
    have hev : evList κ s L [c, b] = some [x, y] := by
      simp only [evList, List.mapM_cons, hx, hy, List.mapM_nil, Option.pure_def,
        Option.bind_eq_bind, Option.bind_some]
    refine ⟨?_, fun s' L' n h => ?_, fun _ _ _ h => ?_⟩
    · simp only [pkF]
      exact max_lt (hG.pkList hC (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, hc, forall_eq, hb,
          and_self]) hev) h1K
    · have h' : evalF κ (.prepInit c b) s L = .ok s' L' n := h
      simp only [evalF, hx, hy, ite_eq_left hcond] at h; cases h
      have hp : s.prep = none := by have := hcond.1; simpa using this
      exact ⟨hG.enc.of_ok h', hG.vb.prepInit hK hp (hG.valW hC hc hwc hx) (hG.valW hC hb hwb
        hy), hG.loc⟩
    · simp only [evalF, hx, hy, ite_eq_left hcond] at h; cases h
  · exact absurd rfl hnb

/-- Safety of the `prepSet` constructor at one state. -/
private theorem safeAt_prepSet (hC : CapsW K κ)
    (h b t : Exp)
    {Γ : Reg → Nat} {s : Core} {L : Loc}
    (hS : (Stm.prepSet h b t).Safe K KH Γ W) (hG : Gd K KH κ Γ s L)
    (hnb : evalF κ (Stm.prepSet h b t) s L ≠ .bug) :
    SafeAt K KH κ Γ W (Stm.prepSet h b t) s L := by
  have hh : h.OK Γ K KH W ∧ h.vw Γ K KH K ≤ K := hS h (by simp)
  have hb : b.OK Γ K KH W ∧ b.vw Γ K KH K ≤ K := hS b (by simp)
  have ht : t.OK Γ K KH W ∧ t.vw Γ K KH K ≤ K := hS t (by simp)
  cases hp : s.prep with
  | none => simp only [evalF, hp, ne_eq, not_true_eq_false] at hnb
  | some pr =>
  cases hvh : h.ev κ s L with
  | none => simp only [evalF, hp, hvh, ne_eq, not_true_eq_false] at hnb
  | some vh =>
  cases hvb : b.ev κ s L with
  | none => simp only [evalF, hp, hvh, hvb, ne_eq, not_true_eq_false] at hnb
  | some vb =>
  cases hvt : t.ev κ s L with
  | none => simp only [evalF, hp, hvh, hvb, hvt, ne_eq, not_true_eq_false] at hnb
  | some vt =>
  have hev : evList κ s L [h, b, t] = some [vh, vb, vt] := by
    simp only [evList, List.mapM_cons, hvh, hvb, hvt, List.mapM_nil, Option.pure_def,
      Option.bind_eq_bind, Option.bind_some]
  refine ⟨?_, fun s' L' n e => ?_, fun _ _ _ e => ?_⟩
  · simp only [pkF]; exact hG.pkList hC (fun e he => (hS e he).1) hev
  · have h' : evalF κ (.prepSet h b t) s L = .ok s' L' n := e
    simp only [evalF, hp, hvh, hvb, hvt] at e; cases e
    exact ⟨hG.enc.of_ok h', hG.vb.prepSet hp (hG.valW hC hh.1 hh.2 hvh) (hG.valW hC hb.1 hb.2 hvb)
      (hG.valW hC ht.1 ht.2 hvt), hG.loc⟩
  · simp only [evalF, hp, hvh, hvb, hvt] at e; cases e

/-- Safety of the `prepPath` constructor at one state. -/
private theorem safeAt_prepPath (hC : CapsW K κ) (hW : K ≤ W)
    (j e : Exp)
    {Γ : Reg → Nat} {s : Core} {L : Loc}
    (hS : (Stm.prepPath j e).Safe K KH Γ W) (hG : Gd K KH κ Γ s L)
    (hnb : evalF κ (Stm.prepPath j e) s L ≠ .bug) :
    SafeAt K KH κ Γ W (Stm.prepPath j e) s L := by
  obtain ⟨hj, he, hw⟩ := hS
  cases hp : s.prep with
  | none => simp only [evalF, hp, ne_eq, not_true_eq_false] at hnb
  | some pr =>
  cases hy : j.ev κ s L with
  | none => simp only [evalF, hp, hy, ne_eq, not_true_eq_false] at hnb
  | some y =>
  cases hv : e.ev κ s L with
  | none => simp only [evalF, hp, hy, hv, ne_eq, not_true_eq_false] at hnb
  | some v =>
  simp only [evalF, hp, hy, hv] at hnb
  split at hnb
  · next hyp =>
    refine ⟨?_, fun s' L' n h => ?_, fun _ _ _ h => ?_⟩
    · simp only [pkF, pidxPk, Exp.val_of hy]
      have hpc := hG.enc.prepC hp
      have hoc : OF.prepChunk.get s = pr.chunk := by simp only [OF.get, hp]
      rw [hoc]
      have := hG.pk hC hj hy; have := hG.pk hC he hv
      have hidx : pr.chunk * κ.pw + y < 2 ^ K := lt_trans (lt_mul_add hpc hyp) hC.path
      have hm : pr.chunk * κ.pw ≤ pr.chunk * κ.pw + y := Nat.le_add_right _ _
      have hm2 : pr.chunk < 2 ^ K := lt_trans hpc (hC.tbl _)
      have hr := rowPk_lt hG.enc hC
      refine max_lt (max_lt (max_lt (max_lt (max_lt ?_ ?_) ?_) ?_) ?_) ?_ <;>
        first | assumption | exact lt_pow_of_lt_K hW (by omega)
    · have h' : evalF κ (.prepPath j e) s L = .ok s' L' n := h
      simp only [evalF, hp, hy, hv, ite_eq_left hyp] at h; cases h
      exact ⟨hG.enc.of_ok h', hG.vb.prepPath hp (hG.valW hC he hw hv), hG.loc⟩
    · simp only [evalF, hp, hy, hv, ite_eq_left hyp] at h; cases h
  · exact absurd rfl hnb

/-- Safety of the `prepCommit` constructor at one state. -/
private theorem safeAt_prepCommit
    {Γ : Reg → Nat} {s : Core} {L : Loc}
    (hG : Gd K KH κ Γ s L)
    (hnb : evalF κ (Stm.prepCommit) s L ≠ .bug) :
    SafeAt K KH κ Γ W (Stm.prepCommit) s L := by
  have h0K : (0 : Nat) < 2 ^ W := Nat.two_pow_pos _
  cases hp : s.prep with
  | none => simp only [evalF, hp, ne_eq, not_true_eq_false] at hnb
  | some pr =>
    refine ⟨by simp only [pkF]; exact h0K, fun s' L' n h => ?_, fun _ _ _ h => ?_⟩
    · have h' : evalF κ .prepCommit s L = .ok s' L' n := h
      simp only [evalF, hp] at h; cases h
      exact ⟨hG.enc.of_ok h', hG.vb.prepCommit hp, hG.loc⟩
    · simp only [evalF, hp] at h; cases h

/-- Safety of the `jobSet` constructor at one state. -/
private theorem safeAt_jobSet (hC : CapsW K κ) (hK : 3 ≤ K) (hW : K ≤ W)
    (x y z t a b c d : Exp)
    {Γ : Reg → Nat} {s : Core} {L : Loc}
    (hS : (Stm.jobSet x y z t a b c d).Safe K KH Γ W) (hG : Gd K KH κ Γ s L)
    (hnb : evalF κ (Stm.jobSet x y z t a b c d) s L ≠ .bug) :
    SafeAt K KH κ Γ W (Stm.jobSet x y z t a b c d) s L := by
  have h1K : (1 : Nat) < 2 ^ W := lt_of_lt_of_le (by have := two_le_pow hK; omega)
    (Nat.pow_le_pow_right (by norm_num) hW)
  cases hv : evList κ s L [x, y, z, t, a, b, c, d] with
  | none => simp only [evalF, hv, ne_eq, not_true_eq_false] at hnb
  | some vs =>
    have hvs := hG.vals hC hS hv
    refine ⟨by simp only [pkF]; exact max_lt (hG.pkList hC (fun e he => (hS e he).1) hv) h1K,
      fun s' L' n h => ?_, fun _ _ _ h => ?_⟩
    · have h' : evalF κ (.jobSet x y z t a b c d) s L = .ok s' L' n := h
      rcases vs with _ | ⟨vx, _ | ⟨vy, _ | ⟨vz, _ | ⟨vt, _ | ⟨va, _ | ⟨vb, _ | ⟨vc, _ | ⟨vd, _
        | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
        simp only [evalF, hv] at h <;> try (solve | cases h)
      split at h
      · next pc hpc =>
        cases h
        exact ⟨hG.enc.of_ok h', hG.vb.jobSet (by omega) hpc (hvs _ (by simp)) (hvs _ (by simp))
          (hvs _ (by simp)) (hvs _ (by simp)) (hvs _ (by simp)) (hvs _ (by simp)) (hvs _ (by
            simp))
          (hvs _ (by simp)), hG.loc⟩
      · cases h
    · rcases vs with _ | ⟨vx, _ | ⟨vy, _ | ⟨vz, _ | ⟨vt, _ | ⟨va, _ | ⟨vb, _ | ⟨vc, _ | ⟨vd, _
      | ⟨_, _⟩⟩⟩⟩⟩⟩⟩⟩⟩ <;>
        simp only [evalF, hv] at h <;> try (solve | cases h)
      split at h <;> cases h

/-- Safety of the `jobClear` constructor at one state. -/
private theorem safeAt_jobClear
    {Γ : Reg → Nat} {s : Core} {L : Loc}
    (hG : Gd K KH κ Γ s L)
    :
    SafeAt K KH κ Γ W (Stm.jobClear) s L := by
  have h0K : (0 : Nat) < 2 ^ W := Nat.two_pow_pos _
  refine ⟨by simp only [pkF]; exact h0K, fun s' L' n h => ?_, fun _ _ _ h => by
    simp only [evalF, reduceCtorEq] at h⟩
  have h' : evalF κ .jobClear s L = .ok s' L' n := h
  simp only [evalF] at h; cases h
  exact ⟨hG.enc.of_ok h', hG.vb.jobClear, hG.loc⟩

/-- Safety of the `pcSet` constructor at one state. -/
private theorem safeAt_pcSet (hC : CapsW K κ)
    (t a b c d : Exp)
    {Γ : Reg → Nat} {s : Core} {L : Loc}
    (hS : (Stm.pcSet t a b c d).Safe K KH Γ W) (hG : Gd K KH κ Γ s L)
    (hnb : evalF κ (Stm.pcSet t a b c d) s L ≠ .bug) :
    SafeAt K KH κ Γ W (Stm.pcSet t a b c d) s L := by
  cases hj : s.resJob with
  | none => simp only [evalF, hj, ne_eq, not_true_eq_false] at hnb
  | some jb =>
  cases hv : evList κ s L [t, a, b, c, d] with
  | none => simp only [evalF, hj, hv, ne_eq, not_true_eq_false] at hnb
  | some vs =>
    have hvs := hG.vals hC hS hv
    refine ⟨by simp only [pkF]; exact hG.pkList hC (fun e he => (hS e he).1) hv,
      fun s' L' n h => ?_, fun _ _ _ h => ?_⟩
    · have h' : evalF κ (.pcSet t a b c d) s L = .ok s' L' n := h
      rcases vs with _ | ⟨vt, _ | ⟨va, _ | ⟨vb, _ | ⟨vc, _ | ⟨vd, _ | ⟨_, _⟩⟩⟩⟩⟩⟩ <;>
        simp only [evalF, hj, hv] at h <;> try (solve | cases h)
      split at h
      · next pc hpc =>
        cases h
        exact ⟨hG.enc.of_ok h', hG.vb.pcSet hj hpc (hvs _ (by simp)) (hvs _ (by simp)) (hvs _
          (by simp))
          (hvs _ (by simp)) (hvs _ (by simp)), hG.loc⟩
      · cases h
    · rcases vs with _ | ⟨vt, _ | ⟨va, _ | ⟨vb, _ | ⟨vc, _ | ⟨vd, _ | ⟨_, _⟩⟩⟩⟩⟩⟩ <;>
        simp only [evalF, hj, hv] at h <;> try (solve | cases h)
      split at h <;> cases h

/-- **Safe statements.** -/
theorem Stm.safe_run (hC : CapsW K κ) (hK : 3 ≤ K) (hW : K ≤ W) :
    ∀ (c : Stm) {Γ : Reg → Nat} {s : Core} {L : Loc}, c.Safe K KH Γ W → Gd K KH κ Γ s L →
      evalF κ c s L ≠ .bug → SafeAt K KH κ Γ W c s L := by
  have h0K : (0 : Nat) < 2 ^ W := Nat.two_pow_pos _
  intro c
  induction c with
  | skip => intro Γ s L _ hG _; exact ⟨by simp only [pkF]; exact h0K, fun s' L' n h => by
      simp only [evalF, Res.ok.injEq] at h; obtain ⟨rfl, rfl, -⟩ := h; exact hG, fun _ _ _ h => by
        simp only [evalF, reduceCtorEq] at h⟩
  | assign x e =>
    intro Γ s L hS hG hnb
    exact safeAt_assign hC x e hS hG hnb
  | wr f i e =>
    intro Γ s L hS hG hnb
    exact safeAt_wr hC f i e hS hG hnb
  | push t x =>
    intro Γ s L hS hG hnb
    exact safeAt_push hC hW t x hS hG hnb
  | seq c d ihc ihd =>
    intro Γ s L hS hG hnb
    exact safeAt_seq  c d ihc ihd hS hG hnb
  | ite c t f iht ihf =>
    intro Γ s L hS hG hnb
    exact safeAt_ite hC c t f iht ihf hS hG hnb
  | loop x n b ihb =>
    intro Γ s L hS hG hnb
    exact safeAt_loop hC x n b ihb hS hG hnb
  | call nm ps b rs args ds ihb =>
    intro Γ s L hS hG hnb
    exact safeAt_call hC nm ps b rs args ds ihb hS hG hnb
  | fail => intro Γ s L _ hG _; exact ⟨by simp only [pkF]; exact h0K, fun s' L' n h => by
    simp only [evalF, reduceCtorEq] at h,
      fun s' L' n h => by
        simp only [evalF, Res.fail.injEq] at h
        obtain ⟨rfl, rfl, -⟩ := h
        exact hG⟩
  | bug => intro Γ s L _ _ hnb; exact absurd rfl hnb
  | «catch» c h ihc ihh =>
    intro Γ s L hS hG hnb
    exact safeAt_catch  c h ihc ihh hS hG hnb
  | lwr k b i j e =>
    intro Γ s L hS hG hnb
    exact safeAt_lwr hC hW k b i j e hS hG hnb
  | lgrow k i a b =>
    intro Γ s L hS hG hnb
    exact safeAt_lgrow hC hW k i a b hS hG hnb
  | lshrink k i =>
    intro Γ s L hS hG hnb
    exact safeAt_lshrink hC hK hW k i hS hG hnb
  | lclear k i =>
    intro Γ s L hS hG hnb
    exact safeAt_lclear hC k i hS hG hnb
  | pwr c j e =>
    intro Γ s L hS hG hnb
    exact safeAt_pwr hC hW c j e hS hG hnb
  | rowReset c =>
    intro Γ s L _ hG hnb
    exact safeAt_rowReset  c hG hnb
  | prepInit c b =>
    intro Γ s L hS hG hnb
    exact safeAt_prepInit hC hK hW c b hS hG hnb
  | prepSet h b t =>
    intro Γ s L hS hG hnb
    exact safeAt_prepSet hC h b t hS hG hnb
  | prepPath j e =>
    intro Γ s L hS hG hnb
    exact safeAt_prepPath hC hW j e hS hG hnb
  | prepCommit =>
    intro Γ s L _ hG hnb
    exact safeAt_prepCommit  hG hnb
  | jobSet x y z t a b c d =>
    intro Γ s L hS hG hnb
    exact safeAt_jobSet hC hK hW x y z t a b c d hS hG hnb
  | jobClear =>
    intro Γ s L _ hG _
    exact safeAt_jobClear hG
  | pcSet t a b c d =>
    intro Γ s L hS hG hnb
    exact safeAt_pcSet hC t a b c d hS hG hnb

end run

end OrderMaintenance.Impl
