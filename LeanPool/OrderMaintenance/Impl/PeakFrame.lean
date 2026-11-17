/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.PeakHP


/-!
# Theorem W, option (A), stage A2: what a run leaves alone

Syntactic frames for the core language: a statement that never writes field `f` (`Stm.wf`)
ends with every value of `f` unchanged (`evalF_frame_fld`), and one that never assigns local `x`
(`Stm.asg`) ends with `x` unchanged (`evalF_frame_loc`). With the inversion lemmas for `;;` and
`if`, they let a peak proof follow the values that a risky store needs through the safe parts of
a procedure.

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg)

variable {κ : Caps}

/-- `c` may write field `f`. -/
def Stm.wf (f : Fld) : Stm → Bool
  | .wr f' _ _ => decide (f' = f)
  | .seq a b | .ite _ a b | .catch a b => a.wf f || b.wf f
  | .loop _ _ b => b.wf f
  | .call _ _ b _ _ _ => b.wf f
  | _ => false

/-- `c` may assign local `x` (of the frame it runs in). -/
def Stm.asg (x : Reg) : Stm → Bool
  | .assign y _ => decide (y = x)
  | .push _ y => decide (y = x)
  | .seq a b | .ite _ a b | .catch a b => a.asg x || b.asg x
  | .loop y _ b => decide (y = x) || b.asg x
  | .call _ _ _ _ _ ds => decide (x ∈ ds)
  | _ => false

/-! ### Fields -/

/-- The outcome keeps every value of field `f`. -/
def Res.keepsF (κ : Caps) (f : Fld) (s : Core) : Res → Prop
  | .ok s' _ _ => ∀ j, j < f.cap κ → f.get s' j = f.get s j
  | .fail s' _ _ => ∀ j, j < f.cap κ → f.get s' j = f.get s j
  | .bug => True

theorem Res.keepsF_addCost {f : Fld} {s : Core} {r : Res} (c : Nat) (h : r.keepsF κ f s) :
    (r.addCost c).keepsF κ f s := by cases r <;> exact h

theorem Res.keepsF_bind {f : Fld} {s : Core} {r : Res} {g : Core → Loc → Res} (h : r.keepsF κ f s)
    (hg : ∀ s1 L1, (g s1 L1).keepsF κ f s1) : (r.bind g).keepsF κ f s := by
  cases r with
  | ok s1 L1 c =>
    simp only [Res.bind]
    have := hg s1 L1
    cases hr : g s1 L1 <;> rw [hr] at this <;> simp only [Res.addCost, Res.keepsF] at this ⊢ <;>
      exact fun j hj => (this j hj).trans (h j hj)
  | fail => exact h
  | bug => trivial

theorem runForF_keepsF {f : Fld} (b : Stm) (x : Reg) (hb : ∀ s L, (evalF κ b s L).keepsF κ f s) :
    ∀ n k s L, (runForF (evalF κ b) x k n s L).keepsF κ f s
  | 0, _, _, _ => fun _ _ => rfl
  | n + 1, k, s, L => by
    simp only [runForF]
    exact Res.keepsF_bind (Res.keepsF_addCost 1 (hb s _)) (fun s1 L1 => runForF_keepsF b x hb n
      (k + 1) s1 L1)

theorem LK.set_fld {s s' : Core} {i : Nat} {l : List (Nat × Nat)} {k : LK} (h : k.set κ s i l =
  some s')
    (f : Fld) (j : Nat) (_ : j < f.cap κ) : f.get s' j = f.get s j := by
  simp only [LK.set] at h
  split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
  subst h
  exact (LK.put_keep s i l k).1 f j

theorem evalF_keepsF (f : Fld) : ∀ (c : Stm) (s : Core) (L : Loc), c.wf f = false → (evalF κ c s
  L).keepsF κ f s
  | .skip, _, _, _ => fun _ _ => rfl
  | .assign x e, s, L, _ => by simp only [evalF]; split <;> first | trivial | exact fun _ _ => rfl
  | .wr f' i e, s, L, h => by
    simp only [Stm.wf, decide_eq_false_iff_not] at h
    simp only [evalF]; split
    · split
      · next s' hs =>
        intro j hj
        rw [Fld.get_set hs f hj, ite_eq_right (fun e => h e.1.symm)]
      · trivial
    · trivial
  | .push t x, s, L, _ => by
    simp only [evalF]; split
    · exact fun j _ => Tbl.push_get s t f j
    · trivial
  | .seq a b, s, L, h => by
    simp only [Stm.wf, Bool.or_eq_false_iff] at h
    exact Res.keepsF_bind (evalF_keepsF f a s L h.1) (fun s1 L1 => evalF_keepsF f b s1 L1 h.2)
  | .ite c a b, s, L, h => by
    simp only [Stm.wf, Bool.or_eq_false_iff] at h
    simp only [evalF]; split
    · apply Res.keepsF_addCost; split
      · exact evalF_keepsF f a s L h.1
      · exact evalF_keepsF f b s L h.2
    · trivial
  | .loop x n b, s, L, h => by
    simp only [Stm.wf] at h
    simp only [evalF]; split
    · exact Res.keepsF_addCost _ (runForF_keepsF b x (fun s L => evalF_keepsF f b s L h) _ _ s L)
    · trivial
  | .call _ ps b rs args ds, s, L, h => by
    simp only [Stm.wf] at h
    simp only [evalF]; split
    · next vs _ =>
      have := evalF_keepsF f b s (Machine.State.setLocs (fun _ => 0) ps vs) h
      split <;> simp only [Res.keepsF] at this ⊢ <;>
        (rename_i heq; rw [heq] at this; exact this)
    · trivial
  | .fail, _, _, _ => fun _ _ => rfl
  | .bug, _, _, _ => trivial
  | .catch a b, s, L, h => by
    simp only [Stm.wf, Bool.or_eq_false_iff] at h
    simp only [evalF]
    have ha := evalF_keepsF f a s L h.1
    split
    · next s' L' n heq =>
      rw [heq] at ha
      have hb := Res.keepsF_addCost (1 + n) (evalF_keepsF f b s' L' h.2)
      revert hb; cases evalF κ b s' L' <;> simp only [Res.addCost, Res.keepsF] <;> intro hb <;>
        first | trivial | exact fun j hj => (hb j hj).trans (ha j hj)
    · next heq => rw [heq] at ha; exact ha
    · trivial
  | .lwr k snd i j e, s, L, _ => by
    simp only [evalF]; split
    · split
      · split
        · next s' h => exact LK.set_fld h f
        · trivial
      · trivial
    · trivial
  | .lgrow k i a b, s, L, _ => by
    simp only [evalF]; split
    · split
      · next s' h => exact LK.set_fld h f
      · trivial
    · trivial
  | .lshrink k i, s, L, _ => by
    simp only [evalF]; split
    · split
      · split
        · next s' h => exact LK.set_fld h f
        · trivial
      · trivial
    · trivial
  | .lclear k i, s, L, _ => by
    simp only [evalF]; split
    · split
      · next s' h => exact LK.set_fld h f
      · trivial
    · trivial
  | .pwr c j e, s, L, _ => by
    simp only [evalF]; split <;> (try split) <;> first | trivial | exact fun j _ => fld_path f j _
  | .rowReset c, s, L, _ => by
    simp only [evalF]; split <;> (try split) <;> first | trivial | exact fun j _ => fld_path f j _
  | .prepInit c b, s, L, _ => by
    simp only [evalF]; split <;> (try split) <;> first | trivial | exact fun j _ => fld_prep f j _
  | .prepSet h b t, s, L, _ => by
    simp only [evalF]; split <;> first | trivial | exact fun j _ => fld_prep f j _
  | .prepPath j e, s, L, _ => by
    simp only [evalF]; split <;> (try split) <;> first | trivial | exact fun j _ => fld_prep f j _
  | .prepCommit, s, L, _ => by
    simp only [evalF]; split <;> first | trivial | exact fun j _ => fld_pp f j _ _
  | .jobSet x y z t a b c d, s, L, _ => by
    simp only [evalF]; split <;> (try split) <;> first | trivial | exact fun j _ => fld_job f j _
  | .jobClear, s, L, _ => fun j _ => fld_job f j _
  | .pcSet t a b c d, s, L, _ => by
    simp only [evalF]; split <;> (try split) <;> first | trivial | exact fun j _ => fld_job f j _

/-- **A run that never writes `f` keeps it.** -/
theorem evalF_frame_fld {c : Stm} {f : Fld} (hf : c.wf f = false) {s s' : Core} {L L' : Loc} {n
  : Nat}
    (h : evalF κ c s L = .ok s' L' n) {j : Nat} (hj : j < f.cap κ) : f.get s' j = f.get s j := by
  have := evalF_keepsF (κ := κ) f c s L hf; rw [h] at this; exact this j hj

/-! ### Locals -/

/-- The outcome keeps local `x` of `L`. -/
def Res.keepsL (x : Reg) (L : Loc) : Res → Prop
  | .ok _ L' _ => L' x = L x
  | .fail _ L' _ => L' x = L x
  | .bug => True

theorem Res.keepsL_addCost {x : Reg} {L : Loc} {r : Res} (c : Nat) (h : r.keepsL x L) :
    (r.addCost c).keepsL x L := by cases r <;> exact h

theorem Res.keepsL_bind {x : Reg} {L : Loc} {r : Res} {g : Core → Loc → Res} (h : r.keepsL x L)
    (hg : ∀ s1 L1, (g s1 L1).keepsL x L1) : (r.bind g).keepsL x L := by
  cases r with
  | ok s1 L1 c =>
    simp only [Res.bind]
    have := hg s1 L1
    cases hr : g s1 L1 <;> rw [hr] at this <;> simp only [Res.addCost, Res.keepsL] at this ⊢ <;>
      exact this.trans h
  | fail => exact h
  | bug => trivial

theorem runForF_keepsL {x y : Reg} (hxy : y ≠ x) (b : Stm) (hb : ∀ s L, (evalF κ b s L).keepsL x
  L) :
    ∀ n k s L, (runForF (evalF κ b) y k n s L).keepsL x L
  | 0, _, _, _ => rfl
  | n + 1, k, s, L => by
    simp only [runForF]
    refine Res.keepsL_bind ?_ (fun s1 L1 => runForF_keepsL hxy b hb n (k + 1) s1 L1)
    have := Res.keepsL_addCost 1 (hb s (Machine.State.upd L y k))
    revert this
    cases (evalF κ b s (Machine.State.upd L y k)).addCost 1 <;> simp only [Res.keepsL] <;> intro
      h <;>
      first | trivial | (rw [h]; simp only [Machine.State.upd, Ne.symm hxy, ↓reduceIte])

theorem setLocs_not_mem {L : Loc} {x : Reg} : ∀ {ds : List Reg} {vs : List Nat}, x ∉ ds →
    Machine.State.setLocs L ds vs x = L x
  | [], vs, _ => by cases vs <;> rfl
  | _ :: _, [], _ => rfl
  | d :: ds, v :: vs, h => by
    simp only [List.mem_cons, not_or] at h
    simp only [Machine.State.setLocs]
    rw [setLocs_not_mem h.2]; simp only [Machine.State.upd, h.1, ↓reduceIte]

theorem evalF_keepsL (x : Reg) : ∀ (c : Stm) (s : Core) (L : Loc), c.asg x = false → (evalF κ c
  s L).keepsL x L
  | .skip, _, _, _ => rfl
  | .assign y e, s, L, h => by
    simp only [Stm.asg, decide_eq_false_iff_not] at h
    simp only [evalF]; split
    · simp only [Res.keepsL, Machine.State.upd, ite_eq_right (Ne.symm h)]
    · trivial
  | .wr f' i e, s, L, _ => by
    simp only [evalF]; split
    · split <;> first | rfl | trivial
    · trivial
  | .push t y, s, L, h => by
    simp only [Stm.asg, decide_eq_false_iff_not] at h
    simp only [evalF]; split
    · simp only [Res.keepsL, Machine.State.upd, ite_eq_right (Ne.symm h)]
    · trivial
  | .seq a b, s, L, h => by
    simp only [Stm.asg, Bool.or_eq_false_iff] at h
    exact Res.keepsL_bind (evalF_keepsL x a s L h.1) (fun s1 L1 => evalF_keepsL x b s1 L1 h.2)
  | .ite c a b, s, L, h => by
    simp only [Stm.asg, Bool.or_eq_false_iff] at h
    simp only [evalF]; split
    · apply Res.keepsL_addCost; split
      · exact evalF_keepsL x a s L h.1
      · exact evalF_keepsL x b s L h.2
    · trivial
  | .loop y n b, s, L, h => by
    simp only [Stm.asg, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    simp only [evalF]; split
    · exact Res.keepsL_addCost _ (runForF_keepsL h.1 b (fun s L => evalF_keepsL x b s L h.2) _ _
      s L)
    · trivial
  | .call _ ps b rs args ds, s, L, h => by
    simp only [Stm.asg, decide_eq_false_iff_not] at h
    simp only [evalF]; split
    · split
      · exact setLocs_not_mem h
      · rfl
      · trivial
    · trivial
  | .fail, _, _, _ => rfl
  | .bug, _, _, _ => trivial
  | .catch a b, s, L, h => by
    simp only [Stm.asg, Bool.or_eq_false_iff] at h
    simp only [evalF]
    have ha := evalF_keepsL x a s L h.1
    split
    · next s' L' n heq =>
      rw [heq] at ha
      have hb := Res.keepsL_addCost (1 + n) (evalF_keepsL x b s' L' h.2)
      revert hb; cases evalF κ b s' L' <;> simp only [Res.addCost, Res.keepsL] <;> intro hb <;>
        first | trivial | exact hb.trans ha
    · next heq => rw [heq] at ha; exact ha
    · trivial
  | .lwr k snd i j e, s, L, _ => by
    simp only [evalF]; split
    · split
      · split <;> first | rfl | trivial
      · trivial
    · trivial
  | .lgrow k i a b, s, L, _ => by
    simp only [evalF]; split
    · split <;> first | rfl | trivial
    · trivial
  | .lshrink k i, s, L, _ => by
    simp only [evalF]; split
    · split
      · split <;> first | rfl | trivial
      · trivial
    · trivial
  | .lclear k i, s, L, _ => by
    simp only [evalF]; split
    · split <;> first | rfl | trivial
    · trivial
  | .pwr c j e, s, L, _ => by simp only [evalF]; split <;> (try split) <;> first | rfl | trivial
  | .rowReset c, s, L, _ => by simp only [evalF]; split <;> (try split) <;> first | rfl | trivial
  | .prepInit c b, s, L, _ => by simp only [evalF]; split <;> (try split) <;> first | rfl | trivial
  | .prepSet h b t, s, L, _ => by simp only [evalF]; split <;> first | rfl | trivial
  | .prepPath j e, s, L, _ => by simp only [evalF]; split <;> (try split) <;> first | rfl | trivial
  | .prepCommit, s, L, _ => by simp only [evalF]; split <;> first | rfl | trivial
  | .jobSet x y z t a b c d, s, L, _ => by
    simp only [evalF]; split <;> (try split) <;> first | rfl | trivial
  | .jobClear, _, _, _ => rfl
  | .pcSet t a b c d, s, L, _ => by
    simp only [evalF]; split <;> (try split) <;> first | rfl | trivial

/-- **A run that never assigns `x` keeps it.** -/
theorem evalF_frame_loc {c : Stm} {x : Reg} (hx : c.asg x = false) {s s' : Core} {L L' : Loc} {n
  : Nat}
    (h : evalF κ c s L = .ok s' L' n) : L' x = L x := by
  have := evalF_keepsL (κ := κ) x c s L hx; rw [h] at this; exact this

/-! ### Inverting a run -/

theorem evalF_seq_inv {c d : Stm} {s s' : Core} {L L' : Loc} {n : Nat} (h : evalF κ (c;; d) s L
  = .ok s' L' n) :
    ∃ s1 L1 n1 n2, evalF κ c s L = .ok s1 L1 n1 ∧ evalF κ d s1 L1 = .ok s' L' n2 := by
  simp only [evalF] at h
  cases h1 : evalF κ c s L with
  | ok s1 L1 n1 =>
    rw [h1] at h; simp only [Res.bind] at h
    cases h2 : evalF κ d s1 L1 with
    | ok s2 L2 n2 =>
      rw [h2] at h
      simp only [Res.addCost, Res.ok.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      exact ⟨_, _, _, _, rfl, h2⟩
    | fail => rw [h2] at h; simp only [Res.addCost, reduceCtorEq] at h
    | bug => rw [h2] at h; simp only [Res.addCost, reduceCtorEq] at h
  | fail => rw [h1] at h; simp only [Res.bind, reduceCtorEq] at h
  | bug => rw [h1] at h; simp only [Res.bind, reduceCtorEq] at h

theorem evalF_ite_inv {c : Exp} {t f : Stm} {s s' : Core} {L L' : Loc} {n : Nat}
    (h : evalF κ (.ite c t f) s L = .ok s' L' n) :
    ∃ v, c.ev κ s L = some v ∧ ∃ m, (if v ≠ 0 then evalF κ t s L else evalF κ f s L) = .ok s' L'
      m := by
  simp only [evalF] at h
  split at h
  · next v hv =>
    refine ⟨v, hv, ?_⟩
    by_cases h0 : v = 0
    · simp only [h0, ne_eq, not_true_eq_false, ite_false] at h ⊢
      revert h; cases evalF κ f s L <;> intro h <;> simp only [Res.addCost, Res.ok.injEq,
          reduceCtorEq] at h
      obtain ⟨rfl, rfl, -⟩ := h; exact ⟨_, rfl⟩
    · simp only [h0, ne_eq, not_false_eq_true, ite_true] at h ⊢
      revert h; cases evalF κ t s L <;> intro h <;> simp only [Res.addCost, Res.ok.injEq,
          reduceCtorEq] at h
      obtain ⟨rfl, rfl, -⟩ := h; exact ⟨_, rfl⟩
  · cases h

/-! ### A field written at one index only -/

/-- Every write of `c` to field `f` is at the index held by local `x`.
Calls do not write `f`. -/
def Stm.wfAt (f : Fld) (x : Reg) : Stm → Bool
  | .wr f' i _ => !decide (f' = f) || decide (i = .var x)
  | .seq a b | .ite _ a b | .catch a b => a.wfAt f x && b.wfAt f x
  | .loop y _ b => !decide (y = x) && b.wfAt f x
  | .call _ _ b _ _ _ => !(b.wf f)
  | _ => true

/-- The outcome keeps `x` and every value of `f` away from index `L x`. -/
def Res.keepsFAt (κ : Caps) (f : Fld) (x : Reg) (s : Core) (L : Loc) : Res → Prop
  | .ok s' L' _ => L' x = L x ∧ ∀ j, j < f.cap κ → j ≠ L x → f.get s' j = f.get s j
  | .fail s' L' _ => L' x = L x ∧ ∀ j, j < f.cap κ → j ≠ L x → f.get s' j = f.get s j
  | .bug => True

theorem Res.keepsFAt_addCost {f : Fld} {x : Reg} {s : Core} {L : Loc} {r : Res} (c : Nat)
    (h : r.keepsFAt κ f x s L) : (r.addCost c).keepsFAt κ f x s L := by cases r <;> exact h

theorem Res.keepsFAt_bind {f : Fld} {x : Reg} {s : Core} {L : Loc} {r : Res} {g : Core → Loc → Res}
    (h : r.keepsFAt κ f x s L) (hg : ∀ s1 L1, L1 x = L x → (g s1 L1).keepsFAt κ f x s1 L1) :
    (r.bind g).keepsFAt κ f x s L := by
  cases r with
  | ok s1 L1 c =>
    simp only [Res.bind]
    have := hg s1 L1 h.1
    cases hr : g s1 L1 <;> rw [hr] at this <;> simp only [Res.addCost, Res.keepsFAt] at this ⊢ <;>
      exact ⟨this.1.trans h.1, fun j hj hne => by
        rw [this.2 j hj (by rw [h.1]; exact hne)]; exact h.2 j hj hne⟩
  | fail => exact h
  | bug => trivial

theorem runForF_keepsFAt {f : Fld} {x y : Reg} (hxy : y ≠ x) (b : Stm)
    (hb : ∀ s L, (evalF κ b s L).keepsFAt κ f x s L) : ∀ n k s L, (runForF (evalF κ b) y k n s
      L).keepsFAt κ f x s L
  | 0, _, _, _ => ⟨rfl, fun _ _ _ => rfl⟩
  | n + 1, k, s, L => by
    simp only [runForF]
    have hL : (Machine.State.upd L y k) x = L x := by simp only [Machine.State.upd, Ne.symm hxy,
        ↓reduceIte]
    refine Res.keepsFAt_bind ?_ (fun s1 L1 h1 => (runForF_keepsFAt hxy b hb n (k + 1) s1 L1))
    have := Res.keepsFAt_addCost 1 (hb s (Machine.State.upd L y k))
    revert this
    cases (evalF κ b s (Machine.State.upd L y k)).addCost 1 <;> simp only [Res.keepsFAt] <;>
      intro h <;>
      first | trivial | exact ⟨h.1.trans hL, fun j hj hne => h.2 j hj (by rw [hL]; exact hne)⟩

theorem evalF_keepsFAt (f : Fld) (x : Reg) : ∀ (c : Stm) (s : Core) (L : Loc), c.wfAt f x = true →
    c.asg x = false → (evalF κ c s L).keepsFAt κ f x s L
  | .skip, _, _, _, _ => ⟨rfl, fun _ _ _ => rfl⟩
  | .assign y e, s, L, _, h => by
    simp only [Stm.asg, decide_eq_false_iff_not] at h
    simp only [evalF]; split
    · exact ⟨by simp only [Machine.State.upd, Ne.symm h, ↓reduceIte], fun _ _ _ => rfl⟩
    · trivial
  | .wr f' i e, s, L, hw, _ => by
    simp only [evalF]; split
    · next j v hj hv =>
      split
      · next s' hs =>
        refine ⟨rfl, fun j' hj' hne => ?_⟩
        rw [Fld.get_set hs f hj']
        rw [ite_eq_right]
        rintro ⟨rfl, rfl⟩
        simp only [Stm.wfAt, decide_true, Bool.not_true, Bool.false_or, decide_eq_true_eq] at hw
        subst hw; simp only [Exp.ev, Option.some.injEq] at hj; exact hne hj.symm
      · trivial
    · trivial
  | .push t y, s, L, _, h => by
    simp only [Stm.asg, decide_eq_false_iff_not] at h
    simp only [evalF]; split
    · exact ⟨by simp only [Machine.State.upd, Ne.symm h, ↓reduceIte],
        fun j _ _ => Tbl.push_get s t f j⟩
    · trivial
  | .seq a b, s, L, hw, h => by
    simp only [Stm.wfAt, Bool.and_eq_true] at hw
    simp only [Stm.asg, Bool.or_eq_false_iff] at h
    exact Res.keepsFAt_bind (evalF_keepsFAt f x a s L hw.1 h.1) (fun s1 L1 _ => evalF_keepsFAt f
      x b s1 L1 hw.2 h.2)
  | .ite c a b, s, L, hw, h => by
    simp only [Stm.wfAt, Bool.and_eq_true] at hw
    simp only [Stm.asg, Bool.or_eq_false_iff] at h
    simp only [evalF]; split
    · apply Res.keepsFAt_addCost; split
      · exact evalF_keepsFAt f x a s L hw.1 h.1
      · exact evalF_keepsFAt f x b s L hw.2 h.2
    · trivial
  | .loop y n b, s, L, hw, h => by
    simp only [Stm.wfAt, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not] at hw
    simp only [Stm.asg, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    simp only [evalF]; split
    · exact Res.keepsFAt_addCost _ (runForF_keepsFAt hw.1 b (fun s L => evalF_keepsFAt f x b s L
      hw.2 h.2) _ _ s L)
    · trivial
  | .call _ ps b rs args ds, s, L, hw, h => by
    simp only [Stm.wfAt, Bool.not_eq_true'] at hw
    simp only [Stm.asg, decide_eq_false_iff_not] at h
    simp only [evalF]; split
    · next vs _ =>
      have hk := evalF_keepsF (κ := κ) f b s (Machine.State.setLocs (fun _ => 0) ps vs) hw
      split
      · next s' L' c heq =>
        rw [heq] at hk
        exact ⟨setLocs_not_mem h, fun j hj _ => hk j hj⟩
      · next s' L' c heq => rw [heq] at hk; exact ⟨rfl, fun j hj _ => hk j hj⟩
      · trivial
    · trivial
  | .fail, _, _, _, _ => ⟨rfl, fun _ _ _ => rfl⟩
  | .bug, _, _, _, _ => trivial
  | .catch a b, s, L, hw, h => by
    simp only [Stm.wfAt, Bool.and_eq_true] at hw
    simp only [Stm.asg, Bool.or_eq_false_iff] at h
    simp only [evalF]
    have ha := evalF_keepsFAt f x a s L hw.1 h.1
    split
    · next s' L' n heq =>
      rw [heq] at ha
      have hb := Res.keepsFAt_addCost (1 + n) (evalF_keepsFAt f x b s' L' hw.2 h.2)
      revert hb; cases evalF κ b s' L' <;> simp only [Res.addCost, Res.keepsFAt] <;> intro hb <;>
        first | trivial | exact ⟨hb.1.trans ha.1, fun j hj hne => by
          rw [hb.2 j hj (by rw [ha.1]; exact hne)]; exact ha.2 j hj hne⟩
    · next heq => rw [heq] at ha; exact ha
    · trivial
  | .lwr k snd i j e, s, L, _, _ => by
    simp only [evalF]; split
    · split
      · split
        · next s' h => exact ⟨rfl, fun j' hj' _ => LK.set_fld h f j' hj'⟩
        · trivial
      · trivial
    · trivial
  | .lgrow k i a b, s, L, _, _ => by
    simp only [evalF]; split
    · split
      · next s' h => exact ⟨rfl, fun j' hj' _ => LK.set_fld h f j' hj'⟩
      · trivial
    · trivial
  | .lshrink k i, s, L, _, _ => by
    simp only [evalF]; split
    · split
      · split
        · next s' h => exact ⟨rfl, fun j' hj' _ => LK.set_fld h f j' hj'⟩
        · trivial
      · trivial
    · trivial
  | .lclear k i, s, L, _, _ => by
    simp only [evalF]; split
    · split
      · next s' h => exact ⟨rfl, fun j' hj' _ => LK.set_fld h f j' hj'⟩
      · trivial
    · trivial
  | .pwr c j e, s, L, _, _ => by
    simp only [evalF]; split <;> (try split) <;> first | trivial | exact ⟨rfl, fun j _ _ =>
      fld_path f j _⟩
  | .rowReset c, s, L, _, _ => by
    simp only [evalF]; split <;> (try split) <;> first | trivial | exact ⟨rfl, fun j _ _ =>
      fld_path f j _⟩
  | .prepInit c b, s, L, _, _ => by
    simp only [evalF]; split <;> (try split) <;> first | trivial | exact ⟨rfl, fun j _ _ =>
      fld_prep f j _⟩
  | .prepSet h b t, s, L, _, _ => by
    simp only [evalF]; split <;> first | trivial | exact ⟨rfl, fun j _ _ => fld_prep f j _⟩
  | .prepPath j e, s, L, _, _ => by
    simp only [evalF]; split <;> (try split) <;> first | trivial | exact ⟨rfl, fun j _ _ =>
      fld_prep f j _⟩
  | .prepCommit, s, L, _, _ => by
    simp only [evalF]; split <;> first | trivial | exact ⟨rfl, fun j _ _ => fld_pp f j _ _⟩
  | .jobSet x' y z t a b c d, s, L, _, _ => by
    simp only [evalF]; split <;> (try split) <;> first | trivial | exact ⟨rfl, fun j _ _ =>
      fld_job f j _⟩
  | .jobClear, s, L, _, _ => ⟨rfl, fun j _ _ => fld_job f j _⟩
  | .pcSet t a b c d, s, L, _, _ => by
    simp only [evalF]; split <;> (try split) <;> first | trivial | exact ⟨rfl, fun j _ _ =>
      fld_job f j _⟩

/-- **A run that writes `f` only at the index held by `x`** keeps every other value of `f`. -/
theorem evalF_frame_fldAt {c : Stm} {f : Fld} {x : Reg} (hw : c.wfAt f x = true) (hx : c.asg x =
  false)
    {s s' : Core} {L L' : Loc} {n : Nat} (h : evalF κ c s L = .ok s' L' n) {j : Nat} (hj : j <
      f.cap κ)
    (hne : j ≠ L x) : f.get s' j = f.get s j := by
  have := evalF_keepsFAt (κ := κ) f x c s L hw hx; rw [h] at this; exact this.2 j hj hne

end OrderMaintenance.Impl
