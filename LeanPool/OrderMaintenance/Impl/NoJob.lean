/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.Loop


/-!
# M6: programs that leave the running job alone

Only `jobSet`, `jobClear` and `pcSet` write the optional record `resJob`. A program without them
(`Stm.noJob`) ends, normally or by a failed guard, with the job it started with.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model

def Stm.noJob : Stm → Bool
  | .seq a b => a.noJob && b.noJob
  | .ite _ a b => a.noJob && b.noJob
  | .loop _ _ b => b.noJob
  | .call _ _ b _ _ _ => b.noJob
  | .catch a b => a.noJob && b.noJob
  | .jobSet .. | .jobClear | .pcSet .. => false
  | _ => true

/-- The outcome keeps the job of `s`. -/
def Res.keepsJob (s : Core) : Res → Prop
  | .ok s' _ _ => s'.resJob = s.resJob
  | .fail s' _ _ => s'.resJob = s.resJob
  | .bug => True

theorem Res.keepsJob_addCost {s : Core} {r : Res} (c : Nat) (h : r.keepsJob s) : (r.addCost
  c).keepsJob s := by
  cases r <;> exact h

theorem Res.keepsJob_bind {s : Core} {r : Res} {g : Core → Loc → Res} (h : r.keepsJob s)
    (hg : ∀ s1 L1, (g s1 L1).keepsJob s1) : (r.bind g).keepsJob s := by
  cases r with
  | ok s1 L1 c =>
    simp only [Res.bind]
    have := hg s1 L1
    cases hr : g s1 L1 <;> rw [hr] at this <;> simp only [Res.addCost, Res.keepsJob] at this ⊢ <;>
      exact this.trans h
  | fail => exact h
  | bug => trivial

theorem Res.keepsJob_trans {s s' : Core} {r : Res} (h : r.keepsJob s') (h' : s'.resJob =
  s.resJob) : r.keepsJob s := by
  cases r with
  | ok => exact (show _ = _ from h).trans h'
  | fail => exact (show _ = _ from h).trans h'
  | bug => trivial

theorem Fld.set_resJob {κ : Caps} {s s' : Core} {i v : Nat} {f : Fld} (h : f.set κ s i v = some
  s') :
    s'.resJob = s.resJob := by
  cases f with
  | a k =>
    simp only [Fld.set] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h
    cases k <;> rfl
  | s k =>
    simp only [Fld.set] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h
    cases k <;> rfl
  | _ =>
    simp only [Fld.set] at h
    split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
    subst h
    rfl

theorem LK.set_resJob {κ : Caps} {s s' : Core} {i : Nat} {l : List (Nat × Nat)} {k : LK} (h :
  k.set κ s i l = some s') :
    s'.resJob = s.resJob := by
  simp only [LK.set] at h; split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h;
    subst h; cases k <;> rfl

theorem runForF_keepsJob {κ : Caps} (b : Stm) (x : Machine.Reg)
    (hb : ∀ s L, (evalF κ b s L).keepsJob s) : ∀ n k s L, (runForF (evalF κ b) x k n s L).keepsJob s
  | 0, _, _, _ => rfl
  | n + 1, k, s, L => by
    simp only [runForF]
    exact Res.keepsJob_bind (Res.keepsJob_addCost 1 (hb s _)) (fun s1 L1 => runForF_keepsJob b x
      hb n (k + 1) s1 L1)

theorem evalF_keepsJob (κ : Caps) : ∀ (c : Stm) (s : Core) (L : Loc), c.noJob = true → (evalF κ
  c s L).keepsJob s
  | .skip, _, _, _ => rfl
  | .assign x e, s, L, _ => by simp only [evalF]; split <;> trivial
  | .wr f i e, s, L, _ => by
    simp only [evalF]; split
    · split
      · next s' h => exact Fld.set_resJob h
      · trivial
    · trivial
  | .push t x, s, L, _ => by simp only [evalF]; split <;> (try trivial); cases t <;> rfl
  | .seq a b, s, L, h => by
    simp only [Stm.noJob, Bool.and_eq_true] at h
    exact Res.keepsJob_bind (evalF_keepsJob κ a s L h.1) (fun s1 L1 => evalF_keepsJob κ b s1 L1 h.2)
  | .ite c a b, s, L, h => by
    simp only [Stm.noJob, Bool.and_eq_true] at h
    simp only [evalF]; split
    · apply Res.keepsJob_addCost; split
      · exact evalF_keepsJob κ a s L h.1
      · exact evalF_keepsJob κ b s L h.2
    · trivial
  | .loop x n b, s, L, h => by
    simp only [Stm.noJob] at h
    simp only [evalF]; split
    · exact Res.keepsJob_addCost _ (runForF_keepsJob b x (fun s L => evalF_keepsJob κ b s L h) _
      _ s L)
    · trivial
  | .call _ ps b rs args ds, s, L, h => by
    simp only [Stm.noJob] at h
    simp only [evalF]; split
    · next vs _ =>
      have := evalF_keepsJob κ b s (Machine.State.setLocs (fun _ => 0) ps vs) h
      split <;> simp only [Res.keepsJob] at this ⊢
      all_goals
        rename_i heq
        rw [heq] at this
        exact this
    · trivial
  | .fail, _, _, _ => rfl
  | .bug, _, _, _ => trivial
  | .catch a b, s, L, h => by
    simp only [Stm.noJob, Bool.and_eq_true] at h
    simp only [evalF]
    have ha := evalF_keepsJob κ a s L h.1
    split
    · next s' L' n heq =>
      rw [heq] at ha
      exact Res.keepsJob_trans (Res.keepsJob_addCost _ (evalF_keepsJob κ b s' L' h.2)) ha
    · next heq => rw [heq] at ha; exact ha
    · trivial
  | .lwr k snd i j e, s, L, _ => by
    simp only [evalF]; split
    · split
      · split
        · next s' h => exact LK.set_resJob h
        · trivial
      · trivial
    · trivial
  | .lgrow k i a b, s, L, _ => by
    simp only [evalF]; split
    · split
      · next s' h => exact LK.set_resJob h
      · trivial
    · trivial
  | .lshrink k i, s, L, _ => by
    simp only [evalF]; split
    · split
      · split
        · next s' h => exact LK.set_resJob h
        · trivial
      · trivial
    · trivial
  | .lclear k i, s, L, _ => by
    simp only [evalF]; split
    · split
      · next s' h => exact LK.set_resJob h
      · trivial
    · trivial
  | .pwr c j e, s, L, _ => by simp only [evalF]; split <;> (try split) <;> first | rfl | trivial
  | .rowReset c, s, L, _ => by simp only [evalF]; split <;> (try split) <;> first | rfl | trivial
  | .prepInit c b, s, L, _ => by simp only [evalF]; split <;> (try split) <;> first | rfl | trivial
  | .prepSet h b t, s, L, _ => by simp only [evalF]; split <;> first | rfl | trivial
  | .prepPath j e, s, L, _ => by simp only [evalF]; split <;> (try split) <;> first | rfl | trivial
  | .prepCommit, s, L, _ => by simp only [evalF]; split <;> first | rfl | trivial
  | .jobSet .., _, _, h => by simp only [Stm.noJob, Bool.false_eq_true] at h
  | .jobClear, _, _, h => by simp only [Stm.noJob, Bool.false_eq_true] at h
  | .pcSet .., _, _, h => by simp only [Stm.noJob, Bool.false_eq_true] at h

theorem evalF_resJob {κ : Caps} {c : Stm} {s s' : Core} {L L' : Loc} {n : Nat} (hc : c.noJob = true)
    (h : evalF κ c s L = .ok s' L' n) : s'.resJob = s.resJob := by
  have := evalF_keepsJob κ c s L hc; rw [h] at this; exact this

end OrderMaintenance.Impl
