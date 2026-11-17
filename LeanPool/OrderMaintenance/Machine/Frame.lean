/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Machine.Exec


/-!
# The arrays a statement may change

`Stmt.arrs c` lists the arrays that `c` stores to or allocates. Running `c` leaves every other
array unchanged, contents and capacity (`exec_frame`), whatever the outcome.
-/


@[expose] public section

namespace OrderMaintenance.Machine

/-- The arrays that `c` stores to or allocates, syntactically. -/
def Stmt.arrs : Stmt → List Arr
  | .skip => []
  | .assign _ _ => []
  | .store a _ _ => [a]
  | .alloc a _ => [a]
  | .seq c d => c.arrs ++ d.arrs
  | .ite _ t f => t.arrs ++ f.arrs
  | .loop _ _ b => b.arrs
  | .call _ _ b _ _ _ => b.arrs
  | .fail => []
  | .catch c h => c.arrs ++ h.arrs

/-- Array `b` is unchanged from `s` to `s'`. -/
def Same (b : Arr) (s s' : State) : Prop := s'.mem b = s.mem b ∧ s'.cap b = s.cap b

theorem Same.trans {b : Arr} {s t u : State} (h1 : Same b s t) (h2 : Same b t u) : Same b s u :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

/-- A statement preserves the value of a local, including on abnormal termination. -/
def PreservesLocal (c : Stmt) (x : Reg) : Prop :=
  ∀ s, (exec c s).st.loc x = s.loc x

theorem preservesLocal_skip (x : Reg) : PreservesLocal .skip x := fun _ => rfl

theorem preservesLocal_assign {x y : Reg} (hxy : x ≠ y) (e : Expr) :
    PreservesLocal (.assign y e) x := by
  intro s
  simp only [exec]
  split
  · simp [State.setLoc, State.upd, State.bump, hxy]
  · rfl

theorem PreservesLocal.seq {a b : Stmt} {x : Reg}
    (ha : PreservesLocal a x) (hb : PreservesLocal b x) : PreservesLocal (.seq a b) x := by
  intro s
  simp only [exec, Out.bind]
  split
  · exact (hb _).trans (ha s)
  · exact ha s

theorem runFor_frame {f : State → Out} {x : Reg} {b : Arr} (hf : ∀ s, Same b s (f s).st) :
    ∀ n k s, Same b s (runFor f x k n s).st
  | 0, _, _ => ⟨rfl, rfl⟩
  | n + 1, k, s => by
    simp only [runFor, Out.bind]
    have h1 := hf (s.setLoc x k)
    cases hs : (f (s.setLoc x k)).status <;> simp only
    · exact (show Same b s (s.setLoc x k) from ⟨rfl, rfl⟩).trans (h1.trans (runFor_frame hf n
      (k + 1) _))
    · exact (show Same b s (s.setLoc x k) from ⟨rfl, rfl⟩).trans h1
    · exact (show Same b s (s.setLoc x k) from ⟨rfl, rfl⟩).trans h1

/-- **The frame of a statement**: arrays it does not mention are unchanged. -/
theorem exec_frame : ∀ (c : Stmt) (s : State) (b : Arr), b ∉ c.arrs → Same b s (exec c s).st
  | .skip, s, b, _ => ⟨rfl, rfl⟩
  | .assign x e, s, b, _ => by
    simp only [exec]; split <;> exact ⟨rfl, rfl⟩
  | .store a i e, s, b, hb => by
    simp only [Stmt.arrs, List.mem_singleton] at hb
    simp only [exec]
    split
    · split
      · simp only [State.write, State.bump]; exact ⟨by simp [hb], rfl⟩
      · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  | .alloc a n, s, b, hb => by
    simp only [Stmt.arrs, List.mem_singleton] at hb
    simp only [exec]
    split
    · simp only [State.alloc, State.bump]; exact ⟨by simp [hb], by simp [State.upd, hb]⟩
    · exact ⟨rfl, rfl⟩
  | .seq c d, s, b, hb => by
    simp only [Stmt.arrs, List.mem_append, not_or] at hb
    simp only [exec, Out.bind]
    have h1 := exec_frame c s b hb.1
    cases hs : (exec c s).status <;> simp only
    · exact h1.trans (exec_frame d _ b hb.2)
    · exact h1
    · exact h1
  | .ite e t f, s, b, hb => by
    simp only [Stmt.arrs, List.mem_append, not_or] at hb
    simp only [exec]
    split
    · simp only [Out.bind]
      split
      · exact (show Same b s (s.bump _) from ⟨rfl, rfl⟩).trans (exec_frame t _ b hb.1)
      · exact (show Same b s (s.bump _) from ⟨rfl, rfl⟩).trans (exec_frame f _ b hb.2)
    · exact ⟨rfl, rfl⟩
  | .loop x n body, s, b, hb => by
    simp only [Stmt.arrs] at hb
    simp only [exec]
    split
    · simp only [Out.bind]
      exact (show Same b s (s.bump _) from ⟨rfl, rfl⟩).trans
        (runFor_frame (fun s => exec_frame body s b hb) _ 0 _)
    · exact ⟨rfl, rfl⟩
  | .call nm ps body rs args ds, s, b, hb => by
    simp only [Stmt.arrs] at hb
    simp only [exec]
    split
    · next vs _ =>
      have h1 := exec_frame body ((s.bump (maxvList s args)).enter ps vs) b hb
      split <;> exact h1
    · exact ⟨rfl, rfl⟩
  | .fail, s, b, _ => ⟨rfl, rfl⟩
  | .catch c h, s, b, hb => by
    simp only [Stmt.arrs, List.mem_append, not_or] at hb
    simp only [exec]
    have h1 := exec_frame c s b hb.1
    split
    · exact h1.trans (exec_frame h _ b hb.2)
    · exact h1

end OrderMaintenance.Machine
