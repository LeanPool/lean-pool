/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Machine.Exec


/-!
# Program logic

A weakest-precondition calculus for `exec`, with cost. Nothing here is trusted: every rule is
a theorem about the interpreter.

`wp c Q s` says: from `s`, `c` terminates normally (no `fail`, no machine error), and `Q` holds
of the final state and the number of steps taken. The rules below push `wp` through the
syntax. For a concrete program, `simp only [wp_simps]` turns the goal into a pure
verification condition; each loop needs an invariant (`wp_loop`).
-/


@[expose] public section

namespace OrderMaintenance.Machine

/-- `o` terminated normally and `Q` holds of its final state and cost. -/
def Out.Ok (o : Out) (Q : State → Nat → Prop) : Prop := o.status = .ok ∧ Q o.st o.cost

/-- Normal-termination weakest precondition for a state-and-cost postcondition. -/
def wp (c : Stmt) (Q : State → Nat → Prop) (s : State) : Prop := (exec c s).Ok Q

/-- Hoare triple with a cost bound: from every state satisfying `P`, `c` terminates normally
in at most `k` steps, in a state satisfying `Q`. -/
def Triple (P : State → Prop) (c : Stmt) (Q : State → Prop) (k : Nat) : Prop :=
  ∀ s, P s → wp c (fun s' n => Q s' ∧ n ≤ k) s

@[inherit_doc] notation "⦃" P "⦄ " c " ⦃" Q "⦄≤ " k => Triple P c Q k

/-! ### Outcomes -/

theorem Out.Ok.mono {o : Out} {Q R : State → Nat → Prop} (h : ∀ s n, Q s n → R s n)
    (ho : o.Ok Q) : o.Ok R := ⟨ho.1, h _ _ ho.2⟩

@[simp] theorem Out.ok_mk {s : State} {n : Nat} {st : Status} {Q : State → Nat → Prop} :
    (Out.mk s n st).Ok Q ↔ st = .ok ∧ Q s n := Iff.rfl

theorem Out.ok_bind {o : Out} {g : State → Out} {Q : State → Nat → Prop} :
    (o.bind g).Ok Q ↔ o.Ok (fun s n => (g s).Ok (fun s' m => Q s' (n + m))) := by
  rcases o with ⟨s, n, _ | _ | _⟩ <;> simp [Out.bind, Out.Ok]

/-! ### One rule per construct -/

theorem wp_mono {c : Stmt} {Q R : State → Nat → Prop} {s : State}
    (h : ∀ s n, Q s n → R s n) (hc : wp c Q s) : wp c R s := Out.Ok.mono h hc

theorem wp_skip {Q : State → Nat → Prop} {s : State} : wp .skip Q s ↔ Q s 1 := by
  simp [wp, exec]

theorem wp_assign {x : Reg} {e : Expr} {Q : State → Nat → Prop} {s : State} :
    wp (.assign x e) Q s ↔
      ∃ v, e.eval s = some v ∧ Q ((s.bump (e.maxv s)).setLoc x v) (1 + e.cost) := by
  simp only [wp, exec]; cases e.eval s <;> simp

theorem wp_store {a : Arr} {i e : Expr} {Q : State → Nat → Prop} {s : State} :
    wp (.store a i e) Q s ↔
      ∃ j v, i.eval s = some j ∧ e.eval s = some v ∧ j < s.cap a ∧
        Q (((s.bump (i.maxv s)).bump (e.maxv s)).write a j v) (1 + i.cost + e.cost) := by
  simp only [wp, exec]
  cases i.eval s with
  | none => simp
  | some j =>
    cases e.eval s with
    | none => simp
    | some v => by_cases hj : j < s.cap a <;> simp [hj]

theorem wp_alloc {a : Arr} {n : Expr} {Q : State → Nat → Prop} {s : State} :
    wp (.alloc a n) Q s ↔ ∃ k, n.eval s = some k ∧ Q ((s.bump (n.maxv s)).alloc a k) (1 +
      n.cost) := by
  simp only [wp, exec]; cases n.eval s <;> simp

theorem wp_seq {c d : Stmt} {Q : State → Nat → Prop} {s : State} :
    wp (.seq c d) Q s ↔ wp c (fun s' n => wp d (fun s'' m => Q s'' (n + m)) s') s := by
  simp only [wp, exec, Out.ok_bind]

theorem wp_ite {c : Expr} {t f : Stmt} {Q : State → Nat → Prop} {s : State} :
    wp (.ite c t f) Q s ↔
      ∃ v, c.eval s = some v ∧
        wp (if v ≠ 0 then t else f) (fun s' m => Q s' (1 + c.cost + m)) (s.bump (c.maxv s)) := by
  simp only [wp, exec]
  cases c.eval s with
  | none => simp
  | some v => by_cases hv : v = 0 <;> simp [hv, Out.ok_bind]

theorem wp_fail {Q : State → Nat → Prop} {s : State} : ¬ wp .fail Q s := by
  simp [wp, exec, Out.Ok]

theorem wp_call {nm : String} {ps rs ds : List Reg} {b : Stmt} {args : List Expr}
    {Q : State → Nat → Prop} {s : State} :
    wp (.call nm ps b rs args ds) Q s ↔
      ∃ vs, evalList s args = some vs ∧
        wp b (fun s' m => Q (s'.leave s.loc rs ds) (1 + costList args + ds.length + m))
          ((s.bump (maxvList s args)).enter ps vs) := by
  simp only [wp, exec]
  cases evalList s args with
  | none => simp
  | some vs =>
    simp only [Option.some.injEq, exists_eq_left']
    generalize exec b _ = o
    rcases o with ⟨s', n, _ | _ | _⟩ <;> simp [Out.Ok]

/-- A `catch` whose body terminates normally behaves like the body, plus one step. -/
theorem wp_catch_ok {c h : Stmt} {Q : State → Nat → Prop} {s : State}
    (hc : wp c (fun s' n => Q s' (1 + n)) s) : wp (.catch c h) Q s := by
  unfold wp at *
  simp only [exec]
  rcases hc with ⟨h1, h2⟩
  simp [h1, Out.Ok, h2]

/-- A `catch` whose body fails runs the handler from the state the body reached. -/
theorem wp_catch_fail {c h : Stmt} {Q : State → Nat → Prop} {s : State}
    (hc : (exec c s).status = .fail)
    (hh : wp h (fun s' m => Q s' (1 + (exec c s).cost + m)) (exec c s).st) :
    wp (.catch c h) Q s := by
  unfold wp at *
  simp only [exec, hc]
  exact hh

/-! ### Loops -/

theorem runFor_inv (f : State → Out) (x : Reg) (I : Nat → State → Prop) (kb N : Nat)
    (hb : ∀ k < N, ∀ s, I k s → (f (s.setLoc x k)).Ok (fun s' m => I (k + 1) s' ∧ m ≤ kb)) :
    ∀ n k s, k + n = N → I k s →
      (runFor f x k n s).Ok (fun s' c => I N s' ∧ c ≤ n * (1 + kb)) := by
  intro n
  induction n with
  | zero => intro k s hk hI; subst hk; simp [runFor, hI]
  | succ n ih =>
    intro k s hk hI
    simp only [runFor, Out.ok_bind, Out.ok_mk, true_and]
    refine (hb k (by omega) s hI).mono ?_
    rintro s' m ⟨hI', hm⟩
    refine (ih (k + 1) s' (by omega) hI').mono ?_
    rintro s'' c ⟨hI'', hc⟩
    refine ⟨hI'', ?_⟩
    rw [Nat.succ_mul]
    omega

/-- The loop rule. `N` is the value of the bound, `I k` the invariant before iteration `k`,
and `kb` a bound on the cost of one execution of the body. -/
theorem wp_loop {x : Reg} {n : Expr} {b : Stmt} {Q : State → Nat → Prop} {s : State}
    (N : Nat) (I : Nat → State → Prop) (kb : Nat)
    (hn : n.eval s = some N) (h0 : I 0 (s.bump (n.maxv s)))
    (hb : ∀ k < N, ∀ s, I k s → wp b (fun s' m => I (k + 1) s' ∧ m ≤ kb) (s.setLoc x k))
    (hQ : ∀ s' c, I N s' → c ≤ 1 + n.cost + N * (1 + kb) → Q s' c) :
    wp (.loop x n b) Q s := by
  unfold wp
  simp only [exec, hn, Out.ok_bind, Out.ok_mk, true_and]
  refine (runFor_inv (exec b) x I kb N hb N 0 _ (by omega) h0).mono ?_
  rintro s' c ⟨hI, hc⟩
  exact hQ s' _ hI (by omega)

/-! ### Triples -/

theorem Triple.conseq {P P' Q Q' : State → Prop} {c : Stmt} {k k' : Nat}
    (h : ⦃P⦄ c ⦃Q⦄≤ k) (hP : ∀ s, P' s → P s) (hQ : ∀ s, Q s → Q' s) (hk : k ≤ k') :
    ⦃P'⦄ c ⦃Q'⦄≤ k' :=
  fun s hs => (h s (hP s hs)).mono fun _ _ ⟨hq, hn⟩ => ⟨hQ _ hq, Nat.le_trans hn hk⟩

theorem Triple.seq {P Q R : State → Prop} {c d : Stmt} {k₁ k₂ : Nat}
    (h₁ : ⦃P⦄ c ⦃R⦄≤ k₁) (h₂ : ⦃R⦄ d ⦃Q⦄≤ k₂) : ⦃P⦄ c;; d ⦃Q⦄≤ k₁ + k₂ := by
  intro s hs
  rw [wp_seq]
  refine (h₁ s hs).mono ?_
  rintro s' n ⟨hr, hn⟩
  refine (h₂ s' hr).mono ?_
  rintro s'' m ⟨hq, hm⟩
  exact ⟨hq, Nat.add_le_add hn hm⟩

/-- Use a triple inside a `wp` goal. -/
theorem Triple.wp {P Q : State → Prop} {c : Stmt} {k : Nat} {R : State → Nat → Prop} {s : State}
    (h : ⦃P⦄ c ⦃Q⦄≤ k) (hs : P s) (hR : ∀ s' n, Q s' → n ≤ k → R s' n) : wp c R s :=
  (h s hs).mono fun _ _ ⟨hq, hn⟩ => hR _ _ hq hn

/-! ### Simp sets -/

attribute [simp] State.setLoc State.write State.alloc State.bump State.upd State.enter State.leave
  State.setLocs Expr.eval Expr.cost Expr.maxv BinOp.eval UnOp.eval evalList costList maxvList

end OrderMaintenance.Machine
