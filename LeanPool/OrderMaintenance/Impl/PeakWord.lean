/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Machine.ExecW
public import LeanPool.OrderMaintenance.Impl.PeakRun


/-!
# Theorems A and B on a machine with fixed-width words

`execW w` (`Machine/ExecW.lean`) is `exec` on `w`-bit words: it ends with `.err` as soon as an
evaluated expression has a value `≥ 2^w` (any value `maxv` records).

* `execW_agree`: if the run of `exec c s` computes no value `≥ 2^w` (`dpk c s < 2^w`), then
  `execW w c s = exec c s` (state, cost and status). The proof: `execW_eq_of` for runs whose final
  peak is below `2^w` (every value recorded along the run is at most the final peak), and
  `execW_raise` (the peak is ghost for `execW` too) to pass from the reset peak of `dpk` to any
  initial peak.
* `runMw w`: `runM` on the `w`-bit machine. `runMw_eq`: it agrees with `runM` when every
  operation's peak is below `2^w`.
* `theoremAB_word`: for a valid sequence of `t` operations and `w ≥ 128·⌊log₂(t + 1)⌋ + 1286`, the
  `w`-bit machine runs initialization and every operation exactly as `exec` does, so Theorems A and
  B hold verbatim for it.

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Machine

/-! ### Evaluation on words -/

theorem Expr.evalW_of_lt {w : Nat} {s : State} {e : Expr} (h : e.maxv s < 2 ^ w) :
    e.evalW w s = e.eval s := by simp only [Expr.evalW, h, ↓reduceIte]

theorem Expr.evalW_of_none {w : Nat} {s : State} {e : Expr} (h : e.eval s = none) :
    e.evalW w s = none := by
  unfold Expr.evalW; split
  · exact h
  · rfl

theorem Expr.eval_of_evalW {w : Nat} {s : State} {e : Expr} {v : Nat} (h : e.evalW w s = some v) :
    e.eval s = some v := by
  unfold Expr.evalW at h; split at h
  · exact h
  · cases h

theorem evalListW_of_lt {w : Nat} {s : State} {es : List Expr} (h : maxvList s es < 2 ^ w) :
    evalListW w s es = evalList s es := by simp only [evalListW, h, ↓reduceIte]

theorem evalListW_of_none {w : Nat} {s : State} {es : List Expr} (h : evalList s es = none) :
    evalListW w s es = none := by
  unfold evalListW; split
  · exact h
  · rfl

theorem Expr.evalW_raise (w : Nat) (s : State) (q : Nat) (e : Expr) :
    e.evalW w (s.raise q) = e.evalW w s := by
  simp only [Expr.evalW, Expr.eval_raise, Expr.maxv_raise]

theorem evalListW_raise (w : Nat) (s : State) (q : Nat) (es : List Expr) :
    evalListW w (s.raise q) es = evalListW w s es := by
  simp only [evalListW, evalList_raise, maxvList_raise]

/-! ### The peak is ghost for `execW` -/

/-- As `exec_raise`. -/
theorem execW_raise (w q : Nat) : ∀ (c : Stmt) (s : State), execW w c (s.raise q) = (execW w c s).raise q
  | .skip, s => rfl
  | .assign x e, s => by
    simp only [execW, Expr.evalW_raise, Expr.maxv_raise]
    split <;> simp [Out.raise, State.raise]
  | .store a i e, s => by
    simp only [execW, Expr.evalW_raise, Expr.maxv_raise, State.raise_cap]
    split
    · split
      · simp [Out.raise, State.raise]
      · rfl
    · rfl
  | .alloc a n, s => by
    simp only [execW, Expr.evalW_raise, Expr.maxv_raise]
    split <;> simp [Out.raise, State.raise]
  | .seq c d, s => by
    simp only [execW, execW_raise w q c s]
    exact Out.raise_bind _ q _ _ (fun s => execW_raise w q d s)
  | .ite e t f, s => by
    simp only [execW, Expr.evalW_raise, Expr.maxv_raise]
    split
    · rw [State.raise_bump]
      have : (Out.mk ((s.bump (e.maxv s)).raise q) (1 + e.cost) .ok) =
          (Out.mk (s.bump (e.maxv s)) (1 + e.cost) .ok).raise q := rfl
      rw [this]
      exact Out.raise_bind _ q _ _ (fun s => by split <;> exact execW_raise w q _ s)
    · rfl
  | .loop x n b, s => by
    simp only [execW, Expr.evalW_raise, Expr.maxv_raise]
    split
    · rw [State.raise_bump]
      have : (Out.mk ((s.bump (n.maxv s)).raise q) (1 + n.cost) .ok) =
          (Out.mk (s.bump (n.maxv s)) (1 + n.cost) .ok).raise q := rfl
      rw [this]
      exact Out.raise_bind _ q _ _ (fun s => runFor_raise _ q (fun s => execW_raise w q b s) x _ 0 s)
    · rfl
  | .call nm ps b rs args ds, s => by
    simp only [execW, evalListW_raise, maxvList_raise]
    split
    · next vs _ =>
      rw [State.raise_bump, State.raise_enter, execW_raise w q b]
      generalize execW w b ((s.bump (maxvList s args)).enter ps vs) = o
      rcases o with ⟨st, n, _ | _ | _⟩ <;> rfl
    · rfl
  | .fail, s => rfl
  | .catch c h, s => by
    simp only [execW, execW_raise w q c s]
    cases hc : (execW w c s).status
    · simp [Out.raise, hc]
    · simp only [Out.raise, hc, execW_raise w q h]
    · simp [Out.raise, hc]

/-! ### Agreement -/

theorem Out.bind_ok {o : Out} {g : State → Out} (h : o.status = .ok) :
    o.bind g = ⟨(g o.st).st, o.cost + (g o.st).cost, (g o.st).status⟩ := by
  unfold Out.bind; rw [h]

theorem Out.bind_agree {o : Out} {g g' : State → Out} (h : o.status = .ok → g' o.st = g o.st) :
    o.bind g' = o.bind g := by
  unfold Out.bind; split
  · next hs => rw [h hs]
  · rfl

theorem Out.bind_peak_le {o : Out} {g : State → Out} (hg : ∀ s, s.peak ≤ (g s).st.peak) :
    o.st.peak ≤ (o.bind g).st.peak := by
  unfold Out.bind; split
  · exact hg _
  · exact le_refl _

theorem runFor_peak_le {f : State → Out} (hf : ∀ s, s.peak ≤ (f s).st.peak) (x : Reg) :
    ∀ (n k : Nat) (s : State), s.peak ≤ (runFor f x k n s).st.peak
  | 0, _, _ => le_refl _
  | n + 1, k, s => by
    have e : runFor f x k (n + 1) s =
        (Out.mk (f (s.setLoc x k)).st (1 + (f (s.setLoc x k)).cost) (f (s.setLoc x k)).status).bind
          (runFor f x (k + 1) n) := rfl
    rw [e]
    exact le_trans (hf (s.setLoc x k))
      (Out.bind_peak_le (o := ⟨(f (s.setLoc x k)).st, 1 + (f (s.setLoc x k)).cost, (f (s.setLoc x k)).status⟩)
        (runFor_peak_le hf x n (k + 1)))

theorem runFor_agree {w : Nat} {f f' : State → Out} (hm : ∀ s, s.peak ≤ (f s).st.peak)
    (hf : ∀ s, (f s).st.peak < 2 ^ w → f' s = f s) (x : Reg) :
    ∀ (n k : Nat) (s : State), (runFor f x k n s).st.peak < 2 ^ w → runFor f' x k n s = runFor f x k n s
  | 0, _, _, _ => rfl
  | n + 1, k, s, h => by
    have e : ∀ g : State → Out, runFor g x k (n + 1) s =
        (Out.mk (g (s.setLoc x k)).st (1 + (g (s.setLoc x k)).cost) (g (s.setLoc x k)).status).bind
          (runFor g x (k + 1) n) := fun _ => rfl
    rw [e] at h ⊢; rw [e]
    have h1 : (f (s.setLoc x k)).st.peak < 2 ^ w :=
      lt_of_le_of_lt
        (Out.bind_peak_le (o := ⟨(f (s.setLoc x k)).st, 1 + (f (s.setLoc x k)).cost, (f (s.setLoc x k)).status⟩)
          (runFor_peak_le hm x n (k + 1))) h
    rw [hf _ h1]
    refine Out.bind_agree (fun hs => runFor_agree hm hf x n (k + 1) _ ?_)
    rw [Out.bind_ok hs] at h; exact h

/-- **Agreement for a run whose final peak is below `2^w`**: every value `exec` records is at most
its final peak, so every check of `execW w` passes. -/
theorem execW_eq_of (w : Nat) : ∀ (c : Stmt) (s : State), (exec c s).st.peak < 2 ^ w → execW w c s = exec c s
  | .skip, _, _ => rfl
  | .assign x e, s, h => by
    cases he : e.eval s with
    | none => simp only [execW, exec, Expr.evalW_of_none he, he]
    | some v =>
      simp only [exec, he, State.setLoc, State.bump] at h
      have hm : e.maxv s < 2 ^ w := by omega
      simp only [execW, exec, Expr.evalW_of_lt hm, he]
  | .store a i e, s, h => by
    by_cases hok : ∃ j v, i.eval s = some j ∧ e.eval s = some v ∧ j < s.cap a
    · obtain ⟨j, v, hi, he, hc⟩ := hok
      simp only [exec, hi, he, hc, ↓reduceIte, State.write, State.bump] at h
      have hmi : i.maxv s < 2 ^ w := by omega
      have hme : e.maxv s < 2 ^ w := by omega
      simp only [execW, exec, Expr.evalW_of_lt hmi, Expr.evalW_of_lt hme, hi, he]
    · have hx : exec (.store a i e) s = ⟨s, 1 + i.cost + e.cost, .err⟩ := by
        simp only [exec]; split
        · next j v hi he =>
          split
          · next hc => exact absurd ⟨j, v, hi, he, hc⟩ hok
          · rfl
        · rfl
      rw [hx]; simp only [execW]; split
      · next j v hi he =>
        split
        · next hc => exact absurd ⟨j, v, Expr.eval_of_evalW hi, Expr.eval_of_evalW he, hc⟩ hok
        · rfl
      · rfl
  | .alloc a n, s, h => by
    cases hn : n.eval s with
    | none => simp only [execW, exec, Expr.evalW_of_none hn, hn]
    | some k =>
      simp only [exec, hn, State.alloc, State.bump] at h
      have hm : n.maxv s < 2 ^ w := by omega
      simp only [execW, exec, Expr.evalW_of_lt hm, hn]
  | .seq c d, s, h => by
    simp only [exec] at h
    have hc : (exec c s).st.peak < 2 ^ w := lt_of_le_of_lt (Out.bind_peak_le (peak_le_exec d)) h
    simp only [execW, exec, execW_eq_of w c s hc]
    refine Out.bind_agree (fun hs => execW_eq_of w d _ ?_)
    rw [Out.bind_ok hs] at h; exact h
  | .ite e t f, s, h => by
    cases he : e.eval s with
    | none => simp only [execW, exec, Expr.evalW_of_none he, he]
    | some v =>
      simp only [exec, he] at h
      rw [Out.bind_ok rfl] at h
      have hb : (s.bump (e.maxv s)).peak < 2 ^ w := by
        refine lt_of_le_of_lt ?_ h
        split
        · exact peak_le_exec t _
        · exact peak_le_exec f _
      have hm : e.maxv s < 2 ^ w := by simp only [State.bump] at hb; omega
      simp only [execW, exec, Expr.evalW_of_lt hm, he]
      refine Out.bind_agree (fun _ => ?_)
      by_cases hv : v ≠ 0
      · have e1 : (if v ≠ 0 then exec t else exec f) = exec t := ite_eq_left_of_eq_true _ _ (eq_true hv)
        have e2 : (if v ≠ 0 then execW w t else execW w f) = execW w t := ite_eq_left_of_eq_true _ _ (eq_true hv)
        rw [e1] at h ⊢; rw [e2]; exact execW_eq_of w t _ h
      · have e1 : (if v ≠ 0 then exec t else exec f) = exec f := ite_eq_right_of_eq_false _ _ (eq_false hv)
        have e2 : (if v ≠ 0 then execW w t else execW w f) = execW w f :=
          ite_eq_right_of_eq_false _ _ (eq_false hv)
        rw [e1] at h ⊢; rw [e2]; exact execW_eq_of w f _ h
  | .loop x n b, s, h => by
    cases hn : n.eval s with
    | none => simp only [execW, exec, Expr.evalW_of_none hn, hn]
    | some k =>
      simp only [exec, hn] at h
      rw [Out.bind_ok rfl] at h
      have hb : (s.bump (n.maxv s)).peak < 2 ^ w :=
        lt_of_le_of_lt (runFor_peak_le (peak_le_exec b) x k 0 _) h
      have hm : n.maxv s < 2 ^ w := by simp only [State.bump] at hb; omega
      simp only [execW, exec, Expr.evalW_of_lt hm, hn]
      refine Out.bind_agree (fun _ => ?_)
      exact runFor_agree (peak_le_exec b) (fun s hs => execW_eq_of w b s hs) x k 0 _ h
  | .call nm ps b rs args ds, s, h => by
    cases ha : evalList s args with
    | none => simp only [execW, exec, evalListW_of_none ha, ha]
    | some vs =>
      simp only [exec, ha] at h
      have ho : (exec b ((s.bump (maxvList s args)).enter ps vs)).st.peak < 2 ^ w := by
        split at h <;> exact h
      have hb : ((s.bump (maxvList s args)).enter ps vs).peak < 2 ^ w :=
        lt_of_le_of_lt (peak_le_exec b _) ho
      have hm : maxvList s args < 2 ^ w := by
        simp only [State.enter, State.bump] at hb; omega
      simp only [execW, exec, evalListW_of_lt hm, ha, execW_eq_of w b _ ho]
      rfl
  | .fail, _, _ => rfl
  | .catch c hd, s, h => by
    simp only [exec] at h
    have hc : (exec c s).st.peak < 2 ^ w := by
      split at h
      · exact lt_of_le_of_lt (peak_le_exec hd _) h
      · exact h
    simp only [execW, exec, execW_eq_of w c s hc]
    cases hs : (exec c s).status
    · rfl
    · simp only [hs] at h ⊢; rw [execW_eq_of w hd _ h]
    · rfl

/-- **The `w`-bit machine agrees with `exec`** on every run that computes no value at or above
`2^w`: same final state, cost and status. -/
theorem execW_agree {w : Nat} {c : Stmt} {s : State} (h : dpk c s < 2 ^ w) : execW w c s = exec c s := by
  have e1 := exec_raise s.peak c { s with peak := 0 }
  have e2 := execW_raise w s.peak c { s with peak := 0 }
  rw [raise_reset] at e1 e2
  rw [e1, e2, execW_eq_of w c _ h]

end OrderMaintenance.Machine

namespace OrderMaintenance.Impl

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top OrderMaintenance.Proof.Word
open OrderMaintenance.Machine (Reg Arr State Out exec execW Stmt Same Expr BinOp UnOp wp wpB dpk)

/-! ### The program on `w`-bit words -/

/-- **`runM` on the `w`-bit machine**: the answers and the cost of each operation (`none` if an
operation fails or reaches an error, including a value that does not fit in `w` bits). -/
def runMw (w : Nat) : State → List OrderMaintenance.Spec.Op → Option (List OrderMaintenance.Spec.Ans × List Nat)
  | _, [] => some ([], [])
  | m, op :: ops =>
    if (execW w (opS op) m).status = .ok then
      (runMw w (execW w (opS op) m).st ops).map fun r =>
        (ansOf op (execW w (opS op) m).st :: r.1, (execW w (opS op) m).cost :: r.2)
    else none

/-- `runMw w` agrees with `runM` when no operation computes a value at or above `2^w`. -/
theorem runMw_eq (w : Nat) : ∀ (ops : List OrderMaintenance.Spec.Op) (m : State),
    (∀ i (hi : i < ops.length), dpk (opS ops[i]) (runSt m (ops.take i)) < 2 ^ w) → runMw w m ops = runM m ops
  | [], _, _ => rfl
  | op :: ops, m, h => by
    have h0 : dpk (opS op) m < 2 ^ w := h 0 (by simp)
    have ih := runMw_eq w ops (exec (opS op) m).st (fun i hi => h (i + 1) (by simpa using hi))
    simp only [runMw, runM, OrderMaintenance.Machine.execW_agree h0, ih]

/-- **The program on `w`-bit words agrees with `exec`.** For a valid sequence of `t` operations
and `w ≥ 128·⌊log₂(t + 1)⌋ + 1286`, initialization and every operation run on the `w`-bit machine
exactly as on `exec`. -/
theorem run_word_agree {m₀ : State} {KB w : Nat} (hkb : m₀.loc "kb" = KB) (h4 : 4 ≤ KB) (h512 : KB < 2 ^ 512)
    (ops : List OrderMaintenance.Spec.Op) (hv : OrderMaintenance.Spec.Valid OrderMaintenance.Spec.State.empty ops)
    (hw : 128 * Nat.log2 (ops.length + 1) + 1286 ≤ w) :
    execW w initWS m₀ = exec initWS m₀ ∧ runMw w (exec initWS m₀).st ops = runM (exec initWS m₀).st ops := by
  obtain ⟨hinit, hops, -⟩ := theoremW_M_run hkb h4 h512 ops hv
  exact ⟨OrderMaintenance.Machine.execW_agree (lt_of_lt_of_le hinit (pow2_mono hw)),
    runMw_eq w ops _ (fun i hi => lt_of_lt_of_le (hops i hi) (pow2_mono hw))⟩

/-- **Theorems A and B on `w`-bit words.** For `4 ≤ K_B < 2^512` (in local `kb`), every valid
sequence of `t` operations and every `w ≥ 128·⌊log₂(t + 1)⌋ + 1286`, the `w`-bit machine's run of
initialization and the operations is `exec`'s, and the conclusion of `theoremAB_M` holds verbatim
for it: the specification's answers, initialization within `initB` steps and every operation
within `opB K_B` steps. -/
theorem theoremAB_word {m₀ : State} {KB w : Nat} (hkb : m₀.loc "kb" = KB) (h4 : 4 ≤ KB) (h512 : KB < 2 ^ 512)
    (ops : List OrderMaintenance.Spec.Op) (hv : OrderMaintenance.Spec.Valid OrderMaintenance.Spec.State.empty ops)
    (hw : 128 * Nat.log2 (ops.length + 1) + 1286 ≤ w) :
    (execW w initWS m₀ = exec initWS m₀ ∧ runMw w (exec initWS m₀).st ops = runM (exec initWS m₀).st ops) ∧
    (execW w initWS m₀).status = .ok ∧ (execW w initWS m₀).cost ≤ initB ∧
      ∃ cs, runMw w (execW w initWS m₀).st ops = some (OrderMaintenance.Spec.run OrderMaintenance.Spec.State.empty ops, cs) ∧
        ∀ c ∈ cs, c ≤ opB KB := by
  obtain ⟨hi, hr⟩ := run_word_agree hkb h4 h512 ops hv hw
  rw [hi, hr]
  exact ⟨⟨rfl, rfl⟩, theoremAB_M hkb h4 ops hv⟩

end OrderMaintenance.Impl
