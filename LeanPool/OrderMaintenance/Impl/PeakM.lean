/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Machine.Logic
public import LeanPool.OrderMaintenance.Impl.Notation


/-!
# Theorem W, option (A), stage A1: the peak of machine code

Tools for the machine-only code (`WrapM`, `RebuildM`, `OpsM`, `InitM`, `NewCore`, `Params`,
`Fresh`), which runs outside the core language and so outside `sim_peak`.

* **The peak is ghost** (`exec_raise`): raising the initial peak raises the final one and changes
  nothing else. So `(exec c s).st.peak = max s.peak (dpk c s)`, where `dpk c s` is the peak of the
  run from `s` with the peak reset to 0: the largest value the run computes (`peak_exec`). This
  is how a statement about one operation is separated from the history (`docs/WORD.md`, option
  (A): status).
* **`wpB B c Q s`**: `wp` with a peak budget: `c` terminates normally, `Q` holds, and every value
  the run computes is at most `B` (precisely: the final peak is at most `max s.peak B`). Its rules
  mirror those of `wp` (`Logic.lean`) and of the state-forgetting rules `wp_*_g` used by the
  machine-only proofs; each adds one side condition per evaluated expression, `maxv ≤ B`.
* **The machine expression lemma** (`Expr.wdM_sound`): the analogue of `Exp.wd_sound` for machine
  expressions, with a width per local and per array, stated only for the leaves the expression
  actually reads (`Expr.LeafB`), so that it applies to states with arbitrary other locals (the
  initial state of `theoremAB_M` is arbitrary).

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Machine

/-! ### The peak is ghost -/

/-- Raise the peak of a state to at least `q`. -/
def State.raise (s : State) (q : Nat) : State := { s with peak := max q s.peak }

def Out.raise (o : Out) (q : Nat) : Out := ⟨o.st.raise q, o.cost, o.status⟩

@[simp] theorem State.raise_mem (s : State) (q : Nat) : (s.raise q).mem = s.mem := rfl
@[simp] theorem State.raise_cap (s : State) (q : Nat) : (s.raise q).cap = s.cap := rfl
@[simp] theorem State.raise_loc (s : State) (q : Nat) : (s.raise q).loc = s.loc := rfl
@[simp] theorem State.raise_peak (s : State) (q : Nat) : (s.raise q).peak = max q s.peak := rfl

theorem Expr.eval_raise (s : State) (q : Nat) : ∀ e : Expr, e.eval (s.raise q) = e.eval s
  | .lit _ => rfl
  | .var _ => rfl
  | .load a i => by simp only [Expr.eval, Expr.eval_raise s q i]; rfl
  | .bin op a b => by simp only [Expr.eval, Expr.eval_raise s q a, Expr.eval_raise s q b]
  | .un op a => by simp only [Expr.eval, Expr.eval_raise s q a]

theorem Expr.maxv_raise (s : State) (q : Nat) : ∀ e : Expr, e.maxv (s.raise q) = e.maxv s
  | .lit _ => rfl
  | .var _ => rfl
  | .load a i => by
    simp only [Expr.maxv, Expr.maxv_raise s q i]
    rw [show Expr.load a i = Expr.load a i from rfl, Expr.eval_raise]
  | .bin op a b => by
    simp only [Expr.maxv, Expr.maxv_raise s q a, Expr.maxv_raise s q b]
    rw [Expr.eval_raise]
  | .un op a => by
    simp only [Expr.maxv, Expr.maxv_raise s q a]
    rw [Expr.eval_raise]

theorem evalList_raise (s : State) (q : Nat) (es : List Expr) :
    evalList (s.raise q) es = evalList s es := by
  simp only [evalList]; congr 1; funext e; exact Expr.eval_raise s q e

theorem maxvList_raise (s : State) (q : Nat) (es : List Expr) :
    maxvList (s.raise q) es = maxvList s es := by
  simp only [maxvList]; congr 1; exact List.map_congr_left (fun e _ => Expr.maxv_raise s q e)

theorem State.raise_bump (s : State) (q v : Nat) : (s.raise q).bump v = (s.bump v).raise q := by
  simp only [State.raise, State.bump]; congr 1; omega

theorem State.raise_setLoc (s : State) (q : Nat) (x : Reg) (v : Nat) :
    (s.raise q).setLoc x v = (s.setLoc x v).raise q := rfl
theorem State.raise_write (s : State) (q : Nat) (a : Arr) (j v : Nat) :
    (s.raise q).write a j v = (s.write a j v).raise q := rfl
theorem State.raise_alloc (s : State) (q : Nat) (a : Arr) (n : Nat) :
    (s.raise q).alloc a n = (s.alloc a n).raise q := rfl
theorem State.raise_enter (s : State) (q : Nat) (ps : List Reg) (vs : List Nat) :
    (s.raise q).enter ps vs = (s.enter ps vs).raise q := rfl
theorem State.raise_leave (s : State) (q : Nat) (c : Reg → Nat) (rs ds : List Reg) :
    (s.raise q).leave c rs ds = (s.leave c rs ds).raise q := rfl

theorem Out.raise_bind (o : Out) (q : Nat) (g g' : State → Out)
    (hg : ∀ s, g (s.raise q) = (g' s).raise q) :
    (o.raise q).bind g = (o.bind g').raise q := by
  rcases o with ⟨st, n, _ | _ | _⟩ <;> simp [Out.raise, Out.bind, hg]

theorem runFor_raise (f : State → Out) (q : Nat) (hf : ∀ s, f (s.raise q) = (f s).raise q)
    (x : Reg) :
    ∀ n k s, runFor f x k n (s.raise q) = (runFor f x k n s).raise q
  | 0, _, _ => rfl
  | n + 1, k, s => by
    simp only [runFor]
    have h1 : (Out.mk (s.raise q) 1 .ok).bind (fun s => f (s.setLoc x k)) =
        ((Out.mk s 1 .ok).bind (fun s => f (s.setLoc x k))).raise q := by
      simp only [Out.bind, State.raise_setLoc, hf]; rfl
    rw [h1]
    exact Out.raise_bind _ q _ _ (fun s => runFor_raise f q hf x n (k + 1) s)

/-- **The peak is ghost**: running from a state with a raised peak gives the same outcome with the
final peak raised the same way. -/
theorem exec_raise (q : Nat) : ∀ (c : Stmt) (s : State), exec c (s.raise q) = (exec c s).raise q
  | .skip, s => rfl
  | .assign x e, s => by
    simp only [exec, Expr.eval_raise, Expr.maxv_raise]
    split <;> simp [Out.raise, State.raise]
  | .store a i e, s => by
    simp only [exec, Expr.eval_raise, Expr.maxv_raise, State.raise_cap]
    split
    · split
      · simp [Out.raise, State.raise]
      · rfl
    · rfl
  | .alloc a n, s => by
    simp only [exec, Expr.eval_raise, Expr.maxv_raise]
    split <;> simp [Out.raise, State.raise]
  | .seq c d, s => by
    simp only [exec, exec_raise q c s]
    exact Out.raise_bind _ q _ _ (fun s => exec_raise q d s)
  | .ite e t f, s => by
    simp only [exec, Expr.eval_raise, Expr.maxv_raise]
    split
    · rw [State.raise_bump]
      have : (Out.mk ((s.bump (e.maxv s)).raise q) (1 + e.cost) .ok) =
          (Out.mk (s.bump (e.maxv s)) (1 + e.cost) .ok).raise q := rfl
      rw [this]
      exact Out.raise_bind _ q _ _ (fun s => by split <;> exact exec_raise q _ s)
    · rfl
  | .loop x n b, s => by
    simp only [exec, Expr.eval_raise, Expr.maxv_raise]
    split
    · rw [State.raise_bump]
      have : (Out.mk ((s.bump (n.maxv s)).raise q) (1 + n.cost) .ok) =
          (Out.mk (s.bump (n.maxv s)) (1 + n.cost) .ok).raise q := rfl
      rw [this]
      exact Out.raise_bind _ q _ _ (fun s => runFor_raise _ q (fun s => exec_raise q b s) x _ 0 s)
    · rfl
  | .call nm ps b rs args ds, s => by
    simp only [exec, evalList_raise, maxvList_raise]
    split
    · next vs _ =>
      rw [State.raise_bump, State.raise_enter, exec_raise q b]
      generalize exec b ((s.bump (maxvList s args)).enter ps vs) = o
      rcases o with ⟨st, n, _ | _ | _⟩ <;> rfl
    · rfl
  | .fail, s => rfl
  | .catch c h, s => by
    simp only [exec, exec_raise q c s]
    cases hc : (exec c s).status
    · simp [Out.raise, hc]
    · simp only [Out.raise, hc, exec_raise q h]
    · simp [Out.raise, hc]

/-- The peak of a run from `s` with the peak reset: the largest value the run computes. -/
def dpk (c : Stmt) (s : State) : Nat := (exec c { s with peak := 0 }).st.peak

theorem raise_reset (s : State) : ({ s with peak := 0 } : State).raise s.peak = s := by
  simp [State.raise]

/-- **The final peak is the initial one or a value the run computes.** -/
theorem peak_exec (c : Stmt) (s : State) : (exec c s).st.peak = max s.peak (dpk c s) := by
  have e := exec_raise s.peak c { s with peak := 0 }
  rw [raise_reset] at e
  rw [e]; rfl

theorem exec_reset (c : Stmt) (s : State) :
    (exec c s).st.mem = (exec c { s with peak := 0 }).st.mem ∧
      (exec c s).st.loc = (exec c { s with peak := 0 }).st.loc ∧
      (exec c s).st.cap = (exec c { s with peak := 0 }).st.cap ∧
      (exec c s).cost = (exec c { s with peak := 0 }).cost ∧
      (exec c s).status = (exec c { s with peak := 0 }).status := by
  have e := exec_raise s.peak c { s with peak := 0 }
  rw [raise_reset] at e
  rw [e]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The peak never decreases. -/
theorem peak_le_exec (c : Stmt) (s : State) : s.peak ≤ (exec c s).st.peak := by
  rw [peak_exec]; exact le_max_left _ _

/-! ### `wp` with a peak budget -/

/-- `c` terminates normally from `s`, `Q` holds, and every value it computes is at most `B`. -/
def wpB (B : Nat) (c : Stmt) (Q : State → Nat → Prop) (s : State) : Prop :=
  wp c (fun s' n => s'.peak ≤ max s.peak B ∧ Q s' n) s

theorem wpB.wp {B : Nat} {c : Stmt} {Q : State → Nat → Prop} {s : State} (h : wpB B c Q s) :
    wp c Q s :=
  wp_mono (fun _ _ h => h.2) h

/-- The final peak of a run with a budget. -/
theorem wpB.peak_le {B : Nat} {c : Stmt} {Q : State → Nat → Prop} {s : State} (h : wpB B c Q s) :
    (exec c s).st.peak ≤ max s.peak B := h.2.1

theorem wpB_mono {B B' : Nat} {c : Stmt} {Q R : State → Nat → Prop} {s : State} (hB : B ≤ B')
    (hQ : ∀ s' n, Q s' n → R s' n) (h : wpB B c Q s) : wpB B' c R s :=
  wp_mono (fun _ _ ⟨h1, h2⟩ => ⟨le_trans h1 (max_le_max (le_refl _) hB), hQ _ _ h2⟩) h

theorem wpB_skip {B : Nat} {Q : State → Nat → Prop} {s : State} (h : Q s 1) : wpB B .skip Q s := by
  unfold wpB; rw [wp_skip]; exact ⟨le_max_left _ _, h⟩

theorem wpB_assign_g {B : Nat} {x : Reg} {e : Expr} {Q : State → Nat → Prop} {s : State} (v : Nat)
    (he : e.eval s = some v) (hB : e.maxv s ≤ B)
    (h : ∀ s', s'.loc = State.upd s.loc x v → s'.mem = s.mem → s'.cap = s.cap → Q s' (1 + e.cost)) :
    wpB B (.assign x e) Q s := by
  unfold wpB; rw [wp_assign]
  exact ⟨v, he, by simp only [State.setLoc, State.bump]; omega, h _ rfl rfl rfl⟩

theorem wpB_store_g {B : Nat} {a : Arr} {i e : Expr} {Q : State → Nat → Prop} {s : State}
    (j v : Nat)
    (hi : i.eval s = some j) (he : e.eval s = some v) (hj : j < s.cap a)
    (hBi : i.maxv s ≤ B) (hBe : e.maxv s ≤ B)
    (h : ∀ s', s'.loc = s.loc → s'.mem = (s.write a j v).mem → s'.cap = s.cap →
      Q s' (1 + i.cost + e.cost)) :
    wpB B (.store a i e) Q s := by
  unfold wpB; rw [wp_store]
  exact ⟨j, v, hi, he, hj, by simp only [State.write, State.bump]; omega, h _ rfl rfl rfl⟩

theorem wpB_alloc_g {B : Nat} {a : Arr} {n : Expr} {Q : State → Nat → Prop} {s : State} (k : Nat)
    (hn : n.eval s = some k) (hB : n.maxv s ≤ B)
    (h : ∀ s', s'.loc = s.loc → s'.mem = (s.alloc a k).mem → s'.cap = (s.alloc a k).cap →
      Q s' (1 + n.cost)) :
    wpB B (.alloc a n) Q s := by
  unfold wpB; rw [wp_alloc]
  exact ⟨k, hn, by simp only [State.alloc, State.bump]; omega, h _ rfl rfl rfl⟩

theorem wpB_seq {B : Nat} {c d : Stmt} {Q : State → Nat → Prop} {s : State}
    (h : wpB B c (fun s' n => wpB B d (fun s'' m => Q s'' (n + m)) s') s) :
    wpB B (.seq c d) Q s := by
  unfold wpB at *; rw [wp_seq]
  refine wp_mono (fun s1 n ⟨h1, h2⟩ => wp_mono (fun s2 m ⟨h3, h4⟩ => ⟨?_, h4⟩) h2) h
  exact le_trans h3 (by omega)

theorem wpB_ite {B : Nat} {c : Expr} {t f : Stmt} {Q : State → Nat → Prop} {s : State} (v : Nat)
    (hc : c.eval s = some v) (hB : c.maxv s ≤ B)
    (h : wpB B (if v ≠ 0 then t else f) (fun s' m => Q s' (1 + c.cost + m)) (s.bump (c.maxv s))) :
    wpB B (.ite c t f) Q s := by
  unfold wpB at *; rw [wp_ite]
  refine ⟨v, hc, wp_mono (fun s' m ⟨h1, h2⟩ => ⟨le_trans h1 ?_, h2⟩) h⟩
  simp only [State.bump]; omega

theorem wpB_call {B : Nat} {nm : String} {ps rs ds : List Reg} {b : Stmt} {args : List Expr}
    {Q : State → Nat → Prop} {s : State} (vs : List Nat) (ha : evalList s args = some vs)
    (hB : maxvList s args ≤ B)
    (h : wpB B b (fun s' m => Q (s'.leave s.loc rs ds) (1 + costList args + ds.length + m))
      ((s.bump (maxvList s args)).enter ps vs)) :
    wpB B (.call nm ps b rs args ds) Q s := by
  unfold wpB at *; rw [wp_call]
  refine ⟨vs, ha, wp_mono (fun s' m ⟨h1, h2⟩ => ⟨le_trans h1 ?_, h2⟩) h⟩
  simp only [State.enter, State.bump]; omega

theorem wpB_catch_ok {B : Nat} {c h : Stmt} {Q : State → Nat → Prop} {s : State}
    (hc : wpB B c (fun s' n => Q s' (1 + n)) s) : wpB B (.catch c h) Q s :=
  wp_catch_ok hc

/-- The loop rule with a budget: the bound's peak and every iteration's within `B`. The invariant
carries the peak bound of the states it describes. -/
theorem wpB_loop {B : Nat} {x : Reg} {n : Expr} {b : Stmt} {Q : State → Nat → Prop} {s : State}
    (N : Nat) (I : Nat → State → Prop) (kb : Nat)
    (hn : n.eval s = some N) (hB : n.maxv s ≤ B) (h0 : I 0 (s.bump (n.maxv s)))
    (hb : ∀ k < N, ∀ s', I k s' → wpB B b (fun s'' m => I (k + 1) s'' ∧ m ≤ kb) (s'.setLoc x k))
    (hQ : ∀ s' c, I N s' → c ≤ 1 + n.cost + N * (1 + kb) → Q s' c) :
    wpB B (.loop x n b) Q s := by
  unfold wpB
  refine wp_loop N (fun k s' => I k s' ∧ s'.peak ≤ max s.peak B) kb hn
    ⟨h0, by simp only [State.bump]; omega⟩
    (fun k hk s' ⟨hI, hp⟩ => ?_) (fun s' c ⟨hI, hp⟩ hc => ⟨hp, hQ s' c hI hc⟩)
  exact wp_mono
    (fun s'' m ⟨h1, h2, h3⟩ => ⟨⟨h2, le_trans h1 (by simp only [State.setLoc]; omega)⟩, h3⟩)
    (hb k hk s' hI)

/-- Lift a `wp` proof whose run computes nothing above `B` (`dpk`). -/
theorem wpB_of_wp {B : Nat} {c : Stmt} {Q : State → Nat → Prop} {s : State} (h : wp c Q s)
    (hd : dpk c s ≤ B) : wpB B c Q s := by
  unfold wpB wp Out.Ok at *
  refine ⟨h.1, ?_, h.2⟩
  rw [peak_exec]; omega

/-! ### Widths of machine expressions -/

/-- The width of a machine expression's value: `Γ x` for a local, `A a` for a cell of array `a`,
`n` for a literal, the operations as in `Exp.wv`. -/
def Expr.wvM (Γ : Reg → Nat) (A : Arr → Nat) (S : Nat) : Expr → Nat
  | .lit n => n
  | .var x => Γ x
  | .load a _ => A a
  | .bin op a b =>
    match op with
    | .add => Max.max (a.wvM Γ A S) (b.wvM Γ A S) + 1
    | .sub | .div | .mod | .shr => a.wvM Γ A S
    | .mul => a.wvM Γ A S + b.wvM Γ A S
    | .shl => a.wvM Γ A S + S
    | .lt | .le | .eq | .and | .or => 1
  | .un op a =>
    match op with
    | .not => 1
    | .msb => a.wvM Γ A S

/-- The width of a machine expression's peak (`maxv`). -/
def Expr.wpM (Γ : Reg → Nat) (A : Arr → Nat) (S : Nat) : Expr → Nat
  | .lit n => n
  | .var x => Γ x
  | .load a i => Max.max (i.wpM Γ A S) (A a)
  | e@(.bin _ a b) => Max.max (Max.max (a.wpM Γ A S) (b.wpM Γ A S)) (e.wvM Γ A S)
  | e@(.un _ a) => Max.max (a.wpM Γ A S) (e.wvM Γ A S)

/-- The leaves an expression reads are small in `s`: each local it reads below `2^(Γ x)`, each
cell it loads below `2^(A a)`, and each shift amount at most `S`. -/
def Expr.LeafB (s : State) (Γ : Reg → Nat) (A : Arr → Nat) (S : Nat) : Expr → Prop
  | .lit _ => True
  | .var x => s.loc x < 2 ^ Γ x
  | .load a i => i.LeafB s Γ A S ∧ ∀ j, i.eval s = some j → j < s.cap a → s.mem a j < 2 ^ A a
  | .bin op a b => a.LeafB s Γ A S ∧ b.LeafB s Γ A S ∧ (op = .shl → (b.eval s).getD 0 ≤ S)
  | .un _ a => a.LeafB s Γ A S

theorem pow_le_max_l (a b : Nat) : 2 ^ a ≤ 2 ^ Max.max a b :=
  Nat.pow_le_pow_right (by decide) (le_max_left a b)
theorem pow_le_max_r (a b : Nat) : 2 ^ b ≤ 2 ^ Max.max a b :=
  Nat.pow_le_pow_right (by decide) (le_max_right a b)

theorem max_lt_pow2 {x y a b : Nat} (hx : x < 2 ^ a) (hy : y < 2 ^ b) :
    Max.max x y < 2 ^ Max.max a b :=
  max_lt (lt_of_lt_of_le hx (pow_le_max_l a b)) (lt_of_lt_of_le hy (pow_le_max_r a b))

/-- **The machine expression lemma.** -/
theorem Expr.wdM_sound {s : State} {Γ : Reg → Nat} {A : Arr → Nat} {S : Nat} :
    ∀ (e : Expr) {v : Nat}, e.LeafB s Γ A S → e.eval s = some v →
      v < 2 ^ e.wvM Γ A S ∧ e.maxv s < 2 ^ e.wpM Γ A S
  | .lit n, v, _, hv => by
    simp only [Expr.eval, Option.some.injEq] at hv; subst hv
    exact ⟨Nat.lt_two_pow_self, by simpa [Expr.maxv, Expr.wpM] using Nat.lt_two_pow_self⟩
  | .var x, v, hl, hv => by
    have hl : s.loc x < 2 ^ Γ x := hl
    simp only [Expr.eval, Option.some.injEq] at hv; subst hv
    exact ⟨hl, by simpa [Expr.maxv, Expr.wpM] using hl⟩
  | .load a i, v, hl, hv => by
    have hv' := hv
    simp only [Expr.eval, Option.bind_eq_some_iff] at hv
    obtain ⟨j, hj, hv⟩ := hv
    split at hv
    · next hc =>
      cases hv
      have hm := hl.2 j hj hc
      obtain ⟨-, hip⟩ := Expr.wdM_sound i hl.1 hj
      refine ⟨hm, ?_⟩
      simp only [Expr.maxv, Expr.wpM, hv', Option.getD_some]
      exact max_lt_pow2 hip hm
    · simp at hv
  | .bin op a b, v, hl, hv => by
    have hv' := hv
    simp only [Expr.eval, Option.bind_eq_some_iff] at hv
    obtain ⟨x, hx, y, hy, hv⟩ := hv
    obtain ⟨hla, hlb, hsh⟩ := hl
    obtain ⟨hxa, hpa⟩ := Expr.wdM_sound a hla hx
    obtain ⟨hyb, hpb⟩ := Expr.wdM_sound b hlb hy
    have hw : v < 2 ^ (Expr.bin op a b).wvM Γ A S := by
      cases op <;> simp only [BinOp.eval, Option.some.injEq] at hv <;> simp only [Expr.wvM]
      · subst hv
        have h1 := lt_of_lt_of_le hxa (pow_le_max_l (a.wvM Γ A S) (b.wvM Γ A S))
        have h2 := lt_of_lt_of_le hyb (pow_le_max_r (a.wvM Γ A S) (b.wvM Γ A S))
        rw [pow_succ]; omega
      · split at hv
        · cases hv; omega
        · simp at hv
      · subst hv; rw [pow_add]; exact Nat.mul_lt_mul'' hxa hyb
      · subst hv; exact lt_of_le_of_lt (Nat.div_le_self _ _) hxa
      · subst hv; exact lt_of_le_of_lt (Nat.mod_le _ _) hxa
      · subst hv
        have hS := hsh rfl
        rw [hy, Option.getD_some] at hS
        rw [pow_add]
        exact Nat.mul_lt_mul_of_lt_of_le hxa
          (Nat.pow_le_pow_right (by decide) hS) (Nat.two_pow_pos _)
      · subst hv; exact lt_of_le_of_lt (Nat.div_le_self _ _) hxa
      all_goals (subst hv; split <;> decide)
    refine ⟨hw, ?_⟩
    simp only [Expr.maxv, Expr.wpM, hv', Option.getD_some]
    exact max_lt_pow2 (max_lt_pow2 hpa hpb) hw
  | .un op a, v, hl, hv => by
    have hv' := hv
    simp only [Expr.eval, Option.map_eq_some_iff] at hv
    obtain ⟨x, hx, hv⟩ := hv
    obtain ⟨hxa, hpa⟩ := Expr.wdM_sound a hl hx
    have hw : v < 2 ^ (Expr.un op a).wvM Γ A S := by
      subst hv
      cases op <;> simp only [UnOp.eval, Expr.wvM]
      · split <;> decide
      · exact lt_of_le_of_lt (Nat.log2_le_self x) hxa
    refine ⟨hw, ?_⟩
    simp only [Expr.maxv, Expr.wpM, hv', Option.getD_some]
    exact max_lt_pow2 hpa hw

theorem maxvList_lt {s : State} {Γ : Reg → Nat} {A : Arr → Nat} {S W : Nat} :
    ∀ {es : List Expr} {vs : List Nat}, (∀ e ∈ es, e.LeafB s Γ A S ∧ e.wpM Γ A S ≤ W) →
      evalList s es = some vs → maxvList s es < 2 ^ W
  | [], _, _, _ => by simp [maxvList]
  | e :: es, vs, h, hv => by
    simp only [evalList, List.mapM_cons] at hv
    cases he : e.eval s with
    | none => simp [he] at hv
    | some v =>
      cases hes : es.mapM (·.eval s) with
      | none => simp [he, hes] at hv
      | some ws =>
        have h1 := (Expr.wdM_sound e (h e (by simp)).1 he).2
        have h2 := maxvList_lt (es := es) (fun e' he' => h e' (by simp [he'])) hes
        simp only [maxvList, List.map_cons, List.foldr_cons] at h2 ⊢
        exact max_lt (lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) (h e (by simp)).2)) h2

end OrderMaintenance.Machine
