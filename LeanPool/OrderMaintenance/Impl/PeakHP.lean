/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.PeakSafe


/-!
# Theorem W, option (A), stage A2: composing peak bounds along a known run

`PK Γ W c s L`: the run of `c` from `(s, L)` computes nothing at or above `2^W`, and a normal end
satisfies the invariant `Gd Γ`. Safe statements have it (`PK.of_safe`); the rules below compose
it along a run whose intermediate states are known (from the agreement lemmas), and the
statements that store a computed value (`PK.assign`, `PK.wr`, …) take the bound of that value as
a hypothesis. These are the rules the per-procedure proofs of stage A2 use.

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg BinOp UnOp State)

variable {K KH : Nat} {κ : Caps}

/-- **The peak bound of a run, with the invariant at its normal end**, for a run that does not
hit a bug. -/
def PK (K KH : Nat) (κ : Caps) (Γ : Reg → Nat) (W : Nat) (c : Stm) (s : Core) (L : Loc) : Prop :=
  evalF κ c s L ≠ .bug → pkF κ c s L < 2 ^ W ∧ ∀ s' L' n, evalF κ c s L = .ok s' L' n → Gd K KH
    κ Γ s' L'

section rules
variable {Γ Γ' : Reg → Nat} {W : Nat} {s s1 : Core} {L L1 : Loc}

theorem PK.lt {c : Stm} (h : PK K KH κ Γ W c s L) {s' : Core} {L' : Loc} {n : Nat}
    (he : evalF κ c s L = .ok s' L' n) : pkF κ c s L < 2 ^ W := (h (by rw [he]; simp)).1

theorem PK.post {c : Stm} (h : PK K KH κ Γ W c s L) {s' : Core} {L' : Loc} {n : Nat}
    (he : evalF κ c s L = .ok s' L' n) : Gd K KH κ Γ s' L' := (h (by rw [he]; simp)).2 _ _ _ he

theorem PK.of_safe (hC : CapsW K κ) (hK : 3 ≤ K) (hW : K ≤ W) {c : Stm} (hS : c.Safe K KH Γ W)
    (hG : Gd K KH κ Γ s L) : PK K KH κ Γ W c s L := fun hnb =>
  let h := Stm.safe_run hC hK hW c hS hG hnb
  ⟨h.1, h.2.1⟩

theorem Gd.mono {Γ Γ' : Reg → Nat} {s : Core} {L : Loc} (h : Gd K KH κ Γ s L) (hΓ : ∀ x, Γ x ≤
  Γ' x) :
    Gd K KH κ Γ' s L :=
  ⟨h.enc, h.vb, fun x => pow_mono_lt (h.loc x) (hΓ x)⟩

theorem PK.mono {c : Stm} (h : PK K KH κ Γ W c s L) {W' : Nat} (hW : W ≤ W') (hΓ : ∀ x, Γ x ≤ Γ'
  x) :
    PK K KH κ Γ' W' c s L := fun hnb =>
  ⟨pow_mono_lt (h hnb).1 hW, fun _ _ _ he => ((h hnb).2 _ _ _ he).mono hΓ⟩

theorem PK.seq {c d : Stm} (hc : PK K KH κ Γ' W c s L)
    (hd : ∀ s1 L1 n1, evalF κ c s L = .ok s1 L1 n1 → PK K KH κ Γ W d s1 L1) : PK K KH κ Γ W (c;;
      d) s L := by
  intro hnb
  cases h1 : evalF κ c s L with
  | ok s1 L1 n1 =>
    have hnb2 : evalF κ d s1 L1 ≠ .bug := by
      intro e; apply hnb; simp only [evalF, Res.bind, h1, Res.addCost, e]
    obtain ⟨q1, q2⟩ := hd _ _ _ h1 hnb2
    refine ⟨by rw [pkF_seq_ok h1]; exact max_lt (hc (by rw [h1]; simp)).1 q1, fun s' L' n h => ?_⟩
    simp only [evalF, h1, Res.bind] at h
    revert h; cases h2 : evalF κ d s1 L1 <;> simp only [Res.addCost, Res.ok.injEq, and_imp,
        reduceCtorEq, IsEmpty.forall_iff]
    intro e1 e2 _; subst e1; subst e2; exact q2 _ _ _ h2
  | fail s1 L1 n1 =>
    exact ⟨by rw [pkF_seq_fail h1]; exact (hc (by rw [h1]; simp)).1,
      fun s' L' n h => by simp only [evalF, Res.bind, h1, reduceCtorEq] at h⟩
  | bug => simp only [evalF, Res.bind, h1, ne_eq, not_true_eq_false] at hnb

theorem PK.seq_g {c d : Stm} (hc : PK K KH κ Γ' W c s L)
    (hd : ∀ s1 L1 n1, evalF κ c s L = .ok s1 L1 n1 → Gd K KH κ Γ' s1 L1 → PK K KH κ Γ W d s1 L1) :
    PK K KH κ Γ W (c;; d) s L :=
  PK.seq hc (fun s1 L1 n1 h => hd s1 L1 n1 h (hc.post h))

theorem PK.seq_ok {c d : Stm} {n1 : Nat} (h1 : evalF κ c s L = .ok s1 L1 n1) (hc : PK K KH κ Γ'
  W c s L)
    (hd : PK K KH κ Γ W d s1 L1) : PK K KH κ Γ W (c;; d) s L :=
  PK.seq hc (fun s2 L2 n2 h => by rw [h1] at h; cases h; exact hd)

theorem PK.ite {c : Exp} {t f : Stm} {v : Nat} (hv : c.ev κ s L = some v) (hp : c.pk κ s L < 2 ^ W)
    (ht : v ≠ 0 → PK K KH κ Γ W t s L) (hf : v = 0 → PK K KH κ Γ W f s L) : PK K KH κ Γ W (.ite
      c t f) s L := by
  intro hnb
  by_cases h0 : v ≠ 0
  · have hnb' : evalF κ t s L ≠ .bug := by
      intro e; apply hnb; simp only [evalF, hv, Res.addCost, ne_eq, h0, not_false_eq_true,
          ↓reduceIte, e]
    obtain ⟨p1, p2⟩ := ht h0 hnb'
    refine ⟨by rw [pkF_ite hv, ite_eq_left h0]; exact max_lt hp p1, fun s' L' n h => ?_⟩
    simp only [evalF, hv, ite_eq_left h0] at h
    revert h; cases h2 : evalF κ t s L <;> simp only [Res.addCost, Res.ok.injEq, and_imp,
        reduceCtorEq, IsEmpty.forall_iff]
    intro e1 e2 _; subst e1; subst e2; exact p2 _ _ _ h2
  · have hnb' : evalF κ f s L ≠ .bug := by
      intro e; apply hnb; simp only [evalF, hv, Res.addCost, h0, ↓reduceIte, e]
    obtain ⟨p1, p2⟩ := hf (not_not.mp h0) hnb'
    refine ⟨by rw [pkF_ite hv, ite_eq_right h0]; exact max_lt hp p1, fun s' L' n h => ?_⟩
    simp only [evalF, hv, ite_eq_right h0] at h
    revert h; cases h2 : evalF κ f s L <;> simp only [Res.addCost, Res.ok.injEq, and_imp,
        reduceCtorEq, IsEmpty.forall_iff]
    intro e1 e2 _; subst e1; subst e2; exact p2 _ _ _ h2

theorem PK.skip (hG : Gd K KH κ Γ s L) : PK K KH κ Γ W .skip s L := fun _ =>
  ⟨by simp only [pkF, Nat.ofNat_pos, pow_pos], fun s' L' n h => by
    simp only [evalF, Res.ok.injEq] at h; obtain ⟨rfl, rfl, -⟩ := h; exact hG⟩

theorem PK.fail : PK K KH κ Γ W .fail s L := fun _ => ⟨by
  simp only [pkF, Nat.ofNat_pos, pow_pos], fun s' L' n h => by
    simp only [evalF, reduceCtorEq] at h⟩

theorem PK.bug : PK K KH κ Γ W .bug s L := fun h => absurd rfl h

theorem PK.assign {x : Reg} {e : Exp} {v : Nat} (hG : Gd K KH κ Γ s L) (hv : e.ev κ s L = some v)
    (hp : e.pk κ s L < 2 ^ W) (hx : v < 2 ^ Γ x) : PK K KH κ Γ W (x ::= e) s L := fun _ =>
  ⟨hp, fun s' L' n h => by
    simp only [evalF, hv, Res.ok.injEq] at h; obtain ⟨rfl, rfl, -⟩ := h; exact ⟨hG.enc, hG.vb,
      upd_lt hG.loc hx⟩⟩

theorem PK.wr {f : Fld} {i e : Exp} {j v : Nat} (hG : Gd K KH κ Γ s L) (hi : i.ev κ s L = some j)
    (he : e.ev κ s L = some v) (hpi : i.pk κ s L < 2 ^ W) (hpe : e.pk κ s L < 2 ^ W) (hv : v < 2
      ^ f.wd K KH) :
    PK K KH κ Γ W (.wr f i e) s L := by
  refine fun _ => ⟨max_lt hpi hpe, fun s' L' n h => ?_⟩
  have h' := h
  simp only [evalF, hi, he] at h
  split at h
  · next s1 hs1 =>
    simp only [Res.ok.injEq] at h; obtain ⟨rfl, rfl, -⟩ := h
    exact ⟨hG.enc.of_ok h', hG.vb.set hs1 hv, hG.loc⟩
  · cases h

theorem PK.catch_bug {c : Stm} (hc : PK K KH κ Γ W c s L) : PK K KH κ Γ W (.catch c .bug) s L := by
  intro hnb
  cases h1 : evalF κ c s L with
  | ok s1 L1 n1 =>
    refine ⟨by rw [pkF_catch_ok h1]; exact (hc (by rw [h1]; simp)).1, fun s' L' n e => ?_⟩
    simp only [evalF, h1, Res.ok.injEq] at e
    obtain ⟨rfl, rfl, -⟩ := e
    exact (hc (by rw [h1]; simp)).2 _ _ _ h1
  | fail s1 L1 n1 =>
    refine ⟨?_, fun s' L' n e => by simp only [evalF, h1, Res.addCost, reduceCtorEq] at e⟩
    rw [pkF_catch_fail h1]
    simp only [pkF]
    exact max_lt (hc (by rw [h1]; simp)).1 (Nat.two_pow_pos _)
  | bug => simp only [evalF, h1, ne_eq, not_true_eq_false] at hnb

/-- **A call**: the arguments, the body from the callee's frame, and the results copied back. -/
theorem PK.call {q : Proc} {args : List Exp} {ds : List Reg} {vs : List Nat} {Γc : Reg → Nat}
    (hG : Gd K KH κ Γ s L) (ha : evList κ s L args = some vs) (hpa : pkList κ s L args < 2 ^ W)
    (hb : PK K KH κ Γc W q.body s (Machine.State.setLocs (fun _ => 0) q.params vs))
    (hr : ∀ r ∈ q.rets, Γc r ≤ K) (hd : ∀ d ∈ ds, K ≤ Γ d) : PK K KH κ Γ W (q.call args ds) s L
      := by
  intro hnb
  have hnb' : evalF κ q.body s (Machine.State.setLocs (fun _ => 0) q.params vs) ≠ .bug := by
    intro e; apply hnb; simp only [Proc.call, evalF, ha, e]
  obtain ⟨b1, b2⟩ := hb hnb'
  refine ⟨by rw [pkF_call ha]; exact max_lt hpa b1, fun s' L' n h => ?_⟩
  simp only [Proc.call, evalF, ha] at h
  revert h; cases h2 : evalF κ q.body s (Machine.State.setLocs (fun _ => 0) q.params vs) <;>
    simp only [
      Res.ok.injEq,
      and_imp,
      reduceCtorEq,
      IsEmpty.forall_iff]
  intro e1 e2 _; subst e1; subst e2
  obtain ⟨g1, g2, g3⟩ := b2 _ _ _ h2
  refine ⟨g1, g2, setLocs_lt hG.loc hd ?_⟩
  intro v hv
  simp only [List.mem_map] at hv
  obtain ⟨r, hr', rfl⟩ := hv
  exact pow_mono_lt (g3 r) (hr r hr')

/-- **A loop**, with an invariant `I k` before iteration `k` that gives the invariant `Gd` and the
body's peak bound. -/
theorem PK.loop {x : Reg} {n : Exp} {b : Stm} {N : Nat} (hn : n.ev κ s L = some N) (hp : n.pk κ
  s L < 2 ^ W)
    (I : Nat → Core → Loc → Prop) (h0 : I 0 s L) (hI : ∀ k s L, I k s L → Gd K KH κ Γ s L)
    (hb : ∀ k s L, k < N → I k s L → PK K KH κ Γ W b s (Machine.State.upd L x k) ∧
      ∀ s' L' c, evalF κ b s (Machine.State.upd L x k) = .ok s' L' c → I (k + 1) s' L') :
    PK K KH κ Γ W (.loop x n b) s L := by
  intro hnb
  -- the iterations `k, …, N - 1`
  have key : ∀ m k s L, k + m = N → I k s L → runForF (evalF κ b) x k m s L ≠ .bug →
      pkFor (evalF κ b) (pkF κ b) x k m s L < 2 ^ W ∧
      ∀ s' L' c, runForF (evalF κ b) x k m s L = .ok s' L' c → Gd K KH κ Γ s' L' := by
    intro m
    induction m with
    | zero =>
      intro k s L _ hIk _
      exact ⟨by simp only [pkFor, Nat.ofNat_pos, pow_pos], fun s' L' c h => by
        simp only [runForF, Res.ok.injEq] at h; obtain ⟨rfl, rfl, -⟩ := h; exact hI k s L hIk⟩
    | succ m ih =>
      intro k s L hk hIk hnb
      obtain ⟨hpk, p3⟩ := hb k s L (by omega) hIk
      simp only [pkFor]
      simp only [runForF] at hnb ⊢
      cases h1 : evalF κ b s (Machine.State.upd L x k) with
      | ok s1 L1 c1 =>
        obtain ⟨p1, -⟩ := hpk (by rw [h1]; simp)
        have hnb2 : runForF (evalF κ b) x (k + 1) m s1 L1 ≠ .bug := by
          intro e; apply hnb; simp only [Res.bind, Res.addCost, h1, e]
        obtain ⟨q1, q2⟩ := ih (k + 1) s1 L1 (by omega) (p3 _ _ _ h1) hnb2
        refine ⟨max_lt p1 q1, fun s' L' c h => ?_⟩
        simp only [Res.addCost, Res.bind] at h
        revert h; cases h2 : runForF (evalF κ b) x (k + 1) m s1 L1 <;> simp only [Res.ok.injEq,
            and_imp,
            reduceCtorEq,
            IsEmpty.forall_iff]
        intro e1 e2 _; subst e1; subst e2; exact q2 _ _ _ h2
      | fail s1 L1 c1 =>
        obtain ⟨p1, -⟩ := hpk (by rw [h1]; simp)
        exact ⟨max_lt p1 (by simp), fun s' L' c h => by
          simp only [Res.bind, Res.addCost, reduceCtorEq] at h⟩
      | bug => simp only [Res.bind, Res.addCost, h1, ne_eq, not_true_eq_false] at hnb
  have hnb' : runForF (evalF κ b) x 0 N s L ≠ .bug := by
    intro e; apply hnb; simp only [evalF, hn, Res.addCost, e]
  obtain ⟨k1, k2⟩ := key N 0 s L (by omega) h0 hnb'
  refine ⟨by simp only [pkF, Exp.val_of hn]; exact max_lt hp k1, fun s' L' c h => ?_⟩
  simp only [evalF, hn] at h
  revert h; cases h2 : runForF (evalF κ b) x 0 N s L <;> simp only [Res.addCost, Res.ok.injEq,
      and_imp, reduceCtorEq,
      IsEmpty.forall_iff]
  intro e1 e2 _; subst e1; subst e2; exact k2 _ _ _ h2

end rules

/-! ### Expressions under the invariant, with any width -/

section exps
variable {Γ : Reg → Nat} {s : Core} {L : Loc}

/-- The peak of an expression (shifts allowed, with their amounts at most `K`). -/
theorem Gd.pkS (hG : Gd K KH κ Γ s L) (hC : CapsW K κ) {e : Exp} (hs : e.ShOK κ s L K) {v : Nat}
    (hv : e.ev κ s L = some v) {W : Nat} (hw : e.wq Γ K KH K ≤ W) : e.pk κ s L < 2 ^ W :=
  pow_mono_lt (Exp.wq_sound (hG.memW hC) hC hG.loc e hs hv) hw

theorem Gd.valS (hG : Gd K KH κ Γ s L) (hC : CapsW K κ) {e : Exp} (hs : e.ShOK κ s L K) {v : Nat}
    (hv : e.ev κ s L = some v) {w : Nat} (hw : e.vw Γ K KH K ≤ w) : v < 2 ^ w :=
  pow_mono_lt (Exp.vw_sound (hG.memW hC) hC hG.loc e hs hv) hw

end exps

/-! ### Normal runs only -/

/-- **`PK` for a normal run**: if the run of `c` ends normally, it computed nothing at or above
`2^W` and ends with the invariant. Enough for the machine theorem (every core call there ends
normally), and it lets a proof use what the end state of the run satisfies. -/
def PKok (K KH : Nat) (κ : Caps) (Γ : Reg → Nat) (W : Nat) (c : Stm) (s : Core) (L : Loc) : Prop :=
  ∀ s' L' n, evalF κ c s L = .ok s' L' n → pkF κ c s L < 2 ^ W ∧ Gd K KH κ Γ s' L'

section okrules
variable {Γ Γ' : Reg → Nat} {W : Nat} {s s1 : Core} {L L1 : Loc}

theorem PK.ok {c : Stm} (h : PK K KH κ Γ W c s L) : PKok K KH κ Γ W c s L := fun _ _ _ he =>
  ⟨h.lt he, h.post he⟩

theorem PKok.seq {c d : Stm} (hc : PKok K KH κ Γ' W c s L)
    (hd : ∀ s1 L1 n1, evalF κ c s L = .ok s1 L1 n1 → Gd K KH κ Γ' s1 L1 → PKok K KH κ Γ W d s1 L1) :
    PKok K KH κ Γ W (c;; d) s L := by
  intro s' L' n h
  obtain ⟨s1, L1, n1, n2, h1, h2⟩ := evalF_seq_inv' h
  obtain ⟨p1, g1⟩ := hc _ _ _ h1
  obtain ⟨q1, q2⟩ := hd _ _ _ h1 g1 _ _ _ h2
  exact ⟨by rw [pkF_seq_ok h1]; exact max_lt p1 q1, q2⟩
where
  evalF_seq_inv' {c d : Stm} {s s' : Core} {L L' : Loc} {n : Nat} (h : evalF κ (c;; d) s L = .ok
    s' L' n) :
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

theorem PKok.ite {c : Exp} {t f : Stm} {v : Nat} (hv : c.ev κ s L = some v) (hp : c.pk κ s L < 2
  ^ W)
    (ht : v ≠ 0 → PKok K KH κ Γ W t s L) (hf : v = 0 → PKok K KH κ Γ W f s L) :
    PKok K KH κ Γ W (.ite c t f) s L := by
  intro s' L' n h
  by_cases h0 : v ≠ 0
  · simp only [evalF, hv, ite_eq_left h0] at h
    revert h; cases h2 : evalF κ t s L <;> simp only [Res.addCost, Res.ok.injEq, and_imp,
        reduceCtorEq, IsEmpty.forall_iff]
    intro e1 e2 _; subst e1; subst e2
    obtain ⟨p1, p2⟩ := ht h0 _ _ _ h2
    exact ⟨by rw [pkF_ite hv, ite_eq_left h0]; exact max_lt hp p1, p2⟩
  · simp only [evalF, hv, ite_eq_right h0] at h
    revert h; cases h2 : evalF κ f s L <;> simp only [Res.addCost, Res.ok.injEq, and_imp,
        reduceCtorEq, IsEmpty.forall_iff]
    intro e1 e2 _; subst e1; subst e2
    obtain ⟨p1, p2⟩ := hf (not_not.mp h0) _ _ _ h2
    exact ⟨by rw [pkF_ite hv, ite_eq_right h0]; exact max_lt hp p1, p2⟩

theorem PKok.catch_bug {c : Stm} (hc : PKok K KH κ Γ W c s L) : PKok K KH κ Γ W (.catch c .bug)
  s L := by
  intro s' L' n e
  cases h1 : evalF κ c s L with
  | ok s1 L1 n1 =>
    rw [evalF] at e; rw [h1] at e; simp only [Res.ok.injEq] at e; obtain ⟨rfl, rfl, -⟩ := e
    exact ⟨by rw [pkF_catch_ok h1]; exact (hc _ _ _ h1).1, (hc _ _ _ h1).2⟩
  | fail s1 L1 n1 => rw [evalF] at e; rw [h1] at e; simp only [Res.addCost, evalF, reduceCtorEq]
    at e
  | bug => rw [evalF] at e; rw [h1] at e; simp only [reduceCtorEq] at e

theorem PKok.call {q : Proc} {args : List Exp} {ds : List Reg} {vs : List Nat} {Γc : Reg → Nat}
    (hG : Gd K KH κ Γ s L) (ha : evList κ s L args = some vs) (hpa : pkList κ s L args < 2 ^ W)
    (hb : PKok K KH κ Γc W q.body s (Machine.State.setLocs (fun _ => 0) q.params vs))
    (hr : ∀ r ∈ q.rets, Γc r ≤ K) (hd : ∀ d ∈ ds, K ≤ Γ d) : PKok K KH κ Γ W (q.call args ds) s
      L := by
  intro s' L' n h
  simp only [Proc.call, evalF, ha] at h
  revert h; cases h2 : evalF κ q.body s (Machine.State.setLocs (fun _ => 0) q.params vs) <;>
    simp only [
      Res.ok.injEq,
      and_imp,
      reduceCtorEq,
      IsEmpty.forall_iff]
  intro e1 e2 _; subst e1; subst e2
  obtain ⟨b1, g1, g2, g3⟩ := hb _ _ _ h2
  refine ⟨by rw [pkF_call ha]; exact max_lt hpa b1, g1, g2, setLocs_lt hG.loc hd ?_⟩
  intro v hv
  simp only [List.mem_map] at hv
  obtain ⟨r, hr', rfl⟩ := hv
  exact pow_mono_lt (g3 r) (hr r hr')

end okrules

section okloop
variable {Γ : Reg → Nat} {W : Nat} {s : Core} {L : Loc}

theorem runForF_ok_inv {b : Stm} {x : Reg} {k m : Nat} {s s' : Core} {L L' : Loc} {c : Nat}
    (h : runForF (evalF κ b) x k (m + 1) s L = .ok s' L' c) :
    ∃ s1 L1 c1 c2, evalF κ b s (Machine.State.upd L x k) = .ok s1 L1 c1 ∧
      runForF (evalF κ b) x (k + 1) m s1 L1 = .ok s' L' c2 := by
  simp only [runForF] at h
  cases h1 : evalF κ b s (Machine.State.upd L x k) with
  | ok s1 L1 c1 =>
    rw [h1] at h; simp only [Res.addCost, Res.bind] at h
    cases h2 : runForF (evalF κ b) x (k + 1) m s1 L1 with
    | ok s2 L2 c2 =>
      rw [h2] at h; simp only [ Res.ok.injEq] at h
      obtain ⟨rfl, rfl, -⟩ := h
      exact ⟨s1, L1, c1, c2, rfl, h2⟩
    | fail => rw [h2] at h; simp only [reduceCtorEq] at h
    | bug => rw [h2] at h; simp only [reduceCtorEq] at h
  | fail => rw [h1] at h; simp only [Res.bind, Res.addCost, reduceCtorEq] at h
  | bug => rw [h1] at h; simp only [Res.bind, Res.addCost, reduceCtorEq] at h

/-- **A loop, for a normal run**, with an invariant `I k` before iteration `k`. -/
theorem PKok.loop {x : Reg} {n : Exp} {b : Stm} {N : Nat} (hn : n.ev κ s L = some N) (hp : n.pk
  κ s L < 2 ^ W)
    (I : Nat → Core → Loc → Prop) (h0 : I 0 s L) (hI : ∀ k s L, I k s L → Gd K KH κ Γ s L)
    (hb : ∀ k s L, k < N → I k s L → ∀ s' L' c, evalF κ b s (Machine.State.upd L x k) = .ok s'
      L' c →
      pkF κ b s (Machine.State.upd L x k) < 2 ^ W ∧ I (k + 1) s' L') :
    PKok K KH κ Γ W (.loop x n b) s L := by
  have key : ∀ m k s L, k + m = N → I k s L → ∀ s' L' c, runForF (evalF κ b) x k m s L = .ok s'
    L' c →
      pkFor (evalF κ b) (pkF κ b) x k m s L < 2 ^ W ∧ Gd K KH κ Γ s' L' := by
    intro m
    induction m with
    | zero =>
      intro k s L _ hIk s' L' c h
      simp only [runForF, Res.ok.injEq] at h; obtain ⟨rfl, rfl, -⟩ := h
      exact ⟨by simp only [pkFor, Nat.ofNat_pos, pow_pos], hI k _ _ hIk⟩
    | succ m ih =>
      intro k s L hk hIk s' L' c h
      obtain ⟨s1, L1, c1, c2, h1, h2⟩ := runForF_ok_inv h
      obtain ⟨p1, hI1⟩ := hb k s L (by omega) hIk _ _ _ h1
      obtain ⟨q1, q2⟩ := ih (k + 1) s1 L1 (by omega) hI1 _ _ _ h2
      simp only [pkFor, h1]
      exact ⟨max_lt p1 q1, q2⟩
  intro s' L' c h
  simp only [evalF, hn] at h
  revert h; cases h2 : runForF (evalF κ b) x 0 N s L <;> simp only [Res.addCost, Res.ok.injEq,
      and_imp, reduceCtorEq,
      IsEmpty.forall_iff]
  intro e1 e2 _; subst e1; subst e2
  obtain ⟨k1, k2⟩ := key N 0 s L (by omega) h0 _ _ _ h2
  exact ⟨by simp only [pkF, Exp.val_of hn]; exact max_lt hp k1, k2⟩

end okloop

end OrderMaintenance.Impl
