/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.ArrayLemmas
public import Mathlib.Tactic.Linarith


/-!
# M6: reasoning about loops of the core language

`evalF_loop`: a loop runs to completion when each iteration succeeds and keeps an invariant,
with cost at most `1 + cost(bound) + N · (1 + body)`.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model
open OrderMaintenance.Machine (Reg)

theorem runForF_inv {κ : Caps} (b : Stm) (x : Reg) (N : Nat)
    (I : Nat → Core → Loc → Prop) (cb : Nat)
    (hb : ∀ k < N, ∀ s L, I k s L →
      ∃ s' L' c, evalF κ b s (Machine.State.upd L x k) = .ok s' L' c ∧ c ≤ cb ∧
        I (k + 1) s' L') :
    ∀ n k s L, k + n = N → I k s L →
      ∃ s' L' c, runForF (evalF κ b) x k n s L = .ok s' L' c ∧ c ≤ n * (1 + cb) ∧ I N s' L'
  | 0, k, s, L, hk, hI => ⟨s, L, 0, rfl, by simp, by rw [← hk]; simpa using hI⟩
  | n + 1, k, s, L, hk, hI => by
    obtain ⟨s1, L1, c1, he, hc, hI1⟩ := hb k (by omega) s L hI
    obtain ⟨s2, L2, c2, he2, hc2, hI2⟩ := runForF_inv b x N I cb hb n (k + 1) s1 L1 (by omega) hI1
    refine ⟨s2, L2, (1 + c1) + c2, ?_, ?_, hI2⟩
    · simp only [runForF, he, Res.addCost, Res.bind, he2]
    · rw [Nat.succ_mul]; nlinarith

theorem evalF_assign_ok {κ : Caps} {x : Reg} {e : Exp} {s : Core} {L : Loc} {v : Nat}
    (h : e.ev κ s L = some v) : evalF κ (.assign x e) s L =
      .ok s (Machine.State.upd L x v) (1 + e.cost) := by
  simp [evalF, h]

theorem evalF_seq_ok2 {κ : Caps} {A B : Stm} {s s1 s2 : Core} {L L1 L2 : Loc} {c1 c2 : Nat}
    (h1 : evalF κ A s L = .ok s1 L1 c1) (h2 : evalF κ B s1 L1 = .ok s2 L2 c2) :
    evalF κ (.seq A B) s L = .ok s2 L2 (c1 + c2) := by
  simp [evalF, h1, h2, Res.bind, Res.addCost]

theorem evalF_ite_t {κ : Caps} {c : Exp} {t f : Stm} {s s' : Core} {L L' : Loc} {v c' : Nat}
    (hc : c.ev κ s L = some v) (hv : v ≠ 0) (ht : evalF κ t s L = .ok s' L' c') :
    evalF κ (.ite c t f) s L = .ok s' L' (1 + c.cost + c') := by
  simp [evalF, hc, hv, ht, Res.addCost]

theorem evalF_ite_f {κ : Caps} {c : Exp} {t f : Stm} {s s' : Core} {L L' : Loc} {c' : Nat}
    (hc : c.ev κ s L = some 0) (hf : evalF κ f s L = .ok s' L' c') :
    evalF κ (.ite c t f) s L = .ok s' L' (1 + c.cost + c') := by
  simp [evalF, hc, hf, Res.addCost]

theorem evalF_skip {κ : Caps} {s : Core} {L : Loc} : evalF κ .skip s L = .ok s L 1 := by
  simp [evalF]

/-- **The loop rule.** -/
theorem evalF_loop {κ : Caps} {x : Reg} {n : Exp} {b : Stm} {s : Core} {L : Loc} {N : Nat}
    (hn : n.ev κ s L = some N)
    (I : Nat → Core → Loc → Prop) (cb : Nat) (h0 : I 0 s L)
    (hb : ∀ k < N, ∀ s L, I k s L →
      ∃ s' L' c, evalF κ b s (Machine.State.upd L x k) = .ok s' L' c ∧ c ≤ cb ∧
        I (k + 1) s' L') :
    ∃ s' L' c, evalF κ (.loop x n b) s L = .ok s' L' c ∧ c ≤ 1 + n.cost + N * (1 + cb) ∧
      I N s' L' := by
  obtain ⟨s', L', c, he, hc, hI⟩ := runForF_inv b x N I cb hb N 0 s L (by omega) h0
  refine ⟨s', L', 1 + n.cost + c, ?_, by omega, hI⟩
  simp only [evalF, hn, he, Res.addCost]

/-- **The loop rule for loops that only change locals**: an abstraction `abs` of the locals follows
the fold of `f` over the iterations, and a frame condition `F` is kept. -/
theorem evalF_loop_pure {κ : Caps} {x : Reg} {n : Exp} {b : Stm} {s : Core} {L : Loc} {N : Nat}
    (hn : n.ev κ s L = some N) {α : Type} (F : Loc → Prop) (abs : Loc → α)
    (f : α → Nat → α) (cb : Nat)
    (h0 : F L)
    (hb : ∀ k < N, ∀ L', F L' → ∃ L'' c, evalF κ b s (Machine.State.upd L' x k) = .ok s L'' c ∧
      c ≤ cb ∧ F L'' ∧ abs L'' = f (abs L') k) :
    ∃ L' c, evalF κ (.loop x n b) s L = .ok s L' c ∧ c ≤ 1 + n.cost + N * (1 + cb) ∧ F L' ∧
      abs L' = (List.range N).foldl f (abs L) := by
  obtain ⟨s', L', c, he, hc, hs, hF, ha⟩ := evalF_loop hn
    (fun k s' L' => s' = s ∧ F L' ∧ abs L' = (List.range k).foldl f (abs L)) cb ⟨rfl, h0, rfl⟩
    (by
      intro k hk s1 L1 ⟨hs, hF, ha⟩
      subst hs
      obtain ⟨L2, c, he, hc, hF2, ha2⟩ := hb k hk L1 hF
      exact ⟨s1, L2, c, he, hc, rfl, hF2, by rw [ha2, ha, List.range_succ, List.foldl_append]; rfl⟩)
  subst hs
  exact ⟨L', c, he, hc, hF, ha⟩

end OrderMaintenance.Impl
