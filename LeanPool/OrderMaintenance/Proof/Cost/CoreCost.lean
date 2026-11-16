/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Cost.Background


/-!
# The cost invariant of a core, and insertion without FALLBACK

`CostInv` collects the invariants of M4 between operations: INV-S, Lemmas G1–G4, C1–C3, the
queue, the chunk count, the top structure's invariant (through its contract) and the zeroing game
with its round accounting. From it, an insertion never takes FALLBACK: it runs exactly
`insertElem` and `background`, and `CostInv` holds again.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model OrderMaintenance.Zeroing
/-- **The cost invariant** of a core. -/
structure CostInv (TI : Core → Prop) (μ : Core → Nat) (J n R : Nat) (L : List Nat) (s : Core) :
    Prop where
  low : LowInv s L
  ti : TI s
  game : ∃ y i a ip js, GameInv n R s y i a ip ∧ RoundOK s.P.reservationBudget J μ s ip js

theorem run_onGuard_ok {α : Type} {act handler : CM α} {s s' : Core} {a : α}
    (h : act.run s = .ok a s') : (onGuard act handler).run s = .ok a s' := by
  rw [run_onGuard, h]

/-- **Insertion without FALLBACK** (Lemma K1 for insertions). From the cost invariant, inserting
after a listed element runs exactly the element link and the background work, never FALLBACK, and
restores the cost invariant. -/
theorem insertAfter_cost {TI : Core → Prop} {μ : Core → Nat} {J n R : Nat} {cap : Params → Nat} {L : List Nat}
    {s : Core} {x : Nat} (hTC : TopContract TI μ J cap) (hC : CostInv TI μ J n R L s)
    (hx : x ∈ L) (hk : 1 ≤ s.P.reservationBudget) (hR : J / s.P.reservationBudget + 1 ≤ R) (hn
      : 1 ≤ n)
    (hsize : 2 + 2 * ((s.count + 1) / (s.P.theta + 1 - cmax s.P)) ≤ n + 1)
    (hcap : 2 + 2 * ((s.count + 1) / (s.P.theta + 1 - cmax s.P)) ≤ cap s.P)
    (hI5 : (s.P.theta : ℝ) + R * (Hn (n - 1) + 1) ≤ s.P.T) (hh : Nat) :
    ∃ s', (insertAfter x hh).run s = .ok s.E.size s' ∧
      (do let y ← insertElem x hh; background y; pure y).run s = .ok s.E.size s' ∧
      CostInv TI μ J n R (OrderMaintenance.Spec.insertAfterL x s.E.size L) s' ∧ s'.count = s.count + 1 ∧
      s'.P = s.P := by
  obtain ⟨y, i, a, ip, js, hG, hRO⟩ := hC.game
  have hdiv : s.count / (s.P.theta + 1 - cmax s.P) ≤ (s.count + 1) / (s.P.theta + 1 - cmax s.P) :=
    Nat.div_le_div_right (Nat.le_succ s.count)
  have hcnt0 : 2 + 2 * (s.count / (s.P.theta + 1 - cmax s.P)) ≤ n + 1 := by omega
  obtain ⟨s1, s2, hrun1, hrun2, hPost, heG, hgC, hE12, hP1⟩ := insert_step hTC hC.low hC.ti hG hRO hx
    hk hR hn hcnt0 hI5 hh
  have hyL : s.E.size ∈ OrderMaintenance.Spec.insertAfterL x s.E.size L :=
    (OrderMaintenance.Spec.mem_insertAfterL hx).mpr (Or.inl rfl)
  rw [heG, hgC] at hrun2
  obtain ⟨s', hbg, hL', hTI', hc', hP', hgame'⟩ := background_ok hTC hPost hyL heG hgC hrun2 hE12
    hP1 rfl hn (by rw [hPost.count]; exact hsize) (by rw [hPost.count]; exact hcap) hI5
  refine ⟨s', ?_, ?_, ⟨hL', hTI', by rw [hP']; exact hgame'⟩, hc'.trans hPost.count, hP'⟩
  · unfold insertAfter
    rw [run_bind, run_onGuard_ok hrun1]
    dsimp only
    rw [run_bind, run_onGuard_ok hbg]
    rfl
  · rw [run_bind, hrun1]
    dsimp only
    rw [run_bind, hbg]
    rfl

end OrderMaintenance.Proof

namespace OrderMaintenance.Proof

open OrderMaintenance.Model OrderMaintenance.Zeroing
/-- **Deletion** (a tombstone) keeps the cost invariant. -/
theorem markDead_cost {TI : Core → Prop} {μ : Core → Nat} {J n R : Nat} {cap : Params → Nat} {L : List Nat}
    {s : Core} (hTC : TopContract TI μ J cap) (hC : CostInv TI μ J n R L s) (x : Nat) :
    ∃ s', (markDead x).run s = .ok () s' ∧ CostInv TI μ J n R L s' := by
  refine ⟨_, markDead_run s x, ?_⟩
  set s' : Core := { s with E := s.E.modify x fun e => { e with live := false } } with hs'
  have hE : ∀ e, eG s' e = eG s e ∧ eL s' e = eL s e := by
    intro e; simp only [hs', eG, eL, Array.getX_modify]; split <;> exact ⟨rfl, rfl⟩
  have hGS : GSame s s' := ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun e => (hE e).1, fun e => (hE e).2,
    rfl, rfl⟩
  obtain ⟨A, hI, hel⟩ := hC.low.inv
  obtain ⟨gh, hG⟩ := hC.low.ginv
  obtain ⟨s₀, hCi, ⟨lg, hL⟩, hLP, hGP⟩ := hC.low.cinv
  obtain ⟨e, pops, hN⟩ := hC.low.cnt
  have hCS : CSame s s' := ⟨rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl, rfl⟩
  have hLS : LSame s s' := ⟨rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ => rfl, fun _ => rfl⟩
  have hQS : QSame s s' := ⟨rfl, rfl, fun _ _ => Iff.rfl, fun _ _ _ => rfl⟩
  have hPS : PQSame s s' := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hTS : TopSame s s' :=
    ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, fun _ => ⟨rfl, rfl, rfl⟩, rfl⟩
  refine ⟨⟨⟨A, markDead_inv hI x, hel⟩, ⟨gh, hG.of_gsame hGS⟩, ⟨s₀, ?_, ⟨lg, hL.transfer hLS⟩, hLP,
    hGP⟩, hC.low.pq.qsame hPS hQS, ⟨e, pops, hN.frame hQS rfl⟩, hC.low.cp⟩,
    hTC.frame _ _ hTS hC.ti, ?_⟩
  swap
  · obtain ⟨y, i, a, ip, js, hGm, hRO⟩ := hC.game
    refine ⟨y, i, a, ip, js, hGm.mono (fun j => le_of_eq (by rw [hQS.gvec])), ?_⟩
    unfold RoundOK at hRO ⊢; rw [hTC.mframe _ _ hTS]; exact hRO
  refine hCi.transfer hCS (fun c => ?_) (fun c => rfl) hCi.δu (fun g hg => hCi.gchk g hg)
  unfold celts; congr 1; funext z; rw [(hE z).1]

/-- **Order queries** change nothing. -/
theorem order_cost (s : Core) (x y : Nat) : ∃ b, (order x y).run s = .ok b s :=
  ⟨_, order_run s x y⟩

end OrderMaintenance.Proof
