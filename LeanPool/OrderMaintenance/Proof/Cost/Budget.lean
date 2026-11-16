/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Cost.ResCost


/-!
# A chunk's budget

Whatever its phase, a chunk's arrivals stay within `3·M_u` and its insertions within `I_C`. For a
quiet chunk this uses its size bound (Lemma R); for a family it uses Lemma C1.
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- The family of a splitting chunk, by C1: its size exceeds `s₀` by less than `k_C(T)`, counting
the undriven insertions. -/
theorem C1.fam_le {s : Core} {δ δu s₀ : Nat → Nat} {x : Nat} (h : C1 s δ δu s₀ x)
    (hK : 2 ≤ s.P.chunkBudget) :
    famC s x ≤ s₀ x + (δ (cLl s x) + δ x + δ (cRr s x)) + (kC s.P s.P.T - 1) ∧
      s₀ x ≤ (cSz s (cLl s x) - δ (cLl s x)) + (cSz s x - δ x) + (cSz s (cRr s x) - δ (cRr s x)) ∧
      (cSz s (cLl s x) - δ (cLl s x)) + (cSz s x - δ x) + (cSz s (cRr s x) - δ (cRr s x)) - s₀ x ≤
        kC s.P s.P.T - 1 := by
  obtain ⟨hT, h1, h2, -, -⟩ := h
  have hU := unitsOf_mono s.P hT
  have hfam : famC s x ≤ ((cSz s (cLl s x) - δ (cLl s x)) + (cSz s x - δ x) +
      (cSz s (cRr s x) - δ (cRr s x))) + (δ (cLl s x) + δ x + δ (cRr s x)) := by
    unfold famC; omega
  generalize hm : s.P.chunkBudget - 1 = m at h2
  have hm1 : 1 ≤ m := by omega
  generalize (cSz s (cLl s x) - δ (cLl s x)) + (cSz s x - δ x) + (cSz s (cRr s x) - δ (cRr s x)) = S
    at h1 h2 hfam ⊢
  have hq : S - s₀ x ≤ unitsOf s.P (s₀ x) / m := by
    rw [Nat.le_div_iff_mul_le (by omega), Nat.mul_comm]
    have := Nat.le_add_left (m * (S - s₀ x)) (units s x - δu x); omega
  have hq2 : unitsOf s.P (s₀ x) / m ≤ unitsOf s.P s.P.T / m := Nat.div_le_div_right hU
  have hk : kC s.P s.P.T = unitsOf s.P s.P.T / m + 1 := by unfold kC; rw [hm]
  refine ⟨?_, h1, by omega⟩
  omega

/-- **A chunk's budget**: arrivals within `3·M_u`, insertions within `I_C`. -/
theorem chunk_budget {s : Core} {L : List Nat} {lg : LGh} {s₀ δ δu : Nat → Nat}
    (hC : CInv s L δ δu s₀) (hL : LInv s lg s₀ δ δu) (hCP : CParams s.P) {c : Nat}
    (hcL : LiveC s c) (hnd : cSt s c ≠ .dead)
    (hδ1 : ∀ x, LiveC s x → cSt s x = .splitting → δ (cLl s x) + δ x + δ (cRr s x) ≤ 1)
    (hq : cSt s c = .quiet → cSz s c ≤ s.P.T + 1) :
    lg.arB c + lg.arF c ≤ 3 * Mu s.P ∧ lg.ins c ≤ IC s.P := by
  have hK := hCP.K2
  have hkC : 1 ≤ kC s.P s.P.T := by unfold kC; exact Nat.le_add_left 1 _
  cases hst : cSt s c with
  | quiet =>
    have h1 := hL.insQ c hcL hst
    have h2 := hq hst
    refine ⟨hL.arrN c hcL (by rw [hst]; simp), ?_⟩
    unfold IC; omega
  | splitting =>
    have h1 := hL.insS c hcL hst
    have hc1 := hC.c1 c hcL hst (by unfold NIL; have := hcL.1; omega)
    have hT := hc1.1
    obtain ⟨hf, -, -⟩ := hc1.fam_le hK
    have hd := hδ1 c hcL hst
    refine ⟨hL.arrN c hcL (by rw [hst]; simp), ?_⟩
    unfold IC; omega
  | overflow =>
    obtain ⟨hxL, hxs, hlr⟩ := hC.covf c hcL hst
    generalize hx : cSrc s c = x at hxL hxs hlr
    have hc1 := hC.c1 x hxL hxs (by unfold NIL; have := hxL.1; omega)
    have hT := hc1.1
    have hU := unitsOf_mono s.P hT
    obtain ⟨hf, h1, h2⟩ := hc1.fam_le hK
    have hd := hδ1 x hxL hxs
    have hA := hL.arrS x hxL hxs
    have hδu := hC.δu x
    have hO := hL.insO c hcL hst
    rw [hx] at hO
    have harr : lg.arB c + lg.arF c ≤ lg.arB (cLl s x) + lg.arF (cLl s x) + lg.arB (cRr s x) +
        lg.arF (cRr s x) := by rcases hlr with h | h <;> rw [← h] <;> omega
    have hfam' : famC s x ≤ ((cSz s (cLl s x) - δ (cLl s x)) + (cSz s x - δ x) +
        (cSz s (cRr s x) - δ (cRr s x))) + (δ (cLl s x) + δ x + δ (cRr s x)) := by
      unfold famC; omega
    refine ⟨?_, ?_⟩
    · unfold Mu
      have hk : kC s.P s.P.T = unitsOf s.P s.P.T / (s.P.chunkBudget - 1) + 1 := rfl
      have hq2 : unitsOf s.P (s₀ x) / (s.P.chunkBudget - 1) ≤ unitsOf s.P s.P.T /
        (s.P.chunkBudget - 1) :=
        Nat.div_le_div_right hU
      generalize famC s x = F at *
      generalize (cSz s (cLl s x) - δ (cLl s x)) + (cSz s x - δ x) +
        (cSz s (cRr s x) - δ (cRr s x)) = S at *
      generalize kC s.P s.P.T = k at *
      omega
    · unfold IC; omega
  | dead => exact absurd hst hnd

/-- Undriven insertions outside every family can be forgotten (chunk invariant). -/
theorem CInvE.drop {s : Core} {L : List Nat} {δ δu s₀ : Nat → Nat} {ex : Nat}
    (hC : CInvE s L δ δu s₀ ex)
    (hδ : ∀ x, LiveC s x → cSt s x = .splitting →
      δ (cLl s x) = 0 ∧ δ x = 0 ∧ δ (cRr s x) = 0 ∧ δu x = 0) :
    CInvE s L (fun _ => 0) (fun _ => 0) s₀ ex := by
  refine { hC with c1 := fun x hx hxs hxe => ?_, δu := fun _ => le_rfl }
  have h := hC.c1 x hx hxs hxe
  obtain ⟨d1, d2, d3, d4⟩ := hδ x hx hxs
  unfold C1 at h ⊢
  rw [d1, d2, d3, d4] at h
  exact h

/-- Undriven insertions outside every family can be forgotten (label invariant). -/
theorem LInv.drop {s : Core} {lg : LGh} {s₀ δ δu : Nat → Nat} (hL : LInv s lg s₀ δ δu)
    (hδ : ∀ x, LiveC s x → cSt s x = .splitting →
      δ (cLl s x) = 0 ∧ δ x = 0 ∧ δ (cRr s x) = 0 ∧ δu x = 0) :
    LInv s lg s₀ (fun _ => 0) (fun _ => 0) := by
  refine { hL with arrS := fun x hx hxs => ?_ }
  have h := hL.arrS x hx hxs
  obtain ⟨d1, d2, d3, d4⟩ := hδ x hx hxs
  rw [d1, d2, d3, d4] at h
  simpa using h

end OrderMaintenance.Proof
