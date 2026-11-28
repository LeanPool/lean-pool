/-
Copyright (c) 2026 bocchitherock888-ux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: bocchitherock888-ux
-/

module

public import LeanPool.FormalLinguistics.LambekCore

/-!
  Thin sequents (Pentus 1993): every derivable sequent is the image, under a renaming of
  primitive types, of a derivable sequent in which each primitive type occurs at most twice.
-/

@[expose] public section

namespace FormalLinguistics

variable {P : Type}

namespace LThin


theorem occList_nil [DecidableEq P] (q : P) : occList q ([] : List (LType P)) = 0 := rfl

theorem occList_cons [DecidableEq P] (q : P) (x : LType P) (a : List (LType P)) :
    occList q (x :: a) = x.occ q + occList q a := by
  simp [occList]

theorem occList_append [DecidableEq P] (q : P) (a b : List (LType P)) :
    occList q (a ++ b) = occList q a + occList q b := by
  simp [occList, List.sum_append]

theorem map_eq_over {Q : Type} {f : P → Q} {X : LType P} {A B : LType Q}
    (h : X.map f = LType.over A B) :
    ∃ A' B', X = LType.over A' B' ∧ A'.map f = A ∧ B'.map f = B := by
  cases X with
  | over a b => simp only [LType.map, LType.over.injEq] at h; exact ⟨a, b, rfl, h.1, h.2⟩
  | _ => simp [LType.map] at h

theorem map_eq_under {Q : Type} {f : P → Q} {X : LType P} {A B : LType Q}
    (h : X.map f = LType.under B A) :
    ∃ B' A', X = LType.under B' A' ∧ B'.map f = B ∧ A'.map f = A := by
  cases X with
  | under b a => simp only [LType.map, LType.under.injEq] at h; exact ⟨b, a, rfl, h.1, h.2⟩
  | _ => simp [LType.map] at h

theorem map_eq_mul {Q : Type} {f : P → Q} {X : LType P} {A B : LType Q}
    (h : X.map f = LType.mul A B) :
    ∃ A' B', X = LType.mul A' B' ∧ A'.map f = A ∧ B'.map f = B := by
  cases X with
  | mul a b => simp only [LType.map, LType.mul.injEq] at h; exact ⟨a, b, rfl, h.1, h.2⟩
  | _ => simp [LType.map] at h

/-- Split a renamed antecedent `Ξ'` with `Ξ'.map f = Γ ++ [A] ++ Δ`. -/
theorem split3 {Q : Type} {f : LType Q → LType P} {Ξ : List (LType Q)}
    {Γ Δ : List (LType P)} {A : LType P} (h : Ξ.map f = Γ ++ [A] ++ Δ) :
    ∃ Γ' A' Δ', Ξ = Γ' ++ [A'] ++ Δ' ∧ Γ'.map f = Γ ∧ f A' = A ∧ Δ'.map f = Δ := by
  obtain ⟨L, Δ', rfl, hL, hΔ⟩ := List.map_eq_append_iff.mp h
  obtain ⟨Γ', L2, rfl, hΓ, hL2⟩ := List.map_eq_append_iff.mp hL
  obtain ⟨A', rfl, hA⟩ := List.map_eq_singleton_iff.mp hL2
  exact ⟨Γ', A', Δ', rfl, hΓ, hA, hΔ⟩

theorem split4 {Q : Type} {f : LType Q → LType P} {Ξ : List (LType Q)}
    {Γ Δ : List (LType P)} {A B : LType P} (h : Ξ.map f = Γ ++ [A, B] ++ Δ) :
    ∃ Γ' A' B' Δ', Ξ = Γ' ++ [A', B'] ++ Δ' ∧ Γ'.map f = Γ ∧ f A' = A ∧ f B' = B ∧
      Δ'.map f = Δ := by
  obtain ⟨L, Δ', rfl, hL, hΔ⟩ := List.map_eq_append_iff.mp h
  obtain ⟨Γ', L2, rfl, hΓ, hL2⟩ := List.map_eq_append_iff.mp hL
  obtain ⟨A', L3, rfl, hA, hL3⟩ := List.map_eq_cons_iff.mp hL2
  obtain ⟨B', rfl, hB⟩ := List.map_eq_singleton_iff.mp hL3
  exact ⟨Γ', A', B', Δ', rfl, hΓ, hA, hB, hΔ⟩

/-- The strengthened statement with index ranges. -/
theorem main [DecidableEq P] {Γ : List (LType P)} {C : LType P} (h : LDer0 Γ C) :
    ∀ n : Nat, ∃ (m : Nat) (Γ' : List (LType (P × Nat))) (C' : LType (P × Nat)),
      n ≤ m ∧ LDer0 Γ' C' ∧
      Γ'.map (LType.map Prod.fst) = Γ ∧ C'.map Prod.fst = C ∧
      (∀ q : P × Nat, occList q Γ' + C'.occ q ≤ 2) ∧
      (∀ q : P × Nat, (q.2 < n ∨ m ≤ q.2) → occList q Γ' + C'.occ q = 0) := by
  induction h with
  | ax p =>
    intro n
    refine ⟨n + 1, [LType.prim (p, n)], LType.prim (p, n), by omega, LDer0.ax _, rfl, rfl,
      ?_, ?_⟩
    · intro q
      by_cases hq : (p, n) = q <;> simp [occList, LType.occ, hq]
    · intro q hq
      have hne : (p, n) ≠ q := by
        rintro rfl; simp at hq; omega
      simp [occList, LType.occ, hne]
  | @overR Γ A B hne _ ih =>
    intro n
    obtain ⟨m, Ξ', A', hnm, d', hΞ, hA, hb, hz⟩ := ih n
    obtain ⟨Γ', L, rfl, hΓ, hL⟩ := List.map_eq_append_iff.mp hΞ
    obtain ⟨B', rfl, hB⟩ := List.map_eq_singleton_iff.mp hL
    refine ⟨m, Γ', LType.over A' B', hnm, LDer0.overR ?_ d', hΓ,
      by simp [LType.map, hA, hB], ?_, ?_⟩
    · rintro rfl; exact hne (by simpa using hΓ.symm)
    · intro q; have := hb q
      simp only [occList_append, occList_cons, occList_nil, LType.occ] at this ⊢; omega
    · intro q hq; have := hz q hq
      simp only [occList_append, occList_cons, occList_nil, LType.occ] at this ⊢; omega
  | @underR Γ A B hne _ ih =>
    intro n
    obtain ⟨m, Ξ', A', hnm, d', hΞ, hA, hb, hz⟩ := ih n
    obtain ⟨B', Γ', rfl, hB, hΓ⟩ := List.map_eq_cons_iff.mp hΞ
    refine ⟨m, Γ', LType.under B' A', hnm, LDer0.underR ?_ d', hΓ,
      by simp [LType.map, hA, hB], ?_, ?_⟩
    · rintro rfl; exact hne (by simpa using hΓ.symm)
    · intro q; have := hb q
      simp only [occList_cons, LType.occ] at this ⊢; omega
    · intro q hq; have := hz q hq
      simp only [occList_cons, LType.occ] at this ⊢; omega
  | @overL Γ Δ Θ A B C _ _ ih1 ih2 =>
    intro n
    obtain ⟨m1, Θ', B', hnm1, d1, hΘ, hB, hb1, hz1⟩ := ih1 n
    obtain ⟨m2, Ξ', C', hm12, d2, hΞ, hC, hb2, hz2⟩ := ih2 m1
    obtain ⟨Γ', A', Δ', rfl, hΓ, hA, hΔ⟩ := split3 hΞ
    refine ⟨m2, Γ' ++ [LType.over A' B'] ++ Θ' ++ Δ', C', by omega, LDer0.overL d1 d2,
      by simp [hΓ, hΔ, hΘ, LType.map, hA, hB], hC, ?_, ?_⟩
    · intro q
      have e1 := hb1 q; have e2 := hb2 q
      by_cases hq : q.2 < m1
      · have e3 := hz2 q (Or.inl hq)
        simp only [occList_append, occList_cons, occList_nil, LType.occ] at e1 e2 e3 ⊢; omega
      · have e3 := hz1 q (Or.inr (by omega))
        simp only [occList_append, occList_cons, occList_nil, LType.occ] at e1 e2 e3 ⊢; omega
    · intro q hq
      have e1 := hz1 q (by omega); have e2 := hz2 q (by omega)
      simp only [occList_append, occList_cons, occList_nil, LType.occ] at e1 e2 ⊢; omega
  | @underL Γ Δ Θ A B C _ _ ih1 ih2 =>
    intro n
    obtain ⟨m1, Θ', B', hnm1, d1, hΘ, hB, hb1, hz1⟩ := ih1 n
    obtain ⟨m2, Ξ', C', hm12, d2, hΞ, hC, hb2, hz2⟩ := ih2 m1
    obtain ⟨Γ', A', Δ', rfl, hΓ, hA, hΔ⟩ := split3 hΞ
    refine ⟨m2, Γ' ++ Θ' ++ [LType.under B' A'] ++ Δ', C', by omega, LDer0.underL d1 d2,
      by simp [hΓ, hΔ, hΘ, LType.map, hA, hB], hC, ?_, ?_⟩
    · intro q
      have e1 := hb1 q; have e2 := hb2 q
      by_cases hq : q.2 < m1
      · have e3 := hz2 q (Or.inl hq)
        simp only [occList_append, occList_cons, occList_nil, LType.occ] at e1 e2 e3 ⊢; omega
      · have e3 := hz1 q (Or.inr (by omega))
        simp only [occList_append, occList_cons, occList_nil, LType.occ] at e1 e2 e3 ⊢; omega
    · intro q hq
      have e1 := hz1 q (by omega); have e2 := hz2 q (by omega)
      simp only [occList_append, occList_cons, occList_nil, LType.occ] at e1 e2 ⊢; omega
  | @mulR Γ Δ A B _ _ ih1 ih2 =>
    intro n
    obtain ⟨m1, Γ', A', hnm1, d1, hΓ, hA, hb1, hz1⟩ := ih1 n
    obtain ⟨m2, Δ', B', hm12, d2, hΔ, hB, hb2, hz2⟩ := ih2 m1
    refine ⟨m2, Γ' ++ Δ', LType.mul A' B', by omega, LDer0.mulR d1 d2,
      by simp [hΓ, hΔ], by simp [LType.map, hA, hB], ?_, ?_⟩
    · intro q
      have e1 := hb1 q; have e2 := hb2 q
      by_cases hq : q.2 < m1
      · have e3 := hz2 q (Or.inl hq)
        simp only [occList_append, LType.occ] at e1 e2 e3 ⊢; omega
      · have e3 := hz1 q (Or.inr (by omega))
        simp only [occList_append, LType.occ] at e1 e2 e3 ⊢; omega
    · intro q hq
      have e1 := hz1 q (by omega); have e2 := hz2 q (by omega)
      simp only [occList_append, LType.occ] at e1 e2 ⊢; omega
  | @mulL Γ Δ A B C _ ih =>
    intro n
    obtain ⟨m, Ξ', C', hnm, d', hΞ, hC, hb, hz⟩ := ih n
    obtain ⟨Γ', A', B', Δ', rfl, hΓ, hA, hB, hΔ⟩ := split4 hΞ
    refine ⟨m, Γ' ++ [LType.mul A' B'] ++ Δ', C', hnm, LDer0.mulL d',
      by simp [hΓ, hΔ, LType.map, hA, hB], hC, ?_, ?_⟩
    · intro q; have := hb q
      simp only [occList_append, occList_cons, occList_nil, LType.occ] at this ⊢; omega
    · intro q hq; have := hz q hq
      simp only [occList_append, occList_cons, occList_nil, LType.occ] at this ⊢; omega

end LThin

/-- Every derivable sequent `Γ → C` over primitive types `P` is obtained, by forgetting the
    numerical index of each primitive type, from a derivable sequent over `P × Nat` in which
    every primitive type occurs at most twice in total. -/
theorem LDer0.exists_thin [DecidableEq P] {Γ : List (LType P)} {C : LType P} (h : LDer0 Γ C) :
    ∃ (Γ' : List (LType (P × Nat))) (C' : LType (P × Nat)),
      LDer0 Γ' C' ∧
      Γ'.map (LType.map Prod.fst) = Γ ∧ C'.map Prod.fst = C ∧
      ∀ q : P × Nat, occList q Γ' + C'.occ q ≤ 2 := by
  obtain ⟨_, Γ', C', _, d, hΓ, hC, hb, _⟩ := LThin.main h 0
  exact ⟨Γ', C', d, hΓ, hC, hb⟩

end FormalLinguistics
