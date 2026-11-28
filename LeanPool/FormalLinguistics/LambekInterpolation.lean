/-
Copyright (c) 2026 bocchitherock888-ux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: bocchitherock888-ux
-/

module

public import LeanPool.FormalLinguistics.LambekCore

/-!
  The interpolation theorem for the Lambek calculus (Roorda 1991), in the form used by
  Pentus (1993).

  The proof follows Jäger's proof as presented by Kanazawa (2018, Theorem 3), restricted
  to the connectives `/`, `\` and `•`: induction on the cut-free derivation, with a case
  distinction on the position of the segment relative to the active formulas of the last
  rule.
-/

@[expose] public section

namespace FormalLinguistics

variable {P : Type}

namespace LInterp

open LType

theorem occList_nil [DecidableEq P] (p : P) : occList p ([] : List (LType P)) = 0 := rfl

theorem occList_cons [DecidableEq P] (p : P) (A : LType P) (Γ : List (LType P)) :
    occList p (A :: Γ) = A.occ p + occList p Γ := by
  simp [occList]

theorem occList_append [DecidableEq P] (p : P) (Γ Δ : List (LType P)) :
    occList p (Γ ++ Δ) = occList p Γ + occList p Δ := by
  simp [occList, List.sum_append]

/-- The interpolation property for the sequent `L, S, R → C` relative to the segment `S`. -/
def IP [DecidableEq P] (L S R : List (LType P)) (C : LType P) : Prop :=
  ∃ E : LType P, LDer0 S E ∧ LDer0 (L ++ [E] ++ R) C ∧
    ∀ p : P, E.occ p ≤ occList p S ∧ E.occ p ≤ occList p L + occList p R + C.occ p

theorem castD {X Y : List (LType P)} {C : LType P} (h : LDer0 X C) (e : X = Y) :
    LDer0 Y C := e ▸ h

theorem overL' {Y : List (LType P)} (G D T : List (LType P)) {A B C : LType P}
    (h1 : LDer0 T B) (h2 : LDer0 Y C) (eY : Y = G ++ [A] ++ D) :
    LDer0 (G ++ [over A B] ++ T ++ D) C := by
  subst eY; exact LDer0.overL h1 h2

theorem underL' {Y : List (LType P)} (G D T : List (LType P)) {A B C : LType P}
    (h1 : LDer0 T B) (h2 : LDer0 Y C) (eY : Y = G ++ [A] ++ D) :
    LDer0 (G ++ T ++ [under B A] ++ D) C := by
  subst eY; exact LDer0.underL h1 h2

theorem mulL' {Y : List (LType P)} (G D : List (LType P)) {A B C : LType P}
    (h : LDer0 Y C) (eY : Y = G ++ [A, B] ++ D) :
    LDer0 (G ++ [mul A B] ++ D) C := by
  subst eY; exact LDer0.mulL h

theorem split3 {α : Type} {L S R A B : List α} (h : L ++ S ++ R = A ++ B) :
    (∃ M, A = L ++ S ++ M ∧ R = M ++ B) ∨ (∃ M, B = M ++ S ++ R ∧ L = A ++ M) ∨
    (∃ S1 S2, S = S1 ++ S2 ∧ S1 ≠ [] ∧ S2 ≠ [] ∧ A = L ++ S1 ∧ B = S2 ++ R) := by
  rw [List.append_assoc, List.append_eq_append_iff] at h
  rcases h with ⟨a', rfl, h⟩ | ⟨c', rfl, rfl⟩
  · rw [List.append_eq_append_iff] at h
    rcases h with ⟨b, rfl, rfl⟩ | ⟨c, rfl, rfl⟩
    · left; exact ⟨b, by simp, rfl⟩
    · by_cases ha : a' = []
      · subst ha; right; left; exact ⟨[], by simp, by simp⟩
      · by_cases hc : c = []
        · subst hc; left; exact ⟨[], by simp, by simp⟩
        · right; right; exact ⟨a', c, rfl, ha, hc, rfl, rfl⟩
  · right; left; exact ⟨c', by simp, rfl⟩

theorem split_mid {α : Type} {L S R P Q : List α} {X : α} (h : L ++ S ++ R = P ++ X :: Q) :
    (∃ M, P = L ++ S ++ M ∧ R = M ++ X :: Q) ∨
    (∃ M, Q = M ++ S ++ R ∧ L = P ++ X :: M) ∨
    (∃ P2 Q1, S = P2 ++ X :: Q1 ∧ P = L ++ P2 ∧ Q = Q1 ++ R) := by
  rcases split3 h with h | ⟨M, hM, rfl⟩ | ⟨S1, S2, rfl, _, hS2, rfl, hB⟩
  · exact Or.inl h
  · rcases M with _ | ⟨m, M⟩
    · rcases S with _ | ⟨s, S⟩
      · left; exact ⟨[], by simp, by simpa using hM.symm⟩
      · simp only [List.nil_append, List.cons_append, List.cons.injEq] at hM
        obtain ⟨rfl, rfl⟩ := hM
        right; right; exact ⟨[], S, by simp, by simp, rfl⟩
    · simp only [List.cons_append, List.cons.injEq] at hM
      obtain ⟨rfl, rfl⟩ := hM
      right; left; exact ⟨M, by simp, rfl⟩
  · rcases S2 with _ | ⟨s, S2⟩
    · exact absurd rfl hS2
    · simp only [List.cons_append, List.cons.injEq] at hB
      obtain ⟨rfl, rfl⟩ := hB
      right; right; exact ⟨S1, S2, rfl, rfl, rfl⟩

/-- Normalize atom-occurrence counts for the arithmetic bounds in interpolation. -/
macro "occBound" : tactic =>
  `(tactic| focus
      simp only [occList_append, occList_cons, occList_nil, LType.occ, List.append_assoc,
        List.cons_append, List.nil_append, List.singleton_append] at *
      omega)

theorem main [DecidableEq P] {Ξ : List (LType P)} {C : LType P} (h : LDer0 Ξ C) :
    ∀ L S R : List (LType P), Ξ = L ++ S ++ R → S ≠ [] → IP L S R C := by
  induction h with
  | ax p =>
    intro L S R e hS
    rcases L with _ | ⟨l, L⟩
    · rcases S with _ | ⟨s, S⟩
      · exact absurd rfl hS
      · simp at e
        obtain ⟨rfl, rfl, rfl⟩ := e
        exact ⟨prim p, LDer0.ax p, LDer0.ax p, fun q => by simp [occList]⟩
    · simp at e
      exact absurd e.2.2.1 hS
  | @overR G A B _ _ ih =>
    intro L S R e hS
    subst e
    obtain ⟨E, h1, h2, hb⟩ := ih L S (R ++ [B]) (by simp) hS
    refine ⟨E, h1, LDer0.overR (by simp) (castD h2 (by simp)), fun p => ?_⟩
    have := hb p
    occBound
  | @underR G A B _ _ ih =>
    intro L S R e hS
    subst e
    obtain ⟨E, h1, h2, hb⟩ := ih (B :: L) S R (by simp) hS
    refine ⟨E, h1, LDer0.underR (by simp) (castD h2 (by simp)), fun p => ?_⟩
    have := hb p
    occBound
  | @overL G D T A B C hT hm ihT ihm =>
    intro L S R e hS
    have e' : L ++ S ++ R = G ++ over A B :: (T ++ D) := by rw [← e]; simp
    rcases split_mid e' with ⟨M, rfl, rfl⟩ | ⟨M, hM, rfl⟩ | ⟨P2, Q1, rfl, rfl, hQ⟩
    · obtain ⟨E, h1, h2, hb⟩ := ihm L S (M ++ [A] ++ D) (by simp) hS
      refine ⟨E, h1, castD (overL' (A := A) (L ++ [E] ++ M) D T hT h2 (by simp)) (by simp),
        fun p => ?_⟩
      have := hb p
      occBound
    · rcases split3 hM.symm with ⟨N, rfl, rfl⟩ | ⟨N, rfl, rfl⟩ |
        ⟨S1, S2, rfl, hS1, hS2, rfl, rfl⟩
      · obtain ⟨E, h1, h2, hb⟩ := ihT M S N rfl hS
        refine ⟨E, h1, castD (overL' (A := A) G D (M ++ [E] ++ N) h2 hm rfl) (by simp),
          fun p => ?_⟩
        have := hb p
        occBound
      · obtain ⟨E, h1, h2, hb⟩ := ihm (G ++ [A] ++ N) S R (by simp) hS
        refine ⟨E, h1, castD (overL' (A := A) G (N ++ [E] ++ R) T hT h2 (by simp)) (by simp),
          fun p => ?_⟩
        have := hb p
        occBound
      · obtain ⟨E, h1, h2, hb⟩ := ihT M S1 [] (by simp) hS1
        obtain ⟨F, h3, h4, hc⟩ := ihm (G ++ [A]) S2 R (by simp) hS2
        refine ⟨mul E F, LDer0.mulR h1 h3,
          castD (mulL' (A := E) (B := F) (G ++ over A B :: M) R
            (overL' (A := A) G (F :: R) (M ++ [E]) (castD h2 (by simp)) h4 (by simp)) (by simp))
            (by simp), fun p => ?_⟩
        have := hb p
        have := hc p
        occBound
    · rw [List.append_eq_append_iff] at hQ
      rcases hQ with ⟨a', rfl, rfl⟩ | ⟨c', rfl, rfl⟩
      · obtain ⟨E, h1, h2, hb⟩ := ihm L (P2 ++ [A] ++ a') R (by simp) (by simp)
        refine ⟨E, castD (overL' (A := A) P2 a' T hT h1 rfl) (by simp), h2, fun p => ?_⟩
        have := hb p
        occBound
      · by_cases hc : c' = []
        · subst hc
          obtain ⟨E, h1, h2, hb⟩ := ihm L (P2 ++ [A]) D (by simp) (by simp)
          refine ⟨E, castD (overL' (A := A) P2 [] (Q1 ++ []) hT h1 (by simp)) (by simp),
            castD h2 (by simp), fun p => ?_⟩
          have := hb p
          occBound
        · obtain ⟨E, h1, h2, hb⟩ := ihT Q1 c' [] (by simp) hc
          obtain ⟨F, h3, h4, hd⟩ := ihm L (P2 ++ [A]) D (by simp) (by simp)
          refine ⟨over F E,
            LDer0.overR (by simp)
              (castD (overL' (A := A) P2 [] (Q1 ++ [E]) (castD h2 (by simp)) h3 (by simp))
                (by simp)),
            castD (overL' (A := F) L D c' h1 h4 (by simp)) (by simp), fun p => ?_⟩
          have := hb p
          have := hd p
          occBound
  | @underL G D T A B C hT hm ihT ihm =>
    intro L S R e hS
    have e' : L ++ S ++ R = (G ++ T) ++ under B A :: D := by rw [← e]; simp
    rcases split_mid e' with ⟨M, hM, rfl⟩ | ⟨M, rfl, rfl⟩ | ⟨P2, Q1, rfl, hP, rfl⟩
    · rcases split3 hM.symm with ⟨N, rfl, rfl⟩ | ⟨N, rfl, rfl⟩ |
        ⟨S1, S2, rfl, hS1, hS2, rfl, rfl⟩
      · obtain ⟨E, h1, h2, hb⟩ := ihm L S (N ++ [A] ++ D) (by simp) hS
        refine ⟨E, h1, castD (underL' (A := A) (L ++ [E] ++ N) D T hT h2 (by simp)) (by simp),
          fun p => ?_⟩
        have := hb p
        occBound
      · obtain ⟨E, h1, h2, hb⟩ := ihT N S M rfl hS
        refine ⟨E, h1, castD (underL' (A := A) G D (N ++ [E] ++ M) h2 hm rfl) (by simp),
          fun p => ?_⟩
        have := hb p
        occBound
      · obtain ⟨E, h1, h2, hb⟩ := ihm L S1 ([A] ++ D) (by simp) hS1
        obtain ⟨F, h3, h4, hc⟩ := ihT [] S2 M (by simp) hS2
        refine ⟨mul E F, LDer0.mulR h1 h3,
          castD (mulL' (A := E) (B := F) L (M ++ under B A :: D)
            (underL' (A := A) (L ++ [E]) D (F :: M) (castD h4 (by simp)) h2 (by simp)) (by simp))
            (by simp), fun p => ?_⟩
        have := hb p
        have := hc p
        occBound
    · obtain ⟨E, h1, h2, hb⟩ := ihm (G ++ [A] ++ M) S R (by simp) hS
      refine ⟨E, h1, castD (underL' (A := A) G (M ++ [E] ++ R) T hT h2 (by simp)) (by simp),
        fun p => ?_⟩
      have := hb p
      occBound
    · rw [List.append_eq_append_iff] at hP
      rcases hP with ⟨a', rfl, rfl⟩ | ⟨c', rfl, rfl⟩
      · by_cases ha : a' = []
        · subst ha
          obtain ⟨E, h1, h2, hb⟩ := ihm (G ++ []) ([A] ++ Q1) R (by simp) (by simp)
          refine ⟨E, castD (underL' (A := A) [] Q1 ([] ++ P2) hT h1 (by simp)) (by simp), h2,
            fun p => ?_⟩
          have := hb p
          occBound
        · obtain ⟨E, h1, h2, hb⟩ := ihT [] a' P2 (by simp) ha
          obtain ⟨F, h3, h4, hd⟩ := ihm G ([A] ++ Q1) R (by simp) (by simp)
          refine ⟨under E F,
            LDer0.underR (by simp)
              (castD (underL' (A := A) [] Q1 (E :: P2) (castD h2 (by simp)) h3 (by simp))
                (by simp)),
            castD (underL' (A := F) G R a' h1 h4 (by simp)) (by simp), fun p => ?_⟩
          have := hb p
          have := hd p
          occBound
      · obtain ⟨E, h1, h2, hb⟩ := ihm L (c' ++ [A] ++ Q1) R (by simp) (by simp)
        refine ⟨E, castD (underL' (A := A) c' Q1 T hT h1 rfl) (by simp), h2, fun p => ?_⟩
        have := hb p
        occBound
  | @mulR G D A B _ _ ih1 ih2 =>
    intro L S R e hS
    rcases split3 e.symm with ⟨M, rfl, rfl⟩ | ⟨M, rfl, rfl⟩ |
      ⟨S1, S2, rfl, hS1, hS2, rfl, rfl⟩
    · obtain ⟨E, h1, h2, hb⟩ := ih1 L S M rfl hS
      refine ⟨E, h1, castD (LDer0.mulR h2 ‹LDer0 D B›) (by simp), fun p => ?_⟩
      have := hb p
      occBound
    · obtain ⟨E, h1, h2, hb⟩ := ih2 M S R rfl hS
      refine ⟨E, h1, castD (LDer0.mulR ‹LDer0 G A› h2) (by simp), fun p => ?_⟩
      have := hb p
      occBound
    · obtain ⟨E, h1, h2, hb⟩ := ih1 L S1 [] (by simp) hS1
      obtain ⟨F, h3, h4, hc⟩ := ih2 [] S2 R (by simp) hS2
      refine ⟨mul E F, LDer0.mulR h1 h3,
        castD (mulL' (A := E) (B := F) L R
          (LDer0.mulR (castD h2 (by simp) : LDer0 (L ++ [E]) A)
            (castD h4 (by simp) : LDer0 (F :: R) B)) (by simp)) (by simp), fun p => ?_⟩
      have := hb p
      have := hc p
      occBound
  | @mulL G D A B C _ ih =>
    intro L S R e hS
    have e' : L ++ S ++ R = G ++ mul A B :: D := by rw [← e]; simp
    rcases split_mid e' with ⟨M, rfl, rfl⟩ | ⟨M, rfl, rfl⟩ | ⟨P2, Q1, rfl, rfl, rfl⟩
    · obtain ⟨E, h1, h2, hb⟩ := ih L S (M ++ [A, B] ++ D) (by simp) hS
      refine ⟨E, h1, castD (mulL' (A := A) (B := B) (L ++ [E] ++ M) D h2 (by simp)) (by simp),
        fun p => ?_⟩
      have := hb p
      occBound
    · obtain ⟨E, h1, h2, hb⟩ := ih (G ++ [A, B] ++ M) S R (by simp) hS
      refine ⟨E, h1, castD (mulL' (A := A) (B := B) G (M ++ [E] ++ R) h2 (by simp)) (by simp),
        fun p => ?_⟩
      have := hb p
      occBound
    · obtain ⟨E, h1, h2, hb⟩ := ih L (P2 ++ [A, B] ++ Q1) R (by simp) (by simp)
      refine ⟨E, castD (mulL' (A := A) (B := B) P2 Q1 h1 rfl) (by simp), h2, fun p => ?_⟩
      have := hb p
      occBound

end LInterp

/-- Interpolation. If `Γ, Δ, Θ → C` is derivable and `Δ` is non-empty, there is a type `E`
    such that `Δ → E` and `Γ, E, Θ → C` are derivable, and every primitive type occurs in
    `E` at most as often as in `Δ` and at most as often as in the rest of the sequent. -/
theorem LDer0.interpolation [DecidableEq P] {Γ Δ Θ : List (LType P)} {C : LType P}
    (h : LDer0 (Γ ++ Δ ++ Θ) C) (hΔ : Δ ≠ []) :
    ∃ E : LType P, LDer0 Δ E ∧ LDer0 (Γ ++ [E] ++ Θ) C ∧
      ∀ p : P, E.occ p ≤ occList p Δ ∧ E.occ p ≤ occList p Γ + occList p Θ + C.occ p :=
  LInterp.main h Γ Δ Θ rfl hΔ

end FormalLinguistics
