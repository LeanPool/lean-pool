/-
Copyright (c) 2026 bocchitherock888-ux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: bocchitherock888-ux
-/

module

public import LeanPool.FormalLinguistics.LambekCore

/-!
  Cut admissibility for the cut-free Lambek calculus `LDer0`, and its equivalence with
  the calculus `LDer` of `Lambek.lean`.
-/

@[expose] public section

namespace FormalLinguistics

variable {P Q : Type}

/-- No sequent with an empty antecedent is derivable. -/
theorem LDer0.ne_nil {Γ : List (LType P)} {C : LType P} (h : LDer0 Γ C) : Γ ≠ [] := by
  induction h with
  | ax p => simp
  | overR hne _ _ => exact hne
  | underR hne _ _ => exact hne
  | overL _ _ _ _ => simp
  | underL _ _ _ _ => simp
  | mulR _ _ ih1 _ => simp [ih1]
  | mulL _ _ => simp

/-- The identity sequent `A → A` is derivable for every type. -/
theorem LDer0.identity (A : LType P) : LDer0 [A] A := by
  induction A with
  | prim p => exact LDer0.ax p
  | over A B ihA ihB =>
    refine LDer0.overR (by simp) ?_
    have := LDer0.overL (A := A) (B := B) (Γ := []) (Δ := []) ihB (by simpa using ihA)
    simpa using this
  | under B A ihB ihA =>
    refine LDer0.underR (by simp) ?_
    have := LDer0.underL (A := A) (B := B) (Γ := []) (Δ := []) ihB (by simpa using ihA)
    simpa using this
  | mul A B ihA ihB =>
    have := LDer0.mulL (A := A) (B := B) (Γ := []) (Δ := []) (by simpa using LDer0.mulR ihA ihB)
    simpa using this

namespace LCut

theorem cast {Γ Γ' : List (LType P)} {C : LType P} (h : LDer0 Γ C) (e : Γ = Γ') :
    LDer0 Γ' C := e ▸ h

theorem single_eq {α : Type} {Γ Δ : List α} {a b : α} (h : Γ ++ [a] ++ Δ = [b]) :
    Γ = [] ∧ a = b ∧ Δ = [] := by
  cases Γ with
  | nil => simpa using h
  | cons x Γ' => simp at h

theorem split1 {α : Type} {Γ Δ X Y : List α} {a : α} (h : Γ ++ [a] ++ Δ = X ++ Y) :
    (∃ M, X = Γ ++ [a] ++ M ∧ Δ = M ++ Y) ∨ (∃ M, Y = M ++ [a] ++ Δ ∧ Γ = X ++ M) := by
  rw [List.append_assoc, List.append_eq_append_iff] at h
  rcases h with ⟨a', hX, hY⟩ | ⟨c', hG, hY⟩
  · cases a' with
    | nil =>
      simp at hX hY
      subst hX hY
      right; exact ⟨[], by simp, by simp⟩
    | cons m a'' =>
      simp at hY
      obtain ⟨rfl, rfl⟩ := hY
      subst hX
      left; exact ⟨a'', by simp, rfl⟩
  · subst hG hY
    right; exact ⟨c', by simp, rfl⟩

theorem split2 {α : Type} {Γ Δ X Y : List α} {a b : α} (h : Γ ++ [a] ++ Δ = X ++ [b] ++ Y) :
    (Γ = X ∧ a = b ∧ Δ = Y) ∨ (∃ M, X = Γ ++ [a] ++ M ∧ Δ = M ++ [b] ++ Y) ∨
      (∃ M, Γ = X ++ [b] ++ M ∧ Y = M ++ [a] ++ Δ) := by
  rw [List.append_assoc X] at h
  rcases split1 h with ⟨M, hX, hD⟩ | ⟨M, hY, hG⟩
  · exact Or.inr (Or.inl ⟨M, hX, by simpa using hD⟩)
  · cases M with
    | nil =>
      simp at hY hG
      obtain ⟨rfl, rfl⟩ := hY
      exact Or.inl ⟨hG, rfl, rfl⟩
    | cons m M' =>
      simp at hY
      obtain ⟨rfl, rfl⟩ := hY
      exact Or.inr (Or.inr ⟨M', by simpa using hG, by simp⟩)

/-- Cut on the cut formula `X` with left premise `Θ → X`, by induction on the right
    premise, given the principal cases. -/
theorem inner {Θ : List (LType P)} {X : LType P} (h1 : LDer0 Θ X) (hne : Θ ≠ [])
    (hover : ∀ A B, X = LType.over A B → ∀ (Θ' Γ Δ : List (LType P)) (C : LType P),
      LDer0 Θ' B → LDer0 (Γ ++ [A] ++ Δ) C → LDer0 (Γ ++ Θ ++ Θ' ++ Δ) C)
    (hunder : ∀ A B, X = LType.under B A → ∀ (Θ' Γ Δ : List (LType P)) (C : LType P),
      LDer0 Θ' B → LDer0 (Γ ++ [A] ++ Δ) C → LDer0 (Γ ++ Θ' ++ Θ ++ Δ) C)
    (hmul : ∀ A B, X = LType.mul A B → ∀ (Γ Δ : List (LType P)) (C : LType P),
      LDer0 (Γ ++ [A, B] ++ Δ) C → LDer0 (Γ ++ Θ ++ Δ) C) :
    ∀ (Γ Δ : List (LType P)) (C : LType P),
      LDer0 (Γ ++ [X] ++ Δ) C → LDer0 (Γ ++ Θ ++ Δ) C := by
  intro Γ Δ C h2
  generalize hE : Γ ++ [X] ++ Δ = L at h2
  induction h2 generalizing Γ Δ with
  | ax p =>
    obtain ⟨rfl, rfl, rfl⟩ := single_eq hE
    simpa using h1
  | @overR G A B _ _ ih =>
    subst hE
    exact LDer0.overR (by simp [hne]) (cast (ih Γ (Δ ++ [B]) (by simp)) (by simp))
  | @underR G A B _ _ ih =>
    subst hE
    exact LDer0.underR (by simp [hne]) (cast (ih (B :: Γ) Δ (by simp)) (by simp))
  | @overL G D T A B C k1 k2 ih1 ih2 =>
    have hE' : Γ ++ [X] ++ Δ = G ++ [LType.over A B] ++ (T ++ D) := hE.trans (by simp)
    rcases split2 hE' with ⟨rfl, rfl, rfl⟩ | ⟨M, rfl, rfl⟩ | ⟨M, rfl, hTD⟩
    · exact cast (hover A B rfl T Γ D C k1 k2) (by simp)
    · have := ih2 Γ (M ++ [A] ++ D) (by simp)
      exact cast (LDer0.overL (A := A) (B := B) (Γ := Γ ++ Θ ++ M) (Δ := D) k1 (cast this (by simp)))
        (by simp)
    · rcases split1 hTD.symm with ⟨N, rfl, rfl⟩ | ⟨N, rfl, rfl⟩
      · have := ih1 M N rfl
        exact cast (LDer0.overL (A := A) (B := B) (Γ := G) (Δ := D) this k2) (by simp)
      · have := ih2 (G ++ [A] ++ N) Δ (by simp)
        exact cast (LDer0.overL (A := A) (B := B) (Γ := G) (Δ := N ++ Θ ++ Δ) k1 (cast this (by simp)))
          (by simp)
  | @underL G D T A B C k1 k2 ih1 ih2 =>
    rcases split2 hE with ⟨rfl, rfl, rfl⟩ | ⟨M, hGT, rfl⟩ | ⟨M, rfl, rfl⟩
    · exact cast (hunder A B rfl T G _ C k1 k2) (by simp)
    · rcases split1 hGT.symm with ⟨N, rfl, rfl⟩ | ⟨N, rfl, rfl⟩
      · have := ih2 Γ (N ++ [A] ++ D) (by simp)
        exact cast (LDer0.underL (A := A) (B := B) (Γ := Γ ++ Θ ++ N) (Δ := D) k1 (cast this (by simp)))
          (by simp)
      · have := ih1 N M rfl
        exact cast (LDer0.underL (A := A) (B := B) (Γ := G) (Δ := D) this k2) (by simp)
    · have := ih2 (G ++ [A] ++ M) Δ (by simp)
      exact cast (LDer0.underL (A := A) (B := B) (Γ := G) (Δ := M ++ Θ ++ Δ) k1 (cast this (by simp)))
        (by simp)
  | @mulR G D A B k1 k2 ih1 ih2 =>
    rcases split1 hE with ⟨M, rfl, rfl⟩ | ⟨M, rfl, rfl⟩
    · exact cast (LDer0.mulR (ih1 Γ M rfl) k2) (by simp)
    · exact cast (LDer0.mulR k1 (ih2 M Δ rfl)) (by simp)
  | @mulL G D A B C k ih =>
    rcases split2 hE with ⟨rfl, rfl, rfl⟩ | ⟨M, rfl, rfl⟩ | ⟨M, rfl, rfl⟩
    · exact hmul A B rfl Γ Δ C k
    · have := ih Γ (M ++ [A, B] ++ D) (by simp)
      exact cast (LDer0.mulL (A := A) (B := B) (Γ := Γ ++ Θ ++ M) (Δ := D) (cast this (by simp))) (by simp)
    · have := ih (G ++ [A, B] ++ M) Δ (by simp)
      exact cast (LDer0.mulL (A := A) (B := B) (Γ := G) (Δ := M ++ Θ ++ Δ) (cast this (by simp))) (by simp)

/-- Cut is admissible on the type `X`. -/
def CutAdm (X : LType P) : Prop :=
  ∀ (Θ Γ Δ : List (LType P)) (C : LType P),
    LDer0 Θ X → LDer0 (Γ ++ [X] ++ Δ) C → LDer0 (Γ ++ Θ ++ Δ) C

/-- Cut is admissible on the immediate subtypes of a type. -/
def SubAdm : LType P → Prop
  | .prim _ => True
  | .over A B => CutAdm A ∧ CutAdm B
  | .under B A => CutAdm B ∧ CutAdm A
  | .mul A B => CutAdm A ∧ CutAdm B

/-- Cut on `X`, by induction on the left premise, given cut on the subtypes of `X`. -/
theorem outer {Θ : List (LType P)} {X : LType P} (h1 : LDer0 Θ X) :
    SubAdm X → ∀ (Γ Δ : List (LType P)) (C : LType P),
      LDer0 (Γ ++ [X] ++ Δ) C → LDer0 (Γ ++ Θ ++ Δ) C := by
  induction h1 with
  | ax p =>
    intro _ Γ Δ C h2
    exact h2
  | @overR G A B hne k _ =>
    intro hs Γ Δ C h2
    simp only [SubAdm] at hs
    refine inner (LDer0.overR hne k) hne ?_ (fun _ _ e => by cases e)
      (fun _ _ e => by cases e) Γ Δ C h2
    intro A' B' e
    cases e
    intro Θ' Γ' Δ' C' hb hc
    have k' := hs.2 Θ' G [] A hb (cast k (by simp))
    exact cast (hs.1 (G ++ Θ') Γ' Δ' C' (cast k' (by simp)) hc) (by simp)
  | @underR G A B hne k _ =>
    intro hs Γ Δ C h2
    simp only [SubAdm] at hs
    refine inner (LDer0.underR hne k) hne (fun _ _ e => by cases e) ?_
      (fun _ _ e => by cases e) Γ Δ C h2
    intro A' B' e
    cases e
    intro Θ' Γ' Δ' C' hb hc
    have k' := hs.1 Θ' [] G A hb (cast k (by simp))
    exact cast (hs.2 (Θ' ++ G) Γ' Δ' C' (cast k' (by simp)) hc) (by simp)
  | @overL G D T A B Y k1 _ _ ih2 =>
    intro hs Γ Δ C h2
    have := ih2 hs Γ Δ C h2
    exact cast (LDer0.overL (A := A) (B := B) (Γ := Γ ++ G) (Δ := D ++ Δ) k1 (cast this (by simp))) (by simp)
  | @underL G D T A B Y k1 _ _ ih2 =>
    intro hs Γ Δ C h2
    have := ih2 hs Γ Δ C h2
    exact cast (LDer0.underL (A := A) (B := B) (Γ := Γ ++ G) (Δ := D ++ Δ) k1 (cast this (by simp))) (by simp)
  | @mulR G D A B k1 k2 _ _ =>
    intro hs Γ Δ C h2
    simp only [SubAdm] at hs
    have hne : G ++ D ≠ [] := by simp [LDer0.ne_nil k1]
    refine inner (LDer0.mulR k1 k2) hne (fun _ _ e => by cases e) (fun _ _ e => by cases e)
      ?_ Γ Δ C h2
    intro A' B' e
    cases e
    intro Γ' Δ' C' hc
    have k' := hs.2 D (Γ' ++ [A]) Δ' C' k2 (cast hc (by simp))
    exact cast (hs.1 G Γ' (D ++ Δ') C' k1 (cast k' (by simp))) (by simp)
  | @mulL G D A B Y _ ih =>
    intro hs Γ Δ C h2
    have := ih hs Γ Δ C h2
    exact cast (LDer0.mulL (A := A) (B := B) (Γ := Γ ++ G) (Δ := D ++ Δ) (cast this (by simp))) (by simp)

theorem cutAdm (X : LType P) : CutAdm X := by
  induction X with
  | prim p =>
    intro Θ Γ Δ C h1 h2
    exact outer h1 (by simp only [SubAdm]) Γ Δ C h2
  | over A B ihA ihB =>
    intro Θ Γ Δ C h1 h2
    exact outer h1 (by simp only [SubAdm]; exact ⟨ihA, ihB⟩) Γ Δ C h2
  | under B A ihB ihA =>
    intro Θ Γ Δ C h1 h2
    exact outer h1 (by simp only [SubAdm]; exact ⟨ihB, ihA⟩) Γ Δ C h2
  | mul A B ihA ihB =>
    intro Θ Γ Δ C h1 h2
    exact outer h1 (by simp only [SubAdm]; exact ⟨ihA, ihB⟩) Γ Δ C h2

end LCut

/-- Cut is admissible in the cut-free calculus. -/
theorem LDer0.cut {Γ Δ Θ : List (LType P)} {A C : LType P}
    (h1 : LDer0 Θ A) (h2 : LDer0 (Γ ++ [A] ++ Δ) C) : LDer0 (Γ ++ Θ ++ Δ) C :=
  LCut.cutAdm A Θ Γ Δ C h1 h2

/-- The cut-free calculus derives the same sequents as the calculus with cut. -/
theorem LDer_iff_LDer0 {Γ : List (LType P)} {C : LType P} : LDer Γ C ↔ LDer0 Γ C := by
  constructor
  · intro h
    induction h with
    | ax A => exact LDer0.identity A
    | overR hne _ ih => exact LDer0.overR hne ih
    | underR hne _ ih => exact LDer0.underR hne ih
    | overL _ _ ih1 ih2 => exact LDer0.overL ih1 ih2
    | underL _ _ ih1 ih2 => exact LDer0.underL ih1 ih2
    | mulR _ _ ih1 ih2 => exact LDer0.mulR ih1 ih2
    | mulL _ ih => exact LDer0.mulL ih
    | cut _ _ ih1 ih2 => exact LDer0.cut ih1 ih2
  · intro h
    induction h with
    | ax p => exact LDer.ax _
    | overR hne _ ih => exact LDer.overR hne ih
    | underR hne _ ih => exact LDer.underR hne ih
    | overL _ _ ih1 ih2 => exact LDer.overL ih1 ih2
    | underL _ _ ih1 ih2 => exact LDer.underL ih1 ih2
    | mulR _ _ ih1 ih2 => exact LDer.mulR ih1 ih2
    | mulL _ ih => exact LDer.mulL ih

/-- Derivability is preserved by renaming primitive types. -/
theorem LDer0.map (f : P → Q) {Γ : List (LType P)} {C : LType P} (h : LDer0 Γ C) :
    LDer0 (Γ.map (LType.map f)) (C.map f) := by
  induction h with
  | ax p => exact LDer0.ax (f p)
  | overR hne _ ih =>
    exact LDer0.overR (by simpa using hne) (by simpa using ih)
  | underR hne _ ih =>
    exact LDer0.underR (by simpa using hne) (by simpa using ih)
  | overL _ _ ih1 ih2 =>
    simpa [LType.map] using LDer0.overL ih1 (by simpa using ih2)
  | underL _ _ ih1 ih2 =>
    simpa [LType.map] using LDer0.underL ih1 (by simpa using ih2)
  | mulR _ _ ih1 ih2 =>
    simpa [LType.map] using LDer0.mulR ih1 ih2
  | mulL _ ih =>
    simpa [LType.map] using LDer0.mulL (by simpa using ih)

end FormalLinguistics
