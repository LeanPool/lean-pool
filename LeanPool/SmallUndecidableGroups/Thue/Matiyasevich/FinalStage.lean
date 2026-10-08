/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Thue.Matiyasevich.Reduction
public import Mathlib.Tactic.FinCases

/-! ## Section 2.5: `T₂` to the final binary three-rule system -/

@[expose] public section

namespace Undecidability

namespace Thue

namespace Matiyasevich1993

/-- The letters `a`, `b`, and `e` of the penultimate alphabet. -/
abbrev A₂ := Fin 3

/-- The first letter of the three-letter alphabet used in the final binary encoding. -/
abbrev finalLetterA : A₂ := 0
/-- The second letter of the three-letter alphabet used in the final binary encoding. -/
abbrev finalLetterB : A₂ := 1
/-- The third letter of the three-letter alphabet used in the final binary encoding. -/
abbrev finalLetterE : A₂ := 2

/-- Equation (26), with `c = 1` and `d = 0`. -/
def rho₂Letter : A₂ → List (Fin 2) := ![
  [(1 : Fin 2)],
  [(1 : Fin 2), 0],
  [(0 : Fin 2), 0]
]

/-- The homomorphic extension of `ρ₂` to words. -/
def rho₂ (W : List A₂) : List (Fin 2) :=
  W.flatMap rho₂Letter

@[simp] theorem rho₂_cons (x : A₂) (W : List A₂) :
    rho₂ (x :: W) = rho₂Letter x ++ rho₂ W := by
  simp [rho₂]

@[simp] theorem rho₂_append (X Y : List A₂) :
    rho₂ (X ++ Y) = rho₂ X ++ rho₂ Y := by
  simp [rho₂]

theorem rho₂_computable : Computable rho₂ :=
  (Primrec.list_flatMap Primrec.id
    ((Primrec.dom_finite rho₂Letter).comp₂ Primrec₂.right)).to_comp

/-- The right-to-left decoder `φ₂` from page 51, expressed on the reversed
input.  Reversed codewords are `1`, `01`, and `00`; a lone leading `0` is the
single possible unmatched `d`. -/
def phi₂Aux : List (Fin 2) → List A₂
  | [] => []
  | x :: xs =>
      if x = 1 then
        finalLetterA :: phi₂Aux xs
      else
        match xs with
        | [] => []
        | y :: ys =>
            if y = 1 then finalLetterB :: phi₂Aux ys else finalLetterE :: phi₂Aux ys

/-- The inverse map `φ₂` in the orientation used in the paper. -/
def phi₂ (W : List (Fin 2)) : List A₂ :=
  (phi₂Aux (W.reverse)).reverse

private theorem phi₂Aux_rho₂_reverse_append (W : List A₂)
    (Z : List (Fin 2)) :
    phi₂Aux ((rho₂ W).reverse ++ Z) = W.reverse ++ phi₂Aux Z := by
  induction W generalizing Z with
  | nil => simp [rho₂]
  | cons x W ih =>
      rw [rho₂_cons, List.reverse_append, List.append_assoc, ih]
      fin_cases x
      · simp only [rho₂Letter]
        rw [phi₂Aux.eq_def]
        simp [finalLetterA]
      · simp only [rho₂Letter]
        rw [phi₂Aux.eq_def]
        simp [finalLetterB]
      · simp only [rho₂Letter]
        rw [phi₂Aux.eq_def]
        simp [finalLetterE]

/-- `φ₂` is a left inverse to the binary encoding, as required below (26). -/
@[simp] theorem phi₂_rho₂ (W : List A₂) : phi₂ (rho₂ W) = W := by
  have h := phi₂Aux_rho₂_reverse_append W []
  simp only [List.append_nil] at h
  rw [phi₂, h]
  simp [phi₂Aux]

/-- Appending a complete encoded word cannot interact with the decoding of
the prefix.  This is the algebraic form of the right-to-left parsing used on
page 52. -/
theorem phi₂_append_rho₂ (X : List (Fin 2)) (W : List A₂) :
    phi₂ (X ++ rho₂ W) = phi₂ X ++ W := by
  have h := phi₂Aux_rho₂_reverse_append W X.reverse
  have h' := congrArg List.reverse h
  simpa [phi₂, List.reverse_append] using h'

theorem phi₂_context_rho₂ (l : List (Fin 2)) (X Y : List A₂) :
    phi₂ (l ++ rho₂ X ++ rho₂ Y) = phi₂ l ++ X ++ Y := by
  calc
    phi₂ (l ++ rho₂ X ++ rho₂ Y) =
        phi₂ (l ++ (rho₂ X ++ rho₂ Y)) := by rw [List.append_assoc]
    _ = phi₂ (l ++ rho₂ (X ++ Y)) := by rw [rho₂_append]
    _ = phi₂ l ++ (X ++ Y) := phi₂_append_rho₂ l (X ++ Y)
    _ = phi₂ l ++ X ++ Y := by rw [List.append_assoc]

private theorem phi₂_context_of_encoded_block (l block : List (Fin 2))
    (X Y : List A₂) (hblock : block = rho₂ X) :
    phi₂ (l ++ block ++ rho₂ Y) = phi₂ l ++ X ++ Y := by
  subst block
  exact phi₂_context_rho₂ l X Y

/-- The word encoding obtained by reversing the input and output of `ρ₂`. -/
def rho₂Reverse (W : List A₂) : List (Fin 2) :=
  (rho₂ W.reverse).reverse

private theorem rho₂Reverse_cons (x : A₂) (W : List A₂) :
    rho₂Reverse (x :: W) = (rho₂Letter x).reverse ++ rho₂Reverse W := by
  simp [rho₂Reverse, rho₂]

private theorem fin₂_cases (x : Fin 2) : x = 0 ∨ x = 1 := by
  omega

private theorem fin₃_cases (x : Fin 3) : x = 0 ∨ x = 1 ∨ x = 2 := by
  omega

@[simp] private theorem phi₂Aux_c (Z : List (Fin 2)) :
    phi₂Aux ((1 : Fin 2) :: Z) = finalLetterA :: phi₂Aux Z := by
  rw [phi₂Aux.eq_def]
  simp

@[simp] private theorem phi₂Aux_dd (Z : List (Fin 2)) :
    phi₂Aux ((0 : Fin 2) :: 0 :: Z) = finalLetterE :: phi₂Aux Z := by
  rw [phi₂Aux.eq_def]
  simp

@[simp] private theorem phi₂Aux_dc (Z : List (Fin 2)) :
    phi₂Aux ((0 : Fin 2) :: 1 :: Z) = finalLetterB :: phi₂Aux Z := by
  rw [phi₂Aux.eq_def]
  simp

@[simp] private theorem rho₂Reverse_a (W : List A₂) :
    rho₂Reverse (finalLetterA :: W) = (1 : Fin 2) :: rho₂Reverse W := by
  simpa [rho₂Letter, finalLetterA] using rho₂Reverse_cons finalLetterA W

@[simp] private theorem rho₂Reverse_b (W : List A₂) :
    rho₂Reverse (finalLetterB :: W) = (0 : Fin 2) :: 1 :: rho₂Reverse W := by
  simpa [rho₂Letter, finalLetterB] using rho₂Reverse_cons finalLetterB W

@[simp] private theorem rho₂Reverse_e (W : List A₂) :
    rho₂Reverse (finalLetterE :: W) = (0 : Fin 2) :: 0 :: rho₂Reverse W := by
  simpa [rho₂Letter, finalLetterE] using rho₂Reverse_cons finalLetterE W

/-- The parser consumes every binary word, with at most one unmatched initial
`d`.  This is the dichotomy immediately after the definition of `φ₂` on
page 51 (written here on reversed words). -/
private theorem phi₂Aux_reconstruct (Z : List (Fin 2)) :
    Z = rho₂Reverse (phi₂Aux Z) ∨
      Z = rho₂Reverse (phi₂Aux Z) ++ [(0 : Fin 2)] := by
  induction Z using List.twoStepInduction with
  | nil => exact Or.inl (by simp [phi₂Aux, rho₂Reverse, rho₂])
  | singleton x =>
      rcases fin₂_cases x with rfl | rfl
      · exact Or.inr (by simp [phi₂Aux.eq_def, rho₂Reverse, rho₂])
      · exact Or.inl (by
          rw [phi₂Aux_c, rho₂Reverse_a]
          simp [phi₂Aux, rho₂Reverse, rho₂])
  | cons_cons x y xs ih ih₁ =>
      rcases fin₂_cases x with rfl | rfl
      · rcases fin₂_cases y with rfl | rfl
        · rcases ih with h | h
          · exact Or.inl (by
              rw [phi₂Aux_dd, rho₂Reverse_e]
              exact congrArg ((0 : Fin 2) :: 0 :: ·) h)
          · exact Or.inr (by
              rw [phi₂Aux_dd, rho₂Reverse_e]
              simpa only [List.cons_append] using
                congrArg ((0 : Fin 2) :: 0 :: ·) h)
        · rcases ih with h | h
          · exact Or.inl (by
              rw [phi₂Aux_dc, rho₂Reverse_b]
              exact congrArg ((0 : Fin 2) :: 1 :: ·) h)
          · exact Or.inr (by
              rw [phi₂Aux_dc, rho₂Reverse_b]
              simpa only [List.cons_append] using
                congrArg ((0 : Fin 2) :: 1 :: ·) h)
      · have htail := ih₁ y
        rcases htail with h | h
        · exact Or.inl (by
            rw [phi₂Aux_c, rho₂Reverse_a]
            exact congrArg ((1 : Fin 2) :: ·) h)
        · exact Or.inr (by
            rw [phi₂Aux_c, rho₂Reverse_a]
            simpa only [List.cons_append] using congrArg ((1 : Fin 2) :: ·) h)

/-- Equivalently, every binary word is either exactly an encoded word or is
an encoded word preceded by the unmatched letter `d`. -/
theorem rho₂_phi₂_reconstruct (W : List (Fin 2)) :
    rho₂ (phi₂ W) = W ∨ (0 : Fin 2) :: rho₂ (phi₂ W) = W := by
  have h := phi₂Aux_reconstruct W.reverse
  rcases h with h | h
  · left
    have := congrArg List.reverse h
    simpa [phi₂, rho₂Reverse] using this.symm
  · right
    have := congrArg List.reverse h
    simpa [phi₂, rho₂Reverse] using this.symm

/-!
The converse to `rho₂_forward` is deliberately not stated for arbitrary
`T₂` words.  Equivalence (10) only applies to words obtained from the original
`T₀` words by the preceding encodings.  Matiyasevich's converse on pages 50--52
uses two invariants of those reachable words:

1. the priority normal form has no run of more than two `a`'s;
2. it has exactly `u` occurrences of `e`, all forced to lie to the left of an
   occurrence of the long rule.

These invariants rule out the sole bad decoder alignment: the unmatched `d`
from `rho₂_phi₂_reconstruct` immediately following `ρ₂(L)` or `ρ₂(M)`.
Treating `rho₂` as an unrestricted embedding would therefore assert a stronger
statement than the paper proves.
-/

/-- The five left sides (20)--(24) of `T₂`. -/
def stage₂F (L : List A₂) : Fin 5 → List A₂ := ![
  [finalLetterE, finalLetterA, finalLetterA],
  [finalLetterE, finalLetterA, finalLetterB],
  [finalLetterE, finalLetterB, finalLetterA],
  [finalLetterE, finalLetterB, finalLetterB],
  L
]

/-- The five right sides (20)--(24) of `T₂`. -/
def stage₂E (M : List A₂) : Fin 5 → List A₂ := ![
  [finalLetterA, finalLetterE],
  [finalLetterB, finalLetterE],
  [finalLetterA, finalLetterE],
  [finalLetterB, finalLetterE],
  M
]

/-- The five-rule priority-stage Thue system parametrized by its long relation. -/
def stage₂System (L M : List A₂) : ThueSystem A₂ :=
  finiteSystem (stage₂F L) (stage₂E M)

private theorem base_rule_step (U V : List (Fin 2)) (i : Fin 3)
    (l r : List (Fin 2)) :
    ThueStep (baseSystem U V)
      (l ++ baseF U i ++ r) (l ++ baseE V i ++ r) :=
  ⟨l, r, baseF U i, baseE V i, ⟨i, rfl⟩,
    Or.inl ⟨rfl, rfl⟩⟩

/-- Each of the five rules of `T₂` is simulated by the final three rules.
The middle two housekeeping simulations use the first or second final rule in
a one-letter right context. -/
theorem rho₂_rule (L M : List A₂) (i : Fin 5) :
    ThueEq (baseSystem (rho₂ L) (rho₂ M))
      (rho₂ (stage₂F L i)) (rho₂ (stage₂E M i)) := by
  fin_cases i
  · exact Relation.ReflTransGen.single
      (by simpa [rho₂, rho₂Letter, stage₂F, stage₂E, baseF, baseE,
        finalLetterA, finalLetterB, finalLetterE] using
        base_rule_step (rho₂ L) (rho₂ M) 1 [] [])
  · exact Relation.ReflTransGen.single
      (by simpa [rho₂, rho₂Letter, stage₂F, stage₂E, baseF, baseE,
        finalLetterA, finalLetterB, finalLetterE] using
        base_rule_step (rho₂ L) (rho₂ M) 1 [] [(0 : Fin 2)])
  · exact Relation.ReflTransGen.single
      (by simpa [rho₂, rho₂Letter, stage₂F, stage₂E, baseF, baseE,
        finalLetterA, finalLetterB, finalLetterE] using
        base_rule_step (rho₂ L) (rho₂ M) 0 [] [])
  · exact Relation.ReflTransGen.single
      (by simpa [rho₂, rho₂Letter, stage₂F, stage₂E, baseF, baseE,
        finalLetterA, finalLetterB, finalLetterE] using
        base_rule_step (rho₂ L) (rho₂ M) 0 [] [(0 : Fin 2)])
  · exact Relation.ReflTransGen.single
      (by simpa [rho₂, rho₂Letter, stage₂F, stage₂E, baseF, baseE,
        finalLetterA, finalLetterB, finalLetterE] using
        base_rule_step (rho₂ L) (rho₂ M) 2 [] [])

/-- Forward half of equivalence (10) for the last stage. -/
theorem rho₂_step (L M : List A₂) {X Y : List A₂}
    (h : ThueStep (stage₂System L M) X Y) :
    ThueEq (baseSystem (rho₂ L) (rho₂ M)) (rho₂ X) (rho₂ Y) := by
  rcases h with ⟨l, r, x, y, ⟨i, hxy⟩, h⟩
  injection hxy with hx hy
  subst x
  subst y
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simpa only [rho₂_append] using
      thueEq_context (rho₂ l) (rho₂ r) (rho₂_rule L M i)
  · simpa only [rho₂_append] using
      thueEq_context (rho₂ l) (rho₂ r) (thueEq_symm (rho₂_rule L M i))

/-- Forward half of equivalence (10) for arbitrary derivations. -/
theorem rho₂_forward (L M : List A₂) {X Y : List A₂}
    (h : ThueEq (stage₂System L M) X Y) :
    ThueEq (baseSystem (rho₂ L) (rho₂ M)) (rho₂ X) (rho₂ Y) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.trans (rho₂_step L M hbc)

/-- Every nonempty `T₂` word has nonempty binary encoding. -/
theorem rho₂_ne_nil {W : List A₂} (hW : W ≠ []) : rho₂ W ≠ [] := by
  cases W with
  | nil => contradiction
  | cons x W =>
      fin_cases x <;> simp [rho₂, rho₂Letter]

private theorem stage₂_rule_step (L M : List A₂) (i : Fin 5)
    (l r : List A₂) :
    ThueStep (stage₂System L M)
      (l ++ stage₂F L i ++ r) (l ++ stage₂E M i ++ r) :=
  ⟨l, r, stage₂F L i, stage₂E M i, ⟨i, rfl⟩,
    Or.inl ⟨rfl, rfl⟩⟩

/-- A use of either short final relation always decodes to one of the four
housekeeping relations (20)--(23).  Which one is selected is determined by the
single residual `d` at the beginning of the right context. -/
theorem phi₂_short_rule (L M : List A₂) (i : Fin 3) (hi : i ≠ 2)
    (l r : List (Fin 2)) :
    ThueEq (stage₂System L M)
      (phi₂ (l ++ baseF (rho₂ L) i ++ r))
      (phi₂ (l ++ baseE (rho₂ M) i ++ r)) := by
  rcases rho₂_phi₂_reconstruct r with hr | hr
  · rcases fin₃_cases i with hi0 | hi1 | hi2
    · have hF : baseF (rho₂ L) 0 = rho₂ [finalLetterE, finalLetterB, finalLetterA] := by
        simp [baseF, rho₂, rho₂Letter, finalLetterA, finalLetterB, finalLetterE]
      have hE : baseE (rho₂ M) 0 = rho₂ [finalLetterA, finalLetterE] := by
        simp [baseE, rho₂, rho₂Letter, finalLetterA, finalLetterE]
      subst i
      have hleft := phi₂_context_of_encoded_block l
        (baseF (rho₂ L) 0) [finalLetterE, finalLetterB, finalLetterA] (phi₂ r) hF
      have hright := phi₂_context_of_encoded_block l
        (baseE (rho₂ M) 0) [finalLetterA, finalLetterE] (phi₂ r) hE
      rw [hr] at hleft hright
      rw [hleft, hright]
      exact Relation.ReflTransGen.single
        (stage₂_rule_step L M 2 (phi₂ l) (phi₂ r))
    · have hF : baseF (rho₂ L) 1 = rho₂ [finalLetterE, finalLetterA, finalLetterA] := by
        simp [baseF, rho₂, rho₂Letter, finalLetterA, finalLetterE]
      have hE : baseE (rho₂ M) 1 = rho₂ [finalLetterA, finalLetterE] := by
        simp [baseE, rho₂, rho₂Letter, finalLetterA, finalLetterE]
      subst i
      have hleft := phi₂_context_of_encoded_block l
        (baseF (rho₂ L) 1) [finalLetterE, finalLetterA, finalLetterA] (phi₂ r) hF
      have hright := phi₂_context_of_encoded_block l
        (baseE (rho₂ M) 1) [finalLetterA, finalLetterE] (phi₂ r) hE
      rw [hr] at hleft hright
      rw [hleft, hright]
      exact Relation.ReflTransGen.single
        (stage₂_rule_step L M 0 (phi₂ l) (phi₂ r))
    · subst i
      exact (hi rfl).elim
  · rcases fin₃_cases i with hi0 | hi1 | hi2
    · have hF :
          baseF (rho₂ L) 0 ++ [(0 : Fin 2)] = rho₂ [finalLetterE, finalLetterB, finalLetterB] := by
        simp [baseF, rho₂, rho₂Letter, finalLetterB, finalLetterE]
      have hE : baseE (rho₂ M) 0 ++ [(0 : Fin 2)] = rho₂ [finalLetterB, finalLetterE] := by
        simp [baseE, rho₂, rho₂Letter, finalLetterB, finalLetterE]
      subst i
      have hleft := phi₂_context_of_encoded_block l
        (baseF (rho₂ L) 0 ++ [(0 : Fin 2)]) [finalLetterE, finalLetterB, finalLetterB]
        (phi₂ r) hF
      have hright := phi₂_context_of_encoded_block l
        (baseE (rho₂ M) 0 ++ [(0 : Fin 2)]) [finalLetterB, finalLetterE] (phi₂ r) hE
      have hleft' :
          phi₂ (l ++ baseF (rho₂ L) 0 ++ r) =
            phi₂ l ++ [finalLetterE, finalLetterB, finalLetterB] ++ phi₂ r := by
        calc
          phi₂ (l ++ baseF (rho₂ L) 0 ++ r) =
              phi₂ (l ++ baseF (rho₂ L) 0 ++
                ((0 : Fin 2) :: rho₂ (phi₂ r))) := by rw [hr]
          _ = phi₂ (l ++ (baseF (rho₂ L) 0 ++ [(0 : Fin 2)]) ++
                rho₂ (phi₂ r)) := by simp only [List.append_assoc,
              List.singleton_append]
          _ = phi₂ l ++ [finalLetterE, finalLetterB, finalLetterB] ++ phi₂ r := hleft
      have hright' :
          phi₂ (l ++ baseE (rho₂ M) 0 ++ r) =
            phi₂ l ++ [finalLetterB, finalLetterE] ++ phi₂ r := by
        calc
          phi₂ (l ++ baseE (rho₂ M) 0 ++ r) =
              phi₂ (l ++ baseE (rho₂ M) 0 ++
                ((0 : Fin 2) :: rho₂ (phi₂ r))) := by rw [hr]
          _ = phi₂ (l ++ (baseE (rho₂ M) 0 ++ [(0 : Fin 2)]) ++
                rho₂ (phi₂ r)) := by simp only [List.append_assoc,
              List.singleton_append]
          _ = phi₂ l ++ [finalLetterB, finalLetterE] ++ phi₂ r := hright
      rw [hleft', hright']
      exact Relation.ReflTransGen.single
        (stage₂_rule_step L M 3 (phi₂ l) (phi₂ r))
    · have hF :
          baseF (rho₂ L) 1 ++ [(0 : Fin 2)] = rho₂ [finalLetterE, finalLetterA, finalLetterB] := by
        simp [baseF, rho₂, rho₂Letter, finalLetterA, finalLetterB, finalLetterE]
      have hE : baseE (rho₂ M) 1 ++ [(0 : Fin 2)] = rho₂ [finalLetterB, finalLetterE] := by
        simp [baseE, rho₂, rho₂Letter, finalLetterB, finalLetterE]
      subst i
      have hleft := phi₂_context_of_encoded_block l
        (baseF (rho₂ L) 1 ++ [(0 : Fin 2)]) [finalLetterE, finalLetterA, finalLetterB]
        (phi₂ r) hF
      have hright := phi₂_context_of_encoded_block l
        (baseE (rho₂ M) 1 ++ [(0 : Fin 2)]) [finalLetterB, finalLetterE] (phi₂ r) hE
      have hleft' :
          phi₂ (l ++ baseF (rho₂ L) 1 ++ r) =
            phi₂ l ++ [finalLetterE, finalLetterA, finalLetterB] ++ phi₂ r := by
        calc
          phi₂ (l ++ baseF (rho₂ L) 1 ++ r) =
              phi₂ (l ++ baseF (rho₂ L) 1 ++
                ((0 : Fin 2) :: rho₂ (phi₂ r))) := by rw [hr]
          _ = phi₂ (l ++ (baseF (rho₂ L) 1 ++ [(0 : Fin 2)]) ++
                rho₂ (phi₂ r)) := by simp only [List.append_assoc,
              List.singleton_append]
          _ = phi₂ l ++ [finalLetterE, finalLetterA, finalLetterB] ++ phi₂ r := hleft
      have hright' :
          phi₂ (l ++ baseE (rho₂ M) 1 ++ r) =
            phi₂ l ++ [finalLetterB, finalLetterE] ++ phi₂ r := by
        calc
          phi₂ (l ++ baseE (rho₂ M) 1 ++ r) =
              phi₂ (l ++ baseE (rho₂ M) 1 ++
                ((0 : Fin 2) :: rho₂ (phi₂ r))) := by rw [hr]
          _ = phi₂ (l ++ (baseE (rho₂ M) 1 ++ [(0 : Fin 2)]) ++
                rho₂ (phi₂ r)) := by simp only [List.append_assoc,
              List.singleton_append]
          _ = phi₂ l ++ [finalLetterB, finalLetterE] ++ phi₂ r := hright
      rw [hleft', hright']
      exact Relation.ReflTransGen.single
        (stage₂_rule_step L M 1 (phi₂ l) (phi₂ r))
    · subst i
      exact (hi rfl).elim

/-- The long final relation also decodes directly when the right context is
aligned.  Thus the only unformalized case in the last-stage converse is the
long relation together with the residual alternative
`0 :: rho₂ (phi₂ r) = r`. -/
theorem phi₂_long_rule_aligned (L M : List A₂)
    (l r : List (Fin 2)) (hr : rho₂ (phi₂ r) = r) :
    ThueEq (stage₂System L M)
      (phi₂ (l ++ baseF (rho₂ L) 2 ++ r))
      (phi₂ (l ++ baseE (rho₂ M) 2 ++ r)) := by
  have hleft := phi₂_context_of_encoded_block l
    (baseF (rho₂ L) 2) L (phi₂ r) (by simp [baseF])
  have hright := phi₂_context_of_encoded_block l
    (baseE (rho₂ M) 2) M (phi₂ r) (by simp [baseE])
  rw [hr] at hleft hright
  rw [hleft, hright]
  exact Relation.ReflTransGen.single
    (stage₂_rule_step L M 4 (phi₂ l) (phi₂ r))

/-- The exact reachability invariant needed to rule out the bad long-rule
alignment on pages 50--52. -/
def LongRuleAlignedFrom (L M X : List A₂) : Prop :=
  ∀ W, ThueEq (baseSystem (rho₂ L) (rho₂ M)) (rho₂ X) W →
    ∀ l r,
      (W = l ++ rho₂ L ++ r ∨ W = l ++ rho₂ M ++ r) →
      rho₂ (phi₂ r) = r

theorem phi₂_step_of_long_aligned (L M : List A₂)
    {X Y : List (Fin 2)}
    (haligned : ∀ l r,
      (X = l ++ rho₂ L ++ r ∨ X = l ++ rho₂ M ++ r) →
      rho₂ (phi₂ r) = r)
    (h : ThueStep (baseSystem (rho₂ L) (rho₂ M)) X Y) :
    ThueEq (stage₂System L M) (phi₂ X) (phi₂ Y) := by
  rcases h with ⟨l, r, x, y, ⟨i, hxy⟩, hXY⟩
  injection hxy with hx hy
  subst x
  subst y
  rcases fin₃_cases i with hi0 | hi1 | hi2
  · subst i
    rcases hXY with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact phi₂_short_rule L M 0 (by decide) l r
    · exact thueEq_symm (phi₂_short_rule L M 0 (by decide) l r)
  · subst i
    rcases hXY with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact phi₂_short_rule L M 1 (by decide) l r
    · exact thueEq_symm (phi₂_short_rule L M 1 (by decide) l r)
  · subst i
    rcases hXY with ⟨hX, rfl⟩ | ⟨hX, rfl⟩
    · have hr := haligned l r (Or.inl (by simpa [baseF] using hX))
      rw [hX]
      simpa [baseF, baseE] using phi₂_long_rule_aligned L M l r hr
    · have hr := haligned l r (Or.inr (by simpa [baseE] using hX))
      rw [hX]
      simpa [baseF, baseE] using
        thueEq_symm (phi₂_long_rule_aligned L M l r hr)

/-- Conditional converse for the final stage.  The rewriting and decoder
bookkeeping reduce precisely to `LongRuleAlignedFrom`, supplied by the
`e`-count and priority-normal-form invariants of Section 2.4. -/
theorem rho₂_reflect_of_longRuleAligned (L M X Y : List A₂)
    (hsafe : LongRuleAlignedFrom L M X)
    (h : ThueEq (baseSystem (rho₂ L) (rho₂ M)) (rho₂ X) (rho₂ Y)) :
    ThueEq (stage₂System L M) X Y := by
  have aux : ∀ {W : List (Fin 2)},
      ThueEq (baseSystem (rho₂ L) (rho₂ M)) (rho₂ X) W →
      ThueEq (stage₂System L M) X (phi₂ W) := by
    intro W hW
    induction hW with
    | refl =>
        rw [phi₂_rho₂]
        exact Relation.ReflTransGen.refl
    | tail hab hbc ih =>
        exact ih.trans (phi₂_step_of_long_aligned L M
          (fun l r hocc => hsafe _ hab l r hocc) hbc)
  simpa using aux h

theorem rho₂_iff_of_longRuleAligned (L M X : List A₂)
    (hsafe : LongRuleAlignedFrom L M X) (Y : List A₂) :
    ThueEq (stage₂System L M) X Y ↔
      ThueEq (baseSystem (rho₂ L) (rho₂ M)) (rho₂ X) (rho₂ Y) :=
  ⟨rho₂_forward L M,
    rho₂_reflect_of_longRuleAligned L M X Y hsafe⟩

end Matiyasevich1993

end Thue

end Undecidability
