/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import Mathlib.Data.Fintype.Sum
public import LeanPool.DeciSigma1.Logic.Flatten

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Deciding Boolean sentences from disjunctive entailment

A decision procedure for disjunctive entailment between flat constraints decides every Boolean
combination of existential and universal sentences. An existential sentence holds exactly when
some clause of the disjunctive normal form of its body is realizable, and a clause is
realizable exactly when the disjunctive entailment of its queries by its flat constraints
fails. A universal sentence holds exactly when the existential sentence with the negated body
fails, and Boolean connectives are decided componentwise.

By the same reduction, two classes of values over which every disjunctive entailment has the
same truth value give every sentence the same truth value
(`BooleanSentence.holdsIn_iff_of_disjEntailsIn_iff`).

## Main declarations

- `DisjEntailmentDecider`: a decision procedure for disjunctive entailment in a class, uniform
  in the variables and the number of queries.
- `decideBooleanSentence`: the decision procedure for Boolean sentences.
- `BooleanSentence.holdsIn_iff_of_disjEntailsIn_iff`: transfer of truth between two classes.
-/

@[expose] public section


namespace DeciSigma1.Logic

variable {T : Type → Type} {D : Type} {I : Interpretation T D} (F : Flattening I)

/-- A decision procedure for disjunctive entailment between flat constraints over the class
`C`, uniform in the finite type of variables and in the number of queries. -/
abbrev DisjEntailmentDecider (C : D → Prop) :=
  ∀ {W : Type} [Fintype W] [DecidableEq W] {k : ℕ} (Γ : List (F.Lit W)) (q : Fin k → W × W),
    Decidable (F.DisjEntailsIn C Γ q)

/-- A clause is realizable in `C` if some assignment with values in `C` satisfies it. -/
def ConjunctiveClause.Realizable {V : Type} (c : ConjunctiveClause T V) (I : Interpretation T D)
    (C : D → Prop) :
    Prop :=
  ∃ ρ : V → D, (∀ v, C (ρ v)) ∧ c.Holds I ρ

theorem Sigma1.holdsIn_iff_exists_realizable (s : Sigma1 T) (C : D → Prop) :
    s.HoldsIn I C ↔ ∃ c ∈ s.body.dnf, c.Realizable I C := by
  simp only [Sigma1.HoldsIn, QuantifierFreeFormula.holds_iff_dnf, ConjunctiveClause.Realizable]
  aesop

variable [∀ m, DecidableEq (T (Fin m))] {C : D → Prop}

/-- Realizability of a clause, decided through the disjunctive entailment of its queries by
its flat constraints. -/
def decideRealizable (hC : I.TermClosed C) (dec : DisjEntailmentDecider F C) {m : ℕ}
    (c : ConjunctiveClause T (Fin m)) : Decidable (c.Realizable I C) :=
  letI := dec (c.constraints F) (c.queries F)
  decidable_of_iff _ (c.realizable_iff_not_disjEntailsIn F hC).symm

/-- Truth of an existential sentence, decided clause by clause. -/
def decideSigma1 (hC : I.TermClosed C) (dec : DisjEntailmentDecider F C) (s : Sigma1 T) :
    Decidable (s.HoldsIn I C) :=
  letI (c : ConjunctiveClause T (Fin s.variableCount)) := decideRealizable F hC dec c
  decidable_of_iff _ (s.holdsIn_iff_exists_realizable C).symm

/-- The decision procedure for Boolean combinations of existential and universal sentences
over a closed class `C`, given a decision procedure for disjunctive entailment over `C`. -/
def decideBooleanSentence (hC : I.TermClosed C) (dec : DisjEntailmentDecider F C) :
    (φ : BooleanSentence T) → Decidable (φ.HoldsIn I C)
  | .ex s => decideSigma1 F hC dec s
  | .all s =>
    letI := decideSigma1 F hC dec ⟨s.variableCount, .not s.body⟩
    decidable_of_iff _ (BooleanSentence.all_iff_not_ex_not I C s).symm
  | .not φ =>
    letI := decideBooleanSentence hC dec φ
    inferInstanceAs (Decidable (¬ φ.HoldsIn I C))
  | .and φ ψ =>
    letI := decideBooleanSentence hC dec φ
    letI := decideBooleanSentence hC dec ψ
    inferInstanceAs (Decidable (φ.HoldsIn I C ∧ ψ.HoldsIn I C))
  | .or φ ψ =>
    letI := decideBooleanSentence hC dec φ
    letI := decideBooleanSentence hC dec ψ
    inferInstanceAs (Decidable (φ.HoldsIn I C ∨ ψ.HoldsIn I C))

omit [(m : ℕ) → DecidableEq (T (Fin m))] in
/-- If every disjunctive entailment between flat constraints has the same truth value over two
closed classes, then so does every Boolean sentence. -/
theorem BooleanSentence.holdsIn_iff_of_disjEntailsIn_iff {C C' : D → Prop} (hC : I.TermClosed C)
    (hC' : I.TermClosed C')
    (h : ∀ {W : Type} [Fintype W] [DecidableEq W] {k : ℕ} (Γ : List (F.Lit W))
      (q : Fin k → W × W), F.DisjEntailsIn C Γ q ↔ F.DisjEntailsIn C' Γ q)
    (φ : BooleanSentence T) : φ.HoldsIn I C ↔ φ.HoldsIn I C' := by
  classical
  have hs (s : Sigma1 T) : s.HoldsIn I C ↔ s.HoldsIn I C' := by
    rw [s.holdsIn_iff_exists_realizable, s.holdsIn_iff_exists_realizable]
    refine exists_congr fun c => and_congr_right fun _ => ?_
    exact (c.realizable_iff_not_disjEntailsIn F hC).trans
      ((not_congr (h _ _)).trans (c.realizable_iff_not_disjEntailsIn F hC').symm)
  induction φ with
  | ex s => exact hs s
  | all s => simp only [BooleanSentence.all_iff_not_ex_not, hs]
  | not φ ih => exact not_congr ih
  | and φ ψ ihφ ihψ => exact and_congr ihφ ihψ
  | or φ ψ ihφ ihψ => exact or_congr ihφ ihψ

end DeciSigma1.Logic
