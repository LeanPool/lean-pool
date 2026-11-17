/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Entailment.Logic
public import LeanPool.DeciSigma1.Full.Logic

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Satisfiability and entailment as Boolean sentences

The classical problems on subtype constraints are sentences of the decided fragment. A flat
constraint `Γ` over the variables `Fin m` becomes the conjunction `⋀Γ` of quantifier-free
formulas, each literal an inequality between terms (`x ≤ y`, `f(a) ≤ x`, `x ≤ f(a)`) or an
equation (`x = ⊥`, `x = ⊤`, a conjunction of two inequalities). Then

- `Γ` has a solution in a class `C` exactly when the Σ₁ sentence `∃x. ⋀Γ` holds in `C`;
- `Γ ⊨ x₁ ≤ y₁ ∨ … ∨ x_k ≤ y_k` in `C` exactly when the Π₁ sentence
  `∀x. ¬⋀Γ ∨ x₁ ≤ y₁ ∨ … ∨ x_k ≤ y_k` holds in `C`. Plain entailment is the case `k = 1`, and
  for `k = 0` the sentence states that `Γ` has no solution in `C`.

This holds in both signatures and for every class of trees. Hence the sentence deciders
`Full.Logic.decideBooleanSentence` and `Entailment.Logic.decideBooleanSentence`, public as
`decideBooleanSentence` and `decideBooleanSentenceTopFree`, decide satisfiability and
disjunctive entailment over arbitrary, regular and finite trees. The generic sentences
`Logic.satisfiabilitySentence` and `Logic.entailmentSentence` take any quantifier-free formulas,
so constraints between arbitrary type expressions, not only flat ones, are decided in the same
way.

## Main declarations

- `Logic.QuantifierFreeFormula.conj`, `Logic.QuantifierFreeFormula.disj`: finite conjunctions
  and disjunctions.
- `Logic.satisfiabilitySentence`, `Logic.entailmentSentence`,
  `Logic.holdsIn_satisfiabilitySentence_iff`, `Logic.holdsIn_entailmentSentence_iff`: the
  sentences for any formulas.
- `Full.Logic.satisfiabilitySentence`, `Full.Logic.entailmentSentence`,
  `Full.Logic.holdsIn_satisfiabilitySentence_iff`, `Full.Logic.holdsIn_entailmentSentence_iff`:
  flat constraints over `{⊥, f, ⊤}` with any variance.
- `Entailment.Logic.satisfiabilitySentence`, `Entailment.Logic.entailmentSentence`,
  `Entailment.Logic.holdsIn_satisfiabilitySentence_iff`,
  `Entailment.Logic.holdsIn_entailmentSentence_iff`: flat constraints over `{⊥, f}`.
-/

@[expose] public section


namespace DeciSigma1.Logic

variable {T : Type → Type} {D V : Type} (I : Interpretation T D)

namespace QuantifierFreeFormula

/-- The conjunction of a list of formulas; the empty conjunction is true. -/
def conj : List (QuantifierFreeFormula T V) → QuantifierFreeFormula T V
  | [] => .tt
  | φ :: φs => .and φ (conj φs)

/-- The disjunction of a list of formulas; the empty disjunction is false. -/
def disj : List (QuantifierFreeFormula T V) → QuantifierFreeFormula T V
  | [] => .ff
  | φ :: φs => .or φ (disj φs)

theorem holds_conj (ρ : V → D) (φs : List (QuantifierFreeFormula T V)) :
    (conj φs).Holds I ρ ↔ ∀ φ ∈ φs, φ.Holds I ρ := by
  induction φs with
  | nil => simp [conj, Holds]
  | cons φ φs ih => simp [conj, Holds, ih]

theorem holds_disj (ρ : V → D) (φs : List (QuantifierFreeFormula T V)) :
    (disj φs).Holds I ρ ↔ ∃ φ ∈ φs, φ.Holds I ρ := by
  induction φs with
  | nil => simp [disj, Holds]
  | cons φ φs ih => simp [disj, Holds, ih]

end QuantifierFreeFormula

variable {m : ℕ}

/-- The Σ₁ sentence `∃ x₀ … x_{m-1}, φ₁ ∧ … ∧ φ_r`, which states that the formulas `φs` have a
common solution. -/
def satisfiabilitySentence (φs : List (QuantifierFreeFormula T (Fin m))) : BooleanSentence T :=
  .ex ⟨m, .conj φs⟩

/-- The Π₁ sentence `∀ x₀ … x_{m-1}, ¬(φ₁ ∧ … ∧ φ_r) ∨ ψ₁ ∨ … ∨ ψ_k`, which states that every
common solution of the formulas `φs` satisfies one of the formulas `ψs`. -/
def entailmentSentence (φs ψs : List (QuantifierFreeFormula T (Fin m))) : BooleanSentence T :=
  .all ⟨m, .or (.not (.conj φs)) (.disj ψs)⟩

/-- The satisfiability sentence holds in `C` exactly when some assignment with values in `C`
satisfies all the formulas. -/
theorem holdsIn_satisfiabilitySentence_iff (C : D → Prop)
    (φs : List (QuantifierFreeFormula T (Fin m))) :
    (satisfiabilitySentence φs).HoldsIn I C ↔
      ∃ ρ : Fin m → D, (∀ v, C (ρ v)) ∧ ∀ φ ∈ φs, φ.Holds I ρ := by
  simp only [satisfiabilitySentence, BooleanSentence.HoldsIn, Sigma1.HoldsIn,
    QuantifierFreeFormula.holds_conj]

/-- The entailment sentence holds in `C` exactly when every assignment with values in `C` that
satisfies the formulas `φs` satisfies one of the formulas `ψs`. -/
theorem holdsIn_entailmentSentence_iff (C : D → Prop)
    (φs ψs : List (QuantifierFreeFormula T (Fin m))) :
    (entailmentSentence φs ψs).HoldsIn I C ↔
      ∀ ρ : Fin m → D, (∀ v, C (ρ v)) → (∀ φ ∈ φs, φ.Holds I ρ) → ∃ ψ ∈ ψs, ψ.Holds I ρ := by
  simp only [entailmentSentence, BooleanSentence.HoldsIn, QuantifierFreeFormula.Holds,
    QuantifierFreeFormula.holds_conj, QuantifierFreeFormula.holds_disj, ← imp_iff_not_or]

end DeciSigma1.Logic

namespace DeciSigma1.Full.Logic

open DeciSigma1.Constraints DeciSigma1.Logic DeciSigma1.Semantics

variable {n k m : ℕ} {V : Type} (c : Fin n → Bool)

/-- A flat literal over `{⊥, f, ⊤}` as a quantifier-free formula: an inequality between terms,
or for `x = ⊥` and `x = ⊤` an equation. -/
def literal : LitT n V → QuantifierFreeFormula (Term n) V
  | .le x y => .le (.var x) (.var y)
  | .fLe a x => .le (.node fun i => .var (a i)) (.var x)
  | .leF x a => .le (.var x) (.node fun i => .var (a i))
  | .eqBot x => .eq (.var x) .bot
  | .eqTop x => .eq (.var x) .top

theorem holds_literal (ρ : V → Tree n) (l : LitT n V) :
    (literal l).Holds (interpretation c) ρ ↔ HoldsT c ρ l := by
  cases l with
  | eqBot x => exact holds_eq_iff c ρ _ _
  | eqTop x => exact holds_eq_iff c ρ _ _
  | _ => rfl

/-- The queries `x_i ≤ y_i` as formulas. -/
def queryFormulas (q : Fin k → V × V) : List (QuantifierFreeFormula (Term n) V) :=
  List.ofFn fun i => .le (.var (q i).1) (.var (q i).2)

/-- The Σ₁ sentence `∃x. ⋀Γ` over `{⊥, f, ⊤}`. -/
def satisfiabilitySentence (Γ : List (LitT n (Fin m))) : BooleanSentence n :=
  DeciSigma1.Logic.satisfiabilitySentence (Γ.map literal)

/-- The Π₁ sentence `∀x. ¬⋀Γ ∨ x₁ ≤ y₁ ∨ … ∨ x_k ≤ y_k` over `{⊥, f, ⊤}`. -/
def entailmentSentence (Γ : List (LitT n (Fin m))) (q : Fin k → Fin m × Fin m) :
    BooleanSentence n :=
  DeciSigma1.Logic.entailmentSentence (Γ.map literal) (queryFormulas q)

/-- A flat constraint over `{⊥, f, ⊤}` has a solution in the class `C` exactly when its
satisfiability sentence holds in `C`. -/
theorem holdsIn_satisfiabilitySentence_iff (C : Tree n → Prop) (Γ : List (LitT n (Fin m))) :
    (satisfiabilitySentence Γ).HoldsIn C c ↔ Models.SatisfiableIn C c Γ := by
  simp only [BooleanSentence.HoldsIn, satisfiabilitySentence,
    DeciSigma1.Logic.holdsIn_satisfiabilitySentence_iff, List.forall_mem_map, holds_literal]
  rfl

/-- A flat constraint over `{⊥, f, ⊤}` entails `x₁ ≤ y₁ ∨ … ∨ x_k ≤ y_k` in the class `C`
exactly when its entailment sentence holds in `C`. -/
theorem holdsIn_entailmentSentence_iff (C : Tree n → Prop) (Γ : List (LitT n (Fin m)))
    (q : Fin k → Fin m × Fin m) :
    (entailmentSentence Γ q).HoldsIn C c ↔ DisjEntailsIn C c Γ q := by
  simp only [BooleanSentence.HoldsIn, entailmentSentence,
    DeciSigma1.Logic.holdsIn_entailmentSentence_iff, List.forall_mem_map, holds_literal,
    queryFormulas, List.mem_ofFn, exists_exists_eq_and]
  rfl

end DeciSigma1.Full.Logic

namespace DeciSigma1.Entailment.Logic

open DeciSigma1.Constraints.TopFree DeciSigma1.Logic DeciSigma1.Semantics

variable {n k m : ℕ} {V : Type}

/-- A flat literal over `{⊥, f}` as a quantifier-free formula: an inequality between terms, or
for `x = ⊥` an equation. -/
def literal : Lit n V → QuantifierFreeFormula (BFTerm n) V
  | .le x y => .le (.var x) (.var y)
  | .fLe a x => .le (.node fun i => .var (a i)) (.var x)
  | .leF x a => .le (.var x) (.node fun i => .var (a i))
  | .eqBot x => .eq (.var x) .bot

theorem holds_literal (ρ : V → PrefixSet n) (l : Lit n V) :
    (literal l).Holds (interpretation n) ρ ↔ l.Holds ρ := by
  cases l with
  | eqBot x => exact ⟨fun h => le_antisymm h.1 h.2, fun h => ⟨h.le, h.ge⟩⟩
  | _ => rfl

/-- The queries `x_i ≤ y_i` as formulas. -/
def queryFormulas (q : Fin k → V × V) : List (QuantifierFreeFormula (BFTerm n) V) :=
  List.ofFn fun i => .le (.var (q i).1) (.var (q i).2)

/-- The Σ₁ sentence `∃x. ⋀Γ` over `{⊥, f}`. -/
def satisfiabilitySentence (Γ : List (Lit n (Fin m))) : BooleanSentence n :=
  DeciSigma1.Logic.satisfiabilitySentence (Γ.map literal)

/-- The Π₁ sentence `∀x. ¬⋀Γ ∨ x₁ ≤ y₁ ∨ … ∨ x_k ≤ y_k` over `{⊥, f}`. -/
def entailmentSentence (Γ : List (Lit n (Fin m))) (q : Fin k → Fin m × Fin m) :
    BooleanSentence n :=
  DeciSigma1.Logic.entailmentSentence (Γ.map literal) (queryFormulas q)

/-- A flat constraint over `{⊥, f}` has a solution in the class `C` exactly when its
satisfiability sentence holds in `C`. -/
theorem holdsIn_satisfiabilitySentence_iff (C : PrefixSet n → Prop) (Γ : List (Lit n (Fin m))) :
    (satisfiabilitySentence Γ).HoldsIn C ↔ ∃ ρ : Fin m → PrefixSet n, (∀ v, C (ρ v)) ∧ Sat ρ Γ := by
  simp only [BooleanSentence.HoldsIn, satisfiabilitySentence,
    DeciSigma1.Logic.holdsIn_satisfiabilitySentence_iff, List.forall_mem_map, holds_literal]
  rfl

/-- A flat constraint over `{⊥, f}` entails `x₁ ≤ y₁ ∨ … ∨ x_k ≤ y_k` in the class `C` exactly
when its entailment sentence holds in `C`. -/
theorem holdsIn_entailmentSentence_iff (C : PrefixSet n → Prop) (Γ : List (Lit n (Fin m)))
    (q : Fin k → Fin m × Fin m) :
    (entailmentSentence Γ q).HoldsIn C ↔ DisjEntailsIn C Γ q := by
  simp only [BooleanSentence.HoldsIn, entailmentSentence,
    DeciSigma1.Logic.holdsIn_entailmentSentence_iff, List.forall_mem_map, holds_literal,
    queryFormulas, List.mem_ofFn, exists_exists_eq_and]
  rfl

end DeciSigma1.Entailment.Logic
