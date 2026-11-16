/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Encodings
public import LeanPool.DeciSigma1.Holes.Fresh.ElementaryBound
public import LeanPool.DeciSigma1.Holes.Tail.ClosedForm
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Decidability of the Σ₁ theory of subtype constraints

The main theorem is that the Σ₁ theory of non-structural subtype constraints, the Boolean
combinations of existential (Σ₁) and universal (Π₁) sentences whose atoms are inequalities
`s ≤ t` between type expressions, is decidable for the signature `{⊥, f, ⊤}` with one
constructor `f` of any arity `n` and any variance `c : Fin n → Bool`, over arbitrary, regular
and finite trees (`decideBooleanSentence`). Over arbitrary and regular trees every sentence has
the same truth value (`booleanSentence_regular_iff`); over finite trees it may differ.

The core problem decided by the proof is disjunctive entailment
`Γ ⊨ x₁ ≤ y₁ ∨ … ∨ x_k ≤ y_k` between a conjunction `Γ` of flat constraints and a disjunction
of `k` inequalities between variables, uniformly in `k`. A query family `q : Fin k → V × V`
lists the inequalities `x_i ≤ y_i`; repeated queries are allowed and `k = 0` expresses
unsatisfiability of `Γ`. Its deciders are public as well:
- over `{⊥, f, ⊤}`: `decideDisjEntails`, `decideDisjEntailsReg` and `decideDisjEntailsFin`
  decide `DisjEntails`, `DisjEntailsReg` and `DisjEntailsFin`;
- over `{⊥, f}`: `decideDisjEntailsTopFree`, `decideDisjEntailsTopFreeReg` and
  `decideDisjEntailsTopFreeFin` decide `DisjEntailsTopFree`, `DisjEntailsTopFreeReg` and
  `DisjEntailsTopFreeFin`, and regular and arbitrary entailment agree
  (`disjEntailsTopFreeReg_iff`).

A Σ₁ sentence holds exactly when some clause of a disjunctive normal form of its body, a
conjunction of inequalities and negated inequalities, is realizable; after naming its subterms,
a clause is realizable exactly when a disjunctive entailment fails. A Π₁ sentence is the
negation of a Σ₁ sentence. The classical problems are special cases: a flat constraint `Γ` has a
solution exactly when the Σ₁ sentence `∃x. ⋀Γ` holds, and it entails
`x₁ ≤ y₁ ∨ … ∨ x_k ≤ y_k` exactly when the Π₁ sentence `∀x. ¬⋀Γ ∨ x₁ ≤ y₁ ∨ … ∨ x_k ≤ y_k`
holds, plain entailment being the case `k = 1` (`DeciSigma1.Encodings`).

The deciders are computable definitions with no hypotheses beyond a finite type of variables
with decidable equality. Over `{⊥, f, ⊤}` each runs a satisfiability test and then a bounded
search for a hole of a structural reader compiled from the constraints; the search is complete
by the small-hole theorem `exists_small_hole`, with the computable bound `smallHoleBound`.

The signature `{⊥, f}` with `f` covariant reduces to `{⊥, f, ⊤}`: the same procedures are
applied to a constraint with a guard that excludes `⊤`. Its Σ₁ theory is decided over the same
classes by `decideBooleanSentenceTopFree`, and truth agrees over regular and arbitrary trees
(`booleanSentenceTopFree_regular_iff`).

## Proof map

1. Trees and orders. Trees over `{⊥, f, ⊤}` are `Semantics.Tree`, ordered with variance by
   `Semantics.Tree.Le` (`Semantics/Order`); trees over `{⊥, f}` are sets of constructor
   positions, `Semantics.PrefixSet`, ordered by inclusion, with regular and finite trees
   `Semantics.IsRegularTree` and `Semantics.IsFiniteTree`. The entailments are
   `Full.DisjEntailsIn` (`Full/Basic`) and `Entailment.DisjEntailsIn` (`Entailment/Basic`).
2. Satisfiability and closures. A constraint with variance is translated into a covariant
   constraint on two signed copies of each variable (`Constraints.signed`,
   `Constraints.sat_iff_signed`); it is satisfiable exactly when the translation has no label
   clash (`Satisfiability.sat_iff_signed_not_labelClash`), which gives `Full.Closure.decideSat`.
   Solutions are sets of signed configurations closed under Horn clauses
   (`Full.Closure.sat_iff_isSolution`), and the upper and lower run automata of the translation
   (`Automata.upperRun`, `Automata.lowerRun`) decide membership in least closures
   (`Full.Closure.leastClosure_membership`).
3. From `{⊥, f}` to `{⊥, f, ⊤}`. A set of constructor positions is embedded as the tree with
   these positions labeled `f` and `⊥` below (`Semantics.PrefixSet.toTree`); the embedding
   preserves the order and the constructors, and its image consists of the trees without `⊤`.
   No tree below a tree `u ≤ f(u, …, u)` contains `⊤`
   (`Semantics.Tree.isTopFree_of_le_of_le_node`), so a constraint over `{⊥, f}` entails a
   disjunction exactly when the constraint `Entailment.guarded`, with a fresh variable `u`, the
   inequality `u ≤ f(u, …, u)` and `x ≤ u` for every variable `x`, entails it over `{⊥, f, ⊤}`
   with a covariant constructor (`Entailment.disjEntailsIn_iff_guarded`). A solution over
   `{⊥, f}` is extended by giving `u` the tree all of whose paths are labeled `f`, or over
   finite trees a complete tree deeper than all values (`Semantics.PrefixSet.complete`,
   `Semantics.exists_le_complete`).
4. Witnesses over `{⊥, f, ⊤}`. In the leaf representation of `Full.Closure`, each failed
   inequality has a mode and a path giving a seed in the solution and an exclusion outside it
   (`Full.failures_iff_exists_leaf_witnesses`); for a satisfiable constraint, a family of seeds
   and exclusions is realized by one solution exactly under `Full.Reduction.SeedConsistency`
   (`Full.Reduction.hasCountermodelIn_iff_exists_seedConsistency`), equivalently
   `Full.Reduction.TerminalRootConditions`.
5. Holes over `{⊥, f, ⊤}`. For each mode `Full.Reduction.compile` builds a reader whose holes
   are the families satisfying `Full.Reduction.TerminalRootConditions`
   (`Full.Reduction.hole_iff_terminalRootConditions`), so on a satisfiable constraint the
   entailment fails exactly when the reader of some mode has a hole
   (`Full.Reduction.not_disjEntails_iff_hole`).
6. The small-hole theorem. `Holes.exists_small_hole` composes a rejected-tail bound,
   `Holes.Tail.exists_hole_rejectedTailLength_le` (periodic continuations and compression),
   with a fresh-tuple bound, `Holes.Fresh.exists_freshDominates_totalLength_le` (deletion of
   repeated blocks), applied to the cover of a hole (`Holes.cover`); `Holes.decideHole`
   searches the bounded tuples.
7. Deciders over arbitrary trees. `Full.decideDisjEntails` combines the satisfiability test
   with the bounded search for each of the finitely many modes
   (`Full.decideExistsModeHole`). This is the only reduction to holes:
   `Entailment.decideDisjEntails` applies the same procedure to the guarded constraint.
8. Regular trees. Over `{⊥, f, ⊤}` the hull of the seeds of a countermodel is again a
   countermodel, and each of its leaf cones is a finite union of regular languages; a tree with
   regular leaf cones has finitely many subtrees (`Full.Closure.regular_of_leaf`,
   `Full.Reduction.SeedConsistency.regular_realizes`). Hence a constraint with a countermodel
   has a regular one (`Full.Reduction.hasCountermodelIn_regularTop_iff`), so
   `Full.Reduction.disjEntails_regular_iff`. The embedding preserves and reflects regularity
   (`Semantics.PrefixSet.subtrees_toTree_finite_iff`), so the guarded constraint also
   characterizes entailment over regular trees over `{⊥, f}`
   (`Entailment.disjEntailsIn_regular_iff_guarded`), which gives
   `Entailment.disjEntailsIn_regular_iff`.
9. Finite trees. Finite satisfiability is the absence of label and cycle clashes in the signed
   translation (`Satisfiability.satFin_iff`, `Satisfiability.satFinB_iff`,
   `Full.Models.Signed.decideSatFin`). The observations of a countermodel are bounds by finite
   trees (`Full.Models.Signed.observation_bound`). A bound by a finite tree is compiled into
   one-sided constructor literals on fresh variables (`Constraints.GroundCompiler.compile`); this
   is a ranked extension of the constraint, which creates no cycle clash
   (`Constraints.Ranked.Extension.satFin_iff`). Hence finitely many compatible bounds are
   realized by a finite solution whenever the constraint has one
   (`Full.Models.finiteBoundPinning`, `Full.Models.Signed.boundRealization_finiteTop`), so
   `Full.Reduction.disjEntails_finite_iff` and `Full.decideDisjEntailsFin`. The embedding
   preserves and reflects finiteness (`Semantics.PrefixSet.finiteTop_toTree_iff`), so the
   guarded constraint characterizes entailment over finite trees over `{⊥, f}`
   (`Entailment.disjEntailsIn_finite_iff_guarded`), which gives
   `Entailment.decideDisjEntailsFin`.
10. Boolean sentences. A quantifier-free formula is a disjunction of conjunctive clauses
    (`Logic.QuantifierFreeFormula.holds_iff_dnf`); a clause is realizable exactly when the
    disjunctive entailment of its negated inequalities by the flat constraints naming its
    subterms fails (`Logic.ConjunctiveClause.realizable_iff_not_disjEntailsIn`).
    `Logic.decideBooleanSentence` decides the sentences from any disjunctive-entailment
    decider, instantiated by `Entailment.Logic.decideBooleanSentence` and
    `Full.Logic.decideBooleanSentence`; truth transfers between regular and
    arbitrary trees by `Logic.BooleanSentence.holdsIn_iff_of_disjEntailsIn_iff`.
11. The classical problems. Satisfiability and disjunctive entailment of a flat constraint are
    the sentences `Full.Logic.satisfiabilitySentence` and `Full.Logic.entailmentSentence`
    (`Full.Logic.holdsIn_satisfiabilitySentence_iff`,
    `Full.Logic.holdsIn_entailmentSentence_iff`), and likewise over `{⊥, f}`
    (`Entailment.Logic.holdsIn_satisfiabilitySentence_iff`,
    `Entailment.Logic.holdsIn_entailmentSentence_iff`).

## Main declarations

- `decideBooleanSentence`, `decideBooleanSentenceTopFree`, `booleanSentence_regular_iff`,
  `booleanSentenceTopFree_regular_iff`: Boolean combinations of Σ₁ and Π₁ sentences.
- `DisjEntails`, `DisjEntailsReg`, `DisjEntailsFin`, `decideDisjEntails`,
  `decideDisjEntailsReg`, `decideDisjEntailsFin`: disjunctive entailment over `{⊥, f, ⊤}`.
- `DisjEntailsTopFree`, `DisjEntailsTopFreeReg`, `DisjEntailsTopFreeFin`,
  `decideDisjEntailsTopFree`, `decideDisjEntailsTopFreeReg`, `decideDisjEntailsTopFreeFin`,
  `disjEntailsTopFreeReg_iff`: disjunctive entailment over `{⊥, f}`.
- `decideBooleanSentence_correct` and the other `_correct` theorems: each decision procedure
  returns `true` exactly when its proposition holds.
- `smallHoleBound`, `exists_small_hole`: every structural reader with a hole has a short one.
- `smallHoleBound_le`: a fixed-height elementary bound independent of the alphabet size.
-/

@[expose] public section


namespace DeciSigma1

/-! ## Boolean combinations of Σ₁ and Π₁ sentences -/

section Sentences

variable {n : ℕ}

/-- The Boolean Σ₁/Π₁ theory of `{⊥, f, ⊤}` with variance `c` is decidable over arbitrary,
regular and finite trees. -/
def decideBooleanSentence (c : Fin n → Bool) (C : Full.Logic.TreeClass)
    (φ : Full.Logic.BooleanSentence n) : Decidable (φ.HoldsIn C.Contains c) :=
  Full.Logic.decideBooleanSentence c C φ

/-- `decideBooleanSentence` returns `true` exactly when the sentence holds in the class. -/
theorem decideBooleanSentence_correct (c : Fin n → Bool) (C : Full.Logic.TreeClass)
    (φ : Full.Logic.BooleanSentence n) :
    @decide _ (decideBooleanSentence c C φ) = true ↔ φ.HoldsIn C.Contains c :=
  @decide_eq_true_iff _ (decideBooleanSentence c C φ)

/-- Over `{⊥, f, ⊤}`, a Boolean Σ₁/Π₁ sentence has the same truth value over regular and over
arbitrary trees. -/
theorem booleanSentence_regular_iff (c : Fin n → Bool) (φ : Full.Logic.BooleanSentence n) :
    φ.HoldsIn Full.Models.RegularTop c ↔ φ.HoldsIn (fun _ => True) c :=
  Full.Logic.booleanSentence_regular_iff c φ

/-- The Boolean Σ₁/Π₁ theory of `{⊥, f}` is decidable over arbitrary, regular and finite
trees. -/
def decideBooleanSentenceTopFree (C : Entailment.Logic.TreeClass)
    (φ : Entailment.Logic.BooleanSentence n) : Decidable (φ.HoldsIn C.Contains) :=
  Entailment.Logic.decideBooleanSentence C φ

/-- `decideBooleanSentenceTopFree` returns `true` exactly when the sentence holds in the
class. -/
theorem decideBooleanSentenceTopFree_correct (C : Entailment.Logic.TreeClass)
    (φ : Entailment.Logic.BooleanSentence n) :
    @decide _ (decideBooleanSentenceTopFree C φ) = true ↔ φ.HoldsIn C.Contains :=
  @decide_eq_true_iff _ (decideBooleanSentenceTopFree C φ)

/-- Over `{⊥, f}`, a Boolean Σ₁/Π₁ sentence has the same truth value over regular and over
arbitrary trees. -/
theorem booleanSentenceTopFree_regular_iff (φ : Entailment.Logic.BooleanSentence n) :
    φ.HoldsIn Semantics.IsRegularTree ↔ φ.HoldsIn (fun _ => True) :=
  Entailment.Logic.booleanSentence_regular_iff φ

end Sentences

/-! ## Disjunctive entailment over `{⊥, f, ⊤}` with any variance -/

section Full

variable {n k : ℕ} {V : Type}

/-- Disjunctive entailment over arbitrary trees: every solution of `Γ` satisfies one of the
inequalities `x_i ≤ y_i` with `q i = (x_i, y_i)`, ordered with the variance `c`. -/
abbrev DisjEntails (c : Fin n → Bool) (Γ : List (Constraints.LitT n V)) (q : Fin k → V × V) :
    Prop :=
  Full.DisjEntailsIn (fun _ => True) c Γ q

/-- Disjunctive entailment over regular trees. -/
abbrev DisjEntailsReg (c : Fin n → Bool) (Γ : List (Constraints.LitT n V))
    (q : Fin k → V × V) : Prop :=
  Full.DisjEntailsIn Full.Models.RegularTop c Γ q

/-- Disjunctive entailment over finite trees. -/
abbrev DisjEntailsFin (c : Fin n → Bool) (Γ : List (Constraints.LitT n V))
    (q : Fin k → V × V) : Prop :=
  Full.DisjEntailsIn Full.Models.FiniteTop c Γ q

variable [Fintype V] [DecidableEq V]

/-- Disjunctive entailment over `{⊥, f, ⊤}` with any variance is decidable over arbitrary trees. -/
def decideDisjEntails (c : Fin n → Bool) (Γ : List (Constraints.LitT n V))
    (q : Fin k → V × V) : Decidable (DisjEntails c Γ q) :=
  Full.decideDisjEntails c Γ q

/-- `decideDisjEntails` returns `true` exactly when the entailment holds. -/
theorem decideDisjEntails_correct (c : Fin n → Bool) (Γ : List (Constraints.LitT n V))
    (q : Fin k → V × V) : @decide _ (decideDisjEntails c Γ q) = true ↔ DisjEntails c Γ q :=
  @decide_eq_true_iff _ (decideDisjEntails c Γ q)

/-- Disjunctive entailment over `{⊥, f, ⊤}` with any variance is decidable over regular trees. -/
def decideDisjEntailsReg (c : Fin n → Bool) (Γ : List (Constraints.LitT n V))
    (q : Fin k → V × V) : Decidable (DisjEntailsReg c Γ q) :=
  Full.decideDisjEntailsReg c Γ q

/-- `decideDisjEntailsReg` returns `true` exactly when the entailment holds over regular
trees. -/
theorem decideDisjEntailsReg_correct (c : Fin n → Bool) (Γ : List (Constraints.LitT n V))
    (q : Fin k → V × V) :
    @decide _ (decideDisjEntailsReg c Γ q) = true ↔ DisjEntailsReg c Γ q :=
  @decide_eq_true_iff _ (decideDisjEntailsReg c Γ q)

/-- Disjunctive entailment over `{⊥, f, ⊤}` with any variance is decidable over finite trees. -/
def decideDisjEntailsFin (c : Fin n → Bool) (Γ : List (Constraints.LitT n V))
    (q : Fin k → V × V) : Decidable (DisjEntailsFin c Γ q) :=
  Full.decideDisjEntailsFin c Γ q

/-- `decideDisjEntailsFin` returns `true` exactly when the entailment holds over finite
trees. -/
theorem decideDisjEntailsFin_correct (c : Fin n → Bool) (Γ : List (Constraints.LitT n V))
    (q : Fin k → V × V) :
    @decide _ (decideDisjEntailsFin c Γ q) = true ↔ DisjEntailsFin c Γ q :=
  @decide_eq_true_iff _ (decideDisjEntailsFin c Γ q)

end Full

/-! ## Disjunctive entailment over `{⊥, f}` -/

section TopFree

variable {n : ℕ} {V : Type}

/-- Disjunctive entailment over arbitrary trees over `{⊥, f}`: every solution of `Γ` satisfies
one of the inequalities `x_i ≤ y_i` with `q i = (x_i, y_i)`. -/
abbrev DisjEntailsTopFree {k : ℕ} (Γ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) : Prop :=
  Entailment.DisjEntailsIn (fun _ => True) Γ q

/-- Disjunctive entailment over regular trees over `{⊥, f}`. -/
abbrev DisjEntailsTopFreeReg {k : ℕ} (Γ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) : Prop :=
  Entailment.DisjEntailsIn Semantics.IsRegularTree Γ q

/-- Disjunctive entailment over finite trees over `{⊥, f}`. -/
abbrev DisjEntailsTopFreeFin {k : ℕ} (Γ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) : Prop :=
  Entailment.DisjEntailsIn Semantics.IsFiniteTree Γ q

variable [Fintype V] [DecidableEq V] {k : ℕ}

/-- Disjunctive entailment over `{⊥, f}` is decidable over arbitrary trees. -/
def decideDisjEntailsTopFree (Γ : List (Constraints.TopFree.Lit n V)) (q : Fin k → V × V) :
    Decidable (DisjEntailsTopFree Γ q) :=
  Entailment.decideDisjEntails Γ q

/-- `decideDisjEntailsTopFree` returns `true` exactly when the entailment holds. -/
theorem decideDisjEntailsTopFree_correct (Γ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) :
    @decide _ (decideDisjEntailsTopFree Γ q) = true ↔ DisjEntailsTopFree Γ q :=
  @decide_eq_true_iff _ (decideDisjEntailsTopFree Γ q)

/-- Disjunctive entailment over `{⊥, f}` is decidable over regular trees. -/
def decideDisjEntailsTopFreeReg (Γ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) : Decidable (DisjEntailsTopFreeReg Γ q) :=
  Entailment.decideDisjEntailsReg Γ q

/-- `decideDisjEntailsTopFreeReg` returns `true` exactly when the entailment holds over
regular trees. -/
theorem decideDisjEntailsTopFreeReg_correct (Γ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) :
    @decide _ (decideDisjEntailsTopFreeReg Γ q) = true ↔ DisjEntailsTopFreeReg Γ q :=
  @decide_eq_true_iff _ (decideDisjEntailsTopFreeReg Γ q)

/-- Disjunctive entailment over `{⊥, f}` is decidable over finite trees. -/
def decideDisjEntailsTopFreeFin (Γ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) : Decidable (DisjEntailsTopFreeFin Γ q) :=
  Entailment.decideDisjEntailsFin Γ q

/-- `decideDisjEntailsTopFreeFin` returns `true` exactly when the entailment holds over finite
trees. -/
theorem decideDisjEntailsTopFreeFin_correct (Γ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) :
    @decide _ (decideDisjEntailsTopFreeFin Γ q) = true ↔ DisjEntailsTopFreeFin Γ q :=
  @decide_eq_true_iff _ (decideDisjEntailsTopFreeFin Γ q)

omit [DecidableEq V] in
omit [Fintype V] in
/-- Over `{⊥, f}`, regular and arbitrary disjunctive entailment agree. -/
theorem disjEntailsTopFreeReg_iff [Finite V] (Γ : List (Constraints.TopFree.Lit n V))
    (q : Fin k → V × V) : DisjEntailsTopFreeReg Γ q ↔ DisjEntailsTopFree Γ q := by
  classical
  let := Fintype.ofFinite V
  exact Entailment.disjEntailsIn_regular_iff Γ q

end TopFree

/-! ## Small holes -/

/-- The small-hole bound for a reader over an alphabet of size `σ` with `k` starts and `N`
states. -/
def smallHoleBound (σ k N : ℕ) : ℕ := Holes.smallHoleBound σ k N

open Arithmetic in
/-- The small-hole bound is at most four iterated exponentials, independently of the alphabet
size. Its innermost argument is polynomial in `N` for each fixed `k`. -/
theorem smallHoleBound_le (σ k N : ℕ) :
    smallHoleBound σ k N ≤ (fun x : ℕ => 2 ^ x)^[4]
      ((k + N + 20) ^ (2 * k + 6)) := by
  let p := (k + N + 20) ^ (2 * k + 5)
  let L := Holes.Tail.tailLengthBound σ k N
  have ht : L ≤ exp2^[2] p := Holes.Tail.tailLengthBound_le_double_exp2 σ k N
  have h₁ : N + L + 1 ≤ exp2^[2] (N + p + 2) := by
    calc
      N + L + 1 ≤ exp2^[2] (N + p + 1) + exp2^[2] 0 :=
        Nat.add_le_add ((Nat.add_le_add (le_iterate_exp2 2 N) ht).trans
          (iterate_exp2_add_le 2 N p (by omega))) (by decide)
      _ ≤ exp2^[2] (N + p + 2) := by
        simpa using iterate_exp2_add_le 2 (N + p + 1) 0 (by omega)
  have h₂ : k * (N + L + 1) ≤ exp2^[2] (k + (N + p + 2) + 1) :=
    (Nat.mul_le_mul (le_iterate_exp2 2 k) h₁).trans
      (iterate_exp2_mul_le 2 k (N + p + 2) (by omega))
  have h₃ : k + (k * (N + L + 1) + 1) + 16 ≤
      exp2^[2] (2 * k + N + p + 21) := by
    calc
      _ = (k + k * (N + L + 1)) + 17 := by omega
      _ ≤ exp2^[2] (k + (k + (N + p + 2) + 1) + 1) + exp2^[2] 16 :=
        Nat.add_le_add ((Nat.add_le_add (le_iterate_exp2 2 k) h₂).trans
          (iterate_exp2_add_le 2 k _ (by omega)))
          ((succ_le_exp2 16).trans (le_exp2 _))
      _ ≤ exp2^[2] (2 * k + N + p + 21) := by
        convert iterate_exp2_add_le 2 (k + (k + (N + p + 2) + 1) + 1) 16 (by omega)
          using 1
        congr 1
        omega
  have harg : 2 * k + N + p + 25 ≤ (k + N + 20) ^ (2 * k + 6) := by
    let R := k + N + 20
    have hR : 20 ≤ R := by dsimp [R]; omega
    have hp : R ≤ p := by
      have h : R ^ 1 ≤ R ^ (2 * k + 5) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      simpa only [pow_one] using h
    have hlin : 2 * k + N + 25 ≤ 2 * R := by dsimp [R]; omega
    calc
      _ ≤ 3 * p := by omega
      _ ≤ R * p := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by
        dsimp [R, p]
        rw [show 2 * k + 6 = (2 * k + 5) + 1 by omega, pow_succ]
        ring
  calc
    smallHoleBound σ k N = Holes.Fresh.freshTupleBound k (k * (N + L + 1) + 1) := rfl
    _ ≤ exp2 (exp2 ((k + (k * (N + L + 1) + 1) + 16) ^ 4)) :=
      Holes.Fresh.freshTupleBound_le_double_exp2 _ _
    _ ≤ exp2 (exp2 ((exp2^[2] (2 * k + N + p + 21)) ^ 4)) :=
      exp2_mono (exp2_mono (Nat.pow_le_pow_left h₃ 4))
    _ ≤ exp2^[4] (2 * k + N + p + 25) :=
      exp2_mono (exp2_mono (double_exp2_pow_le _ 4))
    _ ≤ _ := iterate_exp2_mono 4 harg

/-- Every structural reader with `N` states and `k` starts over a finite alphabet that has a
hole has one of total length at most `smallHoleBound σ k N`. -/
theorem exists_small_hole {α S : Type} [Fintype α] [DecidableEq α] [Fintype S]
    [DecidableEq S] {k : ℕ} (M : Readers.StructuralReader α S k) (h : ∃ W, M.IsHole W) :
    ∃ W, M.IsHole W ∧
      Readers.totalLength W ≤ smallHoleBound (Fintype.card α) k (Fintype.card S) :=
  Holes.exists_small_hole M h

end DeciSigma1
