/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import Mathlib.Data.Fin.VecNotation
public import LeanPool.DeciSigma1.Full.Reduction.Compile

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Examples of readers, holes and fresh domination

The small-hole bound `exists_small_hole` concerns structural readers, and its proof goes through
fresh dominators and minimal fresh tuples. The examples below show that each of these notions
has instances, all checked by the kernel on small tables.

## Main declarations

- `mixedReader`, `mixedReader_hole`, `mixedReader_hasMixedMortality`, `mixedReader_not_hole`: a
  structural reader with four states and two starts, a hole of it with one immortal and one
  mortal coordinate, and a tuple that is not a hole.
- `freshTable_has_shorter_fresh_dominator`: a one-start table where the word `01` has the
  strictly shorter fresh dominator `1`.
- `pairTable_isMinimalFresh`: a minimal fresh pair with an empty coordinate.
- `crossReader`, `crossReader_not_hole`, `crossReader_hole`, `cross_not_entails`: the reader
  compiled from a disjunctive entailment with two queries, an admitted pair on the channel
  between its two coordinates, and a hole, which refutes the entailment.
-/

@[expose] public section


namespace DeciSigma1.Examples

open DeciSigma1.Readers DeciSigma1.Constraints DeciSigma1.Full DeciSigma1.Full.Reduction

/-- Transitions over the alphabet `{0, 1}`: dead state `0`; start `1` with `1 -0→ 2` and
`1 -1→ 3`; rejected immortal state `2` with the loop `2 -0→ 2`; rejected mortal state `3`. -/
def mixedStep : Fin 4 → Fin 2 → Fin 4 := ![![0, 0], ![2, 3], ![2, 0], ![0, 0]]

/-- A structural reader with two starts in state `1`, rejected states `{2, 3}` and the single
admitted pair `(2, 1)`. -/
def mixedReader : StructuralReader (Fin 2) (Fin 4) 2 where
  step := mixedStep
  start := ![1, 1]
  dead := 0
  rejected := fun q => decide (q = 2 ∨ q = 3)
  admitted := fun p q => decide (p = 2 ∧ q = 1)
  step_dead := by decide
  rejected_dead := by decide
  rejected_step := by decide
  not_admitted_step_of_rejected := by decide

/-- The immortal word `000` and the mortal word `1`. -/
def mixedWords : Fin 2 → List (Fin 2) := ![[0, 0, 0], [1]]

/-- The tuple `(000, 1)` is a hole. -/
theorem mixedReader_hole : mixedReader.IsHole mixedWords := by decide +kernel

/-- The hole has mixed mortality: an immortal and a mortal coordinate. -/
theorem mixedReader_hasMixedMortality : mixedReader.HasMixedMortality mixedWords := by
  decide +kernel

/-- The admitted pair `(2, 1)` lies on a channel: the target word `00` is a prefix of the host word
`000` after its first letter, where the host is in state `2` and the target in state `1`. -/
theorem mixedReader_not_hole : ¬ mixedReader.IsHole ![[0, 0, 0], [0, 0]] := by decide +kernel

/-- Transitions over `{0, 1}`: `0 -0→ 0`, `0 -1→ 1`, and every other edge to `2`. -/
def freshStep : Fin 3 → Fin 2 → Fin 3 := ![![0, 1], ![2, 2], ![2, 2]]

/-- One start in state `0`. -/
def freshTable : Table (Fin 2) (Fin 3) 1 := ⟨freshStep, ![0]⟩

/-- The word `01` has the strictly shorter fresh dominator `1`. -/
theorem freshTable_has_shorter_fresh_dominator : FreshDominates freshTable ![[1]] ![[0, 1]] ∧
    totalLength ![[1]] < totalLength (![[0, 1]] : Fin 1 → List (Fin 2)) := by decide +kernel

/-- Two starts in state `0`. -/
def pairTable : Table (Fin 2) (Fin 3) 2 := ⟨freshStep, ![0, 0]⟩

/-- A minimal fresh pair with an empty coordinate. -/
theorem pairTable_isMinimalFresh : IsMinimalFresh pairTable ![[1], []] := by decide +kernel

/-! ## The reader of a disjunctive entailment

The decision procedure compiles a constraint, its queries and a mode into a structural reader.
When the constraint is satisfiable, the entailment fails exactly when the reader of some mode has
a hole (`Full.Reduction.not_disjEntails_iff_hole`). In the mode used below, a word of coordinate
`i` is a path on which `y_i` is `⊥` and `x_i` is not. -/

/-- The constraint `x₀ ≤ y₁` over binary trees, on the variables `x₀ = 0`, `y₀ = 1`, `x₁ = 2` and
`y₁ = 3`. -/
def crossSystem : List (LitT 2 (Fin 4)) := [.le 0 3]

/-- The queries `x₀ ≤ y₀` and `x₁ ≤ y₁`. -/
def crossQueries : Fin 2 → Fin 4 × Fin 4 := ![(0, 1), (2, 3)]

/-- The reader of `crossSystem` and `crossQueries` with a covariant constructor, in the mode that
refutes each query at a path where its right side is `⊥`. -/
def crossReader : StructuralReader (Fin 2) (State (Fin 4)) 2 :=
  compile (fun _ => false) crossSystem crossQueries (fun _ => true)

/-- The pair of empty words is not a hole: since `x₀ ≤ y₁`, the channel from the first coordinate
to the second carries an admitted pair at the empty word. -/
theorem crossReader_not_hole : ¬ crossReader.IsHole ![[], []] := by decide +kernel

/-- The pair of words `([], [0])` is a hole. -/
theorem crossReader_hole : crossReader.IsHole ![[], [0]] := by decide +kernel

/-- Hence `x₀ ≤ y₁` does not entail `x₀ ≤ y₀ ∨ x₁ ≤ y₁`. -/
theorem cross_not_entails :
    ¬ DisjEntailsIn (fun _ => True) (fun _ => false) crossSystem crossQueries :=
  (not_disjEntails_iff_hole
      ⟨fun _ => Semantics.Tree.bot, by simp [Covariant.Sat, Covariant.Holds, crossSystem]⟩).mpr
    ⟨_, _, crossReader_hole⟩

end DeciSigma1.Examples
