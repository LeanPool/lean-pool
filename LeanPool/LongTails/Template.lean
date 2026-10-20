/-
Copyright (c) 2026 LongTails contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Tyurin, QuocViet Pham, Valentin Khrulkov, Ivan Oseledets
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Prod

/-!
Adapted from k3nfalt/longtails, commit 269cbc764dd36851fd0b64f2f950f329ee127de4.
Modified for Lean Pool: module visibility, namespace isolation, and current Mathlib.
-/

@[expose] public section

open MeasureTheory

namespace LongTails.OracleTemplate

universe uP uD uI uQ uR uO

/-- An oracle algorithm with an internal state and its own random seed. -/
structure Algorithm (Query : Type uQ) (Reply : Type uR) (Output : Type uO)
    (numOracles : ℕ := 1) where
  /-- Random seed used to initialize the algorithm. -/
  Seed : Type := Unit
  /-- Measurable structure on algorithm seeds. -/
  [seedSpace : MeasurableSpace Seed]
  /-- Probability law of the algorithm seed. -/
  law : ProbabilityMeasure Seed := by exact ⟨MeasureTheory.Measure.dirac (), inferInstance⟩
  /-- Internal state retained between oracle calls. -/
  State : Type (max uQ uR uO)
  /-- Initial state chosen from the algorithm seed. -/
  initial : Seed → State
  /-- Oracle index and query selected by the current state. -/
  query : State → Fin numOracles × Query
  /-- State after receiving the reply to the selected query. -/
  update : State → Reply → State
  /-- Point reported when the query budget is exhausted. -/
  output : State → Output

attribute [instance] Algorithm.seedSpace

/-- A sequence of oracle replies, with an arbitrary joint law for the query samples. -/
structure Oracle (Query : Type uQ) (Reply : Type uR) (numOracles : ℕ := 1) where
  /-- Sample type at each query index. -/
  Seed : ℕ → Type := fun _ => Unit
  /-- Measurable structure on each query sample. -/
  [seedSpace : ∀ k, MeasurableSpace (Seed k)]
  /-- Joint probability law of all samples; independence is not assumed. -/
  law : ProbabilityMeasure ((k : ℕ) → Seed k) := by
    exact ⟨MeasureTheory.Measure.dirac (fun _ => ()), inferInstance⟩
  /-- Reply at a query index, oracle index, query and sample. -/
  answer : (k : ℕ) → (Fin numOracles × Query) → Seed k → Reply

attribute [instance] Oracle.seedSpace

/-- Run at most the supplied fuel, decrementing the budget of each queried oracle. -/
def executeLoop
    {Query : Type uQ} {Reply : Type uR} {Output : Type uO}
    {numOracles : ℕ}
    (oracle : ℕ → (Fin numOracles × Query) → Reply)
    (A : Algorithm Query Reply Output numOracles) :
    Nat → Nat → (Fin numOracles → ℕ) → A.State → Output
  | 0, _, _, state => A.output state
  | k + 1, call, remaining, state =>
      let query := A.query state
      if remaining query.1 = 0 then A.output state
      else
        let reply := oracle call query
        let remaining := Function.update remaining query.1 (remaining query.1 - 1)
        executeLoop oracle A k (call + 1) remaining (A.update state reply)

/-- Execute an algorithm using explicit per-oracle call budgets and fixed random seeds. -/
def execute
    {Query : Type uQ} {Reply : Type uR} {Output : Type uO}
    {numOracles : ℕ}
    (oracle : Oracle Query Reply numOracles) (A : Algorithm Query Reply Output numOracles)
    (budget : Fin numOracles → ℕ) (seed : A.Seed := by exact ())
    (oracleSeed : (k : ℕ) → oracle.Seed k := by exact fun _ => ()) : Output :=
  executeLoop (fun k query => oracle.answer k query (oracleSeed k))
    A (∑ i, budget i) 0 budget (A.initial seed)

/-- The public information, admissible instances and success criterion of an oracle problem. -/
structure Setup where
  /-- Number of available oracle interfaces. -/
  numOracles : ℕ := 1
  /-- Parameters of a guarantee, including hidden accuracy targets. -/
  Params : Type uP
  /-- Information available to the algorithm. -/
  Public : Type uD
  /-- Mathematical instance hidden behind the oracle. -/
  Instance : Public → Type uI
  /-- Type of query accepted by each oracle. -/
  Query : Public → Type uQ
  /-- Type of oracle reply. -/
  Reply : Public → Type uR
  /-- Type of result returned by the algorithm. -/
  Output : Public → Type uO
  /-- Public information extracted from guarantee parameters. -/
  publicInput : Params → Public
  /-- Admissible numerical regimes for the guarantee parameters. -/
  valid : Params → Prop
  /-- Mathematical assumptions on the instance and its oracle. -/
  admissible : (p : Params) → Instance (publicInput p) →
    Oracle (Query (publicInput p)) (Reply (publicInput p)) numOracles → Prop
  /-- Accuracy criterion evaluated under the supplied law of seeds. -/
  successful : {Ω : Type} → [MeasurableSpace Ω] →
    (p : Params) → Instance (publicInput p) →
    (Ω → Output (publicInput p)) → ProbabilityMeasure Ω → Prop
  /-- Optional restrictions on the algorithm family. -/
  allowedAlgorithm : (p : Public) → Algorithm (Query p) (Reply p) (Output p) numOracles → Prop :=
    fun _ _ => True

/-- One algorithm family meets the setup criterion within the stated query budgets. -/
def Convergence (S : Setup)
    (budget : S.Params → Fin S.numOracles → ℕ) : Prop :=
  ∃ makeAlgorithm : (p : S.Public) → Algorithm (S.Query p) (S.Reply p) (S.Output p) S.numOracles,
    (∀ p, S.valid p →
      ∀ (I : S.Instance (S.publicInput p))
        (oracle : Oracle (S.Query (S.publicInput p)) (S.Reply (S.publicInput p)) S.numOracles),
        S.admissible p I oracle →
          let A := makeAlgorithm (S.publicInput p)
          let result := fun seed : A.Seed × ((k : ℕ) → oracle.Seed k) =>
            execute oracle A (budget p) seed.1 seed.2
          S.successful p I result
            ⟨(A.law : Measure _).prod (oracle.law : Measure _), inferInstance⟩) ∧
    ∀ p, S.valid p → S.allowedAlgorithm (S.publicInput p) (makeAlgorithm (S.publicInput p))

end LongTails.OracleTemplate
