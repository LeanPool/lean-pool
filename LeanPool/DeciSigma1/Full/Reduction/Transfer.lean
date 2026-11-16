/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Full.Reduction.Realization
public import LeanPool.DeciSigma1.Full.Basic
public import LeanPool.DeciSigma1.Full.Models.Signed.Transfer
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Pow

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Regular and finite countermodels over `{⊥, f, ⊤}`

The hull of the seeds of a countermodel is a countermodel with regular leaf cones, hence a regular
countermodel. Thus disjunctive entailment agrees over regular and arbitrary trees. Over finite
trees, the observations of a countermodel are ground bounds, which are realized by a finite
solution whenever the constraint has one.

## Main declarations

- `Reduction.countermodelObservations`: the observations witnessing a countermodel.
- `Reduction.disjEntails_regular_iff`: regular and arbitrary disjunctive entailment agree.
- `Reduction.disjEntails_finite_iff`: entailment over finite trees holds exactly when there is no
  finite solution or entailment holds over arbitrary trees.
-/

@[expose] public section


namespace DeciSigma1.Full.Reduction
open DeciSigma1.Semantics
open DeciSigma1.Full.Models DeciSigma1.Constraints
variable {n k : Nat} {V : Type}
variable {c : Fin n → Bool} {Γ : List (LitT n V)} {q : Fin k → V × V}

theorem realize_observations {C : Semantics.Tree n → Prop} (h : Signed.BoundRealization C c Γ)
    (O : List (Signed.Observation n V))
    (hs : ∃ ρ, SatT c ρ Γ ∧ ∀ o ∈ O, o.Holds c ρ) :
    ∃ τ, (∀ v, C (τ v)) ∧ SatT c τ Γ ∧ ∀ o ∈ O, o.Holds c τ := by
  obtain ⟨ρ, hρ, ho⟩ := hs
  obtain ⟨τ, hc, ht, hb⟩ := h (O.map (Signed.Observation.bound c))
    ⟨ρ, hρ, by simpa only [List.forall_mem_map, Signed.observation_bound] using ho⟩
  exact ⟨τ, hc, ht, by
    simpa only [List.forall_mem_map, Signed.observation_bound] using hb⟩

/-- The seed and exclusion observations of the failures selected by the modes `m` and paths `W`. -/
def countermodelObservations (q : Fin k → V × V) (m : Fin k → Bool)
    (W : Fin k → List (Fin n)) : List (Signed.Observation n V) :=
  (List.finRange k).flatMap fun i =>
    [(seed (q i) (m i) (W i), true), (exclusion (q i) (m i) (W i), false)]

theorem countermodelObservations_holds (ρ : V → Semantics.Tree n) (m : Fin k → Bool)
    (W : Fin k → List (Fin n)) :
    (∀ o ∈ countermodelObservations q m W, o.Holds c ρ) ↔
      ∀ i, seed (q i) (m i) (W i) ∈ Closure.configSet c ρ ∧
        exclusion (q i) (m i) (W i) ∉ Closure.configSet c ρ := by
  simp only [countermodelObservations, List.forall_mem_flatMap]
  simp [Signed.Observation.Holds]

theorem hasCountermodelIn_of_boundRealization {C : Semantics.Tree n → Prop}
    (h : Signed.BoundRealization C c Γ) (hc : HasCountermodelIn (fun _ => True) c Γ q) :
    HasCountermodelIn C c Γ q := by
  obtain ⟨ρ, _, hs, hf⟩ := hc
  obtain ⟨m, W, hm⟩ := (failures_iff_exists_leaf_witnesses c ρ q).mp hf
  obtain ⟨τ, ht, hsτ, ho⟩ := realize_observations h (countermodelObservations q m W)
    ⟨ρ, hs, (countermodelObservations_holds ρ m W).mpr hm⟩
  exact ⟨τ, ht, hsτ, (failures_iff_exists_leaf_witnesses c τ q).mpr
    ⟨m, W, (countermodelObservations_holds τ m W).mp ho⟩⟩

theorem hasCountermodelIn_true_of_hasCountermodelIn {C : Semantics.Tree n → Prop}
    (h : HasCountermodelIn C c Γ q) :
    HasCountermodelIn (fun _ => True) c Γ q := by
  obtain ⟨ρ, _, hs, hf⟩ := h
  exact ⟨ρ, fun _ => trivial, hs, hf⟩

theorem hasCountermodelIn_regularTop_iff [Finite V] :
    HasCountermodelIn RegularTop c Γ q ↔ HasCountermodelIn (fun _ => True) c Γ q := by
  classical
  let := Fintype.ofFinite V
  classical
  refine ⟨hasCountermodelIn_true_of_hasCountermodelIn, ?_⟩
  rintro ⟨ρ, _, hρ, hf⟩
  obtain ⟨m, W, hm⟩ := (failures_iff_exists_leaf_witnesses c ρ q).mp hf
  obtain ⟨τ, hr, ht, hw⟩ :=
    (Realizes.seedConsistency ⟨ρ, hρ, hm⟩).regular_realizes ⟨ρ, hρ⟩
  exact ⟨τ, hr, ht, (failures_iff_exists_leaf_witnesses c τ q).mpr ⟨m, W, hw⟩⟩

theorem hasCountermodelIn_finiteTop_iff :
    HasCountermodelIn FiniteTop c Γ q ↔
      Models.SatFin c Γ ∧ HasCountermodelIn (fun _ => True) c Γ q := by
  constructor
  · intro h
    obtain ⟨ρ, hc, hs, hf⟩ := h
    exact ⟨⟨ρ, hc, hs⟩, ρ, fun _ => trivial, hs, hf⟩
  · rintro ⟨hf, hc⟩
    exact hasCountermodelIn_of_boundRealization (Signed.boundRealization_finiteTop c Γ hf) hc

/-- Disjunctive entailment over `{⊥, f, ⊤}` holds over regular trees exactly when it holds over
arbitrary trees. -/
theorem disjEntails_regular_iff [Finite V] :
    DisjEntailsIn RegularTop c Γ q ↔ DisjEntailsIn (fun _ => True) c Γ q := by
  classical
  let := Fintype.ofFinite V
  classical
  have h := (hasCountermodelIn_regularTop_iff (c := c) (Γ := Γ) (q := q)).not
  simpa only [← not_disjEntailsIn_iff, not_not] using h

/-- Disjunctive entailment over `{⊥, f, ⊤}` holds over finite trees exactly when `Γ` has no finite
solution or the entailment holds over arbitrary trees. -/
theorem disjEntails_finite_iff :
    DisjEntailsIn FiniteTop c Γ q ↔
      ¬ Models.SatFin c Γ ∨ DisjEntailsIn (fun _ => True) c Γ q := by
  classical
  have h := (hasCountermodelIn_finiteTop_iff (c := c) (Γ := Γ) (q := q)).not
  simpa only [← not_disjEntailsIn_iff, not_and_or, not_not] using h

end DeciSigma1.Full.Reduction
