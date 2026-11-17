/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/FiniteNaturalGraph.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.FiniteModelGraph

/-!
# Finite Natural Graph
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

/-- The set-coded graph of `f` on the indices from zero through the supplied bound. -/
noncomputable def finiteNaturalGraph (f : ℕ → ℕ) : ℕ → ZFSet.{u} :=
  finiteModelGraph (fun i => natSet (f i))

/-- The natural graph begins with its value at zero. -/
theorem finiteNaturalGraph_zero (f : ℕ → ℕ) :
    finiteNaturalGraph.{u} f 0 = {ZFSet.pair (natSet 0) (natSet (f 0))} := rfl

/-- The next natural graph adds exactly the next indexed value. -/
theorem finiteNaturalGraph_succ (f : ℕ → ℕ) (n : ℕ) :
    finiteNaturalGraph.{u} f (n+1) = finiteNaturalGraph f n ∪
      ({ZFSet.pair (natSet (n+1)) (natSet (f (n+1)))} : ZFSet.{u}) := rfl

theorem mem_finiteNaturalGraph (f : ℕ → ℕ) (n : ℕ) (z : ZFSet.{u}) :
    z ∈ finiteNaturalGraph f n ↔ ∃ i, i ≤ n ∧ z = ZFSet.pair (natSet i) (natSet (f i)) := by
  exact mem_finiteModelGraph (fun i => natSet (f i)) n z

theorem finiteNaturalGraph_pair (f : ℕ → ℕ) (n i : ℕ) (y : ZFSet.{u}) :
    ZFSet.pair (natSet i) y ∈ finiteNaturalGraph f n ↔ i ≤ n ∧ y = natSet (f i) := by
  exact finiteModelGraph_pair (fun j => natSet (f j)) n i y

theorem finiteNaturalGraph_function (f : ℕ → ℕ) (n : ℕ) :
    TransitiveNameModel.FunctionGraph (natSet (n+1)) ZFSet.omega (finiteNaturalGraph.{u} f n) := by
  exact finiteModelGraph_function ZFSet.omega (fun i => natSet (f i))
    (fun i => (mem_omega _).mpr ⟨f i, rfl⟩) n

theorem finiteNaturalGraph_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hω : ZFSet.omega.{u} ∈ M)
    (f : ℕ → ℕ) (n : ℕ) : finiteNaturalGraph f n ∈ M := by
  exact finiteModelGraph_mem M hM hP hU hω (fun i => natSet (f i))
    (fun i => hM _ hω _ ((mem_omega _).mpr ⟨f i, rfl⟩)) n

theorem internal_finite_natural_graph_bound (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hω : ZFSet.omega.{u} ∈ M) :
    ∃ Q ∈ M, (∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ ZFSet.prod ZFSet.omega ZFSet.omega) ∧
      ∀ f : ℕ → ℕ, ∀ n, finiteNaturalGraph f n ∈ Q := by
  obtain ⟨Q, hQ, hQdef, hgraphs⟩ :=
    internal_finite_model_graph_bound M hM hP hU hPow hS hω ZFSet.omega hω
  exact ⟨Q, hQ, hQdef, fun f n => hgraphs (fun i => natSet (f i))
    (fun i => (mem_omega _).mpr ⟨f i, rfl⟩) n⟩

end TuringRigidity.BoundedSetTheory

end OAI
