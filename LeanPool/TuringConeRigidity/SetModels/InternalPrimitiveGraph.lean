/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalPrimitiveGraph.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.NaturalPrimitiveRecursion

/-!
# Internal Primitive Graph
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u
namespace Formula

def numericalGraph (φ : Formula) : Formula := .existsMem 1 (.existsMem 2
  (.conj (.orderedPair 2 1 0) (unary φ 3 4 1 0)))
end Formula

theorem internal_primitive_graph (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {f : ℕ → ℕ} (hf : Nat.Primrec f) :
    ∃ F ∈ M, ∀ z, z ∈ F ↔ ∃ n, z = ZFSet.pair (natSet n) (natSet (f n)) := by
  have hS := hT.separation.finitePrefix.bounded
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨Q,hQ,_,hbound⟩ := internal_finite_natural_graph_bound M hM hT.pairing hT.union
    hT.powerSet hS hω
  obtain ⟨φ,hφ⟩ := primitive_bounded_definition.{u} hf
  let e := cons ZFSet.omega (fun _ => Q)
  have he : ∀ i, e i ∈ M := by intro i; cases i <;> assumption
  let F := ZFSet.sep (fun z => (Formula.numericalGraph φ).Eval (cons z e))
    (ZFSet.prod ZFSet.omega ZFSet.omega)
  have hF : F ∈ M := sep_mem M hM hS (Formula.numericalGraph φ) e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hS hω hω)
  have hn (n : ℕ) : natSet.{u} n ∈ ZFSet.omega := (mem_omega _).mpr ⟨n,rfl⟩
  have hdef (z y : ZFSet.{u}) (n : ℕ) := Formula.unary_spec hφ 3 4 1 0
    (cons y (cons (natSet n) (cons z e))) rfl hbound n rfl
  refine ⟨F,hF,?_⟩
  intro z
  simp only [F,ZFSet.mem_sep,Formula.numericalGraph,Formula.Eval,Formula.eval_orderedPair,
    cons_zero,cons_succ,e]
  constructor
  · rintro ⟨_,x,hx,y,_,hz,h⟩
    obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
    obtain rfl := (hdef z y n).mp h
    exact ⟨n,hz⟩
  · rintro ⟨n,rfl⟩
    exact ⟨ZFSet.mem_prod.mpr ⟨natSet n,hn n,natSet (f n),hn (f n),rfl⟩,
      natSet n,hn n,natSet (f n),hn (f n),rfl,(hdef _ _ n).mpr rfl⟩

end TuringRigidity.BoundedSetTheory

end OAI
