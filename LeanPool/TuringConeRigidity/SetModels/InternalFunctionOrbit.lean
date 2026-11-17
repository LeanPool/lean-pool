/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalFunctionOrbit.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ModelIterationFormula

/-!
# Internal Function Orbit
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

noncomputable def orbitGraph (a : ℕ → ZFSet.{u}) : ZFSet.{u} :=
  ZFSet.range (fun n => ZFSet.pair (natSet n) (a n))

theorem mem_orbitGraph (a : ℕ → ZFSet.{u}) (z : ZFSet.{u}) :
    z ∈ orbitGraph a ↔ ∃ n, z = ZFSet.pair (natSet n) (a n) := by
  rw [orbitGraph,ZFSet.mem_range]
  exact ⟨fun ⟨n,hn⟩ => ⟨n,hn.symm⟩,fun ⟨n,hn⟩ => ⟨n,hn.symm⟩⟩

theorem orbitGraph_pair (a : ℕ → ZFSet.{u}) (n : ℕ) (x : ZFSet.{u}) :
    ZFSet.pair (natSet n) x ∈ orbitGraph a ↔ x = a n := by
  rw [mem_orbitGraph]
  constructor
  · rintro ⟨m,he⟩
    obtain ⟨hn,hx⟩ := ZFSet.pair_inj.mp he
    have hnm := natSet_injective hn
    exact hnm.symm ▸ hx
  · intro h; exact ⟨n,congrArg (ZFSet.pair (natSet n)) h⟩

theorem orbitGraph_function (d : ZFSet.{u}) (a : ℕ → ZFSet.{u}) (ha : ∀ n, a n ∈ d) :
    TransitiveNameModel.FunctionGraph ZFSet.omega d (orbitGraph a) := by
  constructor
  · intro z hz
    obtain ⟨n,rfl⟩ := (mem_orbitGraph a z).mp hz
    exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,a n,ha n,rfl⟩
  · intro x hx
    obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
    exact ⟨a n,ha n,(orbitGraph_pair a n _).mpr rfl,fun y _ hy => (orbitGraph_pair a n y).mp hy⟩

namespace Formula

def orbitMember (o d Q b F z : ℕ) : Formula := .existsMem o (.existsMem (d+1)
  (.conj (.orderedPair (z+2) 1 0)
    (modelIteration (o+2) (d+2) (Q+2) 1 (b+2) 0 (.pairMem 1 0 (F+5)))))

theorem orbitMember_spec (o d Q b F z : ℕ) (e : ℕ → ZFSet.{u}) (ho : e o = ZFSet.omega)
    (hQ : ∀ a : ℕ → ZFSet.{u}, (∀ i, a i ∈ e d) → ∀ k, finiteModelGraph a k ∈ e Q)
    (hF : TransitiveNameModel.FunctionGraph (e d) (e d) (e F))
    (a : ℕ → ZFSet.{u}) (ha : ∀ i, a i ∈ e d) (hb : e b = a 0)
    (hstep : ∀ i, ZFSet.pair (a i) (a (i+1)) ∈ e F) :
    (orbitMember o d Q b F z).Eval e ↔ e z ∈ orbitGraph a := by
  simp only [orbitMember,Formula.Eval,eval_orderedPair,cons_zero,cons_succ]
  rw [ho,mem_orbitGraph]
  have hs (n : ℕ) (w : ZFSet.{u}) :
      (modelIteration (o+2) (d+2) (Q+2) 1 (b+2) 0 (.pairMem 1 0 (F+5))).Eval
        (cons w (cons (natSet n) e)) ↔ w = a n := by
    apply modelIteration_spec (o+2) (d+2) (Q+2) 1 (b+2) 0 (.pairMem 1 0 (F+5))
      (cons w (cons (natSet n) e)) ho hQ n rfl a ha hb
    intro i v _
    simp only [eval_pairMem,cons_zero,cons_succ]
    exact ⟨fun hv => hF.functional (ha i) hv (hstep i),fun hv => hv.symm ▸ hstep i⟩
  constructor
  · rintro ⟨n,hn,w,_,hz,hw⟩
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    rw [(hs n w).mp hw] at hz
    exact ⟨n,hz⟩
  · rintro ⟨n,hz⟩
    exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,a n,ha n,hz,(hs n _).mpr rfl⟩
end Formula

theorem internal_orbitGraph (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {d F : ZFSet.{u}} (hd : d ∈ M) (hFM : F ∈ M)
    (hF : TransitiveNameModel.FunctionGraph d d F) (a : ℕ → ZFSet.{u})
    (ha : ∀ i, a i ∈ d) (hstep : ∀ i, ZFSet.pair (a i) (a (i + 1)) ∈ F) : orbitGraph a ∈ M := by
  have hS := hT.separation.finitePrefix.bounded
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨Q,hQM,_,hQ⟩ := internal_finite_model_graph_bound M hM hT.pairing hT.union hT.powerSet hS
    hω d hd
  let e := cons ZFSet.omega (cons d (cons Q (cons (a 0) (fun _ => F))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hω
    rcases i with _ | i
    · exact hd
    rcases i with _ | i
    · exact hQM
    rcases i with _ | i
    · exact hM _ hd _ (ha 0)
    exact hFM
  have hs := sep_mem M hM hS (Formula.orbitMember 1 2 3 4 5 0) e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hS hω hd)
  have hEq : ZFSet.sep (fun z => (Formula.orbitMember 1 2 3 4 5 0).Eval (cons z e))
      (ZFSet.prod ZFSet.omega d) = orbitGraph a := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sep,Formula.orbitMember_spec 1 2 3 4 5 0 (cons z e) rfl hQ hF a ha rfl hstep]
    exact ⟨And.right,fun h => ⟨ZFSet.mem_prod.mpr ((orbitGraph_function d a ha).1 z h),h⟩⟩
  exact hEq ▸ hs

end TuringRigidity.BoundedSetTheory

end OAI
