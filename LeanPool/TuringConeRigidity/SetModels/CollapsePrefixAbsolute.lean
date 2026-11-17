/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/CollapsePrefixAbsolute.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.CollapseWithoutChoice
public import LeanPool.TuringConeRigidity.Syntax.FiniteModelGraph

/-!
# Collapse Prefix Absolute
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory.InternalCollapse
open TransitiveNameModel
universe u

theorem prefix_mem_without_choice (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hω : ZFSet.omega.{u} ∈ M)
    {A p : ZFSet.{u}} (hA : A ∈ M) (hp : Prefix A p) : p ∈ M := by
  classical
  obtain ⟨n,hp⟩ := hp
  have h0 : (∅ : ZFSet.{u}) ∈ M := hM _ hω _ ZFSet.omega_zero
  cases n with
  | zero =>
    have eq : p = ∅ := by
      apply ZFSet.ext; intro z
      constructor
      · intro hz
        obtain ⟨i,hi,_,_,_⟩ := hp.1 z hz
        exact False.elim (ZFSet.notMem_empty i hi)
      · exact fun hz => False.elim (ZFSet.notMem_empty z hz)
    exact eq ▸ h0
  | succ n =>
    obtain ⟨v,hv,hva⟩ := InternalWellOrder.FunctionGraph.exists_presentation hp
    let f : ℕ → ZFSet.{u} := fun i => if i ≤ n then v (natSet i) else ∅
    have hf : ∀ i, f i ∈ M := by
      intro i
      dsimp only [f]
      split_ifs with hi
      · exact hM A hA _ (hva _ ((natSet_mem_natSet i (n+1)).mpr (by omega)))
      · exact h0
    have eq : p = finiteModelGraph f n := by
      apply ZFSet.ext; intro z
      rw [mem_finiteModelGraph]
      constructor
      · intro hz
        obtain ⟨j,hj,y,_,rfl⟩ := hp.1 z hz
        obtain ⟨i,hi,rfl⟩ := (mem_natSet (n+1) j).mp hj
        have hin : i ≤ n := by omega
        have hy := ((hv.pair_iff _ _).mp hz).2
        exact ⟨i,hin,by rw [hy]; simp only [f,ite_eq_left hin]⟩
      · rintro ⟨i,hi,rfl⟩
        apply (hv.pair_iff _ _).mpr
        exact ⟨(natSet_mem_natSet i (n+1)).mpr (by omega),by simp only [f,ite_eq_left hi]⟩
    rw [eq]
    exact finiteModelGraph_mem M hM hP hU hω f hf n

theorem conditions_exist_absolute_without_choice (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hω : ZFSet.omega.{u} ∈ M) {A : ZFSet.{u}} (hA : A ∈ M) :
    ∃ c ∈ M, ∀ p, p ∈ c ↔ Prefix A p := by
  obtain ⟨c,hc,hcdef⟩ := conditions_exist_without_choice M hM hP hU hPow hS hω hA
  exact ⟨c,hc,fun p => (hcdef p).trans
    ⟨And.right,fun hp => ⟨prefix_mem_without_choice M hM hP hU hω hA hp,hp⟩⟩⟩

end TuringRigidity.BoundedSetTheory.InternalCollapse

end OAI
