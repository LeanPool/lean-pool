/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ModelNaturalNumbers.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.SourceTheory

/-!
# Model Natural Numbers
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

/-- An element of `M` satisfying its internal finite-ordinal formula. -/
def InternalNatural (M : ZFSet.{u}) :=
  {x : ZFSet.{u} // x ∈ M ∧ (Formula.finiteOrdinal 0).Realize M (fun _ => x)}

theorem internal_natural_iff (M : ZFSet.{u}) (hM : Transitive M)
    {x : ZFSet.{u}} (hx : x ∈ M) :
    (Formula.finiteOrdinal 0).Realize M (fun _ => x) ↔ ∃ n, x = natSet n := by
  rw [Formula.absolute _ M hM _ (fun _ => hx),eval_finiteOrdinal,finiteOrdinal_iff]

theorem sourceT_omega_mem (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    ZFSet.omega.{u} ∈ M := omega_mem M hM hT.separation.finitePrefix.bounded hT.infinity

/-- The equivalence between natural numbers and the model's internal finite ordinals. -/
noncomputable def naturalNumberEquiv (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    ℕ ≃ InternalNatural M := by
  have hω := sourceT_omega_mem M hM hT
  have hn (n : ℕ) : natSet.{u} n ∈ M := hM _ hω _ ((mem_omega _).mpr ⟨n,rfl⟩)
  let f : ℕ → InternalNatural M := fun n =>
    ⟨natSet n,hn n,(internal_natural_iff M hM (hn n)).mpr ⟨n,rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro m n h
    exact natSet_injective (congrArg Subtype.val h)
  · intro x
    obtain ⟨n,hn⟩ := (internal_natural_iff M hM x.property.1).mp x.property.2
    exact ⟨n,Subtype.ext hn.symm⟩

theorem naturalNumberEquiv_value (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) (n : ℕ) :
    (naturalNumberEquiv M hM hT n).val = natSet n := rfl

theorem naturalNumberEquiv_mem (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) (m n : ℕ) :
    (naturalNumberEquiv M hM hT m).val ∈ (naturalNumberEquiv M hM hT n).val ↔ m < n :=
  natSet_mem_natSet m n

theorem naturalNumberEquiv_successor (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) (n : ℕ) :
    (naturalNumberEquiv M hM hT (n+1)).val =
      insert (naturalNumberEquiv M hM hT n).val (naturalNumberEquiv M hM hT n).val := rfl

end TuringRigidity.BoundedSetTheory

end OAI
