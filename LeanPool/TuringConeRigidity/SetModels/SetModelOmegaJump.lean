/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/SetModelOmegaJump.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.SetModelSequences
public import LeanPool.TuringConeRigidity.Constructibility.PersistenceRealClosure

/-!
# Set Model Omega Jump
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SetModelSequences
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelIteration
open JumpIdealPresentation OracleJump
universe u
noncomputable section

theorem omegaJump_mem (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M)
    (hJ : ∀ A ∈ reals M, jump A ∈ reals M)
    {p g : ZFSet.{u}} (hp : p ∈ M) (hpdef : PairingCode p) (hgM : g ∈ M)
    (hg : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (realSet A) (realSet B) ∈ g ↔ B = jump A)
    {A : Oracle} (hA : A ∈ reals M) : omegaJump A ∈ reals M := by
  obtain ⟨r,hr,hrdef⟩ := internal_reals M hM hPow hS hI
  let F : ZFSet.{u} → ZFSet.{u} := fun x => realSet (jump (oracleOf x))
  have hF : ∀ x ∈ r, F x ∈ r := by
    intro x hx
    obtain ⟨B,hB,rfl⟩ := (hrdef x).mp hx
    exact (hrdef _).mpr ⟨jump B,hJ B hB,by simp only [F,oracleOf_realSet]⟩
  have hfg : ∀ x ∈ r, ∀ y ∈ r, ZFSet.pair x y ∈ g ↔ y = F x := by
    intro x hx y hy
    obtain ⟨B,hB,rfl⟩ := (hrdef x).mp hx
    obtain ⟨C,hC,rfl⟩ := (hrdef y).mp hy
    simpa only [F,oracleOf_realSet,realSet_injective.eq_iff] using hg B hB C hC
  have hq := iterationSet_mem M hM hP hU hPow hS hI hr hgM F hF hfg
  have hiter : ∀ n, F^[n] (realSet A) = realSet (OracleJump.iterate A n) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [Function.iterate_succ_apply',ih,F,oracleOf_realSet,OracleJump.iterate]
  have hs := sequence_mem_of_iteration M hM hP hU hPow hS hI hr F hF hq
    ((hrdef _).mpr ⟨A,hA,rfl⟩) (OracleJump.iterate A) hiter
  have hj : ∀ n, OracleJump.iterate A n ∈ reals M := by
    intro n
    induction n with
    | zero => exact hA
    | succ n ih => exact hJ _ ih
  exact flatten_mem M hM hP hU hPow hS hI hr hrdef hp hpdef _ hj hs

theorem realClosure_of_arithmetic_graphs (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hI : Infinity M)
    (hL : ∀ {A B}, B ∈ reals M → Reduces A B → A ∈ reals M)
    (hJoin : ∀ {A B}, A ∈ reals M → B ∈ reals M → join A B ∈ reals M)
    (hJ : ∀ A ∈ reals M, jump A ∈ reals M)
    {p g : ZFSet.{u}} (hp : p ∈ M) (hpdef : PairingCode p) (hgM : g ∈ M)
    (hg : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (realSet A) (realSet B) ∈ g ↔ B = jump A) :
    PersistenceRealClosure.Closed (reals M) :=
  ⟨hL,hJoin,fun hA => omegaJump_mem M hM hP hU hPow hS hI hJ hp hpdef hgM hg hA⟩

end
end TuringRigidity.SetModelSequences

end OAI
