/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OrdinalProductClosure.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalProductPresentation

/-!
# Ordinal Product Closure
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel
universe u

theorem toZFSet_nat (n : ℕ) : (n : Ordinal.{u}).toZFSet = natSet n := by
  induction n with
  | zero => simp [natSet]
  | succ n ih => rw [Nat.cast_add_one,Ordinal.toZFSet_add_one,ih]; rfl

theorem toZFSet_omega : Ordinal.omega0.toZFSet = ZFSet.omega.{u} := by
  apply ZFSet.ext; intro x
  rw [Ordinal.mem_toZFSet_iff,mem_omega]
  constructor
  · rintro ⟨a,ha,rfl⟩
    obtain ⟨n,rfl⟩ := Ordinal.lt_omega0.mp ha
    exact ⟨n,toZFSet_nat n⟩
  · rintro ⟨n,rfl⟩
    exact ⟨n,Ordinal.natCast_lt_omega0 n,toZFSet_nat n⟩

theorem ordinal_mul_internal_schemas (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : Separation M) (hR : SigmaReplacement M)
    (a b : Ordinal.{u}) (ha : a.toZFSet ∈ M) (hb : b.toZFSet ∈ M) :
    (a*b).toZFSet ∈ M ∧ ∃ f ∈ M,
      OrderTypeCertificate (ZFSet.prod b.toZFSet a.toZFSet)
        (productRelation a.toZFSet b.toZFSet) (a*b).toZFSet f := by
  obtain ⟨hc,f,hf,hg,ho⟩ := orderType_internal M _ _ hM hP hU hPow hS hR
    (product_mem M hM hP hU hPow hS hb ha)
    (productRelation_mem M _ _ hM hP hU hPow hS ha hb)
    (productRelation_wellFounded a b) (productRelation_transitive a b)
  rw [product_orderType] at hc hg ho
  exact ⟨hc,f,hf,ZFSet.isOrdinal_toZFSet _,hg,ho⟩

theorem ordinal_mul_omega_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a : Ordinal.{u}) (ha : a.toZFSet ∈ M) : (a*Ordinal.omega0).toZFSet ∈ M := by
  have ho : Ordinal.omega0.toZFSet ∈ M := by
    simpa only [toZFSet_omega] using
      omega_mem M hM hT.separation.finitePrefix.bounded hT.infinity
  exact (ordinal_mul_internal M hM hT a Ordinal.omega0 ha ho).1

theorem ordinal_opow_nat_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a : Ordinal.{u}) (ha : a.toZFSet ∈ M) (n : ℕ) : (a^(n : Ordinal)).toZFSet ∈ M := by
  induction n with
  | zero =>
    rw [Nat.cast_zero,Ordinal.opow_zero,← Nat.cast_one,toZFSet_nat]
    exact hM _ (omega_mem M hM hT.separation.finitePrefix.bounded hT.infinity) _ ((mem_omega
      _).mpr ⟨1,rfl⟩)
  | succ n ih =>
    simpa only [Nat.cast_add_one,Ordinal.opow_add_one] using
      (ordinal_mul_internal M hM hT (a^(n : Ordinal)) a ih ha).1

end TuringRigidity.OrdinalArithmetic

end OAI
