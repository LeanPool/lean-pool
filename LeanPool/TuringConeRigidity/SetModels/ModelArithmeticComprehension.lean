/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ModelArithmeticComprehension.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticSetSyntax

/-!
# Model Arithmetic Comprehension
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel UniformArithmetic
universe u

/-- The characteristic oracle of predicate `P` under the oracle environment `O`. -/
noncomputable def arithmeticReal (P : Predicate) (O : Oracles) : Oracle := fun n => by
  classical
  exact decide (P O n)

theorem arithmeticReal_true (P : Predicate) (O : Oracles) (n : ℕ) :
    arithmeticReal P O n = true ↔ P O n := by
  classical
  simp only [arithmeticReal,decide_eq_true_eq]

theorem sourceT_arithmetic_comprehension (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {P : Predicate} (hP : Arith P) (O : Oracles) (hO : ∀ i, O i ∈ modelReals M) :
    arithmeticReal P O ∈ modelReals M := by
  have hS := hT.separation.finitePrefix.bounded
  have hω := sourceT_omega_mem M hM hT
  obtain ⟨Q,hQ,_,hbound⟩ := internal_finite_natural_graph_bound M hM hT.pairing hT.union
    hT.powerSet hS hω
  obtain ⟨φ,hφ⟩ := arithmetic_bounded_definition.{u} hP
  let e := cons ZFSet.omega (cons Q (fun i => realCode (O i)))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | i
    · exact hω
    rcases i with _ | i
    · exact hQ
    exact hO i
  let B := ZFSet.sep (fun x => φ.Eval (cons x e)) ZFSet.omega
  have hB : B ∈ M := sep_mem M hM hS φ e he hω
  have hBdef (n : ℕ) : natSet.{u} n ∈ B ↔ P O n := by
    rw [ZFSet.mem_sep]
    change (natSet n ∈ ZFSet.omega ∧ φ.Eval (arithmeticEnv Q O n)) ↔ P O n
    rw [hφ Q hbound O n]
    exact and_iff_right ((mem_omega _).mpr ⟨n,rfl⟩)
  have hcode : realCode (arithmeticReal P O) = B := by
    apply ZFSet.ext; intro x
    by_cases hx : x ∈ ZFSet.omega.{u}
    · obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
      rw [natSet_mem_realCode,arithmeticReal_true,hBdef]
    · exact ⟨fun h => False.elim (hx (realCode_subset _ h)),
        fun h => False.elim (hx (ZFSet.mem_sep.mp h).1)⟩
  change realCode (arithmeticReal P O) ∈ M
  rw [hcode]
  exact hB

theorem sourceT_arithmetic_real (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {P : Predicate} (hP : Arith P) (O : Oracles) (hO : ∀ i, O i ∈ modelReals M)
    (A : Oracle) (hA : ∀ n, A n = true ↔ P O n) : A ∈ modelReals M := by
  have he : A = arithmeticReal P O := by
    funext n
    have h := (hA n).trans (arithmeticReal_true P O n).symm
    cases ha : A n <;> cases hb : arithmeticReal P O n <;> simp_all
  rw [he]
  exact sourceT_arithmetic_comprehension M hM hT hP O hO

end TuringRigidity.BoundedSetTheory

end OAI
