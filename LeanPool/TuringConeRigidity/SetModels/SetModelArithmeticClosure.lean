/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/SetModelArithmeticClosure.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.SetModelArithmeticSyntax
public import LeanPool.TuringConeRigidity.Computability.ArithmeticOracles

/-!
# Set Model Arithmetic Closure
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SetModelSyntax
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelArithmetic SetModelFunctions
open BoundedDefinability UniformArithmetic Encodable TableIndices IndexMatrix
universe u
noncomputable section

variable {M : ZFSet.{u}}

theorem arithmetic_comprehension (C : Context M) {P : Predicate} (hP : Arith P)
    (O : Oracles) (hO : ∀ i, O i ∈ reals M) (A : Oracle)
    (hA : ∀ n, P O n ↔ A n = true) : A ∈ reals M := by
  obtain ⟨Q,hQ,hc⟩ := arith_definition C hP
  let e : ℕ → ZFSet.{u} := fun i => realSet (O i)
  have he : ∀ i, e i ∈ M := hO
  have hs := hQ.sep_mem C e he C.omega_mem
  have hspec (n : ℕ) : Q (cons (natSet n) e) ↔ A n = true := by
    have hh := hc (cons (natSet n) e) n rfl
    have ho : (fun i => oracleOf (cons (natSet n) e (i+1))) = O := by
      funext i
      exact oracleOf_realSet (O i)
    rw [ho] at hh
    exact hh.trans (hA n)
  have eq : ZFSet.sep (fun x => Q (cons x e)) ZFSet.omega = realSet A := by
    apply ZFSet.ext
    intro x
    by_cases hx : x ∈ ZFSet.omega
    · obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
      simp only [ZFSet.mem_sep,hspec,nat_mem_realSet]
      exact and_iff_right ((mem_omega _).mpr ⟨n,rfl⟩)
    · constructor
      · intro h
        exact (hx (ZFSet.mem_sep.mp h).1).elim
      · intro h
        exact (hx (realSet_subset A h)).elim
  change realSet A ∈ M
  exact eq ▸ hs

theorem tableOracle_mem (C : Context M) {B : Oracle} (hB : B ∈ reals M) (e : ℕ) :
    tableOracle B e ∈ reals M := by
  have h : Arith (fun O v => tableGraph (O 0) e v) :=
    tableGraph_arith (parameter_arith 0) (Primrec.const 0) (Primrec.const e) Primrec.id
  apply arithmetic_comprehension C h (fun _ => B) (fun _ => hB) (tableOracle B e)
  intro n
  simp [tableOracle]

theorem lower_mem (C : Context M) {A B : Oracle} (hB : B ∈ reals M) (hAB : Reduces A B) :
    A ∈ reals M := by
  obtain ⟨c,hc⟩ := (reduces_iff_represents A B).mp hAB
  have hc' : Represents B (machine (encode c)) A := by simpa using hc
  rw [←tableOracle_eq hc']
  exact tableOracle_mem C hB (encode c)

theorem jump_mem (C : Context M) {A : Oracle} (hA : A ∈ reals M) :
    OracleJump.jump A ∈ reals M := by
  have h : Arith (fun O n => OracleJump.jump (O 0) n = true) :=
    query_at (jump_arith (parameter_arith 0)) (Primrec.const 0) Primrec.id
  exact arithmetic_comprehension C h (fun _ => A) (fun _ => hA) _ (fun _ => Iff.rfl)

theorem run_membership_definition (C : Context M) {B : OracleFamily} (hB : ArithmeticOracle B)
    {c e n z a : ℕ → ℕ} (hc : Primrec c) (he : Primrec e) (hn : Primrec n)
    (hz : Primrec z) (ha : Primrec a) :
    ArithmeticDefinition M (fun O v =>
      TableIndices.run (B O (c v)) (machine (e v)) (n v) (z v) = some (a v)) :=
  arith_definition C (run_arith hB hc he hn hz ha)

end
end TuringRigidity.SetModelSyntax

end OAI
