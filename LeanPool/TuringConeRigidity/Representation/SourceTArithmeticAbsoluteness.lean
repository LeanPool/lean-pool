/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/SourceTArithmeticAbsoluteness.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ModelArithmeticTreeDescent

/-!
# Source TArithmetic Absoluteness
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.ArithmeticTree
open UniformArithmetic BoundedSetTheory TransitiveNameModel ArithmeticPersistence
  ArithmeticHierarchy
universe u
noncomputable section

theorem sourceT_exists_arithmetic_real (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {Q : Predicate} (hQ : Arith Q) (A R : Oracle)
    (hA : A ∈ modelReals M) (hR : R ∈ modelReals M) (v : ℕ) :
    (∃ H : Oracle, Q (parameters A R H) v) ↔
      ∃ H ∈ modelReals M, Q (parameters A R H) v := by
  constructor
  · rintro ⟨H,hH⟩
    obtain ⟨t,ht⟩ := (arithmetic_tests hQ).1
    have htest : ∃ H : Oracle, ∃ f : ℕ → ℕ,
        ∀ n, t.eval (parameters A R H) f (Nat.pair v n) :=
      ⟨H,(ht (parameters A R H) v).mp hH⟩
    have hz : (fun _ : ℕ => false) ∈ modelReals M :=
      sourceT_arithmetic_real M hM hT (equal (Primrec.const 0) (Primrec.const 1))
        (fun _ => A) (fun _ => hA) _ (by intro n; simp)
    have hO : ∀ i, parameters A R (fun _ => false) i ∈ modelReals M := by
      intro i
      rcases i with _ | i
      · exact hA
      rcases i with _ | i
      · exact hR
      exact hz
    obtain ⟨s,G,hGM,hG,hs⟩ := t.mergeReal.sourceT_chain M hM hT
      (parameters A R (fun _ => false)) hO v ((t.exists_mergeReal A R v).mp htest)
    obtain ⟨F,hFM,hF⟩ := sourceT_chainGraph M hM hT s hGM hG
    refine ⟨Test.realPart (chainValue s),sourceT_realPart M hM hT _ hFM hF,?_⟩
    exact (ht _ v).mpr ⟨Test.witnessPart (chainValue s),
      fun n => (t.mergeReal_eval A R (chainValue s) (Nat.pair v n)).mp (hs n)⟩
  · rintro ⟨H,_,hH⟩
    exact ⟨H,hH⟩

theorem sourceT_forall_arithmetic_real (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {Q : Predicate} (hQ : Arith Q) (A R : Oracle)
    (hA : A ∈ modelReals M) (hR : R ∈ modelReals M) (v : ℕ) :
    (∀ H ∈ modelReals M, Q (parameters A R H) v) ↔
      ∀ H : Oracle, Q (parameters A R H) v := by
  classical
  constructor
  · intro h H
    by_contra hn
    obtain ⟨K,hKM,hK⟩ := (sourceT_exists_arithmetic_real M hM hT hQ.neg A R hA hR v).mp ⟨H,hn⟩
    exact hK (h K hKM)
  · exact fun h H _ => h H

theorem sourceT_piOneOne (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {P : Oracle → Oracle → Prop} {Q : Predicate} (hQ : Arith Q)
    (hiff : ∀ A R, P A R ↔ ∀ H : Oracle, Q (parameters A R H) 0)
    (A R : Oracle) (hA : A ∈ modelReals M) (hR : R ∈ modelReals M) :
    (∀ H ∈ modelReals M, Q (parameters A R H) 0) ↔ P A R :=
  (sourceT_forall_arithmetic_real M hM hT hQ A R hA hR 0).trans (hiff A R).symm

theorem sourceT_persistence_presentation (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (A R : Oracle) (hA : A ∈ modelReals M) (hR : R ∈ modelReals M) :
    (∀ H ∈ modelReals M, Base A R ∧ Matrix (parameters A R H) 0) ↔ Property A R := by
  apply sourceT_piOneOne M hM hT (base_arith.and matrix_arith) _ A R hA hR
  intro A R
  rw [property_iff]
  change Base A R ∧ Criterion A R ↔ ∀ H, Base A R ∧
    (NumericalIdeal.JumpCode H → NumericalIdeal.Includes A H →
      ∃ e, NumericalAutomorphism.Action H
        (fun v => tableOracle (OracleJump.iterate H 11) e v = true) ∧
        NumericalExtension.Compatible A H (fun v => R v = true)
          (fun v => tableOracle (OracleJump.iterate H 11) e v = true))
  exact ⟨fun h H => ⟨h.1,h.2 H⟩,
    fun h => ⟨(h FixedArithmetic.zero).1,fun H => (h H).2⟩⟩

end
end TuringRigidity.ArithmeticTree

end OAI
