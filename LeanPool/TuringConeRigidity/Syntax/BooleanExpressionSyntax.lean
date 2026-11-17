/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/BooleanExpressionSyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.BooleanExpressionCertificate

/-!
# Boolean Expression Syntax
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BooleanExpressionCertificate
open TransitiveNameModel BoundedSetTheory InternalBooleanSyntax

def stepFormula (c B Q S K g t U z0 z1 z2 : ℕ) : Formula :=
  .disj (.conj (.member U S) (.orderedPair t z0 U))
    (.disj
      (.existsMem K (.existsMem (B+1)
        (.conj (.orderedPair (t+2) (z1+2) 1)
          (.conj (.pairMem 1 0 (g+2)) (negFormula (c+2) 0 (U+2))))))
      (.existsMem K (.existsMem (Q+1)
        (.conj (.orderedPair (t+2) (z2+2) 1)
          (.conj (supFormula (c+2) 0 (U+2))
            (.conj (.allMem 1 (.existsMem 1 (.pairMem 1 0 (g+4))))
              (.allMem 0 (.existsMem 2 (.pairMem 0 1 (g+4))))))))))

theorem stepFormula_spec (c B Q S K g t U z0 z1 z2 : ℕ) (e : ℕ → ZFSet.{0})
    (h0 : e z0 = natSet 0) (h1 : e z1 = natSet 1) (h2 : e z2 = natSet 2) :
    (stepFormula c B Q S K g t U z0 z1 z2).Eval e ↔
      Step (e c) (e B) (e Q) (e S) (e K) (e g) (e t) (e U) := by
  simp only [stepFormula,Formula.eval_disj,Formula.Eval,Formula.eval_orderedPair,
    Formula.eval_pairMem,Formula.eval_allMem,negFormula_spec,supFormula_spec,
    cons_zero,cons_succ,h0,h1,h2,Step,FiniteTerm.tag]

def certificateFormula (c B Q S K g z0 z1 z2 : ℕ) : Formula :=
  .allMem g (.existsMem (K+1) (.existsMem (B+2)
    (.conj (.orderedPair 2 1 0)
      (stepFormula (c+3) (B+3) (Q+3) (S+3) (K+3) (g+3) 1 0 (z0+3) (z1+3) (z2+3)))))

theorem certificateFormula_spec (c B Q S K g z0 z1 z2 : ℕ) (e : ℕ → ZFSet.{0})
    (h0 : e z0 = natSet 0) (h1 : e z1 = natSet 1) (h2 : e z2 = natSet 2) :
    (certificateFormula c B Q S K g z0 z1 z2).Eval e ↔
      Certificate (e c) (e B) (e Q) (e S) (e K) (e g) := by
  simp only [certificateFormula,Formula.eval_allMem,Formula.Eval,
    Formula.eval_orderedPair,cons_zero,cons_succ,Certificate]
  apply forall_congr'; intro z
  apply imp_congr_right; intro _
  apply exists_congr; intro t
  apply and_congr_right; intro _
  apply exists_congr; intro U
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  exact stepFormula_spec _ _ _ _ _ _ _ _ _ _ _ _ h0 h1 h2

def Witness (c B Q S K U : ZFSet.{0}) : Prop :=
  Transitive K ∧ ∃ g ∈ K, Certificate c B Q S K g ∧
    ∃ t ∈ K, ZFSet.pair t U ∈ g

def witnessFormula (c B Q S K U z0 z1 z2 : ℕ) : Formula :=
  .conj (.allMem K (.subset 0 (K+1)))
    (.existsMem K (.conj
      (certificateFormula (c+1) (B+1) (Q+1) (S+1) (K+1) 0 (z0+1) (z1+1) (z2+1))
      (.existsMem (K+1) (.pairMem 0 (U+2) 1))))

theorem witnessFormula_spec (c B Q S K U z0 z1 z2 : ℕ) (e : ℕ → ZFSet.{0})
    (h0 : e z0 = natSet 0) (h1 : e z1 = natSet 1) (h2 : e z2 = natSet 2) :
    (witnessFormula c B Q S K U z0 z1 z2).Eval e ↔
      Witness (e c) (e B) (e Q) (e S) (e K) (e U) := by
  simp only [witnessFormula,Formula.Eval,Formula.eval_allMem,Formula.eval_subset,
    Formula.eval_pairMem,cons_zero,cons_succ,Witness,TransitiveNameModel.Transitive]
  apply and_congr Iff.rfl
  apply exists_congr; intro g
  apply and_congr_right; intro _
  exact and_congr (certificateFormula_spec _ _ _ _ _ _ _ _ _ _ h0 h1 h2) Iff.rfl

def parameters (c B Q S : ZFSet.{0}) : ℕ → ZFSet.{0} :=
  cons c (cons B (cons Q (cons S (cons (natSet 0) (cons (natSet 1) (fun _ => natSet 2))))))

theorem parameters_mem (M c B Q S : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hB : B ∈ M) (hQ : Q ∈ M) (hS : S ∈ M) :
    ∀ i, parameters c B Q S i ∈ M := by
  intro i
  rcases i with _|_|_|_|_|_|i
  · exact hc
  · exact hB
  · exact hQ
  · exact hS
  all_goals exact hM _ (sourceT_omega_mem M hM hT) _ ((mem_omega _).mpr ⟨_,rfl⟩)

def witnessBody : Formula := witnessFormula 2 3 4 5 0 1 6 7 8

theorem witnessBody_realize (M c B Q S K U : ZFSet.{0}) (hM : Transitive M)
    (he : ∀ i, parameters c B Q S i ∈ M) (hK : K ∈ M) (hU : U ∈ M) :
    witnessBody.Realize M (cons K (cons U (parameters c B Q S))) ↔ Witness c B Q S K U := by
  rw [Formula.absolute _ M hM _ (by
    intro i
    rcases i with _ | _ | i
    · exact hK
    · exact hU
    · exact he i)]
  exact witnessFormula_spec _ _ _ _ _ _ _ _ _ _ rfl rfl rfl

noncomputable def certified (M c B Q S : ZFSet.{0}) : ZFSet.{0} :=
  B.sep (fun U => ∃ K ∈ M, Witness c B Q S K U)

theorem certified_mem (M c B Q S : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hB : B ∈ M) (hQ : Q ∈ M) (hS : S ∈ M) : certified M c B Q S ∈ M := by
  have he := parameters_mem M c B Q S hM hT hc hB hQ hS
  obtain ⟨a,ha,hspec⟩ := hT.separation.finitePrefix
    (.existsSet (.bounded witnessBody)) (parameters c B Q S) he B hB
  have eq : a = certified M c B Q S := by
    apply ZFSet.ext; intro U
    rw [certified,ZFSet.mem_sep]
    constructor
    · intro hU
      obtain ⟨hUB,K,hKM,hK⟩ := (hspec U (hM _ ha _ hU)).mp hU
      exact ⟨hUB,K,hKM,(witnessBody_realize M c B Q S K U hM he hKM (hM _ hB _ hUB)).mp hK⟩
    · rintro ⟨hUB,K,hKM,hK⟩
      have hUM := hM _ hB _ hUB
      exact (hspec U hUM).mpr ⟨hUB,K,hKM,(witnessBody_realize M c B Q S K U hM he hKM hUM).mpr hK⟩
  exact eq ▸ ha

end TuringRigidity.BooleanExpressionCertificate

end OAI
