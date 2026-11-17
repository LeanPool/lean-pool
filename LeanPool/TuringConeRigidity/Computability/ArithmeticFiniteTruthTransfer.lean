/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/ArithmeticFiniteTruthTransfer.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticTruthRequirements
public import LeanPool.TuringConeRigidity.Computability.ArithmeticSourceTruth

/-!
# Arithmetic Finite Truth Transfer
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.ArithmeticFiniteTruthTransfer
open UniformArithmetic ArithmeticPrefixForcing ArithmeticPrefixFamilies
open ShuffleRequirements FiniteShuffle GenericIdentity GenericTruth
open EncodedForcing (word)

theorem generic_meets_family {D : PrefixPredicate} (hD : ArithmeticPrefix D)
    (O : Oracles) (v : ℕ) (hd : ∀ n, DenseOpen (D O (Nat.pair v n)))
    (G : Oracle) (hG : Generic O G) :
    GenericFor (fun n => D O (Nat.pair v n)) G := by
  intro n
  have ha : Arith (fun O s => D O (Nat.pair v n) (word s)) :=
    (hD.comp _ (Primrec₂.natPair.comp (Primrec.const (Nat.pair v n)) Primrec.id)).congr
      (fun _ _ => by simp only [left,right,Nat.unpair_pair,id_eq])
  exact hG (fun O s => D O (Nat.pair v n) s) ha (hd n)

theorem finite_family_of_dense {P : Predicate} (hP : Arith P) (O : Oracles) (v : ℕ)
    (hd : ∀ s : List Bool, ∃ H : Oracle,
      Generic O H ∧ Realizes s H ∧ P (Function.update O 0 H) v) :
    ∃ E : PrefixPredicate, ArithmeticPrefix E ∧ (∀ n, DenseOpen (E O n)) ∧
      ∀ G : Oracle, GenericFor (E O) G → P (Function.update O 0 G) v := by
  obtain ⟨Q,D,hQ,hD,hup,hden,ht⟩ := ArithmeticTruthRequirements.arithmetic_truth_requirements hP
  have hqd : DenseOpen (Q O v) := by
    refine ⟨?_,hup O v⟩
    intro s
    obtain ⟨H,hH,hs,hPH⟩ := hd s
    have hHD := generic_meets_family hD O v (hden O v) H hH
    obtain ⟨t,htQ,htH⟩ := (ht O v H hHD).mp hPH
    obtain ⟨u,hsu,htu,_⟩ := realizes_common hs htH
    exact ⟨u,hsu,hup O v t u htu htQ⟩
  let E : PrefixPredicate := fun O n s => D O (Nat.pair v n) s ∧ Q O v s
  have hE : ArithmeticPrefix E :=
    (prefix_comp hD (Primrec₂.natPair.comp (Primrec.const v) Primrec.id)).and
      (prefix_comp hQ (Primrec.const v))
  refine ⟨E,hE,fun n => dense_and (hden O v n) hqd,?_⟩
  intro G hG
  have hGD : GenericFor (fun n => D O (Nat.pair v n)) G := by
    intro n
    obtain ⟨s,hs,hGs⟩ := hG n
    exact ⟨s,hs.1,hGs⟩
  apply (ht O v G hGD).mpr
  obtain ⟨s,hs,hGs⟩ := hG 0
  exact ⟨s,hs.2,hGs⟩

theorem source_equation_finite_family (p : OracleCode) (P : Oracle)
    (hd : ∀ s : List Bool, ∃ H : Oracle,
      Generic (fun _ => P) H ∧ Realizes s H ∧ SourceEquation p P (triple H)) :
    ∃ E : PrefixPredicate, ArithmeticPrefix E ∧
      (∀ n, DenseOpen (E (fun _ => P) n)) ∧
      ∀ G : Oracle, GenericFor (E (fun _ => P)) G → SourceEquation p P (triple G) := by
  have hden : ∀ s : List Bool, ∃ H : Oracle,
      Generic (fun _ => P) H ∧ Realizes s H ∧
        SourceEquation p ((Function.update (fun _ => P) 0 H) 1)
          (triple ((Function.update (fun _ => P) 0 H) 0)) := by
    simpa using hd
  simpa using finite_family_of_dense (ArithmeticSourceTruth.triple_equation_arith p)
    (fun _ => P) 0 hden

end TuringRigidity.ArithmeticFiniteTruthTransfer

end OAI
