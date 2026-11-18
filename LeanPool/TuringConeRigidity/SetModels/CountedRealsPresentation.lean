/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/CountedRealsPresentation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.SetModelArithmeticDischarge
public import LeanPool.TuringConeRigidity.SetModels.CountableSetReal

/-!
# Counted Reals Presentation
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.SetModelCountability
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions
open SetModelSequences SetDegreeDecoding PersistentRestrictions PersistentPresentation
open EncodedForcing SetModelArithmetic
universe u

theorem counted_reals_columns {M R : ZFSet.{u}} (C : Context M) (hR : R ∈ M)
    (hreal : ∀ x ∈ R, ∃ B : Oracle, realSet B = x)
    (hcount : BoundedSetTheory.InternallyCountable M R) :
    ∃ A ∈ reals M, ∀ B : Oracle, (∃ n, columns A n = B) ↔ realSet B ∈ R := by
  classical
  obtain ⟨q,hq,hqf,hqo⟩ := hcount
  have hex (n : ℕ) : ∃ B : Oracle, realSet B ∈ R ∧
      ZFSet.pair (natSet n) (realSet B) ∈ q := by
    obtain ⟨x,hx,hnx,_⟩ := hqf.2 (natSet n) ((mem_omega _).mpr ⟨n,rfl⟩)
    obtain ⟨B,rfl⟩ := hreal x hx
    exact ⟨B,hx,hnx⟩
  choose B hB using hex
  have hseq : q = sequenceSet B := by
    apply ZFSet.ext; intro z
    constructor
    · intro hz
      obtain ⟨x,hx,y,_,rfl⟩ := hqf.1 z hz
      obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
      have hy := hqf.functional ((mem_omega _).mpr ⟨n,rfl⟩) hz (hB n).2
      exact (mem_sequenceSet B _).mpr ⟨n,by rw [hy]⟩
    · intro hz
      obtain ⟨n,rfl⟩ := (mem_sequenceSet B z).mp hz
      exact (hB n).2
  have hBM (n : ℕ) : B n ∈ reals M := C.transitive R hR _ (hB n).1
  obtain ⟨r,hr,hrc⟩ := internal_reals M C.transitive C.power C.separation C.infinity
  let A : Oracle := fun v => B (Nat.unpair v).1 (Nat.unpair v).2
  have hAM : A ∈ reals M := flatten_mem M C.transitive C.pairing C.union C.power
    C.separation C.infinity hr hrc C.pairing_mem pairingSet_code B hBM (hseq ▸ hq)
  have hcol (n : ℕ) : columns A n = B n := by
    funext k; simp only [columns,A,Nat.unpair_pair]
  refine ⟨A,hAM,fun X => ?_⟩
  constructor
  · rintro ⟨n,rfl⟩; rw [hcol]; exact (hB n).1
  · intro hX
    obtain ⟨n,hn,hnX⟩ := hqo _ hX
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    have he := hqf.functional ((mem_omega _).mpr ⟨n,rfl⟩) (hB n).2 hnX
    refine ⟨n,?_⟩
    rw [hcol]
    exact realSet_injective he

theorem presentation_of_counted_reals {M R : ZFSet.{u}} (C : Context M) (hR : R ∈ M)
    (hreal : ∀ x ∈ R, ∃ B : Oracle, realSet B = x)
    (hcount : BoundedSetTheory.InternallyCountable M R) (I : CountableIdeal)
    (hI : ∀ d, d ∈ I.carrier ↔ ∃ B : Oracle, realSet B ∈ R ∧ degree B = d) :
    ∃ A ∈ reals M, Presented I A := by
  obtain ⟨A,hA,hcols⟩ := counted_reals_columns C hR hreal hcount
  refine ⟨A,hA,fun d => ?_⟩
  rw [hI]
  constructor
  · rintro ⟨B,hB,hBd⟩
    obtain ⟨n,hn⟩ := (hcols B).mpr hB
    exact ⟨n,by rw [hn,hBd]⟩
  · rintro ⟨n,hn⟩
    exact ⟨columns A n,(hcols _).mp ⟨n,rfl⟩,hn⟩

theorem persistent_mem_of_counted_reals {M R : ZFSet.{u}} (C : Context M) (hR : R ∈ M)
    (hreal : ∀ x ∈ R, ∃ B : Oracle, realSet B = x)
    (hcount : BoundedSetTheory.InternallyCountable M R) (I : CountableIdeal)
    (hI : ∀ d, d ∈ I.carrier ↔ ∃ B : Oracle, realSet B ∈ R ∧ degree B = d)
    (ρ : I ≃o I) (hρ : Persistent I ρ)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier) :
    automorphismSet ρ ∈ M := by
  obtain ⟨A,hAM,hA⟩ := presentation_of_counted_reals C hR hreal hcount I hI
  exact (SetModelSyntax.persistent_sets C hA hAM ρ hρ hz).2

end TuringRigidity.SetModelCountability

end OAI
