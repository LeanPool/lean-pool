/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/SetModelCountablePresentation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.SetModelCountability
public import LeanPool.TuringConeRigidity.SetModels.SetModelArithmeticDischarge

/-!
# Set Model Countable Presentation
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SetModelCountability
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions SetModelArithmetic
open BoundedDefinability SetModelSyntax SetDegreeDecoding SetModelSequences
open PersistentRestrictions PersistentPresentation EncodedForcing
universe u
noncomputable section
variable {M : ZFSet.{u}}

theorem countable_presentation (C : Context M) (hCh : InternalChoice M)
    (I : CountableIdeal) (hI : idealSet I ∈ M)
    (hct : InternallyCountable M (idealSet I)) :
    ∃ A ∈ reals M, Presented I A := by
  obtain ⟨q,hq,hqf,hqo⟩ := countable_graph C hI hct
  have hne : ∀ x ∈ idealSet I, ∃ y, y ∈ x := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := (mem_idealSet I x).mp hx
    obtain ⟨B,rfl⟩ := degree_surjective a
    exact ⟨realSet B,(real_mem_degreeSet B _).mpr rfl⟩
  obtain ⟨g,hg,hgf,hgc⟩ := choice_graph C hCh hI hne
  let u := ZFSet.sUnion (idealSet I)
  have hu : u ∈ M := union_mem M C.transitive C.union hI
  have hex (n : ℕ) : ∃ B : Oracle, degree B ∈ I.carrier ∧ realSet B ∈ u ∧
      ZFSet.pair (natSet n) (degreeSet (degree B)) ∈ q ∧
      ZFSet.pair (degreeSet (degree B)) (realSet B) ∈ g := by
    obtain ⟨d,hd,hnd,_⟩ := hqf.2 (natSet n) ((mem_omega _).mpr ⟨n,rfl⟩)
    obtain ⟨x,hx,hdx⟩ := hgc d hd
    obtain ⟨a,ha,hda⟩ := (mem_idealSet I d).mp hd
    rw [hda] at hx
    obtain ⟨B,hxB,hBa⟩ := (mem_degreeSet a x).mp hx
    refine ⟨B,by simpa only [hBa] using ha,?_,?_,?_⟩
    · exact ZFSet.mem_sUnion.mpr ⟨d,hd,by simpa only [hda,←hxB] using hx⟩
    · simpa only [hda,←hBa] using hnd
    · simpa only [hda,hxB,←hBa] using hdx
  choose B hB using hex
  obtain ⟨p,hp,hpc⟩ := composition_mem C C.omega_mem hI hu hq hg
  have hseq : p = sequenceSet B := by
    apply ZFSet.ext
    intro z
    rw [hpc,mem_sequenceSet]
    constructor
    · rintro ⟨x,hx,d,hd,t,ht,hz,hxd,hdt⟩
      obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
      have hd' : d = degreeSet (degree (B n)) := hqf.unique
        ((mem_omega _).mpr ⟨n,rfl⟩) hd ((mem_idealSet I _).mpr ⟨_,(hB n).1,rfl⟩)
        hxd (hB n).2.2.1
      have ht' : t = realSet (B n) := hgf.unique hd ht (hB n).2.1 hdt
        (by simpa only [hd'] using (hB n).2.2.2)
      exact ⟨n,by rw [hz,ht']⟩
    · rintro ⟨n,rfl⟩
      exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,degreeSet (degree (B n)),
        (mem_idealSet I _).mpr ⟨_,(hB n).1,rfl⟩,realSet (B n),(hB n).2.1,rfl,
        (hB n).2.2.1,(hB n).2.2.2⟩
  have hBM (n : ℕ) : B n ∈ reals M := C.transitive u hu _ (hB n).2.1
  obtain ⟨r,hr,hrc⟩ := internal_reals M C.transitive C.power C.separation C.infinity
  let A : Oracle := fun v => B (Nat.unpair v).1 (Nat.unpair v).2
  have hAM : A ∈ reals M := flatten_mem M C.transitive C.pairing C.union C.power
    C.separation C.infinity hr hrc C.pairing_mem pairingSet_code B hBM (hseq ▸ hp)
  have hcol (n : ℕ) : columns A n = B n := by
    funext k
    simp only [columns,A,Nat.unpair_pair]
  refine ⟨A,hAM,?_⟩
  intro a
  constructor
  · intro ha
    obtain ⟨n,hn⟩ := hqo (degreeSet a) ((mem_idealSet I _).mpr ⟨a,ha,rfl⟩)
    have he := hqf.unique ((mem_omega _).mpr ⟨n,rfl⟩)
      ((mem_idealSet I _).mpr ⟨_,(hB n).1,rfl⟩) ((mem_idealSet I _).mpr ⟨a,ha,rfl⟩)
      (hB n).2.2.1 hn
    exact ⟨n,by rw [hcol]; exact degreeSet_injective he⟩
  · rintro ⟨n,hn⟩
    rw [hcol] at hn
    exact hn ▸ (hB n).1

theorem persistent_mem_of_countable (C : Context M) (hCh : InternalChoice M)
    (I : CountableIdeal) (hI : idealSet I ∈ M) (hct : InternallyCountable M (idealSet I))
    (ρ : I ≃o I) (hρ : Persistent I ρ)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier) :
    automorphismSet ρ ∈ M := by
  obtain ⟨A,hAM,hA⟩ := countable_presentation C hCh I hI hct
  exact (persistent_sets C hA hAM ρ hρ hz).2

end
end TuringRigidity.SetModelCountability

end OAI
