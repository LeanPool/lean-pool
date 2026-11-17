/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/ModelReals.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ModelNaturalNumbers

/-!
# Model Reals
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel
universe u

/-- The subset of omega whose numeral members correspond to true bits of the oracle. -/
noncomputable def realCode (A : Oracle) : ZFSet.{u} :=
  ZFSet.sep (fun x => ∃ n, x = natSet n ∧ A n = true) ZFSet.omega

theorem realCode_subset (A : Oracle) : realCode.{u} A ⊆ ZFSet.omega :=
  fun _ hx => (ZFSet.mem_sep.mp hx).1

theorem natSet_mem_realCode (A : Oracle) (n : ℕ) : natSet.{u} n ∈ realCode A ↔ A n = true := by
  rw [realCode,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,m,he,hm⟩
    have hnm := natSet_injective he
    exact hnm.symm ▸ hm
  · intro hn
    exact ⟨(mem_omega _).mpr ⟨n,rfl⟩,n,rfl,hn⟩

/-- The Boolean oracle whose true positions are the numerals belonging to the set. -/
noncomputable def decodeReal (x : ZFSet.{u}) : Oracle := fun n => by
  classical
  exact decide (natSet n ∈ x)

theorem decodeReal_true (x : ZFSet.{u}) (n : ℕ) : decodeReal x n = true ↔ natSet n ∈ x := by
  classical
  simp only [decodeReal,decide_eq_true_eq]

theorem realCode_decodeReal {x : ZFSet.{u}} (hx : x ⊆ ZFSet.omega) : realCode (decodeReal x) = x
  := by
  apply ZFSet.ext; intro z
  by_cases hz : z ∈ ZFSet.omega.{u}
  · obtain ⟨n,rfl⟩ := (mem_omega z).mp hz
    rw [natSet_mem_realCode,decodeReal_true]
  · exact ⟨fun h => False.elim (hz (realCode_subset _ h)),fun h => False.elim (hz (hx h))⟩

theorem realCode_injective : Function.Injective (realCode.{u}) := by
  intro A B he
  funext n
  have h : A n = true ↔ B n = true := by
    rw [←natSet_mem_realCode.{u} A n,←natSet_mem_realCode.{u} B n,he]
  cases ha : A n <;> cases hb : B n <;> simp_all

theorem decodeReal_realCode (A : Oracle) : decodeReal (realCode.{u} A) = A :=
  realCode_injective (realCode_decodeReal (realCode_subset A))

/-- The oracles whose real codes belong to the model. -/
def modelReals (M : ZFSet.{u}) : Set Oracle := {A | realCode A ∈ M}

theorem internal_real_power (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    ∃ R ∈ M, (∀ A : Oracle, realCode A ∈ R ↔ A ∈ modelReals M) ∧
      ∀ x ∈ R, ∃ A ∈ modelReals M, realCode A = x := by
  obtain ⟨R,hR,hRdef⟩ := internal_power M hM hT.powerSet (sourceT_omega_mem M hM hT)
  refine ⟨R,hR,?_,?_⟩
  · intro A
    rw [hRdef]
    exact and_iff_left (realCode_subset A)
  · intro x hx
    have hxm := ((hRdef x).mp hx).1
    have he := realCode_decodeReal ((hRdef x).mp hx).2
    refine ⟨decodeReal x,?_,he⟩
    change realCode (decodeReal x) ∈ M
    rw [he]
    exact hxm

end TuringRigidity.BoundedSetTheory

end OAI
