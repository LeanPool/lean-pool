/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/AmbientExtensionBody.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.AmbientDegreeActual
public import LeanPool.TuringConeRigidity.SetModels.ElementaryModelIdeal
public import LeanPool.TuringConeRigidity.Representation.AmbientDegreeBinding
public import LeanPool.TuringConeRigidity.Representation.SourceTTreeAbsoluteness
public import LeanPool.TuringConeRigidity.SetModels.SetModelActionDecoding

/-!
# Ambient Extension Body
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.FullSetForcing
open BoundedSetTheory TransitiveNameModel ElementaryModel SentenceForm
open SetDegreeDecoding PersistentRestrictions SetModelSatisfaction ArithmeticTree
universe u

theorem ownDegreeUniverse_eq_idealSet (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M) (R : ZFSet.{u})
    (hR : ∀ x, x ∈ R ↔ x ∈ M ∧ x ⊆ ZFSet.omega) :
    degreeUniverse R = idealSet (modelIdeal M hM hT) := by
  apply ZFSet.ext
  intro x
  rw [ownDegreeUniverse_actual M hM hT R hR, mem_idealSet]
  constructor
  · rintro ⟨A,hA,rfl⟩
    exact ⟨degree A,⟨A,hA,rfl⟩,rfl⟩
  · rintro ⟨d,⟨A,hA,rfl⟩,rfl⟩
    exact ⟨A,hA,rfl⟩

/-- A full formula defining a degree action extending the specified source and target
parameters. -/
noncomputable def extensionBody (eqf lef : Formula) : SentenceForm :=
  .conj (degreeSetup eqf lef)
    (fromBounded (.conj (actionFormula 8 1 0)
      (.conj (.subset 4 1) (.subset 5 8))))

theorem extensionBody_spec {eqf lef : Formula} (heq : DegreeEqualityFormula.{u} eqf)
    (hle : DegreeOrderFormula.{u} lef)
    (M : ZFSet.{u}) [Countable (Conditions M)] (hM : Transitive M) (hT : SourceT M)
    (I : CountableIdeal) (ρ : I ≃o I)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (hi : e 4 = idealSet I) (hρ : e 5 = automorphismSet ρ)
    (ho : e 6 = ZFSet.omega) (hz : e 7 = natSet 0) :
    (extensionBody eqf lef).Sat (M : Set ZFSet) e ↔
      (degreeSetup eqf lef).Sat (M : Set ZFSet) e ∧
      ∃ hIJ : I.carrier ⊆ (modelIdeal M hM hT).carrier,
        ∃ σ : modelIdeal M hM hT ≃o modelIdeal M hM hT,
          automorphismSet σ = e 8 ∧ Extends hIJ ρ σ := by
  change (_ ∧ _) ↔ (_ ∧ _)
  apply and_congr_right
  intro hs
  obtain ⟨hR,_,hD,hL⟩ := (degreeSetup_spec heq hle M hM hT e he ho hz).mp hs
  have hd : e 1 = idealSet (modelIdeal M hM hT) :=
    hD.trans (ownDegreeUniverse_eq_idealSet M hM hT (e 3) hR)
  have hl := ownDegreeOrder_actual M hM hT (e 3) hR
  rw [←hL] at hl
  rw [bounded_sat, Formula.absolute _ M hM e he]
  simp only [Formula.Eval, eval_actionFormula, Formula.eval_subset, hi, hρ, hd]
  constructor
  · rintro ⟨ha,hij,hext⟩
    have hij' := ideal_subset_iff.mp hij
    obtain ⟨σ,hσ⟩ := decode_action (sourceContext M hM hT) hl
      (modelIdeal M hM hT) (hd ▸ he 1) ha
    refine ⟨hij',σ,hσ,(extends_sets_iff hij' ρ σ).mp ?_⟩
    rwa [hσ]
  · rintro ⟨hij,σ,hσ,hext⟩
    rw [←hσ]
    exact ⟨action_satisfaction (sourceContext M hM hT) hl (hd ▸ he 1) σ,
      ideal_subset hij, extends_sets hext⟩

end TuringRigidity.FullSetForcing

end OAI
