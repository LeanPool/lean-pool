/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/SetModelPersistentSatisfaction.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.SetModelActionSatisfaction
public import LeanPool.TuringConeRigidity.SetModels.SetModelCountableExtensions

/-!
# Set Model Persistent Satisfaction
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SetModelSatisfaction
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions SetModelSyntax
open SetDegreeDecoding PersistentRestrictions SetModelCountability
universe u
noncomputable section

/-- Internal set-theoretic syntax extending bounded formulas by Boolean operations and set
quantification. -/
inductive InternalFormula where
  | bounded (p : Formula)
  | conj (p q : InternalFormula)
  | neg (p : InternalFormula)
  | existsSet (p : InternalFormula)

/-- Interpret internal syntax with set quantifiers restricted to members of `M`. -/
def InternalFormula.Realize (M : ZFSet.{u}) (e : ℕ → ZFSet.{u}) : InternalFormula → Prop
  | .bounded p => p.Realize M e
  | .conj p q => p.Realize M e ∧ q.Realize M e
  | .neg p => ¬ p.Realize M e
  | .existsSet p => ∃ x ∈ M, p.Realize M (cons x e)

/-- Bounded universal quantification within internal formula syntax. -/
def InternalFormula.allMem (i : ℕ) (p : InternalFormula) : InternalFormula :=
  .neg (.existsSet (.conj (.bounded (.member 0 (i+1))) (.neg p)))

@[simp] theorem InternalFormula.realize_allMem (i : ℕ) (p : InternalFormula)
    (M : ZFSet.{u}) (e : ℕ → ZFSet.{u}) :
    (InternalFormula.allMem i p).Realize M e ↔
      ∀ x ∈ M, x ∈ e i → p.Realize M (cons x e) := by
  classical
  simp [InternalFormula.allMem,InternalFormula.Realize,Formula.Realize]

/-- The bounded matrix describing an enumerated ideal extension and its extending action
graph. -/
def persistenceMatrix : Formula :=
  .conj (idealFormula 2 4 5) (.conj (ontoFormula 0 8 2)
    (.conj (actionFormula 1 2 5) (.conj (.subset 6 2)
      (.conj (.subset 7 1) (.member 3 2)))))

/-- The internal formula asserting a suitable extension witness for every degree-universe
element. -/
def persistenceFormula : InternalFormula :=
  .allMem 0 (.existsSet (.existsSet (.existsSet (.bounded persistenceMatrix))))

variable {M : ZFSet.{u}}

theorem persistent_satisfaction (C : Context M) (hCh : InternalChoice M)
    {D L : ZFSet.{u}} (hDM : D ∈ M) (hLM : L ∈ M)
    (hD : ∀ x, x ∈ D ↔ ∃ A ∈ reals M, x = degreeSet (degree A))
    (hL : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (degreeSet (degree A)) (degreeSet (degree B)) ∈ L ↔ Reduces A B)
    (I : CountableIdeal) (hI : idealSet I ∈ M) (hct : InternallyCountable M (idealSet I))
    (ρ : I ≃o I) (hρ : Persistent I ρ)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier) :
    persistenceFormula.Realize M (cons D (cons L (cons (idealSet I)
      (cons (automorphismSet ρ) (fun _ => ZFSet.omega))))) := by
  have hρM := persistent_mem_of_countable C hCh I hI hct ρ hρ hz
  rw [persistenceFormula,InternalFormula.realize_allMem]
  intro x hxM hxD
  obtain ⟨X,hX,rfl⟩ := (hD x).mp hxD
  obtain ⟨J,σ,hIJ,hXJ,he,hσ,hJM,hσM,hctJ⟩ :=
    persistent_countable_extensions C hCh I hI hct ρ hρ hz hX
  obtain ⟨c,hc,hcc⟩ := hctJ
  have hec : ∀ i, cons c (cons ZFSet.omega (fun _ => idealSet J)) i ∈ M := by
    intro i
    rcases i with _|_|i <;> simp [hc,C.omega_mem,hJM]
  have honto := ((ontoFormula 0 1 2).absolute M C.transitive _ hec).mp hcc
  rw [eval_ontoFormula] at honto
  refine ⟨idealSet J,hJM,automorphismSet σ,hσM,c,hc,?_⟩
  change persistenceMatrix.Realize M _
  let e := cons c (cons (automorphismSet σ) (cons (idealSet J)
    (cons (degreeSet (degree X)) (cons D (cons L (cons (idealSet I)
      (cons (automorphismSet ρ) (fun _ => ZFSet.omega))))))))
  have heM : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|_|_|_|_|_|_|i <;>
      simp [e,hc,hσM,hJM,hxM,hDM,hLM,hI,hρM,C.omega_mem]
  apply (persistenceMatrix.absolute M C.transitive e heM).mpr
  simp only [persistenceMatrix,Formula.Eval,eval_idealFormula,eval_ontoFormula,
    eval_actionFormula,Formula.eval_subset,cons_zero,cons_succ,e]
  exact ⟨ideal_satisfaction C hD hL J hJM,honto,action_satisfaction C hL hJM σ,
    ideal_subset hIJ,extends_sets he,(mem_idealSet J _).mpr ⟨_,hXJ,rfl⟩⟩

theorem source_4_2_5_transitive (C : Context M) (hCh : InternalChoice M)
    (I : CountableIdeal) (hI : idealSet I ∈ M) (hct : InternallyCountable M (idealSet I))
    (ρ : I ≃o I) (hρ : Persistent I ρ)
    (hz : degree (OracleJump.jump FixedArithmetic.zero) ∈ I.carrier) :
    ∃ D ∈ M, ∃ L ∈ M,
      (∀ x, x ∈ D ↔ ∃ A ∈ reals M, x = degreeSet (degree A)) ∧
      (∀ A ∈ reals M, ∀ B ∈ reals M,
        ZFSet.pair (degreeSet (degree A)) (degreeSet (degree B)) ∈ L ↔ Reduces A B) ∧
      automorphismSet ρ ∈ M ∧
      persistenceFormula.Realize M (cons D (cons L (cons (idealSet I)
        (cons (automorphismSet ρ) (fun _ => ZFSet.omega))))) := by
  obtain ⟨D,hDM,hD⟩ := degree_universe C
  obtain ⟨L,hLM,hL⟩ := degree_order C
  exact ⟨D,hDM,L,hLM,hD,hL,persistent_mem_of_countable C hCh I hI hct ρ hρ hz,
    persistent_satisfaction C hCh hDM hLM hD hL I hI hct ρ hρ hz⟩

end
end TuringRigidity.SetModelSatisfaction

end OAI
