/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/RelativeConstruction.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.FiniteRealPacking
public import LeanPool.TuringConeRigidity.Constructibility.RelativeModel

/-!
# Relative Construction
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open TransitiveNameModel BoundedSetTheory ElementaryModel
universe u

/-- Finite relative constructions from a real set, a real parameter, and definable subsets of
ordinal stages. -/
inductive Construction : Type (u + 1)
  | reals : Construction
  | parameter : Construction
  | define (o : Ordinal.{u}) (n : ℕ) (p : SentenceForm)
      (children : Fin n → Construction) : Construction

/-- Evaluate a relative construction using the real set and projected oracle parameters. -/
noncomputable def Construction.value (R : ZFSet.{u}) (P : Oracle) : Construction.{u} → ZFSet.{u}
  | .reals => R
  | .parameter => realCode P
  | .define o n p c => definedSubset (level R o) p
      (fun i : Fin n => (c i).value R (realPart P i))

/-- Certification of parameter membership, formula support bounds, and recursive membership of
child values in their defining stages. -/
def Construction.Certified (R : ZFSet.{u}) (P : Oracle) : Construction.{u} → Prop
  | .reals => True
  | .parameter => realCode P ∈ R
  | .define o n p c => p.bound ≤ n+1 ∧
      ∀ i, (c i).Certified R (realPart P i) ∧ (c i).value R (realPart P i) ∈ level R o

/-- Every ordinal stage used by the construction has its set code in `M`. -/
def Construction.Indexed (M : ZFSet.{u}) : Construction.{u} → Prop
  | .reals => True
  | .parameter => True
  | .define o _ _ c => o.toZFSet ∈ M ∧ ∀ i, (c i).Indexed M

theorem Construction.value_in_relativeL (t : Construction.{u}) (R : ZFSet.{u}) (P : Oracle)
    (ht : t.Certified R P) : InRelativeL R (t.value R P) := by
  cases t with
  | reals => exact parameter_in_relativeL R
  | parameter => exact relativeL_transitive R (parameter_in_relativeL R) ht
  | define o n p c =>
    refine ⟨o+1,?_⟩
    rw [level_succ,mem_definablePower]
    exact ⟨n,p,_,ht.1,fun i => (ht.2 i).2,rfl⟩

theorem Construction.value_in_relativeModel (t : Construction.{u}) (M R : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M) (P : Oracle)
    (ht : t.Certified R P) (hi : t.Indexed M) : InRelativeModel M R (t.value R P) := by
  cases t with
  | reals => exact parameter_in_relativeModel M R hM hT
  | parameter => exact (parameter_in_relativeModel M R hM hT).transitive ht
  | define o n p c =>
    refine ⟨o+1,internal_ordinal_succ M hM hT o hi.1,?_⟩
    rw [level_succ,mem_definablePower]
    exact ⟨n,p,_,ht.1,fun i => (ht.2 i).2,rfl⟩

theorem ground_seed_shape (M : ZFSet.{u}) (hM : Transitive M) :
    seed (groundReals M) = insert (groundReals M) (groundReals M) := by
  let R := groundReals M
  have htrans : Transitive (insert R R) := by
    intro a ha b hb
    rcases ZFSet.mem_insert_iff.mp ha with rfl|ha
    · exact ZFSet.mem_insert_iff.mpr (Or.inr hb)
    · obtain ⟨haM,haω⟩ := (mem_groundReals M a).mp ha
      have hbω := haω hb
      have hbsub : b ⊆ ZFSet.omega := fun z hz => omega_transitive b hbω z hz
      exact ZFSet.mem_insert_iff.mpr (Or.inr ((mem_groundReals M b).mpr ⟨hM a haM b hb,hbsub⟩))
  apply ZFSet.ext; intro x
  constructor
  · exact fun hx => seed_minimal R _ htrans (ZFSet.mem_insert R R) hx
  · intro hx
    rcases ZFSet.mem_insert_iff.mp hx with rfl|hx
    · exact parameter_mem_seed R
    · exact parameter_subset_seed R hx

theorem construction_of_level (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (o : Ordinal.{u}) (ho : o.toZFSet ∈ M) (x : ZFSet.{u})
    (hx : x ∈ level (groundReals M) o) :
    ∃ t : Construction.{u}, ∃ P : Oracle, P ∈ modelReals M ∧
      t.Indexed M ∧ t.Certified (groundReals M) P ∧ t.value (groundReals M) P = x := by
  induction o using WellFoundedLT.induction generalizing x with
  | ind o ih =>
    rcases (mem_stage (groundReals M) o.toZFSet x).mp hx with hx|⟨a,ha,hx⟩
    · rw [ground_seed_shape M hM] at hx
      rcases ZFSet.mem_insert_iff.mp hx with rfl|hx
      · exact ⟨.reals,FixedArithmetic.zero,sourceT_zero_real M hM hT,trivial,trivial,rfl⟩
      · obtain ⟨hxM,hxω⟩ := (mem_groundReals M x).mp hx
        have he := realCode_decodeReal hxω
        refine ⟨.parameter,decodeReal x,?_,trivial,?_,he⟩
        · change realCode (decodeReal x) ∈ M
          rwa [he]
        · change realCode (decodeReal x) ∈ groundReals M
          rwa [he]
    · obtain ⟨a,hao,rfl⟩ := Ordinal.mem_toZFSet_iff.mp ha
      obtain ⟨n,p,v,hb,hv,rfl⟩ := (mem_definablePower _ x).mp hx
      have hc (i : Fin n) := ih a hao (hM _ ho _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr hao))
        (v i) (hv i)
      choose c Q hQ hi ht he using hc
      refine ⟨.define a n p c,packedReal Q,packedReal_internal M hM hT Q hQ,
        ⟨hM _ ho _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr hao),hi⟩,?_,?_⟩
      · refine ⟨hb,fun i => ?_⟩
        rw [realPart_packed]
        exact ⟨ht i,(he i).symm ▸ hv i⟩
      · change definedSubset _ p _ = definedSubset _ p v
        congr 1
        funext i
        rw [realPart_packed,he]

theorem construction_of_relativeModel (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (x : ZFSet.{u}) (hx : x ∈ relativeModel M (groundReals M)) :
    ∃ t : Construction.{u}, ∃ P : Oracle, P ∈ modelReals M ∧
      t.Indexed M ∧ t.Certified (groundReals M) P ∧ t.value (groundReals M) P = x := by
  obtain ⟨_,o,ho,hx⟩ := ZFSet.mem_sep.mp hx
  exact construction_of_level M hM hT o ho x hx

end TuringRigidity.RelativeConstructible

end OAI
