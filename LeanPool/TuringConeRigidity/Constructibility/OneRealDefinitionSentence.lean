/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/OneRealDefinitionSentence.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.OwnStageSourceTheory
public import LeanPool.TuringConeRigidity.Syntax.SetSatisfactionBounded

/-!
# One Real Definition Sentence
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceForm
universe u

noncomputable def modelRealSentence (i : ℕ) : SentenceForm :=
  .ex (.conj (canonicalReals 0) (.member (i+1) 0))

theorem modelRealSentence_spec (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (i : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ j, e j ∈ M) :
    (modelRealSentence i).Sat (M : Set ZFSet) e ↔ e i ∈ groundReals M := by
  have hR := groundReals_mem M hM hT
  have hf (r : ZFSet.{u}) (hr : r ∈ M) := canonicalReals_spec M hM
    (sourceT_omega_mem M hM hT) 0 (cons r e)
    (by
      intro j
      cases j
      · exact hr
      · exact he _)
  change (∃ r ∈ M, (canonicalReals 0).Sat _ (cons r e) ∧ e i ∈ r) ↔ _
  constructor
  · rintro ⟨r,hr,h,hx⟩
    obtain rfl := (hf r hr).mp h
    exact hx
  · intro h
    exact ⟨_,hR,(hf _ hR).mpr rfl,h⟩

noncomputable def oneRealGraphSentence (s p : SentenceForm) : SentenceForm :=
  .ex (.conj (s.rename (fun i => if i = 0 then 0 else 2))
    (.conj (.member 3 0)
      (FullSetForcing.definedSet 1 (.conj (.member 0 1)
        (setBounded p 1 (fun i => if i = 0 then 0 else 4))))))

theorem oneRealGraphSentence_spec (s p : SentenceForm) (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M)
    (hs : ∀ e : ℕ → ZFSet.{u}, (∀ i, e i ∈ M) →
      (s.Sat (M : Set ZFSet) e ↔ e 0 = stage (groundReals M) (e 1)))
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    (oneRealGraphSentence s p).Sat (M : Set ZFSet) e ↔
      e 2 ∈ stage (groundReals M) (e 1) ∧
      e 0 = definedSubset (stage (groundReals M) (e 1)) p
        (fun _ : Fin p.bound => e 2) := by
  have hc (A : ZFSet.{u}) (hA : A ∈ M) : ∀ i, cons A e i ∈ M := by
    intro i
    cases i
    · exact hA
    · exact he _
  have hstage (A : ZFSet.{u}) (hA : A ∈ M) :
      (s.rename (fun i => if i = 0 then 0 else 2)).Sat (M : Set ZFSet) (cons A e) ↔
        A = stage (groundReals M) (e 1) := by
    rw [sat_rename,hs _ (fun i => hc A hA _)]; rfl
  have hdef (A : ZFSet.{u}) (hA : A ∈ M) (hP : e 2 ∈ A) :
      (FullSetForcing.definedSet 1 (.conj (.member 0 1)
        (setBounded p 1 (fun i => if i = 0 then 0 else 4)))).Sat
          (M : Set ZFSet) (cons A e) ↔
        e 0 = definedSubset A p (fun _ : Fin p.bound => e 2) := by
    apply FullSetForcing.definedSet_unique M hM _ _ _ (hc A hA) _
      (definedSubset_mem M A hM hT.separation.finitePrefix.bounded hA p
        (fun _ => e 2) (fun _ => hP) (by omega))
    intro x _
    rw [Formula.Eval,setBounded_eval,mem_definedSubset]
    apply and_congr_right; intro _
    apply p.finite_support
    intro i hi
    rcases i with _|i
    · rfl
    · change e 2 = tupleEnv (fun _ : Fin p.bound => e 2) i
      simp only [tupleEnv,dite_eq_left (show i < p.bound by omega)]
  change (∃ A ∈ M, (s.rename _).Sat _ (cons A e) ∧ e 2 ∈ A ∧
    (FullSetForcing.definedSet _ _).Sat _ (cons A e)) ↔ _
  constructor
  · rintro ⟨A,hA,h,hP,hf⟩
    obtain rfl := (hstage A hA).mp h
    exact ⟨hP,(hdef _ hA hP).mp hf⟩
  · rintro ⟨hP,hf⟩
    have hA := stage_mem M _ _ hM hT (groundReals_mem M hM hT) (he 1)
    exact ⟨_,hA,(hstage _ hA).mpr rfl,hP,(hdef _ hA hP).mpr hf⟩

noncomputable def oneRealSentence (s p : SentenceForm) : SentenceForm :=
  .conj (fromBounded (ordinalFormula 1))
    (.conj (modelRealSentence 2) (oneRealGraphSentence s p))

theorem oneRealSentence_spec (s p : SentenceForm) (M : ZFSet.{u})
    (hM : Transitive M) (hT : SourceT M)
    (hs : ∀ e : ℕ → ZFSet.{u}, (∀ i, e i ∈ M) →
      (s.Sat (M : Set ZFSet) e ↔ e 0 = stage (groundReals M) (e 1)))
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    (oneRealSentence s p).Sat (M : Set ZFSet) e ↔
      (e 1).IsOrdinal ∧ e 2 ∈ groundReals M ∧
      e 2 ∈ stage (groundReals M) (e 1) ∧
      e 0 = definedSubset (stage (groundReals M) (e 1)) p
        (fun _ : Fin p.bound => e 2) := by
  change (_ ∧ _ ∧ _) ↔ _
  rw [bounded_sat,Formula.absolute _ M hM e he,eval_ordinalFormula,
    modelRealSentence_spec M hM hT 2 e he,oneRealGraphSentence_spec s p M hM hT hs e he]

end TuringRigidity.RelativeConstructible

end OAI
