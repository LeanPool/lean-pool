/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/OwnStageSourceTheory.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalInputSyntax

/-!
# Own Stage Source Theory
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel SentenceCoding SetModelFunctions
universe u

theorem seedBoundStage_sourceT (M x A : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (hx : x ∈ M) :
    SeedBoundStage M ZFSet.omega (ZFSet.prod ZFSet.omega ZFSet.omega)
      (groundReals M) x A ↔ A = stage (groundReals M) x := by
  let C : Context M :=
    ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  constructor
  · exact SeedBoundStage.sound hM
      (family_mem M hM hT.pairing hT.union C.omega_mem)
      (supportGraph_mem M hM hT.pairing hT.union C.omega_mem)
  · rintro rfl
    have hR := groundReals_mem M hM hT
    obtain ⟨d,hd,f,hf,hxd,hg⟩ := internal_hierarchy_cover M _ x hM hT hR hx
    exact ⟨seed (groundReals M),seed_mem M _ hM hT hR,d,hd,f,hf,_,
      iterUnion_mem M hM hT.union hf 2,ground_seed_shape M hM,hxd,
      (checkedHierarchyGraph_of_context M _ _ _ _ C).mpr hg,
      (hg.stageStep_iff x hxd _).mpr rfl⟩

theorem own_stage_sourceT_formula :
    ∃ s : SentenceForm, ∀ M : ZFSet.{u}, Transitive M → SourceT M →
      ∀ e : ℕ → ZFSet.{u}, (∀ i, e i ∈ M) →
        (s.Sat (M : Set ZFSet) e ↔ e 0 = stage (groundReals M) (e 1)) := by
  obtain ⟨p,hp⟩ := NumericSyntax.stage_formula.{u}
  refine ⟨ownStageFormula p,?_⟩
  intro M hM hT e he
  have hw := sourceT_omega_mem M hM hT
  have hR := groundReals_mem M hM hT
  have hsq := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hw hw
  obtain ⟨B,hB,hbound,_⟩ := internal_finite_natural_graph_bound M hM hT.pairing hT.union
    hT.powerSet hT.separation.finitePrefix.bounded hw
  have hf (r : ZFSet.{u}) (hr : r ∈ M) :
      (canonicalReals 0).Sat (M : Set ZFSet) (cons r e) ↔ r = groundReals M :=
    canonicalReals_spec M hM hw 0 _ (by
      intro i
      cases i
      · exact hr
      · exact he _)
  have hs : p.Sat (M : Set ZFSet) (cons (e 0) (cons (e 1) (fun _ => groundReals M))) ↔
      e 0 = stage (groundReals M) (e 1) := by
    rw [hp M hM hw hsq (finiteNaturalGraph_mem M hM hT.pairing hT.union hw)
      ⟨B,hB,hbound⟩ _ (by
        intro i
        rcases i with _|_|i
        · exact he 0
        · exact he 1
        · exact hR)]
    exact seedBoundStage_sourceT M _ _ hM hT (he 1)
  change (∃ r ∈ M, (canonicalReals 0).Sat _ (cons r e) ∧
    (p.rename _).Sat _ (cons r e)) ↔ _
  simp only [SentenceForm.sat_rename]
  constructor
  · rintro ⟨r,hr,h,hp⟩
    obtain rfl := (hf r hr).mp h
    apply hs.mp
    convert hp using 1
    funext i
    rcases i with _|_|i <;> rfl
  · intro h
    refine ⟨_,hR,(hf _ hR).mpr rfl,?_⟩
    convert hs.mpr h using 1
    funext i
    rcases i with _|_|i <;> rfl

end TuringRigidity.RelativeConstructible

end OAI
