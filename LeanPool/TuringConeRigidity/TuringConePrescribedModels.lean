/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringConePrescribedModels.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConeForcingDefinition
public import LeanPool.TuringConeRigidity.Representation.GlobalJumpRestriction
public import LeanPool.TuringConeRigidity.Representation.ParameterCoveringModels

/-!
# Prescribed models for an arbitrary global cone map

The two locality anchors are the image of 0' and the preimage of a'. A jump
ideal containing these two degrees is invariant under the global cone map.
Thus a parameter-covering model need only contain representatives of those
anchors, not the arbitrary global map as a set parameter.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConePrescribedModels

open BoundedSetTheory TransitiveNameModel ElementaryModel IdealInterpretation
open PersistentRestrictions OracleJump ConePersistence ConeSetGraphs
open RelativeConstructible

universe u
noncomputable section

def fullConeEquiv (a : Degree) : Set.Ici a ≃o Set.Ici (PersistentLocality.fullEquiv a) where
  toFun x := ⟨PersistentLocality.fullEquiv x.val, x.property⟩
  invFun y := ⟨y.val.val, y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

/-- No definability of the global map, and no assumed invariance of the
prescribed jump ideal, is needed. -/
theorem global_jump_restriction {a : Degree} (e : Degree ≃o Set.Ici a)
    (J : CountableIdeal) (hjump : IdealLocality.JumpClosed (PersistentLocality.ideal J))
    (hpost : (e (degree (jump FixedArithmetic.zero))).val ∈ J.carrier)
    (hpre : e.symm ⟨degreeJump a, Set.mem_Ici.mpr (degree_le_jump a)⟩ ∈ J.carrier) :
    ∃ ρ : J ≃o Cone J a,
      ConePersistence.RestrictsTo e J ρ ∧ ConePersistence.Persistent J ρ := by
  let τ := PersistentLocality.fullEquiv.symm.trans (e.trans (fullConeEquiv a))
  let z₀ : PersistentLocality.fullIdeal :=
    PersistentLocality.fullEquiv (degree (jump FixedArithmetic.zero))
  let z₁ : Set.Ici (PersistentLocality.fullEquiv a) :=
    ⟨PersistentLocality.fullEquiv (degreeJump a), Set.mem_Ici.mpr (degree_le_jump a)⟩
  have haJ : a ∈ J.carrier :=
    J.lower (Set.mem_Ici.mp (e (degree (jump FixedArithmetic.zero))).property) hpost
  obtain ⟨σ, hσ⟩ := ConeIdealLocality.restrict_jump_ideal τ z₀ rfl z₁ rfl
    (J := PersistentLocality.ideal J) (fun _ _ => Set.mem_univ _) haJ hjump hpost hpre
  let ρ := ConePersistentLocality.unlift haJ σ
  have hρ : ConePersistence.RestrictsTo e J ρ := by
    intro x
    exact (hσ ⟨x.val, x.property⟩).symm
  exact ⟨ρ, hρ, ConePersistence.persistent_of_global_restriction e J ρ hρ⟩

/-- A model containing the two anchors has a persistent restriction whose
entire graph is in its relative constructible model over its reals. -/
theorem model_restriction_of_anchors {a : Degree} (e : Degree ≃o Set.Ici a)
    (M : ZFSet.{u}) [Countable (Conditions M)] (hM : Transitive M) (hT : SourceT M)
    (hpost : (e (degree (jump FixedArithmetic.zero))).val ∈ (modelIdeal M hM hT).carrier)
    (hpre : e.symm ⟨degreeJump a, Set.mem_Ici.mpr (degree_le_jump a)⟩ ∈
      (modelIdeal M hM hT).carrier) :
    ∃ ρ : modelIdeal M hM hT ≃o Cone (modelIdeal M hM hT) a,
      ConePersistence.RestrictsTo e (modelIdeal M hM hT) ρ ∧
      ConePersistence.Persistent (modelIdeal M hM hT) ρ ∧
      coneGraph ρ ∈ relativeModel M (groundReals M) := by
  obtain ⟨ρ, he, hp⟩ := global_jump_restriction e (modelIdeal M hM hT)
    (modelIdeal_jump M hM hT) hpost hpre
  exact ⟨ρ, he, hp,
    ConeConstructibleExtension.persistent_modelIdeal_graph_mem_relativeModel M hM hT ρ hp⟩

/-- Cover any prescribed countable sequence of real inputs and obtain the
required persistent restriction of the arbitrary global cone isomorphism. -/
theorem prescribed_covering_model {a : Degree} (e : Degree ≃o Set.Ici a) (W : ℕ → Oracle) :
    ∃ M : ZFSet.{u}, ∃ hM : Transitive M, ∃ hT : SourceT M,
      ∃ hcount : Countable (Conditions M),
        letI := hcount
        (∀ n, W n ∈ modelReals M) ∧
          ∃ ρ : modelIdeal M hM hT ≃o Cone (modelIdeal M hM hT) a,
            ConePersistence.RestrictsTo e (modelIdeal M hM hT) ρ ∧
            ConePersistence.Persistent (modelIdeal M hM hT) ρ ∧
            coneGraph ρ ∈ relativeModel M (groundReals M) := by
  obtain ⟨B, hB⟩ := degree_surjective (e (degree (jump FixedArithmetic.zero))).val
  obtain ⟨C, hC⟩ := degree_surjective
    (e.symm ⟨degreeJump a, Set.mem_Ici.mpr (degree_le_jump a)⟩)
  let S : ℕ → Oracle
    | 0 => B
    | 1 => C
    | n + 2 => W n
  obtain ⟨M, hM, hT, hcount, hS⟩ := parameter_covering_models.{u} S
  let := hcount
  have hpost : (e (degree (jump FixedArithmetic.zero))).val ∈ (modelIdeal M hM hT).carrier :=
    ⟨B, hS 0, hB⟩
  have hpre : e.symm ⟨degreeJump a, Set.mem_Ici.mpr (degree_le_jump a)⟩ ∈
      (modelIdeal M hM hT).carrier := ⟨C, hS 1, hC⟩
  exact ⟨M, hM, hT, hcount, (fun n => hS (n + 2)),
    model_restriction_of_anchors e M hM hT hpost hpre⟩

end
end OAI.TuringRigidity.ConePrescribedModels
