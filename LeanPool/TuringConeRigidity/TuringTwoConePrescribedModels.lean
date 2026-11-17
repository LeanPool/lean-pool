/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringTwoConePrescribedModels.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringTwoConeForcingDefinition
public import LeanPool.TuringConeRigidity.TuringTwoConeLocality
public import LeanPool.TuringConeRigidity.Representation.ParameterCoveringModels

/-!
# Prescribed models for arbitrary global two-cone maps

The global map need not be an internal set parameter. Include representatives
of its two locality anchors e(a') and e^{-1}(b') instead. The model ideal is
then invariant and the actual restriction is persistent. Its entire graph
belongs to the model's relative L(R), not just an arbitrarily chosen extension.
-/


@[expose] public section

namespace OAI.TuringRigidity.TwoConePrescribedModels

open BoundedSetTheory TransitiveNameModel ElementaryModel IdealInterpretation
open PersistentRestrictions OracleJump TwoConeLocality TwoConeSetGraphs
open RelativeConstructible
open ConePersistence (Cone)

universe u
noncomputable section

/-- Locality gives the persistent restriction of this very global map, and
descent puts its native graph in the model's relative constructible universe. -/
theorem model_restriction_of_anchors {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    (M : ZFSet.{u}) [Countable (Conditions M)] (hM : Transitive M) (hT : SourceT M)
    (hpost : forwardAnchor e ∈ (modelIdeal M hM hT).carrier)
    (hpre : inverseAnchor e ∈ (modelIdeal M hM hT).carrier) :
    ∃ ρ : Cone (modelIdeal M hM hT) a ≃o Cone (modelIdeal M hM hT) b,
      TwoConePersistence.RestrictsTo e (modelIdeal M hM hT) ρ ∧
      TwoConePersistence.Persistent (modelIdeal M hM hT) ρ ∧
      coneGraph ρ ∈ relativeModel M (groundReals M) := by
  obtain ⟨ρ, he, hp⟩ := global_jump_restriction e (modelIdeal M hM hT)
    (modelIdeal_jump M hM hT) hpost hpre
  have ha : a ∈ (modelIdeal M hM hT).carrier :=
    (modelIdeal M hM hT).lower (Set.mem_Ici.mp (e.symm (jumpPoint b)).property) hpre
  have hb : b ∈ (modelIdeal M hM hT).carrier :=
    (modelIdeal M hM hT).lower (Set.mem_Ici.mp (e (jumpPoint a)).property) hpost
  exact ⟨ρ, he, hp,
    TwoConeConstructibleExtension.persistent_modelIdeal_graph_mem_relativeModel
      M hM hT ρ hp ha hb⟩

/-- Cover any prescribed countable sequence of inputs, with no definability
assumption on the global isomorphism and no model-existence hypothesis. -/
theorem prescribed_covering_model {a b : Degree} (e : Set.Ici a ≃o Set.Ici b)
    (W : ℕ → Oracle) :
    ∃ M : ZFSet.{u}, ∃ hM : Transitive M, ∃ hT : SourceT M,
      ∃ hcount : Countable (Conditions M),
        letI := hcount
        (∀ n, W n ∈ modelReals M) ∧
          ∃ ρ : Cone (modelIdeal M hM hT) a ≃o Cone (modelIdeal M hM hT) b,
            TwoConePersistence.RestrictsTo e (modelIdeal M hM hT) ρ ∧
            TwoConePersistence.Persistent (modelIdeal M hM hT) ρ ∧
            coneGraph ρ ∈ relativeModel M (groundReals M) := by
  obtain ⟨B, hB⟩ := degree_surjective (forwardAnchor e)
  obtain ⟨C, hC⟩ := degree_surjective (inverseAnchor e)
  let S : ℕ → Oracle
    | 0 => B
    | 1 => C
    | n + 2 => W n
  obtain ⟨M, hM, hT, hcount, hS⟩ := parameter_covering_models.{u} S
  let := hcount
  have hpost : forwardAnchor e ∈ (modelIdeal M hM hT).carrier := ⟨B, hS 0, hB⟩
  have hpre : inverseAnchor e ∈ (modelIdeal M hM hT).carrier := ⟨C, hS 1, hC⟩
  exact ⟨M, hM, hT, hcount, (fun n => hS (n + 2)),
    model_restriction_of_anchors e M hM hT hpost hpre⟩

end
end OAI.TuringRigidity.TwoConePrescribedModels
