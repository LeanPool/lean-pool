/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenProjectedNameLift.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenProjectionSymmetry
public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenSupportedValue

/-!
# Cohen Projected Name Lift
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenProjectedNameLift
open RecursiveNames TransitiveNameModel BoundedSetTheory CountableForcing AtomicForcing
open CohenGroundPoset InternalCohenRestriction InternalCohenPartition InternalCohenProjectedGeneric
open InternalCohenProjectionSymmetry InternalCohenSupportedValue
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
attribute [local instance] CohenNiceNameConstruction.cohenTop

theorem lift_projected_real_name (M A B : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hA : A ∈ M) (hB : B ∈ M) (hBA : B ⊆ A)
    (τ : Name (Conditions (conditions B))) (hτ : τ.encode (label (conditions B)) ∈ M) :
    ∃ y : Name (Conditions (conditions A)), y.encode (label (conditions A)) ∈ M ∧
      (∀ G : GenericFilter (Conditions (conditions A)), GroundGeneric M G →
        τ.val (projected A B hBA G).carrier ⊆ ZFSet.omega →
          y.val G.carrier = τ.val (projected A B hBA G).carrier) ∧
      ∀ a : Conditions (conditions A) ≃o Conditions (conditions A),
        (∀ s, restrict B (label _ (a s)) = restrict B (label _ s)) →
        ∀ G : GenericFilter (Conditions (conditions A)),
          y.val (AutomorphismName.mapFilter a G).carrier = y.val G.carrier := by
  obtain ⟨E,hgraph,hE,_,_,hval⟩ :=
    CohenNiceNameConstruction.internal_nice_name M B hM hT hB τ hτ
  have hEB (n : ℕ) : E n ⊆ conditions B :=
    fun p hp => (ZFSet.mem_sep.mp ((hE n).2.1 hp)).1
  have hEA (n : ℕ) : E n ⊆ conditions A :=
    fun p hp => condition_mono A B p hBA (hEB n hp)
  let y : Name (Conditions (conditions A)) := InternalNiceName.nice E
  refine ⟨y,InternalNiceName.nice_internal M hM hT (conditions_mem M A hM hT hA) E
    (fun n => ⟨(hE n).1,hEA n⟩) hgraph,?_,?_⟩
  · intro G hG hreal
    exact (nice_value_projected A B hBA E hEB G).symm.trans
      (hval _ (projected_groundGeneric M A B hM hT hA hB hBA G hG) hreal)
  · intro a hfix G
    change (InternalNiceName.nice E : Name (Conditions (conditions A))).val _ = _
    rw [←nice_value_projected A B hBA E hEB (AutomorphismName.mapFilter a G),
      projected_carrier_fixed A B hBA a hfix G,nice_value_projected A B hBA E hEB G]

end TuringRigidity.CohenProjectedNameLift

end OAI
