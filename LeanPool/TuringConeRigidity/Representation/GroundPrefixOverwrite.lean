/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/GroundPrefixOverwrite.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.PrefixSingletonRealization
public import LeanPool.TuringConeRigidity.CohenForcing.CohenPrefixOverwrite

/-!
# Ground Prefix Overwrite
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.GroundPrefixOverwrite
open TransitiveNameModel BoundedSetTheory CountableForcing CohenColumnRealName
open FiniteOverwrite
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem overwrite_generic (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (A : Oracle) (hA : AtomicForcing.GroundGeneric M
      (InternalCohen.pushFilter (CohenBorelForcing.realFilter A))) (s : List Bool) :
    AtomicForcing.GroundGeneric M
      (InternalCohen.pushFilter (CohenBorelForcing.realFilter (overwrite s A))) := by
  have ha : natSet 0 ∈ M := hM _ (sourceT_omega_mem M hM hT) _
    ((mem_omega _).mpr ⟨0,rfl⟩)
  have hs := singleton_mem M hM hT.pairing ha
  have hm : natSet 0 ∈ ({natSet 0} : ZFSet.{0}) := ZFSet.mem_singleton.mpr rfl
  obtain ⟨J,hJ,_,hJA⟩ := PrefixSingletonRealization.singleton_realization M (natSet 0) hM hT ha A hA
  obtain ⟨hF,_,hFA⟩ := CohenFiniteFlip.prefixFilter_properties M {natSet 0} (natSet 0)
    hM hT hs hm s A J hJ hJA
  exact selected_real_prefix_generic M {natSet 0} (natSet 0) hM hT hs hm _ hF _ hFA

theorem overwrite_realizes (s : List Bool) (A : Oracle) :
    ShuffleRequirements.Realizes s (overwrite s A) :=
  fun n hn => (overwrite_below s A n hn).symm

end TuringRigidity.GroundPrefixOverwrite

end OAI
