/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenColumnPrefixCone.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenColumnRealValue

/-!
# Cohen Column Prefix Cone
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenColumnRealName
open Set TransitiveNameModel BoundedSetTheory CountableForcing
open CohenGroundPoset InternalCohenProjectedGeneric InternalCohenFactor
open InternalCohen (bitSet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder
  CohenNiceNameConstruction.cohenTop

theorem finite_column_bound (K a : ZFSet.{0}) (p : Conditions (poset K)) :
    ∃ N : ℕ, ∀ n b,
      ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b) ∈ label _ p → n < N := by
  have hfin := ((InternalFiniteSubsets.mem_finiteSubsets_iff _ _).mp
    ((mem_conditions (ZFSet.prod K ZFSet.omega) _).mp (label_mem _ p)).1).2
  let f (b : Bool) (n : ℕ) := ZFSet.pair (ZFSet.pair a (natSet n)) (bitSet b)
  have hi (b : Bool) : Function.Injective (f b) := by
    intro n m he
    exact natSet_injective (ZFSet.pair_inj.mp (ZFSet.pair_inj.mp he).1).2
  have hs := (hfin.preimage (hi false).injOn).union (hfin.preimage (hi true).injOn)
  obtain ⟨N,hN⟩ := hs.bddAbove
  refine ⟨N+1,fun n b hn => Nat.lt_succ_of_le (hN ?_)⟩
  cases b
  · exact Or.inl hn
  · exact Or.inr hn

theorem selected_prefix_cone (M K a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (ha : a ∈ K)
    (G : GenericFilter (Conditions (poset K))) (hG : AtomicForcing.GroundGeneric M G)
    (p : Conditions (poset K)) (hp : p ∈ G.carrier) :
    let C := ZFSet.prod K ZFSet.omega
    let B := ZFSet.prod {a} ZFSet.omega
    let hBC := singleton_coordinates_subset K a ha
    ∃ A : Oracle, (realName K a).val G.carrier = realCode A ∧ ∃ N : ℕ,
      ∀ H : GenericFilter (Conditions (poset K)), AtomicForcing.GroundGeneric M H →
      ∀ A' : Oracle, (realName K a).val H.carrier = realCode A' →
        (∀ n < N, A' n = A n) → project C B hBC p ∈ (projected C B hBC H).carrier := by
  intro C B hBC
  obtain ⟨A,_,hval,_,hfilter⟩ := projected_real_value M K a hM hT hK ha G hG
  obtain ⟨N,hN⟩ := finite_column_bound {a} a (project C B hBC p)
  have hpA := (hfilter _).mp (projected_contains C B hBC G hp)
  refine ⟨A,hval,N,fun H hH A' hval' hprefix => ?_⟩
  obtain ⟨AH,_,hvalH,_,hfilterH⟩ := projected_real_value M K a hM hT hK ha H hH
  have he : AH = A' := realCode_injective (hvalH.symm.trans hval')
  subst AH
  apply (hfilterH _).mpr
  intro n b hb
  exact (hprefix n (hN n b hb)).trans (hpA n b hb)

end TuringRigidity.CohenColumnRealName

end OAI
