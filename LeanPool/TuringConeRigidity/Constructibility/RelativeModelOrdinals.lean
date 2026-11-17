/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/RelativeModelOrdinals.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.RelativeModelPower
public import LeanPool.TuringConeRigidity.Constructibility.RelativeSigmaSchemas

/-!
# Relative Model Ordinals
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel InternalRank
universe u

theorem level_rank_lower_bound (R : ZFSet.{u}) (o : Ordinal.{u}) : o ≤ (level R o).rank := by
  induction o using Ordinal.lt_wf.induction with
  | ind o ih =>
    by_contra h
    have hlt : (level R o).rank < o := lt_of_not_ge h
    have hmem := level_mem_level R hlt
    exact (not_le_of_gt (ZFSet.rank_lt_of_mem hmem)) (ih _ hlt)

theorem ground_relativeModel_ordinal_iff (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (o : Ordinal.{u}) :
    o.toZFSet ∈ relativeModel M (groundReals M) ↔ o.toZFSet ∈ M := by
  constructor
  · intro ho; exact relativeModel_subset M (groundReals M) ho
  · intro ho
    let R := groundReals M
    let N := relativeModel M R
    have hR := groundReals_mem M hM hT
    have hN := relativeModel_transitive M R hM
    have hs := internal_ordinal_succ M hM hT o ho
    have hlevel : level R (o+1) ∈ N := (mem_relativeModel M R _ hM hT hR).mpr
      (level_in_relativeModel M R hM hT (o+1) hs)
    have hr := rankSet_mem_ground N hN (relativeModel_pairing M R hM hT hR)
      (relativeModel_union M R hM hT hR) (relativeModel_power_set M R hM hT hR)
      (relativeModel_bounded_separation M R hM hT hR)
      (relativeModel_sigma_replacement M R hM hT hR)
      (ground_relativeModel_infinity M hM hT) hlevel
    rw [rankSet_eq_ordinal] at hr
    exact hN _ hr _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr
      ((lt_add_one o).trans_le (level_rank_lower_bound R (o+1))))

theorem ground_relativeModel_same_indices (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (x : ZFSet.{u}) :
    InRelativeModel (relativeModel M (groundReals M)) (groundReals M) x ↔
      InRelativeModel M (groundReals M) x := by
  unfold InRelativeModel
  apply exists_congr; intro o
  exact and_congr (ground_relativeModel_ordinal_iff M hM hT o) Iff.rfl

theorem ground_relativeModel_idempotent (M : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) :
    relativeModel (relativeModel M (groundReals M)) (groundReals M) =
      relativeModel M (groundReals M) := by
  apply ZFSet.ext; intro x
  change x ∈ (relativeModel M (groundReals M)).sep
    (InRelativeModel (relativeModel M (groundReals M)) (groundReals M)) ↔ _
  rw [ZFSet.mem_sep,ground_relativeModel_same_indices M hM hT x]
  exact ⟨And.left,fun hx => ⟨hx,(mem_relativeModel M _ x hM hT (groundReals_mem M hM hT)).mp hx⟩⟩

theorem groundReals_relativeModel (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    groundReals (relativeModel M (groundReals M)) = groundReals M := by
  apply ZFSet.ext; intro x
  rw [mem_groundReals,mem_groundReals]
  constructor
  · rintro ⟨hx,hsub⟩; exact ⟨relativeModel_subset M _ hx,hsub⟩
  · rintro ⟨hx,hsub⟩; exact ⟨(relativeModel_ground_reals M hM hT x hsub).mpr hx,hsub⟩

end TuringRigidity.RelativeConstructible

end OAI
