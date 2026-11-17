/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/GroundSeedOrdinalHeight.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.InternalHeightDomains
public import LeanPool.TuringConeRigidity.Constructibility.RelativeConstruction

/-!
# Ground Seed Ordinal Height
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RelativeConstructible
open ElementaryModel BoundedSetTheory TransitiveNameModel
universe u

theorem natSet_isOrdinal (n : ℕ) : (natSet.{u} n).IsOrdinal := by
  induction n with
  | zero => exact ZFSet.isOrdinal_empty
  | succ n ih => exact ZFSet.isOrdinal_succ ih

theorem omega_isOrdinal : ZFSet.omega.{u}.IsOrdinal := by
  apply ZFSet.isOrdinal_iff_forall_mem_isOrdinal.mpr
  refine ⟨omega_transitive,?_⟩
  intro x hx
  obtain ⟨n,rfl⟩ := (mem_omega x).mp hx
  exact natSet_isOrdinal n

theorem omega_mem_groundReals (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    ZFSet.omega ∈ groundReals M :=
  (mem_groundReals M _).mpr ⟨sourceT_omega_mem M hM hT,fun _ h => h⟩

theorem groundReals_not_isOrdinal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    ¬ (groundReals M).IsOrdinal := by
  let s : ZFSet.{u} := {natSet 1}
  have h1ω : natSet.{u} 1 ∈ ZFSet.omega := (mem_omega _).mpr ⟨1,rfl⟩
  have hsM : s ∈ M := singleton_mem M hM hT.pairing
    (hM _ (sourceT_omega_mem M hM hT) _ h1ω)
  have hsR : s ∈ groundReals M := (mem_groundReals M s).mpr ⟨hsM,by
    intro x hx
    obtain rfl := ZFSet.mem_singleton.mp hx
    exact h1ω⟩
  intro h
  have hs := h.mem hsR
  have hz : natSet.{u} 0 ∈ s := hs.isTransitive.mem_trans ((natSet_mem_natSet 0 1).mpr (by decide))
    (ZFSet.mem_singleton.mpr rfl)
  have he : (0 : ℕ) = 1 := natSet_injective (ZFSet.mem_singleton.mp hz)
  exact Nat.zero_ne_one he

theorem ordinalCut_ground_seed (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    ordinalCut (seed (groundReals M)) = insert ZFSet.omega ZFSet.omega := by
  apply ZFSet.ext; intro x
  rw [mem_ordinalCut,ground_seed_shape M hM]
  constructor
  · rintro ⟨hx,ho⟩
    rcases ZFSet.mem_insert_iff.mp hx with rfl|hx
    · exact False.elim (groundReals_not_isOrdinal M hM hT ho)
    · exact ZFSet.mem_insert_iff.mpr
        ((ho.subset_iff_eq_or_mem omega_isOrdinal).mp ((mem_groundReals M x).mp hx).2)
  · intro hx
    rcases ZFSet.mem_insert_iff.mp hx with rfl|hx
    · exact ⟨ZFSet.mem_insert_of_mem _ (omega_mem_groundReals M hM hT),omega_isOrdinal⟩
    · have hxR : x ∈ groundReals M := (mem_groundReals M x).mpr
        ⟨hM _ (sourceT_omega_mem M hM hT) _ hx,fun y hy => omega_transitive x hx y hy⟩
      exact ⟨ZFSet.mem_insert_of_mem _ hxR,omega_isOrdinal.mem hx⟩

theorem ordinalHeight_ground_seed (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    ordinalHeight (seed (groundReals M)) = (insert ZFSet.omega ZFSet.omega : ZFSet.{u}).rank := by
  unfold ordinalHeight
  rw [ordinalCut_ground_seed M hM hT]

theorem ground_level_height_independent (M N : ZFSet.{u})
    (hM : Transitive M) (hTM : SourceT M) (hN : Transitive N) (hTN : SourceT N)
    (o : Ordinal.{u}) :
    ordinalHeight (level (groundReals M) o) = ordinalHeight (level (groundReals N) o) := by
  rw [ordinalHeight_level,ordinalHeight_level,ordinalHeight_ground_seed M hM hTM,
    ordinalHeight_ground_seed N hN hTN]

end TuringRigidity.RelativeConstructible

end OAI
