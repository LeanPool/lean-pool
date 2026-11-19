/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/ParameterCoveringModels.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ElementarySchemas
public import LeanPool.TuringConeRigidity.SetModels.ModelReals

/-!
# Parameter Covering Models
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.ElementaryModel
open BoundedSetTheory TransitiveNameModel RelationCollapse
universe u

/-- The countable seed containing every numeral and every supplied oracle's real code. -/
noncomputable def realSeed (A : ℕ → Oracle) (n : ℕ) : ZFSet.{u} :=
  if n.unpair.1 = 0 then natSet n.unpair.2 else realCode (A n.unpair.2)

theorem seed_naturals (A : ℕ → Oracle) (n : ℕ) : natSet.{u} n ∈ hullSet (realSeed A) := by
  apply (mem_hullSet _ _).mpr
  have h := parameter_mem (realSeed.{u} A) (Nat.pair 0 n)
  simpa [realSeed] using h

theorem seed_reals (A : ℕ → Oracle) (n : ℕ) : realCode.{u} (A n) ∈ hullSet (realSeed A) := by
  apply (mem_hullSet _ _).mpr
  have h := parameter_mem (realSeed.{u} A) (Nat.pair 1 n)
  simpa [realSeed] using h

theorem collapse_nat_fixed (A : ℕ → Oracle) (n : ℕ) :
    structureMap (hullSet (realSeed.{u} A)) (natSet n) = natSet n := by
  apply structureMap_fixed omega_transitive
  · intro z hz
    obtain ⟨i,rfl⟩ := (mem_omega z).mp hz
    exact seed_naturals A i
  · exact (mem_omega _).mpr ⟨n,rfl⟩

theorem collapse_real_fixed (A : ℕ → Oracle) (n : ℕ) :
    structureMap (hullSet (realSeed.{u} A)) (realCode (A n)) = realCode (A n) := by
  apply collapse_fixed _ _ (seed_reals A n)
  intro y hy
  obtain ⟨i,rfl⟩ := (mem_omega y).mp (realCode_subset (A n) hy)
  exact ⟨seed_naturals A i,collapse_nat_fixed A i⟩

theorem collapsed_hull_elementary (a : ℕ → ZFSet.{u}) (p : SentenceForm)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ hullSet a) :
    p.Sat (collapsed (hullSet a) : Set ZFSet) (fun i => structureMap (hullSet a) (e i)) ↔
      p.Sat Set.univ e := by
  rw [←p.collapse_sat (hullSet a) (hullSet_extensional a) e he]
  have hh : (hullSet a : Set ZFSet) = hull a := by ext x; exact mem_hullSet a x
  rw [hh]
  exact hull_elementary a p e (fun i => (mem_hullSet a _).mp (he i))

theorem collapsed_hull_sourceT (a : ℕ → ZFSet.{u}) : SourceT (collapsed (hullSet a)) := by
  apply (collapsed_hull_valid a).sourceT (collapsed_transitive _)
  exact ⟨_,(mem_collapsed _ _).mpr ⟨a 0,(mem_hullSet a _).mpr (parameter_mem a 0),rfl⟩⟩

theorem parameter_covering_models (A : ℕ → Oracle) :
    ∃ M : ZFSet.{u}, Transitive M ∧ SourceT M ∧ Countable (Conditions M) ∧
      ∀ n, A n ∈ modelReals M := by
  let M := collapsed (hullSet (realSeed.{u} A))
  refine ⟨M,collapsed_transitive _,collapsed_hull_sourceT _,inferInstance,?_⟩
  intro n
  exact (mem_collapsed _ _).mpr ⟨realCode (A n),seed_reals A n,(collapse_real_fixed A n).symm⟩

end TuringRigidity.ElementaryModel

end OAI
