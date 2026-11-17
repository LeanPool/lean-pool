/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenFactorReconstruction.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenProjectedGeneric
public import LeanPool.TuringConeRigidity.Representation.GenericFilterName

/-!
# Cohen Factor Reconstruction
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenFactorReconstruction
open TransitiveNameModel BoundedSetTheory CountableForcing
open CohenGroundPoset InternalCohenFactor InternalCohenPartition InternalCohenRestriction
open InternalCohenProjectedGeneric
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem mem_iff_projections (A B : ZFSet.{0}) (hBA : B ⊆ A)
    (G : GenericFilter (Conditions (conditions A))) (p : Conditions (conditions A)) :
    p ∈ G.carrier ↔ project A B hBA p ∈ (projected A B hBA G).carrier ∧
      project A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) p ∈
        (projected A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) G).carrier := by
  constructor
  · intro hp
    exact ⟨projected_contains A B hBA G hp,projected_contains A (A \ B) _ G hp⟩
  · rintro ⟨hb,hd⟩
    obtain ⟨b,hb,hbp⟩ := (mem_projected A B hBA G _).mp hb
    obtain ⟨d,hd,hdp⟩ := (mem_projected A (A \ B) _ G _).mp hd
    obtain ⟨s,hs,hsb,hsd⟩ := G.directed hb hd
    let e := factorIso A B hBA
    have h₁ := (e.monotone hsb).1
    have h₂ := (e.monotone hsd).2
    change project A B hBA s ≤ project A B hBA b at h₁
    change project A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) s ≤
      project A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) d at h₂
    rw [hbp] at h₁
    rw [hdp] at h₂
    exact G.upper (e.le_iff_le.mp ⟨h₁,h₂⟩) hs

/-- Reconstruct a condition filter from its restrictions to a coordinate set and its
complement. -/
noncomputable def reconstruct (A B j l : ZFSet.{0}) : ZFSet.{0} :=
  (conditions A).sep (fun p => ∃ b ∈ j, ∃ d ∈ l,
    ZFSet.pair p b ∈ restrictionGraph A B ∧ ZFSet.pair p d ∈ restrictionGraph A (A \ B))

theorem reconstruct_mem (N A B j l : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (hA : A ∈ N) (hB : B ∈ N) (hj : j ∈ N) (hl : l ∈ N) : reconstruct A B j l ∈ N := by
  have hD := complement_mem N A B hN hT hA hB
  let e := cons j (cons l (cons (restrictionGraph A B) (fun _ => restrictionGraph A (A \ B))))
  have he : ∀ i, e i ∈ N := by
    intro i; rcases i with _|_|_|i
    · exact hj
    · exact hl
    · exact restrictionGraph_mem N A B hN hT hA hB
    · exact restrictionGraph_mem N A _ hN hT hA hD
  simpa only [reconstruct,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e] using
    sep_mem N hN hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (.conj (.pairMem 2 1 5) (.pairMem 2 0 6)))) e he
      (conditions_mem N A hN hT hA)

theorem reconstruct_filter (A B : ZFSet.{0}) (hBA : B ⊆ A)
    (G : GenericFilter (Conditions (conditions A))) :
    reconstruct A B (genericFilterSet (conditions B) (projected A B hBA G).carrier)
      (genericFilterSet (conditions (A \ B))
        (projected A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) G).carrier) =
      genericFilterSet (conditions A) G.carrier := by
  apply ZFSet.ext; intro z
  rw [reconstruct,ZFSet.mem_sep,mem_genericFilterSet]
  constructor
  · rintro ⟨hz,b,hb,d,hd,hzb,hzd⟩
    obtain ⟨p,rfl⟩ := label_surjective _ hz
    obtain ⟨b,hbj,rfl⟩ := (mem_genericFilterSet _ _ b).mp hb
    obtain ⟨d,hdl,rfl⟩ := (mem_genericFilterSet _ _ d).mp hd
    have hbp : project A B hBA p = b := label_injective _
      ((label_project A B hBA p).trans ((pair_restrictionGraph A B _ _).mp hzb).2.2.symm)
    have hdp : project A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) p = d := label_injective _
      ((label_project A (A \ B) _ p).trans ((pair_restrictionGraph A (A \ B) _ _).mp hzd).2.2.symm)
    exact ⟨p,(mem_iff_projections A B hBA G p).mpr ⟨hbp.symm ▸ hbj,hdp.symm ▸ hdl⟩,rfl⟩
  · rintro ⟨p,hp,rfl⟩
    exact ⟨label_mem _ p,label _ (project A B hBA p),
      (mem_genericFilterSet _ _ _).mpr ⟨_,projected_contains A B hBA G hp,rfl⟩,
      label _ (project A (A \ B) (fun _ h => (ZFSet.mem_sdiff.mp h).1) p),
      (mem_genericFilterSet _ _ _).mpr ⟨_,projected_contains A (A \ B) _ G hp,rfl⟩,
      (pair_restrictionGraph A B _ _).mpr ⟨label_mem _ p,label_mem _ _,label_project A B hBA p⟩,
      (pair_restrictionGraph A (A \ B) _ _).mpr ⟨label_mem _ p,label_mem _ _,label_project A _ _ p⟩⟩

end TuringRigidity.CohenFactorReconstruction

end OAI
