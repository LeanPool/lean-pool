/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/RelativeModelPower.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.RelativeModelBounds
public import LeanPool.TuringConeRigidity.Constructibility.RelativeModelClosure

/-!
# Relative Model Power
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelativeConstructible
open BoundedSetTheory TransitiveNameModel ElementaryModel SentenceForm
universe u

theorem subsets_mem_definablePower (A a : ZFSet.{u}) (hA : Transitive A) (ha : a ∈ A) :
    A.sep (fun x => x ⊆ a) ∈ definablePower A := by
  have hs := separation_mem_definablePower A (fromBounded (.subset 0 1))
    (fun _ => a) (fun _ _ => ha)
  have eq : A.sep (fun x => (fromBounded (.subset 0 1)).Sat (A : Set ZFSet)
      (cons x (fun _ => a))) = A.sep (fun x => x ⊆ a) := by
    apply ZFSet.ext; intro x
    simp only [ZFSet.mem_sep]
    apply and_congr_right; intro hx
    rw [bounded_sat,Formula.absolute _ A hA _ (by
      intro i
      cases i
      · exact hx
      · exact ha)]
    exact Formula.eval_subset 0 1 _
  exact eq ▸ hs

theorem relativeModel_power_set (M R : ZFSet.{u}) (hM : Transitive M)
    (hT : SourceT M) (hR : R ∈ M) : PowerSet (relativeModel M R) := by
  intro a ha
  have haM := relativeModel_subset M R ha
  obtain ⟨q,hq,hqdef⟩ := internal_power M hM hT.powerSet haM
  obtain ⟨i,hi,hbound⟩ := relative_part_bounded M R q hM hT hR hq
  obtain ⟨j,hj,hja⟩ := (mem_relativeModel M R a hM hT hR).mp ha
  let o := max i j
  let A := level R o
  let b := A.sep (fun x => x ⊆ a)
  have haA : a ∈ A := level_mono R (le_max_right i j) hja
  have ho : o.toZFSet ∈ M := internal_ordinal_max M hi hj
  have hb : b ∈ relativeModel M R := by
    apply (mem_relativeModel M R b hM hT hR).mpr
    refine ⟨o+1,internal_ordinal_succ M hM hT o ho,?_⟩
    rw [level_succ]
    exact subsets_mem_definablePower A a (level_transitive R o) haA
  refine ⟨b,hb,?_⟩
  intro x hx
  have hsub : (∀ y ∈ relativeModel M R, y ∈ x → y ∈ a) ↔ x ⊆ a :=
    ⟨fun h y hy => h y (relativeModel_transitive M R hM x hx y hy) hy,
      fun h _ _ hy => h hy⟩
  rw [hsub]
  change x ∈ A.sep (fun x => x ⊆ a) ↔ x ⊆ a
  rw [ZFSet.mem_sep]
  constructor
  · exact And.right
  · intro hxa
    have hxq := (hqdef x).mpr ⟨relativeModel_subset M R hx,hxa⟩
    have hxi := (hbound x hxq).mp ((mem_relativeModel M R x hM hT hR).mp hx)
    exact ⟨level_mono R (le_max_left i j) hxi,hxa⟩

end TuringRigidity.RelativeConstructible

end OAI
