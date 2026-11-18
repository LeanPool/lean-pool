/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalUncountableComplement.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalCountableOrdinals
public import LeanPool.TuringConeRigidity.SetModels.InternalInverseGraph
public import LeanPool.TuringConeRigidity.SetModels.InternalOrdinalSubset

/-!
# Internal Uncountable Complement
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalUncountableComplement
open TransitiveNameModel BoundedSetTheory InternalCountableOrdinals InternalCountableClosure

theorem difference_mem (M K C : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (hC : C ∈ M) : K \ C ∈ M := by
  simpa only [ZFSet.sep_notMem,Formula.Eval,cons_zero,cons_succ] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.neg (.member 0 1))
      (fun _ => C) (fun _ => hC) hK

theorem difference_uncountable (M K C : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (hunc : ¬ (K = ∅ ∨ InternallyCountable M K)) (hC : C ∈ M)
    (hCK : C ⊆ K) (hct : C = ∅ ∨ InternallyCountable M C) :
    ¬ (K \ C = ∅ ∨ InternallyCountable M (K \ C)) := by
  classical
  intro h
  have hc := countable_union M C (K \ C) hM hT hC (difference_mem M K C hM hT hK hC) hct h
  have he : C ∪ (K \ C) = K := by
    apply ZFSet.ext; intro x
    rw [ZFSet.mem_union,ZFSet.mem_sdiff]
    exact ⟨fun h => h.elim (fun h => hCK h) And.left,
      fun h => (Classical.em (x ∈ C)).elim Or.inl (fun hn => Or.inr ⟨h,hn⟩)⟩
  exact hunc (he ▸ hc)

theorem uncountable_subset_bijection (M K D : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : FirstUncountable M K) (hD : D ∈ M) (hDK : D ⊆ K)
    (hunc : ¬ (D = ∅ ∨ InternallyCountable M D)) :
    ∃ f ∈ M, FunctionGraph D K f ∧
      (∀ x ∈ D, ∀ x' ∈ D, ∀ y ∈ K, ZFSet.pair x y ∈ f → ZFSet.pair x' y ∈ f → x = x') ∧
      (∀ y ∈ K, ∃ x ∈ D, ZFSet.pair x y ∈ f) := by
  obtain ⟨J,hJM,hJ,hJK,f,hfM,hf,hi,hs⟩ :=
    InternalOrdinalSubset.internal_subset_orderType M K D hM hT hK.1 hD hDK
  have huncJ : ¬ (J = ∅ ∨ InternallyCountable M J) := by
    rintro (rfl|hct)
    · apply hunc; left
      apply ZFSet.ext; intro x
      constructor
      · intro hx
        obtain ⟨y,hy,_,_⟩ := hf.2 x hx
        exact False.elim (ZFSet.notMem_empty y hy)
      · intro hx; exact False.elim (ZFSet.notMem_empty x hx)
    · exact hunc (Or.inr (InternalInverseGraph.countable_of_bijection M D J f hM hT hD hJM hfM hf
      hi hs hct))
  have he : J = K := by
    rcases (hJ.subset_iff_eq_or_mem hK.1).mp hJK with h|h
    · exact h
    · exact False.elim (huncJ (hK.2.2.2 J h))
  exact he ▸ ⟨f,hfM,hf,hi,hs⟩

theorem complement_bijection (M K C : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : FirstUncountable M K) (hC : C ∈ M) (hCK : C ⊆ K)
    (hct : C = ∅ ∨ InternallyCountable M C) :
    ∃ f ∈ M, FunctionGraph (K \ C) K f ∧
      (∀ x ∈ K \ C, ∀ x' ∈ K \ C, ∀ y ∈ K,
        ZFSet.pair x y ∈ f → ZFSet.pair x' y ∈ f → x = x') ∧
      (∀ y ∈ K, ∃ x ∈ K \ C, ZFSet.pair x y ∈ f) :=
  uncountable_subset_bijection M K (K \ C) hM hT hK
    (difference_mem M K C hM hT hK.2.1 hC)
    (fun _ h => (ZFSet.mem_sdiff.mp h).1)
    (difference_uncountable M K C hM hT hK.2.1 hK.2.2.1 hC hCK hct)

end TuringRigidity.InternalUncountableComplement

end OAI
