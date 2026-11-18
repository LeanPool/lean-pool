/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Constructibility/UniformSigmaHull.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.UniformFragmentHull
public import LeanPool.TuringConeRigidity.SetModels.SmallWitnessBound

/-!
# Uniform Sigma Hull
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel RelationCollapse
universe u
namespace FiniteTuple

theorem uniform_internal_sigma_hull (M t : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M)
    (ht : t ∈ M) (h0t : (∅ : ZFSet.{u}) ∈ t) :
    ∃ K ∈ M, ∀ e : ℕ → ZFSet.{u}, (∀ i, e i ∈ t) → ∀ φ : SigmaFormula,
      ∀ x ∈ M, φ.Realize M (cons x e) →
        ∃ h ∈ M, t ⊆ h ∧ x ∈ h ∧ StructureExtensional h ∧ φ.Realize h (cons x e) ∧
          ∃ f ∈ M, ∃ j : ZFSet.{u} → ZFSet.{u}, Presents h f j ∧
            (∀ x ∈ h, j x ∈ K) ∧ (∀ x ∈ h, ∀ y ∈ h, j x = j y → x = y) := by
  obtain ⟨K,hK,hsmall⟩ := uniform_internal_fragment_hull M t hM hP hU hPow hS hR hI hAC ht h0t
  refine ⟨K,hK,?_⟩
  intro e he φ x hx hφ
  obtain ⟨xs,hlen,hxs,hmat⟩ := (φ.realize_iff_prefix M (cons x e)).mp hφ
  have h0 : (∅ : ZFSet.{u}) ∈ M := hM t ht _ h0t
  let s := t ∪ elements (x::xs)
  have hxsM : ∀ y ∈ x::xs, y ∈ M := by
    intro y hy; rcases List.mem_cons.mp hy with rfl|hy
    · exact hx
    · exact hxs y hy
  have hs : s ∈ M := binary_union_mem M hM hP hU ht (elements_mem M hM hP hU h0 (x::xs) hxsM)
  have hts : t ⊆ s := fun _ hy => ZFSet.mem_union.mpr (Or.inl hy)
  have hxsS : ∀ y ∈ x::xs, y ∈ s :=
    fun y hy => ZFSet.mem_union.mpr (Or.inr ((mem_elements y (x::xs)).mpr hy))
  obtain ⟨d,hd,hdt,hsd⟩ := internal_transitive_container M hM hP hU hS.bounded hR hI hs
  have hsd' : s ⊆ d := fun y hy => hdt _ hsd y hy
  have henvS : ∀ i, cons x e i ∈ s := by
    intro i; cases i with
    | zero => exact hxsS x List.mem_cons_self
    | succ i => exact hts (he i)
  have hfeedS := SigmaFormula.feed_mem xs (cons x e) s
    (fun y hy => hxsS y (List.mem_cons_of_mem _ hy)) henvS
  have hfeedM : ∀ i, SigmaFormula.feed xs (cons x e) i ∈ M := fun i => hM s hs _ (hfeedS i)
  have hfeedD : ∀ i, SigmaFormula.feed xs (cons x e) i ∈ d := fun i => hsd' (hfeedS i)
  have hmatD : φ.matrix.Realize d (SigmaFormula.feed xs (cons x e)) :=
    (φ.matrix.absolute d hdt _ hfeedD).mpr ((φ.matrix.absolute M hM _ hfeedM).mp hmat)
  obtain ⟨h,hh,hsh,_,hext,htransfer,f,hf,j,hfj,hj,hi⟩ := hsmall (x::xs) hxsM d hd hdt hsd' φ.matrix
  refine ⟨h,hh,fun y hy => hsh (hts hy),hsh (hxsS x List.mem_cons_self),hext,?_,f,hf,j,hfj,hj,hi⟩
  apply (φ.realize_iff_prefix h (cons x e)).mpr
  exact ⟨xs,hlen,fun y hy => hsh (hxsS y (List.mem_cons_of_mem _ hy)),
    (htransfer _ (fun i => hsh (hfeedS i))).mpr hmatD⟩

theorem internal_uniform_sigma_witness_bound (M t : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M)
    (ht : t ∈ M) (htt : Transitive t) (h0t : (∅ : ZFSet.{u}) ∈ t) :
    ∃ W ∈ M, ∀ e : ℕ → ZFSet.{u}, (∀ i, e i ∈ t) → ∀ φ : SigmaFormula,
      (∃ x ∈ M, φ.Realize M (cons x e)) → ∃ y ∈ W, φ.Realize M (cons y e) := by
  obtain ⟨K,hK,hsmall⟩ := uniform_internal_sigma_hull M t hM hP hU hPow hS hR hI hAC ht h0t
  obtain ⟨W,hW,hbound⟩ := internal_small_witness_bound M K hM hP hU hPow hS hR hK
  refine ⟨W,hW,?_⟩
  intro e he φ hφ
  obtain ⟨x,hx,hφ⟩ := hφ
  obtain ⟨h,hh,hth,hxh,hext,hφh,f,hf,j,hfj,hj,hi⟩ := hsmall e he φ x hx hφ
  exact hbound h hh hext f hf j hfj hj hi t htt hth e he φ x hxh hφh

end FiniteTuple
end TuringRigidity.BoundedSetTheory

end OAI
