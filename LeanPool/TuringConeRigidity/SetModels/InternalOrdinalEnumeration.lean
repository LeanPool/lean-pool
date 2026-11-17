/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalOrdinalEnumeration.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.ChoiceTraceExtension
public import LeanPool.TuringConeRigidity.SetModels.ChoiceTraceFormula
public import LeanPool.TuringConeRigidity.SetModels.InternalHartogs

/-!
# Internal Ordinal Enumeration
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.BoundedSetTheory
open TransitiveNameModel RelationCollapse
universe u
namespace InternalWellOrder

theorem internal_ordinal_enumeration (M : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hI : Infinity M) (hAC : Choice M)
    {a : ZFSet.{u}} (ha : a ∈ M) :
    ∃ δ ∈ M, δ.IsOrdinal ∧ ∃ F ∈ M, TransitiveNameModel.FunctionGraph δ a F ∧
      (∀ x ∈ a, ∃ i ∈ δ, ZFSet.pair i x ∈ F) ∧
      (∀ i ∈ δ, ∀ j ∈ δ, ∀ x, ZFSet.pair i x ∈ F → ZFSet.pair j x ∈ F → i = j) := by
  classical
  obtain ⟨q,hq,s,hsM,hs,hqdef⟩ := internal_selector M hM hPow hS.bounded hAC ha
  obtain ⟨α,hαM,hα,hHartogs⟩ := internal_hartogs M a hM hP hU hPow hS hR hI ha
  have hαT : Transitive α := fun i hi j hj => hα.subset_of_mem hi hj
  obtain ⟨F,hF,htrace,hmax⟩ := internal_maximal_trace M hM hP hU hPow hS.bounded hαM ha hq hsM hαT
    hs
  have hfun := htrace.functional hαT hs
  have hmissing : ∃ i ∈ α, ¬ ∃ x ∈ a, ZFSet.pair i x ∈ F := by
    by_contra hn
    have htotal : ∀ i ∈ α, ∃ x ∈ a, ZFSet.pair i x ∈ F := by
      intro i hi; exact Classical.byContradiction (fun h => hn ⟨i,hi,h⟩)
    have hfg : TransitiveNameModel.FunctionGraph α a F := by
      refine ⟨htrace.shape,?_⟩
      intro i hi
      obtain ⟨x,hx,hix⟩ := htotal i hi
      exact ⟨x,hx,hix,fun y _ hiy => hfun i y x hiy hix⟩
    obtain ⟨v,hv,hva⟩ := FunctionGraph.exists_presentation hfg
    apply hHartogs F hF v hv hva
    intro i hi j hj he
    have hip := (hv.pair_iff i (v i)).mpr ⟨hi,rfl⟩
    have hjp := (hv.pair_iff j (v j)).mpr ⟨hj,rfl⟩
    rw [← he] at hjp
    exact htrace.injective hα hs i j (v i) hip hjp
  have minimal (i : ZFSet.{u}) : i ∈ α → (¬ ∃ x ∈ a, ZFSet.pair i x ∈ F) →
      ∃ j ∈ α, (¬ ∃ x ∈ a, ZFSet.pair j x ∈ F) ∧
        ∀ k ∈ j, ∃ x ∈ a, ZFSet.pair k x ∈ F := by
    induction i using ZFSet.inductionOn with
    | h i ih =>
      intro hi hmiss
      by_cases hex : ∃ j ∈ i, ¬ ∃ x ∈ a, ZFSet.pair j x ∈ F
      · obtain ⟨j,hji,hjmiss⟩ := hex
        exact ih j hji (hα.subset_of_mem hi hji) hjmiss
      · refine ⟨i,hi,hmiss,?_⟩
        intro j hji
        exact Classical.byContradiction (fun h => hex ⟨j,hji,h⟩)
  obtain ⟨i,hi,hmiss⟩ := hmissing
  obtain ⟨i,hi,hmiss,hprev⟩ := minimal i hi hmiss
  have hiM := hM α hαM i hi
  have hiT : Transitive i := fun j hj k hk => (hα.mem hi).subset_of_mem hj hk
  have hdom : ∀ j y, ZFSet.pair j y ∈ F → j ∈ i := htrace.domain_before hα hi hmiss
  have hres := residual_mem M hM hS.bounded ha hF hiM
  have hrem := residual_remaining a F i
  have hempty : ¬ ∃ x, x ∈ residual a F i := by
    intro hex
    have hrq : residual a F i ∈ q := (hqdef _).mpr ⟨hres,hrem.1,hex⟩
    obtain ⟨x,hxr,hrx,_⟩ := hs.2 _ hrq
    have hxa := hrem.1 hxr
    have hpair := orderedPair_mem M hM hP hiM (hM a ha x hxa)
    have hnew := binary_union_mem M hM hP hU hF (singleton_mem M hM hP hpair)
    have hnewtrace := htrace.adjoin hi hiT hxa hrq hrem hrx hprev hdom
    have hnewsub := hmax _ hnew hnewtrace
    exact hmiss ⟨x,hxa,hnewsub (ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_singleton.mpr rfl)))⟩
  refine ⟨i,hiM,hα.mem hi,F,hF,?_,?_,?_⟩
  · refine ⟨?_,?_⟩
    · intro z hz
      obtain ⟨j,_,x,hx,rfl⟩ := htrace.shape z hz
      exact ⟨j,hdom j x hz,x,hx,rfl⟩
    · intro j hj
      obtain ⟨x,hx,hjx⟩ := hprev j hj
      exact ⟨x,hx,hjx,fun y _ hjy => hfun j y x hjy hjx⟩
  · intro x hx
    exact Classical.byContradiction (fun hn => hempty ⟨x,(hrem.2 x hx).mpr hn⟩)
  · intro j _ k _ x hjx hkx
    exact htrace.injective hα hs j k x hjx hkx

end InternalWellOrder
end TuringRigidity.BoundedSetTheory

end OAI
