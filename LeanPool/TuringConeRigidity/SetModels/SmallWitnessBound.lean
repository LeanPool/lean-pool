/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/SmallWitnessBound.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalStructureCollapse

/-!
# Small Witness Bound
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.RelationCollapse
open TransitiveNameModel BoundedSetTheory
universe u

theorem codedRelation_structureMap {k d f : ZFSet.{u}} {j : ZFSet.{u} → ZFSet.{u}}
    (hf : Presents d f j) (hj : ∀ x ∈ d, j x ∈ k)
    (hi : ∀ x ∈ d, ∀ y ∈ d, j x = j y → x = y)
    (wf : WellFounded (Rel k (codedRelation k d f)))
    (x : ZFSet.{u}) (hx : x ∈ d) :
    value k (codedRelation k d f) wf (j x) = structureMap d x := by
  induction x using ZFSet.inductionOn with
  | h x ih =>
    apply ZFSet.ext
    intro z
    rw [structureMap,mem_value,mem_value]
    constructor
    · rintro ⟨u,_,hux,hz⟩
      obtain ⟨y,hy,w,hw,hyw,rfl,hwx⟩ := (codedRelation_pair hf hj u (j x)).mp hux
      have hwx' : x = w := hi x hx w hw hwx
      subst w
      rw [ih y hyw hy] at hz
      exact ⟨y,hy,(membershipRelation_pair d y x).mpr ⟨hy,hx,hyw⟩,hz⟩
    · rintro ⟨y,hy,hyx,hz⟩
      have hyx' := ((membershipRelation_pair d y x).mp hyx).2.2
      exact ⟨j y,hj y hy,(codedRelation_pair hf hj _ _).mpr
        ⟨y,hy,x,hx,hyx',rfl,rfl⟩,hz.trans (ih y hyx' hy).symm⟩

theorem internal_structure_value_bound (M k : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hk : k ∈ M) :
    ∃ W ∈ M, ∀ d ∈ M, ∀ f ∈ M, ∀ j : ZFSet.{u} → ZFSet.{u},
      Presents d f j → (∀ x ∈ d, j x ∈ k) →
      (∀ x ∈ d, ∀ y ∈ d, j x = j y → x = y) →
      ∀ x ∈ d, structureMap d x ∈ W := by
  obtain ⟨W,hW,hbound⟩ := internal_value_bound M k hM hP hU hPow hS hR hk
  refine ⟨W,hW,?_⟩
  intro d hd f hf j hfj hj hi x hx
  have hr := codedRelation_mem M hM hP hU hPow hS.bounded hk hd hf
  have wf := codedRelation_wellFounded hfj hj hi
  have hv := hbound _ hr (codedRelation_on k d f) wf (j x) (hj x hx)
  rwa [codedRelation_structureMap hfj hj hi wf x hx] at hv

theorem internal_small_witness_bound (M k : ZFSet.{u}) (hM : Transitive M)
    (hP : Pairing M) (hU : BoundedSetTheory.Union M) (hPow : PowerSet M)
    (hS : SigmaSeparation M) (hR : SigmaReplacement M) (hk : k ∈ M) :
    ∃ W ∈ M, ∀ d ∈ M, StructureExtensional d →
      ∀ f ∈ M, ∀ j : ZFSet.{u} → ZFSet.{u}, Presents d f j →
      (∀ x ∈ d, j x ∈ k) → (∀ x ∈ d, ∀ y ∈ d, j x = j y → x = y) →
      ∀ t : ZFSet.{u}, Transitive t → t ⊆ d → ∀ e : ℕ → ZFSet.{u}, (∀ i, e i ∈ t) →
      ∀ φ : SigmaFormula, ∀ x ∈ d, φ.Realize d (cons x e) →
        ∃ y ∈ W, φ.Realize M (cons y e) := by
  obtain ⟨W,hW,hbound⟩ := internal_structure_value_bound M k hM hP hU hPow hS hR hk
  refine ⟨W,hW,?_⟩
  intro d hd hext f hf j hfj hj hi t ht htd e he φ x hx hφ
  obtain ⟨b,hb,g,_,_,hbt,hbdef,htransfer⟩ :=
    internal_structure_collapse M d hM hP hU hPow hS.bounded hR hd hext
  have henv : ∀ i, cons x e i ∈ d := by
    intro i; cases i with
    | zero => exact hx
    | succ i => exact htd (he i)
  have hcollapse := (htransfer φ (cons x e) henv).mp hφ
  have hfix : (fun i => structureMap d (cons x e i)) = cons (structureMap d x) e := by
    funext i
    cases i with
    | zero => rfl
    | succ i => exact structureMap_fixed ht htd (e i) (he i)
  have henvb : ∀ i, (fun i => structureMap d (cons x e i)) i ∈ b :=
    fun i => (hbdef _).mpr ⟨cons x e i,henv i,rfl⟩
  have hup := φ.upward b M hbt hM (fun y hy => hM b hb y hy) _ henvb hcollapse
  rw [hfix] at hup
  exact ⟨structureMap d x,hbound d hd f hf j hfj hj hi x hx,hup⟩

end TuringRigidity.RelationCollapse

end OAI
