/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenProductSplitting.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.TaggedProductConditions
public import LeanPool.TuringConeRigidity.CohenForcing.CohenGroundPoset

/-!
# Cohen Product Splitting
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenProductSplitting
open TransitiveNameModel BoundedSetTheory TaggedProductConditions CohenGroundPoset
open CohenSymmetry
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

/-- Encode a pair of conditions as an element of the supplied product code `c`. -/
noncomputable def productMap (a b c : ZFSet.{0})
    (hc : ∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s)
    (x : Conditions a × Conditions b) : Conditions c :=
  equivShrink c ⟨code (label a x.1) (label b x.2),
    (hc _).mpr ⟨_,label_mem _ _,_,label_mem _ _,rfl⟩⟩

theorem label_productMap (a b c : ZFSet.{0})
    (hc : ∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s)
    (x : Conditions a × Conditions b) :
    label c (productMap a b c hc x) = code (label a x.1) (label b x.2) := by
  simp only [productMap,label,Equiv.symm_apply_apply]

/-- Order isomorphism between a product of condition posets and its set-coded product. -/
noncomputable def productIso (a b c : ZFSet.{0})
    (hc : ∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ b, z = code p s) :
    (Conditions a × Conditions b) ≃o Conditions c :=
  { Equiv.ofBijective (productMap a b c hc) ⟨by
      intro x y h
      have he := congrArg (label c) h
      rw [label_productMap,label_productMap,code_injective] at he
      exact Prod.ext (label_injective a he.1) (label_injective b he.2),by
      intro z
      obtain ⟨p,hp,s,hs,he⟩ := (hc _).mp (label_mem c z)
      obtain ⟨p,rfl⟩ := label_surjective a hp
      obtain ⟨s,rfl⟩ := label_surjective b hs
      exact ⟨(p,s),label_injective c ((label_productMap a b c hc (p,s)).trans he.symm)⟩⟩ with
    map_rel_iff' := by
      intro x y
      change label c (productMap a b c hc y) ⊆ label c (productMap a b c hc x) ↔ _
      rw [label_productMap,label_productMap,code_subset]
      rfl }

/-- Assign the Boolean value `b` at coordinate `i`, overwriting any previous assignment there. -/
noncomputable def putBit {ι : Type} (p : Condition ι) (i : ι) (b : Bool) : Condition ι := by
  classical
  exact ⟨fun j => if j = i then some b else p.val j,
    (p.finite.insert i).subset (by intro j hj; by_cases h : j = i <;> simp_all)⟩

theorem putBit_le {ι : Type} (p : Condition ι) (i : ι) (b : Bool) (hi : p.val i = none) :
    putBit p i b ≤ p := by
  classical
  intro j d hd
  by_cases h : j = i
  · subst j; rw [hi] at hd; cases hd
  · simpa only [putBit,ite_eq_right h] using hd

theorem putBit_incompatible {ι : Type} (p : Condition ι) (i : ι) :
    ¬ ∃ r : Condition ι, r ≤ putBit p i false ∧ r ≤ putBit p i true := by
  classical
  rintro ⟨r,h0,h1⟩
  have h0' := h0 i false (by simp [putBit])
  have h1' := h1 i true (by simp [putBit])
  have he := Option.some.inj (h0'.symm.trans h1')
  cases he

theorem cohen_splits (s : ZFSet.{0}) (hs : s ∈ conditions ZFSet.omega) :
    ∃ s0 ∈ conditions ZFSet.omega, ∃ s1 ∈ conditions ZFSet.omega,
      s ⊆ s0 ∧ s ⊆ s1 ∧
        ¬ ∃ r ∈ conditions ZFSet.omega, s0 ⊆ r ∧ s1 ⊆ r := by
  classical
  obtain ⟨p,rfl⟩ := (CohenConditionCode.isCondition_iff_graph _ s).mp ((mem_conditions _ s).mp hs)
  let f (n : ℕ) : Conditions ZFSet.omega :=
    equivShrink _ ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩⟩
  have hf : Function.Injective f := by
    intro n m h
    have he := congrArg (label ZFSet.omega) h
    simp only [f,label,Equiv.symm_apply_apply] at he
    exact natSet_injective he
  have hfin := p.finite.preimage hf.injOn
  obtain ⟨n,hn⟩ := hfin.exists_notMem
  have hn' : p.val (f n) = none := by
    simpa only [Set.mem_preimage, Set.mem_ofPred_eq, not_not] using hn
  let p0 := putBit p (f n) false
  let p1 := putBit p (f n) true
  refine ⟨CohenConditionCode.graph _ p0,(mem_conditions _ _).mpr
    (CohenConditionCode.graph_isCondition _ _),
    CohenConditionCode.graph _ p1,(mem_conditions _ _).mpr (CohenConditionCode.graph_isCondition _
      _),
    (CohenConditionCode.graph_subset_iff _ _ _).mpr (putBit_le p _ false hn'),
    (CohenConditionCode.graph_subset_iff _ _ _).mpr (putBit_le p _ true hn'),?_⟩
  rintro ⟨r,hr,h0,h1⟩
  obtain ⟨r,rfl⟩ := (CohenConditionCode.isCondition_iff_graph _ r).mp ((mem_conditions _ r).mp hr)
  exact putBit_incompatible p (f n) ⟨r,(CohenConditionCode.graph_subset_iff _ _ _).mp h0,
    (CohenConditionCode.graph_subset_iff _ _ _).mp h1⟩

theorem product_splits (a c : ZFSet.{0})
    (hc : ∀ z, z ∈ c ↔ ∃ p ∈ a, ∃ s ∈ conditions ZFSet.omega, z = code p s) :
    ∀ z ∈ c, ∃ z0 ∈ c, ∃ z1 ∈ c, z ⊆ z0 ∧ z ⊆ z1 ∧
      ¬ ∃ r ∈ c, z0 ⊆ r ∧ z1 ⊆ r := by
  intro z hz
  obtain ⟨p,hp,s,hs,rfl⟩ := (hc z).mp hz
  obtain ⟨s0,hs0,s1,hs1,h0,h1,hinc⟩ := cohen_splits s hs
  refine ⟨code p s0,(hc _).mpr ⟨p,hp,s0,hs0,rfl⟩,
    code p s1,(hc _).mpr ⟨p,hp,s1,hs1,rfl⟩,
    (code_subset _ _ _ _).mpr ⟨fun _ h => h,h0⟩,
    (code_subset _ _ _ _).mpr ⟨fun _ h => h,h1⟩,?_⟩
  rintro ⟨r,hr,h0r,h1r⟩
  obtain ⟨p',_,s',hs',rfl⟩ := (hc r).mp hr
  exact hinc ⟨s',hs',(code_subset _ _ _ _).mp h0r |>.2,(code_subset _ _ _ _).mp h1r |>.2⟩

end TuringRigidity.CohenProductSplitting

end OAI
