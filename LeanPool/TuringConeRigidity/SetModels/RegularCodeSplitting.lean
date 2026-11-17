/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/RegularCodeSplitting.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalBooleanDense

/-!
# Regular Code Splitting
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RegularCodeSplitting
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra
open InternalRegularOrder InternalBooleanDense

theorem mem_basic_iff (c p t : ZFSet.{0}) : t ∈ basicCode c p ↔
    t ∈ c ∧ ∀ q ∈ c, t ⊆ q → ∃ r ∈ c, q ⊆ r ∧ p ⊆ r := by
  rw [basicCode,bitCode,mem_regular]
  apply and_congr_right; intro _
  apply forall_congr'; intro q
  apply forall_congr'; intro _
  apply forall_congr'; intro _
  simp only [CohenInternalDecision.below,ZFSet.mem_sep,ZFSet.mem_singleton]
  constructor
  · rintro ⟨r,⟨hr,x,hx,hxr⟩,hqr⟩
    subst x; exact ⟨r,hr,hqr,hxr⟩
  · rintro ⟨r,hr,hqr,hpr⟩; exact ⟨r,⟨hr,p,rfl,hpr⟩,hqr⟩

theorem basic_disjoint (c p q : ZFSet.{0})
    (hinc : ¬ ∃ r ∈ c, p ⊆ r ∧ q ⊆ r) :
    ∀ t ∈ basicCode c p, t ∉ basicCode c q := by
  intro t htp htq
  obtain ⟨r,hr,htr,hpr⟩ := ((mem_basic_iff c p t).mp htp).2 t
    ((mem_basic_iff c p t).mp htp).1 (fun _ h => h)
  have hrq := code_lower c _ (regular_isCode c _) t htq r hr htr
  obtain ⟨s,hs,hrs,hqs⟩ := ((mem_basic_iff c q r).mp hrq).2 r hr (fun _ h => h)
  exact hinc ⟨s,hs,fun _ h => hrs (hpr h),hqs⟩

/-- The part of `U` lying in the regular complement of `V` inside `c`. -/
noncomputable def remainder (U : ZFSet.{0}) (c V : ZFSet.{0}) : ZFSet.{0} :=
  U.sep (fun p => p ∈ neg c V)

theorem remainder_isCode (c U V : ZFSet.{0}) (hU : IsCode c U) (hV : IsCode c V) :
    IsCode c (remainder U c V) := by
  have he : remainder U c V = infCode c {U,neg c V} := by
    apply ZFSet.ext; intro p
    simp only [remainder,infCode,ZFSet.mem_sep,ZFSet.mem_pair]
    constructor
    · rintro ⟨hpu,hpn⟩
      exact ⟨hU.1 hpu,fun W hW => hW.elim (fun h => h ▸ hpu) (fun h => h ▸ hpn)⟩
    · rintro ⟨_,h⟩; exact ⟨h U (Or.inl rfl),h _ (Or.inr rfl)⟩
  rw [he]
  exact inf_isCode c _ (fun W hW => (ZFSet.mem_pair.mp hW).elim
    (fun h => h ▸ hU) (fun h => h ▸ neg_isCode c V hV))

theorem remainder_mem (M c U V : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hU : U ∈ M) (hV : V ∈ M) : remainder U c V ∈ M := by
  simpa only [remainder,Formula.Eval,cons_zero,cons_succ] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.member 0 1)
      (fun _ => neg c V) (fun _ => neg_mem M c V hM hT hc hV) hU

/-- Two nonempty disjoint subsets of `U` whose union is dense below every condition of `U`. -/
def Partition (U V W : ZFSet.{0}) : Prop :=
  V ⊆ U ∧ W ⊆ U ∧ V ≠ ∅ ∧ W ≠ ∅ ∧
    (∀ p ∈ V, p ∉ W) ∧
    ∀ p ∈ U, ∃ r ∈ U, p ⊆ r ∧ (r ∈ V ∨ r ∈ W)

/-- Bounded formula expressing the nonempty disjoint dense-partition property. -/
def partitionFormula (U V W : ℕ) : Formula :=
  .conj (.subset V U) (.conj (.subset W U)
    (.conj (.neg (.empty V)) (.conj (.neg (.empty W))
      (.conj (.allMem V (.neg (.member 0 (W+1))))
        (.allMem U (.existsMem (U+1) (.conj (.subset 1 0)
          (.disj (.member 0 (V+2)) (.member 0 (W+2))))))))))

theorem partitionFormula_spec (U V W : ℕ) (e : ℕ → ZFSet.{0}) :
    (partitionFormula U V W).Eval e ↔ Partition (e U) (e V) (e W) := by
  simp only [partitionFormula,Partition,Formula.Eval,Formula.eval_subset,Formula.eval_empty,
    Formula.eval_allMem,Formula.eval_disj,cons_zero,cons_succ]

theorem partition_join (c U V W : ZFSet.{0}) (hU : IsCode c U)
    (hV : IsCode c V) (hW : IsCode c W) (h : Partition U V W) :
    supCode c {V,W} = U := by
  have hF : ∀ X ∈ ({V,W} : ZFSet.{0}), IsCode c X := fun X hX =>
    (ZFSet.mem_pair.mp hX).elim (fun he => he ▸ hV) (fun he => he ▸ hW)
  have hle := (supCode_le_iff c {V,W} U hF hU).mpr (fun X hX =>
    (ZFSet.mem_pair.mp hX).elim (fun he => he ▸ h.1) (fun he => he ▸ h.2.1))
  apply ZFSet.ext; intro p
  refine ⟨fun hp => hle hp,fun hp => ?_⟩
  apply (mem_regular c _ p).mpr
  refine ⟨hU.1 hp,fun q hq hpq => ?_⟩
  obtain ⟨r,_,hqr,hr⟩ := h.2.2.2.2.2 q (code_lower c U hU p hp q hq hpq)
  refine ⟨r,?_,hqr⟩
  exact hr.elim (fun hr => ZFSet.mem_sUnion.mpr ⟨V,ZFSet.mem_pair.mpr (Or.inl rfl),hr⟩)
    (fun hr => ZFSet.mem_sUnion.mpr ⟨W,ZFSet.mem_pair.mpr (Or.inr rfl),hr⟩)

theorem internal_partition (M c B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hsplit : ∀ p ∈ c, ∃ p0 ∈ c, ∃ p1 ∈ c, p ⊆ p0 ∧ p ⊆ p1 ∧
      ¬ ∃ r ∈ c, p0 ⊆ r ∧ p1 ⊆ r) :
    ∀ U ∈ B, U ≠ ∅ → ∃ V ∈ B, ∃ W ∈ B, Partition U V W := by
  classical
  intro U hUB hU0
  have hUM := ((hB U).mp hUB).1
  have hU := ((hB U).mp hUB).2
  have hex : ∃ p, p ∈ U := by
    by_contra h
    exact hU0 (ZFSet.ext (fun p => ⟨fun hp => False.elim (h ⟨p,hp⟩),
      fun hp => False.elim (ZFSet.notMem_empty p hp)⟩))
  obtain ⟨p,hp⟩ := hex
  obtain ⟨p0,hp0,p1,hp1,h0,h1,hinc⟩ := hsplit p (hU.1 hp)
  let V := basicCode c p0
  let W := remainder U c V
  have hV : IsCode c V := regular_isCode c _
  have hVM := basicCode_mem M c p0 hM hT hc hp0
  have hVU : V ⊆ U := (basicCode_le_iff c p0 U hp0 hU).mpr
    (code_lower c U hU p hp p0 hp0 h0)
  have hp1U := code_lower c U hU p hp p1 hp1 h1
  have hp1N : p1 ∈ neg c V := by
    refine ZFSet.mem_sep.mpr ⟨hp1,fun q hq hp1q => ?_⟩
    obtain ⟨r,hr,hqr,hp0r⟩ := ((mem_basic_iff c p0 q).mp hq).2 q
      ((mem_basic_iff c p0 q).mp hq).1 (fun _ h => h)
    exact hinc ⟨r,hr,hp0r,fun _ h => hqr (hp1q h)⟩
  have hp1W : p1 ∈ W := ZFSet.mem_sep.mpr ⟨hp1U,hp1N⟩
  refine ⟨V,(hB V).mpr ⟨hVM,hV⟩,W,
    (hB W).mpr ⟨remainder_mem M c U V hM hT hc hUM hVM,remainder_isCode c U V hU hV⟩,
    hVU,(fun _ h => (ZFSet.mem_sep.mp h).1),
    (fun h => ZFSet.notMem_empty p0 (h ▸ mem_basicCode c p0 hp0)),
    (fun h => ZFSet.notMem_empty p1 (h ▸ hp1W)),?_,?_⟩
  · intro q hq hqW
    exact (ZFSet.mem_sep.mp (ZFSet.mem_sep.mp hqW).2).2 q hq (fun _ h => h)
  · intro q hq
    by_cases hex : ∃ r ∈ V, q ⊆ r
    · obtain ⟨r,hr,hqr⟩ := hex
      exact ⟨r,hVU hr,hqr,Or.inl hr⟩
    · exact ⟨q,hq,(fun _ h => h),Or.inr (ZFSet.mem_sep.mpr ⟨hq,
        ZFSet.mem_sep.mpr ⟨hU.1 hq,fun r hr hqr => hex ⟨r,hr,hqr⟩⟩⟩)⟩

end TuringRigidity.RegularCodeSplitting

end OAI
