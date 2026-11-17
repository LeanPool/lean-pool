/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenSizeLevels.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenGroundPoset

/-!
# Cohen Size Levels
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenSizeLevels
open Set TransitiveNameModel BoundedSetTheory InternalFiniteSubsets
open RelativeConstructible CohenSymmetry CohenCoordinates CohenConditionCode

def Small (n : ℕ) (p : ZFSet.{0}) : Prop :=
  ∃ k < n, ∃ v : Fin k → ZFSet.{0}, p = ZFSet.range v

theorem small_graph_bound (A : ZFSet.{0}) (p : Condition (Conditions A))
    (n : ℕ) (h : Small n (graph A p)) : (support p).card < n := by
  classical
  obtain ⟨k,hk,v,hv⟩ := h
  have hex (i : ↥(support p)) : ∃ j : Fin k,
      v j = ZFSet.pair (label A i.val) (InternalCohen.bitSet ((p.val i.val).getD false)) := by
    apply ZFSet.mem_range.mp
    rw [←hv]
    exact ZFSet.mem_range_self i
  let f : ↥(support p) → Fin k := fun i => (hex i).choose
  have hf : Function.Injective f := by
    intro i j hij
    have he := (hex i).choose_spec.symm.trans ((congrArg v hij).trans (hex j).choose_spec)
    exact Subtype.ext (label_injective A (ZFSet.pair_inj.mp he).1)
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_coe,Fintype.card_fin] at hc
  exact lt_of_le_of_lt hc hk

theorem graph_small (A : ZFSet.{0}) (p : Condition (Conditions A)) :
    Small ((support p).card + 1) (graph A p) := by
  classical
  let e : Fin (support p).card ≃ ↥(support p) :=
    (finCongr (Fintype.card_coe _).symm).trans (Fintype.equivFin ↥(support p)).symm
  refine ⟨(support p).card,Nat.lt_succ_self _,fun i =>
    ZFSet.pair (label A (e i).val) (InternalCohen.bitSet ((p.val (e i).val).getD false)),?_⟩
  apply ZFSet.ext; intro z
  simp only [graph,ZFSet.mem_range]
  exact ⟨fun ⟨i,hi⟩ => ⟨e.symm i,by simpa using hi⟩,
    fun ⟨i,hi⟩ => ⟨e i,hi⟩⟩

def smallFormula (ω B C n p : ℕ) : Formula :=
  .existsMem n (.existsMem (C+1) (.conj (.functionGraph 0 1 (B+2))
    (rangeFormula (ω+2) (B+2) (p+2) 0)))

theorem smallFormula_spec (ω B C n p : ℕ) (e : ℕ → ZFSet.{0}) (N : ℕ)
    (hω : e ω = ZFSet.omega) (hn : e n = natSet N) (hp : e p ⊆ e B)
    (hC : ∀ g, g ∈ e C ↔ InternalCollapse.Prefix (e B) g) :
    (smallFormula ω B C n p).Eval e ↔ Small N (e p) := by
  simp only [smallFormula,Formula.Eval,Formula.eval_functionGraph,cons_zero,cons_succ]
  change (∃ k ∈ e n, ∃ g ∈ e C, FunctionGraph k (e B) g ∧
    (rangeFormula (ω+2) (B+2) (p+2) 0).Eval (cons g (cons k e))) ↔ _
  rw [hn]
  constructor
  · rintro ⟨k,hk,g,_,hf,hr⟩
    obtain ⟨k,hlt,rfl⟩ := (mem_natSet N k).mp hk
    obtain ⟨v,hv,rfl⟩ := functionGraph_tuple (e B) g k hf
    exact ⟨k,hlt,v,(rangeFormula_spec (ω+2) (B+2) (p+2) 0
      (cons (tupleGraph v) (cons (natSet k) e)) hω hv rfl).mp hr⟩
  · rintro ⟨k,hk,v,hv⟩
    have hvB : ∀ i, v i ∈ e B := fun i => hp (hv ▸ ZFSet.mem_range_self i)
    refine ⟨natSet k,(natSet_mem_natSet _ _).mpr hk,tupleGraph v,
      (hC _).mpr ⟨k,tupleGraph_function _ v hvB⟩,tupleGraph_function _ v hvB,?_⟩
    exact (rangeFormula_spec (ω+2) (B+2) (p+2) 0
      (cons (tupleGraph v) (cons (natSet k) e)) hω hvB rfl).mpr hv

noncomputable def levels (A : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.prod ZFSet.omega (CohenGroundPoset.conditions A)).sep
    (fun z => ∃ n p, z = ZFSet.pair (natSet n) p ∧ Small n p)

theorem pair_levels (A : ZFSet.{0}) (n : ℕ) (p : ZFSet.{0}) :
    ZFSet.pair (natSet n) p ∈ levels A ↔ p ∈ CohenGroundPoset.conditions A ∧ Small n p := by
  simp only [levels,ZFSet.mem_sep,ZFSet.pair_mem_prod]
  constructor
  · rintro ⟨⟨_,hp⟩,m,q,he,hs⟩
    obtain ⟨h1,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hp,natSet_injective h1 ▸ hs⟩
  · rintro ⟨hp,hs⟩
    exact ⟨⟨(mem_omega _).mpr ⟨n,rfl⟩,hp⟩,n,p,rfl,hs⟩

theorem levels_mem (M A : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) : levels A ∈ M := by
  have hω := sourceT_omega_mem M hM hT
  have hc := CohenGroundPoset.conditions_mem M A hM hT hA
  let B := ZFSet.prod A InternalCohen.alphabet
  have hB := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hA (InternalCohen.alphabet_mem M hM hT)
  obtain ⟨C,hCM,hC⟩ := InternalCollapse.conditions_exist_absolute_without_choice M hM
    hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hω hB
  let e := cons ZFSet.omega (cons (CohenGroundPoset.conditions A) (cons B (fun _ => C)))
  let φ : Formula := .existsMem 1 (.existsMem 3
    (.conj (.orderedPair 2 1 0) (smallFormula 3 5 6 1 0)))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | _ | _ | i
    · exact hω
    · exact hc
    · exact hB
    · exact hCM
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded φ e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hω hc)
  have heq : (ZFSet.prod ZFSet.omega (CohenGroundPoset.conditions A)).sep
      (fun z => φ.Eval (cons z e)) = levels A := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sep,levels,ZFSet.mem_sep]
    apply and_congr_right; intro _
    simp only [φ,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,e]
    change (∃ n ∈ ZFSet.omega, ∃ p ∈ CohenGroundPoset.conditions A,
      z = ZFSet.pair n p ∧ (smallFormula 3 5 6 1 0).Eval (cons p (cons n (cons z e)))) ↔ _
    constructor
    · rintro ⟨n,hn,p,hp,hz,hsmall⟩
      obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
      have hpb := ((mem_finiteSubsets_iff _ _).mp ((CohenGroundPoset.mem_conditions A p).mp hp).1).1
      exact ⟨n,p,hz,(smallFormula_spec 3 5 6 1 0 (cons p (cons (natSet n) (cons z e))) n rfl rfl
        hpb hC).mp hsmall⟩
    · rintro ⟨n,p,rfl,hsmall⟩
      rename_i hz
      have hp := (ZFSet.pair_mem_prod.mp hz).2
      have hpb := ((mem_finiteSubsets_iff _ _).mp ((CohenGroundPoset.mem_conditions A p).mp hp).1).1
      exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,p,hp,rfl,
        (smallFormula_spec 3 5 6 1 0 (cons p (cons (natSet n) (cons (ZFSet.pair (natSet n) p) e)))
          n rfl rfl hpb hC).mpr hsmall⟩
  exact heq ▸ hs

end TuringRigidity.CohenSizeLevels

end OAI
