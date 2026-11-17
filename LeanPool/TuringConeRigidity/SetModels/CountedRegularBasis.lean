/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/CountedRegularBasis.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalBooleanDense
public import LeanPool.TuringConeRigidity.SetModels.InternalCountableMap

/-!
# Counted Regular Basis
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CountedRegularBasis
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra
open InternalBooleanDense

/-- Bounded formula identifying a least basis neighborhood of `p` among those containing it. -/
def basicFormula (B p U : ℕ) : Formula :=
  .conj (.member U B) (.conj (.member p U)
    (.allMem B (.imp (.member (p+1) 0) (.subset (U+1) 0))))

theorem basicFormula_spec (M c B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (b p U : ℕ) (e : ℕ → ZFSet.{0}) (hb : e b = B) (hp : e p ∈ c) :
    (basicFormula b p U).Eval e ↔ e U = basicCode c (e p) := by
  have hbasic : basicCode c (e p) ∈ B :=
    (hB _).mpr ⟨basicCode_mem M c _ hM hT hc hp,regular_isCode c _⟩
  simp only [basicFormula,Formula.Eval,Formula.eval_allMem,Formula.eval_imp,
    Formula.eval_subset,cons_zero,cons_succ,hb]
  constructor
  · rintro ⟨hU,hpU,hmin⟩
    have h₁ := hmin _ hbasic (mem_basicCode c _ hp)
    have h₂ := (basicCode_le_iff c _ _ hp ((hB _).mp hU).2).mpr hpU
    exact ZFSet.ext (fun z => ⟨fun hz => h₁ hz,fun hz => h₂ hz⟩)
  · rintro h; rw [h]
    exact ⟨hbasic,mem_basicCode c _ hp,fun V hV hpV =>
      (basicCode_le_iff c _ V hp ((hB V).mp hV).2).mpr hpV⟩

theorem internal_basis (M c : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) :
    ∃ B ∈ M, (∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U) ∧
      ∃ S ∈ M, (∀ U, U ∈ S ↔ ∃ p ∈ c, U = basicCode c p) ∧
        ∃ g ∈ M, FunctionGraph c S g ∧
          (∀ p ∈ c, ∀ U, ZFSet.pair p U ∈ g ↔ U = basicCode c p) ∧
          (∀ U ∈ S, ∃ p ∈ c, ZFSet.pair p U ∈ g) := by
  obtain ⟨B,hBM,hB⟩ := internal_algebra M c hM hT hc
  let e := cons c (fun _ => B)
  have he : ∀ i, e i ∈ M := by
    intro i
    cases i
    · exact hc
    · exact hBM
  let S := B.sep (fun U => ∃ p ∈ c, U = basicCode c p)
  have hs (U : ZFSet.{0}) : U ∈ S ↔ ∃ p ∈ c, U = basicCode c p := by
    change (U ∈ B.sep _) ↔ _
    rw [ZFSet.mem_sep]
    exact ⟨And.right,fun h@⟨p,hp,hU⟩ => ⟨hU ▸ (hB _).mpr
      ⟨basicCode_mem M c p hM hT hc hp,regular_isCode c _⟩,h⟩⟩
  have hφ (U : ZFSet.{0}) : (Formula.existsMem 1 (basicFormula 3 0 1)).Eval (cons U e) ↔
      ∃ p ∈ c, U = basicCode c p := by
    change (∃ p ∈ c, (basicFormula 3 0 1).Eval (cons p (cons U e))) ↔ _
    exact exists_congr (fun p => and_congr_right (fun hp =>
      basicFormula_spec M c B hM hT hc hB 3 0 1 _ rfl hp))
  have hSM : S ∈ M := by
    simpa only [hφ,S] using sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (basicFormula 3 0 1)) e he hBM
  let v := cons c (cons S (fun _ => B))
  have hv : ∀ i, v i ∈ M := by
    intro i
    rcases i with _ | _ | i
    · exact hc
    · exact hSM
    · exact hBM
  let ψ : Formula := .existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0) (basicFormula 5 1 0)))
  let g := (ZFSet.prod c S).sep (fun z => ψ.Eval (cons z v))
  have hgM : g ∈ M := sep_mem M hM hT.separation.finitePrefix.bounded ψ v hv
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hc hSM)
  have hψ (z : ZFSet.{0}) : ψ.Eval (cons z v) ↔
      ∃ p ∈ c, ∃ U ∈ S, z = ZFSet.pair p U ∧ U = basicCode c p := by
    simp only [ψ,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,v]
    apply exists_congr; intro p
    apply and_congr_right; intro hp
    apply exists_congr; intro U
    apply and_congr_right; intro _
    exact and_congr_right (fun _ => basicFormula_spec M c B hM hT hc hB 5 1 0 _ rfl hp)
  have hgs (p U : ZFSet.{0}) (hp : p ∈ c) :
      ZFSet.pair p U ∈ g ↔ U = basicCode c p := by
    simp only [g,ZFSet.mem_sep,hψ]
    constructor
    · rintro ⟨_,p',_,U',_,he,hU⟩
      obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
      exact hU
    · intro hU
      have hUS := (hs U).mpr ⟨p,hp,hU⟩
      exact ⟨ZFSet.pair_mem_prod.mpr ⟨hp,hUS⟩,p,hp,U,hUS,rfl,hU⟩
  refine ⟨B,hBM,hB,S,hSM,hs,g,hgM,⟨?_,?_⟩,(fun p hp U => hgs p U hp),?_⟩
  · intro z hz; exact ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hz).1
  · intro p hp
    exact ⟨basicCode c p,(hs _).mpr ⟨p,hp,rfl⟩,(hgs p _ hp).mpr rfl,
      fun U _ hU => (hgs p U hp).mp hU⟩
  · intro U hU
    obtain ⟨p,hp,he⟩ := (hs U).mp hU
    exact ⟨p,hp,(hgs p U hp).mpr he⟩

theorem counted_basis (M c : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hct : InternallyCountable M c) :
    ∃ S ∈ M, InternallyCountable M S ∧
      (∀ U, U ∈ S ↔ ∃ p ∈ c, U = basicCode c p) ∧
      (∀ U ∈ S, IsCode c U ∧ U ≠ ∅) ∧
      (∀ U, IsCode c U → U ≠ ∅ → ∃ V ∈ S, V ⊆ U) := by
  classical
  obtain ⟨B,_,_,S,hS,hSs,g,hg,hgf,_,hgo⟩ := internal_basis M c hM hT hc
  refine ⟨S,hS,InternalCountableMap.countable_of_surjection M c S g hM hT hc hS hg hgf hgo hct,
    hSs,?_,?_⟩
  · intro U hU
    obtain ⟨p,hp,rfl⟩ := (hSs U).mp hU
    exact ⟨regular_isCode c _,fun h => ZFSet.notMem_empty p (h ▸ mem_basicCode c p hp)⟩
  · intro U hU hne
    have hex : ∃ p, p ∈ U := by
      by_contra h
      exact hne (ZFSet.ext (fun p => ⟨fun hp => False.elim (h ⟨p,hp⟩),
        fun hp => False.elim (ZFSet.notMem_empty p hp)⟩))
    obtain ⟨p,hp⟩ := hex
    exact ⟨basicCode c p,(hSs _).mpr ⟨p,hU.1 hp,rfl⟩,
      (basicCode_le_iff c p U (hU.1 hp) hU).mpr hp⟩

end TuringRigidity.CountedRegularBasis

end OAI
