/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/InternalCohenRestriction.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenGroundPoset

/-!
# Internal Cohen Restriction
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalCohenRestriction
open TransitiveNameModel BoundedSetTheory InternalFiniteSubsets CohenConditionCode CohenGroundPoset
open InternalCohen (alphabet)

noncomputable def restrict (B p : ZFSet.{0}) : ZFSet.{0} :=
  p.sep (fun z => ∃ x ∈ B, ∃ b ∈ alphabet, z = ZFSet.pair x b)

theorem mem_restrict (B p z : ZFSet.{0}) :
    z ∈ restrict B p ↔ z ∈ p ∧ z ∈ ZFSet.prod B alphabet := by
  rw [restrict,ZFSet.mem_sep,ZFSet.mem_prod]

theorem pair_restrict (B p x b : ZFSet.{0}) :
    ZFSet.pair x b ∈ restrict B p ↔ ZFSet.pair x b ∈ p ∧ x ∈ B ∧ b ∈ alphabet := by
  rw [mem_restrict,ZFSet.pair_mem_prod]

theorem restrict_mem (M B p : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hB : B ∈ M) (hp : p ∈ M) : restrict B p ∈ M := by
  let e := cons B (fun _ => alphabet)
  have he : ∀ i, e i ∈ M := by
    intro i
    cases i
    · exact hB
    · exact InternalCohen.alphabet_mem M hM hT
  simpa only [restrict,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (.orderedPair 2 1 0))) e he hp

theorem restrict_condition (A B p : ZFSet.{0}) (hBA : B ⊆ A) (hp : p ∈ conditions A) :
    restrict B p ∈ conditions B := by
  obtain ⟨hfin,hsv⟩ := (mem_conditions A p).mp hp
  obtain ⟨_,hfinite⟩ := (mem_finiteSubsets_iff _ _).mp hfin
  apply (mem_conditions B _).mpr
  refine ⟨(mem_finiteSubsets_iff _ _).mpr ⟨fun z hz => (mem_restrict B p z).mp hz |>.2,
    hfinite.subset (fun z hz => (mem_restrict B p z).mp hz |>.1)⟩,?_⟩
  intro x hx b hb c hc hxb hxc
  exact hsv x (hBA hx) b hb c hc ((pair_restrict B p x b).mp hxb).1
    ((pair_restrict B p x c).mp hxc).1

theorem restrict_mono (B p q : ZFSet.{0}) (hpq : p ⊆ q) : restrict B p ⊆ restrict B q := by
  intro z hz
  obtain ⟨hz,hB⟩ := (mem_restrict B p z).mp hz
  exact (mem_restrict B q z).mpr ⟨hpq hz,hB⟩

theorem restrict_eq_self (B p : ZFSet.{0}) (hp : p ∈ conditions B) : restrict B p = p := by
  have hsub := ((mem_finiteSubsets_iff _ _).mp ((mem_conditions B p).mp hp).1).1
  apply ZFSet.ext; intro z
  rw [mem_restrict]
  exact ⟨And.left,fun hz => ⟨hz,hsub hz⟩⟩

def restrictionFormula (B V p q : ℕ) : Formula := .conj (.subset q p)
  (.allMem p (.iff (.member 0 (q+1))
    (.existsMem (B+1) (.existsMem (V+2) (.orderedPair 2 1 0)))))

theorem restrictionFormula_spec (B V p q : ℕ) (e : ℕ → ZFSet.{0}) (hV : e V = alphabet) :
    (restrictionFormula B V p q).Eval e ↔ e q = restrict (e B) (e p) := by
  simp only [restrictionFormula,Formula.eval_subset,Formula.eval_allMem,
    Formula.eval_iff,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,hV]
  constructor
  · rintro ⟨hsub,h⟩
    apply ZFSet.ext; intro z
    exact ⟨fun hz => ZFSet.mem_sep.mpr ⟨hsub hz,(h z (hsub hz)).mp hz⟩,
      fun hz => (h z (ZFSet.mem_sep.mp hz).1).mpr (ZFSet.mem_sep.mp hz).2⟩
  · rintro h
    rw [h]
    exact ⟨fun _ hz => (ZFSet.mem_sep.mp hz).1,
      fun z hz => ZFSet.mem_sep.trans (and_iff_right hz)⟩

noncomputable def restrictionGraph (A B : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.prod (conditions A) (conditions B)).sep (fun z =>
    ∃ p ∈ conditions A, ∃ q ∈ conditions B, z = ZFSet.pair p q ∧ q = restrict B p)

theorem pair_restrictionGraph (A B p q : ZFSet.{0}) :
    ZFSet.pair p q ∈ restrictionGraph A B ↔
      p ∈ conditions A ∧ q ∈ conditions B ∧ q = restrict B p := by
  simp only [restrictionGraph,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,p',hp,q',hq,he,hr⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hp,hq,hr⟩
  · rintro ⟨hp,hq,hr⟩
    exact ⟨ZFSet.pair_mem_prod.mpr ⟨hp,hq⟩,p,hp,q,hq,rfl,hr⟩

theorem restrictionGraph_mem (M A B : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hB : B ∈ M) : restrictionGraph A B ∈ M := by
  have hcA := conditions_mem M A hM hT hA
  have hcB := conditions_mem M B hM hT hB
  let e := cons (conditions A) (cons (conditions B) (cons B (fun _ => alphabet)))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|i
    · exact hcA
    · exact hcB
    · exact hB
    · exact InternalCohen.alphabet_mem M hM hT
  have hh := sep_mem M hM hT.separation.finitePrefix.bounded
    (.existsMem 1 (.existsMem 3 (.conj (.orderedPair 2 1 0) (restrictionFormula 5 6 1 0)))) e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hcA hcB)
  have hs (z p q : ZFSet.{0}) :=
    restrictionFormula_spec 5 6 1 0 (cons q (cons p (cons z e))) rfl
  simpa only [restrictionGraph,Formula.Eval,Formula.eval_orderedPair,
    hs,cons_zero,cons_succ,e] using hh

theorem restrictionGraph_function (A B : ZFSet.{0}) (hBA : B ⊆ A) :
    FunctionGraph (conditions A) (conditions B) (restrictionGraph A B) := by
  constructor
  · intro z hz; exact ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hz).1
  · intro p hp
    refine ⟨restrict B p,restrict_condition A B p hBA hp,
      (pair_restrictionGraph A B p _).mpr ⟨hp,restrict_condition A B p hBA hp,rfl⟩,?_⟩
    intro q _ hq
    exact ((pair_restrictionGraph A B p q).mp hq).2.2

end TuringRigidity.InternalCohenRestriction

end OAI
