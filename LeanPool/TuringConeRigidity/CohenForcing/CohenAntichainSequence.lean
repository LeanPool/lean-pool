/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenAntichainSequence.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenAntichainStages
public import LeanPool.TuringConeRigidity.Representation.SourceTDependentChoice

/-!
# Cohen Antichain Sequence
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenAntichainSequence
open Set TransitiveNameModel BoundedSetTheory CohenAntichainStages
open CohenGroundPoset CohenConditionCode CohenSizeLevels

def Step (s c U L x y : ZFSet.{0}) : Prop :=
  ∃ n ∈ ZFSet.omega, ∃ E ∈ s, ∃ m ∈ ZFSet.omega, ∃ F ∈ s,
    x = ZFSet.pair n E ∧ y = ZFSet.pair m F ∧ m = insert n n ∧ E ⊆ F ∧
      ∀ p ∈ U, ZFSet.pair n p ∈ L → ∃ q ∈ F, Comp c p q

def stepFormula (ω s c U L x y : ℕ) : Formula :=
  .existsMem ω (.existsMem (s+1) (.existsMem (ω+2) (.existsMem (s+3)
    (.conj (.orderedPair (x+4) 3 2) (.conj (.orderedPair (y+4) 1 0)
      (.conj (.successor 1 3) (.conj (.subset 2 0)
        (.allMem (U+4) (.imp (.pairMem 4 0 (L+5))
          (.existsMem 1 (compFormula (c+6) 1 0)))))))))))

theorem stepFormula_spec (ω s c U L x y : ℕ) (e : ℕ → ZFSet.{0})
    (hω : e ω = ZFSet.omega) :
    (stepFormula ω s c U L x y).Eval e ↔ Step (e s) (e c) (e U) (e L) (e x) (e y) := by
  simp only [stepFormula,Step,Formula.Eval,Formula.eval_orderedPair,
    Formula.eval_successor,Formula.eval_subset,Formula.eval_allMem,Formula.eval_imp,
    Formula.eval_pairMem,compFormula_spec,cons_zero,cons_succ,hω]

noncomputable def relation (s c U L : ZFSet.{0}) : ZFSet.{0} :=
  let d := ZFSet.prod ZFSet.omega s
  (ZFSet.prod d d).sep (fun z => ∃ x ∈ d, ∃ y ∈ d,
    z = ZFSet.pair y x ∧ Step s c U L x y)

theorem pair_relation (s c U L x y : ZFSet.{0}) :
    ZFSet.pair y x ∈ relation s c U L ↔ Step s c U L x y := by
  rw [relation,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,x',_,y',_,he,hs⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact hs
  · intro hs
    have hs' := hs
    obtain ⟨n,hn,E,hE,m,hm,F,hF,hx,hy,_⟩ := hs
    have hxd : x ∈ ZFSet.prod ZFSet.omega s := hx ▸ ZFSet.mem_prod.mpr ⟨n,hn,E,hE,rfl⟩
    have hyd : y ∈ ZFSet.prod ZFSet.omega s := hy ▸ ZFSet.mem_prod.mpr ⟨m,hm,F,hF,rfl⟩
    exact ⟨ZFSet.mem_prod.mpr ⟨y,hyd,x,hxd,rfl⟩,x,hxd,y,hyd,rfl,hs'⟩

theorem relation_mem (M s c U L : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hs : s ∈ M) (hc : c ∈ M) (hU : U ∈ M) (hL : L ∈ M) : relation s c U L ∈ M := by
  let d := ZFSet.prod ZFSet.omega s
  have hd := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded (sourceT_omega_mem M hM hT) hs
  let e := cons ZFSet.omega (cons s (cons c (cons U (cons L (fun _ => d)))))
  let φ : Formula := .existsMem 6 (.existsMem 7 (.conj (.orderedPair 2 0 1)
    (stepFormula 3 4 5 6 7 1 0)))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|_|i
    · exact sourceT_omega_mem M hM hT
    · exact hs
    · exact hc
    · exact hU
    · exact hL
    · exact hd
  have hsep := sep_mem M hM hT.separation.finitePrefix.bounded φ e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hd hd)
  have hφ (z : ZFSet.{0}) : φ.Eval (cons z e) ↔
      ∃ x ∈ d, ∃ y ∈ d, z = ZFSet.pair y x ∧ Step s c U L x y := by
    simp only [φ,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,e]
    apply exists_congr; intro x
    apply and_congr_right; intro _
    apply exists_congr; intro y
    apply and_congr_right; intro _
    apply and_congr_right; intro _
    exact stepFormula_spec 3 4 5 6 7 1 0 _ rfl
  simpa only [hφ,relation] using hsep

theorem internal_sequence (M A U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hU : U ∈ M) (hUc : U ⊆ conditions A) :
    ∃ E : ℕ → ZFSet.{0}, E 0 = ∅ ∧ (∀ n, E n ∈ stages (conditions A) U) ∧
      orbitGraph (fun n => ZFSet.pair (natSet n) (E n)) ∈ M ∧
      (∀ n, E n ⊆ E (n+1)) ∧
      ∀ n p, p ∈ U → Small n p → ∃ q ∈ E (n+1), Comp (conditions A) p q := by
  classical
  let s := stages (conditions A) U
  let d := ZFSet.prod ZFSet.omega s
  have hc := conditions_mem M A hM hT hA
  have hs := stages_mem M _ U hM hT hc hU
  have hd := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded (sourceT_omega_mem M hM hT) hs
  have hserial : ∀ x ∈ d, ∃ y ∈ d, ZFSet.pair y x ∈ relation s (conditions A) U (levels A) := by
    intro x hx
    obtain ⟨n,hn,E,hE,rfl⟩ := ZFSet.mem_prod.mp hx
    obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
    obtain ⟨F,hF,hEF,hpred⟩ := extend_stage A U E hUc hE n
    refine ⟨ZFSet.pair (natSet (n+1)) F,ZFSet.mem_prod.mpr
      ⟨_,(mem_omega _).mpr ⟨n+1,rfl⟩,F,hF,rfl⟩,(pair_relation _ _ _ _ _ _).mpr ?_⟩
    exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,E,hE,natSet (n+1),
      (mem_omega _).mpr ⟨n+1,rfl⟩,F,hF,rfl,rfl,rfl,hEF,
      fun p hp hpn => hpred p hp ((pair_levels A n p).mp hpn).2⟩
  obtain ⟨b,hb0,hb,hbM,hstep⟩ := sourceT_dependent_choice M hM hT hd
    (relation_mem M s (conditions A) U (levels A) hM hT hs hc hU (levels_mem M A hM hT hA))
    (ZFSet.mem_prod.mpr ⟨natSet 0,(mem_omega _).mpr ⟨0,rfl⟩,∅,empty_stage _ _,rfl⟩) hserial
  have shape : ∀ n, ∃ E ∈ s, b n = ZFSet.pair (natSet n) E := by
    intro n
    induction n with
    | zero => exact ⟨∅,empty_stage _ _,hb0⟩
    | succ n ih =>
      obtain ⟨E,_,hE⟩ := ih
      obtain ⟨k,_,F,_,m,_,H,hH,hbk,hbn,hm,_⟩ := (pair_relation _ _ _ _ _ _).mp (hstep n)
      have hk := (ZFSet.pair_inj.mp (hbk.symm.trans hE)).1
      rw [hk] at hm
      exact ⟨H,hH,by rw [hbn,hm]; rfl⟩
  choose E hE hEb using shape
  have h0 : E 0 = ∅ := (ZFSet.pair_inj.mp ((hEb 0).symm.trans hb0)).2
  have b_eq : b = fun n => ZFSet.pair (natSet n) (E n) := funext hEb
  refine ⟨E,h0,hE,b_eq ▸ hbM,?_,?_⟩
  · intro n
    obtain ⟨k,_,F,_,m,_,H,_,hx,hy,_,hFH,_⟩ := (pair_relation _ _ _ _ _ _).mp (hstep n)
    have hf := (ZFSet.pair_inj.mp (hx.symm.trans (hEb n))).2
    have hh := (ZFSet.pair_inj.mp (hy.symm.trans (hEb (n+1)))).2
    rwa [hf,hh] at hFH
  · intro n p hp hsmall
    obtain ⟨k,_,F,_,m,_,H,_,hx,hy,_,_,hpred⟩ := (pair_relation _ _ _ _ _ _).mp (hstep n)
    have hk := (ZFSet.pair_inj.mp (hx.symm.trans (hEb n))).1
    have hh := (ZFSet.pair_inj.mp (hy.symm.trans (hEb (n+1)))).2
    rw [hk,hh] at hpred
    exact hpred p hp ((pair_levels A n p).mpr ⟨hUc hp,hsmall⟩)

end TuringRigidity.CohenAntichainSequence

end OAI
