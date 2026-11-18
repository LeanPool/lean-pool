/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenInternalAntichain.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenAntichainSequence

/-!
# Cohen Internal Antichain
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenInternalAntichain
open Set TransitiveNameModel BoundedSetTheory CohenAntichainStages
open CohenAntichainSequence CohenGroundPoset CohenConditionCode CohenSizeLevels

theorem stage_union_internal (M c U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hU : U ∈ M) (E : ℕ → ZFSet.{0})
    (hE : ∀ n, E n ∈ stages c U)
    (hgraph : orbitGraph (fun n => ZFSet.pair (natSet n) (E n)) ∈ M) :
    ∃ F ∈ M, ∀ p, p ∈ F ↔ ∃ n, p ∈ E n := by
  let s := stages c U
  let d := ZFSet.prod ZFSet.omega s
  let g := orbitGraph (fun n => ZFSet.pair (natSet n) (E n))
  have hs := stages_mem M c U hM hT hc hU
  have hd := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded (sourceT_omega_mem M hM hT) hs
  let e := cons ZFSet.omega (cons s (cons d (fun _ => g)))
  let φ : Formula := .existsMem 1 (.existsMem 3 (.existsMem 5
    (.conj (.orderedPair 0 2 1) (.conj (.pairMem 2 0 7) (.member 3 1)))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|i
    · exact sourceT_omega_mem M hM hT
    · exact hs
    · exact hd
    · exact hgraph
  have hφ (p : ZFSet.{0}) : φ.Eval (cons p e) ↔ ∃ n, p ∈ E n := by
    simp only [φ,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨n,hn,F,_,t,_,ht,hnt,hp⟩
      obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
      have ht' := (orbitGraph_pair (fun n => ZFSet.pair (natSet n) (E n)) n t).mp hnt
      have hF := (ZFSet.pair_inj.mp (ht.symm.trans ht')).2
      exact ⟨n,hF ▸ hp⟩
    · rintro ⟨n,hp⟩
      exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,E n,hE n,
        ZFSet.pair (natSet n) (E n),ZFSet.mem_prod.mpr
          ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,E n,hE n,rfl⟩,
        rfl,(orbitGraph_pair _ n _).mpr rfl,hp⟩
  refine ⟨U.sep (fun p => φ.Eval (cons p e)),
    sep_mem M hM hT.separation.finitePrefix.bounded φ e he hU,?_⟩
  intro p
  rw [ZFSet.mem_sep,hφ]
  exact ⟨And.right,fun ⟨n,hp⟩ => ⟨((mem_stages _ _ _).mp (hE n)).1.1 hp,n,hp⟩⟩

theorem internal_predense_antichain (M A U : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hA : A ∈ M) (hU : U ∈ M)
    (hUc : U ⊆ conditions A) :
    ∃ F ∈ M, F ⊆ U ∧ Anti (conditions A) F ∧
      ∀ p ∈ U, ∃ q ∈ F, Comp (conditions A) p q := by
  obtain ⟨E,_,hE,hg,hstep,hpred⟩ := internal_sequence M A U hM hT hA hU hUc
  obtain ⟨F,hFM,hF⟩ := stage_union_internal M (conditions A) U hM hT
    (conditions_mem M A hM hT hA) hU E hE hg
  have hmono : ∀ n m, n ≤ m → E n ⊆ E m := by
    intro n m hnm
    induction hnm with
    | refl => exact fun _ h => h
    | @step m _ ih => exact fun _ h => hstep m (ih h)
  refine ⟨F,hFM,?_,?_,?_⟩
  · intro p hp
    obtain ⟨n,hn⟩ := (hF p).mp hp
    exact ((mem_stages _ _ _).mp (hE n)).1.1 hn
  · intro p hp q hq hpq hc
    obtain ⟨n,hn⟩ := (hF p).mp hp
    obtain ⟨m,hm⟩ := (hF q).mp hq
    exact ((mem_stages _ _ _).mp (hE (max n m))).2 p
      (hmono n _ (Nat.le_max_left _ _) hn) q (hmono m _ (Nat.le_max_right _ _) hm) hpq hc
  · intro p hp
    obtain ⟨p,rfl⟩ := (isCondition_iff_graph A p).mp ((mem_conditions A p).mp (hUc hp))
    obtain ⟨q,hq,hpq⟩ := hpred _ (graph A p) hp (graph_small A p)
    exact ⟨q,(hF q).mpr ⟨_,hq⟩,hpq⟩

end TuringRigidity.CohenInternalAntichain

end OAI
