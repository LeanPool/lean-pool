/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenCountedAntichain.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenInternalAntichain
public import LeanPool.TuringConeRigidity.SetModels.InternalCountableFiniteUnion

/-!
# Cohen Counted Antichain
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenCountedAntichain
open Set TransitiveNameModel BoundedSetTheory InternalFiniteSubsets
open CohenAntichainStages CohenAntichainSequence CohenInternalAntichain CohenGroundPoset

theorem project_sequence (M S : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hS : S ∈ M) (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ S)
    (hB : orbitGraph (fun n => ZFSet.pair (natSet n) (E n)) ∈ M) : orbitGraph E ∈ M := by
  let B := orbitGraph (fun n => ZFSet.pair (natSet n) (E n))
  let e := cons ZFSet.omega (cons S (fun _ => B))
  let φ : Formula := .existsMem 1 (.existsMem 3
    (.conj (.orderedPair 2 1 0) (.pairMem 1 2 5)))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|i
    · exact sourceT_omega_mem M hM hT
    · exact hS
    · exact hB
  have hφ (z : ZFSet.{0}) : φ.Eval (cons z e) ↔ z ∈ orbitGraph E := by
    simp only [φ,Formula.Eval,Formula.eval_orderedPair,Formula.eval_pairMem,cons_zero,cons_succ,e]
    constructor
    · rintro ⟨n,hn,F,_,hz,hnz⟩
      obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
      have hh := (orbitGraph_pair (fun n => ZFSet.pair (natSet n) (E n)) n z).mp hnz
      exact (mem_orbitGraph E z).mpr ⟨n,hh⟩
    · intro hz
      obtain ⟨n,rfl⟩ := (mem_orbitGraph E z).mp hz
      exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,E n,hE n,rfl,(orbitGraph_pair _ n _).mpr rfl⟩
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded φ e he
    (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
      (sourceT_omega_mem M hM hT) hS)
  have heq : (ZFSet.prod ZFSet.omega S).sep (fun z => φ.Eval (cons z e)) = orbitGraph E := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sep,hφ]
    exact ⟨And.right,fun hz => ⟨ZFSet.mem_prod.mpr ((orbitGraph_function S E hE).1 z hz),hz⟩⟩
  exact heq ▸ hs

theorem internal_counted_antichain (M A U : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (hU : U ∈ M) (hUc : U ⊆ conditions A) :
    ∃ F ∈ M, F ⊆ U ∧ Anti (conditions A) F ∧
      (∀ p ∈ U, ∃ q ∈ F, Comp (conditions A) p q) ∧
      (F = ∅ ∨ InternallyCountable M F) := by
  classical
  obtain ⟨E,_,hE,hg,hstep,hpred⟩ := internal_sequence M A U hM hT hA hU hUc
  have hc := conditions_mem M A hM hT hA
  obtain ⟨F,hFM,hF⟩ := stage_union_internal M (conditions A) U hM hT hc hU E hE hg
  have hmono : ∀ n m, n ≤ m → E n ⊆ E m := by
    intro n m hnm
    induction hnm with
    | refl => exact fun _ h => h
    | @step m _ ih => exact fun _ h => hstep m (ih h)
  refine ⟨F,hFM,?_,?_,?_,?_⟩
  · intro p hp
    obtain ⟨n,hn⟩ := (hF p).mp hp
    exact ((mem_stages _ _ _).mp (hE n)).1.1 hn
  · intro p hp q hq hpq hcomp
    obtain ⟨n,hn⟩ := (hF p).mp hp
    obtain ⟨m,hm⟩ := (hF q).mp hq
    exact ((mem_stages _ _ _).mp (hE (max n m))).2 p
      (hmono n _ (Nat.le_max_left _ _) hn) q (hmono m _ (Nat.le_max_right _ _) hm) hpq hcomp
  · intro p hp
    obtain ⟨p,rfl⟩ := (CohenConditionCode.isCondition_iff_graph A p).mp
      ((mem_conditions A p).mp (hUc hp))
    obtain ⟨q,hq,hpq⟩ := hpred _ (CohenConditionCode.graph A p) hp (CohenSizeLevels.graph_small A p)
    exact ⟨q,(hF q).mpr ⟨_,hq⟩,hpq⟩
  · by_cases hempty : F = ∅
    · exact Or.inl hempty
    · right
      apply InternalCountableFiniteUnion.internally_countable_union M F hM hT hFM E
      · intro n
        exact (mem_finiteSubsets_iff F (E n)).mpr
          ⟨fun p hp => (hF p).mpr ⟨n,hp⟩,((mem_stages _ _ _).mp (hE n)).1.2⟩
      · exact project_sequence M (stages (conditions A) U) hM hT
          (stages_mem M _ U hM hT hc hU) E hE hg
      · exact fun p hp => (hF p).mp hp
      · by_contra h
        apply hempty
        apply ZFSet.ext; intro p
        exact ⟨fun hp => False.elim (h ⟨p,hp⟩),fun hp => False.elim (ZFSet.notMem_empty p hp)⟩

theorem every_internal_antichain_counted (M A E : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (hE : E ∈ M) (hEc : E ⊆ conditions A)
    (ha : Anti (conditions A) E) : E = ∅ ∨ InternallyCountable M E := by
  obtain ⟨F,_,hFE,_,hpred,hcount⟩ := internal_counted_antichain M A E hM hT hA hE hEc
  have he : F = E := by
    apply ZFSet.ext; intro p
    refine ⟨fun hp => hFE hp,fun hp => ?_⟩
    obtain ⟨q,hq,hpq⟩ := hpred p hp
    have hpq' : p = q := Classical.byContradiction (fun hn => ha p hp q (hFE hq) hn hpq)
    exact hpq' ▸ hq
  exact he ▸ hcount

end TuringRigidity.CohenCountedAntichain

end OAI
