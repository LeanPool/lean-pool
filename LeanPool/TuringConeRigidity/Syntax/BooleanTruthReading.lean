/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/BooleanTruthReading.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.BooleanExpressionTruth

/-!
# Boolean Truth Reading
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BooleanExpressionTruth
open TransitiveNameModel BoundedSetTheory CountableForcing
open InternalRegularOperations InternalRegularAlgebra InternalBooleanBits InternalBooleanGeneric
open BooleanExpressionCertificate
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem value_seed (B R U : ZFSet.{0}) (hU : U ∈ B) :
    value B R (FiniteTerm.tag 0 U) ↔ U ∈ R := by
  rw [value_unfold]
  simp [FiniteTerm.tag_inj,hU]

theorem value_neg (B R t : ZFSet.{0}) :
    value B R (FiniteTerm.tag 1 t) ↔ ¬ value B R t := by
  rw [value_unfold]
  simp [FiniteTerm.tag_inj]

theorem value_sup (B R T : ZFSet.{0}) :
    value B R (FiniteTerm.tag 2 T) ↔ ∃ t ∈ T, value B R t := by
  rw [value_unfold]
  simp [FiniteTerm.tag_inj]

theorem certificate_value (M c B Q S K g R : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B)
    (hg : Certificate c B Q S K g)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G)
    (hseed : ∀ U ∈ S, U ∈ R ↔ Hit G U)
    (t U : ZFSet.{0}) (hp : ZFSet.pair t U ∈ g) : value B R t ↔ Hit G U := by
  induction t using rankWF.induction generalizing U with
  | h t ih =>
    have hUB := (hg.step hp).2.1
    rcases (hg.step hp).2.2 with hs | hs | hs
    · obtain ⟨hUS,rfl⟩ := hs
      exact (value_seed B R U hUB).trans (hseed U hUS)
    · obtain ⟨s,_,V,hVB,rfl,hchild,rfl⟩ := hs
      obtain ⟨hVM,hVc⟩ := (hB V).mp hVB
      rw [value_neg,hit_complement_iff M c V hM hT hc hVM hVc G hG,
        ih s (FiniteTerm.pair_rank_right _ _) V hchild]
    · obtain ⟨T,_,F,hFQ,rfl,rfl,hTF,hFT⟩ := hs
      obtain ⟨hFM,hFB⟩ := (hQ F).mp hFQ
      rw [value_sup,hit_supCode_iff M c F hM hT hc hFM (fun V hV => ((hB V).mp (hFB hV)).2) G hG]
      constructor
      · rintro ⟨s,hs,hv⟩
        obtain ⟨V,hVF,hchild⟩ := hTF s hs
        exact ⟨V,hVF,(ih s ((ZFSet.rank_lt_of_mem hs).trans (FiniteTerm.pair_rank_right _ _)) V
          hchild).mp hv⟩
      · rintro ⟨V,hVF,hv⟩
        obtain ⟨s,hs,hchild⟩ := hFT V hVF
        exact ⟨s,hs,(ih s ((ZFSet.rank_lt_of_mem hs).trans (FiniteTerm.pair_rank_right _ _)) V
          hchild).mpr hv⟩

noncomputable def seedTruth (c B : ZFSet.{0}) (E : ℕ → ZFSet.{0}) (X : ZFSet.{0}) : ZFSet.{0} :=
  B.sep (fun U => ∃ n, natSet n ∈ X ∧ U = bitCode c (E n))

theorem seedTruth_mem (N c B : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (hc : c ∈ N) (hB : B ∈ N) (E : ℕ → ZFSet.{0})
    (hE : ∀ n, E n ∈ N ∧ E n ⊆ c) (hgraph : orbitGraph E ∈ N)
    (X : ZFSet.{0}) (hX : X ∈ N) : seedTruth c B E X ∈ N := by
  obtain ⟨Q,hQ,hQdef⟩ := internal_power N hN hT.powerSet hc
  let e := cons c (cons ZFSet.omega (cons Q (cons (orbitGraph E) (fun _ => X))))
  have he : ∀ i, e i ∈ N := by
    intro i; rcases i with _|_|_|_|i
    · exact hc
    · exact sourceT_omega_mem N hN hT
    · exact hQ
    · exact hgraph
    · exact hX
  let φ : Formula := .existsMem 2 (.conj (.member 0 6)
    (.existsMem 4 (.conj (.pairMem 1 0 6) (bitFormula 3 0 2))))
  have spec (U : ZFSet.{0}) : φ.Eval (cons U e) ↔ ∃ n, natSet n ∈ X ∧ U = bitCode c (E n) := by
    simp only [φ,Formula.Eval,Formula.eval_pairMem,bitFormula_spec,e,cons_zero,cons_succ]
    constructor
    · rintro ⟨n,hn,hnX,V,_,hp,hU⟩
      obtain ⟨n,rfl⟩ := (mem_omega n).mp hn
      have hV := (orbitGraph_pair E n V).mp hp
      exact ⟨n,hnX,hV ▸ hU⟩
    · rintro ⟨n,hnX,hU⟩
      exact ⟨natSet n,(mem_omega _).mpr ⟨n,rfl⟩,hnX,E n,(hQdef _).mpr (hE n),
        (orbitGraph_pair E n _).mpr rfl,hU⟩
  have hs := sep_mem N hN hT.separation.finitePrefix.bounded φ e he hB
  simpa only [spec,seedTruth] using hs

theorem seedTruth_hit (M c B : ZFSet.{0}) [Top (Conditions c)]
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M)
    (E : ℕ → ZFSet.{0}) (hE : ∀ n, E n ∈ M ∧ E n ⊆ c)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G)
    (hGt : ⊤ ∈ G.carrier) (U : ZFSet.{0}) (hUS : U ∈ seeds c B E) :
    U ∈ seedTruth c B E ((InternalNiceName.nice E : RecursiveNames.Name (Conditions c)).val
      G.carrier) ↔ Hit G U := by
  constructor
  · intro h
    obtain ⟨_,n,hn,rfl⟩ := ZFSet.mem_sep.mp h
    exact (hit_bit_iff M c hM hT hc E hE G hG hGt n).mpr hn
  · intro h
    obtain ⟨hUB,n,rfl⟩ := ZFSet.mem_sep.mp hUS
    exact ZFSet.mem_sep.mpr ⟨hUB,n,(hit_bit_iff M c hM hT hc E hE G hG hGt n).mp h,rfl⟩

end TuringRigidity.BooleanExpressionTruth

end OAI
