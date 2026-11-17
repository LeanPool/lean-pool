/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OmegaPowerSyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OmegaGraphSyntax
public import LeanPool.TuringConeRigidity.OrdinalCodes.CanonicalOmegaSyntax
public import LeanPool.TuringConeRigidity.OrdinalCodes.OmegaGraphRestriction

/-!
# Omega Power Syntax
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
universe u

def ordinalOneMatrix (s : ℕ) : Formula :=
  .conj (.allMem s (.empty 0)) (.existsMem s (.empty 0))

theorem ordinalOneMatrix_eval (s : ℕ) (e : ℕ → ZFSet.{u}) :
    (ordinalOneMatrix s).Eval e ↔ e s = (1 : Ordinal.{u}).toZFSet := by
  have hone : (1 : Ordinal.{u}).toZFSet = ({∅} : ZFSet.{u}) := by
    rw [← Nat.cast_one,toZFSet_nat]; rfl
  rw [hone]
  simp only [ordinalOneMatrix,Formula.Eval,Formula.eval_allMem,Formula.eval_empty,cons_zero]
  constructor
  · rintro ⟨hall,x,hx,rfl⟩
    apply ZFSet.ext; intro z
    simp only [ZFSet.mem_singleton]
    exact ⟨hall z,fun h => h.symm ▸ hx⟩
  · intro he
    rw [he]
    exact ⟨fun z hz => ZFSet.mem_singleton.mp hz,∅,ZFSet.mem_singleton.mpr rfl,rfl⟩

noncomputable def omegaPowerBody : SentenceForm :=
  .conj (canonicalOmega 4)
    (.conj (fromBounded (.conj (ordinalOneMatrix 3) (.equal 0 6)))
      (.conj (omegaGraphSentence 3 4 0 1 2)
        (fromBounded (omegaStageMatrix 3 2 1 6 5))))

noncomputable def omegaPowerSentence : SentenceForm :=
  .ex (.ex (.ex (.ex (.ex omegaPowerBody))))

theorem omegaPowerSentence_bound : omegaPowerSentence.bound = 2 := by rfl

theorem omegaPowerBody_semantics (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    omegaPowerBody.Sat (M : Set ZFSet) e ↔
      e 4 = ZFSet.omega ∧ e 3 = (1 : Ordinal.{u}).toZFSet ∧
      e 0 = e 6 ∧
      (omegaGraphSentence 3 4 0 1 2).Sat (M : Set ZFSet) e ∧
      StageStep (e 3) (e 2) (e 1) (e 6) (e 5) := by
  change ((canonicalOmega 4).Sat _ e ∧ (fromBounded _).Sat _ e ∧
    (omegaGraphSentence 3 4 0 1 2).Sat _ e ∧ (fromBounded _).Sat _ e) ↔ _
  rw [canonicalOmega_spec M hM hω 4 e he,bounded_sat,
    Formula.absolute _ M hM e he,Formula.Eval,ordinalOneMatrix_eval,
    Formula.Eval,bounded_sat,Formula.absolute _ M hM e he,omegaStageMatrix_eval]
  tauto

theorem omegaPowerSentence_semantics (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    omegaPowerSentence.Sat (M : Set ZFSet) e ↔
      ∃ w ∈ M, ∃ s ∈ M, ∃ f ∈ M, ∃ r ∈ M, ∃ d ∈ M,
        w = ZFSet.omega ∧ s = (1 : Ordinal.{u}).toZFSet ∧ d = e 1 ∧
        (omegaGraphSentence 3 4 0 1 2).Sat (M : Set ZFSet)
          (cons d (cons r (cons f (cons s (cons w e))))) ∧
        StageStep s f r (e 1) (e 0) := by
  change (∃ w ∈ M, ∃ s ∈ M, ∃ f ∈ M, ∃ r ∈ M, ∃ d ∈ M,
    omegaPowerBody.Sat _ _) ↔ _
  apply exists_congr; intro w
  apply and_congr_right; intro hw
  apply exists_congr; intro s
  apply and_congr_right; intro hs
  apply exists_congr; intro f
  apply and_congr_right; intro hf
  apply exists_congr; intro r
  apply and_congr_right; intro hr
  apply exists_congr; intro d
  apply and_congr_right; intro hd
  exact omegaPowerBody_semantics M hM hω _ (by
    intro i; rcases i with _|_|_|_|_|i
    · exact hd
    · exact hr
    · exact hf
    · exact hs
    · exact hw
    · exact he i)

theorem omegaPowerSentence_sound (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    omegaPowerSentence.Sat (M : Set ZFSet) e →
      (e 1).IsOrdinal ∧ e 0 = (Ordinal.omega0 ^ (e 1).rank).toZFSet := by
  rw [omegaPowerSentence_semantics M hM hω e he]
  rintro ⟨w,hw,s,hs,f,hf,r,hr,d,hd,hew,hes,hed,hg,hst⟩
  have hgraph := omegaGraphSentence_sound M hM 3 4 0 1 2 _ (by
    intro i; rcases i with _|_|_|_|_|i
    · exact hd
    · exact hr
    · exact hf
    · exact hs
    · exact hw
    · exact he i) hes hew hg
  change OmegaGraph M d r f at hgraph
  rw [hed] at hgraph
  exact ⟨hgraph.1,omegaStageStep_domain_exact hgraph (hes ▸ hst)⟩

theorem omegaPowerSentence_sourceT (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    omegaPowerSentence.Sat (M : Set ZFSet) e ↔
      (e 1).IsOrdinal ∧ e 0 = (Ordinal.omega0 ^ (e 1).rank).toZFSet := by
  have hω := omega_mem M hM hT.separation.finitePrefix.bounded hT.infinity
  refine ⟨omegaPowerSentence_sound M hM hω e he,?_⟩
  rintro ⟨ho,hy⟩
  obtain ⟨f,hf,hg⟩ := internal_omegaGraph_below M hM hT (e 1) (he 1) ho
  have hs : (1 : Ordinal.{u}).toZFSet ∈ M := by
    rw [← Nat.cast_one,toZFSet_nat]
    exact hM _ hω _ ((mem_omega _).mpr ⟨1,rfl⟩)
  have hr := iterUnion_mem M hM hT.union hf 2
  have hst := omegaStageStep_domain M (e 1) (iterUnion 2 f) f hg
  apply (omegaPowerSentence_semantics M hM hω e he).mpr
  refine ⟨_,hω,_,hs,f,hf,_,hr,e 1,he 1,rfl,rfl,rfl,?_,hy.symm ▸ hst⟩
  exact (omegaGraphSentence_sourceT M hM hT 3 4 0 1 2 _ (by
    intro i; rcases i with _|_|_|_|_|i
    · exact he 1
    · exact hr
    · exact hf
    · exact hs
    · exact hω
    · exact he i) rfl rfl).mpr hg

end TuringRigidity.OrdinalArithmetic

end OAI
