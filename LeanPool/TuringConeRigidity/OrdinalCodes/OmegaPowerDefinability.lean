/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OmegaPowerDefinability.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.InternalOmegaPower

/-!
# Omega Power Definability
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open BoundedDefinability SetModelFunctions SentenceCoding
universe u

theorem omegaStageStep_exact {M d r f x A : ZFSet.{u}} (hg : OmegaGraph M d r f)
    (hx : x ∈ d) (hs : StageStep (1 : Ordinal.{u}).toZFSet f r x A) :
    A = (Ordinal.omega0 ^ x.rank).toZFSet := by
  apply ZFSet.ext; intro z
  rw [omegaPower_members,(hg.1.mem hx).toZFSet_rank_eq]
  constructor
  · intro hz
    rcases hs.2.1 z hz with hz|⟨y,hy,w,hw,hfw,hz⟩
    · exact Or.inl hz
    · exact Or.inr ⟨y,hy,(hg.correct y (hg.1.subset_of_mem hx hy) w hw hfw) ▸ hz⟩
  · rintro (hz|⟨y,hy,hz⟩)
    · exact hs.1 hz
    · obtain ⟨w,hw,hfw,_⟩ := hg.2.1.2 y (hg.1.subset_of_mem hx hy)
      rw [← hg.correct y (hg.1.subset_of_mem hx hy) w hw hfw] at hz
      exact hs.2.2 y hy w hw hfw hz

theorem omegaPower_sigmaDefinable (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    SigmaDefinable M (fun e => (e 1).IsOrdinal ∧ e 0 = (Ordinal.omega0 ^ (e 1).rank).toZFSet) := by
  let C : Context M :=
    ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩
  have h1 : (1 : Ordinal.{u}).toZFSet ∈ M := by
    rw [← Nat.cast_one,toZFSet_nat]; exact C.nat_mem 1
  have hd : Definable M (fun e => e 0 = insert (e 4) (e 4)) := by
    refine ⟨.successor 0 8,fun _ => ZFSet.omega,fun _ => C.omega_mem,?_⟩
    intro e; simp [Formula.eval_successor,mix]
  have hs : SigmaDefinable M (fun e =>
      StageStep (1 : Ordinal.{u}).toZFSet (e 2) (e 1) (e 4) (e 3)) := by
    have hb := (stageStep_definable C 0 3 2 5 4).toSigma hM
    exact (((equal_param h1 0).toSigma hM).and hb).existsSet.congr (fun e _ => by simp [h1])
  have hg := (hd.toSigma hM).and ((omegaGraph_sigmaDefinable M hM hT 0 1 2).and hs)
  apply hg.existsSet.existsSet.existsSet.congr
  intro e he
  change (∃ f ∈ M, ∃ r ∈ M, ∃ d ∈ M,
    d = insert (e 1) (e 1) ∧ OmegaGraph M d r f ∧
      StageStep (1 : Ordinal.{u}).toZFSet f r (e 1) (e 0)) ↔ _
  constructor
  · rintro ⟨f,_,r,_,d,_,rfl,hg,hs⟩
    have hx : e 1 ∈ insert (e 1) (e 1) := ZFSet.mem_insert_iff.mpr (Or.inl rfl)
    exact ⟨hg.1.mem hx,omegaStageStep_exact hg hx hs⟩
  · rintro ⟨ho,hy⟩
    obtain ⟨f,hf,hg⟩ := internal_omegaGraph M hM hT (e 1) (he 1) ho
    have hx : e 1 ∈ insert (e 1) (e 1) := ZFSet.mem_insert_iff.mpr (Or.inl rfl)
    obtain ⟨v,hv,hfv,_⟩ := hg.2.1.2 (e 1) hx
    obtain ⟨A,_,hA,_⟩ := hg.2.2 (e 1) hx v hv hfv
    have hAy : A = e 0 := (omegaStageStep_exact hg hx hA).trans hy.symm
    exact ⟨f,hf,_,iterUnion_mem M hM hT.union hf 2,_,
      insert_self_mem M hM hT.pairing hT.union (he 1),rfl,hg,hAy ▸ hA⟩

theorem uniform_omega_power (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) :
    ∃ p : SigmaFormula, ∃ e : ℕ → ZFSet.{u}, (∀ i, e i ∈ M) ∧
      ∀ x ∈ M, ∀ y ∈ M, p.Realize M (cons y (cons x e)) ↔
        x.IsOrdinal ∧ y = (Ordinal.omega0 ^ x.rank).toZFSet :=
  sigma_binary_relation _ (omegaPower_sigmaDefinable M hM hT)

theorem omega_power_image_internal (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (a : Ordinal.{u}) (ha : a.toZFSet ∈ M) :
    ∃ b ∈ M, ∀ y, y ∈ b ↔ ∃ c < a, y = (Ordinal.omega0 ^ c).toZFSet := by
  obtain ⟨p,e,he,hp⟩ := uniform_omega_power M hM hT
  obtain ⟨b,hb,hdef⟩ := replacement_image M hM hT.replacement.finitePrefix p e he ha
    (fun x => (Ordinal.omega0 ^ x.rank).toZFSet) (by
      intro x hx
      obtain ⟨c,hc,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hx
      rw [Ordinal.rank_toZFSet]
      exact ordinal_omega_opow_internal M hM hT c
        (hM _ ha _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr hc))) (by
      intro x hx y hy
      rw [hp x (hM _ ha x hx) y hy]
      exact and_iff_right ((ZFSet.isOrdinal_toZFSet a).mem hx))
  refine ⟨b,hb,?_⟩
  intro y
  rw [hdef y]
  constructor
  · rintro ⟨x,hx,hy⟩
    obtain ⟨c,hc,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hx
    exact ⟨c,hc,by simpa using hy.symm⟩
  · rintro ⟨c,hc,rfl⟩
    exact ⟨c.toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr hc,by rw [Ordinal.rank_toZFSet]⟩

end TuringRigidity.OrdinalArithmetic

end OAI
