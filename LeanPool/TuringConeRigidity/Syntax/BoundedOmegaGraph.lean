/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/BoundedOmegaGraph.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.FiniteStageSetBounds
public import LeanPool.TuringConeRigidity.OrdinalCodes.LimitOmegaGraphSyntax
public import LeanPool.TuringConeRigidity.SetModels.ExactOmegaGraph

/-!
# Bounded Omega Graph
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
  OrdinalCoding
universe u

/-- Add a bounded-coordinate witness to the full omega-successor-pair definition. -/
noncomputable def boundedOmegaNextPairSentence : SentenceForm :=
  .conj (.ex (.conj (.member 0 2) (.ex (fromBounded (.orderedPair 2 1 0))))) omegaNextPairSentence

theorem boundedOmegaNextPairSentence_spec (A : ZFSet.{u}) (hA : Transitive A)
    (hω : ZFSet.omega.{u} ∈ A) (a : Ordinal.{u}) (ha : Order.IsSuccLimit a)
    (haA : a.toZFSet ∈ A)
    (hpow : ∀ c < a, (Ordinal.omega0 ^ c).toZFSet ∈ A ∧ OmegaPowerCertificates A c.toZFSet)
    (z : ZFSet.{u}) (hz : z ∈ A) :
    boundedOmegaNextPairSentence.Sat (A : Set ZFSet) (cons z (fun _ => a.toZFSet)) ↔
      ∃ x ∈ a.toZFSet, z = ZFSet.pair x (omegaNext x) := by
  let e := cons z (fun _ => a.toZFSet)
  have he (i : ℕ) : e i ∈ A := by
    cases i
    · exact hz
    · exact haA
  have hbound : (SentenceForm.ex (.conj (.member 0 2) (.ex (fromBounded (.orderedPair 2 1 0))))).Sat
      (A : Set ZFSet) e ↔ ∃ x ∈ a.toZFSet, ∃ y ∈ A, z = ZFSet.pair x y := by
    change (∃ x ∈ A, x ∈ a.toZFSet ∧ ∃ y ∈ A,
      (fromBounded (.orderedPair 2 1 0)).Sat (A : Set ZFSet) (cons y (cons x e))) ↔ _
    have hp (x y : ZFSet.{u}) (hx : x ∈ A) (hy : y ∈ A) :
        (fromBounded (.orderedPair 2 1 0)).Sat (A : Set ZFSet) (cons y (cons x e)) ↔
          z = ZFSet.pair x y := by
      rw [bounded_sat,Formula.absolute _ A hA _ (by
        intro i
        rcases i with _ | _ | i
        · exact hy
        · exact hx
        · exact he i)]
      exact Formula.eval_orderedPair _ _ _ _
    constructor
    · rintro ⟨x,hx,hxa,y,hy,h⟩
      exact ⟨x,hxa,y,hy,(hp x y hx hy).mp h⟩
    · rintro ⟨x,hx,y,hy,h⟩
      have hxA := hA _ haA _ hx
      exact ⟨x,hxA,hx,y,hy,(hp x y hxA hy).mpr h⟩
  change (_ ∧ omegaNextPairSentence.Sat (A : Set ZFSet) e) ↔ _
  rw [hbound,omegaNextPairSentence_semantics A hA e he]
  constructor
  · rintro ⟨⟨x,hx,y,hy,hzxy⟩,x',hx',y',hy',k,hk,⟨ho,hks,hzp⟩,hp⟩
    have heq : ZFSet.pair x y = ZFSet.pair x' y' := hzxy.symm.trans hzp
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp heq
    have hv := (codePowerAt_sound A hA hω 1 0 _ (by
      intro i; rcases i with _|_|_|i
      · exact hk
      · exact hy'
      · exact hx'
      · exact he i) hp).2
    change y = (Ordinal.omega0 ^ k.rank).toZFSet at hv
    have hsucc : k = (x.rank+1).toZFSet := by
      rw [Ordinal.toZFSet_add_one,ho.toZFSet_rank_eq,hks]
    rw [hsucc,Ordinal.rank_toZFSet] at hv
    exact ⟨x,hx,hzxy.trans (congrArg (ZFSet.pair x) hv)⟩
  · rintro ⟨x,hx,hzdef⟩
    obtain ⟨c,hc,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hx
    have hc : c < a := by simpa only [Ordinal.toZFSet_mem_toZFSet_iff] using hc
    have hs : c+1 < a := ha.succ_lt hc
    have hxA := hA _ haA _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr hc)
    have hk := hA _ haA _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr hs)
    obtain ⟨hy,hcert⟩ := hpow (c+1) hs
    have hzdef' : z = ZFSet.pair c.toZFSet (Ordinal.omega0 ^ (c+1)).toZFSet := by
      simpa only [omegaNext,Ordinal.rank_toZFSet] using hzdef
    refine ⟨⟨c.toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr hc,_,hy,hzdef'⟩,
      c.toZFSet,hxA,_,hy,(c+1).toZFSet,hk,
      ⟨ZFSet.isOrdinal_toZFSet _,Ordinal.toZFSet_add_one c,hzdef'⟩,?_⟩
    apply codePowerAt_of_certificates A hA hω 1 0 _ (fun i => by
      rcases i with _ | _ | _ | i
      · exact hk
      · exact hy
      · exact hxA
      · exact he i) hcert
    simp only [cons_zero,cons_succ,Ordinal.rank_toZFSet]

theorem omega_limit_certificates_at_add_five (R : ZFSet.{u}) (γ a : Ordinal.{u})
    (ha : Order.IsSuccLimit a) (haA : a.toZFSet ∈ level R γ)
    (hω : ZFSet.omega.{u} ∈ level R γ)
    (hpow : ∀ c < a, (Ordinal.omega0 ^ c).toZFSet ∈ level R γ ∧
      OmegaPowerCertificates (level R γ) c.toZFSet) :
    OmegaPowerCertificates (level R (γ+5)) a.toZFSet := by
  let A := level R (γ+2)
  let f := A.sep (fun z => boundedOmegaNextPairSentence.Sat (A : Set ZFSet)
    (cons z (fun _ => a.toZFSet)))
  have h02 : γ ≤ γ+2 := le_self_add
  have h25 : γ+2 ≤ γ+5 := add_le_add le_rfl (by exact_mod_cast (show (2 : ℕ) ≤ 5 by decide))
  have h05 := h02.trans h25
  have h35 : γ+3 ≤ γ+5 := add_le_add le_rfl (by exact_mod_cast (show (3 : ℕ) ≤ 5 by decide))
  have ha2 := level_mono R h02 haA
  have hpow2 (c : Ordinal.{u}) (hc : c < a) :
      (Ordinal.omega0 ^ c).toZFSet ∈ A ∧ OmegaPowerCertificates A c.toZFSet :=
    ⟨level_mono R h02 (hpow c hc).1,(hpow c hc).2.mono (level_mono R h02)⟩
  have hspec := boundedOmegaNextPairSentence_spec A (level_transitive R (γ+2))
    (level_mono R h02 hω) a ha ha2 hpow2
  have hf : f ∈ level R (γ+3) := by
    have h := separation_mem_definablePower A boundedOmegaNextPairSentence (fun _ => a.toZFSet)
      (fun _ _ => ha2)
    change f ∈ definablePower A at h
    have h' : f ∈ level R (γ+2+1) := by rw [level_succ]; exact h
    simpa only [add_assoc,show (2 : Ordinal.{u})+1=3 by norm_num] using h'
  have hexact (z : ZFSet.{u}) : z ∈ f ↔ ∃ x ∈ a.toZFSet, z = ZFSet.pair x (omegaNext x) := by
    change z ∈ A.sep _ ↔ _
    rw [ZFSet.mem_sep]
    constructor
    · rintro ⟨hz,h⟩; exact (hspec z hz).mp h
    · rintro ⟨x,hx,rfl⟩
      obtain ⟨c,hc,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hx
      have hc : c < a := by simpa only [Ordinal.toZFSet_mem_toZFSet_iff] using hc
      have hy : omegaNext c.toZFSet ∈ level R γ := by
        simpa only [omegaNext,Ordinal.rank_toZFSet] using (hpow (c+1) (ha.succ_lt hc)).1
      have hz := orderedPair_mem_level_add_two R γ
        (level_transitive R γ _ haA _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr hc)) hy
      exact ⟨hz,(hspec _ hz).mpr ⟨_,Ordinal.toZFSet_mem_toZFSet_iff.mpr hc,rfl⟩⟩
  have hr : iterUnion 2 f ∈ level R (γ+5) := by
    simpa only [Nat.cast_ofNat,add_assoc,show (3 : Ordinal.{u})+2=5 by norm_num] using
      iterUnion_mem_level_add R (γ+3) hf 2
  refine ⟨level_mono R h05 haA,f,level_mono R h35 hf,_,hr,
    omegaGraph_of_exact_pairs _ _ f (ZFSet.isOrdinal_toZFSet a) hexact ?_,?_⟩
  · intro x hx
    obtain ⟨c,hc,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hx
    rw [Ordinal.rank_toZFSet]
    exact level_mono R h05 (hpow c hc).1
  · intro x hx
    obtain ⟨c,hc,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hx
    obtain ⟨_,g,hg,r,hr,hgraph,hprod⟩ := (hpow (c+1) (ha.succ_lt hc)).2
    exact (hprod c.toZFSet (Ordinal.toZFSet_mem_toZFSet_iff.mpr (lt_add_one c))).mono
      (level_mono R h05)

end TuringRigidity.OrdinalArithmetic

end OAI
