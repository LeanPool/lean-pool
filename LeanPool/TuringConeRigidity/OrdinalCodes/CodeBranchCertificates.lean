/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/CodeBranchCertificates.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.CodeOperationCertificates
public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalPairSyntax

/-!
# Code Branch Certificates
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
  OrdinalArithmetic
universe u

def CodeBranchCertificates (M : ZFSet.{u}) (twice : Bool) (a b : Ordinal.{u}) : Prop :=
  (a+1).toZFSet ∈ M ∧ (Ordinal.omega0 ^ (a+1)).toZFSet ∈ M ∧
    (Ordinal.omega0 ^ b).toZFSet ∈ M ∧
    (codeScale twice (Ordinal.omega0 ^ (a+1))).toZFSet ∈ M ∧
    OmegaPowerCertificates M (a+1).toZFSet ∧ OmegaPowerCertificates M b.toZFSet ∧
    (twice = true → SumCertificates M (Ordinal.omega0 ^ (a+1)) (Ordinal.omega0 ^ (a+1))) ∧
    SumCertificates M (codeScale twice (Ordinal.omega0 ^ (a+1))) (Ordinal.omega0 ^ b)

theorem CodeBranchCertificates.mono {M N : ZFSet.{u}} {twice : Bool} {a b : Ordinal.{u}}
    (h : CodeBranchCertificates M twice a b) (hMN : M ⊆ N) : CodeBranchCertificates N twice a b :=
      by
  obtain ⟨hk,hu,hv,ht,hp,hq,hd,hs⟩ := h
  exact ⟨hMN hk,hMN hu,hMN hv,hMN ht,hp.mono hMN,hq.mono hMN,
    fun h => (hd h).mono hMN,hs.mono hMN⟩

theorem codeBranchSentence_of_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (twice : Bool) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (a b : Ordinal.{u}) (ha : e 1 = a.toZFSet) (hb : e 2 = b.toZFSet)
    (hcert : CodeBranchCertificates M twice a b)
    (hc : e 0 = (codeBranchValue twice a b).toZFSet) :
    (codeBranchSentence twice).Sat (M : Set ZFSet) e := by
  obtain ⟨hk,hu,hv,ht,hp,hq,hd,hs⟩ := hcert
  let k := (a+1).toZFSet
  let u := (Ordinal.omega0 ^ (a+1)).toZFSet
  let v := (Ordinal.omega0 ^ b).toZFSet
  let t := (codeScale twice (Ordinal.omega0 ^ (a+1))).toZFSet
  let E := cons t (cons v (cons u (cons k e)))
  have hE : ∀ i, E i ∈ M := by
    intro i; rcases i with _|_|_|_|i
    · exact ht
    · exact hv
    · exact hu
    · exact hk
    · exact he i
  refine ⟨k,hk,u,hu,v,hv,t,ht,?_,?_,?_,?_,?_⟩
  · rw [bounded_sat,Formula.absolute _ M hM E hE,Formula.eval_successor]
    change k = insert (e 1) (e 1)
    rw [ha,← Ordinal.toZFSet_add_one]
  · apply codePowerAt_of_certificates M hM hω 2 3 E hE hp
    simp [E,u,k]
  · apply codePowerAt_of_certificates M hM hω 1 6 E hE
    · simpa only [E,cons_succ,hb] using hq
    · simp [E,v,hb]
  · exact codeScaleAt_of_certificates M hM hω twice 0 2 E hE _ rfl hd rfl
  · exact codeSumAt_of_certificates M hM hω 4 0 1 E hE _ _ rfl rfl hs hc

def PairCodeCertificates (M : ZFSet.{u}) (a b : Ordinal.{u}) : Prop :=
  if b ≤ a then CodeBranchCertificates M false a b else CodeBranchCertificates M true b a

theorem PairCodeCertificates.mono {M N : ZFSet.{u}} {a b : Ordinal.{u}}
    (h : PairCodeCertificates M a b) (hMN : M ⊆ N) : PairCodeCertificates N a b := by
  unfold PairCodeCertificates at h ⊢
  split <;> rename_i hc
  · exact (by simpa only [ite_eq_left hc] using h : CodeBranchCertificates M false a b).mono hMN
  · exact (by simpa only [ite_eq_right hc] using h : CodeBranchCertificates M true b a).mono hMN

theorem pairCodeSentence_of_certificates (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (a b : Ordinal.{u}) (ha : e 1 = a.toZFSet) (hb : e 2 = b.toZFSet)
    (hcert : PairCodeCertificates M a b) (hc : e 0 = (pairCode a b).toZFSet) :
    pairCodeSentence.Sat (M : Set ZFSet) e := by
  apply (pairCodeSentence_semantics M hM e he).mpr
  refine ⟨⟨ha.symm ▸ ZFSet.isOrdinal_toZFSet _,hb.symm ▸ ZFSet.isOrdinal_toZFSet _⟩,?_⟩
  have hsub : e 2 ⊆ e 1 ↔ b ≤ a := by rw [ha,hb,Ordinal.toZFSet_subset_toZFSet_iff]
  by_cases hle : b ≤ a
  · left
    refine ⟨hsub.mpr hle,codeBranchSentence_of_certificates M hM hω false e he a b ha hb ?_ ?_⟩
    · simpa only [PairCodeCertificates,ite_eq_left hle] using hcert
    · simpa only [pairCode, ite_eq_left hle, codeBranchValue, codeScale,
        Bool.false_eq_true, ↓reduceIte] using hc
  · right
    refine ⟨fun h => hle (hsub.mp h),codeBranchSentence_of_certificates M hM hω true
      (fun i => e (if i = 0 then 0 else if i = 1 then 2 else 1)) (fun i => he _) b a hb ha ?_ ?_⟩
    · simpa only [PairCodeCertificates,ite_eq_right hle] using hcert
    · simpa only [pairCode,ite_eq_right hle,codeBranchValue,codeScale,↓reduceIte] using hc

end TuringRigidity.OrdinalCoding

end OAI
