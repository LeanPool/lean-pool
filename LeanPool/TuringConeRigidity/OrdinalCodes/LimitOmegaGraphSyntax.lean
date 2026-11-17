/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/LimitOmegaGraphSyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.CodeOperationCertificates
public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalCodeBranch

/-!
# Limit Omega Graph Syntax
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
open OrdinalCoding
universe u

/-- A full formula coding the successor-ordinal input and its next omega-power pair. -/
noncomputable def omegaNextPairSentence : SentenceForm :=
  .ex (.ex (.ex (.conj
    (fromBounded (.conj (ordinalFormula 2) (.conj (.successor 0 2) (.orderedPair 3 2 1))))
    (codePowerAt 1 0))))

theorem omegaNextPairSentence_bound : omegaNextPairSentence.bound = 1 := by
  have hbounded :
      (fromBounded (.conj (ordinalFormula 2) (.conj (.successor 0 2) (.orderedPair 3 2 1)))).bound
        = 4 := by
    rfl
  have hpower : (codePowerAt 1 0).bound ≤ 4 :=
    code_rename_bound omegaPowerSentence _ 4 (by intro i _; split <;> omega)
  have finish (p q : SentenceForm) (hp : p.bound = 4) (hq : q.bound ≤ 4) :
      (SentenceForm.ex (.ex (.ex (.conj p q)))).bound = 1 := by
    change max p.bound q.bound - 1 - 1 - 1 = 1
    rw [hp, max_eq_left hq]
  exact finish _ _ hbounded hpower


theorem omegaNextPairSentence_semantics (M : ZFSet.{u}) (hM : Transitive M)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    omegaNextPairSentence.Sat (M : Set ZFSet) e ↔
      ∃ x ∈ M, ∃ y ∈ M, ∃ k ∈ M,
        (x.IsOrdinal ∧ k = insert x x ∧ e 0 = ZFSet.pair x y) ∧
        (codePowerAt 1 0).Sat (M : Set ZFSet) (cons k (cons y (cons x e))) := by
  change (∃ x ∈ M, ∃ y ∈ M, ∃ k ∈ M, _) ↔ _
  apply exists_congr; intro x
  apply and_congr_right; intro hx
  apply exists_congr; intro y
  apply and_congr_right; intro hy
  apply exists_congr; intro k
  apply and_congr_right; intro hk
  have hE : ∀ i, cons k (cons y (cons x e)) i ∈ M := by
    intro i; rcases i with _|_|_|i
    · exact hk
    · exact hy
    · exact hx
    · exact he i
  rw [SentenceForm.Sat,bounded_sat,Formula.absolute _ M hM _ hE]
  simp only [Formula.Eval,eval_ordinalFormula,Formula.eval_successor,
    Formula.eval_orderedPair,cons_zero,cons_succ]

theorem omegaNextPairSentence_at_cut (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (a : Ordinal.{u}) (ha : Order.IsSuccLimit a)
    (hcut : ∀ c : Ordinal.{u}, c.toZFSet ∈ M ↔ c < a)
    (hpow : ∀ c < a, (Ordinal.omega0 ^ c).toZFSet ∈ M ∧ OmegaPowerCertificates M c.toZFSet)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    omegaNextPairSentence.Sat (M : Set ZFSet) e ↔
      ∃ c < a, e 0 = ZFSet.pair c.toZFSet (omegaNext c.toZFSet) := by
  rw [omegaNextPairSentence_semantics M hM e he]
  constructor
  · rintro ⟨x,hx,y,hy,k,hk,⟨ho,hkdef,hz⟩,hp⟩
    have hE : ∀ i, cons k (cons y (cons x e)) i ∈ M := by
      intro i; rcases i with _|_|_|i
      · exact hk
      · exact hy
      · exact hx
      · exact he i
    have hv := (codePowerAt_sound M hM hω 1 0 _ hE hp).2
    change y = (Ordinal.omega0 ^ k.rank).toZFSet at hv
    have hsucc : k = (x.rank+1).toZFSet := by
      rw [Ordinal.toZFSet_add_one,ho.toZFSet_rank_eq,hkdef]
    rw [hsucc,Ordinal.rank_toZFSet] at hv
    refine ⟨x.rank,(hcut _).mp (ho.toZFSet_rank_eq.symm ▸ hx),?_⟩
    simpa only [ho.toZFSet_rank_eq,omegaNext] using hz.trans (congrArg (ZFSet.pair x) hv)
  · rintro ⟨c,hc,hz⟩
    have hs : c+1 < a := ha.succ_lt hc
    have hx := (hcut c).mpr hc
    have hk := (hcut (c+1)).mpr hs
    obtain ⟨hy,hcert⟩ := hpow (c+1) hs
    refine ⟨c.toZFSet,hx,(Ordinal.omega0 ^ (c+1)).toZFSet,hy,(c+1).toZFSet,hk,
      ⟨ZFSet.isOrdinal_toZFSet _,Ordinal.toZFSet_add_one c,?_⟩,?_⟩
    · simpa only [omegaNext,Ordinal.rank_toZFSet] using hz
    · apply codePowerAt_of_certificates M hM hω 1 0 _ (fun i => by
        rcases i with _|_|_|i
        · exact hk
        · exact hy
        · exact hx
        · exact he i) hcert
      simp only [cons_zero,cons_succ,Ordinal.rank_toZFSet]

end TuringRigidity.OrdinalArithmetic

end OAI
