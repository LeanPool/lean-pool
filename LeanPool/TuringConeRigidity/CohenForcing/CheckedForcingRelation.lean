/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CheckedForcingRelation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.CheckedMembershipSeparation

/-!
# Checked Forcing Relation
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CheckedForcingRelation
open TransitiveNameModel BoundedSetTheory CountableForcing RecursiveNames AtomicForcing
variable {c : ZFSet.{0}} [Preorder (Conditions c)] [Top (Conditions c)]

/-- Set-coded graph pairing a ground-model element with conditions forcing its membership in
`τ`. -/
noncomputable def relation (a : ZFSet.{0}) (τ : Name (Conditions c)) : ZFSet.{0} :=
  (ZFSet.prod a c).sep (fun z => ∃ x ∈ a, ∃ p : Conditions c,
    z = ZFSet.pair x (label c p) ∧ MemForces (Name.check x) τ p)

theorem pair_relation (a x : ZFSet.{0}) (τ : Name (Conditions c)) (p : Conditions c) :
    ZFSet.pair x (label c p) ∈ relation a τ ↔ x ∈ a ∧ MemForces (Name.check x) τ p := by
  rw [relation,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,y,hy,q,he,hf⟩
    have hpq := label_injective c (ZFSet.pair_inj.mp he).2
    have hxy := (ZFSet.pair_inj.mp he).1
    subst y; subst q; exact ⟨hy,hf⟩
  · rintro ⟨hx,hf⟩
    exact ⟨ZFSet.mem_prod.mpr ⟨x,hx,_,label_mem c p,rfl⟩,x,hx,p,rfl,hf⟩

theorem relation_mem (M a : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (ha : a ∈ M) {o : ZFSet.{0}} (hoM : o ∈ M)
    (ho : ∀ p q : Conditions c, ZFSet.pair (label c p) (label c q) ∈ o ↔ p ≤ q)
    (τ : Name (Conditions c)) (hτ : τ.encode (label c) ∈ M) : relation a τ ∈ M := by
  let e := cons a (cons c (cons o (cons (τ.encode (label c)) (fun _ => label c ⊤))))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|_|_|i
    · exact ha
    · exact hc
    · exact hoM
    · exact hτ
    · exact hM c hc _ (label_mem c ⊤)
  let ren : ℕ → ℕ := fun | 0 => 1 | 1 => 4 | 2 => 5 | 3 => 0 | 4 => 6 | _ => 7
  let φ : SigmaFormula := .existsMem 1 (.existsMem 3 (.andBounded (.orderedPair 2 1 0)
    (FullSetForcing.checkedMembershipSigma.rename ren)))
  have hpM := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    ha hc
  obtain ⟨R,hRM,hR⟩ := hT.separation.finitePrefix φ e he (ZFSet.prod a c) hpM
  have spec (x y z : ZFSet.{0}) (hx : x ∈ M) (hy : y ∈ M)
      (p : Conditions c) (hpy : label c p = y) :
      (FullSetForcing.checkedMembershipSigma.rename ren).Realize M (cons y (cons x (cons z e))) ↔
        MemForces (Name.check x) τ p := by
    rw [SigmaFormula.realize_rename,FullSetForcing.checkedMembershipSigma_spec]
    have hv : ∀ i, (cons y (cons x (cons z e)) ∘ ren) i ∈ M := by
      intro i; rcases i with _|_|_|_|_|i
      · exact hx
      · exact hc
      · exact hoM
      · exact hy
      · exact hτ
      · exact he 4
    exact FullSetForcing.checkedMembership_spec M hM hT ho τ p x _ hv
      rfl rfl rfl hpy.symm rfl rfl
  have pairSpec (x y z : ZFSet.{0}) (hx : x ∈ M) (hy : y ∈ M) (hz : z ∈ M) :
      (BoundedSetTheory.Formula.orderedPair 2 1 0).Realize M (cons y (cons x (cons z e))) ↔
        z = ZFSet.pair x y := by
    have hv : ∀ i, cons y (cons x (cons z e)) i ∈ M := by
      intro i
      rcases i with _ | _ | _ | i
      · exact hy
      · exact hx
      · exact hz
      · exact he i
    exact (BoundedSetTheory.Formula.absolute _ M hM _ hv).trans
      (by simp only [BoundedSetTheory.Formula.eval_orderedPair,cons_zero,cons_succ])
  have heq : R = relation a τ := by
    apply ZFSet.ext; intro z
    constructor
    · intro hzR
      have hz := hM R hRM z hzR
      obtain ⟨hzprod,hf⟩ := (hR z hz).mp hzR
      simp only [φ,SigmaFormula.realize_existsMem,SigmaFormula.realize_andBounded,
        cons_zero,cons_succ,e] at hf
      obtain ⟨x,hx,hxa,y,hy,hyc,hzxy,hf⟩ := hf
      obtain ⟨p,hpy⟩ := label_surjective c hyc
      exact ZFSet.mem_sep.mpr ⟨hzprod,x,hxa,p,((pairSpec x y z hx hy hz).mp hzxy).trans (congrArg
        (ZFSet.pair x) hpy.symm),
        (spec x y z hx hy p hpy).mp hf⟩
    · intro hzR
      obtain ⟨hzprod,x,hxa,p,hzxy,hf⟩ := ZFSet.mem_sep.mp hzR
      have hz := hM _ hpM z hzprod
      have hx := hM a ha x hxa
      have hy := hM c hc _ (label_mem c p)
      apply (hR z hz).mpr
      refine ⟨hzprod,?_⟩
      simp only [φ,SigmaFormula.realize_existsMem,SigmaFormula.realize_andBounded,
        cons_zero,cons_succ,e]
      exact ⟨x,hx,hxa,label c p,hy,label_mem c p,(pairSpec x (label c p) z hx hy hz).mpr hzxy,
        (spec x (label c p) z hx hy p rfl).mpr hf⟩
  exact heq ▸ hRM

end TuringRigidity.CheckedForcingRelation

end OAI
