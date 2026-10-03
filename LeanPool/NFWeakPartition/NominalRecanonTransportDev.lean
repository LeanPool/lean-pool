/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAtomicRecanonDev

/-! NF weak partition development: NominalRecanonTransportDev. -/


public section

namespace NFChoice.DirectNominalPrf.Nominal.RecanonTransportDev

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.DirectCertificate.ClassBoundaryNormalizationDev005
open NFChoice.DirectCertificate.ClassBoundaryCoreDev006
open NFChoice.DirectCertificate.ClassBoundaryBiimpDev009
open NFChoice.DirectCertificate.ClassBoundaryRawHandlersDev010
open NFChoice.DirectNominalPrf.Nominal.AtomicRecanonDev

abbrev Theory : Fol.SentTheory LNF :=
  LiteralHailperinNF

/-! The existing semantic certificate relation lives in `Prop`.  Flypitch proof
objects live in `Type`, so Lean correctly forbids eliminating that relation
to construct a proof object.  This byte-for-byte structural counterpart lives
in `Type`; the source emitter produces it directly.
-/

mutual
  inductive TRecanonClass : Class → Class → Type where
    | same (A : Class) : TRecanonClass A A
    |
    cab {x : Var} {p q : Wff} (h : TRecanonWff p q) : TRecanonClass (.cab x p) (.cab x q)
  inductive TRecanonWff : Wff → Wff → Type where
    | same (p : Wff) : TRecanonWff p p
    |
    imp {p p' q q' : Wff} (hp : TRecanonWff p p') (hq : TRecanonWff q q') :
      TRecanonWff (.imp p q) (.imp p' q')
    | all {x : Var} {p q : Wff} (h : TRecanonWff p q) : TRecanonWff (.all x p) (.all x q)
    | objEq_classEq (x y : Var) : TRecanonWff (.objEq x y) (.classEq (.cv x) (.cv y))
    | classEq_objEq (x y : Var) : TRecanonWff (.classEq (.cv x) (.cv y)) (.objEq x y)
    | objMem_classMem (x y : Var) : TRecanonWff (.objMem x y) (.classMem (.cv x) (.cv y))
    | classMem_objMem (x y : Var) : TRecanonWff (.classMem (.cv x) (.cv y)) (.objMem x y)
    |
    classEq {A A' B B' : Class} (hA : TRecanonClass A A') (hB : TRecanonClass B B') :
      TRecanonWff (.classEq A B) (.classEq A' B')
    |
    classMem {A A' B B' : Class} (hA : TRecanonClass A A') (hB : TRecanonClass B B') :
      TRecanonWff (.classMem A B) (.classMem A' B')
end

@[expose]
noncomputable def liftedTheoryBiimp {p q : Fol.formula LNF} (h : Theory.fst ⊢ p ⇔ q) :
    Fol.lift_formula1 '' Theory.fst ⊢ p ⇔ q :=
  by
  rw [Fol.SentTheory.lift_irrel Theory]
  exact h

@[expose]
noncomputable def impCongr {L : Fol.Language} {Γ : Set (Fol.formula L)}
    {p p' q q' : Fol.formula L} (hp : Γ ⊢ p ⇔ p') (hq : Γ ⊢ q ⇔ q') :
    Γ ⊢ (p ⟹ q) ⇔ (p' ⟹ q') := by
  apply Fol.biimpI
  · apply Fol.prf.impI
    let Δ := insert p' (insert (p ⟹ q) Γ)
    have hpΔ : Δ ⊢ p ⇔ p' :=
      Fol.weakening
        (by
          intro f hf
          exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hf))
        hp
    have hqΔ : Δ ⊢ q ⇔ q' :=
      Fol.weakening
        (by
          intro f hf
          exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hf))
        hq
    have hImp : Δ ⊢ p ⟹ q := Fol.axm2
    have hp' : Δ ⊢ p' := Fol.axm1
    exact biimpForward hqΔ (Fol.prf.impE p hImp (biimpBackward hpΔ hp'))
  · apply Fol.prf.impI
    let Δ := insert p (insert (p' ⟹ q') Γ)
    have hpΔ : Δ ⊢ p ⇔ p' :=
      Fol.weakening
        (by
          intro f hf
          exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hf))
        hp
    have hqΔ : Δ ⊢ q ⇔ q' :=
      Fol.weakening
        (by
          intro f hf
          exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hf))
        hq
    have hImp : Δ ⊢ p' ⟹ q' := Fol.axm2
    have hp0 : Δ ⊢ p := Fol.axm1
    exact biimpBackward hqΔ (Fol.prf.impE p' hImp (biimpForward hpΔ hp0))

@[expose]
noncomputable def andCongr {L : Fol.Language} {Γ : Set (Fol.formula L)}
    {p p' q q' : Fol.formula L} (hp : Γ ⊢ p ⇔ p') (hq : Γ ⊢ q ⇔ q') :
    Γ ⊢ (p ⊓' q) ⇔ (p' ⊓' q') := by
  apply Fol.biimpI
  · let Δ := insert (p ⊓' q) Γ
    have hpΔ : Δ ⊢ p ⇔ p' := Fol.weakening (Set.subset_insert _ _) hp
    have hqΔ : Δ ⊢ q ⇔ q' := Fol.weakening (Set.subset_insert _ _) hq
    have hSource : Δ ⊢ p ⊓' q := Fol.axm1
    exact
      Fol.andI (biimpForward hpΔ (Fol.andE1 q hSource))
        (biimpForward hqΔ (Fol.andE2 p hSource))
  · let Δ := insert (p' ⊓' q') Γ
    have hpΔ : Δ ⊢ p ⇔ p' := Fol.weakening (Set.subset_insert _ _) hp
    have hqΔ : Δ ⊢ q ⇔ q' := Fol.weakening (Set.subset_insert _ _) hq
    have hSource : Δ ⊢ p' ⊓' q' := Fol.axm1
    exact
      Fol.andI (biimpBackward hpΔ (Fol.andE1 q' hSource))
        (biimpBackward hqΔ (Fol.andE2 p' hSource))

mutual
  @[expose]
  noncomputable def classBridge :
      {A B : Class} →
        TRecanonClass A B →
          ∀ (rho : Var → Nat) (candidate : Nat),
            Theory.fst ⊢ lowerClassPred rho candidate A ⇔ lowerClassPred rho candidate B
    | _, _, .same A => fun rho candidate =>
      Fol.biimp_refl Theory.fst (lowerClassPred rho candidate A)
    | _, _, .cab h => fun rho candidate => wffBridge h (updateRho rho _ candidate)
  @[expose]
  noncomputable def wffBridge :
      {p q : Wff} →
        TRecanonWff p q → ∀ rho : Var → Nat, Theory.fst ⊢ lowerWff rho p ⇔ lowerWff rho q
    | _, _, .same p => fun rho => Fol.biimp_refl Theory.fst (lowerWff rho p)
    | _, _, .imp hp hq => fun rho => impCongr (wffBridge hp rho) (wffBridge hq rho)
    | _, _, .all h => fun rho => by
      exact allCongr (liftedTheoryBiimp (wffBridge h (bindRho rho _)))
    | _, _, .objEq_classEq x y => fun rho => by
      simpa [biimp, conj, neg, Fol.biimp, Fol.ex', Fol.and', Fol.not', lowerWff,
        lowerClassPred, liftRho, classEq, cvPred, GenericLogicalHandlers.nfMem, mem,
        Fol.lift_term1, Fol.lift_term_at] using (objEqClassEqBiimp (&(rho x)) (&(rho y)))
    | _, _, .classEq_objEq x y => fun rho => by
      simpa [biimp, conj, neg, Fol.biimp, Fol.ex', Fol.and', Fol.not', lowerWff,
        lowerClassPred, liftRho, classEq, cvPred, GenericLogicalHandlers.nfMem, mem,
        Fol.lift_term1, Fol.lift_term_at] using
        (biimpSymm (objEqClassEqBiimp (&(rho x)) (&(rho y))))
    | _, _, .objMem_classMem x y => fun rho => by
      simpa [biimp, conj, neg, Fol.biimp, Fol.ex', Fol.and', Fol.not', lowerWff,
        lowerClassPred, liftRho, classMem, cvPred, applyPred, represents,
        GenericLogicalHandlers.nfMem, mem, ex, conj, neg, biimp, Fol.and', Fol.not',
        Fol.lift_term1, Fol.lift_term_at] using
        (objMemClassMemBiimp (&(rho x)) (&(rho y)))
    | _, _, .classMem_objMem x y => fun rho => by
      simpa [biimp, conj, neg, Fol.biimp, Fol.ex', Fol.and', Fol.not', lowerWff,
        lowerClassPred, liftRho, classMem, cvPred, applyPred, represents,
        GenericLogicalHandlers.nfMem, mem, ex, conj, neg, biimp, Fol.and', Fol.not',
        Fol.lift_term1, Fol.lift_term_at] using
        (biimpSymm (objMemClassMemBiimp (&(rho x)) (&(rho y))))
    | _, _, .classEq hA hB => fun rho =>
      by
      have hBody :=
        biimpCongr (classBridge hA (liftRho rho) 0) (classBridge hB (liftRho rho) 0)
      simpa [biimp, conj, neg, Fol.biimp, Fol.ex', Fol.and', Fol.not', lowerWff,
        biimp] using (allCongr (liftedTheoryBiimp hBody))
    | _, _, .classMem hA hB => fun rho =>
      by
      have hFixed :
        Theory.fst ⊢
          GenericLogicalHandlers.nfMem (&0) (&1) ⇔
            GenericLogicalHandlers.nfMem (&0) (&1) :=
        Fol.biimp_refl _ _
      have hRepBody := biimpCongr hFixed (classBridge hA (liftRho (liftRho rho)) 0)
      have hRep := allCongr (liftedTheoryBiimp hRepBody)
      have hBody := andCongr hRep (classBridge hB (liftRho rho) 0)
      simpa [biimp, conj, neg, Fol.biimp, Fol.ex', Fol.and', Fol.not', lowerWff, ex, conj,
        neg, biimp, Fol.and', Fol.not'] using (exCongr (liftedTheoryBiimp hBody))
end

@[expose]
noncomputable def transport {p q : Wff} (h : TRecanonWff p q) (hp : NPrf p) : NPrf q :=
  fun rho => biimpForward (wffBridge h rho) (hp rho)


end NFChoice.DirectNominalPrf.Nominal.RecanonTransportDev
