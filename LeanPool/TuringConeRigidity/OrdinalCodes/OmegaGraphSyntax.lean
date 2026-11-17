/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OmegaGraphSyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OmegaStageSyntax
public import LeanPool.TuringConeRigidity.OrdinalCodes.OmegaPowerStage
public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalProductClosure

/-!
# Omega Graph Syntax
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
universe u

/-- A full formula describing a graph of the omega-power recursion on ordinals. -/
noncomputable def omegaGraphSentence (s w d r f : ℕ) : SentenceForm :=
  .conj (fromBounded (ordinalFormula d))
    (.conj (fromBounded (.functionGraph f d r))
      (ordinalAllMem d (ordinalAllMem (r+1)
        (.imp (fromBounded (.pairMem 1 0 (f+2)))
          (.ex (.conj (fromBounded (omegaStageMatrix (s+3) (f+3) (r+3) 2 0))
            (.conj (fromBounded (ordinalFormula 0)) (ordinalProductAt 1 0 (w+3)))))))))

theorem omegaGraphSentence_semantics (M : ZFSet.{u}) (hM : Transitive M)
    (s w d r f : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M) :
    (omegaGraphSentence s w d r f).Sat (M : Set ZFSet) e ↔
      (e d).IsOrdinal ∧ FunctionGraph (e d) (e r) (e f) ∧
      ∀ x ∈ e d, ∀ v ∈ e r, ZFSet.pair x v ∈ e f →
        ∃ A ∈ M, StageStep (e s) (e f) (e r) x A ∧ A.IsOrdinal ∧
          (ordinalProductAt 1 0 (w+3)).Sat (M : Set ZFSet) (cons A (cons v (cons x e))) := by
  have hb (p : Formula) : (fromBounded p).Sat (M : Set ZFSet) e ↔ p.Eval e := by
    rw [bounded_sat,Formula.absolute _ M hM e he]
  change ((fromBounded _).Sat _ e ∧ (fromBounded _).Sat _ e ∧
    (ordinalAllMem d _).Sat _ e) ↔ _
  rw [hb,hb,eval_ordinalFormula,Formula.eval_functionGraph,
    ordinalAllMem_sat M hM d _ e (he d)]
  apply and_congr_right; intro _
  apply and_congr_right; intro _
  apply forall_congr'; intro x
  apply forall_congr'; intro hx
  have hxM := hM _ (he d) x hx
  rw [ordinalAllMem_sat M hM (r+1) _ (cons x e) (he r)]
  apply forall_congr'; intro v
  apply forall_congr'; intro hv
  have hvM := hM _ (he r) v hv
  rw [SentenceForm.sat_imp,bounded_sat,Formula.absolute _ M hM _ (by
    intro i
    rcases i with _ | _ | i
    · exact hvM
    · exact hxM
    · exact he i),Formula.eval_pairMem]
  apply forall_congr'; intro _
  change (∃ A ∈ M, (fromBounded _).Sat _ _ ∧ (fromBounded _).Sat _ _ ∧ _) ↔ _
  apply exists_congr; intro A
  apply and_congr_right; intro hA
  have heA : ∀ i, cons A (cons v (cons x e)) i ∈ M := by
    intro i
    rcases i with _ | _ | _ | i
    · exact hA
    · exact hvM
    · exact hxM
    · exact he i
  rw [bounded_sat,Formula.absolute _ M hM _ heA,omegaStageMatrix_eval,
    bounded_sat,Formula.absolute _ M hM _ heA,eval_ordinalFormula]
  rfl

theorem omegaGraphSentence_sound (M : ZFSet.{u}) (hM : Transitive M)
    (s w d r f : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (hs : e s = (1 : Ordinal.{u}).toZFSet) (hw : e w = ZFSet.omega) :
    (omegaGraphSentence s w d r f).Sat (M : Set ZFSet) e →
      OmegaGraph M (e d) (e r) (e f) := by
  rw [omegaGraphSentence_semantics M hM s w d r f e he]
  rintro ⟨hd,hf,hstep⟩
  refine ⟨hd,hf,?_⟩
  intro x hx v hv hfv
  obtain ⟨A,hA,hst,ho,hp⟩ := hstep x hx v hv hfv
  have hwOrd : ZFSet.omega.{u}.IsOrdinal := toZFSet_omega ▸ ZFSet.isOrdinal_toZFSet Ordinal.omega0
  have hm := ordinalProductAt_sound M hM 1 0 (w+3) _ (by
    intro i
    rcases i with _ | _ | _ | i
    · exact hA
    · exact hM _ (he r) v hv;
    · exact hM _ (he d) x hx
    · exact he i) ho (by simpa [hw] using hwOrd) hp
  simp only [cons_zero,cons_succ,hw,← toZFSet_omega,Ordinal.rank_toZFSet] at hm
  exact ⟨A,hA,hs ▸ hst,ho,hm⟩

theorem omegaGraphSentence_sourceT (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (s w d r f : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (hs : e s = (1 : Ordinal.{u}).toZFSet) (hw : e w = ZFSet.omega) :
    (omegaGraphSentence s w d r f).Sat (M : Set ZFSet) e ↔
      OmegaGraph M (e d) (e r) (e f) := by
  refine ⟨omegaGraphSentence_sound M hM s w d r f e he hs hw,?_⟩
  intro hg
  apply (omegaGraphSentence_semantics M hM s w d r f e he).mpr
  refine ⟨hg.1,hg.2.1,?_⟩
  intro x hx v hv hfv
  obtain ⟨A,hA,hst,ho,hp⟩ := hg.2.2 x hx v hv hfv
  refine ⟨A,hA,hs.symm ▸ hst,ho,?_⟩
  have hwOrd : ZFSet.omega.{u}.IsOrdinal := toZFSet_omega ▸ ZFSet.isOrdinal_toZFSet Ordinal.omega0
  apply (ordinalProductAt_sourceT M hM hT 1 0 (w+3) _ (by
    intro i
    rcases i with _ | _ | _ | i
    · exact hA
    · exact hM _ (he r) v hv;
    · exact hM _ (he d) x hx
    · exact he i) ho (by simpa [hw] using hwOrd)).mpr
  simpa only [cons_zero,cons_succ,hw,← toZFSet_omega,Ordinal.rank_toZFSet] using hp

end TuringRigidity.OrdinalArithmetic

end OAI
