/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OrdinalVectorSyntax.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalPairSyntax
public import LeanPool.TuringConeRigidity.SetModels.InternalOrdinalCodes

/-!
# Ordinal Vector Syntax
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
  OrdinalArithmetic
universe u

/-- Variable renaming reserving the slots introduced while recursively coding the vector tail. -/
def vectorTailSlots : ℕ → ℕ
  | 0 => 0
  | i+1 => i+3

/-- A full formula defining a finite ordinal-vector code by recursively pairing its entries. -/
noncomputable def vectorCodeSentence : ℕ → SentenceForm
  | 0 => fromBounded (ordinalOneMatrix 0)
  | n+1 => .ex (.conj
      (pairCodeSentence.rename (fun i => if i = 0 then 1 else if i = 1 then 2 else 0))
      ((vectorCodeSentence n).rename vectorTailSlots))

theorem vectorCodeSentence_bound (n : ℕ) : (vectorCodeSentence n).bound ≤ n+1 := by
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    have hp := code_rename_bound pairCodeSentence
      (fun i => if i = 0 then 1 else if i = 1 then 2 else 0) 3 (by
        intro i _; split <;> (try split) <;> omega)
    have ht := code_rename_bound (vectorCodeSentence n) vectorTailSlots (n+3) (by
      intro i hi
      cases i with
      | zero => simp [vectorTailSlots]
      | succ i => change i+3 < n+3; omega)
    change max _ _ - 1 ≤ n+1+1
    omega

theorem vectorCodeSentence_sound (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (n : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (v : Fin n → Ordinal.{u}) (hv : ∀ i, e (i.val + 1) = (v i).toZFSet) :
    (vectorCodeSentence n).Sat (M : Set ZFSet) e → e 0 = (vectorCode v).toZFSet := by
  induction n generalizing e with
  | zero =>
    rw [vectorCodeSentence,bounded_sat,Formula.absolute _ M hM e he,ordinalOneMatrix_eval]
    exact id
  | succ n ih =>
    rintro ⟨t,ht,hp,hrest⟩
    rw [SentenceForm.sat_rename] at hp hrest
    have htail := ih _ (fun i => by
      cases i
      · exact ht
      · exact he _) (fun i => v i.succ) (fun i => hv i.succ) hrest
    have hpair := pairCodeSentence_sound M hM hω _ (fun i => by
      split
      · exact he 0
      split
      · exact he 1
      exact ht) hp
    have hh : e 1 = (v 0).toZFSet := hv 0
    change t = (vectorCode (fun i => v i.succ)).toZFSet at htail
    have hpval : e 0 = (pairCode (e 1).rank t.rank).toZFSet := hpair.2.2
    simpa only [hh,htail,Ordinal.rank_toZFSet,vectorCode] using hpval

theorem vectorCodeSentence_sourceT (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (n : ℕ) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (v : Fin n → Ordinal.{u}) (hv : ∀ i, e (i.val + 1) = (v i).toZFSet) :
    (vectorCodeSentence n).Sat (M : Set ZFSet) e ↔ e 0 = (vectorCode v).toZFSet := by
  have hω := omega_mem M hM hT.separation.finitePrefix.bounded hT.infinity
  refine ⟨vectorCodeSentence_sound M hM hω n e he v hv,?_⟩
  induction n generalizing e with
  | zero =>
    intro hc
    rw [vectorCodeSentence,bounded_sat,Formula.absolute _ M hM e he,ordinalOneMatrix_eval]
    exact hc
  | succ n ih =>
    intro hc
    let t := (vectorCode (fun i => v i.succ)).toZFSet
    have ht : t ∈ M := vectorCode_internal M hM hT _ (fun i => hv i.succ ▸ he _)
    refine ⟨t,ht,?_,?_⟩
    · rw [SentenceForm.sat_rename]
      apply (pairCodeSentence_sourceT M hM hT _ (fun i => by
        split
        · exact he 0
        split
        · exact he 1
        exact ht)).mpr
      change (e 1).IsOrdinal ∧ t.IsOrdinal ∧ e 0 = (pairCode (e 1).rank t.rank).toZFSet
      have hh : e 1 = (v 0).toZFSet := hv 0
      rw [hh]
      exact ⟨ZFSet.isOrdinal_toZFSet _,ZFSet.isOrdinal_toZFSet _,by simpa [t,vectorCode] using hc⟩
    · rw [SentenceForm.sat_rename]
      exact ih _ (fun i => by
        cases i
        · exact ht
        · exact he _) _ (fun i => hv i.succ) rfl

end TuringRigidity.OrdinalCoding

end OAI
