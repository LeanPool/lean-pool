/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/OrdinalCodeBranch.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalCodeOperations

/-!
# Ordinal Code Branch
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalCoding
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
  OrdinalArithmetic
universe u

theorem code_rename_bound (p : SentenceForm) (r : ℕ → ℕ) (n : ℕ)
    (h : ∀ i, i < p.bound → r i < n) : (p.rename r).bound ≤ n := by
  induction p generalizing r n with
  | equal i j =>
    have hi := h i (by simp [SentenceForm.bound])
    have hj := h j (by simp [SentenceForm.bound])
    simp only [SentenceForm.rename,SentenceForm.bound]; omega
  | member i j =>
    have hi := h i (by simp [SentenceForm.bound])
    have hj := h j (by simp [SentenceForm.bound])
    simp only [SentenceForm.rename,SentenceForm.bound]; omega
  | conj p q ihp ihq =>
    exact max_le (ihp r n (fun i hi => h i (by change i < max p.bound q.bound; omega)))
      (ihq r n (fun i hi => h i (by change i < max p.bound q.bound; omega)))
  | neg p ih => exact ih r n h
  | ex p ih =>
    have ht := ih (fun i => match i with | 0 => 0 | j+1 => r j+1) (n+1) (by
      intro i hi
      cases i with
      | zero => simp
      | succ i => have hh := h i (by change i < p.bound-1; omega); simp; omega)
    exact (Nat.sub_le_sub_right ht 1).trans (by omega)

noncomputable def codeBranchValue (twice : Bool) (a b : Ordinal.{u}) : Ordinal.{u} :=
  codeScale twice (Ordinal.omega0 ^ (a+1)) + Ordinal.omega0 ^ b

noncomputable def codeBranchBody (twice : Bool) : SentenceForm :=
  .conj (fromBounded (.successor 3 5))
    (.conj (codePowerAt 2 3) (.conj (codePowerAt 1 6)
      (.conj (codeScaleAt twice 0 2) (codeSumAt 4 0 1))))

noncomputable def codeBranchSentence (twice : Bool) : SentenceForm :=
  .ex (.ex (.ex (.ex (codeBranchBody twice))))

theorem codeBranchSentence_bound (twice : Bool) : (codeBranchSentence twice).bound = 3 := by
  have hfirst : (fromBounded (.successor 3 5)).bound = 6 := by rfl
  have hleft : (codePowerAt 2 3).bound ≤ 7 :=
    code_rename_bound omegaPowerSentence _ 7 (by intro i _; split <;> omega)
  have hright : (codePowerAt 1 6).bound ≤ 7 :=
    code_rename_bound omegaPowerSentence _ 7 (by intro i _; split <;> omega)
  have hright_lower : 7 ≤ (codePowerAt 1 6).bound := by
    have lower (p q r : SentenceForm) :
        7 ≤ ((SentenceForm.ex (.ex (.ex (.ex (.ex
          (.conj p (.conj (.conj q (.equal 0 6)) r))))))).rename
          (fun i => if i = 0 then 1 else 6)).bound := by
      simp [SentenceForm.rename, SentenceForm.bound]
      omega
    exact lower (canonicalOmega 4) (fromBounded (ordinalOneMatrix 3))
        (.conj (omegaGraphSentence 3 4 0 1 2) (fromBounded (omegaStageMatrix 3 2 1 6 5)))
  have hright_eq := Nat.le_antisymm hright hright_lower
  have hscale : (codeScaleAt twice 0 2).bound ≤ 7 := by
    cases twice with
    | false => decide
    | true => exact code_rename_bound doubleSentence _ 7 (by intro i _; split <;> omega)
  have hsum : (codeSumAt 4 0 1).bound ≤ 7 :=
    code_rename_bound sumSentence _ 7 (by intro i _; split <;> (try split) <;> omega)
  have finish (a b c : ℕ) (ha : a ≤ 7) (hb : b ≤ 7) (hc : c ≤ 7) :
      max 6 (max a (max 7 (max b c))) - 1 - 1 - 1 - 1 = 3 := by omega
  change max (fromBounded (.successor 3 5)).bound
    (max (codePowerAt 2 3).bound (max (codePowerAt 1 6).bound
      (max (codeScaleAt twice 0 2).bound (codeSumAt 4 0 1).bound))) - 1 - 1 - 1 - 1 = 3
  rw [hfirst, hright_eq]
  exact finish _ _ _ hleft hscale hsum

theorem codeBranchBody_sound (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (twice : Bool) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (a b : Ordinal.{u}) (ha : e 5 = a.toZFSet) (hb : e 6 = b.toZFSet) :
    (codeBranchBody twice).Sat (M : Set ZFSet) e → e 4 = (codeBranchValue twice a b).toZFSet := by
  intro h
  obtain ⟨hk,hu,hv,ht,hc⟩ := h
  have hks : e 3 = (a+1).toZFSet := by
    rw [bounded_sat,Formula.absolute _ M hM e he,Formula.eval_successor,ha] at hk
    simpa only [Ordinal.toZFSet_add_one] using hk
  have hus := (codePowerAt_sound M hM hω 2 3 e he hu).2
  rw [hks,Ordinal.rank_toZFSet] at hus
  have hvs := (codePowerAt_sound M hM hω 1 6 e he hv).2
  rw [hb,Ordinal.rank_toZFSet] at hvs
  have hts := codeScaleAt_sound M hM twice 0 2 e he _ hus ht
  exact codeSumAt_sound M hM 4 0 1 e he _ _ hts hvs hc

theorem codeBranchSentence_sound (M : ZFSet.{u}) (hM : Transitive M)
    (hω : ZFSet.omega.{u} ∈ M) (twice : Bool) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (a b : Ordinal.{u}) (ha : e 1 = a.toZFSet) (hb : e 2 = b.toZFSet) :
    (codeBranchSentence twice).Sat (M : Set ZFSet) e → e 0 = (codeBranchValue twice a b).toZFSet
      := by
  rintro ⟨k,hk,u,hu,v,hv,t,ht,h⟩
  exact codeBranchBody_sound M hM hω twice _ (by
    intro i; rcases i with _|_|_|_|i
    · exact ht
    · exact hv
    · exact hu
    · exact hk
    · exact he i) a b ha hb h

theorem codeBranchSentence_sourceT (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (twice : Bool) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ M)
    (a b : Ordinal.{u}) (ha : e 1 = a.toZFSet) (hb : e 2 = b.toZFSet) :
    (codeBranchSentence twice).Sat (M : Set ZFSet) e ↔ e 0 = (codeBranchValue twice a b).toZFSet
      := by
  have hω := omega_mem M hM hT.separation.finitePrefix.bounded hT.infinity
  refine ⟨codeBranchSentence_sound M hM hω twice e he a b ha hb,?_⟩
  intro hc
  let k := (a+1).toZFSet
  let u := (Ordinal.omega0 ^ (a+1)).toZFSet
  let v := (Ordinal.omega0 ^ b).toZFSet
  let t := (codeScale twice (Ordinal.omega0 ^ (a+1))).toZFSet
  have hk : k ∈ M := internal_ordinal_succ M hM hT a (ha ▸ he 1)
  have hu : u ∈ M := ordinal_omega_opow_internal M hM hT (a+1) hk
  have hv : v ∈ M := ordinal_omega_opow_internal M hM hT b (hb ▸ he 2)
  have ht : t ∈ M := codeScale_internal M hM hT twice _ hu
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
  · apply (codePowerAt_sourceT M hM hT 2 3 E hE).mpr
    exact ⟨ZFSet.isOrdinal_toZFSet _,by change u = (Ordinal.omega0 ^ k.rank).toZFSet; simp [u,k]⟩
  · apply (codePowerAt_sourceT M hM hT 1 6 E hE).mpr
    change (e 2).IsOrdinal ∧ v = (Ordinal.omega0 ^ (e 2).rank).toZFSet
    rw [hb,Ordinal.rank_toZFSet]
    exact ⟨ZFSet.isOrdinal_toZFSet _,rfl⟩
  · exact (codeScaleAt_sourceT M hM hT twice 0 2 E hE _ rfl).mpr rfl
  · exact (codeSumAt_sourceT M hM hT 4 0 1 E hE _ _ rfl rfl).mpr hc

end TuringRigidity.OrdinalCoding

end OAI
