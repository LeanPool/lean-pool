/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/BoundedTruthRecursion.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.SourceTheory
public import LeanPool.TuringConeRigidity.Syntax.BoundedFormulaRename

/-!
# Bounded Truth Recursion
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BoundedTruthRecursion
open TransitiveNameModel BoundedSetTheory

/-- The truth formula at `t` depends only on lower-rank members of the proposed truth set. -/
def Local (φ : Formula) (e : ℕ → ZFSet.{0}) : Prop :=
  ∀ D : ZFSet.{0}, Transitive D → ∀ t ∈ D, ∀ Y Z : ZFSet.{0},
    (∀ s ∈ D, ZFSet.rank s < ZFSet.rank t → (s ∈ Y ↔ s ∈ Z)) →
      (φ.Eval (cons t (cons Y e)) ↔ φ.Eval (cons t (cons Z e)))

/-- A truth subset on a transitive part of `K` satisfies the recursive truth equation. -/
def Partial (φ : Formula) (e : ℕ → ZFSet.{0}) (K D Y : ZFSet.{0}) : Prop :=
  Transitive D ∧ D ⊆ K ∧ Y ⊆ D ∧
    ∀ t ∈ D, t ∈ Y ↔ φ.Eval (cons t (cons Y e))

theorem partial_sound (φ : Formula) (e : ℕ → ZFSet.{0}) (K D Y Z : ZFSet.{0})
    (hl : Local φ e) (hp : Partial φ e K D Y)
    (hz : ∀ t ∈ K, t ∈ Z ↔ φ.Eval (cons t (cons Z e))) :
    ∀ t ∈ D, t ∈ Y ↔ t ∈ Z := by
  have wf : WellFounded (fun a b : ZFSet.{0} => ZFSet.rank a < ZFSet.rank b) :=
    InvImage.wf ZFSet.rank Ordinal.lt_wf
  intro t
  induction t using wf.induction with
  | h t ih =>
    intro ht
    exact (hp.2.2.2 t ht).trans ((hl D hp.1 t ht Y Z
      (fun s hs hst => ih s hst hs)).trans (hz t (hp.2.1 ht)).symm)

/-- Variable renaming reserving slots for the partial domain and truth-set witnesses. -/
def dropSlots : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n+2 => n+4

/-- Bounded formula expressing the partial truth-recursion property. -/
def partialFormula (φ : Formula) : Formula :=
  .conj (.transitive 1) (.conj (.subset 1 2) (.conj (.subset 0 1)
    (.allMem 1 (.iff (.member 0 1) (φ.rename dropSlots)))))

theorem partialFormula_spec (φ : Formula) (e : ℕ → ZFSet.{0}) (K D Y : ZFSet.{0}) :
    (partialFormula φ).Eval (cons Y (cons D (cons K e))) ↔ Partial φ e K D Y := by
  simp only [partialFormula,Formula.Eval,Formula.eval_transitive,Formula.eval_subset,
    Formula.eval_allMem,Formula.eval_iff,Formula.eval_rename_comp,cons_zero,cons_succ,Partial]
  have eq (t : ZFSet.{0}) : cons t (cons Y (cons D (cons K e))) ∘ dropSlots = cons t (cons Y e) :=
    by
    funext i; rcases i with _|_|i <;> rfl
  simp only [eq]

/-- The union of domains of partial truth recursions whose domain and truth set belong to `Q`. -/
noncomputable def domain (φ : Formula) (e : ℕ → ZFSet.{0}) (K Q : ZFSet.{0}) : ZFSet.{0} :=
  K.sep (fun t => ∃ D ∈ Q, ∃ Y ∈ Q, Partial φ e K D Y ∧ t ∈ D)

/-- The union of truth sets of partial recursions whose domain and truth set belong to `Q`. -/
noncomputable def truth (φ : Formula) (e : ℕ → ZFSet.{0}) (K Q : ZFSet.{0}) : ZFSet.{0} :=
  K.sep (fun t => ∃ D ∈ Q, ∃ Y ∈ Q, Partial φ e K D Y ∧ t ∈ Y)

/-- Variable placement for the domain and truth witnesses in the union formula. -/
def candidateSlots : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n+2 => n+4

/-- Bounded formula selecting membership in a partial recursion's domain or truth set. -/
def unionFormula (φ : Formula) (which : ℕ) : Formula :=
  .existsMem 1 (.existsMem 2 (.conj ((partialFormula φ).rename candidateSlots) (.member 2 which)))

theorem unionFormula_spec (φ : Formula) (e : ℕ → ZFSet.{0}) (K Q t : ZFSet.{0}) (which : ℕ) :
    (unionFormula φ which).Eval (cons t (cons Q (cons K e))) ↔
      ∃ D ∈ Q, ∃ Y ∈ Q, Partial φ e K D Y ∧
        t ∈ cons Y (cons D (cons t (cons Q (cons K e)))) which := by
  simp only [unionFormula,Formula.Eval,Formula.eval_rename_comp,cons_zero,cons_succ]
  have eq (D Y : ZFSet.{0}) :
      cons Y (cons D (cons t (cons Q (cons K e)))) ∘ candidateSlots = cons Y (cons D (cons K e))
        := by
    funext i; rcases i with _|_|i <;> rfl
  simp only [eq,partialFormula_spec]

theorem domain_truth_mem (M K Q : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hK : K ∈ M) (hQ : Q ∈ M) (φ : Formula) (e : ℕ → ZFSet.{0}) (he : ∀ i, e i ∈ M) :
    domain φ e K Q ∈ M ∧ truth φ e K Q ∈ M := by
  have henv : ∀ i, cons Q (cons K e) i ∈ M := by
    intro i
    rcases i with _ | _ | i
    · exact hQ
    · exact hK
    · exact he i
  constructor
  · have hs := sep_mem M hM hT.separation.finitePrefix.bounded (unionFormula φ 1) _ henv hK
    simpa only [unionFormula_spec,cons_succ,cons_zero,domain] using hs
  · have hs := sep_mem M hM hT.separation.finitePrefix.bounded (unionFormula φ 0) _ henv hK
    simpa only [unionFormula_spec,cons_succ,cons_zero,truth] using hs

theorem domain_transitive (φ : Formula) (e : ℕ → ZFSet.{0}) (K Q : ZFSet.{0}) :
    Transitive (domain φ e K Q) := by
  intro t ht s hst
  obtain ⟨_,D,hD,Y,hY,hp,htD⟩ := ZFSet.mem_sep.mp ht
  have hsD := hp.1 t htD s hst
  exact ZFSet.mem_sep.mpr ⟨hp.2.1 hsD,D,hD,Y,hY,hp,hsD⟩

theorem truth_subset_domain (φ : Formula) (e : ℕ → ZFSet.{0}) (K Q : ZFSet.{0}) :
    truth φ e K Q ⊆ domain φ e K Q := by
  intro t ht
  obtain ⟨htK,D,hD,Y,hY,hp,htY⟩ := ZFSet.mem_sep.mp ht
  exact ZFSet.mem_sep.mpr ⟨htK,D,hD,Y,hY,hp,hp.2.2.1 htY⟩

theorem truth_agrees (φ : Formula) (e : ℕ → ZFSet.{0}) (K Q Z : ZFSet.{0})
    (hl : Local φ e) (hz : ∀ t ∈ K, t ∈ Z ↔ φ.Eval (cons t (cons Z e))) :
    ∀ t ∈ domain φ e K Q, t ∈ truth φ e K Q ↔ t ∈ Z := by
  intro t ht
  constructor
  · intro h
    obtain ⟨_,D,_,Y,_,hp,htY⟩ := ZFSet.mem_sep.mp h
    exact (partial_sound φ e K D Y Z hl hp hz t (hp.2.2.1 htY)).mp htY
  · intro h
    obtain ⟨htK,D,hD,Y,hY,hp,htD⟩ := ZFSet.mem_sep.mp ht
    exact ZFSet.mem_sep.mpr ⟨htK,D,hD,Y,hY,hp,(partial_sound φ e K D Y Z hl hp hz t htD).mpr h⟩

theorem partial_of_agrees (φ : Formula) (e : ℕ → ZFSet.{0}) (K D Y Z : ZFSet.{0})
    (hl : Local φ e) (hz : ∀ t ∈ K, t ∈ Z ↔ φ.Eval (cons t (cons Z e)))
    (hD : Transitive D) (hDK : D ⊆ K) (hYD : Y ⊆ D)
    (ha : ∀ t ∈ D, t ∈ Y ↔ t ∈ Z) : Partial φ e K D Y := by
  refine ⟨hD,hDK,hYD,?_⟩
  intro t ht
  exact (ha t ht).trans ((hz t (hDK ht)).trans
    (hl D hD t ht Y Z (fun s hs _ => ha s hs)).symm)

theorem truth_internal (M K Z : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hKM : K ∈ M) (hK : Transitive K) (φ : Formula) (e : ℕ → ZFSet.{0})
    (he : ∀ i, e i ∈ M) (hl : Local φ e)
    (hz : ∀ t ∈ K, t ∈ Z ↔ φ.Eval (cons t (cons Z e))) :
    K.sep (fun t => t ∈ Z) ∈ M := by
  classical
  obtain ⟨Q,hQM,hQ⟩ := internal_power M hM hT.powerSet hKM
  let D := domain φ e K Q
  let Y := truth φ e K Q
  obtain ⟨hDM,hYM⟩ := domain_truth_mem M K Q hM hT hKM hQM φ e he
  have hD : Transitive D := domain_transitive φ e K Q
  have hDK : D ⊆ K := fun _ h => (ZFSet.mem_sep.mp h).1
  have hYD : Y ⊆ D := truth_subset_domain φ e K Q
  have ha : ∀ t ∈ D, t ∈ Y ↔ t ∈ Z := truth_agrees φ e K Q Z hl hz
  have hcover (t : ZFSet.{0}) : t ∈ K → t ∈ D := by
    induction t using ZFSet.inductionOn with
    | h t ih =>
      intro htK
      by_cases htD : t ∈ D
      · exact htD
      have hchildren : t ⊆ D := fun s hs => ih s hs (hK t htK s hs)
      let D' := D ∪ ({t} : ZFSet.{0})
      let Y' := if t ∈ Z then Y ∪ ({t} : ZFSet.{0}) else Y
      have hDD' : D ⊆ D' := fun _ h => ZFSet.mem_union.mpr (Or.inl h)
      have htD' : t ∈ D' := ZFSet.mem_union.mpr (Or.inr (ZFSet.mem_singleton.mpr rfl))
      have hD' : Transitive D' := by
        intro a ha b hb
        rcases ZFSet.mem_union.mp ha with ha | ha
        · exact hDD' (hD a ha b hb)
        · have ha := ZFSet.mem_singleton.mp ha
          subst a
          exact hDD' (hchildren hb)
      have hD'K : D' ⊆ K := by
        intro a ha
        rcases ZFSet.mem_union.mp ha with ha | ha
        · exact hDK ha
        · exact (ZFSet.mem_singleton.mp ha) ▸ htK
      have hY'D' : Y' ⊆ D' := by
        intro a ha
        dsimp [Y'] at ha
        split_ifs at ha
        · rcases ZFSet.mem_union.mp ha with ha | ha
          · exact hDD' (hYD ha)
          · exact (ZFSet.mem_singleton.mp ha) ▸ htD'
        · exact hDD' (hYD ha)
      have ha' : ∀ a ∈ D', a ∈ Y' ↔ a ∈ Z := by
        intro a haD'
        by_cases hat : a = t
        · subst a
          have htY : t ∉ Y := fun h => htD (hYD h)
          simp only [Y']
          split_ifs with htZ <;> simp [htZ,htY]
        · have haD : a ∈ D := (ZFSet.mem_union.mp haD').resolve_right (fun h => hat
          (ZFSet.mem_singleton.mp h))
          have hae := ha a haD
          dsimp [Y']
          split_ifs <;> simpa only [ZFSet.mem_union,ZFSet.mem_singleton,hat,or_false] using hae
      have htM := hM K hKM t htK
      have hsM := singleton_mem M hM hT.pairing htM
      have hD'M : D' ∈ M := binary_union_mem M hM hT.pairing hT.union hDM hsM
      have hY'M : Y' ∈ M := by
        dsimp [Y']; split_ifs
        · exact binary_union_mem M hM hT.pairing hT.union hYM hsM
        · exact hYM
      exact ZFSet.mem_sep.mpr ⟨htK,D',(hQ _).mpr ⟨hD'M,hD'K⟩,
        Y',(hQ _).mpr ⟨hY'M,fun _ h => hD'K (hY'D' h)⟩,
        partial_of_agrees φ e K D' Y' Z hl hz hD' hD'K hY'D' ha',htD'⟩
  have eq : Y = K.sep (fun t => t ∈ Z) := by
    apply ZFSet.ext; intro t
    constructor
    · intro ht
      exact ZFSet.mem_sep.mpr ⟨hDK (hYD ht),(ha t (hYD ht)).mp ht⟩
    · intro ht
      obtain ⟨htK,htZ⟩ := ZFSet.mem_sep.mp ht
      exact (ha t (hcover t htK)).mpr htZ
  exact eq ▸ hYM

end TuringRigidity.BoundedTruthRecursion

end OAI
