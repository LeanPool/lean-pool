/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.Substitution

/-!
# Geometric sequent calculus and its soundness

`GeometricTheory.Provable T σ` is the provability of a geometric sequent from the axioms of `T`
in geometric sequent calculus (Johnstone, *Elephant*, D1.3.1; Caramello, *Theories, Sites,
Toposes*, 1.1.4): identity, cut, substitution of terms, the rules for `⊤` and `∧`, for
infinitary disjunctions and for existential quantification, distributivity, Frobenius, and the
equality rules.

## Main results

* `LeanPool.ClassifyingTopoi.GeometricTheory.Provable.sound`: **soundness**, a provable sequent
  holds in every model of `T` in every topos of sheaves on a small site. The structural rules
  follow from the order of subobjects, substitution from the substitution lemma
  (`CatStructure.interp_subst`), the existential rules from the adjunction between existential
  quantification and pullback, and distributivity, Frobenius and the equality rules, which are
  valid in every structure on a type, from the transfer of such validities to sheaf topoi
  (`CatStructure.interp_eq_of_realize_iff`);
* `LeanPool.ClassifyingTopoi.IsClassifyingSite.interp_le_iff`: a sequent holds in the generic
  model of a classifying site iff it holds in every model; hence provable sequents hold in the
  generic model (`IsClassifyingSite.interp_le_of_provable`).

## Not formalised

Completeness (a sequent holding in the generic model is provable) is not formalised: the
classifying site of `LeanPool.ClassifyingTopoi.Syntactic` is not the syntactic category of `T`.
-/

@[expose] public section

universe w u₁ u₂ u

namespace LeanPool.ClassifyingTopoi

open FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits

attribute [local instance high] Sheaf.instHasColimitsOfShape

variable {L : Language.{u₁, u₂}}

namespace GeometricTheory

/-- Provability of geometric sequents from the axioms of a geometric theory, in geometric
sequent calculus. -/
inductive Provable (T : GeometricTheory.{w} L) : Sequent.{w} L → Prop
  /-- The axioms of the theory. -/
  | ax {σ : Sequent.{w} L} : σ ∈ T → Provable T σ
  /-- Identity. -/
  | refl {n : ℕ} (φ : GeometricFormula.{w} L n) : Provable T ⟨n, φ, φ⟩
  /-- Cut. -/
  | trans {n : ℕ} {φ ψ χ : GeometricFormula.{w} L n} :
      Provable T ⟨n, φ, ψ⟩ → Provable T ⟨n, ψ, χ⟩ → Provable T ⟨n, φ, χ⟩
  /-- Substitution of terms. -/
  | subst {n m : ℕ} {φ ψ : GeometricFormula.{w} L n} (σ : Fin n → L.Term (Fin m)) :
      Provable T ⟨n, φ, ψ⟩ → Provable T ⟨m, φ.subst σ, ψ.subst σ⟩
  /-- `⊤` is the greatest formula. -/
  | top {n : ℕ} (φ : GeometricFormula.{w} L n) : Provable T ⟨n, φ, .top⟩
  /-- First projection of a conjunction. -/
  | and_left {n : ℕ} (φ ψ : GeometricFormula.{w} L n) : Provable T ⟨n, .and φ ψ, φ⟩
  /-- Second projection of a conjunction. -/
  | and_right {n : ℕ} (φ ψ : GeometricFormula.{w} L n) : Provable T ⟨n, .and φ ψ, ψ⟩
  /-- Introduction of a conjunction. -/
  | and_intro {n : ℕ} {χ φ ψ : GeometricFormula.{w} L n} :
      Provable T ⟨n, χ, φ⟩ → Provable T ⟨n, χ, ψ⟩ → Provable T ⟨n, χ, .and φ ψ⟩
  /-- Introduction of a disjunction. -/
  | iSup_intro {n : ℕ} {ι : Type w} (φ : ι → GeometricFormula.{w} L n) (i : ι) :
      Provable T ⟨n, φ i, .iSup φ⟩
  /-- Elimination of a disjunction. -/
  | iSup_elim {n : ℕ} {ι : Type w} {φ : ι → GeometricFormula.{w} L n}
      {ψ : GeometricFormula.{w} L n} :
      (∀ i, Provable T ⟨n, φ i, ψ⟩) → Provable T ⟨n, .iSup φ, ψ⟩
  /-- Existential quantification, from the quantified sequent. -/
  | ex_left {n : ℕ} {φ : GeometricFormula.{w} L (n + 1)} {ψ : GeometricFormula.{w} L n} :
      Provable T ⟨n, .ex φ, ψ⟩ → Provable T ⟨n + 1, φ, ψ.weaken⟩
  /-- Existential quantification, to the quantified sequent. -/
  | ex_right {n : ℕ} {φ : GeometricFormula.{w} L (n + 1)} {ψ : GeometricFormula.{w} L n} :
      Provable T ⟨n + 1, φ, ψ.weaken⟩ → Provable T ⟨n, .ex φ, ψ⟩
  /-- Distributivity of conjunctions over disjunctions. -/
  | distrib {n : ℕ} (φ : GeometricFormula.{w} L n) {ι : Type w}
      (ψ : ι → GeometricFormula.{w} L n) :
      Provable T ⟨n, .and φ (.iSup ψ), .iSup fun i => .and φ (ψ i)⟩
  /-- The Frobenius rule. -/
  | frobenius {n : ℕ} (φ : GeometricFormula.{w} L n) (ψ : GeometricFormula.{w} L (n + 1)) :
      Provable T ⟨n, .and φ (.ex ψ), .ex (.and φ.weaken ψ)⟩
  /-- Reflexivity of equality. -/
  | eq_refl {n : ℕ} (t : L.Term (Fin n)) : Provable T ⟨n, .top, .equal t t⟩
  /-- Substitution of equal terms. -/
  | eq_subst {m : ℕ} (φ : GeometricFormula.{w} L (m + 1)) (t₁ t₂ : L.Term (Fin m)) :
      Provable T ⟨m, .and (.equal t₁ t₂) (φ.subst (Fin.snoc Term.var t₁)),
        φ.subst (Fin.snoc Term.var t₂)⟩

end GeometricTheory

namespace CatStructure

variable {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
  (M : CatStructure L (Sheaf K (Type u)))

/-- A sequent valid in every structure on a type holds in every structure in a sheaf topos. -/
theorem interp_le_of_realize {n : ℕ} {φ ψ : GeometricFormula.{u} L n}
    (h : ∀ (N : Type u) [L.Structure N] (x : Fin n → N), φ.Realize x → ψ.Realize x) :
    M.interp φ ≤ M.interp ψ := by
  have e := interp_eq_of_realize_iff (φ := φ) (ψ := .and φ ψ)
    (fun N _ x => ⟨fun hx => ⟨hx, h N x hx⟩, fun hx => hx.1⟩) M
  rw [e]
  exact inf_le_right

/-- The interpretation of a weakened formula is the pullback along the projection. -/
theorem interp_weaken {n : ℕ} (ψ : GeometricFormula.{u} L n) :
    M.interp ψ.weaken = (Subobject.pullback (Pi.lift fun i : Fin n =>
      Pi.π (fun _ : Fin (n + 1) => M.carrier) i.castSucc)).obj (M.interp ψ) :=
  M.interp_subst ψ _

end CatStructure

namespace GeometricTheory.Provable

/-- **Soundness of geometric sequent calculus.** A sequent provable from the axioms of `T`
holds in every model of `T` in every topos of sheaves on a small site. -/
theorem sound {T : GeometricTheory.{u} L} {σ : Sequent.{u} L} (h : T.Provable σ)
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {M : CatStructure L (Sheaf K (Type u))} (hM : M.IsModel T) :
    M.interp σ.lhs ≤ M.interp σ.rhs := by
  induction h with
  | ax hσ => exact hM _ hσ
  | refl φ => exact le_rfl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | subst σ _ ih =>
    rw [CatStructure.interp_subst, CatStructure.interp_subst]
    exact (Subobject.pullback _).monotone ih
  | top φ => exact le_top
  | and_left φ ψ => exact inf_le_left
  | and_right φ ψ => exact inf_le_right
  | and_intro _ _ ih₁ ih₂ => exact le_inf ih₁ ih₂
  | iSup_intro φ i =>
    change M.interp (φ i) ≤ imageSubobject (Sigma.desc fun i => (M.interp (φ i)).arrow)
    exact Subobject.le_of_comm (Sigma.ι (fun i => (M.interp (φ i) : Sheaf K (Type u))) i ≫
      factorThruImageSubobject _) (by simp)
  | iSup_elim _ ih =>
    change imageSubobject (Sigma.desc fun i => (M.interp _).arrow) ≤ _
    exact imageSubobject_le _ (Sigma.desc fun i => Subobject.ofLE _ _ (ih i)) (by ext; simp)
  | ex_left _ ih =>
    change (Subobject.exists _).obj _ ≤ _ at ih
    rw [CatStructure.interp_weaken]
    exact ((Subobject.existsPullbackAdj _).gc.le_iff_le).1 ih
  | ex_right _ ih =>
    rw [CatStructure.interp_weaken] at ih
    exact ((Subobject.existsPullbackAdj _).gc.le_iff_le).2 ih
  | distrib φ ψ =>
    exact M.interp_le_of_realize fun N _ x ⟨hφ, i, hψ⟩ => ⟨i, hφ, hψ⟩
  | frobenius φ ψ =>
    refine M.interp_le_of_realize fun N _ x ⟨hφ, a, hψ⟩ => ⟨a, ?_, hψ⟩
    rw [GeometricFormula.realize_weaken, Fin.init_snoc]
    exact hφ
  | eq_refl t => exact M.interp_le_of_realize fun N _ x _ => rfl
  | eq_subst φ t₁ t₂ =>
    refine M.interp_le_of_realize fun N _ x ⟨he, hφ⟩ => ?_
    rw [GeometricFormula.realize_subst] at hφ ⊢
    convert hφ using 2
    rename_i i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]
      exact he.symm
    · simp

end GeometricTheory.Provable

namespace IsClassifyingSite

variable {T : GeometricTheory.{u} L} {C : Type u} [SmallCategory C]
  {J : GrothendieckTopology C} {U : CatStructure L (Sheaf J (Type u))}

/-- **Universality of the generic model.** A sequent holds in the generic model of a classifying
site iff it holds in every model of the theory in every topos of sheaves on a small site. -/
theorem interp_le_iff (hU : IsClassifyingSite T J U) (σ : Sequent.{u} L) :
    U.interp σ.lhs ≤ U.interp σ.rhs ↔
      ∀ (D : Type u) [SmallCategory D] (K : GrothendieckTopology D)
        (M : CatStructure L (Sheaf K (Type u))), M.IsModel T → M.interp σ.lhs ≤ M.interp σ.rhs := by
  refine ⟨fun h D _ K M hM => ?_, fun h => h C J U hU.isModel⟩
  obtain ⟨F, _, hF, hMF⟩ := hU.exists_isomorphic hM
  have := hF
  refine hMF.symm.isModel (T := {σ}) ?_ σ rfl
  intro τ hτ
  rw [Set.mem_singleton_iff] at hτ
  subst hτ
  rw [CatStructure.interp_map, CatStructure.interp_map]
  exact mapSubobject_mono _ h

/-- Provable sequents hold in the generic model of a classifying site. -/
theorem interp_le_of_provable (hU : IsClassifyingSite T J U) {σ : Sequent.{u} L}
    (h : T.Provable σ) : U.interp σ.lhs ≤ U.interp σ.rhs :=
  h.sound hU.isModel

end IsClassifyingSite

end LeanPool.ClassifyingTopoi
