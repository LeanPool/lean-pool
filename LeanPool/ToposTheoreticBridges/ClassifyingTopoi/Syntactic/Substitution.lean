/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.ToposTheoreticBridges.ClassifyingTopoi.Syntactic.Transport

/-!
# Substitution in geometric formulas

`GeometricFormula.subst φ σ` substitutes the terms `σ i` (in the context `Fin m`) for the variables
of `φ` (in the context `Fin n`), lifting the substitution under existential quantifiers.

## Main results

* `LeanPool.ClassifyingTopoi.GeometricFormula.realize_subst`: the substitution lemma in
  structures on types;
* `LeanPool.ClassifyingTopoi.CatStructure.interp_subst`: the substitution lemma in every topos of
  sheaves on a small site: the interpretation of `φ.subst σ` is the pullback of the
  interpretation of `φ` along the tuple of the interpretations of the terms `σ i`. It is proved
  objectwise in presheaf topoi (`CatStructure.interp_subst_of_presheaf`, from the Kripke–Joyal
  semantics `Syntactic.mem_range_interp_app_iff`), then transported along sheafification, which
  commutes with interpretations, and along isomorphisms of structures.
-/

@[expose] public section

universe w u₁ u₂ u

namespace LeanPool.ClassifyingTopoi

open FirstOrder FirstOrder.Language CategoryTheory CategoryTheory.Limits

attribute [local instance high] Sheaf.instHasColimitsOfShape

variable {L : Language.{u₁, u₂}}

namespace GeometricFormula

/-- The lift of a substitution under an existential quantifier: the last variable is sent to
the last variable. -/
def liftSubst {n m : ℕ} (σ : Fin n → L.Term (Fin m)) : Fin (n + 1) → L.Term (Fin (m + 1)) :=
  Fin.snoc (fun i => (σ i).relabel Fin.castSucc) (Term.var (Fin.last m))

/-- Substitution of terms for the variables of a geometric formula. -/
def subst : {n m : ℕ} → GeometricFormula.{w} L n → (Fin n → L.Term (Fin m)) →
    GeometricFormula.{w} L m
  | _, _, .top, _ => .top
  | _, _, .and φ ψ, σ => .and (φ.subst σ) (ψ.subst σ)
  | _, _, .iSup φ, σ => .iSup fun i => (φ i).subst σ
  | _, _, .equal t₁ t₂, σ => .equal (t₁.subst σ) (t₂.subst σ)
  | _, _, .rel R ts, σ => .rel R fun i => (ts i).subst σ
  | _, _, .ex φ, σ => .ex (φ.subst (liftSubst σ))

/-- The weakening of a formula to a context with one more variable. -/
def weaken {n : ℕ} (φ : GeometricFormula.{w} L n) : GeometricFormula.{w} L (n + 1) :=
  φ.subst fun i => Term.var (Fin.castSucc i)

/-- The realization of a lifted substitution. -/
theorem realize_liftSubst {M : Type*} [L.Structure M] {n m : ℕ} (σ : Fin n → L.Term (Fin m))
    (x : Fin m → M) (a : M) :
    (fun i => (liftSubst σ i).realize (Fin.snoc x a : Fin (m + 1) → M)) =
      Fin.snoc (fun i => (σ i).realize x) a := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [liftSubst]
  · simp only [liftSubst, Fin.snoc_castSucc, Term.realize_relabel]
    congr 1
    funext k
    simp

/-- **Substitution lemma** in structures on types. -/
theorem realize_subst {M : Type*} [L.Structure M] {n m : ℕ} (φ : GeometricFormula.{w} L n)
    (σ : Fin n → L.Term (Fin m)) (x : Fin m → M) :
    (φ.subst σ).Realize x ↔ φ.Realize fun i => (σ i).realize x := by
  induction φ generalizing m with
  | top => exact Iff.rfl
  | and φ ψ ihφ ihψ => exact and_congr (ihφ σ x) (ihψ σ x)
  | iSup φ ih => exact exists_congr fun i => ih i σ x
  | equal t₁ t₂ =>
    change (t₁.subst σ).realize x = (t₂.subst σ).realize x ↔ _
    rw [Term.realize_subst, Term.realize_subst]
    rfl
  | rel R ts =>
    change Structure.RelMap R (fun i => ((ts i).subst σ).realize x) ↔ _
    simp only [Term.realize_subst]
    rfl
  | ex φ ih =>
    change (∃ a, (φ.subst (liftSubst σ)).Realize (Fin.snoc x a)) ↔ ∃ a, φ.Realize _
    refine exists_congr fun a => ?_
    rw [ih, realize_liftSubst]

/-- Satisfaction of a weakened formula. -/
theorem realize_weaken {M : Type*} [L.Structure M] {n : ℕ} (φ : GeometricFormula.{w} L n)
    (x : Fin (n + 1) → M) : φ.weaken.Realize x ↔ φ.Realize (Fin.init x) := by
  rw [weaken, realize_subst]
  rfl

end GeometricFormula

namespace CatStructure

section General

variable {E : Type*} [Category E] [HasFiniteLimits E] [HasImages E] [HasCoproducts.{w} E]

/-- The substitution property of a structure: substitution is interpreted by pullback along
the tuple of interpretations of the terms. -/
def SubstProp (M : CatStructure L E) : Prop :=
  ∀ {n m : ℕ} (φ : GeometricFormula.{w} L n) (σ : Fin n → L.Term (Fin m)),
    M.interp (φ.subst σ) =
      (Subobject.pullback (Pi.lift fun i => M.termMap (σ i))).obj (M.interp φ)

/-- The substitution property is invariant under isomorphism of structures. -/
theorem SubstProp.of_isomorphic {M N : CatStructure L E} (hM : M.SubstProp)
    (h : M.Isomorphic N) : N.SubstProp := by
  obtain ⟨ε, h₁, h₂⟩ := h
  intro n m φ σ
  rw [Isomorphic.interp_eq_pullback h₁ h₂, Isomorphic.interp_eq_pullback h₁ h₂, hM,
    ← Subobject.pullback_comp, ← Subobject.pullback_comp]
  congr 2
  ext i
  simp [h₂.termMap]

variable {E' : Type*} [Category E'] [HasFiniteLimits E'] [HasImages E'] [HasCoproducts.{w} E']
  [StrongEpiCategory E'] (F : E ⥤ E') [PreservesFiniteLimits F] [F.PreservesEpimorphisms]
  [∀ ι : Type w, PreservesColimitsOfShape (Discrete ι) F]

/-- The substitution property is preserved by functors commuting with interpretations. -/
theorem SubstProp.map {M : CatStructure L E} (hM : M.SubstProp) : (M.map F).SubstProp := by
  intro n m φ σ
  rw [interp_map, interp_map, hM, mapSubobject_pullback _ (piComparison F _)]
  congr 2
  simp only [termMap_map]
  rw [map_piLift]

end General

section Presheaf

variable {D : Type*} [Category D]

/-- Terms in a presheaf structure are interpreted objectwise. -/
theorem termMap_app (P : CatStructure L (D ⥤ Type w)) {n : ℕ} (t : L.Term (Fin n)) (d : D)
    (z : (P.pow n).obj d) :
    (P.termMap t).app d z =
      @Term.realize L _ (P.fiberStr d) _ (Syntactic.secEquiv P.carrier n d z) t := by
  induction t with
  | var i => exact (Syntactic.secEquiv_apply z i).symm
  | func f ts ih =>
    change (P.funMap f).app d ((Pi.lift fun j => P.termMap (ts j)).app d z) =
      (P.fiberStr d).funMap f _
    rw [fiberStr_funMap]
    congr 1
    rw [Equiv.eq_symm_apply]
    funext j
    rw [Syntactic.secEquiv_apply, ← NatTrans.comp_app_apply, Pi.lift_comp_π, ih]

/-- The substitution lemma in presheaf topoi. -/
theorem substProp_of_presheaf (P : CatStructure L (D ⥤ Type w)) : P.SubstProp := by
  intro n m φ σ
  have key : ∀ (d : D) (z : (P.pow m).obj d),
      Syntactic.secEquiv P.carrier n d ((Pi.lift fun i => P.termMap (σ i)).app d z) =
        fun i => @Term.realize L _ (P.fiberStr d) _ (Syntactic.secEquiv P.carrier m d z) (σ i) :=
    fun d z => by
      funext i
      rw [Syntactic.secEquiv_apply, ← NatTrans.comp_app_apply, Pi.lift_comp_π, termMap_app]
  refine le_antisymm ?_ ?_ <;> rw [Syntactic.le_iff_range_app_subset] <;> intro d z hz
  · rw [Syntactic.range_app_pullback, Set.mem_preimage, Syntactic.mem_range_interp_app_iff,
      key, ← @GeometricFormula.realize_subst L _ (P.fiberStr d)]
    exact (Syntactic.mem_range_interp_app_iff P _ d z).1 hz
  · rw [Syntactic.range_app_pullback, Set.mem_preimage, Syntactic.mem_range_interp_app_iff,
      key, ← @GeometricFormula.realize_subst L _ (P.fiberStr d)] at hz
    exact (Syntactic.mem_range_interp_app_iff P _ d z).2 hz

end Presheaf

/-- **Substitution lemma in sheaf topoi.** In a topos of sheaves on a small site, the
interpretation of `φ.subst σ` is the pullback of the interpretation of `φ` along the tuple of
interpretations of the terms `σ i`. -/
theorem interp_subst {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    (M : CatStructure L (Sheaf K (Type u))) {n m : ℕ} (φ : GeometricFormula.{u} L n)
    (σ : Fin n → L.Term (Fin m)) :
    M.interp (φ.subst σ) =
      (Subobject.pullback (Pi.lift fun i => M.termMap (σ i))).obj (M.interp φ) :=
  SubstProp.of_isomorphic (SubstProp.map (presheafToSheaf K (Type u))
    (substProp_of_presheaf (M.map (sheafToPresheaf K (Type u)))))
      (isomorphic_map_sheafToPresheaf_map_presheafToSheaf M).symm φ σ

end CatStructure

end LeanPool.ClassifyingTopoi
