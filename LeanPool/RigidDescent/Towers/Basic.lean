/-
Copyright (c) 2026 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
module

public import LeanPool.RigidDescent.Defs.Tower
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.Tactic.Lemma

/-!
# Towers: level maps and pro-isomorphisms

Paper, Conventions. Elementary facts about `IsProIso` (`Defs/Tower.lean`) used throughout:

* `isProIso_iff`: a level map `u : cst U ⟶ Y` is a pro-isomorphism if and only if some `u_k` is a
  monomorphism and, for `m ≥ k`, far enough up the tower the transition maps into `Y_m` factor
  through `u_m`;
* `IsProIso.of_app`, `IsProIso.map`: pro-isomorphisms are preserved by every functor and
  transported along isomorphisms (paper: "a functor acts on towers levelwise, and this extends
  to the pro-categories");
* `IsProIso.exists_const`: a level map of towers induces a map of the constant values (`cst` is
  full), and `IsProIso.isIso_of_comp`: `cst` reflects isomorphisms;
* `IsProZero`, a tower isomorphic to `0` in the pro-category.
-/

@[expose] public section

open CategoryTheory Opposite Limits

namespace RigidDescent

variable {S : Type*} [Category S]

namespace Tower

variable (Y : ℕᵒᵖ ⥤ S)

@[simp]
lemma t_refl (m : ℕ) : Tower.t Y (le_refl m) = 𝟙 _ := by
  simp [Tower.t]

@[reassoc (attr := simp)]
lemma t_comp {m m' m'' : ℕ} (h : m ≤ m') (h' : m' ≤ m'') :
    Tower.t Y h' ≫ Tower.t Y h = Tower.t Y (h.trans h') :=
  (Y.map_comp _ _).symm

variable {Y}

@[reassoc (attr := simp)]
lemma app_t {U : S} (u : (Functor.const ℕᵒᵖ).obj U ⟶ Y) {m m' : ℕ} (h : m ≤ m') :
    u.app (op m') ≫ Tower.t Y h = u.app (op m) :=
  (u.naturality _).symm.trans (Category.id_comp _)

@[reassoc]
lemma t_naturality {Y' : ℕᵒᵖ ⥤ S} (α : Y ⟶ Y') {m m' : ℕ} (h : m ≤ m') :
    Tower.t Y h ≫ α.app (op m) = α.app (op m') ≫ Tower.t Y' h :=
  α.naturality _

/-- A family of maps into the levels that is compatible with consecutive transition maps is
compatible with all of them. -/
lemma comp_t_of_succ {X : S} (f : ∀ m, X ⟶ Y.obj (op m))
    (hf : ∀ m, f (m + 1) ≫ Tower.t Y (Nat.le_succ m) = f m) {m m' : ℕ} (h : m ≤ m') :
    f m' ≫ Tower.t Y h = f m := by
  induction m', h using Nat.le_induction with
  | base => simp
  | succ n hmn ih => rw [← t_comp Y hmn (Nat.le_succ n), ← Category.assoc, hf, ih]

/-- The level map `cst X ⟶ Y` with components `f m`, for a compatible family `f`. -/
@[simps]
def levelMap {X : S} (f : ∀ m, X ⟶ Y.obj (op m))
    (hf : ∀ m, f (m + 1) ≫ Tower.t Y (Nat.le_succ m) = f m) :
    (Functor.const ℕᵒᵖ).obj X ⟶ Y where
  app m := f m.unop
  naturality m m' g := by
    exact (Category.id_comp _).trans (comp_t_of_succ f hf (leOfHom g.unop)).symm

end Tower

open Tower

variable {Y : ℕᵒᵖ ⥤ S} {U : S} {u : (Functor.const ℕᵒᵖ).obj U ⟶ Y}

/-- The data of a pro-isomorphism, with the factorization holding at every level `j` far
enough up the tower. -/
lemma IsProIso.exists_data (hu : IsProIso u) :
    ∃ (k : ℕ) (v : Y.obj (op k) ⟶ U) (N : ℕ → ℕ), u.app (op k) ≫ v = 𝟙 U ∧
      ∀ m j (hk : k ≤ j) (hm : m ≤ j), N m ≤ j →
        Tower.t Y hk ≫ v ≫ u.app (op m) = Tower.t Y hm := by
  obtain ⟨k, v, hv, H⟩ := hu
  choose N hkN hmN hN using H
  refine ⟨k, v, N, hv, fun m j hk hm hj => ?_⟩
  rw [← t_comp Y (hkN m) hj, Category.assoc, hN, t_comp]

/-- Paper, Conventions: a level map `u : cst U ⟶ Y` is an isomorphism in `Pro(S)` if and only
if some component `u_k` is a monomorphism and, for every `m ≥ k`, some transition map
`Y_{m'} ⟶ Y_m` factors through `u_m`. -/
theorem isProIso_iff :
    IsProIso u ↔ ∃ k, Mono (u.app (op k)) ∧ ∀ m, k ≤ m → ∃ (m' : ℕ) (h : m ≤ m')
      (w : Y.obj (op m') ⟶ U), Tower.t Y h = w ≫ u.app (op m) := by
  constructor
  · rintro ⟨k, v, hv, H⟩
    have : IsSplitMono (u.app (op k)) := IsSplitMono.mk' ⟨v, hv⟩
    refine ⟨k, inferInstance, fun m _ => ?_⟩
    obtain ⟨k', hk, hm, e⟩ := H m
    exact ⟨k', hm, Tower.t Y hk ≫ v, by rw [← e, Category.assoc]⟩
  · rintro ⟨k, hk, H⟩
    obtain ⟨m₁, h₁, w₁, e₁⟩ := H k le_rfl
    refine ⟨m₁, w₁, ?_, fun n => ?_⟩
    · rw [← cancel_mono (u.app (op k)), Category.assoc, ← e₁, app_t]
      exact (Category.id_comp _).symm
    · have hkp : k ≤ max n m₁ := le_trans h₁ (le_max_right n m₁)
      obtain ⟨p', hp, wp, ep⟩ := H (max n m₁) hkp
      refine ⟨p', le_trans (le_max_right n m₁) hp, le_trans (le_max_left n m₁) hp, ?_⟩
      have key : Tower.t Y (le_trans (le_max_right n m₁) hp) ≫ w₁ = wp := by
        rw [← cancel_mono (u.app (op k)), Category.assoc, ← e₁, t_comp,
          ← app_t u hkp, ← Category.assoc, ← ep, t_comp]
      rw [← Category.assoc, key, ← app_t u (le_max_left n m₁), ← Category.assoc, ← ep, t_comp]

lemma IsProIso.mono_app (hu : IsProIso u) : ∃ k, ∀ m, k ≤ m → Mono (u.app (op m)) := by
  obtain ⟨k, hk, -⟩ := isProIso_iff.1 hu
  refine ⟨k, fun m hm => ?_⟩
  have : Mono (u.app (op m) ≫ Tower.t Y hm) := by rw [app_t]; exact hk
  exact mono_of_mono _ (Tower.t Y hm)

/-- Pro-isomorphisms are transported along a functor `F` and isomorphisms `U' ≅ F U`,
`Y ⋙ F ≅ Y'`. -/
lemma IsProIso.of_app {S' : Type*} [Category S'] (hu : IsProIso u) (F : S ⥤ S')
    {Y' : ℕᵒᵖ ⥤ S'} {U' : S'} (u' : (Functor.const ℕᵒᵖ).obj U' ⟶ Y') (e : U' ≅ F.obj U)
    (β : Y ⋙ F ≅ Y')
    (h : ∀ m, u'.app (op m) = e.hom ≫ F.map (u.app (op m)) ≫ β.hom.app (op m)) :
    IsProIso u' := by
  obtain ⟨k, v, hv, H⟩ := hu
  refine ⟨k, β.inv.app (op k) ≫ F.map v ≫ e.inv, ?_, fun m => ?_⟩
  · rw [h]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← F.map_comp_assoc, hv, F.map_id, Category.id_comp, Iso.hom_inv_id]
    rfl
  · obtain ⟨k', hk, hm, e'⟩ := H m
    refine ⟨k', hk, hm, ?_⟩
    have n₁ : Tower.t Y' hk ≫ β.inv.app (op k) = β.inv.app (op k') ≫ F.map (Tower.t Y hk) :=
      β.inv.naturality _
    have n₂ : F.map (Tower.t Y hm) ≫ β.hom.app (op m) = β.hom.app (op k') ≫ Tower.t Y' hm :=
      β.hom.naturality _
    have e'' : F.map (Tower.t Y hk) ≫ F.map v ≫ F.map (u.app (op m)) = F.map (Tower.t Y hm) := by
      rw [← e', F.map_comp, F.map_comp]
    rw [h]
    simp only [Category.assoc]
    rw [reassoc_of% n₁, Iso.inv_hom_id_assoc, reassoc_of% e'', n₂, Iso.inv_hom_id_app_assoc]

/-- A functor `F` sends the level map with components `u_m` to the level map with components
`F(u_m)`. -/
noncomputable abbrev mapLevelMap {S' : Type*} [Category S'] (u : (Functor.const ℕᵒᵖ).obj U ⟶ Y)
    (F : S ⥤ S') : (Functor.const ℕᵒᵖ).obj (F.obj U) ⟶ Y ⋙ F :=
  Tower.levelMap (Y := Y ⋙ F) (fun m => F.map (u.app (op m)))
    (fun m => (F.map_comp _ _).symm.trans (congrArg F.map (app_t u (Nat.le_succ m))))

/-- Paper, Conventions: a functor preserves pro-isomorphisms of level maps. -/
lemma IsProIso.map (hu : IsProIso u) {S' : Type*} [Category S'] (F : S ⥤ S') :
    IsProIso (mapLevelMap u F) :=
  hu.of_app F _ (Iso.refl _) (Iso.refl _) (fun m => by simp)

lemma IsProIso.of_iso_comp {U' : S} {u' : (Functor.const ℕᵒᵖ).obj U' ⟶ Y} (hu' : IsProIso u')
    (φ : U ⟶ U') [IsIso φ] (u : (Functor.const ℕᵒᵖ).obj U ⟶ Y)
    (h : ∀ m, u.app (op m) = φ ≫ u'.app (op m)) : IsProIso u :=
  hu'.of_app (𝟭 S) u (asIso φ) (Functor.rightUnitor Y) (fun m => by simp [h])

/-- A level map `P ⟶ Q` induces a map `U ⟶ U'` of constant values, for level maps
`cst U ⟶ P` and a pro-isomorphism `cst U' ⟶ Q` (`cst` is full). -/
lemma IsProIso.exists_const {P Q : ℕᵒᵖ ⥤ S} {U U' : S} (u : (Functor.const ℕᵒᵖ).obj U ⟶ P)
    {u' : (Functor.const ℕᵒᵖ).obj U' ⟶ Q} (hu' : IsProIso u') (f : P ⟶ Q) :
    ∃ φ : U ⟶ U', ∀ m, φ ≫ u'.app (op m) = u.app (op m) ≫ f.app (op m) := by
  obtain ⟨k, v, -, H⟩ := hu'
  refine ⟨u.app (op k) ≫ f.app (op k) ≫ v, fun m => ?_⟩
  obtain ⟨k', hk, hm, e⟩ := H m
  calc (u.app (op k) ≫ f.app (op k) ≫ v) ≫ u'.app (op m)
      = u.app (op k') ≫ f.app (op k') ≫ Tower.t Q hk ≫ v ≫ u'.app (op m) := by
        rw [← app_t u hk]; simp only [Category.assoc, t_naturality_assoc]
    _ = u.app (op m) ≫ f.app (op m) := by
        rw [e, ← t_naturality, app_t_assoc]

/-- `cst` reflects isomorphisms: if `cst φ ≫ u'` and `u'` are pro-isomorphisms, then `φ` is an
isomorphism. -/
lemma IsProIso.isIso_of_comp {U' : S} {u' : (Functor.const ℕᵒᵖ).obj U' ⟶ Y} (hu : IsProIso u)
    (hu' : IsProIso u') (φ : U ⟶ U') (h : ∀ m, u.app (op m) = φ ≫ u'.app (op m)) :
    IsIso φ := by
  obtain ⟨k, v, hv, H⟩ := hu
  obtain ⟨k₁, v₁, hv₁, -⟩ := hu'
  obtain ⟨k', hk, hk₁, e⟩ := H k₁
  refine ⟨⟨u'.app (op k) ≫ v, by rw [← Category.assoc, ← h, hv], ?_⟩⟩
  calc (u'.app (op k) ≫ v) ≫ φ = (u'.app (op k) ≫ v ≫ φ) ≫ u'.app (op k₁) ≫ v₁ := by
        rw [hv₁, Category.comp_id, Category.assoc]
    _ = u'.app (op k') ≫ (Tower.t Y hk ≫ v ≫ u.app (op k₁)) ≫ v₁ := by
        rw [h k₁, ← app_t u' hk]; simp only [Category.assoc]
    _ = 𝟙 U' := by rw [e, app_t_assoc, hv₁]

lemma IsProConstant.of_iso {Y' : ℕᵒᵖ ⥤ S} (h : IsProConstant Y) (β : Y ≅ Y') :
    IsProConstant Y' := by
  obtain ⟨U, u, hu⟩ := h
  exact ⟨U, u ≫ β.hom,
    hu.of_app (𝟭 S) _ (Iso.refl _) (Functor.rightUnitor Y ≪≫ β) (fun m => by simp)⟩

lemma isProIso_id (X : S) : IsProIso (𝟙 ((Functor.const ℕᵒᵖ).obj X)) :=
  ⟨0, 𝟙 X, Category.comp_id _, fun m =>
    ⟨m, Nat.zero_le _, le_rfl, by simp [Tower.t]⟩⟩

lemma isProConstant_const (X : S) : IsProConstant ((Functor.const ℕᵒᵖ).obj X) :=
  ⟨X, _, isProIso_id X⟩

/-- Paper, Conventions: a functor preserves pro-constant towers. -/
lemma IsProConstant.map (h : IsProConstant Y) {S' : Type*} [Category S'] (F : S ⥤ S') :
    IsProConstant (Y ⋙ F) := by
  obtain ⟨U, u, hu⟩ := h
  exact ⟨F.obj U, _, hu.map F⟩

section Zero

variable [HasZeroMorphisms S]

/-- A tower is *pro-zero* (isomorphic to `0` in the pro-category) if every level is killed by
some transition map into it. -/
def IsProZero (Y : ℕᵒᵖ ⥤ S) : Prop :=
  ∀ m, ∃ (m' : ℕ) (h : m ≤ m'), Tower.t Y h = 0

lemma IsProIso.isProZero (hU : IsZero U) (hu : IsProIso u) : IsProZero Y := by
  obtain ⟨k, v, -, H⟩ := hu
  intro m
  obtain ⟨k', hk, hm, e⟩ := H m
  exact ⟨k', hm, by rw [← e, hU.eq_of_tgt v 0, zero_comp, comp_zero]⟩

open ZeroObject in
lemma IsProZero.isProIso_zero [HasZeroObject S] (h : IsProZero Y) :
    IsProIso (0 : (Functor.const ℕᵒᵖ).obj (0 : S) ⟶ Y) := by
  refine ⟨0, 0, (isZero_zero S).eq_of_src _ _, fun m => ?_⟩
  obtain ⟨m', hm, e⟩ := h m
  exact ⟨m', Nat.zero_le _, hm, by rw [e, zero_comp, comp_zero]⟩

open ZeroObject in
lemma IsProZero.isProConstant [HasZeroObject S] (h : IsProZero Y) : IsProConstant Y :=
  ⟨0, 0, h.isProIso_zero⟩

open ZeroObject in
lemma isProZero_iff [HasZeroObject S] :
    IsProZero Y ↔ ∃ (U : S) (_ : IsZero U) (u : (Functor.const ℕᵒᵖ).obj U ⟶ Y), IsProIso u :=
  ⟨fun h => ⟨0, isZero_zero S, 0, h.isProIso_zero⟩,
    fun ⟨_, hU, _, hu⟩ => hu.isProZero hU⟩

end Zero

end RigidDescent
