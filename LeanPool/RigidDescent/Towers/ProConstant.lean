/-
Copyright (c) 2026 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
module

public import LeanPool.RigidDescent.Towers.AddCommGrp
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.Algebra.Category.Grp.EpiMono

/-!
# Lemma 3.1: pro-constancy in a five-term exact sequence

Paper, Lemma 3.1 (`lem:proab`): if `A₁ → A₂ → Z → A₃ → A₄` is an exact sequence of towers in
`A(T)` and every `Aᵢ` is pro-constant, then `Z` is pro-constant. We work with towers in any
functor category `C ⥤ AddCommGrpCat` (`A(T)` is the case `C = (T^ω)ᵒᵖ`), and with sequences that
are exact levelwise, which is how the lemma is used (Prop. 3.5).

There are no pro-categories here (a design decision), so the proof is direct: `Z` is
pro-isomorphic to the constant tower on its objectwise limit `towerLim Z`, by the criterion
`isProIso_iff`. Both conditions of the criterion are checked elementwise at each object `K` of
`C`, with bounds that do not depend on `K` (`ProIsoBounds`):

* `ExactFive.eq_zero_of_isCompatible`: a compatible family in `Z` vanishing at a fixed level `k`
  vanishes;
* `ExactFive.exists_isCompatible`: for every `m`, there is `m'` such that the image of
  `Z_{m'} → Z_m` consists of components of compatible families.

The first two sentences of Lemma 3.1 (`Pro(A(T))` is abelian, `cst` is exact and fully
faithful) are replaced by what the paper uses them for: `IsProIso.exists_const` and
`IsProIso.isIso_of_comp` (`Towers/Basic.lean`) and the five-term statement here.
-/

@[expose] public section

open CategoryTheory Opposite Limits

universe w

namespace RigidDescent

open Tower

namespace Tower

/-! ### Compatible families -/

section Groups

variable {G G' : ℕᵒᵖ ⥤ AddCommGrpCat.{w}}

lemma IsCompatible.map (α : G ⟶ G') {x : ∀ m, G.obj (op m)} (hx : IsCompatible G x) :
    IsCompatible G' fun m => α.app (op m) (x m) := fun m => by
  rw [← t_naturality_apply, hx]

lemma isCompatible_app {U : AddCommGrpCat.{w}} (u : (Functor.const ℕᵒᵖ).obj U ⟶ G) (z : U) :
    IsCompatible G fun m => u.app (op m) z :=
  fun _ => app_t_apply u _ z

lemma IsCompatible.add {x y : ∀ m, G.obj (op m)} (hx : IsCompatible G x)
    (hy : IsCompatible G y) : IsCompatible G fun m => x m + y m := fun m => by
  rw [map_add, hx m, hy m]

variable (G) in
/-- `lim G`, as the subgroup of compatible families in `∏ G_m`. -/
def limSubgroup : AddSubgroup (∀ m, G.obj (op m)) where
  carrier := {x | IsCompatible G x}
  add_mem' {x y} hx hy := hx.add hy
  zero_mem' _ := map_zero _
  neg_mem' {x} hx m := by
    change Tower.t G _ (-x (m + 1)) = -x m
    rw [map_neg, hx m]

/-- The map `lim G → lim G'` induced by a map of towers. -/
def limMap (α : G ⟶ G') : limSubgroup G →+ limSubgroup G' where
  toFun x := ⟨fun m => α.app (op m) (x.1 m), x.2.map α⟩
  map_zero' := by
    ext m
    exact map_zero _
  map_add' x y := by
    ext m
    exact map_add _ _ _

/-- Lifting a compatible family along `β`, when `ker β = im α` levelwise and `lim¹` vanishes on
the source of `α`. -/
lemma exists_isCompatible_lift {A₁ A₂ Z : ℕᵒᵖ ⥤ AddCommGrpCat.{w}} (α : A₁ ⟶ A₂)
    (β : A₂ ⟶ Z) (hαβ : ∀ m x, β.app (op m) (α.app (op m) x) = 0)
    (ex : ∀ m y, β.app (op m) y = 0 → ∃ x, α.app (op m) x = y) (h1 : LimOneVanishes A₁)
    {ζ : ∀ m, Z.obj (op m)} (hζ : IsCompatible Z ζ) (hlift : ∀ m, ∃ y, β.app (op m) y = ζ m) :
    ∃ y : ∀ m, A₂.obj (op m), IsCompatible A₂ y ∧ ∀ m, β.app (op m) (y m) = ζ m := by
  choose y₀ hy₀ using hlift
  have hd : ∀ m, β.app (op m) (y₀ m - Tower.t A₂ (Nat.le_succ m) (y₀ (m + 1))) = 0 :=
    fun m => by rw [map_sub, t_naturality_apply, hy₀, hy₀, hζ m, sub_self]
  choose x hx using fun m => ex m _ (hd m)
  obtain ⟨e, he⟩ := h1 x
  refine ⟨fun m => y₀ m - α.app (op m) (e m), fun m => ?_, fun m => ?_⟩
  · dsimp only
    rw [map_sub, ← t_naturality_apply]
    have h1 := hx m
    rw [← he m, map_sub] at h1
    rw [sub_eq_iff_eq_add.1 h1]
    abel
  · rw [map_sub, hy₀, hαβ, sub_zero]

end Groups

/-! ### Bounds for a pro-isomorphism -/

variable {G : ℕᵒᵖ ⥤ AddCommGrpCat.{w}} {U : AddCommGrpCat.{w}}

/-- Elementwise consequences of a pro-isomorphism `u : cst U ⟶ G`, with explicit bounds `k`
and `N`: `u_m` is injective for `m ≥ k`; the image of `G_j → G_m` lies in the image of `u_m`
for `j ≥ N m`; `lim¹ G = 0`; and every element of `lim G` comes from `U` (Lemma 3.2). -/
structure ProIsoBounds (u : (Functor.const ℕᵒᵖ).obj U ⟶ G) (k : ℕ) (N : ℕ → ℕ) : Prop where
  inj : ∀ m, k ≤ m → ∀ z : U, u.app (op m) z = 0 → z = 0
  image : ∀ m j (h : m ≤ j), N m ≤ j → ∀ x : G.obj (op j),
    ∃ z : U, u.app (op m) z = Tower.t G h x
  limOne : LimOneVanishes G
  lim : ∀ x, IsCompatible G x → ∃ z : U, ∀ m, u.app (op m) z = x m

/-- The bounds of a pro-isomorphism `u`, after applying a functor `F` to abelian groups: they
depend only on the data of `u`, not on `F`. -/
lemma ProIsoBounds.of_map {S : Type*} [Category S] {Y : ℕᵒᵖ ⥤ S} {V : S}
    {u : (Functor.const ℕᵒᵖ).obj V ⟶ Y} (hu : IsProIso u) {k : ℕ} (v : Y.obj (op k) ⟶ V)
    (N : ℕ → ℕ) (hv : u.app (op k) ≫ v = 𝟙 V)
    (hN : ∀ m j (hk : k ≤ j) (hm : m ≤ j), N m ≤ j →
      Tower.t Y hk ≫ v ≫ u.app (op m) = Tower.t Y hm)
    (F : S ⥤ AddCommGrpCat.{w}) :
    ProIsoBounds (mapLevelMap u F) k fun m => max (N m) k where
  inj m hm z hz := by
    have h1 : F.map v ((mapLevelMap u F).app (op k) z) = z := by
      have := ConcreteCategory.congr_hom (congrArg F.map hv) z
      rw [F.map_comp, CategoryTheory.comp_apply] at this
      exact this.trans
        ((ConcreteCategory.congr_hom (F.map_id V) z).trans (CategoryTheory.id_apply _))
    have h2 : (mapLevelMap u F).app (op k) z = 0 := by
      rw [← app_t_apply (mapLevelMap u F) hm z, hz, map_zero]
    rw [← h1, h2, map_zero]
  image m j h hj x := by
    have hk : k ≤ j := le_trans (le_max_right _ _) hj
    refine ⟨F.map v (Tower.t (Y ⋙ F) hk x), ?_⟩
    have := ConcreteCategory.congr_hom
      (congrArg F.map (hN m j hk h (le_trans (le_max_left _ _) hj))) x
    simp only [F.map_comp, CategoryTheory.comp_apply] at this
    exact this
  limOne := (hu.map F).limOneVanishes
  lim x hx := ((hu.map F).existsUnique_eq hx).exists

/-! ### Five-term exact sequences of towers of abelian groups -/

section Five

variable {A₁ A₂ Z A₃ A₄ : ℕᵒᵖ ⥤ AddCommGrpCat.{w}}

/-- A sequence of towers `A₁ → A₂ → Z → A₃ → A₄` that is exact levelwise (at `A₂`, `Z` and
`A₃`). -/
structure ExactFive (α : A₁ ⟶ A₂) (β : A₂ ⟶ Z) (γ : Z ⟶ A₃) (ε : A₃ ⟶ A₄) : Prop where
  αβ : ∀ m (x : A₁.obj (op m)), β.app (op m) (α.app (op m) x) = 0
  βγ : ∀ m (x : A₂.obj (op m)), γ.app (op m) (β.app (op m) x) = 0
  γε : ∀ m (x : Z.obj (op m)), ε.app (op m) (γ.app (op m) x) = 0
  ex₂ : ∀ m (y : A₂.obj (op m)), β.app (op m) y = 0 → ∃ x, α.app (op m) x = y
  exZ : ∀ m (z : Z.obj (op m)), γ.app (op m) z = 0 → ∃ y, β.app (op m) y = z
  ex₃ : ∀ m (w : A₃.obj (op m)), ε.app (op m) w = 0 → ∃ z, γ.app (op m) z = w

variable {α : A₁ ⟶ A₂} {β : A₂ ⟶ Z} {γ : Z ⟶ A₃} {ε : A₃ ⟶ A₄}

/-- In a levelwise exact `A₁ → A₂ → Z → A₃ → A₄` with `A₁, A₂, A₃` pro-constant, a compatible
family in `Z` vanishing at a level `k ≥ k₂, N₁ k₂, k₃` vanishes. -/
lemma ExactFive.eq_zero_of_isCompatible (hE : ExactFive α β γ ε)
    {U₁ U₂ U₃ : AddCommGrpCat.{w}} {u₁ : (Functor.const ℕᵒᵖ).obj U₁ ⟶ A₁}
    {u₂ : (Functor.const ℕᵒᵖ).obj U₂ ⟶ A₂} {u₃ : (Functor.const ℕᵒᵖ).obj U₃ ⟶ A₃}
    {k₁ k₂ k₃ : ℕ} {N₁ N₂ N₃ : ℕ → ℕ} (b₁ : ProIsoBounds u₁ k₁ N₁)
    (b₂ : ProIsoBounds u₂ k₂ N₂) (b₃ : ProIsoBounds u₃ k₃ N₃) {k : ℕ} (hk₂ : k₂ ≤ k)
    (hN₁ : N₁ k₂ ≤ k) (hk₃ : k₃ ≤ k) {ζ : ∀ m, Z.obj (op m)} (hζ : IsCompatible Z ζ)
    (h0 : ζ k = 0) (m : ℕ) : ζ m = 0 := by
  obtain ⟨z₃, hz₃⟩ := b₃.lim _ (hζ.map γ)
  have hz₃0 : z₃ = 0 := b₃.inj k hk₃ z₃ (by rw [hz₃, h0, map_zero])
  have hγ : ∀ n, γ.app (op n) (ζ n) = 0 := fun n => by rw [← hz₃ n, hz₃0, map_zero]
  obtain ⟨y, hy, hβy⟩ := exists_isCompatible_lift α β hE.αβ hE.ex₂ b₁.limOne hζ
    (fun n => hE.exZ n _ (hγ n))
  obtain ⟨z₂, hz₂⟩ := b₂.lim y hy
  obtain ⟨p, hp⟩ := hE.ex₂ k (y k) (by rw [hβy, h0])
  obtain ⟨y₁, hy₁⟩ := b₁.image k₂ k hk₂ hN₁ p
  obtain ⟨z', hz'⟩ := b₂.lim _ ((isCompatible_app u₁ y₁).map α)
  have hz : z' = z₂ := by
    have : u₂.app (op k₂) (z' - z₂) = 0 := by
      rw [map_sub, hz', hz₂, hy₁, t_naturality_apply, hp, hy.t_apply, sub_self]
    exact sub_eq_zero.1 (b₂.inj k₂ le_rfl _ this)
  rw [← hβy m, ← hz₂ m, ← hz, hz' m, hE.αβ]

/-- In a levelwise exact `A₁ → A₂ → Z → A₃ → A₄` with `A₂, A₃, A₄` pro-constant, for
`m ≤ m₁ ≤ m'` far enough apart, the image of `Z_{m'} → Z_m` consists of components of compatible
families. -/
lemma ExactFive.exists_isCompatible (hE : ExactFive α β γ ε)
    {U₂ U₃ U₄ : AddCommGrpCat.{w}} {u₂ : (Functor.const ℕᵒᵖ).obj U₂ ⟶ A₂}
    {u₃ : (Functor.const ℕᵒᵖ).obj U₃ ⟶ A₃} {u₄ : (Functor.const ℕᵒᵖ).obj U₄ ⟶ A₄}
    {k₂ k₃ k₄ : ℕ} {N₂ N₃ N₄ : ℕ → ℕ} (b₂ : ProIsoBounds u₂ k₂ N₂)
    (b₃ : ProIsoBounds u₃ k₃ N₃) (b₄ : ProIsoBounds u₄ k₄ N₄) {m m₁ m' : ℕ} (hm : m ≤ m₁)
    (hN₂ : N₂ m ≤ m₁) (hk₄ : k₄ ≤ m₁) (hm₁ : m₁ ≤ m') (hN₃ : N₃ m₁ ≤ m')
    (x : Z.obj (op m')) :
    ∃ ζ : ∀ n, Z.obj (op n), IsCompatible Z ζ ∧ ζ m = Tower.t Z (hm.trans hm₁) x := by
  obtain ⟨z₃, hz₃⟩ := b₃.image m₁ m' hm₁ hN₃ (γ.app (op m') x)
  obtain ⟨z₄, hz₄⟩ := b₄.lim _ ((isCompatible_app u₃ z₃).map ε)
  have hz₄0 : z₄ = 0 :=
    b₄.inj m₁ hk₄ z₄ (by rw [hz₄, hz₃, t_naturality_apply, hE.γε, map_zero])
  have hε : ∀ n, ε.app (op n) (u₃.app (op n) z₃) = 0 := fun n => by
    rw [← hz₄ n, hz₄0, map_zero]
  obtain ⟨ζ', hζ', hγζ'⟩ := exists_isCompatible_lift β γ hE.βγ hE.exZ b₂.limOne
    (isCompatible_app u₃ z₃) (fun n => hE.ex₃ n _ (hε n))
  obtain ⟨a, ha⟩ := hE.exZ m₁ (Tower.t Z hm₁ x - ζ' m₁) (by
    rw [map_sub, t_naturality_apply, ← hz₃, hγζ', sub_self])
  obtain ⟨z₂, hz₂⟩ := b₂.image m m₁ hm hN₂ a
  refine ⟨fun n => ζ' n + β.app (op n) (u₂.app (op n) z₂),
    hζ'.add ((isCompatible_app u₂ z₂).map β), ?_⟩
  dsimp only
  rw [hz₂, t_naturality_apply, ha, map_sub, t_t_apply, hζ'.t_apply]
  abel

end Five

end Tower

/-! ### Towers in a functor category -/

section Functor

variable {C : Type*} [Category C]

/-- The objectwise limit of a tower in `C ⥤ AddCommGrpCat`: compatible families. -/
noncomputable def towerLim (Z : ℕᵒᵖ ⥤ C ⥤ AddCommGrpCat.{w}) : C ⥤ AddCommGrpCat.{w} where
  obj K := AddCommGrpCat.of (limSubgroup (Z ⋙ (evaluation C AddCommGrpCat.{w}).obj K))
  map f := AddCommGrpCat.ofHom
    (limMap (Functor.whiskerLeft Z ((evaluation C AddCommGrpCat.{w}).map f)))
  map_id K := by
    ext x m
    exact ConcreteCategory.congr_hom ((Z.obj (op m)).map_id K) (x.1 m)
  map_comp f g := by
    ext x m
    exact ConcreteCategory.congr_hom ((Z.obj (op m)).map_comp f g) (x.1 m)

/-- The projections `towerLim Z ⟶ Z_m`. -/
noncomputable def towerLimπ (Z : ℕᵒᵖ ⥤ C ⥤ AddCommGrpCat.{w}) :
    (Functor.const ℕᵒᵖ).obj (towerLim Z) ⟶ Z where
  app m :=
    { app K := AddCommGrpCat.ofHom
        ((Pi.evalAddMonoidHom (fun n => (Z.obj (op n)).obj K) m.unop).comp
          (limSubgroup _).subtype)
      naturality K K' f := by
        ext x
        rfl }
  naturality m m' g := by
    ext K x
    exact (x.2.t_apply (leOfHom g.unop)).symm

lemma towerLimπ_app_app_apply (Z : ℕᵒᵖ ⥤ C ⥤ AddCommGrpCat.{w}) (m : ℕ) (K : C)
    (x : (towerLim Z).obj K) : ((towerLimπ Z).app (op m)).app K x = x.1 m :=
  rfl

/-- Levelwise exactness of a sequence of towers in `C ⥤ AddCommGrpCat`, objectwise. -/
def LevelwiseExactFive {A₁ A₂ Z A₃ A₄ : ℕᵒᵖ ⥤ C ⥤ AddCommGrpCat.{w}} (α : A₁ ⟶ A₂)
    (β : A₂ ⟶ Z) (γ : Z ⟶ A₃) (ε : A₃ ⟶ A₄) : Prop :=
  ∀ K : C, ExactFive (Functor.whiskerRight α ((evaluation C AddCommGrpCat.{w}).obj K))
    (Functor.whiskerRight β ((evaluation C AddCommGrpCat.{w}).obj K))
    (Functor.whiskerRight γ ((evaluation C AddCommGrpCat.{w}).obj K))
    (Functor.whiskerRight ε ((evaluation C AddCommGrpCat.{w}).obj K))

/-- Data of a pro-isomorphism in `C ⥤ AddCommGrpCat`, giving bounds uniform in the object. -/
lemma IsProConstant.exists_bounds {A : ℕᵒᵖ ⥤ C ⥤ AddCommGrpCat.{w}} (h : IsProConstant A) :
    ∃ (U : C ⥤ AddCommGrpCat.{w}) (u : (Functor.const ℕᵒᵖ).obj U ⟶ A) (k : ℕ) (N : ℕ → ℕ),
      ∀ K, ProIsoBounds (mapLevelMap u ((evaluation C AddCommGrpCat.{w}).obj K)) k N := by
  obtain ⟨U, u, hu⟩ := h
  obtain ⟨k, v, N, hv, hN⟩ := hu.exists_data
  exact ⟨U, u, k, _, fun K => ProIsoBounds.of_map hu v N hv hN _⟩

/-- Paper, Lemma 3.1 (`lem:proab`), in the form used (Prop. 3.5): if
`A₁ → A₂ → Z → A₃ → A₄` is a levelwise exact sequence of towers in `C ⥤ AddCommGrpCat` (for
instance in `A(T)`) and every `Aᵢ` is pro-constant, then `Z` is pro-constant. -/
theorem isProConstant_of_levelwiseExactFive {A₁ A₂ Z A₃ A₄ : ℕᵒᵖ ⥤ C ⥤ AddCommGrpCat.{w}}
    {α : A₁ ⟶ A₂} {β : A₂ ⟶ Z} {γ : Z ⟶ A₃} {ε : A₃ ⟶ A₄} (hE : LevelwiseExactFive α β γ ε)
    (h₁ : IsProConstant A₁) (h₂ : IsProConstant A₂) (h₃ : IsProConstant A₃)
    (h₄ : IsProConstant A₄) : IsProConstant Z := by
  obtain ⟨U₁, u₁, k₁, N₁, b₁⟩ := h₁.exists_bounds
  obtain ⟨U₂, u₂, k₂, N₂, b₂⟩ := h₂.exists_bounds
  obtain ⟨U₃, u₃, k₃, N₃, b₃⟩ := h₃.exists_bounds
  obtain ⟨U₄, u₄, k₄, N₄, b₄⟩ := h₄.exists_bounds
  set k := max (max k₂ (N₁ k₂)) k₃ with hk
  have hzero : ∀ K (x : (towerLim Z).obj K), x.1 k = 0 → x = 0 := fun K x hx =>
    Subtype.ext (funext fun n => (hE K).eq_zero_of_isCompatible (b₁ K) (b₂ K) (b₃ K)
      (by omega) (by omega) (by omega) x.2 hx n)
  have hmono : ∀ m, k ≤ m → Mono ((towerLimπ Z).app (op m)) := by
    intro m hm
    rw [NatTrans.mono_iff_mono_app]
    intro K
    rw [AddCommGrpCat.mono_iff_injective, injective_iff_map_eq_zero]
    intro x hx
    refine hzero K x ?_
    rw [← x.2.t_apply hm]
    exact (congrArg _ hx).trans (map_zero _)
  refine ⟨towerLim Z, towerLimπ Z, isProIso_iff.2 ⟨k, hmono k le_rfl, fun m hm => ?_⟩⟩
  have := hmono m hm
  set m₁ := max (max m (N₂ m)) k₄ with hm₁
  set m' := max m₁ (N₃ m₁) with hm'
  have h₁ : m ≤ m₁ := by omega
  have h₂ : m₁ ≤ m' := by omega
  have hcond : Tower.t Z (h₁.trans h₂) ≫ cokernel.π ((towerLimπ Z).app (op m)) = 0 := by
    ext K x
    obtain ⟨ζ, hζ, hζm⟩ := (hE K).exists_isCompatible (b₂ K) (b₃ K) (b₄ K) h₁ (by omega)
      (by omega) h₂ (by omega) x
    let xζ : (towerLim Z).obj K := ⟨ζ, hζ⟩
    have e : (Tower.t Z (h₁.trans h₂)).app K x = ((towerLimπ Z).app (op m)).app K xζ :=
      hζm.symm
    have h0 := ConcreteCategory.congr_hom
      (NatTrans.congr_app (cokernel.condition ((towerLimπ Z).app (op m))) K) xζ
    simp only [NatTrans.comp_app, CategoryTheory.comp_apply, NatTrans.app_zero] at h0 ⊢
    rw [e, h0]
    rfl
  exact ⟨m', h₁.trans h₂, Abelian.monoLift _ _ hcond, (Abelian.monoLift_comp _ _ _).symm⟩

/-- Paper, Lemma 3.1 (`lem:proab`) with `A₁ = A₂ = 0`: if `0 → Z → A₃ → A₄` is levelwise exact
and `A₃`, `A₄` are pro-constant, then `Z` is pro-constant. -/
theorem isProConstant_of_levelwiseKernel {Z A₃ A₄ : ℕᵒᵖ ⥤ C ⥤ AddCommGrpCat.{w}}
    {γ : Z ⟶ A₃} {ε : A₃ ⟶ A₄}
    (hγε : ∀ m K (x : (Z.obj (op m)).obj K), (ε.app (op m)).app K ((γ.app (op m)).app K x) = 0)
    (hγ : ∀ m K (x : (Z.obj (op m)).obj K), (γ.app (op m)).app K x = 0 → x = 0)
    (hex : ∀ m K (w : (A₃.obj (op m)).obj K), (ε.app (op m)).app K w = 0 →
      ∃ z, (γ.app (op m)).app K z = w)
    (h₃ : IsProConstant A₃) (h₄ : IsProConstant A₄) : IsProConstant Z := by
  let A₀ : ℕᵒᵖ ⥤ C ⥤ AddCommGrpCat.{w} :=
    (Functor.const ℕᵒᵖ).obj ((Functor.const C).obj (AddCommGrpCat.of PUnit))
  refine isProConstant_of_levelwiseExactFive (α := (0 : A₀ ⟶ A₀)) (β := (0 : A₀ ⟶ Z))
    (fun K => ⟨fun _ _ => rfl, fun _ _ => ?_, fun m x => hγε m K x, fun _ _ _ => ⟨0, rfl⟩,
      fun m z hz => ⟨0, (hγ m K z hz).symm⟩, fun m w hw => hex m K w hw⟩)
    (isProConstant_const _) (isProConstant_const _) h₃ h₄
  exact map_zero _

end Functor

end RigidDescent
