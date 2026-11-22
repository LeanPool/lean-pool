/-
Copyright (c) 2026 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
module

public import LeanPool.RigidDescent.Defs.Descent
public import LeanPool.RigidDescent.Towers.AddCommGrp

/-!
# Homotopy limits of towers

Paper, Conventions, and Lemma 3.3 (`lem:holim-const`).

* `exists_isHolim`: homotopy limits exist (in a pretriangulated category with countable
  products);
* `IsHolim.exists_iso`, `IsHolim.of_iso`: they are unique up to an isomorphism compatible with
  the projections;
* the Milnor sequence `0 → lim¹ Hom(ΣZ, Y_m) → Hom(Z, holim Y) → lim Hom(Z, Y_m) → 0`, stated
  as `IsHolim.exists_lift` (surjectivity) and `IsHolim.eq_zero` (injectivity when the `lim¹`
  term vanishes);
* `isHolim_zero_iff`: `0` is a homotopy limit if and only if `1 - shift` is invertible, and
  then `lim` and `lim¹` of `Hom(Z, Y_m)` vanish for every `Z`;
* Lemma 3.3: for a pro-isomorphism `u : cst U ⟶ Y`, `U` is a limit of `Y`
  (`IsProIso.isLimit`, in any category), and so is every homotopy limit (`IsHolim.isLimit`);
* the paper's wording of Definition 1.1 (`isEffectiveDescentType_iff_isIso`): the comparison
  map `τ : B ⊗ holim Y ⟶ holim (B ⊗ Y)` is an isomorphism.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory Opposite Preadditive Pretriangulated ZeroObject

universe v u

namespace RigidDescent

open Tower

section Additive

variable {T : Type u} [Category.{v} T] [Preadditive T] [HasCountableProducts T]

/-! ### `1 - shift` -/

section OneSubShift

variable (Y : ℕᵒᵖ ⥤ T)

@[reassoc]
lemma oneSubShift_π (m : ℕ) :
    oneSubShift Y ≫ Pi.π (fun n : ℕ => Y.obj (op n)) m =
      Pi.π (fun n : ℕ => Y.obj (op n)) m -
        Pi.π (fun n : ℕ => Y.obj (op n)) (m + 1) ≫ Tower.t Y (Nat.le_succ m) := by
  simp [oneSubShift]

lemma lift_comp_oneSubShift {Z : T} (x : ∀ m, Z ⟶ Y.obj (op m)) :
    Pi.lift x ≫ oneSubShift Y =
      Pi.lift fun m => x m - x (m + 1) ≫ Tower.t Y (Nat.le_succ m) :=
  Pi.hom_ext _ _ fun m => by simp [oneSubShift_π]

end OneSubShift

/-! ### Towers `Hom(Z, Y_m)` -/

variable {Y : ℕᵒᵖ ⥤ T}

omit [HasCountableProducts T] in
lemma isCompatible_coyoneda_iff {Z : T} (x : ∀ m, Z ⟶ Y.obj (op m)) :
    IsCompatible (Y ⋙ preadditiveCoyoneda.obj (op Z)) x ↔
      ∀ m, x (m + 1) ≫ Tower.t Y (Nat.le_succ m) = x m :=
  Iff.rfl

omit [HasCountableProducts T] in
lemma limOneVanishes_coyoneda_iff {Z : T} :
    LimOneVanishes (Y ⋙ preadditiveCoyoneda.obj (op Z)) ↔
      ∀ a : ∀ m, Z ⟶ Y.obj (op m), ∃ b : ∀ m, Z ⟶ Y.obj (op m),
        ∀ m, b m - b (m + 1) ≫ Tower.t Y (Nat.le_succ m) = a m :=
  Iff.rfl

/-- If `1 - shift` is invertible, then `lim Hom(Z, Y_m) = 0`. -/
lemma limVanishes_of_isIso [IsIso (oneSubShift Y)] (Z : T) :
    LimVanishes (Y ⋙ preadditiveCoyoneda.obj (op Z)) := by
  intro x hx m
  let x' : ∀ m, Z ⟶ Y.obj (op m) := x
  have hx' : ∀ m, x' (m + 1) ≫ Tower.t Y (Nat.le_succ m) = x' m := hx
  have h0 : Pi.lift x' ≫ oneSubShift Y = 0 := by
    rw [lift_comp_oneSubShift]
    exact Pi.hom_ext _ _ fun m => by simp [hx']
  have h1 : Pi.lift x' = 0 := by rw [← cancel_mono (oneSubShift Y), h0, zero_comp]
  have := congrArg (· ≫ Pi.π (fun n : ℕ => Y.obj (op n)) m) h1
  simp only [Pi.lift_comp_π, zero_comp] at this
  exact this

/-- If `1 - shift` is invertible, then `lim¹ Hom(Z, Y_m) = 0`. -/
lemma limOneVanishes_of_isIso [IsIso (oneSubShift Y)] (Z : T) :
    LimOneVanishes (Y ⋙ preadditiveCoyoneda.obj (op Z)) := by
  rw [limOneVanishes_coyoneda_iff]
  intro a
  let b : Z ⟶ ∏ᶜ fun m : ℕ => Y.obj (op m) := Pi.lift a ≫ inv (oneSubShift Y)
  refine ⟨fun m => b ≫ Pi.π (fun n : ℕ => Y.obj (op n)) m, fun m => ?_⟩
  have hb : b ≫ oneSubShift Y = Pi.lift a := by simp [b]
  have := congrArg (· ≫ Pi.π (fun n : ℕ => Y.obj (op n)) m) hb
  simp only [Category.assoc, oneSubShift_π, comp_sub, Pi.lift_comp_π] at this
  rw [Category.assoc]
  exact this

end Additive

variable {T : Type u} [Category.{v} T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T] [HasCountableProducts T]

/-! ### Existence, uniqueness, the Milnor sequence -/

variable {Y : ℕᵒᵖ ⥤ T} {L : T} {p : ∀ m, L ⟶ Y.obj (op m)}

/-- Paper, Conventions: homotopy limits exist. -/
theorem exists_isHolim (Y : ℕᵒᵖ ⥤ T) : ∃ (L : T) (p : ∀ m, L ⟶ Y.obj (op m)), IsHolim Y L p := by
  obtain ⟨L, f, e, hT⟩ := distinguished_cocone_triangle₁ (oneSubShift Y)
  refine ⟨L, fun m => f ≫ Pi.π (fun n : ℕ => Y.obj (op n)) m, e, ?_⟩
  have : Pi.lift (fun m => f ≫ Pi.π (fun n : ℕ => Y.obj (op n)) m) = f :=
    Pi.hom_ext _ _ fun m => by simp
  rw [this]
  exact hT

/-- The projections of a homotopy limit are compatible with the transition maps. -/
lemma IsHolim.comp_p (h : IsHolim Y L p) (m : ℕ) :
    p (m + 1) ≫ Tower.t Y (Nat.le_succ m) = p m := by
  obtain ⟨e, he⟩ := h
  have h0 : Pi.lift p ≫ oneSubShift Y = 0 := comp_distTriang_mor_zero₁₂ _ he
  rw [lift_comp_oneSubShift] at h0
  have := congrArg (· ≫ Pi.π (fun n : ℕ => Y.obj (op n)) m) h0
  simp only [Pi.lift_comp_π, zero_comp] at this
  exact (sub_eq_zero.1 this).symm

/-- A homotopy limit `(L, p)` is transported along an isomorphism `L' ≅ L`. -/
lemma IsHolim.of_iso (h : IsHolim Y L p) {L' : T} (φ : L' ≅ L) :
    IsHolim Y L' fun m => φ.hom ≫ p m := by
  obtain ⟨e, he⟩ := h
  refine ⟨e ≫ φ.inv⟦(1 : ℤ)⟧', isomorphic_distinguished _ he _ ?_⟩
  refine Triangle.isoMk _ _ φ (Iso.refl _) (Iso.refl _) ?_ ?_ ?_
  · exact Pi.hom_ext _ _ fun m => by simp
  · simp
  · simp [← Functor.map_comp]

/-- Paper, Conventions: homotopy limits are unique up to an isomorphism compatible with the
projections. -/
theorem IsHolim.exists_iso (h : IsHolim Y L p) {L' : T} {p' : ∀ m, L' ⟶ Y.obj (op m)}
    (h' : IsHolim Y L' p') : ∃ φ : L ≅ L', ∀ m, φ.hom ≫ p' m = p m := by
  obtain ⟨e, he⟩ := h
  obtain ⟨e', he'⟩ := h'
  obtain ⟨a, ha₁, ha₂⟩ := complete_distinguished_triangle_morphism₁ _ _ he he' (𝟙 _) (𝟙 _)
    (by simp)
  let φ : Triangle.mk (Pi.lift p) (oneSubShift Y) e ⟶
      Triangle.mk (Pi.lift p') (oneSubShift Y) e' :=
    { hom₁ := a
      hom₂ := 𝟙 _
      hom₃ := 𝟙 _
      comm₁ := ha₁
      comm₂ := by simp
      comm₃ := ha₂ }
  have : IsIso a := isIso₁_of_isIso₂₃ φ he he' (by dsimp [φ]; infer_instance)
    (by dsimp [φ]; infer_instance)
  refine ⟨asIso a, fun m => ?_⟩
  have := congrArg (· ≫ Pi.π (fun n : ℕ => Y.obj (op n)) m) ha₁
  simp only [Triangle.mk_mor₁, Category.comp_id, Category.assoc, Pi.lift_comp_π] at this
  exact this.symm

/-- The Milnor sequence, surjectivity: a compatible family of maps `Z ⟶ Y_m` factors through
the homotopy limit. -/
theorem IsHolim.exists_lift (h : IsHolim Y L p) {Z : T} (x : ∀ m, Z ⟶ Y.obj (op m))
    (hx : ∀ m, x (m + 1) ≫ Tower.t Y (Nat.le_succ m) = x m) :
    ∃ y : Z ⟶ L, ∀ m, y ≫ p m = x m := by
  obtain ⟨e, he⟩ := h
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ _ he (Pi.lift x) (by
    change Pi.lift x ≫ oneSubShift Y = 0
    rw [lift_comp_oneSubShift]
    exact Pi.hom_ext _ _ fun m => by simp [hx])
  refine ⟨g, fun m => ?_⟩
  have := congrArg (· ≫ Pi.π (fun n : ℕ => Y.obj (op n)) m) hg
  simp only [Triangle.mk_mor₁, Category.assoc, Pi.lift_comp_π] at this
  exact this.symm

/-- The Milnor sequence, injectivity: if `lim¹ Hom(Z⟦1⟧, Y_m) = 0`, a map `Z ⟶ holim Y` is
determined by its components. -/
theorem IsHolim.eq_zero (h : IsHolim Y L p) {Z : T}
    (h1 : LimOneVanishes (Y ⋙ preadditiveCoyoneda.obj (op (Z⟦(1 : ℤ)⟧)))) {x : Z ⟶ L}
    (hx : ∀ m, x ≫ p m = 0) : x = 0 := by
  obtain ⟨e, he⟩ := h
  have hx' : x ≫ Pi.lift p = 0 := Pi.hom_ext _ _ fun m => by simp [hx]
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₁ _ he (x⟦(1 : ℤ)⟧') (by
    change x⟦(1 : ℤ)⟧' ≫ (Pi.lift p)⟦(1 : ℤ)⟧' = 0
    rw [← Functor.map_comp, hx', Functor.map_zero])
  obtain ⟨b, hb⟩ := limOneVanishes_coyoneda_iff.1 h1
    fun m => g ≫ Pi.π (fun n : ℕ => Y.obj (op n)) m
  have hg' : g = Pi.lift b ≫ oneSubShift Y := by
    refine Pi.hom_ext _ _ fun m => ?_
    rw [Category.assoc, oneSubShift_π, comp_sub, Pi.lift_comp_π, ← Category.assoc, Pi.lift_comp_π]
    exact (hb m).symm
  apply (shiftFunctor T (1 : ℤ)).map_injective
  have h23 : oneSubShift Y ≫ e = 0 := comp_distTriang_mor_zero₂₃ _ he
  change x⟦(1 : ℤ)⟧' = (0 : Z ⟶ L)⟦(1 : ℤ)⟧'
  rw [hg, hg', Functor.map_zero]
  change (Pi.lift b ≫ oneSubShift Y) ≫ e = 0
  rw [Category.assoc, h23, comp_zero]

/-! ### Zero homotopy limits -/

/-- `0` is a homotopy limit of `Y` if and only if `1 - shift` is an isomorphism. -/
theorem isHolim_zero_iff : IsHolim Y 0 0 ↔ IsIso (oneSubShift Y) := by
  constructor
  · rintro ⟨e, he⟩
    exact (Triangle.isZero₁_iff_isIso₂ _ he).1 (isZero_zero T)
  · intro
    refine ⟨0, isomorphic_distinguished _
      (contractible_distinguished₁ (∏ᶜ fun m : ℕ => Y.obj (op m))) _ ?_⟩
    refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (asIso (oneSubShift Y)).symm ?_ ?_ ?_
    · exact Pi.hom_ext _ _ fun m => by simp
    · simp
    · simp

/-- A tower with zero transition maps has homotopy limit `0`. -/
lemma isHolim_zero_of_t_eq_zero (h : ∀ m, Tower.t Y (Nat.le_succ m) = 0) : IsHolim Y 0 0 := by
  have e : oneSubShift Y = 𝟙 _ := by
    have : (Pi.lift fun m => Pi.π (fun n : ℕ => Y.obj (op n)) (m + 1) ≫
        Tower.t Y (Nat.le_succ m)) = 0 := Pi.hom_ext _ _ fun m => by simp [h]
    rw [oneSubShift, this, sub_zero]
  rw [isHolim_zero_iff, e]
  infer_instance


/-! ### Lemma 3.3, second half -/

/-- Paper, Lemma 3.3 (`lem:holim-const`): if `Y` is pro-constant, every homotopy limit of `Y`,
with its maps `p_m`, is a limit of `Y`. -/
noncomputable def IsHolim.isLimit (h : IsHolim Y L p) (hY : IsProConstant Y) :
    IsLimit (Cone.mk L (Tower.levelMap p h.comp_p)) := by
  refine IsLimit.ofExistsUnique fun s => ?_
  obtain ⟨y, hy⟩ := h.exists_lift (fun m => s.π.app (op m)) fun m => app_t s.π (Nat.le_succ m)
  refine ⟨y, fun j => hy j.unop, fun f hf => ?_⟩
  rw [← sub_eq_zero]
  refine h.eq_zero (hY.map (preadditiveCoyoneda.obj (op _))).limOneVanishes fun m => ?_
  rw [sub_comp, hy m]
  exact sub_eq_zero.2 (hf (op m))

/-- Over a pro-constant tower, a compatible family of maps factors uniquely through a homotopy
limit. -/
lemma IsHolim.existsUnique_comp (h : IsHolim Y L p) (hY : IsProConstant Y) {M : T}
    (q : ∀ m, M ⟶ Y.obj (op m)) (hq : ∀ m, q (m + 1) ≫ Tower.t Y (Nat.le_succ m) = q m) :
    ∃! τ : M ⟶ L, ∀ m, τ ≫ p m = q m := by
  obtain ⟨τ, hτ, hτ'⟩ := (h.isLimit hY).existsUnique (Cone.mk M (Tower.levelMap q hq))
  exact ⟨τ, fun m => hτ (op m), fun τ' h' => hτ' τ' fun j => h' j.unop⟩

/-- Over a pro-constant tower, `(M, q)` is a homotopy limit if and only if the comparison map
`τ : M ⟶ L` to a homotopy limit `(L, p)` is an isomorphism. -/
theorem IsHolim.isHolim_iff_isIso (h : IsHolim Y L p) (hY : IsProConstant Y) {M : T}
    {q : ∀ m, M ⟶ Y.obj (op m)} (τ : M ⟶ L) (hτ : ∀ m, τ ≫ p m = q m) :
    IsHolim Y M q ↔ IsIso τ := by
  constructor
  · intro hM
    obtain ⟨φ, hφ⟩ := hM.exists_iso h
    have : τ = φ.hom := (h.isLimit hY).hom_ext fun j => (hτ j.unop).trans (hφ j.unop).symm
    rw [this]
    infer_instance
  · intro
    have := h.of_iso (asIso τ)
    have e : (fun m => (asIso τ).hom ≫ p m) = q := funext hτ
    rwa [e] at this

/-! ### Definition 1.1 in the paper's wording -/

section Descent

variable [MonoidalCategory T]

/-- Paper, Definition 1.1 (`def:descent`), in the paper's wording: `B` is of effective descent
type if and only if `B ⊗ X = 0` implies `X = 0`, and for every tower `Y` with `B ⊗ Y`
pro-constant, the map `τ : B ⊗ holim Y ⟶ holim (B ⊗ Y)` with `p'_m ∘ τ = B ⊗ p_m` (which
exists and is unique, `IsHolim.existsUnique_comp`) is an isomorphism. -/
theorem isEffectiveDescentType_iff_isIso (B : T) :
    IsEffectiveDescentType B ↔ (∀ X : T, IsZero (B ⊗ X) → IsZero X) ∧
      ∀ Y : ℕᵒᵖ ⥤ T, IsProConstant (Y ⋙ tensorLeft B) →
        ∀ (L : T) (p : ∀ m, L ⟶ Y.obj (op m)), IsHolim Y L p →
        ∀ (L' : T) (p' : ∀ m, L' ⟶ (Y ⋙ tensorLeft B).obj (op m)),
          IsHolim (Y ⋙ tensorLeft B) L' p' →
        ∀ τ : B ⊗ L ⟶ L', (∀ m, τ ≫ p' m = B ◁ p m) → IsIso τ := by
  refine and_congr_right fun _ => ⟨fun H Y hY L p hL L' p' hL' τ hτ => ?_,
    fun H Y hY L p hL => ?_⟩
  · exact (hL'.isHolim_iff_isIso hY τ hτ).1 (H Y hY L p hL)
  · obtain ⟨L', p', hL'⟩ := exists_isHolim (Y ⋙ tensorLeft B)
    have hq : ∀ m, (B ◁ p (m + 1)) ≫ Tower.t (Y ⋙ tensorLeft B) (Nat.le_succ m) = B ◁ p m :=
      fun m => by
        change (B ◁ p (m + 1)) ≫ B ◁ Tower.t Y (Nat.le_succ m) = _
        rw [← MonoidalCategory.whiskerLeft_comp, hL.comp_p]
    obtain ⟨τ, hτ, -⟩ := hL'.existsUnique_comp hY (fun m => B ◁ p m) hq
    exact (hL'.isHolim_iff_isIso hY τ hτ).2 (H Y hY L p hL L' p' hL' τ hτ)

end Descent

end RigidDescent
