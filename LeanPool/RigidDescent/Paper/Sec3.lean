/-
Copyright (c) 2026 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
module

public import LeanPool.RigidDescent.Paper.Sec2
public import LeanPool.RigidDescent.Holim.Basic
public import LeanPool.RigidDescent.Towers.ProConstant
public import LeanPool.RigidDescent.Foundations.Brown

/-!
# Paper, §3: nil-purity implies effective descent

Fix a pure monomorphism `j : 𝟙 ⟶ E` with `E ∈ Thick^⊗(B)` (by Lemma 2.7 this is what nil-purity
of `B` gives), with cone `q : E ⟶ C`, and `g = (j ⊗ C) ∘ q : E ⟶ E ⊗ C`.

* Lemma 3.4 (`lem:pure-exact`): `restrictedYoneda_pureExact`, i.e.
  `0 → hZ → h(E ⊗ Z) → h(E ⊗ C ⊗ Z)` is exact; elementwise:
  `isPureMono_unitWhisker`, `unitWhisker_comp_eq_zero`, `exists_comp_unitWhisker_eq`.
* Proposition 3.5 (`prop:tails`): (a) `isProIso_map_holim_of_isPureMono`,
  `IsNilPure.isProIso_map_holim`; (b) `isIso_of_isHolim_tensor_of_isPureMono`,
  `IsNilPure.isIso_of_isHolim_tensor`.
* Theorem 3.6 (`thm:effective`): `isEffectiveDescentType_of_isPureMono`,
  `IsNilPure.isEffectiveDescentType`.

The proof of Proposition 3.5(a) works with `J'(M)`: "`h(W ⊗ M ⊗ Y)` is pro-constant for every
`W`" (`tensorProConstIdeal`), a thick tensor ideal containing `B` because `B ⊗ Y` is already
pro-constant in `T`. So (a) needs only Lemma 2.3, not that `h` is monoidal; (b) uses
`F_W ∘ h ≅ h ∘ (W ⊗ -)` (`tensorLeftATIso`).
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated ZeroObject

universe v u

namespace RigidDescent

open Tower

variable {T : Type u} [Category.{v} T] [Preadditive T]

section PureMono

lemma IsPureMono.comp {X Y Z : T} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsPureMono f)
    (hg : IsPureMono g) : IsPureMono (f ≫ g) :=
  fun K hK k hk => hf K hK k (hg K hK _ (by rw [Category.assoc, hk]))

lemma isPureMono_of_isIso {X Y : T} (f : X ⟶ Y) [IsIso f] : IsPureMono f :=
  fun _ _ k hk => by rw [← cancel_mono f, hk, zero_comp]

end PureMono

variable [HasZeroObject T] [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated T] [MonoidalCategory T] [TensorTriangulated T]

/-! ### Exactness after tensoring -/

section Exact

/-- For a distinguished triangle `X → Y → Z → ΣX` and any `W`, a map `K ⟶ Y ⊗ W` killed by
`g ⊗ W` lifts along `f ⊗ W`. -/
lemma exists_comp_whiskerRight_eq (Tr : Triangle T) (hT : Tr ∈ distTriang T) (W : T) {K : T}
    (y : K ⟶ Tr.obj₂ ⊗ W) (hy : y ≫ Tr.mor₂ ▷ W = 0) :
    ∃ x : K ⟶ Tr.obj₁ ⊗ W, x ≫ Tr.mor₁ ▷ W = y := by
  obtain ⟨x, hx⟩ := Triangle.coyoneda_exact₂ _ ((tensorRight W).map_distinguished Tr hT) y hy
  exact ⟨x, hx.symm⟩

lemma whiskerRight_comp_whiskerRight_eq_zero (Tr : Triangle T) (hT : Tr ∈ distTriang T)
    (W : T) : Tr.mor₁ ▷ W ≫ Tr.mor₂ ▷ W = 0 := by
  rw [← comp_whiskerRight, comp_distTriang_mor_zero₁₂ _ hT, MonoidalPreadditive.zero_whiskerRight]

/-- `M⟦n⟧ ≅ 𝟙⟦n⟧ ⊗ M`. -/
noncomputable def shiftIsoUnitTensor (M : T) (n : ℤ) : M⟦n⟧ ≅ (𝟙_ T)⟦n⟧ ⊗ M :=
  (shiftFunctor T n).mapIso (λ_ M).symm ≪≫ (((tensorRight M).commShiftIso n).app (𝟙_ T)).symm

/-- The objects `M` with `M ⊗ X = 0` form a thick tensor ideal. -/
lemma isThickTensorIdeal_isZero_tensor (X : T) :
    IsThickTensorIdeal (fun M => IsZero (M ⊗ X)) := by
  refine ⟨{ exists_zero := ?_, isStableUnderShiftBy := ?_, ext₂' := ?_ }, ⟨?_⟩, ?_⟩
  · exact ⟨0, isZero_zero T, Functor.map_isZero (tensorRight X) (isZero_zero T)⟩
  · intro n
    exact ⟨fun M h => (Functor.map_isZero (shiftFunctor T n) h).of_iso
      (((tensorRight X).commShiftIso n).app M)⟩
  · intro Tr hT h₁ h₃
    refine ObjectProperty.le_isoClosure _ _ ?_
    exact Triangle.isZero₂_of_isZero₁₃ _ ((tensorRight X).map_distinguished Tr hT) h₁ h₃
  · intro M N r h
    refine (IsZero.iff_id_eq_zero _).2 ?_
    rw [← id_whiskerRight, ← r.retract, comp_whiskerRight, h.eq_of_tgt (r.i ▷ X) 0, zero_comp]
  · intro W M h
    exact (Functor.map_isZero (tensorLeft W) h).of_iso (α_ W M X)

end Exact

/-! ### Lemma 3.4 -/

section PureExact

variable [IsTriangulated T] [CompactlyGenerated T] [BraidedCategory T] [MonoidalClosed T]
  {E C : T} {j : 𝟙_ T ⟶ E} {q : E ⟶ C} {w : C ⟶ (𝟙_ T)⟦(1 : ℤ)⟧}

/-- Paper, Lemma 3.4 (`lem:pure-exact`): `j ⊗ Z : Z ≅ 𝟙 ⊗ Z ⟶ E ⊗ Z` is a pure monomorphism
(Lemma 2.3). -/
lemma isPureMono_unitWhisker (hj : IsPureMono j) (Z : T) : IsPureMono ((λ_ Z).inv ≫ j ▷ Z) :=
  (isPureMono_of_isIso _).comp (hj.whiskerRight Z)

omit [IsTriangulated T] [CompactlyGenerated T] [BraidedCategory T] [MonoidalClosed T] in
lemma unitWhisker_comp_eq_zero (hT : Triangle.mk j q w ∈ distTriang T) (Z : T) :
    ((λ_ Z).inv ≫ j ▷ Z) ≫ (q ≫ (λ_ C).inv ≫ j ▷ C) ▷ Z = 0 := by
  have h : j ≫ q = 0 := comp_distTriang_mor_zero₁₂ _ hT
  rw [Category.assoc, ← comp_whiskerRight, ← Category.assoc j, h, zero_comp,
    MonoidalPreadditive.zero_whiskerRight, comp_zero]

/-- Paper, Lemma 3.4 (`lem:pure-exact`), exactness at `h(E ⊗ Z)`, elementwise: a map
`K ⟶ E ⊗ Z` from a compact `K` killed by `g ⊗ Z` factors through `j ⊗ Z`. -/
lemma exists_comp_unitWhisker_eq (hj : IsPureMono j) (hT : Triangle.mk j q w ∈ distTriang T)
    (Z : T) {K : T} (hK : IsCompactObj K) (y : K ⟶ E ⊗ Z)
    (hy : y ≫ (q ≫ (λ_ C).inv ≫ j ▷ C) ▷ Z = 0) :
    ∃ x : K ⟶ Z, x ≫ (λ_ Z).inv ≫ j ▷ Z = y := by
  have hpm : IsPureMono (((λ_ C).inv ≫ j ▷ C) ▷ Z) :=
    ((isPureMono_of_isIso _).comp (hj.whiskerRight C)).whiskerRight Z
  have hq : y ≫ q ▷ Z = 0 :=
    hpm K hK _ (by rw [Category.assoc, ← comp_whiskerRight]; exact hy)
  obtain ⟨x, hx⟩ := exists_comp_whiskerRight_eq _ hT Z y hq
  exact ⟨x ≫ (λ_ Z).hom, by rw [Category.assoc, Iso.hom_inv_id_assoc]; exact hx⟩

/-- Paper, Lemma 3.4 (`lem:pure-exact`): for a pure monomorphism `j : 𝟙 ⟶ E` with cone
`q : E ⟶ C`, and `g = (j ⊗ C) ∘ q`, the sequence `0 → hZ → h(E ⊗ Z) → h(E ⊗ C ⊗ Z)`, with maps
`h(j ⊗ Z)` and `h(g ⊗ Z)`, is exact in `A(T)`. -/
theorem restrictedYoneda_pureExact (hj : IsPureMono j) (hT : Triangle.mk j q w ∈ distTriang T)
    (Z : T) :
    Mono ((restrictedYoneda T).map ((λ_ Z).inv ≫ j ▷ Z)) ∧
      (ShortComplex.mk ((restrictedYoneda T).map ((λ_ Z).inv ≫ j ▷ Z))
        ((restrictedYoneda T).map ((q ≫ (λ_ C).inv ≫ j ▷ C) ▷ Z))
        (by rw [← Functor.map_comp, unitWhisker_comp_eq_zero hT, Functor.map_zero])).Exact := by
  refine ⟨(mono_restrictedYoneda_map_iff _).2 (isPureMono_unitWhisker hj Z), ?_⟩
  refine exact_of_forall_exact_evaluation _ fun K => ?_
  rw [ShortComplex.ab_exact_iff]
  intro y hy
  obtain ⟨x, hx⟩ := exists_comp_unitWhisker_eq hj hT Z (isCompactObj_compactObj K.unop) y hy
  exact ⟨x, hx⟩

end PureExact

/-! ### Towers `h(M ⊗ Y)` -/

section Towers

variable [IsTriangulated T] [CompactlyGenerated T]

variable (Y : ℕᵒᵖ ⥤ T)

/-- The tower `h(M ⊗ Y_m)` in `A(T)`. -/
noncomputable abbrev hTower (M : T) : ℕᵒᵖ ⥤ AT T := Y ⋙ tensorLeft M ⋙ restrictedYoneda T

/-- The map of towers `h(f ⊗ Y_m)`. -/
@[simps]
noncomputable def hTowerMap {M M' : T} (f : M ⟶ M') : hTower Y M ⟶ hTower Y M' where
  app m := (restrictedYoneda T).map (f ▷ Y.obj m)
  naturality m m' a := by
    simp only [Functor.comp_map, curriedTensor_obj_map, ← Functor.map_comp, whisker_exchange]

/-- The map of towers `h(j ⊗ Y_m) : h(Y_m) ⟶ h(E ⊗ Y_m)`. -/
@[simps]
noncomputable def unitTowerMap {E : T} (j : 𝟙_ T ⟶ E) : Y ⋙ restrictedYoneda T ⟶ hTower Y E where
  app m := (restrictedYoneda T).map ((λ_ (Y.obj m)).inv ≫ j ▷ Y.obj m)
  naturality m m' a := by
    simp only [Functor.comp_map, curriedTensor_obj_map, ← Functor.map_comp]
    congr 1
    rw [leftUnitor_inv_naturality_assoc, whisker_exchange, Category.assoc]

/-- `h(M ⊗ Y) ≅ h(M' ⊗ Y)` for `M ≅ M'`. -/
noncomputable def hTowerIso {M M' : T} (e : M ≅ M') : hTower Y M ≅ hTower Y M' :=
  NatIso.ofComponents (fun m => (restrictedYoneda T).mapIso (whiskerRightIso e (Y.obj m)))
    (fun a => (hTowerMap Y e.hom).naturality a)

variable {Y}

omit [TensorTriangulated T] in
lemma isProConstant_hTower_of_iso {M M' : T} (e : M ≅ M') (h : IsProConstant (hTower Y M)) :
    IsProConstant (hTower Y M') :=
  h.of_iso (hTowerIso Y e)

lemma isProConstant_hTower_of_isZero {M : T} (hM : IsZero M) : IsProConstant (hTower Y M) := by
  refine IsProZero.isProConstant fun m => ⟨m, le_rfl, ?_⟩
  have hz : IsZero ((hTower Y M).obj (op m)) :=
    Functor.map_isZero (restrictedYoneda T) (Functor.map_isZero (tensorRight (Y.obj (op m))) hM)
  exact hz.eq_of_tgt _ _

/-- A retract of a pro-constant tower `h(N ⊗ Y)` is pro-constant: `h(M ⊗ Y)` is the kernel of
`h((1 - e) ⊗ Y)` for the idempotent `e` of `N` (Lemma 3.1). -/
lemma isProConstant_hTower_of_retract {M N : T} (i : M ⟶ N) (r : N ⟶ M) (hir : i ≫ r = 𝟙 M)
    (h : IsProConstant (hTower Y N)) : IsProConstant (hTower Y M) := by
  refine isProConstant_of_levelwiseKernel (γ := hTowerMap Y i) (ε := hTowerMap Y (𝟙 N - r ≫ i))
    ?_ ?_ ?_ h h
  · rintro m K (x : compactObj T K.unop ⟶ M ⊗ Y.obj (op m))
    change (x ≫ i ▷ Y.obj (op m)) ≫ (𝟙 N - r ≫ i) ▷ Y.obj (op m) = 0
    rw [Category.assoc, ← comp_whiskerRight, Preadditive.comp_sub, Category.comp_id,
      ← Category.assoc, hir, Category.id_comp, sub_self, MonoidalPreadditive.zero_whiskerRight,
      comp_zero]
  · rintro m K (x : compactObj T K.unop ⟶ M ⊗ Y.obj (op m)) hx
    have hx' : x ≫ i ▷ Y.obj (op m) = 0 := hx
    have e : x = (x ≫ i ▷ Y.obj (op m)) ≫ r ▷ Y.obj (op m) := by
      rw [Category.assoc, ← comp_whiskerRight, hir, id_whiskerRight, Category.comp_id]
    exact e.trans (by rw [hx', zero_comp]; rfl)
  · rintro m K (y : compactObj T K.unop ⟶ N ⊗ Y.obj (op m)) hy
    have hy' : y ≫ (𝟙 N - r ≫ i) ▷ Y.obj (op m) = 0 := hy
    have e : (𝟙 N - r ≫ i) ▷ Y.obj (op m) = 𝟙 _ - (r ≫ i) ▷ Y.obj (op m) := by
      rw [← id_whiskerRight]
      exact (tensorRight (Y.obj (op m))).map_sub
    rw [e, Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at hy'
    refine ⟨y ≫ r ▷ Y.obj (op m), ?_⟩
    change (y ≫ r ▷ Y.obj (op m)) ≫ i ▷ Y.obj (op m) = y
    rw [Category.assoc, ← comp_whiskerRight, ← hy']

/-- Extensions: for a distinguished triangle `M' → M → M'' → ΣM'`, the five-term sequence
`h(Σ⁻¹M'' ⊗ Y) → h(M' ⊗ Y) → h(M ⊗ Y) → h(M'' ⊗ Y) → h(ΣM' ⊗ Y)` is exact levelwise, so
`h(M ⊗ Y)` is pro-constant if the other four are (Lemma 3.1). -/
lemma isProConstant_hTower_of_distTriang (Tr : Triangle T) (hT : Tr ∈ distTriang T)
    (h₁ : IsProConstant (hTower Y (Tr.obj₃⟦(-1 : ℤ)⟧))) (h₂ : IsProConstant (hTower Y Tr.obj₁))
    (h₃ : IsProConstant (hTower Y Tr.obj₃)) (h₄ : IsProConstant (hTower Y (Tr.obj₁⟦(1 : ℤ)⟧))) :
    IsProConstant (hTower Y Tr.obj₂) := by
  have hT' := inv_rot_of_distTriang _ hT
  have hT'' := rot_of_distTriang _ hT
  let first : Tr.obj₃⟦(-1 : ℤ)⟧ ⟶ Tr.obj₁ := Tr.invRotate.mor₁
  refine isProConstant_of_levelwiseExactFive (α := hTowerMap Y first)
    (β := hTowerMap Y Tr.mor₁) (γ := hTowerMap Y Tr.mor₂) (ε := hTowerMap Y Tr.mor₃)
    (fun K => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩) h₁ h₂ h₃ h₄
  · rintro m (x : compactObj T K.unop ⟶ Tr.obj₃⟦(-1 : ℤ)⟧ ⊗ Y.obj (op m))
    change (x ≫ first ▷ Y.obj (op m)) ≫ Tr.mor₁ ▷ Y.obj (op m) = 0
    rw [Category.assoc]
    exact (x ≫= whiskerRight_comp_whiskerRight_eq_zero _ hT' (Y.obj (op m))).trans comp_zero
  · rintro m (x : compactObj T K.unop ⟶ Tr.obj₁ ⊗ Y.obj (op m))
    change (x ≫ Tr.mor₁ ▷ Y.obj (op m)) ≫ Tr.mor₂ ▷ Y.obj (op m) = 0
    rw [Category.assoc]
    exact (x ≫= whiskerRight_comp_whiskerRight_eq_zero _ hT (Y.obj (op m))).trans comp_zero
  · rintro m (x : compactObj T K.unop ⟶ Tr.obj₂ ⊗ Y.obj (op m))
    change (x ≫ Tr.mor₂ ▷ Y.obj (op m)) ≫ Tr.mor₃ ▷ Y.obj (op m) = 0
    rw [Category.assoc]
    exact (x ≫= whiskerRight_comp_whiskerRight_eq_zero _ hT'' (Y.obj (op m))).trans comp_zero
  · rintro m (y : compactObj T K.unop ⟶ Tr.obj₁ ⊗ Y.obj (op m)) hy
    obtain ⟨x, hx⟩ := exists_comp_whiskerRight_eq _ hT' (Y.obj (op m)) y hy
    exact ⟨x, hx⟩
  · rintro m (y : compactObj T K.unop ⟶ Tr.obj₂ ⊗ Y.obj (op m)) hy
    obtain ⟨x, hx⟩ := exists_comp_whiskerRight_eq _ hT (Y.obj (op m)) y hy
    exact ⟨x, hx⟩
  · rintro m (y : compactObj T K.unop ⟶ Tr.obj₃ ⊗ Y.obj (op m)) hy
    obtain ⟨x, hx⟩ := exists_comp_whiskerRight_eq _ hT'' (Y.obj (op m)) y hy
    exact ⟨x, hx⟩

variable (Y) in
/-- `J'(M)`: `h(W ⊗ M ⊗ Y)` is pro-constant for every `W` (proof of Prop. 3.5(a)). -/
def tensorProConstIdeal : ObjectProperty T := fun M => ∀ W : T, IsProConstant (hTower Y (W ⊗ M))

lemma tensorProConstIdeal.shift {M : T} (h : tensorProConstIdeal Y M) (n : ℤ) :
    tensorProConstIdeal Y (M⟦n⟧) := fun W =>
  isProConstant_hTower_of_iso (α_ W ((𝟙_ T)⟦n⟧) M ≪≫ whiskerLeftIso W (shiftIsoUnitTensor M n).symm)
    (h (W ⊗ (𝟙_ T)⟦n⟧))

variable (Y) in
/-- `J'` is a thick tensor ideal (proof of Prop. 3.5(a)). -/
lemma isThickTensorIdeal_tensorProConstIdeal : IsThickTensorIdeal (tensorProConstIdeal Y) := by
  refine ⟨{ exists_zero := ?_, isStableUnderShiftBy := ?_, ext₂' := ?_ }, ⟨?_⟩, ?_⟩
  · exact ⟨0, isZero_zero T, fun W =>
      isProConstant_hTower_of_isZero (Functor.map_isZero (tensorLeft W) (isZero_zero T))⟩
  · intro n
    exact ⟨fun M h => h.shift n⟩
  · intro Tr hT h₁ h₃
    refine ObjectProperty.le_isoClosure _ _ fun W => ?_
    have hT' := (tensorLeft W).map_distinguished Tr hT
    refine isProConstant_hTower_of_distTriang _ hT' ?_ (h₁ W) (h₃ W) ?_
    · exact isProConstant_hTower_of_iso (((tensorLeft W).commShiftIso (-1 : ℤ)).app Tr.obj₃)
        ((h₃.shift (-1)) W)
    · exact isProConstant_hTower_of_iso (((tensorLeft W).commShiftIso (1 : ℤ)).app Tr.obj₁)
        ((h₁.shift 1) W)
  · intro M N r h W
    exact isProConstant_hTower_of_retract (W ◁ r.i) (W ◁ r.r)
      (by rw [← MonoidalCategory.whiskerLeft_comp, r.retract, MonoidalCategory.whiskerLeft_id])
      (h W)
  · intro W' M h W
    exact isProConstant_hTower_of_iso (α_ W W' M) (h (W ⊗ W'))

omit [TensorTriangulated T] in
/-- `J'` contains `B` if `B ⊗ Y` is pro-constant: `h(W ⊗ -)` preserves pro-constancy. -/
lemma tensorProConstIdeal_of_isProConstant {B : T} (hY : IsProConstant (Y ⋙ tensorLeft B)) :
    tensorProConstIdeal Y B := fun W =>
  (hY.map (tensorLeft W ⋙ restrictedYoneda T)).of_iso
    (Functor.isoWhiskerLeft Y
      (Functor.isoWhiskerRight (tensorLeftTensor W B).symm (restrictedYoneda T)))

end Towers

/-! ### Proposition 3.5 and Theorem 3.6 -/

section Tails

variable [IsTriangulated T] [CompactlyGenerated T]

variable {Y : ℕᵒᵖ ⥤ T}

omit [MonoidalCategory T] [TensorTriangulated T] in
/-- If `hY` is pro-constant, then `lim¹_m Hom(K, Y_m) = 0` for every compact `K` (Lemma 3.2). -/
lemma limOneVanishes_of_isProConstant (hY : IsProConstant (Y ⋙ restrictedYoneda T)) {K : T}
    (hK : IsCompactObj K) : LimOneVanishes (Y ⋙ preadditiveCoyoneda.obj (op K)) := by
  obtain ⟨i, ⟨e⟩⟩ := exists_iso_compactObj hK
  have h : LimOneVanishes (Y ⋙ preadditiveCoyoneda.obj (op (compactObj T (CompactModel.of i)))) :=
    (hY.map ((evaluation _ AddCommGrpCat.{v}).obj (op (CompactModel.of i)))).limOneVanishes
  exact LimOneVanishes.of_iso h (Functor.isoWhiskerLeft Y (preadditiveCoyoneda.mapIso e.op))

omit [MonoidalCategory T] [TensorTriangulated T] in
/-- Paper, Proposition 3.5(a) (`prop:tails`), second half: if `hY` is pro-constant, then for a
homotopy limit `(L, p)` of `Y` the level map `cst(h L) ⟶ hY` with components `h p_m` is a
pro-isomorphism. -/
theorem isProIso_map_holim_of_isProConstant (hY : IsProConstant (Y ⋙ restrictedYoneda T))
    {L : T} {p : ∀ m, L ⟶ Y.obj (op m)} (hL : IsHolim Y L p) :
    IsProIso (mapLevelMap (Tower.levelMap p hL.comp_p) (restrictedYoneda T)) := by
  obtain ⟨U, u, hu⟩ := hY
  obtain ⟨φ, hφ⟩ := hu.exists_const (mapLevelMap (Tower.levelMap p hL.comp_p) (restrictedYoneda T))
    (𝟙 _)
  have hφ' : ∀ m, (restrictedYoneda T).map (p m) = φ ≫ u.app (op m) := fun m =>
    ((hφ m).trans (Category.comp_id _)).symm
  have key : ∀ (c : (CompactModel T)ᵒᵖ) (m : ℕ) (x : compactObj T c.unop ⟶ L),
      (u.app (op m)).app c (φ.app c x) = x ≫ p m := fun c m x =>
    (ConcreteCategory.congr_hom (NatTrans.congr_app (hφ' m) c) x).symm
  have : IsIso φ := by
    have : ∀ c, IsIso (φ.app c) := fun c => by
      have hc := hu.map ((evaluation _ AddCommGrpCat.{v}).obj c)
      rw [ConcreteCategory.isIso_iff_bijective]
      refine ⟨(injective_iff_map_eq_zero (φ.app c).hom).2 fun x hx => ?_, fun z => ?_⟩
      · refine hL.eq_zero (limOneVanishes_of_isProConstant ⟨U, u, hu⟩
          ((isCompactObj_compactObj c.unop).shift 1)) fun m => ?_
        rw [← key c m x]
        exact (congrArg _ hx).trans (map_zero _)
      · have hcomp := isCompatible_app (mapLevelMap u ((evaluation _ AddCommGrpCat.{v}).obj c)) z
        obtain ⟨y, hy⟩ := hL.exists_lift
          (fun m => ((u.app (op m)).app c z : compactObj T c.unop ⟶ Y.obj (op m))) hcomp
        exact ⟨y, (hc.existsUnique_eq hcomp).unique (fun m => (key c m y).trans (hy m))
          (fun m => rfl)⟩
    exact NatIso.isIso_of_isIso_app φ
  exact hu.of_iso_comp φ _ hφ'

variable [BraidedCategory T] [MonoidalClosed T] {B E : T} {j : 𝟙_ T ⟶ E}

/-- Proof of Proposition 3.5(a): if `j : 𝟙 ⟶ E` is a pure monomorphism with
`E ∈ Thick^⊗(B)` and `B ⊗ Y` is pro-constant, then `hY` is pro-constant: it is the kernel of
`h(g ⊗ Y) : h(E ⊗ Y) ⟶ h(E ⊗ C ⊗ Y)` (Lemma 3.4), and `E, E ⊗ C ∈ J'`. -/
theorem isProConstant_restrictedYoneda_tower (hj : IsPureMono j) (hE : thickTensorIdeal B E)
    (hY : IsProConstant (Y ⋙ tensorLeft B)) : IsProConstant (Y ⋙ restrictedYoneda T) := by
  obtain ⟨C, q, w, hT⟩ := distinguished_cocone_triangle j
  have hJ : tensorProConstIdeal Y E :=
    hE _ (isThickTensorIdeal_tensorProConstIdeal Y) (tensorProConstIdeal_of_isProConstant hY)
  have h₃ : IsProConstant (hTower Y E) := isProConstant_hTower_of_iso (λ_ E) (hJ (𝟙_ T))
  have h₄ : IsProConstant (hTower Y (E ⊗ C)) :=
    isProConstant_hTower_of_iso (λ_ _ ≪≫ β_ C E)
      ((isThickTensorIdeal_tensorProConstIdeal Y).2.2 C E hJ (𝟙_ T))
  refine isProConstant_of_levelwiseKernel (γ := unitTowerMap Y j)
    (ε := hTowerMap Y (q ≫ (λ_ C).inv ≫ j ▷ C)) ?_ ?_ ?_ h₃ h₄
  · rintro m K (x : compactObj T K.unop ⟶ Y.obj (op m))
    change (x ≫ (λ_ _).inv ≫ j ▷ _) ≫ (q ≫ (λ_ C).inv ≫ j ▷ C) ▷ Y.obj (op m) = 0
    rw [Category.assoc, unitWhisker_comp_eq_zero hT, comp_zero]
  · rintro m K (x : compactObj T K.unop ⟶ Y.obj (op m)) hx
    exact isPureMono_unitWhisker hj _ _ (isCompactObj_compactObj K.unop) x hx
  · rintro m K (y : compactObj T K.unop ⟶ E ⊗ Y.obj (op m)) hy
    obtain ⟨x, hx⟩ := exists_comp_unitWhisker_eq hj hT _ (isCompactObj_compactObj K.unop) y hy
    exact ⟨x, hx⟩

/-- Paper, Proposition 3.5(a) (`prop:tails`), for a pure monomorphism `j : 𝟙 ⟶ E` with
`E ∈ Thick^⊗(B)`: if `B ⊗ Y` is pro-constant and `(L, p)` is a homotopy limit of `Y`, the level
map `cst(h L) ⟶ hY` with components `h p_m` is a pro-isomorphism. -/
theorem isProIso_map_holim_of_isPureMono (hj : IsPureMono j) (hE : thickTensorIdeal B E)
    (hY : IsProConstant (Y ⋙ tensorLeft B)) {L : T} {p : ∀ m, L ⟶ Y.obj (op m)}
    (hL : IsHolim Y L p) :
    IsProIso (mapLevelMap (Tower.levelMap p hL.comp_p) (restrictedYoneda T)) :=
  isProIso_map_holim_of_isProConstant (isProConstant_restrictedYoneda_tower hj hE hY) hL

/-- Paper, Proposition 3.5(b) (`prop:tails`), for a pure monomorphism `j : 𝟙 ⟶ E` with
`E ∈ Thick^⊗(B)`, and `W` such that `B ⊗ W ⊗ Y` is pro-constant: a map
`τ : W ⊗ holim Y ⟶ holim (W ⊗ Y)` with `p'_m ∘ τ = W ⊗ p_m` is an isomorphism. -/
theorem isIso_of_isHolim_tensor_of_isPureMono' (hj : IsPureMono j) (hE : thickTensorIdeal B E)
    (hY : IsProConstant (Y ⋙ tensorLeft B)) (W : T)
    (hYW : IsProConstant ((Y ⋙ tensorLeft W) ⋙ tensorLeft B)) {L : T}
    {p : ∀ m, L ⟶ Y.obj (op m)} (hL : IsHolim Y L p) {L' : T}
    {p' : ∀ m, L' ⟶ (Y ⋙ tensorLeft W).obj (op m)} (hL' : IsHolim (Y ⋙ tensorLeft W) L' p')
    (τ : W ⊗ L ⟶ L') (hτ : ∀ m, τ ≫ p' m = W ◁ p m) : IsIso τ := by
  have ha := isProIso_map_holim_of_isPureMono hj hE hY hL
  have hb := isProIso_map_holim_of_isPureMono hj hE hYW hL'
  have hq : ∀ m, (W ◁ p (m + 1)) ≫ Tower.t (Y ⋙ tensorLeft W) (Nat.le_succ m) = W ◁ p m :=
    fun m => by
      change (W ◁ p (m + 1)) ≫ W ◁ Tower.t Y (Nat.le_succ m) = _
      rw [← MonoidalCategory.whiskerLeft_comp, hL.comp_p]
  have hc : IsProIso (mapLevelMap (Tower.levelMap (Y := Y ⋙ tensorLeft W) (fun m => W ◁ p m) hq)
      (restrictedYoneda T)) := by
    refine ha.of_app (tensorLeftAT W) _ ((tensorLeftATIso W).app L).symm
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft Y (tensorLeftATIso W) ≪≫
        (Functor.associator _ _ _).symm) fun m => ?_
    have hn : (tensorLeftAT W).map ((restrictedYoneda T).map (p m)) ≫
        (tensorLeftATIso W).hom.app (Y.obj (op m)) =
          (tensorLeftATIso W).hom.app L ≫ (restrictedYoneda T).map (W ◁ p m) :=
      (tensorLeftATIso W).hom.naturality (p m)
    simp only [Tower.levelMap_app, Iso.symm_hom, Iso.app_inv, Iso.trans_hom,
      NatTrans.comp_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Iso.symm_hom, Functor.associator_inv_app, Category.id_comp,
      Category.comp_id]
    rw [hn, Iso.inv_hom_id_app_assoc]
  have : IsIso ((restrictedYoneda T).map τ) := hc.isIso_of_comp hb _ fun m => by
    change (restrictedYoneda T).map (W ◁ p m) =
      (restrictedYoneda T).map τ ≫ (restrictedYoneda T).map (p' m)
    rw [← Functor.map_comp, hτ]
  exact isIso_of_reflects_iso τ (restrictedYoneda T)

/-- Paper, Proposition 3.5(b) (`prop:tails`), for a pure monomorphism `j : 𝟙 ⟶ E` with
`E ∈ Thick^⊗(B)`: for every `W`, a map `τ : W ⊗ holim Y ⟶ holim (W ⊗ Y)` with
`p'_m ∘ τ = W ⊗ p_m` is an isomorphism. -/
theorem isIso_of_isHolim_tensor_of_isPureMono (hj : IsPureMono j) (hE : thickTensorIdeal B E)
    (hY : IsProConstant (Y ⋙ tensorLeft B)) (W : T) {L : T}
    {p : ∀ m, L ⟶ Y.obj (op m)} (hL : IsHolim Y L p) {L' : T}
    {p' : ∀ m, L' ⟶ (Y ⋙ tensorLeft W).obj (op m)} (hL' : IsHolim (Y ⋙ tensorLeft W) L' p')
    (τ : W ⊗ L ⟶ L') (hτ : ∀ m, τ ≫ p' m = W ◁ p m) : IsIso τ := by
  refine isIso_of_isHolim_tensor_of_isPureMono' hj hE hY W ((hY.map (tensorLeft W)).of_iso ?_)
    hL hL' τ hτ
  refine NatIso.ofComponents (fun m => (α_ W B (Y.obj m)).symm ≪≫
    whiskerRightIso (β_ W B) (Y.obj m) ≪≫ α_ B W (Y.obj m)) fun {m m'} a => ?_
  simp only [Functor.comp_map, curriedTensor_obj_map, Iso.trans_hom, Iso.symm_hom,
    whiskerRightIso_hom]
  rw [associator_inv_naturality_right_assoc, whisker_exchange_assoc,
    associator_naturality_right]
  simp only [Category.assoc]

/-- Paper, Theorem 3.6 (`thm:effective`), for a pure monomorphism `j : 𝟙 ⟶ E` with
`E ∈ Thick^⊗(B)` (the proof uses nothing else about `B`). -/
theorem isEffectiveDescentType_of_isPureMono (hj : IsPureMono j) (hE : thickTensorIdeal B E) :
    IsEffectiveDescentType B := by
  refine (isEffectiveDescentType_iff_isIso B).2 ⟨fun X hX => ?_,
    fun Y hY L p hL L' p' hL' τ hτ => ?_⟩
  · have hEX : IsZero (E ⊗ X) :=
      hE (fun M => IsZero (M ⊗ X)) (isThickTensorIdeal_isZero_tensor X) hX
    obtain ⟨ι, G, hG, hgen⟩ := CompactlyGenerated.exists_generators (T := T)
    exact hgen X fun i n f =>
      isPureMono_unitWhisker hj X _ ((hG i).shift n) f (hEX.eq_of_tgt _ _)
  · exact isIso_of_isHolim_tensor_of_isPureMono' hj hE hY B (hY.map (tensorLeft B)) hL hL' τ hτ

variable {I : T} {η : 𝟙_ T ⟶ B} {δ : I ⟶ 𝟙_ T} {ε : B ⟶ I⟦(1 : ℤ)⟧}

/-- Paper, Proposition 3.5(a) (`prop:tails`): let `B` be nil-pure and `Y` a tower with `B ⊗ Y`
pro-constant. For a homotopy limit `(L, p)` of `Y`, the level map `cst(h L) ⟶ hY` with
components `h p_m` is a pro-isomorphism. -/
theorem IsNilPure.isProIso_map_holim (hT : Triangle.mk δ η ε ∈ distTriang T)
    (hB : IsNilPure δ) (hY : IsProConstant (Y ⋙ tensorLeft B)) {L : T}
    {p : ∀ m, L ⟶ Y.obj (op m)} (hL : IsHolim Y L p) :
    IsProIso (mapLevelMap (Tower.levelMap p hL.comp_p) (restrictedYoneda T)) := by
  obtain ⟨E, j, hj, hE⟩ := hB.exists_isPureMono hT
  exact isProIso_map_holim_of_isPureMono hj hE hY hL

/-- Paper, Proposition 3.5(b) (`prop:tails`): let `B` be nil-pure and `Y` a tower with `B ⊗ Y`
pro-constant. For every `W`, a map `τ : W ⊗ holim Y ⟶ holim (W ⊗ Y)` with
`p'_m ∘ τ = W ⊗ p_m` is an isomorphism. -/
theorem IsNilPure.isIso_of_isHolim_tensor (hT : Triangle.mk δ η ε ∈ distTriang T)
    (hB : IsNilPure δ) (hY : IsProConstant (Y ⋙ tensorLeft B)) (W : T)
    {L : T} {p : ∀ m, L ⟶ Y.obj (op m)} (hL : IsHolim Y L p) {L' : T}
    {p' : ∀ m, L' ⟶ (Y ⋙ tensorLeft W).obj (op m)} (hL' : IsHolim (Y ⋙ tensorLeft W) L' p')
    (τ : W ⊗ L ⟶ L') (hτ : ∀ m, τ ≫ p' m = W ◁ p m) : IsIso τ := by
  obtain ⟨E, j, hj, hE⟩ := hB.exists_isPureMono hT
  exact isIso_of_isHolim_tensor_of_isPureMono hj hE hY W hL hL' τ hτ

/-- Paper, Theorem 3.6 (`thm:effective`): a nil-pure `B` is of effective descent type. (Only
"(3) ⇒ (4)" of Lemma 2.7 is used, so this holds for any map `η`, as Remark 4.3 notes.) -/
theorem IsNilPure.isEffectiveDescentType (hT : Triangle.mk δ η ε ∈ distTriang T)
    (hB : IsNilPure δ) : IsEffectiveDescentType B := by
  obtain ⟨E, j, hj, hE⟩ := hB.exists_isPureMono hT
  exact isEffectiveDescentType_of_isPureMono hj hE

end Tails

end RigidDescent
