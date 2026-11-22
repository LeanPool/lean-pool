/-
Copyright (c) 2026 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
module

public import LeanPool.RigidDescent.Foundations.CompactsThick
public import LeanPool.RigidDescent.Foundations.Extension
public import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!
# The colimit formula

Let `H : T ⥤ AddCommGrpCat` be additive, homological and spanned by summands (for instance,
preserving coproducts). Then `H(W) = colim_{(L, l : L → W)} H(L)`, the colimit over maps into
`W` from the objects `L` of the small model of the compact objects. This is the input for
[BKS20, Prop. A.14] (via [Kra00, Cor. 2.4]), which the paper uses for Lemma 2.3 and
Prop. 3.5; the formula is `Foundations/TensorYoneda.lean`'s route to it.

* `colimFun H`: `W ↦ colim_{(L, l)} H(L)`, the pointwise left Kan extension of `H` restricted to
  the small model `compactIncl T : CompactModel T ⥤ T`, and `colimFunπ H : colimFun H ⟶ H`.
* The index categories `CostructuredArrow (compactIncl T) W` are filtered: sums give upper
  bounds, and `g, g'` are equalized by the map to the cone of `g - g'`.
* `colimFun H` is additive, spanned by summands, and homological: if `(L, l, a)` dies in
  `Φ(W₃)`, there is `γ : L → L''` over `W₃` with `H(γ)(a) = 0`; with `e : L₀ → L` the fiber of
  `γ`, `a = H(e)(a₀)`, and `l ∘ e` dies in `W₃`, so it lifts to `l₀ : L₀ → W₁`; then
  `(L₀, l₀, a₀)` is a preimage.
* `isIso_colimFunπ_app`: `colimFunπ H` is an isomorphism. It is one at compact objects, so
  everywhere by `NatTrans.isIso_app_of_homological`.
* `exists_compactObj_map_eq` and `exists_compactObj_factor_of_map_eq_zero`: the formula
  elementwise. Every `x ∈ H(W)` is `H(l)(y)` for some `l : L → W` with `L` compact; if
  `H(l)(y) = 0` for compact `L`, then `l` factors as `L →g L' → W` with `L'` compact and
  `H(g)(y) = 0`.
-/

@[expose] public section

open CategoryTheory Limits Opposite Pretriangulated
open scoped ZeroObject

universe v u

namespace RigidDescent

section

variable {T : Type u} [Category.{v} T]

lemma functor_map_map_apply (H : T ⥤ AddCommGrpCat.{v}) {X Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : H.obj X) : H.map g (H.map f x) = H.map (f ≫ g) x := by
  rw [H.map_comp, ConcreteCategory.comp_apply]

lemma functor_map_add_apply [Preadditive T] (H : T ⥤ AddCommGrpCat.{v}) [H.Additive]
    {X Y : T} (f g : X ⟶ Y) (x : H.obj X) : H.map (f + g) x = H.map f x + H.map g x := by
  rw [H.map_add]
  rfl

end

variable {T : Type u} [Category.{v} T] [Preadditive T] [HasZeroObject T] [HasShift T ℤ]
  [∀ n : ℤ, (shiftFunctor T n).Additive] [Pretriangulated T] [IsTriangulated T]
  [CompactlyGenerated T]

variable (T) in
/-- The small model of the compact objects, as a category: objects `CompactIndex T`, maps
`compactObj T i ⟶ compactObj T j`. -/
noncomputable abbrev CompactModel : Type v := InducedCategory T (compactObj T)

/-- An index of the small model, as an object of `CompactModel T`. -/
noncomputable abbrev CompactModel.of (i : CompactIndex T) : CompactModel T := i

variable (T) in
/-- The inclusion of the small model of the compact objects. -/
noncomputable abbrev compactIncl : CompactModel T ⥤ T := inducedFunctor (compactObj T)

namespace ColimitFormula

/-- The index category of the colimit formula at `W` is filtered. -/
instance isFiltered (W : T) : IsFiltered (CostructuredArrow (compactIncl T) W) := by
  have : Nonempty (CostructuredArrow (compactIncl T) W) := by
    obtain ⟨i, -⟩ := exists_iso_compactObj (isCompactObj_of_isZero (isZero_zero T))
    exact ⟨CostructuredArrow.mk (Y := CompactModel.of i) (0 : compactObj T i ⟶ W)⟩
  refine { cocone_objs := fun X Y => ?_, cocone_maps := fun X Y f g => ?_ }
  · obtain ⟨k, ⟨e⟩⟩ := exists_iso_compactObj
      ((isCompactObj_compactObj X.left).biprod (isCompactObj_compactObj Y.left))
    let Z : CostructuredArrow (compactIncl T) W :=
      CostructuredArrow.mk (Y := CompactModel.of k) (e.inv ≫ biprod.desc X.hom Y.hom)
    exact ⟨Z, CostructuredArrow.homMk (InducedCategory.homMk (biprod.inl ≫ e.hom))
      (by simp [Z]), CostructuredArrow.homMk (InducedCategory.homMk (biprod.inr ≫ e.hom))
      (by simp [Z]), trivial⟩
  · have hd : (f.left.hom - g.left.hom) ≫ Y.hom = 0 := by
      rw [Preadditive.sub_comp, sub_eq_zero]
      exact (CostructuredArrow.w f).trans (CostructuredArrow.w g).symm
    obtain ⟨Z, c, δ, hT⟩ := distinguished_cocone_triangle (f.left.hom - g.left.hom)
    have hdc : (f.left.hom - g.left.hom) ≫ c = 0 := comp_distTriang_mor_zero₁₂ _ hT
    obtain ⟨b, hb⟩ := Triangle.yoneda_exact₂ _ hT Y.hom hd
    have hZ : IsCompactObj Z := isCompactObj₃_of_distTriang _ hT
      (isCompactObj_compactObj Y.left) ((isCompactObj_compactObj X.left).shift 1)
    obtain ⟨k, ⟨e⟩⟩ := exists_iso_compactObj hZ
    let Z' : CostructuredArrow (compactIncl T) W :=
      CostructuredArrow.mk (Y := CompactModel.of k) (e.inv ≫ b)
    refine ⟨Z', CostructuredArrow.homMk (InducedCategory.homMk (c ≫ e.hom)) ?_, ?_⟩
    · change (c ≫ e.hom) ≫ e.inv ≫ b = Y.hom
      simpa using hb.symm
    · refine CostructuredArrow.hom_ext _ _ (InducedCategory.hom_ext ?_)
      change f.left.hom ≫ c ≫ e.hom = g.left.hom ≫ c ≫ e.hom
      rw [← sub_eq_zero, ← Preadditive.sub_comp, ← Category.assoc, hdc, zero_comp]

end ColimitFormula

variable (H : T ⥤ AddCommGrpCat.{v})

/-- `W ↦ colim_{(L, l : L → W)} H(L)`, the colimit over maps into `W` from objects of the small
model of the compact objects. -/
noncomputable abbrev colimFun : T ⥤ AddCommGrpCat.{v} :=
  (compactIncl T).pointwiseLeftKanExtension (compactIncl T ⋙ H)

/-- The comparison map `colim_{(L, l : L → W)} H(L) ⟶ H(W)`, induced by the maps `H(l)`. -/
noncomputable def colimFunπ : colimFun H ⟶ H :=
  (colimFun H).descOfIsLeftKanExtension
    ((compactIncl T).pointwiseLeftKanExtensionUnit (compactIncl T ⋙ H)) H (𝟙 _)

namespace ColimitFormula

/-- The class in `colim_{(L, l)} H(L)` of an element of `H(L)`, for `l : L → W`. -/
noncomputable def cl {W : T} (i : CompactIndex T) (l : compactObj T i ⟶ W) :
    H.obj (compactObj T i) ⟶ (colimFun H).obj W :=
  colimit.ι (CostructuredArrow.proj (compactIncl T) W ⋙ compactIncl T ⋙ H)
    (CostructuredArrow.mk (Y := CompactModel.of i) l)

variable {H}

lemma cl_comp {W : T} {i i' : CompactIndex T} (g : compactObj T i ⟶ compactObj T i')
    (l : compactObj T i' ⟶ W) (a : H.obj (compactObj T i)) :
    cl H i (g ≫ l) a = cl H i' l (H.map g a) := by
  have h := ConcreteCategory.congr_hom
    (colimit.w (CostructuredArrow.proj (compactIncl T) W ⋙ compactIncl T ⋙ H)
      (CostructuredArrow.homMk' (CostructuredArrow.mk (Y := CompactModel.of i') l)
        (InducedCategory.homMk (X := CompactModel.of i) g))) a
  rw [ConcreteCategory.comp_apply] at h
  exact h.symm

lemma colimFunπ_cl {W : T} (i : CompactIndex T) (l : compactObj T i ⟶ W)
    (a : H.obj (compactObj T i)) : (colimFunπ H).app W (cl H i l a) = H.map l a := by
  rw [colimFunπ, Functor.pointwiseLeftKanExtension_desc_app]
  exact (colimit.ι_desc_apply
    ((compactIncl T).costructuredArrowMapCocone (compactIncl T ⋙ H) H (𝟙 _) W)
    (CostructuredArrow.mk (Y := CompactModel.of i) l) a).trans (by simp; rfl)

lemma map_cl {W W' : T} (f : W ⟶ W') (i : CompactIndex T) (l : compactObj T i ⟶ W)
    (a : H.obj (compactObj T i)) : (colimFun H).map f (cl H i l a) = cl H i (l ≫ f) a := by
  rw [Functor.pointwiseLeftKanExtension_map]
  exact colimit.ι_desc_apply (F := CostructuredArrow.proj (compactIncl T) W ⋙ compactIncl T ⋙ H)
    _ (CostructuredArrow.mk (Y := CompactModel.of i) l) a

lemma exists_cl {W : T} (x : (colimFun H).obj W) :
    ∃ (i : CompactIndex T) (l : compactObj T i ⟶ W) (a : H.obj (compactObj T i)),
      cl H i l a = x := by
  obtain ⟨j, a, h⟩ := Concrete.colimit_exists_rep
    (CostructuredArrow.proj (compactIncl T) W ⋙ compactIncl T ⋙ H) x
  exact ⟨j.left, j.hom, a, h⟩

lemma cl_eq_zero_iff {W : T} (i : CompactIndex T) (l : compactObj T i ⟶ W)
    (a : H.obj (compactObj T i)) :
    cl H i l a = 0 ↔ ∃ (i' : CompactIndex T) (g : compactObj T i ⟶ compactObj T i')
      (l' : compactObj T i' ⟶ W), g ≫ l' = l ∧ H.map g a = 0 := by
  constructor
  · intro h
    have h' : colimit.ι (CostructuredArrow.proj (compactIncl T) W ⋙ compactIncl T ⋙ H)
        (CostructuredArrow.mk (Y := CompactModel.of i) l) a =
        colimit.ι (CostructuredArrow.proj (compactIncl T) W ⋙ compactIncl T ⋙ H)
          (CostructuredArrow.mk (Y := CompactModel.of i) l) 0 :=
      h.trans (map_zero _).symm
    obtain ⟨k, f, f', hf⟩ := Concrete.colimit_exists_of_rep_eq _ _ _ h'
    refine ⟨k.left, f.left.hom, k.hom, CostructuredArrow.w f, ?_⟩
    rw [map_zero] at hf
    exact hf
  · rintro ⟨i', g, l', rfl, h⟩
    rw [cl_comp, h, map_zero]

lemma isHomological_colimFun (hH : IsHomological H) : IsHomological (colimFun H) := by
  intro Tr hTr y hy
  obtain ⟨i, l, a, rfl⟩ := exists_cl y
  rw [map_cl, cl_eq_zero_iff] at hy
  obtain ⟨i', γ, l'', hγ, ha⟩ := hy
  obtain ⟨Z, c, δ, hZ⟩ := distinguished_cocone_triangle γ
  let Tr' := (Triangle.mk γ c δ).invRotate
  have hTr' : Tr' ∈ distTriang T := inv_rot_of_distTriang _ hZ
  obtain ⟨a₀, ha₀⟩ := hH Tr' hTr' a ha
  let first : Tr'.obj₁ ⟶ compactObj T i := Tr'.mor₁
  have h0 : (first ≫ l) ≫ Tr.mor₂ = 0 := by
    have : first ≫ γ = 0 := comp_distTriang_mor_zero₁₂ _ hTr'
    rw [Category.assoc, ← hγ, ← Category.assoc, this, zero_comp]
  obtain ⟨l₀, hl₀⟩ := Triangle.coyoneda_exact₂ Tr hTr _ h0
  have hL₀ : IsCompactObj Tr'.obj₁ := isCompactObj₁_of_distTriang _ hTr'
    (isCompactObj_compactObj i) (isCompactObj_compactObj i')
  obtain ⟨k, ⟨e⟩⟩ := exists_iso_compactObj hL₀
  refine ⟨cl H k (e.inv ≫ l₀) (H.map e.hom a₀), ?_⟩
  rw [map_cl, Category.assoc, ← hl₀, ← Category.assoc, cl_comp, functor_map_map_apply,
    ← Category.assoc, e.hom_inv_id, Category.id_comp]
  exact congrArg _ ha₀

/-- At a compact object the comparison map is an isomorphism. -/
lemma isIso_colimFunπ_app_of_isCompactObj {W : T} (hW : IsCompactObj W) :
    IsIso ((colimFunπ H).app W) := by
  obtain ⟨k, ⟨e⟩⟩ := exists_iso_compactObj hW
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(injective_iff_map_eq_zero (ConcreteCategory.hom ((colimFunπ H).app W))).2
    fun x hx => ?_, fun y => ⟨cl H k e.inv (H.map e.hom y), ?_⟩⟩
  · obtain ⟨i, l, a, rfl⟩ := exists_cl x
    change (colimFunπ H).app W (cl H i l a) = 0 at hx
    rw [colimFunπ_cl] at hx
    rw [cl_eq_zero_iff]
    refine ⟨k, l ≫ e.hom, e.inv, by simp, ?_⟩
    rw [← functor_map_map_apply, hx, map_zero]
  · change (colimFunπ H).app W (cl H k e.inv (H.map e.hom y)) = y
    rw [colimFunπ_cl, functor_map_map_apply, e.hom_inv_id, H.map_id]
    rfl

variable [H.Additive]

lemma cl_add {W : T} (i : CompactIndex T) (l l' : compactObj T i ⟶ W)
    (a : H.obj (compactObj T i)) : cl H i (l + l') a = cl H i l a + cl H i l' a := by
  obtain ⟨k, ⟨e⟩⟩ := exists_iso_compactObj
    ((isCompactObj_compactObj i).biprod (isCompactObj_compactObj i))
  let m : compactObj T k ⟶ W := e.inv ≫ biprod.desc l l'
  have h₁ : l = (biprod.inl ≫ e.hom) ≫ m := by simp [m]
  have h₂ : l' = (biprod.inr ≫ e.hom) ≫ m := by simp [m]
  have h₃ : l + l' = (biprod.lift (𝟙 _) (𝟙 _) ≫ e.hom) ≫ m := by simp [m]
  have hΔ : biprod.lift (𝟙 _) (𝟙 _) ≫ e.hom = biprod.inl ≫ e.hom + biprod.inr ≫ e.hom := by
    rw [biprod.lift_eq, ← Preadditive.add_comp]
    simp
  calc cl H i (l + l') a = cl H i ((biprod.lift (𝟙 _) (𝟙 _) ≫ e.hom) ≫ m) a := by rw [← h₃]
    _ = cl H k m (H.map (biprod.inl ≫ e.hom) a) + cl H k m (H.map (biprod.inr ≫ e.hom) a) := by
      rw [cl_comp, hΔ, functor_map_add_apply, map_add]
    _ = cl H i l a + cl H i l' a := by rw [← cl_comp, ← cl_comp, ← h₁, ← h₂]

lemma cl_zero {W : T} (i : CompactIndex T) (a : H.obj (compactObj T i)) :
    cl H i (0 : compactObj T i ⟶ W) a = 0 := by
  have h := cl_add i (0 : compactObj T i ⟶ W) 0 a
  rw [add_zero] at h
  exact add_eq_left.1 h.symm

/-- `l ↦ cl H i l a` is additive. -/
noncomputable def clHom (W : T) (i : CompactIndex T) (a : H.obj (compactObj T i)) :
    (compactObj T i ⟶ W) →+ (colimFun H).obj W :=
  AddMonoidHom.mk' (fun l => cl H i l a) fun l l' => cl_add i l l' a

lemma cl_sum {W : T} (i : CompactIndex T) {J : Type*} (S : Finset J)
    (l : J → (compactObj T i ⟶ W)) (a : H.obj (compactObj T i)) :
    cl H i (∑ j ∈ S, l j) a = ∑ j ∈ S, cl H i (l j) a :=
  map_sum (clHom W i a) l S

instance additive_colimFun : (colimFun H).Additive where
  map_add {X Y f g} := by
    ext x
    obtain ⟨i, l, a, rfl⟩ := exists_cl x
    change (colimFun H).map (f + g) (cl H i l a) =
      (colimFun H).map f (cl H i l a) + (colimFun H).map g (cl H i l a)
    rw [map_cl, map_cl, map_cl, Preadditive.comp_add, cl_add]

lemma spannedBySummands_colimFun : SpannedBySummands (colimFun H) := by
  intro J Y x
  obtain ⟨i, l, a, rfl⟩ := exists_cl x
  obtain ⟨S, p, hp⟩ := (isCompactObj_compactObj i).isFiniteSum l
  refine ⟨S, fun j => cl H i (p j) a, ?_⟩
  rw [hp, cl_sum]
  exact Finset.sum_congr rfl fun j _ => (map_cl _ _ _ _).symm

/-- The comparison map `colim_{(L, l : L → W)} H(L) ⟶ H(W)` is an isomorphism, for `H`
additive, homological and spanned by summands. -/
theorem isIso_colimFunπ_app (hH : IsHomological H) (hHc : SpannedBySummands H) (W : T) :
    IsIso ((colimFunπ H).app W) :=
  NatTrans.isIso_app_of_homological (isHomological_colimFun hH) hH
    spannedBySummands_colimFun hHc (colimFunπ H)
    (fun i n => isIso_colimFunπ_app_of_isCompactObj
      ((CompactlyGenerated.isCompactObj_gen i).shift n)) W

end ColimitFormula

open ColimitFormula

variable {H} [H.Additive]

/-- The colimit formula, surjectivity: for `H` additive, homological and spanned by summands,
every element of `H(W)` is `H(l)(y)` for some map `l : L → W` from a compact object `L` of the
small model. -/
theorem exists_compactObj_map_eq (hH : IsHomological H) (hHc : SpannedBySummands H) {W : T}
    (x : H.obj W) : ∃ (i : CompactIndex T) (l : compactObj T i ⟶ W)
      (y : H.obj (compactObj T i)), H.map l y = x := by
  have := isIso_colimFunπ_app hH hHc W
  obtain ⟨x', rfl⟩ := ((ConcreteCategory.isIso_iff_bijective _).1 this).2 x
  obtain ⟨i, l, y, rfl⟩ := exists_cl x'
  exact ⟨i, l, y, (colimFunπ_cl i l y).symm⟩

/-- The colimit formula, injectivity: for `H` additive, homological and spanned by summands, if
`H(l)(y) = 0` for a map `l : K → W` from a compact object `K`, then `l` factors as
`K →g L → W` with `L` a compact object of the small model and `H(g)(y) = 0`. -/
theorem exists_compactObj_factor_of_map_eq_zero (hH : IsHomological H)
    (hHc : SpannedBySummands H) {K W : T} (hK : IsCompactObj K) (l : K ⟶ W) (y : H.obj K)
    (hy : H.map l y = 0) : ∃ (i : CompactIndex T) (g : K ⟶ compactObj T i)
      (l' : compactObj T i ⟶ W), g ≫ l' = l ∧ H.map g y = 0 := by
  obtain ⟨k, ⟨e⟩⟩ := exists_iso_compactObj hK
  have := isIso_colimFunπ_app hH hHc W
  have hinj := ((ConcreteCategory.isIso_iff_bijective _).1 this).1
  have h0 : cl H k (e.inv ≫ l) (H.map e.hom y) = 0 := by
    apply (injective_iff_map_eq_zero (ConcreteCategory.hom ((colimFunπ H).app W))).1 hinj
    change (colimFunπ H).app W (cl H k (e.inv ≫ l) (H.map e.hom y)) = 0
    rw [colimFunπ_cl, functor_map_map_apply, ← Category.assoc, e.hom_inv_id, Category.id_comp,
      hy]
  obtain ⟨i, g, l', hgl, hg⟩ := (cl_eq_zero_iff _ _ _).1 h0
  refine ⟨i, e.hom ≫ g, l', ?_, ?_⟩
  · rw [Category.assoc, hgl, ← Category.assoc, e.hom_inv_id, Category.id_comp]
  · rw [← functor_map_map_apply]
    exact hg

end RigidDescent
