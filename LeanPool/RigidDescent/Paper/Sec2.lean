/-
Copyright (c) 2026 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
module

public import LeanPool.RigidDescent.Foundations.TensorYoneda
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import LeanPool.RigidDescent.Defs.Purity
public import Mathlib.CategoryTheory.Abelian.FunctorCategory

/-!
# Paper, §2: purity and phantom maps

* Basic facts: phantom maps form an ideal, and phantom maps and pure monomorphisms are stable
  under shifts (`IsPhantom.shift`, `IsPureMono.shift`).
* Lemma 2.2 (`lem:AT`): restricted Yoneda `h` is homological (`isHomological_restrictedYoneda`)
  and reflects isomorphisms (`reflectsIsomorphisms_restrictedYoneda`); `f` is phantom iff
  `h f = 0` (`restrictedYoneda_map_eq_zero_iff`), a pure monomorphism iff `h f` is a
  monomorphism (`mono_restrictedYoneda_map_iff`); for a distinguished triangle, the three
  conditions of the lemma are equivalent (`pureTriangle_tfae`).
* Lemma 2.3 (`lem:ideal`): `IsPhantom.whiskerLeft`, `IsPhantom.whiskerRight`,
  `IsPureMono.whiskerLeft`, `IsPureMono.whiskerRight`.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated ZeroObject

universe v u

namespace RigidDescent

variable {T : Type u} [Category.{v} T] [Preadditive T]

/-! ### Phantom maps form an ideal -/

section Ideal

lemma isPhantom_zero (X Y : T) : IsPhantom (0 : X ⟶ Y) :=
  fun _ _ _ => comp_zero

lemma IsPhantom.comp {X Y : T} {f : X ⟶ Y} (hf : IsPhantom f) {Z : T} (g : Y ⟶ Z) :
    IsPhantom (f ≫ g) :=
  fun K hK k => by rw [← Category.assoc, hf K hK k, zero_comp]

lemma IsPhantom.precomp {X Y : T} {f : X ⟶ Y} (hf : IsPhantom f) {W : T} (g : W ⟶ X) :
    IsPhantom (g ≫ f) :=
  fun K hK k => by rw [← Category.assoc, hf K hK (k ≫ g)]

lemma IsPhantom.neg {X Y : T} {f : X ⟶ Y} (hf : IsPhantom f) : IsPhantom (-f) :=
  fun K hK k => by rw [Preadditive.comp_neg, hf K hK k, neg_zero]

lemma IsPhantom.of_iso {X Y X' Y' : T} {f : X ⟶ Y} (hf : IsPhantom f) (e₁ : X' ≅ X)
    (e₂ : Y ≅ Y') : IsPhantom (e₁.hom ≫ f ≫ e₂.hom) :=
  (hf.comp _).precomp _

end Ideal

/-! ### Shifts -/

section Shift

variable [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive]

omit [Preadditive T] [∀ n : ℤ, (shiftFunctor T n).Additive] in
/-- Shifting back by `-n`: `(k ≫ f⟦n⟧)⟦-n⟧` is `k⟦-n⟧ ≫ f` up to the canonical isomorphisms. -/
lemma shift_neg_comp {K X Y : T} (n : ℤ) (k : K ⟶ X⟦n⟧) (f : X ⟶ Y) :
    (k ≫ f⟦n⟧')⟦-n⟧' ≫ (shiftFunctorCompIsoId T n (-n) (add_neg_cancel n)).hom.app Y =
      (k⟦-n⟧' ≫ (shiftFunctorCompIsoId T n (-n) (add_neg_cancel n)).hom.app X) ≫ f := by
  rw [Functor.map_comp, Category.assoc, Category.assoc]
  congr 1
  exact (shiftFunctorCompIsoId T n (-n) (add_neg_cancel n)).hom.naturality f

variable [HasCoproducts.{v} T]

lemma IsPhantom.shift {X Y : T} {f : X ⟶ Y} (hf : IsPhantom f) (n : ℤ) :
    IsPhantom (f⟦n⟧') := by
  intro K hK k
  have h := shift_neg_comp n k f
  rw [hf _ (hK.shift (-n))] at h
  have h' : (k ≫ f⟦n⟧')⟦-n⟧' = 0 :=
    (cancel_mono ((shiftFunctorCompIsoId T n (-n) (add_neg_cancel n)).hom.app Y)).1
      (h.trans zero_comp.symm)
  exact (Functor.map_eq_zero_iff (shiftFunctor T (-n))).1 h'

lemma isPhantom_shift_iff {X Y : T} (f : X ⟶ Y) (n : ℤ) : IsPhantom (f⟦n⟧') ↔ IsPhantom f := by
  refine ⟨fun hf => ?_, fun hf => hf.shift n⟩
  have e := (shiftFunctorCompIsoId T n (-n) (add_neg_cancel n)).hom.naturality f
  have hf' : f = (shiftFunctorCompIsoId T n (-n) (add_neg_cancel n)).inv.app X ≫
      (f⟦n⟧')⟦-n⟧' ≫ (shiftFunctorCompIsoId T n (-n) (add_neg_cancel n)).hom.app Y := by
    have e' : (f⟦n⟧')⟦-n⟧' ≫ (shiftFunctorCompIsoId T n (-n) (add_neg_cancel n)).hom.app Y =
        (shiftFunctorCompIsoId T n (-n) (add_neg_cancel n)).hom.app X ≫ f := e
    rw [e', Iso.inv_hom_id_app_assoc]
  rw [hf']
  exact ((hf.shift (-n)).comp _).precomp _

lemma IsPureMono.shift {X Y : T} {f : X ⟶ Y} (hf : IsPureMono f) (n : ℤ) :
    IsPureMono (f⟦n⟧') := by
  intro K hK k hk
  have h := shift_neg_comp n k f
  rw [hk, Functor.map_zero, zero_comp] at h
  have h' := hf _ (hK.shift (-n)) _ h.symm
  have h'' : k⟦-n⟧' = 0 :=
    (cancel_mono ((shiftFunctorCompIsoId T n (-n) (add_neg_cancel n)).hom.app X)).1
      (h'.trans zero_comp.symm)
  exact (Functor.map_eq_zero_iff (shiftFunctor T (-n))).1 h''

variable [HasZeroObject T] [Pretriangulated T]

/-- Paper, Lemma 2.2 (`lem:AT`), the part that does not involve `h`: for a distinguished
triangle `X → Y → Z → ΣX`, the first map is a pure monomorphism iff the third is phantom. -/
lemma isPureMono_iff_isPhantom (Tr : Triangle T) (hT : Tr ∈ distTriang T) :
    IsPureMono Tr.mor₁ ↔ IsPhantom Tr.mor₃ := by
  constructor
  · intro hf K hK k
    apply hf.shift 1 K hK
    rw [Category.assoc, comp_distTriang_mor_zero₃₁ _ hT, comp_zero]
  · intro h K hK k hk
    obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₁ _ hT (k⟦(1 : ℤ)⟧')
      (by rw [← Functor.map_comp, hk, Functor.map_zero])
    have h1 : k⟦(1 : ℤ)⟧' = 0 := by rw [hg, h _ (hK.shift 1) g]
    exact (Functor.map_eq_zero_iff (shiftFunctor T (1 : ℤ))).1 h1

end Shift

/-! ### Lemma 2.2: restricted Yoneda -/

section RestrictedYoneda

variable [HasZeroObject T] [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated T] [IsTriangulated T] [CompactlyGenerated T]

/-- A short complex of functors to abelian groups is exact if it is exact at every object. -/
lemma exact_of_forall_exact_evaluation {J : Type*} [Category J]
    (S : ShortComplex (J ⥤ AddCommGrpCat.{v}))
    (h : ∀ j, (S.map ((evaluation J AddCommGrpCat.{v}).obj j)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  refine Functor.isZero _ fun j => ?_
  exact ((ShortComplex.exact_iff_isZero_homology _).1 (h j)).of_iso
    (S.mapHomologyIso ((evaluation J _).obj j)).symm

instance : (restrictedYoneda T).Additive where
  map_add {X Y f g} := by
    ext K a
    exact Preadditive.comp_add _ _ _ _ _ _

/-- Paper, Lemma 2.2 (`lem:AT`): restricted Yoneda `h : T ⥤ A(T)` is homological. -/
instance isHomological_restrictedYoneda : (restrictedYoneda T).IsHomological where
  exact Tr hT := by
    refine exact_of_forall_exact_evaluation _ fun K => ?_
    rw [ShortComplex.ab_exact_iff]
    intro x hx
    obtain ⟨y, hy⟩ := Triangle.coyoneda_exact₂ Tr hT x hx
    exact ⟨y, hy.symm⟩

/-- Paper, Lemma 2.2 (`lem:AT`): `f` is phantom iff `h f = 0`. -/
lemma restrictedYoneda_map_eq_zero_iff {X Y : T} (f : X ⟶ Y) :
    (restrictedYoneda T).map f = 0 ↔ IsPhantom f := by
  constructor
  · intro h K hK k
    obtain ⟨i, ⟨e⟩⟩ := exists_iso_compactObj hK
    have h1 := restrictedYoneda_map_app f (CompactModel.of i) (e.inv ≫ k)
    rw [h] at h1
    have h1 : (e.inv ≫ k) ≫ f = 0 := h1.symm.trans rfl
    rw [← e.hom_inv_id_assoc k, Category.assoc, h1, comp_zero]
  · intro h
    ext K a
    exact h _ (isCompactObj_compactObj K.unop) a

/-- Paper, Lemma 2.2 (`lem:AT`): `f` is a pure monomorphism iff `h f` is a monomorphism. -/
lemma mono_restrictedYoneda_map_iff {X Y : T} (f : X ⟶ Y) :
    Mono ((restrictedYoneda T).map f) ↔ IsPureMono f := by
  rw [NatTrans.mono_iff_mono_app]
  constructor
  · intro h K hK k hk
    obtain ⟨i, ⟨e⟩⟩ := exists_iso_compactObj hK
    have hinj := (AddCommGrpCat.mono_iff_injective _).1 (h (op (CompactModel.of i)))
    have h1 : e.inv ≫ k = 0 := by
      refine (injective_iff_map_eq_zero
        (((restrictedYoneda T).map f).app (op (CompactModel.of i))).hom).1 hinj _ ?_
      change (e.inv ≫ k) ≫ f = 0
      rw [Category.assoc, hk, comp_zero]
    rw [← e.hom_inv_id_assoc k, h1, comp_zero]
  · intro h K
    rw [AddCommGrpCat.mono_iff_injective]
    refine (injective_iff_map_eq_zero (((restrictedYoneda T).map f).app K).hom).2 fun a ha => ?_
    exact h _ (isCompactObj_compactObj K.unop) a ha

/-- `h g` is an epimorphism iff every map from a compact object to the target of `g` lifts. -/
lemma epi_restrictedYoneda_map_iff {Y Z : T} (g : Y ⟶ Z) :
    Epi ((restrictedYoneda T).map g) ↔
      ∀ K : T, IsCompactObj K → ∀ k : K ⟶ Z, ∃ y : K ⟶ Y, y ≫ g = k := by
  rw [NatTrans.epi_iff_epi_app]
  constructor
  · intro h K hK k
    obtain ⟨i, ⟨e⟩⟩ := exists_iso_compactObj hK
    obtain ⟨y, hy⟩ := (AddCommGrpCat.epi_iff_surjective _).1 (h (op (CompactModel.of i)))
      (e.inv ≫ k)
    obtain ⟨y, hy'⟩ : ∃ y' : compactObj T i ⟶ Y, y' ≫ g = e.inv ≫ k := ⟨y, hy⟩
    exact ⟨e.hom ≫ y, by rw [Category.assoc, hy', e.hom_inv_id_assoc]⟩
  · intro h K
    rw [AddCommGrpCat.epi_iff_surjective]
    intro a
    obtain ⟨y, hy⟩ := h _ (isCompactObj_compactObj K.unop) a
    exact ⟨y, hy⟩

/-- Paper, Lemma 2.2 (`lem:AT`): for a distinguished triangle `X →f Y →g Z →∂ ΣX`, the
following are equivalent: `f` is a pure monomorphism; `∂` is phantom;
`0 → hX → hY → hZ → 0` is (short) exact. -/
theorem pureTriangle_tfae (Tr : Triangle T) (hT : Tr ∈ distTriang T) :
    List.TFAE [IsPureMono Tr.mor₁, IsPhantom Tr.mor₃,
      ((shortComplexOfDistTriangle Tr hT).map (restrictedYoneda T)).ShortExact] := by
  tfae_have 1 ↔ 2 := isPureMono_iff_isPhantom Tr hT
  tfae_have 3 → 1 := fun h => (mono_restrictedYoneda_map_iff _).1 h.mono_f
  tfae_have 1 → 3 := fun h => by
    have h2 := (isPureMono_iff_isPhantom Tr hT).1 h
    have : Mono ((shortComplexOfDistTriangle Tr hT).map (restrictedYoneda T)).f :=
      (mono_restrictedYoneda_map_iff _).2 h
    have : Epi ((shortComplexOfDistTriangle Tr hT).map (restrictedYoneda T)).g :=
      (epi_restrictedYoneda_map_iff _).2 fun K hK k => by
        obtain ⟨y, hy⟩ := Triangle.coyoneda_exact₃ _ hT k (h2 K hK k)
        exact ⟨y, hy.symm⟩
    exact ⟨(restrictedYoneda T).map_distinguished_exact Tr hT⟩
  tfae_finish

/-- Paper, Lemma 2.2 (`lem:AT`): restricted Yoneda reflects isomorphisms. -/
instance reflectsIsomorphisms_restrictedYoneda : (restrictedYoneda T).ReflectsIsomorphisms where
  reflects {X Y} f _ := by
    obtain ⟨Z, g, w, hT⟩ := distinguished_cocone_triangle f
    have hmono : IsPureMono f := (mono_restrictedYoneda_map_iff f).1 inferInstance
    have hepi := (epi_restrictedYoneda_map_iff f).1 inferInstance
    have hw : IsPhantom w := (isPureMono_iff_isPhantom _ hT).1 hmono
    have h12 : f ≫ g = 0 := comp_distTriang_mor_zero₁₂ _ hT
    refine (Triangle.isZero₃_iff_isIso₁ _ hT).1 ?_
    obtain ⟨ι, G, hG, hgen⟩ := CompactlyGenerated.exists_generators (T := T)
    refine hgen Z fun i n k => ?_
    obtain ⟨y, hy⟩ := Triangle.coyoneda_exact₃ _ hT k (hw _ ((hG i).shift n) k)
    obtain ⟨x, rfl⟩ := hepi _ ((hG i).shift n) y
    change k = (x ≫ f) ≫ g at hy
    rw [hy, Category.assoc, h12, comp_zero]

end RestrictedYoneda

/-! ### Lemma 2.3: phantom maps form a tensor ideal -/

section TensorIdeal

variable [HasZeroObject T] [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated T] [MonoidalCategory T] [TensorTriangulated T]

/-- In a tensor-triangulated category the tensor product is additive in each variable. -/
instance TensorTriangulated.monoidalPreadditive : MonoidalPreadditive T where
  whiskerLeft_zero {X Y Z} := (tensorLeft X).map_zero Y Z
  zero_whiskerRight {X Y Z} := (tensorRight X).map_zero Y Z
  whiskerLeft_add {X _ _} f g := (tensorLeft X).map_add (f := f) (g := g)
  add_whiskerRight {X _ _} f g := (tensorRight X).map_add (f := f) (g := g)

variable [IsTriangulated T] [CompactlyGenerated T] [MonoidalClosed T]

/-- Paper, Lemma 2.3 (`lem:ideal`): if `φ` is phantom, so is `W ⊗ φ`.

The paper uses that `h` is strong monoidal [BKS20, Prop. A.14]. We use the surjectivity half
of `F_W ∘ h ≅ h ∘ (W ⊗ -)` (`Foundations/TensorYoneda.lean`) in elementwise form: every map
`K → W ⊗ X` from a compact `K` factors as `K → W ⊗ L → W ⊗ X` through `W ⊗ l` for some
`l : L → X` with `L` compact. -/
lemma IsPhantom.whiskerLeft {X Y : T} {φ : X ⟶ Y} (hφ : IsPhantom φ) (W : T) :
    IsPhantom (W ◁ φ) := by
  intro K hK k
  obtain ⟨c, ⟨e⟩⟩ := exists_iso_compactObj hK
  obtain ⟨i, l, x, hx⟩ := exists_compactObj_map_eq
    (isHomological_homTensor W (CompactModel.of c))
    (spannedBySummands_homTensor W (CompactModel.of c)) (W := X) (e.inv ≫ k)
  obtain ⟨x', hx'⟩ : ∃ x' : compactObj T c ⟶ W ⊗ compactObj T i, x' ≫ W ◁ l = e.inv ≫ k :=
    ⟨x, hx⟩
  rw [← e.hom_inv_id_assoc k, ← hx', Category.assoc, Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp, hφ _ (isCompactObj_compactObj i) l,
    MonoidalPreadditive.whiskerLeft_zero, comp_zero, comp_zero]

/-- Paper, Lemma 2.3 (`lem:ideal`), as stated: if `φ` is phantom, so is `φ ⊗ W`. -/
lemma IsPhantom.whiskerRight [BraidedCategory T] {X Y : T} {φ : X ⟶ Y} (hφ : IsPhantom φ)
    (W : T) : IsPhantom (φ ▷ W) := by
  have h : φ ▷ W = (β_ X W).hom ≫ W ◁ φ ≫ (β_ Y W).inv := by
    rw [← BraidedCategory.braiding_naturality_left_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [h]
  exact ((hφ.whiskerLeft W).comp _).precomp _

/-- Paper, Lemma 2.3 (`lem:ideal`): pure monomorphisms, hence pure triangles, are stable under
`W ⊗ -`. -/
lemma IsPureMono.whiskerLeft {X Y : T} {f : X ⟶ Y} (hf : IsPureMono f) (W : T) :
    IsPureMono (W ◁ f) := by
  obtain ⟨Z, g, w, hT⟩ := distinguished_cocone_triangle f
  have hw := (isPureMono_iff_isPhantom _ hT).1 hf
  have hT' := (tensorLeft W).map_distinguished _ hT
  exact (isPureMono_iff_isPhantom _ hT').2 ((hw.whiskerLeft W).comp _)

/-- Paper, Lemma 2.3 (`lem:ideal`): pure monomorphisms are stable under `- ⊗ W`. -/
lemma IsPureMono.whiskerRight [BraidedCategory T] {X Y : T} {f : X ⟶ Y} (hf : IsPureMono f)
    (W : T) : IsPureMono (f ▷ W) := by
  obtain ⟨Z, g, w, hT⟩ := distinguished_cocone_triangle f
  have hw := (isPureMono_iff_isPhantom _ hT).1 hf
  have hT' := (tensorRight W).map_distinguished _ hT
  exact (isPureMono_iff_isPhantom _ hT').2 ((hw.whiskerRight W).comp _)

end TensorIdeal

/-! ### Definition 2.5 and Lemma 2.6: `M`-zero maps -/

section MZeroDef

variable [MonoidalCategory T]

/-- Paper, Definition 2.5 (`def:zero`), after [Mat16, §3.4]: a map `f` is *`M`-zero* if
`M ⊗ f = 0`. -/
def IsTensorZero (M : T) : MorphismProperty T := fun _ _ f => M ◁ f = 0

lemma whiskerLeft_whiskerRight_eq_zero [MonoidalPreadditive T] {M X Y : T} {f : X ⟶ Y}
    (h : M ◁ f = 0) (Z : T) :
    M ◁ f ▷ Z = 0 := by
  rw [← cancel_mono (α_ M Y Z).inv, associator_inv_naturality_middle, h,
    MonoidalPreadditive.zero_whiskerRight, comp_zero, zero_comp]

end MZeroDef

section CompOf

omit [Preadditive T]

/-- `IsCompOf P n f`: `f` is a composite of `n` composable maps with the property `P` (a
composite of no maps is an identity). Used for "every composite of `s` composable `B`-zero
maps" (Lemma 2.6(b)) and "every composite of `s` phantom maps" (Remark 2.8(i)). -/
inductive IsCompOf (P : MorphismProperty T) : ℕ → ∀ {X Y : T}, (X ⟶ Y) → Prop
  | id (X : T) : IsCompOf P 0 (𝟙 X)
  | comp {X Y Z : T} {n : ℕ} {f : X ⟶ Y} {g : Y ⟶ Z} :
      IsCompOf P n f → P g → IsCompOf P (n + 1) (f ≫ g)

namespace IsCompOf

variable {P : MorphismProperty T}

lemma one {X Y : T} {f : X ⟶ Y} (hf : P f) : IsCompOf P 1 f := by
  simpa using IsCompOf.comp (IsCompOf.id X) hf

lemma append {m : ℕ} {X Y : T} {f : X ⟶ Y} (hf : IsCompOf P m f) :
    ∀ {n : ℕ} {Z : T} {g : Y ⟶ Z}, IsCompOf P n g → IsCompOf P (m + n) (f ≫ g)
  | _, _, _, .id _ => by simpa using hf
  | _, _, _, .comp hg hh => by
    rw [← Category.assoc]
    exact IsCompOf.comp (append hf hg) hh

lemma cons {n : ℕ} {X Y Z : T} {f : X ⟶ Y} {g : Y ⟶ Z} (hf : P f) (hg : IsCompOf P n g) :
    IsCompOf P (n + 1) (f ≫ g) := by
  have h := (one hf).append hg
  rwa [Nat.add_comm] at h

lemma split {m : ℕ} : ∀ {n : ℕ} {X Y : T} {f : X ⟶ Y}, IsCompOf P (m + n) f →
    ∃ (Z : T) (g : X ⟶ Z) (h : Z ⟶ Y), IsCompOf P m g ∧ IsCompOf P n h ∧ g ≫ h = f
  | 0, _, Y, f, hf => ⟨Y, f, 𝟙 Y, hf, IsCompOf.id Y, Category.comp_id f⟩
  | _ + 1, _, _, _, hf => by
    cases hf with
    | comp hf hg =>
      obtain ⟨Z, g, h, hg₁, hh, rfl⟩ := split hf
      exact ⟨Z, g, h ≫ _, hg₁, IsCompOf.comp hh hg, (Category.assoc _ _ _).symm⟩

end IsCompOf

end CompOf

section MZeroMonoidal

variable [MonoidalCategory T]

lemma IsTensorZero.of_retract {M M' : T} (i : M' ⟶ M) (r : M ⟶ M') (hir : i ≫ r = 𝟙 M')
    {X Y : T} {f : X ⟶ Y} (h : IsTensorZero M f) : IsTensorZero M' f := by
  have h' : M ◁ f = 0 := h
  change M' ◁ f = 0
  rw [← Category.comp_id (M' ◁ f), ← id_whiskerRight, ← hir, comp_whiskerRight,
    whisker_exchange_assoc, h', zero_comp, comp_zero]

omit [Preadditive T] in
/-- `g ≫ j = (j ⊗ X) ≫ (E ⊗ g)`, up to unitors, for `g : X ⟶ 𝟙` and `j : 𝟙 ⟶ E`. -/
lemma comp_eq_whiskerRight_comp_whiskerLeft {X E : T} (g : X ⟶ 𝟙_ T) (j : 𝟙_ T ⟶ E) :
    g ≫ j = (λ_ X).inv ≫ j ▷ X ≫ E ◁ g ≫ (ρ_ E).hom := by
  rw [← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc, unitors_inv_equal,
    rightUnitor_naturality, Iso.inv_hom_id_assoc]

variable {I : T}

omit [Preadditive T] in
lemma tensorPowHom_succ (δ : I ⟶ 𝟙_ T) (n : ℕ) :
    tensorPowHom δ (n + 1) =
      (δ ▷ tensorPow I n ≫ (λ_ (tensorPow I n)).hom) ≫ tensorPowHom δ n := by
  have h := (δ ▷ tensorPow I n) ≫= leftUnitor_naturality (tensorPowHom δ n)
  rw [← tensorHom_def_assoc] at h
  exact h.trans (Category.assoc _ _ _).symm

omit [Preadditive T] in
lemma tensorPowHom_succ' (δ : I ⟶ 𝟙_ T) (n : ℕ) :
    tensorPowHom δ (n + 1) = (I ◁ tensorPowHom δ n ≫ (ρ_ I).hom) ≫ δ := by
  have h := (I ◁ tensorPowHom δ n) ≫= rightUnitor_naturality δ
  rw [← unitors_equal, ← tensorHom_def'_assoc] at h
  exact h.trans (Category.assoc _ _ _).symm

/-- `I^{⊗ n} ⊗ δ^{⊗ m}`: `δ^{⊗ m}` applied to the innermost `m` factors of `I^{⊗ (m + n)}`. -/
noncomputable def tensorPowHomInner (δ : I ⟶ 𝟙_ T) (m : ℕ) :
    (n : ℕ) → tensorPow I (m + n) ⟶ tensorPow I n
  | 0 => tensorPowHom δ m
  | n + 1 => I ◁ tensorPowHomInner δ m n

omit [Preadditive T] in
lemma tensorPowHom_add (δ : I ⟶ 𝟙_ T) (m n : ℕ) :
    tensorPowHom δ (m + n) = tensorPowHomInner δ m n ≫ tensorPowHom δ n := by
  induction n with
  | zero => exact (Category.comp_id _).symm
  | succ n ih =>
    change tensorPowHom δ ((m + n) + 1) = I ◁ tensorPowHomInner δ m n ≫ tensorPowHom δ (n + 1)
    rw [tensorPowHom_succ' δ (m + n), ih, tensorPowHom_succ' δ n,
      MonoidalCategory.whiskerLeft_comp]
    simp only [Category.assoc]
    rfl

/-- Paper, Definition 2.4 (`def:nilpure`): when `𝟙` is compact, `IsNilPure δ` (which allows
`n = 0`) agrees with the paper's definition, which asks for `n ≥ 1`. -/
lemma isNilPure_iff_exists_one_le {δ : I ⟶ 𝟙_ T} (hu : IsCompactObj (𝟙_ T)) :
    IsNilPure δ ↔ ∃ n, 1 ≤ n ∧ IsPhantom (tensorPowHom δ n) := by
  constructor
  · rintro ⟨_ | n, hn⟩
    · have h := hn _ hu (𝟙 _)
      change 𝟙 (𝟙_ T) ≫ 𝟙 (𝟙_ T) = 0 at h
      have h0 : IsZero (𝟙_ T) := (IsZero.iff_id_eq_zero _).2 (by simpa using h)
      exact ⟨1, le_rfl, fun _ _ _ => h0.eq_of_tgt _ _⟩
    · exact ⟨n + 1, by omega, hn⟩
  · rintro ⟨n, -, hn⟩
    exact ⟨n, hn⟩

/-- `δ^{⊗ n}` is a composite of the `n` maps `δ ⊗ I^{⊗ i} : I^{⊗ (i+1)} → I^{⊗ i}`, which are
`B`-zero whenever `B ◁ δ = 0`. -/
lemma isCompOf_tensorPowHom [MonoidalPreadditive T] {B : T} {δ : I ⟶ 𝟙_ T}
    (hδ : B ◁ δ = 0)
    (n : ℕ) : IsCompOf (IsTensorZero B) n (tensorPowHom δ n) := by
  induction n with
  | zero => exact IsCompOf.id _
  | succ n ih =>
    rw [tensorPowHom_succ]
    refine IsCompOf.cons ?_ ih
    change B ◁ (δ ▷ tensorPow I n ≫ (λ_ (tensorPow I n)).hom) = 0
    rw [MonoidalCategory.whiskerLeft_comp, whiskerLeft_whiskerRight_eq_zero hδ, zero_comp]

end MZeroMonoidal

section MZero

variable [HasZeroObject T] [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated T] [MonoidalCategory T] [TensorTriangulated T]

lemma IsTensorZero.tensor (W : T) {M X Y : T} {f : X ⟶ Y} (h : IsTensorZero M f) :
    IsTensorZero (W ⊗ M) f := by
  have h' : M ◁ f = 0 := h
  change (W ⊗ M) ◁ f = 0
  rw [tensor_whiskerLeft, h', MonoidalPreadditive.whiskerLeft_zero, zero_comp, comp_zero]

lemma IsTensorZero.of_isZero {M : T} (hM : IsZero M) {X Y : T} (f : X ⟶ Y) :
    IsTensorZero M f :=
  (Functor.map_isZero (tensorRight X) hM).eq_of_src _ _

/-- `M⟦n⟧ ≅ 𝟙⟦n⟧ ⊗ M`. -/
noncomputable def shiftIsoUnitTensor (M : T) (n : ℤ) : M⟦n⟧ ≅ (𝟙_ T)⟦n⟧ ⊗ M :=
  (shiftFunctor T n).mapIso (λ_ M).symm ≪≫ (((tensorRight M).commShiftIso n).app (𝟙_ T)).symm

/-- `M`-zero maps are `M⟦n⟧`-zero, as `M⟦n⟧ ≅ 𝟙⟦n⟧ ⊗ M`. -/
lemma IsTensorZero.shift (n : ℤ) {M X Y : T} {f : X ⟶ Y} (h : IsTensorZero M f) :
    IsTensorZero (M⟦n⟧) f := by
  let e := shiftIsoUnitTensor M n
  exact (h.tensor _).of_retract e.hom e.inv e.hom_inv_id

variable (B : T) in
/-- The objects `M` such that, for some `s ≥ 1`, every composite of `s` composable `B`-zero
maps is `M`-zero. -/
def nilIdeal : ObjectProperty T := fun M =>
  ∃ s, 1 ≤ s ∧ ∀ ⦃X Y : T⦄ (f : X ⟶ Y), IsCompOf (IsTensorZero B) s f → IsTensorZero M f

/-- `nilIdeal B` is a thick tensor ideal, by the proof of [Mat16, Prop. 3.27]. -/
lemma isThickTensorIdeal_nilIdeal (B : T) : IsThickTensorIdeal (nilIdeal B) := by
  refine ⟨{ exists_zero := ?_, isStableUnderShiftBy := ?_, ext₂' := ?_ }, ⟨?_⟩, ?_⟩
  · exact ⟨0, isZero_zero T, 1, le_rfl, fun X Y f _ => IsTensorZero.of_isZero (isZero_zero T) f⟩
  · intro n
    exact ⟨fun M ⟨s, hs, h⟩ => ⟨s, hs, fun X Y f hf => (h f hf).shift n⟩⟩
  · rintro Tr hT ⟨s₁, hs₁, h₁⟩ ⟨s₃, -, h₃⟩
    refine ObjectProperty.le_isoClosure _ _ ⟨s₃ + s₁, by omega, fun X Y f hf => ?_⟩
    obtain ⟨Z, g, h, hg, hh, rfl⟩ := IsCompOf.split hf
    have hg₃ : Tr.obj₃ ◁ g = 0 := h₃ g hg
    have hh₁ : Tr.obj₁ ◁ h = 0 := h₁ h hh
    have hT' := (tensorRight Z).map_distinguished _ hT
    obtain ⟨u, hu⟩ := Triangle.coyoneda_exact₂ _ hT' (Tr.obj₂ ◁ g) (by
      change Tr.obj₂ ◁ g ≫ Tr.mor₂ ▷ Z = 0
      rw [whisker_exchange, hg₃, comp_zero])
    change Tr.obj₂ ◁ g = u ≫ Tr.mor₁ ▷ Z at hu
    change Tr.obj₂ ◁ (g ≫ h) = 0
    rw [MonoidalCategory.whiskerLeft_comp, hu, Category.assoc, ← whisker_exchange, hh₁,
      zero_comp, comp_zero]
  · intro M M' r ⟨s, hs, h⟩
    exact ⟨s, hs, fun X Y f hf => (h f hf).of_retract r.i r.r r.retract⟩
  · intro W M ⟨s, hs, h⟩
    exact ⟨s, hs, fun X Y f hf => (h f hf).tensor W⟩

/-- Paper, Lemma 2.6(b) (`lem:zero`): for every `M ∈ Thick^⊗(B)` there is an `s ≥ 1` such that
every composite of `s` composable `B`-zero maps is `M`-zero. -/
theorem exists_isCompOf_isTensorZero {B M : T} (hM : thickTensorIdeal B M) :
    ∃ s, 1 ≤ s ∧ ∀ ⦃X Y : T⦄ (f : X ⟶ Y), IsCompOf (IsTensorZero B) s f → IsTensorZero M f :=
  hM (nilIdeal B) (isThickTensorIdeal_nilIdeal B)
    ⟨1, le_rfl, fun X Y f hf => by
      cases hf with
      | comp hf' hg => cases hf' with
        | id => simpa using hg⟩

variable {B I : T} {η : 𝟙_ T ⟶ B} {δ : I ⟶ 𝟙_ T} {ε : B ⟶ I⟦(1 : ℤ)⟧}

/-- Paper, Lemma 2.6(a) (`lem:zero`). Let `I →δ 𝟙 →η B → ΣI` be distinguished, with `B ⊗ η` a
split monomorphism (as for the unit of a ring object; Remark 4.3). A map `g : X ⟶ 𝟙` is
`B`-zero iff `η ∘ g = 0` iff `g` factors through `δ`. -/
theorem isTensorZero_tfae (hT : Triangle.mk δ η ε ∈ distTriang T) [IsSplitMono (B ◁ η)]
    {X : T} (g : X ⟶ 𝟙_ T) :
    List.TFAE [IsTensorZero B g, g ≫ η = 0, ∃ g' : X ⟶ I, g = g' ≫ δ] := by
  have h12 : δ ≫ η = 0 := comp_distTriang_mor_zero₁₂ _ hT
  tfae_have 1 → 2 := fun h => by
    have h' : B ◁ g = 0 := h
    rw [comp_eq_whiskerRight_comp_whiskerLeft g η, h', zero_comp, comp_zero, comp_zero]
  tfae_have 2 → 1 := fun h => by
    change B ◁ g = 0
    rw [← cancel_mono (B ◁ η), ← MonoidalCategory.whiskerLeft_comp, h,
      MonoidalPreadditive.whiskerLeft_zero, zero_comp]
  tfae_have 2 → 3 := fun h => Triangle.coyoneda_exact₂ _ hT g h
  tfae_have 3 → 2 := fun ⟨g', hg'⟩ => by
    rw [hg', Category.assoc, h12, comp_zero]
  tfae_finish

/-- Paper, Lemma 2.6(a) (`lem:zero`): `δ` is `B`-zero. -/
lemma isTensorZero_δ (hT : Triangle.mk δ η ε ∈ distTriang T) [IsSplitMono (B ◁ η)] :
    IsTensorZero B δ :=
  ((isTensorZero_tfae hT δ).out 3 1).1
    (⟨𝟙 I, (Category.id_comp δ).symm⟩ : ∃ g' : I ⟶ I, δ = g' ≫ δ)

end MZero

/-! ### Lemma 2.7, Definition 2.4, Remark 2.8 -/

/-- In a rigidly-compactly generated category the unit is compact (it is dualizable). -/
lemma isCompactObj_unit [HasShift T ℤ] [MonoidalCategory T] [RigidlyCompactlyGenerated T] :
    IsCompactObj (𝟙_ T) :=
  (RigidlyCompactlyGenerated.isCompactObj_iff_isDualizable _).2 ⟨𝟙_ T, ⟨inferInstance⟩⟩

section NilPure

variable [HasZeroObject T] [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated T] [IsTriangulated T] [MonoidalCategory T] [TensorTriangulated T]
  [CompactlyGenerated T]

variable {B I : T} {η : 𝟙_ T ⟶ B} {δ : I ⟶ 𝟙_ T} {ε : B ⟶ I⟦(1 : ℤ)⟧}

omit [CompactlyGenerated T] in
/-- Paper, Lemma 2.7 (`lem:four`): the cone of `δ^{⊗ n}` lies in `Thick^⊗(B)`. As
`δ^{⊗ (n+1)} = δ ∘ (I ⊗ δ^{⊗ n})` (up to `I ⊗ 𝟙 ≅ I`), the octahedral axiom makes the cone of
`δ^{⊗ (n+1)}` an extension of `B` by `I ⊗ (cone of δ^{⊗ n})`. -/
lemma thickTensorIdeal_of_tensorPowHom (hT : Triangle.mk δ η ε ∈ distTriang T) (n : ℕ)
    {E : T} {j : 𝟙_ T ⟶ E} {w : E ⟶ (tensorPow I n)⟦(1 : ℤ)⟧}
    (hE : Triangle.mk (tensorPowHom δ n) j w ∈ distTriang T) : thickTensorIdeal B E := by
  intro P hP hB
  have : P.IsTriangulated := hP.1
  have : P.IsStableUnderRetracts := hP.2.1
  induction n generalizing E j with
  | zero =>
    refine P.prop_of_isZero ((Triangle.isZero₃_iff_isIso₁ _ hE).2 ?_)
    change IsIso (𝟙 (𝟙_ T))
    infer_instance
  | succ n ih =>
    obtain ⟨E', j', w', hE'⟩ := distinguished_cocone_triangle (tensorPowHom δ n)
    have h₁₂ : Triangle.mk (I ◁ tensorPowHom δ n ≫ (ρ_ I).hom) ((ρ_ I).inv ≫ I ◁ j')
        (I ◁ w' ≫ ((tensorLeft I).commShiftIso (1 : ℤ)).hom.app (tensorPow I n)) ∈
          distTriang T := by
      refine isomorphic_distinguished _ ((tensorLeft I).map_distinguished _ hE') _ ?_
      exact Triangle.isoMk _ _ (Iso.refl _) (ρ_ I).symm (Iso.refl _) (by simp) (by simp)
        (by simp)
    let o := Triangulated.someOctahedron (tensorPowHom_succ' δ n).symm h₁₂ hT hE
    exact P.ext_of_isTriangulatedClosed₂ _ o.mem (hP.2.2 I E' (ih hE')) hB

omit [IsTriangulated T] [TensorTriangulated T] in
/-- Paper, Lemma 2.7 (`lem:four`): if `δ^{⊗ n}` is phantom, the map `𝟙 → E` to its cone is a
pure monomorphism. -/
lemma isPureMono_of_tensorPowHom {n : ℕ} (hn : IsPhantom (tensorPowHom δ n)) {E : T}
    {j : 𝟙_ T ⟶ E} {w : E ⟶ (tensorPow I n)⟦(1 : ℤ)⟧}
    (hE : Triangle.mk (tensorPowHom δ n) j w ∈ distTriang T) : IsPureMono j :=
  (isPureMono_iff_isPhantom _ (rot_of_distTriang _ hE)).2 (hn.shift 1).neg

/-- Paper, Lemma 2.7 (`lem:four`), "(3) ⇒ (4)": if `δ^{⊗ n}` is phantom, the map `𝟙 → E` to its
cone is a pure monomorphism with `E ∈ Thick^⊗(B)`. This direction holds for any map `η`, as
Remark 4.3 notes. -/
lemma IsNilPure.exists_isPureMono (hT : Triangle.mk δ η ε ∈ distTriang T) (hB : IsNilPure δ) :
    ∃ (E : T) (j : 𝟙_ T ⟶ E), IsPureMono j ∧ thickTensorIdeal B E := by
  obtain ⟨n, hn⟩ := hB
  obtain ⟨E, j, w, hE⟩ := distinguished_cocone_triangle (tensorPowHom δ n)
  exact ⟨E, j, isPureMono_of_tensorPowHom hn hE, thickTensorIdeal_of_tensorPowHom hT n hE⟩

/-- Paper, Lemma 2.7 (`lem:four`): `B` is nil-pure iff there is a pure monomorphism `𝟙 → E` with
`E ∈ Thick^⊗(B)`. (If `δ^{⊗ n}` is phantom, its cone is such an `E`:
`IsNilPure.exists_isPureMono`.) -/
theorem isNilPure_iff (hT : Triangle.mk δ η ε ∈ distTriang T) [IsSplitMono (B ◁ η)] :
    IsNilPure δ ↔ ∃ (E : T) (j : 𝟙_ T ⟶ E), IsPureMono j ∧ thickTensorIdeal B E := by
  constructor
  · exact IsNilPure.exists_isPureMono hT
  · rintro ⟨E, j, hj, hE⟩
    obtain ⟨s, -, hs⟩ := exists_isCompOf_isTensorZero hE
    refine ⟨s, fun K hK k => hj K hK _ ?_⟩
    have h : E ◁ tensorPowHom δ s = 0 := hs _ (isCompOf_tensorPowHom (isTensorZero_δ hT) s)
    rw [Category.assoc, comp_eq_whiskerRight_comp_whiskerLeft (tensorPowHom δ s) j, h,
      zero_comp, comp_zero, comp_zero, comp_zero]

/-- Paper, Definition 2.4 (`def:nilpure`), after [Mat16, Def. 3.18]: `B` is *descendable* if
`𝟙 ∈ Thick^⊗(B)`. -/
def IsDescendable (B : T) : Prop := thickTensorIdeal B (𝟙_ T)

omit [CompactlyGenerated T] in
/-- Tensor-triangulated extension of the unit case of Mathew–Naumann–Noel, Proposition 4.7.
Their result takes an algebra object in a symmetric monoidal stable ∞-category. Here `η` is
a map from the tensor unit with `B ◁ η` split monic. Then `B` is descendable exactly when
`δ^{⊗ n} = 0` for some `n`. -/
theorem isDescendable_iff (hT : Triangle.mk δ η ε ∈ distTriang T) [IsSplitMono (B ◁ η)] :
    IsDescendable B ↔ ∃ n, tensorPowHom δ n = 0 := by
  constructor
  · intro h
    obtain ⟨s, -, hs⟩ := exists_isCompOf_isTensorZero h
    refine ⟨s, ?_⟩
    have h1 : 𝟙_ T ◁ tensorPowHom δ s = 0 := hs _ (isCompOf_tensorPowHom (isTensorZero_δ hT) s)
    have h2 := congrArg (fun φ => (λ_ _).inv ≫ φ ≫ (λ_ _).hom) h1
    simpa using h2
  · rintro ⟨n, hn⟩
    obtain ⟨E, j, w, hE⟩ := distinguished_cocone_triangle (tensorPowHom δ n)
    obtain ⟨r, hr⟩ := Triangle.yoneda_exact₂ _ hE (𝟙 (𝟙_ T)) (by
      change tensorPowHom δ n ≫ 𝟙 _ = 0
      rw [hn, zero_comp])
    intro P hP hB
    have : P.IsStableUnderRetracts := hP.2.1
    exact P.prop_of_retract ⟨j, r, hr.symm⟩ (thickTensorIdeal_of_tensorPowHom hT n hE P hP hB)

omit [IsTriangulated T] [TensorTriangulated T] in
/-- Paper, Remark 2.8 (`rem:nilpure`): `B` is pure (`η` is a pure monomorphism) iff it is
nil-pure with `n = 1`. -/
theorem isPureMono_iff_isPhantom_tensorPowHom_one (hT : Triangle.mk δ η ε ∈ distTriang T) :
    IsPureMono η ↔ IsPhantom (tensorPowHom δ 1) := by
  have h1 : tensorPowHom δ 1 = (ρ_ I).hom ≫ δ := by
    rw [tensorPowHom_succ']
    change (I ◁ 𝟙 (𝟙_ T) ≫ (ρ_ I).hom) ≫ δ = _
    rw [MonoidalCategory.whiskerLeft_id, Category.id_comp]
  rw [h1]
  refine (isPureMono_iff_isPhantom _ (rot_of_distTriang _ hT)).trans ⟨fun h => ?_, fun h => ?_⟩
  · change IsPhantom (-(δ⟦(1 : ℤ)⟧')) at h
    have hδ : IsPhantom δ := (isPhantom_shift_iff δ 1).1 (by simpa using h.neg)
    exact hδ.precomp _
  · change IsPhantom ((ρ_ I).hom ≫ δ) at h
    have hδ := h.precomp (ρ_ I).inv
    rw [Iso.inv_hom_id_assoc] at hδ
    exact (hδ.shift 1).neg

omit [CompactlyGenerated T] in
/-- Paper, Remark 2.8 (`rem:nilpure`): descendable ring objects are nil-pure. -/
theorem IsDescendable.isNilPure (hT : Triangle.mk δ η ε ∈ distTriang T) [IsSplitMono (B ◁ η)]
    (h : IsDescendable B) : IsNilPure δ := by
  obtain ⟨n, hn⟩ := (isDescendable_iff hT).1 h
  exact ⟨n, by rw [hn]; exact isPhantom_zero _ _⟩

omit [IsTriangulated T] [TensorTriangulated T] in
/-- Paper, Remark 2.8(ii) (`rem:nilpure`): if every pure monomorphism out of `𝟙` splits
(`𝟙` is pure-injective) and `δ^{⊗ n}` is phantom, then `δ^{⊗ n} = 0`. -/
theorem tensorPowHom_eq_zero_of_pureInjective
    (h : ∀ (E : T) (j : 𝟙_ T ⟶ E), IsPureMono j → IsSplitMono j) {n : ℕ}
    (hn : IsPhantom (tensorPowHom δ n)) : tensorPowHom δ n = 0 := by
  obtain ⟨E, j, w, hE⟩ := distinguished_cocone_triangle (tensorPowHom δ n)
  obtain ⟨⟨r, hr⟩⟩ := (h E j (isPureMono_of_tensorPowHom hn hE)).exists_splitMono
  have h12 : tensorPowHom δ n ≫ j = 0 := comp_distTriang_mor_zero₁₂ _ hE
  rw [← Category.comp_id (tensorPowHom δ n), ← hr, ← Category.assoc, h12, zero_comp]

/-- Paper, Remark 2.8(ii) (`rem:nilpure`): if `𝟙` is pure-injective, nil-pure ring objects are
descendable. -/
theorem IsNilPure.isDescendable_of_pureInjective (hT : Triangle.mk δ η ε ∈ distTriang T)
    [IsSplitMono (B ◁ η)] (h : ∀ (E : T) (j : 𝟙_ T ⟶ E), IsPureMono j → IsSplitMono j)
    (hδ : IsNilPure δ) : IsDescendable B := by
  obtain ⟨n, hn⟩ := hδ
  exact (isDescendable_iff hT).2 ⟨n, tensorPowHom_eq_zero_of_pureInjective h hn⟩

variable [MonoidalClosed T]

lemma IsPhantom.tensorPowHomInner {m : ℕ} (hm : IsPhantom (tensorPowHom δ m)) (n : ℕ) :
    IsPhantom (tensorPowHomInner δ m n) := by
  induction n with
  | zero => exact hm
  | succ n ih => exact ih.whiskerLeft I

/-- `δ^{⊗ nj}` is a composite of `j` phantom maps if `δ^{⊗ n}` is phantom (Lemma 2.3). -/
lemma isCompOf_isPhantom_tensorPowHom {n : ℕ} (hn : IsPhantom (tensorPowHom δ n)) (j : ℕ) :
    IsCompOf (fun _ _ f => IsPhantom f) j (tensorPowHom δ (n * j)) := by
  induction j with
  | zero => exact IsCompOf.id _
  | succ j ih =>
    rw [show n * (j + 1) = n + n * j by ring, tensorPowHom_add]
    exact IsCompOf.cons (hn.tensorPowHomInner (n * j)) ih

/-- Paper, Remark 2.8(i) (`rem:nilpure`): if every composite of `s` phantom maps vanishes and
`δ^{⊗ n}` is phantom, then `δ^{⊗ sn} = 0`. -/
theorem tensorPowHom_mul_eq_zero {s n : ℕ}
    (hs : ∀ ⦃X Y : T⦄ (f : X ⟶ Y), IsCompOf (fun _ _ f => IsPhantom f) s f → f = 0)
    (hn : IsPhantom (tensorPowHom δ n)) : tensorPowHom δ (s * n) = 0 := by
  rw [Nat.mul_comm]
  exact hs _ (isCompOf_isPhantom_tensorPowHom hn s)

/-- Paper, Remark 2.8(i) (`rem:nilpure`): if every composite of `s` phantom maps vanishes,
nil-pure ring objects are descendable. -/
theorem IsNilPure.isDescendable_of_isCompOf_isPhantom
    (hT : Triangle.mk δ η ε ∈ distTriang T) [IsSplitMono (B ◁ η)] {s : ℕ}
    (hs : ∀ ⦃X Y : T⦄ (f : X ⟶ Y), IsCompOf (fun _ _ f => IsPhantom f) s f → f = 0)
    (hδ : IsNilPure δ) : IsDescendable B := by
  obtain ⟨n, hn⟩ := hδ
  exact (isDescendable_iff hT).2 ⟨s * n, tensorPowHom_mul_eq_zero hs hn⟩

end NilPure

end RigidDescent
