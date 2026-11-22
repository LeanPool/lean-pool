/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Statement
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit

/-!
# The degreewise split exact structure on cochain complexes

Let `C` be an additive category. A short complex of cochain complexes over `C` is a
*degreewise split conflation* when it is split exact in every degree, not necessarily compatibly
with the differentials. These conflations form a Quillen exact structure on
`CochainComplex C ℤ` (Keller, *Chain complexes and stable categories*, Section 1). No limits or
colimits are assumed in `C`: the kernels, cokernels, pushouts and pullbacks required by the
axioms exist degreewise because the sequences split, and are assembled into complexes by the
degreewise (co)limits of `HomologicalComplex`.

## Split short exact sequences in an additive category

* `splitComp`, `splitCompDeflation`: composites of split monomorphisms (resp. split
  epimorphisms) with split cokernels (resp. kernels) again have split cokernels (resp. kernels).
* `isPushout_split`, `isPullback_split`: the pushout of a split monomorphism and the pullback of a
  split epimorphism, as biproducts.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits HomologicalComplex Statement

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-! ### Split short exact sequences -/

section Split

variable [HasBinaryBiproducts C]

/-- The cokernel of a composite of two split monomorphisms with split cokernels. -/
noncomputable def splitComp {X Y Z W₁ W₂ : C} {f : X ⟶ Y} {p : Y ⟶ W₁} {g : Y ⟶ Z}
    {p' : Z ⟶ W₂} {w₁ : f ≫ p = 0} {w₂ : g ≫ p' = 0}
    (σ₁ : (ShortComplex.mk f p w₁).Splitting) (σ₂ : (ShortComplex.mk g p' w₂).Splitting) :
    (ShortComplex.mk (f ≫ g) (biprod.lift (σ₂.r ≫ p) p') (by
      apply biprod.hom_ext
      · have h := σ₂.f_r
        dsimp at h
        simp [reassoc_of% h, w₁]
      · simp [w₂])).Splitting where
  r := σ₂.r ≫ σ₁.r
  s := biprod.desc (σ₁.s ≫ g) σ₂.s
  f_r := by
    have h₁ := σ₁.f_r
    have h₂ := σ₂.f_r
    dsimp at h₁ h₂ ⊢
    simp [reassoc_of% h₂, h₁]
  s_g := by
    have h₁ := σ₁.s_g
    have h₂ := σ₂.s_g
    have h₃ := σ₂.f_r
    have h₄ := σ₂.s_r
    dsimp at h₁ h₂ h₃ h₄ ⊢
    apply biprod.hom_ext'
    · apply biprod.hom_ext
      · simp [reassoc_of% h₃, h₁]
      · simp [w₂]
    · apply biprod.hom_ext
      · simp [reassoc_of% h₄]
      · simp [h₂]
  id := by
    have h₁ := σ₁.id
    have h₂ := σ₂.id
    dsimp at h₁ h₂ ⊢
    rw [← h₂]
    simp only [Category.assoc, biprod.lift_desc]
    have : σ₂.r ≫ σ₁.r ≫ f ≫ g + σ₂.r ≫ p ≫ σ₁.s ≫ g = σ₂.r ≫ g := by
      rw [← Preadditive.comp_add]
      congr 1
      rw [← Category.assoc, ← Category.assoc p, ← Preadditive.add_comp, h₁, Category.id_comp]
    rw [← add_assoc, this]

/-- The kernel of a composite of two split epimorphisms with split kernels. -/
noncomputable def splitCompDeflation {K₁ K₂ Y Z W : C} {i : K₁ ⟶ Y} {p : Y ⟶ Z} {i' : K₂ ⟶ Z}
    {p' : Z ⟶ W} {w₁ : i ≫ p = 0} {w₂ : i' ≫ p' = 0}
    (σ₁ : (ShortComplex.mk i p w₁).Splitting) (σ₂ : (ShortComplex.mk i' p' w₂).Splitting) :
    (ShortComplex.mk (biprod.desc i (i' ≫ σ₁.s)) (p ≫ p') (by
      apply biprod.hom_ext'
      · simp [reassoc_of% w₁]
      · have h := σ₁.s_g
        dsimp at h
        simp [reassoc_of% h, w₂])).Splitting where
  r := biprod.lift σ₁.r (p ≫ σ₂.r)
  s := σ₂.s ≫ σ₁.s
  f_r := by
    have h₁ := σ₁.f_r
    have h₂ := σ₂.f_r
    have h₃ := σ₁.s_g
    have h₄ := σ₁.s_r
    dsimp at h₁ h₂ h₃ h₄ ⊢
    apply biprod.hom_ext'
    · apply biprod.hom_ext
      · simp [h₁]
      · simp [reassoc_of% w₁]
    · apply biprod.hom_ext
      · simp [h₄]
      · simp [reassoc_of% h₃, h₂]
  s_g := by
    have h₁ := σ₁.s_g
    have h₂ := σ₂.s_g
    dsimp at h₁ h₂ ⊢
    simp [reassoc_of% h₁, h₂]
  id := by
    have h₁ := σ₁.id
    have h₂ := σ₂.id
    dsimp at h₁ h₂ ⊢
    rw [← h₁]
    simp only [biprod.lift_desc, Category.assoc]
    have : p ≫ σ₂.r ≫ i' ≫ σ₁.s + p ≫ p' ≫ σ₂.s ≫ σ₁.s = p ≫ σ₁.s := by
      rw [← Preadditive.comp_add, ← Category.assoc σ₂.r, ← Category.assoc p',
        ← Preadditive.add_comp, h₂, Category.id_comp]
    rw [add_assoc, this]

/-- The pushout of a split monomorphism `i : X ⟶ Y` with split cokernel `p : Y ⟶ W` along
`t : X ⟶ X'` is `X' ⊞ W`. -/
lemma isPushout_split {X Y W X' : C} {i : X ⟶ Y} {p : Y ⟶ W} {w : i ≫ p = 0}
    (σ : (ShortComplex.mk i p w).Splitting) (t : X ⟶ X') :
    IsPushout i t (biprod.lift (σ.r ≫ t) p) (biprod.inl : X' ⟶ X' ⊞ W) := by
  have f_r := σ.f_r
  have s_r := σ.s_r
  have s_g := σ.s_g
  have hid := σ.id
  dsimp at f_r s_r s_g hid
  refine IsPushout.of_isColimit' ⟨by apply biprod.hom_ext <;> simp [reassoc_of% f_r, w]⟩
    (PushoutCocone.IsColimit.mk _ (fun s => biprod.desc s.inr (σ.s ≫ s.inl)) ?_ ?_ ?_)
  · intro s
    dsimp
    simp only [biprod.lift_desc, Category.assoc]
    rw [← s.condition, ← Category.assoc, ← Category.assoc p, ← Preadditive.add_comp, hid,
      Category.id_comp]
  · intro s
    exact biprod.inl_desc _ _
  · intro s m h₁ h₂
    apply biprod.hom_ext'
    · simp [h₂]
    · rw [biprod.inr_desc, ← h₁, ← Category.assoc]
      congr 1
      apply biprod.hom_ext <;> simp [reassoc_of% s_r, s_g]

/-- The pullback of a split epimorphism `p : Y ⟶ Z` with split kernel `i : X ⟶ Y` along
`t : Z' ⟶ Z` is `X ⊞ Z'`. -/
lemma isPullback_split {X Y Z Z' : C} {i : X ⟶ Y} {p : Y ⟶ Z} {w : i ≫ p = 0}
    (σ : (ShortComplex.mk i p w).Splitting) (t : Z' ⟶ Z) :
    IsPullback (biprod.desc i (t ≫ σ.s)) (biprod.snd : X ⊞ Z' ⟶ Z') p t := by
  have f_r := σ.f_r
  have s_r := σ.s_r
  have s_g := σ.s_g
  have hid := σ.id
  dsimp at f_r s_r s_g hid
  refine IsPullback.of_isLimit' ⟨by apply biprod.hom_ext' <;> simp [w, s_g]⟩
    (PullbackCone.IsLimit.mk _ (fun s => biprod.lift (s.fst ≫ σ.r) s.snd) ?_ ?_ ?_)
  · intro s
    simp only [biprod.lift_desc, Category.assoc]
    rw [← s.condition_assoc, ← Preadditive.comp_add, hid, Category.comp_id]
  · intro s
    simp
  · intro s m h₁ h₂
    apply biprod.hom_ext
    · rw [biprod.lift_fst, ← h₁, Category.assoc]
      congr 1
      apply biprod.hom_ext' <;> simp [f_r, s_r]
    · simp [h₂]

/-- A split sequence stays split when its cokernel is replaced by another cokernel. -/
noncomputable def splittingOfIsColimit [HasZeroObject C] {S : ShortComplex C} (σ : S.Splitting)
    {Z : C} {q : S.X₂ ⟶ Z} {w : S.f ≫ q = 0} (hc : IsColimit (CokernelCofork.ofπ q w)) :
    (ShortComplex.mk S.f q w).Splitting :=
  have h : S.g ≫ (IsColimit.coconePointUniqueUpToIso σ.gIsCokernel hc).hom = q :=
    IsColimit.comp_coconePointUniqueUpToIso_hom σ.gIsCokernel hc WalkingParallelPair.one
  σ.ofIso (ShortComplex.isoMk (Iso.refl _) (Iso.refl _)
    (IsColimit.coconePointUniqueUpToIso σ.gIsCokernel hc) (by simp) (by simpa using h.symm))

/-- A split sequence stays split when its kernel is replaced by another kernel. -/
noncomputable def splittingOfIsLimit [HasZeroObject C] {S : ShortComplex C} (σ : S.Splitting)
    {K : C} {i : K ⟶ S.X₂} {w : i ≫ S.g = 0} (hc : IsLimit (KernelFork.ofι i w)) :
    (ShortComplex.mk i S.g w).Splitting :=
  have h : (IsLimit.conePointUniqueUpToIso σ.fIsKernel hc).hom ≫ i = S.f :=
    IsLimit.conePointUniqueUpToIso_hom_comp σ.fIsKernel hc WalkingParallelPair.zero
  σ.ofIso (ShortComplex.isoMk (IsLimit.conePointUniqueUpToIso σ.fIsKernel hc) (Iso.refl _)
    (Iso.refl _) (by simpa using h) (by simp))

end Split

/-! ### Degreewise split conflations of cochain complexes -/

section Complexes

/-- A short complex of cochain complexes is a degreewise split conflation when it is split
exact in every degree. -/
def IsDegreewiseSplit (S : ShortComplex (CochainComplex C ℤ)) : Prop :=
  ∀ n, Nonempty (S.map (eval C (ComplexShape.up ℤ) n)).Splitting

lemma IsDegreewiseSplit.of_iso {S S' : ShortComplex (CochainComplex C ℤ)} (e : S ≅ S')
    (hS : IsDegreewiseSplit S) : IsDegreewiseSplit S' :=
  fun n => ⟨(hS n).some.ofIso ((eval C (ComplexShape.up ℤ) n).mapShortComplex.mapIso e)⟩

lemma IsDegreewiseSplit.isLimit [HasZeroObject C] {S : ShortComplex (CochainComplex C ℤ)}
    (hS : IsDegreewiseSplit S) : Nonempty (IsLimit (KernelFork.ofι S.f S.zero)) :=
  ⟨isLimitOfEval _ _ fun n =>
    (KernelFork.isLimitMapConeEquiv _ (eval C (ComplexShape.up ℤ) n)).symm (hS n).some.fIsKernel⟩

lemma IsDegreewiseSplit.isColimit [HasZeroObject C] {S : ShortComplex (CochainComplex C ℤ)}
    (hS : IsDegreewiseSplit S) : Nonempty (IsColimit (CokernelCofork.ofπ S.g S.zero)) :=
  ⟨isColimitOfEval _ _ fun n =>
    (CokernelCofork.isColimitMapCoconeEquiv _ (eval C (ComplexShape.up ℤ) n)).symm
      (hS n).some.gIsCokernel⟩

end Complexes

/-! ### The axioms -/

section Axioms

variable [HasZeroObject C] [HasBinaryBiproducts C]

open ShortComplex ZeroObject

omit [HasBinaryBiproducts C] in
lemma isDegreewiseSplit_id_zero (X : CochainComplex C ℤ) :
    IsDegreewiseSplit (ShortComplex.mk (𝟙 X) (0 : X ⟶ 0) (by simp)) := fun n =>
  ⟨Splitting.ofIsIsoOfIsZero _
    (show IsIso (HomologicalComplex.Hom.f (𝟙 X) n) by rw [HomologicalComplex.id_f]; infer_instance)
    ((eval C _ n).map_isZero (isZero_zero _))⟩

omit [HasBinaryBiproducts C] in
lemma isDegreewiseSplit_zero_id (X : CochainComplex C ℤ) :
    IsDegreewiseSplit (ShortComplex.mk (0 : 0 ⟶ X) (𝟙 X) (by simp)) := fun n =>
  ⟨Splitting.ofIsZeroOfIsIso _ ((eval C _ n).map_isZero (isZero_zero _))
    (show IsIso (HomologicalComplex.Hom.f (𝟙 X) n) by rw [HomologicalComplex.id_f]; infer_instance)⟩

/-- [E1] Composites of inflations are inflations. -/
lemma IsDegreewiseSplit.exists_comp {X Y Z W₁ W₂ : CochainComplex C ℤ} {f : X ⟶ Y}
    {p : Y ⟶ W₁} {g : Y ⟶ Z} {p' : Z ⟶ W₂} {w₁ : f ≫ p = 0} {w₂ : g ≫ p' = 0}
    (h₁ : IsDegreewiseSplit (ShortComplex.mk f p w₁))
    (h₂ : IsDegreewiseSplit (ShortComplex.mk g p' w₂)) :
    ∃ (W : CochainComplex C ℤ) (q : Z ⟶ W) (w : (f ≫ g) ≫ q = 0),
      IsDegreewiseSplit (ShortComplex.mk (f ≫ g) q w) := by
  let σ n := splitComp (h₁ n).some (h₂ n).some
  have : ∀ n, HasColimit (parallelPair (f ≫ g) 0 ⋙ eval C (ComplexShape.up ℤ) n) := fun n => by
    have : HasColimit (parallelPair ((f ≫ g).f n) 0) := ⟨⟨⟨_, (σ n).gIsCokernel⟩⟩⟩
    exact hasColimit_of_iso (F := parallelPair ((f ≫ g).f n) 0)
      (parallelPair.ext (Iso.refl _) (Iso.refl _) (by simp) (by simp))
  refine ⟨cokernel (f ≫ g), cokernel.π _, cokernel.condition _, fun n => ⟨?_⟩⟩
  have hc : IsColimit (CokernelCofork.ofπ ((cokernel.π (f ≫ g)).f n)
      (show (f ≫ g).f n ≫ (cokernel.π (f ≫ g)).f n = 0 by
        rw [← HomologicalComplex.comp_f, cokernel.condition, HomologicalComplex.zero_f])) :=
    (CokernelCofork.isColimitMapCoconeEquiv
      (CokernelCofork.ofπ (cokernel.π (f ≫ g)) (cokernel.condition _))
        (eval C (ComplexShape.up ℤ) n))
      (isColimitOfPreserves (eval C (ComplexShape.up ℤ) n) (cokernelIsCokernel (f ≫ g)))
  exact splittingOfIsColimit (σ n) hc

/-- [E1ᵒᵖ] Composites of deflations are deflations. -/
lemma IsDegreewiseSplit.exists_comp_deflation {K₁ K₂ Y Z W : CochainComplex C ℤ} {i : K₁ ⟶ Y}
    {p : Y ⟶ Z} {i' : K₂ ⟶ Z} {p' : Z ⟶ W} {w₁ : i ≫ p = 0} {w₂ : i' ≫ p' = 0}
    (h₁ : IsDegreewiseSplit (ShortComplex.mk i p w₁))
    (h₂ : IsDegreewiseSplit (ShortComplex.mk i' p' w₂)) :
    ∃ (K : CochainComplex C ℤ) (j : K ⟶ Y) (w : j ≫ (p ≫ p') = 0),
      IsDegreewiseSplit (ShortComplex.mk j (p ≫ p') w) := by
  let σ n := splitCompDeflation (h₁ n).some (h₂ n).some
  have : ∀ n, HasLimit (parallelPair (p ≫ p') 0 ⋙ eval C (ComplexShape.up ℤ) n) := fun n => by
    have : HasLimit (parallelPair ((p ≫ p').f n) 0) := ⟨⟨⟨_, (σ n).fIsKernel⟩⟩⟩
    exact hasLimit_of_iso (F := parallelPair ((p ≫ p').f n) 0)
      (parallelPair.ext (F := parallelPair ((p ≫ p').f n) 0)
        (G := parallelPair (p ≫ p') 0 ⋙ eval C (ComplexShape.up ℤ) n)
        (Iso.refl _) (Iso.refl _) (by simp) (by simp))
  refine ⟨kernel (p ≫ p'), kernel.ι _, kernel.condition _, fun n => ⟨?_⟩⟩
  have hc : IsLimit (KernelFork.ofι ((kernel.ι (p ≫ p')).f n)
      (show (kernel.ι (p ≫ p')).f n ≫ (p ≫ p').f n = 0 by
        rw [← HomologicalComplex.comp_f, kernel.condition, HomologicalComplex.zero_f])) :=
    (KernelFork.isLimitMapConeEquiv (KernelFork.ofι (kernel.ι (p ≫ p')) (kernel.condition _))
        (eval C (ComplexShape.up ℤ) n))
      (isLimitOfPreserves (eval C (ComplexShape.up ℤ) n) (kernelIsKernel (p ≫ p')))
  exact splittingOfIsLimit (σ n) hc

omit [HasZeroObject C] in
/-- [E2] Pushouts of inflations exist and are inflations. -/
lemma IsDegreewiseSplit.exists_pushout {X Y W X' : CochainComplex C ℤ} {i : X ⟶ Y} {p : Y ⟶ W}
    {w : i ≫ p = 0} (h : IsDegreewiseSplit (ShortComplex.mk i p w)) (t : X ⟶ X') :
    ∃ (Y' : CochainComplex C ℤ) (i' : X' ⟶ Y') (t' : Y ⟶ Y'), IsPushout i t t' i' ∧
      ∃ (W' : CochainComplex C ℤ) (p' : Y' ⟶ W') (w' : i' ≫ p' = 0),
        IsDegreewiseSplit (ShortComplex.mk i' p' w') := by
  have : ∀ n, HasColimit (span i t ⋙ eval C (ComplexShape.up ℤ) n) := fun n => by
    have : HasColimit (span (i.f n) (t.f n)) := (isPushout_split (h n).some (t.f n)).hasPushout
    exact hasColimit_of_iso (F := span (i.f n) (t.f n)) (diagramIsoSpan _)
  have hw : i ≫ p = t ≫ 0 := by rw [w, comp_zero]
  refine ⟨pushout i t, pushout.inr i t, pushout.inl i t, IsPushout.of_hasPushout i t, W,
    pushout.desc p 0 hw, pushout.inr_desc _ _ _, fun n => ⟨?_⟩⟩
  have hP := (IsPushout.of_hasPushout i t).map (eval C (ComplexShape.up ℤ) n)
  have hM := isPushout_split (h n).some (t.f n)
  let e := hP.isoIsPushout _ _ hM
  have h₁ : (pushout.inr i t).f n ≫ e.hom = biprod.inl := hP.inr_isoIsPushout_hom _ _ hM
  have h₂ : (pushout.desc p 0 hw).f n = e.hom ≫ biprod.snd := by
    apply hP.hom_ext
    · have h₀ : (pushout.inl i t).f n ≫ e.hom = _ := hP.inl_isoIsPushout_hom _ _ hM
      change (pushout.inl i t).f n ≫ _ = (pushout.inl i t).f n ≫ e.hom ≫ _
      rw [← HomologicalComplex.comp_f, pushout.inl_desc, ← Category.assoc, h₀]
      exact (biprod.lift_snd _ _).symm
    · change (pushout.inr i t).f n ≫ _ = (pushout.inr i t).f n ≫ e.hom ≫ _
      rw [← HomologicalComplex.comp_f, pushout.inr_desc, ← Category.assoc, h₁,
        HomologicalComplex.zero_f]
      exact biprod.inl_snd.symm
  refine (Splitting.ofHasBinaryBiproduct _ _).ofIso
    (ShortComplex.isoMk (Iso.refl _) e.symm (Iso.refl _) ?_ ?_)
  · change 𝟙 _ ≫ (pushout.inr i t).f n = biprod.inl ≫ e.inv
    rw [Category.id_comp, Iso.eq_comp_inv]
    exact h₁
  · change e.inv ≫ (pushout.desc p 0 hw).f n = biprod.snd ≫ 𝟙 _
    rw [h₂, Iso.inv_hom_id_assoc, Category.comp_id]

omit [HasZeroObject C] in
/-- [E2ᵒᵖ] Pullbacks of deflations exist and are deflations. -/
lemma IsDegreewiseSplit.exists_pullback {X Y Z Z' : CochainComplex C ℤ} {i : X ⟶ Y} {p : Y ⟶ Z}
    {w : i ≫ p = 0} (h : IsDegreewiseSplit (ShortComplex.mk i p w)) (t : Z' ⟶ Z) :
    ∃ (Y' : CochainComplex C ℤ) (p' : Y' ⟶ Z') (t' : Y' ⟶ Y), IsPullback t' p' p t ∧
      ∃ (K : CochainComplex C ℤ) (i' : K ⟶ Y') (w' : i' ≫ p' = 0),
        IsDegreewiseSplit (ShortComplex.mk i' p' w') := by
  have : ∀ n, HasLimit (cospan p t ⋙ eval C (ComplexShape.up ℤ) n) := fun n => by
    have : HasLimit (cospan (p.f n) (t.f n)) := (isPullback_split (h n).some (t.f n)).hasPullback
    exact hasLimit_of_iso (F := cospan (p.f n) (t.f n))
      (diagramIsoCospan (cospan p t ⋙ eval C (ComplexShape.up ℤ) n)).symm
  have hw : i ≫ p = 0 ≫ t := by rw [w, zero_comp]
  refine ⟨pullback p t, pullback.snd p t, pullback.fst p t, IsPullback.of_hasPullback p t, X,
    pullback.lift i 0 hw, pullback.lift_snd _ _ _, fun n => ⟨?_⟩⟩
  have hP := (IsPullback.of_hasPullback p t).map (eval C (ComplexShape.up ℤ) n)
  have hM := isPullback_split (h n).some (t.f n)
  let e := hP.isoIsPullback _ _ hM
  have h₂ : e.hom ≫ biprod.snd = (pullback.snd p t).f n := hP.isoIsPullback_hom_snd _ _ hM
  have h₁ : (pullback.lift i 0 hw).f n ≫ e.hom = biprod.inl := by
    apply hM.hom_ext
    · rw [Category.assoc, hP.isoIsPullback_hom_fst _ _ hM, biprod.inl_desc]
      change (pullback.lift i 0 hw).f n ≫ (pullback.fst p t).f n = _
      rw [← HomologicalComplex.comp_f, pullback.lift_fst]
      rfl
    · rw [Category.assoc, h₂, ← HomologicalComplex.comp_f, pullback.lift_snd,
        HomologicalComplex.zero_f]
      exact biprod.inl_snd.symm
  refine (Splitting.ofHasBinaryBiproduct _ _).ofIso
    (ShortComplex.isoMk (Iso.refl _) e.symm (Iso.refl _) ?_ ?_)
  · change 𝟙 _ ≫ (pullback.lift i 0 hw).f n = biprod.inl ≫ e.inv
    rw [Category.id_comp, Iso.eq_comp_inv]
    exact h₁
  · change e.inv ≫ (pullback.snd p t).f n = biprod.snd ≫ 𝟙 _
    rw [← h₂, Iso.inv_hom_id_assoc, Category.comp_id]

variable (C) in
/-- The degreewise split exact structure on `CochainComplex C ℤ`. -/
noncomputable def degreewiseSplit : ExactStructure (CochainComplex C ℤ) where
  Conflation := IsDegreewiseSplit
  conflation_iso := fun ⟨e⟩ h => h.of_iso e
  isLimit_kernelFork := IsDegreewiseSplit.isLimit
  isColimit_cokernelCofork := IsDegreewiseSplit.isColimit
  id_inflation X := ⟨0, 0, by simp, isDegreewiseSplit_id_zero X⟩
  id_deflation X := ⟨0, 0, by simp, isDegreewiseSplit_zero_id X⟩
  inflation_comp f g := by
    rintro ⟨W₁, p, w₁, h₁⟩ ⟨W₂, p', w₂, h₂⟩
    exact h₁.exists_comp h₂
  deflation_comp f g := by
    rintro ⟨K₁, i, w₁, h₁⟩ ⟨K₂, i', w₂, h₂⟩
    exact h₁.exists_comp_deflation h₂
  pushout_inflation i t := by
    rintro ⟨W, p, w, h⟩
    exact h.exists_pushout t
  pullback_deflation p t := by
    rintro ⟨K, i, w, h⟩
    exact h.exists_pullback t

end Axioms

end ExtriangulatedRealization
