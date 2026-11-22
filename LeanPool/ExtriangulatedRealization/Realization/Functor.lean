/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Realization.XPart
public import LeanPool.ExtriangulatedRealization.Categories.OnePointLift
public import LeanPool.ExtriangulatedRealization.Categories.Biproduct

/-!
# The realization functor `F : C_J ⥤ K(Q)` (Proposition 2.3, Step 2)

The category `C_J` is modelled as the additive envelope of the one-point extension of the
intervals with index in `J`. The functor `F` sends an interval to (the image in `K(Q)` of) its
resolution, `X` to `L[-1]`, and `u ∈ D_i = C_J(X, A i)` to the class `xLin u`.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement IntervalLabel ZeroObject DerivedCategory

universe u

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I]

attribute [local instance] HasDerivedCategory.standard

/-! ### Linearity of the resolution functor -/

instance ι₀_linear : (ι₀ (k := k) (I := I)).Linear k where
  map_smul {M N} f c :=
    biproduct_matrix_smul (fun i => (IntervalLabel.rep k (M.X i))) (fun j => rep k (N.X j))
      (fun i j => (f i j).hom) c

instance Gfun_linear : (Gfun k I).Linear k := by
  unfold Gfun
  infer_instance

instance resFunctor_linear : (resFunctor (k := k) (I := I)).Linear k where
  map_smul {l l'} φ c := by
    apply (Gfun_map_bijective (resK l) l').1
    change (Gfun k I).map (resFunctor.map (c • φ)) = (Gfun k I).map (c • resFunctor.map φ)
    rw [(Gfun k I).map_smul, Gfun_map_resFunctor, Gfun_map_resFunctor]
    change _ ≫ (singleFunctor (Rep k I) 0).map (c • φ.hom) ≫ _ = _
    rw [(singleFunctor (Rep k I) 0).map_smul, Linear.smul_comp, Linear.comp_smul]
    rfl

/-! ### The category `C_J` -/

variable (J : Set I)

/-- The interval labels with index in `J`. -/
abbrev LabelInJ : ObjectProperty (IntervalCat k I) := fun l => labelIn J (some l)

/-- The intervals with index in `J`. -/
abbrev IntervalJ := (LabelInJ (k := k) J).FullSubcategory

variable (D : Iᵒᵖ ⥤ ModuleCat.{u} k)

/-- `Ψ` restricted to the intervals with index in `J`. -/
noncomputable abbrev psiJ : IntervalJ (k := k) J ⥤ ModuleCat.{u} k := (LabelInJ J).ι ⋙ psi D

/-- The indecomposables of `C_J`: `X` adjoined to the intervals with index in `J`. -/
abbrev IndJ := OnePointExtension (IntervalJ (k := k) J) (psiJ J D)

/-- The model `Mat_ IndJ` of the category `C_J`. -/
abbrev CDJ := Mat_ (IndJ J D)

variable {J D} {R : RealizationData D J}

namespace RealizationData

instance e₀_linear : R.e₀.Linear k := by
  unfold e₀
  infer_instance

/-- There are no nonzero morphisms from `L[-1]` to the resolution of `Y` or `P i`. -/
lemma hom_Xc_eq_zero {l : IntervalCat k I} (hl : HasBot l)
    (f : (HomotopyCategory.quotient R.Q (ComplexShape.up ℤ)).obj R.Xc ⟶
      (HomotopyCategory.quotient R.Q (ComplexShape.up ℤ)).obj (R.resCQ l)) : f = 0 := by
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient R.Q (ComplexShape.up ℤ)).map_surjective f
  have hz : IsZero ((R.resCQ l).X 1) := by
    change IsZero (R.e₀.obj ((resC l).X 1))
    refine R.e₀.map_isZero (IsZero.of_iso ?_ (HomologicalComplex.doubleXIso₁ _ _ (by lia)))
    rcases l with _ | i | i
    · exact isZero_zero _
    · exact absurd hl id
    · exact isZero_zero _
  have : g = 0 := by
    apply HomologicalComplex.from_single_hom_ext
    exact hz.eq_of_tgt _ _
  rw [this, Functor.map_zero]

variable (R) (hR : R.IsCompatible)

/-- The interval part of the realization functor. -/
noncomputable abbrev FB : IntervalJ (k := k) J ⥤ HomotopyCategory R.Q (ComplexShape.up ℤ) :=
  (LabelInJ J).ι ⋙ resFunctor ⋙ R.e₀.mapHomotopyCategory (ComplexShape.up ℤ)

/-- The morphisms out of `L[-1]`. -/
noncomputable def ιX : ∀ a : IntervalJ (k := k) J, (psiJ J D).obj a →ₗ[k]
    ((HomotopyCategory.quotient R.Q (ComplexShape.up ℤ)).obj R.Xc ⟶ (R.FB).obj a)
  | ⟨Y, _⟩ => 0
  | ⟨A i, hi⟩ => R.xLin hR i hi
  | ⟨P _, _⟩ => 0

lemma ιX_nat {a b : IntervalJ (k := k) J} (g : a ⟶ b) (x : (psiJ J D).obj a) :
    R.ιX hR b (((psiJ J D).map g).hom x) = R.ιX hR a x ≫ (R.FB).map g := by
  rcases a with ⟨_ | j | j, ha⟩
  · have : Subsingleton ((psiJ J D).obj ⟨Y, ha⟩) := inferInstanceAs (Subsingleton PUnit)
    obtain rfl : x = 0 := Subsingleton.elim _ _
    rw [map_zero, map_zero, map_zero, zero_comp]
  rotate_left
  · have : Subsingleton ((psiJ J D).obj ⟨P j, ha⟩) := inferInstanceAs (Subsingleton PUnit)
    obtain rfl : x = 0 := Subsingleton.elim _ _
    rw [map_zero, map_zero, map_zero, zero_comp]
  rcases b with ⟨_ | i | i, hb⟩
  · exact (R.hom_Xc_eq_zero (l := Y) trivial _).symm
  rotate_left
  · exact (R.hom_Xc_eq_zero (l := P i) trivial _).symm
  change R.xLin hR i hb ((psiMap D g.hom).hom x) = R.xLin hR j ha x ≫ (R.FB).map g
  by_cases hij : i ≤ j
  · have hg : g.hom = coeffRep g.hom.hom • aHom hij :=
      InducedCategory.hom_ext (eq_coeffRep_smul_aMap hij g.hom.hom)
    have hFg : (R.FB).map g = coeffRep g.hom.hom •
        (R.e₀.mapHomotopyCategory _).map (resFunctor.map (aHom (k := k) hij)) := by
      change (R.e₀.mapHomotopyCategory _).map (resFunctor.map g.hom) = _
      conv_lhs => rw [hg]
      rw [Functor.map_smul, Functor.map_smul]
    have hψ : (psiMap D g.hom).hom x =
        coeffRep g.hom.hom • (D.map (homOfLE hij).op).hom x := by
      change ((if h : i ≤ j then coeffRep g.hom.hom • D.map (homOfLE h).op else 0).hom x) = _
      rw [dite_eq_left hij]
      rfl
    rw [hψ, (R.xLin hR i hb).map_smul, ← R.xLin_comp_aMap hR hb ha hij x, hFg]
    exact (Linear.comp_smul _ _ _ _ _ _).symm
  · have hg : g.hom.hom = 0 := eq_zero_of_not_le hij g.hom.hom
    have hFg : (R.FB).map g = 0 := by
      change (R.e₀.mapHomotopyCategory _).map (resFunctor.map g.hom) = 0
      rw [show g.hom = 0 from InducedCategory.hom_ext hg, Functor.map_zero, Functor.map_zero]
    have hψ : (psiMap D g.hom).hom x = 0 := by
      change ((if h : i ≤ j then coeffRep g.hom.hom • D.map (homOfLE h).op else 0).hom x) = _
      rw [dite_eq_right hij]
      rfl
    rw [hψ, hFg]
    exact ((R.xLin hR i hb).map_zero).trans comp_zero.symm

/-- The lift data of the realization functor on `IndJ`. -/
noncomputable def liftData : OnePointExtension.LiftData (psiJ J D)
    (HomotopyCategory R.Q (ComplexShape.up ℤ)) where
  FB := R.FB
  Xt := (HomotopyCategory.quotient R.Q (ComplexShape.up ℤ)).obj R.Xc
  sc c := c • 𝟙 _
  ι a := R.ιX hR a
  sc_one := one_smul _ _
  sc_mul c c' := by rw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, mul_smul]
  sc_add c c' := add_smul _ _ _
  ι_add a := (R.ιX hR a).map_add
  ι_nat g x := R.ιX_nat hR g x
  ι_sc c a x := by rw [Linear.smul_comp, Category.id_comp, map_smul]

/-- The realization functor on the indecomposables of `C_J`. -/
noncomputable def F₁ : IndJ J D ⥤ HomotopyCategory R.Q (ComplexShape.up ℤ) :=
  OnePointExtension.lift (R.liftData hR)

instance F₁_additive : (R.F₁ hR).Additive := OnePointExtension.lift_additive _

/-- The realization functor `F : C_J ⥤ K(Q)` (Proposition 2.3). -/
noncomputable def realF : CDJ J D ⥤ HomotopyCategory R.Q (ComplexShape.up ℤ) :=
  matLift (R.F₁ hR)

end RealizationData

end ExtriangulatedRealization
