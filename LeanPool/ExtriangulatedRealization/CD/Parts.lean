/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.CD.Singles
public import LeanPool.ExtriangulatedRealization.Intervals.Decomposition

/-!
# The interval part and the `X`-part of an object of `C(D)`

Every object `M` of `C(D)` is the direct sum of its interval part `bPart M` (the summands
`Y`, `A i`, `P i`) and its `X`-part `xPart M`. The functor `ρ` kills the `X`-part, is fully
faithful on objects without copies of `X`, and sends every object to a good representation.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement IntervalLabel

universe u

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I] (D : Iᵒᵖ ⥤ ModuleCat.{u} k)

/-! ### `ρ` on objects without `X` -/

lemma rho0_map_bijective {a b : IndCat D} (ha : a.isSome) (hb : b.isSome) :
    Function.Bijective ((rho0 D).map : (a ⟶ b) → _) := by
  rcases a with _ | l
  · simp at ha
  rcases b with _ | l'
  · simp at hb
  refine ⟨fun f g h => ?_, fun g => ⟨(⟨g⟩ : (l : IntervalCat k I) ⟶ l'), rfl⟩⟩
  exact InducedCategory.hom_ext h

lemma mapMat_rho0_bijective {M N : CD D} (hM : XFree D M) (hN : XFree D N) :
    Function.Bijective ((rho0 D).mapMat_.map : (M ⟶ N) → _) := by
  constructor
  · intro f g h
    ext i j
    exact (rho0_map_bijective D (hM i) (hN j)).1 (congrFun (congrFun h i) j)
  · intro g
    choose f hf using fun i j => (rho0_map_bijective D (hM i) (hN j)).2 (g i j)
    exact ⟨f, funext fun i => funext fun j => hf i j⟩

/-- `ρ` is fully faithful on objects without copies of `X`. -/
lemma rho_map_bijective {M N : CD D} (hM : XFree D M) (hN : XFree D N) :
    Function.Bijective ((rho D).map : (M ⟶ N) → _) := by
  have hL : Function.Bijective ((Mat_.lift (𝟭 (Rep k I))).map :
      ((rho0 D).mapMat_.obj M ⟶ (rho0 D).mapMat_.obj N) → _) := by
    let e := Mat_.equivalenceSelfOfHasFiniteBiproducts (Rep k I)
    exact ⟨e.functor.map_injective, e.functor.map_surjective⟩
  exact hL.comp (mapMat_rho0_bijective D hM hN)

/-! ### Good representations from objects of `C(D)` -/

variable {D}

lemma isGood_zero_rep (E : Finset I) {M : Rep k I} (hM : IsZero M) : IsGood E M := by
  have h : ∀ t, Subsingleton (M.obj t) := fun t =>
    ModuleCat.subsingleton_of_isZero (hM.obj t)
  exact
    { finite := fun t => inferInstance
      surj := fun {s t} _ y => ⟨0, Subsingleton.elim _ _⟩
      inj := fun {s t} _ _ x y _ => Subsingleton.elim _ _
      zero := fun t _ => h _ }

lemma IsGood.of_iso {E : Finset I} {M N : Rep k I} (e : M ≅ N) (hM : IsGood E M) : IsGood E N :=
  hM.of_retract _ e.inv e.hom e.inv_hom_id

lemma IsGood.biprod {E : Finset I} {M N : Rep k I} (hM : IsGood E M) (hN : IsGood E N) :
    IsGood E (M ⊞ N) := by
  let s : ShortComplex.Splitting (ShortComplex.mk (biprod.inl : M ⟶ M ⊞ N) biprod.snd
      biprod.inl_snd) :=
    { r := biprod.fst
      s := biprod.inr
      f_r := biprod.inl_fst
      s_g := biprod.inr_snd
      id := by simp [biprod.total] }
  exact IsGood.of_shortExact E s.shortExact hM hN

lemma IsGood.biproduct {E : Finset I} (ι : Type*) [Finite ι] (f : ι → Rep k I)
    (hf : ∀ i, IsGood E (f i)) : IsGood E (⨁ f) := by
  let := Fintype.ofFinite ι
  revert f
  refine Fintype.induction_empty_option
    (P := fun ι _ => ∀ f : ι → Rep k I, (∀ i, IsGood E (f i)) → IsGood E (⨁ f)) ?_ ?_ ?_ ι
  · intro ι ι' _ e ih f hf
    let _ : Fintype ι := Fintype.ofEquiv ι' e.symm
    have := ih (f ∘ e) (fun i => hf (e i))
    exact this.of_iso (biproduct.whiskerEquiv e (fun _ => Iso.refl _))
  · intro f _
    exact isGood_zero_rep E (isZero_biproduct_empty f)
  · intro ι _ ih f hf
    have h₁ := (hf none).biprod (ih (fun i => f (some i)) (fun i => hf (some i)))
    refine h₁.of_iso (isoBiprodBiproduct (f none) (fun i => f (some i)) ≪≫ eqToIso ?_)
    exact congrArg (fun F => ⨁ F) (funext fun o => by cases o <;> rfl)

variable (D)

lemma isGood_rho0 (E : Finset I) (l : IndCat D) (hl : labelIn (E : Set I) l) :
    IsGood E ((rho0 D).obj l) := by
  rcases l with _ | l
  · exact isGood_zero_rep E (isZero_zero _)
  · rcases l with _ | i | i
    · exact isGood_rep E Y trivial
    · exact isGood_rep E (A i) hl
    · exact isGood_rep E (P i) hl

/-- `ρ` of an object whose labels lie in `E` is `E`-good. -/
lemma isGood_rho (E : Finset I) (M : CD D) (hM : ∀ i, labelIn (E : Set I) (M.X i)) :
    IsGood E ((rho D).obj M) :=
  IsGood.biproduct M.ι _ (fun i => isGood_rho0 D E _ (hM i))

/-! ### Sub-objects of `Mat_` objects given by a set of indices -/

section SubObj

variable {𝒞 : Type*} [Category.{u} 𝒞] [Preadditive 𝒞]

lemma subIncl_subProj (M : Mat_ 𝒞) (p : M.ι → Bool) :
    subIncl M p ≫ subProj M p = 𝟙 _ := by
  classical
  ext i i'
  rw [Mat_.comp_apply, Finset.sum_eq_single i.1]
  · simp only [subIncl, subProj, dite_true]
    by_cases h : i = i'
    · subst h
      simp only [dite_true]
      rw [Mat_.id_apply_self]
      exact (eqToHom_trans _ _).trans (eqToHom_refl _ _)
    · rw [dite_eq_right (fun h' => h (Subtype.ext h')), comp_zero, Mat_.id_apply_of_ne _ _ _ h]
  · intro j _ hj
    simp [subIncl, Ne.symm hj]
  · simp

lemma subIncl_subProj_of_disjoint (M : Mat_ 𝒞) (p q : M.ι → Bool)
    (hpq : ∀ i, p i = true → q i = true → False) : subIncl M p ≫ subProj M q = 0 := by
  classical
  ext i i'
  rw [Mat_.comp_apply, Finset.sum_eq_single i.1]
  · simp only [subIncl, subProj, dite_true]
    rw [dite_eq_right (fun h => hpq i.1 i.2 (by rw [h]; exact i'.2)), comp_zero]
    rfl
  · intro j _ hj
    simp [subIncl, Ne.symm hj]
  · simp

open Classical in
lemma subProj_subIncl_apply (M : Mat_ 𝒞) (p : M.ι → Bool) (i j : M.ι) :
    (subProj M p ≫ subIncl M p) i j =
      if h : i = j then (if p i then eqToHom (congrArg M.X h) else 0) else 0 := by
  classical
  rw [Mat_.comp_apply]
  by_cases hp : p i = true
  · rw [Finset.sum_eq_single ⟨i, hp⟩]
    · simp only [subProj, subIncl, dite_true, hp, ite_true]
      by_cases h : i = j
      · subst h
        rw [dite_eq_left rfl, dite_eq_left rfl]
        exact eqToHom_trans _ _
      · rw [dite_eq_right h, dite_eq_right h, comp_zero]
    · intro k _ hk
      change (if h : i = k.1 then _ else 0) ≫ _ = 0
      rw [dite_eq_right (fun h => hk (Subtype.ext h.symm)), zero_comp]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [Finset.sum_eq_zero]
    · split_ifs <;> rfl
    · intro k _
      change (if h : i = k.1 then _ else 0) ≫ _ = 0
      rw [dite_eq_right (fun h => hp (by rw [h]; exact k.2)), zero_comp]

open Classical in
lemma subProj_subIncl_add (M : Mat_ 𝒞) (p q : M.ι → Bool) (hpq : ∀ i, p i = true ∨ q i = true)
    (hdisj : ∀ i, p i = true → q i = true → False) :
    subProj M p ≫ subIncl M p + subProj M q ≫ subIncl M q = 𝟙 M := by
  classical
  ext i j
  rw [Mat_.add_apply, subProj_subIncl_apply, subProj_subIncl_apply]
  by_cases h : i = j
  · subst h
    rw [dite_eq_left rfl, dite_eq_left rfl, Mat_.id_apply_self]
    rcases hpq i with hp | hq
    · have hq : ¬ q i = true := fun hq => hdisj i hp hq
      rw [ite_eq_left hp, ite_eq_right hq, add_zero]
      rfl
    · have hp : ¬ p i = true := fun hp => hdisj i hp hq
      rw [ite_eq_right hp, ite_eq_left hq, zero_add]
      rfl
  · rw [dite_eq_right h, dite_eq_right h, add_zero, Mat_.id_apply_of_ne _ _ _ h]

end SubObj

/-! ### The interval part and the `X`-part -/

/-- The interval part of an object of `C(D)`. -/
abbrev bPart (M : CD D) : CD D := subObj M (fun i => (M.X i).isSome)

/-- The inclusion of the interval part. -/
noncomputable abbrev bIncl (M : CD D) : bPart D M ⟶ M := subIncl M _

/-- The projection onto the interval part. -/
noncomputable abbrev bProj (M : CD D) : M ⟶ bPart D M := subProj M _

lemma xPart_eq (M : CD D) : xPart D M = subObj M (fun i => (M.X i).isNone) := rfl

lemma xIncl_eq (M : CD D) : xIncl D M = subIncl M (fun i => (M.X i).isNone) := rfl

lemma xProj_eq (M : CD D) : xProj D M = subProj M (fun i => (M.X i).isNone) := rfl

lemma xFree_bPart (M : CD D) : XFree D (bPart D M) := fun i => i.2

/-- Morphisms from an object without copies of `X` to an `X`-part vanish. -/
lemma hom_xFree_xPart_eq_zero {M N : CD D} (hM : XFree D M) (f : M ⟶ xPart D N) : f = 0 := by
  funext i j
  have key : ∀ (x y : IndCat D), x.isSome → y.isNone → ∀ g g' : x ⟶ y, g = g' := by
    rintro (_ | a) (_ | b) hx hy g g'
    · exact absurd hx (by simp)
    · exact absurd hx (by simp)
    · exact Subsingleton.elim (α := PUnit) _ _
    · exact absurd hy (by simp)
  exact key (M.X i) (N.X j.1) (hM i) j.2 _ _

lemma bIncl_bProj (M : CD D) : bIncl D M ≫ bProj D M = 𝟙 _ := subIncl_subProj _ _

lemma xIncl_xProj (M : CD D) : xIncl D M ≫ xProj D M = 𝟙 _ := subIncl_subProj _ _

lemma xIncl_bProj (M : CD D) : xIncl D M ≫ bProj D M = 0 :=
  subIncl_subProj_of_disjoint _ _ _ (fun i h1 h2 => by
    cases h : M.X i <;> simp_all)

lemma bIncl_xProj (M : CD D) : bIncl D M ≫ xProj D M = 0 :=
  subIncl_subProj_of_disjoint _ _ _ (fun i h1 h2 => by
    cases h : M.X i <;> simp_all)

lemma bProj_bIncl_add (M : CD D) : bProj D M ≫ bIncl D M + xProj D M ≫ xIncl D M = 𝟙 M :=
  subProj_subIncl_add _ _ _ (fun i => by cases h : M.X i <;> simp [])
    (fun i h1 h2 => by cases h : M.X i <;> simp_all)

lemma isZero_rho_xPart (M : CD D) : IsZero ((rho D).obj (xPart D M)) := by
  have hz : ∀ i : (xPart D M).ι, IsZero ((rho0 D).obj ((xPart D M).X i)) := by
    intro i
    have h1 : (M.X i.1).isNone = true := i.2
    change IsZero ((rho0 D).obj (M.X i.1))
    cases h : M.X i.1 with
    | none => exact isZero_zero _
    | some l => simp [h] at h1
  exact ⟨fun Y => ⟨⟨0⟩, fun f => biproduct.hom_ext' _ _ (fun i => (hz i).eq_of_src _ _)⟩,
    fun Y => ⟨⟨0⟩, fun f => biproduct.hom_ext _ _ (fun i => (hz i).eq_of_tgt _ _)⟩⟩

lemma rho_bProj_bIncl (M : CD D) : (rho D).map (bProj D M ≫ bIncl D M) = 𝟙 _ := by
  have h := congrArg (rho D).map (bProj_bIncl_add D M)
  rw [Functor.map_add, CategoryTheory.Functor.map_id, (rho D).map_comp (xProj D M),
    (isZero_rho_xPart D M).eq_of_src ((rho D).map (xIncl D M)) 0, comp_zero, add_zero] at h
  exact h

/-- `ρ` identifies an object with its interval part. -/
noncomputable def rhoBPartIso (M : CD D) : (rho D).obj (bPart D M) ≅ (rho D).obj M where
  hom := (rho D).map (bIncl D M)
  inv := (rho D).map (bProj D M)
  hom_inv_id := by rw [← Functor.map_comp, bIncl_bProj, CategoryTheory.Functor.map_id]
  inv_hom_id := by rw [← Functor.map_comp, rho_bProj_bIncl]

lemma labelIn_bPart {J : Set I} {M : CD D} (hM : ∀ i, labelIn J (M.X i)) :
    ∀ i, labelIn J ((bPart D M).X i) := fun i => hM i.1

end ExtriangulatedRealization
