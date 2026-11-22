/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Categories.Biproduct
public import LeanPool.ExtriangulatedRealization.Categories.Indecomposable
public import LeanPool.ExtriangulatedRealization.CD.Closure
public import LeanPool.ExtriangulatedRealization.CD.Extensions
public import LeanPool.ExtriangulatedRealization.Intervals.Ext

/-!
# Indecomposables of `C(D)` and their extensions (Proposition 4.4, Step 1 and (4.1))

The single objects `X`, `Y`, `A i`, `P i` have endomorphism ring `k`: for `X` this is
Construction 2.2, and for an interval `ρ` is fully faithful and every endomorphism of an
interval representation is a scalar. Hence they are indecomposable with local endomorphism
rings, and they are pairwise nonisomorphic since `ρ` separates them. Every object of `C(D)` is
the direct sum of its entries, so `C(D)` is Krull–Schmidt and every indecomposable is a single
object. Finally `E(C, A) = Ext¹(ρC, ρA)` on single objects is read off from the table (4.1) for
interval representations.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement IntervalLabel Abelian

universe u

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I] (D : Iᵒᵖ ⥤ ModuleCat.{u} k)

attribute [local instance] HasExt.standard

/-! ### Endomorphisms of single objects -/

lemma single_id_ne_zero (l : IndCat D) : 𝟙 (single D l) ≠ 0 := by
  rcases l with _ | a
  · intro h
    have h' := congrFun (congrFun h PUnit.unit) PUnit.unit
    erw [Mat_.id_apply_self] at h'
    exact one_ne_zero (α := k) h'
  · intro h
    apply label_id_ne_zero (k := k) a
    have h2 := congrArg (rho D).map h
    rw [CategoryTheory.Functor.map_id, Functor.map_zero] at h2
    have h3 := (rhoSingleIso D (indI D a)).inv ≫= h2 =≫ (rhoSingleIso D (indI D a)).hom
    have h4 : 𝟙 ((rho0 D).obj (indI D a)) = 0 := by simpa using h3
    exact h4

lemma singleX_endo_eq_smul (f : single D (indX D) ⟶ single D (indX D)) :
    ∃ c : k, f = c • 𝟙 _ := by
  refine ⟨show k from f PUnit.unit PUnit.unit, ?_⟩
  ext i j
  cases i
  cases j
  have h1 : (𝟙 (single D (indX D)) : single D (indX D) ⟶ single D (indX D)) PUnit.unit
      PUnit.unit = (1 : k) := Mat_.id_apply_self _ _
  change _ = (show k from f PUnit.unit PUnit.unit) • (𝟙 (single D (indX D)) :
    single D (indX D) ⟶ single D (indX D)) PUnit.unit PUnit.unit
  rw [h1]
  exact (mul_one (show k from f PUnit.unit PUnit.unit)).symm

lemma singleI_endo_eq_smul (a : IntervalCat k I) (f : single D (indI D a) ⟶ single D (indI D a)) :
    ∃ c : k, f = c • 𝟙 _ := by
  let e : (rho D).obj (single D (indI D a)) ≅ a.rep k := rhoSingleIso D (indI D a)
  obtain ⟨c, hc⟩ := label_endo_eq_smul (k := k) a (e.inv ≫ (rho D).map f ≫ e.hom)
  refine ⟨c, (rho_map_bijective D (xFree_single D a) (xFree_single D a)).1 ?_⟩
  have h : (rho D).map f = e.hom ≫ (c • 𝟙 (a.rep k)) ≫ e.inv := by
    rw [← hc]
    simp
  rw [h, Functor.map_smul, CategoryTheory.Functor.map_id]
  simp

lemma single_endo_eq_smul (l : IndCat D) (f : single D l ⟶ single D l) :
    ∃ c : k, f = c • 𝟙 _ := by
  rcases l with _ | a
  · exact singleX_endo_eq_smul D f
  · exact singleI_endo_eq_smul D a f

lemma single_isIndecomposable (l : IndCat D) : IsIndecomposable (single D l) :=
  isIndecomposable_of_endo_scalar (single_id_ne_zero D l) (single_endo_eq_smul D l)

lemma single_existsUnique_smul (l : IndCat D) (f : single D l ⟶ single D l) :
    ∃! c : k, f = c • 𝟙 _ :=
  existsUnique_smul_id (single_id_ne_zero D l) (single_endo_eq_smul D l) f

lemma single_isLocalRing (l : IndCat D) : IsLocalRing (End (single D l)) :=
  isLocalRing_end (single_id_ne_zero D l) (single_endo_eq_smul D l)

/-- Isomorphic single objects have the same label. -/
lemma eq_of_single_iso {l l' : IndCat D} (e : single D l ≅ single D l') : l = l' := by
  have e' : (rho0 D).obj l ≅ (rho0 D).obj l' :=
    (rhoSingleIso D l).symm ≪≫ (rho D).mapIso e ≪≫ rhoSingleIso D l'
  rcases l with _ | a <;> rcases l' with _ | b
  · rfl
  · exact absurd ((IsZero.of_iso (isZero_zero _) e'.symm).eq_of_src _ _)
      (label_id_ne_zero (k := k) b)
  · exact absurd ((IsZero.of_iso (isZero_zero _) e').eq_of_src _ _)
      (label_id_ne_zero (k := k) a)
  · exact congrArg some (label_eq_of_iso e')

/-! ### Krull–Schmidt -/

/-- `C(D)` is Krull–Schmidt: every object is the direct sum of its entries. -/
lemma isKrullSchmidt_CD : IsKrullSchmidt (CD D) := by
  intro M
  let e := Fintype.equivFin M.ι
  exact ⟨Fintype.card M.ι, fun j => single D (M.X (e.symm j)), fun j => single_isLocalRing D _,
    ⟨Mat_.isoReindex M e ≪≫ Mat_.isoBiproductEmbedding _⟩⟩

/-- Every indecomposable object of `C(D)` is a single object. -/
lemma exists_iso_single_of_isIndecomposable {M : CD D} (hM : IsIndecomposable M) :
    ∃ l : IndCat D, Nonempty (M ≅ single D l) := by
  classical
  rcases isEmpty_or_nonempty M.ι with hι | hne
  · exfalso
    apply hM.1
    rw [IsZero.iff_id_eq_zero]
    ext i
    exact isEmptyElim i
  obtain ⟨i₀⟩ := hne
  let p : M.ι → Bool := fun i => decide (i = i₀)
  let q : M.ι → Bool := fun i => !decide (i = i₀)
  have hdisj : ∀ i, p i = true → q i = true → False := fun i hp hq => by
    simp_all [p, q]
  have hcov : ∀ i, p i = true ∨ q i = true := fun i => by
    by_cases h : i = i₀ <;> simp [p, q, h]
  let iso : M ≅ subObj M p ⊞ subObj M q :=
    isoBiprodOfTotal (subIncl M p) (subIncl M q) (subProj M p) (subProj M q)
      (subIncl_subProj M p) (subIncl_subProj M q) (subIncl_subProj_of_disjoint M p q hdisj)
      (subIncl_subProj_of_disjoint M q p fun i hq hp => hdisj i hp hq)
      (subProj_subIncl_add M p q hcov hdisj)
  let : Unique (subObj M p).ι :=
    { default := ⟨i₀, by simp [p]⟩
      uniq := fun x => Subtype.ext (by simpa [p] using x.2) }
  let e₀ : subObj M p ≅ single D (M.X i₀) := Mat_.isoSingleOfUnique (subObj M p)
  refine ⟨M.X i₀, ?_⟩
  rcases hM.2 _ _ ⟨iso⟩ with hp | hq
  · exact absurd ((IsZero.of_iso hp e₀.symm).eq_of_src _ _) (single_id_ne_zero D _)
  · exact ⟨iso ≪≫ (isoBiprodZero hq).symm ≪≫ e₀⟩

/-! ### The table (4.1) in `C(D)` -/

/-- `E` on single objects is `Ext¹` between the corresponding representations. -/
noncomputable def extSingleEquiv (c a : IndCat D) :
    (cdData D).Ext (single D c) (single D a) ≃ₗ[k] Ext ((rho0 D).obj c) ((rho0 D).obj a) 1 :=
  Ext.linearEquivOfIso (rhoSingleIso D c) (rhoSingleIso D a) 1

lemma rank_zero_of_forall_eq_zero {V : Type*} [AddCommGroup V] [Module k V]
    (h : ∀ v : V, v = 0) : Module.rank k V = 0 :=
  rank_zero_iff.mpr ⟨fun v w => (h v).trans (h w).symm⟩

/-- `Ext¹` between the representations of two labels vanishes unless they form an Ext pair. -/
lemma ext_rho0_eq_zero {c a : IndCat D} (h : ¬ IsExtPair c a)
    (η : Ext ((rho0 D).obj c) ((rho0 D).obj a) 1) : η = 0 := by
  rcases c with _ | c
  · exact Ext.eq_zero_of_isZero_source (isZero_zero _) η
  rcases a with _ | a
  · exact Ext.eq_zero_of_isZero_target (isZero_zero _) η
  rcases a with _ | i | i
  · exact ext_one_Y_eq_zero η
  · rcases c with _ | j | j
    · exact absurd trivial h
    · exact ext_one_A_A_eq_zero i j η
    · exact ext_one_P_A_eq_zero (not_lt.mp h) η
  · exact ext_one_P_eq_zero i η

/-- `E(C, A)` vanishes when no entry of `C` and entry of `A` form an Ext pair. -/
lemma cdExt_eq_zero {C A : CD D} (h : ∀ i j, ¬ IsExtPair (C.X i) (A.X j))
    (ξ : (cdData D).Ext C A) : ξ = 0 :=
  Ext.eq_zero_of_source_biproduct (fun i => (rho0 D).obj (C.X i))
    (fun i η => Ext.eq_zero_of_target_biproduct (fun j => (rho0 D).obj (A.X j))
      (fun j => ext_rho0_eq_zero D (h i j)) η) ξ

open Classical in
/-- **(4.1)**: the only nonzero spaces `E(C, A)` between indecomposables are
`E(Y, A i) ≃ k` and `E(P j, A i) ≃ k` for `j < i`. -/
lemma rank_ext_single (c a : IndCat D) :
    Module.rank k ((cdData D).Ext (single D c) (single D a)) =
      if IsExtPair c a then 1 else 0 := by
  rw [(extSingleEquiv D c a).rank_eq]
  split_ifs with h
  · rcases c with _ | _ | j | j <;> rcases a with _ | _ | i | i <;> try exact h.elim
    · exact rank_eq_one_iff.mpr (ext_one_Y_A i)
    · exact rank_eq_one_iff.mpr (ext_one_P_A h)
  · exact rank_zero_of_forall_eq_zero (ext_rho0_eq_zero D h)

end ExtriangulatedRealization
