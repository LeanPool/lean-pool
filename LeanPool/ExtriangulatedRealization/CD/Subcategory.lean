/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.CD.Existence

/-!
# The subcategories `C_J` are defined by their labels

`C_J` is the isomorphism closure of the objects of `C(D)` all of whose labels have their index
in `J`. The labels of an object are invariant under isomorphism in the following weak sense,
which is all we need: if `M ≅ N` and every label of `N` lies in `J`, then so does every label of
`M`. Indeed `ρN` is `E`-good for the finite set `E` of indices of `N`, hence so is `ρM`, hence so
is each interval summand of `ρM`, and a good interval has its index in `E`. So `C_J` is exactly
the full subcategory of objects with all labels in `J`.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement IntervalLabel

universe u

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I] (D : Iᵒᵖ ⥤ ModuleCat.{u} k)

/-- The objects of `C(D)` all of whose labels have their index in `J`. -/
def labelsIn (J : Set I) : ObjectProperty (CD D) := fun M => ∀ i, labelIn J (M.X i)

omit [Field k] [LinearOrder I] in
lemma mem_of_mem_labelIdx {J : Set I} {l : Option (IntervalLabel I)} (hl : labelIn J l) {e : I}
    (he : e ∈ labelIdx l) : e ∈ J := by
  rcases l with _ | _ | i | i
  · exact absurd he (Finset.notMem_empty e)
  · exact absurd he (Finset.notMem_empty e)
  · obtain rfl := Finset.mem_singleton.mp he
    exact hl
  · obtain rfl := Finset.mem_singleton.mp he
    exact hl

/-- An object whose image under `ρ` is `E`-good, for a finite `E ⊆ J`, has its labels in `J`. -/
lemma labelsIn_of_isGood {J : Set I} {M : CD D} (E : Finset I) (hEJ : ∀ e ∈ E, e ∈ J)
    (hgood : IsGood E ((rho D).obj M)) : labelsIn D J M := by
  intro i
  have hi : IsGood E ((rho0 D).obj (M.X i)) :=
    IsGood.of_retract E (biproduct.ι (fun j => (rho0 D).obj (M.X j)) i)
      (biproduct.π (fun j => (rho0 D).obj (M.X j)) i) (biproduct.ι_π_self _ _) hgood
  generalize M.X i = l at hi ⊢
  rcases l with _ | l
  · trivial
  · have hl := labelIn_of_isGood E l hi
    rcases l with _ | j | j
    · trivial
    · exact hEJ j hl
    · exact hEJ j hl

lemma mem_of_mem_objIdx {J : Set I} {M : CD D} (hM : labelsIn D J M) {e : I}
    (he : e ∈ objIdx D M) : e ∈ J := by
  obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.mp he
  exact mem_of_mem_labelIdx (hM j) hj

lemma labelsIn_of_retract {J : Set I} {M N : CD D} (r : M ⟶ N) (p : N ⟶ M) (hrp : r ≫ p = 𝟙 M)
    (hN : labelsIn D J N) : labelsIn D J M := by
  refine labelsIn_of_isGood D (objIdx D N) (fun e he => mem_of_mem_objIdx D hN he) ?_
  exact IsGood.of_retract _ ((rho D).map r) ((rho D).map p)
    (by rw [← Functor.map_comp, hrp, CategoryTheory.Functor.map_id])
    (isGood_rho D _ N (labelIn_objIdx D N subset_rfl))

lemma labelsIn_of_iso {J : Set I} {M N : CD D} (e : M ≅ N) (hN : labelsIn D J N) :
    labelsIn D J M :=
  labelsIn_of_retract D e.hom e.inv e.hom_inv_id hN

/-- `C_J` is the full subcategory of objects all of whose labels lie in `J`. -/
lemma subcatJ_eq_labelsIn (J : Set I) : subcatJ D J = labelsIn D J := by
  ext M
  constructor
  · rintro ⟨N, hN, ⟨e⟩⟩
    exact labelsIn_of_iso D e hN
  · intro h
    exact ObjectProperty.le_isoClosure _ _ h


/-- If countable sets of indices are bounded, every countable family of objects has its labels in
some initial segment `Iic m`. -/
lemma exists_labelsIn_Iic_of_countable (hI : ∀ T : Set I, T.Countable → BddAbove T)
    {S : Set (CD D)} (hS : S.Countable) : ∃ m : I, ∀ M ∈ S, labelsIn D (Set.Iic m) M := by
  classical
  let T : Set I := ⋃ M ∈ S, (objIdx D M : Set I)
  have hT : T.Countable := hS.biUnion fun M _ => (objIdx D M).countable_toSet
  obtain ⟨m, hm⟩ := hI T hT
  refine ⟨m, fun M hM i => ?_⟩
  have hsub : labelIdx (M.X i) ⊆ objIdx D M :=
    Finset.subset_biUnion_of_mem (fun i => labelIdx (M.X i)) (Finset.mem_univ i)
  have hmem : ∀ j ∈ labelIdx (M.X i), j ≤ m := fun j hj =>
    hm (Set.mem_biUnion hM (Finset.mem_coe.mpr (hsub hj)))
  rcases h : M.X i with _ | _ | j | j
  · trivial
  · trivial
  · exact hmem j (by rw [h]; simp [labelIdx])
  · exact hmem j (by rw [h]; simp [labelIdx])

end ExtriangulatedRealization
