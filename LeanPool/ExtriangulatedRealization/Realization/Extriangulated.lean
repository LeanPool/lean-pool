/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Realization.Transfer

/-!
# Corollary 2.4: `C(D)` is extriangulated

Every finite set of objects of `C(D)` lies in `C_J` for `J = Iic m`, and `C_J` has a triangulated
realization built from `W = D_m` with `q_i = π_{mi}` (surjective since the transition maps are).
So each instance of an axiom holds in `C(D)` because it holds in some `C_J`.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Limits Opposite Statement IntervalLabel

universe u

attribute [local instance] HasExt.standard

variable {k : Type u} [Field k] {I : Type u} [LinearOrder I] (D : Iᵒᵖ ⥤ ModuleCat.{u} k)

/-- The realization data `W = D_m`, `q_i = π_{mi}` for `J = Iic m`. -/
noncomputable def iicData (m : I) : RealizationData D (Set.Iic m) where
  W := D.obj (op m)
  q i hi := D.map (homOfLE (show i ≤ m from hi)).op

lemma iicData_isCompatible (hD : HasSurjectiveTransitions D) (m : I) :
    (iicData D m).IsCompatible where
  surj i hi := hD (show i ≤ m from hi)
  comm i j hi hj h := by
    change D.map _ ≫ D.map _ = D.map _
    rw [← D.map_comp]
    rfl

/-- Finitely many objects of `C(D)` lie in some `C_{Iic m}`. -/
lemma exists_labelsIn_Iic [Nonempty I] (L : List (CD D)) :
    ∃ m : I, ∀ M ∈ L, labelsIn D (Set.Iic m) M := by
  classical
  let E : Finset I := L.toFinset.biUnion (objIdx D)
  obtain ⟨m, hm⟩ : ∃ m : I, ∀ e ∈ E, e ≤ m := by
    by_cases hE : E.Nonempty
    · exact ⟨E.max' hE, fun e he => E.le_max' e he⟩
    · exact ⟨Classical.arbitrary I, fun e he => absurd ⟨e, he⟩ hE⟩
  refine ⟨m, fun M hM i => ?_⟩
  have hsub : objIdx D M ⊆ E := Finset.subset_biUnion_of_mem _ (List.mem_toFinset.mpr hM)
  have := labelIn_objIdx D M (E := objIdx D M) subset_rfl i
  rcases h : M.X i with _ | _ | j | j
  · trivial
  · trivial
  all_goals
    rw [h] at this
    exact hm j (hsub this)

variable [WellFoundedLT I] [Nonempty I]

/-- **Corollary 2.4**, the axioms: `C(D)` is an extriangulated category. -/
theorem cdData_isExtriangulated (hD : HasSurjectiveTransitions D) :
    (cdData D).IsExtriangulated where
  push_add a a' δ := cdData_push_add D a a' δ
  push_smul r a δ := cdData_push_smul D r a δ
  pull_add c c' δ := cdData_pull_add D c c' δ
  pull_smul r c δ := cdData_pull_smul D r c δ
  exists_realizes δ := cd_exists_realizes D δ
  realizes_unique {A B B' C δ x y x' y'} h h' := by
    obtain ⟨m, hm⟩ := exists_labelsIn_Iic D [A, B, B', C]
    obtain ⟨b, h₁, h₂⟩ := (iicData D m).realizes_unique (iicData_isCompatible D hD m)
      (A := ⟨A, hm A (by simp)⟩) (B := ⟨B, hm B (by simp)⟩) (B' := ⟨B', hm B' (by simp)⟩)
      (C := ⟨C, hm C (by simp)⟩) (x := ObjectProperty.homMk x) (y := ObjectProperty.homMk y)
      (x' := ObjectProperty.homMk x') (y' := ObjectProperty.homMk y') h h'
    exact ⟨(labelsIn D _).ι.mapIso b, congrArg InducedCategory.Hom.hom h₁,
      congrArg InducedCategory.Hom.hom h₂⟩
  realizes_iso b h := cdData_realizes_iso D b h
  realizes_morphism {A B C A' B' C' δ δ' x y x' y'} h h' a c hac := by
    obtain ⟨m, hm⟩ := exists_labelsIn_Iic D [A, B, C, A', B', C']
    obtain ⟨b, h₁, h₂⟩ := (iicData D m).realizes_morphism (iicData_isCompatible D hD m)
      (A := ⟨A, hm A (by simp)⟩) (B := ⟨B, hm B (by simp)⟩) (C := ⟨C, hm C (by simp)⟩)
      (A' := ⟨A', hm A' (by simp)⟩) (B' := ⟨B', hm B' (by simp)⟩) (C' := ⟨C', hm C' (by simp)⟩)
      (x := ObjectProperty.homMk x) (y := ObjectProperty.homMk y)
      (x' := ObjectProperty.homMk x') (y' := ObjectProperty.homMk y') h h'
      (ObjectProperty.homMk a) (ObjectProperty.homMk c) hac
    exact ⟨b.hom, congrArg InducedCategory.Hom.hom h₁, congrArg InducedCategory.Hom.hom h₂⟩
  realizes_zero A C := by
    obtain ⟨m, hm⟩ := exists_labelsIn_Iic D [A, C]
    exact (iicData D m).realizes_zero (iicData_isCompatible D hD m) ⟨A, hm A (by simp)⟩
      ⟨C, hm C (by simp)⟩
  realizes_sum {A B C A' B' C' δ δ' x y x' y'} h h' := by
    obtain ⟨m, hm⟩ := exists_labelsIn_Iic D [A, B, C, A', B', C']
    exact (iicData D m).realizes_sum (iicData_isCompatible D hD m)
      (A := ⟨A, hm A (by simp)⟩) (B := ⟨B, hm B (by simp)⟩) (C := ⟨C, hm C (by simp)⟩)
      (A' := ⟨A', hm A' (by simp)⟩) (B' := ⟨B', hm B' (by simp)⟩) (C' := ⟨C', hm C' (by simp)⟩)
      (x := ObjectProperty.homMk x) (y := ObjectProperty.homMk y)
      (x' := ObjectProperty.homMk x') (y' := ObjectProperty.homMk y') h h'
  et3 {A B C A' B' C' δ δ' x y x' y'} h h' a b hab := by
    obtain ⟨m, hm⟩ := exists_labelsIn_Iic D [A, B, C, A', B', C']
    obtain ⟨c, h₁, h₂⟩ := (iicData D m).et3 (iicData_isCompatible D hD m)
      (A := ⟨A, hm A (by simp)⟩) (B := ⟨B, hm B (by simp)⟩) (C := ⟨C, hm C (by simp)⟩)
      (A' := ⟨A', hm A' (by simp)⟩) (B' := ⟨B', hm B' (by simp)⟩) (C' := ⟨C', hm C' (by simp)⟩)
      (x := ObjectProperty.homMk x) (y := ObjectProperty.homMk y)
      (x' := ObjectProperty.homMk x') (y' := ObjectProperty.homMk y') h h'
      (ObjectProperty.homMk a) (ObjectProperty.homMk b) (ObjectProperty.hom_ext _ hab)
    exact ⟨c.hom, congrArg InducedCategory.Hom.hom h₁, h₂⟩
  et3_op {A B C A' B' C' δ δ' x y x' y'} h h' b c hbc := by
    obtain ⟨m, hm⟩ := exists_labelsIn_Iic D [A, B, C, A', B', C']
    obtain ⟨a, h₁, h₂⟩ := (iicData D m).et3_op (iicData_isCompatible D hD m)
      (A := ⟨A, hm A (by simp)⟩) (B := ⟨B, hm B (by simp)⟩) (C := ⟨C, hm C (by simp)⟩)
      (A' := ⟨A', hm A' (by simp)⟩) (B' := ⟨B', hm B' (by simp)⟩) (C' := ⟨C', hm C' (by simp)⟩)
      (x := ObjectProperty.homMk x) (y := ObjectProperty.homMk y)
      (x' := ObjectProperty.homMk x') (y' := ObjectProperty.homMk y') h h'
      (ObjectProperty.homMk b) (ObjectProperty.homMk c) (ObjectProperty.hom_ext _ hbc)
    exact ⟨a.hom, congrArg InducedCategory.Hom.hom h₁, h₂⟩
  et4 {A B C D' F f f' g g' δ δ'} h h' := by
    obtain ⟨m, hm⟩ := exists_labelsIn_Iic D [A, B, C, D', F]
    obtain ⟨E, h'', d, e, δ'', h₁, h₂, h₃, h₄, h₅, h₆⟩ := (iicData D m).et4
      (iicData_isCompatible D hD m)
      (A := ⟨A, hm A (by simp)⟩) (B := ⟨B, hm B (by simp)⟩) (C' := ⟨C, hm C (by simp)⟩)
      (D' := ⟨D', hm D' (by simp)⟩) (F' := ⟨F, hm F (by simp)⟩)
      (f := ObjectProperty.homMk f) (f' := ObjectProperty.homMk f')
      (g := ObjectProperty.homMk g) (g' := ObjectProperty.homMk g') h h'
    exact ⟨E.obj, h''.hom, d.hom, e.hom, δ'', h₁, congrArg InducedCategory.Hom.hom h₂,
      congrArg InducedCategory.Hom.hom h₃, h₄, h₅, h₆⟩
  et4_op {D' A B F C f' f g' g δ δ'} h h' := by
    obtain ⟨m, hm⟩ := exists_labelsIn_Iic D [D', A, B, F, C]
    obtain ⟨E, h'', d, e, δ'', h₁, h₂, h₃, h₄, h₅, h₆⟩ := (iicData D m).et4_op
      (iicData_isCompatible D hD m)
      (D' := ⟨D', hm D' (by simp)⟩) (A := ⟨A, hm A (by simp)⟩) (B := ⟨B, hm B (by simp)⟩)
      (F' := ⟨F, hm F (by simp)⟩) (C' := ⟨C, hm C (by simp)⟩)
      (f' := ObjectProperty.homMk f') (f := ObjectProperty.homMk f)
      (g' := ObjectProperty.homMk g') (g := ObjectProperty.homMk g) h h'
    exact ⟨E.obj, h''.hom, d.hom, e.hom, δ'', h₁, congrArg InducedCategory.Hom.hom h₂,
      congrArg InducedCategory.Hom.hom h₃, h₄, h₅, h₆⟩

omit [WellFoundedLT I] [Nonempty I] in
instance subcatJ_isClosedUnderIsomorphisms (J : Set I) :
    (subcatJ D J).IsClosedUnderIsomorphisms := by
  unfold subcatJ
  infer_instance

end ExtriangulatedRealization
