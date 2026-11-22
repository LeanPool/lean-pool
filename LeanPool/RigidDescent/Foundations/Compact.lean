/-
Copyright (c) 2026 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
module

public import LeanPool.RigidDescent.Defs.Setting
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.Tactic.Lemma
public import Mathlib.Tactic.TypeStar

/-!
# Compact objects

Paper, §1 and Conventions: facts about compact objects used throughout.

* `isCompactObj_iff`: `K` is compact if and only if every map `K ⟶ ∐ Yⱼ` is a finite sum of
  maps `K ⟶ Yⱼ` followed by the inclusions (`IsFiniteSum`). The proof uses that in
  `AddCommGrpCat` the images of the inclusions of a coproduct generate it
  (`AddCommGrpCat.exists_eq_sum_of_isColimit`): the quotient by the subgroup they generate is
  killed by every inclusion, so it is zero by the universal property.
* Compact objects are closed under isomorphisms and retracts, shifts, finite sums, and the
  two-out-of-three property for distinguished triangles.
-/

@[expose] public section

open CategoryTheory Limits Opposite Pretriangulated

universe v u

namespace RigidDescent

/-- Merging two finite sums of images of additive maps into one sum over the union. -/
lemma sum_add_sum_eq_sum_union {J : Type*} [DecidableEq J] {M : J → Type*}
    [∀ j, AddCommGroup (M j)] {N : Type*} [AddCommGroup N] (g : ∀ j, M j →+ N)
    (F F' : Finset J) (a a' : ∀ j, M j) :
    ∑ j ∈ F, g j (a j) + ∑ j ∈ F', g j (a' j) =
      ∑ j ∈ F ∪ F', g j ((if j ∈ F then a j else 0) + (if j ∈ F' then a' j else 0)) := by
  simp only [map_add, Finset.sum_add_distrib, apply_ite (g _), map_zero]
  rw [Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.union_inter_cancel_left,
    Finset.union_inter_cancel_right]

/-- In `AddCommGrpCat`, the images of the inclusions of a coproduct generate it: every element
is a finite sum of elements of the summands. -/
lemma AddCommGrpCat.exists_eq_sum_of_isColimit {J : Type*} {A : J → AddCommGrpCat.{v}}
    {c : Cofan A} (hc : IsColimit c) (x : c.pt) :
    ∃ (F : Finset J) (a : ∀ j, A j), x = ∑ j ∈ F, c.inj j (a j) := by
  classical
  let N : AddSubgroup c.pt :=
    { carrier := {x | ∃ (F : Finset J) (a : ∀ j, A j), x = ∑ j ∈ F, c.inj j (a j)}
      add_mem' := by
        rintro _ _ ⟨F, a, rfl⟩ ⟨F', a', rfl⟩
        exact ⟨F ∪ F', _, sum_add_sum_eq_sum_union (fun j => (c.inj j).hom) F F' a a'⟩
      zero_mem' := ⟨∅, 0, by simp⟩
      neg_mem' := by
        rintro _ ⟨F, a, rfl⟩
        exact ⟨F, -a, by simp [Finset.sum_neg_distrib]⟩ }
  let q : c.pt ⟶ AddCommGrpCat.of (c.pt ⧸ N) := AddCommGrpCat.ofHom (QuotientAddGroup.mk' N)
  have hq : q = 0 := Cofan.IsColimit.hom_ext hc _ _ fun j => by
    ext a
    simp only [q, AddCommGrpCat.hom_comp, AddCommGrpCat.hom_ofHom, AddMonoidHom.coe_comp,
      Function.comp_apply, QuotientAddGroup.mk'_apply, Limits.comp_zero,
      AddCommGrpCat.hom_zero, AddMonoidHom.zero_apply, QuotientAddGroup.eq_zero_iff]
    exact ⟨{j}, Pi.single j a, by simp⟩
  have : q x = 0 := by rw [hq]; rfl
  exact (QuotientAddGroup.eq_zero_iff x).mp this

variable {T : Type u} [Category.{v} T] [Preadditive T]

section FiniteSum

variable {J : Type*} {Y : J → T} [HasCoproduct Y] {K : T}

/-- A map `k : K ⟶ ∐ Y` is a *finite sum*: `k = ∑_{j ∈ F} a_j ≫ ι_j` for a finite set `F` of
indices and maps `a_j : K ⟶ Y_j`. -/
def IsFiniteSum (k : K ⟶ ∐ Y) : Prop :=
  ∃ (F : Finset J) (a : ∀ j, K ⟶ Y j), k = ∑ j ∈ F, a j ≫ Sigma.ι Y j

lemma IsFiniteSum.zero : IsFiniteSum (0 : K ⟶ ∐ Y) := ⟨∅, 0, by simp⟩

lemma IsFiniteSum.add {k k' : K ⟶ ∐ Y} (h : IsFiniteSum k) (h' : IsFiniteSum k') :
    IsFiniteSum (k + k') := by
  classical
  obtain ⟨F, a, rfl⟩ := h
  obtain ⟨F', a', rfl⟩ := h'
  exact ⟨F ∪ F', _, sum_add_sum_eq_sum_union
    (fun j => Preadditive.rightComp K (Sigma.ι Y j)) F F' a a'⟩

lemma IsFiniteSum.precomp {K' : T} (x : K' ⟶ K) {k : K ⟶ ∐ Y} (h : IsFiniteSum k) :
    IsFiniteSum (x ≫ k) := by
  obtain ⟨F, a, rfl⟩ := h
  exact ⟨F, fun j => x ≫ a j, by simp [Preadditive.comp_sum]⟩

/-- The components of a finite sum are recovered by the projections `Sigma.π`. -/
lemma sum_comp_sigmaπ [DecidableEq J] (F : Finset J) (a : ∀ j, K ⟶ Y j) (i : J) :
    (∑ j ∈ F, a j ≫ Sigma.ι Y j) ≫ Sigma.π Y i = if i ∈ F then a i else 0 := by
  rw [Preadditive.sum_comp]
  split_ifs with hi
  · rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [Sigma.ι_π_of_ne _ hj]
    · intro h; exact absurd hi h
  · refine Finset.sum_eq_zero fun j hj => ?_
    have : j ≠ i := fun h => hi (h ▸ hj)
    simp [Sigma.ι_π_of_ne _ this]

end FiniteSum

section Criterion

variable [HasCoproducts.{v} T]

omit [HasCoproducts.{v} T] in
/-- A map from a compact object into a coproduct indexed by a `v`-small type is a finite
sum. -/
lemma IsCompactObj.isFiniteSum_of_small {K : T} (hK : IsCompactObj K) {J : Type*}
    [Small.{v} J] {Y : J → T} [HasCoproduct Y] (k : K ⟶ ∐ Y) : IsFiniteSum k := by
  have := hK (Shrink.{v} J)
  have : PreservesColimitsOfShape (Discrete J) (preadditiveCoyoneda.obj (op K)) :=
    preservesColimitsOfShape_of_equiv (Discrete.equivalence (equivShrink J).symm) _
  obtain ⟨F, a, h⟩ := AddCommGrpCat.exists_eq_sum_of_isColimit
    (isColimitOfHasCoproductOfPreservesColimit (preadditiveCoyoneda.obj (op K)) Y) k
  exact ⟨F, a, h⟩

/-- A map from a compact object into a coproduct is a finite sum. -/
lemma IsCompactObj.isFiniteSum {K : T} (hK : IsCompactObj K) {J : Type v} {Y : J → T}
    (k : K ⟶ ∐ Y) : IsFiniteSum k :=
  hK.isFiniteSum_of_small k

/-- An object is compact if and only if every map from it into a coproduct is a finite sum. -/
theorem isCompactObj_iff {K : T} :
    IsCompactObj K ↔ ∀ (J : Type v) (Y : J → T) (k : K ⟶ ∐ Y), IsFiniteSum k := by
  refine ⟨fun hK J Y k => hK.isFiniteSum k, fun h J => ?_⟩
  classical
  have : ∀ Y : J → T, PreservesColimit (Discrete.functor Y) (preadditiveCoyoneda.obj (op K)) := by
    intro Y
    let G := preadditiveCoyoneda.obj (op K)
    have hι : ∀ (j : J) (a : K ⟶ Y j),
        sigmaComparison G Y (Sigma.ι (fun j => G.obj (Y j)) j a) = a ≫ Sigma.ι Y j := by
      intro j a
      change (Sigma.ι (fun j => G.obj (Y j)) j ≫ sigmaComparison G Y) a = _
      rw [ι_comp_sigmaComparison]
      rfl
    have : IsIso (sigmaComparison G Y) := by
      rw [ConcreteCategory.isIso_iff_bijective]
      constructor
      · rw [injective_iff_map_eq_zero]
        intro x hx
        obtain ⟨F, a, rfl⟩ := AddCommGrpCat.exists_eq_sum_of_isColimit
          (colimit.isColimit (Discrete.functor fun j => G.obj (Y j))) x
        let a' : ∀ j, K ⟶ Y j := a
        rw [map_sum] at hx
        have hx' : ∑ j ∈ F, a' j ≫ Sigma.ι Y j = 0 :=
          (Finset.sum_congr rfl fun j _ => (hι j (a j)).symm).trans hx
        have ha : ∀ i ∈ F, a' i = 0 := by
          intro i hi
          have := congrArg (· ≫ Sigma.π Y i) hx'
          simpa [sum_comp_sigmaπ, hi] using this
        exact Finset.sum_eq_zero fun i hi => by
          change Sigma.ι (fun j => G.obj (Y j)) i (a' i) = 0
          rw [ha i hi]
          exact map_zero _
      · intro k
        obtain ⟨F, a, rfl⟩ := h J Y k
        exact ⟨∑ j ∈ F, Sigma.ι (fun j => G.obj (Y j)) j (a j), by
          rw [map_sum]; exact Finset.sum_congr rfl fun j _ => hι j (a j)⟩
    exact PreservesCoproduct.of_iso_comparison G Y
  exact preservesColimitsOfShape_of_discrete _

/-- Compact objects are closed under retracts. -/
lemma IsCompactObj.of_retract {K K' : T} (hK' : IsCompactObj K') (i : K ⟶ K') (r : K' ⟶ K)
    (h : i ≫ r = 𝟙 K) : IsCompactObj K := by
  rw [isCompactObj_iff] at hK' ⊢
  intro J Y k
  have := (hK' J Y (r ≫ k)).precomp i
  rwa [← Category.assoc, h, Category.id_comp] at this

/-- Compact objects are closed under isomorphisms. -/
lemma IsCompactObj.of_iso {K K' : T} (hK : IsCompactObj K) (e : K' ≅ K) : IsCompactObj K' :=
  hK.of_retract e.hom e.inv e.hom_inv_id

/-- Zero objects are compact. -/
lemma isCompactObj_of_isZero {K : T} (hK : IsZero K) : IsCompactObj K := by
  rw [isCompactObj_iff]
  intro J Y k
  rw [hK.eq_of_src k 0]
  exact IsFiniteSum.zero

variable [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive]

/-- Compact objects are closed under shifts. -/
lemma IsCompactObj.shift {K : T} (hK : IsCompactObj K) (n : ℤ) : IsCompactObj (K⟦n⟧) := by
  rw [isCompactObj_iff]
  intro J Y k
  let G := shiftFunctor T (-n)
  obtain ⟨F, a, ha⟩ := hK.isFiniteSum
    ((shiftShiftNeg K n).inv ≫ G.map k ≫ (PreservesCoproduct.iso G Y).hom)
  have hk : G.map k = (shiftShiftNeg K n).hom ≫ ∑ j ∈ F, a j ≫ G.map (Sigma.ι Y j) := by
    have e : G.map k = (shiftShiftNeg K n).hom ≫ ((shiftShiftNeg K n).inv ≫ G.map k ≫
        (PreservesCoproduct.iso G Y).hom) ≫ (PreservesCoproduct.iso G Y).inv := by
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.hom_inv_id_assoc]
    rw [e, ha, Preadditive.sum_comp]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Category.assoc, PreservesCoproduct.inv_hom, ι_comp_sigmaComparison]
  choose b hb using fun j => G.map_surjective ((shiftShiftNeg K n).hom ≫ a j)
  refine ⟨F, b, G.map_injective ?_⟩
  rw [hk, Functor.map_sum, Preadditive.comp_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [G.map_comp, hb, Category.assoc]

variable [HasZeroObject T] [Pretriangulated T]

/-- In a distinguished triangle `X₁ → X₂ → X₃ → X₁⟦1⟧`, if `X₂` and `X₁⟦1⟧` are compact,
so is `X₃`. -/
lemma isCompactObj₃_of_distTriang (Tr : Triangle T) (hTr : Tr ∈ distTriang T)
    (h₂ : IsCompactObj Tr.obj₂) (h₁ : IsCompactObj (Tr.obj₁⟦(1 : ℤ)⟧)) :
    IsCompactObj Tr.obj₃ := by
  classical
  rw [isCompactObj_iff]
  intro J Y k
  obtain ⟨F, a, ha⟩ := h₂.isFiniteSum (Tr.mor₂ ≫ k)
  have hb : ∀ i, ∃ b : Tr.obj₃ ⟶ Y i, i ∈ F → a i = Tr.mor₂ ≫ b := by
    intro i
    by_cases hi : i ∈ F
    · have : Tr.mor₁ ≫ a i = 0 := by
        have := congrArg (fun x => Tr.mor₁ ≫ x ≫ Sigma.π Y i) ha
        simp only [sum_comp_sigmaπ, hi, ↓reduceIte] at this
        rw [← this, ← Category.assoc, ← Category.assoc, comp_distTriang_mor_zero₁₂ _ hTr]
        simp
      obtain ⟨b, hb⟩ := Triangle.yoneda_exact₂ Tr hTr (a i) this
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun h => absurd h hi⟩
  choose b hb using hb
  have hk : Tr.mor₂ ≫ (k - ∑ j ∈ F, b j ≫ Sigma.ι Y j) = 0 := by
    rw [Preadditive.comp_sub, ha, Preadditive.comp_sum, sub_eq_zero]
    exact Finset.sum_congr rfl fun j hj => by rw [hb j hj, Category.assoc]
  obtain ⟨c, hc⟩ := Triangle.yoneda_exact₃ Tr hTr _ hk
  have := ((h₁.isFiniteSum c).precomp Tr.mor₃).add ⟨F, b, rfl⟩
  rwa [← hc, sub_add_cancel] at this

/-- In a distinguished triangle `X₁ → X₂ → X₃ → X₁⟦1⟧`, if `X₁` and `X₃` are compact, so
is `X₂`. -/
lemma isCompactObj₂_of_distTriang (Tr : Triangle T) (hTr : Tr ∈ distTriang T)
    (h₁ : IsCompactObj Tr.obj₁) (h₃ : IsCompactObj Tr.obj₃) : IsCompactObj Tr.obj₂ :=
  isCompactObj₃_of_distTriang _ (inv_rot_of_distTriang _ hTr) h₁
    ((h₃.shift (-1)).shift 1)

/-- In a distinguished triangle `X₁ → X₂ → X₃ → X₁⟦1⟧`, if `X₂` and `X₃` are compact, so
is `X₁`. -/
lemma isCompactObj₁_of_distTriang (Tr : Triangle T) (hTr : Tr ∈ distTriang T)
    (h₂ : IsCompactObj Tr.obj₂) (h₃ : IsCompactObj Tr.obj₃) : IsCompactObj Tr.obj₁ :=
  isCompactObj₂_of_distTriang _ (inv_rot_of_distTriang _ hTr) (h₃.shift (-1)) h₂

/-- Compact objects are closed under binary biproducts. -/
lemma IsCompactObj.biprod {K₁ K₂ : T} (h₁ : IsCompactObj K₁) (h₂ : IsCompactObj K₂) :
    IsCompactObj (K₁ ⊞ K₂) :=
  isCompactObj₂_of_distTriang _ (binaryBiproductTriangle_distinguished K₁ K₂) h₁ h₂

end Criterion

end RigidDescent
