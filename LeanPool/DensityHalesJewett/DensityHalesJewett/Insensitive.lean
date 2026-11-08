/-
Copyright (c) 2026 Gabriel Dahia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Dahia
-/
module

public import LeanPool.DensityHalesJewett.DensityHalesJewett.UniformFibers
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.NNRat.BigOperators

/-!
# Insensitive word families and tilings

Boolean closure of insensitive families and the subspace-tiling results used in the density
increment argument.
-/

@[expose] public section

open Finset
open Combinatorics
open scoped BigOperators

namespace DensityHalesJewett

/-- Two words are equivalent after freely interchanging the letters `i` and `j`. -/
def InsensitiveEquiv {α ι : Type*} (i j : α) (x y : ι → α) : Prop :=
  ∀ a, a ≠ i → a ≠ j → ∀ c, (x c = a ↔ y c = a)

/-- Membership in an `(i,j)`-insensitive family is constant on insensitive-equivalence classes. -/
def IsInsensitive {α ι : Type*} (i j : α) (D : Finset (ι → α)) : Prop :=
  ∀ ⦃x y⦄, InsensitiveEquiv i j x y → (x ∈ D ↔ y ∈ D)

/-- Transport a word family along an equivalence of coordinate types. -/
def transportWords {α ι ι' : Type*}
    (e : ι ≃ ι') (D : Finset (ι → α)) : Finset (ι' → α) :=
  D.map ((e.arrowCongr (Equiv.refl α)).toEmbedding)

@[simp]
lemma mem_transportWords {α ι ι' : Type*}
    {e : ι ≃ ι'} {D : Finset (ι → α)} {w : ι' → α} :
    w ∈ transportWords e D ↔ w ∘ e ∈ D := by
  rw [transportWords, mem_map_equiv]
  rfl

@[simp]
lemma dens_transportWords {α ι ι' : Type*} [Fintype (ι → α)] [Fintype (ι' → α)]
    (e : ι ≃ ι') (D : Finset (ι → α)) : (transportWords e D).dens = D.dens := by
  rw [transportWords, dens_map_equiv]

/-- Intersecting a family with a subspace range factors its ambient density into relative density
and range density. -/
lemma Subspace.dens_inter_range {η α ι : Type*} [Fintype (η → α)] [Fintype (ι → α)]
    [DecidableEq (ι → α)] (W : Combinatorics.Subspace η α ι) (A : Finset (ι → α)) :
    ((A ∩ range W).dens : ℝ) = (relativeDensity W A : ℝ) * ((range W).dens : ℝ) := by
  classical
  have hA : A ∩ range W = (univ.filter fun x ↦ W x ∈ A).image W := by
    ext w
    simp only [range, mem_inter, mem_image, mem_filter, mem_univ, true_and]
    grind
  rw [hA, relativeDensity, nnratCast_dens (range W), range,
    card_image_of_injective _ (Subspace.injective W), card_univ, ← mul_div_assoc,
    nnratCast_dens_mul_natCast_card, nnratCast_dens,
    card_image_of_injective _ (Subspace.injective W)]

namespace IsInsensitive

/-- Reindexing coordinates preserves insensitivity. -/
lemma reindex {α ι ι' : Type*}
    {i j : α} {D : Finset (ι → α)} (e : ι ≃ ι') (hD : IsInsensitive i j D) :
    IsInsensitive i j (DensityHalesJewett.transportWords e D) := by
  intro x y hxy
  simp only [mem_transportWords]
  apply hD
  intro a hai haj c
  exact hxy a hai haj (e c)

/-- Fixing a prefix of coordinates preserves insensitivity of the remaining section. -/
lemma fiberSection {α ι κ : Type*} [Fintype (κ → α)] [DecidableEq (ι ⊕ κ → α)]
    {i j : α} {D : Finset (ι ⊕ κ → α)} (hD : IsInsensitive i j D) (v : ι → α) :
    IsInsensitive i j (DensityHalesJewett.fiber D v) := by
  intro x y hxy
  simp only [mem_fiber]
  apply hD
  intro a hai haj c
  cases c with
  | inl c => simp only [Sum.elim_inl]
  | inr c => exact hxy a hai haj c

/-- Complements preserve insensitivity. -/
lemma compl {α ι : Type*} [Fintype (ι → α)] [DecidableEq (ι → α)]
    {i j : α} {D : Finset (ι → α)} (hD : IsInsensitive i j D) :
    IsInsensitive i j Dᶜ := by
  intro x y hxy
  simp only [mem_compl, hD hxy]

/-- The part of `D` left uncovered by a set of subspaces. -/
noncomputable def uncovered {η α ι : Type*} [Fintype (η → α)]
    [DecidableEq (ι → α)] (D : Finset (ι → α))
    (𝒱 : Set (Combinatorics.Subspace η α ι)) : Finset (ι → α) := by
  classical
  exact D.filter fun w ↦ ∀ V ∈ 𝒱, w ∉ Subspace.range V

@[simp]
lemma mem_uncovered {η α ι : Type*} [Fintype (η → α)] [DecidableEq (ι → α)]
    {D : Finset (ι → α)} {𝒱 : Set (Combinatorics.Subspace η α ι)} {w : ι → α} :
    w ∈ uncovered D 𝒱 ↔ w ∈ D ∧ ∀ V ∈ 𝒱, w ∉ Subspace.range V := by
  simp [uncovered]

@[simp]
lemma uncovered_empty {η α ι : Type*} [Fintype (η → α)] [DecidableEq (ι → α)]
    (D : Finset (ι → α)) :
    uncovered D (∅ : Set (Combinatorics.Subspace η α ι)) = D := by
  ext w
  simp

/-- Placing two sets of subspaces one after the other leaves the same part uncovered as placing
both at once. -/
lemma uncovered_union {η α ι : Type*} [Fintype (η → α)] [DecidableEq (ι → α)]
    (D : Finset (ι → α)) (𝒱 𝒲 : Set (Combinatorics.Subspace η α ι)) :
    uncovered D (𝒱 ∪ 𝒲) = uncovered (uncovered D 𝒱) 𝒲 := by
  ext w
  simp [or_imp, forall_and, and_assoc]

/-- The intersection of a finite indexed family of finite sets. -/
noncomputable def intersection {r : ℕ} {X : Type*} [Fintype X]
    (D : Fin r → Finset X) : Finset X := by
  classical
  exact univ.inf D

@[simp]
lemma mem_intersection {r : ℕ} {X : Type*} [Fintype X]
    {D : Fin r → Finset X} {x : X} :
    x ∈ intersection D ↔ ∀ i, x ∈ D i := by
  simp [intersection, ← singleton_subset_iff, Finset.le_inf_iff]

/-- Splitting off the last family of an intersection. -/
lemma intersection_eq_inter_last {r : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (D : Fin (r + 1) → Finset X) :
    intersection D = intersection (fun i ↦ D i.castSucc) ∩ D (Fin.last r) := by
  ext x
  simp [Fin.forall_fin_succ']

/-- `𝒱` is a tiling of part of `D`: a finite family of pairwise disjoint subspaces, all contained
in `D`. -/
structure IsTiling {η α ι : Type*} [Fintype (η → α)] [DecidableEq (ι → α)]
    (𝒱 : Set (Combinatorics.Subspace η α ι)) (D : Finset (ι → α)) : Prop where
  finite : 𝒱.Finite
  isContained : ∀ V ∈ 𝒱, Subspace.IsContained V D
  pairwiseDisjoint : 𝒱.PairwiseDisjoint fun V ↦ (Subspace.range V : Set (ι → α))

namespace IsTiling

variable {η α ι : Type*} [Fintype (η → α)] [DecidableEq (ι → α)] {D : Finset (ι → α)}
  {𝒱 𝒲 : Set (Combinatorics.Subspace η α ι)}

lemma empty : IsTiling (∅ : Set (Combinatorics.Subspace η α ι)) D :=
  ⟨Set.finite_empty, by simp, Set.pairwiseDisjoint_empty⟩

/-- A tiling of part of `D`, together with a tiling of part of what it leaves uncovered, is a
tiling of part of `D`. -/
lemma union (h𝒱 : IsTiling 𝒱 D) (h𝒲 : IsTiling 𝒲 (uncovered D 𝒱)) :
    IsTiling (𝒱 ∪ 𝒲) D where
  finite := h𝒱.finite.union h𝒲.finite
  isContained := by
    rintro V (hV | hV) x
    · exact h𝒱.isContained V hV x
    · exact (mem_uncovered.1 (h𝒲.isContained V hV x)).1
  pairwiseDisjoint := by
    refine h𝒱.pairwiseDisjoint.union h𝒲.pairwiseDisjoint ?_
    intro V hV W hW _
    rw [Set.disjoint_left]
    intro w hwV hwW
    obtain ⟨x, rfl⟩ := Subspace.mem_range.1 hwW
    exact (mem_uncovered.1 (h𝒲.isContained W hW x)).2 V hV hwV

/-- The part of `D` covered by a tiling is the union of its subspaces. -/
lemma sdiff_uncovered_eq_biUnion (h : IsTiling 𝒱 D) :
    D \ uncovered D 𝒱 = h.finite.toFinset.biUnion Subspace.range := by
  ext x
  simp only [mem_sdiff, mem_uncovered, mem_biUnion, Set.Finite.mem_toFinset, Subspace.mem_range,
    not_and, not_forall, not_not, exists_prop]
  constructor
  · rintro ⟨hx, hcovered⟩
    exact hcovered hx
  · rintro ⟨V, hV, y, rfl⟩
    exact ⟨h.isContained V hV y, fun _ ↦ ⟨V, hV, y, rfl⟩⟩

/-- The subspaces of a tiling split every family along the part of `D` they cover. -/
lemma sum_dens_inter_range [Fintype (ι → α)] (h : IsTiling 𝒱 D) (B : Finset (ι → α)) :
    ∑ W ∈ h.finite.toFinset, ((B ∩ Subspace.range W).dens : ℝ) =
      ((B ∩ (D \ uncovered D 𝒱)).dens : ℝ) := by
  rw [h.sdiff_uncovered_eq_biUnion, inter_biUnion, dens_biUnion, NNRat.cast_sum]
  intro V hV W hW hVW
  exact (disjoint_coe.1 (h.pairwiseDisjoint (by simpa using hV) (by simpa using hW) hVW)).mono
    inter_subset_right inter_subset_right

/-- If `A` has density at least `ε` relative to the nonempty part of `D` covered by a tiling, then
it has relative density at least `ε` in one of its subspaces. -/
lemma exists_le_relativeDensity [Fintype (ι → α)] [Nonempty α] (h : IsTiling 𝒱 D)
    {A : Finset (ι → α)} {ε : ℝ}
    (hne : (D \ uncovered D 𝒱).Nonempty)
    (hA : ε * ((D \ uncovered D 𝒱).dens : ℝ) ≤ ((A ∩ (D \ uncovered D 𝒱)).dens : ℝ)) :
    ∃ W ∈ 𝒱, ε ≤ (Subspace.relativeDensity W A : ℝ) := by
  have hD := h.sum_dens_inter_range univ
  simp only [univ_inter] at hD
  rw [← hD, ← h.sum_dens_inter_range A, mul_sum] at hA
  obtain ⟨V, hV, -⟩ := biUnion_nonempty.1 (h.sdiff_uncovered_eq_biUnion ▸ hne)
  obtain ⟨W, hW, hle⟩ := exists_le_of_sum_le ⟨V, hV⟩ hA
  rw [Subspace.dens_inter_range] at hle
  exact ⟨W, by simpa using hW, le_of_mul_le_mul_right hle
    (mod_cast dens_pos.2 ⟨_, Subspace.mem_range.2 ⟨Classical.arbitrary _, rfl⟩⟩)⟩

end IsTiling

/-- An ambient dimension is sufficient for tiling one-pair insensitive families: each of them has a
tiling by `m`-dimensional subspaces leaving density less than `2 * β` uncovered. -/
def TilingSufficient (k m : ℕ) (β : ℝ) (n : ℕ) : Prop :=
  ∀ i : Fin k, ∀ D : Finset (Fin n → Fin (k + 1)), IsInsensitive i.castSucc (Fin.last k) D →
    ∃ 𝒱 : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)),
      IsTiling 𝒱 D ∧ ((uncovered D 𝒱).dens : ℝ) < 2 * β

/-- Differences preserve insensitivity. -/
lemma sdiff {α ι : Type*} [DecidableEq (ι → α)]
    {i j : α} {D E : Finset (ι → α)} (hD : IsInsensitive i j D)
    (hE : IsInsensitive i j E) : IsInsensitive i j (D \ E) := by
  intro x y hxy
  simp [hD hxy, hE hxy]

/-- Insensitive-equivalent prefixes have the same section. -/
lemma fiber_congr {α ι κ : Type*} [Fintype (κ → α)] [DecidableEq (ι ⊕ κ → α)]
    {i j : α} {D : Finset (ι ⊕ κ → α)} (hD : IsInsensitive i j D) {v w : ι → α}
    (hvw : InsensitiveEquiv i j v w) :
    DensityHalesJewett.fiber D v = DensityHalesJewett.fiber D w := by
  ext y
  simp only [mem_fiber]
  apply hD
  intro a hai haj c
  cases c with
  | inl c => exact hvw a hai haj c
  | inr c => simp only [Sum.elim_inr]

end IsInsensitive

/-- Regroup the coordinates `ω ⊕ ν` as `(ω ⊕ ν₁) ⊕ ν₂` along a splitting `s : ν ≃ ν₁ ⊕ ν₂`. -/
private def regroup {ι ω ν ν₁ ν₂ : Type*} (e : ι ≃ ω ⊕ ν) (s : ν ≃ ν₁ ⊕ ν₂) :
    ι ≃ (ω ⊕ ν₁) ⊕ ν₂ :=
  e.trans (((Equiv.refl ω).sumCongr s).trans (Equiv.sumAssoc ω ν₁ ν₂).symm)

private lemma concat_comp_regroup {α ι ω ν ν₁ ν₂ : Type*} (e : ι ≃ ω ⊕ ν) (s : ν ≃ ν₁ ⊕ ν₂)
    (u : ω → α) (r : ν₁ → α) (x : ν₂ → α) :
    Sum.elim (Sum.elim u r) x ∘ regroup e s = Sum.elim u (Sum.elim r x ∘ s) ∘ e := by
  funext c
  simp only [regroup, Function.comp_apply, Equiv.trans_apply]
  cases e c with
  | inl a => simp [Equiv.sumAssoc]
  | inr n => cases hn : s n <;> simp [Equiv.sumAssoc, hn]

/-- Sections over the outer coordinates and a first block are sections of sections. -/
private lemma fiber_transportWords_regroup {α ι ω ν ν₁ ν₂ : Type*}
    [Fintype α] [DecidableEq α] [Fintype ω]
    [Fintype ν] [DecidableEq ν] [Fintype ν₁] [Fintype ν₂] [DecidableEq ν₂]
    (e : ι ≃ ω ⊕ ν) (s : ν ≃ ν₁ ⊕ ν₂) (U : Finset (ι → α)) (u : ω → α) (r : ν₁ → α) :
    DensityHalesJewett.fiber (transportWords (regroup e s) U) (Sum.elim u r) =
      DensityHalesJewett.fiber
        (transportWords s (DensityHalesJewett.fiber (transportWords e U) u)) r := by
  ext x
  simp only [mem_fiber, mem_transportWords, concat_comp_regroup]

/-- Moving the last block into the outer coordinates exchanges the roles of the two blocks. -/
private lemma mem_fiber_regroup_sumComm {α ι ω ν ν₁ ν₂ : Type*}
    [Fintype α] [DecidableEq α] [Fintype ω] [Fintype ν₁] [DecidableEq ν₁] [Fintype ν₂]
    [DecidableEq ν₂]
    (e : ι ≃ ω ⊕ ν) (s : ν ≃ ν₁ ⊕ ν₂) (X : Finset (ι → α)) (u : ω → α) (y : ν₁ → α)
    (x : ν₂ → α) :
    y ∈ DensityHalesJewett.fiber
        (transportWords (regroup e (s.trans (Equiv.sumComm ν₁ ν₂))) X) (Sum.elim u x) ↔
      x ∈ DensityHalesJewett.fiber (transportWords (regroup e s) X) (Sum.elim u y) := by
  have hswap : Sum.elim x y ∘ s.trans (Equiv.sumComm ν₁ ν₂) = Sum.elim y x ∘ s := by
    funext c
    simp only [Function.comp_apply, Equiv.trans_apply]
    cases s c <;> rfl
  simp only [mem_fiber, mem_transportWords, concat_comp_regroup, hswap]

/-- Sections commute with set difference. -/
private lemma fiber_transportWords_sdiff {α ι ω ν : Type*}
    [Fintype α] [DecidableEq α] [Fintype ι] [Fintype ω]
    [Fintype ν] [DecidableEq ν]
    (e : ι ≃ ω ⊕ ν) (A B : Finset (ι → α)) (v : ω → α) :
    DensityHalesJewett.fiber (transportWords e (A \ B)) v =
      DensityHalesJewett.fiber (transportWords e A) v \
        DensityHalesJewett.fiber (transportWords e B) v := by
  ext y
  simp only [mem_sdiff, mem_fiber, mem_transportWords]

/-- Removing a subset from a family subtracts its density. -/
private lemma dens_sdiff_of_subset {X : Type*} [Fintype X] [DecidableEq X] {A B : Finset X}
    (h : B ⊆ A) : (((A \ B).dens : ℝ)) = (A.dens : ℝ) - (B.dens : ℝ) := by
  push_cast [← dens_sdiff_add_dens_eq_dens h]
  ring

/-- A nonempty family occupies at least one point of the ambient cube. -/
private lemma one_div_card_le_dens {X : Type*} [Fintype X] {A : Finset X} (h : A.Nonempty) :
    1 / (Fintype.card X : ℝ) ≤ (A.dens : ℝ) := by
  rw [nnratCast_dens]
  gcongr
  exact_mod_cast h.card_pos

/-- An insensitive family that is dense in a large enough block contains a full subspace: the
restricted-alphabet subspace lemma gives the `Fin k`-restricted range, and insensitivity
extends containment to the whole parameter cube. -/
lemma exists_isContained_of_insensitive {k m b : ℕ} {F : ℝ → ℕ} (hF : IsDHJBound k F)
    (hm : 1 ≤ m) {i : Fin k} {β : ℝ} (hβ : 0 < β)
    (hb : Subspace.restrictAlphabetBound k F m β ≤ b)
    {E : Finset (Fin b → Fin (k + 1))}
    (hE : IsInsensitive i.castSucc (Fin.last k) E) (hdens : β ≤ (E.dens : ℝ)) :
    ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin b), Subspace.IsContained V E := by
  obtain ⟨V, hV⟩ :=
    Subspace.exists_restrictAlphabet_subset i.pos hF hm hβ hb
      (by exact_mod_cast Subspace.card_le_of_density_le (Nat.succ_pos k) hdens)
  use V
  intro x
  refine (hE ?_).mpr
    (hV (mem_image.mpr ⟨fun e ↦ if h : x e = Fin.last k then i else (x e).castPred h,
      mem_univ _, rfl⟩))
  intro a hai hal c
  cases hc : V.idxFun c with
  | inl t => simp only [V.apply_inl hc]
  | inr e =>
      simp only [V.apply_inr hc, Function.comp_apply]
      by_cases hx : x e = Fin.last k
      · rw [dite_eq_left hx, hx, Fin.castSuccEmb_apply]
        apply iff_of_false
        · intro h
          exact hal h.symm
        · intro h
          exact hai h.symm
      · rw [dite_eq_right hx, Fin.castSuccEmb_apply, Fin.castSucc_castPred]

/-- A canonical subspace contained in a family, depending on nothing but the family. -/
noncomputable def pickSubspace {k m b : ℕ} (hm : 1 ≤ m) (hmb : m ≤ b)
    (E : Finset (Fin b → Fin (k + 1))) :
    Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin b) := by
  classical
  exact if h : ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin b),
      Subspace.IsContained V E then Classical.choose h
    else Subspace.repeatInitial (Fin (k + 1)) hm hmb

lemma pickSubspace_isContained {k m b : ℕ} (hm : 1 ≤ m) (hmb : m ≤ b)
    {E : Finset (Fin b → Fin (k + 1))}
    (h : ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin b),
      Subspace.IsContained V E) :
    Subspace.IsContained (pickSubspace hm hmb E) E := by
  classical
  rw [pickSubspace, dite_eq_left h]
  exact Classical.choose_spec h

namespace IsInsensitive

/-- Place, over each word `z` on the outer coordinates, the subspaces `tiles z` of the block
coordinates. -/
def placeTiles {α η ι ζ ν : Type*} (e : ι ≃ ζ ⊕ ν)
    (tiles : (ζ → α) → Set (Combinatorics.Subspace η α ν)) :
    Set (Combinatorics.Subspace η α ι) :=
  ⋃ z, transportSubspace e z '' tiles z

private lemma elim_comp_eq_elim_comp_iff {α ι ζ ν : Type*} {e : ι ≃ ζ ⊕ ν} {a a' : ζ → α}
    {b b' : ν → α} : Sum.elim a b ∘ e = Sum.elim a' b' ∘ e ↔ a = a' ∧ b = b' := by
  rw [e.surjective.injective_comp_right.eq_iff]
  constructor
  · intro h
    exact ⟨funext fun c ↦ congrFun h (.inl c), funext fun c ↦ congrFun h (.inr c)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

variable {k m : ℕ}

/-- Tilings of the sections over the outer coordinates, placed over their outer words, form a
tiling of the whole family. -/
lemma IsTiling.placeTiles {ι ζ ν : Type*} [Fintype ι] [Fintype ζ] [Fintype ν] [DecidableEq ν]
    {e : ι ≃ ζ ⊕ ν} {D : Finset (ι → Fin (k + 1))}
    {tiles : (ζ → Fin (k + 1)) → Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) ν)}
    (h : ∀ z, IsTiling (tiles z) (fiber (transportWords e D) z)) :
    IsTiling (placeTiles e tiles) D where
  finite := Set.finite_iUnion fun z ↦ (h z).finite.image _
  isContained := by
    simp only [IsInsensitive.placeTiles, Set.mem_iUnion, Set.mem_image]
    rintro _ ⟨z, W, hW, rfl⟩ x
    simpa using (h z).isContained W hW x
  pairwiseDisjoint := by
    rw [Set.pairwiseDisjoint_iff]
    simp only [IsInsensitive.placeTiles, Set.mem_iUnion, Set.mem_image]
    rintro _ ⟨z, W, hW, rfl⟩ _ ⟨z', W', hW', rfl⟩ ⟨w, hw, hw'⟩
    obtain ⟨x, rfl⟩ := Subspace.mem_range.1 hw
    obtain ⟨x', hx'⟩ := Subspace.mem_range.1 hw'
    rw [transportSubspace_apply, transportSubspace_apply, elim_comp_eq_elim_comp_iff] at hx'
    obtain ⟨rfl, hx'⟩ := hx'
    rw [Set.pairwiseDisjoint_iff.1 (h z').pairwiseDisjoint hW hW'
      ⟨W x, Subspace.mem_range.2 ⟨x, rfl⟩, Subspace.mem_range.2 ⟨x', hx'⟩⟩]

/-- The section of the uncovered part over an outer word is the part of the section that its own
tiles leave uncovered. -/
lemma fiber_uncovered_placeTiles {ι ζ ν : Type*} [Fintype ι] [Fintype ζ] [Fintype ν]
    [DecidableEq ν] (e : ι ≃ ζ ⊕ ν) (D : Finset (ι → Fin (k + 1)))
    (tiles : (ζ → Fin (k + 1)) → Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) ν))
    (z : ζ → Fin (k + 1)) :
    fiber (transportWords e (uncovered D (placeTiles e tiles))) z =
      uncovered (fiber (transportWords e D) z) (tiles z) := by
  ext y
  simp only [mem_fiber, mem_transportWords, mem_uncovered, IsInsensitive.placeTiles,
    Set.mem_iUnion, Set.mem_image, forall_exists_index, and_imp]
  rw [and_congr_right_iff]
  intro _
  constructor
  · intro h W hW hyW
    obtain ⟨x, rfl⟩ := Subspace.mem_range.1 hyW
    exact h _ z W hW rfl (Subspace.mem_range.2 ⟨x, by simp⟩)
  · rintro h _ z' W hW rfl hyW
    obtain ⟨x, hx⟩ := Subspace.mem_range.1 hyW
    rw [transportSubspace_apply, elim_comp_eq_elim_comp_iff] at hx
    obtain ⟨rfl, rfl⟩ := hx
    exact h W hW (Subspace.mem_range.2 ⟨x, rfl⟩)

/-- Tilings of the sections over the outer coordinates, each leaving density less than `c`
uncovered, give a tiling of the whole family leaving density less than `c` uncovered. -/
private lemma exists_tiling_of_sections {ι ζ ν : Type*} [Fintype ι] [DecidableEq ι] [Fintype ζ]
    [Fintype ν] [DecidableEq ν] {e : ι ≃ ζ ⊕ ν} {D : Finset (ι → Fin (k + 1))} {c : ℝ}
    (h : ∀ z, ∃ 𝒱 : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) ν),
      IsTiling 𝒱 (fiber (transportWords e D) z) ∧
        ((uncovered (fiber (transportWords e D) z) 𝒱).dens : ℝ) < c) :
    ∃ 𝒱 : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι),
      IsTiling 𝒱 D ∧ ((uncovered D 𝒱).dens : ℝ) < c := by
  classical
  choose tiles htiles hc using h
  refine ⟨placeTiles e tiles, .placeTiles htiles, ?_⟩
  rw [← dens_transportWords e, ← average_density_fiber]
  simp_rw [fiber_uncovered_placeTiles]
  exact expect_lt (fun z _ ↦ (hc z).le) ⟨fun _ ↦ 0, mem_univ _, hc _⟩

/-- A positive-density set of nonempty fibers gives a proportional ambient density lower bound. -/
private lemma density_of_nonempty_fibers {k b : ℕ} {ι ζ : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype ζ]
    [Fintype (ζ → Fin (k + 1))]
    {e : ι ≃ ζ ⊕ Fin b} {R : Finset (ι → Fin (k + 1))}
    {good : Finset (ζ → Fin (k + 1))} {β : ℝ}
    (hgood : β ≤ (good.dens : ℝ))
    (hnonempty : ∀ z ∈ good, (fiber (transportWords e R) z).Nonempty) :
    β / ((k : ℝ) + 1) ^ b ≤ (R.dens : ℝ) := by
  classical
  have hcard : (Fintype.card (Fin b → Fin (k + 1)) : ℝ) = ((k : ℝ) + 1) ^ b := by
    simp only [Fintype.card_pi_const, Fintype.card_fin, Nat.cast_pow, Nat.cast_add,
      Nat.cast_one]
  have hfiber (z : ζ → Fin (k + 1)) (hz : z ∈ good) :
      1 / ((k : ℝ) + 1) ^ b ≤ ((fiber (transportWords e R) z).dens : ℝ) := by
    rw [← hcard]
    exact one_div_card_le_dens (hnonempty z hz)
  have haverage : (R.dens : ℝ) =
      𝔼 z : (ζ → Fin (k + 1)), ((fiber (transportWords e R) z).dens : ℝ) := by
    rw [average_density_fiber, dens_transportWords]
  rw [haverage, div_eq_mul_inv, mul_comm β (((k : ℝ) + 1) ^ b)⁻¹, ← one_div]
  apply le_trans (mul_le_mul_of_nonneg_left hgood (by positivity))
  rw [← expect_indicator_one (s := good), mul_expect]
  apply expect_le_expect
  intro z _
  by_cases hz : z ∈ good
  · rw [Set.indicator_of_mem (by simpa using hz)]
    simpa [Pi.one_apply, mul_one] using hfiber z hz
  · rw [Set.indicator_of_notMem (by simpa using hz), mul_zero]
    positivity

/-- The subspace chosen by `pickSubspace` in a family of density at least `β`, as a set of tiles
with at most one element. -/
noncomputable def pickTiles {b : ℕ} (hm : 1 ≤ m) (hmb : m ≤ b) (β : ℝ)
    (E : Finset (Fin b → Fin (k + 1))) :
    Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin b)) :=
  {V | β ≤ (E.dens : ℝ) ∧ V = pickSubspace hm hmb E}

private lemma isTiling_pickTiles {b : ℕ} (hm : 1 ≤ m) (hmb : m ≤ b) {β : ℝ}
    {E : Finset (Fin b → Fin (k + 1))}
    (hE : β ≤ (E.dens : ℝ) →
      ∃ V : Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin b), Subspace.IsContained V E) :
    IsTiling (pickTiles hm hmb β E) E where
  finite := (Set.finite_singleton (pickSubspace hm hmb E)).subset fun _ hV ↦ hV.2
  isContained := by
    rintro _ ⟨hβ, rfl⟩
    exact pickSubspace_isContained hm hmb (hE hβ)
  pairwiseDisjoint :=
    (Set.subsingleton_singleton.anti fun _ hV ↦ hV.2 :
      (pickTiles hm hmb β E).Subsingleton).pairwise _

/-- One stage of the tiling of a family of density at least `2 * β`: the tiles `pickTiles`
chooses in the sections over a block of `b` coordinates cover density at least
`β / (k + 1) ^ b`. -/
private lemma dens_uncovered_pickTiles_add_le {b : ℕ} (hm : 1 ≤ m) (hmb : m ≤ b) {β : ℝ}
    (hβ₀ : 0 < β) (hβ₁ : β < 1) {ι ζ : Type*} [Fintype ι] [DecidableEq ι] [Fintype ζ]
    {e : ι ≃ ζ ⊕ Fin b} {U : Finset (ι → Fin (k + 1))}
    (hU : 2 * β ≤ (U.dens : ℝ))
    (htiles : ∀ z, IsTiling (pickTiles hm hmb β (fiber (transportWords e U) z))
      (fiber (transportWords e U) z)) :
    ((uncovered U (placeTiles e fun z ↦ pickTiles hm hmb β (fiber (transportWords e U) z))).dens
        : ℝ) + β / ((k : ℝ) + 1) ^ b ≤ (U.dens : ℝ) := by
  classical
  set 𝒱 := placeTiles e fun z ↦ pickTiles hm hmb β (fiber (transportWords e U) z)
  have hgood : β ≤ ((univ.filter fun z ↦
      β ≤ ((fiber (transportWords e U) z).dens : ℝ)).dens : ℝ) := by
    refine le_trans ?_ (density_ge_threshold (fun z ↦ by exact_mod_cast dens_le_one)
      (by linarith : β < 2 * β) (by rwa [average_density_fiber, dens_transportWords]))
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  have hcovered := density_of_nonempty_fibers (e := e) (R := U \ uncovered U 𝒱) hgood
    fun z hz ↦ by
      rw [fiber_transportWords_sdiff, fiber_uncovered_placeTiles]
      have hpick : pickSubspace hm hmb (fiber (transportWords e U) z) ∈
          pickTiles hm hmb β (fiber (transportWords e U) z) := ⟨(mem_filter.1 hz).2, rfl⟩
      exact ⟨_, mem_sdiff.2 ⟨(htiles z).isContained _ hpick (fun _ ↦ 0),
        fun h ↦ (mem_uncovered.1 h).2 _ hpick (Subspace.mem_range.2 ⟨_, rfl⟩)⟩⟩
  rw [dens_sdiff_of_subset fun _ hw ↦ (mem_uncovered.1 hw).1] at hcovered
  linarith

/-- After one stage, the sections of the uncovered part over the remaining blocks are still
insensitive: whether a word is covered depends on its outer coordinates only through the section
of the family over them, which is the same for insensitive-equivalent words. -/
private lemma isInsensitive_fiber_uncovered_pickTiles {b : ℕ} (hm : 1 ≤ m) (hmb : m ≤ b)
    {β : ℝ} {i j : Fin (k + 1)} {ι ω ν ν₁ : Type*} [Fintype ι] [Fintype ω] [Fintype ν]
    [DecidableEq ν] [Fintype ν₁] [DecidableEq ν₁] {e : ι ≃ ω ⊕ ν} (s : ν ≃ ν₁ ⊕ Fin b)
    {U : Finset (ι → Fin (k + 1))}
    (hU : ∀ u, IsInsensitive i j (fiber (transportWords e U) u)) (v : ω ⊕ Fin b → Fin (k + 1)) :
    IsInsensitive i j (fiber (transportWords (regroup e (s.trans (Equiv.sumComm ν₁ (Fin b))))
      (uncovered U (placeTiles (regroup e s)
        fun z ↦ pickTiles hm hmb β (fiber (transportWords (regroup e s) U) z)))) v) := by
  rw [← Sum.elim_comp_inl_inr v]
  intro y y' hyy'
  rw [mem_fiber_regroup_sumComm, mem_fiber_regroup_sumComm, fiber_uncovered_placeTiles,
    fiber_uncovered_placeTiles, fiber_transportWords_regroup, fiber_transportWords_regroup,
    fiber_congr ((hU _).reindex s) hyy']

/-- The sections of a family over the outer coordinates and a first block are insensitive when
its sections over the outer coordinates are. -/
private lemma isInsensitive_fiber_regroup {i j : Fin (k + 1)} {ι ω ν ν₁ ν₂ : Type*} [Fintype ω]
    [Fintype ν] [DecidableEq ν] [Fintype ν₁] [Fintype ν₂] [DecidableEq ν₂] {e : ι ≃ ω ⊕ ν}
    (s : ν ≃ ν₁ ⊕ ν₂)
    {U : Finset (ι → Fin (k + 1))} (hU : ∀ u, IsInsensitive i j (fiber (transportWords e U) u))
    (z : ω ⊕ ν₁ → Fin (k + 1)) :
    IsInsensitive i j (fiber (transportWords (regroup e s) U) z) := by
  rw [← Sum.elim_comp_inl_inr z, fiber_transportWords_regroup]
  exact ((hU _).reindex s).fiberSection _

/-- The block density-increment tiling of paper Lemma 12.

The coordinates are split into an already consumed part `ω` and `T` fresh blocks of size `b`, and
the sections of the family over `ω` are insensitive. Each stage either finds that less than
`2 * β` of the density is left, or places the tiles of `pickTiles` in the sections over the first
fresh block, which cover density at least `β / (k + 1) ^ b`, and moves that block into `ω`.
Because those tiles are chosen from the sections alone, the sections of what is left over the new
`ω` are still insensitive. -/
private lemma exists_tiling_of_insensitive_sections {k : ℕ} (i : Fin k) {F : ℝ → ℕ}
    (hF : IsDHJBound k F) {m b : ℕ} (hm : 1 ≤ m) (hmb : m ≤ b) {β : ℝ} (hβ₀ : 0 < β)
    (hβ₁ : β < 1) (hb : Subspace.restrictAlphabetBound k F m β ≤ b) (T : ℕ) {ι ω : Type}
    [Fintype ι] [DecidableEq ι] [Fintype ω] (e : ι ≃ ω ⊕ Fin (T * b))
    (U : Finset (ι → Fin (k + 1)))
    (hU : ∀ v, IsInsensitive i.castSucc (Fin.last k) (fiber (transportWords e U) v)) :
    ∃ 𝒱 : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) ι), IsTiling 𝒱 U ∧
      (((uncovered U 𝒱).dens : ℝ) < 2 * β ∨
        ((uncovered U 𝒱).dens : ℝ) + T * (β / ((k : ℝ) + 1) ^ b) ≤ (U.dens : ℝ)) := by
  induction T generalizing ω U with
  | zero => exact ⟨∅, .empty, .inr (by simp)⟩
  | succ S ih =>
    obtain hlt | hle := lt_or_ge (U.dens : ℝ) (2 * β)
    · exact ⟨∅, .empty, .inl (by simpa using hlt)⟩
    let s : Fin ((S + 1) * b) ≃ Fin (S * b) ⊕ Fin b :=
      (finSumFinEquiv.trans (finCongr (by ring))).symm
    have htiles (z : ω ⊕ Fin (S * b) → Fin (k + 1)) :=
      isTiling_pickTiles hm hmb (β := β) fun hz ↦
        exists_isContained_of_insensitive hF hm hβ₀ hb (isInsensitive_fiber_regroup s hU z) hz
    obtain ⟨𝒲, h𝒲, hsmall⟩ := ih _ _ (isInsensitive_fiber_uncovered_pickTiles hm hmb s hU)
    refine ⟨_ ∪ 𝒲, (IsTiling.placeTiles htiles).union h𝒲, ?_⟩
    have hstage := dens_uncovered_pickTiles_add_le hm hmb hβ₀ hβ₁ hle htiles
    rw [uncovered_union, Nat.cast_add_one]
    refine hsmall.imp_right ?_
    intro h
    linarith

/-- The tiling procedure tiles one insensitive family in `T` stages, over blocks of any size `b`
that supports the restricted-alphabet subspace lemma, once `T` exceeds the number of possible
density increments. -/
lemma tilingSufficient_mul {k m : ℕ} {F : ℝ → ℕ} (hF : IsDHJBound k F) (hm : 1 ≤ m)
    {β : ℝ} (hβ₀ : 0 < β) {b : ℕ} (hmb : m ≤ b)
    (hb : Subspace.restrictAlphabetBound k F m β ≤ b) {T : ℕ}
    (hT : 1 / (β / ((k : ℝ) + 1) ^ b) < T) :
    TilingSufficient k m β (T * b) := by
  intro i D hD
  have hD₁ : (D.dens : ℝ) ≤ 1 := by exact_mod_cast dens_le_one
  obtain hβ | hβ := lt_or_ge β 1
  · obtain ⟨𝒱, h𝒱, hsmall⟩ := exists_tiling_of_insensitive_sections i hF hm hmb hβ₀ hβ hb T
      (Equiv.emptySum (Fin 0) (Fin (T * b))).symm D fun v ↦ (hD.reindex _).fiberSection v
    refine ⟨𝒱, h𝒱, hsmall.resolve_right ?_⟩
    rw [div_lt_iff₀ (by positivity)] at hT
    intro h
    linarith [(by positivity : (0 : ℝ) ≤ (uncovered D 𝒱).dens)]
  · exact ⟨∅, .empty, by simp; linarith⟩

/-- A tiling of every section over some extra coordinates gives a tiling of the whole cube. -/
private lemma tilingSufficient_mono {k m N n : ℕ} {β : ℝ}
    (hN : TilingSufficient k m β N) (hNn : N ≤ n) :
    TilingSufficient k m β n := by
  intro i D hD
  exact exists_tiling_of_sections (e := (Subspace.cutEquiv (Nat.sub_add_cancel hNn)).symm)
    fun z ↦ hN i _ ((hD.reindex _).fiberSection z)

/-- A dimension sufficient for tiling one insensitive family by `m`-dimensional subspaces with
tolerance `β`: blocks whose size supports the restricted-alphabet subspace lemma, one more than the
number of possible density increments. -/
noncomputable def tilingBound (k : ℕ) (F : ℝ → ℕ) (m : ℕ) (β : ℝ) : ℕ :=
  (⌊((k : ℝ) + 1) ^ max m (Subspace.restrictAlphabetBound k F m β) / β⌋₊ + 1) *
    max m (Subspace.restrictAlphabetBound k F m β)

/-- `TilingSufficient k m β n` holds for every `n ≥ tilingBound k F m β`. -/
lemma tilingSufficient_of_le {k m n : ℕ} {F : ℝ → ℕ} (hF : IsDHJBound k F) (hm : 1 ≤ m)
    {β : ℝ} (hβ₀ : 0 < β) (hn : tilingBound k F m β ≤ n) : TilingSufficient k m β n := by
  refine tilingSufficient_mono
    (tilingSufficient_mul hF hm hβ₀ (le_max_left _ _) (le_max_right _ _) ?_) hn
  rw [one_div_div, Nat.cast_add, Nat.cast_one]
  exact Nat.lt_floor_add_one _

/-- Pulling an insensitive family back through a subspace preserves its sensitivity pair. -/
lemma parameterPreimage_isInsensitive {α η ι : Type*}
    [Fintype (η → α)] {a b : α} (V : Combinatorics.Subspace η α ι) {D : Finset (ι → α)}
    (hD : IsInsensitive a b D) : IsInsensitive a b (parameterPreimage V D) := by
  classical
  intro x y hxy
  simp only [parameterPreimage, mem_filter, mem_univ, true_and]
  apply hD
  intro c hca hcb i
  cases hi : V.idxFun i with
  | inl d => rw [V.apply_inl hi, V.apply_inl hi]
  | inr e =>
    rw [V.apply_inr hi, V.apply_inr hi]
    exact hxy c hca hcb e

/-- Inside each subspace `V ∈ 𝒱`, the subspaces `tiles V` of its parameter cube, composed with
`V`. -/
def composeTiles {α η θ ι : Type*} (𝒱 : Set (Combinatorics.Subspace θ α ι))
    (tiles : Combinatorics.Subspace θ α ι → Set (Combinatorics.Subspace η α θ)) :
    Set (Combinatorics.Subspace η α ι) :=
  ⋃ V ∈ 𝒱, Subspace.compose V '' tiles V

variable {M n : ℕ} {A E : Finset (Fin n → Fin (k + 1))}
  {𝒱 : Set (Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n))}
  {tiles : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n) →
    Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin M))}

/-- Tilings of the parameter preimages of `E` inside the subspaces of a tiling of `A`, composed
with those subspaces, form a tiling of `A ∩ E`. -/
lemma IsTiling.composeTiles (h𝒱 : IsTiling 𝒱 A)
    (htiles : ∀ V ∈ 𝒱, IsTiling (tiles V) (parameterPreimage V E)) :
    IsTiling (composeTiles 𝒱 tiles) (A ∩ E) where
  finite := h𝒱.finite.biUnion fun V hV ↦ (htiles V hV).finite.image _
  isContained := by
    simp only [IsInsensitive.composeTiles, Set.mem_iUnion, Set.mem_image]
    rintro _ ⟨V, hV, W, hW, rfl⟩ x
    have hx := (htiles V hV).isContained W hW x
    simp only [parameterPreimage, mem_filter, mem_univ, true_and] at hx
    simpa using ⟨h𝒱.isContained V hV (W x), hx⟩
  pairwiseDisjoint := by
    rw [Set.pairwiseDisjoint_iff]
    simp only [IsInsensitive.composeTiles, Set.mem_iUnion, Set.mem_image]
    rintro _ ⟨V, hV, W, hW, rfl⟩ _ ⟨V', hV', W', hW', rfl⟩ ⟨w, hw, hw'⟩
    obtain ⟨x, rfl⟩ := Subspace.mem_range.1 hw
    obtain ⟨x', hx'⟩ := Subspace.mem_range.1 hw'
    simp only [Subspace.compose_apply] at hx'
    obtain rfl := Set.pairwiseDisjoint_iff.1 h𝒱.pairwiseDisjoint hV hV'
      ⟨V (W x), Subspace.mem_range.2 ⟨W x, rfl⟩, Subspace.mem_range.2 ⟨W' x', hx'⟩⟩
    rw [Set.pairwiseDisjoint_iff.1 (htiles V hV).pairwiseDisjoint hW hW'
      ⟨W x, Subspace.mem_range.2 ⟨x, rfl⟩, Subspace.mem_range.2 ⟨x', Subspace.injective V hx'⟩⟩]

/-- Mapping a parameter-cube family into a subspace scales its ambient density by the density of
the whole subspace range. -/
private lemma dens_map_subspace_eq_mul_range {α η ι : Type*}
    [Fintype (η → α)] [Fintype (ι → α)] [DecidableEq (ι → α)]
    (V : Combinatorics.Subspace η α ι) (A : Finset (η → α)) :
    ((A.map ⟨V, Subspace.injective V⟩).dens : ℝ) =
      (A.dens : ℝ) * ((Subspace.range V).dens : ℝ) := by
  simp only [nnratCast_dens, Subspace.range, card_map]
  rw [card_image_iff.mpr (Subspace.injective V).injOn]
  by_cases h : Fintype.card (η → α) = 0
  · let : IsEmpty (η → α) := Fintype.card_eq_zero_iff.mp h
    have hA : A = ∅ := Subsingleton.elim _ _
    rw [hA]
    simp
  · field_simp
    simp only [card_univ]

/-- Families of relative density at most `ε` inside the subspaces of a tiling have total density
at most `ε`. -/
private lemma dens_biUnion_map_le (h𝒱 : IsTiling 𝒱 A)
    {L : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n) → Finset (Fin M → Fin (k + 1))}
    {ε : ℝ} (hε₀ : 0 ≤ ε) (hL : ∀ V ∈ 𝒱, ((L V).dens : ℝ) ≤ ε) :
    ((h𝒱.finite.toFinset.biUnion fun V ↦ (L V).map ⟨V, Subspace.injective V⟩).dens : ℝ) ≤ ε := by
  have hdisjoint : (h𝒱.finite.toFinset : Set _).PairwiseDisjoint
      fun V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n) ↦ Subspace.range V := by
    simpa [← pairwiseDisjoint_coe] using h𝒱.pairwiseDisjoint
  calc ((h𝒱.finite.toFinset.biUnion fun V ↦ (L V).map ⟨V, Subspace.injective V⟩).dens : ℝ)
      ≤ ∑ V ∈ h𝒱.finite.toFinset, ((L V).dens : ℝ) * ((Subspace.range V).dens : ℝ) := by
        simp_rw [← dens_map_subspace_eq_mul_range, ← NNRat.cast_sum]
        exact_mod_cast dens_biUnion_le
    _ ≤ ∑ V ∈ h𝒱.finite.toFinset, ε * ((Subspace.range V).dens : ℝ) := by
        gcongr with V hV
        exact hL V (by simpa using hV)
    _ = ε * ((h𝒱.finite.toFinset.biUnion Subspace.range).dens : ℝ) := by
        rw [dens_biUnion hdisjoint, NNRat.cast_sum, mul_sum]
    _ ≤ ε := mul_le_of_le_one_right hε₀ (by exact_mod_cast dens_le_one)

/-- A word of `A ∩ E` missed by all composed tiles is missed by all subspaces of `𝒱`, or lies in
the image of the part of the preimage of `E` that the tiles inside its subspace leave uncovered. -/
private lemma uncovered_composeTiles_subset (h𝒱 : 𝒱.Finite) :
    uncovered (A ∩ E) (composeTiles 𝒱 tiles) ⊆ uncovered A 𝒱 ∪
      h𝒱.toFinset.biUnion fun V ↦
        (uncovered (parameterPreimage V E) (tiles V)).map ⟨V, Subspace.injective V⟩ := by
  intro w hw
  rw [mem_uncovered, mem_inter] at hw
  rw [mem_union, mem_uncovered]
  by_cases h : ∃ V ∈ 𝒱, w ∈ Subspace.range V
  · right
    obtain ⟨V, hV, hwV⟩ := h
    obtain ⟨x, rfl⟩ := Subspace.mem_range.1 hwV
    refine mem_biUnion.2 ⟨V, by simpa using hV, mem_map.2 ⟨x, ?_, rfl⟩⟩
    rw [mem_uncovered]
    refine ⟨by simpa [parameterPreimage] using hw.1.2, ?_⟩
    intro W hW hxW
    obtain ⟨y, rfl⟩ := Subspace.mem_range.1 hxW
    exact hw.2 _ (Set.mem_biUnion hV (Set.mem_image_of_mem _ hW))
      (Subspace.mem_range.2 ⟨y, by simp⟩)
  · exact .inl ⟨hw.1.1, fun V hV hwV ↦ h ⟨V, hV, hwV⟩⟩

/-- Composing tilings that leave relative density at most `ε` of the preimages of `E` uncovered
leaves at most `ε` more of `A ∩ E` uncovered than `𝒱` leaves of `A`. -/
private lemma dens_uncovered_composeTiles_le (h𝒱 : IsTiling 𝒱 A) {ε : ℝ} (hε₀ : 0 ≤ ε)
    (hε : ∀ V ∈ 𝒱, ((uncovered (parameterPreimage V E) (tiles V)).dens : ℝ) ≤ ε) :
    ((uncovered (A ∩ E) (composeTiles 𝒱 tiles)).dens : ℝ) ≤ (uncovered A 𝒱).dens + ε := by
  have h := (NNRat.cast_le (K := ℝ)).2 ((dens_mono (uncovered_composeTiles_subset
    (A := A) (E := E) (tiles := tiles) h𝒱.finite)).trans (dens_union_le _ _))
  rw [NNRat.cast_add] at h
  linarith [dens_biUnion_map_le h𝒱 hε₀ hε]

/-- An ambient dimension is sufficient for tiling intersections of `r` insensitive families: each
of them has a tiling by `m`-dimensional subspaces leaving density less than `2 * r * β`
uncovered. -/
def IntersectionTilingSufficient (k r m : ℕ) (β : ℝ) (n : ℕ) : Prop :=
  ∀ hrk : r ≤ k, ∀ D : Fin r → Finset (Fin n → Fin (k + 1)),
    (∀ i, IsInsensitive (Fin.castLE hrk i).castSucc (Fin.last k) (D i)) →
    ∃ 𝒱 : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)),
      IsTiling 𝒱 (intersection D) ∧ ((uncovered (intersection D) 𝒱).dens : ℝ) < 2 * r * β

/-- One indexed insensitive family is exactly the one-family tiling statement. -/
private lemma intersectionTilingSufficient_one {β : ℝ} (h : TilingSufficient k m β n) :
    IntersectionTilingSufficient k 1 m β n := by
  intro hrk D hD
  have hD₀ : intersection D = D 0 := by
    ext x
    simp [Fin.forall_fin_one]
  simpa [hD₀] using h _ (D 0) (hD 0)

/-- Tiling the intersection of the first `r` families by `M`-dimensional subspaces, and the
preimage of the last family inside each of them by `m`-dimensional subspaces, tiles the
intersection of all `r + 1`. -/
private lemma extend_intersection_tiling {r : ℕ} {β : ℝ} (hβ₀ : 0 < β)
    (houter : IntersectionTilingSufficient k r M β n) (hinner : TilingSufficient k m β M) :
    IntersectionTilingSufficient k (r + 1) m β n := by
  intro hrk D hD
  obtain ⟨𝒱, h𝒱, houter⟩ := houter (by omega) _ fun i ↦ hD i.castSucc
  choose tiles htiles hinner using fun V : Combinatorics.Subspace (Fin M) (Fin (k + 1)) (Fin n) ↦
    hinner _ _ (parameterPreimage_isInsensitive V (hD (Fin.last r)))
  refine ⟨composeTiles 𝒱 tiles, ?_, ?_⟩
  · rw [intersection_eq_inter_last]
    exact h𝒱.composeTiles fun V _ ↦ htiles V
  · rw [intersection_eq_inter_last]
    have h := dens_uncovered_composeTiles_le h𝒱 (by positivity) fun V _ ↦ (hinner V).le
    rw [Nat.cast_add_one]
    linarith

/-- Intersection-tiling sufficiency in one dimension gives it in every larger one. -/
private lemma intersectionTilingSufficient_mono {r N : ℕ} {β : ℝ}
    (hN : IntersectionTilingSufficient k r m β N) (hNn : N ≤ n) :
    IntersectionTilingSufficient k r m β n := by
  intro hrk D hD
  refine exists_tiling_of_sections (e := (Subspace.cutEquiv (Nat.sub_add_cancel hNn)).symm) ?_
  intro z
  have hz : fiber (transportWords (Subspace.cutEquiv (Nat.sub_add_cancel hNn)).symm
      (intersection D)) z = intersection fun i ↦
        fiber (transportWords (Subspace.cutEquiv (Nat.sub_add_cancel hNn)).symm (D i)) z := by
    ext y
    simp
  rw [hz]
  exact hN hrk _ fun i ↦ ((hD i).reindex _).fiberSection z

/-- A dimension sufficient for tiling an intersection of `r` insensitive families by
`m`-dimensional subspaces with tolerance `β`, by induction on `r`: tile the first `r - 1` families
by subspaces large enough to tile the last one. -/
noncomputable def intersectionTilingBound (k : ℕ) (F : ℝ → ℕ) : ℕ → ℕ → ℝ → ℕ
  | 0, _, _ => 0
  | 1, m, β => tilingBound k F m β
  | r + 2, m, β => intersectionTilingBound k F (r + 1) (max 1 (tilingBound k F m β)) β

/-- `IntersectionTilingSufficient k r m β n` holds for every
`n ≥ intersectionTilingBound k F r m β`. -/
lemma intersectionTilingSufficient_of_le {r : ℕ} {F : ℝ → ℕ} (hF : IsDHJBound k F)
    (hr₀ : 1 ≤ r) (hm : 1 ≤ m) {β : ℝ} (hβ₀ : 0 < β)
    (hn : intersectionTilingBound k F r m β ≤ n) :
    IntersectionTilingSufficient k r m β n := by
  refine intersectionTilingSufficient_mono ?_ hn
  clear hn
  induction r using Nat.strong_induction_on generalizing m with
  | h r ih =>
    obtain _ | _ | r := r
    · omega
    · exact intersectionTilingSufficient_one (tilingSufficient_of_le hF hm hβ₀ le_rfl)
    · exact extend_intersection_tiling hβ₀ (ih (r + 1) (by omega) (by omega) (le_max_left _ _))
        (tilingSufficient_of_le hF hm hβ₀ (le_max_right _ _))

/-- An intersection of insensitive families can be tiled by disjoint subspaces. -/
lemma exists_disjoint_subspaces_iInter {r : ℕ} {F : ℝ → ℕ} (hF : IsDHJBound k F)
    (hr₀ : 1 ≤ r) (hrk : r ≤ k) (hm : 1 ≤ m) {β : ℝ} (hβ₀ : 0 < β)
    (hn : intersectionTilingBound k F r m β ≤ n) {D : Fin r → Finset (Fin n → Fin (k + 1))}
    (hD : ∀ i, IsInsensitive (Fin.castLE hrk i).castSucc (Fin.last k) (D i)) :
    ∃ 𝒱 : Set (Combinatorics.Subspace (Fin m) (Fin (k + 1)) (Fin n)),
      IsTiling 𝒱 (intersection D) ∧ ((uncovered (intersection D) 𝒱).dens : ℝ) < 2 * r * β :=
  intersectionTilingSufficient_of_le hF hr₀ hm hβ₀ hn hrk D hD

end IsInsensitive
end DensityHalesJewett
