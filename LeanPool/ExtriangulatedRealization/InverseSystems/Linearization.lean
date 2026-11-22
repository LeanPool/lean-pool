/-
Copyright (c) 2026 Haruhisa Enomoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haruhisa Enomoto
-/
module

public import LeanPool.ExtriangulatedRealization.Statement
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions

/-!
# Linearizing inverse systems of sets (Lemma 4.1)

For an inverse system `S` of sets with surjective transition maps, the free vector spaces
`k^(S_i)` form an inverse system with surjective transition maps. If moreover every countable
set of indices is bounded and `lim S = ∅`, then `lim k^(S_i) = 0` (Bergman [Be, Lemma 3], after
Higman and Stone).

Proof (finite supports): for a compatible family `(v_i)` with `v_{i₀} ≠ 0`, the support sizes
`|supp v_i|` are monotone, hence eventually constant, because countable sets of indices are
bounded. From then on, the transition maps restrict to bijections between supports, and lifting
one point of a support through these bijections gives an element of `lim S`.
-/

@[expose] public section

namespace ExtriangulatedRealization

open CategoryTheory Opposite Statement

universe u

variable {I : Type u} [LinearOrder I]

/-- A monotone `ℕ`-valued function on a linear order whose countable subsets are bounded is
eventually constant. -/
lemma Monotone.exists_eventually_const
    (hI : ∀ T : Set I, T.Countable → BddAbove T) {g : I → ℕ} (hg : Monotone g) :
    ∃ m, ∀ j, m ≤ j → g j = g m := by
  classical
  let c : {n : ℕ // ∃ i, n ≤ g i} → I := fun n => n.2.choose
  obtain ⟨m, hm⟩ := hI (Set.range c) (Set.countable_range c)
  refine ⟨m, fun j hj => le_antisymm ?_ (hg hj)⟩
  by_contra hlt
  have hn : ∃ i, g j ≤ g i := ⟨j, le_rfl⟩
  have h1 : g j ≤ g (c ⟨g j, hn⟩) := hn.choose_spec
  have h2 : c ⟨g j, hn⟩ ≤ m := hm ⟨⟨g j, hn⟩, rfl⟩
  exact hlt (h1.trans (hg h2))

variable (S : Iᵒᵖ ⥤ Type u)

/-- The transition map `S_b → S_a` for `a ≤ b`. -/
abbrev smapS {a b : I} (h : a ≤ b) : S.obj (op b) → S.obj (op a) := S.map (homOfLE h).op

lemma smapS_smapS {a b c : I} (hab : a ≤ b) (hbc : b ≤ c) (x : S.obj (op c)) :
    smapS S hab (smapS S hbc x) = smapS S (hab.trans hbc) x := by
  change (S.map (homOfLE hbc).op ≫ S.map (homOfLE hab).op) x = _
  rw [← S.map_comp]
  rfl

variable (k : Type u) [Field k]

/-- The linearization `k^(S_i)` of an inverse system of sets. -/
noncomputable abbrev linearize : Iᵒᵖ ⥤ ModuleCat.{u} k := S ⋙ ModuleCat.free k

lemma linearize_map_apply {a b : I} (h : a ≤ b) (v : (linearize S k).obj (op b)) :
    ((linearize S k).map (homOfLE h).op).hom v = Finsupp.mapDomain (smapS S h) v := rfl

/-- **Lemma 4.1**, surjectivity. -/
lemma linearize_hasSurjectiveTransitions
    (hS : ∀ {a b : I} (h : a ≤ b), Function.Surjective (smapS S h)) :
    HasSurjectiveTransitions (linearize S k) := fun h =>
  Finsupp.mapDomain_surjective (hS h)

/-- **Lemma 4.1**, vanishing of the limit: with countable index sets bounded and `lim S = ∅`,
every compatible family in `k^(S_i)` is zero. -/
theorem linearize_compatible_eq_zero (hI : ∀ T : Set I, T.Countable → BddAbove T)
    (hlim : ¬ ∃ s : ∀ i, S.obj (op i), ∀ {a b : I} (h : a ≤ b), smapS S h (s b) = s a)
    (v : ∀ i, (linearize S k).obj (op i))
    (hv : ∀ {a b : I} (h : a ≤ b), ((linearize S k).map (homOfLE h).op).hom (v b) = v a) (i : I) :
    v i = 0 := by
  classical
  by_contra hi₀
  have : Nonempty I := ⟨i⟩
  let F : ∀ j, Finset (S.obj (op j)) := fun j => (v j).support
  have hF : ∀ {a b : I} (h : a ≤ b), F a ⊆ (F b).image (smapS S h) := fun {a b} h => by
    change (v a).support ⊆ _
    rw [← hv h, linearize_map_apply]
    exact Finsupp.mapDomain_support
  have hmono : Monotone fun j => (F j).card := fun a b h =>
    (Finset.card_le_card (hF h)).trans Finset.card_image_le
  obtain ⟨m₀, hm₀⟩ := Monotone.exists_eventually_const hI hmono
  let m := m₀ ⊔ i
  have hcard : ∀ {a b : I} (ha : m ≤ a) (hab : a ≤ b), (F b).card = (F a).card := fun ha hab =>
    (hm₀ _ ((le_sup_left.trans ha).trans hab)).trans (hm₀ _ (le_sup_left.trans ha)).symm
  have himage : ∀ {a b : I} (ha : m ≤ a) (hab : a ≤ b), (F b).image (smapS S hab) = F a :=
    fun ha hab => (Finset.eq_of_subset_of_card_le (hF hab)
      (Finset.card_image_le.trans (hcard ha hab).le)).symm
  have hinj : ∀ {a b : I} (ha : m ≤ a) (hab : a ≤ b), Set.InjOn (smapS S hab) (F b) :=
    fun ha hab => Finset.card_image_iff.mp ((himage ha hab).symm ▸ (hcard ha hab).symm)
  have hvm : v m ≠ 0 := fun h => hi₀ (by rw [← hv (le_sup_right : i ≤ m), h, map_zero])
  obtain ⟨s₀, hs₀⟩ : (F m).Nonempty := Finsupp.support_nonempty_iff.mpr hvm
  have hsel : ∀ j (hj : m ≤ j), ∃ t ∈ F j, smapS S hj t = s₀ := fun j hj => by
    have : s₀ ∈ (F j).image (smapS S hj) := (himage le_rfl hj).symm ▸ hs₀
    simpa using this
  let sel : ∀ j, m ≤ j → S.obj (op j) := fun j hj => (hsel j hj).choose
  have sel_mem : ∀ j hj, sel j hj ∈ F j := fun j hj => (hsel j hj).choose_spec.1
  have sel_map : ∀ j hj, smapS S hj (sel j hj) = s₀ := fun j hj => (hsel j hj).choose_spec.2
  have sel_compat : ∀ {a b} (ha : m ≤ a) (hab : a ≤ b),
      smapS S hab (sel b (ha.trans hab)) = sel a ha := by
    intro a b ha hab
    apply hinj le_rfl ha
    · have : smapS S hab (sel b (ha.trans hab)) ∈ (F b).image (smapS S hab) :=
        Finset.mem_image_of_mem _ (sel_mem _ _)
      rw [himage ha hab] at this
      exact this
    · exact sel_mem a ha
    · rw [smapS_smapS, sel_map, sel_map]
  apply hlim
  refine ⟨fun j => smapS S (le_sup_left : j ≤ j ⊔ m) (sel (j ⊔ m) le_sup_right),
    fun {a b} h => ?_⟩
  have hab : a ⊔ m ≤ b ⊔ m := sup_le_sup_right h m
  change smapS S h (smapS S _ (sel (b ⊔ m) _)) = smapS S _ (sel (a ⊔ m) _)
  rw [smapS_smapS, ← sel_compat le_sup_right hab, smapS_smapS]

/-- **Lemma 4.1**, consequence: if some `S_i` is nonempty, the projections from `lim k^(S_i)` are
not all surjective. -/
theorem linearize_not_projectionsSurjective (hI : ∀ T : Set I, T.Countable → BddAbove T)
    (hlim : ¬ ∃ s : ∀ i, S.obj (op i), ∀ {a b : I} (h : a ≤ b), smapS S h (s b) = s a)
    (i : I) (x : S.obj (op i)) : ¬ ProjectionsSurjective (linearize S k) := by
  intro hP
  obtain ⟨y, hy, hyi⟩ := hP i (Finsupp.single x 1)
  have h0 := linearize_compatible_eq_zero S k hI hlim y (fun h => hy h) i
  rw [hyi] at h0
  exact one_ne_zero (Finsupp.single_eq_zero.mp h0)

end ExtriangulatedRealization
