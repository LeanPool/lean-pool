/-
Copyright (c) 2026 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
module

public import LeanPool.RigidDescent.Foundations.Compact
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.Shapes.Countable

/-!
# Telescopes

For a sequence `X₀ →x₀ X₁ →x₁ ⋯` in a pretriangulated category with countable coproducts, a
*telescope* is the third vertex `X∞` of a distinguished triangle
`∐ Xₙ →(1 - σ) ∐ Xₙ →c X∞ →e (∐ Xₙ)⟦1⟧`, where `σ` has components `xₙ` followed by the
inclusion of `Xₙ₊₁` (`telescopeShift`). With `ιₙ : Xₙ ⟶ X∞` the inclusion of `Xₙ` followed by
`c`:

* `Telescope.x_comp_ι`: `xₙ ≫ ιₙ₊₁ = ιₙ`;
* `Telescope.exists_desc`: compatible maps `Xₙ ⟶ Z` extend along the `ιₙ` to `X∞ ⟶ Z`;
* `Telescope.exists_factor`: for compact `K`, every map `K ⟶ X∞` factors through some `ιₙ`.
  In the rotated triangle the map after `e` is `-(1 - σ)⟦1⟧'`, which is injective on maps from
  a compact object, since `1 - σ` is injective on finite sums (`eq_zero_of_isFiniteSum`). So
  `k ≫ e = 0`, `k` factors through `c`, and the map into `∐ Xₙ` is a finite sum.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

universe v u

namespace RigidDescent

variable {T : Type u} [Category.{v} T] [Preadditive T] [HasCoproducts.{v} T]

variable (X : ℕ → T) (x : ∀ n, X n ⟶ X (n + 1))

/-- `σ : ∐ Xₙ ⟶ ∐ Xₙ`, with components `xₙ` followed by the inclusion of `Xₙ₊₁`. -/
noncomputable def telescopeShift : ∐ X ⟶ ∐ X :=
  Sigma.desc fun n => x n ≫ Sigma.ι X (n + 1)

omit [Preadditive T] in
@[reassoc (attr := simp)]
lemma ι_telescopeShift (n : ℕ) :
    Sigma.ι X n ≫ telescopeShift X x = x n ≫ Sigma.ι X (n + 1) := by
  simp [telescopeShift]

@[reassoc]
lemma telescopeShift_π_zero : telescopeShift X x ≫ Sigma.π X 0 = 0 := by
  ext n
  simp [Sigma.ι_π_of_ne _ (Nat.succ_ne_zero n)]

@[reassoc]
lemma telescopeShift_π_succ (m : ℕ) :
    telescopeShift X x ≫ Sigma.π X (m + 1) = Sigma.π X m ≫ x m := by
  ext n
  simp only [ι_telescopeShift_assoc]
  by_cases h : n = m
  · subst h; simp
  · rw [Sigma.ι_π_of_ne _ (by omega : n + 1 ≠ m + 1), Sigma.ι_π_of_ne_assoc _ h]
    simp

/-- `1 - σ` is injective on finite sums. -/
lemma eq_zero_of_isFiniteSum {K : T} {b : K ⟶ ∐ X} (hb : IsFiniteSum b)
    (h : b ≫ (𝟙 _ - telescopeShift X x) = 0) : b = 0 := by
  rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at h
  have hc : ∀ m, b ≫ Sigma.π X m = 0 := by
    intro m
    induction m with
    | zero => rw [h, Category.assoc, telescopeShift_π_zero, Limits.comp_zero]
    | succ m ih => rw [h, Category.assoc, telescopeShift_π_succ, ← Category.assoc, ih,
        Limits.zero_comp]
  obtain ⟨F, a, rfl⟩ := hb
  refine Finset.sum_eq_zero fun n hn => ?_
  have := hc n
  simp only [sum_comp_sigmaπ, hn, ↓reduceIte] at this
  rw [this, Limits.zero_comp]

variable [HasZeroObject T] [HasShift T ℤ] [∀ n : ℤ, (shiftFunctor T n).Additive]
  [Pretriangulated T]

/-- The transition map `Xₙ ⟶ Xₘ` for `n ≤ m`. -/
noncomputable abbrev seqMap {n m : ℕ} (h : n ≤ m) : X n ⟶ X m :=
  (Functor.ofSequence x).map (homOfLE h)

/-- A *telescope* of `X₀ → X₁ → ⋯`: a distinguished triangle
`∐ Xₙ →(1 - σ) ∐ Xₙ →c X∞ →e (∐ Xₙ)⟦1⟧`. -/
structure Telescope where
  /-- The telescope `X∞`. -/
  obj : T
  /-- The map `∐ Xₙ ⟶ X∞`. -/
  c : ∐ X ⟶ obj
  /-- The map `X∞ ⟶ (∐ Xₙ)⟦1⟧`. -/
  e : obj ⟶ (∐ X)⟦(1 : ℤ)⟧
  distinguished : Triangle.mk (𝟙 (∐ X) - telescopeShift X x) c e ∈ distTriang T

/-- A chosen telescope. -/
noncomputable def telescope : Telescope X x :=
  let h := distinguished_cocone_triangle (𝟙 (∐ X) - telescopeShift X x)
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.choose,
    h.choose_spec.choose_spec.choose_spec⟩

namespace Telescope

variable {X x} (t : Telescope X x)

/-- The map `ιₙ : Xₙ ⟶ X∞`. -/
noncomputable def ι (n : ℕ) : X n ⟶ t.obj := Sigma.ι X n ≫ t.c

lemma oneSub_comp_c : (𝟙 _ - telescopeShift X x) ≫ t.c = 0 :=
  comp_distTriang_mor_zero₁₂ _ t.distinguished

@[reassoc (attr := simp)]
lemma x_comp_ι (n : ℕ) : x n ≫ t.ι (n + 1) = t.ι n := by
  have := Sigma.ι X n ≫= t.oneSub_comp_c
  rw [Preadditive.sub_comp, Category.id_comp, Preadditive.comp_sub, ι_telescopeShift_assoc,
    Limits.comp_zero, sub_eq_zero] at this
  simp only [ι, ← this]

@[reassoc (attr := simp)]
lemma seqMap_comp_ι {n m : ℕ} (h : n ≤ m) : seqMap X x h ≫ t.ι m = t.ι n := by
  induction m, h using Nat.le_induction with
  | base =>
    change Functor.OfSequence.map x n n le_rfl ≫ t.ι n = t.ι n
    rw [Functor.OfSequence.map_id, Category.id_comp]
  | succ m hnm ih =>
    change Functor.OfSequence.map x n m hnm ≫ t.ι m = t.ι n at ih
    change Functor.OfSequence.map x n (m + 1) (hnm.trans (Nat.le_succ m)) ≫ t.ι (m + 1) = t.ι n
    rw [Functor.OfSequence.map_comp x n m (m + 1) hnm (Nat.le_succ m),
      Category.assoc, Functor.OfSequence.map_le_succ, x_comp_ι, ih]

/-- Compatible maps `Xₙ ⟶ Z` extend along the `ιₙ` to a map `X∞ ⟶ Z`. -/
lemma exists_desc {Z : T} (f : ∀ n, X n ⟶ Z) (hf : ∀ n, x n ≫ f (n + 1) = f n) :
    ∃ g : t.obj ⟶ Z, ∀ n, t.ι n ≫ g = f n := by
  have : (𝟙 _ - telescopeShift X x) ≫ Sigma.desc f = 0 := by
    ext n
    simp [hf]
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ _ t.distinguished _ this
  refine ⟨g, fun n => ?_⟩
  dsimp at hg
  rw [ι, Category.assoc, ← hg, Sigma.ι_comp_desc]

/-- For compact `K`, every map `K ⟶ X∞` factors through some `ιₙ`. -/
lemma exists_factor {K : T} (hK : IsCompactObj K) (k : K ⟶ t.obj) :
    ∃ (n : ℕ) (k' : K ⟶ X n), k = k' ≫ t.ι n := by
  -- `k ≫ e = 0`, since `e ≫ (1 - σ)⟦1⟧' = 0` and `(1 - σ)⟦1⟧'` is injective on maps from `K`.
  have he : k ≫ t.e = 0 := by
    obtain ⟨y, hy⟩ := (shiftFunctor T (1 : ℤ)).map_surjective
      ((shiftNegShift K (1 : ℤ)).hom ≫ k ≫ t.e)
    have h0 : y ≫ (𝟙 _ - telescopeShift X x) = 0 := by
      apply (shiftFunctor T (1 : ℤ)).map_injective
      rw [Functor.map_comp, hy, Functor.map_zero, Category.assoc, Category.assoc]
      have := comp_distTriang_mor_zero₃₁ _ t.distinguished
      dsimp at this
      rw [this, Limits.comp_zero, Limits.comp_zero]
    have hy0 : y = 0 := eq_zero_of_isFiniteSum X x ((hK.shift (-1)).isFiniteSum_of_small y) h0
    rw [hy0, Functor.map_zero] at hy
    apply (cancel_epi (shiftNegShift K (1 : ℤ)).hom).mp
    rw [Limits.comp_zero]
    exact hy.symm
  obtain ⟨b, rfl⟩ := Triangle.coyoneda_exact₃ _ t.distinguished k he
  obtain ⟨F, a, rfl⟩ := hK.isFiniteSum_of_small b
  have key : ∀ n ∈ F, n ≤ F.sup id := fun n hn => Finset.le_sup (f := id) hn
  refine ⟨F.sup id, ∑ p ∈ F.attach, a p.1 ≫ seqMap X x (key p.1 p.2), ?_⟩
  rw [Preadditive.sum_comp, Preadditive.sum_comp]
  conv_lhs => rw [← Finset.sum_attach]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Category.assoc, Category.assoc, seqMap_comp_ι]
  rfl

end Telescope

end RigidDescent
