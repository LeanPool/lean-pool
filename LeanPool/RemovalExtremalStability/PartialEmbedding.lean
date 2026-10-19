/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform
public import Mathlib.Tactic

/-!
# Extending a partial graph embedding

The existence and counting lemmas use the same local extension step. Their estimates for how many
extension vertices exist remain separate.
-/

@[expose] public section

open Finset SimpleGraph

namespace PartialEmbedding

noncomputable def candidates {α β : Type*} (G : SimpleGraph α) (L : SimpleGraph β)
    (parts : β → Finset α) (f : β → α) (S : Finset β) (y : β) : Finset α := by
  classical
  exact {w ∈ parts y | ∀ z ∈ S, L.Adj z y → G.Adj (f z) w}

/-- An admissible new image extends a partial embedding and preserves the lower bounds on all
remaining candidate sets. The density argument that produces an admissible image is kept in the
respective existence and counting lemmas. -/
theorem extend {α β : Type*} [DecidableEq α] [DecidableEq β]
    (G : SimpleGraph α) [DecidableRel G.Adj] (L : SimpleGraph β)
    (parts : β → Finset α) {d : ℝ} (hd : 0 < d) (hd₁ : d ≤ 1)
    (S : Finset β) (x : β) (hxS : x ∉ S) (f : β → α) (v : α)
    (hinj : Set.InjOn f S) (hmem : ∀ z ∈ S, f z ∈ parts z)
    (hadj : ∀ a ∈ S, ∀ b ∈ S, L.Adj a b → G.Adj (f a) (f b))
    (hcand : ∀ y ∉ S, d ^ #S * #(parts y) ≤ #(candidates G L parts f S y))
    (hvC : v ∈ candidates G L parts f S x) (hvS : v ∉ S.image f)
    (hgood : ∀ y, y ∉ insert x S → L.Adj x y →
      d * #(candidates G L parts f S y) ≤
        #{w ∈ candidates G L parts f S y | G.Adj v w}) :
    Set.InjOn (Function.update f x v) (↑(insert x S) : Set β) ∧
      (∀ z ∈ insert x S, Function.update f x v z ∈ parts z) ∧
      (∀ a ∈ insert x S, ∀ b ∈ insert x S, L.Adj a b →
        G.Adj (Function.update f x v a) (Function.update f x v b)) ∧
      ∀ y ∉ insert x S,
        d ^ #(insert x S) * #(parts y) ≤
          #(candidates G L parts (Function.update f x v) (insert x S) y) := by
  classical
  have hvC' : v ∈ parts x ∧ ∀ z ∈ S, L.Adj z x → G.Adj (f z) v := by
    simpa only [candidates, mem_filter] using hvC
  have hfS : ∀ z ∈ S, Function.update f x v z = f z := fun z hz =>
    Function.update_of_ne (by rintro rfl; exact hxS hz) _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [coe_insert, Set.injOn_insert (by simpa using hxS)]
    refine ⟨fun a ha b hb h => hinj ha hb ?_, ?_⟩
    · rwa [hfS a ha, hfS b hb] at h
    · rintro ⟨z, hz, hzv⟩
      rw [Function.update_self, hfS z hz] at hzv
      exact hvS (mem_image.2 ⟨z, hz, hzv⟩)
  · intro z hz
    rcases mem_insert.1 hz with rfl | hz
    · simpa using hvC'.1
    · rw [hfS z hz]; exact hmem z hz
  · have key : ∀ z ∈ S, L.Adj z x → G.Adj (f z) v := fun z hz h => hvC'.2 z hz h
    intro a ha b hb hab
    rcases mem_insert.1 ha with hax | ha' <;> rcases mem_insert.1 hb with hbx | hb'
    · subst hax; subst hbx; exact absurd hab (SimpleGraph.irrefl _)
    · subst hax; rw [Function.update_self, hfS b hb']; exact (key b hb' hab.symm).symm
    · subst hbx; rw [Function.update_self, hfS a ha']; exact key a ha' hab
    · rw [hfS a ha', hfS b hb']; exact hadj a ha' b hb' hab
  · intro y hy
    rw [mem_insert, not_or] at hy
    rw [card_insert_of_notMem hxS, pow_succ]
    by_cases hxy : L.Adj x y
    · have hsub : {w ∈ candidates G L parts f S y | G.Adj v w} ⊆
          candidates G L parts (Function.update f x v) (insert x S) y := by
        intro w hw
        simp only [candidates, mem_filter, mem_insert] at hw ⊢
        refine ⟨hw.1.1, ?_⟩
        rintro z (rfl | hz) hzy
        · simpa using hw.2
        · rw [hfS z hz]; exact hw.1.2 z hz hzy
      calc d ^ #S * d * (#(parts y) : ℝ) = d * (d ^ #S * #(parts y)) := by ring
        _ ≤ d * #(candidates G L parts f S y) := by gcongr; exact hcand y hy.2
        _ ≤ _ := hgood y (by simp [hy.1, hy.2]) hxy
        _ ≤ _ := by exact_mod_cast card_le_card hsub
    · have hsub : candidates G L parts f S y ⊆
          candidates G L parts (Function.update f x v) (insert x S) y := by
        intro w hw
        simp only [candidates, mem_filter, mem_insert] at hw ⊢
        refine ⟨hw.1, ?_⟩
        rintro z (rfl | hz) hzy
        · exact absurd hzy hxy
        · rw [hfS z hz]; exact hw.2 z hz hzy
      calc d ^ #S * d * (#(parts y) : ℝ) ≤ d ^ #S * 1 * #(parts y) := by gcongr
        _ = d ^ #S * #(parts y) := by ring
        _ ≤ _ := hcand y hy.2
        _ ≤ _ := by exact_mod_cast card_le_card hsub

end PartialEmbedding
