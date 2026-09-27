/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the weighted nibble with slack

`Nibble.fracNibbleWeighted_nearPerfect` needs the fractional matching `w` to *saturate* almost
every vertex (load `≥ 1 - γ` outside a small exceptional set).  A fractional triangle packing of a
general graph is very far from that: most vertices carry very little load.

This file removes the hypothesis by **padding**.  Write

    S := |X| - ∑_v load w v

for the total slack.  Add `2m` dummy vertices (`m ≈ S`), split into a "left" and a "right" half, and
for every real vertex `v` and every pair `(i, j)` of a left and a right dummy add the triple
`{v, i, j}` with weight `(1 - load w v) / m²`.  Then

* every real vertex has load exactly `1`;
* every dummy has load exactly `S / m ∈ [1 - γ, 1]`;
* all weighted codegrees are at most `max γ (1/m)`;
* the total weight goes up by exactly `S`.

So the padded system is near-perfect and `fracNibble_weightedCodegree` applies. A matching of the
padded hypergraph uses at most `m` of the added triples (each contains a left dummy, and they are
disjoint), so the real part of the matching has at least `(1-β)(∑w + S) - m ≥ (1-β)∑w - βS - 1`
edges.

The result is `Nibble.fracNibble_withSlack`: no regularity, no near-perfection, only small weighted
codegrees and *enough slack*.  Sorry-free and axiom-clean.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.WeightedSpreadNibble

/-! # Three-uniform weighted rounding with total slack -/

@[expose] public section

open Finset Hypergraph

namespace Nibble

namespace Slack

variable {X : Type} [DecidableEq X]

/-- The `w`-load of a vertex: the total weight of the edges through it. -/
def wLoad (K : Finset (Finset X)) (w : Finset X → ℝ) (v : X) : ℝ :=
  ∑ T ∈ K.filter (fun T => v ∈ T), w T

/-- The padded vertex type: the real vertices together with `2m` dummies, `m` on each side. -/
abbrev Pad (X : Type) (m : ℕ) := X ⊕ (Fin m × Bool)

/-- The added triple joining the real vertex `v` to the left dummy `i` and the right dummy `j`. -/
def mixTriple (m : ℕ) (v : X) (i j : Fin m) : Finset (Pad X m) :=
  {Sum.inl v, Sum.inr (i, false), Sum.inr (j, true)}

/-- The padded hypergraph: the image of `K` together with all the mixed triples. -/
def padFam [Fintype X] (K : Finset (Finset X)) (m : ℕ) : Finset (Finset (Pad X m)) :=
  K.image (Finset.image Sum.inl) ∪
    (Finset.univ : Finset (X × Fin m × Fin m)).image (fun t => mixTriple m t.1 t.2.1 t.2.2)

/-- The padded weighting. -/
noncomputable def padWt (K : Finset (Finset X)) (w : Finset X → ℝ) (m : ℕ) :
    Finset (Pad X m) → ℝ :=
  fun U => if U.toRight = ∅ then w U.toLeft
           else (∑ v ∈ U.toLeft, (1 - wLoad K w v)) / (m : ℝ) ^ 2

section
variable (K : Finset (Finset X)) (w : Finset X → ℝ) (m : ℕ)

@[simp] lemma toLeft_image_inl (T : Finset X) :
    (T.image (Sum.inl : X → Pad X m)).toLeft = T := by
  ext x; simp

@[simp] lemma toRight_image_inl (T : Finset X) :
    (T.image (Sum.inl : X → Pad X m)).toRight = (∅ : Finset (Fin m × Bool)) := by
  ext x; simp

@[simp] lemma mixTriple_toLeft (v : X) (i j : Fin m) :
    (mixTriple m v i j).toLeft = {v} := by
  ext x; simp [mixTriple]

@[simp] lemma mixTriple_toRight (v : X) (i j : Fin m) :
    (mixTriple m v i j).toRight = {(i, false), (j, true)} := by
  ext x; simp [mixTriple]

lemma mixTriple_card (v : X) (i j : Fin m) : (mixTriple m v i j).card = 3 := by
  simp [mixTriple, Finset.card_insert_of_notMem]

lemma mem_mixTriple_inl (v u : X) (i j : Fin m) :
    (Sum.inl u : Pad X m) ∈ mixTriple m v i j ↔ u = v := by
  simp [mixTriple]

lemma mem_mixTriple_inr (v : X) (i j : Fin m) (d : Fin m × Bool) :
    (Sum.inr d : Pad X m) ∈ mixTriple m v i j ↔ d = (i, false) ∨ d = (j, true) := by
  simp [mixTriple]

lemma mixTriple_inj {v v' : X} {i i' j j' : Fin m}
    (h : mixTriple m v i j = mixTriple m v' i' j') : v = v' ∧ i = i' ∧ j = j' := by
  have hL : ({v} : Finset X) = {v'} := by
    have := congrArg Finset.toLeft h; simpa using this
  have hR : ({(i, false), (j, true)} : Finset (Fin m × Bool)) = {(i', false), (j', true)} := by
    have := congrArg Finset.toRight h; simpa using this
  refine ⟨by simpa using hL, ?_, ?_⟩
  · have : ((i, false) : Fin m × Bool) ∈ ({(i', false), (j', true)} : Finset (Fin m × Bool)) := by
      rw [← hR]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at this
    rcases this with h1 | h2
    · exact h1.1
    · exact absurd h2.2 (by simp)
  · have : ((j, true) : Fin m × Bool) ∈ ({(i', false), (j', true)} : Finset (Fin m × Bool)) := by
      rw [← hR]; simp
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at this
    rcases this with h1 | h2
    · exact absurd h1.2 (by simp)
    · exact h2.1

lemma padWt_image_inl (T : Finset X) : padWt K w m (T.image Sum.inl) = w T := by
  simp [padWt]

lemma padWt_mixTriple (v : X) (i j : Fin m) :
    padWt K w m (mixTriple m v i j) = (1 - wLoad K w v) / (m : ℝ) ^ 2 := by
  simp [padWt]

lemma padWt_nonneg (hw : ∀ T, 0 ≤ w T) (hload : ∀ v : X, wLoad K w v ≤ 1) (U : Finset (Pad X m)) :
    0 ≤ padWt K w m U := by
  rw [padWt]
  split
  · exact hw _
  · have : 0 ≤ ∑ v ∈ U.toLeft, (1 - wLoad K w v) :=
      Finset.sum_nonneg fun v _ => by linarith only [hload v]
    positivity

end

section
variable [Fintype X] (K : Finset (Finset X)) (w : Finset X → ℝ) (m : ℕ)

/-- The two halves of the padded family are disjoint, and both index maps are injective: so a sum
over `padFam` splits into a sum over `K` and a sum over the mixed triples. -/
lemma sum_padFam (f : Finset (Pad X m) → ℝ) :
    ∑ U ∈ padFam K m, f U
      = (∑ T ∈ K, f (T.image Sum.inl))
        + ∑ v : X, ∑ i : Fin m, ∑ j : Fin m, f (mixTriple m v i j) := by
  classical
  have hdisj : Disjoint (K.image (Finset.image (Sum.inl : X → Pad X m)))
      ((Finset.univ : Finset (X × Fin m × Fin m)).image
        (fun t => mixTriple m t.1 t.2.1 t.2.2)) := by
    rw [Finset.disjoint_left]
    rintro U hU hU'
    rw [Finset.mem_image] at hU hU'
    obtain ⟨T, -, rfl⟩ := hU
    obtain ⟨t, -, ht⟩ := hU'
    have h1 : (T.image (Sum.inl : X → Pad X m)).toRight = ∅ := by simp
    rw [← ht] at h1
    simp at h1
  rw [padFam, Finset.sum_union hdisj]
  congr 1
  · exact Finset.sum_image (fun T _ T' _ h => Finset.image_injective Sum.inl_injective h)
  · rw [Finset.sum_image (fun t _ t' _ h => ?_)]
    · rw [Fintype.sum_prod_type]
      exact Finset.sum_congr rfl fun v _ => by rw [Fintype.sum_prod_type]
    · obtain ⟨h1, h2, h3⟩ := mixTriple_inj m h
      exact Prod.ext h1 (Prod.ext h2 h3)

/-- **Weighted handshake.**  For a `3`-uniform hypergraph the loads add up to `3` times the total
weight. -/
lemma sum_wLoad (h3 : IsUniform K 3) : ∑ x : X, wLoad K w x = 3 * ∑ T ∈ K, w T := by
  classical
  simp_rw [wLoad, Finset.sum_filter]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, h3 T hT, nsmul_eq_mul]
  norm_num

/-- The total slack of the weighting. -/
def slackTotal : ℝ := ∑ v : X, (1 - wLoad K w v)

lemma padLoad_inl (hm : 0 < m) (v : X) :
    ∑ U ∈ (padFam K m).filter (fun U => (Sum.inl v : Pad X m) ∈ U), padWt K w m U = 1 := by
  classical
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [Finset.sum_filter, sum_padFam]
  have h1 : (∑ T ∈ K, if (Sum.inl v : Pad X m) ∈ T.image Sum.inl then
        padWt K w m (T.image Sum.inl) else 0) = wLoad K w v := by
    rw [wLoad, Finset.sum_filter]
    refine Finset.sum_congr rfl fun T _ => ?_
    simp [padWt_image_inl]
  have h2 : ∀ u : X, (∑ i : Fin m, ∑ j : Fin m,
      if (Sum.inl v : Pad X m) ∈ mixTriple m u i j then padWt K w m (mixTriple m u i j) else 0)
      = if u = v then (1 - wLoad K w u) else 0 := by
    intro u
    simp only [mem_mixTriple_inl, padWt_mixTriple]
    by_cases huv : v = u
    · subst huv
      simp only [ite_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    · rw [ite_eq_right huv, ite_eq_right (fun h => huv h.symm)]
      simp
  rw [h1, Finset.sum_congr rfl (fun u _ => h2 u), Finset.sum_ite_eq' Finset.univ v
    (fun u => 1 - wLoad K w u)]
  simp

lemma padLoad_inr (hm : 0 < m) (d : Fin m × Bool) :
    ∑ U ∈ (padFam K m).filter (fun U => (Sum.inr d : Pad X m) ∈ U), padWt K w m U
      = slackTotal K w / (m : ℝ) := by
  classical
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [Finset.sum_filter, sum_padFam]
  have h1 : (∑ T ∈ K, if (Sum.inr d : Pad X m) ∈ T.image Sum.inl then
        padWt K w m (T.image Sum.inl) else 0) = 0 := by
    refine Finset.sum_eq_zero fun T _ => ?_
    simp
  have h2 : ∀ u : X, (∑ i : Fin m, ∑ j : Fin m,
      if (Sum.inr d : Pad X m) ∈ mixTriple m u i j then padWt K w m (mixTriple m u i j) else 0)
      = (1 - wLoad K w u) / (m : ℝ) := by
    intro u
    simp only [mem_mixTriple_inr, padWt_mixTriple]
    obtain ⟨d1, b⟩ := d
    cases b
    · have : ∑ i : Fin m, ∑ j : Fin m,
          (if ((d1, false) : Fin m × Bool) = (i, false) ∨ ((d1, false) : Fin m × Bool) = (j, true)
            then (1 - wLoad K w u) / (m : ℝ) ^ 2 else 0)
          = (m : ℝ) * ((1 - wLoad K w u) / (m : ℝ) ^ 2) := by simp
      rw [this]
      field_simp
    · have : ∑ i : Fin m, ∑ j : Fin m,
          (if ((d1, true) : Fin m × Bool) = (i, false) ∨ ((d1, true) : Fin m × Bool) = (j, true)
            then (1 - wLoad K w u) / (m : ℝ) ^ 2 else 0)
          = (m : ℝ) * ((1 - wLoad K w u) / (m : ℝ) ^ 2) := by simp
      rw [this]
      field_simp
  rw [h1, Finset.sum_congr rfl (fun u _ => h2 u), zero_add, slackTotal, Finset.sum_div]

lemma padFam_uniform (hK : IsUniform K 3) : IsUniform (padFam K m) 3 := by
  intro U hU
  rw [padFam, Finset.mem_union] at hU
  rcases hU with hU | hU
  · rw [Finset.mem_image] at hU
    obtain ⟨T, hT, rfl⟩ := hU
    rw [Finset.card_image_of_injective _ Sum.inl_injective]
    exact hK T hT
  · rw [Finset.mem_image] at hU
    obtain ⟨t, -, rfl⟩ := hU
    exact mixTriple_card m t.1 t.2.1 t.2.2

lemma slackTotal_nonneg (hload : ∀ v : X, wLoad K w v ≤ 1) : 0 ≤ slackTotal K w :=
  Finset.sum_nonneg fun v _ => by linarith only [hload v]

lemma sum_padWt (hm : 0 < m) :
    ∑ U ∈ padFam K m, padWt K w m U = (∑ T ∈ K, w T) + slackTotal K w := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [sum_padFam]
  congr 1
  · exact Finset.sum_congr rfl fun T _ => padWt_image_inl K w m T
  · rw [slackTotal]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [padWt_mixTriple, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

lemma padCodeg_inl_inl {v v' : X} (hvv : v ≠ v') :
    ∑ U ∈ (padFam K m).filter
        (fun U => (Sum.inl v : Pad X m) ∈ U ∧ (Sum.inl v' : Pad X m) ∈ U), padWt K w m U
      = ∑ T ∈ K.filter (fun T => v ∈ T ∧ v' ∈ T), w T := by
  classical
  rw [Finset.sum_filter, sum_padFam, Finset.sum_filter]
  have h2 : ∀ u : X, (∑ i : Fin m, ∑ j : Fin m,
      if (Sum.inl v : Pad X m) ∈ mixTriple m u i j ∧ (Sum.inl v' : Pad X m) ∈ mixTriple m u i j
        then padWt K w m (mixTriple m u i j) else 0) = 0 := by
    intro u
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    rw [ite_eq_right]
    rintro ⟨h1, h2⟩
    rw [mem_mixTriple_inl] at h1 h2
    exact hvv (h1.trans h2.symm)
  rw [Finset.sum_congr rfl (fun u _ => h2 u), Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun T _ => ?_
  simp [padWt_image_inl]

lemma padCodeg_inl_inr (hm : 0 < m) (v : X) (d : Fin m × Bool) :
    ∑ U ∈ (padFam K m).filter
        (fun U => (Sum.inl v : Pad X m) ∈ U ∧ (Sum.inr d : Pad X m) ∈ U), padWt K w m U
      = (1 - wLoad K w v) / (m : ℝ) := by
  classical
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [Finset.sum_filter, sum_padFam]
  have h1 : (∑ T ∈ K, if (Sum.inl v : Pad X m) ∈ T.image Sum.inl ∧
        (Sum.inr d : Pad X m) ∈ T.image Sum.inl then padWt K w m (T.image Sum.inl) else 0) = 0 :=
    Finset.sum_eq_zero fun T _ => by simp
  have h2 : ∀ u : X, (∑ i : Fin m, ∑ j : Fin m,
      if (Sum.inl v : Pad X m) ∈ mixTriple m u i j ∧ (Sum.inr d : Pad X m) ∈ mixTriple m u i j
        then padWt K w m (mixTriple m u i j) else 0)
      = if u = v then (1 - wLoad K w u) / (m : ℝ) else 0 := by
    intro u
    simp only [mem_mixTriple_inl, mem_mixTriple_inr, padWt_mixTriple]
    by_cases huv : v = u
    · subst huv
      obtain ⟨d1, b⟩ := d
      cases b
      · have : ∑ i : Fin m, ∑ j : Fin m,
            (if (v = v) ∧ (((d1, false) : Fin m × Bool) = (i, false) ∨
                ((d1, false) : Fin m × Bool) = (j, true))
              then (1 - wLoad K w v) / (m : ℝ) ^ 2 else 0)
            = (m : ℝ) * ((1 - wLoad K w v) / (m : ℝ) ^ 2) := by simp
        rw [this, ite_eq_left rfl]
        field_simp
      · have : ∑ i : Fin m, ∑ j : Fin m,
            (if (v = v) ∧ (((d1, true) : Fin m × Bool) = (i, false) ∨
                ((d1, true) : Fin m × Bool) = (j, true))
              then (1 - wLoad K w v) / (m : ℝ) ^ 2 else 0)
            = (m : ℝ) * ((1 - wLoad K w v) / (m : ℝ) ^ 2) := by simp
        rw [this, ite_eq_left rfl]
        field_simp
    · rw [ite_eq_right (fun h => huv h.symm)]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      rw [ite_eq_right]
      rintro ⟨h, -⟩
      exact huv h
  rw [h1, Finset.sum_congr rfl (fun u _ => h2 u), zero_add,
    Finset.sum_ite_eq' Finset.univ v (fun u => (1 - wLoad K w u) / (m : ℝ))]
  simp

lemma padCodeg_inr_inr (hm : 0 < m) (hload : ∀ v : X, wLoad K w v ≤ 1) {d d' : Fin m × Bool}
    (hd : d ≠ d') :
    ∑ U ∈ (padFam K m).filter
        (fun U => (Sum.inr d : Pad X m) ∈ U ∧ (Sum.inr d' : Pad X m) ∈ U), padWt K w m U
      ≤ slackTotal K w / (m : ℝ) ^ 2 := by
  classical
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [Finset.sum_filter, sum_padFam]
  have h1 : (∑ T ∈ K, if (Sum.inr d : Pad X m) ∈ T.image Sum.inl ∧
        (Sum.inr d' : Pad X m) ∈ T.image Sum.inl then padWt K w m (T.image Sum.inl) else 0) = 0 :=
    Finset.sum_eq_zero fun T _ => by simp
  have h2 : ∀ u : X, (∑ i : Fin m, ∑ j : Fin m,
      if (Sum.inr d : Pad X m) ∈ mixTriple m u i j ∧ (Sum.inr d' : Pad X m) ∈ mixTriple m u i j
        then padWt K w m (mixTriple m u i j) else 0)
      ≤ (1 - wLoad K w u) / (m : ℝ) ^ 2 := by
    intro u
    have hnn : 0 ≤ (1 - wLoad K w u) / (m : ℝ) ^ 2 :=
      div_nonneg (by linarith only [hload u]) (by positivity)
    simp only [mem_mixTriple_inr, padWt_mixTriple]
    obtain ⟨a, b⟩ := d
    obtain ⟨a', b'⟩ := d'
    cases b <;> cases b'
    · have hne : a ≠ a' := fun h => hd (by rw [h])
      refine le_of_eq_of_le ?_ hnn
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      rw [ite_eq_right]
      rintro ⟨h, h'⟩
      simp only [Prod.mk.injEq, Bool.false_eq_true, and_false, or_false, and_true] at h h'
      exact hne (h.trans h'.symm)
    · have : ∑ i : Fin m, ∑ j : Fin m,
          (if (((a, false) : Fin m × Bool) = (i, false) ∨ ((a, false) : Fin m × Bool) = (j, true)) ∧
              (((a', true) : Fin m × Bool) = (i, false) ∨ ((a', true) : Fin m × Bool) = (j, true))
            then (1 - wLoad K w u) / (m : ℝ) ^ 2 else 0)
          = (1 - wLoad K w u) / (m : ℝ) ^ 2 := by simp [ite_and]
      exact le_of_eq this
    · have : ∑ i : Fin m, ∑ j : Fin m,
          (if (((a, true) : Fin m × Bool) = (i, false) ∨ ((a, true) : Fin m × Bool) = (j, true)) ∧
              (((a', false) : Fin m × Bool) = (i, false) ∨ ((a', false) : Fin m × Bool) = (j, true))
            then (1 - wLoad K w u) / (m : ℝ) ^ 2 else 0)
          = (1 - wLoad K w u) / (m : ℝ) ^ 2 := by simp [ite_and]
      exact le_of_eq this
    · have hne : a ≠ a' := fun h => hd (by rw [h])
      refine le_of_eq_of_le ?_ hnn
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      rw [ite_eq_right]
      rintro ⟨h, h'⟩
      simp only [Prod.mk.injEq, Bool.true_eq_false, and_false, false_or, and_true] at h h'
      exact hne (h.trans h'.symm)
  rw [h1, zero_add, slackTotal, Finset.sum_div]
  exact Finset.sum_le_sum fun u _ => h2 u

/-- A member of the padded family with no dummy vertices comes from `K`. -/
lemma mem_padFam_of_toRight_empty {U : Finset (Pad X m)} (hU : U ∈ padFam K m)
    (hR : U.toRight = ∅) : U.toLeft ∈ K ∧ U = U.toLeft.image Sum.inl := by
  rw [padFam, Finset.mem_union] at hU
  rcases hU with hU | hU
  · rw [Finset.mem_image] at hU
    obtain ⟨T, hT, rfl⟩ := hU
    rw [toLeft_image_inl]
    exact ⟨hT, rfl⟩
  · rw [Finset.mem_image] at hU
    obtain ⟨t, -, rfl⟩ := hU
    exfalso
    have : ((t.2.1, false) : Fin m × Bool) ∈ (mixTriple m t.1 t.2.1 t.2.2).toRight := by simp
    rw [hR] at this
    simp at this

/-- A member of the padded family that does use a dummy contains a *left* dummy. -/
lemma exists_left_dummy {U : Finset (Pad X m)} (hU : U ∈ padFam K m) (hR : U.toRight ≠ ∅) :
    ∃ i : Fin m, (Sum.inr (i, false) : Pad X m) ∈ U := by
  rw [padFam, Finset.mem_union] at hU
  rcases hU with hU | hU
  · rw [Finset.mem_image] at hU
    obtain ⟨T, -, rfl⟩ := hU
    exact absurd (by simp) hR
  · rw [Finset.mem_image] at hU
    obtain ⟨t, -, rfl⟩ := hU
    exact ⟨t.2.1, by simp [mixTriple]⟩

/-- A matching of the padded family uses at most `m` of the added triples: they are disjoint and
each contains one of the `m` left dummies. -/
lemma card_mixedPart_le (hm : 0 < m) {M : Finset (Finset (Pad X m))}
    (hM : IsMatching (padFam K m) M) :
    ((M.filter (fun U => U.toRight ≠ ∅)).card : ℝ) ≤ (m : ℝ) := by
  classical
  have hcard : (M.filter (fun U => U.toRight ≠ ∅)).card ≤ m := by
    have key : ∀ U ∈ M.filter (fun U => U.toRight ≠ ∅),
        ∃ i : Fin m, (Sum.inr (i, false) : Pad X m) ∈ U := by
      intro U hU
      rw [Finset.mem_filter] at hU
      exact exists_left_dummy K m (hM.subset hU.1) hU.2
    set f : Finset (Pad X m) → Fin m := fun U =>
      if h : ∃ i : Fin m, (Sum.inr (i, false) : Pad X m) ∈ U then h.choose else ⟨0, hm⟩ with hf
    have hfmem : ∀ U ∈ M.filter (fun U => U.toRight ≠ ∅),
        (Sum.inr (f U, false) : Pad X m) ∈ U := by
      intro U hU
      have h := key U hU
      rw [hf]
      simp only [dite_eq_left h]
      exact h.choose_spec
    have : (M.filter (fun U => U.toRight ≠ ∅)).card ≤ (Finset.univ : Finset (Fin m)).card := by
      refine Finset.card_le_card_of_injOn f (fun U _ => by simp) ?_
      intro U hU V hV hUV
      by_contra hne
      have hUM := (Finset.mem_filter.mp hU).1
      have hVM := (Finset.mem_filter.mp hV).1
      have hdisj := hM.disjoint U hUM V hVM hne
      have h1 := hfmem U hU
      have h2 := hfmem V hV
      rw [hUV] at h1
      exact (Finset.disjoint_left.mp hdisj h1) h2
    simpa using this
  exact_mod_cast hcard

/-- The real part of a matching of the padded family projects to a matching of `K` of the same
size. -/
lemma exists_matching_of_padMatching {M : Finset (Finset (Pad X m))}
    (hM : IsMatching (padFam K m) M) :
    ∃ M' : Finset (Finset X), IsMatching K M' ∧
      (M'.card : ℝ) = ((M.filter (fun U => U.toRight = ∅)).card : ℝ) := by
  classical
  set R := M.filter (fun U => U.toRight = ∅) with hR
  have hmem : ∀ U ∈ R, U.toLeft ∈ K ∧ U = U.toLeft.image Sum.inl := by
    intro U hU
    rw [hR, Finset.mem_filter] at hU
    exact mem_padFam_of_toRight_empty K m (hM.subset hU.1) hU.2
  have hinj : Set.InjOn (Finset.toLeft : Finset (Pad X m) → Finset X) ↑R := by
    intro U hU V hV h
    rw [(hmem U hU).2, (hmem V hV).2, h]
  refine ⟨R.image Finset.toLeft, ⟨?_, ?_⟩, ?_⟩
  · intro T hT
    rw [Finset.mem_image] at hT
    obtain ⟨U, hU, rfl⟩ := hT
    exact (hmem U hU).1
  · intro T hT T' hT' hne
    rw [Finset.mem_image] at hT hT'
    obtain ⟨U, hU, rfl⟩ := hT
    obtain ⟨V, hV, rfl⟩ := hT'
    have hUV : U ≠ V := fun h => hne (by rw [h])
    have hdisj := hM.disjoint U (Finset.mem_filter.mp hU).1 V (Finset.mem_filter.mp hV).1 hUV
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_toLeft] at hx hx'
    exact (Finset.disjoint_left.mp hdisj hx) hx'
  · rw [Finset.card_image_of_injOn hinj]

lemma padCodeg_comm (x z : Pad X m) :
    ∑ U ∈ (padFam K m).filter (fun U => x ∈ U ∧ z ∈ U), padWt K w m U
      = ∑ U ∈ (padFam K m).filter (fun U => z ∈ U ∧ x ∈ U), padWt K w m U := by
  refine Finset.sum_congr (Finset.filter_congr fun U _ => ?_) fun _ _ => rfl
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

end

end Slack

/-- **The weighted nibble with slack.**  No near-perfection hypothesis: instead the weighting is
required to leave a total slack `S = |X| - ∑_v load v` of at least `1/γ`, and the conclusion loses
`β·|X| + 1`. -/
theorem fracNibble_withSlack (β : ℝ) (hβ : 0 < β) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ {X : Type} [Fintype X] [DecidableEq X] (K : Finset (Finset X)) (w : Finset X → ℝ),
        IsUniform K 3 →
        (∀ T, 0 ≤ w T) →
        (∀ v : X, Slack.wLoad K w v ≤ 1) →
        (∀ x z : X, x ≠ z → ∑ T ∈ K.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ) →
        1 / γ ≤ (Fintype.card X : ℝ) - ∑ v : X, Slack.wLoad K w v →
        ∃ M : Finset (Finset X), IsMatching K M ∧
          (1 - β) * (∑ T ∈ K, w T) - β * (Fintype.card X : ℝ) - 1 ≤ (M.card : ℝ) := by
  classical
  obtain ⟨γ₀, hγ₀, η, hη, hmain⟩ := fracNibble_weightedCodegree 3 (by norm_num) β hβ
  have hγpos : 0 < min γ₀ 1 := lt_min hγ₀ one_pos
  refine ⟨min γ₀ 1, hγpos, ?_⟩
  intro X _ _ K w hK hw hload hcod hslack
  have hγle : min γ₀ 1 ≤ γ₀ := min_le_left _ _
  have hγ1 : min γ₀ 1 ≤ 1 := min_le_right _ _
  set γ := min γ₀ 1 with hγdef
  set S := Slack.slackTotal K w with hSdef
  have hSeq : S = (Fintype.card X : ℝ) - ∑ v : X, Slack.wLoad K w v := by
    rw [hSdef, Slack.slackTotal, Finset.sum_sub_distrib]
    simp
  have hS : 1 / γ ≤ S := by rw [hSeq]; exact hslack
  have hγS : 1 ≤ S * γ := (div_le_iff₀ hγpos).mp hS
  have hS1 : 1 ≤ S := by nlinarith
  set m := ⌈S⌉₊ with hmdef
  have hmS : S ≤ (m : ℝ) := Nat.le_ceil S
  have hmpos : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le (by linarith) hmS
  have hm : 0 < m := by exact_mod_cast hmpos
  have hmlt : (m : ℝ) < S + 1 := Nat.ceil_lt_add_one (by linarith)
  have hinvm : 1 / (m : ℝ) ≤ γ := by
    rw [div_le_iff₀ hmpos]; nlinarith
  -- the padded system satisfies every hypothesis of the near-perfect weighted nibble
  have hunif := Slack.padFam_uniform K m hK
  have hnn := Slack.padWt_nonneg K w m hw hload
  have hle : ∀ v : Slack.Pad X m,
      ∑ U ∈ (Slack.padFam K m).filter (fun U => v ∈ U), Slack.padWt K w m U ≤ 1 := by
    intro v
    cases v with
    | inl a => rw [Slack.padLoad_inl K w m hm a]
    | inr d =>
        rw [Slack.padLoad_inr K w m hm d, div_le_one hmpos]
        exact hmS
  have hge : ∀ v : Slack.Pad X m, v ∉ (∅ : Finset (Slack.Pad X m)) →
      1 - γ₀ ≤ ∑ U ∈ (Slack.padFam K m).filter (fun U => v ∈ U), Slack.padWt K w m U := by
    rintro v -
    cases v with
    | inl a => rw [Slack.padLoad_inl K w m hm a]; linarith
    | inr d =>
        rw [Slack.padLoad_inr K w m hm d, le_div_iff₀ hmpos]
        nlinarith
  have hexc : ((∅ : Finset (Slack.Pad X m)).card : ℝ)
      ≤ η * (Fintype.card (Slack.Pad X m) : ℝ) := by
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  have hcodeg : ∀ x z : Slack.Pad X m, x ≠ z →
      ∑ U ∈ (Slack.padFam K m).filter (fun U => x ∈ U ∧ z ∈ U), Slack.padWt K w m U ≤ γ₀ := by
    intro x z hxz
    have hmixbound : ∀ a : X, (1 - Slack.wLoad K w a) / (m : ℝ) ≤ γ₀ := by
      intro a
      have h0 : 0 ≤ Slack.wLoad K w a := Finset.sum_nonneg fun T _ => hw T
      have : (1 - Slack.wLoad K w a) / (m : ℝ) ≤ 1 / (m : ℝ) := by
        gcongr
        linarith
      linarith [hinvm]
    cases x with
    | inl a =>
        cases z with
        | inl b =>
            have hab : a ≠ b := fun h => hxz (by rw [h])
            rw [Slack.padCodeg_inl_inl K w m hab]
            exact le_trans (hcod a b hab) hγle
        | inr d =>
            rw [Slack.padCodeg_inl_inr K w m hm a d]
            exact hmixbound a
    | inr d =>
        cases z with
        | inl b =>
            rw [Slack.padCodeg_comm, Slack.padCodeg_inl_inr K w m hm b d]
            exact hmixbound b
        | inr d' =>
            have hdd : d ≠ d' := fun h => hxz (by rw [h])
            refine le_trans (Slack.padCodeg_inr_inr K w m hm hload hdd) ?_
            have hSnn : 0 ≤ S := by linarith
            have : S / (m : ℝ) ^ 2 ≤ 1 / (m : ℝ) := by
              rw [div_le_div_iff₀ (by positivity) hmpos]
              nlinarith
            linarith [hinvm]
  obtain ⟨M, hM, -, hMcard⟩ :=
    hmain (Slack.padFam K m) (Slack.padWt K w m) ∅ hunif hnn hle hge hexc hcodeg
  rw [Slack.sum_padWt K w m hm] at hMcard
  have hsplit : ((M.filter (fun U => U.toRight = ∅)).card : ℝ)
      + ((M.filter (fun U => ¬ (U.toRight = ∅))).card : ℝ) = (M.card : ℝ) := by
    rw [← Nat.cast_add, Finset.card_filter_add_card_filter_not]
  have hmix := Slack.card_mixedPart_le K m hm hM
  obtain ⟨M', hM', hM'card⟩ := Slack.exists_matching_of_padMatching K m hM
  refine ⟨M', hM', ?_⟩
  have hloadnn : (0 : ℝ) ≤ ∑ v : X, Slack.wLoad K w v :=
    Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun T _ => hw T
  have hScard : S ≤ (Fintype.card X : ℝ) := by rw [hSeq]; linarith
  rw [hM'card]
  nlinarith only [hMcard, hmix, hsplit, hScard, hmlt, hβ.le]

-- Axiom check: `[propext, Classical.choice, Quot.sound]`.


end Nibble
