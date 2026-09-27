/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the weighted nibble with slack, in every uniformity

`Nibble.fracNibble_withSlack` (`Nibble.FracNibbleSlack`) removes the near-perfection hypothesis of
`Nibble.fracNibble_weightedCodegree` by padding, but only for `3`-uniform hypergraphs.  The
placement hypergraph of the box-allocation nibble has uniformity `6s₀²+1`, so the same padding is
carried out here for an arbitrary uniformity `r ≥ 3`.

The padding.  Write `k := r - 1` and `S := |X| - ∑_v load w v` for the total slack.  Add `k·m`
dummy vertices (`m := ⌈S⌉`) arranged in `k` *columns* `Fin m`, and for every real vertex `v` and
every choice `i : Fin k → Fin m` of one dummy per column add the edge
`{v} ∪ {(j, i j) : j}` with weight `(1 - load w v) / m^k`.  Then

* every real vertex has load exactly `1`;
* every dummy has load exactly `S / m ∈ [1 - γ, 1]`;
* the weighted codegree of two dummies is `0` (same column) or `S/m² ≤ 1/m` (different columns),
  and that of a real vertex and a dummy is `(1 - load v)/m ≤ 1/m`;
* the total weight goes up by exactly `S`.

A matching of the padded hypergraph uses at most `m` of the added edges (each contains a dummy of
column `0`, and they are disjoint), so the real part of the matching has at least
`(1-β)(∑w + S) - m ≥ (1-β)∑w - βS - 1` edges.

Sorry-free and axiom-clean.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.WeightedSlack3

/-! # Uniform weighted rounding with total slack -/

@[expose] public section

open Finset Hypergraph

namespace Nibble

namespace SlackR

variable {X : Type} [DecidableEq X]

/-- The padded vertex type: the real vertices together with `k` columns of `m` dummies. -/
abbrev PadR (X : Type) (k m : ℕ) := X ⊕ (Fin k × Fin m)

/-- The added edge joining the real vertex `v` to the dummy `i j` of every column `j`. -/
def mixEdge (k m : ℕ) (v : X) (i : Fin k → Fin m) : Finset (PadR X k m) :=
  insert (Sum.inl v) ((univ : Finset (Fin k)).image (fun j => Sum.inr (j, i j)))

/-- The padded hypergraph: the image of `K` together with all the mixed edges. -/
def padFamR [Fintype X] (K : Finset (Finset X)) (k m : ℕ) : Finset (Finset (PadR X k m)) :=
  K.image (Finset.image Sum.inl) ∪
    (univ : Finset (X × (Fin k → Fin m))).image (fun t => mixEdge k m t.1 t.2)

/-- The padded weighting. -/
noncomputable def padWtR (K : Finset (Finset X)) (w : Finset X → ℝ) (k m : ℕ) :
    Finset (PadR X k m) → ℝ :=
  fun U => if U.toRight = ∅ then w U.toLeft
           else (∑ v ∈ U.toLeft, (1 - Slack.wLoad K w v)) / (m : ℝ) ^ k

/-! ### Counting the dummy choices -/

/-- The number of choice functions with a prescribed value in one column. -/
theorem card_filter_eq_at (k m : ℕ) (j₀ : Fin k) (d : Fin m) :
    #(univ.filter (fun i : Fin k → Fin m => i j₀ = d)) = m ^ (k - 1) := by
  classical
  have h : (univ.filter (fun i : Fin k → Fin m => i j₀ = d))
      = Fintype.piFinset (fun j => if j = j₀ then ({d} : Finset (Fin m)) else univ) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h j
      split
      · next hj => subst hj; simpa using h
      · simp
    · intro h; have := h j₀; simpa using this
  rw [h, Fintype.card_piFinset, ← Finset.mul_prod_erase univ _ (Finset.mem_univ j₀)]
  rw [Finset.prod_congr rfl (fun j hj => by rw [ite_eq_right (Finset.ne_of_mem_erase hj)])]
  simp

/-- The number of choice functions with prescribed values in two distinct columns. -/
theorem card_filter_eq_at2 (k m : ℕ) {j₀ j₁ : Fin k} (hj : j₀ ≠ j₁) (d d' : Fin m) :
    #(univ.filter (fun i : Fin k → Fin m => i j₀ = d ∧ i j₁ = d')) = m ^ (k - 2) := by
  classical
  have h : (univ.filter (fun i : Fin k → Fin m => i j₀ = d ∧ i j₁ = d'))
      = Fintype.piFinset (fun j => if j = j₀ then ({d} : Finset (Fin m))
          else if j = j₁ then ({d'} : Finset (Fin m)) else univ) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro h j
      by_cases h0 : j = j₀
      · subst h0; simpa using h.1
      · by_cases h1 : j = j₁
        · subst h1; simp [h0, h.2]
        · simp [h0, h1]
    · intro h
      exact ⟨by have := h j₀; simpa using this,
        by have := h j₁; simp [Ne.symm hj] at this; simpa using this⟩
  rw [h, Fintype.card_piFinset, ← Finset.mul_prod_erase univ _ (Finset.mem_univ j₀),
    ← Finset.mul_prod_erase (univ.erase j₀) _
      (Finset.mem_erase.mpr ⟨Ne.symm hj, Finset.mem_univ j₁⟩)]
  rw [Finset.prod_congr rfl (fun j hj' => by
    rw [ite_eq_right (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hj')),
      ite_eq_right (Finset.ne_of_mem_erase hj')])]
  have hcard : #((univ.erase j₀).erase j₁) = k - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hj, Finset.mem_univ j₁⟩),
      Finset.card_erase_of_mem (Finset.mem_univ j₀)]
    simp [Nat.sub_sub]
  rw [ite_eq_left rfl, ite_eq_right (Ne.symm hj), ite_eq_left rfl]
  simp [hcard]

/-- The sum of a constant over the choice functions with a prescribed value in one column. -/
theorem sum_ite_at (k m : ℕ) (j₀ : Fin k) (d : Fin m) (c : ℝ) :
    ∑ i : (Fin k → Fin m), (if i j₀ = d then c else 0) = c * (m : ℝ) ^ (k - 1) := by
  classical
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, card_filter_eq_at,
    nsmul_eq_mul]
  push_cast
  ring

/-- The sum of a constant over the choice functions with prescribed values in two columns. -/
theorem sum_ite_at2 (k m : ℕ) {j₀ j₁ : Fin k} (hj : j₀ ≠ j₁) (d d' : Fin m) (c : ℝ) :
    ∑ i : (Fin k → Fin m), (if i j₀ = d ∧ i j₁ = d' then c else 0) = c * (m : ℝ) ^ (k - 2) := by
  classical
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, card_filter_eq_at2 k m hj,
    nsmul_eq_mul]
  push_cast
  ring

section
variable (K : Finset (Finset X)) (w : Finset X → ℝ) (k m : ℕ)

@[simp] lemma toLeft_image_inl (T : Finset X) :
    (T.image (Sum.inl : X → PadR X k m)).toLeft = T := by
  ext x; simp

@[simp] lemma toRight_image_inl (T : Finset X) :
    (T.image (Sum.inl : X → PadR X k m)).toRight = (∅ : Finset (Fin k × Fin m)) := by
  ext x; simp

@[simp] lemma mixEdge_toLeft (v : X) (i : Fin k → Fin m) :
    (mixEdge k m v i).toLeft = {v} := by
  ext x; simp [mixEdge]

@[simp] lemma mem_mixEdge_inl (v u : X) (i : Fin k → Fin m) :
    (Sum.inl u : PadR X k m) ∈ mixEdge k m v i ↔ u = v := by
  simp [mixEdge]

@[simp] lemma mem_mixEdge_inr (v : X) (i : Fin k → Fin m) (j : Fin k) (d : Fin m) :
    (Sum.inr (j, d) : PadR X k m) ∈ mixEdge k m v i ↔ i j = d := by
  simp only [mixEdge, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨j', hj'⟩)
    · exact absurd h (by simp)
    · rw [Sum.inr.injEq, Prod.ext_iff] at hj'
      obtain ⟨h1, h2⟩ := hj'
      subst h1; exact h2
  · intro h; exact Or.inr ⟨j, by rw [h]⟩

lemma mixEdge_toRight_nonempty (hk : 0 < k) (v : X) (i : Fin k → Fin m) :
    (mixEdge k m v i).toRight ≠ (∅ : Finset (Fin k × Fin m)) := by
  intro h
  have : ((⟨0, hk⟩ : Fin k), i ⟨0, hk⟩) ∈ (mixEdge k m v i).toRight := by
    rw [Finset.mem_toRight]
    exact (mem_mixEdge_inr k m v i _ _).mpr rfl
  rw [h] at this
  simp at this

lemma mixEdge_card (v : X) (i : Fin k → Fin m) : #(mixEdge k m v i) = k + 1 := by
  classical
  have hinj : Set.InjOn
      (fun j : Fin k => (Sum.inr (j, i j) : PadR X k m)) ↑(univ : Finset (Fin k)) := by
    intro a _ b _ h
    simp only [Sum.inr.injEq, Prod.ext_iff] at h
    exact h.1
  have hnot : (Sum.inl v : PadR X k m) ∉
      (univ : Finset (Fin k)).image (fun j => Sum.inr (j, i j)) := by
    simp
  rw [mixEdge, Finset.card_insert_of_notMem hnot, Finset.card_image_of_injOn hinj]
  simp

lemma mixEdge_inj {v v' : X} {i i' : Fin k → Fin m}
    (h : mixEdge k m v i = mixEdge k m v' i') : v = v' ∧ i = i' := by
  constructor
  · have hL : ({v} : Finset X) = {v'} := by
      have := congrArg Finset.toLeft h; simpa using this
    simpa using hL
  · funext j
    have h1 : (Sum.inr (j, i j) : PadR X k m) ∈ mixEdge k m v' i' := by
      rw [← h]; exact (mem_mixEdge_inr k m v i j (i j)).mpr rfl
    exact ((mem_mixEdge_inr k m v' i' j (i j)).mp h1).symm

lemma padWtR_image_inl (T : Finset X) : padWtR K w k m (T.image Sum.inl) = w T := by
  simp [padWtR]

lemma padWtR_mixEdge (hk : 0 < k) (v : X) (i : Fin k → Fin m) :
    padWtR K w k m (mixEdge k m v i) = (1 - Slack.wLoad K w v) / (m : ℝ) ^ k := by
  rw [padWtR, ite_eq_right (mixEdge_toRight_nonempty k m hk v i)]
  simp

lemma padWtR_nonneg (hw : ∀ T, 0 ≤ w T) (hload : ∀ v : X, Slack.wLoad K w v ≤ 1)
    (U : Finset (PadR X k m)) : 0 ≤ padWtR K w k m U := by
  rw [padWtR]
  split
  · exact hw _
  · have : 0 ≤ ∑ v ∈ U.toLeft, (1 - Slack.wLoad K w v) :=
      Finset.sum_nonneg fun v _ => by linarith only [hload v]
    positivity

end

section
variable [Fintype X] (K : Finset (Finset X)) (w : Finset X → ℝ) (k m : ℕ)

/-- A sum over the padded family splits into a sum over `K` and a sum over the mixed edges. -/
lemma sum_padFamR (hk : 0 < k) (f : Finset (PadR X k m) → ℝ) :
    ∑ U ∈ padFamR K k m, f U
      = (∑ T ∈ K, f (T.image Sum.inl))
        + ∑ v : X, ∑ i : (Fin k → Fin m), f (mixEdge k m v i) := by
  classical
  have hdisj : Disjoint (K.image (Finset.image (Sum.inl : X → PadR X k m)))
      ((univ : Finset (X × (Fin k → Fin m))).image (fun t => mixEdge k m t.1 t.2)) := by
    rw [Finset.disjoint_left]
    rintro U hU hU'
    rw [Finset.mem_image] at hU hU'
    obtain ⟨T, -, rfl⟩ := hU
    obtain ⟨t, -, ht⟩ := hU'
    have h1 : (T.image (Sum.inl : X → PadR X k m)).toRight = ∅ := by simp
    rw [← ht] at h1
    exact mixEdge_toRight_nonempty k m hk t.1 t.2 h1
  rw [padFamR, Finset.sum_union hdisj]
  congr 1
  · exact Finset.sum_image (fun T _ T' _ h => Finset.image_injective Sum.inl_injective h)
  · rw [Finset.sum_image (fun t _ t' _ h => ?_)]
    · exact Fintype.sum_prod_type _
    · obtain ⟨h1, h2⟩ := mixEdge_inj k m h
      exact Prod.ext h1 h2

lemma padFamR_uniform (hK : IsUniform K (k + 1)) : IsUniform (padFamR K k m) (k + 1) := by
  intro U hU
  rw [padFamR, Finset.mem_union] at hU
  rcases hU with hU | hU
  · rw [Finset.mem_image] at hU
    obtain ⟨T, hT, rfl⟩ := hU
    rw [Finset.card_image_of_injective _ Sum.inl_injective]
    exact hK T hT
  · rw [Finset.mem_image] at hU
    obtain ⟨t, -, rfl⟩ := hU
    exact mixEdge_card k m t.1 t.2

end

/-! ### The number of dummy choice functions -/

/-- The number of choice functions of one dummy per column, as a real number. -/
theorem card_pi_fun (d m : ℕ) : ((Fintype.card (Fin d → Fin m) : ℕ) : ℝ) = (m : ℝ) ^ d := by
  simp

/-! ### Loads, codegrees and matchings of the padded system -/

lemma pow_split_one (m k : ℕ) (hk : 0 < k) : (m : ℝ) ^ k = (m : ℝ) ^ (k - 1) * (m : ℝ) := by
  rw [← pow_succ]
  congr 1
  omega

lemma pow_split_two (m k : ℕ) (hk : 2 ≤ k) :
    (m : ℝ) ^ k = (m : ℝ) ^ (k - 2) * (m : ℝ) ^ 2 := by
  rw [← pow_add]
  congr 1
  omega

section
variable [Fintype X] (K : Finset (Finset X)) (w : Finset X → ℝ) (k m : ℕ)

/-- The total weight of the padded system exceeds that of `K` by exactly the total slack. -/
lemma sum_padWtR (hk : 0 < k) (hm : 0 < m) :
    ∑ U ∈ padFamR K k m, padWtR K w k m U = (∑ T ∈ K, w T) + Slack.slackTotal K w := by
  classical
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hpk : ((m : ℝ)) ^ k ≠ 0 := ne_of_gt (pow_pos hm' k)
  rw [sum_padFamR K k m hk]
  congr 1
  · exact Finset.sum_congr rfl fun T _ => padWtR_image_inl K w k m T
  · rw [Slack.slackTotal]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [padWtR_mixEdge K w k m hk]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_pi_fun]
    field_simp

/-- Every real vertex has load exactly `1` in the padded system. -/
lemma padLoad_inl (hk : 0 < k) (hm : 0 < m) (v : X) :
    ∑ U ∈ (padFamR K k m).filter (fun U => (Sum.inl v : PadR X k m) ∈ U), padWtR K w k m U = 1 := by
  classical
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hpk : ((m : ℝ)) ^ k ≠ 0 := ne_of_gt (pow_pos hm' k)
  rw [Finset.sum_filter, sum_padFamR K k m hk]
  have h1 : (∑ T ∈ K, if (Sum.inl v : PadR X k m) ∈ T.image Sum.inl then
      padWtR K w k m (T.image Sum.inl) else 0) = Slack.wLoad K w v := by
    rw [Slack.wLoad, Finset.sum_filter]
    refine Finset.sum_congr rfl fun T _ => ?_
    simp [padWtR_image_inl]
  have h2 : ∀ u : X, (∑ i : (Fin k → Fin m),
      if (Sum.inl v : PadR X k m) ∈ mixEdge k m u i then
        padWtR K w k m (mixEdge k m u i) else 0)
      = if u = v then (1 - Slack.wLoad K w u) else 0 := by
    intro u
    simp only [mem_mixEdge_inl, padWtR_mixEdge K w k m hk]
    by_cases huv : u = v
    · subst huv
      simp only [ite_true, Finset.sum_const, Finset.card_univ, card_pi_fun,
        nsmul_eq_mul]
      field_simp
    · rw [ite_eq_right huv]
      exact Finset.sum_eq_zero fun i _ => ite_eq_right (fun h => huv h.symm)
  rw [h1, Finset.sum_congr rfl (fun u _ => h2 u),
    Finset.sum_ite_eq' Finset.univ v (fun u => 1 - Slack.wLoad K w u)]
  simp

/-- Every dummy has load exactly `S/m`. -/
lemma padLoad_inr (hk : 0 < k) (hm : 0 < m) (j : Fin k) (e : Fin m) :
    ∑ U ∈ (padFamR K k m).filter (fun U => (Sum.inr (j, e) : PadR X k m) ∈ U), padWtR K w k m U
      = Slack.slackTotal K w / (m : ℝ) := by
  classical
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hp1 : ((m : ℝ)) ^ (k - 1) ≠ 0 := ne_of_gt (pow_pos hm' _)
  rw [Finset.sum_filter, sum_padFamR K k m hk]
  have h1 : (∑ T ∈ K, if (Sum.inr (j, e) : PadR X k m) ∈ T.image Sum.inl then
      padWtR K w k m (T.image Sum.inl) else 0) = 0 :=
    Finset.sum_eq_zero fun T _ => by simp
  have h2 : ∀ u : X, (∑ i : (Fin k → Fin m),
      if (Sum.inr (j, e) : PadR X k m) ∈ mixEdge k m u i then
        padWtR K w k m (mixEdge k m u i) else 0)
      = (1 - Slack.wLoad K w u) / (m : ℝ) := by
    intro u
    simp only [mem_mixEdge_inr, padWtR_mixEdge K w k m hk]
    rw [sum_ite_at k m j e ((1 - Slack.wLoad K w u) / (m : ℝ) ^ k), pow_split_one m k hk]
    field_simp
  rw [h1, Finset.sum_congr rfl (fun u _ => h2 u), zero_add, Slack.slackTotal, Finset.sum_div]

/-- The weighted codegree of two real vertices is unchanged. -/
lemma padCodeg_inl_inl (hk : 0 < k) {v v' : X} (hvv : v ≠ v') :
    ∑ U ∈ (padFamR K k m).filter
        (fun U => (Sum.inl v : PadR X k m) ∈ U ∧ (Sum.inl v' : PadR X k m) ∈ U),
      padWtR K w k m U = ∑ T ∈ K.filter (fun T => v ∈ T ∧ v' ∈ T), w T := by
  classical
  rw [Finset.sum_filter, sum_padFamR K k m hk, Finset.sum_filter]
  have h2 : ∀ u : X, (∑ i : (Fin k → Fin m),
      if (Sum.inl v : PadR X k m) ∈ mixEdge k m u i ∧ (Sum.inl v' : PadR X k m) ∈ mixEdge k m u i
        then padWtR K w k m (mixEdge k m u i) else 0) = 0 := by
    intro u
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [ite_eq_right]
    rintro ⟨ha, hb⟩
    rw [mem_mixEdge_inl] at ha hb
    exact hvv (ha.trans hb.symm)
  rw [Finset.sum_congr rfl (fun u _ => h2 u), Finset.sum_const_zero, add_zero]
  refine Finset.sum_congr rfl fun T _ => ?_
  simp [padWtR_image_inl]

/-- The weighted codegree of a real vertex and a dummy. -/
lemma padCodeg_inl_inr (hk : 0 < k) (hm : 0 < m) (v : X) (j : Fin k) (e : Fin m) :
    ∑ U ∈ (padFamR K k m).filter
        (fun U => (Sum.inl v : PadR X k m) ∈ U ∧ (Sum.inr (j, e) : PadR X k m) ∈ U),
      padWtR K w k m U = (1 - Slack.wLoad K w v) / (m : ℝ) := by
  classical
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hp1 : ((m : ℝ)) ^ (k - 1) ≠ 0 := ne_of_gt (pow_pos hm' _)
  rw [Finset.sum_filter, sum_padFamR K k m hk]
  have h1 : (∑ T ∈ K, if (Sum.inl v : PadR X k m) ∈ T.image Sum.inl ∧
      (Sum.inr (j, e) : PadR X k m) ∈ T.image Sum.inl then
        padWtR K w k m (T.image Sum.inl) else 0) = 0 :=
    Finset.sum_eq_zero fun T _ => by simp
  have h2 : ∀ u : X, (∑ i : (Fin k → Fin m),
      if (Sum.inl v : PadR X k m) ∈ mixEdge k m u i ∧
        (Sum.inr (j, e) : PadR X k m) ∈ mixEdge k m u i
        then padWtR K w k m (mixEdge k m u i) else 0)
      = if u = v then (1 - Slack.wLoad K w u) / (m : ℝ) else 0 := by
    intro u
    simp only [mem_mixEdge_inl, mem_mixEdge_inr, padWtR_mixEdge K w k m hk]
    by_cases huv : u = v
    · subst huv
      simp only [true_and, ite_true]
      rw [sum_ite_at k m j e ((1 - Slack.wLoad K w u) / (m : ℝ) ^ k), pow_split_one m k hk]
      field_simp
    · rw [ite_eq_right huv]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [ite_eq_right]
      rintro ⟨ha, -⟩
      exact huv ha.symm
  rw [h1, Finset.sum_congr rfl (fun u _ => h2 u), zero_add,
    Finset.sum_ite_eq' Finset.univ v (fun u => (1 - Slack.wLoad K w u) / (m : ℝ))]
  simp

/-- The weighted codegree of two distinct dummies is at most `S/m²`. -/
lemma padCodeg_inr_inr (hk : 0 < k) (hm : 0 < m) (hload : ∀ v : X, Slack.wLoad K w v ≤ 1)
    {d d' : Fin k × Fin m} (hd : d ≠ d') :
    ∑ U ∈ (padFamR K k m).filter
        (fun U => (Sum.inr d : PadR X k m) ∈ U ∧ (Sum.inr d' : PadR X k m) ∈ U),
      padWtR K w k m U ≤ Slack.slackTotal K w / (m : ℝ) ^ 2 := by
  classical
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [Finset.sum_filter, sum_padFamR K k m hk]
  have h1 : (∑ T ∈ K, if (Sum.inr d : PadR X k m) ∈ T.image Sum.inl ∧
      (Sum.inr d' : PadR X k m) ∈ T.image Sum.inl then
        padWtR K w k m (T.image Sum.inl) else 0) = 0 :=
    Finset.sum_eq_zero fun T _ => by simp
  have h2 : ∀ u : X, (∑ i : (Fin k → Fin m),
      if (Sum.inr d : PadR X k m) ∈ mixEdge k m u i ∧
        (Sum.inr d' : PadR X k m) ∈ mixEdge k m u i
        then padWtR K w k m (mixEdge k m u i) else 0)
      ≤ (1 - Slack.wLoad K w u) / (m : ℝ) ^ 2 := by
    intro u
    have hnn : 0 ≤ (1 - Slack.wLoad K w u) / (m : ℝ) ^ 2 :=
      div_nonneg (by linarith only [hload u]) (by positivity)
    obtain ⟨j, e⟩ := d
    obtain ⟨j', e'⟩ := d'
    simp only [mem_mixEdge_inr, padWtR_mixEdge K w k m hk]
    by_cases hj : j = j'
    · subst hj
      have hee : e ≠ e' := fun h => hd (by rw [h])
      refine le_of_eq_of_le ?_ hnn
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [ite_eq_right]
      rintro ⟨ha, hb⟩
      exact hee (ha.symm.trans hb)
    · have hk2 : 2 ≤ k := by
        by_contra hlt
        have h0 := j.isLt
        have h1 := j'.isLt
        exact hj (Fin.ext (by omega))
      have hp2 : ((m : ℝ)) ^ (k - 2) ≠ 0 := ne_of_gt (pow_pos hm' _)
      refine le_of_eq ?_
      rw [sum_ite_at2 k m hj e e' ((1 - Slack.wLoad K w u) / (m : ℝ) ^ k), pow_split_two m k hk2]
      field_simp
  rw [h1, zero_add, Slack.slackTotal, Finset.sum_div]
  exact Finset.sum_le_sum fun u _ => h2 u

lemma padCodegR_comm (x z : PadR X k m) :
    ∑ U ∈ (padFamR K k m).filter (fun U => x ∈ U ∧ z ∈ U), padWtR K w k m U
      = ∑ U ∈ (padFamR K k m).filter (fun U => z ∈ U ∧ x ∈ U), padWtR K w k m U := by
  refine Finset.sum_congr (Finset.filter_congr fun U _ => ?_) fun _ _ => rfl
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- A member of the padded family with no dummy vertices comes from `K`. -/
lemma mem_padFamR_of_toRight_empty (hk : 0 < k) {U : Finset (PadR X k m)}
    (hU : U ∈ padFamR K k m) (hR : U.toRight = ∅) :
    U.toLeft ∈ K ∧ U = U.toLeft.image Sum.inl := by
  rw [padFamR, Finset.mem_union] at hU
  rcases hU with hU | hU
  · rw [Finset.mem_image] at hU
    obtain ⟨T, hT, rfl⟩ := hU
    rw [toLeft_image_inl]
    exact ⟨hT, rfl⟩
  · rw [Finset.mem_image] at hU
    obtain ⟨t, -, rfl⟩ := hU
    exact absurd hR (mixEdge_toRight_nonempty k m hk t.1 t.2)

/-- A member of the padded family that uses a dummy contains a dummy of the first column. -/
lemma exists_col_zero_dummy (hk : 0 < k) {U : Finset (PadR X k m)}
    (hU : U ∈ padFamR K k m) (hR : U.toRight ≠ ∅) :
    ∃ e : Fin m, (Sum.inr (⟨0, hk⟩, e) : PadR X k m) ∈ U := by
  rw [padFamR, Finset.mem_union] at hU
  rcases hU with hU | hU
  · rw [Finset.mem_image] at hU
    obtain ⟨T, -, rfl⟩ := hU
    exact absurd (by simp) hR
  · rw [Finset.mem_image] at hU
    obtain ⟨t, -, rfl⟩ := hU
    exact ⟨t.2 ⟨0, hk⟩, (mem_mixEdge_inr k m t.1 t.2 _ _).mpr rfl⟩

/-- A matching of the padded family uses at most `m` of the added edges. -/
lemma card_mixedPartR_le (hk : 0 < k) (hm : 0 < m) {M : Finset (Finset (PadR X k m))}
    (hM : IsMatching (padFamR K k m) M) :
    ((M.filter (fun U => U.toRight ≠ ∅)).card : ℝ) ≤ (m : ℝ) := by
  classical
  have hcard : (M.filter (fun U => U.toRight ≠ ∅)).card ≤ m := by
    have key : ∀ U ∈ M.filter (fun U => U.toRight ≠ ∅),
        ∃ e : Fin m, (Sum.inr (⟨0, hk⟩, e) : PadR X k m) ∈ U := by
      intro U hU
      rw [Finset.mem_filter] at hU
      exact exists_col_zero_dummy K k m hk (hM.subset hU.1) hU.2
    set f : Finset (PadR X k m) → Fin m := fun U =>
      if h : ∃ e : Fin m, (Sum.inr (⟨0, hk⟩, e) : PadR X k m) ∈ U then h.choose else ⟨0, hm⟩
      with hf
    have hfmem : ∀ U ∈ M.filter (fun U => U.toRight ≠ ∅),
        (Sum.inr (⟨0, hk⟩, f U) : PadR X k m) ∈ U := by
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
lemma exists_matching_of_padMatchingR (hk : 0 < k) {M : Finset (Finset (PadR X k m))}
    (hM : IsMatching (padFamR K k m) M) :
    ∃ M' : Finset (Finset X), IsMatching K M' ∧
      (M'.card : ℝ) = ((M.filter (fun U => U.toRight = ∅)).card : ℝ) := by
  classical
  set R := M.filter (fun U => U.toRight = ∅) with hR
  have hmem : ∀ U ∈ R, U.toLeft ∈ K ∧ U = U.toLeft.image Sum.inl := by
    intro U hU
    rw [hR, Finset.mem_filter] at hU
    exact mem_padFamR_of_toRight_empty K k m hk (hM.subset hU.1) hU.2
  have hinj : Set.InjOn (Finset.toLeft : Finset (PadR X k m) → Finset X) ↑R := by
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

end

/-- **The weighted nibble with slack, in uniformity `k+1`.**  No near-perfection hypothesis:
instead the weighting is required to leave a total slack of at least `1/γ`, and the conclusion
loses `β·S + 1`. -/
theorem fracNibbleR_withSlack (k : ℕ) (hk : 0 < k) (β : ℝ) (hβ : 0 < β) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ {X : Type} [Fintype X] [DecidableEq X] (K : Finset (Finset X)) (w : Finset X → ℝ),
        IsUniform K (k + 1) →
        (∀ T, 0 ≤ w T) →
        (∀ v : X, Slack.wLoad K w v ≤ 1) →
        (∀ x z : X, x ≠ z → ∑ T ∈ K.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ) →
        1 / γ ≤ Slack.slackTotal K w →
        ∃ M : Finset (Finset X), IsMatching K M ∧
          (1 - β) * (∑ T ∈ K, w T) - β * Slack.slackTotal K w - 1 ≤ (M.card : ℝ) := by
  classical
  obtain ⟨γ₀, hγ₀, η, hη, hmain⟩ := fracNibble_weightedCodegree (k + 1) (by omega) β hβ
  have hγpos : 0 < min γ₀ 1 := lt_min hγ₀ one_pos
  refine ⟨min γ₀ 1, hγpos, ?_⟩
  intro X _ _ K w hK hw hload hcod hslack
  have hγle : min γ₀ 1 ≤ γ₀ := min_le_left _ _
  have hγ1 : min γ₀ 1 ≤ 1 := min_le_right _ _
  set γ := min γ₀ 1 with hγdef
  set S := Slack.slackTotal K w with hSdef
  have hS : 1 / γ ≤ S := hslack
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
  have hunif := padFamR_uniform K k m hK
  have hnn := padWtR_nonneg K w k m hw hload
  have hle : ∀ v : PadR X k m,
      ∑ U ∈ (padFamR K k m).filter (fun U => v ∈ U), padWtR K w k m U ≤ 1 := by
    intro v
    cases v with
    | inl a => rw [padLoad_inl K w k m hk hm a]
    | inr d =>
        obtain ⟨j, e⟩ := d
        rw [padLoad_inr K w k m hk hm j e, div_le_one hmpos]
        exact hmS
  have hge : ∀ v : PadR X k m, v ∉ (∅ : Finset (PadR X k m)) →
      1 - γ₀ ≤ ∑ U ∈ (padFamR K k m).filter (fun U => v ∈ U), padWtR K w k m U := by
    rintro v -
    cases v with
    | inl a => rw [padLoad_inl K w k m hk hm a]; linarith
    | inr d =>
        obtain ⟨j, e⟩ := d
        rw [padLoad_inr K w k m hk hm j e, le_div_iff₀ hmpos]
        nlinarith
  have hexc : ((∅ : Finset (PadR X k m)).card : ℝ)
      ≤ η * (Fintype.card (PadR X k m) : ℝ) := by
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  have hcodeg : ∀ x z : PadR X k m, x ≠ z →
      ∑ U ∈ (padFamR K k m).filter (fun U => x ∈ U ∧ z ∈ U), padWtR K w k m U ≤ γ₀ := by
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
            rw [padCodeg_inl_inl K w k m hk hab]
            exact le_trans (hcod a b hab) hγle
        | inr d =>
            obtain ⟨j, e⟩ := d
            rw [padCodeg_inl_inr K w k m hk hm a j e]
            exact hmixbound a
    | inr d =>
        obtain ⟨j, e⟩ := d
        cases z with
        | inl b =>
            rw [padCodegR_comm K w k m _ _, padCodeg_inl_inr K w k m hk hm b j e]
            exact hmixbound b
        | inr d' =>
            have hdd : (j, e) ≠ d' := fun h => hxz (by rw [h])
            refine le_trans (padCodeg_inr_inr K w k m hk hm hload hdd) ?_
            have hSnn : 0 ≤ S := by linarith
            have : S / (m : ℝ) ^ 2 ≤ 1 / (m : ℝ) := by
              rw [div_le_div_iff₀ (by positivity) hmpos]
              nlinarith
            rw [← hSdef]
            linarith [hinvm]
  obtain ⟨M, hM, -, hMcard⟩ :=
    hmain (padFamR K k m) (padWtR K w k m) ∅ hunif hnn hle hge hexc hcodeg
  rw [sum_padWtR K w k m hk hm, ← hSdef] at hMcard
  have hsplit : ((M.filter (fun U => U.toRight = ∅)).card : ℝ)
      + ((M.filter (fun U => ¬ (U.toRight = ∅))).card : ℝ) = (M.card : ℝ) := by
    rw [← Nat.cast_add, Finset.card_filter_add_card_filter_not]
  have hmix := card_mixedPartR_le K k m hk hm hM
  obtain ⟨M', hM', hM'card⟩ := exists_matching_of_padMatchingR K k m hk hM
  refine ⟨M', hM', ?_⟩
  rw [hM'card]
  nlinarith only [hMcard, hmix, hsplit, hmlt, hβ.le]

end SlackR

export SlackR (fracNibbleR_withSlack)

-- Axiom check: `[propext, Classical.choice, Quot.sound]`.


end Nibble
