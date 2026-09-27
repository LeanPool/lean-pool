/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini, Aristotle
-/

module

/-
# Nibble — the weighted nibble for hypergraphs of **bounded** edge size

`Nibble.fracNibbleR_withSlack` (`Nibble.FracNibbleSlackR`) needs an exactly `(k+1)`-uniform
hypergraph.  The placement hypergraph of the box-allocation nibble is *not* uniform: the edge of a
placement of a copy `c` occupies one token plus the `∑_a sz(c,a)·sz(c,a+1)` cell slots of its three
rectangles, and that number varies with `c`.  All edges are however nonempty and of size at most
`r`, and this file removes the uniformity hypothesis under exactly that assumption.

The padding.  Put `r` *columns* of `m` dummies each and, for an edge `T` of size `t`, attach to `T`
one dummy from each of the first `r - t` columns; the weight `w T` is spread uniformly over the
`m^(r-t)` choices.  Then

* the padded family is exactly `r`-uniform;
* the load of a real vertex is unchanged, that of a dummy of column `j` is
  `(∑_{T : r - #T > j} w T)/m ≤ (∑_T w T)/m ≤ 1` as soon as `m ≥ ∑_T w T`;
* the weighted codegree of two real vertices is unchanged, that of a real vertex and a dummy is at
  most `1/m`, that of two dummies of the same column is `0` and of two dummies of different columns
  at most `(∑_T w T)/m² ≤ 1/m`;
* the total weight is unchanged, and the total slack is between `r·(m - ∑_T w T)` and
  `|X| + r·m ≤ (1+r)|X| + r(1/γ + 3)`;
* a matching of the padded family projects to a matching of `K` of the same size, because two
  padded edges coming from the same `T` meet in `T` (nonempty).

Must be sorry-free and axiom-clean `[propext, Classical.choice, Quot.sound]`.
-/
public import LeanPool.AsymptoticTrianglePacking.Internal.WeightedSlackUniform

/-! # Weighted rounding for nonuniform hypergraphs with bounded edge size -/

@[expose] public section

open Finset Hypergraph

namespace Nibble

namespace LEUnif

variable {X : Type} [DecidableEq X]

/-- The padded vertex type: the real vertices together with `r` columns of `m` dummies. -/
abbrev PadV (X : Type) (r m : ℕ) := X ⊕ (Fin r × Fin m)

variable {r m : ℕ} {T : Finset X} {i : Fin (r - #T) → Fin m}

/-- The padded edge of `T` for the dummy choice `i`: one dummy in each of the first `r - #T`
columns. -/
def padEdgeD (r m : ℕ) (T : Finset X) (i : Fin (r - #T) → Fin m) : Finset (PadV X r m) :=
  T.image Sum.inl ∪ (univ : Finset (Fin (r - #T))).image
    (fun j => Sum.inr (Fin.castLE (Nat.sub_le r #T) j, i j))

/-- The padded family. -/
def padFamLE (r m : ℕ) (K : Finset (Finset X)) : Finset (Finset (PadV X r m)) :=
  K.biUnion (fun T => (univ : Finset (Fin (r - #T) → Fin m)).image (padEdgeD r m T))

/-- The padded weighting: the weight of `T` spread over its `m^(r-#T)` padded edges. -/
noncomputable def padWtLE (r m : ℕ) (w : Finset X → ℝ) : Finset (PadV X r m) → ℝ :=
  fun U => w U.toLeft / (m : ℝ) ^ (r - #U.toLeft)

@[simp] lemma mem_padEdgeD_inl {x : X} :
    (Sum.inl x : PadV X r m) ∈ padEdgeD r m T i ↔ x ∈ T := by
  simp [padEdgeD]

lemma mem_padEdgeD_inr {j : Fin r} {e : Fin m} :
    (Sum.inr (j, e) : PadV X r m) ∈ padEdgeD r m T i ↔
      ∃ j' : Fin (r - #T), (j' : ℕ) = (j : ℕ) ∧ i j' = e := by
  constructor
  · intro h
    rw [padEdgeD, Finset.mem_union] at h
    rcases h with h | h
    · rw [Finset.mem_image] at h
      obtain ⟨x, -, hx⟩ := h
      exact absurd hx (by simp)
    · rw [Finset.mem_image] at h
      obtain ⟨j', -, hj'⟩ := h
      rw [Sum.inr.injEq, Prod.mk.injEq] at hj'
      exact ⟨j', by simpa using congrArg Fin.val hj'.1, hj'.2⟩
  · rintro ⟨j', h1, h2⟩
    rw [padEdgeD, Finset.mem_union]
    refine Or.inr ?_
    rw [Finset.mem_image]
    refine ⟨j', Finset.mem_univ _, ?_⟩
    rw [Sum.inr.injEq, Prod.mk.injEq]
    exact ⟨Fin.ext (by simpa using h1), h2⟩

@[simp] lemma padEdgeD_toLeft : (padEdgeD r m T i).toLeft = T := by
  ext x
  rw [Finset.mem_toLeft, mem_padEdgeD_inl]

lemma padEdgeD_inl_disj_inr :
    Disjoint (T.image (Sum.inl : X → PadV X r m))
      ((univ : Finset (Fin (r - #T))).image
        (fun j => Sum.inr (Fin.castLE (Nat.sub_le r #T) j, i j))) := by
  rw [Finset.disjoint_left]
  rintro x hx hx'
  rw [Finset.mem_image] at hx hx'
  obtain ⟨a, -, rfl⟩ := hx
  obtain ⟨b, -, hb⟩ := hx'
  exact absurd hb (by simp)

lemma padEdgeD_card (hT : #T ≤ r) : #(padEdgeD r m T i) = r := by
  have hinj : Function.Injective
      (fun j : Fin (r - #T) => (Sum.inr (Fin.castLE (Nat.sub_le r #T) j, i j) : PadV X r m)) := by
    intro a b h
    simp only [Sum.inr.injEq, Prod.mk.injEq, Fin.ext_iff, Fin.val_castLE] at h
    exact Fin.ext h.1
  rw [padEdgeD, Finset.card_union_of_disjoint padEdgeD_inl_disj_inr,
    Finset.card_image_of_injective _ Sum.inl_injective, Finset.card_image_of_injective _ hinj,
    Finset.card_univ, Fintype.card_fin]
  omega

lemma padEdgeD_inj_i {i' : Fin (r - #T) → Fin m} (h : padEdgeD r m T i = padEdgeD r m T i') :
    i = i' := by
  funext j
  have hmem : (Sum.inr (Fin.castLE (Nat.sub_le r #T) j, i j) : PadV X r m)
      ∈ padEdgeD r m T i := by
    rw [mem_padEdgeD_inr]
    exact ⟨j, rfl, rfl⟩
  rw [h, mem_padEdgeD_inr] at hmem
  obtain ⟨j', h1, h2⟩ := hmem
  have : j' = j := Fin.ext (by simpa using h1)
  subst this
  exact h2.symm

lemma mem_padFamLE {K : Finset (Finset X)} {U : Finset (PadV X r m)} (hU : U ∈ padFamLE r m K) :
    ∃ (T : Finset X) (_ : T ∈ K) (i : Fin (r - #T) → Fin m), U = padEdgeD r m T i := by
  rw [padFamLE, Finset.mem_biUnion] at hU
  obtain ⟨T, hT, hU⟩ := hU
  rw [Finset.mem_image] at hU
  obtain ⟨i, -, rfl⟩ := hU
  exact ⟨T, hT, i, rfl⟩

lemma sum_padFamLE (K : Finset (Finset X)) (f : Finset (PadV X r m) → ℝ) :
    ∑ U ∈ padFamLE r m K, f U
      = ∑ T ∈ K, ∑ i : (Fin (r - #T) → Fin m), f (padEdgeD r m T i) := by
  classical
  have hpd : (↑K : Set (Finset X)).PairwiseDisjoint
      (fun T => (univ : Finset (Fin (r - #T) → Fin m)).image (padEdgeD r m T)) := by
    intro T hT T' hT' hne
    rw [Function.onFun, Finset.disjoint_left]
    rintro U hU hU'
    rw [Finset.mem_image] at hU hU'
    obtain ⟨a, -, rfl⟩ := hU
    obtain ⟨b, -, hb⟩ := hU'
    have hTT : T' = T := by
      have hc := congrArg Finset.toLeft hb
      rwa [padEdgeD_toLeft, padEdgeD_toLeft] at hc
    exact hne hTT.symm
  rw [padFamLE, Finset.sum_biUnion hpd]
  refine Finset.sum_congr rfl fun T _ => ?_
  exact Finset.sum_image fun i _ i' _ h => padEdgeD_inj_i h

lemma padWtLE_edge (w : Finset X → ℝ) :
    padWtLE r m w (padEdgeD r m T i) = w T / (m : ℝ) ^ (r - #T) := by
  rw [padWtLE, padEdgeD_toLeft]

omit [DecidableEq X] in
lemma padWtLE_nonneg (w : Finset X → ℝ) (hw : ∀ T, 0 ≤ w T) (U : Finset (PadV X r m)) :
    0 ≤ padWtLE r m w U := by
  rw [padWtLE]
  exact div_nonneg (hw _) (by positivity)

lemma padFamLE_uniform {K : Finset (Finset X)} (hK : ∀ T ∈ K, #T ≤ r) :
    IsUniform (padFamLE r m K) r := by
  intro U hU
  obtain ⟨T, hT, i, rfl⟩ := mem_padFamLE hU
  exact padEdgeD_card (hK T hT)

lemma mul_pow_sub_one_div (x y : ℝ) (hy : 0 < y) (a : ℕ) (ha : 0 < a) :
    x * y ^ (a - 1) / y ^ a = x / y := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ]
  have hy' : y ≠ 0 := ne_of_gt hy
  field_simp

lemma mul_pow_sub_two_div (x y : ℝ) (hy : 0 < y) (a : ℕ) (ha : 2 ≤ a) :
    x * y ^ (a - 2) / y ^ a = x / y ^ 2 := by
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 2 := ⟨a - 2, by omega⟩
  rw [Nat.add_sub_cancel, pow_add]
  have hy' : y ≠ 0 := ne_of_gt hy
  field_simp

/-- One prescribed dummy: the weight `x` spread over `m^d` choices contributes `x/m`. -/
lemma sum_col_one (hm : 0 < m) (x : ℝ) {d : ℕ} (j₀ : Fin d) (e : Fin m) :
    ∑ f : (Fin d → Fin m), (if f j₀ = e then x / (m : ℝ) ^ d else 0) = x / (m : ℝ) := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hd : 0 < d := lt_of_le_of_lt (Nat.zero_le _) j₀.isLt
  rw [SlackR.sum_ite_at d m j₀ e (x / (m : ℝ) ^ d), div_mul_eq_mul_div,
    mul_pow_sub_one_div _ _ hm' d hd]

/-- Two prescribed dummies in different columns contribute `x/m²`. -/
lemma sum_col_two (hm : 0 < m) (x : ℝ) {d : ℕ} {j₀ j₁ : Fin d} (hj : j₀ ≠ j₁) (e e' : Fin m) :
    ∑ f : (Fin d → Fin m), (if f j₀ = e ∧ f j₁ = e' then x / (m : ℝ) ^ d else 0)
      = x / (m : ℝ) ^ 2 := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hd : 2 ≤ d := by
    by_contra hlt
    have h0 := j₀.isLt
    have h1 := j₁.isLt
    have : (j₀ : ℕ) = (j₁ : ℕ) := by omega
    exact hj (Fin.ext this)
  rw [SlackR.sum_ite_at2 d m hj e e' (x / (m : ℝ) ^ d), div_mul_eq_mul_div,
    mul_pow_sub_two_div _ _ hm' d hd]

omit [DecidableEq X] in
/-- The sum of the padded weight over the padded edges of one `T`. -/
lemma sum_over_i (hm : 0 < m) (w : Finset X → ℝ) (T : Finset X) :
    ∑ _i : (Fin (r - #T) → Fin m), w T / (m : ℝ) ^ (r - #T) = w T := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, SlackR.card_pi_fun]
  field_simp

lemma sum_padWtLE (hm : 0 < m) (K : Finset (Finset X)) (w : Finset X → ℝ) :
    ∑ U ∈ padFamLE r m K, padWtLE r m w U = ∑ T ∈ K, w T := by
  rw [sum_padFamLE]
  refine Finset.sum_congr rfl fun T _ => ?_
  simp only [padWtLE_edge]
  exact sum_over_i hm w T

lemma padLoad_inl (hm : 0 < m) (K : Finset (Finset X)) (w : Finset X → ℝ) (v : X) :
    Slack.wLoad (padFamLE r m K) (padWtLE r m w) (Sum.inl v) = Slack.wLoad K w v := by
  classical
  rw [Slack.wLoad, Slack.wLoad, Finset.sum_filter, sum_padFamLE, Finset.sum_filter]
  refine Finset.sum_congr rfl fun T _ => ?_
  simp only [mem_padEdgeD_inl, padWtLE_edge]
  by_cases hv : v ∈ T
  · simp only [ite_eq_left hv]
    exact sum_over_i hm w T
  · simp [hv]

lemma padLoad_inr (hm : 0 < m) (K : Finset (Finset X)) (w : Finset X → ℝ) (j : Fin r)
    (e : Fin m) :
    Slack.wLoad (padFamLE r m K) (padWtLE r m w) (Sum.inr (j, e))
      = (∑ T ∈ K.filter (fun T => (j : ℕ) < r - #T), w T) / (m : ℝ) := by
  classical
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [Slack.wLoad, Finset.sum_filter, sum_padFamLE, Finset.sum_filter, Finset.sum_div]
  refine Finset.sum_congr rfl fun T _ => ?_
  simp only [mem_padEdgeD_inr, padWtLE_edge]
  by_cases hj : (j : ℕ) < r - #T
  · rw [ite_eq_left hj]
    have hcond : ∀ f : Fin (r - #T) → Fin m,
        (∃ j' : Fin (r - #T), (j' : ℕ) = (j : ℕ) ∧ f j' = e) ↔ f ⟨(j : ℕ), hj⟩ = e := by
      intro f
      constructor
      · rintro ⟨j', h1, h2⟩
        have : j' = ⟨(j : ℕ), hj⟩ := Fin.ext (by simpa using h1)
        rwa [this] at h2
      · intro h
        exact ⟨⟨(j : ℕ), hj⟩, rfl, h⟩
    simp only [hcond]
    exact sum_col_one hm (w T) ⟨(j : ℕ), hj⟩ e
  · rw [ite_eq_right hj, zero_div]
    refine Finset.sum_eq_zero fun f _ => ?_
    rw [ite_eq_right]
    rintro ⟨j', h1, -⟩
    exact hj (h1 ▸ j'.isLt)

lemma padCodeg_inl_inl (K : Finset (Finset X)) (w : Finset X → ℝ) (hm : 0 < m) {v v' : X} :
    ∑ U ∈ (padFamLE r m K).filter
        (fun U => (Sum.inl v : PadV X r m) ∈ U ∧ (Sum.inl v' : PadV X r m) ∈ U),
      padWtLE r m w U = ∑ T ∈ K.filter (fun T => v ∈ T ∧ v' ∈ T), w T := by
  classical
  rw [Finset.sum_filter, sum_padFamLE, Finset.sum_filter]
  refine Finset.sum_congr rfl fun T _ => ?_
  simp only [mem_padEdgeD_inl, padWtLE_edge]
  by_cases hv : v ∈ T ∧ v' ∈ T
  · simp only [ite_eq_left hv]
    exact sum_over_i hm w T
  · simp [hv]

lemma padCodeg_inl_inr (hm : 0 < m) (K : Finset (Finset X)) (w : Finset X → ℝ)
    (hw : ∀ T, 0 ≤ w T) (v : X) (j : Fin r) (e : Fin m) :
    ∑ U ∈ (padFamLE r m K).filter
        (fun U => (Sum.inl v : PadV X r m) ∈ U ∧ (Sum.inr (j, e) : PadV X r m) ∈ U),
      padWtLE r m w U ≤ Slack.wLoad K w v / (m : ℝ) := by
  classical
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [Finset.sum_filter, sum_padFamLE, Slack.wLoad, Finset.sum_filter, Finset.sum_div]
  refine Finset.sum_le_sum fun T _ => ?_
  simp only [mem_padEdgeD_inl, mem_padEdgeD_inr, padWtLE_edge]
  by_cases hv : v ∈ T
  · rw [ite_eq_left hv]
    by_cases hj : (j : ℕ) < r - #T
    · have hcond : ∀ f : Fin (r - #T) → Fin m,
          (v ∈ T ∧ ∃ j' : Fin (r - #T), (j' : ℕ) = (j : ℕ) ∧ f j' = e) ↔ f ⟨(j : ℕ), hj⟩ = e := by
        intro f
        constructor
        · rintro ⟨-, j', h1, h2⟩
          have : j' = ⟨(j : ℕ), hj⟩ := Fin.ext (by simpa using h1)
          rwa [this] at h2
        · intro h
          exact ⟨hv, ⟨(j : ℕ), hj⟩, rfl, h⟩
      simp only [hcond]
      rw [sum_col_one hm (w T) ⟨(j : ℕ), hj⟩ e]
    · have hzero : ∑ f : (Fin (r - #T) → Fin m),
          (if v ∈ T ∧ ∃ j' : Fin (r - #T), (j' : ℕ) = (j : ℕ) ∧ f j' = e
            then w T / (m : ℝ) ^ (r - #T) else 0) = 0 := by
        refine Finset.sum_eq_zero fun f _ => ?_
        rw [ite_eq_right]
        rintro ⟨-, j', h1, -⟩
        exact hj (h1 ▸ j'.isLt)
      rw [hzero]
      exact div_nonneg (hw T) hm'.le
  · have hzero : ∑ f : (Fin (r - #T) → Fin m),
        (if v ∈ T ∧ ∃ j' : Fin (r - #T), (j' : ℕ) = (j : ℕ) ∧ f j' = e
          then w T / (m : ℝ) ^ (r - #T) else 0) = 0 := by
      refine Finset.sum_eq_zero fun f _ => ?_
      rw [ite_eq_right]
      rintro ⟨h, -⟩
      exact hv h
    rw [hzero, ite_eq_right hv, zero_div]

lemma padCodeg_inr_inr (hm : 0 < m) (K : Finset (Finset X)) (w : Finset X → ℝ)
    (hw : ∀ T, 0 ≤ w T) {j j' : Fin r} {e e' : Fin m} (hne : (j, e) ≠ (j', e')) :
    ∑ U ∈ (padFamLE r m K).filter
        (fun U => (Sum.inr (j, e) : PadV X r m) ∈ U ∧ (Sum.inr (j', e') : PadV X r m) ∈ U),
      padWtLE r m w U ≤ (∑ T ∈ K, w T) / (m : ℝ) ^ 2 := by
  classical
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [Finset.sum_filter, sum_padFamLE, Finset.sum_div]
  refine Finset.sum_le_sum fun T _ => ?_
  simp only [mem_padEdgeD_inr, padWtLE_edge]
  by_cases hj : (j : ℕ) = (j' : ℕ)
  · -- same column: the two dummies cannot both occur
    have hee : e ≠ e' := by
      intro h
      exact hne (Prod.ext (Fin.ext hj) h)
    have hzero : ∑ f : (Fin (r - #T) → Fin m),
        (if (∃ a : Fin (r - #T), (a : ℕ) = (j : ℕ) ∧ f a = e) ∧
            (∃ b : Fin (r - #T), (b : ℕ) = (j' : ℕ) ∧ f b = e')
          then w T / (m : ℝ) ^ (r - #T) else 0) = 0 := by
      refine Finset.sum_eq_zero fun f _ => ?_
      rw [ite_eq_right]
      rintro ⟨⟨a, ha1, ha2⟩, ⟨b, hb1, hb2⟩⟩
      have : a = b := Fin.ext (by rw [ha1, hj, ← hb1])
      subst this
      exact hee (ha2.symm.trans hb2)
    rw [hzero]
    exact div_nonneg (hw T) (by positivity)
  · by_cases hjr : (j : ℕ) < r - #T ∧ (j' : ℕ) < r - #T
    · obtain ⟨hj1, hj2⟩ := hjr
      have hcond : ∀ f : Fin (r - #T) → Fin m,
          ((∃ a : Fin (r - #T), (a : ℕ) = (j : ℕ) ∧ f a = e) ∧
            (∃ b : Fin (r - #T), (b : ℕ) = (j' : ℕ) ∧ f b = e'))
            ↔ (f ⟨(j : ℕ), hj1⟩ = e ∧ f ⟨(j' : ℕ), hj2⟩ = e') := by
        intro f
        constructor
        · rintro ⟨⟨a, ha1, ha2⟩, ⟨b, hb1, hb2⟩⟩
          have hA : a = ⟨(j : ℕ), hj1⟩ := Fin.ext (by simpa using ha1)
          have hB : b = ⟨(j' : ℕ), hj2⟩ := Fin.ext (by simpa using hb1)
          exact ⟨hA ▸ ha2, hB ▸ hb2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨⟨(j : ℕ), hj1⟩, rfl, h1⟩, ⟨⟨(j' : ℕ), hj2⟩, rfl, h2⟩⟩
      simp only [hcond]
      have hjj : (⟨(j : ℕ), hj1⟩ : Fin (r - #T)) ≠ ⟨(j' : ℕ), hj2⟩ := by
        intro h
        exact hj (by simpa using congrArg Fin.val h)
      rw [sum_col_two hm (w T) hjj e e']
    · have hzero : ∑ f : (Fin (r - #T) → Fin m),
          (if (∃ a : Fin (r - #T), (a : ℕ) = (j : ℕ) ∧ f a = e) ∧
              (∃ b : Fin (r - #T), (b : ℕ) = (j' : ℕ) ∧ f b = e')
            then w T / (m : ℝ) ^ (r - #T) else 0) = 0 := by
        refine Finset.sum_eq_zero fun f _ => ?_
        rw [ite_eq_right]
        rintro ⟨⟨a, ha1, -⟩, ⟨b, hb1, -⟩⟩
        exact hjr ⟨ha1 ▸ a.isLt, hb1 ▸ b.isLt⟩
      rw [hzero]
      exact div_nonneg (hw T) (by positivity)

lemma padCodegLE_comm (K : Finset (Finset X)) (w : Finset X → ℝ) (x z : PadV X r m) :
    ∑ U ∈ (padFamLE r m K).filter (fun U => x ∈ U ∧ z ∈ U), padWtLE r m w U
      = ∑ U ∈ (padFamLE r m K).filter (fun U => z ∈ U ∧ x ∈ U), padWtLE r m w U := by
  refine Finset.sum_congr (Finset.filter_congr fun U _ => ?_) fun _ _ => rfl
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

/-- **Weighted handshake.** -/
lemma sum_wLoad_eq [Fintype X] (K : Finset (Finset X)) (w : Finset X → ℝ) :
    ∑ v : X, Slack.wLoad K w v = ∑ T ∈ K, (#T : ℝ) * w T := by
  classical
  simp_rw [Slack.wLoad, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]

/-- A matching of the padded family projects to a matching of `K` of the same size. -/
lemma exists_matching_of_padMatchingLE {K : Finset (Finset X)} (hne : ∀ T ∈ K, T.Nonempty)
    {M : Finset (Finset (PadV X r m))} (hM : IsMatching (padFamLE r m K) M) :
    ∃ M' : Finset (Finset X), IsMatching K M' ∧ (M'.card : ℝ) = (M.card : ℝ) := by
  classical
  have hmem : ∀ U ∈ M, U.toLeft ∈ K ∧ (U.toLeft).Nonempty := by
    intro U hU
    obtain ⟨T, hT, i, rfl⟩ := mem_padFamLE (hM.subset hU)
    rw [padEdgeD_toLeft]
    exact ⟨hT, hne T hT⟩
  have hdisjL : ∀ U ∈ M, ∀ V ∈ M, U ≠ V → Disjoint U.toLeft V.toLeft := by
    intro U hU V hV hUV
    have hdisj := hM.disjoint U hU V hV hUV
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_toLeft] at hx hx'
    exact (Finset.disjoint_left.mp hdisj hx) hx'
  have hinj : Set.InjOn (Finset.toLeft : Finset (PadV X r m) → Finset X) ↑M := by
    intro U hU V hV h
    by_contra hUV
    obtain ⟨x, hx⟩ := (hmem U hU).2
    have hx' : x ∈ V.toLeft := by rw [← h]; exact hx
    exact (Finset.disjoint_left.mp (hdisjL U hU V hV hUV) hx) hx'
  refine ⟨M.image Finset.toLeft, ⟨?_, ?_⟩, ?_⟩
  · intro T hT
    rw [Finset.mem_image] at hT
    obtain ⟨U, hU, rfl⟩ := hT
    exact (hmem U hU).1
  · intro T hT T' hT' hTT
    rw [Finset.mem_image] at hT hT'
    obtain ⟨U, hU, rfl⟩ := hT
    obtain ⟨V, hV, rfl⟩ := hT'
    exact hdisjL U hU V hV (fun h => hTT (by rw [h]))
  · rw [Finset.card_image_of_injOn hinj]

end LEUnif

/-- **The weighted nibble for hypergraphs with edges of size at most `r`.**  For every accuracy `β`
and every bound `r` on the edge size there are a codegree threshold `γ` and a constant `C`,
depending on `β` and `r` alone, such that every weighting of a family of nonempty edges of size at
most `r` with loads at most `1` and weighted codegrees at most `γ` admits a matching of size at
least `(1-β)·∑w − β·|X| − C`. -/
theorem fracNibble_leUniform (r : ℕ) (hr : 2 ≤ r) (β : ℝ) (hβ : 0 < β) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ C : ℝ, 0 < C ∧
      ∀ {X : Type} [Fintype X] [DecidableEq X] (K : Finset (Finset X)) (w : Finset X → ℝ),
        (∀ T ∈ K, T.Nonempty ∧ #T ≤ r) →
        (∀ T, 0 ≤ w T) →
        (∀ v : X, Slack.wLoad K w v ≤ 1) →
        (∀ x z : X, x ≠ z → ∑ T ∈ K.filter (fun T => x ∈ T ∧ z ∈ T), w T ≤ γ) →
        ∃ M : Finset (Finset X), IsMatching K M ∧
          (1 - β) * (∑ T ∈ K, w T) - β * (Fintype.card X : ℝ) - C ≤ (M.card : ℝ) := by
  classical
  have hrpos : (0 : ℝ) < 1 + (r : ℝ) := by positivity
  set b : ℝ := β / (1 + (r : ℝ)) with hbdef
  have hb : 0 < b := by positivity
  have hbβ : b ≤ β := by
    rw [hbdef, div_le_iff₀ hrpos]
    nlinarith
  obtain ⟨γ₂, hγ₂, hmain⟩ := fracNibbleR_withSlack (r - 1) (by omega) b hb
  refine ⟨min γ₂ 1, lt_min hγ₂ one_pos, b * (r : ℝ) * (1 / γ₂ + 3) + 1, by positivity, ?_⟩
  intro X _ _ K w hsize hw hload hcod
  set W : ℝ := ∑ T ∈ K, w T with hWdef
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun T _ => hw T
  set m : ℕ := ⌈W⌉₊ + ⌈1 / γ₂⌉₊ + 1 with hmdef
  have hm : 0 < m := by omega
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmW : W + 1 / γ₂ ≤ (m : ℝ) := by
    have h1 : W ≤ (⌈W⌉₊ : ℝ) := Nat.le_ceil W
    have h2 : 1 / γ₂ ≤ (⌈1 / γ₂⌉₊ : ℝ) := Nat.le_ceil _
    rw [hmdef]
    push_cast
    linarith
  have hmub : (m : ℝ) ≤ W + 1 / γ₂ + 3 := by
    have h1 : (⌈W⌉₊ : ℝ) < W + 1 := Nat.ceil_lt_add_one hW0
    have h2 : (⌈1 / γ₂⌉₊ : ℝ) < 1 / γ₂ + 1 := Nat.ceil_lt_add_one (by positivity)
    rw [hmdef]
    push_cast
    linarith
  have hWm : W ≤ (m : ℝ) := by
    have : (0 : ℝ) < 1 / γ₂ := by positivity
    linarith
  have hinvm : 1 / (m : ℝ) ≤ γ₂ := by
    rw [div_le_iff₀ hm']
    have : 1 / γ₂ ≤ (m : ℝ) := by linarith
    rw [div_le_iff₀ hγ₂] at this
    linarith
  -- the padded system
  set K' := LEUnif.padFamLE r m K with hK'
  set w' := LEUnif.padWtLE r m w with hw'
  have hunif : IsUniform K' (r - 1 + 1) := by
    have hrr : r - 1 + 1 = r := by omega
    rw [hrr]
    exact LEUnif.padFamLE_uniform (fun T hT => (hsize T hT).2)
  have hnn : ∀ U, 0 ≤ w' U := fun U => LEUnif.padWtLE_nonneg w hw U
  have hfilW : ∀ p : Finset X → Prop, ∀ _ : DecidablePred p,
      ∑ T ∈ K.filter p, w T ≤ W := by
    intro p _
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun T _ _ => hw T)
  have hloadPad : ∀ v : LEUnif.PadV X r m, Slack.wLoad K' w' v ≤ 1 := by
    intro v
    cases v with
    | inl a => rw [hK', hw', LEUnif.padLoad_inl hm K w a]; exact hload a
    | inr d =>
        obtain ⟨j, e⟩ := d
        rw [hK', hw', LEUnif.padLoad_inr hm K w j e, div_le_one hm']
        exact le_trans (hfilW _ _) hWm
  have hloadX : ∀ v : X, 0 ≤ Slack.wLoad K w v :=
    fun v => Finset.sum_nonneg fun T _ => hw T
  have hcodPad : ∀ x z : LEUnif.PadV X r m, x ≠ z →
      ∑ U ∈ K'.filter (fun U => x ∈ U ∧ z ∈ U), w' U ≤ γ₂ := by
    intro x z hxz
    have hmix : ∀ a : X, Slack.wLoad K w a / (m : ℝ) ≤ γ₂ := by
      intro a
      have h1 : Slack.wLoad K w a / (m : ℝ) ≤ 1 / (m : ℝ) := by
        gcongr
        exact hload a
      linarith [hinvm]
    cases x with
    | inl a =>
        cases z with
        | inl c =>
            have hac : a ≠ c := fun h => hxz (by rw [h])
            rw [hK', hw', LEUnif.padCodeg_inl_inl K w hm]
            exact le_trans (hcod a c hac) (le_trans (min_le_left _ _) (le_refl _))
        | inr d =>
            obtain ⟨j, e⟩ := d
            exact le_trans (LEUnif.padCodeg_inl_inr hm K w hw a j e) (hmix a)
    | inr d =>
        obtain ⟨j, e⟩ := d
        cases z with
        | inl c =>
            rw [hK', hw', LEUnif.padCodegLE_comm]
            exact le_trans (LEUnif.padCodeg_inl_inr hm K w hw c j e) (hmix c)
        | inr d' =>
            obtain ⟨j', e'⟩ := d'
            have hne : (j, e) ≠ (j', e') := fun h => hxz (by rw [h])
            refine le_trans (LEUnif.padCodeg_inr_inr hm K w hw hne) ?_
            have h1 : W / (m : ℝ) ^ 2 ≤ 1 / (m : ℝ) := by
              rw [div_le_div_iff₀ (by positivity) hm']
              nlinarith
            linarith [hinvm]
  -- the slack of the padded system
  have hslackEq : Slack.slackTotal K' w'
      = (∑ v : X, (1 - Slack.wLoad K' w' (Sum.inl v)))
        + ∑ d : Fin r × Fin m, (1 - Slack.wLoad K' w' (Sum.inr d)) := by
    rw [Slack.slackTotal]
    exact Fintype.sum_sum_type _
  have hdummy : ∀ d : Fin r × Fin m, Slack.wLoad K' w' (Sum.inr d) ≤ W / (m : ℝ) := by
    rintro ⟨j, e⟩
    rw [hK', hw', LEUnif.padLoad_inr hm K w j e]
    gcongr
    exact hfilW _ _
  have hslackLB : 1 / γ₂ ≤ Slack.slackTotal K' w' := by
    have hreal : 0 ≤ ∑ v : X, (1 - Slack.wLoad K' w' (Sum.inl v)) := by
      refine Finset.sum_nonneg fun v _ => ?_
      have := hloadPad (Sum.inl v)
      linarith
    have hdum : (Fintype.card (Fin r × Fin m) : ℝ) * (1 - W / (m : ℝ))
        ≤ ∑ d : Fin r × Fin m, (1 - Slack.wLoad K' w' (Sum.inr d)) := by
      have hconst : (Fintype.card (Fin r × Fin m) : ℝ) * (1 - W / (m : ℝ))
          = ∑ _d : Fin r × Fin m, (1 - W / (m : ℝ)) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [hconst]
      refine Finset.sum_le_sum fun d _ => ?_
      have := hdummy d
      linarith
    have hcardrm : (Fintype.card (Fin r × Fin m) : ℝ) = (r : ℝ) * (m : ℝ) := by
      simp
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : 1 ≤ r)
    have hmWpos : 1 / γ₂ ≤ (m : ℝ) - W := by linarith
    have hkey : (r : ℝ) * (m : ℝ) * (1 - W / (m : ℝ)) = (r : ℝ) * ((m : ℝ) - W) := by
      field_simp
    rw [hslackEq]
    rw [hcardrm, hkey] at hdum
    nlinarith [hmWpos]
  obtain ⟨M, hM, hMcard⟩ :=
    hmain K' w' hunif hnn hloadPad hcodPad hslackLB
  -- the total weight and the size of the slack
  have hsumw' : ∑ U ∈ K', w' U = W := LEUnif.sum_padWtLE hm K w
  have hslackUB : Slack.slackTotal K' w'
      ≤ (Fintype.card X : ℝ) + (r : ℝ) * (m : ℝ) := by
    have hbound : ∀ v : LEUnif.PadV X r m, 1 - Slack.wLoad K' w' v ≤ 1 := by
      intro v
      have : 0 ≤ Slack.wLoad K' w' v := Finset.sum_nonneg fun U _ => hnn U
      linarith
    have := Finset.sum_le_sum (fun v (_ : v ∈ (univ : Finset (LEUnif.PadV X r m))) => hbound v)
    rw [Slack.slackTotal]
    refine le_trans this ?_
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    have : (Fintype.card (LEUnif.PadV X r m) : ℝ)
        = (Fintype.card X : ℝ) + (r : ℝ) * (m : ℝ) := by simp
    rw [this]
  have hWX : W ≤ (Fintype.card X : ℝ) := by
    have h1 : W ≤ ∑ T ∈ K, (#T : ℝ) * w T := by
      refine Finset.sum_le_sum fun T hT => ?_
      have h2 : (1 : ℝ) ≤ (#T : ℝ) := by
        have := (hsize T hT).1
        have : 1 ≤ #T := Finset.card_pos.mpr this
        exact_mod_cast this
      nlinarith [hw T]
    have h3 : ∑ v : X, Slack.wLoad K w v ≤ (Fintype.card X : ℝ) := by
      have := Finset.sum_le_sum (fun v (_ : v ∈ (univ : Finset X)) => hload v)
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at this
      exact this
    rw [LEUnif.sum_wLoad_eq K w] at h3
    linarith
  obtain ⟨M', hM', hM'card⟩ :=
    LEUnif.exists_matching_of_padMatchingLE (fun T hT => (hsize T hT).1) hM
  refine ⟨M', hM', ?_⟩
  rw [hM'card]
  rw [hsumw'] at hMcard
  have hslackbound : b * Slack.slackTotal K' w'
      ≤ β * (Fintype.card X : ℝ) + b * (r : ℝ) * (1 / γ₂ + 3) := by
    have h1 : b * Slack.slackTotal K' w'
        ≤ b * ((Fintype.card X : ℝ) + (r : ℝ) * (m : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hslackUB hb.le
    have h2 : (r : ℝ) * (m : ℝ) ≤ (r : ℝ) * (W + 1 / γ₂ + 3) := by
      have hr0 : (0 : ℝ) ≤ (r : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_left hmub hr0
    have hbr : b * (1 + (r : ℝ)) = β := by
      rw [hbdef]
      field_simp
    nlinarith [hb.le, hWX, hW0]
  have hbw : b * W ≤ β * W := mul_le_mul_of_nonneg_right hbβ hW0
  linarith only [hMcard, hslackbound, hbw]

-- Axiom check: `[propext, Classical.choice, Quot.sound]`.


end Nibble
