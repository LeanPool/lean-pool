/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Bridge.WalkCalculus

import Mathlib.Tactic.Linarith

/-!
# Kemperman's formula for forests and the first-passage decomposition

Work package WP2a of the bridge plan (no toolkit). Source lines 1137–1139 and 1338–1341 (Dwass'
formula for a forest of `ℓ` independent Bienaymé trees, used in Lemma `lem:forest_estimates` and in
Corollary `cor:consequenceS`(iii)), 2250–2255 (the Markov property at the first passage time to
`-ℓ`, proof of Lemma `lem:parent`(iii)).

`PlaneTree.forestSizeWeight μ ℓ q` (`Bienayme/Basic.lean`) is the total weight of the `ℓ`-tuples of
trees with `q` vertices in total, i.e. `P(|𝒢_ℓ| = q)` for a forest `𝒢_ℓ` of `ℓ` independent
`μ`-Bienaymé trees, and `Lukasiewicz.walkMass μ q s = P(S_q = s)`.

## Main statements

* `exists_first_sum_take_eq`: discrete intermediate value property of skip-free sequences.
* `card_filter_rotate_firstPassageAt` (**generalized cycle lemma**): a sequence of `q` integers
  `≥ -1` with sum `-ℓ`, `ℓ ≥ 1`, has exactly `ℓ` cyclic shifts whose first passage time to `-ℓ`
  is `q` (`FirstPassageAt ℓ`).
* `walkVecLaw_firstPassageAt`: `P((X_1..X_q) first reaches -ℓ at time q) = P(|𝒢_ℓ| = q)` (forests
  are coded by `forestSeq`, a bijection onto `forestSet ℓ q`, `forestMap_bijective`).
* `natCast_mul_forestSizeWeight` (**Kemperman's formula for forests**):
  `1 ≤ ℓ → q P(|𝒢_ℓ| = q) = ℓ P(S_q = -ℓ)`; real forms `natCast_mul_forestSizeWeight_toReal` and
  `forestSizeWeight_toReal_eq` (`P(|𝒢_ℓ| = q) = (ℓ / q) Ψ_q(-ℓ)` for `q ≥ 1`).
* `walkMass_neg_eq_sum`, `walkProb_neg_eq_sum` (**forest first-passage decomposition**):
  `Ψ_N(-ℓ) = ∑_{q ≤ N} P(|𝒢_ℓ| = q) Ψ_{N-q}(0)`.

The proof of Kemperman's formula is the classical one: the `q` cyclic shifts of `(X_1..X_q)` have
the same law (`walkVecLaw_rotate`), and on `{S_q = -ℓ}` exactly `ℓ` of them are forest sequences.
No criticality is assumed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PoissonDeclumping.Bridge

open Lukasiewicz PlaneTree Cyclic

/-! ### First hitting times of skip-free sequences -/

/-- **Discrete intermediate value property.** If the increments are `≥ -1`, `v ≤ 0` and some
partial sum `x_1 + ⋯ + x_b` is `≤ v`, then there is a first time `l ≤ b` with
`x_1 + ⋯ + x_l = v`, all earlier partial sums being `> v`. -/
theorem exists_first_sum_take_eq {x : List ℤ} (hx : ∀ a ∈ x, -1 ≤ a) {v : ℤ} (hv : v ≤ 0)
    {b : ℕ} (hb : (x.take b).sum ≤ v) :
    ∃ l ≤ b, (x.take l).sum = v ∧ ∀ l' < l, v < (x.take l').sum := by
  classical
  have hex : ∃ l, (x.take l).sum ≤ v := ⟨b, hb⟩
  refine ⟨Nat.find hex, Nat.find_min' hex hb, ?_, fun l' hl' => ?_⟩
  · have hle := Nat.find_spec hex
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0] at hle ⊢
      simp only [List.take_zero, List.sum_nil] at hle ⊢
      omega
    · obtain ⟨l, hl⟩ : ∃ l, Nat.find hex = l + 1 := ⟨Nat.find hex - 1, by omega⟩
      have hprev : v < (x.take l).sum := by
        have := Nat.find_min hex (show l < Nat.find hex by omega)
        exact lt_of_not_ge this
      rw [hl] at hle ⊢
      rcases lt_or_ge l x.length with hlt | hge
      · rw [List.sum_take_succ _ _ hlt] at hle ⊢
        have := hx _ (List.getElem_mem hlt)
        omega
      · rw [List.take_of_length_le (by omega)] at hle
        rw [List.take_of_length_le hge] at hprev
        omega
  · exact lt_of_not_ge (Nat.find_min hex hl')

/-! ### The generalized cycle lemma -/

/-- `𝐱` has its first passage time to `-ℓ` at its end: `x_1 + ⋯ + x_q = -ℓ` (`q = |𝐱|`) and
all proper partial sums `x_1 + ⋯ + x_j`, `j < q`, are `> -ℓ`. -/
def FirstPassageAt (ℓ : ℕ) (x : List ℤ) : Prop :=
  x.sum = -(ℓ : ℤ) ∧ ∀ j < x.length, -(ℓ : ℤ) < (x.take j).sum


/-- The partial sums of the rotation `x.rotate i` stay above `-ℓ` before time `|x|` iff `i` is a
strict running minimum of the partial sums of `x` that the later partial sums (before `|x|`) do
not undercut by `ℓ` or more. -/
theorem rotate_forest_iff {x : List ℤ} {ℓ : ℕ} (hs : x.sum = -(ℓ : ℤ)) {i : ℕ}
    (hi : i < x.length) :
    (∀ j < x.length, -(ℓ : ℤ) < ((x.rotate i).take j).sum) ↔
      (∀ l, i ≤ l → l < x.length → (x.take i).sum - ℓ < (x.take l).sum) ∧
        (∀ l < i, (x.take i).sum < (x.take l).sum) := by
  constructor
  · intro h
    refine ⟨fun l hil hl => ?_, fun l hl => ?_⟩
    · have := h (l - i) (by omega)
      rw [sum_take_rotate_of_le hi.le (by omega), Nat.add_sub_cancel' hil] at this
      linarith
    · have := h (x.length - i + l) (by omega)
      rw [sum_take_rotate_of_ge hi.le hl.le, hs] at this
      linarith
  · rintro ⟨h1, h2⟩ j hj
    rcases lt_or_ge j (x.length - i) with hji | hji
    · rw [sum_take_rotate_of_le hi.le hji.le]
      have := h1 (i + j) (by omega) (by omega)
      linarith
    · obtain ⟨j', rfl⟩ : ∃ j', j = x.length - i + j' := ⟨j - (x.length - i), by omega⟩
      rw [sum_take_rotate_of_ge hi.le (by omega), hs]
      have := h2 j' (by omega)
      linarith

/-- A cyclic shift of a sequence with sum `-ℓ` has first passage time `|𝐱|` to `-ℓ` iff the
characterization of `rotate_forest_iff` holds. -/
theorem firstPassageAt_rotate_iff {x : List ℤ} {ℓ : ℕ} (hs : x.sum = -(ℓ : ℤ)) {i : ℕ}
    (hi : i < x.length) :
    FirstPassageAt ℓ (x.rotate i) ↔
      (∀ l, i ≤ l → l < x.length → (x.take i).sum - ℓ < (x.take l).sum) ∧
        (∀ l < i, (x.take i).sum < (x.take l).sum) := by
  rw [← rotate_forest_iff hs hi, FirstPassageAt, List.length_rotate, (List.rotate_perm x i).sum_eq,
    hs]
  simp only [true_and]

/-- **Generalized cycle lemma** (the combinatorial core of Kemperman's formula, source lines
1137–1139). A sequence `𝐱` of integers `≥ -1` with sum `-ℓ`, `ℓ ≥ 1`, has exactly `ℓ` cyclic
shifts `𝐱.rotate i` (`0 ≤ i < |𝐱|`) whose first passage time to `-ℓ` is `|𝐱|`. -/
theorem card_filter_rotate_firstPassageAt {x : List ℤ} (hx : ∀ a ∈ x, -1 ≤ a) {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) (hs : x.sum = -(ℓ : ℤ))
    [DecidablePred fun i : ℕ => FirstPassageAt ℓ (x.rotate i)] :
    ((Finset.range x.length).filter (fun i => FirstPassageAt ℓ (x.rotate i))).card = ℓ := by
  have hq1 : 1 ≤ x.length := by
    rcases Nat.eq_zero_or_pos x.length with h0 | h
    · have : x = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [this, List.sum_nil] at hs
      omega
    · exact h
  set S : ℕ → ℤ := fun l => (x.take l).sum with hS
  obtain ⟨l₀, hl₀, hmin⟩ := Finset.exists_min_image (Finset.range x.length) S
    ⟨0, Finset.mem_range.mpr (by omega)⟩
  have hl₀q : l₀ < x.length := Finset.mem_range.mp hl₀
  set m := S l₀ with hm
  have hmin' : ∀ l < x.length, m ≤ S l := fun l hl => hmin l (Finset.mem_range.mpr hl)
  have hm0 : m ≤ 0 := by
    have := hmin' 0 (by omega)
    simpa [hS] using this
  have hmℓ : m + ℓ - 1 ≤ 0 := by
    have h1 := hmin' (x.length - 1) (by omega)
    have h2 : S x.length = S (x.length - 1) + x[x.length - 1] := by
      have := List.sum_take_succ x (x.length - 1) (by omega)
      rw [show x.length - 1 + 1 = x.length by omega] at this
      exact this
    have h3 : S x.length = -(ℓ : ℤ) := by simp only [hS, List.take_length, hs]
    have h4 := hx _ (List.getElem_mem (show x.length - 1 < x.length by omega))
    omega
  have hcard : (Finset.Icc m (m + ℓ - 1)).card = ℓ := by
    rw [Int.card_Icc]
    omega
  refine Eq.trans ?_ hcard
  refine Finset.card_bij (fun i _ => S i) ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_filter, Finset.mem_range] at hi
    obtain ⟨h1, h2⟩ := (firstPassageAt_rotate_iff hs hi.1).mp hi.2
    rw [Finset.mem_Icc]
    refine ⟨hmin' i hi.1, ?_⟩
    rcases le_or_gt i l₀ with hil | hil
    · have := h1 l₀ hil hl₀q
      change S i - ℓ < m at this
      omega
    · have := h2 l₀ hil
      have := hmin' i hi.1
      change S i < m at *
      omega
  · intro i hi i' hi' he
    rw [Finset.mem_filter, Finset.mem_range] at hi hi'
    obtain ⟨-, h2⟩ := (firstPassageAt_rotate_iff hs hi.1).mp hi.2
    obtain ⟨-, h2'⟩ := (firstPassageAt_rotate_iff hs hi'.1).mp hi'.2
    change S i = S i' at he
    rcases lt_trichotomy i i' with h | h | h
    · have := h2' i h
      change S i' < S i at this
      omega
    · exact h
    · have := h2 i' h
      change S i < S i' at this
      omega
  · intro v hv
    rw [Finset.mem_Icc] at hv
    obtain ⟨l, hll₀, hlv, hlt⟩ := exists_first_sum_take_eq hx (v := v) (b := l₀) (by omega)
      (by change m ≤ v; omega)
    have hlq : l < x.length := lt_of_le_of_lt hll₀ hl₀q
    refine ⟨l, ?_, hlv⟩
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨hlq, (firstPassageAt_rotate_iff hs hlq).mpr ⟨fun l' _ hl' => ?_, fun l' hl' => ?_⟩⟩
    · have := hmin' l' hl'
      change m ≤ S l' at this
      change S l - ℓ < S l'
      change S l = v at hlv
      omega
    · have := hlt l' hl'
      change v < S l' at this
      change S l = v at hlv
      change S l < S l'
      omega


/-! ### Forest sequences -/

/-- The sequences in `ℤ_{≥ -1}^q` whose first passage time to `-ℓ` is `q`: the DFS sequences of the
forests of `ℓ` trees with `q` vertices in total. -/
def forestSet (ℓ q : ℕ) : Set (List ℤ) :=
  {x | x.length = q ∧ (∀ a ∈ x, -1 ≤ a) ∧ FirstPassageAt ℓ x}

/-- Excursion property of forest sequences (a public copy of a private lemma of
`Lukasiewicz/Coding.lean`). -/
theorem excursion_forestSeq (ts : List PlaneTree) :
    (forestSeq ts).sum = -(ts.length : ℤ) ∧
      ∀ j < (forestSeq ts).length, -(ts.length : ℤ) < ((forestSeq ts).take j).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    obtain ⟨hs, hp⟩ := ih
    obtain ⟨hts, htp⟩ := dfsSeq_excursion t
    simp only [forestSeq_cons, List.sum_append, List.length_cons, hs, hts, List.length_append]
    refine ⟨by push_cast; omega, fun j hj => ?_⟩
    rw [List.take_append, List.sum_append]
    rcases lt_or_ge j t.dfsSeq.length with hjt | hjt
    · have h1 := htp j hjt
      rw [Nat.sub_eq_zero_of_le hjt.le]
      simp only [List.take_zero, List.sum_nil]
      push_cast
      linarith
    · rw [List.take_of_length_le hjt, hts]
      have h2 := hp (j - t.dfsSeq.length) (by omega)
      push_cast
      linarith

theorem length_forestSeq_eq_sum (ts : List PlaneTree) :
    (forestSeq ts).length = (ts.map vertexCount).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih => simp [forestSeq_cons, ih, length_dfsSeq]

/-- Forests with the same number of trees are determined by their DFS sequence. -/
theorem forestSeq_injective_of_length_eq {ts us : List PlaneTree} (hl : ts.length = us.length)
    (h : forestSeq ts = forestSeq us) : ts = us := by
  induction ts generalizing us with
  | nil =>
    cases us with
    | nil => rfl
    | cons _ _ => simp at hl
  | cons t ts ih =>
    cases us with
    | nil => simp at hl
    | cons u us =>
      simp only [forestSeq_cons] at h
      obtain ⟨rfl, h'⟩ := dfsSeq_append_inj h
      rw [ih (by simpa using hl) h']

theorem walkWeight_forestSeq (μ : PMF ℕ) (ts : List PlaneTree) :
    walkWeight μ (forestSeq ts) = (ts.map (weight μ)).prod := by
  induction ts with
  | nil => simp [walkWeight]
  | cons t ts ih =>
    rw [forestSeq_cons, walkWeight_append, ih, ← weight_eq_walkWeight, List.map_cons,
      List.prod_cons]

theorem forestSeq_ofFn_mem_forestSet {ℓ : ℕ} (f : Fin ℓ → PlaneTree) :
    forestSeq (List.ofFn f) ∈ forestSet ℓ (∑ i, (f i).vertexCount) := by
  obtain ⟨hs, hp⟩ := excursion_forestSeq (List.ofFn f)
  rw [List.length_ofFn] at hs hp
  refine ⟨by rw [length_forestSeq_eq_sum, List.map_ofFn, List.sum_ofFn]; rfl, fun a ha => ?_, hs,
    hp⟩
  simp only [forestSeq, List.mem_flatMap] at ha
  obtain ⟨t, -, ht⟩ := ha
  exact neg_one_le_of_mem_dfsSeq ht

/-- The DFS coding of forests of `ℓ` trees with `q` vertices in total. -/
def forestMap (ℓ q : ℕ) :
    {f : Fin ℓ → PlaneTree | ∑ i, (f i).vertexCount = q} → forestSet ℓ q :=
  fun f => ⟨forestSeq (List.ofFn f.1), by
    have := forestSeq_ofFn_mem_forestSet f.1
    rwa [show ∑ i, (f.1 i).vertexCount = q from f.2] at this⟩

theorem forestMap_bijective (ℓ q : ℕ) : Function.Bijective (forestMap ℓ q) := by
  constructor
  · rintro ⟨f, hf⟩ ⟨g, hg⟩ h
    have h' : forestSeq (List.ofFn f) = forestSeq (List.ofFn g) := congrArg Subtype.val h
    exact Subtype.ext (List.ofFn_injective (forestSeq_injective_of_length_eq (by simp) h'))
  · rintro ⟨x, hxl, hge, hs, hp⟩
    obtain ⟨ts, hlen, hts⟩ := exists_forestSeq_eq x hge ℓ hs hp
    subst hlen
    have hof : List.ofFn (fun i : Fin ts.length => ts[(i : ℕ)]) = ts := List.ofFn_getElem
    refine ⟨⟨fun i => ts[(i : ℕ)], ?_⟩, Subtype.ext ?_⟩
    · change ∑ i : Fin ts.length, (ts[(i : ℕ)]).vertexCount = q
      have hsum : (ts.map vertexCount).sum = ∑ i : Fin ts.length, (ts[(i : ℕ)]).vertexCount := by
        conv_lhs => rw [← hof]
        rw [List.map_ofFn, List.sum_ofFn]
        rfl
      rw [← hsum, ← length_forestSeq_eq_sum, hts, hxl]
    · change forestSeq (List.ofFn fun i : Fin ts.length => ts[(i : ℕ)]) = x
      rw [hof, hts]

/-- The total weight of the forests of `ℓ` trees with `q` vertices is the total walk weight of
their DFS sequences. -/
theorem forestSizeWeight_eq_tsum (μ : PMF ℕ) (ℓ q : ℕ) :
    forestSizeWeight μ ℓ q = ∑' x : forestSet ℓ q, walkWeight μ x.1 := by
  rw [← (Equiv.ofBijective _ (forestMap_bijective ℓ q)).tsum_eq]
  have h1 : ∀ f : {f : Fin ℓ → PlaneTree | ∑ i, (f i).vertexCount = q},
      walkWeight μ (Equiv.ofBijective _ (forestMap_bijective ℓ q) f).1 = ∏ i, weight μ (f.1 i) := by
    intro f
    change walkWeight μ (forestSeq (List.ofFn f.1)) = _
    rw [walkWeight_forestSeq, List.map_ofFn, List.prod_ofFn]
    rfl
  simp_rw [h1]
  rw [tsum_subtype {f : Fin ℓ → PlaneTree | ∑ i, (f i).vertexCount = q}
    (fun f => ∏ i, weight μ (f i)), forestSizeWeight]
  refine tsum_congr fun f => ?_
  by_cases hf : ∑ i, (f i).vertexCount = q
  · rw [ite_eq_left hf, Set.indicator_of_mem (show f ∈ {f : Fin ℓ → PlaneTree |
      ∑ i, (f i).vertexCount = q} from hf)]
  · rw [ite_eq_right hf, Set.indicator_of_notMem (show f ∉ {f : Fin ℓ → PlaneTree |
      ∑ i, (f i).vertexCount = q} from hf)]

/-- **Forests in the walk.** `P((X_1, …, X_q) has first passage time `q` to `-ℓ`) = P(|𝒢_ℓ| = q)`,
where `𝒢_ℓ` is a forest of `ℓ` independent Bienaymé trees. -/
theorem walkVecLaw_firstPassageAt (μ : PMF ℕ) (ℓ q : ℕ) :
    walkVecLaw μ q {ω | FirstPassageAt ℓ (List.ofFn ω)} = forestSizeWeight μ ℓ q := by
  rw [forestSizeWeight_eq_tsum]
  refine walkVecLaw_eq_tsum μ (fun x hx => ⟨hx.1, hx.2.1⟩) (fun ω => ?_)
  simp only [forestSet, Set.mem_ofPred_eq, List.length_ofFn, List.mem_ofFn, true_and,
    forall_exists_index, forall_apply_eq_imp_iff]
  exact and_comm

/-- Almost surely all increments are `≥ -1`. -/
theorem ae_walkVecLaw_neg_one_le (μ : PMF ℕ) (n : ℕ) :
    ∀ᵐ ω ∂walkVecLaw μ n, ∀ i, -1 ≤ ω i := by
  rw [ae_iff, ← Measure.tsum_indicator_apply_singleton _ _ (Set.to_countable _).measurableSet]
  refine ENNReal.tsum_eq_zero.mpr fun ω => ?_
  by_cases h : ω ∈ {ω : Fin n → ℤ | ¬∀ i, -1 ≤ ω i}
  · rw [Set.indicator_of_mem h, walkVecLaw_singleton]
    simp only [Set.mem_ofPred_eq, not_forall, not_le] at h
    obtain ⟨i, hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [stepPMF_apply, ite_eq_right (by omega)])
  · rw [Set.indicator_of_notMem h]

/-- **Kemperman's formula for forests** (Dwass, source lines 1137–1139, 1338–1341): for `ℓ ≥ 1`,
`q P(|𝒢_ℓ| = q) = ℓ P(S_q = -ℓ)`, where `𝒢_ℓ` is a forest of `ℓ` independent Bienaymé trees. -/
theorem natCast_mul_forestSizeWeight (μ : PMF ℕ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (q : ℕ) :
    (q : ℝ≥0∞) * forestSizeWeight μ ℓ q = ℓ * walkMass μ q (-ℓ) := by
  classical
  have hrot : ∀ r : ℕ, walkVecLaw μ q {ω | FirstPassageAt ℓ ((List.ofFn ω).rotate r)} =
      forestSizeWeight μ ℓ q := by
    intro r
    rw [walkVecLaw_rotate μ q r (FirstPassageAt ℓ), walkVecLaw_firstPassageAt]
  have hsum : ∑ r ∈ Finset.range q, walkVecLaw μ q {ω | FirstPassageAt ℓ ((List.ofFn ω).rotate r)} =
      q * forestSizeWeight μ ℓ q := by
    simp only [hrot, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← hsum, ← walkVecLaw_sum_eq μ q (-ℓ)]
  simp_rw [← lintegral_indicator_one (Set.to_countable _).measurableSet]
  rw [← lintegral_finsetSum _ (fun r _ => measurable_of_countable _),
    ← lintegral_const_mul _ (measurable_of_countable _)]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_walkVecLaw_neg_one_le μ q] with ω hω
  have hx : ∀ a ∈ List.ofFn ω, -1 ≤ a := by
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact hω i
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, Pi.one_apply]
  rw [Finset.sum_boole]
  by_cases hs : ∑ i, ω i = -(ℓ : ℤ)
  · have hs' : (List.ofFn ω).sum = -(ℓ : ℤ) := by rw [List.sum_ofFn]; exact hs
    rw [ite_eq_left hs, mul_one]
    have h := card_filter_rotate_firstPassageAt hx hℓ hs'
    rw [List.length_ofFn] at h
    rw [h]
  · rw [ite_eq_right hs, mul_zero, Nat.cast_eq_zero, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff]
    intro r _ h
    apply hs
    rw [← List.sum_ofFn, ← (List.rotate_perm _ r).sum_eq]
    exact h.1

/-- `P(|𝒢_ℓ| = q) ≤ 1`. -/
theorem forestSizeWeight_le_one (μ : PMF ℕ) (ℓ q : ℕ) : forestSizeWeight μ ℓ q ≤ 1 :=
  (ENNReal.le_tsum q).trans ((tsum_forestSizeWeight μ ℓ).le.trans
    (pow_le_one₀ zero_le (bienayme_univ_le_one μ)))

theorem forestSizeWeight_ne_top (μ : PMF ℕ) (ℓ q : ℕ) : forestSizeWeight μ ℓ q ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (forestSizeWeight_le_one μ ℓ q)

/-- **Kemperman's formula for forests**, with `Ψ`: `q P(|𝒢_ℓ| = q) = ℓ Ψ_q(-ℓ)`. -/
theorem natCast_mul_forestSizeWeight_toReal (μ : PMF ℕ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (q : ℕ) :
    (q : ℝ) * (forestSizeWeight μ ℓ q).toReal = ℓ * walkProb μ q (-ℓ) := by
  have h := congrArg ENNReal.toReal (natCast_mul_forestSizeWeight μ hℓ q)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast] at h
  rw [h, walkProb_eq_toReal_walkMass]

/-- **Kemperman's formula for forests**, the paper's form (source line 1138):
`P(|𝒢_ℓ| = q) = (ℓ / q) P(S_q = -ℓ)` for `q ≥ 1`. -/
theorem forestSizeWeight_toReal_eq (μ : PMF ℕ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {q : ℕ} (hq : 1 ≤ q) :
    (forestSizeWeight μ ℓ q).toReal = ℓ / q * walkProb μ q (-ℓ) := by
  have h := natCast_mul_forestSizeWeight_toReal μ hℓ q
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  field_simp
  linarith


/-! ### The first-passage decomposition at level `-ℓ` -/

/-- The first passage time to `-ℓ` is unique: if both `(x_1, …, x_q)` and `(x_1, …, x_{q'})`
have their first passage time to `-ℓ` at their end, then `q = q'` (for `q, q' ≤ |𝐱|`). -/
theorem firstPassageAt_take_unique {x : List ℤ} {ℓ q q' : ℕ} (hq : q ≤ x.length)
    (hq' : q' ≤ x.length) (h : FirstPassageAt ℓ (x.take q)) (h' : FirstPassageAt ℓ (x.take q')) :
    q = q' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := h'.2 q (by rw [List.length_take]; omega)
    rw [List.take_take, min_eq_left hlt.le, h.1] at this
    exact lt_irrefl _ this
  · have := h.2 q' (by rw [List.length_take]; omega)
    rw [List.take_take, min_eq_left hlt.le, h'.1] at this
    exact lt_irrefl _ this

/-- **Forest first-passage decomposition** (source lines 2250–2255): decomposing according to the
first passage time `q` of the walk to `-ℓ` (the size of the forest of the first `ℓ` trees),
`Ψ_N(-ℓ) = ∑_{q ≤ N} P(|𝒢_ℓ| = q) Ψ_{N-q}(0)`. -/
theorem walkMass_neg_eq_sum (μ : PMF ℕ) (ℓ N : ℕ) :
    walkMass μ N (-ℓ) =
      ∑ q ∈ Finset.range (N + 1), forestSizeWeight μ ℓ q * walkMass μ (N - q) 0 := by
  set E : ℕ → Set (Fin N → ℤ) :=
    fun q => {ω | FirstPassageAt ℓ ((List.ofFn ω).take q) ∧ ∑ i, ω i = -(ℓ : ℤ)} with hEdef
  have hE : ∀ q ≤ N, walkVecLaw μ N (E q) = forestSizeWeight μ ℓ q * walkMass μ (N - q) 0 := by
    intro q hq
    have h := walkVecLaw_take_drop_sum μ hq (FirstPassageAt ℓ) (fun _ => True) (-(ℓ : ℤ))
      (-(ℓ : ℤ))
    simp only [true_and, sub_self] at h
    have e1 : E q = {ω : Fin N → ℤ | FirstPassageAt ℓ ((List.ofFn ω).take q) ∧
        ((List.ofFn ω).take q).sum = -(ℓ : ℤ) ∧ ∑ i, ω i = -(ℓ : ℤ)} := by
      ext ω
      simp only [hEdef, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, h1.1, h2⟩
      · rintro ⟨h1, -, h2⟩
        exact ⟨h1, h2⟩
    have e2 : {a : Fin q → ℤ | FirstPassageAt ℓ (List.ofFn a) ∧ ∑ i, a i = -(ℓ : ℤ)} =
        {a | FirstPassageAt ℓ (List.ofFn a)} := by
      ext a
      simp only [Set.mem_ofPred_eq, and_iff_left_iff_imp]
      intro h1
      rw [← List.sum_ofFn]
      exact h1.1
    rw [e1, h, e2, walkVecLaw_firstPassageAt, walkVecLaw_sum_eq]
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (N + 1))) E := by
    intro q hq q' hq' hne
    refine Set.disjoint_left.mpr fun ω h h' => hne ?_
    have hq1 : q ≤ (List.ofFn ω).length := by
      rw [List.length_ofFn]; have := Finset.mem_range.mp hq; omega
    have hq1' : q' ≤ (List.ofFn ω).length := by
      rw [List.length_ofFn]; have := Finset.mem_range.mp hq'; omega
    exact firstPassageAt_take_unique hq1 hq1' h.1 h'.1
  have hsub : ⋃ q ∈ Finset.range (N + 1), E q ⊆ {ω : Fin N → ℤ | ∑ i, ω i = -(ℓ : ℤ)} := by
    intro ω hω
    simp only [Set.mem_iUnion, Finset.mem_range, exists_prop] at hω
    obtain ⟨q, -, -, h2⟩ := hω
    exact h2
  have hcover : {ω : Fin N → ℤ | ∑ i, ω i = -(ℓ : ℤ)} ∩ {ω | ∀ i, -1 ≤ ω i} ⊆
      ⋃ q ∈ Finset.range (N + 1), E q := by
    rintro ω ⟨hs, hge⟩
    simp only [Set.mem_ofPred_eq] at hs hge
    have hx : ∀ a ∈ List.ofFn ω, -1 ≤ a := by
      intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      exact hge i
    obtain ⟨l, hlN, hl, hlt⟩ := exists_first_sum_take_eq hx (v := -(ℓ : ℤ)) (b := N)
      (by omega) (by rw [List.take_of_length_le (by simp), List.sum_ofFn, hs])
    simp only [Set.mem_iUnion, Finset.mem_range, exists_prop]
    refine ⟨l, by omega, ⟨hl, fun j hj => ?_⟩, hs⟩
    rw [List.length_take, List.length_ofFn] at hj
    rw [List.take_take, min_eq_left (by omega)]
    exact hlt j (by omega)
  have hnull : walkVecLaw μ N {ω : Fin N → ℤ | ∀ i, -1 ≤ ω i}ᶜ = 0 :=
    ae_iff.mp (ae_walkVecLaw_neg_one_le μ N)
  rw [← walkVecLaw_sum_eq]
  calc walkVecLaw μ N {ω | ∑ i, ω i = -(ℓ : ℤ)}
      = walkVecLaw μ N (⋃ q ∈ Finset.range (N + 1), E q) := by
        refine le_antisymm ?_ (measure_mono hsub)
        rw [← measure_inter_conull hnull]
        exact measure_mono hcover
    _ = ∑ q ∈ Finset.range (N + 1), walkVecLaw μ N (E q) :=
        measure_biUnion_finset hdisj fun _ _ => (Set.to_countable _).measurableSet
    _ = _ := Finset.sum_congr rfl fun q hq => hE q (by have := Finset.mem_range.mp hq; omega)

/-- **Forest first-passage decomposition**, with `Ψ` (source lines 2250–2255):
`Ψ_N(-ℓ) = ∑_{q ≤ N} P(|𝒢_ℓ| = q) Ψ_{N-q}(0)`. -/
theorem walkProb_neg_eq_sum (μ : PMF ℕ) (ℓ N : ℕ) :
    walkProb μ N (-ℓ) = ∑ q ∈ Finset.range (N + 1),
      (forestSizeWeight μ ℓ q).toReal * walkProb μ ((N - q : ℕ) : ℤ) 0 := by
  rw [walkProb_eq_toReal_walkMass, walkMass_neg_eq_sum, ENNReal.toReal_sum
    (fun q _ => ENNReal.mul_ne_top (forestSizeWeight_ne_top μ ℓ q)
      (by rw [← walkVecLaw_sum_eq]; exact measure_ne_top _ _))]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [ENNReal.toReal_mul, walkProb_eq_toReal_walkMass]

end PoissonDeclumping.Bridge
