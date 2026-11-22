/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.PseudolineArrangements.Realizable
public import Mathlib.Tactic.Bound
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Monotone arrangements of pseudolines

A monotone arrangement of `n` pseudolines is a family of continuous functions `f i : ℝ → ℝ`
whose graphs cross pairwise exactly once, the indices increasing upwards at the far left. Its
chirotope function `MonotoneArrangement.chiFun` is a function of ordered triples of elements of
`Option (Fin n)`, `none` standing for the line at infinity: on three pseudolines `i < j < k` it is
the sign of `crossX j k - crossX i j`, on `i < j` and the line at infinity it is `1`, and it is
extended alternatingly.

For an arrangement of straight lines `y = a i * x + b i` with decreasing slopes
(`MonotoneArrangement.ofLines`), this is the chirotope of the vectors `(-1, a i, b i)` and
`(0, 0, 1)` (`MonotoneArrangement.chiFun_ofLines`); in particular it is a chirotope as soon as
there are two lines (`MonotoneArrangement.isChirotope_chiFun_ofLines`). For every monotone
arrangement, the chirotope function is uniform exactly when the arrangement is simple
(`MonotoneArrangement.isUniform_chiFun_iff`).

## References

* S. Felsner, J. E. Goodman, *Pseudoline arrangements*, Chapter 5 of *Handbook of Discrete and
  Computational Geometry*, 3rd ed., 2017, §5.1–5.2.
* J. Richter-Gebert, G. M. Ziegler, *Oriented matroids*, Chapter 6 of *Handbook of Discrete and
  Computational Geometry*, 3rd ed., 2017, §6.2.3.
-/

@[expose] public section

namespace LeanPool.PseudolineArrangements

open Equiv

/-- The comparison sign in a linear order: `1` when `x < y`, `-1` when `y < x`, `0` when equal. -/
def ltSign {α : Type*} [LinearOrder α] (x y : α) : SignType :=
  if x < y then 1 else if y < x then -1 else 0

/-- The sign of the permutation sorting a triple of distinct elements, and `0` on a triple with a
repeated entry. -/
def tupleSign {α : Type*} [LinearOrder α] (t : Fin 3 → α) : SignType :=
  ltSign (t 0) (t 1) * ltSign (t 0) (t 2) * ltSign (t 1) (t 2)

/-- A monotone (x-monotone) arrangement of `n` pseudolines: indices increase upward at the far
left, and each pair crosses exactly once. -/
structure MonotoneArrangement (n : ℕ) where
  /-- The pseudolines, as graphs of functions. -/
  f : Fin n → ℝ → ℝ
  /-- Each pseudoline is continuous. -/
  continuous : ∀ i, Continuous (f i)
  /-- The abscissa where `i` and `j` cross. -/
  crossX : Fin n → Fin n → ℝ
  /-- The crossing abscissa is symmetric. -/
  crossX_comm : ∀ i j, crossX i j = crossX j i
  /-- The value on the diagonal is fixed, so that the data are determined by `f`. -/
  crossX_self : ∀ i, crossX i i = 0
  /-- Two pseudolines cross exactly once, at `crossX i j`, `i` below `j` on the left. -/
  cross : ∀ i j, i < j → (∀ x < crossX i j, f i x < f j x) ∧
    f i (crossX i j) = f j (crossX i j) ∧ ∀ x, crossX i j < x → f j x < f i x

namespace MonotoneArrangement

variable {n : ℕ} (A : MonotoneArrangement n)

/-- Simple: no three pseudolines through a common point. -/
def IsSimple : Prop :=
  ∀ i j k : Fin n, i < j → j < k → A.crossX i j ≠ A.crossX j k

/-- The value on the increasing enumeration `i < j < k` of `{i, j, k}`:
`sign (crossX j k - crossX i j)`. -/
noncomputable def tripleSign (i j k : Fin n) : SignType :=
  SignType.sign (A.crossX (max (min i j) (min (max i j) k)) (max (max i j) k) -
    A.crossX (min (min i j) k) (max (min i j) (min (max i j) k)))

/-- The chirotope function: `sign (crossX j k - crossX i j)` on `some i, some j, some k` with
`i < j < k`, `1` on `some i, some j, none` with `i < j`, extended alternatingly (`none` is last in
`WithTop (Fin n)`). -/
noncomputable def chiFun (t : Fin 3 → Option (Fin n)) : SignType :=
  tupleSign (α := WithTop (Fin n)) t *
    match t 0, t 1, t 2 with
    | some i, some j, some k => A.tripleSign i j k
    | _, _, _ => 1

/-- Straight lines `y = a i * x + b i` with strictly decreasing slopes. -/
noncomputable def ofLines (a b : Fin n → ℝ) (ha : StrictAnti a) : MonotoneArrangement n where
  f i x := a i * x + b i
  continuous _ := by fun_prop
  crossX i j := if i = j then 0 else (b j - b i) / (a i - a j)
  crossX_comm i j := by
    by_cases h : i = j
    · subst h; rfl
    · simp only [h, Ne.symm h, ite_false]
      rw [← neg_div_neg_eq (b i - b j), neg_sub, neg_sub]
  crossX_self i := by simp
  cross i j hij := by
    have h : 0 < a i - a j := sub_pos.2 (ha hij)
    simp only [hij.ne, ite_false]
    refine ⟨fun x hx => ?_, ?_, fun x hx => ?_⟩
    · have := (lt_div_iff₀ h).1 hx
      nlinarith
    · field_simp
      ring
    · have := (div_lt_iff₀ h).1 hx
      nlinarith

/-! ### Signs of comparisons -/

theorem ltSign_swap {α : Type*} [LinearOrder α] (x y : α) : ltSign y x = -ltSign x y := by
  unfold ltSign
  rcases lt_trichotomy x y with h | rfl | h
  · simp [h, h.not_gt]
  · simp
  · simp [h, h.not_gt]

theorem ltSign_self {α : Type*} [LinearOrder α] (x : α) : ltSign x x = 0 := by simp [ltSign]

theorem ltSign_of_lt {α : Type*} [LinearOrder α] {x y : α} (h : x < y) : ltSign x y = 1 := by
  simp [ltSign, h]

theorem ltSign_coe {α : Type*} [LinearOrder α] (x y : α) :
    ltSign (α := WithTop α) (some x) (some y) = ltSign x y := by
  unfold ltSign
  change (if (x : WithTop α) < y then _ else if (y : WithTop α) < x then _ else _) = _
  simp only [WithTop.coe_lt_coe]

theorem ltSign_coe_top {α : Type*} [LinearOrder α] (x : α) :
    ltSign (α := WithTop α) (some x) none = 1 :=
  ltSign_of_lt (WithTop.coe_lt_top x)

theorem ltSign_top_coe {α : Type*} [LinearOrder α] (x : α) :
    ltSign (α := WithTop α) none (some x) = -1 := by
  have h := ltSign_swap (α := WithTop α) (x : WithTop α) ⊤
  rw [show ltSign (α := WithTop α) (x : WithTop α) ⊤ = 1 from ltSign_coe_top x] at h
  exact h

theorem ltSign_top_top {α : Type*} [LinearOrder α] :
    ltSign (α := WithTop α) none none = 0 := ltSign_self _

/-- The sign of a difference of values of a strictly antitone function compares the
arguments. -/
theorem sign_sub_of_strictAnti {α : Type*} [LinearOrder α] {a : α → ℝ} (ha : StrictAnti a)
    (p q : α) : SignType.sign (a p - a q) = ltSign p q := by
  unfold ltSign
  rcases lt_trichotomy p q with h | rfl | h
  · simp [h, sign_pos (sub_pos.2 (ha h))]
  · simp
  · simp [h, h.not_gt, sign_neg (sub_neg.2 (ha h))]

/-- A comparison principle for functions of three indices: two functions that change sign under
the transpositions of the first two and of the last two arguments, agree on increasing triples
and vanish on triples with a repeated entry are equal. -/
theorem eq_of_antisymm {α : Type*} [LinearOrder α] {F G : α → α → α → SignType}
    (hF₁ : ∀ p q r, F q p r = -F p q r) (hF₂ : ∀ p q r, F p r q = -F p q r)
    (hG₁ : ∀ p q r, G q p r = -G p q r) (hG₂ : ∀ p q r, G p r q = -G p q r)
    (hsort : ∀ p q r, p < q → q < r → F p q r = G p q r)
    (hrep : ∀ p q r, (p = q ∨ q = r ∨ p = r) → F p q r = G p q r) (p q r : α) :
    F p q r = G p q r := by
  by_cases h : p = q ∨ q = r ∨ p = r
  · exact hrep p q r h
  push Not at h
  obtain ⟨hpq, hqr, hpr⟩ := h
  rcases hpq.lt_or_gt with h1 | h1 <;> rcases hqr.lt_or_gt with h2 | h2 <;>
    rcases hpr.lt_or_gt with h3 | h3
  · exact hsort p q r h1 h2
  · exact absurd (h1.trans h2) h3.not_gt
  · rw [← neg_neg (F p q r), ← hF₂, hsort p r q h3 h2, hG₂, neg_neg]
  · rw [← neg_neg (F p q r), ← hF₂, ← neg_neg (F p r q), ← hF₁, hsort r p q h3 h1, hG₁, hG₂,
      neg_neg, neg_neg]
  · rw [← neg_neg (F p q r), ← hF₁, hsort q p r h1 h3, hG₁, neg_neg]
  · rw [← neg_neg (F p q r), ← hF₁, ← neg_neg (F q p r), ← hF₂, hsort q r p h2 h3, hG₂, hG₁,
      neg_neg, neg_neg]
  · exact absurd (h2.trans h1) h3.not_gt
  · rw [← neg_neg (F p q r), ← hF₁, ← neg_neg (F q p r), ← hF₂, ← neg_neg (F q r p), ← hF₁,
      hsort r q p h2 h1, hG₁, hG₂, hG₁, neg_neg, neg_neg, neg_neg]

/-! ### Uniformity -/

theorem tripleSign_comm₁ (p q r : Fin n) : A.tripleSign q p r = A.tripleSign p q r := by
  simp only [tripleSign, min_comm q p, max_comm q p]

theorem tripleSign_of_lt {p q r : Fin n} (h₁ : p < q) (h₂ : q < r) :
    A.tripleSign p q r = SignType.sign (A.crossX q r - A.crossX p q) := by
  simp [tripleSign, min_eq_left h₁.le, max_eq_right h₁.le, min_eq_left h₂.le, max_eq_right h₂.le,
    min_eq_left (h₁.trans h₂).le]

theorem tripleSign_comm₂ (p q r : Fin n) : A.tripleSign p r q = A.tripleSign p q r := by
  have h₁ : min (min p r) q = min (min p q) r := min_right_comm _ _ _
  have h₂ : max (max p r) q = max (max p q) r := max_right_comm _ _ _
  have h₃ : max (min p r) (min (max p r) q) = max (min p q) (min (max p q) r) := by
    rw [Fin.ext_iff]; simp only [Fin.val_max, Fin.val_min]; omega
  simp only [tripleSign, h₁, h₂, h₃]

theorem tupleSign_coe (p q r : Fin n) :
    tupleSign (α := WithTop (Fin n)) ![some p, some q, some r] =
      ltSign p q * ltSign p r * ltSign q r := by
  simp [tupleSign, ltSign_coe]

theorem chiFun_coe (p q r : Fin n) :
    A.chiFun ![some p, some q, some r] =
      ltSign p q * ltSign p r * ltSign q r * A.tripleSign p q r := by
  simp only [chiFun, tupleSign]
  erw [ltSign_coe, ltSign_coe, ltSign_coe]
  rfl

theorem ltSign_ne_zero {α : Type*} [LinearOrder α] {x y : α} (h : x ≠ y) : ltSign x y ≠ 0 := by
  unfold ltSign
  rcases h.lt_or_gt with h | h
  · simp [h]
  · simp [h, h.not_gt]

/-- The arrangement chirotope is uniform exactly when the arrangement is simple. -/
theorem isUniform_chiFun_iff : Chirotope.IsUniform A.chiFun ↔ A.IsSimple := by
  constructor
  · intro hu i j k hij hjk heq
    have hinj : Function.Injective ![some i, some j, some k] := by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp_all [hij.ne, hjk.ne, (hij.trans hjk).ne, hij.ne',
        hjk.ne', (hij.trans hjk).ne']
    apply hu _ hinj
    rw [chiFun_coe, A.tripleSign_of_lt hij hjk, heq, sub_self, sign_zero, mul_zero]
  · intro hs t ht
    have hne : ∀ x y : Fin 3, x ≠ y → t x ≠ t y := fun x y h h' => h (ht h')
    have ht01 := hne 0 1 (by decide)
    have ht02 := hne 0 2 (by decide)
    have ht12 := hne 1 2 (by decide)
    have htuple : tupleSign (α := WithTop (Fin n)) t ≠ 0 := by
      unfold tupleSign
      exact mul_ne_zero (mul_ne_zero (ltSign_ne_zero ht01) (ltSign_ne_zero ht02))
        (ltSign_ne_zero ht12)
    unfold chiFun
    refine mul_ne_zero htuple ?_
    generalize hx : t 0 = x at ht01 ht02
    generalize hy : t 1 = y at ht01 ht12
    generalize hz : t 2 = z at ht02 ht12
    rcases x with _ | p <;> rcases y with _ | q <;> rcases z with _ | r <;>
      try exact one_ne_zero
    have hpq : p ≠ q := fun h => ht01 (h ▸ rfl)
    have hpr : p ≠ r := fun h => ht02 (h ▸ rfl)
    have hqr : q ≠ r := fun h => ht12 (h ▸ rfl)
    change A.tripleSign p q r ≠ 0
    have key : ∀ p q r : Fin n, p < q → q < r → A.tripleSign p q r ≠ 0 := by
      intro p q r h₁ h₂
      rw [A.tripleSign_of_lt h₁ h₂, Ne, sign_eq_zero_iff, sub_eq_zero]
      exact fun h => hs p q r h₁ h₂ h.symm
    rcases hpq.lt_or_gt with h1 | h1 <;> rcases hqr.lt_or_gt with h2 | h2 <;>
      rcases hpr.lt_or_gt with h3 | h3
    · exact key p q r h1 h2
    · exact absurd (h1.trans h2) h3.not_gt
    · rw [← A.tripleSign_comm₂]; exact key p r q h3 h2
    · rw [← A.tripleSign_comm₂, ← A.tripleSign_comm₁]; exact key r p q h3 h1
    · rw [← A.tripleSign_comm₁]; exact key q p r h1 h3
    · rw [← A.tripleSign_comm₁, ← A.tripleSign_comm₂]; exact key q r p h2 h3
    · exact absurd (h2.trans h1) h3.not_gt
    · rw [← A.tripleSign_comm₁, ← A.tripleSign_comm₂, ← A.tripleSign_comm₁]
      exact key r q p h2 h1

/-! ### Arrangements of straight lines -/

/-- The vectors of an arrangement of lines: `(-1, a i, b i)` for the line `y = a i * x + b i`,
and `(0, 0, 1)` for the line at infinity. -/
def lineVectors (a b : Fin n → ℝ) : Option (Fin n) → Fin 3 → ℝ
  | none => ![0, 0, 1]
  | some i => ![-1, a i, b i]

/-- The determinant of the vectors of three lines. -/
theorem det_lineVectors (a b : Fin n → ℝ) (p q r : Fin n) :
    (Matrix.of ![lineVectors a b (some p), lineVectors a b (some q),
      lineVectors a b (some r)]).det =
      -(a q * b r) + a r * b q + a p * b r - a r * b p - a p * b q + a q * b p := by
  simp [lineVectors, Matrix.det_fin_three]
  ring

theorem crossX_ofLines (a b : Fin n → ℝ) (ha : StrictAnti a) {p q : Fin n} (h : p ≠ q) :
    (ofLines a b ha).crossX p q = (b q - b p) / (a p - a q) := by
  simp [ofLines, h]

/-- The vector chirotope of three lines, on an increasing triple, is the sign of the difference
of the crossing abscissae. -/
theorem sign_det_lineVectors_of_lt (a b : Fin n → ℝ) (ha : StrictAnti a) {p q r : Fin n}
    (h₁ : p < q) (h₂ : q < r) :
    SignType.sign (Matrix.of ![lineVectors a b (some p), lineVectors a b (some q),
      lineVectors a b (some r)]).det =
      SignType.sign ((ofLines a b ha).crossX q r - (ofLines a b ha).crossX p q) := by
  have hpq : 0 < a p - a q := sub_pos.2 (ha h₁)
  have hqr : 0 < a q - a r := sub_pos.2 (ha h₂)
  have key : (Matrix.of ![lineVectors a b (some p), lineVectors a b (some q),
      lineVectors a b (some r)]).det = (a p - a q) * (a q - a r) *
        ((ofLines a b ha).crossX q r - (ofLines a b ha).crossX p q) := by
    rw [det_lineVectors, crossX_ofLines a b ha h₂.ne, crossX_ofLines a b ha h₁.ne]
    field_simp
    ring
  rw [key, sign_mul, sign_mul, sign_pos hpq, sign_pos hqr, one_mul, one_mul]

/-- The chirotope of an arrangement of straight lines is the chirotope of its vectors
`(-1, a i, b i)` and `(0, 0, 1)` (equality, not equality up to sign). -/
theorem chiFun_ofLines (a b : Fin n → ℝ) (ha : StrictAnti a) :
    (ofLines a b ha).chiFun = Chirotope.ofVectorsFun (lineVectors a b) := by
  funext t
  have hmat : (Matrix.of fun i j => lineVectors a b (t i) j) =
      Matrix.of ![lineVectors a b (t 0), lineVectors a b (t 1), lineVectors a b (t 2)] := by
    ext i j; fin_cases i <;> rfl
  rw [Chirotope.ofVectorsFun, hmat]
  unfold chiFun tupleSign
  generalize t 0 = x
  generalize t 1 = y
  generalize t 2 = z
  have hz : ∀ M : Matrix (Fin 3) (Fin 3) ℝ, M.det = 0 → SignType.sign M.det = 0 := fun M h => by
    rw [h, sign_zero]
  rcases x with _ | p <;> rcases y with _ | q <;> rcases z with _ | r
  · erw [ltSign_top_top]
    rw [zero_mul, zero_mul, zero_mul, hz]
    simp [lineVectors, Matrix.det_fin_three]
  · erw [ltSign_top_top]
    rw [zero_mul, zero_mul, zero_mul, hz]
    simp [lineVectors, Matrix.det_fin_three]
  · erw [ltSign_top_top]
    rw [mul_zero, zero_mul, zero_mul, hz]
    simp [lineVectors, Matrix.det_fin_three]
  · erw [ltSign_top_coe q]
    erw [ltSign_coe q r]
    change -1 * -1 * ltSign q r * 1 = _
    rw [← sign_sub_of_strictAnti ha]
    simp [lineVectors, Matrix.det_fin_three]
    ring_nf
  · erw [ltSign_top_top]
    rw [mul_zero, zero_mul, hz]
    simp [lineVectors, Matrix.det_fin_three]
  · erw [ltSign_coe_top p]
    erw [ltSign_coe p r]
    erw [ltSign_top_coe r]
    change 1 * ltSign p r * -1 * 1 = _
    rw [← sign_sub_of_strictAnti ha, show (1 : SignType) * SignType.sign (a p - a r) * -1 * 1 =
      SignType.sign (-(a p - a r)) by rw [Left.sign_neg]; simp]
    congr 1
    simp [lineVectors, Matrix.det_fin_three]
    ring
  · erw [ltSign_coe p q]
    erw [ltSign_coe_top p]
    change ltSign p q * 1 * 1 * 1 = _
    rw [← sign_sub_of_strictAnti ha]
    simp only [mul_one]
    congr 1
    simp [lineVectors, Matrix.det_fin_three]
    ring
  · erw [ltSign_coe p q, ltSign_coe p r, ltSign_coe q r]
    change ltSign p q * ltSign p r * ltSign q r * (ofLines a b ha).tripleSign p q r = _
    refine eq_of_antisymm (F := fun p q r => ltSign p q * ltSign p r * ltSign q r *
        (ofLines a b ha).tripleSign p q r)
      (G := fun p q r => SignType.sign (Matrix.of ![lineVectors a b (some p),
        lineVectors a b (some q), lineVectors a b (some r)]).det) ?_ ?_ ?_ ?_ ?_ ?_ p q r
    · intro p q r
      rw [ltSign_swap p q, tripleSign_comm₁, neg_mul, neg_mul, neg_mul]
      congr 1
      ac_rfl
    · intro p q r
      rw [ltSign_swap q r, tripleSign_comm₂, mul_neg, neg_mul]
      congr 1
      ac_rfl
    · intro p q r
      simp only [det_lineVectors, ← Left.sign_neg]
      congr 1
      ring
    · intro p q r
      simp only [det_lineVectors, ← Left.sign_neg]
      congr 1
      ring
    · intro p q r h₁ h₂
      simp only [ltSign_of_lt h₁, ltSign_of_lt h₂, ltSign_of_lt (h₁.trans h₂), one_mul,
        tripleSign_of_lt _ h₁ h₂]
      exact (sign_det_lineVectors_of_lt a b ha h₁ h₂).symm
    · intro p q r h
      have h0 : (Matrix.of ![lineVectors a b (some p), lineVectors a b (some q),
          lineVectors a b (some r)]).det = 0 := by
        rcases h with rfl | rfl | rfl <;> rw [det_lineVectors] <;> ring
      simp only [h0, sign_zero]
      rcases h with rfl | rfl | rfl <;> simp [ltSign_self]

/-- The vectors of at least two lines with distinct slopes span `ℝ³`. -/
theorem span_range_lineVectors (a b : Fin n → ℝ) (ha : StrictAnti a) (hn : 2 ≤ n) :
    Submodule.span ℝ (Set.range (lineVectors a b)) = ⊤ := by
  set i₀ : Fin n := ⟨0, by omega⟩
  set i₁ : Fin n := ⟨1, by omega⟩
  have h01 : i₀ < i₁ := Fin.mk_lt_mk.2 zero_lt_one
  set M := Matrix.of ![lineVectors a b (some i₀), lineVectors a b (some i₁), lineVectors a b none]
  have hM : M.det ≠ 0 := by
    have : M.det = a i₀ - a i₁ := by
      simp [M, lineVectors, Matrix.det_fin_three]
      ring
    rw [this]
    exact (sub_pos.2 (ha h01)).ne'
  rw [eq_top_iff, ← Chirotope.span_rows_eq_top_of_det_ne_zero hM]
  refine Submodule.span_mono ?_
  rintro _ ⟨k, rfl⟩
  fin_cases k
  · exact ⟨some i₀, rfl⟩
  · exact ⟨some i₁, rfl⟩
  · exact ⟨none, rfl⟩

/-- The chirotope function of an arrangement of at least two straight lines is a chirotope. -/
theorem isChirotope_chiFun_ofLines (a b : Fin n → ℝ) (ha : StrictAnti a) (hn : 2 ≤ n) :
    IsChirotope (ofLines a b ha).chiFun := by
  rw [chiFun_ofLines]
  exact Chirotope.isChirotope_ofVectorsFun _ (span_range_lineVectors a b ha hn)

/-- The chirotope function of an arrangement of straight lines is realizable over `ℝ`. -/
theorem isRealizable_chiFun_ofLines (a b : Fin n → ℝ) (ha : StrictAnti a) :
    Chirotope.IsRealizable (ofLines a b ha).chiFun ℝ :=
  ⟨lineVectors a b, chiFun_ofLines a b ha⟩

end MonotoneArrangement

end LeanPool.PseudolineArrangements
