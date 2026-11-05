/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

module

public import LeanPool.IwaniecLinearSieve.PrimeSums.Mertens
import LeanPool.IwaniecLinearSieve.PrimeSums.SummationByParts
import Mathlib.Algebra.Order.Star.Real

/-!
# [I71, Lemma 13] and [I71, Lemma 14]

For `b ≥ 0` monotone on `[B, A]`, `2 ≤ B ≤ A`,
`∑_{B ≤ p ≤ A} b(p)/p = ∫_B^A b(x) / (x log x) dx + O(b(A) exp(-κ √(log B)))`,
and the analogous statement with `b(B)` for `b` antitone.

The proof is Iwaniec's: summation by parts against `S(n)` (in the abstract form
`abs_sum_sub_integral_le`) at the points `B, ⌊B⌋ + 1, …, ⌊A⌋, A`, using `S_asymp`.
-/

@[expose] public section

open Real Finset MeasureTheory intervalIntegral

namespace IwaniecLinearSieve

/-! ### Elementary facts about `log ∘ log` -/
theorem continuousOn_inv_mul_log {u v : ℝ} (hu : 1 < u) :
    ContinuousOn (fun x ↦ (x * log x)⁻¹) (Set.Icc u v) := by
  have hpos : ∀ x ∈ Set.Icc u v, 1 < x := fun x hx ↦ by linarith [hx.1]
  refine ContinuousOn.inv₀ (ContinuousOn.mul continuousOn_id ?_) fun x hx ↦ ?_
  · exact continuousOn_log.mono fun x hx ↦ by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [hpos x hx]
  · have := hpos x hx
    have := log_pos this
    positivity

theorem integral_inv_mul_log {u v : ℝ} (hu : 1 < u) (huv : u ≤ v) :
    ∫ x in u..v, (x * log x)⁻¹ = log (log v) - log (log u) := by
  have hpos : ∀ x ∈ Set.uIcc u v, 1 < x := fun x hx ↦ by
    rw [Set.uIcc_of_le huv] at hx; linarith [hx.1]
  refine integral_eq_sub_of_hasDerivAt (f := fun x ↦ log (log x)) (fun x hx ↦ ?_) ?_
  · have hx := hpos x hx
    have h := (hasDerivAt_log (by linarith : x ≠ 0)).log (log_pos hx).ne'
    convert h using 1
    rw [mul_inv, div_eq_mul_inv]
  · refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le huv]
    exact continuousOn_inv_mul_log hu

theorem log_log_sub_log_log_le {u v : ℝ} (hu : 1 < u) (huv : u ≤ v) :
    log (log v) - log (log u) ≤ (v - u) / (u * log u) := by
  have hu0 : 0 < u := by linarith
  have hlu : 0 < log u := log_pos hu
  have hlv : 0 < log v := log_pos (by linarith)
  have h1 : log (log v) - log (log u) ≤ log v / log u - 1 := by
    rw [← log_div hlv.ne' hlu.ne']
    exact log_le_sub_one_of_pos (div_pos hlv hlu)
  have h2 : log v - log u ≤ v / u - 1 := by
    rw [← log_div (by linarith) hu0.ne']
    exact log_le_sub_one_of_pos (div_pos (by linarith) hu0)
  calc log (log v) - log (log u) ≤ log v / log u - 1 := h1
    _ = (log v - log u) / log u := by field_simp
    _ ≤ (v / u - 1) / log u := by gcongr
    _ = (v - u) / (u * log u) := by field_simp

/-! ### The partition `B, ⌊B⌋ + 1, …, ⌊A⌋, A` of `[B, A]` -/

/-- The points `B = a 0 ≤ ⌊B⌋ + 1 ≤ ⋯ ≤ ⌊A⌋ ≤ A = a (⌊A⌋ - ⌊B⌋ + 1)`. -/
noncomputable def clampPt (B A : ℝ) (j : ℕ) : ℝ := max B (min ((⌊B⌋₊ + j : ℕ) : ℝ) A)

theorem clampPt_mono (B A : ℝ) : Monotone (clampPt B A) := fun i j hij ↦ by
  unfold clampPt
  gcongr

theorem clampPt_zero {B A : ℝ} (hB : 0 ≤ B) : clampPt B A 0 = B := by
  unfold clampPt
  exact max_eq_left ((min_le_left _ _).trans (by simpa using Nat.floor_le hB))

theorem clampPt_last {B A : ℝ} (hBA : B ≤ A) :
    clampPt B A (⌊A⌋₊ - ⌊B⌋₊ + 1) = A := by
  unfold clampPt
  have h : ⌊B⌋₊ + (⌊A⌋₊ - ⌊B⌋₊ + 1) = ⌊A⌋₊ + 1 := by
    have := Nat.floor_le_floor (a := B) hBA; omega
  rw [h, min_eq_right (by push_cast; exact (Nat.lt_floor_add_one A).le), max_eq_right hBA]

theorem le_clampPt (B A : ℝ) (j : ℕ) : B ≤ clampPt B A j := le_max_left _ _

theorem clampPt_le {B A : ℝ} (hBA : B ≤ A) (j : ℕ) : clampPt B A j ≤ A :=
  max_le hBA (min_le_right _ _)

theorem clampPt_succ_le (B A : ℝ) (j : ℕ) : clampPt B A (j + 1) ≤ clampPt B A j + 1 := by
  unfold clampPt
  push_cast
  simp only [max_def, min_def]
  split_ifs <;> linarith

theorem clampPt_eq {B A : ℝ} {j : ℕ} (hj : 1 ≤ j)
    (hjA : ((⌊B⌋₊ + j : ℕ) : ℝ) ≤ A) : clampPt B A j = ((⌊B⌋₊ + j : ℕ) : ℝ) := by
  unfold clampPt
  rw [min_eq_left hjA, max_eq_right]
  have := Nat.lt_floor_add_one B
  have : (1 : ℝ) ≤ j := by exact_mod_cast hj
  push_cast
  linarith

theorem floor_clampPt {B A : ℝ} (hB : 0 ≤ B) (hBA : B ≤ A) (j : ℕ) :
    ⌊clampPt B A j⌋₊ = min (⌊B⌋₊ + j) ⌊A⌋₊ := by
  unfold clampPt
  set k := ⌊B⌋₊ + j with hk
  rcases le_or_gt (k : ℝ) A with hkA | hkA
  · rw [min_eq_left hkA, min_eq_left (Nat.le_floor hkA)]
    rcases le_or_gt B (k : ℝ) with hBk | hBk
    · rw [max_eq_right hBk, Nat.floor_natCast]
    · rw [max_eq_left hBk.le]
      have : k ≤ ⌊B⌋₊ := Nat.le_floor hBk.le
      omega
  · rw [min_eq_right hkA.le, max_eq_right hBA, min_eq_right]
    exact (Nat.cast_lt (α := ℝ)).1 ((Nat.floor_le (hB.trans hBA)).trans_lt hkA) |>.le

/-- `S x` only depends on `⌊x⌋₊`. -/
theorem S_eq_S_floor (x : ℝ) : S x = S (⌊x⌋₊ : ℝ) := by
  rw [S_eq_sum, S_eq_sum, Nat.floor_natCast]

theorem S_succ_sub (k : ℕ) :
    S ((k + 1 : ℕ) : ℝ) - S (k : ℝ) = if (k + 1).Prime then ((k + 1 : ℕ) : ℝ)⁻¹ else 0 := by
  rw [S_eq_sum, S_eq_sum, Nat.floor_natCast, Nat.floor_natCast, sum_range_succ]
  ring

/-- The primes `p` with `B < p ≤ A`. -/
noncomputable def primesIoc (B A : ℝ) : Finset ℕ := {p ∈ Ioc ⌊B⌋₊ ⌊A⌋₊ | p.Prime}

/-- The primes `p` with `B ≤ p ≤ A`. -/
noncomputable def primesIcc (B A : ℝ) : Finset ℕ := {p ∈ Icc ⌈B⌉₊ ⌊A⌋₊ | p.Prime}

/-- The primes `p` with `B < p < A`. -/
noncomputable def primesIoo (B A : ℝ) : Finset ℕ := {p ∈ Ioo ⌊B⌋₊ ⌈A⌉₊ | p.Prime}

theorem le_floor_iff_of_prime {p : ℕ} (hp : p.Prime) {A : ℝ} : p ≤ ⌊A⌋₊ ↔ (p : ℝ) ≤ A := by
  rcases le_or_gt 0 A with hA | hA
  · exact Nat.le_floor_iff hA
  · rw [Nat.floor_of_nonpos hA.le]
    have : (0 : ℝ) < p := by exact_mod_cast hp.pos
    constructor <;> intro h
    · exact absurd h (by have := hp.pos; omega)
    · linarith

theorem floor_lt_iff_of_prime {p : ℕ} (hp : p.Prime) {B : ℝ} : ⌊B⌋₊ < p ↔ B < p := by
  rcases le_or_gt 0 B with hB | hB
  · exact Nat.floor_lt hB
  · rw [Nat.floor_of_nonpos hB.le]
    have : (0 : ℝ) < p := by exact_mod_cast hp.pos
    exact ⟨fun _ ↦ by linarith, fun _ ↦ hp.pos⟩

theorem mem_primesIoc {B A : ℝ} {p : ℕ} : p ∈ primesIoc B A ↔ p.Prime ∧ B < p ∧ (p : ℝ) ≤ A := by
  simp only [primesIoc, mem_filter, mem_Ioc]
  constructor
  · rintro ⟨⟨h1, h2⟩, hp⟩
    exact ⟨hp, (floor_lt_iff_of_prime hp).1 h1, (le_floor_iff_of_prime hp).1 h2⟩
  · rintro ⟨hp, h1, h2⟩
    exact ⟨⟨(floor_lt_iff_of_prime hp).2 h1, (le_floor_iff_of_prime hp).2 h2⟩, hp⟩

theorem mem_primesIcc {B A : ℝ} {p : ℕ} :
    p ∈ primesIcc B A ↔ p.Prime ∧ B ≤ p ∧ (p : ℝ) ≤ A := by
  simp only [primesIcc, mem_filter, mem_Icc, Nat.ceil_le]
  constructor
  · rintro ⟨⟨h1, h2⟩, hp⟩
    exact ⟨hp, h1, (le_floor_iff_of_prime hp).1 h2⟩
  · rintro ⟨hp, h1, h2⟩
    exact ⟨⟨h1, (le_floor_iff_of_prime hp).2 h2⟩, hp⟩

theorem mem_primesIoo {B A : ℝ} {p : ℕ} : p ∈ primesIoo B A ↔ p.Prime ∧ B < p ∧ (p : ℝ) < A := by
  simp only [primesIoo, mem_filter, mem_Ioo, Nat.lt_ceil]
  constructor
  · rintro ⟨⟨h1, h2⟩, hp⟩
    exact ⟨hp, (floor_lt_iff_of_prime hp).1 h1, h2⟩
  · rintro ⟨hp, h1, h2⟩
    exact ⟨⟨(floor_lt_iff_of_prime hp).2 h1, h2⟩, hp⟩

/-- Summation by parts identity: the Stieltjes sum against `S` over the partition `clampPt`
is the sum over primes in `(B, A]`. -/
theorem sum_clampPt_eq (b : ℝ → ℝ) {B A : ℝ} (hB : 0 ≤ B) (hBA : B ≤ A) :
    ∑ j ∈ range (⌊A⌋₊ - ⌊B⌋₊ + 1),
        b (clampPt B A (j + 1)) * (S (clampPt B A (j + 1)) - S (clampPt B A j)) =
      ∑ p ∈ primesIoc B A, b p / p := by
  have hmN : ⌊B⌋₊ ≤ ⌊A⌋₊ := Nat.floor_le_floor hBA
  have hS : ∀ j, S (clampPt B A j) = S ((min (⌊B⌋₊ + j) ⌊A⌋₊ : ℕ) : ℝ) := fun j ↦ by
    rw [S_eq_S_floor, floor_clampPt hB hBA]
  rw [sum_range_succ, hS, hS, show min (⌊B⌋₊ + (⌊A⌋₊ - ⌊B⌋₊ + 1)) ⌊A⌋₊ = ⌊A⌋₊ by omega,
    show min (⌊B⌋₊ + (⌊A⌋₊ - ⌊B⌋₊)) ⌊A⌋₊ = ⌊A⌋₊ by omega, sub_self, mul_zero, add_zero,
    primesIoc, sum_filter, ← Finset.Ico_add_one_add_one_eq_Ioc, sum_Ico_eq_sum_range,
    show ⌊A⌋₊ + 1 - (⌊B⌋₊ + 1) = ⌊A⌋₊ - ⌊B⌋₊ by omega]
  refine sum_congr rfl fun j hj ↦ ?_
  have hj : j < ⌊A⌋₊ - ⌊B⌋₊ := mem_range.1 hj
  have hc : clampPt B A (j + 1) = ((⌊B⌋₊ + (j + 1) : ℕ) : ℝ) := by
    refine clampPt_eq (by omega) ?_
    exact (Nat.le_floor_iff (hB.trans hBA)).1 (by omega)
  rw [hS, hS, min_eq_left (by omega), min_eq_left (by omega), hc,
    show ⌊B⌋₊ + (j + 1) = ⌊B⌋₊ + j + 1 by ring, S_succ_sub,
    show ⌊B⌋₊ + 1 + j = ⌊B⌋₊ + j + 1 by ring]
  split_ifs <;> simp [div_eq_mul_inv]

theorem S_asymp_nonneg : ∃ c₅ C : ℝ, 0 ≤ C ∧ ∀ x ≥ 2, |S x - log (log x) - c₅| ≤ C * pntE x := by
  obtain ⟨c₅, C, hC⟩ := S_asymp
  refine ⟨c₅, C, ?_, hC⟩
  exact nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hC 2 le_rfl)) (pntE_pos 2)

/-! ### Lemma 13 -/

/-- [I71, Lemma 13] for the primes in `(B, A]`. -/
theorem lemma13_Ioc : ∃ C, 0 ≤ C ∧ ∀ (b : ℝ → ℝ) (A B : ℝ), 2 ≤ B → B ≤ A →
    MonotoneOn b (Set.Icc B A) → (∀ x ∈ Set.Icc B A, 0 ≤ b x) →
    |∑ p ∈ primesIoc B A, b p / p - ∫ x in B..A, b x / (x * log x)| ≤ C * b A * pntE B := by
  obtain ⟨c₅, C, hC0, hC⟩ := S_asymp_nonneg
  refine ⟨2 + 2 * C, by linarith, fun b A B hB hBA hb hb0 ↦ ?_⟩
  set n := ⌊A⌋₊ - ⌊B⌋₊ + 1
  have h0 : clampPt B A 0 = B := clampPt_zero (by linarith)
  have hn : clampPt B A n = A := clampPt_last hBA
  have h2 : ∀ j, 2 ≤ clampPt B A j := fun j ↦ hB.trans (le_clampPt B A j)
  have hE : ∀ j, pntE (clampPt B A j) ≤ pntE B := fun j ↦
    pntE_le_pntE (by linarith) (le_clampPt B A j)
  have hFf : ∀ j < n, ∫ x in clampPt B A j..clampPt B A (j + 1), (x * log x)⁻¹ =
      (log (log (clampPt B A (j + 1))) + c₅) - (log (log (clampPt B A j)) + c₅) := by
    intro j _
    rw [integral_inv_mul_log (by linarith [h2 j]) (clampPt_mono B A (Nat.le_succ j))]
    ring
  have hδ : ∀ j < n, (log (log (clampPt B A (j + 1))) + c₅) - (log (log (clampPt B A j)) + c₅) ≤
      2 * pntE B := by
    intro j _
    have hj := h2 j
    have hlog : 0 < log (clampPt B A j) := log_pos (by linarith)
    calc _ = log (log (clampPt B A (j + 1))) - log (log (clampPt B A j)) := by ring
      _ ≤ (clampPt B A (j + 1) - clampPt B A j) / (clampPt B A j * log (clampPt B A j)) :=
          log_log_sub_log_log_le (by linarith) (clampPt_mono B A (Nat.le_succ j))
      _ ≤ 1 / (clampPt B A j * log (clampPt B A j)) := by
          gcongr
          linarith [clampPt_succ_le B A j]
      _ ≤ 2 * pntE (clampPt B A j) := one_div_mul_log_le_pntE hj
      _ ≤ 2 * pntE B := by linarith [hE j]
  have hε : ∀ j ≤ n, |S (clampPt B A j) - (log (log (clampPt B A j)) + c₅)| ≤ C * pntE B := by
    intro j _
    rw [← sub_sub]
    exact (hC _ (h2 j)).trans (mul_le_mul_of_nonneg_left (hE j) hC0)
  have key := abs_sum_sub_integral_le (n := n) (a := clampPt B A) (clampPt_mono B A)
    (b := b) (f := fun x ↦ (x * log x)⁻¹) (F := fun x ↦ log (log x) + c₅)
    (g := fun j ↦ S (clampPt B A j)) (by linarith [pntE_pos B]) (by rw [h0, hn]; exact hb)
    (by rw [h0]; exact hb0 B ⟨le_rfl, hBA⟩)
    (by
      rw [h0, hn]
      intro x hx
      have : 0 < log x := log_pos (by linarith [hx.1])
      have : 0 < x := by linarith [hx.1]
      positivity)
    (by rw [h0, hn]; exact continuousOn_inv_mul_log (by linarith)) hFf hδ hε
  rw [h0, hn, sum_clampPt_eq b (by linarith) hBA] at key
  simp_rw [div_eq_mul_inv (b _)]
  calc _ ≤ (2 * pntE B + 2 * (C * pntE B)) * b A := key
    _ = (2 + 2 * C) * b A * pntE B := by ring

theorem sum_of_forall_cast_eq {t : Finset ℕ} {v : ℝ} (h : ∀ p ∈ t, (p : ℝ) = v) (φ : ℝ → ℝ)
    (hφ : 0 ≤ φ v) : 0 ≤ ∑ p ∈ t, φ p ∧ ∑ p ∈ t, φ p ≤ φ v := by
  have hcard : t.card ≤ 1 := card_le_one.2 fun a ha b hb ↦ by
    exact_mod_cast (h a ha).trans (h b hb).symm
  have hcard' : (t.card : ℝ) ≤ 1 := by exact_mod_cast hcard
  rw [sum_congr rfl fun p hp ↦ by rw [h p hp], sum_const, nsmul_eq_mul]
  exact ⟨by positivity, by nlinarith⟩

/-- [I71, Lemma 13], increasing case, for any set of primes between those in `(B, A)` and
those in `[B, A]`. -/
theorem lemma13_mono_of_subset : ∃ C, 0 ≤ C ∧ ∀ (b : ℝ → ℝ) (A B : ℝ) (s : Finset ℕ), 2 ≤ B →
    B ≤ A → MonotoneOn b (Set.Icc B A) → (∀ x ∈ Set.Icc B A, 0 ≤ b x) →
    (∀ p ∈ s, p.Prime ∧ B ≤ p ∧ (p : ℝ) ≤ A) → (∀ p : ℕ, p.Prime → B < p → (p : ℝ) < A → p ∈ s) →
    |∑ p ∈ s, b p / p - ∫ x in B..A, b x / (x * log x)| ≤ C * b A * pntE B := by
  obtain ⟨C, hC0, hC⟩ := lemma13_Ioc
  refine ⟨C + 1, by linarith, fun b A B s hB hBA hb hb0 hs1 hs2 ↦ ?_⟩
  have hB0 : 0 < B := by linarith
  have hbA : 0 ≤ b A := hb0 A ⟨hBA, le_rfl⟩
  have hbB : 0 ≤ b B := hb0 B ⟨le_rfl, hBA⟩
  have hbBA : b B ≤ b A := hb ⟨le_rfl, hBA⟩ ⟨hBA, le_rfl⟩ hBA
  have h1 := sum_of_forall_cast_eq (t := s \ primesIoc B A) (v := B) (fun p hp ↦ by
      rw [Finset.mem_sdiff, mem_primesIoc] at hp
      obtain ⟨hp1, hp2⟩ := hp
      obtain ⟨hpp, hBp, hpA⟩ := hs1 p hp1
      exact le_antisymm (not_lt.1 fun h ↦ hp2 ⟨hpp, h, hpA⟩) hBp)
    (fun x ↦ b x / x) (div_nonneg hbB hB0.le)
  have h2 := sum_of_forall_cast_eq (t := primesIoc B A \ s) (v := A) (fun p hp ↦ by
      rw [Finset.mem_sdiff, mem_primesIoc] at hp
      obtain ⟨⟨hpp, hBp, hpA⟩, hp2⟩ := hp
      exact le_antisymm hpA (not_lt.1 fun h ↦ hp2 (hs2 p hpp hBp h)))
    (fun x ↦ b x / x) (div_nonneg hbA (by linarith))
  have h3 : b B / B ≤ b A * pntE B := by
    calc b B / B ≤ b A / B := by gcongr
      _ = b A * B⁻¹ := div_eq_mul_inv _ _
      _ ≤ b A * pntE B := mul_le_mul_of_nonneg_left (inv_le_pntE hB) hbA
  have h4 : b A / A ≤ b A * pntE B := by
    calc b A / A ≤ b A / B := by gcongr
      _ = b A * B⁻¹ := div_eq_mul_inv _ _
      _ ≤ b A * pntE B := mul_le_mul_of_nonneg_left (inv_le_pntE hB) hbA
  have hdiff := sum_sdiff_sub_sum_sdiff (s₁ := primesIoc B A) (s₂ := s) (f := fun p : ℕ ↦ b p / p)
  have hI := hC b A B hB hBA hb hb0
  rw [abs_le] at hI ⊢
  constructor <;> nlinarith [pntE_pos B]

/-- [I71, Lemma 13]: for `b ≥ 0` increasing on `[B, A]`, `2 ≤ B ≤ A`,
`|∑_{B ≤ p ≤ A} b(p)/p - ∫_B^A b(x)/(x log x) dx| ≤ C b(A) exp(-κ √(log B))`. -/
theorem lemma13_mono : ∃ C, ∀ (b : ℝ → ℝ) (A B : ℝ), 2 ≤ B → B ≤ A →
    MonotoneOn b (Set.Icc B A) → (∀ x ∈ Set.Icc B A, 0 ≤ b x) →
    |∑ p ∈ primesIcc B A, b p / p - ∫ x in B..A, b x / (x * log x)| ≤ C * b A * pntE B := by
  obtain ⟨C, -, hC⟩ := lemma13_mono_of_subset
  exact ⟨C, fun b A B hB hBA hb hb0 ↦ hC b A B _ hB hBA hb hb0 (fun p hp ↦ mem_primesIcc.1 hp)
    fun p hp h1 h2 ↦ mem_primesIcc.2 ⟨hp, h1.le, h2.le⟩⟩

theorem intervalIntegrable_div_mul_log {b : ℝ → ℝ} {A B : ℝ} (hB : 1 < B) (hBA : B ≤ A)
    (hb : MonotoneOn b (Set.Icc B A) ∨ AntitoneOn b (Set.Icc B A)) :
    IntervalIntegrable (fun x ↦ b x / (x * log x)) volume B A := by
  simp_rw [div_eq_mul_inv (b _)]
  have hc := continuousOn_inv_mul_log (v := A) hB
  rw [← Set.uIcc_of_le hBA] at hc hb
  rcases hb with hb | hb
  · exact hb.intervalIntegrable.mul_continuousOn hc
  · exact hb.intervalIntegrable.mul_continuousOn hc

/-- [I71, Lemma 13], decreasing case, for any set of primes between those in `(B, A)` and
those in `[B, A]`. -/
theorem lemma13_anti_of_subset : ∃ C, 0 ≤ C ∧ ∀ (b : ℝ → ℝ) (A B : ℝ) (s : Finset ℕ), 2 ≤ B →
    B ≤ A → AntitoneOn b (Set.Icc B A) → (∀ x ∈ Set.Icc B A, 0 ≤ b x) →
    (∀ p ∈ s, p.Prime ∧ B ≤ p ∧ (p : ℝ) ≤ A) → (∀ p : ℕ, p.Prime → B < p → (p : ℝ) < A → p ∈ s) →
    |∑ p ∈ s, b p / p - ∫ x in B..A, b x / (x * log x)| ≤ C * b B * pntE B := by
  obtain ⟨C, hC0, hC⟩ := lemma13_mono_of_subset
  refine ⟨2 * C, by linarith, fun b A B s hB hBA hb hb0 hs1 hs2 ↦ ?_⟩
  set c := b B
  have hc : 0 ≤ c := hb0 B ⟨le_rfl, hBA⟩
  have hbA : 0 ≤ b A := hb0 A ⟨hBA, le_rfl⟩
  have hbA' : b A ≤ c := hb ⟨le_rfl, hBA⟩ ⟨hBA, le_rfl⟩ hBA
  have hb' : MonotoneOn (fun x ↦ c - b x) (Set.Icc B A) := fun x hx y hy hxy ↦ by
    simp only; linarith [hb hx hy hxy]
  have hb'0 : ∀ x ∈ Set.Icc B A, 0 ≤ c - b x := fun x hx ↦ by
    simp only [c]; linarith [hb ⟨le_rfl, hBA⟩ hx hx.1]
  have e1 := hC (fun _ ↦ c) A B s hB hBA (fun _ _ _ _ _ ↦ le_rfl) (fun _ _ ↦ hc) hs1 hs2
  have e2 := hC (fun x ↦ c - b x) A B s hB hBA hb' hb'0 hs1 hs2
  have hsum : ∑ p ∈ s, b p / p = ∑ p ∈ s, c / p - ∑ p ∈ s, (c - b p) / p := by
    rw [← sum_sub_distrib]; exact sum_congr rfl fun p _ ↦ by ring
  have hint : ∫ x in B..A, b x / (x * log x) =
      (∫ x in B..A, c / (x * log x)) - ∫ x in B..A, (c - b x) / (x * log x) := by
    rw [← integral_sub (intervalIntegrable_div_mul_log (by linarith) hBA
      (Or.inl fun _ _ _ _ _ ↦ le_rfl)) (intervalIntegrable_div_mul_log (by linarith) hBA
      (Or.inl hb'))]
    exact integral_congr fun x _ ↦ by ring
  rw [hsum, hint]
  have h5 : 0 ≤ C * b A * pntE B := mul_nonneg (mul_nonneg hC0 hbA) (pntE_pos B).le
  rw [abs_le] at e1 e2 ⊢
  constructor <;> linarith

/-- [I71, Lemma 13], decreasing case: for `b ≥ 0` decreasing on `[B, A]`, `2 ≤ B ≤ A`,
`|∑_{B ≤ p ≤ A} b(p)/p - ∫_B^A b(x)/(x log x) dx| ≤ C b(B) exp(-κ √(log B))`. -/
theorem lemma13_anti : ∃ C, ∀ (b : ℝ → ℝ) (A B : ℝ), 2 ≤ B → B ≤ A →
    AntitoneOn b (Set.Icc B A) → (∀ x ∈ Set.Icc B A, 0 ≤ b x) →
    |∑ p ∈ primesIcc B A, b p / p - ∫ x in B..A, b x / (x * log x)| ≤ C * b B * pntE B := by
  obtain ⟨C, -, hC⟩ := lemma13_anti_of_subset
  exact ⟨C, fun b A B hB hBA hb hb0 ↦ hC b A B _ hB hBA hb hb0 (fun p hp ↦ mem_primesIcc.1 hp)
    fun p hp h1 h2 ↦ mem_primesIcc.2 ⟨hp, h1.le, h2.le⟩⟩

/-! ### Lemma 14 -/
theorem integral_inv_log_div_mul_log {u v : ℝ} (hu : 1 < u) (huv : u ≤ v) :
    ∫ x in u..v, (log x)⁻¹ / (x * log x) = 1 / log u - 1 / log v := by
  have hpos : ∀ x ∈ Set.uIcc u v, 1 < x := fun x hx ↦ by
    rw [Set.uIcc_of_le huv] at hx; linarith [hx.1]
  have hderiv : ∀ x ∈ Set.uIcc u v,
      HasDerivAt (fun x ↦ -(log x)⁻¹) ((log x)⁻¹ / (x * log x)) x := fun x hx ↦ by
    have hx := hpos x hx
    have hl := (log_pos hx).ne'
    convert ((hasDerivAt_log (by linarith : x ≠ 0)).inv hl).neg using 1
    field_simp
  have hint : IntervalIntegrable (fun x ↦ (log x)⁻¹ / (x * log x)) volume u v := by
    have hc := continuousOn_inv_mul_log (v := v) hu
    have hl : ContinuousOn (fun x ↦ (log x)⁻¹) (Set.Icc u v) :=
      ContinuousOn.inv₀ (continuousOn_log.mono fun x hx ↦ by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [hx.1])
        fun x hx ↦ (log_pos (by linarith [hx.1])).ne'
    simp_rw [div_eq_mul_inv ((log _)⁻¹)]
    exact (hl.mul hc).intervalIntegrable_of_Icc huv
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  ring

/-- [I71, Lemma 14]: `∑_{B < p < A} 1/(p log p) = 1/log B - 1/log A + O(exp(-κ √(log B)))`,
for any set of primes between those in `(B, A)` and those in `[B, A]`. -/
theorem lemma14_of_subset : ∃ C, ∀ (A B : ℝ) (s : Finset ℕ), 2 ≤ B → B ≤ A →
    (∀ p ∈ s, p.Prime ∧ B ≤ p ∧ (p : ℝ) ≤ A) → (∀ p : ℕ, p.Prime → B < p → (p : ℝ) < A → p ∈ s) →
    |∑ p ∈ s, 1 / (p * log p) - (1 / log B - 1 / log A)| ≤ C * pntE B := by
  obtain ⟨C, hC0, hC⟩ := lemma13_anti_of_subset
  refine ⟨2 * C, fun A B s hB hBA hs1 hs2 ↦ ?_⟩
  have hlogB : 1 / 2 ≤ log B := half_le_log hB
  have hb : AntitoneOn (fun x ↦ (log x)⁻¹) (Set.Icc B A) := fun x hx y hy hxy ↦ by
    have hx0 : 0 < log x := log_pos (by linarith [hx.1])
    exact inv_anti₀ hx0 (log_le_log (by linarith [hx.1]) hxy)
  have hb0 : ∀ x ∈ Set.Icc B A, 0 ≤ (log x)⁻¹ := fun x hx ↦
    inv_nonneg.2 (log_nonneg (by linarith [hx.1]))
  have h := hC _ A B s hB hBA hb hb0 hs1 hs2
  rw [integral_inv_log_div_mul_log (by linarith) hBA] at h
  have hsum : ∑ p ∈ s, (log (p : ℝ))⁻¹ / p = ∑ p ∈ s, 1 / (p * log p) :=
    sum_congr rfl fun p _ ↦ by ring
  rw [hsum] at h
  refine h.trans ?_
  have hinv : (log B)⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
  have := pntE_pos B
  calc C * (log B)⁻¹ * pntE B ≤ C * 2 * pntE B := by gcongr
    _ = 2 * C * pntE B := by ring

/-- [I71, Lemma 14]: `∑_{B < p < A} 1/(p log p) = 1/log B - 1/log A + O(exp(-κ √(log B)))`. -/
theorem lemma14 : ∃ C, ∀ A B : ℝ, 2 ≤ B → B ≤ A →
    |∑ p ∈ primesIoo B A, 1 / (p * log p) - (1 / log B - 1 / log A)| ≤ C * pntE B := by
  obtain ⟨C, hC⟩ := lemma14_of_subset
  exact ⟨C, fun A B hB hBA ↦ hC A B _ hB hBA
    (fun p hp ↦ by
      obtain ⟨h1, h2, h3⟩ := mem_primesIoo.1 hp
      exact ⟨h1, h2.le, h3.le⟩)
    fun p hp h1 h2 ↦ mem_primesIoo.2 ⟨hp, h1, h2⟩⟩

end IwaniecLinearSieve
