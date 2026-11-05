/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

/- Adapted for Lean Pool from roos-j/lean-trilinearht at
7b4209609e6a7fb9d9935973ee8541495f943660. Imports, names, proof organization and
Mathlib interfaces have been updated; original authorship is retained above. -/

public import LeanPool.TrilinearHilbertTransform.Auto.Sec153FiniteSparseCountLemma.CombinationBound

/-!
# Trilinear Hilbert transform: sparse_count_explicit
-/

@[expose] public section

section
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

open scoped Classical in
private def SparseCountExplicitFGapStatement : Prop :=
  ∀ (d : ℕ)
    (ζ : Fin d → ℝ)
    (B : ℝ)
    (Sg : ℝ)
    (Q : ℝ)
    (μ : ℝ)
    (ν : ℝ)
    (R₀ : ℝ)
    (_ : (1 : ℝ) ≤ B)
    (_ : (0 : ℝ) < μ)
    (_ : μ ≤ (1 : ℝ))
    (_ : (1 : ℝ) ≤ ν)
    (S : Finset ℤ)
    (E : ℤ → Finset (Fin (4 : ℕ) → ℝ))
    (_ : ∀ s ∈ S, (E s).Nonempty → ∀ (n : Fin d → ℤ), (∀ (k : Fin d), |(↑(n k) : ℝ)| ≤ Q) →
      |∑ k : Fin d, (↑(n k) : ℝ) * ζ k| ∉ Set.Icc (μ * (R₀ * (2 : ℝ) ^ s) / (1000 : ℝ))
      ((1000 : ℝ) * ν * (R₀ * (2 : ℝ) ^ s)))
    (hSne : S.Nonempty),
  let R : ℤ → ℝ :=
    fun (s : ℤ) => R₀ * (2 : ℝ) ^ s
  ∀ (_ : ∀ (s : ℤ), (0 : ℝ) < R s),
  let Rmin : ℝ :=
    R (S.min' hSne)
  let K : ℝ :=
    (27 : ℝ) + (↑d : ℝ) * Q + (18 : ℝ) * (↑d : ℝ) * B
  let h : ℝ :=
    min (Sg * Rmin / ((12 : ℝ) + (↑d : ℝ) * Q)) (μ * Rmin / ((1000 : ℝ) * K))
  ∀ (_ : (0 : ℝ) < h),
  let rd : (Fin (4 : ℕ) → ℝ) → Fin (4 : ℕ) → ℤ :=
    fun (x : Fin (4 : ℕ) → ℝ) (i : Fin (4 : ℕ)) => gridLabel h (x i)
  let E' : ℤ → Finset (Fin (4 : ℕ) → ℤ) :=
    fun (s : ℤ) => Finset.image rd (E s)
  let ζ' : Fin d → ℤ :=
    fun (k : Fin d) => round (ζ k / h)
  ∀ (_ : ∀ (s : ℤ), ∀ x' ∈ E' s, ∃ x ∈ E s, rd x = x')
    (_ : ∀ (s : ℤ), R₀ / h * (2 : ℝ) ^ s = R s / h)
    (_ : ∀ s ∈ S, h * ((1000 : ℝ) * K) ≤ μ * R s),
  ∀ s ∈ S, (E' s).Nonempty → ∀ (n : Fin d → ℤ), (∀ (r : Fin d), |(↑(n r) : ℝ)| ≤ Q) →
    ¬(μ / (2 : ℝ) * (R₀ / h * (2 : ℝ) ^ s) / (50 : ℝ) ≤ |(↑(shiftDot n ζ') : ℝ)| ∧
    |(↑(shiftDot n ζ') : ℝ)| ≤ (50 : ℝ) * ((2 : ℝ) * ν) * (R₀ / h * (2 : ℝ) ^ s))


open scoped Classical in
private def SparseCountExplicitFSepStatement : Prop :=
  ∀ (d : ℕ)
    (ζ : Fin d → ℝ)
    (core : Finset (Fin (4 : ℕ)))
    (B : ℝ)
    (Sg : ℝ)
    (Q : ℝ)
    (μ : ℝ)
    (R₀ : ℝ)
    (S : Finset ℤ)
    (E : ℤ → Finset (Fin (4 : ℕ) → ℝ))
    (_ : ∀ i ∈ core, ∀ s ∈ S, ∀ s' ∈ S, ∀ x ∈ E s, ∀ x' ∈ E s', x i ≠ x' i → ∀ (n : Fin d →
      ℤ), (∀ (k : Fin d), |(↑(n k) : ℝ)| ≤ Q) → Sg * max (R₀ * (2 : ℝ) ^ s) (R₀ * (2 :
      ℝ) ^ s') < |x i - x' i + ∑ k : Fin d, (↑(n k) : ℝ) * ζ k|)
    (_ : (0 : ℝ) < Sg)
    (hSne : S.Nonempty),
  let R : ℤ → ℝ :=
    fun (s : ℤ) => R₀ * (2 : ℝ) ^ s
  let Rmin : ℝ :=
    R (S.min' hSne)
  ∀ (_ : ∀ s ∈ S, Rmin ≤ R s),
  let K : ℝ :=
    (27 : ℝ) + (↑d : ℝ) * Q + (18 : ℝ) * (↑d : ℝ) * B
  let h : ℝ :=
    min (Sg * Rmin / ((12 : ℝ) + (↑d : ℝ) * Q)) (μ * Rmin / ((1000 : ℝ) * K))
  ∀ (_ : (0 : ℝ) < h)
    (_ : h * ((12 : ℝ) + (↑d : ℝ) * Q) ≤ Sg * Rmin),
  let rd : (Fin (4 : ℕ) → ℝ) → Fin (4 : ℕ) → ℤ :=
    fun (x : Fin (4 : ℕ) → ℝ) (i : Fin (4 : ℕ)) => gridLabel h (x i)
  let E' : ℤ → Finset (Fin (4 : ℕ) → ℤ) :=
    fun (s : ℤ) => Finset.image rd (E s)
  let ζ' : Fin d → ℤ :=
    fun (k : Fin d) => round (ζ k / h)
  ∀ (_ : ∀ (s : ℤ), ∀ x' ∈ E' s, ∃ x ∈ E s, rd x = x')
    (_ : ∀ (s : ℤ), R₀ / h * (2 : ℝ) ^ s = R s / h),
  ∀ i ∈ core, ∀ s ∈ S, ∀ s' ∈ S, ∀ x ∈ E' s, ∀ x' ∈ E' s', x i ≠ x' i → ∀ (n : Fin d →
    ℤ), (∀ (r : Fin d), |(↑(n r) : ℝ)| ≤ Q) → Sg / (2 : ℝ) * max (R₀ / h * (2 : ℝ) ^
    s) (R₀ / h * (2 : ℝ) ^ s') < |(↑(x i - x' i + shiftDot n ζ') : ℝ)|


open scoped Classical in
private def SparseCountExplicitHresStatement : Prop :=
  ∀ (d : ℕ)
    (ζ : Fin d → ℝ)
    (B : ℝ)
    (Sg : ℝ)
    (Q : ℝ)
    (μ : ℝ)
    (R₀ : ℝ)
    (_ : (1 : ℝ) ≤ B)
    (_ : (0 : ℝ) < μ)
    (_ : (0 : ℝ) < R₀)
    (S : Finset ℤ)
    (_ : (0 : ℝ) ≤ Q)
    (_ : (0 : ℝ) < Sg)
    (hSne : S.Nonempty),
  let R : ℤ → ℝ :=
    fun (s : ℤ) => R₀ * (2 : ℝ) ^ s
  let Rmin : ℝ :=
    R (S.min' hSne)
  let K : ℝ :=
    (27 : ℝ) + (↑d : ℝ) * Q + (18 : ℝ) * (↑d : ℝ) * B
  let h : ℝ :=
    min (Sg * Rmin / ((12 : ℝ) + (↑d : ℝ) * Q)) (μ * Rmin / ((1000 : ℝ) * K))
  ∀ (_ : (0 : ℝ) < h),
  let rd : (Fin (4 : ℕ) → ℝ) → Fin (4 : ℕ) → ℤ :=
    fun (x : Fin (4 : ℕ) → ℝ) (i : Fin (4 : ℕ)) => gridLabel h (x i)
  let ζ' : Fin d → ℤ :=
    fun (k : Fin d) => round (ζ k / h)
  ∀ (T : Finset (Fin (4 : ℕ))) (l : Fin (4 : ℕ)), T.card = (3 : ℕ) → (∀ i ∈ T, i ≠ l)
    → ∀ (x : Fin (4 : ℕ) → ℝ) (n : Fin d → ℤ), (∀ (k : Fin d), |(↑(n k) : ℝ)| ≤ B) →
    |h * (↑(∑ i ∈ T, roleCoeff i l * rd x i + (36 : ℤ) * shiftDot n ζ') : ℝ) - (∑ i ∈
    T, (↑(roleCoeff i l) : ℝ) * x i + (36 : ℝ) * ∑ k : Fin d, (↑(n k) : ℝ) * ζ k)| ≤ h
    * K


open scoped Classical in
private def SparseCountExplicitStage1Statement : Prop :=
  ∀ (d : ℕ)
    (ζ : Fin d → ℝ)
    (core : Finset (Fin (4 : ℕ)))
    (_ : core.card = (3 : ℕ) ∨ core.card = (4 : ℕ))
    (A : Fin (4 : ℕ) → Finset ℝ)
    (M : ℝ)
    (L : ℝ)
    (_ : (1 : ℝ) ≤ M)
    (_ : (1 : ℝ) ≤ L)
    (_ : ∀ i ∈ core, (↑(A i).card : ℝ) ≤ M)
    (B : ℝ)
    (Sg : ℝ)
    (Q : ℝ)
    (μ : ℝ)
    (ν : ℝ)
    (R₀ : ℝ)
    (_ : (1 : ℝ) ≤ B)
    (_ : (0 : ℝ) < μ)
    (_ : μ ≤ (1 : ℝ))
    (_ : (1 : ℝ) ≤ ν)
    (_ : (0 : ℝ) < R₀)
    (S : Finset ℤ)
    (E : ℤ → Finset (Fin (4 : ℕ) → ℝ))
    (_ : ∀ s ∈ S, ∀ x ∈ E s, (∀ i ∈ core, x i ∈ A i) ∧ ∀ i ∉ core, x i = (0 : ℝ))
    (_ : ∀ i ∈ core, ∀ j ∈ core, i ≠ j → ∀ s ∈ S, ∀ s' ∈ S, ∀ x ∈ E s, ∀ x' ∈ E s', x i = x'
      i → x j = x' j → x = x')
    (_ : ∀ (x : Fin (4 : ℕ) → ℝ), (↑(Finset.card ({s ∈ S | x ∈ E s})) : ℝ) ≤ L)
    (_ : ∀ i ∈ core, ∀ s ∈ S, ∀ s' ∈ S, ∀ x ∈ E s, ∀ x' ∈ E s', x i ≠ x' i → ∀ (n : Fin d →
      ℤ), (∀ (k : Fin d), |(↑(n k) : ℝ)| ≤ Q) → Sg * max (R₀ * (2 : ℝ) ^ s) (R₀ * (2 :
      ℝ) ^ s') < |x i - x' i + ∑ k : Fin d, (↑(n k) : ℝ) * ζ k|)
    (_ : ∀ T ⊆ core, T.card = (3 : ℕ) → ∀ l ∉ T, ∀ s ∈ S, ∀ x ∈ E s, ∃ (n : Fin d → ℤ), (∀ (k
      : Fin d), |(↑(n k) : ℝ)| ≤ B) ∧ μ * (R₀ * (2 : ℝ) ^ s) ≤ |∑ i ∈ T, (↑(roleCoeff i
      l) : ℝ) * x i + (36 : ℝ) * ∑ k : Fin d, (↑(n k) : ℝ) * ζ k| ∧ |∑ i ∈ T,
      (↑(roleCoeff i l) : ℝ) * x i + (36 : ℝ) * ∑ k : Fin d, (↑(n k) : ℝ) * ζ k| ≤ ν *
      (R₀ * (2 : ℝ) ^ s))
    (_ : ∀ s ∈ S, (E s).Nonempty → ∀ (n : Fin d → ℤ), (∀ (k : Fin d), |(↑(n k) : ℝ)| ≤ Q) →
      |∑ k : Fin d, (↑(n k) : ℝ) * ζ k| ∉ Set.Icc (μ * (R₀ * (2 : ℝ) ^ s) / (1000 : ℝ))
      ((1000 : ℝ) * ν * (R₀ * (2 : ℝ) ^ s)))
    (_ : (7200000 : ℝ) * ((↑d : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * B ≤ Q)
    (_ : (7200000 : ℝ) * ((↑d : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * ν ≤ Sg)
    (δ : ℝ)
    (_ : (0 : ℝ) < δ)
    (_ : δ ≤ (1 : ℝ))
    (_ : (0 : ℝ) ≤ Q)
    (_ : (0 : ℝ) < Sg)
    (hSne : S.Nonempty),
  let R : ℤ → ℝ :=
    fun (s : ℤ) => R₀ * (2 : ℝ) ^ s
  ∀ (_ : ∀ (s : ℤ), (0 : ℝ) < R s),
  let Rmin : ℝ :=
    R (S.min' hSne)
  ∀ (_ : ∀ s ∈ S, Rmin ≤ R s),
  let K : ℝ :=
    (27 : ℝ) + (↑d : ℝ) * Q + (18 : ℝ) * (↑d : ℝ) * B
  ∀ (_ : (27 : ℝ) ≤ K),
  let h : ℝ :=
    min (Sg * Rmin / ((12 : ℝ) + (↑d : ℝ) * Q)) (μ * Rmin / ((1000 : ℝ) * K))
  ∀ (_ : (0 : ℝ) < h)
    (_ : h * ((12 : ℝ) + (↑d : ℝ) * Q) ≤ Sg * Rmin)
    (_ : h * ((1000 : ℝ) * K) ≤ μ * Rmin)
    (_ : ∀ i ∈ core, ∀ s ∈ S, ∀ s' ∈ S, ∀ x ∈ E s, ∀ x' ∈ E s', gridLabel h (x i) = gridLabel
      h (x' i) → x i = x' i),
  let rd : (Fin (4 : ℕ) → ℝ) → Fin (4 : ℕ) → ℤ :=
    fun (x : Fin (4 : ℕ) → ℝ) (i : Fin (4 : ℕ)) => gridLabel h (x i)
  ∀ (_ : ∀ s ∈ S, ∀ s' ∈ S, ∀ x ∈ E s, ∀ x' ∈ E s', rd x = rd x' → x = x'),
  let E' : ℤ → Finset (Fin (4 : ℕ) → ℤ) :=
    fun (s : ℤ) => Finset.image rd (E s)
  let ζ' : Fin d → ℤ :=
    fun (k : Fin d) => round (ζ k / h)
  ∀ (_ : ∀ s ∈ S, (E' s).card = (E s).card)
    (_ : ∀ (s : ℤ), ∀ x' ∈ E' s, ∃ x ∈ E s, rd x = x')
    (w : ℤ → ℝ)
    (_ : ∀ (s : ℤ), (0 : ℝ) ≤ w s)
    (_ : ∑ s ∈ S, w s ≤ M)
    (_ : core.card = (3 : ℕ) → ∀ s ∈ S, ∀ i ∈ core, ∀ (a : ℝ), (↑(Finset.card ({x ∈ E s | x i
      = a})) : ℝ) ≤ w s)
    (_ : ∀ (T : Finset (Fin (4 : ℕ))) (l : Fin (4 : ℕ)), T.card = (3 : ℕ) → (∀ i ∈ T, i ≠ l)
      → ∀ (x : Fin (4 : ℕ) → ℝ) (n : Fin d → ℤ), (∀ (k : Fin d), |(↑(n k) : ℝ)| ≤ B) →
      |h * (↑(∑ i ∈ T, roleCoeff i l * rd x i + (36 : ℤ) * shiftDot n ζ') : ℝ) - (∑ i ∈
      T, (↑(roleCoeff i l) : ℝ) * x i + (36 : ℝ) * ∑ k : Fin d, (↑(n k) : ℝ) * ζ k)| ≤ h
      * K),
  ∑ s ∈ S with (↑(E s).card : ℝ) ≤ δ * M ^ (2 : ℕ), (↑(E s).card : ℝ) ≤ (3 : ℝ) * (10
    : ℝ) ^ (11 : ℕ) * ((1 : ℝ) + Real.logb (2 : ℝ) ((2 : ℝ) + ((↑d : ℝ) + (1 : ℝ)) ^
    (2 : ℕ) * ν / μ)) * L ^ (12 : ℕ) * δ ^ (1 / 300 : ℝ) * M ^ (2 : ℕ)




private theorem sparse_count_explicit_f_gap : SparseCountExplicitFGapStatement := by
  classical
  intro d ζ B Sg Q μ ν R₀ hB hμ hμ1 hν S E hgap hSne R hRpos Rmin K h hh rd E' ζ' hmemE hRh hRS s
    hs hne n hn ⟨hlo, hhi⟩
  obtain ⟨y, hy⟩ := hne
  obtain ⟨x, hx, -⟩ := hmemE s y hy
  have herr := shift_round_err hh ζ n hn
  have hdQ : d * Q * h / 2 ≤ μ * R s / 2000 := by
    have h1 := hRS s hs
    have hdK : (d : ℝ) * Q ≤ K := by
      have : (0 : ℝ) ≤ 18 * d * B := by positivity
      simp only [K]; linarith only [this]
    have h2 : (d : ℝ) * Q * h ≤ K * h := mul_le_mul_of_nonneg_right hdK hh.le
    linarith only [h1, h2]
  rw [hRh] at hlo hhi
  refine hgap s hs ⟨x, hx⟩ n hn ⟨?_, ?_⟩
  · have h1 : μ * R s / 100 ≤ h * |(shiftDot n ζ' : ℝ)| := by
      rw [show μ / 2 * (R s / h) / 50 = (μ * R s / 100) / h by ring, div_le_iff₀ hh] at hlo
      linarith
    have h2 := abs_sub_abs_le_abs_sub (h * (shiftDot n ζ' : ℝ)) (∑ k, (n k : ℝ) * ζ k)
    rw [abs_mul, abs_of_pos hh] at h2
    have : 0 ≤ μ * R s := (mul_pos hμ (hRpos s)).le
    linarith
  · have h1 : h * |(shiftDot n ζ' : ℝ)| ≤ 100 * ν * R s := by
      rw [show 50 * (2 * ν) * (R s / h) = (100 * ν * R s) / h by ring, le_div_iff₀ hh] at hhi
      linarith
    have h2 := abs_sub_abs_le_abs_sub (∑ k, (n k : ℝ) * ζ k) (h * (shiftDot n ζ' : ℝ))
    rw [abs_sub_comm, abs_mul, abs_of_pos hh] at h2
    have : μ * R s ≤ ν * R s := mul_le_mul_of_nonneg_right (by linarith) (hRpos s).le
    have : 0 ≤ μ * R s := (mul_pos hμ (hRpos s)).le
    linarith
-- the grid data



private theorem sparse_count_explicit_f_sep : SparseCountExplicitFSepStatement := by
  classical
  intro d ζ core B Sg Q μ R₀ S E hsep hSg0 hSne R Rmin hRmin K h hh hh1 rd E' ζ' hmemE hRh i hi s
    hs s' hs' y hy y' hy' hne n hn
  obtain ⟨x, hx, rfl⟩ := hmemE s y hy
  obtain ⟨x', hx', rfl⟩ := hmemE s' y' hy'
  have hne' : x i ≠ x' i := fun h' => hne (by simp only [rd, h'])
  have h1 := hsep i hi s hs s' hs' x hx x' hx' hne' n hn
  have e1 := gridLabel_err hh (x i)
  have e2 := gridLabel_err hh (x' i)
  have e3 := shift_round_err hh ζ n hn
  rw [hRh, hRh, max_div_div_right hh.le]
  have hmax : Rmin ≤ max (R s) (R s') := (hRmin s hs).trans (le_max_left _ _)
  -- `h |Δ'| ≥ |Δ| - h (12 + d Q)/2`
  have key : |x i - x' i + ∑ k, (n k : ℝ) * ζ k| ≤
      h * |((rd x i - rd x' i + shiftDot n ζ' : ℤ) : ℝ)| + h * (12 + d * Q) / 2 := by
    have e : x i - x' i + ∑ k, (n k : ℝ) * ζ k =
        h * ((rd x i - rd x' i + shiftDot n ζ' : ℤ) : ℝ) -
          ((h * gridLabel h (x i) - x i) - (h * gridLabel h (x' i) - x' i) +
            (h * (shiftDot n ζ' : ℝ) - ∑ k, (n k : ℝ) * ζ k)) := by
      simp only [rd]; push_cast; ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_pos hh]
    have : |(h * gridLabel h (x i) - x i) - (h * gridLabel h (x' i) - x' i) +
        (h * (shiftDot n ζ' : ℝ) - ∑ k, (n k : ℝ) * ζ k)| ≤ 3 * h + 3 * h + d * Q * h / 2 :=
      (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add e1 e2)) e3)
    linarith
  rw [← mul_div_assoc, div_lt_iff₀ hh]
  have h2 : Sg * max (R s) (R s') - h * (12 + d * Q) / 2 ≥ Sg / 2 * max (R s) (R s') := by
    have := mul_le_mul_of_nonneg_left hmax hSg0.le
    linarith
  nlinarith only [hSg0, hh1, h1, hmax, key]



private theorem sparse_count_explicit_hres : SparseCountExplicitHresStatement := by
  classical
  intro d ζ B Sg Q μ R₀ hB hμ hR₀ S hQ0 hSg0 hSne R Rmin K h hh rd ζ' T l hT3 hTl x n hn
  have h1 := shift_round_err hh ζ n hn
  have h2 : |∑ i ∈ T, (h * (roleCoeff i l * rd x i : ℤ) - (roleCoeff i l : ℝ) * x i)| ≤
      27 * h := by
    calc _ ≤ ∑ i ∈ T, |h * ((roleCoeff i l * rd x i : ℤ) : ℝ) - (roleCoeff i l : ℝ) * x i| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ T, 9 * h := by
          refine Finset.sum_le_sum fun i hi => ?_
          have e : h * ((roleCoeff i l * rd x i : ℤ) : ℝ) - (roleCoeff i l : ℝ) * x i =
              (roleCoeff i l : ℝ) * (h * gridLabel h (x i) - x i) := by push_cast; ring
          rw [e, abs_mul]
          have ha : |(roleCoeff i l : ℝ)| ≤ 3 := by
            rw [← Int.cast_abs]; exact_mod_cast (roleCoeff_spec (hTl i hi)).1
          have := gridLabel_err hh (x i)
          nlinarith only [abs_nonneg (roleCoeff i l : ℝ),
              abs_nonneg (h * gridLabel h (x i) - x i), ha, this]
      _ = 27 * h := by rw [Finset.sum_const, hT3]; ring
  have e : h * ((∑ i ∈ T, roleCoeff i l * rd x i + 36 * shiftDot n ζ' : ℤ) : ℝ) -
      (∑ i ∈ T, (roleCoeff i l : ℝ) * x i + 36 * ∑ k, (n k : ℝ) * ζ k) =
      ∑ i ∈ T, (h * (roleCoeff i l * rd x i : ℤ) - (roleCoeff i l : ℝ) * x i) +
        36 * (h * (shiftDot n ζ' : ℝ) - ∑ k, (n k : ℝ) * ζ k) := by
    push_cast
    rw [Finset.sum_sub_distrib, mul_add, Finset.mul_sum]
    ring
  rw [e]
  calc _ ≤ |∑ i ∈ T, (h * (roleCoeff i l * rd x i : ℤ) - (roleCoeff i l : ℝ) * x i)| +
        |36 * (h * (shiftDot n ζ' : ℝ) - ∑ k, (n k : ℝ) * ζ k)| := abs_add_le _ _
    _ ≤ 27 * h + 36 * (d * B * h / 2) := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 36)]
        gcongr
    _ ≤ h * K := by
        have : (0 : ℝ) ≤ d * Q * h := by positivity
        simp only [K]; nlinarith only [this]



private theorem sparse_count_explicit_stage_1 : SparseCountExplicitStage1Statement := by
  classical
  intro d ζ core hcore A M L hM hL hA B Sg Q μ ν R₀ hB hμ hμ1 hν hR₀ S E hE hpair hmult hsep hann
    hgap hQ hSg δ hδ0 hδ1 hQ0 hSg0 hSne R hRpos Rmin hRmin K hK h hh hh1 hh2 hlab rd hinj E'
  let A' : Fin (4 : ℕ) → Finset ℤ :=
    fun (i : Fin (4 : ℕ)) => Finset.image (gridLabel h) (A i)
  intro ζ' hcardE hmemE w hw0 hws hwi hres
  have hRh : ∀ s : ℤ, R₀ / h * 2 ^ s = R s / h := fun s => by simp only [R]; ring
  -- the fields of the grid data
  have f_card_A : ∀ i ∈ core, ((A' i).card : ℝ) ≤ M := fun i hi =>
    (Nat.cast_le.mpr Finset.card_image_le).trans (hA i hi)
  have f_mem_A : ∀ s ∈ S, ∀ x ∈ E' s, ∀ i ∈ core, x i ∈ A' i := by
    intro s hs x' hx' i hi
    obtain ⟨x, hx, rfl⟩ := hmemE s x' hx'
    exact Finset.mem_image_of_mem _ ((hE s hs x hx).1 i hi)
  have f_six : ∀ s ∈ S, ∀ x ∈ E' s, ∀ i ∈ core, (6 : ℤ) ∣ x i := by
    intro s _ x' hx' i _
    obtain ⟨x, -, rfl⟩ := hmemE s x' hx'
    exact six_dvd_gridLabel h (x i)
  have f_L : 1 ≤ ⌊L⌋₊ := Nat.one_le_floor_iff _ |>.mpr hL
  have f_pair : ∀ i ∈ core, ∀ j ∈ core, i ≠ j → ∀ s ∈ S, ∀ s' ∈ S, ∀ x ∈ E' s, ∀ x' ∈ E' s',
      x i = x' i → x j = x' j → x = x' := by
    intro i hi j hj hij s hs s' hs' y hy y' hy' h1 h2
    obtain ⟨x, hx, rfl⟩ := hmemE s y hy
    obtain ⟨x', hx', rfl⟩ := hmemE s' y' hy'
    rw [hpair i hi j hj hij s hs s' hs' x hx x' hx' (hlab i hi s hs s' hs' x hx x' hx' h1)
      (hlab j hj s hs s' hs' x hx x' hx' h2)]
  have f_mult : ∀ x', (S.filter fun s => x' ∈ E' s).card ≤ ⌊L⌋₊ := by
    intro x'
    rcases (S.filter fun s => x' ∈ E' s).eq_empty_or_nonempty with h0 | ⟨s₀, hs₀⟩
    · rw [h0]; exact Nat.zero_le _
    obtain ⟨hs₀S, hx's₀⟩ := Finset.mem_filter.mp hs₀
    obtain ⟨x₀, hx₀, hrx₀⟩ := hmemE s₀ x' hx's₀
    refine Nat.le_floor ((Nat.cast_le.mpr (Finset.card_le_card fun s hs => ?_)).trans (hmult x₀))
    obtain ⟨hsS, hx's⟩ := Finset.mem_filter.mp hs
    obtain ⟨x, hx, hrx⟩ := hmemE s x' hx's
    have := hinj s hsS s₀ hs₀S x hx x₀ hx₀ (hrx.trans hrx₀.symm)
    exact Finset.mem_filter.mpr ⟨hsS, this ▸ hx⟩
  have f_w_inc : core.card = 3 → ∀ s ∈ S, ∀ i ∈ core, ∀ a,
      (((E' s).filter fun x => x i = a).card : ℝ) ≤ w s := by
    intro h3 s hs i hi a
    rcases ((E' s).filter fun x => x i = a).eq_empty_or_nonempty with h0 | ⟨y₀, hy₀⟩
    · rw [h0, Finset.card_empty, Nat.cast_zero]; exact hw0 s
    obtain ⟨hy₀E, hy₀a⟩ := Finset.mem_filter.mp hy₀
    obtain ⟨x₀, hx₀, rfl⟩ := hmemE s y₀ hy₀E
    refine le_trans (Nat.cast_le.mpr ?_) (hwi h3 s hs i hi (x₀ i))
    have hsub : ((E' s).filter fun x => x i = a) ⊆
        ((E s).filter fun x => x i = x₀ i).image rd := by
      intro y hy
      obtain ⟨hyE, hya⟩ := Finset.mem_filter.mp hy
      obtain ⟨x, hx, rfl⟩ := hmemE s y hyE
      exact Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hx, hlab i hi s hs s hs x hx x₀ hx₀
        (hya.trans hy₀a.symm)⟩, rfl⟩
    exact (Finset.card_le_card hsub).trans Finset.card_image_le
  have hRS : ∀ s ∈ S, h * (1000 * K) ≤ μ * R s := fun s hs =>
    hh2.trans (mul_le_mul_of_nonneg_left (hRmin s hs) hμ.le)
  have f_μR : ∀ s ∈ S, 1 ≤ μ / 2 * (R₀ / h * 2 ^ s) := by
    intro s hs
    rw [hRh s, show μ / 2 * (R s / h) = μ * R s / (2 * h) by ring, le_div_iff₀ (by positivity)]
    have := hRS s hs
    nlinarith only [hK, hh, this]
  have f_sep : ∀ i ∈ core, ∀ s ∈ S, ∀ s' ∈ S, ∀ x ∈ E' s, ∀ x' ∈ E' s', x i ≠ x' i →
      ∀ n : Fin d → ℤ, (∀ r, |(n r : ℝ)| ≤ Q) →
        Sg / 2 * max (R₀ / h * 2 ^ s) (R₀ / h * 2 ^ s') <
          |((x i - x' i + shiftDot n ζ' : ℤ) : ℝ)| := by
    expose_names
    exact @sparse_count_explicit_f_sep d ζ core B Sg Q μ R₀ S E hsep hSg0 hSne hRmin hh hh1 hmemE
      hRh
  have f_ann : ∀ T ⊆ core, T.card = 3 → ∀ l, l ∉ T → ∀ s ∈ S, ∀ x ∈ E' s, ∃ n : Fin d → ℤ,
      (∀ r, |(n r : ℝ)| ≤ B) ∧
        μ / 2 * (R₀ / h * 2 ^ s) ≤
          |((∑ r ∈ T, roleCoeff r l * x r + 36 * shiftDot n ζ' : ℤ) : ℝ)| ∧
        |((∑ r ∈ T, roleCoeff r l * x r + 36 * shiftDot n ζ' : ℤ) : ℝ)| ≤
          2 * ν * (R₀ / h * 2 ^ s) := by
    intro T hT hT3 l hl s hs y hy
    obtain ⟨x, hx, rfl⟩ := hmemE s y hy
    obtain ⟨n, hn, h1, h2⟩ := hann T hT hT3 l hl s hs x hx
    refine ⟨n, hn, ?_⟩
    have herr := hres T l hT3 (fun i hi h' => hl (h' ▸ hi)) x n hn
    have hK1 : h * K ≤ μ * R s / 2 := by
      have := hRS s hs; nlinarith only [hK, hh, this]
    rw [hRh]
    set r' := ((∑ r ∈ T, roleCoeff r l * rd x r + 36 * shiftDot n ζ' : ℤ) : ℝ)
    set r := ∑ i ∈ T, (roleCoeff i l : ℝ) * x i + 36 * ∑ k, (n k : ℝ) * ζ k
    have hab := abs_sub_abs_le_abs_sub (h * r') r
    have hab' := abs_sub_abs_le_abs_sub r (h * r')
    rw [abs_sub_comm] at hab'
    rw [abs_mul, abs_of_pos hh] at hab hab'
    have hμν : μ * R s ≤ ν * R s := mul_le_mul_of_nonneg_right (by linarith) (hRpos s).le
    constructor
    · rw [show μ / 2 * (R s / h) = (μ * R s / 2) / h by ring, div_le_iff₀ hh]
      nlinarith only [hK1, h1, herr, hab']
    · rw [show 2 * ν * (R s / h) = (2 * ν * R s) / h by ring, le_div_iff₀ hh]
      nlinarith only [hK, hh, hK1, h1, h2, herr, hab]
  have f_gap : ∀ s ∈ S, (E' s).Nonempty → ∀ n : Fin d → ℤ, (∀ r, |(n r : ℝ)| ≤ Q) →
      ¬ (μ / 2 * (R₀ / h * 2 ^ s) / 50 ≤ |(shiftDot n ζ' : ℝ)| ∧
        |(shiftDot n ζ' : ℝ)| ≤ 50 * (2 * ν) * (R₀ / h * 2 ^ s)) := by
    expose_names
    exact @sparse_count_explicit_f_gap d ζ B Sg Q μ ν R₀ hB hμ hμ1 hν S E hgap hSne hRpos hh hmemE
      hRh hRS
  have hfinal : ∑ s ∈ S.filter (fun s => ((E' s).card : ℝ) ≤ δ * M ^ 2), ((E' s).card : ℝ) ≤
      10 ^ 11 * (1 + Real.logb 2 (2 + ((d : ℝ) + 1) ^ 2 * (2 * ν) / (μ / 2))) *
        ((⌊L⌋₊ : ℕ) : ℝ) ^ 12 * δ ^ (1 / 300 : ℝ) * M ^ 2 :=
    SparseCountData.sparse_mass_bound
      { d := d, ζ := ζ', core := core, core_card := hcore, S := S, R₀ := R₀ / h,
        R₀_pos := div_pos hR₀ hh, E := E', A := A', M := M, one_le_M := hM, card_A := f_card_A,
        mem_A := f_mem_A, six_dvd := f_six, L := ⌊L⌋₊, one_le_L := f_L, pair := f_pair,
        mult := f_mult, w := w, w_nonneg := hw0, w_sum := hws, w_inc := f_w_inc,
        μ := μ / 2, ν := 2 * ν, Sg := Sg / 2, Q := Q, B := B, μ_pos := half_pos hμ,
        μ_le_ν := by linarith, one_le_B := hB, one_le_μR := f_μR, sep := f_sep, ann := f_ann,
        gap := f_gap } hQ (by linarith) hδ0 hδ1
  have hsum : ∑ s ∈ S.filter (fun s => ((E' s).card : ℝ) ≤ δ * M ^ 2), ((E' s).card : ℝ) =
      ∑ s ∈ S.filter (fun s => ((E s).card : ℝ) ≤ δ * M ^ 2), ((E s).card : ℝ) := by
    rw [Finset.filter_congr fun s hs => by rw [hcardE s hs]]
    exact Finset.sum_congr rfl fun s hs => by rw [hcardE s (Finset.mem_filter.mp hs).1]
  rw [hsum] at hfinal
  exact sparse_count_final_arith hδ0 hL hμ (by linarith) hfinal


/-- Blueprint `lem:sparse-count` (lines 2587-2705), `eq:sparse-count`, with the explicit absolute
constants `C = 3 · 10^{11}`, `C_res = 7200000`: for real labels `A_i` (`|A_i| ≤ M`,
`M, L ≥ 1`), frequencies `ζ ∈ ℝ^d`, `B ≥ 1`, `0 < μ ≤ 1 ≤ ν`, scales `R_s = R₀ 2^s` and tuple
sets `E_s` satisfying (1) pair determination with at most `L` scale occurrences, (2) side
incidence, (3) separation, (4) annular witnesses for every triple, and (5) the pure-shift gap,
the reserves `Q ≥ C_res (d+1)² B`, `Σ ≥ C_res (d+1)² ν` imply, for `0 < δ ≤ 1`,
`Σ_{s : N_s ≤ δ M²} N_s ≤ C ℓ L¹² δ^{1/300} M²` with `ℓ = 1 + log₂(2 + (d+1)² ν/μ)`.
Tuples are functions on the four roles vanishing off the core roles; a role coefficient is
`α_i = i - l'`. -/
theorem sparse_count_explicit :
    ∀ (d : ℕ) (ζ : Fin d → ℝ) (core : Finset (Fin 4)), (core.card = 3 ∨ core.card = 4) →
    ∀ (A : Fin 4 → Finset ℝ) (M L : ℝ), 1 ≤ M → 1 ≤ L → (∀ i ∈ core, ((A i).card : ℝ) ≤ M) →
    ∀ (B Sg Q μ ν R₀ : ℝ), 1 ≤ B → 0 < μ → μ ≤ 1 → 1 ≤ ν → 0 < R₀ →
    ∀ (S : Finset ℤ) (E : ℤ → Finset (Fin 4 → ℝ)),
    (∀ s ∈ S, ∀ x ∈ E s, (∀ i ∈ core, x i ∈ A i) ∧ ∀ i ∉ core, x i = 0) →
    (∀ i ∈ core, ∀ j ∈ core, i ≠ j → ∀ s ∈ S, ∀ s' ∈ S, ∀ x ∈ E s, ∀ x' ∈ E s',
      x i = x' i → x j = x' j → x = x') →
    (∀ x, ((S.filter fun s => x ∈ E s).card : ℝ) ≤ L) →
    (core.card = 3 → ∃ w : ℤ → ℝ, (∀ s, 0 ≤ w s) ∧ ∑ s ∈ S, w s ≤ M ∧
      ∀ s ∈ S, ∀ i ∈ core, ∀ a, (((E s).filter fun x => x i = a).card : ℝ) ≤ w s) →
    (∀ i ∈ core, ∀ s ∈ S, ∀ s' ∈ S, ∀ x ∈ E s, ∀ x' ∈ E s', x i ≠ x' i →
      ∀ n : Fin d → ℤ, (∀ k, |(n k : ℝ)| ≤ Q) →
        Sg * max (R₀ * 2 ^ s) (R₀ * 2 ^ s') < |x i - x' i + ∑ k, (n k : ℝ) * ζ k|) →
    (∀ T ⊆ core, T.card = 3 → ∀ l, l ∉ T → ∀ s ∈ S, ∀ x ∈ E s, ∃ n : Fin d → ℤ,
      (∀ k, |(n k : ℝ)| ≤ B) ∧
        μ * (R₀ * 2 ^ s) ≤ |∑ i ∈ T, (roleCoeff i l : ℝ) * x i + 36 * ∑ k, (n k : ℝ) * ζ k| ∧
        |∑ i ∈ T, (roleCoeff i l : ℝ) * x i + 36 * ∑ k, (n k : ℝ) * ζ k| ≤ ν * (R₀ * 2 ^ s)) →
    (∀ s ∈ S, (E s).Nonempty → ∀ n : Fin d → ℤ, (∀ k, |(n k : ℝ)| ≤ Q) →
      |∑ k, (n k : ℝ) * ζ k| ∉ Set.Icc (μ * (R₀ * 2 ^ s) / 1000) (1000 * ν * (R₀ * 2 ^ s))) →
    7200000 * ((d : ℝ) + 1) ^ 2 * B ≤ Q → 7200000 * ((d : ℝ) + 1) ^ 2 * ν ≤ Sg →
    ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∑ s ∈ S.filter (fun s => ((E s).card : ℝ) ≤ δ * M ^ 2), ((E s).card : ℝ) ≤
        3 * 10 ^ 11 * (1 + Real.logb 2 (2 + ((d : ℝ) + 1) ^ 2 * ν / μ)) * L ^ 12 *
          δ ^ (1 / 300 : ℝ) * M ^ 2 := by
  intro d ζ core hcore A M L hM hL hA B Sg Q μ ν R₀ hB hμ hμ1 hν hR₀ S E hE hpair hmult hside
    hsep hann hgap hQ hSg δ hδ0 hδ1
  have hd1 : (1 : ℝ) ≤ ((d : ℝ) + 1) ^ 2 := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    nlinarith
  have hQ0 : 0 ≤ Q := le_trans (by positivity) hQ
  have hSg0 : 0 < Sg := lt_of_lt_of_le (by positivity) hSg
  have hℓ0 : 0 ≤ Real.logb 2 (2 + ((d : ℝ) + 1) ^ 2 * ν / μ) := by
    refine Real.logb_nonneg (by norm_num) ?_
    have : 0 ≤ ((d : ℝ) + 1) ^ 2 * ν / μ := by positivity
    linarith
  rcases S.eq_empty_or_nonempty with hS | hSne
  · simp only [hS, Finset.filter_empty, Finset.sum_empty]
    positivity
  -- the grid step
  set! R : ℤ → ℝ := fun s => R₀ * 2 ^ s
  have hRpos : ∀ s, 0 < R s := fun s => mul_pos hR₀ (zpow_pos (by norm_num) s)
  set! Rmin := R (S.min' hSne)
  have hRmin : ∀ s ∈ S, Rmin ≤ R s := fun s hs =>
    mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ (by norm_num) (Finset.min'_le _ _ hs)) hR₀.le
  have hRmin0 : 0 < Rmin := hRpos _
  set! K := 27 + d * Q + 18 * d * B
  have hK : 27 ≤ K := by
    have : (0 : ℝ) ≤ d * Q := by positivity
    have : (0 : ℝ) ≤ 18 * d * B := by positivity
    linarith
  set! h := min (Sg * Rmin / (12 + d * Q)) (μ * Rmin / (1000 * K))
  have hh : 0 < h := lt_min (by positivity) (by positivity)
  have hh1 : h * (12 + d * Q) ≤ Sg * Rmin := by
    have := min_le_left (Sg * Rmin / (12 + d * Q)) (μ * Rmin / (1000 * K))
    rwa [le_div_iff₀ (by positivity)] at this
  have hh2 : h * (1000 * K) ≤ μ * Rmin := by
    have := min_le_right (Sg * Rmin / (12 + d * Q)) (μ * Rmin / (1000 * K))
    rwa [le_div_iff₀ (by positivity)] at this
  -- labels at the same scale or across scales with equal grid labels are equal
  have hlab : ∀ i ∈ core, ∀ s ∈ S, ∀ s' ∈ S, ∀ x ∈ E s, ∀ x' ∈ E s',
      gridLabel h (x i) = gridLabel h (x' i) → x i = x' i := by
    intro i hi s hs s' hs' x hx x' hx' hg
    by_contra hne
    have h1 := hsep i hi s hs s' hs' x hx x' hx' hne 0 (fun k => by simp [hQ0])
    simp only [Pi.zero_apply, Int.cast_zero, zero_mul, Finset.sum_const_zero, add_zero] at h1
    have h2 := gridLabel_close hh hg
    have h3 : Sg * Rmin ≤ Sg * max (R s) (R s') :=
      mul_le_mul_of_nonneg_left ((hRmin s hs).trans (le_max_left _ _)) hSg0.le
    have h4 : 6 * h < Sg * Rmin := by
      have : (0 : ℝ) ≤ d * Q := by positivity
      nlinarith only [hh, hh1, this]
    linarith
  set! rd : (Fin 4 → ℝ) → Fin 4 → ℤ := fun x i => gridLabel h (x i)
  have hinj : ∀ s ∈ S, ∀ s' ∈ S, ∀ x ∈ E s, ∀ x' ∈ E s', rd x = rd x' → x = x' := by
    intro s hs s' hs' x hx x' hx' heq
    funext i
    by_cases hi : i ∈ core
    · exact hlab i hi s hs s' hs' x hx x' hx' (congrFun heq i)
    · rw [(hE s hs x hx).2 i hi, (hE s' hs' x' hx').2 i hi]
  have hrdinj : ∀ s ∈ S, Set.InjOn rd (E s) := fun s hs x hx x' hx' h =>
    hinj s hs s hs x hx x' hx' h
  set! E' : ℤ → Finset (Fin 4 → ℤ) := fun s => (E s).image rd
  set! A' : Fin 4 → Finset ℤ := fun i => (A i).image (gridLabel h)
  set! ζ' : Fin d → ℤ := fun k => round (ζ k / h)
  have hcardE : ∀ s ∈ S, (E' s).card = (E s).card := fun s hs =>
    Finset.card_image_of_injOn (hrdinj s hs)
  have hmemE : ∀ s, ∀ x' ∈ E' s, ∃ x ∈ E s, rd x = x' := fun s x' hx' => Finset.mem_image.mp hx'
  -- the side weights
  have hw : ∃ w : ℤ → ℝ, (∀ s, 0 ≤ w s) ∧ ∑ s ∈ S, w s ≤ M ∧ (core.card = 3 →
      ∀ s ∈ S, ∀ i ∈ core, ∀ a, (((E s).filter fun x => x i = a).card : ℝ) ≤ w s) := by
    by_cases h3 : core.card = 3
    · obtain ⟨w, hw0, hws, hwi⟩ := hside h3
      exact ⟨w, hw0, hws, fun _ => hwi⟩
    · exact ⟨0, fun _ => le_rfl, by simp; linarith, fun h => absurd h h3⟩
  obtain ⟨w, hw0, hws, hwi⟩ := hw
  -- the error of rounded residuals
  have hres : ∀ (T : Finset (Fin 4)) (l : Fin 4), T.card = 3 → (∀ i ∈ T, i ≠ l) →
      ∀ (x : Fin 4 → ℝ) (n : Fin d → ℤ), (∀ k, |(n k : ℝ)| ≤ B) →
      |h * ((∑ i ∈ T, roleCoeff i l * rd x i + 36 * shiftDot n ζ' : ℤ) : ℝ) -
        (∑ i ∈ T, (roleCoeff i l : ℝ) * x i + 36 * ∑ k, (n k : ℝ) * ζ k)| ≤ h * K := by
    expose_names
    exact @sparse_count_explicit_hres d ζ B Sg Q μ R₀ hB hμ hR₀ S hQ0 hSg0 hSne hh
  expose_names
  exact @sparse_count_explicit_stage_1 d ζ core hcore A M L hM hL hA B Sg Q μ ν R₀ hB hμ hμ1 hν
    hR₀ S E hE hpair hmult hsep hann hgap hQ hSg δ hδ0 hδ1 hQ0 hSg0 hSne hRpos hRmin hK hh hh1 hh2
    hlab hinj hcardE hmemE w hw0 hws hwi hres

end TrilinearHT.Auto

end

section

namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

/-- The reference data of a tested three-core tuple (side role `l`) at scale `R`: a box shift
`m` with `μ R ≤ |T_l + 36 m·ζ| ≤ ν R`, `T_l = Σ_{i ≠ l} (i - l) x_i` (blueprint lines
2552-2553, the nonzero `T_l` test). -/
def ThreeRef {d : ℕ} (ζ : Fin d → ℝ) (l : Fin 4) (B μ ν R : ℝ) (x : Fin 4 → ℝ) : Prop :=
  ∃ m : Fin d → ℤ, (∀ p, |(m p : ℝ)| ≤ B) ∧
    μ * R ≤ |∑ i ∈ Finset.univ.erase l, (roleCoeff i l : ℝ) * x i + 36 * ∑ p, (m p : ℝ) * ζ p| ∧
    |∑ i ∈ Finset.univ.erase l, (roleCoeff i l : ℝ) * x i + 36 * ∑ p, (m p : ℝ) * ζ p| ≤ ν * R

end TrilinearHT.Auto

end
