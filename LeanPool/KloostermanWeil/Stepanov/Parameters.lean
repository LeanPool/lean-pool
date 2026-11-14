/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import LeanPool.KloostermanWeil.Stepanov.Auxiliary
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Data.Nat.Sqrt


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# Uniform Stepanov parameters

The variable-and-constraint estimates following Harcos (2015), equation (22), with
parameters uniform in the extension degree; see Stepanov (1972).
-/

@[expose] public section

open scoped BigOperators

namespace KloostermanWeil.Stepanov

open Polynomial

/-- Closed form for the number of scalar equations contributed by the first
`l` Hasse-derivative rows. -/
theorem stepanov_constraint_sum_eq (l d m J : ℕ) :
    (∑ k : Fin l, (d + (k : ℕ) * (m - 1) + J)) =
      l * (d + J) + (m - 1) * (l * (l - 1) / 2) := by
  have hconv : (∑ k : Fin l, (d + (k : ℕ) * (m - 1) + J)) =
      ∑ k ∈ Finset.range l, (d + k * (m - 1) + J) := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    simp [Finset.mem_range.mp hk]
  rw [hconv]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]
  rw [← Finset.sum_mul, Finset.sum_range_id]
  rw [Nat.mul_add]
  simp [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- A concrete integer parameter choice satisfying the strict homogeneous
dimension inequality after (22).  Here `d = ceil((q-m)/2)` is exactly the
source coefficient cutoff, while `J` is a uniform integral enlargement of
the source optimizing choice. -/
theorem stepanov_constraint_dimension_bound
    {q m l : ℕ} (hm : 3 < m) (hl : 0 < l)
    (hlsq : l * l ≤ q + 2 * l + 1)
    (hq : 100 * (m + 1) * l < q) :
    let d := (q - m) ⌈/⌉ 2
    let J := (l + 1) / 2 + 10 * (m + 1)
    (∑ k : Fin l, (d + (k : ℕ) * (m - 1) + J)) < 2 * J * d := by
  dsimp
  rw [stepanov_constraint_sum_eq]
  have hqm : m < q := by nlinarith only [hm, hl, hq]
  have hqmsub : q - m + m = q := by omega
  have hdlo : q - m ≤ 2 * ((q - m) ⌈/⌉ 2) := by
    exact (ceilDiv_le_iff_le_mul (by omega)).1 le_rfl
  have hdhi : 2 * ((q - m) ⌈/⌉ 2) ≤ q - m + 1 := by
    simp only [Nat.ceilDiv_eq_add_pred_div]
    omega
  have hJlo : l + 20 * (m + 1) ≤
      2 * ((l + 1) / 2 + 10 * (m + 1)) := by omega
  have hJhi : 2 * ((l + 1) / 2 + 10 * (m + 1)) ≤
      l + 1 + 20 * (m + 1) := by omega
  have hmone : m - 1 + 1 = m := by omega
  have hbasele : 100 * (m + 1) ≤ 100 * (m + 1) * l := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (100 * (m + 1)) hl
  have hqbase : 100 * (m + 1) < q := hbasele.trans_lt hq
  have hqsmall : 25 * (m + 1) * l < q := by nlinarith only [hq]
  have hqscaled := Nat.mul_lt_mul_of_pos_left hqbase
    (by positivity : 0 < 19 * m)
  have hmsmall : 20 * m * (m + 1) + (m - 1) < 19 * m * q := by
    nlinarith only [hqscaled, hm, hmone]
  have hbudget :
      20 * m * (m + 1) + 25 * (m + 1) * l + m <
        (19 * m + 20) * q := by
    nlinarith only [hmsmall, hqsmall, hmone]
  have htri : 2 * (l * (l - 1) / 2) ≤ l * (l - 1) :=
    Nat.mul_div_le _ _
  have hprodLower :
      (l + 20 * (m + 1)) * (q - m) ≤
        (2 * ((l + 1) / 2 + 10 * (m + 1))) *
          (2 * ((q - m) ⌈/⌉ 2)) :=
    Nat.mul_le_mul hJlo hdlo
  have hdterm :
      2 * (l * ((q - m) ⌈/⌉ 2)) ≤ l * (q - m + 1) := by
    nlinarith only [Nat.mul_le_mul_left l hdhi]
  have hJterm :
      2 * (l * ((l + 1) / 2 + 10 * (m + 1))) ≤
        l * (l + 1 + 20 * (m + 1)) := by
    nlinarith only [Nat.mul_le_mul_left l hJhi]
  have hmterm :
      2 * ((m - 1) * (l * (l - 1) / 2)) ≤
        (m - 1) * (l * (l - 1)) := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (Nat.mul_le_mul_left (m - 1) htri)
  have hpoly :
      l * (q - m + 1) + l * (l + 1 + 20 * (m + 1)) +
          (m - 1) * (l * (l - 1)) <
        (l + 20 * (m + 1)) * (q - m) := by
    have hUsimp :
        l * (q - m + 1) + l * (l + 1 + 20 * (m + 1)) +
            (m - 1) * (l * (l - 1)) =
          l * q + m * (l * l) + 18 * m * l + 23 * l := by
      apply Nat.cast_injective (R := ℤ)
      push_cast
      rw [Nat.cast_sub hqm.le, Nat.cast_sub (by omega : 1 ≤ m),
        Nat.cast_sub (by omega : 1 ≤ l)]
      ring
    have hmlsq := Nat.mul_le_mul_left m hlsq
    have hUupper :
        l * q + m * (l * l) + 18 * m * l + 23 * l ≤
          l * q + m * (q + 2 * l + 1) + 18 * m * l + 23 * l := by
      omega
    rw [hUsimp]
    have hPalgebra :
        (l + 20 * (m + 1)) * (q - m) +
            (l * m + 20 * (m + 1) * m) =
          l * q + 20 * (m + 1) * q := by
      nlinarith only [hqmsub]
    have hstrict :
        (l * q + m * (q + 2 * l + 1) + 18 * m * l + 23 * l) +
            (l * m + 20 * (m + 1) * m) <
          l * q + 20 * (m + 1) * q := by
      nlinarith only [hbudget]
    omega
  have hdouble :
      2 * (l * (((q - m) ⌈/⌉ 2) +
            ((l + 1) / 2 + 10 * (m + 1))) +
          (m - 1) * (l * (l - 1) / 2)) <
        (2 * ((l + 1) / 2 + 10 * (m + 1))) *
          (2 * ((q - m) ⌈/⌉ 2)) := by
    nlinarith only [hdterm, hJterm, hmterm, hpoly, hprodLower]
  nlinarith only [hdouble]

/-- All elementary side conditions for the square-root-scale choice of the
Stepanov parameters. -/
theorem stepanov_sqrt_parameters
    {q m : ℕ} (hm : 3 < m)
    (hq : 100 * (m + 1) * (Nat.sqrt q + 1) < q) :
    let l := Nat.sqrt q + 1
    let d := (q - m) ⌈/⌉ 2
    let J := (l + 1) / 2 + 10 * (m + 1)
    0 < d ∧ 0 < l ∧ l ≤ q ∧
      2 * (d - 1) + m < q ∧
      (∑ k : Fin l, (d + (k : ℕ) * (m - 1) + J)) < 2 * J * d := by
  dsimp
  have hqm : m < q := by nlinarith only [hm, hq]
  have hspos : 0 < Nat.sqrt q + 1 := by omega
  have hsle : Nat.sqrt q + 1 ≤ q := by
    have hscale : Nat.sqrt q + 1 ≤
        100 * (m + 1) * (Nat.sqrt q + 1) := by
      nlinarith only [hm]
    exact hscale.trans (Nat.le_of_lt hq)
  have hlsq : (Nat.sqrt q + 1) * (Nat.sqrt q + 1) ≤
      q + 2 * (Nat.sqrt q + 1) + 1 := by
    have hs := Nat.sqrt_le q
    nlinarith only [hs]
  have hdpos : 0 < (q - m) ⌈/⌉ 2 := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    have : 2 ≤ q - m + 1 := by omega
    omega
  have hdhi : 2 * ((q - m) ⌈/⌉ 2) ≤ q - m + 1 := by
    simp only [Nat.ceilDiv_eq_add_pred_div]
    omega
  refine ⟨hdpos, hspos, hsle, ?_, ?_⟩
  · omega
  · exact stepanov_constraint_dimension_bound hm hspos hlsq hq

/-- Equation (14) with every parameter instantiated at square-root scale.
This is the high-extension-degree estimate used in the
subsequent point-count argument. -/
theorem stepanov_point_set_sqrt_bound
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {p n : ℕ} [Fact p.Prime] [CharP F p]
    (hcard : Fintype.card F = p ^ n)
    (f : F[X]) (a : F) (hf : f ≠ 0) (hm : 3 < f.natDegree)
    (hqodd : Odd (p ^ n))
    (hlarge : 100 * (f.natDegree + 1) * (Nat.sqrt (p ^ n) + 1) < p ^ n)
    (hf0 : f.coeff 0 ≠ 0) (hnsq : ¬ IsScalarSquare f) :
    let q := p ^ n
    let l := Nat.sqrt q + 1
    let d := (q - f.natDegree) ⌈/⌉ 2
    let J := (l + 1) / 2 + 10 * (f.natDegree + 1)
    l * (Finset.univ.filter fun x : F =>
      f.eval x = 0 ∨ (f.eval x) ^ ((q - 1) / 2) = a).card <
      f.natDegree * (l + ((q - 1) / 2)) + d + J * q := by
  dsimp
  obtain ⟨hd, hl, hlq, hsize, hdim⟩ :=
    stepanov_sqrt_parameters hm hlarge
  exact stepanov_point_set_cardinality_bound hcard f a hf (by omega)
    hd hl hlq hqodd hsize hf0 hnsq hdim

/-- The elementary final simplification of the instantiated degree bound:
the raw equation-(14) right side gives a uniform square-root error. -/
theorem stepanov_raw_bound_to_sqrt
    {q m S : ℕ}
    (hm : 3 < m)
    (hlarge : 100 * (m + 1) * (Nat.sqrt q + 1) < q)
    (hraw : (Nat.sqrt q + 1) * S <
      m * ((Nat.sqrt q + 1) + ((q - 1) / 2)) +
        ((q - m) ⌈/⌉ 2) +
          (((Nat.sqrt q + 2) / 2 + 10 * (m + 1)) * q)) :
    S < (q + 1) / 2 + 40 * (m + 1) * (Nat.sqrt q + 1) := by
  let l := Nat.sqrt q + 1
  let d := (q - m) ⌈/⌉ 2
  let J := (l + 1) / 2 + 10 * (m + 1)
  have hqpos : 0 < q := by nlinarith only [hlarge]
  have hlpos : 0 < l := by dsimp [l]; omega
  have hqm : m < q := by nlinarith only [hm, hlarge]
  have hsqrt : q < l * l := by
    dsimp [l]
    exact Nat.lt_succ_sqrt q
  have hdhi : 2 * d ≤ q - m + 1 := by
    dsimp [d]
    simp only [Nat.ceilDiv_eq_add_pred_div]
    omega
  have hJhi : 2 * J ≤ l + 1 + 20 * (m + 1) := by
    dsimp [J]
    omega
  have hhalfm : 2 * ((q - 1) / 2) ≤ q - 1 := Nat.mul_div_le _ _
  have hhalfLower : q ≤ 2 * ((q + 1) / 2) := by omega
  have hhalfLowerL := Nat.mul_le_mul_left l hhalfLower
  have hJhiq := Nat.mul_le_mul_right q hJhi
  have hsqrtM := Nat.mul_lt_mul_of_pos_left hsqrt
    (by positivity : 0 < 80 * (m + 1))
  have hRdouble :
      2 * (m * (l + ((q - 1) / 2)) + d + J * q) ≤
        2 * m * l + m * (q - 1) + (q - m + 1) +
          (l + 1 + 20 * (m + 1)) * q := by
    nlinarith only [hdhi, hJhiq, hhalfm]
  have hBdouble :
      l * q + 80 * (m + 1) * q ≤
        2 * (l * ((q + 1) / 2 + 40 * (m + 1) * l)) := by
    have hleft : l * q ≤ 2 * l * ((q + 1) / 2) := by
      calc
        l * q ≤ l * (2 * ((q + 1) / 2)) := hhalfLowerL
        _ = 2 * l * ((q + 1) / 2) := by ring
    have hright : 80 * (m + 1) * q ≤
        80 * (m + 1) * (l * l) := hsqrtM.le
    calc
      l * q + 80 * (m + 1) * q ≤
          2 * l * ((q + 1) / 2) + 80 * (m + 1) * (l * l) :=
        Nat.add_le_add hleft hright
      _ = 2 * (l * ((q + 1) / 2 + 40 * (m + 1) * l)) := by ring
  have hRtoB :
      2 * m * l + m * (q - 1) + (q - m + 1) +
          (l + 1 + 20 * (m + 1)) * q <
        l * q + 80 * (m + 1) * q := by
    have hlq : l ≤ q := by
      dsimp [l] at hlarge ⊢
      have : Nat.sqrt q + 1 ≤
          100 * (m + 1) * (Nat.sqrt q + 1) := by nlinarith only [hm]
      exact this.trans (Nat.le_of_lt hlarge)
    have hmlq := Nat.mul_le_mul_left (2 * m) hlq
    have hmhalf : m * (q - 1) ≤ m * q :=
      Nat.mul_le_mul_left m (Nat.sub_le q 1)
    have hqsub : q - m + 1 ≤ q := by omega
    have hexpand :
        (l + 1 + 20 * (m + 1)) * q =
          l * q + (20 * m + 21) * q := by ring
    rw [hexpand]
    nlinarith only [hmlq, hmhalf, hqsub, hm]
  have htarget :
      m * (l + ((q - 1) / 2)) + d + J * q ≤
        l * ((q + 1) / 2 + 40 * (m + 1) * l) := by
    nlinarith only [hRdouble, hBdouble, hRtoB]
  exact (Nat.mul_lt_mul_left hlpos).mp (hraw.trans_le htarget)

end KloostermanWeil.Stepanov
