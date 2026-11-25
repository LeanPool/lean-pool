/-
Copyright (c) 2026 Mike Lady. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Lady
-/

module

public import LeanPool.TetrahedronPacking.IntegerProjections
public import LeanPool.TetrahedronPacking.PeriodicClearance
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Integer witnesses for clearance

The dot product with an integer direction has operator norm at most the
sum of the absolute values of the coefficients for the coordinate sup norm.
We can therefore check both support bounds and the perturbation margin
using integers. The witness direction, including its sign, is part of the
certificate.
-/

@[expose] public section

namespace TetrahedronPacking

open Set

/-- An oriented integer axis separates the two vertex sets with room for
coordinate errors whose sum is `budget`. The offset is the projection of
the translation of the second vertex set. -/
def integerClearance (n : Fin 3 → ℤ) (v w : Fin 4 → Fin 3 → ℤ)
    (offset budget : ℤ) : Bool :=
  decide (0 ≤ budget ∧ n ≠ 0 ∧ (integerProjectionBounds n v).2 +
    (|n 0| + |n 1| + |n 2|) * budget ≤ (integerProjectionBounds n w).1 + offset)

example : integerClearance ![1, 0, 0] (fun _ => ![0, 0, 0])
    (fun _ => ![2, 0, 0]) 0 2 = true := by decide

example : integerClearance ![1, 0, 0] (fun _ => ![0, 0, 0])
    (fun _ => ![2, 0, 0]) 0 3 = false := by decide

example : integerClearance ![0, 0, 0] (fun _ => ![0, 0, 0])
    (fun _ => ![2, 0, 0]) 0 0 = false := by decide

example : integerClearance ![1, 0, 0] (fun _ => ![0, 0, 0])
    (fun _ => ![0, 0, 0]) 0 (-1) = false := by decide

/-- Check a support gap in numerator units, then transport it to real
coordinates after division by a positive common scale. -/
theorem integerClearance_plane (n : Fin 3 → ℤ) (v w : Fin 4 → Fin 3 → ℤ)
    (t : Fin 3 → ℤ) {d : ℤ} (hd : 0 < d) {εv εw : ℤ}
    (hεv : 0 ≤ εv) (hεw : 0 ≤ εw)
    (h : integerClearance n v w (integerDot n t) (εv + εw) = true) :
    ∃ (f : (Fin 3 → ℝ) →L[ℝ] ℝ) (a b : ℝ), f ≠ 0 ∧
      (∀ i, f (fun j => (v i j : ℝ) / d) ≤ a) ∧
      (∀ i, b ≤ f ((fun j => (w i j : ℝ) / d) + (fun j => (t j : ℝ) / d))) ∧
      a + ‖f‖ * (εv / (d : ℝ)) ≤ b - ‖f‖ * (εw / (d : ℝ)) := by
  obtain ⟨_, hn, hmargin⟩ := of_decide_eq_true h
  let f : (Fin 3 → ℝ) →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    ((n 0 : ℝ) • LinearMap.proj 0 + (n 1 : ℝ) • LinearMap.proj 1 +
      (n 2 : ℝ) • LinearMap.proj 2)
  have hf_apply (u : Fin 3 → ℝ) : f u = n 0 * u 0 + n 1 * u 1 + n 2 * u 2 := rfl
  have hf_ne : f ≠ 0 := by
    intro hzero
    apply hn
    ext r
    have hz := congrArg (fun g : (Fin 3 → ℝ) →L[ℝ] ℝ => g (Pi.single r 1)) hzero
    change f (Pi.single r 1) = 0 at hz
    have hr : f (Pi.single r 1) = n r := by
      fin_cases r
      · norm_num [hf_apply, Pi.single_apply, Fin.ext_iff]
      · norm_num [hf_apply, Pi.single_apply, Fin.ext_iff]
      · norm_num [hf_apply, Pi.single_apply, Fin.ext_iff]
    rw [hr] at hz
    exact_mod_cast hz
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hf_int (u : Fin 3 → ℤ) :
      f (fun j => (u j : ℝ) / d) = (integerDot n u : ℝ) / d := by
    push_cast [hf_apply, integerDot]
    ring
  let N : ℝ := |(n 0 : ℝ)| + |(n 1 : ℝ)| + |(n 2 : ℝ)|
  have hN : 0 ≤ N := by positivity
  have hnorm : ‖f‖ ≤ N := by
    apply f.opNorm_le_bound hN
    intro x
    have hj (j : Fin 3) : |x j| ≤ ‖x‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j
    rw [hf_apply, Real.norm_eq_abs]
    calc
      _ ≤ |n 0 * x 0 + n 1 * x 1| + |n 2 * x 2| := abs_add_le _ _
      _ ≤ |n 0 * x 0| + |n 1 * x 1| + |n 2 * x 2| := by
        gcongr
        exact abs_add_le _ _
      _ ≤ N * ‖x‖ := by
        simp only [abs_mul, N, add_mul]
        gcongr <;> apply hj
  refine ⟨f, ((integerProjectionBounds n v).2 : ℝ) / d,
    (((integerProjectionBounds n w).1 + integerDot n t : ℤ) : ℝ) / d,
    hf_ne, ?_, ?_, ?_⟩
  · intro i
    rw [hf_int]
    exact div_le_div_of_nonneg_right (by exact_mod_cast
      (integerProjectionBounds_spec n v i).2) hdR.le
  · intro i
    rw [map_add, hf_int, hf_int, ← add_div]
    push_cast
    apply div_le_div_of_nonneg_right _ hdR.le
    gcongr
    exact_mod_cast (integerProjectionBounds_spec n w i).1
  · have hg : ((integerProjectionBounds n v).2 : ℝ) + N * ((εv : ℝ) + εw) ≤
        (((integerProjectionBounds n w).1 + integerDot n t : ℤ) : ℝ) := by
      dsimp only [N]
      exact_mod_cast hmargin
    have hV : 0 ≤ (εv : ℝ) / d := div_nonneg (by exact_mod_cast hεv) hdR.le
    have hW : 0 ≤ (εw : ℝ) / d := div_nonneg (by exact_mod_cast hεw) hdR.le
    have hh := div_le_div_of_nonneg_right hg hdR.le
    rw [add_div, mul_div_assoc, add_div, mul_add] at hh
    linarith [mul_le_mul_of_nonneg_right hnorm hV, mul_le_mul_of_nonneg_right hnorm hW]


def coordinateBounds (v : Fin 4 → Fin 3 → ℤ) (j : Fin 3) : ℤ × ℤ :=
  (min (min (v 0 j) (v 1 j)) (min (v 2 j) (v 3 j)),
   max (max (v 0 j) (v 1 j)) (max (v 2 j) (v 3 j)))

private theorem coordinateBounds_spec (v : Fin 4 → Fin 3 → ℤ) (i : Fin 4) (j : Fin 3) :
    (coordinateBounds v j).1 ≤ v i j ∧ v i j ≤ (coordinateBounds v j).2 := by
  fin_cases i <;> simp [coordinateBounds, min_le_iff, le_max_iff]

example : coordinateBounds (fun i => ![(i.val : ℤ), 0, 0]) 0 = (0, 3) := by decide
example : coordinateBounds (fun i => ![(i.val : ℤ), 0, 0]) 0 ≠ (0, 2) := by decide

/-- Inclusive integer shifts whose coordinate bounds permit contact after
perturbation. The vertices and total coordinate budget are numerators in
a chart whose integer lattice spacing is `d`. -/
def clearanceShiftBox (v w : Fin 4 → Fin 3 → ℤ) (d budget : ℤ) :
    Finset (Fin 3 → ℤ) :=
  integerShiftBox
    (fun j => -(((coordinateBounds w j).2 - (coordinateBounds v j).1 + budget) / d))
    (fun j => ((coordinateBounds v j).2 - (coordinateBounds w j).1 + budget) / d)

example : (![1, 0, 0] : Fin 3 → ℤ) ∈ clearanceShiftBox
    (fun _ => ![0, 0, 0]) (fun _ => ![0, 0, 0]) 10 10 := by decide
example : (![1, 0, 0] : Fin 3 → ℤ) ∉ clearanceShiftBox
    (fun _ => ![0, 0, 0]) (fun _ => ![0, 0, 0]) 10 9 := by decide

/-- Integer certificates for finitely many shifts suffice for every
required image and every realization of the cell in the fractional
coordinate budgets. -/
theorem disjoint_interiors_of_integer_clearance
    (C : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ))
    (v w : Fin 4 → Fin 3 → ℤ) (v' w' : Fin 4 → Fin 3 → ℝ)
    (required : (Fin 3 → ℤ) → Prop) {d εv εw : ℤ}
    (hd : 0 < d) (hεv : 0 ≤ εv) (hεw : 0 ≤ εw)
    (hδv : ∀ i j, |v' i j - (v i j : ℝ) / d| ≤ (εv : ℝ) / d)
    (hδw : ∀ i j, |w' i j - (w i j : ℝ) / d| ≤ (εw : ℝ) / d)
    (certificate : ∀ k ∈ clearanceShiftBox v w d (εv + εw), required k →
      ∃ n : Fin 3 → ℤ,
        integerClearance n v w (integerDot n (fun j => d * k j)) (εv + εw) = true) :
    ∀ k : Fin 3 → ℤ, required k →
      Disjoint (interior (convexHull ℝ (range (fun i => C.symm (v' i)))))
        (interior (convexHull ℝ (range (fun j => C.symm (w' j) +
          C.symm (fun i => (k i : ℝ)))))) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hV : 0 ≤ (εv : ℝ) / d := div_nonneg (by exact_mod_cast hεv) hdR.le
  have hW : 0 ≤ (εw : ℝ) / d := div_nonneg (by exact_mod_cast hεw) hdR.le
  let lo (u : Fin 4 → Fin 3 → ℤ) (j : Fin 3) := ((coordinateBounds u j).1 : ℝ) / d
  let hi (u : Fin 4 → Fin 3 → ℤ) (j : Fin 3) := ((coordinateBounds u j).2 : ℝ) / d
  have bounds (u : Fin 4 → Fin 3 → ℤ) (i : Fin 4) (j : Fin 3) :
      lo u j ≤ (u i j : ℝ) / d ∧ (u i j : ℝ) / d ≤ hi u j := by
    obtain ⟨hl, hh⟩ := coordinateBounds_spec u i j
    exact ⟨div_le_div_of_nonneg_right (by exact_mod_cast hl) hdR.le,
      div_le_div_of_nonneg_right (by exact_mod_cast hh) hdR.le⟩
  apply disjoint_interiors_of_fractional_clearance C
    (fun i j => (v i j : ℝ) / d) v' (fun i j => (w i j : ℝ) / d) w' required
    (lo v) (hi v) (lo w) (hi w) hV hW (bounds v) (bounds w) hδv hδw
  intro k hk hb
  have hbox : k ∈ clearanceShiftBox v w d (εv + εw) := by
    apply (mem_integerShiftBox _ _ _).mpr
    intro j
    obtain ⟨hl, hh⟩ := hb j
    have hneg : -(k j) * d ≤ (coordinateBounds w j).2 - (coordinateBounds v j).1 +
        (εv + εw) := by
      have h := (le_div_iff₀ hdR).mp (show -(k j : ℝ) ≤
          (((coordinateBounds w j).2 : ℝ) - (coordinateBounds v j).1 + ((εv : ℝ) + εw)) / d by
        dsimp only [lo, hi] at hl
        rw [add_div, sub_div, add_div]
        linarith)
      exact_mod_cast h
    have hpos : k j * d ≤ (coordinateBounds v j).2 - (coordinateBounds w j).1 +
        (εv + εw) := by
      have h := (le_div_iff₀ hdR).mp (show (k j : ℝ) ≤
          (((coordinateBounds v j).2 : ℝ) - (coordinateBounds w j).1 + ((εv : ℝ) + εw)) / d by
        dsimp only [lo, hi] at hh
        rw [add_div, sub_div, add_div]
        linarith)
      exact_mod_cast h
    exact ⟨by simpa only [neg_neg] using neg_le_neg ((Int.le_ediv_iff_mul_le hd).mpr hneg),
      (Int.le_ediv_iff_mul_le hd).mpr hpos⟩
  obtain ⟨n, hn⟩ := certificate k hbox hk
  have hscale (j : Fin 3) : ((d * k j : ℤ) : ℝ) / d = k j := by
    push_cast
    field_simp
  simpa only [hscale] using integerClearance_plane n v w (fun j => d * k j) hd hεv hεw hn


/-- Check a per-shift witness table. A missing or zero direction rejects
the certificate. The only omitted shift is zero for a self-pair. -/
def checkClearancePair (v w : Fin 4 → Fin 3 → ℤ) (d budget : ℤ) (same : Bool)
    (axes : List ((Fin 3 → ℤ) × (Fin 3 → ℤ))) : Bool :=
  decide (0 < d ∧ 0 ≤ budget ∧ ∀ k ∈ clearanceShiftBox v w d budget,
    (same = true ∧ k = 0) ∨
      (axes.find? (fun entry => entry.1 == k)).any
        (fun entry => integerClearance entry.2 v w
          (integerDot entry.2 (fun j => d * k j)) budget) = true)

example : checkClearancePair (fun _ => ![0, 0, 0]) (fun _ => ![0, 0, 0])
    10 0 true [] = true := by decide
example : checkClearancePair (fun _ => ![0, 0, 0]) (fun _ => ![0, 0, 0])
    10 0 false [] = false := by decide
example : checkClearancePair (fun _ => ![0, 0, 0]) (fun _ => ![0, 0, 0])
    0 0 true [] = false := by decide
example : checkClearancePair (fun _ => ![0, 0, 0]) (fun _ => ![12, 0, 0])
    10 2 false [(![-1, 0, 0], ![1, 0, 0])] = true := by decide
example : checkClearancePair (fun _ => ![0, 0, 0]) (fun _ => ![12, 0, 0])
    10 3 false [(![-1, 0, 0], ![1, 0, 0])] = false := by decide

theorem disjoint_interiors_of_checkClearancePair {m : ℕ}
    (C : (Fin 3 → ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ))
    (v : Fin m → Fin 4 → Fin 3 → ℤ) (u : Fin m → Fin 4 → Fin 3 → ℝ)
    (i j : Fin m) {d ε : ℤ} (hd : 0 < d) (hε : 0 ≤ ε)
    (hδ : ∀ i a r, |u i a r - (v i a r : ℝ) / d| ≤ (ε : ℝ) / d)
    (axes : List ((Fin 3 → ℤ) × (Fin 3 → ℤ)))
    (checked : checkClearancePair (v i) (v j) d (ε + ε) (decide (i = j)) axes = true)
    (k : Fin 3 → ℤ) (hk : i ≠ j ∨ k ≠ 0) :
    Disjoint (interior (convexHull ℝ (range (fun a => C.symm (u i a)))))
      (interior (convexHull ℝ (range (fun a => C.symm (u j a) +
        C.symm (fun r => (k r : ℝ)))))) := by
  apply disjoint_interiors_of_integer_clearance C (v i) (v j) (u i) (u j)
    (fun k => i ≠ j ∨ k ≠ 0) hd hε hε (hδ i) (hδ j) _ k hk
  intro s hs hrequired
  obtain hself | haxis := (of_decide_eq_true checked).2.2 s hs
  · have hij : i = j := of_decide_eq_true hself.1
    exact (hrequired.elim (fun h => h hij) (fun h => h hself.2)).elim
  · cases hh : axes.find? (fun entry => entry.1 == s) with
    | none => simp [hh] at haxis
    | some entry => exact ⟨entry.2, by simpa [hh] using haxis⟩


/-- Check the one-unit quantization bound with an integer comparison,
avoiding kernel evaluation of rational division. -/
theorem rational_quantization_bound {n m z d : ℤ}
    (hm : 0 < m) (hd : 0 < d) (h : |n * d - z * m| ≤ m) :
    |(n : ℚ) / m - (z : ℚ) / d| ≤ (1 : ℚ) / d := by
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  have hQ : |(n : ℚ) * d - z * m| ≤ (m : ℚ) := by exact_mod_cast h
  rw [div_sub_div _ _ hmQ.ne' hdQ.ne', mul_comm (m : ℚ) (z : ℚ),
    abs_div, abs_of_pos (mul_pos hmQ hdQ)]
  calc
    _ ≤ (m : ℚ) / ((m : ℚ) * d) := div_le_div_of_nonneg_right hQ (mul_pos hmQ hdQ).le
    _ = (1 : ℚ) / d := by field_simp


/-- Transfer a coordinate tolerance to a quantized reference. The
quantization error uses part of the certified budget. -/
theorem clearance_of_quantized_coordinate (x : ℝ) (q : ℚ) (z d ε : ℤ)
    (hq : |q - (z : ℚ) / d| ≤ (1 : ℚ) / d)
    (hx : |x - (q : ℝ)| ≤ ((ε : ℝ) - 1) / d) :
    |x - (z : ℝ) / d| ≤ (ε : ℝ) / d := by
  have hqR : |(q : ℝ) - (z : ℝ) / d| ≤ (1 : ℝ) / d := by exact_mod_cast hq
  rw [show x - (z : ℝ) / d = (x - q) + ((q : ℝ) - z / d) by ring]
  calc
    _ ≤ |x - (q : ℝ)| + |(q : ℝ) - z / d| := abs_add_le _ _
    _ ≤ ((ε : ℝ) - 1) / d + 1 / d := add_le_add hx hqR
    _ = (ε : ℝ) / d := by rw [← add_div, sub_add_cancel]


end TetrahedronPacking
