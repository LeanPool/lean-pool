/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section11b
public import LeanPool.GraphMinor.GM12.Defs
import LeanPool.GraphMinor.GM12.Section2PeriodicHits

/-!
# Joining the original region intervals around the circle

For Case 1 of XII (2.1), page 244, the original curve can be read
as the cyclic concatenation of its region intervals. Interpolate
between the uniform circle parameters and the chosen real interval
parameters. At every joining endpoint the two parameters agree,
except at the last join, where both differ by one period. Thus the
interpolation is a homotopy of closed curves, entirely in the original
curve image. The origin of its real parameter may vary freely.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM07

/-- Concatenating arbitrary consecutive real intervals of one period
is homotopic to the original circle parameterization, with the homotopy
contained in that curve's image. -/
theorem closedCurve_homotopic_to_cyclic_real_pieces
    {S : Type*} [TopologicalSpace S] {φ : C(Circle, S)} {Z : Set S}
    (hφZ : range φ ⊆ Z) {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ)
    (hstep : ∀ i, b i = a (finNext hn i) + if i.val + 1 = n then 1 else 0)
    (γ : Fin n → C(unitInterval, S))
    (hγ : ∀ i t, γ i t = periodicCurve φ (a i + t.val * (b i - a i)))
    (hmatch : ∀ i, γ i 1 = γ (finNext hn i) 0) :
    ClosedCurvesHomotopicIn Z φ (concatLoop hn γ hmatch) := by
  let H : Fin n → C(unitInterval × unitInterval, S) := fun i =>
    ⟨fun p => periodicCurve φ ((1 - p.2.val) * (((i.val : ℝ) + p.1.val) / (n : ℝ)) +
      p.2.val * (a i + p.1.val * (b i - a i))),
      (periodicCurve_continuous φ).comp (by fun_prop)⟩
  have hHZ : ∀ i p, H i p ∈ Z := fun i p => hφZ (mem_range_self _)
  have hH0 : ∀ i t, H i (t, 0) = curvePiece hn φ i t := by
    intro i t
    change periodicCurve φ ((1 - (0 : unitInterval).val) * (((i.val : ℝ) + t.val) / (n : ℝ)) +
      (0 : unitInterval).val * (a i + t.val * (b i - a i))) = _
    simp only [Icc.coe_zero, sub_zero, one_mul, zero_mul, add_zero]
    change φ (Circle.exp (2 * Real.pi * (((i.val : ℝ) + t.val) / (n : ℝ)))) = _
    rw [← mul_div_assoc]
    rfl
  have hH1 : ∀ i t, H i (t, 1) = γ i t := by
    intro i t
    rw [hγ]
    change periodicCurve φ ((1 - (1 : unitInterval).val) * (((i.val : ℝ) + t.val) / (n : ℝ)) +
      (1 : unitInterval).val * (a i + t.val * (b i - a i))) = _
    simp only [Icc.coe_one, sub_self, zero_mul, one_mul, zero_add]
  have hHmatch : ∀ i s, H i (1, s) = H (finNext hn i) (0, s) := by
    intro i s
    change periodicCurve φ ((1 - s.val) * (((i.val : ℝ) + 1) / (n : ℝ)) +
      s.val * (a i + 1 * (b i - a i))) =
      periodicCurve φ ((1 - s.val) * ((((finNext hn i).val : ℝ) + 0) / (n : ℝ)) +
        s.val * (a (finNext hn i) + 0 * (b (finNext hn i) - a (finNext hn i))))
    by_cases hlast : i.val + 1 = n
    · have hnext : (finNext hn i).val = 0 := by simp only [finNext, hlast, Nat.mod_self]
      have hnreal : (i.val : ℝ) + 1 = (n : ℝ) := by exact_mod_cast hlast
      have hnne : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      rw [hnext, Nat.cast_zero, hnreal, div_self hnne, hstep i]
      simp only [hlast, ↓reduceIte]
      calc
        periodicCurve φ _ = periodicCurve φ (s.val * a (finNext hn i) + 1) :=
          congrArg (periodicCurve φ) (by ring)
        _ = periodicCurve φ (s.val * a (finNext hn i)) := periodicCurve_periodic φ _
        _ = periodicCurve φ _ := congrArg (periodicCurve φ) (by ring)
    · have hlt : i.val + 1 < n := lt_of_le_of_ne (Nat.succ_le_of_lt i.isLt) hlast
      have hnext : (finNext hn i).val = i.val + 1 := by simp only [finNext, Nat.mod_eq_of_lt hlt]
      rw [hstep i]
      simp only [hlast, ↓reduceIte]
      rw [hnext, Nat.cast_add, Nat.cast_one]
      congr 1
      ring
  have hh := concatLoop_homotopic hn (curvePiece hn φ) γ (curvePiece_match hn φ) hmatch
    H hHZ hH0 hH1 hHmatch
  rw [concatLoop_curvePiece] at hh
  exact hh

end GraphMinor.GM12
