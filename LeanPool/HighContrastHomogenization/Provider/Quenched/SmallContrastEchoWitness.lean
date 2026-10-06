/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSharpLineAtJb
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRecursionAssembly

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastEchoWitness

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The echo witness: the construction recursion admits a staircase solution

gate branch (c).  The two-component scheduler's below-range
echo re-excites, and the certificate is stronger than an envelope-class
kill: the construction's hypothesis set — the recursion at the preserved-lag
anchor `shiftedBaseIndex ns` available from `ns`, the a-priori floor, the
origin initial datum (the stated condition), antitonicity, and a source that
still exceeds the floor on the pre-base block — **admits an explicit
solution**, the echo witness, whose value on the `j`-th octave of the inverse
anchor orbit is the tower `echoTower (j+1) = A^(2^(j+1)-1)·δ₀^(2^(j+1))`.

The octaves stretch geometrically (`echoBoundary (j+1) − ns` is at least
`(4/3)^(j+1)` times the burn-in `m₀+1−ns`), so at the fixed octave `j₀`
with `(D+1)·3^(j₀) ≤ 4^(j₀)` the witness value is a law-free positive
constant while any target `M·3^(−mu·(n−T₀))` with `T₀ ≤ ns + D·(m₀+1−ns)`
is smaller once the burn-in is large, with the smallness threshold made
explicit by the logarithmic echo gap.  Hence
NO method consuming only the construction hypotheses — the late-start/original-
anchor two-component scheduler included — can conclude a law-free rate at
a linear threshold.  The first echo damps in magnitude (`δ₀ → A·δ₀²`),
exactly as the scheduler's design intuited; the tower records that the
demand at the octaves outruns the damping against any geometric target.
-/

namespace HCPolySupport.HighContrast.Quenched

noncomputable section

/-- The tower of levels: each octave squares the previous level. -/
@[expose]
def echoTower (A d0 : ℝ) : ℕ → ℝ
  | 0 => d0
  | k + 1 => A * echoTower A d0 k ^ 2

/-! ## Boundary arithmetic -/

/-! ## Index computation -/

/-! ## Tower facts -/

theorem echoTower_pos {A d0 : ℝ} (hA : 1 ≤ A) (hd0 : 0 < d0) :
    ∀ k, 0 < echoTower A d0 k := by
  intro k
  induction k with
  | zero => exact hd0
  | succ k ih =>
      show 0 < A * echoTower A d0 k ^ 2
      have hA0 : (0 : ℝ) < A := lt_of_lt_of_le one_pos hA
      positivity

theorem echoTower_le_floor {A d0 : ℝ} (hA : 1 ≤ A) (hd0 : 0 < d0)
    (hAd : A * d0 ≤ 1) : ∀ k, echoTower A d0 k ≤ d0 := by
  intro k
  induction k with
  | zero => exact le_refl d0
  | succ k ih =>
      show A * echoTower A d0 k ^ 2 ≤ d0
      have hpos := echoTower_pos hA hd0 k
      nlinarith only [ih, hpos, hAd, hd0]

/-! ## The witness satisfies every construction hypothesis -/

/-! ## The kill -/

end

end HCPolySupport.HighContrast.Quenched
