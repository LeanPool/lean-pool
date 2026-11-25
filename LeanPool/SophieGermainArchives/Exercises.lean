/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.SophieGermainArchives.Fr9118
public import LeanPool.SophieGermainArchives.Mechanics.Fr9115Elasticity
public import LeanPool.SophieGermainArchives.NumberTheory.Fr9115Arithmetic
public import Mathlib.Algebra.Ring.Identities
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The Sophie Germain chapter of the exercise book

The exercise book `exercises/exercices.fr.tex` of germain-project, section « Sophie Germain
(1776--1831) ». One group of theorems per exercise, in the book's order; each docstring names
the exercise and the question. Physics is
outside Lean: what is proved is the mathematical core (the rational numbers of the sounds, the
comparison of intervals, the unit correction, the solutions of the plate and lamina equations).

* « Les sons de la plaque rectangulaire 9 : 8 » (fr-9115, views 524–533): `plate98_numbers`,
  `plate98_ratios`, `plate98_judgements`. Cents (logarithms) are not formalised; each judgement is
  proved as the equivalent comparison of two ratios.
* « La cire sur les bords » (fr-9115, views 416, 539–546): `wax_dose`, `wax_unit_correction`,
  `wax_one_side`, `wax_two_adjacent`, `wax_two_opposite`, `wax_lamina`. The rule « a dose of wax is
  worth a strip of plate of the same weight » is physics, assumed.
* « L'équation de la plaque s'abaisse au second degré » (fr-9115, views 399–409, 469–485):
  `plate_lowered`, `plate_split`, `plate_square_mode`, `plate_square_sound`, `n15_eq`, `n15_lap`,
  `n15_diagonals`, `n15_thirds`, `cos_sq_range`, `n15_medians`.
* « La lame tenue en son milieu : la seconde solution d'Euler » (fr-9115, views 214, 322):
  `lamina_first_family`, `lamina_objection`, `lamina_second_family`.
* « p⁴ + 4, p⁴ + q⁴ et les nombres de Fermat » (fr-9118, views 91–93): `p4_plus_four_leaf`,
  `p4_plus_four_factor`, `p4_plus_four_prime_iff`, `p4_plus_four_pairs`, `fermat_as_p4_plus_q4`,
  `x_sq_sub_two_y_sq`.
* « Le nombre 2 et les formes 8k ± 3 ; une extension fausse » (fr-9115, views 704, 720–723):
  `two_method_divisors`, `two_method`, `two_method_checks`, `two_method_gaps`, `four_n_two`,
  `false_extension`.
* « Les nombres premiers de Fermat : 3, 5, 7 et « cela est faux » » (fr-9115, views 729–730):
  `fermat_primes_mod`, `fermat_primes_residues`, `fermat_primes_roots`, `twelve_n_five`.
* « Le manuscrit C : deux cas et trois lacunes » (fr-9115, views 708–710): `manuscriptC_case_one`,
  `manuscriptC_trivial`, `manuscriptC_odd`, `manuscriptC_Phi`, `manuscriptC_inequalities`,
  `manuscriptC_n_two`, `manuscriptC_fermat_four`.

Not formalised: logarithms and cents, the acoustics of the experiments; the numerical roots of
`tan x = tanh x`; Darmon–Merel and Wiles; Fermat's theorem on `X⁴ − Y⁴ = W²`, which the exercise
admits, is a hypothesis of `manuscriptC_n_two`.
-/

@[expose] public section

namespace LeanPool.SophieGermainArchives.Exercises

open Real

/-! ## « Les sons de la plaque rectangulaire 9 : 8 » -/

/-- Germain's number `N = (64T² + 81L²)/64` of the figure `T|L`. -/
def N98 (T L : ℚ) : ℚ := (64 * T ^ 2 + 81 * L ^ 2) / 64

/-- **Les sons de la plaque rectangulaire 9 : 8**, question 1. `N` is `81 (T²/9² + L²/8²)`, and
its six values. -/
theorem plate98_numbers :
    (∀ T L : ℚ, 81 * (T ^ 2 / 9 ^ 2 + L ^ 2 / 8 ^ 2) = N98 T L) ∧
    N98 2 2 = 145 / 16 ∧ N98 2 3 = 985 / 64 ∧ N98 3 3 = 1305 / 64 ∧ N98 4 3 = 1753 / 64 ∧
    N98 5 5 = 3625 / 64 ∧ N98 6 2 = 657 / 16 := by
  refine ⟨fun T L => by unfold N98; ring, ?_⟩
  norm_num [N98]

/-- **Les sons de la plaque rectangulaire 9 : 8**, question 2. The heard interval divided by the
theoretical ratio `R = N/8`, for `2|3`, `3|3`, `4|3`, `5|5`, `6|2`. -/
theorem plate98_ratios :
    (15 / 8) / (N98 2 3 / 8) = 192 / 197 ∧ (8 / 3) / (N98 3 3 / 8) = 4096 / 3915 ∧
    (32 / 9) / (N98 4 3 / 8) = 16384 / 15777 ∧ 8 / (N98 5 5 / 8) = 4096 / 3625 ∧
    (50 / 9) / (N98 6 2 / 8) = 6400 / 5913 := by
  norm_num [N98]

/-- **Les sons de la plaque rectangulaire 9 : 8**, questions 3 and 4, as comparisons of ratios
(minor semitone `25/24`, major semitone `16/15`, major tone `9/8`). `2|2` exceeds `9/8` by
`145/144`, less than a minor semitone; `3|3` exceeds a minor semitone, against the leaf, whose
written check compares a ratio below `1`; `4|3` is under a minor semitone, against the leaf;
`5|5` exceeds a major tone; `6|2`, taken at `50/9`, exceeds a major semitone. So two cases, not
one, pass the half-tone. -/
theorem plate98_judgements :
    (N98 2 2 / 8) / (9 / 8) = 145 / 144 ∧ (1 : ℚ) < 145 / 144 ∧ (145 / 144 : ℚ) < 25 / 24 ∧
    (25 / 24 : ℚ) < 4096 / 3915 ∧ (3 * 1305 / (8 * 512) : ℚ) < 1 ∧
    (1 : ℚ) < 16384 / 15777 ∧ (16384 / 15777 : ℚ) < 25 / 24 ∧
    (9 / 8 : ℚ) < 4096 / 3625 ∧ (16 / 15 : ℚ) < 6400 / 5913 := by
  norm_num [N98]

/-! ## « La cire sur les bords : une erreur d'unité et sa correction » -/

/-- **La cire sur les bords**, question 1. The plate weighs `594` grains, its eighth `74.25`; a dose
weighs `74` grains; an eighth of `106` mm is `13.25` mm. -/
theorem wax_dose :
    (576 + 18 : ℚ) = 594 ∧ (594 : ℚ) / 8 = 74.25 ∧ (72 + 2 : ℚ) = 74 ∧ (106 : ℚ) / 8 = 13.25 := by
  norm_num

/-- **La cire sur les bords**, question 2, the unit correction of view 416. The ratio of the
sound of the square of side `n` to that of the rectangle `N × n`, both measured in the same unit,
is `2N²/(N² + n²)`; the leaf's `(N² + n²)/(2n²)` is `(N/n)²` divided by it, the two numbers being
referred to different sides. -/
theorem wax_unit_correction {N n : ℚ} (hN : N ≠ 0) (hn : n ≠ 0) :
    (1 / n ^ 2 + 1 / n ^ 2) / (1 / N ^ 2 + 1 / n ^ 2) = 2 * N ^ 2 / (N ^ 2 + n ^ 2) ∧
      (N ^ 2 + n ^ 2) / (2 * n ^ 2) = (N / n) ^ 2 / (2 * N ^ 2 / (N ^ 2 + n ^ 2)) := by
  have h : N ^ 2 + n ^ 2 ≠ 0 := by positivity
  constructor
  · field_simp
    ring
  · field_simp

/-- **La cire sur les bords**, question 2, numbers: `N = 9`, `n = 8`. The leaf's `145/128` and the
corrected `162/145` lie on either side of the major tone `9/8`, the corrected one above the
minor tone `10/9`. -/
theorem wax_one_side :
    (9 ^ 2 + 8 ^ 2 : ℚ) / (2 * 8 ^ 2) = 145 / 128 ∧ (2 * 9 ^ 2 : ℚ) / (9 ^ 2 + 8 ^ 2) = 162 / 145 ∧
      (10 / 9 : ℚ) < 162 / 145 ∧ (162 / 145 : ℚ) < 9 / 8 ∧ (9 / 8 : ℚ) < 145 / 128 := by
  norm_num

/-- **La cire sur les bords**, question 3. Two squares of sides `9` and `8`: the interval is
`81/64`, two major tones. -/
theorem wax_two_adjacent :
    ((2 : ℚ) / 8 ^ 2) / (2 / 9 ^ 2) = 81 / 64 ∧ (9 / 8 : ℚ) ^ 2 = 81 / 64 := by
  norm_num

/-- **La cire sur les bords**, question 4. Rectangle `10 × 8`: the corrected interval `50/41` is
below two major tones, the leaf's `41/32` above; with the lengths `132` and `106` mm the
corrected value is still below. -/
theorem wax_two_opposite :
    (2 / 8 ^ 2 : ℚ) / (1 / 10 ^ 2 + 1 / 8 ^ 2) = 50 / 41 ∧
      (10 ^ 2 + 8 ^ 2 : ℚ) / (2 * 8 ^ 2) = 41 / 32 ∧
      (50 / 41 : ℚ) < 81 / 64 ∧ (81 / 64 : ℚ) < 41 / 32 ∧
      (2 * 132 ^ 2 : ℚ) / (132 ^ 2 + 106 ^ 2) < 81 / 64 := by
  norm_num

/-- **La cire sur les bords**, question 5. The lamina weighs `300` grains, the wax `75`, a quarter,
worth `50` mm; the fictitious lamina of `250` mm has its lines at `62.5` and `187.5` mm, that
is `12.5` mm from the loaded end, `125` mm apart and `62.5` mm from the other end. -/
theorem wax_lamina :
    (4 * 72 + 12 : ℚ) = 300 ∧ (72 + 3 : ℚ) = 300 / 4 ∧ (200 : ℚ) / 4 = 50 ∧
      (250 : ℚ) / 4 - 50 = 12.5 ∧ (3 * 250 : ℚ) / 4 - 250 / 4 = 125 ∧
      (250 : ℚ) - 3 * 250 / 4 = 62.5 ∧ (12 + 121 + 61 : ℚ) = 194 := by
  norm_num

/-! ## « L'équation de la plaque s'abaisse au second degré » -/

open Fr9115Elasticity in
/-- **L'équation de la plaque s'abaisse au second degré**, question 1, first half: a solution of
`h²ΔZ = ±Z` solves `h⁴Δ²Z = Z` (`Δ` any linear operator). -/
theorem plate_lowered {V : Type*} [AddCommGroup V] [Module ℝ V] (L : V →ₗ[ℝ] V) (h : ℝ) (z : V)
    (hz : h ^ 2 • L z = z ∨ h ^ 2 • L z = -z) : h ^ 4 • L (L z) = z :=
  factor_B_left L h z hz

open Fr9115Elasticity in
/-- **L'équation de la plaque s'abaisse au second degré**, question 1, second half: every solution
of (B) is `Z' + Z''` with `h²ΔZ' = Z'` and `h²ΔZ'' = -Z''`. -/
theorem plate_split {V : Type*} [AddCommGroup V] [Module ℝ V] (L : V →ₗ[ℝ] V) (h : ℝ) (z : V)
    (hz : h ^ 4 • L (L z) = z) :
    ∃ z' z'' : V, z = z' + z'' ∧ h ^ 2 • L z' = z' ∧ h ^ 2 • L z'' = -z'' :=
  let H := factor_B_split L h z hz
  ⟨_, _, H.1, H.2.1, H.2.2⟩

open Fr9115Elasticity in
/-- **L'équation de la plaque s'abaisse au second degré**, question 2: `sin(nπx/A) sin(mπy/A)` has
`ΔZ = -(α² + β²)Z`, `Δ²Z = (α² + β²)²Z`, and vanishes on the four sides of the square. -/
theorem plate_square_mode (n m : ℤ) {A : ℝ} (hA : A ≠ 0) :
    lap (fun x y => sin (π * n / A * x) * sin (π * m / A * y)) =
        (fun x y => -((π * n / A) ^ 2 + (π * m / A) ^ 2) *
          (sin (π * n / A * x) * sin (π * m / A * y))) ∧
      lap (lap (fun x y => sin (π * n / A * x) * sin (π * m / A * y))) =
        (fun x y => ((π * n / A) ^ 2 + (π * m / A) ^ 2) ^ 2 *
          (sin (π * n / A * x) * sin (π * m / A * y))) ∧
      ∀ x y : ℝ, sin (π * n / A * 0) * sin (π * m / A * y) = 0 ∧
        sin (π * n / A * A) * sin (π * m / A * y) = 0 ∧
        sin (π * n / A * x) * sin (π * m / A * 0) = 0 ∧
        sin (π * n / A * x) * sin (π * m / A * A) = 0 :=
  ⟨(plate_D _ _).1, (plate_D _ _).2, plate_D_boundary n m hA⟩

open Fr9115Elasticity in
/-- **L'équation de la plaque s'abaisse au second degré**, question 2, the sound: (B) holds when
`Kbτ²(α² + β²)² = 1`, and then `√(1/K) = π²(m² + n²)τ√b/A²`. -/
theorem plate_square_sound {K b τ A n m : ℝ} (hτ : 0 < τ) (hA : A ≠ 0)
    (hK : K * b * τ ^ 2 * ((π * n / A) ^ 2 + (π * m / A) ^ 2) ^ 2 = 1) :
    √(1 / K) = π ^ 2 * (m ^ 2 + n ^ 2) * τ * √b / A ^ 2 := by
  have h := plate_D_sound hτ hA hK
  have hπ := pi_ne_zero
  rw [div_eq_iff hπ] at h
  rw [h]; field_simp

/-- `sin 3u = sin u (4 cos² u − 1)`. -/
lemma sin_three_mul_eq (u : ℝ) : sin (3 * u) = sin u * (4 * cos u ^ 2 - 1) := by
  rw [sin_three_mul]; linear_combination (-4 * sin u) * sin_sq_add_cos_sq u

/-- Germain's `Z` of N° 15, in `u = πx/A`, `v = πy/A`. -/
noncomputable def Z15 (β β' u v : ℝ) : ℝ :=
  sin u * sin v * (β * cos u ^ 2 + β' * cos v ^ 2 - (β + β') / 4)

/-- **L'équation de la plaque s'abaisse au second degré**, question 3, the identity:
`Z = (β/4) sin 3u sin v + (β'/4) sin u sin 3v`. -/
theorem n15_eq (β β' u v : ℝ) :
    Z15 β β' u v = β / 4 * (sin (3 * u) * sin v) + β' / 4 * (sin u * sin (3 * v)) := by
  rw [Z15, sin_three_mul_eq, sin_three_mul_eq]; ring

open Fr9115Elasticity in
/-- The Laplacian of a sum of two products. -/
theorem lap_prod_add (F G F₂ G₂ F' G' F'' G'' F₂' G₂' F₂'' G₂'' : ℝ → ℝ)
    (hF : ∀ x, HasDerivAt F (F' x) x) (hF' : ∀ x, HasDerivAt F' (F'' x) x)
    (hG : ∀ y, HasDerivAt G (G' y) y) (hG' : ∀ y, HasDerivAt G' (G'' y) y)
    (hF₂ : ∀ x, HasDerivAt F₂ (F₂' x) x) (hF₂' : ∀ x, HasDerivAt F₂' (F₂'' x) x)
    (hG₂ : ∀ y, HasDerivAt G₂ (G₂' y) y) (hG₂' : ∀ y, HasDerivAt G₂' (G₂'' y) y) :
    lap (fun x y => F x * G y + F₂ x * G₂ y) =
      fun x y => F'' x * G y + F x * G'' y + (F₂'' x * G₂ y + F₂ x * G₂'' y) := by
  funext x y
  have h1 : (fun x' => deriv (fun x'' => F x'' * G y + F₂ x'' * G₂ y) x') =
      fun x' => F' x' * G y + F₂' x' * G₂ y :=
    funext fun x' => (((hF x').mul_const (G y)).add ((hF₂ x').mul_const (G₂ y))).deriv
  have h2 : (fun y' => deriv (fun y'' => F x * G y'' + F₂ x * G₂ y'') y') =
      fun y' => F x * G' y' + F₂ x * G₂' y' :=
    funext fun y' => (((hG y').const_mul (F x)).add ((hG₂ y').const_mul (F₂ x))).deriv
  change deriv (fun x' => deriv (fun x'' => F x'' * G y + F₂ x'' * G₂ y) x') x +
    deriv (fun y' => deriv (fun y'' => F x * G y'' + F₂ x * G₂ y'') y') y = _
  rw [h1, h2,
    show deriv (fun x' => F' x' * G y + F₂' x' * G₂ y) x = F'' x * G y + F₂'' x * G₂ y from
      (((hF' x).mul_const (G y)).add ((hF₂' x).mul_const (G₂ y))).deriv,
    show deriv (fun y' => F x * G' y' + F₂ x * G₂' y') y = F x * G'' y + F₂ x * G₂'' y from
      (((hG' y).const_mul (F x)).add ((hG₂' y).const_mul (F₂ x))).deriv]
  ring

open Fr9115Elasticity in
/-- The two modes `(3, 1)` and `(1, 3)` with coefficients `c₁`, `c₂`, in `x`, `y`, `a = π/A`. -/
lemma lap_three_one (a c₁ c₂ : ℝ) :
    lap (fun x y => c₁ * sin (3 * a * x) * sin (a * y) + c₂ * sin (a * x) * sin (3 * a * y)) =
      fun x y => -(10 * a ^ 2) *
        (c₁ * sin (3 * a * x) * sin (a * y) + c₂ * sin (a * x) * sin (3 * a * y)) := by
  have hz : (fun x y => c₁ * sin (3 * a * x) * sin (a * y) + c₂ * sin (a * x) * sin (3 * a * y)) =
      fun x y => modeY (3 * a) 0 0 0 c₁ x * modeY a 0 0 0 1 y +
        modeY a 0 0 0 c₂ x * modeY (3 * a) 0 0 0 1 y := by
    funext x y; simp only [modeY]; ring
  rw [hz, lap_prod_add _ _ _ _ _ _ _ _ _ _ _ _
    (hasDerivAt_modeY _ _ _ _ _) (hasDerivAt_modeY _ _ _ _ _)
    (hasDerivAt_modeY _ _ _ _ _) (hasDerivAt_modeY _ _ _ _ _)
    (hasDerivAt_modeY _ _ _ _ _) (hasDerivAt_modeY _ _ _ _ _)
    (hasDerivAt_modeY _ _ _ _ _) (hasDerivAt_modeY _ _ _ _ _)]
  funext x y; simp only [modeY]; ring

open Fr9115Elasticity in
/-- **L'équation de la plaque s'abaisse au second degré**, question 3: with `a = π/A`, the `Z` of
N° 15 has `ΔZ = -10a²Z` and `Δ²Z = 100a⁴Z`; it satisfies (B) when `Kbτ² · 100a⁴ = 1`, and its
sound is that of `m² + n² = 10`. -/
theorem n15_lap (a β β' : ℝ) :
    lap (fun x y => Z15 β β' (a * x) (a * y)) =
        (fun x y => -(10 * a ^ 2) * Z15 β β' (a * x) (a * y)) ∧
      lap (lap (fun x y => Z15 β β' (a * x) (a * y))) =
        (fun x y => 100 * a ^ 4 * Z15 β β' (a * x) (a * y)) := by
  have hz : (fun x y => Z15 β β' (a * x) (a * y)) =
      fun x y =>
        β / 4 * sin (3 * a * x) * sin (a * y) + β' / 4 * sin (a * x) * sin (3 * a * y) := by
    funext x y; rw [n15_eq]; ring_nf
  have h1 := lap_three_one a (β / 4) (β' / 4)
  have e : ∀ x y, Z15 β β' (a * x) (a * y) =
      β / 4 * sin (3 * a * x) * sin (a * y) + β' / 4 * sin (a * x) * sin (3 * a * y) :=
    fun x y => congrFun (congrFun hz x) y
  refine ⟨by rw [hz, h1]; funext x y; rw [e], ?_⟩
  have hz' : (fun x y => -(10 * a ^ 2) *
        (β / 4 * sin (3 * a * x) * sin (a * y) + β' / 4 * sin (a * x) * sin (3 * a * y))) =
      fun x y => (-(10 * a ^ 2) * (β / 4)) * sin (3 * a * x) * sin (a * y) +
        (-(10 * a ^ 2) * (β' / 4)) * sin (a * x) * sin (3 * a * y) := by
    funext x y; ring
  rw [hz, h1, hz', lap_three_one]
  funext x y; rw [e]; ring

/-- **L'équation de la plaque s'abaisse au second degré**, question 4: for `β' = -β`,
`Z = β sin u sin v (cos u − cos v)(cos u + cos v)`, which vanishes on both diagonals
`v = u` and `v = π − u`. -/
theorem n15_diagonals (β u v : ℝ) :
    Z15 β (-β) u v = β * sin u * sin v * (cos u - cos v) * (cos u + cos v) ∧
      Z15 β (-β) u u = 0 ∧ Z15 β (-β) u (π - u) = 0 := by
  refine ⟨by unfold Z15; ring, by unfold Z15; ring, ?_⟩
  unfold Z15; rw [cos_pi_sub]; ring

/-- **L'équation de la plaque s'abaisse au second degré**, question 4: for `β' = 0`,
`Z = (β/4) sin 3u sin v`, zero on `u = π/3` and `u = 2π/3`. -/
theorem n15_thirds (β u v : ℝ) :
    Z15 β 0 u v = β / 4 * sin (3 * u) * sin v ∧ Z15 β 0 (π / 3) v = 0 ∧
      Z15 β 0 (2 * π / 3) v = 0 := by
  have e : ∀ u, Z15 β 0 u v = β / 4 * sin (3 * u) * sin v := fun u => by rw [n15_eq]; ring
  refine ⟨e u, ?_, ?_⟩
  · rw [e, show 3 * (π / 3) = π by ring, sin_pi]; ring
  · rw [e, show 3 * (2 * π / 3) = 2 * π by ring, sin_two_pi]; ring

/-- `cos² u` takes exactly the values of `[0, 1]`. -/
theorem cos_sq_range (c : ℝ) : (∃ u, cos u ^ 2 = c) ↔ 0 ≤ c ∧ c ≤ 1 := by
  constructor
  · rintro ⟨u, rfl⟩; exact ⟨sq_nonneg _, cos_sq_le_one u⟩
  · rintro ⟨h0, h1⟩
    refine ⟨arccos √c, ?_⟩
    have hs : √c ≤ 1 := by rw [sqrt_le_one]; exact h1
    rw [cos_arccos (by linarith [sqrt_nonneg c]) hs, sq_sqrt h0]

/-- **L'équation de la plaque s'abaisse au second degré**, question 5: with `r = β'/β ≠ 0`, both
`(1 + r)/4` and `(1 + r)/(4r)` lie in `[0, 1]` (that is, by `cos_sq_range`, both medians carry
a point of the nodal line) iff `1/3 ≤ r ≤ 3` or `r = -1`. -/
theorem n15_medians {r : ℝ} (hr : r ≠ 0) :
    ((0 ≤ (1 + r) / 4 ∧ (1 + r) / 4 ≤ 1) ∧ (0 ≤ (1 + r) / (4 * r) ∧ (1 + r) / (4 * r) ≤ 1)) ↔
      (1 / 3 ≤ r ∧ r ≤ 3) ∨ r = -1 := by
  rcases lt_or_gt_of_ne hr with hneg | hpos
  · have h4 : 4 * r < 0 := by linarith
    rw [le_div_iff_of_neg h4, div_le_iff_of_neg h4]
    constructor
    · rintro ⟨⟨h1, _⟩, h3, _⟩
      right; linarith
    · rintro (⟨h1, _⟩ | rfl)
      · linarith
      · norm_num
  · have h4 : 0 < 4 * r := by linarith
    rw [le_div_iff₀ h4, div_le_iff₀ h4]
    constructor
    · rintro ⟨⟨_, h2⟩, _, h4'⟩
      left; constructor <;> linarith
    · rintro (⟨h1, h2⟩ | rfl)
      · refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
      · linarith

/-! ## « La lame tenue en son milieu : la seconde solution d'Euler » -/

open Fr9115Elasticity in
/-- **La lame tenue en son milieu**, question 1: `sin 2kπu` on both halves satisfies the eight
conditions (supported ends, `Y = 0` at the stylet, slope and curvature continuous), with no
force at the stylet (same function on both sides). -/
theorem lamina_first_family (k : ℤ) (hk : k ≠ 0) :
    SupportedStylet (1 / 2) (modeY (2 * k * π) 0 0 0 1) (modeY (2 * k * π) 0 0 0 1) :=
  (first_family_sign k hk).1

open Fr9115Elasticity in
/-- **La lame tenue en son milieu**, question 2, the leaf's computation: if `tan x = tanh x`
(written `sin x cosh x = cos x sinh x`, `x = ω/2`), then `sin ω cosh ω = sinh ω`, and
`sin ω = 0` forces `ω = 0`. The computation is right; the conclusion drawn from it is not
(`lamina_second_family`). -/
theorem lamina_objection (x : ℝ) (h : sin x * cosh x = cos x * sinh x) :
    sin (2 * x) * cosh (2 * x) = sinh (2 * x) ∧ (sin (2 * x) = 0 → x = 0) :=
  ⟨objection_sin_eq_tanh x h, objection_sin_zero x h⟩

open Fr9115Elasticity in
/-- **La lame tenue en son milieu**, question 3: for every root `ω > 0` of `tan(ω/2) = tanh(ω/2)`,
`Y₁(u) = sinh ωu / sinh(ω/2) − sin ωu / sin(ω/2)` and its mirror image satisfy the eight
conditions, are not zero, and `Y'''` jumps at the stylet: Euler's second solution is a genuine
mode, in which the stylet exerts a force. -/
theorem lamina_second_family {ω : ℝ} (hω : 0 < ω)
    (h : sin (ω / 2) * cosh (ω / 2) = cos (ω / 2) * sinh (ω / 2)) :
    SupportedStylet (1 / 2) (secondY₁ ω) (secondY₂ ω) ∧ secondY₁ ω ≠ 0 ∧
      iteratedDeriv 3 (secondY₁ ω) (1 / 2) ≠ iteratedDeriv 3 (secondY₂ ω) (1 / 2) :=
  second_family_is_mode hω h

/-! ## « p⁴ + 4, p⁴ + q⁴ et les nombres de Fermat » -/

/-- **p⁴ + 4, p⁴ + q⁴ et les nombres de Fermat**, question 1: the identities of the leaf. -/
theorem p4_plus_four_leaf (p q : ℤ) :
    p ^ 4 + 4 = (p ^ 2 - 2) ^ 2 + 4 * p ^ 2 ∧
      p ^ 4 + q ^ 4 = (p ^ 2 - q ^ 2) ^ 2 + 2 * (p * q) ^ 2 ∧
      p ^ 4 + q ^ 4 = (p ^ 2 + q ^ 2) ^ 2 - 2 * (p * q) ^ 2 :=
  ⟨by ring, Fr9118.p4_add_q4_identities p q⟩

/-- **p⁴ + 4, p⁴ + q⁴ et les nombres de Fermat**, question 2: the factorisation (not on the
leaf). -/
theorem p4_plus_four_factor (a b : ℤ) :
    a ^ 4 + 4 * b ^ 4 = (a ^ 2 + 2 * b ^ 2 - 2 * a * b) * (a ^ 2 + 2 * b ^ 2 + 2 * a * b) := by
  rw [pow_four_add_four_mul_pow_four']
  ring

/-- **p⁴ + 4, p⁴ + q⁴ et les nombres de Fermat**, question 2: `p⁴ + 4` is prime only for `p = 1`. -/
theorem p4_plus_four_prime_iff (p : ℕ) : (p ^ 4 + 4).Prime ↔ p = 1 :=
  Fr9118.p4_add_four_prime_iff p

/-- **p⁴ + 4, p⁴ + q⁴ et les nombres de Fermat**, question 3: the pairs `{p², 2}` and
`{|p² − 2|, 2p}` coincide exactly for `p ≤ 2`; for `p ≥ 1`, at `p = 1` and `p = 2`. -/
theorem p4_plus_four_pairs (p : ℕ) :
    (((p : ℤ) ^ 2 = |(p : ℤ) ^ 2 - 2| ∧ (2 : ℤ) = 2 * p) ∨
      ((p : ℤ) ^ 2 = 2 * p ∧ (2 : ℤ) = |(p : ℤ) ^ 2 - 2|)) ↔ p ≤ 2 :=
  Fr9118.same_pair_iff p

/-- **p⁴ + 4, p⁴ + q⁴ et les nombres de Fermat**, question 4: `2^{2^i} + 1` is `p⁴ + q⁴` for
`i ≥ 2`, and `3`, `5` are not sums of two fourth powers. -/
theorem fermat_as_p4_plus_q4 :
    (∀ i, 2 ≤ i → 2 ^ 2 ^ i + 1 = (2 ^ 2 ^ (i - 2)) ^ 4 + 1 ^ 4) ∧
      ∀ p q : ℕ, p ^ 4 + q ^ 4 ≠ 3 ∧ p ^ 4 + q ^ 4 ≠ 5 :=
  ⟨Fr9118.fermat_number_eq, Fr9118.three_five_not_sum_fourth⟩

/-- **p⁴ + 4, p⁴ + q⁴ et les nombres de Fermat**, question 5: the representation by `x² + 2y²` of
`17` is unique, by `x² − 2y²` it is not, and each representation by `x² − 2y²` gives another. -/
theorem x_sq_sub_two_y_sq :
    (∀ x y : ℕ, x ^ 2 + 2 * y ^ 2 = 17 → x = 3 ∧ y = 2) ∧
      ((17 : ℤ) = 5 ^ 2 - 2 * 2 ^ 2 ∧ (17 : ℤ) = 23 ^ 2 - 2 * 16 ^ 2) ∧
      ∀ x y : ℤ, x ^ 2 - 2 * y ^ 2 = (3 * x + 4 * y) ^ 2 - 2 * (2 * x + 3 * y) ^ 2 :=
  ⟨Fr9118.seventeen_unique, by norm_num, fun x y => by ring⟩

/-! ## « Le nombre 2 et les formes 8k ± 3 ; une extension fausse » -/

/-- **Le nombre 2 et les formes 8k ± 3**, question 1 (for any divisor `m` of `p − 1`, not only a
prime one): `m` is a residue if `m ≡ 1 (mod 4)`, `−m` if `m ≡ 3 (mod 4)`. -/
theorem two_method_divisors {p m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hdvd : m ∣ p - 1) :
    (m % 4 = 1 → IsSquare ((m : ℤ) : ZMod p)) ∧ (m % 4 = 3 → IsSquare ((-(m : ℤ) : ℤ) : ZMod p)) :=
  ⟨fun hm => Fr9115Arithmetic.residue_of_dvd_pred_one hp2 hm hdvd,
    fun hm => Fr9115Arithmetic.neg_residue_of_dvd_pred_three hp2 hm hdvd⟩

/-- **Le nombre 2 et les formes 8k ± 3**, questions 2 and 3: `2` is a non-residue of `p ≡ 3`, a
residue of `p ≡ 7 (mod 8)`, and a residue when `p − 1 = 2^e w`, `w` odd, `e ≥ 3` odd. -/
theorem two_method {p : ℕ} [Fact p.Prime] :
    (p % 8 = 3 → ¬ IsSquare (2 : ZMod p)) ∧ (p % 8 = 7 → IsSquare (2 : ZMod p)) ∧
      ∀ k w : ℕ, Odd w → p = 2 ^ (2 * k + 3) * w + 1 → IsSquare (2 : ZMod p) :=
  ⟨Fr9115Arithmetic.two_nonresidue_of_three_mod_eight,
    Fr9115Arithmetic.two_residue_of_seven_mod_eight,
    fun _ _ hw hp => Fr9115Arithmetic.two_residue_of_odd_two_power hw hp⟩

/-- **Le nombre 2 et les formes 8k ± 3**, question 2, the checks: `2` is not a square mod `11`
and `19`, and `5² ≡ 2 (mod 23)`. -/
theorem two_method_checks :
    ¬ IsSquare (2 : ZMod 11) ∧ ¬ IsSquare (2 : ZMod 19) ∧ (5 : ZMod 23) ^ 2 = 2 := by
  refine ⟨?_, ?_, by decide⟩ <;> unfold IsSquare <;> decide

/-- **Le nombre 2 et les formes 8k ± 3**, question 3: the primes `p ≡ 1 (mod 4)` below `60` are
`5, 13, 17, 29, 37, 41, 53`; the exponent of `2` in `p − 1` is even (`2` or `4`) for all but
`41`, where it is `3`, and the method covers `41`. -/
theorem two_method_gaps :
    (∀ p, p.Prime → p < 60 → p % 4 = 1 → p ∈ ({5, 13, 17, 29, 37, 41, 53} : Finset ℕ)) ∧
      (5 - 1 = 2 ^ 2 * 1 ∧ 13 - 1 = 2 ^ 2 * 3 ∧ 17 - 1 = 2 ^ 4 * 1 ∧ 29 - 1 = 2 ^ 2 * 7 ∧
        37 - 1 = 2 ^ 2 * 9 ∧ 53 - 1 = 2 ^ 2 * 13 ∧ 41 - 1 = 2 ^ 3 * 5) ∧
      IsSquare (2 : ZMod 41) := by
  refine ⟨fun p hp h60 h4 => ?_, by norm_num, ?_⟩
  · interval_cases p <;>
      first | (norm_num at hp; done) | (norm_num at h4; done) | simp
  · have : Fact (Nat.Prime 41) := ⟨by norm_num⟩
    exact Fr9115Arithmetic.two_residue_of_odd_two_power (k := 0) (w := 5) (by decide)
      (by norm_num)

/-- **Le nombre 2 et les formes 8k ± 3**, question 4: every `m ≡ 2 (mod 4)` is a non-residue of
a prime `q ≡ 3 (mod 4)`. -/
theorem four_n_two {m : ℕ} (hm : m % 4 = 2) : ∃ q, q.Prime ∧ q % 4 = 3 ∧ ¬ IsSquare (m : ZMod q) :=
  Fr9115Arithmetic.four_n_two_nonresidue hm

/-- **Le nombre 2 et les formes 8k ± 3**, question 5: `−5`, `−17`, `−21` are residues of every
smaller prime `q ≡ 3 (mod 4)` (the divisors of `21` included, `0` being a square): the
extension of view 720 is false. -/
theorem false_extension :
    (∀ q, q.Prime → q % 4 = 3 → q < 5 → IsSquare (-(5 : ZMod q))) ∧
    (∀ q, q.Prime → q % 4 = 3 → q < 17 → IsSquare (-(17 : ZMod q))) ∧
    (∀ q, q.Prime → q % 4 = 3 → q < 21 → IsSquare (-(21 : ZMod q))) :=
  Fr9115Arithmetic.false_extension

/-! ## « Les nombres premiers de Fermat : 3, 5, 7 et « cela est faux » » -/

/-- **Les nombres premiers de Fermat**, question 1: `F_k ≡ 2 (mod F_j)` for `j < k`; and for
Fermat primes `F_j < F_k`, `F_j` is a residue of `F_k` iff `2` is a residue of `F_j`. -/
theorem fermat_primes_mod {j k : ℕ} (hjk : j < k) :
    Nat.fermatNumber k % Nat.fermatNumber j = 2 ∧
      ((Nat.fermatNumber j).Prime → (Nat.fermatNumber k).Prime →
        (IsSquare ((Nat.fermatNumber j : ℕ) : ZMod (Nat.fermatNumber k)) ↔
          IsSquare (2 : ZMod (Nat.fermatNumber j)))) :=
  ⟨Fr9115Arithmetic.fermatNumber_mod hjk,
    fun hj hk => Fr9115Arithmetic.fermat_residue_iff hjk hj hk⟩

/-- **Les nombres premiers de Fermat**, questions 2 and 3: for a Fermat prime `F_k`, `3` and `7`
are non-residues when `k ≥ 1`, `5` when `k ≥ 2`; but `17` is a residue of `257` and of `65537`,
and `257` of `65537` (« cela est faux »). -/
theorem fermat_primes_residues {k : ℕ} (hk : (Nat.fermatNumber k).Prime) :
    (1 ≤ k → ¬ IsSquare (3 : ZMod (Nat.fermatNumber k))) ∧
      (2 ≤ k → ¬ IsSquare (5 : ZMod (Nat.fermatNumber k))) ∧
      (1 ≤ k → ¬ IsSquare (7 : ZMod (Nat.fermatNumber k))) ∧
      (IsSquare ((17 : ℕ) : ZMod 257) ∧ IsSquare ((17 : ℕ) : ZMod 65537) ∧
        IsSquare ((257 : ℕ) : ZMod 65537)) :=
  ⟨fun h1 => Fr9115Arithmetic.three_nonresidue_fermat h1 hk,
    fun h2 => Fr9115Arithmetic.five_nonresidue_fermat h2 hk,
    fun h1 => Fr9115Arithmetic.seven_nonresidue_fermat h1 hk,
    Fr9115Arithmetic.seventeen_residue⟩

/-- **Les nombres premiers de Fermat**, question 4: every non-residue of a Fermat prime is a
primitive root; so `3` and `7` are primitive roots of every Fermat prime `F_k`, `k ≥ 1`. -/
theorem fermat_primes_roots {k : ℕ} (hk : (Nat.fermatNumber k).Prime) :
    (∀ a : ZMod (Nat.fermatNumber k), ¬ IsSquare a →
        IsPrimitiveRoot a (Nat.fermatNumber k - 1)) ∧
      (1 ≤ k → IsPrimitiveRoot (3 : ZMod (Nat.fermatNumber k)) (Nat.fermatNumber k - 1) ∧
        IsPrimitiveRoot (7 : ZMod (Nat.fermatNumber k)) (Nat.fermatNumber k - 1)) :=
  ⟨fun _ ha => Fr9115Arithmetic.fermat_primitive_root hk ha,
    fun h1 => ⟨Fr9115Arithmetic.three_primitive_root_fermat h1 hk,
      Fr9115Arithmetic.seven_primitive_root_fermat h1 hk⟩⟩

/-- **Les nombres premiers de Fermat**, question 5 (view 729): if `12n + 5` and `3n + 1` are prime,
`3` is a primitive root of `12n + 5`; so for `29` and `53`. -/
theorem twelve_n_five :
    (∀ n : ℕ, (3 * n + 1).Prime → (12 * n + 5).Prime →
      IsPrimitiveRoot (3 : ZMod (12 * n + 5)) (12 * n + 4)) ∧
      IsPrimitiveRoot (3 : ZMod 29) 28 ∧ IsPrimitiveRoot (3 : ZMod 53) 52 :=
  ⟨fun _ hq hp => Fr9115Arithmetic.three_primitive_root hq hp,
    Fr9115Arithmetic.three_primitive_root (n := 2) (by norm_num) (by norm_num),
    Fr9115Arithmetic.three_primitive_root (n := 4) (by norm_num) (by norm_num)⟩

/-! ## « Le manuscrit C : deux cas et trois lacunes » -/

/-- **Le manuscrit C**, question 1: the parametrisation, and two primitive solutions of
`x² + y² = 2z²` with `x² ≠ y²`. -/
theorem manuscriptC_case_one :
    (∀ P Q : ℤ, (P ^ 2 - Q ^ 2 - 2 * P * Q) ^ 2 + (P ^ 2 - Q ^ 2 + 2 * P * Q) ^ 2 =
      2 * (P ^ 2 + Q ^ 2) ^ 2) ∧
      (1 : ℤ) ^ 2 + 7 ^ 2 = 2 * 5 ^ 2 ∧ (7 : ℤ) ^ 2 + 17 ^ 2 = 2 * 13 ^ 2 :=
  ⟨Fr9115Arithmetic.param_identity, Fr9115Arithmetic.manuscriptC_n_one⟩

/-- **Le manuscrit C**, question 2: the statement as written fails at `x = y = z = 1` for every
`n`, and `x^n = x` for `x = ±1` and `n` odd: the conclusion « n = 1 » forgets this case. -/
theorem manuscriptC_trivial (n : ℕ) :
    (¬ ∀ x y z : ℤ, IsCoprime x y → 2 * z ^ (2 * n) ≠ x ^ (2 * n) + y ^ (2 * n)) ∧
      (Odd n → ∀ x : ℤ, (x = 1 ∨ x = -1) → x ^ n = x) :=
  ⟨Fr9115Arithmetic.manuscriptC_not_as_written n,
    fun hn _ hx => Fr9115Arithmetic.trivial_case hn hx⟩

/-- **Le manuscrit C**, question 3: if `x`, `y` are coprime (no hypothesis on `z` is needed) and
`x^{2n} + y^{2n} = 2z^{2n}`, `n ≥ 1`, then `x`, `y`, `z` are odd. -/
theorem manuscriptC_odd {n : ℕ} (hn : 1 ≤ n) {x y z : ℤ} (hxy : IsCoprime x y)
    (h : x ^ (2 * n) + y ^ (2 * n) = 2 * z ^ (2 * n)) : Odd x ∧ Odd y ∧ Odd z :=
  Fr9115Arithmetic.manuscriptC_odd hn hxy h

/-- **Le manuscrit C**, question 4: `x^{2n} + y^{2n} = (x² + y²)Φ`, `Φ ≡ n y^{2n−2}`, a common
divisor of `x² + y²` and `Φ` divides `n`, and for `n = 5`, `x = 1`, `y = 3`, `Φ = 5905` and `5`
divides both. -/
theorem manuscriptC_Phi {n : ℕ} (hn : Odd n) {x y : ℤ} (hxy : IsCoprime x y) :
    x ^ (2 * n) + y ^ (2 * n) = (x ^ 2 + y ^ 2) * Fr9115Arithmetic.Phi n x y ∧
      x ^ 2 + y ^ 2 ∣ Fr9115Arithmetic.Phi n x y - n * y ^ (2 * n - 2) ∧
      (∀ d : ℤ, d ∣ x ^ 2 + y ^ 2 → d ∣ Fr9115Arithmetic.Phi n x y → d ∣ n) ∧
      (Fr9115Arithmetic.Phi 5 1 3 = 5905 ∧ (5 : ℤ) ∣ 1 ^ 2 + 3 ^ 2 ∧
        (5 : ℤ) ∣ Fr9115Arithmetic.Phi 5 1 3) :=
  ⟨Fr9115Arithmetic.factor_Phi hn x y, Fr9115Arithmetic.Phi_modEq hn x y,
    fun _ h1 h2 => Fr9115Arithmetic.dvd_n_of_dvd_both hn hxy h1 h2,
    Fr9115Arithmetic.Phi_counterexample⟩

/-- **Le manuscrit C**, question 5: `2(y² − x²) − (x + y)² = (x + y)(y − 3x)`, and the two
solutions `(∓7, 17)` of `x² + y² = 2·13²` where one inequality of the chain fails. -/
theorem manuscriptC_inequalities :
    (∀ x y : ℤ, 2 * (y ^ 2 - x ^ 2) - (x + y) ^ 2 = (x + y) * (y - 3 * x)) ∧
    ((3 : ℤ) ^ 2 - 2 ^ 2 - 2 * 3 * 2 = -7 ∧ (3 : ℤ) ^ 2 - 2 ^ 2 + 2 * 3 * 2 = 17) ∧
    ((-7 : ℤ) ^ 2 + 17 ^ 2 = 2 * 13 ^ 2 ∧ (-7 + 17 : ℤ) ^ 2 < 2 * (17 ^ 2 - (-7) ^ 2) ∧
      (-7 + 17 : ℤ) ^ 2 < 17 ^ 2) ∧
    ((7 : ℤ) ^ 2 + 17 ^ 2 = 2 * 13 ^ 2 ∧ 2 * ((17 : ℤ) ^ 2 - 7 ^ 2) < (7 + 17) ^ 2) :=
  ⟨Fr9115Arithmetic.inequality_identity, Fr9115Arithmetic.inequality_counterexamples⟩

/-- **Le manuscrit C**, question 6, the case `n = 2`. Fermat's theorem on `X⁴ − Y⁴ = W²`, which
the exercise admits, is the hypothesis `hF`. Then the coprime solutions of `x⁴ + y⁴ = 2z⁴` are
`x² = y² = z² = 1`. -/
theorem manuscriptC_n_two
    (hF : ∀ X Y W : ℤ, X ≠ 0 → Y ≠ 0 → X ^ 4 - Y ^ 4 = W ^ 2 → W = 0)
    {x y z : ℤ} (hxy : IsCoprime x y) (h : x ^ 4 + y ^ 4 = 2 * z ^ 4) :
    x ^ 2 = 1 ∧ y ^ 2 = 1 ∧ z ^ 2 = 1 := by
  obtain ⟨hx, hy, hz⟩ := Fr9115Arithmetic.manuscriptC_odd (n := 2) (by norm_num) hxy
    (by norm_num; exact h)
  have hx0 : x ≠ 0 := by rintro rfl; norm_num at hx
  have hy0 : y ≠ 0 := by rintro rfl; norm_num at hy
  have hz0 : z ≠ 0 := by rintro rfl; norm_num at hz
  obtain ⟨W, hW⟩ : Even (x ^ 4 - y ^ 4) := Odd.sub_odd (hx.pow) (hy.pow)
  have key4 : 4 * ((z ^ 2) ^ 4 - (x * y) ^ 4) = 4 * W ^ 2 := by
    linear_combination (-(2 * z ^ 4 + x ^ 4 + y ^ 4)) * h + (x ^ 4 - y ^ 4 + 2 * W) * hW
  have key : (z ^ 2) ^ 4 - (x * y) ^ 4 = W ^ 2 := by linarith
  have hW0 := hF (z ^ 2) (x * y) W (pow_ne_zero 2 hz0) (mul_ne_zero hx0 hy0) key
  subst hW0
  have hxy4 : x ^ 4 = y ^ 4 := by linarith
  have hx2pos : 0 < x ^ 2 := by positivity
  have hxy2 : x ^ 2 = y ^ 2 := by
    have : (x ^ 2 - y ^ 2) * (x ^ 2 + y ^ 2) = 0 := by linear_combination hxy4
    rcases mul_eq_zero.mp this with h1 | h1
    · linarith
    · nlinarith [sq_nonneg y]
  have hu : IsUnit (x ^ 2) := by
    have hc : IsCoprime (x ^ 2) (y ^ 2) := hxy.pow
    rw [← hxy2] at hc
    exact isCoprime_self.mp hc
  have hx1 : x ^ 2 = 1 := by
    rcases Int.isUnit_iff.mp hu with h1 | h1
    · exact h1
    · nlinarith
  refine ⟨hx1, by rw [← hxy2, hx1], ?_⟩
  have hz4 : (z ^ 2) ^ 2 = 1 := by nlinarith
  have hz2 : 0 < z ^ 2 := by positivity
  nlinarith

/-- **Le manuscrit C**, question 6, the second theorem for `n = 2`: `Z + Y` need not divide
`Z² + Y²` (`4 ∤ 10`), and `Z⁴ = X⁴ + Y⁴` has no solution in nonzero integers (Fermat's
exponent `4`, in mathlib). -/
theorem manuscriptC_fermat_four :
    ¬ ((3 : ℤ) + 1 ∣ 3 ^ 2 + 1 ^ 2) ∧ FermatLastTheoremFor 4 :=
  ⟨Fr9115Arithmetic.even_n_no_factor, fermatLastTheoremFour⟩

end LeanPool.SophieGermainArchives.Exercises
