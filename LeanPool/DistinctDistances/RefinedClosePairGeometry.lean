/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.AnnularClosePairCounting
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Refined close pairs in a thin planar annulus

Formalizes the geometric inputs of Steps L0, L1 and Ant of
`docs/results/refined-constant-gain-2026-10-19.md`.

* Step L0: three points on a circle about an apex in the unit annulus
  `1 - x ≤ ‖·‖² ≤ 1` contain a pair of squared distance at most `t`, whenever
  `σ² ≤ 1 - x` and `x(σ + 1) ≤ σ t`
  (`annular_equidistant_triple_close_pair_sharp`).
* Step L1: the same conclusion for circles of squared radius at most `3`, under
  the parameter conditions of the note with `κ` and `γ`
  (`annular_equidistant_triple_close_pair_small_radius`).
* Step Ant: no three points of a closed disk of radius `ρ` are pairwise more than
  `√3 ρ` apart (`not_three_pairwise_sq_far`), and an apex of such a far pair in the
  annulus has squared radius in `(ρ²(1 - 2x), 3ρ²)` (`apex_sq_dist_mem_of_sq_far`).

The proofs use exact coordinates in the apex frame of
`annular_equidistant_triple_close_pair` and inner-product identities; no angles
are used. All thresholds are squared distances.
-/

@[expose] public section

namespace Esgk

open scoped RealInnerProductSpace

/-- Two points of a circle of radius `r` on the same side of a diameter line:
their squared chord is at most `2r` times the gap of their coordinates along
that line. -/
lemma same_side_chord_sq_le {X Y X' Y' r : ℝ} (hr : 0 ≤ r)
    (h1 : X ^ 2 + Y ^ 2 = r ^ 2) (h2 : X' ^ 2 + Y' ^ 2 = r ^ 2) (hside : 0 ≤ Y * Y') :
    (X - X') ^ 2 + (Y - Y') ^ 2 ≤ 2 * r * |X - X'| := by
  have hX : |X| ≤ r := by
    apply abs_le_of_sq_le_sq' _ hr |>.elim (fun a b ↦ abs_le.mpr ⟨a, b⟩)
    nlinarith [sq_nonneg Y]
  have hX' : |X'| ≤ r := by
    apply abs_le_of_sq_le_sq' _ hr |>.elim (fun a b ↦ abs_le.mpr ⟨a, b⟩)
    nlinarith [sq_nonneg Y']
  obtain ⟨hXl, hXu⟩ := abs_le.mp hX
  obtain ⟨hXl', hXu'⟩ := abs_le.mp hX'
  set d := r * |X - X'| with hd
  have hd0 : 0 ≤ d := mul_nonneg hr (abs_nonneg _)
  -- `d ≤ r² - XX'`
  have hdle : d ≤ r ^ 2 - X * X' := by
    rcases abs_cases (X - X') with ⟨h, -⟩ | ⟨h, -⟩
    · rw [hd, h]; nlinarith [mul_nonneg (sub_nonneg.mpr hXu) (neg_le_iff_add_nonneg.mp hXl')]
    · rw [hd, h]; nlinarith [mul_nonneg (sub_nonneg.mpr hXu') (neg_le_iff_add_nonneg.mp hXl)]
  -- the key identity `(r² - XX')² - (r² - X²)(r² - X'²) = d²`
  have hid : (r ^ 2 - X * X') ^ 2 - (Y * Y') ^ 2 = d ^ 2 := by
    have : (Y * Y') ^ 2 = (r ^ 2 - X ^ 2) * (r ^ 2 - X' ^ 2) := by
      rw [mul_pow]; congr 1 <;> linarith
    rw [this, hd, mul_pow, sq_abs]; ring
  have hkey : r ^ 2 - X * X' - d ≤ Y * Y' := by
    by_cases hneg : r ^ 2 - X * X' - d ≤ 0
    · linarith
    · have hpos := not_le.mp hneg
      have hsq : (r ^ 2 - X * X' - d) ^ 2 ≤ (Y * Y') ^ 2 := by
        nlinarith [mul_nonneg hd0 (sub_nonneg.mpr hdle)]
      nlinarith
  nlinarith

/-- Two points of a circle of radius `r` on the same side of a diameter line, whose
coordinates along that line satisfy `X² ≤ γ² r²`: the squared chord, scaled by
`1 - γ²`, is at most the squared gap of those coordinates. -/
lemma same_side_chord_sq_le_of_sq_le {X Y X' Y' r γ : ℝ}
    (h1 : X ^ 2 + Y ^ 2 = r ^ 2) (h2 : X' ^ 2 + Y' ^ 2 = r ^ 2) (hside : 0 ≤ Y * Y')
    (hγ1 : γ ^ 2 ≤ 1) (hX : X ^ 2 ≤ γ ^ 2 * r ^ 2) (hX' : X' ^ 2 ≤ γ ^ 2 * r ^ 2) :
    (1 - γ ^ 2) * ((X - X') ^ 2 + (Y - Y') ^ 2) ≤ (X - X') ^ 2 := by
  have hg : 0 ≤ γ ^ 2 := sq_nonneg γ
  have hc : 0 ≤ 1 - γ ^ 2 := by linarith
  -- each point: `(1 - γ²) X² ≤ γ² Y²`
  have hA : (1 - γ ^ 2) * X ^ 2 ≤ γ ^ 2 * Y ^ 2 := by nlinarith
  have hB : (1 - γ ^ 2) * X' ^ 2 ≤ γ ^ 2 * Y' ^ 2 := by nlinarith
  -- the cross term
  have hcross : (1 - γ ^ 2) * (X * X') ≤ γ ^ 2 * (Y * Y') := by
    have h0A : 0 ≤ (1 - γ ^ 2) * X ^ 2 := mul_nonneg hc (sq_nonneg _)
    have h0B : 0 ≤ (1 - γ ^ 2) * X' ^ 2 := mul_nonneg hc (sq_nonneg _)
    have hsq : ((1 - γ ^ 2) * (X * X')) ^ 2 ≤ (γ ^ 2 * (Y * Y')) ^ 2 := by
      calc ((1 - γ ^ 2) * (X * X')) ^ 2
          = ((1 - γ ^ 2) * X ^ 2) * ((1 - γ ^ 2) * X' ^ 2) := by ring
        _ ≤ (γ ^ 2 * Y ^ 2) * (γ ^ 2 * Y' ^ 2) := mul_le_mul hA hB h0B (h0A.trans hA)
        _ = (γ ^ 2 * (Y * Y')) ^ 2 := by ring
    exact (abs_le_of_sq_le_sq' hsq (mul_nonneg hg hside)).2
  have hsum : (1 - γ ^ 2) * (X + X') ^ 2 ≤ γ ^ 2 * (Y + Y') ^ 2 := by nlinarith
  have hdiff : (Y - Y') * (Y + Y') = -((X - X') * (X + X')) := by
    linear_combination h1 - h2
  have hid : (Y - Y') ^ 2 * (Y + Y') ^ 2 = (X - X') ^ 2 * (X + X') ^ 2 := by
    calc (Y - Y') ^ 2 * (Y + Y') ^ 2 = ((Y - Y') * (Y + Y')) ^ 2 := by ring
      _ = ((X - X') * (X + X')) ^ 2 := by rw [hdiff, neg_sq]
      _ = _ := by ring
  by_cases h0 : Y + Y' = 0
  · have hY' : Y' = -Y := by linarith
    rw [hY'] at hside
    have hY : Y = 0 := by nlinarith [sq_nonneg Y]
    have hYY : Y - Y' = 0 := by rw [hY', hY]; ring
    rw [hYY]
    nlinarith [sq_nonneg (X - X')]
  · have hpos : 0 < (Y + Y') ^ 2 := by positivity
    have key : (1 - γ ^ 2) * (Y - Y') ^ 2 ≤ γ ^ 2 * (X - X') ^ 2 := by
      have hm : (1 - γ ^ 2) * (Y - Y') ^ 2 * (Y + Y') ^ 2 ≤
          γ ^ 2 * (X - X') ^ 2 * (Y + Y') ^ 2 := by
        calc (1 - γ ^ 2) * (Y - Y') ^ 2 * (Y + Y') ^ 2
            = (X - X') ^ 2 * ((1 - γ ^ 2) * (X + X') ^ 2) := by
              rw [mul_assoc, hid]; ring
          _ ≤ (X - X') ^ 2 * (γ ^ 2 * (Y + Y') ^ 2) :=
              mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
          _ = γ ^ 2 * (X - X') ^ 2 * (Y + Y') ^ 2 := by ring
      exact le_of_mul_le_mul_right hm hpos
    nlinarith

/-- The orthonormal frame with the apex `p` at `(‖p‖, 0)`: coordinates `u, v` of
three points, with their squared norms, mutual squared distances, and squared
distances to the apex. -/
private lemma exists_apex_frame (p : Point) (q : Fin 3 → Point) (ha0 : ‖p‖ ≠ 0) :
    ∃ u v : Fin 3 → ℝ, (∀ i, u i ^ 2 + v i ^ 2 = ‖q i‖ ^ 2) ∧
      (∀ i j, (u i - u j) ^ 2 + (v i - v j) ^ 2 = dist (q i) (q j) ^ 2) ∧
      ∀ i, (u i - ‖p‖) ^ 2 + v i ^ 2 = dist p (q i) ^ 2 := by
  set a := ‖p‖ with ha
  have hpa : p 0 ^ 2 + p 1 ^ 2 = a ^ 2 := (point_norm_sq_coordinates p).symm
  let u : Fin 3 → ℝ := fun i ↦ (p 0 * q i 0 + p 1 * q i 1) / a
  let v : Fin 3 → ℝ := fun i ↦ (-p 1 * q i 0 + p 0 * q i 1) / a
  have hnorm (i : Fin 3) : u i ^ 2 + v i ^ 2 = ‖q i‖ ^ 2 := by
    rw [point_norm_sq_coordinates]
    dsimp [u, v]
    field_simp [ha0]
    calc
      _ = (p 0 ^ 2 + p 1 ^ 2) * (q i 0 ^ 2 + q i 1 ^ 2) := by ring
      _ = _ := by rw [hpa]
  have hdist (i j : Fin 3) :
      (u i - u j) ^ 2 + (v i - v j) ^ 2 = dist (q i) (q j) ^ 2 := by
    rw [point_dist_sq_coordinates]
    dsimp [u, v]
    field_simp [ha0]
    calc
      _ = (p 0 ^ 2 + p 1 ^ 2) *
          ((q i 0 - q j 0) ^ 2 + (q i 1 - q j 1) ^ 2) := by ring
      _ = _ := by rw [hpa]
  have hapex (i : Fin 3) : (u i - a) ^ 2 + v i ^ 2 = dist p (q i) ^ 2 := by
    have hu : a * u i = p 0 * q i 0 + p 1 * q i 1 := by
      dsimp [u]; field_simp [ha0]
    calc
      _ = a ^ 2 - 2 * (a * u i) + (u i ^ 2 + v i ^ 2) := by ring
      _ = _ := by
        rw [hnorm, hu, point_norm_sq_coordinates, point_dist_sq_coordinates,
          point_norm_sq_coordinates]
        nlinarith [hpa]
  exact ⟨u, v, hnorm, hdist, hapex⟩

/-- Step L0 in the unit annulus, arbitrary planar frame: three points of the annulus
`1 - x ≤ ‖·‖² ≤ 1` equidistant from an apex `p` of the annulus contain a pair of
squared distance at most `t`, provided `0 < σ`, `σ² ≤ 1 - x` and `x(σ + 1) ≤ σ t`.
No bound on the common radius is assumed. -/
theorem annular_equidistant_triple_close_pair_sharp (p : Point) (q : Fin 3 → Point)
    {x σ t : ℝ} (hσ : 0 < σ) (hσx : σ ^ 2 ≤ 1 - x) (ht : x * (σ + 1) ≤ σ * t)
    (hp : 1 - x ≤ ‖p‖ ^ 2)
    (hlo : ∀ i, 1 - x ≤ ‖q i‖ ^ 2) (hhi : ∀ i, ‖q i‖ ^ 2 ≤ 1)
    (heq : ∀ i j, dist p (q i) = dist p (q j)) :
    ∃ i j : Fin 3, i ≠ j ∧ dist (q i) (q j) ^ 2 ≤ t := by
  have hx : 0 ≤ x := by linarith [hlo 0, hhi 0]
  have ha : σ ≤ ‖p‖ := by nlinarith [norm_nonneg p]
  have ha0 : 0 < ‖p‖ := hσ.trans_le ha
  obtain ⟨u, v, hnorm, hdist, hapex⟩ := exists_apex_frame p q ha0.ne'
  obtain ⟨i, j, hij, hside⟩ := three_has_same_transverse_side v
  refine ⟨i, j, hij, ?_⟩
  have hqi : ‖q i‖ ≤ 1 := by nlinarith [norm_nonneg (q i), hhi i]
  have hrle : dist p (q i) ≤ ‖p‖ + 1 := by
    rw [dist_eq_norm]
    exact (norm_sub_le _ _).trans (by linarith)
  set a := ‖p‖
  set r := dist p (q i)
  have hr0 : 0 ≤ r := dist_nonneg
  have h1 : (u i - a) ^ 2 + v i ^ 2 = r ^ 2 := hapex i
  have h2 : (u j - a) ^ 2 + v j ^ 2 = r ^ 2 := by rw [hapex j, ← heq i j]
  have hchord := same_side_chord_sq_le hr0 h1 h2 hside
  rw [show u i - a - (u j - a) = u i - u j by ring, hdist] at hchord
  have hrow : 2 * a * (u i - u j) = ‖q i‖ ^ 2 - ‖q j‖ ^ 2 := by
    rw [← hnorm, ← hnorm]; linear_combination h2 - h1
  have hgap : 2 * a * |u i - u j| ≤ x := by
    have habs : |2 * a * (u i - u j)| ≤ x := by
      rw [hrow, abs_le]
      constructor <;> linarith [hlo i, hhi i, hlo j, hhi j]
    rwa [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * a)] at habs
  have e1 : a * dist (q i) (q j) ^ 2 ≤ (a + 1) * x := by
    calc a * dist (q i) (q j) ^ 2 ≤ a * (2 * r * |u i - u j|) :=
          mul_le_mul_of_nonneg_left hchord ha0.le
      _ = r * (2 * a * |u i - u j|) := by ring
      _ ≤ r * x := mul_le_mul_of_nonneg_left hgap hr0
      _ ≤ (a + 1) * x := mul_le_mul_of_nonneg_right hrle hx
  have e2 : (a + 1) * x ≤ a * t := by
    have hσt : σ * ((a + 1) * x) ≤ σ * (a * t) := by
      nlinarith [mul_nonneg hx (sub_nonneg.mpr ha), mul_le_mul_of_nonneg_left ht ha0.le]
    exact le_of_mul_le_mul_left hσt hσ
  exact le_of_mul_le_mul_left (e1.trans e2) ha0

/-- For a radius `r ∈ [κx, √3]`, the convexity bound `r² + x ≤ 2γr` of Step L1, from
its values at `r = κx` and `r² = 3`. -/
private lemma sq_add_le_two_mul_of_mem {r x κ γ : ℝ} (hx : 0 ≤ x) (hκ : 0 < κ)
    (hγ : 0 ≤ γ) (hC2 : κ ^ 2 * x + 1 ≤ 2 * γ * κ) (hC3 : (3 + x) ^ 2 ≤ 12 * γ ^ 2)
    (hbig : κ * x ≤ r) (hr3 : r ^ 2 ≤ 3) :
    r ^ 2 + x ≤ 2 * γ * r := by
  have hr0 : 0 ≤ r := (mul_nonneg hκ.le hx).trans hbig
  set m := κ ^ 2 * x ^ 2 with hm
  have hm0 : 0 ≤ m := by positivity
  have hmR : m ≤ r ^ 2 := by
    rw [hm, ← mul_pow]; exact pow_le_pow_left₀ (mul_nonneg hκ.le hx) hbig 2
  -- the value at `R = m`
  have hfm : (m + x) ^ 2 ≤ 4 * γ ^ 2 * m := by
    have hlin : m + x ≤ 2 * γ * κ * x := by
      rw [hm]; nlinarith [mul_le_mul_of_nonneg_right hC2 hx]
    have h0 : 0 ≤ m + x := by linarith
    calc (m + x) ^ 2 ≤ (2 * γ * κ * x) ^ 2 := pow_le_pow_left₀ h0 hlin 2
      _ = 4 * γ ^ 2 * m := by rw [hm]; ring
  -- the value at `R = 3`
  have hf3 : (3 + x) ^ 2 ≤ 4 * γ ^ 2 * 3 := by linarith
  -- the linear part of `f(R) - (R - m)(R - 3)` is nonpositive on `[m, 3]`
  set R := r ^ 2 with hR
  have hlinR : (2 * x - 4 * γ ^ 2 + m + 3) * R + x ^ 2 - 3 * m ≤ 0 := by
    rcases le_total 0 (2 * x - 4 * γ ^ 2 + m + 3) with hs | hs
    · nlinarith [mul_le_mul_of_nonneg_left hr3 hs]
    · nlinarith [mul_le_mul_of_nonpos_left hmR hs]
  have hf : (R + x) ^ 2 ≤ (2 * γ * r) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hmR) (sub_nonneg.mpr hr3)]
  exact (abs_le_of_sq_le_sq' hf (by positivity)).2

/-- Step L1, the offset bound: a point `q` of the unit annulus on the circle of
radius `r ∈ [κx, √3]` about an apex at distance `a ∈ [σ, 1]` from the origin has
`X² ≤ γ² r²`, where `‖q‖² = r² + 2aX + a²`. -/
private lemma offset_sq_le {a r x σ κ γ X N : ℝ} (hσ : 0 < σ) (hσx : σ ^ 2 ≤ 1 - x)
    (hκ : 0 < κ) (hγ : 0 ≤ γ) (hCu : 1 ≤ 2 * σ * γ * κ) (hC1 : 3 ≤ 4 * γ ^ 2 * σ ^ 2)
    (hC2 : κ ^ 2 * x + 1 ≤ 2 * γ * κ) (hC3 : (3 + x) ^ 2 ≤ 12 * γ ^ 2)
    (hx : 0 ≤ x) (hσa : σ ≤ a) (ha1 : a ≤ 1) (ha2 : 1 - x ≤ a ^ 2)
    (hbig : κ * x ≤ r) (hr3 : r ^ 2 ≤ 3)
    (hN : N = r ^ 2 + 2 * a * X + a ^ 2) (hlo : 1 - x ≤ N) (hhi : N ≤ 1) :
    X ^ 2 ≤ γ ^ 2 * r ^ 2 := by
  have hr0 : 0 ≤ r := (mul_nonneg hκ.le hx).trans hbig
  have ha0 : 0 < a := hσ.trans_le hσa
  have hγr : 0 ≤ γ * r := mul_nonneg hγ hr0
  -- upper side: `2aX ≤ x ≤ 2σγκx ≤ 2aγr`
  have hup : X ≤ γ * r := by
    have h1 : 2 * a * X ≤ x := by nlinarith [sq_nonneg r]
    have h2 : x ≤ 2 * σ * γ * (κ * x) := by nlinarith [mul_le_mul_of_nonneg_right hCu hx]
    have h3 : 2 * σ * γ * (κ * x) ≤ 2 * a * (γ * r) := by
      have : σ * (γ * (κ * x)) ≤ a * (γ * r) :=
        mul_le_mul hσa (mul_le_mul_of_nonneg_left hbig hγ)
          (mul_nonneg hγ (mul_nonneg hκ.le hx)) ha0.le
      linarith
    have h4 : a * X ≤ a * (γ * r) := by linarith
    exact le_of_mul_le_mul_left h4 ha0
  -- lower side: `a² - 2γra + r² - (1 - x) ≤ 0` on `[σ, 1]`
  have hgσ : σ ^ 2 - 2 * γ * r * σ + r ^ 2 - (1 - x) ≤ 0 := by
    have hr2 : r ≤ 2 * γ * σ := by
      have hsq : r ^ 2 ≤ (2 * γ * σ) ^ 2 := by nlinarith
      exact (abs_le_of_sq_le_sq' hsq (by positivity)).2
    nlinarith [mul_le_mul_of_nonneg_left hr2 hr0]
  have hg1 : 1 - 2 * γ * r + r ^ 2 - (1 - x) ≤ 0 := by
    have := sq_add_le_two_mul_of_mem hx hκ hγ hC2 hC3 hbig hr3
    linarith
  have hga : a ^ 2 - 2 * γ * r * a + r ^ 2 - (1 - x) ≤ 0 := by
    have hq : (a - σ) * (a - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr hσa) (sub_nonpos.mpr ha1)
    rcases le_total 0 (σ + 1 - 2 * γ * r) with hs | hs
    · nlinarith [mul_le_mul_of_nonneg_left ha1 hs]
    · nlinarith [mul_le_mul_of_nonpos_left hσa hs]
  have hlow : -(γ * r) ≤ X := by
    have h4 : a * (-(γ * r)) ≤ a * X := by nlinarith
    exact le_of_mul_le_mul_left h4 ha0
  calc X ^ 2 ≤ (γ * r) ^ 2 := sq_le_sq' hlow hup
    _ = γ ^ 2 * r ^ 2 := by ring

/-- Step L1 in the unit annulus, arbitrary planar frame: three points of the annulus
`1 - x ≤ ‖·‖² ≤ 1` at a common squared distance at most `3` from an apex `p` of the
annulus contain a pair of squared distance at most `t`. The parameter conditions
`hCu`, `hC1`, `hC2`, `hC3` bound the offset of each point by `γ` times the radius,
and `ht1`, `ht2` are the two branches `r < κx` and `r ≥ κx` of the threshold. -/
theorem annular_equidistant_triple_close_pair_small_radius (p : Point) (q : Fin 3 → Point)
    {x σ κ γ t : ℝ} (hσ : 0 < σ) (hσx : σ ^ 2 ≤ 1 - x) (hκ : 0 < κ) (hγ : 0 ≤ γ)
    (hγ1 : γ ^ 2 < 1) (hCu : 1 ≤ 2 * σ * γ * κ) (hC1 : 3 ≤ 4 * γ ^ 2 * σ ^ 2)
    (hC2 : κ ^ 2 * x + 1 ≤ 2 * γ * κ) (hC3 : (3 + x) ^ 2 ≤ 12 * γ ^ 2)
    (ht1 : 4 * κ ^ 2 * x ^ 2 ≤ t) (ht2 : x ^ 2 ≤ 4 * σ ^ 2 * (1 - γ ^ 2) * t)
    (hp : 1 - x ≤ ‖p‖ ^ 2) (hp1 : ‖p‖ ^ 2 ≤ 1)
    (hlo : ∀ i, 1 - x ≤ ‖q i‖ ^ 2) (hhi : ∀ i, ‖q i‖ ^ 2 ≤ 1)
    (heq : ∀ i j, dist p (q i) = dist p (q j)) (hr : ∀ i, dist p (q i) ^ 2 ≤ 3) :
    ∃ i j : Fin 3, i ≠ j ∧ dist (q i) (q j) ^ 2 ≤ t := by
  have hx : 0 ≤ x := by linarith [hlo 0, hhi 0]
  obtain ⟨r, hrk⟩ : ∃ r, ∀ k, dist p (q k) = r := ⟨dist p (q 0), fun k ↦ heq k 0⟩
  have hr0 : 0 ≤ r := hrk 0 ▸ dist_nonneg
  have hr3 : r ^ 2 ≤ 3 := hrk 0 ▸ hr 0
  by_cases hsmall : r < κ * x
  · refine ⟨0, 1, by decide, ?_⟩
    have htri : dist (q 0) (q 1) ≤ 2 * r := by
      calc dist (q 0) (q 1) ≤ dist (q 0) p + dist p (q 1) := dist_triangle _ _ _
        _ = 2 * r := by rw [dist_comm, hrk 0, hrk 1]; ring
    have h0 : 0 ≤ dist (q 0) (q 1) := dist_nonneg
    nlinarith [mul_le_mul htri htri h0 (by linarith), mul_self_lt_mul_self hr0 hsmall]
  have hbig : κ * x ≤ r := not_lt.mp hsmall
  have ha : σ ≤ ‖p‖ := by nlinarith [norm_nonneg p]
  have ha0 : 0 < ‖p‖ := hσ.trans_le ha
  have ha1 : ‖p‖ ≤ 1 := by nlinarith [norm_nonneg p]
  obtain ⟨u, v, hnorm, hdist, hapex⟩ := exists_apex_frame p q ha0.ne'
  set a := ‖p‖
  have hXk (k : Fin 3) : (u k - a) ^ 2 ≤ γ ^ 2 * r ^ 2 := by
    refine offset_sq_le hσ hσx hκ hγ hCu hC1 hC2 hC3 hx ha ha1 hp hbig hr3
      (N := ‖q k‖ ^ 2) ?_ (hlo k) (hhi k)
    have hk := hapex k
    rw [hrk k] at hk
    rw [← hnorm k]
    linear_combination hk
  obtain ⟨i, j, hij, hside⟩ := three_has_same_transverse_side v
  refine ⟨i, j, hij, ?_⟩
  have h1 : (u i - a) ^ 2 + v i ^ 2 = r ^ 2 := by rw [hapex i, hrk i]
  have h2 : (u j - a) ^ 2 + v j ^ 2 = r ^ 2 := by rw [hapex j, hrk j]
  have hchord := same_side_chord_sq_le_of_sq_le h1 h2 hside hγ1.le (hXk i) (hXk j)
  rw [show u i - a - (u j - a) = u i - u j by ring, hdist] at hchord
  have hrow : 2 * a * (u i - u j) = ‖q i‖ ^ 2 - ‖q j‖ ^ 2 := by
    rw [← hnorm, ← hnorm]; linear_combination h2 - h1
  have hgap : (2 * a * (u i - u j)) ^ 2 ≤ x ^ 2 := by
    rw [hrow]
    exact sq_le_sq' (by linarith [hlo i, hhi i, hlo j, hhi j])
      (by linarith [hlo i, hhi i, hlo j, hhi j])
  have hσa2 : σ ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hσ.le ha 2
  have hc : 0 < 4 * σ ^ 2 * (1 - γ ^ 2) := by
    have : 0 < 1 - γ ^ 2 := by linarith
    positivity
  have hmain : 4 * σ ^ 2 * (1 - γ ^ 2) * dist (q i) (q j) ^ 2 ≤
      4 * σ ^ 2 * (1 - γ ^ 2) * t := by
    calc 4 * σ ^ 2 * (1 - γ ^ 2) * dist (q i) (q j) ^ 2
        = 4 * σ ^ 2 * ((1 - γ ^ 2) * dist (q i) (q j) ^ 2) := by ring
      _ ≤ 4 * σ ^ 2 * (u i - u j) ^ 2 :=
          mul_le_mul_of_nonneg_left hchord (by positivity)
      _ ≤ 4 * a ^ 2 * (u i - u j) ^ 2 := by
          gcongr
      _ = (2 * a * (u i - u j)) ^ 2 := by ring
      _ ≤ x ^ 2 := hgap
      _ ≤ 4 * σ ^ 2 * (1 - γ ^ 2) * t := ht2
  exact le_of_mul_le_mul_left hmain hc

/-- Step L0 after translation by `c` and positive scaling by `ρ`: three points of the
annulus `ρ²(1 - x) ≤ dist · c² ≤ ρ²` equidistant from an apex `p` with
`ρ²(1 - x) ≤ dist p c²` contain a pair of squared distance at most `t ρ²`. -/
theorem scaled_annular_equidistant_triple_close_pair_sharp
    (c p : Point) (q : Fin 3 → Point) {ρ x σ t : ℝ} (hρ : 0 < ρ)
    (hσ : 0 < σ) (hσx : σ ^ 2 ≤ 1 - x) (ht : x * (σ + 1) ≤ σ * t)
    (hp : ρ ^ 2 * (1 - x) ≤ dist p c ^ 2)
    (hlo : ∀ i, ρ ^ 2 * (1 - x) ≤ dist (q i) c ^ 2)
    (hhi : ∀ i, dist (q i) c ^ 2 ≤ ρ ^ 2)
    (heq : ∀ i j, dist p (q i) = dist p (q j)) :
    ∃ i j : Fin 3, i ≠ j ∧ dist (q i) (q j) ^ 2 ≤ t * ρ ^ 2 := by
  let f : Point → Point := fun z ↦ ρ⁻¹ • (z - c)
  have hsq : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have hf (z : Point) : ‖f z‖ ^ 2 = dist z c ^ 2 / ρ ^ 2 := by
    simp [f, norm_smul, Real.norm_eq_abs, dist_eq_norm, mul_pow, div_eq_mul_inv, mul_comm]
  have hd (z w : Point) : dist (f z) (f w) = dist z w / ρ := by
    simp only [f, dist_smul₀, Real.norm_eq_abs, abs_inv, abs_of_pos hρ, dist_sub_right]
    rw [div_eq_mul_inv, mul_comm]
  obtain ⟨i, j, hij, hclose⟩ := annular_equidistant_triple_close_pair_sharp (f p)
    (fun i ↦ f (q i)) hσ hσx ht
    (by rw [hf]; exact (le_div_iff₀ hsq).mpr (by nlinarith [hp]))
    (fun i ↦ by rw [hf]; exact (le_div_iff₀ hsq).mpr (by nlinarith [hlo i]))
    (fun i ↦ by rw [hf]; exact (div_le_iff₀ hsq).mpr (by simpa using hhi i))
    (fun i j ↦ by rw [hd, hd, heq i j])
  rw [hd, div_pow] at hclose
  exact ⟨i, j, hij, (div_le_iff₀ hsq).mp hclose⟩

/-- Step L1 after translation by `c` and positive scaling by `ρ`: three points of the
annulus `ρ²(1 - x) ≤ dist · c² ≤ ρ²` at a common squared distance at most `3ρ²`
from an apex `p` of the annulus contain a pair of squared distance at most `t ρ²`. -/
theorem scaled_annular_equidistant_triple_close_pair_small_radius
    (c p : Point) (q : Fin 3 → Point) {ρ x σ κ γ t : ℝ} (hρ : 0 < ρ)
    (hσ : 0 < σ) (hσx : σ ^ 2 ≤ 1 - x) (hκ : 0 < κ) (hγ : 0 ≤ γ)
    (hγ1 : γ ^ 2 < 1) (hCu : 1 ≤ 2 * σ * γ * κ) (hC1 : 3 ≤ 4 * γ ^ 2 * σ ^ 2)
    (hC2 : κ ^ 2 * x + 1 ≤ 2 * γ * κ) (hC3 : (3 + x) ^ 2 ≤ 12 * γ ^ 2)
    (ht1 : 4 * κ ^ 2 * x ^ 2 ≤ t) (ht2 : x ^ 2 ≤ 4 * σ ^ 2 * (1 - γ ^ 2) * t)
    (hp : ρ ^ 2 * (1 - x) ≤ dist p c ^ 2) (hp1 : dist p c ^ 2 ≤ ρ ^ 2)
    (hlo : ∀ i, ρ ^ 2 * (1 - x) ≤ dist (q i) c ^ 2)
    (hhi : ∀ i, dist (q i) c ^ 2 ≤ ρ ^ 2)
    (heq : ∀ i j, dist p (q i) = dist p (q j))
    (hr : ∀ i, dist p (q i) ^ 2 ≤ 3 * ρ ^ 2) :
    ∃ i j : Fin 3, i ≠ j ∧ dist (q i) (q j) ^ 2 ≤ t * ρ ^ 2 := by
  let f : Point → Point := fun z ↦ ρ⁻¹ • (z - c)
  have hsq : 0 < ρ ^ 2 := sq_pos_of_pos hρ
  have hf (z : Point) : ‖f z‖ ^ 2 = dist z c ^ 2 / ρ ^ 2 := by
    simp [f, norm_smul, Real.norm_eq_abs, dist_eq_norm, mul_pow, div_eq_mul_inv, mul_comm]
  have hd (z w : Point) : dist (f z) (f w) = dist z w / ρ := by
    simp only [f, dist_smul₀, Real.norm_eq_abs, abs_inv, abs_of_pos hρ, dist_sub_right]
    rw [div_eq_mul_inv, mul_comm]
  obtain ⟨i, j, hij, hclose⟩ := annular_equidistant_triple_close_pair_small_radius (f p)
    (fun i ↦ f (q i)) hσ hσx hκ hγ hγ1 hCu hC1 hC2 hC3 ht1 ht2
    (by rw [hf]; exact (le_div_iff₀ hsq).mpr (by nlinarith [hp]))
    (by rw [hf]; exact (div_le_iff₀ hsq).mpr (by simpa using hp1))
    (fun i ↦ by rw [hf]; exact (le_div_iff₀ hsq).mpr (by nlinarith [hlo i]))
    (fun i ↦ by rw [hf]; exact (div_le_iff₀ hsq).mpr (by simpa using hhi i))
    (fun i j ↦ by rw [hd, hd, heq i j])
    (fun i ↦ by rw [hd, div_pow]; exact (div_le_iff₀ hsq).mpr (hr i))
  rw [hd, div_pow] at hclose
  exact ⟨i, j, hij, (div_le_iff₀ hsq).mp hclose⟩

/-- Step Ant (a): no three points of the closed disk of radius `ρ` about `c` are
pairwise at squared distance more than `3ρ²`. -/
theorem not_three_pairwise_sq_far {c u v w : Point} {ρ : ℝ}
    (hu : dist u c ≤ ρ) (hv : dist v c ≤ ρ) (hw : dist w c ≤ ρ)
    (huv : 3 * ρ ^ 2 < dist u v ^ 2) (huw : 3 * ρ ^ 2 < dist u w ^ 2)
    (hvw : 3 * ρ ^ 2 < dist v w ^ 2) : False := by
  have hU : ‖u - c‖ ^ 2 ≤ ρ ^ 2 := by
    rw [← dist_eq_norm]; exact pow_le_pow_left₀ dist_nonneg hu 2
  have hV : ‖v - c‖ ^ 2 ≤ ρ ^ 2 := by
    rw [← dist_eq_norm]; exact pow_le_pow_left₀ dist_nonneg hv 2
  have hW : ‖w - c‖ ^ 2 ≤ ρ ^ 2 := by
    rw [← dist_eq_norm]; exact pow_le_pow_left₀ dist_nonneg hw 2
  rw [dist_eq_norm, ← sub_sub_sub_cancel_right u v c] at huv
  rw [dist_eq_norm, ← sub_sub_sub_cancel_right u w c] at huw
  rw [dist_eq_norm, ← sub_sub_sub_cancel_right v w c] at hvw
  set U := u - c
  set V := v - c
  set W := w - c
  clear_value U V W
  have hid : ‖U - V‖ ^ 2 + ‖U - W‖ ^ 2 + ‖V - W‖ ^ 2 + ‖U + V + W‖ ^ 2 =
      3 * (‖U‖ ^ 2 + ‖V‖ ^ 2 + ‖W‖ ^ 2) := by
    rw [norm_sub_sq_real, norm_sub_sq_real, norm_sub_sq_real, norm_add_sq_real,
      norm_add_sq_real, inner_add_left]
    ring
  nlinarith [sq_nonneg ‖U + V + W‖]

/-- Step Ant (b): in the annulus `ρ²(1 - x) ≤ dist · c² ≤ ρ²`, an apex `z` of a pair
`a, b` at squared distance more than `3ρ²` has squared radius `dist z a²` strictly
between `ρ²(1 - 2x)` and `3ρ²`. -/
theorem apex_sq_dist_mem_of_sq_far {c z a b : Point} {ρ x : ℝ} (hρ : 0 < ρ)
    (hz : ρ ^ 2 * (1 - x) ≤ dist z c ^ 2) (hz1 : dist z c ^ 2 ≤ ρ ^ 2)
    (ha : ρ ^ 2 * (1 - x) ≤ dist a c ^ 2) (ha1 : dist a c ^ 2 ≤ ρ ^ 2)
    (hb : ρ ^ 2 * (1 - x) ≤ dist b c ^ 2) (hb1 : dist b c ^ 2 ≤ ρ ^ 2)
    (hab : 3 * ρ ^ 2 < dist a b ^ 2) (heq : dist z a = dist z b) :
    ρ ^ 2 * (1 - 2 * x) < dist z a ^ 2 ∧ dist z a ^ 2 < 3 * ρ ^ 2 := by
  rw [dist_eq_norm] at hz hz1 ha ha1 hb hb1
  rw [dist_eq_norm, ← sub_sub_sub_cancel_right a b c] at hab
  have hza : dist z a = ‖(z - c) - (a - c)‖ := by
    rw [dist_eq_norm, sub_sub_sub_cancel_right]
  have hzb : dist z b = ‖(z - c) - (b - c)‖ := by
    rw [dist_eq_norm, sub_sub_sub_cancel_right]
  rw [hza] at heq ⊢
  rw [hzb] at heq
  set Z := z - c
  set A := a - c
  set B := b - c
  clear_value Z A B
  have hS : ‖A + B‖ ^ 2 < ρ ^ 2 := by
    have e1 := norm_add_sq_real A B
    have e2 := norm_sub_sq_real A B
    nlinarith
  have hSρ : ‖A + B‖ < ρ := by nlinarith [norm_nonneg (A + B)]
  have hZρ : ‖Z‖ ≤ ρ := by nlinarith [norm_nonneg Z]
  have hin : |⟪Z, A + B⟫| < ρ ^ 2 := by
    refine (abs_real_inner_le_norm Z (A + B)).trans_lt ?_
    calc ‖Z‖ * ‖A + B‖ ≤ ρ * ‖A + B‖ := mul_le_mul_of_nonneg_right hZρ (norm_nonneg _)
      _ < ρ * ρ := mul_lt_mul_of_pos_left hSρ hρ
      _ = ρ ^ 2 := by ring
  have h2 : 2 * ‖Z - A‖ ^ 2 = 2 * ‖Z‖ ^ 2 + ‖A‖ ^ 2 + ‖B‖ ^ 2 - 2 * ⟪Z, A + B⟫ := by
    have e1 := norm_sub_sq_real Z A
    have e2 := norm_sub_sq_real Z B
    rw [inner_add_right]
    have e3 : ‖Z - A‖ ^ 2 = ‖Z - B‖ ^ 2 := by rw [heq]
    linarith
  obtain ⟨hl, hu⟩ := abs_lt.mp hin
  constructor <;> nlinarith

end Esgk
