/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.RefinedClosePairGeometry
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The radius form of the chord bound in a thin annulus

Formalizes the chord bound `ChordRadiusBound` of the Lean closure plan in
`docs/results/explicit-constant-gain-1-40-2026-10-21.md` (§5): the radius form of Step L0 of
`docs/results/refined-constant-gain-2026-10-19.md`. It gives the chord side conditions
`C(I, t)` of the rows `Pa`, `Pb`, `Pc`, `AA` and of the thresholds of Lemma AB, as built by
`scripts/verify_constant_gain_1_40.py`. Thresholds are squared distances.

Let the apex `p` and three points `q i` lie in the annulus `σ²ρ² ≤ |x - c|² ≤ ρ²`
(`0 < σ`, `0 < ρ`), with all three points at the same distance `r` from `p`, and write
`a = |p - c| ≥ σρ`. Two of the three points lie on the same side of the line through `c`
and `p`. In the frame with `p - c = (a, 0)`, the coordinate `X` of a point `q` of the
circle along that line, measured from `p`, satisfies `|q - c|² = a² + 2aX + r²`, so two
points of the annulus on the circle have `|X - X′| ≤ (1 - σ²)ρ²/(2a)`. The same-side chord
bound `chord² ≤ 2r|X - X′|` then gives

`chord² ≤ r (1 - σ²) ρ² / a`.

With `a ≥ σρ` and `r² ≤ vρ²` this is at most `tρ²` when `(1 - σ²) √v ≤ σ t` (the squared
form `(1 - σ²)² v ≤ σ² t²` with `t ≥ 0`). With `r ≤ a + ρ` it is at most `tρ²` when
`(1 - σ²)(1 + σ) ≤ σ t` (the uniform Step L0). The trivial bound `chord ≤ 2r` gives
`chord² ≤ tρ²` when `4v ≤ t`.

The saturated-incidence form gives, under any one of these three conditions, a pair of
increasing indices within squared distance `tρ²` on every saturated circle of squared
radius at most `vρ²`, in the shape of the hypothesis of
`Esgk.sum_closedBall_sq_card_sub_one_lower_bound_radius_cut`.
-/

@[expose] public section

namespace Esgk

open EuclideanGeometry

variable {n : ℕ}

/-- The orthonormal frame with the apex `p` at `(‖p‖, 0)`: coordinates `u, v` of
three points, with their squared norms, mutual squared distances, and squared
distances to the apex. (A copy of the private `exists_apex_frame` of
`Esgk.RefinedClosePairGeometry`.) -/
private lemma exists_apex_frame_coordinates (p : Point) (q : Fin 3 → Point) (ha0 : ‖p‖ ≠ 0) :
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

/-- The radius form of the same-side chord bound, unscaled. Let the apex `p` and three
points `q i` lie in the annulus `σ²ρ² ≤ |x - c|²`, `|q i - c|² ≤ ρ²`, all three at distance
`r` from `p`. Then two of them satisfy `|p - c| · |q i - q j|² ≤ r (1 - σ²) ρ²`. -/
private lemma exists_pair_mul_chord_sq_le (c p : Point) (q : Fin 3 → Point) {ρ σ r : ℝ}
    (hσρ : 0 < σ * ρ) (hp : σ ^ 2 * ρ ^ 2 ≤ dist p c ^ 2)
    (hlo : ∀ i, σ ^ 2 * ρ ^ 2 ≤ dist (q i) c ^ 2)
    (hhi : ∀ i, dist (q i) c ^ 2 ≤ ρ ^ 2) (hd : ∀ i, dist p (q i) = r) :
    ∃ i j : Fin 3, i ≠ j ∧
      dist p c * dist (q i) (q j) ^ 2 ≤ r * ((1 - σ ^ 2) * ρ ^ 2) := by
  set P := p - c with hP
  set Q : Fin 3 → Point := fun i ↦ q i - c with hQ
  have hPn : ‖P‖ = dist p c := (dist_eq_norm p c).symm
  have hQn (i : Fin 3) : ‖Q i‖ = dist (q i) c := (dist_eq_norm (q i) c).symm
  have hPQ (i : Fin 3) : dist P (Q i) = dist p (q i) := dist_sub_right p (q i) c
  have hQQ (i j : Fin 3) : dist (Q i) (Q j) = dist (q i) (q j) := dist_sub_right (q i) (q j) c
  have hσa : σ * ρ ≤ ‖P‖ := by
    rw [hPn]
    exact (abs_le_of_sq_le_sq' (by rw [mul_pow]; exact hp) dist_nonneg).2
  have ha0 : 0 < ‖P‖ := hσρ.trans_le hσa
  obtain ⟨u, v, hnorm, hdist, hapex⟩ := exists_apex_frame_coordinates P Q ha0.ne'
  obtain ⟨i, j, hij, hside⟩ := three_has_same_transverse_side v
  refine ⟨i, j, hij, ?_⟩
  rw [← hPn, ← hQQ]
  set a := ‖P‖
  have hr0 : 0 ≤ r := hd i ▸ dist_nonneg
  have h1 : (u i - a) ^ 2 + v i ^ 2 = r ^ 2 := by rw [hapex i, hPQ, hd]
  have h2 : (u j - a) ^ 2 + v j ^ 2 = r ^ 2 := by rw [hapex j, hPQ, hd]
  have hchord := same_side_chord_sq_le hr0 h1 h2 hside
  rw [show u i - a - (u j - a) = u i - u j by ring, hdist] at hchord
  have hrow : 2 * a * (u i - u j) = ‖Q i‖ ^ 2 - ‖Q j‖ ^ 2 := by
    rw [← hnorm, ← hnorm]; linear_combination h2 - h1
  have hgap : 2 * a * |u i - u j| ≤ (1 - σ ^ 2) * ρ ^ 2 := by
    have habs : |2 * a * (u i - u j)| ≤ (1 - σ ^ 2) * ρ ^ 2 := by
      rw [hrow, hQn, hQn, abs_le]
      constructor <;> linarith [hlo i, hhi i, hlo j, hhi j]
    rwa [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * a)] at habs
  calc a * dist (Q i) (Q j) ^ 2 ≤ a * (2 * r * |u i - u j|) :=
        mul_le_mul_of_nonneg_left hchord ha0.le
    _ = r * (2 * a * |u i - u j|) := by ring
    _ ≤ r * ((1 - σ ^ 2) * ρ ^ 2) := mul_le_mul_of_nonneg_left hgap hr0

/-- **The radius form of Step L0.** Let the apex `p` and three points `q i` lie in the
annulus `σ²ρ² ≤ |x - c|² ≤ ρ²` (`0 < σ`, `0 < ρ`; the upper bound is used for the `q i`
only), all three at the same distance `r` from `p`, with `r² ≤ v ρ²`. If one of

* (a) `(1 - σ²)² v ≤ σ² t²` and `0 ≤ t` (the squared form of `(1 - σ²) √v ≤ σ t`),
* (b) `(1 - σ²)(1 + σ) ≤ σ t` (the uniform Step L0),
* (c) `4 v ≤ t`

holds, then two of the three points are within squared distance `t ρ²`. This is the chord
condition `C((·, √v], √t)` of `scripts/verify_constant_gain_1_40.py` in units of the
scale `ρ`. -/
theorem annular_equidistant_triple_close_pair_of_radius (c p : Point) (q : Fin 3 → Point)
    {ρ σ r v t : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ)
    (hp : σ ^ 2 * ρ ^ 2 ≤ dist p c ^ 2)
    (hlo : ∀ i, σ ^ 2 * ρ ^ 2 ≤ dist (q i) c ^ 2)
    (hhi : ∀ i, dist (q i) c ^ 2 ≤ ρ ^ 2)
    (hd : ∀ i, dist p (q i) = r) (hr : r ^ 2 ≤ v * ρ ^ 2)
    (hcond : ((1 - σ ^ 2) ^ 2 * v ≤ σ ^ 2 * t ^ 2 ∧ 0 ≤ t) ∨
      (1 - σ ^ 2) * (1 + σ) ≤ σ * t ∨ 4 * v ≤ t) :
    ∃ i j : Fin 3, i ≠ j ∧ dist (q i) (q j) ^ 2 ≤ t * ρ ^ 2 := by
  have hσρ : 0 < σ * ρ := mul_pos hσ hρ
  have hρ2 : 0 ≤ ρ ^ 2 := sq_nonneg ρ
  rcases hcond with ⟨ha, ht0⟩ | hb | hc
  · -- (a): `σρ · chord² ≤ |p - c| · chord² ≤ r(1 - σ²)ρ² ≤ σtρ · ρ²`
    obtain ⟨i, j, hij, hmul⟩ := exists_pair_mul_chord_sq_le c p q hσρ hp hlo hhi hd
    refine ⟨i, j, hij, ?_⟩
    have hσa : σ * ρ ≤ dist p c :=
      (abs_le_of_sq_le_sq' (by rw [mul_pow]; exact hp) dist_nonneg).2
    have hsq : (r * (1 - σ ^ 2)) ^ 2 ≤ (σ * t * ρ) ^ 2 := by
      calc (r * (1 - σ ^ 2)) ^ 2 = r ^ 2 * (1 - σ ^ 2) ^ 2 := by ring
        _ ≤ (v * ρ ^ 2) * (1 - σ ^ 2) ^ 2 := mul_le_mul_of_nonneg_right hr (sq_nonneg _)
        _ = ((1 - σ ^ 2) ^ 2 * v) * ρ ^ 2 := by ring
        _ ≤ (σ ^ 2 * t ^ 2) * ρ ^ 2 := mul_le_mul_of_nonneg_right ha hρ2
        _ = (σ * t * ρ) ^ 2 := by ring
    have hlin : r * (1 - σ ^ 2) ≤ σ * t * ρ :=
      (abs_le_of_sq_le_sq' hsq (by positivity)).2
    have hmain : σ * ρ * dist (q i) (q j) ^ 2 ≤ σ * ρ * (t * ρ ^ 2) := by
      calc σ * ρ * dist (q i) (q j) ^ 2 ≤ dist p c * dist (q i) (q j) ^ 2 :=
            mul_le_mul_of_nonneg_right hσa (sq_nonneg _)
        _ ≤ r * ((1 - σ ^ 2) * ρ ^ 2) := hmul
        _ = (r * (1 - σ ^ 2)) * ρ ^ 2 := by ring
        _ ≤ (σ * t * ρ) * ρ ^ 2 := mul_le_mul_of_nonneg_right hlin hρ2
        _ = σ * ρ * (t * ρ ^ 2) := by ring
    exact le_of_mul_le_mul_left hmain hσρ
  · -- (b): the uniform Step L0 with `x = 1 - σ²`
    exact scaled_annular_equidistant_triple_close_pair_sharp c p q hρ (x := 1 - σ ^ 2) hσ
      (by linarith) (by linarith [hb, show (1 - σ ^ 2) * (σ + 1) = (1 - σ ^ 2) * (1 + σ) by ring])
      (by linarith [hp, show ρ ^ 2 * (1 - (1 - σ ^ 2)) = σ ^ 2 * ρ ^ 2 by ring])
      (fun i ↦ by linarith [hlo i, show ρ ^ 2 * (1 - (1 - σ ^ 2)) = σ ^ 2 * ρ ^ 2 by ring])
      hhi (fun i j ↦ (hd i).trans (hd j).symm)
  · -- (c): `chord ≤ 2r`
    refine ⟨0, 1, by decide, ?_⟩
    have hr0 : 0 ≤ r := hd 0 ▸ dist_nonneg
    have htri : dist (q 0) (q 1) ≤ 2 * r := by
      calc dist (q 0) (q 1) ≤ dist (q 0) p + dist p (q 1) := dist_triangle _ _ _
        _ = 2 * r := by rw [dist_comm, hd 0, hd 1]; ring
    have hsq := pow_le_pow_left₀ dist_nonneg htri 2
    have hv : 4 * v * ρ ^ 2 ≤ t * ρ ^ 2 := mul_le_mul_of_nonneg_right hc hρ2
    nlinarith

/-- A saturated incidence carries an increasing pair below `t` whenever every
indexed triple on its circle has a pair below `t`. (A copy of the private
`saturated_incidence_pair_of_triple'` of `Esgk.ShortChainConstantGain`.) -/
private lemma saturated_incidence_increasing_pair_of_triple {p : Config n} {t : ℝ}
    {ir : Fin n × ℝ} (hir : ir ∈ SaturatedDistanceIncidences p)
    (htriple : ∀ f : Fin 3 → Fin n, (∀ i, dist (p ir.1) (p (f i)) = ir.2) →
      ∃ i j : Fin 3, i ≠ j ∧ dist (p (f i)) (p (f j)) ^ 2 ≤ t) :
    ∃ a b, a ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
      b ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
      a < b ∧ dist (p a) (p b) ^ 2 ≤ t := by
  classical
  have hc := (Finset.mem_filter.mp hir).2
  obtain ⟨a, b, c, hab, hac, hbc, hs⟩ := Finset.card_eq_three.mp hc
  let f : Fin 3 → Fin n := ![a, b, c]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hmem (i : Fin 3) : f i ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 := by
    rw [hs]; fin_cases i <;> simp [f]
  have hd (i : Fin 3) : dist (p ir.1) (p (f i)) = ir.2 :=
    (Finset.mem_filter.mp (hmem i)).2.2
  obtain ⟨i, j, hij, hclose⟩ := htriple f hd
  rcases lt_or_gt_of_ne (hf.ne hij) with hlt | hgt
  · exact ⟨f i, f j, hmem i, hmem j, hlt, hclose⟩
  · exact ⟨f j, f i, hmem j, hmem i, hgt, by simpa [dist_comm] using hclose⟩

/-- **The radius form of Step L0 on saturated circles.** Let the configuration lie in the
annulus `σ²ρ² ≤ |p i - c|² ≤ ρ²` (`0 < σ`, `0 < ρ`). If one of

* (a) `(1 - σ²)² v ≤ σ² t²` and `0 ≤ t`,
* (b) `(1 - σ²)(1 + σ) ≤ σ t`,
* (c) `4 v ≤ t`

holds, then every saturated incidence `(i, r)` with `r² ≤ v ρ²` has two neighbours `a < b`
on its circle within squared distance `t ρ²`. The lower cut `u < r²` is not used; it is
there to match the hypothesis of the radius-cut forms of Lemma P''
(`Esgk.sum_closedBall_sq_card_sub_one_lower_bound_radius_cut` and its relatives) with
`v ρ²` and `t ρ²` as the thresholds. -/
theorem saturated_incidence_close_pair_of_radius {p : Config n} {c : Point}
    {ρ σ v t : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ)
    (hlo : ∀ i, σ ^ 2 * ρ ^ 2 ≤ dist (p i) c ^ 2) (hhi : ∀ i, dist (p i) c ^ 2 ≤ ρ ^ 2)
    (hcond : ((1 - σ ^ 2) ^ 2 * v ≤ σ ^ 2 * t ^ 2 ∧ 0 ≤ t) ∨
      (1 - σ ^ 2) * (1 + σ) ≤ σ * t ∨ 4 * v ≤ t) (u : ℝ) :
    ∀ ir ∈ SaturatedDistanceIncidences p, u < ir.2 ^ 2 → ir.2 ^ 2 ≤ v * ρ ^ 2 → ∃ a b,
      a ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧
      b ∈ DistanceOutNeighborsAtValue p ir.1 ir.2 ∧ a < b ∧
      dist (p a) (p b) ^ 2 ≤ t * ρ ^ 2 := by
  intro ir hir _ hrv
  exact saturated_incidence_increasing_pair_of_triple hir fun f hf ↦
    annular_equidistant_triple_close_pair_of_radius c (p ir.1) (fun i ↦ p (f i)) hρ hσ
      (hlo ir.1) (fun i ↦ hlo (f i)) (fun i ↦ hhi (f i)) hf hrv hcond

end Esgk
