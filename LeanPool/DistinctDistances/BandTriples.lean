/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.ApexPairCount
public import LeanPool.DistinctDistances.RefinedClosePairGeometry
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Apex bands

Formalizes Lemma AB (apex bands) of `docs/results/explicit-constant-gain-2-89-2026-10-20.md`
(§2: rows AB1–AB4 and the AB6 consequences of AB5, with the box of the band variables of §3),
as used by Theorem S4 of `docs/results/explicit-constant-gain-1-40-2026-10-21.md`, in count
form. Thresholds are squared distances, scaled by `ρ²`.

The points `p i` lie in the annulus `σ²ρ² ≤ |p_i - c|² ≤ ρ²` about a point `c`; only the
annulus is used, not the centroid property of `c`. The radial excess is
`y_i = |p_i - c|²/ρ² - σ²` (`radialExcess`). For a squared far threshold `Λ = λ²` and squared
band ends `Elo = e_j²`, `Ehi = e_{j+1}²`, the band triples (`apexBandTriples`) are the triples
`(z, a, b)` of indices with `a ≠ b`, `z ∉ {a, b}`, `|ab|² > Λρ²`, `|za| = |zb|` and
`Elo ρ² < |za|² ≤ Ehi ρ²`. Their number is `n² W_j`; the sums of `y_a + y_b` and of `y_z`
over them are `n² U_j` and `n² V_j`.

Write `P(t) = Σ_j (N_j(t) - 1)` for the ordered pairs at squared distance at most `t`, where
`N_j(t)` counts the indices `q` with `|p_j p_q|² ≤ t`, `R(t)` for the number of palette values
`r` with `r² ≤ t`, `D` for the palette size and `Q = 3D - n + 1`. Band edges are a function
`E : ℕ → ℝ`; the bands are `(E j, E (j + 1)]` for `j < m`.

* AB1 (`sum_card_apexBandTriples_ge`): `Σ_j |T_j| ≥ 2(n² - n - P(Λρ²)) - 2nQ` when
  `4 E 0 ≤ Λ` and `4 ≤ E m`. Every far equidistant triple lies in a band, the triples over a
  far pair are its equidistant witnesses, and the witness deficiency bound applies.
* AB2 (`card_apexBandTriples_le_window`): `|T_j| ≤ (4/3)(P(Ehi ρ²) - P(Elo ρ²))` under the
  Step L0 chord condition `(1 - σ²)(σ + 1) ≤ σΛ`.
* AB3, AB4 (`lower_edge_mul_card_apexBandTriples_le`,
  `upper_edge_mul_card_apexBandTriples_le`): from the per-triple bounds
  `K⁻ + (1 - 2/t)Y + (2 - t)y_z ≤ 2|za|²/ρ² ≤ K⁺ + (1 + 2/t)Y + (2 + t)y_z`, with
  `Y = y_a + y_b` and `K^± = (4 ± t)σ² ± (4σ² - Λ)/t`. These use the parallelogram law, the
  Cauchy–Schwarz inequality and `2uv ≤ t u² + v²/t`; they need only `t > 0` (no positivity of
  `Λ` or `σ`).
* AB6 (`sum_bands_base_excess_le_far_palette`, `sum_bands_apex_excess_le_far_palette`):
  `Σ_j U′_j ≤ 12 (Σ_i y_i)(D - R(Λρ²))`, and `Σ_j V′_j ≤ 4 (Σ_i y_i)(D - R(Hρ²))` for
  `4H ≤ Λ` under the chord condition. Input: a point sees at most `3(D - R(T))` points farther
  than `T` (`card_sq_far_le_three_mul_far_palette`).
* Box: `|T_j| ≤ 2n²`, `Σ_j |T_j| ≤ 2n²`, `0 ≤ U′_j ≤ 2(1 - σ²)|T_j|`,
  `0 ≤ V′_j ≤ (1 - σ²)|T_j|`, and `0 ≤ y_i ≤ 1 - σ²`.
-/

@[expose] public section

namespace Esgk

open EuclideanGeometry
open scoped RealInnerProductSpace

variable {n : ℕ}

/-! ### Definitions -/

/-- The radial excess `y_i = |p_i - c|²/ρ² - σ²` of the point `p i` over the inner circle of the
annulus `σ²ρ² ≤ |p_i - c|² ≤ ρ²` (the excess `y_p` of Lemma AB, at scale `ρ`). -/
noncomputable def radialExcess (p : Config n) (c : Point) (ρ σ : ℝ) (i : Fin n) : ℝ :=
  dist (p i) c ^ 2 / ρ ^ 2 - σ ^ 2

/-- The band triples of Lemma AB: the triples `(z, a, b)` of indices (apex `z`, base pair
`(a, b)`) with `a ≠ b`, `z ≠ a`, `z ≠ b`, base pair farther than the squared threshold `Λρ²`,
apex equidistant from `a` and `b`, and squared apex distance in the band `(Elo ρ², Ehi ρ²]`.
Its cardinality is `n² W_j` for `Λ = λ²`, `Elo = e_j²`, `Ehi = e_{j+1}²`. -/
noncomputable def apexBandTriples (p : Config n) (ρ Λ Elo Ehi : ℝ) :
    Finset (Fin n × Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n × Fin n × Fin n)).filter fun x ↦
    x.2.1 ≠ x.2.2 ∧ x.1 ≠ x.2.1 ∧ x.1 ≠ x.2.2 ∧ Λ * ρ ^ 2 < dist (p x.2.1) (p x.2.2) ^ 2 ∧
      dist (p x.1) (p x.2.1) = dist (p x.1) (p x.2.2) ∧
      Elo * ρ ^ 2 < dist (p x.1) (p x.2.1) ^ 2 ∧ dist (p x.1) (p x.2.1) ^ 2 ≤ Ehi * ρ ^ 2

/-- Membership in the band triples. -/
private lemma mem_apexBandTriples {p : Config n} {ρ Λ Elo Ehi : ℝ}
    {x : Fin n × Fin n × Fin n} :
    x ∈ apexBandTriples p ρ Λ Elo Ehi ↔
      x.2.1 ≠ x.2.2 ∧ x.1 ≠ x.2.1 ∧ x.1 ≠ x.2.2 ∧ Λ * ρ ^ 2 < dist (p x.2.1) (p x.2.2) ^ 2 ∧
        dist (p x.1) (p x.2.1) = dist (p x.1) (p x.2.2) ∧
        Elo * ρ ^ 2 < dist (p x.1) (p x.2.1) ^ 2 ∧ dist (p x.1) (p x.2.1) ^ 2 ≤ Ehi * ρ ^ 2 := by
  rw [apexBandTriples, Finset.mem_filter]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.mem_univ _, h⟩⟩

/-- The far equidistant triples: the band triples without the band condition (the set `T` of
Lemma AB). -/
private noncomputable def farEquidistantTriples (p : Config n) (ρ Λ : ℝ) :
    Finset (Fin n × Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n × Fin n × Fin n)).filter fun x ↦
    x.2.1 ≠ x.2.2 ∧ x.1 ≠ x.2.1 ∧ x.1 ≠ x.2.2 ∧ Λ * ρ ^ 2 < dist (p x.2.1) (p x.2.2) ^ 2 ∧
      dist (p x.1) (p x.2.1) = dist (p x.1) (p x.2.2)

/-- Membership in the far equidistant triples. -/
private lemma mem_farEquidistantTriples {p : Config n} {ρ Λ : ℝ}
    {x : Fin n × Fin n × Fin n} :
    x ∈ farEquidistantTriples p ρ Λ ↔
      x.2.1 ≠ x.2.2 ∧ x.1 ≠ x.2.1 ∧ x.1 ≠ x.2.2 ∧ Λ * ρ ^ 2 < dist (p x.2.1) (p x.2.2) ^ 2 ∧
        dist (p x.1) (p x.2.1) = dist (p x.1) (p x.2.2) := by
  rw [farEquidistantTriples, Finset.mem_filter]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.mem_univ _, h⟩⟩

/-- Every band triple is a far equidistant triple. -/
private lemma apexBandTriples_subset (p : Config n) (ρ Λ Elo Ehi : ℝ) :
    apexBandTriples p ρ Λ Elo Ehi ⊆ farEquidistantTriples p ρ Λ := by
  intro x hx
  obtain ⟨h1, h2, h3, h4, h5, -, -⟩ := mem_apexBandTriples.mp hx
  exact mem_farEquidistantTriples.mpr ⟨h1, h2, h3, h4, h5⟩

/-! ### The radial excess in the annulus -/

/-- In the annulus `σ²ρ² ≤ |p_i - c|²`, the radial excess is nonnegative. -/
theorem radialExcess_nonneg {p : Config n} {c : Point} {ρ σ : ℝ} (hρ : 0 < ρ)
    (hlo : ∀ i, σ ^ 2 * ρ ^ 2 ≤ dist (p i) c ^ 2) (i : Fin n) :
    0 ≤ radialExcess p c ρ σ i := by
  have hρ2 : 0 < ρ ^ 2 := by positivity
  rw [radialExcess, sub_nonneg, le_div_iff₀ hρ2]
  exact hlo i

/-- In the annulus `|p_i - c|² ≤ ρ²`, the radial excess is at most `1 - σ²` (the width `ω` of
Lemma AB). -/
theorem radialExcess_le {p : Config n} {c : Point} {ρ σ : ℝ} (hρ : 0 < ρ)
    (hhi : ∀ i, dist (p i) c ^ 2 ≤ ρ ^ 2) (i : Fin n) :
    radialExcess p c ρ σ i ≤ 1 - σ ^ 2 := by
  have hρ2 : 0 < ρ ^ 2 := by positivity
  rw [radialExcess, sub_le_sub_iff_right, div_le_iff₀ hρ2, one_mul]
  exact hhi i

/-! ### Per-triple geometry (Lemma AB, "Geometry") -/

/-- Apex distance bounds in vector form. If `z` is equidistant from `a` and `b`, and
`T < |ab|²`, then for every `t > 0`, with `u = |a - c|² + |b - c|²`,
`(2 - t)|z - c|² + (1 - 2/t)u + T/t ≤ 2|za|² ≤ (2 + t)|z - c|² + (1 + 2/t)u - T/t`. The
proof adds `|z - a|²` and `|z - b|²`, uses the parallelogram law
`|(a - c) + (b - c)|² = 2u - |ab|²`, the Cauchy–Schwarz inequality and
`2 t |z - c| |w| ≤ t² |z - c|² + |w|²`. -/
private lemma two_mul_sq_dist_apex_bounds {z a b c : Point} {T t : ℝ} (ht : 0 < t)
    (heq : dist z a = dist z b) (hfar : T < dist a b ^ 2) :
    2 * dist z a ^ 2 ≤
        (2 + t) * dist z c ^ 2 + (1 + 2 / t) * (dist a c ^ 2 + dist b c ^ 2) - T / t ∧
      (2 - t) * dist z c ^ 2 + (1 - 2 / t) * (dist a c ^ 2 + dist b c ^ 2) + T / t ≤
        2 * dist z a ^ 2 := by
  have e1 := norm_sub_sq_real (z - c) (a - c)
  have e2 := norm_sub_sq_real (z - c) (b - c)
  have e3 := norm_sub_sq_real (a - c) (b - c)
  have e4 := norm_add_sq_real (a - c) (b - c)
  have e5 := inner_add_right (𝕜 := ℝ) (z - c) (a - c) (b - c)
  have hcs := abs_real_inner_le_norm (z - c) ((a - c) + (b - c))
  rw [sub_sub_sub_cancel_right, ← dist_eq_norm, ← dist_eq_norm, ← dist_eq_norm] at e1 e2 e3
  rw [← dist_eq_norm, ← dist_eq_norm] at e4
  rw [← dist_eq_norm, e5] at hcs
  set s := ⟪z - c, a - c⟫ + ⟪z - c, b - c⟫ with hs
  set N := dist z c with hN
  set M := ‖(a - c) + (b - c)‖ with hM
  set u := dist a c ^ 2 + dist b c ^ 2 with hu
  have hN0 : 0 ≤ N := dist_nonneg
  have hM0 : 0 ≤ M := norm_nonneg _
  obtain ⟨hs1, hs2⟩ := abs_le.mp hcs
  have hM2 : M ^ 2 = 2 * u - dist a b ^ 2 := by rw [hu]; linarith
  have hsq : 0 ≤ (t * N - M) ^ 2 := sq_nonneg _
  have key1 : t * (2 * s) ≤ t ^ 2 * N ^ 2 + (2 * u - T) := by
    nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hs2)]
  have key2 : t * (-(2 * s)) ≤ t ^ 2 * N ^ 2 + (2 * u - T) := by
    nlinarith [mul_nonneg ht.le (neg_le_iff_add_nonneg.mp hs1)]
  have h2r : 2 * dist z a ^ 2 = 2 * N ^ 2 + u - 2 * s := by
    have hzab : dist z a ^ 2 = dist z b ^ 2 := by rw [heq]
    rw [hs, hu]
    linarith
  have hrw : t * N ^ 2 + 2 / t * u - T / t = (t ^ 2 * N ^ 2 + (2 * u - T)) / t := by
    field_simp
    ring
  have hdiv1 : -(2 * s) ≤ t * N ^ 2 + 2 / t * u - T / t := by
    rw [hrw, le_div_iff₀ ht]
    linarith
  have hdiv2 : 2 * s ≤ t * N ^ 2 + 2 / t * u - T / t := by
    rw [hrw, le_div_iff₀ ht]
    linarith
  constructor
  · have hR : (2 + t) * N ^ 2 + (1 + 2 / t) * u - T / t =
        2 * N ^ 2 + u + (t * N ^ 2 + 2 / t * u - T / t) := by ring
    rw [hR, h2r]
    linarith
  · have hR : (2 - t) * N ^ 2 + (1 - 2 / t) * u + T / t =
        2 * N ^ 2 + u - (t * N ^ 2 + 2 / t * u - T / t) := by ring
    rw [hR, h2r]
    linarith

/-- Apex distance bounds in normalized form (Lemma AB, "Geometry"). For a far equidistant
triple `(z, a, b)` with `Λρ² < |ab|²` and every `t > 0`,
`K⁻ + (1 - 2/t)(y_a + y_b) + (2 - t)y_z ≤ 2|za|²/ρ² ≤ K⁺ + (1 + 2/t)(y_a + y_b) + (2 + t)y_z`
with `K^± = (4 ± t)σ² ± (4σ² - Λ)/t`. -/
private lemma apex_sq_dist_div_bounds {p : Config n} {c : Point} {ρ σ Λ t : ℝ} (hρ : 0 < ρ)
    (ht : 0 < t) {z a b : Fin n} (heq : dist (p z) (p a) = dist (p z) (p b))
    (hfar : Λ * ρ ^ 2 < dist (p a) (p b) ^ 2) :
    2 * (dist (p z) (p a) ^ 2 / ρ ^ 2) ≤ (4 + t) * σ ^ 2 + (4 * σ ^ 2 - Λ) / t +
        (1 + 2 / t) * (radialExcess p c ρ σ a + radialExcess p c ρ σ b) +
        (2 + t) * radialExcess p c ρ σ z ∧
      (4 - t) * σ ^ 2 - (4 * σ ^ 2 - Λ) / t +
          (1 - 2 / t) * (radialExcess p c ρ σ a + radialExcess p c ρ σ b) +
          (2 - t) * radialExcess p c ρ σ z ≤ 2 * (dist (p z) (p a) ^ 2 / ρ ^ 2) := by
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hρ0 : ρ ≠ 0 := hρ.ne'
  have ht0 : t ≠ 0 := ht.ne'
  obtain ⟨h1, h2⟩ := two_mul_sq_dist_apex_bounds (c := c) ht heq hfar
  have hup : (4 + t) * σ ^ 2 + (4 * σ ^ 2 - Λ) / t +
        (1 + 2 / t) * (radialExcess p c ρ σ a + radialExcess p c ρ σ b) +
        (2 + t) * radialExcess p c ρ σ z =
      ((2 + t) * dist (p z) c ^ 2 + (1 + 2 / t) * (dist (p a) c ^ 2 + dist (p b) c ^ 2) -
        Λ * ρ ^ 2 / t) / ρ ^ 2 := by
    unfold radialExcess
    field_simp
    ring
  have hlow : (4 - t) * σ ^ 2 - (4 * σ ^ 2 - Λ) / t +
        (1 - 2 / t) * (radialExcess p c ρ σ a + radialExcess p c ρ σ b) +
        (2 - t) * radialExcess p c ρ σ z =
      ((2 - t) * dist (p z) c ^ 2 + (1 - 2 / t) * (dist (p a) c ^ 2 + dist (p b) c ^ 2) +
        Λ * ρ ^ 2 / t) / ρ ^ 2 := by
    unfold radialExcess
    field_simp
    ring
  rw [hup, hlow, mul_div_assoc']
  exact ⟨div_le_div_of_nonneg_right h1 hρ2.le, div_le_div_of_nonneg_right h2 hρ2.le⟩

/-! ### Rows AB3 and AB4 -/

/-- Row AB3 of Lemma AB times `n²`: for `t > 0`, with `K⁺ = (4 + t)σ² + (4σ² - Λ)/t`, the band
triples `T_j` with lower band end `Elo = e_j²` satisfy
`(2 Elo - K⁺)|T_j| ≤ (1 + 2/t) Σ_{T_j}(y_a + y_b) + (2 + t) Σ_{T_j} y_z`. In normalized form
this is `(2e_j² - K⁺)W_j - (1 + 2/t)U_j - (2 + t)V_j ≤ 0`. No annulus hypothesis is needed. -/
theorem lower_edge_mul_card_apexBandTriples_le {p : Config n} {c : Point}
    {ρ σ Λ Elo Ehi t : ℝ} (hρ : 0 < ρ) (ht : 0 < t) :
    (2 * Elo - ((4 + t) * σ ^ 2 + (4 * σ ^ 2 - Λ) / t)) *
        ((apexBandTriples p ρ Λ Elo Ehi).card : ℝ) ≤
      (1 + 2 / t) * ∑ x ∈ apexBandTriples p ρ Λ Elo Ehi,
          (radialExcess p c ρ σ x.2.1 + radialExcess p c ρ σ x.2.2) +
        (2 + t) * ∑ x ∈ apexBandTriples p ρ Λ Elo Ehi, radialExcess p c ρ σ x.1 := by
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hL : (2 * Elo - ((4 + t) * σ ^ 2 + (4 * σ ^ 2 - Λ) / t)) *
      ((apexBandTriples p ρ Λ Elo Ehi).card : ℝ) =
      ∑ _x ∈ apexBandTriples p ρ Λ Elo Ehi,
        (2 * Elo - ((4 + t) * σ ^ 2 + (4 * σ ^ 2 - Λ) / t)) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hL, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x hx
  obtain ⟨-, -, -, hfar, heq, hElo, -⟩ := mem_apexBandTriples.mp hx
  have hb := (apex_sq_dist_div_bounds (c := c) (σ := σ) hρ ht heq hfar).1
  have hE : Elo < dist (p x.1) (p x.2.1) ^ 2 / ρ ^ 2 := (lt_div_iff₀ hρ2).mpr hElo
  linarith

/-- Row AB4 of Lemma AB times `n²`: for `t > 0`, with `K⁻ = (4 - t)σ² - (4σ² - Λ)/t`, the band
triples `T_j` with upper band end `Ehi = e_{j+1}²` satisfy
`(K⁻ - 2 Ehi)|T_j| ≤ (2/t - 1)⁺ Σ_{T_j}(y_a + y_b) + (t - 2)⁺ Σ_{T_j} y_z`, for points in the
annulus `σ²ρ² ≤ |p_i - c|²`. In normalized form this is
`(K⁻ - 2e_{j+1}²)W_j - (2/t - 1)⁺U_j - (t - 2)⁺V_j ≤ 0`. -/
theorem upper_edge_mul_card_apexBandTriples_le {p : Config n} {c : Point}
    {ρ σ Λ Elo Ehi t : ℝ} (hρ : 0 < ρ) (ht : 0 < t)
    (hlo : ∀ i, σ ^ 2 * ρ ^ 2 ≤ dist (p i) c ^ 2) :
    ((4 - t) * σ ^ 2 - (4 * σ ^ 2 - Λ) / t - 2 * Ehi) *
        ((apexBandTriples p ρ Λ Elo Ehi).card : ℝ) ≤
      max (2 / t - 1) 0 * ∑ x ∈ apexBandTriples p ρ Λ Elo Ehi,
          (radialExcess p c ρ σ x.2.1 + radialExcess p c ρ σ x.2.2) +
        max (t - 2) 0 * ∑ x ∈ apexBandTriples p ρ Λ Elo Ehi, radialExcess p c ρ σ x.1 := by
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hL : ((4 - t) * σ ^ 2 - (4 * σ ^ 2 - Λ) / t - 2 * Ehi) *
      ((apexBandTriples p ρ Λ Elo Ehi).card : ℝ) =
      ∑ _x ∈ apexBandTriples p ρ Λ Elo Ehi,
        ((4 - t) * σ ^ 2 - (4 * σ ^ 2 - Λ) / t - 2 * Ehi) := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  rw [hL, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro x hx
  obtain ⟨-, -, -, hfar, heq, -, hEhi⟩ := mem_apexBandTriples.mp hx
  have hb := (apex_sq_dist_div_bounds (c := c) (σ := σ) hρ ht heq hfar).2
  have hE : dist (p x.1) (p x.2.1) ^ 2 / ρ ^ 2 ≤ Ehi := (div_le_iff₀ hρ2).mpr hEhi
  have hY : 0 ≤ radialExcess p c ρ σ x.2.1 + radialExcess p c ρ σ x.2.2 :=
    add_nonneg (radialExcess_nonneg hρ hlo _) (radialExcess_nonneg hρ hlo _)
  have hz : 0 ≤ radialExcess p c ρ σ x.1 := radialExcess_nonneg hρ hlo _
  have hm1 := mul_le_mul_of_nonneg_right (le_max_left (2 / t - 1) 0) hY
  have hm2 := mul_le_mul_of_nonneg_right (le_max_left (t - 2) 0) hz
  linarith

/-! ### Fibers of triples -/

/-- A sum over a set of triples, fibered over the apex. -/
private lemma sum_eq_sum_apex_fibers {β : Type*} [AddCommMonoid β]
    (T : Finset (Fin n × Fin n × Fin n)) (f : Fin n × Fin n × Fin n → β) :
    ∑ x ∈ T, f x = ∑ z : Fin n,
      ∑ ab ∈ (Finset.univ : Finset (Fin n × Fin n)).filter (fun ab ↦ (z, ab) ∈ T), f (z, ab) := by
  have h1 : ∑ x ∈ T, f x = ∑ x, if x ∈ T then f x else 0 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [h1, Fintype.sum_prod_type]
  simp only [Finset.sum_filter]

/-- A sum over a set of triples, fibered over the base pair. -/
private lemma sum_eq_sum_pair_fibers {β : Type*} [AddCommMonoid β]
    (T : Finset (Fin n × Fin n × Fin n)) (f : Fin n × Fin n × Fin n → β) :
    ∑ x ∈ T, f x = ∑ ab : Fin n × Fin n,
      ∑ z ∈ (Finset.univ : Finset (Fin n)).filter (fun z ↦ (z, ab) ∈ T), f (z, ab) := by
  have h1 : ∑ x ∈ T, f x = ∑ x, if x ∈ T then f x else 0 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [h1, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [Finset.sum_filter]

/-- The cardinality of a set of triples, fibered over the apex. -/
private lemma card_eq_sum_apex_fibers (T : Finset (Fin n × Fin n × Fin n)) :
    T.card = ∑ z : Fin n,
      ((Finset.univ : Finset (Fin n × Fin n)).filter (fun ab ↦ (z, ab) ∈ T)).card := by
  rw [Finset.card_eq_sum_ones, sum_eq_sum_apex_fibers]
  simp only [Finset.card_eq_sum_ones]

/-- The cardinality of a set of triples, fibered over the base pair. -/
private lemma card_eq_sum_pair_fibers (T : Finset (Fin n × Fin n × Fin n)) :
    T.card = ∑ ab : Fin n × Fin n,
      ((Finset.univ : Finset (Fin n)).filter (fun z ↦ (z, ab) ∈ T)).card := by
  rw [Finset.card_eq_sum_ones, sum_eq_sum_pair_fibers]
  simp only [Finset.card_eq_sum_ones]

/-- A sum over a set `S` of ordered pairs, of a function of the first coordinate, is the sum
over the first coordinate weighted by the number of its partners in `S`. -/
private lemma sum_pairs_fst_eq (S : Finset (Fin n × Fin n)) (g : Fin n → ℝ) :
    ∑ ab ∈ S, g ab.1 =
      ∑ a, (((Finset.univ : Finset (Fin n)).filter (fun b ↦ (a, b) ∈ S)).card : ℝ) * g a := by
  have h1 : ∑ ab ∈ S, g ab.1 = ∑ ab, if ab ∈ S then g ab.1 else 0 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [h1, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  by_cases h : (a, b) ∈ S <;> simp [h]

/-- A sum over a set `S` of ordered pairs, of a function of the second coordinate, is the sum
over the second coordinate weighted by the number of its partners in `S`. -/
private lemma sum_pairs_snd_eq (S : Finset (Fin n × Fin n)) (g : Fin n → ℝ) :
    ∑ ab ∈ S, g ab.2 =
      ∑ b, (((Finset.univ : Finset (Fin n)).filter (fun a ↦ (a, b) ∈ S)).card : ℝ) * g b := by
  have h1 : ∑ ab ∈ S, g ab.2 = ∑ ab, if ab ∈ S then g ab.2 else 0 := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [h1, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  by_cases h : (a, b) ∈ S <;> simp [h]

/-! ### Witness counts over the base pairs -/

/-- Over a fixed base pair, a set of far equidistant triples has at most two apexes: under no
three collinear points a pair of distinct points has at most two equidistant witnesses. -/
private lemma card_pair_fiber_le_two {p : Config n} (hp : Function.Injective p)
    (hgp3 : NonTrilinear (Config.toFinset p : Set Point)) (ρ Λ : ℝ) (ab : Fin n × Fin n) :
    ((Finset.univ : Finset (Fin n)).filter
      (fun z ↦ (z, ab) ∈ farEquidistantTriples p ρ Λ)).card ≤ 2 := by
  by_cases hab : ab.1 = ab.2
  · have hempty : (Finset.univ : Finset (Fin n)).filter
        (fun z ↦ (z, ab) ∈ farEquidistantTriples p ρ Λ) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro z _ hz
      exact (mem_farEquidistantTriples.mp hz).1 hab
    rw [hempty, Finset.card_empty]
    norm_num
  · refine (Finset.card_le_card ?_).trans
      (indexedEquidistantWitnesses_card_le_two_of_nonTrilinear hp hgp3 hab)
    intro z hz
    rw [Finset.mem_filter, mem_farEquidistantTriples] at hz
    simp only [IndexedEquidistantWitnesses, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hz.2.2.2.2.2

/-- The far equidistant triples number at most `2n²`. -/
private lemma card_farEquidistantTriples_le {p : Config n} (hp : Function.Injective p)
    (hgp3 : NonTrilinear (Config.toFinset p : Set Point)) (ρ Λ : ℝ) :
    (farEquidistantTriples p ρ Λ).card ≤ 2 * (n * n) := by
  rw [card_eq_sum_pair_fibers]
  calc ∑ ab : Fin n × Fin n, ((Finset.univ : Finset (Fin n)).filter
        (fun z ↦ (z, ab) ∈ farEquidistantTriples p ρ Λ)).card
      ≤ ∑ _ab : Fin n × Fin n, 2 :=
        Finset.sum_le_sum fun ab _ ↦ card_pair_fiber_le_two hp hgp3 ρ Λ ab
    _ = 2 * (n * n) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul,
          mul_comm]

/-- The equidistant witnesses of the ordered far pairs are counted by the far equidistant
triples: `Σ_Φ α ≤ |T|`, where `Φ` is the set of ordered pairs of distinct indices farther than
`Λρ²` and `α` the witness count. -/
private lemma sum_witnesses_le_card_farEquidistantTriples {p : Config n}
    (hp : Function.Injective p) (ρ Λ : ℝ) :
    ∑ ab ∈ (Finset.univ : Finset (Fin n)).offDiag.filter
        (fun ab ↦ Λ * ρ ^ 2 < dist (p ab.1) (p ab.2) ^ 2),
        (IndexedEquidistantWitnesses p ab.1 ab.2).card ≤
      (farEquidistantTriples p ρ Λ).card := by
  rw [card_eq_sum_pair_fibers]
  calc ∑ ab ∈ (Finset.univ : Finset (Fin n)).offDiag.filter
          (fun ab ↦ Λ * ρ ^ 2 < dist (p ab.1) (p ab.2) ^ 2),
          (IndexedEquidistantWitnesses p ab.1 ab.2).card
      ≤ ∑ ab ∈ (Finset.univ : Finset (Fin n)).offDiag.filter
          (fun ab ↦ Λ * ρ ^ 2 < dist (p ab.1) (p ab.2) ^ 2),
          ((Finset.univ : Finset (Fin n)).filter
            (fun z ↦ (z, ab) ∈ farEquidistantTriples p ρ Λ)).card := by
        refine Finset.sum_le_sum fun ab hab ↦ Finset.card_le_card ?_
        rw [Finset.mem_filter, Finset.mem_offDiag] at hab
        obtain ⟨⟨-, -, hne⟩, hfar⟩ := hab
        intro z hz
        simp only [IndexedEquidistantWitnesses, Finset.mem_filter, Finset.mem_univ,
          true_and] at hz
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        refine mem_farEquidistantTriples.mpr ⟨hne, ?_, ?_, hfar, hz⟩
        · change z ≠ ab.1
          intro h
          rw [h, dist_self] at hz
          exact hne (hp (dist_eq_zero.mp hz.symm))
        · change z ≠ ab.2
          intro h
          rw [h, dist_self] at hz
          exact hne (hp (dist_eq_zero.mp hz)).symm
    _ ≤ ∑ ab : Fin n × Fin n, ((Finset.univ : Finset (Fin n)).filter
          (fun z ↦ (z, ab) ∈ farEquidistantTriples p ρ Λ)).card :=
        Finset.sum_le_sum_of_subset (Finset.subset_univ _)

/-- A sum over the far equidistant triples of a nonnegative function of the base pair is at
most twice its sum over the ordered far pairs of distinct indices. -/
private lemma sum_farEquidistantTriples_pair_le {p : Config n} (hp : Function.Injective p)
    (hgp3 : NonTrilinear (Config.toFinset p : Set Point)) (ρ Λ : ℝ)
    (g : Fin n × Fin n → ℝ) (hg : ∀ ab, 0 ≤ g ab) :
    ∑ x ∈ farEquidistantTriples p ρ Λ, g x.2 ≤
      2 * ∑ ab ∈ (Finset.univ : Finset (Fin n × Fin n)).filter
        (fun ab ↦ ab.1 ≠ ab.2 ∧ Λ * ρ ^ 2 < dist (p ab.1) (p ab.2) ^ 2), g ab := by
  rw [sum_eq_sum_pair_fibers, Finset.sum_filter, Finset.mul_sum]
  refine Finset.sum_le_sum fun ab _ ↦ ?_
  simp only [Finset.sum_const, nsmul_eq_mul]
  split_ifs with hP
  · exact mul_le_mul_of_nonneg_right
      (by exact_mod_cast card_pair_fiber_le_two hp hgp3 ρ Λ ab) (hg ab)
  · have hempty : (Finset.univ : Finset (Fin n)).filter
        (fun z ↦ (z, ab) ∈ farEquidistantTriples p ρ Λ) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro z _ hz
      obtain ⟨hne, -, -, hfar, -⟩ := mem_farEquidistantTriples.mp hz
      exact hP ⟨hne, hfar⟩
    rw [hempty, Finset.card_empty, Nat.cast_zero, zero_mul, mul_zero]

/-! ### Far points and the palette -/

/-- Far points and the palette above a threshold. With the degree cap three, a point `p w` sees
at most `3(D - R(T))` other points at squared distance more than `T`: each such point lies at
one of the `D - R(T)` palette values `r` with `r² > T`, at most three per value. -/
theorem card_sq_far_le_three_mul_far_palette {p : Config n}
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) (T : ℝ) (w : Fin n) :
    (((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ w ≠ q ∧ T < dist (p w) (p q) ^ 2)).card : ℝ) ≤
      3 * ((NumDistancesOrdered p : ℝ) -
        (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ T)).card : ℝ)) := by
  set F := (OrderedDistanceValues p).filter (fun r ↦ ¬r ^ 2 ≤ T) with hF
  have hsub : (Finset.univ : Finset (Fin n)).filter
      (fun q ↦ w ≠ q ∧ T < dist (p w) (p q) ^ 2) ⊆
      F.biUnion (fun r ↦ DistanceOutNeighborsAtValue p w r) := by
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq
    rw [Finset.mem_biUnion]
    refine ⟨dist (p w) (p q), Finset.mem_filter.mpr
      ⟨dist_mem_orderedDistanceValues_of_ne hq.1, not_le.mpr hq.2⟩, ?_⟩
    rw [DistanceOutNeighborsAtValue, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hq.1, rfl⟩
  have h1 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
  have h2 : ∑ r ∈ F, (DistanceOutNeighborsAtValue p w r).card ≤ ∑ _r ∈ F, 3 :=
    Finset.sum_le_sum fun r _ ↦ hcap w r
  rw [Finset.sum_const, smul_eq_mul] at h2
  have h3 := Finset.card_filter_add_card_filter_not (s := OrderedDistanceValues p)
    (p := fun r ↦ r ^ 2 ≤ T)
  rw [← hF] at h3
  have h3R : (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ T)).card : ℝ) + (F.card : ℝ) =
      (NumDistancesOrdered p : ℝ) := by
    rw [NumDistancesOrdered]
    exact_mod_cast h3
  have h12 : (((Finset.univ : Finset (Fin n)).filter
      (fun q ↦ w ≠ q ∧ T < dist (p w) (p q) ^ 2)).card : ℝ) ≤ (F.card : ℝ) * 3 := by
    exact_mod_cast h1.trans h2
  linarith

/-! ### Triangle-free apex circles and the per-apex count -/

/-- Step L0 at `x = 1 - σ²` and `t = Λ`: when `(1 - σ²)(σ + 1) ≤ σΛ`, three points of the
annulus equidistant from a point of the annulus are not pairwise at squared distance more than
`Λρ²`. -/
private lemma false_of_three_far_on_apex_circle {p : Config n} {c : Point} {ρ σ Λ : ℝ}
    (hρ : 0 < ρ) (hσ : 0 < σ) (hchord : (1 - σ ^ 2) * (σ + 1) ≤ σ * Λ)
    (hlo : ∀ i, σ ^ 2 * ρ ^ 2 ≤ dist (p i) c ^ 2) (hhi : ∀ i, dist (p i) c ^ 2 ≤ ρ ^ 2)
    {z a b d : Fin n} (hzab : dist (p z) (p a) = dist (p z) (p b))
    (hzad : dist (p z) (p a) = dist (p z) (p d))
    (hab : Λ * ρ ^ 2 < dist (p a) (p b) ^ 2) (hbd : Λ * ρ ^ 2 < dist (p b) (p d) ^ 2)
    (had : Λ * ρ ^ 2 < dist (p a) (p d) ^ 2) : False := by
  have hx : ρ ^ 2 * (1 - (1 - σ ^ 2)) = σ ^ 2 * ρ ^ 2 := by ring
  obtain ⟨i, j, hij, hclose⟩ := scaled_annular_equidistant_triple_close_pair_sharp c (p z)
    ![p a, p b, p d] hρ (x := 1 - σ ^ 2) (t := Λ) hσ (by linarith) hchord
    (by rw [hx]; exact hlo z)
    (fun i ↦ by rw [hx]; fin_cases i <;> simp [hlo])
    (fun i ↦ by fin_cases i <;> simp [hhi])
    (fun i j ↦ by fin_cases i <;> fin_cases j <;> simp [← hzab, ← hzad])
  have hba : Λ * ρ ^ 2 < dist (p b) (p a) ^ 2 := by rwa [dist_comm]
  have hdb : Λ * ρ ^ 2 < dist (p d) (p b) ^ 2 := by rwa [dist_comm]
  have hda : Λ * ρ ^ 2 < dist (p d) (p a) ^ 2 := by rwa [dist_comm]
  fin_cases i <;> fin_cases j <;> simp at hij hclose <;> linarith

/-- Per-apex count. Let `S` be a set of ordered base pairs `(a, b)` of distinct indices, both
different from the apex `z`, farther than `Λρ²`, equidistant from `z` at a radius `r` with
`G r`. If no circle about an index carries three points pairwise farther than `Λρ²`, then with
the degree cap three, `3|S| ≤ 4 #{q ≠ z : G |zq|}`. An adaptation of
`three_mul_apexPairs_card_le` with the radius condition in the counted set. -/
private lemma three_mul_card_apex_pairs_le {p : Config n} {ρ Λ : ℝ}
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3)
    (htri : ∀ z a b d : Fin n, dist (p z) (p a) = dist (p z) (p b) →
      dist (p z) (p a) = dist (p z) (p d) → Λ * ρ ^ 2 < dist (p a) (p b) ^ 2 →
      Λ * ρ ^ 2 < dist (p b) (p d) ^ 2 → Λ * ρ ^ 2 < dist (p a) (p d) ^ 2 → False)
    (G : ℝ → Prop) [DecidablePred G] (z : Fin n) (S : Finset (Fin n × Fin n))
    (hS : ∀ ab ∈ S, ab.1 ≠ ab.2 ∧ z ≠ ab.1 ∧ z ≠ ab.2 ∧
      Λ * ρ ^ 2 < dist (p ab.1) (p ab.2) ^ 2 ∧ dist (p z) (p ab.1) = dist (p z) (p ab.2) ∧
      G (dist (p z) (p ab.1))) :
    3 * S.card ≤ 4 * ((Finset.univ : Finset (Fin n)).filter
      (fun q ↦ z ≠ q ∧ G (dist (p z) (p q)))).card := by
  set T := (Finset.univ : Finset (Fin n)).filter (fun q ↦ z ≠ q ∧ G (dist (p z) (p q)))
    with hT
  have hmemT : ∀ q, q ∈ T ↔ z ≠ q ∧ G (dist (p z) (p q)) := by
    intro q
    rw [hT, Finset.mem_filter]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨Finset.mem_univ _, h⟩⟩
  have hmapsS : ∀ ab ∈ S, dist (p z) (p ab.1) ∈ OrderedDistanceValues p := fun ab hab ↦
    dist_mem_orderedDistanceValues_of_ne (hS ab hab).2.1
  have hmapsT : ∀ q ∈ T, dist (p z) (p q) ∈ OrderedDistanceValues p := fun q hq ↦
    dist_mem_orderedDistanceValues_of_ne ((hmemT q).mp hq).1
  rw [Finset.card_eq_sum_card_fiberwise hmapsS, Finset.card_eq_sum_card_fiberwise hmapsT,
    Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ ↦ ?_
  set U := T.filter (fun q ↦ dist (p z) (p q) = r) with hU
  have hmemU : ∀ q, q ∈ U ↔ (z ≠ q ∧ G (dist (p z) (p q))) ∧ dist (p z) (p q) = r := by
    intro q
    rw [hU, Finset.mem_filter, hmemT]
  have hUcard : U.card ≤ 3 := by
    refine (Finset.card_le_card ?_).trans (hcap z r)
    intro q hq
    rw [hmemU] at hq
    rw [DistanceOutNeighborsAtValue, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hq.1.1, hq.2⟩
  have key := three_mul_card_filter_product_le_of_triangleFree U
    (fun a b ↦ a ≠ b ∧ Λ * ρ ^ 2 < dist (p a) (p b) ^ 2)
    (fun _ h ↦ h.1 rfl) (fun _ _ h ↦ ⟨h.1.symm, by rw [dist_comm]; exact h.2⟩) hUcard
    (fun a ha b hb d hd hab hbd had ↦ by
      rw [hmemU] at ha hb hd
      exact htri z a b d (ha.2.trans hb.2.symm) (ha.2.trans hd.2.symm) hab.2 hbd.2 had.2)
  refine le_trans (Nat.mul_le_mul_left 3 (Finset.card_le_card ?_)) key
  intro ab hab
  rw [Finset.mem_filter] at hab
  obtain ⟨hne, hza, hzb, hfar, heq, hG⟩ := hS ab hab.1
  rw [Finset.mem_filter, Finset.mem_product, hmemU, hmemU]
  exact ⟨⟨⟨⟨hza, hG⟩, hab.2⟩, ⟨hzb, heq ▸ hG⟩, heq ▸ hab.2⟩, hne, hfar⟩

/-- An apex of a pair farther than `T` (in squared distance) is farther than `T/4` from both
ends: `|ab| ≤ |az| + |zb| = 2|za|`. -/
private lemma lt_four_mul_sq_dist_apex {p : Config n} {T : ℝ} {z a b : Fin n}
    (heq : dist (p z) (p a) = dist (p z) (p b)) (hfar : T < dist (p a) (p b) ^ 2) :
    T < 4 * dist (p z) (p a) ^ 2 := by
  have htri : dist (p a) (p b) ≤ 2 * dist (p z) (p a) := by
    calc dist (p a) (p b) ≤ dist (p a) (p z) + dist (p z) (p b) := dist_triangle _ _ _
      _ = 2 * dist (p z) (p a) := by rw [dist_comm (p a) (p z), ← heq]; ring
  have h0 : 0 ≤ dist (p a) (p b) := dist_nonneg
  nlinarith [mul_le_mul htri htri h0 (by linarith)]

/-! ### Row AB2 -/

/-- Row AB2 of Lemma AB times `n²`: with the degree cap three, points in the annulus
`σ²ρ² ≤ |p_i - c|² ≤ ρ²` with `0 < σ`, the Step L0 chord condition `(1 - σ²)(σ + 1) ≤ σΛ`
(which gives `C((0, 2], λ)` for `Λ = λ²`) and squared band ends `Elo ≤ Ehi`, the band triples
satisfy `|T_j| ≤ (4/3)(P(Ehi ρ²) - P(Elo ρ²))`. In normalized form this is
`W_j - (4/3)(𝒜(e_{j+1}) - 𝒜(e_j)) ≤ 0`. -/
theorem card_apexBandTriples_le_window {p : Config n} {c : Point} {ρ σ Λ Elo Ehi : ℝ}
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) (hρ : 0 < ρ) (hσ : 0 < σ)
    (hchord : (1 - σ ^ 2) * (σ + 1) ≤ σ * Λ)
    (hlo : ∀ i, σ ^ 2 * ρ ^ 2 ≤ dist (p i) c ^ 2) (hhi : ∀ i, dist (p i) c ^ 2 ≤ ρ ^ 2)
    (hE : Elo ≤ Ehi) :
    ((apexBandTriples p ρ Λ Elo Ehi).card : ℝ) ≤
      4 / 3 * (∑ j, ((((Finset.univ : Finset (Fin n)).filter
          (fun q ↦ dist (p j) (p q) ^ 2 ≤ Ehi * ρ ^ 2)).card : ℝ) - 1) -
        ∑ j, ((((Finset.univ : Finset (Fin n)).filter
          (fun q ↦ dist (p j) (p q) ^ 2 ≤ Elo * ρ ^ 2)).card : ℝ) - 1)) := by
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hEρ : Elo * ρ ^ 2 ≤ Ehi * ρ ^ 2 := mul_le_mul_of_nonneg_right hE hρ2.le
  have htri : ∀ z a b d : Fin n, dist (p z) (p a) = dist (p z) (p b) →
      dist (p z) (p a) = dist (p z) (p d) → Λ * ρ ^ 2 < dist (p a) (p b) ^ 2 →
      Λ * ρ ^ 2 < dist (p b) (p d) ^ 2 → Λ * ρ ^ 2 < dist (p a) (p d) ^ 2 → False :=
    fun _ _ _ _ h1 h2 h3 h4 h5 ↦
      false_of_three_far_on_apex_circle hρ hσ hchord hlo hhi h1 h2 h3 h4 h5
  have hnat : 3 * (apexBandTriples p ρ Λ Elo Ehi).card ≤
      4 * ∑ z, ((Finset.univ : Finset (Fin n)).filter (fun q ↦
        Elo * ρ ^ 2 < dist (p z) (p q) ^ 2 ∧ dist (p z) (p q) ^ 2 ≤ Ehi * ρ ^ 2)).card := by
    rw [card_eq_sum_apex_fibers, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun z _ ↦ ?_
    have h := three_mul_card_apex_pairs_le hcap htri
      (fun r ↦ Elo * ρ ^ 2 < r ^ 2 ∧ r ^ 2 ≤ Ehi * ρ ^ 2) z
      ((Finset.univ : Finset (Fin n × Fin n)).filter
        (fun ab ↦ (z, ab) ∈ apexBandTriples p ρ Λ Elo Ehi))
      (fun ab hab ↦ by
        rw [Finset.mem_filter, mem_apexBandTriples] at hab
        obtain ⟨-, hne, hza, hzb, hfar, heq, h1, h2⟩ := hab
        exact ⟨hne, hza, hzb, hfar, heq, h1, h2⟩)
    refine h.trans (Nat.mul_le_mul_left _ (Finset.card_le_card ?_))
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
    exact hq.2
  have hwin : ∀ z, (((Finset.univ : Finset (Fin n)).filter (fun q ↦
      Elo * ρ ^ 2 < dist (p z) (p q) ^ 2 ∧ dist (p z) (p q) ^ 2 ≤ Ehi * ρ ^ 2)).card : ℝ) +
      (((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p z) (p q) ^ 2 ≤ Elo * ρ ^ 2)).card : ℝ) ≤
      (((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p z) (p q) ^ 2 ≤ Ehi * ρ ^ 2)).card : ℝ) := fun z ↦ by
    have hdisj : Disjoint
        ((Finset.univ : Finset (Fin n)).filter (fun q ↦
          Elo * ρ ^ 2 < dist (p z) (p q) ^ 2 ∧ dist (p z) (p q) ^ 2 ≤ Ehi * ρ ^ 2))
        ((Finset.univ : Finset (Fin n)).filter
          (fun q ↦ dist (p z) (p q) ^ 2 ≤ Elo * ρ ^ 2)) :=
      Finset.disjoint_filter.mpr fun q _ h1 h2 ↦ by linarith [h1.1]
    have hsub : (Finset.univ : Finset (Fin n)).filter (fun q ↦
          Elo * ρ ^ 2 < dist (p z) (p q) ^ 2 ∧ dist (p z) (p q) ^ 2 ≤ Ehi * ρ ^ 2) ∪
        (Finset.univ : Finset (Fin n)).filter
          (fun q ↦ dist (p z) (p q) ^ 2 ≤ Elo * ρ ^ 2) ⊆
        (Finset.univ : Finset (Fin n)).filter
          (fun q ↦ dist (p z) (p q) ^ 2 ≤ Ehi * ρ ^ 2) := by
      intro q hq
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hq ⊢
      rcases hq with hq | hq
      · exact hq.2
      · exact hq.trans hEρ
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj] at hc
    exact_mod_cast hc
  have hreal : 3 * ((apexBandTriples p ρ Λ Elo Ehi).card : ℝ) ≤
      4 * ∑ z, (((Finset.univ : Finset (Fin n)).filter (fun q ↦
        Elo * ρ ^ 2 < dist (p z) (p q) ^ 2 ∧ dist (p z) (p q) ^ 2 ≤ Ehi * ρ ^ 2)).card : ℝ) := by
    exact_mod_cast hnat
  have hsum : ∑ z, (((Finset.univ : Finset (Fin n)).filter (fun q ↦
        Elo * ρ ^ 2 < dist (p z) (p q) ^ 2 ∧ dist (p z) (p q) ^ 2 ≤ Ehi * ρ ^ 2)).card : ℝ) ≤
      ∑ j, ((((Finset.univ : Finset (Fin n)).filter
          (fun q ↦ dist (p j) (p q) ^ 2 ≤ Ehi * ρ ^ 2)).card : ℝ) - 1) -
        ∑ j, ((((Finset.univ : Finset (Fin n)).filter
          (fun q ↦ dist (p j) (p q) ^ 2 ≤ Elo * ρ ^ 2)).card : ℝ) - 1) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum fun z _ ↦ by linarith [hwin z]
  linarith

/-! ### Row AB1 -/

/-- For a squared threshold `T ≥ 0`, the ordered pairs of distinct indices farther than `T`
number `n² - n - P(T)`. -/
private lemma card_far_pairs_eq {p : Config n} {T : ℝ} (hT : 0 ≤ T) :
    ((((Finset.univ : Finset (Fin n)).offDiag.filter
      (fun ab ↦ T < dist (p ab.1) (p ab.2) ^ 2)).card : ℕ) : ℝ) =
      (n : ℝ) * n - n - ∑ j, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ T)).card : ℝ) - 1) := by
  have hirr : ∀ a : Fin n, ¬T < dist (p a) (p a) ^ 2 := fun a h ↦ by
    rw [dist_self] at h
    nlinarith
  rw [card_offDiag_filter_eq_sum_rows (fun a b ↦ T < dist (p a) (p b) ^ 2) hirr]
  push_cast
  have hsplit : ∀ z, (((Finset.univ : Finset (Fin n)).filter
      (fun q ↦ T < dist (p z) (p q) ^ 2)).card : ℝ) +
      (((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p z) (p q) ^ 2 ≤ T)).card : ℝ) = n := fun z ↦ by
    have hs := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (p := fun q ↦ T < dist (p z) (p q) ^ 2)
    simp only [not_lt, Finset.card_univ, Fintype.card_fin] at hs
    exact_mod_cast hs
  have hS := Finset.sum_congr rfl
    (fun z (_ : z ∈ (Finset.univ : Finset (Fin n))) ↦ hsplit z)
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hS
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  linarith

/-- Band location: if `F 0 < v ≤ F m`, then `F j < v ≤ F (j + 1)` for some `j < m`. -/
private lemma exists_band_of_mem {F : ℕ → ℝ} {v : ℝ} :
    ∀ m : ℕ, F 0 < v → v ≤ F m → ∃ j < m, F j < v ∧ v ≤ F (j + 1)
  | 0, h0, hm => absurd (h0.trans_le hm) (lt_irrefl _)
  | m + 1, h0, hm => by
    by_cases hv : v ≤ F m
    · obtain ⟨j, hj, h⟩ := exists_band_of_mem m h0 hv
      exact ⟨j, by omega, h⟩
    · exact ⟨m, by omega, not_le.mp hv, hm⟩

/-- Row AB1 of Lemma AB times `n²`. Let the band edges `E 0, …, E m` (squared, scaled by `ρ²`)
satisfy `4 E 0 ≤ Λ` (that is, `e₀ ≤ λ/2`) and `4 ≤ E m` (every apex distance is at most `2ρ`),
with `0 ≤ Λ`. For points within `ρ` of `c`, with no three collinear, the band triples over the
bands `(E j, E (j + 1)]`, `j < m`, satisfy
`Σ_j |T_j| ≥ 2(n² - n - P(Λρ²)) - 2nQ`, where `Q = 3D - n + 1`. In normalized form this is
`-Σ_j W_j - 2𝒜(λ) - 6dd - 4ee ≤ -4`. -/
theorem sum_card_apexBandTriples_ge {p : Config n} {c : Point} {ρ Λ : ℝ} {m : ℕ}
    {E : ℕ → ℝ} (hp : Function.Injective p)
    (hgp3 : NonTrilinear (Config.toFinset p : Set Point)) (hρ : 0 < ρ)
    (hhi : ∀ i, dist (p i) c ^ 2 ≤ ρ ^ 2) (hΛ : 0 ≤ Λ) (hE0 : 4 * E 0 ≤ Λ) (hEm : 4 ≤ E m) :
    2 * ((n : ℝ) * n - n - ∑ j, ((((Finset.univ : Finset (Fin n)).filter
        (fun q ↦ dist (p j) (p q) ^ 2 ≤ Λ * ρ ^ 2)).card : ℝ) - 1)) -
        2 * (n : ℝ) * (3 * (NumDistancesOrdered p : ℝ) - (n : ℝ) + 1) ≤
      ∑ j ∈ Finset.range m, ((apexBandTriples p ρ Λ (E j) (E (j + 1))).card : ℝ) := by
  have hρ2 : 0 < ρ ^ 2 := by positivity
  have hle : ∀ i, dist (p i) c ≤ ρ := fun i ↦ by
    nlinarith [hhi i, dist_nonneg (x := p i) (y := c)]
  have hcover : farEquidistantTriples p ρ Λ ⊆
      (Finset.range m).biUnion (fun j ↦ apexBandTriples p ρ Λ (E j) (E (j + 1))) := by
    intro x hx
    obtain ⟨hne, hza, hzb, hfar, heq⟩ := mem_farEquidistantTriples.mp hx
    have h4 := lt_four_mul_sq_dist_apex heq hfar
    have hlow : E 0 * ρ ^ 2 < dist (p x.1) (p x.2.1) ^ 2 := by
      have := mul_le_mul_of_nonneg_right hE0 hρ2.le
      linarith
    have hup : dist (p x.1) (p x.2.1) ^ 2 ≤ E m * ρ ^ 2 := by
      have hr : dist (p x.1) (p x.2.1) ≤ 2 * ρ := by
        calc dist (p x.1) (p x.2.1) ≤ dist (p x.1) c + dist c (p x.2.1) := dist_triangle _ _ _
          _ ≤ ρ + ρ := by rw [dist_comm c]; exact add_le_add (hle _) (hle _)
          _ = 2 * ρ := by ring
      have hr0 : 0 ≤ dist (p x.1) (p x.2.1) := dist_nonneg
      have := mul_le_mul_of_nonneg_right hEm hρ2.le
      nlinarith
    obtain ⟨j, hj, hj1, hj2⟩ := exists_band_of_mem (F := fun j ↦ E j * ρ ^ 2) m hlow hup
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_range.mpr hj,
      mem_apexBandTriples.mpr ⟨hne, hza, hzb, hfar, heq, hj1, hj2⟩⟩
  have hcardT : (farEquidistantTriples p ρ Λ).card ≤
      ∑ j ∈ Finset.range m, (apexBandTriples p ρ Λ (E j) (E (j + 1))).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have hwit := (sum_witnesses_le_card_farEquidistantTriples hp ρ Λ).trans hcardT
  have hwitR : ∑ ab ∈ (Finset.univ : Finset (Fin n)).offDiag.filter
        (fun ab ↦ Λ * ρ ^ 2 < dist (p ab.1) (p ab.2) ^ 2),
        ((IndexedEquidistantWitnesses p ab.1 ab.2).card : ℝ) ≤
      ∑ j ∈ Finset.range m, ((apexBandTriples p ρ Λ (E j) (E (j + 1))).card : ℝ) := by
    exact_mod_cast hwit
  have hdef := sum_two_sub_witnesses_le hp hgp3
    (Finset.filter_subset (fun ab ↦ Λ * ρ ^ 2 < dist (p ab.1) (p ab.2) ^ 2)
      (Finset.univ : Finset (Fin n)).offDiag)
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hdef
  have hΦ := card_far_pairs_eq (p := p) (T := Λ * ρ ^ 2) (by positivity)
  linarith

/-! ### Disjoint bands -/

/-- Monotone edges: `E j ≤ E k` for `j ≤ k ≤ m` when `E i ≤ E (i + 1)` for every `i < m`. -/
private lemma edge_mono {E : ℕ → ℝ} {m : ℕ} (hmono : ∀ j < m, E j ≤ E (j + 1)) {j k : ℕ}
    (hjk : j ≤ k) (hk : k ≤ m) : E j ≤ E k := by
  revert hk
  induction k, hjk using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ k _ ih => intro hk; exact (ih (by omega)).trans (hmono k (by omega))

/-- For monotone band edges the bands are disjoint, so the band sums of a function that is
nonnegative on the far equidistant triples are at most its sum over all of them. -/
private lemma sum_bands_le_sum_far {p : Config n} {ρ Λ : ℝ} {m : ℕ} {E : ℕ → ℝ} (hρ : 0 < ρ)
    (hmono : ∀ j < m, E j ≤ E (j + 1)) (f : Fin n × Fin n × Fin n → ℝ)
    (hf : ∀ x ∈ farEquidistantTriples p ρ Λ, 0 ≤ f x) :
    ∑ j ∈ Finset.range m, ∑ x ∈ apexBandTriples p ρ Λ (E j) (E (j + 1)), f x ≤
      ∑ x ∈ farEquidistantTriples p ρ Λ, f x := by
  have hρ2 : 0 ≤ ρ ^ 2 := by positivity
  have key : ∀ j k, j < k → k < m → Disjoint (apexBandTriples p ρ Λ (E j) (E (j + 1)))
      (apexBandTriples p ρ Λ (E k) (E (k + 1))) := by
    intro j k hjk hk
    rw [Finset.disjoint_left]
    intro x hxj hxk
    have h1 := (mem_apexBandTriples.mp hxj).2.2.2.2.2.2
    have h2 := (mem_apexBandTriples.mp hxk).2.2.2.2.2.1
    have hE := mul_le_mul_of_nonneg_right
      (edge_mono hmono (show j + 1 ≤ k by omega) hk.le) hρ2
    linarith
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range m) : Set ℕ)
      (fun j ↦ apexBandTriples p ρ Λ (E j) (E (j + 1))) := by
    intro j hj k hk hjk
    rcases lt_or_gt_of_ne hjk with h | h
    · exact key j k h (Finset.mem_range.mp (Finset.mem_coe.mp hk))
    · exact (key k j h (Finset.mem_range.mp (Finset.mem_coe.mp hj))).symm
  rw [← Finset.sum_biUnion hdisj]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro x hx
    obtain ⟨j, -, hxj⟩ := Finset.mem_biUnion.mp hx
    exact apexBandTriples_subset p ρ Λ _ _ hxj
  · intro x hx _
    exact hf x hx

/-! ### Rows AB6 -/

/-- Row AB6u of Lemma AB times `n²` (from AB5). For monotone band edges, points in the annulus
`σ²ρ² ≤ |p_i - c|²`, no three collinear and the degree cap three, the base-pair excess sums
over the bands satisfy `Σ_j Σ_{T_j}(y_a + y_b) ≤ 12 (Σ_i y_i)(D - R(Λρ²))`. The assembly
bounds `n⁻¹ Σ_i y_i ≤ Y_hi` to obtain the normalized row
`Σ_j U_j - 12 Y_hi (dd - ℛ(λ)) ≤ 0`. -/
theorem sum_bands_base_excess_le_far_palette {p : Config n} {c : Point} {ρ σ Λ : ℝ} {m : ℕ}
    {E : ℕ → ℝ} (hp : Function.Injective p)
    (hgp3 : NonTrilinear (Config.toFinset p : Set Point))
    (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) (hρ : 0 < ρ)
    (hlo : ∀ i, σ ^ 2 * ρ ^ 2 ≤ dist (p i) c ^ 2) (hmono : ∀ j < m, E j ≤ E (j + 1)) :
    ∑ j ∈ Finset.range m, ∑ x ∈ apexBandTriples p ρ Λ (E j) (E (j + 1)),
        (radialExcess p c ρ σ x.2.1 + radialExcess p c ρ σ x.2.2) ≤
      12 * (∑ i, radialExcess p c ρ σ i) *
        ((NumDistancesOrdered p : ℝ) -
          (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ Λ * ρ ^ 2)).card : ℝ)) := by
  set K := (NumDistancesOrdered p : ℝ) -
    (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ Λ * ρ ^ 2)).card : ℝ) with hK
  have hy0 : ∀ i, 0 ≤ radialExcess p c ρ σ i := radialExcess_nonneg hρ hlo
  refine (sum_bands_le_sum_far hρ hmono _ fun x _ ↦ add_nonneg (hy0 _) (hy0 _)).trans ?_
  rw [Finset.sum_add_distrib]
  have hfa : ∀ a, (((Finset.univ : Finset (Fin n)).filter
      (fun b ↦ (a, b) ∈ (Finset.univ : Finset (Fin n × Fin n)).filter
        (fun ab ↦ ab.1 ≠ ab.2 ∧ Λ * ρ ^ 2 < dist (p ab.1) (p ab.2) ^ 2))).card : ℝ) ≤
      3 * K := fun a ↦ by
    have heq : (Finset.univ : Finset (Fin n)).filter
        (fun b ↦ (a, b) ∈ (Finset.univ : Finset (Fin n × Fin n)).filter
          (fun ab ↦ ab.1 ≠ ab.2 ∧ Λ * ρ ^ 2 < dist (p ab.1) (p ab.2) ^ 2)) =
        (Finset.univ : Finset (Fin n)).filter
          (fun q ↦ a ≠ q ∧ Λ * ρ ^ 2 < dist (p a) (p q) ^ 2) := by
      apply Finset.filter_congr
      intro q _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [heq]
    exact card_sq_far_le_three_mul_far_palette hcap _ a
  have hfb : ∀ b, (((Finset.univ : Finset (Fin n)).filter
      (fun a ↦ (a, b) ∈ (Finset.univ : Finset (Fin n × Fin n)).filter
        (fun ab ↦ ab.1 ≠ ab.2 ∧ Λ * ρ ^ 2 < dist (p ab.1) (p ab.2) ^ 2))).card : ℝ) ≤
      3 * K := fun b ↦ by
    have heq : (Finset.univ : Finset (Fin n)).filter
        (fun a ↦ (a, b) ∈ (Finset.univ : Finset (Fin n × Fin n)).filter
          (fun ab ↦ ab.1 ≠ ab.2 ∧ Λ * ρ ^ 2 < dist (p ab.1) (p ab.2) ^ 2)) =
        (Finset.univ : Finset (Fin n)).filter
          (fun q ↦ b ≠ q ∧ Λ * ρ ^ 2 < dist (p b) (p q) ^ 2) := by
      apply Finset.filter_congr
      intro q _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [ne_comm, dist_comm]
    rw [heq]
    exact card_sq_far_le_three_mul_far_palette hcap _ b
  have h1 : ∑ x ∈ farEquidistantTriples p ρ Λ, radialExcess p c ρ σ x.2.1 ≤
      6 * (∑ i, radialExcess p c ρ σ i) * K := by
    calc ∑ x ∈ farEquidistantTriples p ρ Λ, radialExcess p c ρ σ x.2.1
        ≤ 2 * ∑ ab ∈ (Finset.univ : Finset (Fin n × Fin n)).filter
            (fun ab ↦ ab.1 ≠ ab.2 ∧ Λ * ρ ^ 2 < dist (p ab.1) (p ab.2) ^ 2),
            radialExcess p c ρ σ ab.1 :=
          sum_farEquidistantTriples_pair_le hp hgp3 ρ Λ (fun ab ↦ radialExcess p c ρ σ ab.1)
            fun ab ↦ hy0 _
      _ = 2 * ∑ a, (((Finset.univ : Finset (Fin n)).filter
            (fun b ↦ (a, b) ∈ (Finset.univ : Finset (Fin n × Fin n)).filter
              (fun ab ↦ ab.1 ≠ ab.2 ∧ Λ * ρ ^ 2 < dist (p ab.1) (p ab.2) ^ 2))).card : ℝ) *
            radialExcess p c ρ σ a := by
          rw [sum_pairs_fst_eq _ (radialExcess p c ρ σ)]
      _ ≤ 2 * ∑ a, 3 * K * radialExcess p c ρ σ a :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ ↦
            mul_le_mul_of_nonneg_right (hfa a) (hy0 a)) (by norm_num)
      _ = 6 * (∑ i, radialExcess p c ρ σ i) * K := by
          rw [← Finset.mul_sum]
          ring
  have h2 : ∑ x ∈ farEquidistantTriples p ρ Λ, radialExcess p c ρ σ x.2.2 ≤
      6 * (∑ i, radialExcess p c ρ σ i) * K := by
    calc ∑ x ∈ farEquidistantTriples p ρ Λ, radialExcess p c ρ σ x.2.2
        ≤ 2 * ∑ ab ∈ (Finset.univ : Finset (Fin n × Fin n)).filter
            (fun ab ↦ ab.1 ≠ ab.2 ∧ Λ * ρ ^ 2 < dist (p ab.1) (p ab.2) ^ 2),
            radialExcess p c ρ σ ab.2 :=
          sum_farEquidistantTriples_pair_le hp hgp3 ρ Λ (fun ab ↦ radialExcess p c ρ σ ab.2)
            fun ab ↦ hy0 _
      _ = 2 * ∑ b, (((Finset.univ : Finset (Fin n)).filter
            (fun a ↦ (a, b) ∈ (Finset.univ : Finset (Fin n × Fin n)).filter
              (fun ab ↦ ab.1 ≠ ab.2 ∧ Λ * ρ ^ 2 < dist (p ab.1) (p ab.2) ^ 2))).card : ℝ) *
            radialExcess p c ρ σ b := by
          rw [sum_pairs_snd_eq _ (radialExcess p c ρ σ)]
      _ ≤ 2 * ∑ b, 3 * K * radialExcess p c ρ σ b :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ ↦
            mul_le_mul_of_nonneg_right (hfb b) (hy0 b)) (by norm_num)
      _ = 6 * (∑ i, radialExcess p c ρ σ i) * K := by
          rw [← Finset.mul_sum]
          ring
  linarith

/-- Row AB6v of Lemma AB times `n²` (from AB5). For monotone band edges, the degree cap three,
points in the annulus `σ²ρ² ≤ |p_i - c|² ≤ ρ²` with `0 < σ`, the Step L0 chord condition
`(1 - σ²)(σ + 1) ≤ σΛ` and a squared threshold `H` with `4H ≤ Λ` (that is, `h ≤ λ/2`), the
apex excess sums over the bands satisfy `Σ_j Σ_{T_j} y_z ≤ 4 (Σ_i y_i)(D - R(Hρ²))`. The
assembly bounds `n⁻¹ Σ_i y_i ≤ Y_hi` to obtain the normalized row
`Σ_j V_j - 4 Y_hi (dd - ℛ(h)) ≤ 0`. -/
theorem sum_bands_apex_excess_le_far_palette {p : Config n} {c : Point} {ρ σ Λ H : ℝ} {m : ℕ}
    {E : ℕ → ℝ} (hcap : ∀ i r, (DistanceOutNeighborsAtValue p i r).card ≤ 3) (hρ : 0 < ρ)
    (hσ : 0 < σ) (hchord : (1 - σ ^ 2) * (σ + 1) ≤ σ * Λ)
    (hlo : ∀ i, σ ^ 2 * ρ ^ 2 ≤ dist (p i) c ^ 2) (hhi : ∀ i, dist (p i) c ^ 2 ≤ ρ ^ 2)
    (hH : 4 * H ≤ Λ) (hmono : ∀ j < m, E j ≤ E (j + 1)) :
    ∑ j ∈ Finset.range m, ∑ x ∈ apexBandTriples p ρ Λ (E j) (E (j + 1)),
        radialExcess p c ρ σ x.1 ≤
      4 * (∑ i, radialExcess p c ρ σ i) *
        ((NumDistancesOrdered p : ℝ) -
          (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ H * ρ ^ 2)).card : ℝ)) := by
  have hρ2 : 0 < ρ ^ 2 := by positivity
  set K := (NumDistancesOrdered p : ℝ) -
    (((OrderedDistanceValues p).filter (fun r ↦ r ^ 2 ≤ H * ρ ^ 2)).card : ℝ) with hK
  have hy0 : ∀ i, 0 ≤ radialExcess p c ρ σ i := radialExcess_nonneg hρ hlo
  refine (sum_bands_le_sum_far hρ hmono _ fun x _ ↦ hy0 _).trans ?_
  have htri : ∀ z a b d : Fin n, dist (p z) (p a) = dist (p z) (p b) →
      dist (p z) (p a) = dist (p z) (p d) → Λ * ρ ^ 2 < dist (p a) (p b) ^ 2 →
      Λ * ρ ^ 2 < dist (p b) (p d) ^ 2 → Λ * ρ ^ 2 < dist (p a) (p d) ^ 2 → False :=
    fun _ _ _ _ h1 h2 h3 h4 h5 ↦
      false_of_three_far_on_apex_circle hρ hσ hchord hlo hhi h1 h2 h3 h4 h5
  have hHρ := mul_le_mul_of_nonneg_right hH hρ2.le
  have hz : ∀ z, (((Finset.univ : Finset (Fin n × Fin n)).filter
      (fun ab ↦ (z, ab) ∈ farEquidistantTriples p ρ Λ)).card : ℝ) ≤ 4 * K := fun z ↦ by
    have h3 : 3 * ((Finset.univ : Finset (Fin n × Fin n)).filter
        (fun ab ↦ (z, ab) ∈ farEquidistantTriples p ρ Λ)).card ≤
        4 * ((Finset.univ : Finset (Fin n)).filter
          (fun q ↦ z ≠ q ∧ H * ρ ^ 2 < dist (p z) (p q) ^ 2)).card :=
      three_mul_card_apex_pairs_le hcap htri (fun r ↦ H * ρ ^ 2 < r ^ 2) z _
        (fun ab hab ↦ by
          rw [Finset.mem_filter, mem_farEquidistantTriples] at hab
          obtain ⟨-, hne, hza, hzb, hfar, heq⟩ := hab
          have h4 := lt_four_mul_sq_dist_apex heq hfar
          refine ⟨hne, hza, hzb, hfar, heq, ?_⟩
          show H * ρ ^ 2 < dist (p z) (p ab.1) ^ 2
          linarith)
    have h3R : 3 * (((Finset.univ : Finset (Fin n × Fin n)).filter
        (fun ab ↦ (z, ab) ∈ farEquidistantTriples p ρ Λ)).card : ℝ) ≤
        4 * (((Finset.univ : Finset (Fin n)).filter
          (fun q ↦ z ≠ q ∧ H * ρ ^ 2 < dist (p z) (p q) ^ 2)).card : ℝ) := by
      exact_mod_cast h3
    have hf := card_sq_far_le_three_mul_far_palette hcap (H * ρ ^ 2) z
    linarith
  rw [sum_eq_sum_apex_fibers]
  calc ∑ z, ∑ ab ∈ (Finset.univ : Finset (Fin n × Fin n)).filter
          (fun ab ↦ (z, ab) ∈ farEquidistantTriples p ρ Λ), radialExcess p c ρ σ (z, ab).1
      = ∑ z, (((Finset.univ : Finset (Fin n × Fin n)).filter
          (fun ab ↦ (z, ab) ∈ farEquidistantTriples p ρ Λ)).card : ℝ) *
          radialExcess p c ρ σ z := by
        refine Finset.sum_congr rfl fun z _ ↦ ?_
        simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ z, 4 * K * radialExcess p c ρ σ z :=
        Finset.sum_le_sum fun z _ ↦ mul_le_mul_of_nonneg_right (hz z) (hy0 z)
    _ = 4 * (∑ i, radialExcess p c ρ σ i) * K := by
        rw [← Finset.mul_sum]
        ring

/-! ### Box -/

/-- Box for `W_j`: with no three collinear, the band triples number at most `2n²` (each ordered
pair of distinct indices has at most two equidistant witnesses), so `W_j ≤ 2`. -/
theorem card_apexBandTriples_le_two_mul {p : Config n} (hp : Function.Injective p)
    (hgp3 : NonTrilinear (Config.toFinset p : Set Point)) (ρ Λ Elo Ehi : ℝ) :
    ((apexBandTriples p ρ Λ Elo Ehi).card : ℝ) ≤ 2 * (n : ℝ) * n := by
  have h := (Finset.card_le_card (apexBandTriples_subset p ρ Λ Elo Ehi)).trans
    (card_farEquidistantTriples_le hp hgp3 ρ Λ)
  have hR : ((apexBandTriples p ρ Λ Elo Ehi).card : ℝ) ≤ ((2 * (n * n) : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at hR
  linarith

/-- Box for `Σ_j W_j`: for monotone band edges and no three collinear, the band triples over
all bands number at most `2n²`. -/
theorem sum_card_apexBandTriples_le_two_mul {p : Config n} {ρ Λ : ℝ} {m : ℕ} {E : ℕ → ℝ}
    (hp : Function.Injective p) (hgp3 : NonTrilinear (Config.toFinset p : Set Point))
    (hρ : 0 < ρ) (hmono : ∀ j < m, E j ≤ E (j + 1)) :
    ∑ j ∈ Finset.range m, ((apexBandTriples p ρ Λ (E j) (E (j + 1))).card : ℝ) ≤
      2 * (n : ℝ) * n := by
  have h := sum_bands_le_sum_far (p := p) (Λ := Λ) hρ hmono (fun _ ↦ (1 : ℝ))
    fun _ _ ↦ zero_le_one
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  have hR : ((farEquidistantTriples p ρ Λ).card : ℝ) ≤ ((2 * (n * n) : ℕ) : ℝ) := by
    exact_mod_cast card_farEquidistantTriples_le hp hgp3 ρ Λ
  push_cast at hR
  linarith

/-- Box for `U_j`, lower side: in the annulus `σ²ρ² ≤ |p_i - c|²`, the base-pair excess sum
over the band triples is nonnegative. -/
theorem sum_apexBandTriples_base_excess_nonneg {p : Config n} {c : Point} {ρ σ Λ Elo Ehi : ℝ}
    (hρ : 0 < ρ) (hlo : ∀ i, σ ^ 2 * ρ ^ 2 ≤ dist (p i) c ^ 2) :
    0 ≤ ∑ x ∈ apexBandTriples p ρ Λ Elo Ehi,
      (radialExcess p c ρ σ x.2.1 + radialExcess p c ρ σ x.2.2) :=
  Finset.sum_nonneg fun _ _ ↦
    add_nonneg (radialExcess_nonneg hρ hlo _) (radialExcess_nonneg hρ hlo _)

/-- Box for `U_j`, upper side: in the annulus `|p_i - c|² ≤ ρ²`, the base-pair excess sum over
the band triples is at most `2(1 - σ²)|T_j|` (that is, `U_j ≤ 2ω W_j`). -/
theorem sum_apexBandTriples_base_excess_le {p : Config n} {c : Point} {ρ σ Λ Elo Ehi : ℝ}
    (hρ : 0 < ρ) (hhi : ∀ i, dist (p i) c ^ 2 ≤ ρ ^ 2) :
    ∑ x ∈ apexBandTriples p ρ Λ Elo Ehi,
        (radialExcess p c ρ σ x.2.1 + radialExcess p c ρ σ x.2.2) ≤
      2 * (1 - σ ^ 2) * ((apexBandTriples p ρ Λ Elo Ehi).card : ℝ) := by
  have h := Finset.sum_le_card_nsmul (apexBandTriples p ρ Λ Elo Ehi)
    (fun x ↦ radialExcess p c ρ σ x.2.1 + radialExcess p c ρ σ x.2.2) (2 * (1 - σ ^ 2))
    fun x _ ↦ by
      have h1 := radialExcess_le (σ := σ) hρ hhi x.2.1
      have h2 := radialExcess_le (σ := σ) hρ hhi x.2.2
      change radialExcess p c ρ σ x.2.1 + radialExcess p c ρ σ x.2.2 ≤ 2 * (1 - σ ^ 2)
      linarith
  rw [nsmul_eq_mul] at h
  linarith

/-- Box for `V_j`, lower side: in the annulus `σ²ρ² ≤ |p_i - c|²`, the apex excess sum over
the band triples is nonnegative. -/
theorem sum_apexBandTriples_apex_excess_nonneg {p : Config n} {c : Point} {ρ σ Λ Elo Ehi : ℝ}
    (hρ : 0 < ρ) (hlo : ∀ i, σ ^ 2 * ρ ^ 2 ≤ dist (p i) c ^ 2) :
    0 ≤ ∑ x ∈ apexBandTriples p ρ Λ Elo Ehi, radialExcess p c ρ σ x.1 :=
  Finset.sum_nonneg fun _ _ ↦ radialExcess_nonneg hρ hlo _

/-- Box for `V_j`, upper side: in the annulus `|p_i - c|² ≤ ρ²`, the apex excess sum over the
band triples is at most `(1 - σ²)|T_j|` (that is, `V_j ≤ ω W_j`). -/
theorem sum_apexBandTriples_apex_excess_le {p : Config n} {c : Point} {ρ σ Λ Elo Ehi : ℝ}
    (hρ : 0 < ρ) (hhi : ∀ i, dist (p i) c ^ 2 ≤ ρ ^ 2) :
    ∑ x ∈ apexBandTriples p ρ Λ Elo Ehi, radialExcess p c ρ σ x.1 ≤
      (1 - σ ^ 2) * ((apexBandTriples p ρ Λ Elo Ehi).card : ℝ) := by
  have h := Finset.sum_le_card_nsmul (apexBandTriples p ρ Λ Elo Ehi)
    (fun x ↦ radialExcess p c ρ σ x.1) (1 - σ ^ 2)
    fun x _ ↦ radialExcess_le (σ := σ) hρ hhi x.1
  rw [nsmul_eq_mul] at h
  linarith

end Esgk
