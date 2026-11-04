/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.RefinedClosePairGeometry
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Shift
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# The sharp same-side chord bound on an (apex distance, radius) box

Formalizes Lemma C and Lemma C′ of `docs/results/explicit-constant-gain-5-239-2026-10-20.md`
(§2), the chord evaluator `chord_sq_box` / `Chords._adapt` of
`scripts/verify_constant_gain_5_239.py`, which `scripts/verify_constant_gain_1_40.py` uses for
the chord side conditions `C(I, t)`. All lengths carry the scale `ρ`; thresholds are squared.

Setting. Let `c` be a centre, `ρ > 0`, and let three points `q i` lie in the annulus
`σ²ρ² ≤ |x - c|² ≤ ρ²`, all at the same distance `r = Rρ` from an apex `p` with
`|p - c| = Aρ`. In the frame with `p - c` on the positive first axis, a point of the circle is
`q = p + (X, Y)` with `X² + Y² = r²` and `|q - c|² = (A² + R²)ρ² + 2AρX`, so the annulus
condition reads `X / r ∈ [L, L + w]` with

`L = (σ² - A² - R²) / (2AR)`, `w = (1 - σ²) / (2AR)`.

Two of the three points lie on the same side of the axis (`three_has_same_transverse_side`).

* **Cosine window** (`same_side_inner_ge_of_mem_cosine_window`,
  `same_side_chord_sq_le_of_mem_cosine_window`): two points of a circle of radius `r` on the
  same side of a diameter, with first coordinates in `[r u, r v]`, have inner product at least
  `r² (u v + √(1 - u²) √(1 - v²))`; the proof compares the angles `arccos (X / r)` and uses
  that `cos` decreases on `[0, π]`.
* **Arc window.** With `cl` the clamp to `[-1, 1]` (`unitClamp`), the arc
  `f(L, w) = arccos (cl L) - arccos (cl (L + w))` is nondecreasing in `w`; for fixed `w ≥ 0`
  it is nondecreasing on `(-∞, -1]`, nonincreasing on `[-1, -w/2]`, nondecreasing on
  `[-w/2, 1 - w]` and nonincreasing on `[1 - w, ∞)`. The middle pieces come from the
  derivative `1/√(1 - (m + w/2)²) - 1/√(1 - (m - w/2)²) ≥ 0` of
  `m ↦ arccos (m - w/2) - arccos (m + w/2)` on `[0, 1 - w/2]` and the symmetry
  `arccos (-x) = π - arccos x`. Hence on `[Llo, Lhi]` the maximum of `f(·, w)` is at `Llo`,
  `Lhi`, `-1` (if inside) or `1 - w` (if inside).
* **Box lemma** (`exists_dist_sq_le_of_mem_chord_box`, Lemma C′): on the box
  `A ∈ [a0, a1]`, `R ∈ [r0, r1]`, a lower bound `β` of `cos f` at the candidates, stated
  without square roots (`WindowCosineBound`), gives a pair at squared distance at most
  `2 r1² (1 - β) ρ²`. The trivial cell gives `4 r1² ρ²` (`exists_dist_sq_le_four_mul_sq`).
* **Box tree** (`ChordBoxTree`): rational boxes refined at midpoints, as `Chords._adapt`, with
  a structurally recursive `Bool` check over `ℚ` (`ChordBoxTree.check`) and its soundness
  (`ChordBoxTree.exists_dist_sq_le_of_check`); `chordApexCellsCheck` combines the apex cells of
  `[σ, 1]` for one radius cell and `chordRadiusCellsCheck` combines radius cells for one
  target. `chordTableCheck` checks a table of radius cells with one bound per cell (proved
  once), and `chordTableBoundCheck` reads off a range from it without re-checking the trees.
  The checks are meant to be discharged by `decide +kernel`.
-/

@[expose] public section

namespace Esgk

open Real

/-! ### The cosine window -/

/-- Two points of a circle of radius `r > 0` on the same side of the first axis, with first
coordinates in `[r u, r v]`: their inner product is at least `r² cos (arccos u - arccos v)`. -/
private lemma inner_ge_cos_arccos_sub {X Y X' Y' r u v : ℝ} (hr : 0 < r)
    (h1 : X ^ 2 + Y ^ 2 = r ^ 2) (h2 : X' ^ 2 + Y' ^ 2 = r ^ 2) (hside : 0 ≤ Y * Y')
    (hu : -1 ≤ u) (hv : v ≤ 1) (hXu : r * u ≤ X) (hXv : X ≤ r * v)
    (hX'u : r * u ≤ X') (hX'v : X' ≤ r * v) :
    r ^ 2 * cos (arccos u - arccos v) ≤ X * X' + Y * Y' := by
  set x := X / r with hxdef
  set x' := X' / r with hx'def
  have hX : X = r * x := by rw [hxdef]; field_simp
  have hX' : X' = r * x' := by rw [hx'def]; field_simp
  have hxu : u ≤ x := (le_div_iff₀ hr).mpr (by linarith)
  have hxv : x ≤ v := (div_le_iff₀ hr).mpr (by linarith)
  have hx'u : u ≤ x' := (le_div_iff₀ hr).mpr (by linarith)
  have hx'v : x' ≤ v := (div_le_iff₀ hr).mpr (by linarith)
  have hx1 : -1 ≤ x := hu.trans hxu
  have hx2 : x ≤ 1 := hxv.trans hv
  have hx'1 : -1 ≤ x' := hu.trans hx'u
  have hx'2 : x' ≤ 1 := hx'v.trans hv
  have habsY {Z z : ℝ} (hz1 : -1 ≤ z) (hz2 : z ≤ 1) (hZ : (r * z) ^ 2 + Z ^ 2 = r ^ 2) :
      |Z| = r * √(1 - z ^ 2) := by
    have hsq : Z ^ 2 = (r * √(1 - z ^ 2)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by nlinarith)]
      linear_combination hZ
    rw [← Real.sqrt_sq_eq_abs, hsq, Real.sqrt_sq (by positivity)]
  have hY := habsY hx1 hx2 (by rw [← hX]; exact h1)
  have hY' := habsY hx'1 hx'2 (by rw [← hX']; exact h2)
  have hYY : Y * Y' = r ^ 2 * (√(1 - x ^ 2) * √(1 - x' ^ 2)) := by
    rw [← abs_of_nonneg hside, abs_mul, hY, hY']; ring
  have hcos : cos (arccos x - arccos x') = x * x' + √(1 - x ^ 2) * √(1 - x' ^ 2) := by
    rw [cos_sub, cos_arccos hx1 hx2, cos_arccos hx'1 hx'2, sin_arccos, sin_arccos]
  have hmono : cos (arccos u - arccos v) ≤ cos (arccos x - arccos x') := by
    rw [← cos_abs (arccos x - arccos x')]
    apply cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
    · linarith [arccos_le_pi u, arccos_nonneg v]
    · have a1 := arccos_le_arccos hxu
      have a2 := arccos_le_arccos hxv
      have a3 := arccos_le_arccos hx'u
      have a4 := arccos_le_arccos hx'v
      rw [abs_le]
      constructor <;> linarith
  calc r ^ 2 * cos (arccos u - arccos v)
      ≤ r ^ 2 * cos (arccos x - arccos x') := mul_le_mul_of_nonneg_left hmono (sq_nonneg r)
    _ = X * X' + Y * Y' := by rw [hcos, hYY, hX, hX']; ring

/-- The cosine of the angle between the ends of a cosine window:
`cos (arccos u - arccos v) = u v + √(1 - u²) √(1 - v²)` for `u, v ∈ [-1, 1]`. -/
private lemma cos_arccos_sub_arccos {u v : ℝ} (hu1 : -1 ≤ u) (hu2 : u ≤ 1) (hv1 : -1 ≤ v)
    (hv2 : v ≤ 1) :
    cos (arccos u - arccos v) = u * v + √(1 - u ^ 2) * √(1 - v ^ 2) := by
  rw [cos_sub, cos_arccos hu1 hu2, cos_arccos hv1 hv2, sin_arccos, sin_arccos]

/-- **Cosine window** (Lemma C, inner-product form). Two points `(X, Y)`, `(X', Y')` of the
circle of radius `r > 0` about the origin on the same side of the first axis (`0 ≤ Y Y'`),
whose first coordinates lie in the window `[r u, r v]` with `-1 ≤ u` and `v ≤ 1`, have inner
product at least `r² (u v + √(1 - u²) √(1 - v²))`, the value at the two ends of the window. -/
theorem same_side_inner_ge_of_mem_cosine_window {X Y X' Y' r u v : ℝ} (hr : 0 < r)
    (h1 : X ^ 2 + Y ^ 2 = r ^ 2) (h2 : X' ^ 2 + Y' ^ 2 = r ^ 2) (hside : 0 ≤ Y * Y')
    (hu : -1 ≤ u) (hv : v ≤ 1) (hX : r * u ≤ X ∧ X ≤ r * v) (hX' : r * u ≤ X' ∧ X' ≤ r * v) :
    r ^ 2 * (u * v + √(1 - u ^ 2) * √(1 - v ^ 2)) ≤ X * X' + Y * Y' := by
  have huv : u ≤ v := le_of_mul_le_mul_left (hX.1.trans hX.2) hr
  rw [← cos_arccos_sub_arccos hu (huv.trans hv) (hu.trans huv) hv]
  exact inner_ge_cos_arccos_sub hr h1 h2 hside hu hv hX.1 hX.2 hX'.1 hX'.2

/-- **Cosine window** (Lemma C, chord form). Two points of the circle of radius `r > 0` about
the origin on the same side of the first axis, with first coordinates in `[r u, r v]`
(`-1 ≤ u`, `v ≤ 1`), are at squared distance at most
`2 r² (1 - (u v + √(1 - u²) √(1 - v²)))`. -/
theorem same_side_chord_sq_le_of_mem_cosine_window {X Y X' Y' r u v : ℝ} (hr : 0 < r)
    (h1 : X ^ 2 + Y ^ 2 = r ^ 2) (h2 : X' ^ 2 + Y' ^ 2 = r ^ 2) (hside : 0 ≤ Y * Y')
    (hu : -1 ≤ u) (hv : v ≤ 1) (hX : r * u ≤ X ∧ X ≤ r * v) (hX' : r * u ≤ X' ∧ X' ≤ r * v) :
    (X - X') ^ 2 + (Y - Y') ^ 2 ≤ 2 * r ^ 2 * (1 - (u * v + √(1 - u ^ 2) * √(1 - v ^ 2))) := by
  have := same_side_inner_ge_of_mem_cosine_window hr h1 h2 hside hu hv hX hX'
  nlinarith

/-! ### The arc window -/

/-- The clamp of a real number to `[-1, 1]`, `max (-1) (min 1 x)` (`cl` of Lemma C). -/
def unitClamp (x : ℝ) : ℝ := max (-1) (min 1 x)

private lemma neg_one_le_unitClamp (x : ℝ) : -1 ≤ unitClamp x := le_max_left _ _

private lemma unitClamp_le_one (x : ℝ) : unitClamp x ≤ 1 :=
  max_le (by norm_num) (min_le_left _ _)

private lemma unitClamp_mono {x y : ℝ} (h : x ≤ y) : unitClamp x ≤ unitClamp y :=
  max_le_max le_rfl (min_le_min le_rfl h)

private lemma unitClamp_of_mem {x : ℝ} (h1 : -1 ≤ x) (h2 : x ≤ 1) : unitClamp x = x := by
  rw [unitClamp, min_eq_right h2, max_eq_right h1]

private lemma unitClamp_of_le_neg_one {x : ℝ} (h : x ≤ -1) : unitClamp x = -1 := by
  rw [unitClamp, min_eq_right (by linarith), max_eq_left h]

private lemma unitClamp_of_one_le {x : ℝ} (h : 1 ≤ x) : unitClamp x = 1 := by
  rw [unitClamp, min_eq_left h, max_eq_right (by norm_num)]

/-- The arc `f(L, w) = arccos (cl L) - arccos (cl (L + w))` of Lemma C: the angle of the
directions on a half circle whose cosine lies in `[L, L + w]`. -/
private noncomputable def arcWindow (L w : ℝ) : ℝ :=
  arccos (unitClamp L) - arccos (unitClamp (L + w))

private lemma arcWindow_nonneg {L w : ℝ} (hw : 0 ≤ w) : 0 ≤ arcWindow L w :=
  sub_nonneg.mpr (arccos_le_arccos (unitClamp_mono (by linarith)))

private lemma arcWindow_le_pi (L w : ℝ) : arcWindow L w ≤ π := by
  unfold arcWindow
  linarith [arccos_le_pi (unitClamp L), arccos_nonneg (unitClamp (L + w))]

/-- The arc window is nondecreasing in the width. -/
private lemma arcWindow_mono_width {L w w' : ℝ} (h : w ≤ w') :
    arcWindow L w ≤ arcWindow L w' := by
  unfold arcWindow
  linarith [arccos_le_arccos (unitClamp_mono (by linarith : L + w ≤ L + w'))]

/-- The arc window is nondecreasing on `(-∞, -1]`. -/
private lemma arcWindow_mono_of_le_neg_one {L L' w : ℝ} (h : L ≤ L') (h' : L' ≤ -1) :
    arcWindow L w ≤ arcWindow L' w := by
  unfold arcWindow
  rw [unitClamp_of_le_neg_one (h.trans h'), unitClamp_of_le_neg_one h']
  linarith [arccos_le_arccos (unitClamp_mono (by linarith : L + w ≤ L' + w))]

/-- The arc window is nonincreasing on `[1 - w, ∞)`. -/
private lemma arcWindow_anti_of_one_sub_le {L L' w : ℝ} (h0 : 1 - w ≤ L) (h : L ≤ L') :
    arcWindow L' w ≤ arcWindow L w := by
  unfold arcWindow
  rw [unitClamp_of_one_le (by linarith : 1 ≤ L + w), unitClamp_of_one_le (by linarith : 1 ≤ L' + w)]
  linarith [arccos_le_arccos (unitClamp_mono h)]

/-- `m ↦ arccos (m - w/2) - arccos (m + w/2)` is monotone on `[0, 1 - w/2]`: its derivative
`1/√(1 - (m + w/2)²) - 1/√(1 - (m - w/2)²)` is nonnegative there. -/
private lemma arccos_sub_arccos_monotoneOn {w : ℝ} (hw : 0 ≤ w) :
    MonotoneOn (fun m ↦ arccos (m - w / 2) - arccos (m + w / 2)) (Set.Icc 0 (1 - w / 2)) := by
  have hderiv : ∀ m ∈ Set.Ioo 0 (1 - w / 2),
      HasDerivAt (fun m ↦ arccos (m - w / 2) - arccos (m + w / 2))
        (-(1 / √(1 - (m - w / 2) ^ 2)) - -(1 / √(1 - (m + w / 2) ^ 2))) m := by
    intro m hm
    obtain ⟨h0, h1⟩ := hm
    have e1 : HasDerivAt (fun m ↦ arccos (m - w / 2)) (-(1 / √(1 - (m - w / 2) ^ 2))) m :=
      (hasDerivAt_arccos (x := m - w / 2) (by linarith) (by linarith)).comp_sub_const m (w / 2)
    have e2 : HasDerivAt (fun m ↦ arccos (m + w / 2)) (-(1 / √(1 - (m + w / 2) ^ 2))) m :=
      (hasDerivAt_arccos (x := m + w / 2) (by linarith) (by linarith)).comp_add_const m (w / 2)
    exact e1.sub e2
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 (1 - w / 2))
  · exact ((continuous_arccos.comp (continuous_id.sub continuous_const)).sub
      (continuous_arccos.comp (continuous_id.add continuous_const))).continuousOn
  · rw [interior_Icc]
    intro m hm
    exact (hderiv m hm).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro m hm
    rw [(hderiv m hm).deriv]
    obtain ⟨h0, h1⟩ := hm
    have hpos : 0 < 1 - (m + w / 2) ^ 2 := by nlinarith
    have hle : 1 - (m + w / 2) ^ 2 ≤ 1 - (m - w / 2) ^ 2 := by nlinarith
    have := one_div_le_one_div_of_le (Real.sqrt_pos.mpr hpos) (Real.sqrt_le_sqrt hle)
    linarith

/-- On `[-1, 1 - w]` the clamps are inactive and the arc window is
`arccos (m - w/2) - arccos (m + w/2)` at the midpoint `m = L + w/2`. -/
private lemma arcWindow_eq_mid {L w : ℝ} (hw : 0 ≤ w) (h1 : -1 ≤ L) (h2 : L + w ≤ 1) :
    arcWindow L w = arccos ((L + w / 2) - w / 2) - arccos ((L + w / 2) + w / 2) := by
  unfold arcWindow
  rw [unitClamp_of_mem h1 (by linarith), unitClamp_of_mem (by linarith) h2]
  congr 2 <;> ring

/-- The midpoint form is even in the midpoint. -/
private lemma arccos_mid_neg (w m : ℝ) :
    arccos (-m - w / 2) - arccos (-m + w / 2) = arccos (m - w / 2) - arccos (m + w / 2) := by
  rw [show -m - w / 2 = -(m + w / 2) by ring, show -m + w / 2 = -(m - w / 2) by ring,
    arccos_neg, arccos_neg]
  ring

/-- The arc window is nondecreasing on `[-w/2, 1 - w]`. -/
private lemma arcWindow_mono_of_mid_le {L L' w : ℝ} (hw : 0 ≤ w) (h0 : -(w / 2) ≤ L)
    (h : L ≤ L') (h1 : L' ≤ 1 - w) : arcWindow L w ≤ arcWindow L' w := by
  rw [arcWindow_eq_mid hw (by linarith) (by linarith),
    arcWindow_eq_mid hw (by linarith) (by linarith)]
  exact arccos_sub_arccos_monotoneOn hw ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
    (by linarith)

/-- The arc window is nonincreasing on `[-1, -w/2]`. -/
private lemma arcWindow_anti_of_le_mid {L L' w : ℝ} (hw : 0 ≤ w) (h0 : -1 ≤ L)
    (h : L ≤ L') (h1 : L' ≤ -(w / 2)) : arcWindow L' w ≤ arcWindow L w := by
  rw [arcWindow_eq_mid hw (by linarith) (by linarith),
    arcWindow_eq_mid hw (by linarith) (by linarith),
    ← arccos_mid_neg w (L + w / 2), ← arccos_mid_neg w (L' + w / 2)]
  exact arccos_sub_arccos_monotoneOn hw ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
    (by linarith)

/-- **Maximum of the arc window on an interval.** For `w ≥ 0` and `L ∈ [Llo, Lhi]`, the arc
window at `L` is at most its value at one of the candidates `Llo`, `Lhi`, `-1` (when
`-1 ∈ [Llo, Lhi]`) and `1 - w` (when `1 - w ∈ [Llo, Lhi]`). -/
private lemma arcWindow_le_candidate {Llo Lhi L w : ℝ} (hw : 0 ≤ w) (hL0 : Llo ≤ L)
    (hL1 : L ≤ Lhi) :
    arcWindow L w ≤ arcWindow Llo w ∨ arcWindow L w ≤ arcWindow Lhi w ∨
      (Llo ≤ -1 ∧ -1 ≤ Lhi ∧ arcWindow L w ≤ arcWindow (-1) w) ∨
      (Llo ≤ 1 - w ∧ 1 - w ≤ Lhi ∧ arcWindow L w ≤ arcWindow (1 - w) w) := by
  rcases le_or_gt L (-1) with hm | hm
  · rcases le_or_gt (-1) Lhi with hh | hh
    · exact Or.inr (Or.inr (Or.inl ⟨by linarith, hh, arcWindow_mono_of_le_neg_one hm le_rfl⟩))
    · exact Or.inr (Or.inl (arcWindow_mono_of_le_neg_one hL1 hh.le))
  rcases le_or_gt (1 - w) L with hp | hp
  · rcases le_or_gt Llo (1 - w) with hl | hl
    · exact Or.inr (Or.inr (Or.inr ⟨hl, by linarith, arcWindow_anti_of_one_sub_le le_rfl hp⟩))
    · exact Or.inl (arcWindow_anti_of_one_sub_le hl.le hL0)
  rcases le_total L (-(w / 2)) with hc | hc
  · rcases le_or_gt Llo (-1) with hl | hl
    · exact Or.inr (Or.inr (Or.inl ⟨hl, by linarith,
        arcWindow_anti_of_le_mid hw le_rfl hm.le hc⟩))
    · exact Or.inl (arcWindow_anti_of_le_mid hw hl.le hL0 hc)
  · rcases le_or_gt (1 - w) Lhi with hh | hh
    · exact Or.inr (Or.inr (Or.inr ⟨by linarith, hh,
        arcWindow_mono_of_mid_le hw hc hp.le le_rfl⟩))
    · exact Or.inr (Or.inl (arcWindow_mono_of_mid_le hw hc hL1 hh.le))

/-- The square-root-free form of `β ≤ u v + √((1 - u²)(1 - v²))` at the clamped window
`u = cl L`, `v = cl (L + w)` of Lemma C′: either `β ≤ u v`, or `(β - u v)² ≤ (1 - u²)(1 - v²)`.
It says that `β` is at most the cosine of the arc `arccos (cl L) - arccos (cl (L + w))`. -/
def WindowCosineBound (β L w : ℝ) : Prop :=
  β - unitClamp L * unitClamp (L + w) ≤ 0 ∨
    (β - unitClamp L * unitClamp (L + w)) ^ 2 ≤
      (1 - unitClamp L ^ 2) * (1 - unitClamp (L + w) ^ 2)

/-- The candidate condition bounds the cosine of the arc window from below. -/
private lemma le_cos_arcWindow_of_bound {β L w : ℝ} (h : WindowCosineBound β L w) :
    β ≤ cos (arcWindow L w) := by
  unfold arcWindow
  set u := unitClamp L
  set v := unitClamp (L + w)
  have hu1 := neg_one_le_unitClamp L
  have hu2 := unitClamp_le_one L
  have hv1 := neg_one_le_unitClamp (L + w)
  have hv2 := unitClamp_le_one (L + w)
  rw [cos_arccos_sub_arccos hu1 hu2 hv1 hv2]
  have hsq0 : 0 ≤ √(1 - u ^ 2) * √(1 - v ^ 2) := by positivity
  rcases h with h | h
  · linarith
  · have hsq : β - u * v ≤ √(1 - u ^ 2) * √(1 - v ^ 2) := by
      rw [← Real.sqrt_mul (by nlinarith)]
      calc β - u * v ≤ |β - u * v| := le_abs_self _
        _ = √((β - u * v) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
        _ ≤ √((1 - u ^ 2) * (1 - v ^ 2)) := Real.sqrt_le_sqrt h
    linarith

/-- Lemma C′, analytic part: for `0 ≤ w ≤ wmax` and `L ∈ [Llo, Lhi]`, a common lower bound `β`
of the candidate cosines at width `wmax` bounds `cos (arcWindow L w)` from below. -/
private lemma le_cos_arcWindow {β Llo Lhi L w wmax : ℝ} (hw0 : 0 ≤ w) (hw : w ≤ wmax)
    (hL0 : Llo ≤ L) (hL1 : L ≤ Lhi)
    (hβlo : WindowCosineBound β Llo wmax) (hβhi : WindowCosineBound β Lhi wmax)
    (hβm : Llo ≤ -1 → -1 ≤ Lhi → WindowCosineBound β (-1) wmax)
    (hβw : Llo ≤ 1 - wmax → 1 - wmax ≤ Lhi → WindowCosineBound β (1 - wmax) wmax) :
    β ≤ cos (arcWindow L w) := by
  have key : ∀ L', WindowCosineBound β L' wmax → arcWindow L w ≤ arcWindow L' wmax →
      β ≤ cos (arcWindow L w) := fun L' hb hle ↦
    (le_cos_arcWindow_of_bound hb).trans
      (cos_le_cos_of_nonneg_of_le_pi (arcWindow_nonneg hw0) (arcWindow_le_pi _ _) hle)
  have hm : arcWindow L w ≤ arcWindow L wmax := arcWindow_mono_width hw
  rcases arcWindow_le_candidate (hw0.trans hw) hL0 hL1 with h | h | ⟨h1, h2, h⟩ | ⟨h1, h2, h⟩
  · exact key _ hβlo (hm.trans h)
  · exact key _ hβhi (hm.trans h)
  · exact key _ (hβm h1 h2) (hm.trans h)
  · exact key _ (hβw h1 h2) (hm.trans h)

/-! ### The box lemma -/

/-- The annulus window of a point of the circle of radius `R` about an apex at distance `A`
from the origin: if `x² + y² = R²` and `σ² ≤ R² + 2Ax + A² ≤ 1`, then `x / R` lies in the
clamped window `[cl L, cl (L + w)]`, `L = (σ² - A² - R²)/(2AR)`, `w = (1 - σ²)/(2AR)`. -/
private lemma mem_clamped_window {A R x y σ : ℝ} (hA : 0 < A) (hR : 0 < R)
    (h : x ^ 2 + y ^ 2 = R ^ 2) (hlo : σ ^ 2 ≤ R ^ 2 + 2 * A * x + A ^ 2)
    (hhi : R ^ 2 + 2 * A * x + A ^ 2 ≤ 1) :
    R * unitClamp ((σ ^ 2 - A ^ 2 - R ^ 2) / (2 * A * R)) ≤ x ∧
      x ≤ R * unitClamp ((σ ^ 2 - A ^ 2 - R ^ 2) / (2 * A * R) + (1 - σ ^ 2) / (2 * A * R)) := by
  have hD : 0 < 2 * A * R := by positivity
  set t := x / R with htdef
  have hx : x = R * t := by rw [htdef]; field_simp
  have ht1 : -1 ≤ t := by
    rw [htdef, le_div_iff₀ hR]; nlinarith [sq_nonneg y, sq_nonneg (x + R)]
  have ht2 : t ≤ 1 := by
    rw [htdef, div_le_iff₀ hR]; nlinarith [sq_nonneg y, sq_nonneg (x - R)]
  have hLt : (σ ^ 2 - A ^ 2 - R ^ 2) / (2 * A * R) ≤ t := by
    rw [div_le_iff₀ hD]; rw [hx] at hlo; nlinarith
  have htw : t ≤ (σ ^ 2 - A ^ 2 - R ^ 2) / (2 * A * R) + (1 - σ ^ 2) / (2 * A * R) := by
    rw [← add_div, le_div_iff₀ hD]; rw [hx] at hhi; nlinarith
  constructor
  · rw [hx]
    exact mul_le_mul_of_nonneg_left (max_le ht1 ((min_le_right _ _).trans hLt)) hR.le
  · rw [hx]
    exact mul_le_mul_of_nonneg_left (le_max_of_le_right (le_min ht2 htw)) hR.le

/-- The box bounds of the window: for `A ∈ [a0, a1]`, `R ∈ [r0, r1]` with `a0, r0 > 0` and
`σ² ≤ a0² + r0²`, the left end `L = (σ² - A² - R²)/(2AR)` lies in `[Llo, Lhi]` and the width
`(1 - σ²)/(2AR)` lies in `[0, w]`, under the stated linear bounds on `Llo`, `Lhi`, `w`. -/
private lemma window_mem_box {σ A R a0 a1 r0 r1 Llo Lhi w : ℝ} (ha0 : 0 < a0) (hr0 : 0 < r0)
    (hA0 : a0 ≤ A) (hA1 : A ≤ a1) (hR0 : r0 ≤ R) (hR1 : R ≤ r1)
    (hσa : σ ^ 2 ≤ a0 ^ 2 + r0 ^ 2) (hσ1 : σ ^ 2 ≤ 1)
    (hLlo : Llo * (2 * a0 * r0) ≤ σ ^ 2 - a1 ^ 2 - r1 ^ 2)
    (hLhi : σ ^ 2 - a0 ^ 2 - r0 ^ 2 ≤ Lhi * (2 * a1 * r1))
    (hw : 1 - σ ^ 2 ≤ w * (2 * a0 * r0)) :
    Llo ≤ (σ ^ 2 - A ^ 2 - R ^ 2) / (2 * A * R) ∧ (σ ^ 2 - A ^ 2 - R ^ 2) / (2 * A * R) ≤ Lhi ∧
      0 ≤ (1 - σ ^ 2) / (2 * A * R) ∧ (1 - σ ^ 2) / (2 * A * R) ≤ w := by
  have hA : 0 < A := ha0.trans_le hA0
  have hR : 0 < R := hr0.trans_le hR0
  have hD0 : 0 < 2 * a0 * r0 := by positivity
  have hD : 0 < 2 * A * R := by positivity
  have hD0D : 2 * a0 * r0 ≤ 2 * A * R := by
    have := mul_le_mul hA0 hR0 hr0.le hA.le
    linarith
  have hDD1 : 2 * A * R ≤ 2 * a1 * r1 := by
    have := mul_le_mul hA1 hR1 hR.le (hA.le.trans hA1)
    linarith
  have hA2 : a0 ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ ha0.le hA0 2
  have hA2' : A ^ 2 ≤ a1 ^ 2 := pow_le_pow_left₀ hA.le hA1 2
  have hR2 : r0 ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hr0.le hR0 2
  have hR2' : R ^ 2 ≤ r1 ^ 2 := pow_le_pow_left₀ hR.le hR1 2
  have hN : σ ^ 2 - A ^ 2 - R ^ 2 ≤ 0 := by linarith
  refine ⟨?_, ?_, div_nonneg (by linarith) hD.le, ?_⟩
  · rw [le_div_iff₀ hD]
    rcases le_or_gt Llo 0 with hl | hl
    · have := mul_le_mul_of_nonpos_left hD0D hl
      linarith
    · have := mul_pos hl hD0
      linarith
  · rw [div_le_iff₀ hD]
    rcases le_or_gt 0 Lhi with hl | hl
    · have := mul_nonneg hl hD.le
      linarith
    · have := mul_le_mul_of_nonpos_left hDD1 hl.le
      linarith
  · calc (1 - σ ^ 2) / (2 * A * R) ≤ (1 - σ ^ 2) / (2 * a0 * r0) :=
          div_le_div_of_nonneg_left (by linarith) hD0 hD0D
      _ ≤ w := (div_le_iff₀ hD0).mpr hw

/-- The orthonormal frame with the apex `p` at `(‖p‖, 0)`: coordinates `u, v` of
three points, with their squared norms, mutual squared distances, and squared
distances to the apex. (A copy of the private `exists_apex_frame` of
`Esgk.RefinedClosePairGeometry`.) -/
private lemma apex_frame_exists (p : Point) (q : Fin 3 → Point) (ha0 : ‖p‖ ≠ 0) :
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

/-- Lemma C′ in the unit annulus `σ² ≤ ‖·‖² ≤ 1` about the origin, arbitrary planar frame. -/
private lemma unit_exists_dist_sq_le_of_mem_chord_box (p : Point) (q : Fin 3 → Point)
    {σ a0 a1 r0 r1 Llo Lhi w β : ℝ} (ha0 : 0 < a0) (hr0 : 0 < r0)
    (hσa : σ ^ 2 ≤ a0 ^ 2 + r0 ^ 2)
    (hLlo : Llo * (2 * a0 * r0) ≤ σ ^ 2 - a1 ^ 2 - r1 ^ 2)
    (hLhi : σ ^ 2 - a0 ^ 2 - r0 ^ 2 ≤ Lhi * (2 * a1 * r1))
    (hw : 1 - σ ^ 2 ≤ w * (2 * a0 * r0))
    (hβlo : WindowCosineBound β Llo w) (hβhi : WindowCosineBound β Lhi w)
    (hβm : Llo ≤ -1 → -1 ≤ Lhi → WindowCosineBound β (-1) w)
    (hβw : Llo ≤ 1 - w → 1 - w ≤ Lhi → WindowCosineBound β (1 - w) w)
    (hlo : ∀ i, σ ^ 2 ≤ ‖q i‖ ^ 2) (hhi : ∀ i, ‖q i‖ ^ 2 ≤ 1)
    (heq : ∀ i j, dist p (q i) = dist p (q j))
    (hpa0 : a0 ≤ ‖p‖) (hpa1 : ‖p‖ ≤ a1) (hpr0 : r0 ≤ dist p (q 0))
    (hpr1 : dist p (q 0) ≤ r1) :
    ∃ i j : Fin 3, i ≠ j ∧ dist (q i) (q j) ^ 2 ≤ 2 * r1 ^ 2 * (1 - β) := by
  have hA : 0 < ‖p‖ := ha0.trans_le hpa0
  have hR : 0 < dist p (q 0) := hr0.trans_le hpr0
  have hσ1 : σ ^ 2 ≤ 1 := (hlo 0).trans (hhi 0)
  obtain ⟨u, v, hnorm, hdist, hapex⟩ := apex_frame_exists p q hA.ne'
  set A := ‖p‖
  set R := dist p (q 0)
  have hRk (k : Fin 3) : (u k - A) ^ 2 + v k ^ 2 = R ^ 2 := by rw [hapex k, heq k 0]
  have hNk (k : Fin 3) : ‖q k‖ ^ 2 = R ^ 2 + 2 * A * (u k - A) + A ^ 2 := by
    rw [← hnorm k]; linear_combination hRk k
  obtain ⟨hLL, hLH, hw0, hww⟩ := window_mem_box ha0 hr0 hpa0 hpa1 hpr0 hpr1 hσa hσ1 hLlo hLhi hw
  set L := (σ ^ 2 - A ^ 2 - R ^ 2) / (2 * A * R)
  set wA := (1 - σ ^ 2) / (2 * A * R)
  have hβc : β ≤ cos (arcWindow L wA) := le_cos_arcWindow hw0 hww hLL hLH hβlo hβhi hβm hβw
  have hmem (k : Fin 3) : R * unitClamp L ≤ u k - A ∧ u k - A ≤ R * unitClamp (L + wA) :=
    mem_clamped_window hA hR (hRk k) (by rw [← hNk k]; exact hlo k)
      (by rw [← hNk k]; exact hhi k)
  obtain ⟨i, j, hij, hside⟩ := three_has_same_transverse_side v
  refine ⟨i, j, hij, ?_⟩
  have hinner := inner_ge_cos_arccos_sub hR (hRk i) (hRk j) hside (neg_one_le_unitClamp L)
    (unitClamp_le_one (L + wA)) (hmem i).1 (hmem i).2 (hmem j).1 (hmem j).2
  have hchord : dist (q i) (q j) ^ 2 ≤ 2 * R ^ 2 * (1 - cos (arcWindow L wA)) := by
    rw [← hdist i j]
    have h1 := hRk i
    have h2 := hRk j
    unfold arcWindow
    nlinarith
  have hβ1 : 0 ≤ 1 - β := by linarith [cos_le_one (arcWindow L wA)]
  have hR2 : R ^ 2 ≤ r1 ^ 2 := pow_le_pow_left₀ hR.le hpr1 2
  calc dist (q i) (q j) ^ 2 ≤ 2 * R ^ 2 * (1 - cos (arcWindow L wA)) := hchord
    _ ≤ 2 * R ^ 2 * (1 - β) := by
        have := mul_le_mul_of_nonneg_left (by linarith : 1 - cos (arcWindow L wA) ≤ 1 - β)
          (by positivity : (0 : ℝ) ≤ 2 * R ^ 2)
        linarith
    _ ≤ 2 * r1 ^ 2 * (1 - β) := by nlinarith

/-- The translation by `c` and scaling by `ρ⁻¹`: norms and distances. -/
private lemma scaled_norm_dist (c : Point) {ρ : ℝ} (hρ : 0 < ρ) :
    (∀ z : Point, ‖ρ⁻¹ • (z - c)‖ = dist z c / ρ) ∧
      ∀ z z' : Point, dist (ρ⁻¹ • (z - c)) (ρ⁻¹ • (z' - c)) = dist z z' / ρ := by
  constructor
  · intro z
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hρ, ← dist_eq_norm, div_eq_inv_mul]
  · intro z z'
    rw [dist_smul₀, Real.norm_eq_abs, abs_inv, abs_of_pos hρ, dist_sub_right, div_eq_inv_mul]

/-- **Lemma C′ (box lemma).** Let three points `q i` lie in the annulus
`σ²ρ² ≤ |q i - c|² ≤ ρ²`, all at the same distance `r` from an apex `p`, with
`a0 ρ ≤ |p - c| ≤ a1 ρ` and `r0 ρ ≤ r ≤ r1 ρ`, `0 < a0`, `0 < r0` and `σ² ≤ a0² + r0²`
(for instance `σ ≤ a0`). Let `Llo`, `Lhi`, `w` bound the window of the box,
`Llo ≤ (σ² - a1² - r1²)/(2 a0 r0)`, `(σ² - a0² - r0²)/(2 a1 r1) ≤ Lhi`,
`(1 - σ²)/(2 a0 r0) ≤ w` (stated multiplied out), and let `β` satisfy the square-root-free
candidate condition `WindowCosineBound β L w` at `L = Llo`, `L = Lhi`, `L = -1` when
`-1 ∈ [Llo, Lhi]` and `L = 1 - w` when `1 - w ∈ [Llo, Lhi]`. Then two of the three points are
at squared distance at most `2 r1² (1 - β) ρ²`. This is `chord_sq_box` of
`scripts/verify_constant_gain_5_239.py` with `β` its `worst_cos`, in units of `ρ`. -/
theorem exists_dist_sq_le_of_mem_chord_box (c p : Point) (q : Fin 3 → Point)
    {ρ σ a0 a1 r0 r1 Llo Lhi w β : ℝ} (hρ : 0 < ρ) (ha0 : 0 < a0) (hr0 : 0 < r0)
    (hσa : σ ^ 2 ≤ a0 ^ 2 + r0 ^ 2)
    (hLlo : Llo * (2 * a0 * r0) ≤ σ ^ 2 - a1 ^ 2 - r1 ^ 2)
    (hLhi : σ ^ 2 - a0 ^ 2 - r0 ^ 2 ≤ Lhi * (2 * a1 * r1))
    (hw : 1 - σ ^ 2 ≤ w * (2 * a0 * r0))
    (hβlo : WindowCosineBound β Llo w) (hβhi : WindowCosineBound β Lhi w)
    (hβm : Llo ≤ -1 → -1 ≤ Lhi → WindowCosineBound β (-1) w)
    (hβw : Llo ≤ 1 - w → 1 - w ≤ Lhi → WindowCosineBound β (1 - w) w)
    (hlo : ∀ i, σ ^ 2 * ρ ^ 2 ≤ dist (q i) c ^ 2) (hhi : ∀ i, dist (q i) c ^ 2 ≤ ρ ^ 2)
    (heq : ∀ i j, dist p (q i) = dist p (q j))
    (hpa0 : a0 * ρ ≤ dist p c) (hpa1 : dist p c ≤ a1 * ρ)
    (hpr0 : r0 * ρ ≤ dist p (q 0)) (hpr1 : dist p (q 0) ≤ r1 * ρ) :
    ∃ i j : Fin 3, i ≠ j ∧ dist (q i) (q j) ^ 2 ≤ 2 * r1 ^ 2 * (1 - β) * ρ ^ 2 := by
  obtain ⟨hn, hd⟩ := scaled_norm_dist c hρ
  have hsq : 0 < ρ ^ 2 := by positivity
  have hn2 (z : Point) : ‖ρ⁻¹ • (z - c)‖ ^ 2 = dist z c ^ 2 / ρ ^ 2 := by rw [hn, div_pow]
  obtain ⟨i, j, hij, hclose⟩ := unit_exists_dist_sq_le_of_mem_chord_box
    (ρ⁻¹ • (p - c)) (fun i ↦ ρ⁻¹ • (q i - c)) ha0 hr0 hσa hLlo hLhi hw hβlo hβhi hβm hβw
    (fun i ↦ by rw [hn2]; exact (le_div_iff₀ hsq).mpr (hlo i))
    (fun i ↦ by rw [hn2]; exact (div_le_iff₀ hsq).mpr (by simpa using hhi i))
    (fun i j ↦ by rw [hd, hd, heq i j])
    (by rw [hn]; exact (le_div_iff₀ hρ).mpr hpa0)
    (by rw [hn]; exact (div_le_iff₀ hρ).mpr hpa1)
    (by rw [hd]; exact (le_div_iff₀ hρ).mpr hpr0)
    (by rw [hd]; exact (div_le_iff₀ hρ).mpr hpr1)
  rw [hd, div_pow] at hclose
  exact ⟨i, j, hij, (div_le_iff₀ hsq).mp hclose⟩

/-- **The trivial cell of Lemma C′.** Three points at the same distance `r ≤ r1 ρ` from an
apex contain a pair at squared distance at most `4 r1² ρ²` (the chord is at most `2r`). This is
the `r0 = 0` cell `4 r1²` of `scripts/verify_constant_gain_5_239.py`. -/
theorem exists_dist_sq_le_four_mul_sq (p : Point) (q : Fin 3 → Point) {ρ r1 : ℝ}
    (heq : ∀ i j, dist p (q i) = dist p (q j)) (hpr1 : dist p (q 0) ≤ r1 * ρ) :
    ∃ i j : Fin 3, i ≠ j ∧ dist (q i) (q j) ^ 2 ≤ 4 * r1 ^ 2 * ρ ^ 2 := by
  refine ⟨0, 1, by decide, ?_⟩
  have htri : dist (q 0) (q 1) ≤ 2 * dist p (q 0) := by
    calc dist (q 0) (q 1) ≤ dist (q 0) p + dist p (q 1) := dist_triangle _ _ _
      _ = 2 * dist p (q 0) := by rw [dist_comm, heq 1 0]; ring
  have h0 : 0 ≤ dist (q 0) (q 1) := dist_nonneg
  have h1 : 0 ≤ dist p (q 0) := dist_nonneg
  nlinarith

/-! ### The box tree over the rationals -/

/-- The clamp to `[-1, 1]` on rationals; its cast to `ℝ` is `unitClamp`. -/
def unitClampRat (x : ℚ) : ℚ := max (-1) (min 1 x)

/-- The rational check of `WindowCosineBound β L w`, with products in place of squares. -/
def windowCosineCheck (β L w : ℚ) : Bool :=
  decide (β - unitClampRat L * unitClampRat (L + w) ≤ 0) ||
    decide ((β - unitClampRat L * unitClampRat (L + w)) *
        (β - unitClampRat L * unitClampRat (L + w)) ≤
      (1 - unitClampRat L * unitClampRat L) * (1 - unitClampRat (L + w) * unitClampRat (L + w)))

/-- The rational check of one box `[a0, a1] × [r0, r1]` of Lemma C′ with cosine bound `β`
against the squared target `T`: `0 < a0`, `0 < r0`, `σ² ≤ a0² + r0²`, the candidate conditions
at the exact window ends `Llo = (σ² - a1² - r1²)/(2 a0 r0)`, `Lhi = (σ² - a0² - r0²)/(2 a1 r1)`
and width `w = (1 - σ²)/(2 a0 r0)`, and `2 r1² (1 - β) ≤ T`. This is `chord_sq_box ≤ target`
of `scripts/verify_constant_gain_5_239.py`. -/
def chordBoxCheck (σ T a0 a1 r0 r1 β : ℚ) : Bool :=
  let Llo := (σ * σ - a1 * a1 - r1 * r1) / (2 * a0 * r0)
  let Lhi := (σ * σ - a0 * a0 - r0 * r0) / (2 * a1 * r1)
  let w := (1 - σ * σ) / (2 * a0 * r0)
  decide (0 < a0) && decide (0 < r0) && decide (σ * σ ≤ a0 * a0 + r0 * r0) &&
    windowCosineCheck β Llo w && windowCosineCheck β Lhi w &&
    (!(decide (Llo ≤ -1) && decide (-1 ≤ Lhi)) || windowCosineCheck β (-1) w) &&
    (!(decide (Llo ≤ 1 - w) && decide (1 - w ≤ Lhi)) || windowCosineCheck β (1 - w) w) &&
    decide (2 * (r1 * r1) * (1 - β) ≤ T)

/-- A refinement tree of a rational (apex distance, radius) box `[a0, a1] × [r0, r1]`, as the
adaptive refinement `Chords._adapt` of `scripts/verify_constant_gain_5_239.py`: leaves carry
the bound of Lemma C′ or the trivial bound, inner nodes halve the box at midpoints. -/
inductive ChordBoxTree : Type where
  /-- A leaf certified by Lemma C′ with the rational cosine bound `β` (`chordBoxCheck`). -/
  | cert (β : ℚ) : ChordBoxTree
  /-- A leaf certified by the trivial bound `4 r1²` (any box, in particular `r0 = 0`). -/
  | disk : ChordBoxTree
  /-- Quartering at the midpoints `am`, `rm`: the children are the boxes `[a0, am] × [r0, rm]`,
  `[a0, am] × [rm, r1]`, `[am, a1] × [r0, rm]` and `[am, a1] × [rm, r1]`. -/
  | split (t₁ t₂ t₃ t₄ : ChordBoxTree) : ChordBoxTree
  /-- Halving the apex interval: `[a0, am] × [r0, r1]` and `[am, a1] × [r0, r1]`. -/
  | splitApex (t₁ t₂ : ChordBoxTree) : ChordBoxTree
  /-- Halving the radius interval: `[a0, a1] × [r0, rm]` and `[a0, a1] × [rm, r1]`. -/
  | splitRadius (t₁ t₂ : ChordBoxTree) : ChordBoxTree

namespace ChordBoxTree

/-- The structurally recursive check of a box tree on the box `[a0, a1] × [r0, r1]` for the
annulus parameter `σ` and the squared target `T`: every `cert` leaf passes `chordBoxCheck`
and every `disk` leaf has `4 r1² ≤ T`. Rational arithmetic only, for `decide +kernel`. -/
def check (σ T : ℚ) : ChordBoxTree → ℚ → ℚ → ℚ → ℚ → Bool
  | cert β, a0, a1, r0, r1 => chordBoxCheck σ T a0 a1 r0 r1 β
  | disk, _, _, _, r1 => decide (4 * (r1 * r1) ≤ T)
  | split t₁ t₂ t₃ t₄, a0, a1, r0, r1 =>
      t₁.check σ T a0 ((a0 + a1) / 2) r0 ((r0 + r1) / 2) &&
      t₂.check σ T a0 ((a0 + a1) / 2) ((r0 + r1) / 2) r1 &&
      t₃.check σ T ((a0 + a1) / 2) a1 r0 ((r0 + r1) / 2) &&
      t₄.check σ T ((a0 + a1) / 2) a1 ((r0 + r1) / 2) r1
  | splitApex t₁ t₂, a0, a1, r0, r1 =>
      t₁.check σ T a0 ((a0 + a1) / 2) r0 r1 && t₂.check σ T ((a0 + a1) / 2) a1 r0 r1
  | splitRadius t₁ t₂, a0, a1, r0, r1 =>
      t₁.check σ T a0 a1 r0 ((r0 + r1) / 2) && t₂.check σ T a0 a1 ((r0 + r1) / 2) r1

end ChordBoxTree

private lemma unitClampRat_cast (x : ℚ) : ((unitClampRat x : ℚ) : ℝ) = unitClamp (x : ℝ) := by
  simp [unitClampRat, unitClamp, Rat.cast_max, Rat.cast_min]

private lemma windowCosineBound_of_check {β L w : ℚ} (h : windowCosineCheck β L w = true) :
    WindowCosineBound (β : ℝ) (L : ℝ) (w : ℝ) := by
  unfold windowCosineCheck at h
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  have hv : ((unitClampRat (L + w) : ℚ) : ℝ) = unitClamp ((L : ℝ) + w) := by
    rw [unitClampRat_cast]; push_cast; rfl
  unfold WindowCosineBound
  rw [← unitClampRat_cast, ← hv]
  rcases h with h | h
  · left; exact_mod_cast h
  · right
    have := (Rat.cast_le (K := ℝ)).mpr h
    push_cast at this
    nlinarith [this]

/-- One certified leaf: `chordBoxCheck` gives the box lemma with `T`. -/
private lemma exists_dist_sq_le_of_chordBoxCheck (c p : Point) (q : Fin 3 → Point) {ρ : ℝ}
    {σ T a0 a1 r0 r1 β : ℚ} (h : chordBoxCheck σ T a0 a1 r0 r1 β = true) (hρ : 0 < ρ)
    (hlo : ∀ i, (σ : ℝ) ^ 2 * ρ ^ 2 ≤ dist (q i) c ^ 2) (hhi : ∀ i, dist (q i) c ^ 2 ≤ ρ ^ 2)
    (heq : ∀ i j, dist p (q i) = dist p (q j))
    (hpa0 : (a0 : ℝ) * ρ ≤ dist p c) (hpa1 : dist p c ≤ (a1 : ℝ) * ρ)
    (hpr0 : (r0 : ℝ) * ρ ≤ dist p (q 0)) (hpr1 : dist p (q 0) ≤ (r1 : ℝ) * ρ) :
    ∃ i j : Fin 3, i ≠ j ∧ dist (q i) (q j) ^ 2 ≤ (T : ℝ) * ρ ^ 2 := by
  simp only [chordBoxCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨ha0, hr0⟩, hσa⟩, hc1⟩, hc2⟩, hc3⟩, hc4⟩, hT⟩ := h
  set Llo := (σ * σ - a1 * a1 - r1 * r1) / (2 * a0 * r0)
  set Lhi := (σ * σ - a0 * a0 - r0 * r0) / (2 * a1 * r1)
  set w := (1 - σ * σ) / (2 * a0 * r0)
  have ha0' : 0 < a0 := of_decide_eq_true ha0
  have hr0' : 0 < r0 := of_decide_eq_true hr0
  have hσa' : σ * σ ≤ a0 * a0 + r0 * r0 := of_decide_eq_true hσa
  have hT' : 2 * (r1 * r1) * (1 - β) ≤ T := of_decide_eq_true hT
  have hD0 : 2 * a0 * r0 ≠ 0 := by positivity
  have hLlo : Llo * (2 * a0 * r0) ≤ σ ^ 2 - a1 ^ 2 - r1 ^ 2 := by
    rw [div_mul_cancel₀ _ hD0]; nlinarith
  have hLhi : σ ^ 2 - a0 ^ 2 - r0 ^ 2 ≤ Lhi * (2 * a1 * r1) := by
    by_cases hD1 : 2 * a1 * r1 = 0
    · rw [hD1, mul_zero]; nlinarith
    · rw [div_mul_cancel₀ _ hD1]; nlinarith
  have hw : 1 - σ ^ 2 ≤ w * (2 * a0 * r0) := by
    rw [div_mul_cancel₀ _ hD0]; nlinarith
  have hc3' : (Llo : ℝ) ≤ -1 → -1 ≤ (Lhi : ℝ) → WindowCosineBound β (-1) w := by
    intro h1 h2
    have h1' : Llo ≤ -1 := by exact_mod_cast h1
    have h2' : -1 ≤ Lhi := by exact_mod_cast h2
    have := windowCosineBound_of_check (by simpa [h1', h2'] using hc3)
    simpa using this
  have hc4' : (Llo : ℝ) ≤ 1 - w → 1 - w ≤ (Lhi : ℝ) → WindowCosineBound β (1 - w) w := by
    intro h1 h2
    have h1' : Llo ≤ 1 - w := by exact_mod_cast h1
    have h2' : 1 - w ≤ Lhi := by exact_mod_cast h2
    have := windowCosineBound_of_check (by simpa [h1', h2'] using hc4)
    simpa using this
  obtain ⟨i, j, hij, hclose⟩ := exists_dist_sq_le_of_mem_chord_box c p q (σ := σ) (β := β)
    (Llo := Llo) (Lhi := Lhi) (w := w) hρ (by exact_mod_cast ha0') (by exact_mod_cast hr0')
    (by exact_mod_cast (show σ ^ 2 ≤ a0 ^ 2 + r0 ^ 2 by nlinarith))
    (by exact_mod_cast hLlo) (by exact_mod_cast hLhi) (by exact_mod_cast hw)
    (windowCosineBound_of_check hc1) (windowCosineBound_of_check hc2) hc3' hc4'
    hlo hhi heq hpa0 hpa1 hpr0 hpr1
  refine ⟨i, j, hij, hclose.trans ?_⟩
  have hT'' : 2 * (r1 : ℝ) ^ 2 * (1 - β) ≤ T := by
    have := (Rat.cast_le (K := ℝ)).mpr hT'
    push_cast at this
    nlinarith [this]
  exact mul_le_mul_of_nonneg_right hT'' (sq_nonneg ρ)

/-- **Soundness of the box tree.** If `t.check σ T a0 a1 r0 r1 = true`, then for every
configuration of three points `q i` of the annulus `σ²ρ² ≤ |q i - c|² ≤ ρ²` at a common
distance `r` from an apex `p` with `a0 ρ ≤ |p - c| ≤ a1 ρ` and `r0 ρ ≤ r ≤ r1 ρ`, two of the
points are at squared distance at most `T ρ²`. This is `Chords._adapt` of
`scripts/verify_constant_gain_5_239.py` returning `True` on the box, in units of `ρ`. -/
theorem ChordBoxTree.exists_dist_sq_le_of_check (c p : Point) (q : Fin 3 → Point) {ρ : ℝ}
    {σ T : ℚ} (hρ : 0 < ρ) (hlo : ∀ i, (σ : ℝ) ^ 2 * ρ ^ 2 ≤ dist (q i) c ^ 2)
    (hhi : ∀ i, dist (q i) c ^ 2 ≤ ρ ^ 2) (heq : ∀ i j, dist p (q i) = dist p (q j)) :
    ∀ (t : ChordBoxTree) {a0 a1 r0 r1 : ℚ}, t.check σ T a0 a1 r0 r1 = true →
      (a0 : ℝ) * ρ ≤ dist p c → dist p c ≤ (a1 : ℝ) * ρ →
      (r0 : ℝ) * ρ ≤ dist p (q 0) → dist p (q 0) ≤ (r1 : ℝ) * ρ →
      ∃ i j : Fin 3, i ≠ j ∧ dist (q i) (q j) ^ 2 ≤ (T : ℝ) * ρ ^ 2 := by
  intro t
  induction t with
  | cert β =>
    intro a0 a1 r0 r1 h hpa0 hpa1 hpr0 hpr1
    exact exists_dist_sq_le_of_chordBoxCheck c p q h hρ hlo hhi heq hpa0 hpa1 hpr0 hpr1
  | disk =>
    intro a0 a1 r0 r1 h _ _ _ hpr1
    have hT : 4 * (r1 * r1) ≤ T := of_decide_eq_true h
    obtain ⟨i, j, hij, hclose⟩ := exists_dist_sq_le_four_mul_sq p q heq hpr1
    refine ⟨i, j, hij, hclose.trans ?_⟩
    have hT' : 4 * (r1 : ℝ) ^ 2 ≤ T := by
      have := (Rat.cast_le (K := ℝ)).mpr hT
      push_cast at this
      nlinarith [this]
    exact mul_le_mul_of_nonneg_right hT' (sq_nonneg ρ)
  | split t₁ t₂ t₃ t₄ ih₁ ih₂ ih₃ ih₄ =>
    intro a0 a1 r0 r1 h hpa0 hpa1 hpr0 hpr1
    simp only [ChordBoxTree.check, Bool.and_eq_true] at h
    obtain ⟨⟨⟨h₁, h₂⟩, h₃⟩, h₄⟩ := h
    rcases le_total (dist p c) ((((a0 + a1) / 2 : ℚ) : ℝ) * ρ) with ha | ha <;>
      rcases le_total (dist p (q 0)) ((((r0 + r1) / 2 : ℚ) : ℝ) * ρ) with hr | hr
    · exact ih₁ h₁ hpa0 ha hpr0 hr
    · exact ih₂ h₂ hpa0 ha hr hpr1
    · exact ih₃ h₃ ha hpa1 hpr0 hr
    · exact ih₄ h₄ ha hpa1 hr hpr1
  | splitApex t₁ t₂ ih₁ ih₂ =>
    intro a0 a1 r0 r1 h hpa0 hpa1 hpr0 hpr1
    simp only [ChordBoxTree.check, Bool.and_eq_true] at h
    rcases le_total (dist p c) ((((a0 + a1) / 2 : ℚ) : ℝ) * ρ) with ha | ha
    · exact ih₁ h.1 hpa0 ha hpr0 hpr1
    · exact ih₂ h.2 ha hpa1 hpr0 hpr1
  | splitRadius t₁ t₂ ih₁ ih₂ =>
    intro a0 a1 r0 r1 h hpa0 hpa1 hpr0 hpr1
    simp only [ChordBoxTree.check, Bool.and_eq_true] at h
    rcases le_total (dist p (q 0)) ((((r0 + r1) / 2 : ℚ) : ℝ) * ρ) with hr | hr
    · exact ih₁ h.1 hpa0 hpa1 hpr0 hr
    · exact ih₂ h.2 hpa0 hpa1 hr hpr1

/-- The check of the apex cells `[a, a₁], [a₁, a₂], …, [a_{k-1}, a_k]` with `a_k ≥ 1` (the list
holds the pairs `(a_m, tree_m)`), all for the radius cell `[r0, r1]`: every tree passes
`ChordBoxTree.check` on its cell. Started at `a = σ` it is the 32 apex cells of
`Chords.holds_on` of `scripts/verify_constant_gain_5_239.py` for one radius cell. -/
def chordApexCellsCheck (σ T r0 r1 : ℚ) : ℚ → List (ℚ × ChordBoxTree) → Bool
  | _, [] => false
  | a, (a', t) :: rest =>
      t.check σ T a a' r0 r1 && (decide (1 ≤ a') || chordApexCellsCheck σ T r0 r1 a' rest)

/-- **Soundness of the apex cells.** If `chordApexCellsCheck σ T r0 r1 a cells = true`, then for
every configuration of three points `q i` of the annulus `σ²ρ² ≤ |q i - c|² ≤ ρ²` at a common
distance `r` from an apex `p` with `a ρ ≤ |p - c| ≤ ρ` and `r0 ρ ≤ r ≤ r1 ρ`, two of the
points are at squared distance at most `T ρ²`. -/
theorem exists_dist_sq_le_of_chordApexCellsCheck (c p : Point) (q : Fin 3 → Point) {ρ : ℝ}
    {σ T r0 r1 : ℚ} (hρ : 0 < ρ) (hlo : ∀ i, (σ : ℝ) ^ 2 * ρ ^ 2 ≤ dist (q i) c ^ 2)
    (hhi : ∀ i, dist (q i) c ^ 2 ≤ ρ ^ 2) (heq : ∀ i j, dist p (q i) = dist p (q j))
    (hpc : dist p c ≤ ρ) (hpr0 : (r0 : ℝ) * ρ ≤ dist p (q 0))
    (hpr1 : dist p (q 0) ≤ (r1 : ℝ) * ρ) :
    ∀ (cells : List (ℚ × ChordBoxTree)) {a : ℚ}, chordApexCellsCheck σ T r0 r1 a cells = true →
      (a : ℝ) * ρ ≤ dist p c →
      ∃ i j : Fin 3, i ≠ j ∧ dist (q i) (q j) ^ 2 ≤ (T : ℝ) * ρ ^ 2 := by
  intro cells
  induction cells with
  | nil => intro a h; simp [chordApexCellsCheck] at h
  | cons cell rest ih =>
    obtain ⟨a', t⟩ := cell
    intro a h hpa
    simp only [chordApexCellsCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
    obtain ⟨ht, hrest⟩ := h
    rcases le_or_gt (dist p c) ((a' : ℝ) * ρ) with ha | ha
    · exact ChordBoxTree.exists_dist_sq_le_of_check c p q hρ hlo hhi heq t ht hpa ha hpr0 hpr1
    · rcases hrest with h1 | hrest
      · have h1' : (1 : ℝ) ≤ a' := by exact_mod_cast h1
        nlinarith
      · exact ih hrest ha.le

/-- The check of the radius cells `[lo, r₁], [r₁, r₂], …, [r_{k-1}, r_k]` with `r_k ≥ hi` (the
list holds the pairs `(r_m, apex cells_m)`): the apex cells of each radius cell, started at
`σ`, pass `chordApexCellsCheck`. This is `Chords.holds_on lo hi T` of
`scripts/verify_constant_gain_5_239.py` with the cells clipped to `[lo, hi]`. -/
def chordRadiusCellsCheck (σ T hi : ℚ) : ℚ → List (ℚ × List (ℚ × ChordBoxTree)) → Bool
  | _, [] => false
  | r, (r', cells) :: rest =>
      chordApexCellsCheck σ T r r' σ cells &&
        (decide (hi ≤ r') || chordRadiusCellsCheck σ T hi r' rest)

/-- **The chord condition from radius cells.** If `chordRadiusCellsCheck σ T hi lo cells = true`
and `0 ≤ hi`, then for every apex `p` of the annulus `σ²ρ² ≤ |p - c|² ≤ ρ²` and three points
`q i` of the annulus at a common distance `r` from `p` with `lo² ρ² ≤ r² ≤ hi² ρ²`, two of the
points are at squared distance at most `T ρ²`. This is the chord side condition `C([lo, hi], √T)`
of `scripts/verify_constant_gain_1_40.py` (which uses `(lo, hi]`) in units of `ρ`; all
hypotheses on the configuration are on squared distances. -/
theorem exists_dist_sq_le_of_chordRadiusCellsCheck (c p : Point) (q : Fin 3 → Point) {ρ : ℝ}
    {σ T lo hi : ℚ} (cells : List (ℚ × List (ℚ × ChordBoxTree)))
    (hcheck : chordRadiusCellsCheck σ T hi lo cells = true) (hhi0 : 0 ≤ hi) (hρ : 0 < ρ)
    (hp : (σ : ℝ) ^ 2 * ρ ^ 2 ≤ dist p c ^ 2) (hp1 : dist p c ^ 2 ≤ ρ ^ 2)
    (hlo : ∀ i, (σ : ℝ) ^ 2 * ρ ^ 2 ≤ dist (q i) c ^ 2) (hhi : ∀ i, dist (q i) c ^ 2 ≤ ρ ^ 2)
    (heq : ∀ i j, dist p (q i) = dist p (q j))
    (hr0 : (lo : ℝ) ^ 2 * ρ ^ 2 ≤ dist p (q 0) ^ 2)
    (hr1 : dist p (q 0) ^ 2 ≤ (hi : ℝ) ^ 2 * ρ ^ 2) :
    ∃ i j : Fin 3, i ≠ j ∧ dist (q i) (q j) ^ 2 ≤ (T : ℝ) * ρ ^ 2 := by
  have hle {x y : ℝ} (hy : 0 ≤ y) (h : x ^ 2 ≤ y ^ 2) : x ≤ y := (abs_le_of_sq_le_sq' h hy).2
  have hpσ : (σ : ℝ) * ρ ≤ dist p c := hle dist_nonneg (by rw [mul_pow]; exact hp)
  have hpc : dist p c ≤ ρ := hle hρ.le hp1
  have hplo : (lo : ℝ) * ρ ≤ dist p (q 0) := hle dist_nonneg (by rw [mul_pow]; exact hr0)
  have hhi0' : (0 : ℝ) ≤ hi := by exact_mod_cast hhi0
  have hphi : dist p (q 0) ≤ (hi : ℝ) * ρ :=
    hle (mul_nonneg hhi0' hρ.le) (by rw [mul_pow]; exact hr1)
  clear hr0 hr1 hp hp1
  induction cells generalizing lo with
  | nil => simp [chordRadiusCellsCheck] at hcheck
  | cons cell rest ih =>
    obtain ⟨r', acells⟩ := cell
    simp only [chordRadiusCellsCheck, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq] at hcheck
    obtain ⟨ha, hrest⟩ := hcheck
    rcases le_or_gt (dist p (q 0)) ((r' : ℝ) * ρ) with hr | hr
    · exact exists_dist_sq_le_of_chordApexCellsCheck c p q hρ hlo hhi heq hpc hplo hr acells ha
        hpσ
    · rcases hrest with h1 | hrest
      · have h1' : (hi : ℝ) ≤ r' := by exact_mod_cast h1
        nlinarith
      · exact ih hrest hr.le

/-- The check of a chord table: radius cells `[lo, r₁], [r₁, r₂], …, [r_{k-1}, r_k]` with
`r_k ≥ hi`, the entry `(r_m, T_m, apex cells_m)` carrying its own squared bound `T_m`, as the
table `Chords.tab` of `scripts/verify_constant_gain_5_239.py`. Proved once by `decide +kernel`,
it serves every range through the cheap `chordTableBoundCheck`. -/
def chordTableCheck (σ hi : ℚ) : ℚ → List (ℚ × ℚ × List (ℚ × ChordBoxTree)) → Bool
  | _, [] => false
  | r, (r', T', cells) :: rest =>
      chordApexCellsCheck σ T' r r' σ cells && (decide (hi ≤ r') || chordTableCheck σ hi r' rest)

/-- The bound check of a chord table on the radius range `(x, y]`: every table cell
`[r_{m-1}, r_m]` with `x < r_m` and `r_{m-1} ≤ y` has `T_m ≤ τ`. It reads only the cell ends and
bounds, not the trees (`Chords.max_on x y ≤ τ` of `scripts/verify_constant_gain_5_239.py`). -/
def chordTableBoundCheck (τ x y : ℚ) : ℚ → List (ℚ × ℚ × List (ℚ × ChordBoxTree)) → Bool
  | _, [] => true
  | r, (r', T', _) :: rest =>
      (decide (y < r) || decide (r' ≤ x) || decide (T' ≤ τ)) && chordTableBoundCheck τ x y r' rest

/-- **The chord condition from a chord table.** If `chordTableCheck σ hi lo table = true` and
`chordTableBoundCheck τ x y lo table = true`, with `0 ≤ hi` and `0 ≤ y`, then for every apex `p`
of the annulus `σ²ρ² ≤ |p - c|² ≤ ρ²` and three points `q i` of the annulus at a common distance
`r` from `p` with `lo² ρ² ≤ r² ≤ hi² ρ²` and `x² ρ² < r² ≤ y² ρ²`, two of the points are at
squared distance at most `τ ρ²`. This is the chord side condition `C((x, y], √τ)` of
`scripts/verify_constant_gain_1_40.py` from the table, in units of `ρ`. -/
theorem exists_dist_sq_le_of_chordTableCheck (c p : Point) (q : Fin 3 → Point) {ρ : ℝ}
    {σ τ lo hi x y : ℚ} (table : List (ℚ × ℚ × List (ℚ × ChordBoxTree)))
    (htable : chordTableCheck σ hi lo table = true)
    (hbound : chordTableBoundCheck τ x y lo table = true) (hhi0 : 0 ≤ hi) (hy0 : 0 ≤ y)
    (hρ : 0 < ρ) (hp : (σ : ℝ) ^ 2 * ρ ^ 2 ≤ dist p c ^ 2) (hp1 : dist p c ^ 2 ≤ ρ ^ 2)
    (hlo : ∀ i, (σ : ℝ) ^ 2 * ρ ^ 2 ≤ dist (q i) c ^ 2) (hhi : ∀ i, dist (q i) c ^ 2 ≤ ρ ^ 2)
    (heq : ∀ i j, dist p (q i) = dist p (q j))
    (hr0 : (lo : ℝ) ^ 2 * ρ ^ 2 ≤ dist p (q 0) ^ 2)
    (hr1 : dist p (q 0) ^ 2 ≤ (hi : ℝ) ^ 2 * ρ ^ 2)
    (hx : (x : ℝ) ^ 2 * ρ ^ 2 < dist p (q 0) ^ 2) (hy : dist p (q 0) ^ 2 ≤ (y : ℝ) ^ 2 * ρ ^ 2) :
    ∃ i j : Fin 3, i ≠ j ∧ dist (q i) (q j) ^ 2 ≤ (τ : ℝ) * ρ ^ 2 := by
  have hle {u v : ℝ} (hv : 0 ≤ v) (h : u ^ 2 ≤ v ^ 2) : u ≤ v := (abs_le_of_sq_le_sq' h hv).2
  have hpσ : (σ : ℝ) * ρ ≤ dist p c := hle dist_nonneg (by rw [mul_pow]; exact hp)
  have hpc : dist p c ≤ ρ := hle hρ.le hp1
  have hplo : (lo : ℝ) * ρ ≤ dist p (q 0) := hle dist_nonneg (by rw [mul_pow]; exact hr0)
  have hhi0' : (0 : ℝ) ≤ hi := by exact_mod_cast hhi0
  have hy0' : (0 : ℝ) ≤ y := by exact_mod_cast hy0
  have hphi : dist p (q 0) ≤ (hi : ℝ) * ρ :=
    hle (mul_nonneg hhi0' hρ.le) (by rw [mul_pow]; exact hr1)
  have hpx : (x : ℝ) * ρ < dist p (q 0) :=
    (abs_lt_of_sq_lt_sq' (by rw [mul_pow]; exact hx) dist_nonneg).2
  have hpy : dist p (q 0) ≤ (y : ℝ) * ρ := hle (mul_nonneg hy0' hρ.le) (by rw [mul_pow]; exact hy)
  clear hr0 hr1 hp hp1 hx hy
  induction table generalizing lo with
  | nil => simp [chordTableCheck] at htable
  | cons entry rest ih =>
    obtain ⟨r', T', acells⟩ := entry
    simp only [chordTableCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at htable
    simp only [chordTableBoundCheck, Bool.and_eq_true, Bool.or_eq_true,
      decide_eq_true_eq] at hbound
    obtain ⟨ha, hrest⟩ := htable
    obtain ⟨hb, hbrest⟩ := hbound
    rcases le_or_gt (dist p (q 0)) ((r' : ℝ) * ρ) with hr | hr
    · obtain ⟨i, j, hij, hclose⟩ :=
        exists_dist_sq_le_of_chordApexCellsCheck c p q hρ hlo hhi heq hpc hplo hr acells ha hpσ
      have hT : (T' : ℝ) ≤ τ := by
        rcases hb with (hb | hb) | hb
        · have : (y : ℝ) < lo := by exact_mod_cast hb
          nlinarith
        · have : (r' : ℝ) ≤ x := by exact_mod_cast hb
          nlinarith
        · exact_mod_cast hb
      exact ⟨i, j, hij, hclose.trans (mul_le_mul_of_nonneg_right hT (sq_nonneg ρ))⟩
    · rcases hrest with h1 | hrest
      · have h1' : (hi : ℝ) ≤ r' := by exact_mod_cast h1
        nlinarith
      · exact ih hrest hbrest hr.le

end Esgk
