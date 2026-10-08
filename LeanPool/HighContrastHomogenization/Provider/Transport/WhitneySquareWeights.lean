/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Transport.WhitneyRows

/-!
# High-contrast homogenization: Provider.Transport.WhitneySquareWeights

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The square weights of a filling row

The centered part of the principal cell sum of the grid transport is estimated
row by row, and each row contributes through the square weight
`(Σ_{V ∈ 𝒱_r(W;q)} (|V|/|W|)²)^{1/2}`: the finite-range matrix averaging lemma
turns a first-moment row bound into a bound on a centered matrix sum only at
the cost of replacing the row's weights by their `ℓ²` norm.  This file proves
the two square weights the transport uses, the square-weight bounds for the
boundary and bulk cells.

Both are pure counting, and both follow from a single observation: the cells of
one row of the filling are aligned cells of the *same* scale, so they all have
the same relative volume, and the sum of squares is that common weight times the
row's first-moment sum.  The boundary row therefore pays the cross-grid row
bound `e.two.grid.whitney.volumes`, of size `3^{r-j}`, once, and the
common weight, of size `3^{d(r-j)}`, once, for the printed exponent
`(d+1)(r-j)`.  The bulk row pays only the common weight, the first-moment sum of
a disjoint family inside the target being at most one, for the printed exponent
`-dλ_j`.

The one quantitative ingredient beyond the rows is the determinant ratio of the
two grids: the common weight of a scale-`r` row is `|det q|/|det p| · 3^{d(r-j)}`,
and the printed constant `C(d,K_hop)` must absorb the ratio.  It does, because a
linear image of the unit cube fits inside a cube of side `√d |M|`, so
`|det M| ≤ (√d|M|)^d`, and the grid ratio dominates `|p^{-1}q|`.  The exhibited
constant is

`C(d,K_hop) = (6 d^{3/2} K_hop (√d K_hop)^d)^{1/2}`,

one constant for both displays.
-/

namespace HCPolySupport
namespace HighContrast
namespace Transport

open MeasureTheory

open scoped Matrix

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-! ## The determinant of a linear map against its operator norm -/

/-- The volume of a centered coordinate cube of half-side `R`. -/
private theorem volume_absLe₀ {R : ℝ} (hR : 0 ≤ R) :
    volume {x : Vec d | ∀ i, |x i| ≤ R} = ENNReal.ofReal ((2 * R) ^ d) := by
  have hpi : {x : Vec d | ∀ i, |x i| ≤ R} = Set.univ.pi fun _ : Fin d => Set.Icc (-R) R := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_univ_pi, Set.mem_Icc, abs_le]
  rw [hpi, volume_pi, MeasureTheory.Measure.pi_pi]
  have hterm : ∀ _i : Fin d, volume (Set.Icc (-R) R) = ENNReal.ofReal (2 * R) := by
    intro _i
    rw [Real.volume_Icc]
    congr 1
    ring
  rw [Finset.prod_congr rfl fun i _ => hterm i, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← ENNReal.ofReal_pow (by linarith only [hR])]

/-- **The determinant against the operator norm.**  The image of the unit cube
under `M` lies in the coordinate cube of side `√d |M|`, and the image has volume
`|det M|`, so `|det M| ≤ (√d|M|)^d`.  The dimensional factor is the passage from
the Euclidean norm, which the operator norm measures, to the coordinate cube. -/
theorem abs_det_le_pow_norm (M : Mat d) : |M.det| ≤ (Real.sqrt d * ‖M‖) ^ d := by
  set R : ℝ := ‖M‖ * (Real.sqrt d * (1 / 2)) with hRdef
  have hR : 0 ≤ R := by positivity
  have hsub : matVecMul M '' centeredCube d 0 ⊆ {x : Vec d | ∀ i, |x i| ≤ R} := by
    rintro _ ⟨z, hz, rfl⟩ i
    refine abs_matVecMul_le_of_abs_le M (fun k => ?_) i
    rw [Recurrence.mem_centeredCube_iff] at hz
    have h := hz k
    rw [zpow_zero] at h
    rw [abs_le]
    constructor <;> linarith only [h.1, h.2]
  have himg : (fun z => (0 : Vec d) + matVecMul M z) '' centeredCube d 0
      = matVecMul M '' centeredCube d 0 := by
    refine congrArg (fun f => f '' centeredCube d 0) ?_
    funext z
    rw [zero_add]
  have hcube : volume (centeredCube d 0) = 1 := by
    rw [volume_centeredCube]
    norm_num
  have hvol : ENNReal.ofReal |M.det| ≤ ENNReal.ofReal ((2 * R) ^ d) := by
    have h1 := volume_image_affine M (0 : Vec d) (centeredCube d 0)
    rw [himg, hcube, mul_one] at h1
    rw [← h1, ← volume_absLe₀ (d := d) hR]
    exact measure_mono hsub
  have hkey : (2 * R) ^ d = (Real.sqrt d * ‖M‖) ^ d := by
    congr 1
    rw [hRdef]
    ring
  rw [hkey] at hvol
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hvol

/-- **The grid ratio is at least one**, its base being at least one.  Hence any
`K_hop` dominating it is at least one, and the printed constants may be compared
across the two square weights. -/
theorem one_le_gridRatio (q q' : Mat d) : 1 ≤ gridRatio q q' := by
  refine one_le_pow₀ ?_
  have hA : (0 : ℝ) ≤ ‖q⁻¹ * q'‖ := norm_nonneg _
  have hB : (0 : ℝ) ≤ ‖(q')⁻¹ * q‖ := norm_nonneg _
  linarith only [hA, hB]

/-! ## The common relative volume of a row -/

/-- **Every cell of a filling row has the same relative volume**, in closed
form: an aligned scale-`a` cell of the grid `q` inside the scale-`j` target cell
of the grid `p` has relative volume `|det q| 3^{ad} / (|det p| 3^{jd})`. -/
theorem relative_volume_eq (p q : Mat d) (a j : ℤ) (y : Vec d) (w : Fin d → ℤ) :
    (volume (adaptedCellAt q a w)).toReal / (volume (adaptedCellTranslate p j y)).toReal
      = (|q.det| * (3 : ℝ) ^ (a * (d : ℤ))) / (|p.det| * (3 : ℝ) ^ (j * (d : ℤ))) := by
  rw [adaptedCellAt_eq_adaptedCellTranslate, volume_adaptedCellTranslate,
    volume_adaptedCellTranslate, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity)]

/-- **The sum of squares of a row is the common weight times the row sum.**
This is the whole content of the two square weights: a row of the filling
consists of cells of one scale, so its `ℓ²` norm is controlled by its `ℓ¹` norm
with the common weight as the loss. -/
theorem sum_sq_relative_volume_eq (p q : Mat d) (a j : ℤ) (y : Vec d)
    (Z : Finset (Fin d → ℤ)) :
    ∑ w ∈ Z, ((volume (adaptedCellAt q a w)).toReal /
        (volume (adaptedCellTranslate p j y)).toReal) ^ 2 =
      (|q.det| * (3 : ℝ) ^ (a * (d : ℤ))) / (|p.det| * (3 : ℝ) ^ (j * (d : ℤ))) *
        ∑ w ∈ Z, (volume (adaptedCellAt q a w)).toReal /
          (volume (adaptedCellTranslate p j y)).toReal := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [relative_volume_eq p q a j y w]
  ring

/-- **The common weight of a row against the grid ratio.**  The relative volume
of a scale-`a` cell inside the scale-`j` target is the determinant ratio of the
two grids times `3^{d(a-j)}`, and the determinant ratio is at most
`(√d K_hop)^d`. -/
theorem relative_volume_le_hop {p q : Mat d} (hp : p.PosDef) {a j : ℤ} {Khop : ℝ}
    (hK : gridRatio q p ≤ Khop) (hd : 1 ≤ d) :
    (|q.det| * (3 : ℝ) ^ (a * (d : ℤ))) / (|p.det| * (3 : ℝ) ^ (j * (d : ℤ))) ≤
      (Real.sqrt d * Khop) ^ d * (3 : ℝ) ^ ((d : ℤ) * (a - j)) := by
  have hpd : (0 : ℝ) < |p.det| := abs_pos.mpr hp.det_pos.ne'
  have hdetratio : |q.det| / |p.det| ≤ (Real.sqrt d * Khop) ^ d := by
    have hprod : (p⁻¹ * q).det = (p.det)⁻¹ * q.det := by
      rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
    have habs : |(p⁻¹ * q).det| = |q.det| / |p.det| := by
      rw [hprod, abs_mul, abs_inv, div_eq_inv_mul]
    have hnorm : ‖p⁻¹ * q‖ ≤ Khop := ((norm_inv_mul_le_gridRatio hd q p).1).trans hK
    refine (habs ▸ abs_det_le_pow_norm (p⁻¹ * q)).trans ?_
    exact pow_le_pow_left₀ (by positivity)
      (mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _)) d
  have hsplit : (|q.det| * (3 : ℝ) ^ (a * (d : ℤ))) / (|p.det| * (3 : ℝ) ^ (j * (d : ℤ)))
      = |q.det| / |p.det| * (3 : ℝ) ^ ((d : ℤ) * (a - j)) := by
    rw [show (d : ℤ) * (a - j) = a * (d : ℤ) - j * (d : ℤ) by ring,
      zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
    have h3a : (0 : ℝ) < (3 : ℝ) ^ (a * (d : ℤ)) := by positivity
    have h3j : (0 : ℝ) < (3 : ℝ) ^ (j * (d : ℤ)) := by positivity
    field_simp
  rw [hsplit]
  exact mul_le_mul_of_nonneg_right hdetratio (by positivity)

/-! ## The two square weights -/

/-- **The boundary square weight in squared form.**  For a row below the
starting scale the first-moment sum carries the cross-grid decay `3^{a-j}` and
the common weight carries `3^{d(a-j)}`, for the printed exponent `(d+1)(a-j)`. -/
theorem sum_sq_relative_volume_row_le {p q : Mat d} (hd : 1 ≤ d) (hp : p.PosDef)
    (hq : q.PosDef) {n j a : ℤ} (han : a < n) {y : Vec d} {Z : Finset (Fin d → ℤ)}
    (hZ : ↑Z = fillingIndex q n (adaptedCellTranslate p j y) a) {Khop : ℝ}
    (hK : gridRatio q p ≤ Khop) :
    ∑ w ∈ Z, ((volume (adaptedCellAt q a w)).toReal /
        (volume (adaptedCellTranslate p j y)).toReal) ^ 2 ≤
      6 * (d : ℝ) * Real.sqrt d * Khop * (Real.sqrt d * Khop) ^ d *
        (3 : ℝ) ^ (((d : ℤ) + 1) * (a - j)) := by
  have hrow := sum_relative_volume_row_le_hop hd hp hq han hZ hK
  have hrownn : (0 : ℝ) ≤ ∑ w ∈ Z, (volume (adaptedCellAt q a w)).toReal /
      (volume (adaptedCellTranslate p j y)).toReal :=
    Finset.sum_nonneg fun _ _ => div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hw := relative_volume_le_hop (q := q) hp (a := a) (j := j) hK hd
  have hwnn : (0 : ℝ) ≤ (Real.sqrt d * Khop) ^ d * (3 : ℝ) ^ ((d : ℤ) * (a - j)) := by
    have hKnn : (0 : ℝ) ≤ Khop := le_trans zero_le_one ((one_le_gridRatio q p).trans hK)
    positivity
  rw [sum_sq_relative_volume_eq p q a j y Z]
  refine (mul_le_mul hw hrow hrownn hwnn).trans_eq ?_
  rw [show ((d : ℤ) + 1) * (a - j) = (d : ℤ) * (a - j) + (a - j) by ring,
    zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
  ring

/-- **The bulk square weight in squared form.**  A row is a disjoint family
inside the target, so its first-moment sum is at most one and only the common
weight survives. -/
theorem sum_sq_relative_volume_row_le_bulk {p q : Mat d} (hd : 1 ≤ d) (hp : p.PosDef)
    (hq : q.PosDef) {n j a : ℤ} {y : Vec d} {Z : Finset (Fin d → ℤ)}
    (hZ : ↑Z = fillingIndex q n (adaptedCellTranslate p j y) a) {Khop : ℝ}
    (hK : gridRatio q p ≤ Khop) :
    ∑ w ∈ Z, ((volume (adaptedCellAt q a w)).toReal /
        (volume (adaptedCellTranslate p j y)).toReal) ^ 2 ≤
      (Real.sqrt d * Khop) ^ d * (3 : ℝ) ^ ((d : ℤ) * (a - j)) := by
  have hrow := sum_relative_volume_row_le_one hp hq hZ
  have hrownn : (0 : ℝ) ≤ ∑ w ∈ Z, (volume (adaptedCellAt q a w)).toReal /
      (volume (adaptedCellTranslate p j y)).toReal :=
    Finset.sum_nonneg fun _ _ => div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hw := relative_volume_le_hop (q := q) hp (a := a) (j := j) hK hd
  have hwnn : (0 : ℝ) ≤ (Real.sqrt d * Khop) ^ d * (3 : ℝ) ^ ((d : ℤ) * (a - j)) := by
    have hKnn : (0 : ℝ) ≤ Khop := le_trans zero_le_one ((one_le_gridRatio q p).trans hK)
    positivity
  rw [sum_sq_relative_volume_eq p q a j y Z]
  refine (mul_le_mul hw hrow hrownn hwnn).trans_eq ?_
  rw [mul_one]

/-! ## The printed displays -/

/-- The square root of a triadic power is the triadic power of half the
exponent. -/
private theorem sqrt_zpow_three₀ (e : ℤ) :
    Real.sqrt ((3 : ℝ) ^ e) = (3 : ℝ) ^ ((e : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_intCast (3 : ℝ) e,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

/-- **The square-weight bound for the boundary cells.**  At a boundary source
scale the `ℓ²` norm of the relative volumes of a filling row is at most
`C(d,K_hop) 3^{(d+1)(r-j)/2}`, with

`C(d,K_hop) = (6 d^{3/2} K_hop (√d K_hop)^d)^{1/2}`.

A boundary scale is one strictly below the scale at which the filling of the
target starts; for the filling of a scale-`j` target with buffer `λ_j` that is
exactly the printed condition `r < j - λ_j`. -/
theorem boundary_square_weights {p q : Mat d} (hd : 1 ≤ d) (hp : p.PosDef)
    (hq : q.PosDef) {n j a : ℤ} (han : a < n) {y : Vec d} {Z : Finset (Fin d → ℤ)}
    (hZ : ↑Z = fillingIndex q n (adaptedCellTranslate p j y) a) {Khop : ℝ}
    (hK : gridRatio q p ≤ Khop) :
    Real.sqrt (∑ w ∈ Z, ((volume (adaptedCellAt q a w)).toReal /
        (volume (adaptedCellTranslate p j y)).toReal) ^ 2) ≤
      Real.sqrt (6 * (d : ℝ) * Real.sqrt d * Khop * (Real.sqrt d * Khop) ^ d) *
        (3 : ℝ) ^ (((d : ℝ) + 1) * ((a : ℝ) - (j : ℝ)) / 2) := by
  have hKnn : (0 : ℝ) ≤ Khop := le_trans zero_le_one ((one_le_gridRatio q p).trans hK)
  have hCnn : (0 : ℝ) ≤ 6 * (d : ℝ) * Real.sqrt d * Khop * (Real.sqrt d * Khop) ^ d := by
    positivity
  have hexp : ((((d : ℤ) + 1) * (a - j) : ℤ) : ℝ) / 2
      = ((d : ℝ) + 1) * ((a : ℝ) - (j : ℝ)) / 2 := by
    push_cast
    ring
  calc Real.sqrt (∑ w ∈ Z, ((volume (adaptedCellAt q a w)).toReal /
          (volume (adaptedCellTranslate p j y)).toReal) ^ 2)
      ≤ Real.sqrt (6 * (d : ℝ) * Real.sqrt d * Khop * (Real.sqrt d * Khop) ^ d *
          (3 : ℝ) ^ (((d : ℤ) + 1) * (a - j))) :=
        Real.sqrt_le_sqrt (sum_sq_relative_volume_row_le hd hp hq han hZ hK)
    _ = Real.sqrt (6 * (d : ℝ) * Real.sqrt d * Khop * (Real.sqrt d * Khop) ^ d) *
          Real.sqrt ((3 : ℝ) ^ (((d : ℤ) + 1) * (a - j))) := Real.sqrt_mul hCnn _
    _ = Real.sqrt (6 * (d : ℝ) * Real.sqrt d * Khop * (Real.sqrt d * Khop) ^ d) *
          (3 : ℝ) ^ (((d : ℝ) + 1) * ((a : ℝ) - (j : ℝ)) / 2) := by
        rw [sqrt_zpow_three₀, hexp]

/-- **The square-weight bound for the bulk cells.**  At the bulk source scale
`j - λ` the `ℓ²` norm of the relative volumes of a filling row is at most
`C(d,K_hop) 3^{-dλ/2}`, with the same constant

`C(d,K_hop) = (6 d^{3/2} K_hop (√d K_hop)^d)^{1/2}`

as the boundary display.  Unlike the boundary rows this one is unconditional in
the scale: it needs only disjointness inside the target, which is why the row at
which the filling starts, carrying no cross-grid decay, is still summable. -/
theorem bulk_square_weights {p q : Mat d} (hd : 1 ≤ d) (hp : p.PosDef)
    (hq : q.PosDef) {n j lam : ℤ} {y : Vec d} {Z : Finset (Fin d → ℤ)}
    (hZ : ↑Z = fillingIndex q n (adaptedCellTranslate p j y) (j - lam)) {Khop : ℝ}
    (hK : gridRatio q p ≤ Khop) :
    Real.sqrt (∑ w ∈ Z, ((volume (adaptedCellAt q (j - lam) w)).toReal /
        (volume (adaptedCellTranslate p j y)).toReal) ^ 2) ≤
      Real.sqrt (6 * (d : ℝ) * Real.sqrt d * Khop * (Real.sqrt d * Khop) ^ d) *
        (3 : ℝ) ^ (-(d : ℝ) * (lam : ℝ) / 2) := by
  have hKone : (1 : ℝ) ≤ Khop := (one_le_gridRatio q p).trans hK
  have hdone : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hsqrtd : (1 : ℝ) ≤ Real.sqrt d := by
    rw [show (1 : ℝ) = Real.sqrt 1 by rw [Real.sqrt_one]]
    exact Real.sqrt_le_sqrt hdone
  have hCbig : ((Real.sqrt d * Khop) ^ d : ℝ) ≤
      6 * (d : ℝ) * Real.sqrt d * Khop * (Real.sqrt d * Khop) ^ d := by
    have hpow : (0 : ℝ) ≤ (Real.sqrt d * Khop) ^ d := by positivity
    have h1 : (1 : ℝ) ≤ (d : ℝ) * Real.sqrt d :=
      hdone.trans (le_mul_of_one_le_right (by linarith only [hdone]) hsqrtd)
    have h2 : (1 : ℝ) ≤ (d : ℝ) * Real.sqrt d * Khop :=
      h1.trans (le_mul_of_one_le_right (by linarith only [h1]) hKone)
    exact le_mul_of_one_le_left hpow (by linarith only [h2])
  have hCnn : (0 : ℝ) ≤ 6 * (d : ℝ) * Real.sqrt d * Khop * (Real.sqrt d * Khop) ^ d := by
    positivity
  have hexp : ((((d : ℤ) * (j - lam - j)) : ℤ) : ℝ) / 2 = -(d : ℝ) * (lam : ℝ) / 2 := by
    push_cast
    ring
  have hbulk := sum_sq_relative_volume_row_le_bulk hd hp hq (a := j - lam) hZ hK
  have hstep : ∑ w ∈ Z, ((volume (adaptedCellAt q (j - lam) w)).toReal /
      (volume (adaptedCellTranslate p j y)).toReal) ^ 2 ≤
      6 * (d : ℝ) * Real.sqrt d * Khop * (Real.sqrt d * Khop) ^ d *
        (3 : ℝ) ^ ((d : ℤ) * (j - lam - j)) :=
    hbulk.trans (mul_le_mul_of_nonneg_right hCbig (by positivity))
  calc Real.sqrt (∑ w ∈ Z, ((volume (adaptedCellAt q (j - lam) w)).toReal /
          (volume (adaptedCellTranslate p j y)).toReal) ^ 2)
      ≤ Real.sqrt (6 * (d : ℝ) * Real.sqrt d * Khop * (Real.sqrt d * Khop) ^ d *
          (3 : ℝ) ^ ((d : ℤ) * (j - lam - j))) := Real.sqrt_le_sqrt hstep
    _ = Real.sqrt (6 * (d : ℝ) * Real.sqrt d * Khop * (Real.sqrt d * Khop) ^ d) *
          Real.sqrt ((3 : ℝ) ^ ((d : ℤ) * (j - lam - j))) := Real.sqrt_mul hCnn _
    _ = Real.sqrt (6 * (d : ℝ) * Real.sqrt d * Khop * (Real.sqrt d * Khop) ^ d) *
          (3 : ℝ) ^ (-(d : ℝ) * (lam : ℝ) / 2) := by
        rw [sqrt_zpow_three₀, hexp]

end

end Transport
end HighContrast
end HCPolySupport
