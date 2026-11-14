/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.CubeCarrier
public import LeanPool.HighContrastHomogenization.Support.Sobolev.W1p.ZeroExtensionGraph
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeNeumannW22CZ.WeakInteriorDQ.DiffQuotientLp

/-!
# ZeroTraceBoundary

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The boundary values of a zero-trace function on a cube

A function of `H¹₀(y + □_n)` has no pointwise boundary values, but a
representative that is continuous up to the boundary does, and they vanish.
This module proves that, with no regularity hypothesis whatsoever beyond
membership in `H¹₀` and the existence of the representative.

The mechanism is the translation estimate for the zero extension.  Write `w`
for the extension of `w : H¹₀(y + □_n)` by zero, an `H¹` function of the whole
space whose gradient is the zero extension of the gradient of `w`, and fix a
coordinate direction `e_i` in which the boundary point `x₀` sits on a face of
the cube.  For a step `t` the `L²` norm of the difference quotient
`(w(·) − w(· − t e_i))/t` is at most the `L²` norm of `∂_i w`, a quantity
independent of `t`.  If the representative had modulus at least `ε` on
`(y + □_n) ∩ B_ρ(x₀)`, then that difference quotient would have modulus at
least `ε/t` on an explicit box of measure of order `t · ρ^{d−1}` just outside
the face: the shifted point lies in the cube near `x₀`, where the modulus is at
least `ε`, and the point itself lies outside the cube, where the extension
vanishes.  The two statements give `ε² ρ^{d−1} ≲ t`, which fails for small `t`.

At an edge or a corner of the cube the same box works: only one coordinate is
moved, and the remaining coordinates are confined to intervals pushed into the
cube by the fixed factor `1 − θ`, which is what the box below records.

## References

* ABK26, the localized estimates of Section 5.1.
-/

namespace Algsuperdiff.Section5.Support

open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The cube and its boundary in coordinates -/

/-- Membership in `y + □_n` written with absolute values. -/
theorem mem_cubeSetAt_iff_abs_coord {y : Vec d} {n : ℤ} {x : Vec d} :
    x ∈ cubeSetAt y n ↔ ∀ j, |x j - y j| < (1 / 2 : ℝ) * (3 : ℝ) ^ n := by
  rw [mem_cubeSetAt_iff_forall_coord]
  refine forall_congr' fun j => ?_
  rw [abs_lt]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith only [h1], h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith only [h1], h2⟩

private theorem cubeSetAt_subset_closedBall (y : Vec d) (n : ℤ) :
    cubeSetAt y n ⊆ Metric.closedBall y ((1 / 2 : ℝ) * (3 : ℝ) ^ n) := by
  intro x hx
  rw [mem_cubeSetAt_iff_abs_coord] at hx
  rw [Metric.mem_closedBall, dist_eq_norm]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  rw [Pi.sub_apply, Real.norm_eq_abs]
  exact (hx j).le

/-- Every coordinate of a boundary point of `y + □_n` is within the half-width
of the corresponding coordinate of the centre. -/
theorem abs_coord_le_of_mem_frontier_cubeSetAt {y : Vec d} {n : ℤ} {x₀ : Vec d}
    (hx₀ : x₀ ∈ frontier (cubeSetAt y n)) (j : Fin d) :
    |x₀ j - y j| ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ n := by
  have hcl : x₀ ∈ Metric.closedBall y ((1 / 2 : ℝ) * (3 : ℝ) ^ n) :=
    closure_minimal (cubeSetAt_subset_closedBall y n) Metric.isClosed_closedBall
      (frontier_subset_closure hx₀)
  rw [Metric.mem_closedBall, dist_eq_norm] at hcl
  have hj := norm_le_pi_norm (x₀ - y) j
  rw [Pi.sub_apply, Real.norm_eq_abs] at hj
  linarith only [hj, hcl]

/-- A boundary point of `y + □_n` sits on a face: some coordinate attains the
half-width exactly. -/
theorem exists_abs_coord_eq_of_mem_frontier_cubeSetAt {y : Vec d} {n : ℤ} {x₀ : Vec d}
    (hx₀ : x₀ ∈ frontier (cubeSetAt y n)) :
    ∃ i : Fin d, |x₀ i - y i| = (1 / 2 : ℝ) * (3 : ℝ) ^ n := by
  have hA : (0 : ℝ) < (1 / 2 : ℝ) * (3 : ℝ) ^ n := by positivity
  have hnot : x₀ ∉ cubeSetAt y n := by
    have h := hx₀.2
    rwa [(isOpen_cubeSetAt y n).interior_eq] at h
  rw [mem_cubeSetAt_iff_abs_coord] at hnot
  push Not at hnot
  obtain ⟨i, hi⟩ := hnot
  exact ⟨i, le_antisymm (abs_coord_le_of_mem_frontier_cubeSetAt hx₀ i) hi⟩

/-- The coordinates of a coordinate shift. -/
private theorem coordShift_apply (h : ℝ) (i : Fin d) (x : Vec d) (j : Fin d) :
    euclideanCoordShift h i x j = if j = i then x j + h else x j := by
  by_cases hj : j = i <;> simp [euclideanCoordShift, basisVec, hj]

/-! ## 2. The box just outside a face -/

/-- The geometry of the argument: a point whose `i₀` coordinate has been pushed
just outside the face of `y + □_n` through `x₀`, and whose other coordinates are
confined to intervals contracted towards the centre by the factor `1 - θ`, lies
outside the cube, while its backward shift by `sgn * t` in the direction `i₀`
lies inside the cube and within `ρ` of `x₀`. -/
private theorem outside_and_shift_mem {y : Vec d} {n : ℤ} {x₀ : Vec d}
    (hx₀ : x₀ ∈ frontier (cubeSetAt y n))
    {i₀ : Fin d} {sgn theta t rho : ℝ}
    (hsgn1 : sgn = 1 ∨ sgn = -1)
    (hsgn : x₀ i₀ - y i₀ = sgn * ((1 / 2 : ℝ) * (3 : ℝ) ^ n))
    (htheta0 : 0 < theta) (htheta1 : theta ≤ 1)
    (hthetarho : 2 * theta * ((1 / 2 : ℝ) * (3 : ℝ) ^ n) ≤ rho)
    (ht0 : 0 < t) (htA : t ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ n) (htrho : t ≤ rho)
    {x : Vec d}
    (hxbox : ∀ j, j ≠ i₀ →
      |x j - (y j + (1 - theta) * (x₀ j - y j))| < theta * ((1 / 2 : ℝ) * (3 : ℝ) ^ n))
    (hxlo : 0 < sgn * (x i₀ - x₀ i₀)) (hxhi : sgn * (x i₀ - x₀ i₀) < t / 2) :
    x ∉ cubeSetAt y n ∧
      euclideanCoordShift (-(sgn * t)) i₀ x ∈ cubeSetAt y n ∧
      ‖euclideanCoordShift (-(sgn * t)) i₀ x - x₀‖ < rho := by
  have hA : (0 : ℝ) < (1 / 2 : ℝ) * (3 : ℝ) ^ n := by positivity
  have hsgnsq : sgn * sgn = 1 := by rcases hsgn1 with rfl | rfl <;> norm_num
  have hsgnabs : |sgn| = 1 := by rcases hsgn1 with rfl | rfl <;> norm_num
  have habs : ∀ u : ℝ, |sgn * u| = |u| := by
    intro u
    rw [abs_mul, hsgnabs, one_mul]
  have hxi : sgn * (x i₀ - y i₀) = sgn * (x i₀ - x₀ i₀) + (1 / 2 : ℝ) * (3 : ℝ) ^ n := by
    have hsplit : x i₀ - y i₀ = (x i₀ - x₀ i₀) + (x₀ i₀ - y i₀) := by ring
    rw [hsplit, mul_add, hsgn, ← mul_assoc, hsgnsq, one_mul]
  -- the tangential coordinates stay inside and close to `x₀`
  have htang : ∀ j, j ≠ i₀ →
      |x j - y j| < (1 / 2 : ℝ) * (3 : ℝ) ^ n ∧ |x j - x₀ j| < rho := by
    intro j hj
    have hbj := hxbox j hj
    have hfr := abs_coord_le_of_mem_frontier_cubeSetAt hx₀ j
    have hcy : |(y j + (1 - theta) * (x₀ j - y j)) - y j| ≤
        (1 - theta) * ((1 / 2 : ℝ) * (3 : ℝ) ^ n) := by
      have hrw : (y j + (1 - theta) * (x₀ j - y j)) - y j = (1 - theta) * (x₀ j - y j) := by
        ring
      rw [hrw, abs_mul, abs_of_nonneg (by linarith only [htheta1] : (0 : ℝ) ≤ 1 - theta)]
      exact mul_le_mul_of_nonneg_left hfr (by linarith only [htheta1])
    have hcx : |(y j + (1 - theta) * (x₀ j - y j)) - x₀ j| ≤
        theta * ((1 / 2 : ℝ) * (3 : ℝ) ^ n) := by
      have hrw : (y j + (1 - theta) * (x₀ j - y j)) - x₀ j = (-theta) * (x₀ j - y j) := by
        ring
      rw [hrw, abs_mul, abs_neg, abs_of_nonneg htheta0.le]
      exact mul_le_mul_of_nonneg_left hfr htheta0.le
    constructor
    · have htri : |x j - y j| ≤
          |x j - (y j + (1 - theta) * (x₀ j - y j))| +
            |(y j + (1 - theta) * (x₀ j - y j)) - y j| :=
        abs_sub_le _ _ _
      have hsum : theta * ((1 / 2 : ℝ) * (3 : ℝ) ^ n) +
          (1 - theta) * ((1 / 2 : ℝ) * (3 : ℝ) ^ n) = (1 / 2 : ℝ) * (3 : ℝ) ^ n := by ring
      linarith only [htri, hbj, hcy, hsum]
    · have htri : |x j - x₀ j| ≤
          |x j - (y j + (1 - theta) * (x₀ j - y j))| +
            |(y j + (1 - theta) * (x₀ j - y j)) - x₀ j| :=
        abs_sub_le _ _ _
      have hsum : theta * ((1 / 2 : ℝ) * (3 : ℝ) ^ n) +
          theta * ((1 / 2 : ℝ) * (3 : ℝ) ^ n) = 2 * theta * ((1 / 2 : ℝ) * (3 : ℝ) ^ n) := by
        ring
      linarith only [htri, hbj, hcx, hsum, hthetarho]
  refine ⟨?_, ?_, ?_⟩
  · intro hmem
    rw [mem_cubeSetAt_iff_abs_coord] at hmem
    have h1 : sgn * (x i₀ - y i₀) ≤ |x i₀ - y i₀| := by
      calc sgn * (x i₀ - y i₀) ≤ |sgn * (x i₀ - y i₀)| := le_abs_self _
        _ = |x i₀ - y i₀| := habs _
    have h2 := hmem i₀
    linarith only [h1, h2, hxi, hxlo]
  · rw [mem_cubeSetAt_iff_abs_coord]
    intro j
    rcases eq_or_ne j i₀ with rfl | hj
    · rw [coordShift_apply, ite_eq_left rfl]
      have hval : sgn * (x j + -(sgn * t) - y j) =
          sgn * (x j - y j) - t := by
        have hrw : sgn * (x j + -(sgn * t) - y j) = sgn * (x j - y j) - (sgn * sgn) * t := by
          ring
        rw [hrw, hsgnsq, one_mul]
      rw [← habs (x j + -(sgn * t) - y j), hval, abs_lt]
      constructor <;> linarith only [hxi, hxlo, hxhi, htA, hA]
    · rw [coordShift_apply, ite_eq_right hj]
      exact (htang j hj).1
  · refine (pi_norm_lt_iff (lt_of_lt_of_le ht0 htrho)).2 fun j => ?_
    rw [Pi.sub_apply, Real.norm_eq_abs]
    rcases eq_or_ne j i₀ with rfl | hj
    · rw [coordShift_apply, ite_eq_left rfl]
      have hval : sgn * (x j + -(sgn * t) - x₀ j) = sgn * (x j - x₀ j) - t := by
        have hrw : sgn * (x j + -(sgn * t) - x₀ j) = sgn * (x j - x₀ j) - (sgn * sgn) * t := by
          ring
        rw [hrw, hsgnsq, one_mul]
      rw [← habs (x j + -(sgn * t) - x₀ j), hval, abs_lt]
      constructor <;> linarith only [hxlo, hxhi, ht0, htrho]
    · rw [coordShift_apply, ite_eq_right hj]
      exact (htang j hj).2

/-! ## 3. Arbitrarily small values arbitrarily close to the boundary -/

private theorem mem_Ioo_min_max {sgn t a u : ℝ} (hsgn1 : sgn = 1 ∨ sgn = -1) (ht0 : 0 < t)
    (hu : u ∈ Set.Ioo (a + min 0 (sgn * t / 2)) (a + max 0 (sgn * t / 2))) :
    0 < sgn * (u - a) ∧ sgn * (u - a) < t / 2 := by
  rw [Set.mem_Ioo] at hu
  rcases hsgn1 with rfl | rfl
  · rw [one_mul, min_eq_left (by linarith only [ht0]),
      max_eq_right (by linarith only [ht0])] at hu
    exact ⟨by linarith only [hu.1], by linarith only [hu.2]⟩
  · rw [show ((-1 : ℝ) * t / 2) = -(t / 2) by ring, min_eq_right (by linarith only [ht0]),
      max_eq_left (by linarith only [ht0])] at hu
    exact ⟨by linarith only [hu.2], by linarith only [hu.1]⟩

/-- **Arbitrarily close to a boundary point of `y + □_n`, and inside the cube, a
representative of an `H¹₀` function takes arbitrarily small values.** -/
theorem exists_mem_cubeSetAt_abs_lt_of_mem_frontier {y : Vec d} {n : ℤ}
    (w : H10Function (cubeSetAt y n)) {v : Vec d → ℝ}
    (hv : v =ᵐ[volume.restrict (cubeSetAt y n)] w.toH1Function.toFun)
    {x₀ : Vec d} (hx₀ : x₀ ∈ frontier (cubeSetAt y n))
    {rho eps : ℝ} (hrho : 0 < rho) (heps : 0 < eps) :
    ∃ x ∈ cubeSetAt y n, ‖x - x₀‖ < rho ∧ |v x| < eps := by
  by_contra hcontra
  push Not at hcontra
  have hA : (0 : ℝ) < (1 / 2 : ℝ) * (3 : ℝ) ^ n := by positivity
  obtain ⟨i₀, hi₀⟩ := exists_abs_coord_eq_of_mem_frontier_cubeSetAt hx₀
  obtain ⟨sgn, hsgn1, hsgn⟩ :
      ∃ sgn : ℝ, (sgn = 1 ∨ sgn = -1) ∧ x₀ i₀ - y i₀ = sgn * ((1 / 2 : ℝ) * (3 : ℝ) ^ n) := by
    rcases (abs_eq hA.le).1 hi₀ with h | h
    · exact ⟨1, Or.inl rfl, by rw [h]; ring⟩
    · exact ⟨-1, Or.inr rfl, by rw [h]; ring⟩
  have hUmeas : MeasurableSet (cubeSetAt y n) := measurableSet_cubeSetAt y n
  set W : H10Function (Set.univ : Set (Vec d)) :=
    w.extendByZeroToOpenSuperset hUmeas isOpen_univ (Set.subset_univ _) with hWdef
  have hRtop : eLpNorm (fun z => W.toH1Function.grad z i₀) 2 (volume.restrict Set.univ) ≠ ⊤ :=
    (W.toH1Function.gradMemL2 i₀).eLpNorm_lt_top.ne
  set R : ℝ := (eLpNorm (fun z => W.toH1Function.grad z i₀) 2 (volume.restrict Set.univ)).toReal
    with hRdef
  have hR0 : (0 : ℝ) ≤ R := ENNReal.toReal_nonneg
  -- the tangential contraction factor and the step
  set theta : ℝ := min 1 (rho / (2 * ((1 / 2 : ℝ) * (3 : ℝ) ^ n))) with hthetadef
  have htheta0 : 0 < theta := lt_min one_pos (by positivity)
  have htheta1 : theta ≤ 1 := min_le_left _ _
  have hthetarho : 2 * theta * ((1 / 2 : ℝ) * (3 : ℝ) ^ n) ≤ rho := by
    have hle : theta ≤ rho / (2 * ((1 / 2 : ℝ) * (3 : ℝ) ^ n)) := min_le_right _ _
    have hstep : 2 * theta * ((1 / 2 : ℝ) * (3 : ℝ) ^ n) ≤
        2 * (rho / (2 * ((1 / 2 : ℝ) * (3 : ℝ) ^ n))) * ((1 / 2 : ℝ) * (3 : ℝ) ^ n) := by
      have h2 : (0 : ℝ) ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ n := hA.le
      nlinarith only [hle, h2]
    have hcalc : 2 * (rho / (2 * ((1 / 2 : ℝ) * (3 : ℝ) ^ n))) * ((1 / 2 : ℝ) * (3 : ℝ) ^ n)
        = rho := by
      field_simp
    linarith only [hstep, hcalc]
  set eta : ℝ := theta * ((1 / 2 : ℝ) * (3 : ℝ) ^ n) with hetadef
  have heta0 : 0 < eta := by rw [hetadef]; positivity
  set m : ℝ := (2 * eta) ^ (d - 1) with hmdef
  have hm0 : 0 < m := by rw [hmdef]; positivity
  set t : ℝ := min (min rho ((1 / 2 : ℝ) * (3 : ℝ) ^ n)) (eps ^ 2 * m / (2 * (R ^ 2 + 1)))
    with htdef
  have ht0 : 0 < t := by
    rw [htdef]
    exact lt_min (lt_min hrho hA) (by positivity)
  have htrho : t ≤ rho := le_trans (min_le_left _ _) (min_le_left _ _)
  have htA : t ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ n := le_trans (min_le_left _ _) (min_le_right _ _)
  have htlast : t ≤ eps ^ 2 * m / (2 * (R ^ 2 + 1)) := min_le_right _ _
  have hsgnne : sgn ≠ 0 := by rcases hsgn1 with rfl | rfl <;> norm_num
  have hs0 : sgn * t ≠ 0 := mul_ne_zero hsgnne ht0.ne'
  -- the box just outside the face
  set J : Fin d → Set ℝ :=
    Function.update (fun j => Set.Ioo (y j + (1 - theta) * (x₀ j - y j) - eta)
        (y j + (1 - theta) * (x₀ j - y j) + eta)) i₀
      (Set.Ioo (x₀ i₀ + min 0 (sgn * t / 2)) (x₀ i₀ + max 0 (sgn * t / 2))) with hJdef
  have hJi : J i₀ = Set.Ioo (x₀ i₀ + min 0 (sgn * t / 2)) (x₀ i₀ + max 0 (sgn * t / 2)) := by
    rw [hJdef, Function.update_self]
  have hJne : ∀ j, j ≠ i₀ → J j = Set.Ioo (y j + (1 - theta) * (x₀ j - y j) - eta)
      (y j + (1 - theta) * (x₀ j - y j) + eta) := fun j hj => by
    rw [hJdef, Function.update_of_ne hj]
  set Q : Set (Vec d) := Set.univ.pi J with hQdef
  have hQmeas : MeasurableSet Q := by
    rw [hQdef]
    refine MeasurableSet.univ_pi fun j => ?_
    rcases eq_or_ne j i₀ with rfl | hj
    · rw [hJi]; exact measurableSet_Ioo
    · rw [hJne j hj]; exact measurableSet_Ioo
  have hvolQ : volume Q = ENNReal.ofReal (t / 2 * m) := by
    rw [hQdef, volume_pi_pi, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
    have hfst : volume (J i₀) = ENNReal.ofReal (t / 2) := by
      rw [hJi, Real.volume_Ioo]
      congr 1
      have hrw : x₀ i₀ + max 0 (sgn * t / 2) - (x₀ i₀ + min 0 (sgn * t / 2))
          = max 0 (sgn * t / 2) - min 0 (sgn * t / 2) := by ring
      rw [hrw, max_sub_min_eq_abs, sub_zero, abs_div, abs_mul]
      rcases hsgn1 with rfl | rfl <;>
        · rw [abs_of_pos ht0]
          norm_num
    have hsnd : ∏ j ∈ Finset.univ.erase i₀, volume (J j)
        = ∏ _j ∈ Finset.univ.erase i₀, ENNReal.ofReal (2 * eta) := by
      refine Finset.prod_congr rfl fun j hj => ?_
      rw [hJne j (Finset.ne_of_mem_erase hj), Real.volume_Ioo]
      congr 1
      ring
    rw [hfst, hsnd, Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i₀),
      Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← hmdef]
  -- the difference quotient is large on the box
  have hPU : ∀ᵐ z ∂(volume : Measure (Vec d)),
      z ∈ cubeSetAt y n → v z = w.toH1Function.toFun z := (ae_restrict_iff' hUmeas).1 hv
  have hPshift : ∀ᵐ z ∂(volume : Measure (Vec d)),
      euclideanCoordShift (-(sgn * t)) i₀ z ∈ cubeSetAt y n →
        v (euclideanCoordShift (-(sgn * t)) i₀ z)
          = w.toH1Function.toFun (euclideanCoordShift (-(sgn * t)) i₀ z) :=
    (measurePreserving_add_right volume ((-(sgn * t)) • basisVec i₀)).quasiMeasurePreserving.ae
      hPU
  have hae : ∀ᵐ z ∂(volume.restrict Q),
      ‖(eps / t : ℝ)‖ ≤
        ‖euclideanBackwardDifferenceQuotient (sgn * t) i₀ W.toH1Function.toFun z‖ := by
    refine (ae_restrict_iff' hQmeas).2 ?_
    filter_upwards [hPshift] with z hzae hzQ
    have hzJ : ∀ j, z j ∈ J j := Set.mem_univ_pi.1 hzQ
    have hzi := mem_Ioo_min_max hsgn1 ht0 (by rw [← hJi]; exact hzJ i₀)
    have hzbox : ∀ j, j ≠ i₀ →
        |z j - (y j + (1 - theta) * (x₀ j - y j))| < theta * ((1 / 2 : ℝ) * (3 : ℝ) ^ n) := by
      intro j hj
      have h := hzJ j
      rw [hJne j hj, Set.mem_Ioo] at h
      rw [abs_lt, ← hetadef]
      exact ⟨by linarith only [h.1], by linarith only [h.2]⟩
    obtain ⟨hzout, hzin, hzrho⟩ :=
      outside_and_shift_mem hx₀ hsgn1 hsgn htheta0 htheta1 hthetarho ht0 htA htrho hzbox
        hzi.1 hzi.2
    have hWz : W.toH1Function.toFun z = 0 := by
      rw [hWdef, H10Function.extendByZeroToOpenSuperset_toFun,
        H10Function.zeroExtension_apply_of_not_mem _ hzout]
    have hWshift : W.toH1Function.toFun (euclideanCoordShift (-(sgn * t)) i₀ z)
        = v (euclideanCoordShift (-(sgn * t)) i₀ z) := by
      rw [hWdef, H10Function.extendByZeroToOpenSuperset_toFun,
        H10Function.zeroExtension_apply_of_mem _ hzin, ← hzae hzin]
    have hbig : eps ≤ |v (euclideanCoordShift (-(sgn * t)) i₀ z)| :=
      hcontra _ hzin hzrho
    have habs : |sgn * t| = t := by
      rcases hsgn1 with rfl | rfl <;> simp [abs_of_pos ht0]
    rw [euclideanBackwardDifferenceQuotient_apply, hWz, hWshift, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (show (0 : ℝ) < eps / t by positivity), abs_div, habs,
      zero_sub, abs_neg]
    gcongr
  -- the translation estimate for the zero extension closes the argument
  have hconst : eLpNorm (fun _ : Vec d => (eps / t : ℝ)) 2 (volume.restrict Q)
      ≤ eLpNorm (euclideanBackwardDifferenceQuotient (sgn * t) i₀ W.toH1Function.toFun) 2
          (volume.restrict Q) := eLpNorm_mono_ae aestronglyMeasurable_const hae
  have hrest : eLpNorm (euclideanBackwardDifferenceQuotient (sgn * t) i₀ W.toH1Function.toFun) 2
        (volume.restrict Q)
      ≤ eLpNorm (euclideanBackwardDifferenceQuotient (sgn * t) i₀ W.toH1Function.toFun) 2
          volume := eLpNorm_mono_measure _ Measure.restrict_le_self
  have hgradle := WeakPoissonEquationOn.eLpNorm_h10_backwardDifferenceQuotient_le_eLpNorm_grad
    (U := (Set.univ : Set (Vec d))) MeasurableSet.univ W (Set.subset_univ _) hs0 i₀
  have hchain : eLpNorm (fun _ : Vec d => (eps / t : ℝ)) 2 (volume.restrict Q)
      ≤ ENNReal.ofReal R := by
    rw [hRdef, ENNReal.ofReal_toReal hRtop]
    exact hconst.trans (hrest.trans hgradle)
  rw [eLpNorm_const' _ (by norm_num) (by norm_num), Measure.restrict_apply_univ, hvolQ,
    Real.enorm_eq_ofReal_abs, abs_of_pos (show (0 : ℝ) < eps / t by positivity),
    show ((2 : ℝ≥0∞).toReal) = 2 by norm_num,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
    ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff hR0] at hchain
  have htne : t ≠ 0 := ht0.ne'
  set S : ℝ := Real.sqrt (t / 2 * m) with hSdef
  have hSsq : S * S = t / 2 * m := Real.mul_self_sqrt (by positivity)
  have hS0 : 0 < S := Real.sqrt_pos.2 (by positivity)
  have hchain2 : eps / t * S ≤ R := by
    rw [hSdef, Real.sqrt_eq_rpow]
    exact hchain
  have hsq : eps / t * S * (eps / t * S) ≤ R * R :=
    mul_self_le_mul_self (by positivity) hchain2
  have hexp : eps / t * S * (eps / t * S) = eps / t * (eps / t) * (S * S) := by ring
  rw [hexp, hSsq] at hsq
  have hmul : eps / t * (eps / t) * (t / 2 * m) * (2 * t) ≤ R * R * (2 * t) :=
    mul_le_mul_of_nonneg_right hsq (by positivity)
  have hlhs : eps / t * (eps / t) * (t / 2 * m) * (2 * t) = eps * eps * m := by
    field_simp
  rw [hlhs] at hmul
  have hbound2 : t * (2 * (R ^ 2 + 1)) ≤ eps ^ 2 * m := (le_div_iff₀ (by positivity)).1 htlast
  linarith only [hmul, hbound2, ht0]

end

end Algsuperdiff.Section5.Support
