/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.HarmonicGauge
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.OscillationMeanSquare

/-!
# OscillationDecayAverage

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Averaging toolkit for the arbitrary-gap oscillation estimate

The arbitrary-gap estimate behind `e.nablaw.oscillations` is proved by turning
a *pointwise* interior bound for the gradient of a harmonic function into a
*mean-square* bound on a concentric triadic cube.  Three purely
measure-theoretic steps are needed for that passage, and none of them is
available in CoarseGraining:

1. **Cauchy--Schwarz against the constant `1`.**  The interior estimate produces
   the average of `|grad u - c|`, while the right-hand side of the target is the
   normalized `L^2` deviation.  The elementary inequality
   `(avg_V |f - c|)^2 <= avg_V (f - c)^2` bridges the two.  It is proved here
   from `0 <= int_V (|f - c| - t)^2` with the optimal `t`, so no `L^p` duality,
   Holder machinery or `MemLp` bookkeeping is used.
2. **Mean recentring.**  `meanSquareOscillationVecOn` is the deviation from the
   volume average, whereas the pointwise bound is naturally centred at a fixed
   point of the cube.  The variance identity
   `int_V (f - c)^2 = int_V (f - avg_V f)^2 + |V| (avg_V f - c)^2` shows that the
   average is the minimizer, so any centre may be used.
3. **Pointwise to mean-square.**  A uniform bound for `vecNormSq (h - c)` on `V`
   bounds `meanSquareDeviationVecOn V h c` by the same constant.

The remaining declarations are the two elementary facts about the concentric
cube family that the pointwise step consumes: the centre belongs to the cube,
the sup-norm diameter is `3^m`, and a continuous function is integrable on it.

## Contents

* `mem_openCubeAtScale_self`, `norm_sub_le_of_mem_openCubeAtScale`,
  `integrableOn_openCubeAtScale_of_continuous` -- the cube facts.
* `sq_setIntegral_abs_le_mul_setIntegral_sq`,
  `sq_volumeAverage_abs_sub_le_meanSquareDeviationOn` -- Cauchy--Schwarz.
* `meanSquareDeviationOn_volumeAverage_le`,
  `meanSquareOscillationVecOn_le_meanSquareDeviationVecOn` -- mean recentring.
* `meanSquareDeviationVecOn_le_of_forall_vecNormSq_le` -- pointwise to
  mean-square.

## References

* ABK26, `e.nablaw.oscillations` (the eventual consumer).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport HCPolySupport.Book.Ch03 MeasureTheory

variable {d : ℕ}

/-! ### Elementary facts about the concentric cube family -/

/-- The centre of a concentric triadic cube belongs to it. -/
theorem mem_openCubeAtScale_self (z : Vec d) (m : ℤ) : z ∈ openCubeAtScale z m := by
  rw [mem_openCubeAtScale_iff]
  intro i
  simpa using (by positivity : (0 : ℝ) < (3 : ℝ) ^ m / 2)

/-- **The sup-norm diameter of a concentric cube.**

`Vec d` carries the sup norm, so two points of the cube of scale `m` differ by at
most its side length `3^m`.  This is the gauge in which the convex mean-value
inequality is applied on the cube. -/
theorem norm_sub_le_of_mem_openCubeAtScale {z : Vec d} {m : ℤ} {x y : Vec d}
    (hx : x ∈ openCubeAtScale z m) (hy : y ∈ openCubeAtScale z m) :
    ‖x - y‖ ≤ (3 : ℝ) ^ m := by
  rw [mem_openCubeAtScale_iff] at hx hy
  refine (pi_norm_le_iff_of_nonneg (zpow_three_pos m).le).2 fun i => ?_
  have hxi := abs_lt.mp (hx i)
  have hyi := abs_lt.mp (hy i)
  have hval : (x - y) i = x i - y i := by simp
  rw [hval, Real.norm_eq_abs, abs_le]
  constructor <;> linarith [hxi.1, hxi.2, hyi.1, hyi.2]

/-- A concentric triadic cube is contained in a concentric Euclidean **closed**
ball whose radius is an explicit polynomial in the dimension. -/
theorem openCubeAtScale_subset_euclideanClosedBall_dim (z : Vec d) (m : ℤ) :
    openCubeAtScale z m ⊆ euclideanClosedBall z (((d : ℝ) + 1) * (3 : ℝ) ^ m) := by
  have hpos := zpow_three_pos m
  have hsqrt := sqrt_natCast_le_natCast_add_one_div_two d
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hlt : Real.sqrt (d : ℝ) * ((3 : ℝ) ^ m / 2) < ((d : ℝ) + 1) * (3 : ℝ) ^ m := by
    have hstep : Real.sqrt (d : ℝ) * ((3 : ℝ) ^ m / 2) ≤
        (((d : ℝ) + 1) / 2) * ((3 : ℝ) ^ m / 2) :=
      mul_le_mul_of_nonneg_right hsqrt (by positivity)
    nlinarith
  intro x hx
  have hball : euclideanSqDist x z < (((d : ℝ) + 1) * (3 : ℝ) ^ m) ^ 2 :=
    openCubeAtScale_subset_euclideanBall hlt hx
  exact le_of_lt hball

/-- A continuous function is integrable on every concentric triadic cube. -/
theorem integrableOn_openCubeAtScale_of_continuous {f : Vec d → ℝ} (hf : Continuous f)
    (z : Vec d) (m : ℤ) : IntegrableOn f (openCubeAtScale z m) volume := by
  have hR : (0 : ℝ) ≤ ((d : ℝ) + 1) * (3 : ℝ) ^ m := by
    have h3 : (0 : ℝ) < (3 : ℝ) ^ m := zpow_three_pos m
    have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    nlinarith
  exact (ContinuousOn.integrableOn_compact (isCompact_euclideanClosedBall z hR)
    hf.continuousOn).mono_set (openCubeAtScale_subset_euclideanClosedBall_dim z m)

/-! ### Cauchy--Schwarz against the constant -/

/-- **Cauchy--Schwarz against `1`.**

`(int_V |f|)^2 <= |V| int_V f^2`, proved from the nonnegativity of
`int_V (|f| - t)^2` at the optimal `t = (int_V |f|) / |V|`. -/
theorem sq_setIntegral_abs_le_mul_setIntegral_sq {V : Set (Vec d)}
    (hfin : volume V ≠ ⊤) (hpos : 0 < (volume V).toReal) {f : Vec d → ℝ}
    (hf : IntegrableOn f V volume) (hf2 : IntegrableOn (fun x => f x ^ 2) V volume) :
    (∫ x in V, |f x| ∂volume) ^ 2 ≤
      (volume V).toReal * ∫ x in V, f x ^ 2 ∂volume := by
  have habs : IntegrableOn (fun x => |f x|) V volume := hf.abs
  have hconst : IntegrableOn (fun _ : Vec d => (1 : ℝ)) V volume := integrableOn_const hfin
  set m : ℝ := (volume V).toReal with hmdef
  set I : ℝ := ∫ x in V, |f x| ∂volume with hIdef
  set J : ℝ := ∫ x in V, f x ^ 2 ∂volume with hJdef
  set t : ℝ := I / m with htdef
  have hexp : (fun x => (|f x| - t) ^ 2)
      = fun x => f x ^ 2 + (-(2 * t) * |f x| + t ^ 2) := by
    funext x
    have h : |f x| ^ 2 = f x ^ 2 := sq_abs (f x)
    linear_combination h
  have hint2 : IntegrableOn (fun x => -(2 * t) * |f x| + t ^ 2) V volume :=
    (habs.const_mul (-(2 * t))).add (integrableOn_const hfin)
  have hcalc : ∫ x in V, (|f x| - t) ^ 2 ∂volume = J + (-(2 * t) * I + t ^ 2 * m) := by
    rw [hexp, integral_add hf2 hint2, integral_add (habs.const_mul (-(2 * t)))
      (integrableOn_const hfin), integral_const_mul, setIntegral_const, measureReal_def,
      smul_eq_mul]
    ring
  have hnn : (0 : ℝ) ≤ ∫ x in V, (|f x| - t) ^ 2 ∂volume :=
    integral_nonneg fun x => sq_nonneg _
  rw [hcalc] at hnn
  have ht : t * m = I := by
    rw [htdef]
    field_simp
  have hexpand : m * (J + (-(2 * t) * I + t ^ 2 * m)) = m * J - I ^ 2 := by
    linear_combination (t * m - I) * ht
  have hmul : (0 : ℝ) ≤ m * (J + (-(2 * t) * I + t ^ 2 * m)) := mul_nonneg hpos.le hnn
  rw [hexpand] at hmul
  linarith

/-- **Cauchy--Schwarz in average form.**

The square of the average of `|f - c|` is dominated by the mean-square deviation
of `f` from `c`.  This is the step that converts the output of the interior
gradient estimate, an `L^1` average, into the normalized `L^2` deviation which
`e.nablaw.oscillations` displays. -/
theorem sq_volumeAverage_abs_sub_le_meanSquareDeviationOn {V : Set (Vec d)}
    (hfin : volume V ≠ ⊤) (hpos : 0 < (volume V).toReal) {f : Vec d → ℝ} {c : ℝ}
    (hf : IntegrableOn (fun x => f x - c) V volume)
    (hf2 : IntegrableOn (fun x => (f x - c) ^ 2) V volume) :
    volumeAverage V (fun x => |f x - c|) ^ 2 ≤ Book.Ch01.meanSquareDeviationOn V f c := by
  have hcs := sq_setIntegral_abs_le_mul_setIntegral_sq hfin hpos hf hf2
  have hJnn : (0 : ℝ) ≤ ∫ x in V, (f x - c) ^ 2 ∂volume :=
    integral_nonneg fun x => sq_nonneg _
  show ((volume V).toReal⁻¹ * ∫ x in V, |f x - c| ∂volume) ^ 2 ≤
    (volume V).toReal⁻¹ * ∫ x in V, (f x - c) ^ 2 ∂volume
  rw [mul_pow]
  have hinv : ((volume V).toReal⁻¹) ^ 2 * ((volume V).toReal *
      ∫ x in V, (f x - c) ^ 2 ∂volume)
      = (volume V).toReal⁻¹ * ∫ x in V, (f x - c) ^ 2 ∂volume := by
    field_simp
  calc ((volume V).toReal⁻¹) ^ 2 * (∫ x in V, |f x - c| ∂volume) ^ 2
      ≤ ((volume V).toReal⁻¹) ^ 2 *
          ((volume V).toReal * ∫ x in V, (f x - c) ^ 2 ∂volume) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = (volume V).toReal⁻¹ * ∫ x in V, (f x - c) ^ 2 ∂volume := hinv

/-! ### Mean recentring -/

/-- **The volume average minimizes the mean-square deviation.**

`int_V (f - c)^2 = int_V (f - avg_V f)^2 + |V| (avg_V f - c)^2`, so recentring a
mean-square deviation at the volume average can only decrease it.  This is what
lets a pointwise estimate centred at an arbitrary point of the cube be converted
into a bound for `meanSquareOscillationVecOn`. -/
theorem meanSquareDeviationOn_volumeAverage_le {V : Set (Vec d)}
    (hfin : volume V ≠ ⊤) (hpos : 0 < (volume V).toReal) {f : Vec d → ℝ} (c : ℝ)
    (hf : IntegrableOn f V volume) (hf2 : IntegrableOn (fun x => f x ^ 2) V volume) :
    Book.Ch01.meanSquareDeviationOn V f (volumeAverage V f) ≤
      Book.Ch01.meanSquareDeviationOn V f c := by
  have hne : (volume V).toReal ≠ 0 := ne_of_gt hpos
  have hshift : ∀ b : ℝ, IntegrableOn (fun x => (f x - b) ^ 2) V volume := by
    intro b
    have hexp : (fun x => (f x - b) ^ 2)
        = fun x => f x ^ 2 + (-(2 * b) * f x + b ^ 2) := by
      funext x
      ring
    rw [hexp]
    exact hf2.add ((hf.const_mul (-(2 * b))).add (integrableOn_const hfin))
  have haint : ∫ x in V, f x ∂volume = (volume V).toReal * volumeAverage V f := by
    show ∫ x in V, f x ∂volume
      = (volume V).toReal * ((volume V).toReal⁻¹ * ∫ x in V, f x ∂volume)
    rw [← mul_assoc, mul_inv_cancel₀ hne, one_mul]
  set a : ℝ := volumeAverage V f with hadef
  have hsplit : ∫ x in V, (f x - c) ^ 2 ∂volume
      = (∫ x in V, (f x - a) ^ 2 ∂volume)
        + (2 * (a - c) * ((volume V).toReal * a)
          + (volume V).toReal * (c ^ 2 - a ^ 2)) := by
    have hexp : (fun x => (f x - c) ^ 2)
        = fun x => (f x - a) ^ 2 + (2 * (a - c) * f x + (c ^ 2 - a ^ 2)) := by
      funext x
      ring
    have hint2 : IntegrableOn (fun x => 2 * (a - c) * f x + (c ^ 2 - a ^ 2)) V volume :=
      (hf.const_mul (2 * (a - c))).add (integrableOn_const hfin)
    rw [hexp, integral_add (hshift a) hint2,
      integral_add (hf.const_mul (2 * (a - c))) (integrableOn_const hfin),
      integral_const_mul, setIntegral_const, measureReal_def, smul_eq_mul, haint]
  have hnn : (0 : ℝ) ≤ (volume V).toReal * (a - c) ^ 2 := by positivity
  have hle : ∫ x in V, (f x - a) ^ 2 ∂volume ≤ ∫ x in V, (f x - c) ^ 2 ∂volume := by
    rw [hsplit]
    nlinarith [hnn]
  show (volume V).toReal⁻¹ * ∫ x in V, (f x - a) ^ 2 ∂volume
    ≤ (volume V).toReal⁻¹ * ∫ x in V, (f x - c) ^ 2 ∂volume
  exact mul_le_mul_of_nonneg_left hle (by positivity)

/-- **Mean recentring for the vector oscillation.**

`meanSquareOscillationVecOn V h <= meanSquareDeviationVecOn V h c` for every
centre `c`: the coordinatewise volume average minimizes each summand. -/
theorem meanSquareOscillationVecOn_le_meanSquareDeviationVecOn {V : Set (Vec d)}
    (hfin : volume V ≠ ⊤) (hpos : 0 < (volume V).toReal) {h : Vec d → Vec d} (c : Vec d)
    (hint : ∀ i : Fin d, IntegrableOn (fun x => h x i) V volume)
    (hint2 : ∀ i : Fin d, IntegrableOn (fun x => (h x i) ^ 2) V volume) :
    Book.Ch01.meanSquareOscillationVecOn V h ≤ Book.Ch01.meanSquareDeviationVecOn V h c := by
  show ∑ i : Fin d, Book.Ch01.meanSquareDeviationOn V (fun y => h y i)
      (volumeAverageVec V h i) ≤
    ∑ i : Fin d, Book.Ch01.meanSquareDeviationOn V (fun y => h y i) (c i)
  exact Finset.sum_le_sum fun i _ =>
    meanSquareDeviationOn_volumeAverage_le hfin hpos (c i) (hint i) (hint2 i)

/-! ### Pointwise to mean-square -/

/-- **A uniform pointwise bound bounds the mean-square deviation.** -/
theorem meanSquareDeviationVecOn_le_of_forall_vecNormSq_le {V : Set (Vec d)}
    (hV : MeasurableSet V) (hfin : volume V ≠ ⊤) (hpos : 0 < (volume V).toReal)
    {h : Vec d → Vec d} {c : Vec d} {B : ℝ}
    (hint : ∀ i : Fin d, IntegrableOn (fun x => (h x i - c i) ^ 2) V volume)
    (hbound : ∀ x ∈ V, vecNormSq (h x - c) ≤ B) :
    Book.Ch01.meanSquareDeviationVecOn V h c ≤ B := by
  have hvecint : IntegrableOn (fun x => vecNormSq (h x - c)) V volume := by
    have hfun : (fun x => vecNormSq (h x - c)) = fun x => ∑ i : Fin d, (h x i - c i) ^ 2 := by
      funext x
      simp [vecNormSq, vecDot, sq]
    rw [hfun]
    exact integrable_finsetSum Finset.univ fun i _ => hint i
  have hmono : ∫ x in V, vecNormSq (h x - c) ∂volume ≤ ∫ x in V, B ∂volume := by
    refine integral_mono_ae hvecint (integrableOn_const hfin) ?_
    exact (ae_restrict_iff' hV).2 (Filter.Eventually.of_forall hbound)
  rw [Book.Ch01.meanSquareDeviationVecOn_eq_volumeAverage_vecNormSq_sub hint, volumeAverage]
  rw [setIntegral_const, measureReal_def, smul_eq_mul] at hmono
  calc (volume V).toReal⁻¹ * ∫ x in V, vecNormSq (h x - c) ∂volume
      ≤ (volume V).toReal⁻¹ * ((volume V).toReal * B) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = B := by field_simp

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
