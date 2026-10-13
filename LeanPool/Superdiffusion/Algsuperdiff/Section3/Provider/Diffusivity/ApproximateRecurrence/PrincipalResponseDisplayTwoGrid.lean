/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.CubeJensenVec
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.CubeEuclideanL8
public import LeanPool.HighContrastHomogenization.Support.Besov.Localization

/-!
# PrincipalResponseDisplayTwoGrid

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
Binder descriptions below are an informal inventory only, NOT a source
certification; certification vocabulary is reserved for frozen source-facing
declarations.

# Provider: the grid re-assembly behind display 2 of leg (iv)

Display 2 of leg (iv) of `l.approximate.recurrence.formula` is

```
  ( avsum_{z in 3^n Zd cap cu_K} E[ | bfAhom_{m-1}^{1/2} P_z |^4 ] )^{1/4} <= C .
```

Sub-step (ii) (`ellipticityBudget_eq`, module
`PrincipalResponseLegsBudgetEllipticity`) collapses the integrand into the raw
averaged slope pair, so what has to be estimated on the grid is

```
  avsum_R  | c + (u)_R |^4 ,
```

with `R` running over the triadic descendants of `cu_K` at the localization
depth, `c` one of the two unit directions `e`, `e'`, and `u` one of the two
fields `grad w_D` and `grad w_N + shom^{-1} h e'`.  This module reduces that
grid average to the single *global* volume-normalized `L^8` norm of `u` on
`cu_K`, which is the quantity `e.nablaw.in.L.eight` controls:

```
  avsum_R | c + (u)_R |^4  <=  8 |c|^4 + 8 ( ‖u‖_{L^8(cu_K)} )^4 .
```

## The three inputs

* the **vector Jensen inequality at the fourth power** on each subcube,
  `sq_vecNormSq_cubeAverageVec_le_cubeAverage_sq_of_memLp` (portable module
  `CubeJensenVec`), which replaces `|(u)_R|^4` by `avg_R |u|^4`;
* the **grid re-assembly**
  `cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn` of
  CoarseGraining, which turns the average over subcubes of the subcube averages
  back into the single average over `cu_K`;
* the **`L^4 <= L^8` bridge**
  `cubeAverage_vecNormSq_sq_le_cubeLpNorm_eight_vecNorm_pow_four_of_memLp`
  (portable module `CubeJensenVec`), which is where the volume-normalized `L^8`
  norm of the display appears.

Only one hypothesis is carried: that `u` lies in `L^8` of the normalized cube
measure of `cu_K`.  Everything the subcubes need is deduced from it by
`memLp_normalizedCubeMeasure_of_mem_descendantsAtDepth`, which is the statement
that a descendant carries at most `|cu_K| / |R|` times the parent's normalized
mass.

## The Minkowski step

The second of the two fields is a sum, `grad w_N + shom^{-1} h e'`, whose two
summands are controlled separately (the gradient by the Calderon-Zygmund step,
the forcing by `e.km.kn.Lp`).  `cubeEuclideanLpNorm_add_le` is the triangle
inequality for the manuscript's Euclidean volume-normalized `L^p` norm, proved
here from the pointwise Euclidean triangle inequality `vecNorm_add_le`.

## Main results

* `vecNorm_add_le`, `cubeEuclideanLpNorm_add_le`
* `memLp_normalizedCubeMeasure_of_mem_descendantsAtDepth`
* `descendantsAverage_sq_vecNormSq_add_cubeAverageVec_le`
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector
open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The Euclidean triangle inequality on `Vec d` -/

/-- The Euclidean length on `Vec d` obeys the triangle inequality. -/
theorem vecNorm_add_le (a b : Vec d) :
    Book.Ch02.vecNorm (a + b) ≤ Book.Ch02.vecNorm a + Book.Ch02.vecNorm b := by
  have hna : (0 : ℝ) ≤ Book.Ch02.vecNorm a := Book.Ch02.vecNorm_nonneg a
  have hnb : (0 : ℝ) ≤ Book.Ch02.vecNorm b := Book.Ch02.vecNorm_nonneg b
  have hA : Book.Ch02.vecNorm a ^ (2 : ℕ) = vecNormSq a :=
    Book.Ch02.vecNorm_sq_eq_vecNormSq a
  have hB : Book.Ch02.vecNorm b ^ (2 : ℕ) = vecNormSq b :=
    Book.Ch02.vecNorm_sq_eq_vecNormSq b
  have hAB : Book.Ch02.vecNorm (a + b) ^ (2 : ℕ) = vecNormSq (a + b) :=
    Book.Ch02.vecNorm_sq_eq_vecNormSq (a + b)
  have hexpand : vecNormSq (a + b) = vecNormSq a + 2 * vecDot a b + vecNormSq b := by
    simp only [vecNormSq, vecDot, Pi.add_apply, Finset.mul_sum, two_mul,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hcs : vecDot a b ≤ Book.Ch02.vecNorm a * Book.Ch02.vecNorm b := by
    have hsq := sq_vecDot_le_vecNormSq_mul_vecNormSq a b
    have hprod : vecDot a b ^ (2 : ℕ) ≤
        (Book.Ch02.vecNorm a * Book.Ch02.vecNorm b) ^ (2 : ℕ) := by
      rw [mul_pow, hA, hB]
      exact hsq
    exact le_of_sq_le_sq hprod (mul_nonneg hna hnb)
  have hexp2 : (Book.Ch02.vecNorm a + Book.Ch02.vecNorm b) ^ (2 : ℕ) =
      vecNormSq a + 2 * (Book.Ch02.vecNorm a * Book.Ch02.vecNorm b) + vecNormSq b := by
    rw [add_sq, hA, hB]
    ring
  have hsum : Book.Ch02.vecNorm (a + b) ^ (2 : ℕ) ≤
      (Book.Ch02.vecNorm a + Book.Ch02.vecNorm b) ^ (2 : ℕ) := by
    rw [hAB, hexpand, hexp2]
    linarith [hcs]
  exact le_of_sq_le_sq hsum (by linarith)

/-! ## Minkowski for the Euclidean volume-normalized norm -/

/-- **The triangle inequality for `cubeEuclideanLpNorm`.**  The manuscript's
Euclidean reading of the volume-normalized `L^p` norm is a norm: for `p >= 1`
and two fields whose Euclidean lengths lie in `L^p` of the normalized cube
measure, the norm of the sum is at most the sum of the norms. -/
theorem cubeEuclideanLpNorm_add_le (Q : TriadicCube d) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (f g : Vec d → Vec d)
    (hf : MemLp (fun x => Book.Ch02.vecNorm (f x)) p (normalizedCubeMeasure Q))
    (hg : MemLp (fun x => Book.Ch02.vecNorm (g x)) p (normalizedCubeMeasure Q)) :
    cubeEuclideanLpNorm Q p (fun x => f x + g x) ≤
      cubeEuclideanLpNorm Q p f + cubeEuclideanLpNorm Q p g := by
  by_cases hm : AEStronglyMeasurable (fun x => Book.Ch02.vecNorm (f x + g x))
      (normalizedCubeMeasure Q)
  swap
  · have h0 : cubeEuclideanLpNorm Q p (fun x => f x + g x) = 0 := by
      show (eLpNorm (fun x => Book.Ch02.vecNorm (f x + g x)) p
        (normalizedCubeMeasure Q)).toReal = 0
      rw [eLpNorm_of_not_aestronglyMeasurable hm, ENNReal.toReal_top]
    rw [h0]
    exact add_nonneg (cubeEuclideanLpNorm_nonneg Q p f) (cubeEuclideanLpNorm_nonneg Q p g)
  have hmono : eLpNorm (fun x => Book.Ch02.vecNorm (f x + g x)) p
        (normalizedCubeMeasure Q) ≤
      eLpNorm (fun x => Book.Ch02.vecNorm (f x) + Book.Ch02.vecNorm (g x)) p
        (normalizedCubeMeasure Q) := by
    refine eLpNorm_mono hm fun x => ?_
    have hle := vecNorm_add_le (f x) (g x)
    have hnn : (0 : ℝ) ≤ Book.Ch02.vecNorm (f x) + Book.Ch02.vecNorm (g x) := by
      have := Book.Ch02.vecNorm_nonneg (f x)
      have := Book.Ch02.vecNorm_nonneg (g x)
      linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (Book.Ch02.vecNorm_nonneg (f x + g x))]
    exact hle.trans (le_abs_self _)
  have htri : eLpNorm (fun x => Book.Ch02.vecNorm (f x) + Book.Ch02.vecNorm (g x)) p
        (normalizedCubeMeasure Q) ≤
      eLpNorm (fun x => Book.Ch02.vecNorm (f x)) p (normalizedCubeMeasure Q) +
        eLpNorm (fun x => Book.Ch02.vecNorm (g x)) p (normalizedCubeMeasure Q) :=
    eLpNorm_add_le hp
  have hsum : eLpNorm (fun x => Book.Ch02.vecNorm (f x + g x)) p
        (normalizedCubeMeasure Q) ≤
      eLpNorm (fun x => Book.Ch02.vecNorm (f x)) p (normalizedCubeMeasure Q) +
        eLpNorm (fun x => Book.Ch02.vecNorm (g x)) p (normalizedCubeMeasure Q) :=
    hmono.trans htri
  have hfin : eLpNorm (fun x => Book.Ch02.vecNorm (f x)) p (normalizedCubeMeasure Q) +
      eLpNorm (fun x => Book.Ch02.vecNorm (g x)) p (normalizedCubeMeasure Q) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hf.eLpNorm_ne_top, hg.eLpNorm_ne_top⟩
  have htoReal := ENNReal.toReal_mono hfin hsum
  rw [ENNReal.toReal_add hf.eLpNorm_ne_top hg.eLpNorm_ne_top] at htoReal
  exact htoReal

/-! ## Restriction of `MemLp` to a descendant cube -/

/-- **A descendant inherits the parent's `L^p` membership.**  The normalized
measure of a subcube is dominated by `|Q| / |R|` times that of the parent, so
`L^p` of the parent's normalized measure sits inside `L^p` of every
descendant's. -/
theorem memLp_normalizedCubeMeasure_of_mem_descendantsAtDepth {E : Type*}
    [NormedAddCommGroup E] {Q R : TriadicCube d} {j : ℕ} {p : ℝ≥0∞}
    {f : Vec d → E} (hR : R ∈ descendantsAtDepth Q j)
    (hf : MemLp f p (normalizedCubeMeasure Q)) :
    MemLp f p (normalizedCubeMeasure R) := by
  have hsub : cubeSet R ⊆ cubeSet Q := cubeSet_subset_of_mem_descendantsAtDepth hR
  have hQpos : (0 : ℝ) < cubeVolume Q := cubeVolume_pos Q
  have hRpos : (0 : ℝ) < cubeVolume R := cubeVolume_pos R
  set c : ℝ≥0∞ := ENNReal.ofReal (cubeVolume Q / cubeVolume R) with hcdef
  have hscale : c * ENNReal.ofReal ((cubeVolume Q)⁻¹) =
      ENNReal.ofReal ((cubeVolume R)⁻¹) := by
    rw [hcdef, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  have hsmul : MemLp f p (c • normalizedCubeMeasure Q) :=
    hf.smul_measure (by simp [hcdef])
  refine hsmul.mono_measure ?_
  refine Measure.le_iff.2 fun s hs => ?_
  have hrestrict : (volume.restrict (cubeSet R)) s ≤ (volume.restrict (cubeSet Q)) s :=
    Measure.restrict_mono hsub le_rfl s
  calc normalizedCubeMeasure R s
      = ENNReal.ofReal ((cubeVolume R)⁻¹) * (volume.restrict (cubeSet R)) s := by
        rw [normalizedCubeMeasure, cubeMeasure, Measure.smul_apply, smul_eq_mul]
    _ ≤ ENNReal.ofReal ((cubeVolume R)⁻¹) * (volume.restrict (cubeSet Q)) s := by
        gcongr
    _ = (c • normalizedCubeMeasure Q) s := by
        rw [Measure.smul_apply, smul_eq_mul, normalizedCubeMeasure, cubeMeasure,
          Measure.smul_apply, smul_eq_mul, ← mul_assoc, hscale]

/-! ## `MemLp` of the Euclidean length -/

/-- The Euclidean length of an `L^p` field is `L^p`: it never exceeds
`sqrt d` times the ambient sup norm. -/
theorem memLp_vecNorm_of_memLp (Q : TriadicCube d) {p : ℝ≥0∞} {u : Vec d → Vec d}
    (hu : MemLp u p (normalizedCubeMeasure Q)) :
    MemLp (fun x => Book.Ch02.vecNorm (u x)) p (normalizedCubeMeasure Q) := by
  have hsmul : MemLp (fun x => Real.sqrt (d : ℝ) • u x) p (normalizedCubeMeasure Q) :=
    hu.const_smul (Real.sqrt (d : ℝ))
  refine hsmul.of_le
    (continuous_vecNorm.comp_aestronglyMeasurable hu.aestronglyMeasurable) ?_
  filter_upwards with x
  have hle := vecNorm_le_sqrt_dim_mul_norm (u x)
  rw [Real.norm_eq_abs, abs_of_nonneg (Book.Ch02.vecNorm_nonneg (u x)), norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg ((d : ℝ)))]
  exact hle

/-! ## Integrability of the fourth power on the cube -/

private theorem integrableOn_vecNormSq_sq_of_memLp (Q : TriadicCube d)
    {u : Vec d → Vec d} (hu : MemLp u (8 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    IntegrableOn (fun x => vecNormSq (u x) ^ (2 : ℕ)) (cubeSet Q) volume := by
  have huE : MemLp (fun x => Book.Ch02.vecNorm (u x)) (8 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := memLp_vecNorm_of_memLp Q hu
  have huE4 : MemLp (fun x => Book.Ch02.vecNorm (u x)) (4 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := huE.mono_exponent (by norm_num)
  have hsq : MemLp (fun x => Book.Ch02.vecNorm (u x) ^ (2 : ℕ)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := by
    have h := (memLp_norm_rpow_iff (μ := normalizedCubeMeasure Q)
        (f := fun x => Book.Ch02.vecNorm (u x)) (p := (4 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
        huE4.aestronglyMeasurable (by norm_num) (by norm_num)).2 huE4
    have hdiv : (4 : ℝ≥0∞) / 2 = 2 := by
      rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num]
      rw [mul_div_assoc, ENNReal.div_self (by norm_num) (by norm_num), mul_one]
    rw [hdiv] at h
    have hfun : (fun x => ‖Book.Ch02.vecNorm (u x)‖ ^ ((2 : ℝ≥0∞).toReal)) =
        fun x => Book.Ch02.vecNorm (u x) ^ (2 : ℕ) := by
      funext x
      rw [show ((2 : ℝ≥0∞).toReal) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        Real.norm_eq_abs, ← abs_pow,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ Book.Ch02.vecNorm (u x) ^ (2 : ℕ))]
    rwa [hfun] at h
  have hint : Integrable (fun x => vecNormSq (u x) ^ (2 : ℕ))
      (normalizedCubeMeasure Q) := by
    have h := hsq.integrable_sq
    have hfun : (fun x => (Book.Ch02.vecNorm (u x) ^ (2 : ℕ)) ^ (2 : ℕ)) =
        fun x => vecNormSq (u x) ^ (2 : ℕ) := by
      funext x
      rw [Book.Ch02.vecNorm_sq_eq_vecNormSq]
    rwa [hfun] at h
  have hne : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (cubeVolume_pos Q))).ne'
  rw [normalizedCubeMeasure] at hint
  exact (integrable_smul_measure hne ENNReal.ofReal_ne_top).1 hint

/-! ## The grid re-assembly -/

/-- **The grid form of the fourth power of a shifted cube average.**

For a field `u` in `L^8` of the normalized measure of `Q`, the average over the
triadic descendants of `Q` at any depth `j` of the fourth power of
`|c + (u)_R|` is bounded by the constant term and the *global* volume-normalized
`L^8` norm of `u` on `Q`:

```
  avsum_R | c + (u)_R |^4  <=  8 |c|^4 + 8 ( ‖u‖_{L^8(Q)} )^4 .
```

The three steps are the vector Jensen inequality on each subcube, the
CoarseGraining grid re-assembly of subcube averages, and the volume-normalized
`L^4 <= L^8` comparison. -/
theorem descendantsAverage_sq_vecNormSq_add_cubeAverageVec_le (Q : TriadicCube d)
    (j : ℕ) (c : Vec d) (u : Vec d → Vec d)
    (hu : MemLp u (8 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    descendantsAverage Q j
        (fun R => vecNormSq (c + cubeAverageVec R u) ^ (2 : ℕ)) ≤
      8 * vecNormSq c ^ (2 : ℕ) +
        8 * cubeEuclideanLpNorm Q 8 u ^ (4 : ℕ) := by
  classical
  have hint := integrableOn_vecNormSq_sq_of_memLp Q hu
  have hpoint : ∀ R ∈ descendantsAtDepth Q j,
      vecNormSq (c + cubeAverageVec R u) ^ (2 : ℕ) ≤
        8 * vecNormSq c ^ (2 : ℕ) +
          8 * cubeAverage R (fun x => vecNormSq (u x) ^ (2 : ℕ)) := by
    intro R hR
    have hR4 : MemLp u (4 : ℝ≥0∞) (normalizedCubeMeasure R) :=
      (memLp_normalizedCubeMeasure_of_mem_descendantsAtDepth hR hu).mono_exponent
        (by norm_num)
    have hjensen := sq_vecNormSq_cubeAverageVec_le_cubeAverage_sq_of_memLp R u hR4
    have hsplit := vecNormSq_add_le c (cubeAverageVec R u)
    have hc0 : (0 : ℝ) ≤ vecNormSq c := vecNormSq_nonneg c
    have hv0 : (0 : ℝ) ≤ vecNormSq (cubeAverageVec R u) :=
      vecNormSq_nonneg (cubeAverageVec R u)
    have hsq : vecNormSq (c + cubeAverageVec R u) ^ (2 : ℕ) ≤
        8 * vecNormSq c ^ (2 : ℕ) +
          8 * vecNormSq (cubeAverageVec R u) ^ (2 : ℕ) := by
      nlinarith [vecNormSq_nonneg (c + cubeAverageVec R u), hsplit, hc0, hv0,
        sq_nonneg (vecNormSq c - vecNormSq (cubeAverageVec R u))]
    linarith
  have hmono := descendantsAverage_le_descendantsAverage Q j
    (F := fun R => vecNormSq (c + cubeAverageVec R u) ^ (2 : ℕ))
    (G := fun R => 8 * vecNormSq c ^ (2 : ℕ) +
      8 * cubeAverage R (fun x => vecNormSq (u x) ^ (2 : ℕ))) hpoint
  have hreassemble : descendantsAverage Q j
      (fun R => 8 * vecNormSq c ^ (2 : ℕ) +
        8 * cubeAverage R (fun x => vecNormSq (u x) ^ (2 : ℕ))) =
      8 * vecNormSq c ^ (2 : ℕ) +
        8 * cubeAverage Q (fun x => vecNormSq (u x) ^ (2 : ℕ)) := by
    rw [descendantsAverage_add Q j (fun _ => 8 * vecNormSq c ^ (2 : ℕ))
        (fun R => 8 * cubeAverage R (fun x => vecNormSq (u x) ^ (2 : ℕ))),
      descendantsAverage_const,
      descendantsAverage_mul_left Q j 8
        (fun R => cubeAverage R (fun x => vecNormSq (u x) ^ (2 : ℕ))),
      ← cubeAverage_eq_descendantsAverage_cubeAverage_of_integrableOn Q j
        (fun x => vecNormSq (u x) ^ (2 : ℕ)) hint]
  have hbridge :
      cubeAverage Q (fun x => vecNormSq (u x) ^ (2 : ℕ)) ≤
        cubeEuclideanLpNorm Q 8 u ^ (4 : ℕ) :=
    cubeAverage_vecNormSq_sq_le_cubeLpNorm_eight_vecNorm_pow_four_of_memLp Q u
      (memLp_vecNorm_of_memLp Q hu)
  rw [hreassemble] at hmono
  linarith

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
