/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Stream.IncrementLpGain

/-!
# CubeEuclideanL8

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The Euclidean normalized `L^p` carrier of `e.nablaw.in.L.eight`

ABK26's display `e.nablaw.in.L.eight` is written with the *Euclidean* pointwise
length of a vector field, under the manuscript's volume-normalized cube
average.  The project ambient carrier is `Vec d = Fin d -> ℝ`, whose
`NormedAddCommGroup` instance is the **sup** norm, so
`Homogenization.cubeLpNorm Q p (f : Vec d -> Vec d)` reads the display in the
sup gauge.  This module records the Euclidean reading explicitly and proves the
two-sided comparison between the two gauges, so that no reading choice is made
silently anywhere downstream.

## Main definitions

* `cubeEuclideanLpNorm Q p f` -- the manuscript's `‖f‖_{L^p(Q)}` under the
  volume-normalized cube average, defined as the scalar `cubeLpNorm` of the
  pointwise Euclidean length `Book.Ch02.vecNorm` of `f`.

## Main results

* `norm_le_vecNorm`, `vecNorm_le_sqrt_dim_mul_norm` -- the pointwise gauge
  comparison `‖v‖_sup ≤ |v|_2 ≤ sqrt d * ‖v‖_sup`.
* `cubeLpNorm_le_cubeEuclideanLpNorm`,
  `cubeEuclideanLpNorm_le_sqrt_dim_mul_cubeLpNorm` -- its `L^p` form.  The two
  gauges therefore differ by at most `sqrt d`, which the display's
  dimension-only constant `C(d)` absorbs.
* `cubeLpNorm_streamIncrementSize_eq_streamIncrementLpNorm` -- the identification
  of the `Provider.Stream` carrier `streamIncrementLpNorm p l n m`, which is
  built from the Euclidean matrix operator norm and `Book.Ch02.average`, with a
  scalar `cubeLpNorm` on the origin cube.
* `memLp_normalizedCubeMeasure_of_continuous` -- every continuous field lies in
  every `L^p` of a normalized cube measure.

## References

* ABK26, `e.nablaw.in.L.eight`.
* ABK26, `e.km.kn.Lp`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The pointwise gauge comparison -/

/-- The ambient sup norm of `Vec d` is below the Euclidean length. -/
theorem norm_le_vecNorm (v : Vec d) : ‖v‖ ≤ Book.Ch02.vecNorm v := by
  refine (pi_norm_le_iff_of_nonneg (Book.Ch02.vecNorm_nonneg v)).2 ?_
  intro i
  have hsq : Book.Ch02.vecNorm v ^ 2 = ∑ j, v j * v j := by
    rw [Book.Ch02.vecNorm_sq_eq_vecNormSq]
    rfl
  have hle : v i ^ 2 ≤ Book.Ch02.vecNorm v ^ 2 := by
    rw [hsq, pow_two]
    refine Finset.single_le_sum (f := fun j => v j * v j) ?_ (Finset.mem_univ i)
    intro j _
    exact mul_self_nonneg _
  have habs : |v i| ≤ Book.Ch02.vecNorm v := by
    have hmono := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq (Book.Ch02.vecNorm_nonneg v)] at hmono
  simpa [Real.norm_eq_abs] using habs

/-- The Euclidean length of `Vec d` is below `sqrt d` times the ambient sup
norm. -/
theorem vecNorm_le_sqrt_dim_mul_norm (v : Vec d) :
    Book.Ch02.vecNorm v ≤ Real.sqrt (d : ℝ) * ‖v‖ := by
  have hnn : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
  have hcoord : ∀ i : Fin d, v i * v i ≤ ‖v‖ * ‖v‖ := by
    intro i
    have hi : |v i| ≤ ‖v‖ := by
      simpa [Real.norm_eq_abs] using norm_le_pi_norm v i
    nlinarith [abs_nonneg (v i), sq_abs (v i), hi]
  have hsum : Book.Ch02.vecNorm v ^ 2 ≤ (Real.sqrt (d : ℝ) * ‖v‖) ^ 2 := by
    have hsq : Book.Ch02.vecNorm v ^ 2 = ∑ j, v j * v j := by
      rw [Book.Ch02.vecNorm_sq_eq_vecNormSq]
      rfl
    have hd : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) := Real.sq_sqrt (by positivity)
    rw [hsq, mul_pow, hd]
    calc (∑ j, v j * v j) ≤ ∑ _j : Fin d, ‖v‖ * ‖v‖ :=
          Finset.sum_le_sum fun j _ => hcoord j
      _ = (d : ℝ) * ‖v‖ ^ 2 := by
          simp [Finset.sum_const, nsmul_eq_mul, pow_two]
  have hrhs : (0 : ℝ) ≤ Real.sqrt (d : ℝ) * ‖v‖ :=
    mul_nonneg (Real.sqrt_nonneg _) hnn
  have hmono := Real.sqrt_le_sqrt hsum
  rwa [Real.sqrt_sq (Book.Ch02.vecNorm_nonneg v), Real.sqrt_sq hrhs] at hmono

/-- The Euclidean length as a square root of the coordinate sum. -/
theorem vecNorm_eq_sqrt_vecNormSq (v : Vec d) :
    Book.Ch02.vecNorm v = Real.sqrt (vecNormSq v) := by
  rw [← Book.Ch02.vecNorm_sq_eq_vecNormSq,
    Real.sqrt_sq (Book.Ch02.vecNorm_nonneg v)]

/-- The Euclidean length is continuous. -/
theorem continuous_vecNorm : Continuous (Book.Ch02.vecNorm : Vec d → ℝ) := by
  have h : (Book.Ch02.vecNorm : Vec d → ℝ) =
      fun v => Real.sqrt (∑ i, v i * v i) := by
    funext v
    rw [vecNorm_eq_sqrt_vecNormSq]
    rfl
  rw [h]
  exact Real.continuous_sqrt.comp
    (continuous_finsetSum _ fun i _ => (continuous_apply i).mul (continuous_apply i))

/-- The Euclidean gauge of an `Lᵖ` vector field is `Lᵖ` for any measure and exponent. -/
theorem memLp_vecNorm_of_memLp {Omega : Type*} [MeasurableSpace Omega] {mu : Measure Omega}
    {p : ℝ≥0∞} {u : Omega → Vec d}
    (hu : MemLp u p mu) :
    MemLp (fun x => Book.Ch02.vecNorm (u x)) p mu := by
  have hsmul : MemLp (fun x => Real.sqrt (d : ℝ) • u x) p mu :=
    hu.const_smul (Real.sqrt (d : ℝ))
  refine hsmul.of_le
    (continuous_vecNorm.comp_aestronglyMeasurable hu.aestronglyMeasurable) ?_
  filter_upwards with x
  have hle := vecNorm_le_sqrt_dim_mul_norm (u x)
  rw [Real.norm_eq_abs, abs_of_nonneg (Book.Ch02.vecNorm_nonneg (u x)), norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg ((d : ℝ)))]
  exact hle

/-- Integrability for normalized cube measure gives Lebesgue integrability on the closed cube. -/
theorem integrableOn_cubeSet_of_integrable_normalized {E : Type*}
    [NormedAddCommGroup E] (Q : TriadicCube d)
    {g : Vec d → E} (hg : Integrable g (normalizedCubeMeasure Q)) :
    IntegrableOn g (cubeSet Q) volume := by
  have hne : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (cubeVolume_pos Q))).ne'
  rw [normalizedCubeMeasure] at hg
  exact (integrable_smul_measure hne ENNReal.ofReal_ne_top).1 hg

/-- An `L⁴` field has integrable squared energy on the closed cube. -/
theorem integrableOn_cubeSet_vecNormSq_sq_of_memLp_four (Q : TriadicCube d)
    {u : Vec d → Vec d} (hu : MemLp u (4 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    IntegrableOn (fun x => vecNormSq (u x) ^ (2 : ℕ)) (cubeSet Q) volume := by
  have hint := (memLp_vecNorm_of_memLp hu).integrable_norm_pow (p := 4) (by norm_num)
  have hfun : (fun x => ‖Book.Ch02.vecNorm (u x)‖ ^ (4 : ℕ)) =
      fun x => vecNormSq (u x) ^ (2 : ℕ) := by
    funext x
    rw [Real.norm_eq_abs, abs_of_nonneg (Book.Ch02.vecNorm_nonneg (u x)),
      show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Book.Ch02.vecNorm_sq_eq_vecNormSq]
  exact integrableOn_cubeSet_of_integrable_normalized Q (hfun ▸ hint)

/-! ## Elementary `cubeLpNorm` A -/

/-- Pointwise domination transfers to `cubeLpNorm`, provided the dominating
field has finite norm. -/
theorem cubeLpNorm_mono_of_memLp {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] (Q : TriadicCube d) (p : ℝ≥0∞) {f : Vec d → E}
    {g : Vec d → F} (hfg : ∀ x, ‖f x‖ ≤ ‖g x‖)
    (hg : MemLp g p (normalizedCubeMeasure Q)) :
    cubeLpNorm Q p f ≤ cubeLpNorm Q p g := by
  by_cases hf : AEStronglyMeasurable f (normalizedCubeMeasure Q)
  · exact ENNReal.toReal_mono hg.eLpNorm_lt_top.ne (eLpNorm_mono hf hfg)
  · rw [cubeLpNorm, eLpNorm_of_not_aestronglyMeasurable hf, ENNReal.toReal_top]
    exact ENNReal.toReal_nonneg

/-- `cubeLpNorm` of a nonnegative constant multiple of a field. -/
theorem cubeLpNorm_const_mul_of_nonneg {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (Q : TriadicCube d) (p : ℝ≥0∞) {c : ℝ} (hc : 0 ≤ c)
    (f : Vec d → E) :
    cubeLpNorm Q p (fun x => c • f x) = c * cubeLpNorm Q p f := by
  unfold cubeLpNorm
  have hfun : (fun x => c • f x) = c • f := rfl
  rw [hfun, eLpNorm_const_smul, ENNReal.toReal_mul]
  congr 1
  simp [Real.enorm_eq_ofReal hc, ENNReal.toReal_ofReal hc]

/-! ## The Euclidean normalized cube norm -/

/-- The manuscript's volume-normalized `L^p` norm of a vector field, read with
the **Euclidean** pointwise length, as in `e.nablaw.in.L.eight`. -/
def cubeEuclideanLpNorm (Q : TriadicCube d) (p : ℝ≥0∞) (f : Vec d → Vec d) : ℝ :=
  cubeLpNorm Q p (fun x => Book.Ch02.vecNorm (f x))

theorem cubeEuclideanLpNorm_nonneg (Q : TriadicCube d) (p : ℝ≥0∞)
    (f : Vec d → Vec d) : 0 ≤ cubeEuclideanLpNorm Q p f :=
  cubeLpNorm_nonneg _ _ _

/-- The sup-gauge cube norm is below the Euclidean one. -/
theorem cubeLpNorm_le_cubeEuclideanLpNorm (Q : TriadicCube d) (p : ℝ≥0∞)
    (f : Vec d → Vec d)
    (hf : MemLp (fun x => Book.Ch02.vecNorm (f x)) p (normalizedCubeMeasure Q)) :
    cubeLpNorm Q p f ≤ cubeEuclideanLpNorm Q p f := by
  refine cubeLpNorm_mono_of_memLp Q p (fun x => ?_) hf
  have hx := norm_le_vecNorm (f x)
  simpa [Real.norm_eq_abs,
    abs_of_nonneg (Book.Ch02.vecNorm_nonneg (f x))] using hx

/-- The Euclidean cube norm is below `sqrt d` times the sup-gauge one. -/
theorem cubeEuclideanLpNorm_le_sqrt_dim_mul_cubeLpNorm (Q : TriadicCube d)
    (p : ℝ≥0∞) (f : Vec d → Vec d) (hf : MemLp f p (normalizedCubeMeasure Q)) :
    cubeEuclideanLpNorm Q p f ≤ Real.sqrt (d : ℝ) * cubeLpNorm Q p f := by
  have hsmul : MemLp (fun x => Real.sqrt (d : ℝ) • f x) p
      (normalizedCubeMeasure Q) := by
    have h := hf.const_smul (Real.sqrt (d : ℝ))
    exact h
  have hmono : cubeLpNorm Q p (fun x => Book.Ch02.vecNorm (f x)) ≤
      cubeLpNorm Q p (fun x => Real.sqrt (d : ℝ) • f x) := by
    refine cubeLpNorm_mono_of_memLp Q p (fun x => ?_) hsmul
    have hle := vecNorm_le_sqrt_dim_mul_norm (f x)
    simpa [Real.norm_eq_abs, abs_of_nonneg (Book.Ch02.vecNorm_nonneg (f x)),
      norm_smul, abs_of_nonneg (Real.sqrt_nonneg ((d : ℝ)))] using hle
  have heq := cubeLpNorm_const_mul_of_nonneg Q p (Real.sqrt_nonneg ((d : ℝ))) f
  rw [cubeEuclideanLpNorm]
  exact hmono.trans_eq heq

/-! ## `MemLp` for continuous fields on a normalized cube -/

/-- Every continuous field lies in every `L^p` of a normalized cube measure:
the measure is finite and supported in a bounded set. -/
theorem memLp_normalizedCubeMeasure_of_continuous {E : Type*}
    [NormedAddCommGroup E] (Q : TriadicCube d) (p : ℝ≥0∞) {f : Vec d → E}
    (hf : Continuous f) : MemLp f p (normalizedCubeMeasure Q) := by
  have hcompact : IsCompact (Metric.closedBall (cubeCenter Q) (cubeRadius Q)) :=
    isCompact_closedBall _ _
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn hf.continuousOn
  have hsub : cubeSet Q ⊆ Metric.closedBall (cubeCenter Q) (cubeRadius Q) :=
    cubeSet_subset_closedBall Q
  have hbase : ∀ᵐ x ∂ cubeMeasure Q, ‖f x‖ ≤ C := by
    rw [cubeMeasure]
    refine (ae_restrict_iff' (measurableSet_cubeSet Q)).2 ?_
    exact Filter.Eventually.of_forall fun x hx => hC x (hsub hx)
  have hae : ∀ᵐ x ∂ normalizedCubeMeasure Q, ‖f x‖ ≤ C := by
    rw [normalizedCubeMeasure]
    exact Measure.ae_smul_measure hbase _
  exact (memLp_top_of_bound hf.aestronglyMeasurable C hae).mono_exponent le_top

/-! ## The stream-increment carrier as a `cubeLpNorm` -/

/-- The scalar field whose `cubeLpNorm` is the manuscript's
`‖k_m - k_n‖_{L^p(cu_l)}`: the pointwise Euclidean operator norm of the stream
increment. -/
def streamIncrementSize (n m : ℤ) (omega : Cutoff.ShellSeq d) (x : Vec d) : ℝ :=
  Book.Ch02.matrixOperatorNorm (Cutoff.finiteShellIncrement omega n m x)

theorem streamIncrementSize_nonneg (n m : ℤ) (omega : Cutoff.ShellSeq d)
    (x : Vec d) : 0 ≤ streamIncrementSize n m omega x :=
  Book.Ch02.matrixOperatorNorm_nonneg _

theorem continuous_streamIncrementSize (n m : ℤ) (omega : Cutoff.ShellSeq d) :
    Continuous (streamIncrementSize (d := d) n m omega) := by
  have h := Stream.continuous_streamIncrementLpDensity (d := d)
    (p := 1) (by norm_num) n m omega
  have hfun : Stream.streamIncrementLpDensity (d := d) 1 n m omega =
      streamIncrementSize n m omega := by
    funext x
    simp [Stream.streamIncrementLpDensity, streamIncrementSize,
      Real.rpow_one]
  rwa [hfun] at h

/-- **The identification of the two `L^p` carriers.**  The `Provider.Stream`
norm `streamIncrementLpNorm p l n m`, built from `Book.Ch02.average` over the
open origin cube and the Euclidean matrix operator norm, is the `cubeLpNorm` of
the scalar field `streamIncrementSize` on the same cube. -/
theorem cubeLpNorm_streamIncrementSize_eq_streamIncrementLpNorm {p : ℝ}
    (hp : 0 < p) (l n m : ℤ) (omega : Cutoff.ShellSeq d) :
    cubeLpNorm (originCube d l) (ENNReal.ofReal p)
        (streamIncrementSize n m omega) =
      Stream.streamIncrementLpNorm p l n m omega := by
  have hp0 : (ENNReal.ofReal p) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, not_le, hp]
  have hpTop : (ENNReal.ofReal p) ≠ ∞ := ENNReal.ofReal_ne_top
  have hpReal : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp.le
  have hmem : MemLp (streamIncrementSize (d := d) n m omega) (ENNReal.ofReal p)
      (normalizedCubeMeasure (originCube d l)) :=
    memLp_normalizedCubeMeasure_of_continuous _ _
      (continuous_streamIncrementSize n m omega)
  have hpow := cubeLpNorm_rpow_eq_cubeAverage_norm_rpow (originCube d l)
    (ENNReal.ofReal p) (streamIncrementSize (d := d) n m omega) hp0 hpTop hmem
  rw [hpReal] at hpow
  have hdensity : (fun x => ‖streamIncrementSize (d := d) n m omega x‖ ^ p) =
      Stream.streamIncrementLpDensity p n m omega := by
    funext x
    rw [Stream.streamIncrementLpDensity]
    congr 1
    exact abs_of_nonneg (streamIncrementSize_nonneg n m omega x)
  rw [hdensity, ← Stream.streamIncrementLpMass_eq_cubeAverage hp l n m omega]
    at hpow
  have hnn : (0 : ℝ) ≤ cubeLpNorm (originCube d l) (ENNReal.ofReal p)
      (streamIncrementSize (d := d) n m omega) := cubeLpNorm_nonneg _ _ _
  rw [Stream.streamIncrementLpNorm, ← hpow, ← Real.rpow_mul hnn,
    mul_inv_cancel₀ hp.ne', Real.rpow_one]

end

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
