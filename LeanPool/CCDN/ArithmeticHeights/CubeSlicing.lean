/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ArithmeticHeights.ProductOfBalls
public import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Vaaler's cube-slicing theorem

**Bombieri–Gubler, Theorem C.3.8 (Vaaler 1979).** Let `Q` be a product of euclidean balls each of
volume one, one factor per block of a partition of the coordinates of `ℝᴺ`. Then every central
slice of `Q` by a linear subspace `V` has volume at least one, the volume being computed on `V`
with its own inner-product structure. Two corollaries: the cube `[-1, 1]ᴺ` has central slices of
volume at least `2 ^ dim V`, and the unit polydisc of `ℂⁿ` has central slices of real volume at
least `2 ^ (dim V / 2)`.

## Main definitions

* `Submodule.prodOrthogonalEquiv V`: the orthogonal decomposition `E ≃ₗ[ℝ] V × Vᗮ`, as a
  measure-preserving linear equivalence.
* `unitBallVolume n`: the volume of the unit ball of `EuclideanSpace ℝ (Fin n)`.

## Main results

* `one_le_volume_subtype_mem`: **Bombieri–Gubler, Theorem C.3.8** in the form the slice bound gives
  it, for an arbitrary measurable convex symmetric `Q` satisfying `HasSliceBound`.
* `one_le_volume_inter_prodBall`: the product-of-balls theorem in the roadmap's form.
* `two_pow_finrank_le_volume_inter_cube`: **Vaaler's cube-slicing theorem**.
* `two_pow_le_volume_inter_polydisc`: the inscribed-cube bound at a complex place.

## Implementation notes

⚠ **The `ε`-thickening needs no dominated convergence, because a slice of a symmetric convex body
is largest at the centre.** Bombieri–Gubler pass to the limit `ε → 0` in
`vol (Q ∩ L_ε) / vol (B_ε)` by computing the limit of the integrand and dominating it. The same
limit is avoided here: the function `z ↦ vol_V {y | y + z ∈ Q}` on `Vᗮ` is log-concave, by Lemma
C.3.4, and even, because `Q` is symmetric, so it is *bounded by its value at zero* — which is the
slice volume being estimated. That turns the right-hand side into
`vol_V (Q ∩ V) * vol (B_ε)` with no limit at all, and the left-hand side is bounded below by
`exp (-π ε ^ 2) * vol (B_ε)` because the Gauss density is. Dividing and letting `ε → 0` is then a
one-line limit of `exp (-π ε ^ 2)`. Brunn's principle — that the central slice is the largest one —
is thus the only extra ingredient, and log-concavity of marginals already supplies it.

⚠ **The complex structure is not needed for the polydisc bound.** The roadmap states
`two_pow_le_volume_inter_polydisc` for a subspace closed under the complex structure `J`, since
that is where the bound is applied; but the proof inscribes the cube of half-side `2 ^ (-1/2)` in
the polydisc and applies the cube case, which gives `√2 ^ dim V`, and `2 ^ (dim V / 2) ≤ √2 ^ dim V`
holds whether or not `dim V` is even. So the hypothesis is dropped here.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Theorem C.3.8; J. D. Vaaler, *A geometric inequality with applications to linear forms*, Pacific
Journal of Mathematics **83** (1979), 543–553.

This is Layer 4.5 of the `ArithmeticHeights` roadmap.
-/

public section

open MeasureTheory Measure Set ENNReal Pointwise
open scoped Real

section OrthogonalDecomposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- The orthogonal decomposition `E ≃ₗ[ℝ] V × Vᗮ`, forgetting the `L²` structure of the target. -/
noncomputable def Submodule.prodOrthogonalEquiv (V : Submodule ℝ E) :
    E ≃ₗ[ℝ] (V × (Vᗮ : Submodule ℝ E)) :=
  V.orthogonalDecomposition.toLinearEquiv ≪≫ₗ WithLp.linearEquiv 2 ℝ (V × (Vᗮ : Submodule ℝ E))

theorem Submodule.prodOrthogonalEquiv_symm_apply (V : Submodule ℝ E)
    (q : V × (Vᗮ : Submodule ℝ E)) : V.prodOrthogonalEquiv.symm q = (q.1 : E) + (q.2 : E) := by
  simp [Submodule.prodOrthogonalEquiv]

theorem Submodule.norm_prodOrthogonalEquiv_symm (V : Submodule ℝ E)
    (q : V × (Vᗮ : Submodule ℝ E)) :
    ‖V.prodOrthogonalEquiv.symm q‖ ^ 2 = ‖q.1‖ ^ 2 + ‖q.2‖ ^ 2 := by
  have h : V.prodOrthogonalEquiv.symm q = V.orthogonalDecomposition.symm (WithLp.toLp 2 q) := rfl
  rw [h, V.orthogonalDecomposition.symm.norm_map, WithLp.prod_norm_sq_eq_of_L2]
  simp

variable [MeasurableSpace E] [BorelSpace E]

theorem Submodule.measurePreserving_prodOrthogonalEquiv (V : Submodule ℝ E) :
    MeasurePreserving V.prodOrthogonalEquiv (volume : Measure E)
      ((volume : Measure V).prod (volume : Measure (Vᗮ : Submodule ℝ E))) := by
  have h1 : MeasurePreserving V.orthogonalDecomposition (volume : Measure E) volume :=
    LinearIsometryEquiv.measurePreserving _
  have h2 := WithLp.volume_preserving_ofLp (V : Type _) ((Vᗮ : Submodule ℝ E) : Type _)
  rw [← Measure.volume_eq_prod]
  exact h2.comp h1

end OrthogonalDecomposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **A log-concave even function attains its maximum at the origin** (Brunn's principle, for the
marginals of a symmetric convex body). -/
theorem LogConcave.le_apply_zero {F : Type*} [AddCommGroup F] [Module ℝ F] {f : F → ℝ≥0∞}
    (hf : LogConcave f) (hfe : ∀ x, f (-x) = f x) (x : F) : f x ≤ f 0 := by
  have h := hf (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num) x (-x)
  rw [hfe x, show (1/2 : ℝ) • x + (1/2 : ℝ) • (-x) = 0 by module] at h
  calc f x = f x ^ ((1:ℝ)/2) * f x ^ ((1:ℝ)/2) := by
        rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
        norm_num
    _ ≤ f 0 := h

/-- **Bombieri–Gubler, Theorem C.3.8.** If the Gauss measure of every measurable convex symmetric
set is at most its volume inside `Q`, then every central slice of `Q` by a linear subspace has
volume at least one, computed on the subspace. -/
theorem one_le_volume_subtype_mem
    {Q : Set E} (hQm : MeasurableSet Q) (hQc : Convex ℝ Q) (hQs : ∀ x ∈ Q, -x ∈ Q)
    (hQ : HasSliceBound (volume : Measure E) gaussDensity Q) (V : Submodule ℝ E) :
    1 ≤ volume {y : V | (y : E) ∈ Q} := by
  have hψmeas : Measurable V.prodOrthogonalEquiv :=
    V.measurePreserving_prodOrthogonalEquiv.measurable
  have hψsymm : Measurable V.prodOrthogonalEquiv.symm :=
    (LinearMap.continuous_of_finiteDimensional
      (V.prodOrthogonalEquiv.symm : (V × (Vᗮ : Submodule ℝ E)) →ₗ[ℝ] E)).measurable
  let ψm : E ≃ᵐ (V × (Vᗮ : Submodule ℝ E)) :=
    ⟨V.prodOrthogonalEquiv.toEquiv, hψmeas, hψsymm⟩
  have hMPsymm : MeasurePreserving V.prodOrthogonalEquiv.symm
      ((volume : Measure V).prod (volume : Measure (Vᗮ : Submodule ℝ E))) (volume : Measure E) :=
    (V.measurePreserving_prodOrthogonalEquiv).symm ψm
  have hQ' := HasSliceBound.of_measurePreserving V.prodOrthogonalEquiv.symm hMPsymm hψmeas
    measurable_gaussDensity hQm hQ
  set W := (Vᗮ : Submodule ℝ E)
  set QQ : Set (V × W) := V.prodOrthogonalEquiv.symm ⁻¹' Q with hQQdef
  have hQQm : MeasurableSet QQ := hψsymm hQm
  have hQQc : Convex ℝ QQ :=
    hQc.linear_preimage (V.prodOrthogonalEquiv.symm : (V × W) →ₗ[ℝ] E)
  have hQQs : ∀ q ∈ QQ, -q ∈ QQ := by
    intro q hq
    have hneg : V.prodOrthogonalEquiv.symm (-q) = -(V.prodOrthogonalEquiv.symm q) := map_neg _ _
    simpa [hQQdef, Set.mem_preimage, hneg] using hQs _ hq
  -- the marginal of `QQ` in the `V` direction
  set f : W → ℝ≥0∞ := fun z => (volume : Measure V) {y : V | (y, z) ∈ QQ} with hfdef
  have hfmeas : Measurable f := measurable_measure_prodMk_right hQQm
  have hsecm : ∀ z : W, MeasurableSet {y : V | (y, z) ∈ QQ} :=
    fun z => hQQm.preimage (by fun_prop)
  have hfeven : ∀ z, f (-z) = f z := by
    intro z
    have hset : {y : V | (y, -z) ∈ QQ} = -{y : V | (y, z) ∈ QQ} := by
      ext y
      simp only [Set.mem_neg, Set.mem_ofPred_eq]
      exact ⟨fun hy => by simpa using hQQs _ hy, fun hy => by simpa using hQQs _ hy⟩
    rw [hfdef]
    simp only
    rw [hset, measure_neg]
  have hflc : LogConcave f := by
    have hswapc : Convex ℝ {q : W × V | (q.2, q.1) ∈ QQ} :=
      fun _ h1 _ h2 _ _ ha hb hab => hQQc h1 h2 ha hb hab
    have heq : (fun z => ∫⁻ y in (Set.univ : Set V),
        Set.indicator {q : W × V | (q.2, q.1) ∈ QQ} (fun _ => (1 : ℝ≥0∞)) (z, y)
        ∂(volume : Measure V)) = f := by
      funext z
      rw [show (fun y : V =>
          Set.indicator {q : W × V | (q.2, q.1) ∈ QQ} (fun _ => (1 : ℝ≥0∞)) (z, y))
          = Set.indicator {y : V | (y, z) ∈ QQ} (fun _ => (1 : ℝ≥0∞)) from rfl,
        lintegral_indicator (hsecm z), setLIntegral_one, hfdef]
      simp
    exact heq ▸ LogConcave.setLIntegral_prod_right hasPrekopaLeindler_innerProductSpace
      (measurable_one.indicator (hQQm.preimage (by fun_prop))) (logConcave_indicator hswapc 1)
      MeasurableSet.univ convex_univ
  have hfle : ∀ z, f z ≤ f 0 := fun z => hflc.le_apply_zero hfeven z
  have hf0 : f 0 = volume {y : V | (y : E) ∈ Q} := by
    rw [hfdef]
    simp only
    congr 1
    ext y
    simp [hQQdef, Set.mem_preimage, Submodule.prodOrthogonalEquiv_symm_apply]
  have hdens : ∀ q : V × W, gaussDensity (V.prodOrthogonalEquiv.symm q)
      = gaussDensity q.1 * gaussDensity q.2 := by
    intro q
    rw [gaussDensity_def, gaussDensity_def, gaussDensity_def,
      V.norm_prodOrthogonalEquiv_symm q, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  have key : ∀ ε : ℝ, 0 < ε → ENNReal.ofReal (Real.exp (-π * ε ^ 2)) ≤ f 0 := by
    intro ε hε
    have hSm : MeasurableSet (Metric.closedBall (0 : W) ε) := measurableSet_closedBall
    have hApp := hQ' (Set.univ ×ˢ Metric.closedBall (0 : W) ε)
      (MeasurableSet.univ.prod hSm)
      (convex_univ.prod (convex_closedBall _ _))
      (fun q hq => ⟨Set.mem_univ _, by
        have hn : ‖-q.2‖ ≤ ε := by
          rw [norm_neg]; simpa [Metric.mem_closedBall, dist_zero_right] using hq.2
        simpa [Metric.mem_closedBall, dist_zero_right] using hn⟩)
    have hlhs : ∫⁻ q in Set.univ ×ˢ Metric.closedBall (0 : W) ε,
        gaussDensity (V.prodOrthogonalEquiv.symm q)
        ∂((volume : Measure V).prod (volume : Measure W))
        = (∫⁻ y : V, gaussDensity y) * ∫⁻ z in Metric.closedBall (0 : W) ε, gaussDensity z := by
      rw [← Measure.prod_restrict, Measure.restrict_univ, lintegral_congr hdens]
      exact lintegral_prod_mul measurable_gaussDensity.aemeasurable
        measurable_gaussDensity.aemeasurable
    have hlow : ENNReal.ofReal (Real.exp (-π * ε ^ 2)) * volume (Metric.closedBall (0 : W) ε)
        ≤ ∫⁻ z in Metric.closedBall (0 : W) ε, gaussDensity z := by
      rw [← setLIntegral_const]
      refine setLIntegral_mono' hSm fun z hz => ?_
      rw [gaussDensity_def]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
      have hznorm : ‖z‖ ≤ ε := by simpa [Metric.mem_closedBall, dist_zero_right] using hz
      have hsq : ‖z‖ ^ 2 ≤ ε ^ 2 := by nlinarith [norm_nonneg z]
      nlinarith [Real.pi_pos]
    have hrhs : ((volume : Measure V).prod (volume : Measure W))
        ((Set.univ ×ˢ Metric.closedBall (0 : W) ε) ∩ QQ)
        ≤ f 0 * volume (Metric.closedBall (0 : W) ε) := by
      rw [Measure.prod_apply_symm ((MeasurableSet.univ.prod hSm).inter hQQm)]
      calc ∫⁻ z : W, (volume : Measure V)
              ((fun y => (y, z)) ⁻¹' ((Set.univ ×ˢ Metric.closedBall (0 : W) ε) ∩ QQ))
          ≤ ∫⁻ z : W, Set.indicator (Metric.closedBall (0 : W) ε) (fun _ => f 0) z := by
            refine lintegral_mono fun z => ?_
            by_cases hz : z ∈ Metric.closedBall (0 : W) ε
            · rw [Set.indicator_of_mem hz]
              refine le_trans (le_of_eq ?_) (hfle z)
              rw [hfdef]
              congr 1
              ext y; simp [hz]
            · rw [Set.indicator_of_notMem hz,
                show ((fun y => (y, z)) ⁻¹'
                    ((Set.univ ×ˢ Metric.closedBall (0 : W) ε) ∩ QQ)) = ∅ by ext y; simp [hz]]
              simp
        _ = f 0 * volume (Metric.closedBall (0 : W) ε) := by
            rw [lintegral_indicator hSm, setLIntegral_const]
    have hvpos : volume (Metric.closedBall (0 : W) ε) ≠ 0 :=
      (Metric.measure_closedBall_pos volume 0 hε).ne'
    have hvtop : volume (Metric.closedBall (0 : W) ε) ≠ ⊤ := measure_closedBall_lt_top.ne
    have hcomb : ENNReal.ofReal (Real.exp (-π * ε ^ 2)) * volume (Metric.closedBall (0 : W) ε)
        ≤ f 0 * volume (Metric.closedBall (0 : W) ε) := by
      calc ENNReal.ofReal (Real.exp (-π * ε ^ 2)) * volume (Metric.closedBall (0 : W) ε)
          ≤ ∫⁻ z in Metric.closedBall (0 : W) ε, gaussDensity z := hlow
        _ = (∫⁻ y : V, gaussDensity y) * ∫⁻ z in Metric.closedBall (0 : W) ε, gaussDensity z := by
              rw [lintegral_gaussDensity_eq_one, one_mul]
        _ = ∫⁻ q in Set.univ ×ˢ Metric.closedBall (0 : W) ε,
              gaussDensity (V.prodOrthogonalEquiv.symm q)
              ∂((volume : Measure V).prod (volume : Measure W)) := hlhs.symm
        _ ≤ ((volume : Measure V).prod (volume : Measure W))
              ((Set.univ ×ˢ Metric.closedBall (0 : W) ε) ∩ QQ) := hApp
        _ ≤ f 0 * volume (Metric.closedBall (0 : W) ε) := hrhs
    have hcomb' : volume (Metric.closedBall (0 : W) ε) * ENNReal.ofReal (Real.exp (-π * ε ^ 2))
        ≤ volume (Metric.closedBall (0 : W) ε) * f 0 := by
      rw [mul_comm, mul_comm (volume (Metric.closedBall (0 : W) ε)) (f 0)]; exact hcomb
    exact (ENNReal.mul_le_mul_iff_right hvpos hvtop).mp hcomb'
  rw [← hf0]
  have hcont : Filter.Tendsto (fun ε : ℝ => ENNReal.ofReal (Real.exp (-π * ε ^ 2)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have h1 : Filter.Tendsto (fun ε : ℝ => ENNReal.ofReal (Real.exp (-π * ε ^ 2)))
        (nhds 0) (nhds (ENNReal.ofReal (Real.exp (-π * (0 : ℝ) ^ 2)))) :=
      (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (by fun_prop))).tendsto 0
    simpa using h1.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto hcont ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact key ε hε

section Milestones

/-- The volume `ω_n` of the unit ball of `EuclideanSpace ℝ (Fin n)`. -/
@[expose] noncomputable def unitBallVolume (n : ℕ) : ℝ :=
  (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1)).toReal

theorem unitBallVolume_pos (n : ℕ) : 0 < unitBallVolume n := volume_ball_one_pos

theorem ballRadius_eq (n : ℕ) : ballRadius n = unitBallVolume n ^ (-(1 / (n : ℝ))) := by
  rw [ballRadius, unitVolumeRadius, finrank_euclideanSpace_fin, unitBallVolume]

theorem ballRadius_sq (n : ℕ) : ballRadius n ^ 2 = unitBallVolume n ^ (-(2 / (n : ℝ))) := by
  rw [ballRadius_eq, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (unitBallVolume_pos n).le]
  congr 1
  push_cast
  ring

theorem unitBallVolume_one : unitBallVolume 1 = 2 := by
  rw [unitBallVolume, EuclideanSpace.volume_ball]
  simp only [Fintype.card_fin, Nat.cast_one, ofReal_one, one_mul, pow_one]
  rw [Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq,
    ENNReal.toReal_ofReal (by positivity), div_eq_iff (by positivity)]
  have h : Real.sqrt π ≠ 0 := by positivity
  field_simp

theorem ballRadius_one : ballRadius 1 = 1 / 2 := by
  rw [ballRadius_eq, unitBallVolume_one, Nat.cast_one, div_one, Real.rpow_neg_one]
  norm_num

theorem unitBallVolume_two : unitBallVolume 2 = π := by
  rw [unitBallVolume, EuclideanSpace.volume_ball_fin_two]
  simp [Real.pi_pos.le]

theorem ballRadius_two : ballRadius 2 = 1 / Real.sqrt π := by
  rw [ballRadius_eq, unitBallVolume_two, show ((2 : ℕ) : ℝ) = 2 by norm_num,
    Real.rpow_neg Real.pi_pos.le, ← Real.sqrt_eq_rpow, one_div]

theorem sq_le_sq_iff_abs_le {a c : ℝ} (hc : 0 ≤ c) : a ^ 2 ≤ c ^ 2 ↔ |a| ≤ c := by
  rw [sq_le_sq, abs_of_nonneg hc]

/-- **The product-of-balls theorem for an arbitrary index type.** -/
theorem one_le_volume_prodBall_subtype {ι κ : Type*} [Fintype ι] [DecidableEq κ] [Countable κ]
    (blk : ι → κ) (V : Submodule ℝ (EuclideanSpace ℝ ι)) :
    1 ≤ volume {y : V | (y : EuclideanSpace ℝ ι) ∈ prodBall blk} :=
  one_le_volume_subtype_mem (measurableSet_prodBall blk) (convex_prodBall blk)
    (fun _ hx => neg_mem_prodBall blk hx) (hasSliceBound_prodBall blk) V

/-- With singleton blocks, the product of balls of volume one is the cube of half-side `1 / 2`. -/
theorem prodBall_id {ι : Type*} [Fintype ι] [DecidableEq ι] :
    prodBall (id : ι → ι) = {x : EuclideanSpace ℝ ι | ∀ i, |x i| ≤ 1 / 2} := by
  have hsum : ∀ (f : ι → ℝ) (k : ι), ∑ j : {j : ι // id j = k}, f ↑j = f k := by
    intro f k
    rw [← Finset.sum_subtype ({k} : Finset ι) (by simp) f]
    simp
  have hcard : ∀ k : ι, Fintype.card {j : ι // id j = k} = 1 := by
    intro k
    rw [Fintype.card_subtype]
    simp [Finset.filter_eq']
  ext x
  constructor
  · intro h i
    have hi := h i
    rw [hsum (fun j => (x j) ^ 2) i, hcard i, ballRadius_one] at hi
    exact (sq_le_sq_iff_abs_le (by norm_num)).mp hi
  · intro h k
    rw [hsum (fun j => (x j) ^ 2) k, hcard k, ballRadius_one]
    exact (sq_le_sq_iff_abs_le (by norm_num)).mpr (h k)

theorem smul_setOf_abs_le {ι : Type*} (V : Submodule ℝ (EuclideanSpace ℝ ι))
    {r c : ℝ} (hr : 0 < r) :
    (r • {y : V | ∀ i, |(y : EuclideanSpace ℝ ι) i| ≤ c})
      = {y : V | ∀ i, |(y : EuclideanSpace ℝ ι) i| ≤ r * c} := by
  ext y
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hr.ne']
  constructor
  · intro h i
    have hi := h i
    rw [Submodule.coe_smul] at hi
    simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hr)] at hi
    rw [inv_mul_le_iff₀ hr] at hi
    linarith
  · intro h i
    have hi := h i
    rw [Submodule.coe_smul]
    simp only [PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos (inv_pos.mpr hr)]
    rw [inv_mul_le_iff₀ hr]
    linarith

/-- **Vaaler's cube-slicing theorem** (Vaaler 1979; Bombieri–Gubler, Theorem C.3.8): every central
slice of the cube `[-1, 1]ᴺ` by a `k`-dimensional subspace has `k`-volume at least `2 ^ k`. -/
theorem two_pow_finrank_le_volume_inter_cube {ι : Type*} [Fintype ι]
    (V : Submodule ℝ (EuclideanSpace ℝ ι)) :
    (2 : ℝ≥0∞) ^ Module.finrank ℝ V ≤
      volume {y : V | ∀ i, |(y : EuclideanSpace ℝ ι) i| ≤ 1} := by
  classical
  have h1 : 1 ≤ volume {y : V | ∀ i, |(y : EuclideanSpace ℝ ι) i| ≤ 1 / 2} := by
    have h := one_le_volume_prodBall_subtype (id : ι → ι) V
    rwa [prodBall_id] at h
  have h2 : {y : V | ∀ i, |(y : EuclideanSpace ℝ ι) i| ≤ 1}
      = (2 : ℝ) • {y : V | ∀ i, |(y : EuclideanSpace ℝ ι) i| ≤ 1 / 2} := by
    rw [smul_setOf_abs_le V (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [h2, Measure.addHaar_smul]
  calc (2 : ℝ≥0∞) ^ Module.finrank ℝ V
      = ENNReal.ofReal |(2 : ℝ) ^ Module.finrank ℝ (V : Type _)| * 1 := by
        rw [mul_one, abs_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
        norm_num
    _ ≤ ENNReal.ofReal |(2 : ℝ) ^ Module.finrank ℝ (V : Type _)| *
        volume {y : V | ∀ i, |(y : EuclideanSpace ℝ ι) i| ≤ 1 / 2} := by gcongr

/-- **The product-of-balls theorem** (Bombieri–Gubler, Theorem C.3.8), in the roadmap's form:
partition the `N` coordinates into blocks by `blk`, let `Q` be the product over the blocks of the
euclidean ball of volume one in that block's coordinates, and every central slice of `Q` by a
subspace `V` has volume at least one, computed on `V`. -/
theorem one_le_volume_inter_prodBall {N r : ℕ} (blk : Fin N → Fin r)
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin N))) :
    1 ≤ volume {x : V | ∀ i : Fin r,
      ∑ j ∈ Finset.univ.filter (fun j => blk j = i), (x : EuclideanSpace ℝ (Fin N)) j ^ 2 ≤
        unitBallVolume (Finset.univ.filter (fun j => blk j = i)).card ^
          (-(2 / ((Finset.univ.filter (fun j => blk j = i)).card : ℝ)))} := by
  have hset : {x : V | ∀ i : Fin r,
      ∑ j ∈ Finset.univ.filter (fun j => blk j = i), (x : EuclideanSpace ℝ (Fin N)) j ^ 2 ≤
        unitBallVolume (Finset.univ.filter (fun j => blk j = i)).card ^
          (-(2 / ((Finset.univ.filter (fun j => blk j = i)).card : ℝ)))}
      = {y : V | (y : EuclideanSpace ℝ (Fin N)) ∈ prodBall blk} := by
    have hsum : ∀ (y : V) (i : Fin r),
        ∑ j ∈ Finset.univ.filter (fun j => blk j = i), (y : EuclideanSpace ℝ (Fin N)) j ^ 2
        = ∑ j : {j : Fin N // blk j = i}, (y : EuclideanSpace ℝ (Fin N)) (j : Fin N) ^ 2 :=
      fun y i => Finset.sum_subtype _ (by simp) _
    have hcard : ∀ i : Fin r, (Finset.univ.filter (fun j => blk j = i)).card
        = Fintype.card {j : Fin N // blk j = i} := fun i => (Fintype.card_subtype _).symm
    ext y
    constructor
    · intro h i
      have hi := h i
      rw [hsum y i, hcard i] at hi
      rw [← ballRadius_sq] at hi
      exact hi
    · intro h i
      have hi := h i
      rw [hsum y i, hcard i, ← ballRadius_sq]
      exact hi
  rw [hset]
  exact one_le_volume_prodBall_subtype blk V

/-- **The inscribed-cube bound at a complex place**: a subspace of `ℝ^{2n}`, with coordinates
paired as the real and imaginary parts of `ℂⁿ`, meets the unit polydisc in volume at least
`2 ^ (dim V / 2)`. The polydisc contains the cube of half-side `2 ^ (-1/2)`, and the cube case
gives `√2 ^ dim V` there, which dominates `2 ^ (dim V / 2)` for every dimension, even or odd. -/
theorem two_pow_le_volume_inter_polydisc {n : ℕ}
    (V : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin 2))) :
    (2 : ℝ≥0∞) ^ (Module.finrank ℝ V / 2) ≤
      volume {y : V | ∀ i : Fin n,
        (y : EuclideanSpace ℝ (Fin n × Fin 2)) (i, 0) ^ 2
          + (y : EuclideanSpace ℝ (Fin n × Fin 2)) (i, 1) ^ 2 ≤ 1} := by
  set k := Module.finrank ℝ (V : Type _) with hk
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsub : {y : V | ∀ p, |(y : EuclideanSpace ℝ (Fin n × Fin 2)) p| ≤ 1 / Real.sqrt 2}
      ⊆ {y : V | ∀ i : Fin n,
        (y : EuclideanSpace ℝ (Fin n × Fin 2)) (i, 0) ^ 2
          + (y : EuclideanSpace ℝ (Fin n × Fin 2)) (i, 1) ^ 2 ≤ 1} := by
    intro y hy i
    have e0 := (sq_le_sq_iff_abs_le (a := (y : EuclideanSpace ℝ (Fin n × Fin 2)) (i, 0))
      (c := 1 / Real.sqrt 2) (by positivity)).mpr (hy (i, 0))
    have e1 := (sq_le_sq_iff_abs_le (a := (y : EuclideanSpace ℝ (Fin n × Fin 2)) (i, 1))
      (c := 1 / Real.sqrt 2) (by positivity)).mpr (hy (i, 1))
    have hhalf : (1 / Real.sqrt 2 : ℝ) ^ 2 = 1 / 2 := by rw [div_pow, one_pow, hsq2]
    rw [hhalf] at e0 e1
    linarith
  refine le_trans ?_ (measure_mono hsub)
  have hscale : {y : V | ∀ p, |(y : EuclideanSpace ℝ (Fin n × Fin 2)) p| ≤ 1 / Real.sqrt 2}
      = (1 / Real.sqrt 2 : ℝ) • {y : V | ∀ p, |(y : EuclideanSpace ℝ (Fin n × Fin 2)) p| ≤ 1} := by
    rw [smul_setOf_abs_le V (by positivity)]
    norm_num
  rw [hscale, Measure.addHaar_smul, ← hk]
  have hcube := two_pow_finrank_le_volume_inter_cube V
  rw [← hk] at hcube
  have habs : |(1 / Real.sqrt 2 : ℝ) ^ k| = (1 / Real.sqrt 2) ^ k := abs_of_pos (by positivity)
  rw [habs]
  have hreal : (2 : ℝ) ^ (k / 2) ≤ (1 / Real.sqrt 2) ^ k * 2 ^ k := by
    have hprod : (1 / Real.sqrt 2 : ℝ) ^ k * 2 ^ k = Real.sqrt 2 ^ k := by
      rw [← mul_pow]
      congr 1
      field_simp
      nlinarith [hsq2]
    rw [hprod]
    conv_rhs => rw [← Nat.div_add_mod k 2]
    rw [pow_add, pow_mul, hsq2]
    have h1 : (1 : ℝ) ≤ Real.sqrt 2 ^ (k % 2) :=
      one_le_pow₀ (by nlinarith [hsq2, hs2])
    nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) (k / 2)]
  calc (2 : ℝ≥0∞) ^ (k / 2) = ENNReal.ofReal ((2 : ℝ) ^ (k / 2)) := by
        rw [ENNReal.ofReal_pow (by norm_num)]
        norm_num
    _ ≤ ENNReal.ofReal ((1 / Real.sqrt 2 : ℝ) ^ k * 2 ^ k) := ENNReal.ofReal_le_ofReal hreal
    _ = ENNReal.ofReal ((1 / Real.sqrt 2 : ℝ) ^ k) * (2 : ℝ≥0∞) ^ k := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
        norm_num
    _ ≤ ENNReal.ofReal ((1 / Real.sqrt 2 : ℝ) ^ k) *
        volume {y : V | ∀ p, |(y : EuclideanSpace ℝ (Fin n × Fin 2)) p| ≤ 1} := by gcongr

end Milestones
