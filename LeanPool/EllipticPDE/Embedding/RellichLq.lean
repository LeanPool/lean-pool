/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Embedding.H01Sobolev
public import LeanPool.EllipticPDE.Analysis.LpInterpolation
public import LeanPool.EllipticPDE.Spectrum.RellichDischarge


/-!
# Rellich-Kondrachov below the critical exponent

`EllipticPdes.Spectrum.embL2_isCompact` is the compact embedding `H₀¹(Ω) ↪ L²(Ω)` on a bounded
measurable domain. `EllipticPdes.Embedding.eLpNorm_le_of_mem_H01` bounds the same function at the
Sobolev conjugate `2⋆`. Between the two exponents the embedding stays compact, which is
Rellich-Kondrachov in the form that asks nothing of the boundary.

## Interpolation in place of mollification

Guo proves the theorem by mollifying, bounding `‖u^ε - u‖_{L¹}` by `ε‖Du‖_{L¹}` uniformly over a
bounded family, interpolating between `L¹` and `L^{p⋆}`, and finishing with Arzelà-Ascoli at fixed
`ε`. The first and last moves produce compactness at the lower exponent, which
`embL2_isCompact` already supplies here by a translation-modulus argument that needs no extension
operator. What remains is the interpolation, `EllipticPdes.Analysis.eLpNorm_le_rpow_mul_rpow`,
applied between `L²` and `L^{2⋆}` in place of Guo's `L¹` and `L^{p⋆}`: a finite net of the unit
ball's image in `L²` is a net in `L^q`, since the `L^{2⋆}` seminorms of the differences are
bounded on the ball.

The exponent hypothesis is the reciprocal relation `1/q = θ/2 + (1-θ)/2⋆` with `θ ∈ (0,1)`, which
is what `2 < q < 2⋆` amounts to, in the form the estimates use.

## Main declarations

* `EllipticPdes.Embedding.rellichEmbL`: the embedding `H₀¹(Ω) →L[ℝ] L^q(Ω)` on a bounded domain.
* `EllipticPdes.Embedding.norm_rellichEmbL_sub_le`: the interpolation estimate on the unit ball.
* `EllipticPdes.Embedding.rellichEmbL_isCompact`: compactness of that embedding.

## References

Y. Guo, *Partial Differential Equations*, Theorem IV.2.10; L. C. Evans, *Partial Differential
Equations* (2nd ed.), §5.7 Theorem 1.
-/

@[expose] public section

open MeasureTheory Metric Bornology
open scoped NNReal ENNReal

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Sobolev EllipticPdes.Analysis

variable {d : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin d))} {p' q : ℝ≥0}

section

variable [Fact (1 ≤ (q : ℝ≥0∞))]

/-- The Sobolev embedding of `H₀¹(Ω)` into `L^q(Ω)` on a bounded domain, at any exponent up to
the critical one. -/
def rellichEmbL (hΩm : MeasurableSet Ω) (hΩb : IsBounded Ω) (hd : 2 < d)
    (hq : ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) :
    H01 Ω →L[ℝ] Lp ℝ (q : ℝ≥0∞) (volume.restrict Ω) :=
  sobolevEmbL (fun _U hU => eLpNorm_le_of_mem_H01_of_isBounded hΩm hΩb hd hq hU)

/-- The difference of two images is the image of the difference, almost everywhere. -/
lemma coeFn_rellichEmbL_sub (hΩm : MeasurableSet Ω) (hΩb : IsBounded Ω) (hd : 2 < d)
    (hq : ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) (U V : H01 Ω) :
    ⇑(rellichEmbL hΩm hΩb hd hq U - rellichEmbL hΩm hΩb hd hq V)
      =ᵐ[volume.restrict Ω] ⇑(((U - V : H01 Ω) : H1amb Ω) 0) := by
  have hUc : ⇑(rellichEmbL hΩm hΩb hd hq U) =ᵐ[volume.restrict Ω] ⇑((U : H1amb Ω) 0) :=
    coeFn_sobolevEmbL _ U
  have hVc : ⇑(rellichEmbL hΩm hΩb hd hq V) =ᵐ[volume.restrict Ω] ⇑((V : H1amb Ω) 0) :=
    coeFn_sobolevEmbL _ V
  filter_upwards [Lp.coeFn_sub (rellichEmbL hΩm hΩb hd hq U) (rellichEmbL hΩm hΩb hd hq V),
    hUc, hVc, Lp.coeFn_sub ((U : H1amb Ω) 0) ((V : H1amb Ω) 0)] with x hsub hU hV hcoord
  rw [hsub, Pi.sub_apply, hU, hV, show ((U - V : H01 Ω) : H1amb Ω) 0
    = (U : H1amb Ω) 0 - (V : H1amb Ω) 0 from rfl, hcoord, Pi.sub_apply]

/-- **Interpolation estimate on the unit ball.** With `1/q = θ/2 + (1-θ)/2⋆`, the distance in
`L^q(Ω)` between the images of two elements of the unit ball is bounded by the `θ`-th power of
their distance in `L²(Ω)`, times a constant. -/
theorem norm_rellichEmbL_sub_le (hΩm : MeasurableSet Ω) (hΩb : IsBounded Ω) (hd : 2 < d)
    (hq : ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) (hq0 : q ≠ 0)
    (hp' : (p' : ℝ)⁻¹ = ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹) (hp'0 : p' ≠ 0)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hqθ : (q : ℝ)⁻¹ = θ * ((2 : ℝ≥0) : ℝ)⁻¹ + (1 - θ) * (p' : ℝ)⁻¹)
    {U V : H01 Ω} (hU : ‖U‖ ≤ 1) (hV : ‖V‖ ≤ 1) :
    ‖rellichEmbL hΩm hΩb hd hq U - rellichEmbL hΩm hΩb hd hq V‖
      ≤ ‖embL2 Ω U - embL2 Ω V‖ ^ θ * (2 * (sobolevConst d : ℝ) * d) ^ (1 - θ) := by
  set W : H1amb Ω := ((U - V : H01 Ω) : H1amb Ω) with hW
  have hWmem : W ∈ H01 Ω := (U - V : H01 Ω).2
  have hcoe := coeFn_rellichEmbL_sub hΩm hΩb hd hq U V
  -- The `L²` end is the distance of the images under `embL2`.
  have h2 : eLpNorm (W 0) 2 (volume.restrict Ω) = ‖embL2 Ω U - embL2 Ω V‖ₑ := by
    rw [← Lp.enorm_def, embL2_apply, embL2_apply]
    rfl
  -- The critical end is bounded on the ball.
  have hM : eLpNorm (W 0) p' (volume.restrict Ω)
      ≤ ENNReal.ofReal (2 * (sobolevConst d : ℝ) * d) := by
    have hUV : ‖U - V‖ ≤ 2 := (norm_sub_le _ _).trans (by linarith)
    calc eLpNorm (W 0) p' (volume.restrict Ω)
        ≤ sobolevConst d * ∑ i : Fin d, ‖W i.succ‖ₑ :=
          eLpNorm_le_of_mem_H01 hΩm (by omega) hp' hWmem
      _ ≤ (sobolevConst d : ℝ≥0∞) * ENNReal.ofReal ((d : ℝ) * ‖U - V‖) := by
          gcongr
          exact sum_enorm_succ_le (U - V : H01 Ω)
      _ ≤ ENNReal.ofReal (2 * (sobolevConst d : ℝ) * d) := by
          rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          calc (sobolevConst d : ℝ) * ((d : ℝ) * ‖U - V‖)
              ≤ (sobolevConst d : ℝ) * ((d : ℝ) * 2) := by gcongr
            _ = 2 * (sobolevConst d : ℝ) * d := by ring
  -- Interpolate.
  have hinterp : eLpNorm (W 0) q (volume.restrict Ω)
      ≤ ‖embL2 Ω U - embL2 Ω V‖ₑ ^ θ
        * ENNReal.ofReal (2 * (sobolevConst d : ℝ) * d) ^ (1 - θ) := by
    refine eLpNorm_le_of_le_of_le (r := 2) (s := (p' : ℝ≥0∞)) (q := (q : ℝ≥0∞))
      two_ne_zero (by simp) (by simpa using hp'0) (by simp) (by simpa using hq0) (by simp)
      hθ0 hθ1 ?_ (Lp.aestronglyMeasurable _) (le_of_eq h2) hM
    simpa using hqθ
  -- Read it back as a norm in `L^q`.
  rw [Lp.norm_def]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  rw [eLpNorm_congr_ae hcoe]
  refine hinterp.trans (le_of_eq ?_)
  conv_rhs =>
    rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ ‖embL2 Ω U - embL2 Ω V‖ ^ θ)]
  rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hθ0.le,
    ← ENNReal.ofReal_rpow_of_nonneg
      (by positivity : (0:ℝ) ≤ 2 * (sobolevConst d : ℝ) * d) (by linarith),
    ofReal_norm]

/-- **Rellich-Kondrachov below the critical exponent.** On a bounded measurable domain the
embedding `H₀¹(Ω) ↪ L^q(Ω)` is a compact operator for every `q` strictly between `2` and the
Sobolev conjugate `2⋆`, the strictness being the hypothesis `1/q = θ/2 + (1-θ)/2⋆` with
`θ ∈ (0,1)`.

A finite net of the unit ball's image in `L²(Ω)`, which `embL2_isCompact` supplies, is a net in
`L^q(Ω)` at the radius the interpolation estimate names. No regularity of the boundary is used,
the zero-boundary condition standing in for it. -/
theorem rellichEmbL_isCompact (hΩm : MeasurableSet Ω) (hΩb : IsBounded Ω) (hd : 2 < d)
    (hq : ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) (hq0 : q ≠ 0)
    (hp' : (p' : ℝ)⁻¹ = ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹) (hp'0 : p' ≠ 0)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hqθ : (q : ℝ)⁻¹ = θ * ((2 : ℝ≥0) : ℝ)⁻¹ + (1 - θ) * (p' : ℝ)⁻¹) :
    IsCompactOperator (rellichEmbL hΩm hΩb hd hq) := by
  set T := rellichEmbL hΩm hΩb hd hq with hT
  set M : ℝ := 2 * (sobolevConst d : ℝ) * d with hM
  have hM0 : 0 ≤ M := by positivity
  -- The `L²` image of the unit ball is totally bounded.
  have hL2 : TotallyBounded (⇑(embL2 Ω) '' closedBall (0 : H01 Ω) 1) := by
    have hcpt : IsCompactOperator ((embL2 Ω).toLinearMap) := embL2_isCompact hΩm hΩb
    have hcl := (isCompactOperator_iff_isCompact_closure_image_closedBall
      (embL2 Ω).toLinearMap one_pos).mp hcpt
    exact hcl.totallyBounded.subset subset_closure
  refine (isCompactOperator_iff_isCompact_closure_image_closedBall T.toLinearMap one_pos).mpr ?_
  refine TotallyBounded.isCompact_of_isClosed ?_ isClosed_closure
  refine TotallyBounded.closure ?_
  rw [Metric.totallyBounded_iff]
  intro ε hε
  -- The radius the interpolation estimate turns into `ε`.
  set K : ℝ := M ^ (1 - θ) + 1 with hK
  have hK0 : 0 < K := by positivity
  set δ : ℝ := (ε / K) ^ θ⁻¹ with hδ
  have hδ0 : 0 < δ := Real.rpow_pos_of_pos (by positivity) _
  obtain ⟨t, hts, htf, htcov⟩ :=
    totallyBounded_iff_subset.1 hL2 _ (Metric.dist_mem_uniformity hδ0)
  -- A preimage in the unit ball for each net point.
  have hchoice : ∀ y : L2D Ω, ∃ U : H01 Ω, ‖U‖ ≤ 1 ∧
      (y ∈ ⇑(embL2 Ω) '' closedBall (0 : H01 Ω) 1 → embL2 Ω U = y) := by
    intro y
    by_cases hy : y ∈ ⇑(embL2 Ω) '' closedBall (0 : H01 Ω) 1
    · obtain ⟨U, hU, rfl⟩ := hy
      exact ⟨U, by simpa using hU, fun _ => rfl⟩
    · exact ⟨0, by simp, fun h => absurd h hy⟩
  choose g hg1 hg2 using hchoice
  refine ⟨(fun y => T (g y)) '' t, htf.image _, ?_⟩
  rintro _ ⟨U, hU, rfl⟩
  have hUball : ‖U‖ ≤ 1 := by simpa using hU
  have hUim : embL2 Ω U ∈ ⇑(embL2 Ω) '' closedBall (0 : H01 Ω) 1 := ⟨U, hU, rfl⟩
  obtain ⟨y, hyt, hdy⟩ : ∃ y ∈ t, dist (embL2 Ω U) y < δ := by
    have := htcov hUim
    simpa using this
  refine Set.mem_iUnion₂.2 ⟨T (g y), Set.mem_image_of_mem _ hyt, ?_⟩
  rw [Metric.mem_ball, dist_eq_norm]
  have hgy : embL2 Ω (g y) = y := hg2 y (hts hyt)
  have hdist : ‖embL2 Ω U - embL2 Ω (g y)‖ < δ := by
    rw [hgy, ← dist_eq_norm]; exact hdy
  calc ‖T U - T (g y)‖
      ≤ ‖embL2 Ω U - embL2 Ω (g y)‖ ^ θ * M ^ (1 - θ) :=
        norm_rellichEmbL_sub_le hΩm hΩb hd hq hq0 hp' hp'0 hθ0 hθ1 hqθ hUball (hg1 y)
    _ ≤ δ ^ θ * M ^ (1 - θ) := by gcongr
    _ = ε / K * M ^ (1 - θ) := by
        rw [← Real.rpow_mul (le_of_lt (div_pos hε hK0)), inv_mul_cancel₀ (ne_of_gt hθ0),
          Real.rpow_one]
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ hK0]
        have hMK : M ^ (1 - θ) < K := by rw [hK]; linarith
        nlinarith [Real.rpow_nonneg hM0 (1 - θ)]

end

/-! ### Exponents below `2` -/

section LowExponent

variable [Fact (1 ≤ (q : ℝ≥0∞))]

/-- On a finite measure the identity includes `L²` into `L^q` for `q ≤ 2`, as a continuous linear
map, with the operator norm the measure supplies. -/
def lqOfL2 [IsFiniteMeasure (volume.restrict Ω)] (hq2 : (q : ℝ≥0∞) ≤ 2) :
    L2D Ω →L[ℝ] Lp ℝ (q : ℝ≥0∞) (volume.restrict Ω) :=
  LinearMap.mkContinuous
    { toFun := fun f => ((Lp.memLp f).mono_exponent hq2).toLp f
      map_add' := fun f g => by
        rw [MemLp.toLp_congr _ (((Lp.memLp f).mono_exponent hq2).add
              ((Lp.memLp g).mono_exponent hq2)) (Lp.coeFn_add f g), MemLp.toLp_add]
      map_smul' := fun c f => by
        rw [MemLp.toLp_congr _ (((Lp.memLp f).mono_exponent hq2).const_smul c)
          (Lp.coeFn_smul c f), MemLp.toLp_const_smul]
        rfl }
    (((volume.restrict Ω) Set.univ).toReal ^
      (1 / (q : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal))
    (fun f => by
      change ‖((Lp.memLp f).mono_exponent hq2).toLp f‖ ≤ _ * ‖f‖
      rw [Lp.norm_toLp, Lp.norm_def]
      have hq1 : (1 : ℝ) ≤ (q : ℝ≥0∞).toReal := by
        have := ENNReal.toReal_mono ENNReal.coe_ne_top (Fact.out : (1 : ℝ≥0∞) ≤ (q : ℝ≥0∞))
        simpa using this
      have hq2' : (q : ℝ≥0∞).toReal ≤ (2 : ℝ≥0∞).toReal :=
        ENNReal.toReal_mono (by simp) hq2
      have he : (0 : ℝ) ≤ 1 / (q : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal := by
        rw [sub_nonneg]
        exact one_div_le_one_div_of_le (by linarith) hq2'
      have hb := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict Ω) hq2
        (Lp.aestronglyMeasurable f)
      have hfin : eLpNorm (f : EuclideanSpace ℝ (Fin d) → ℝ) 2 (volume.restrict Ω)
          * (volume.restrict Ω) Set.univ ^ (1 / (q : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)
          ≠ ⊤ :=
        ENNReal.mul_ne_top (Lp.memLp f).eLpNorm_ne_top
          (ENNReal.rpow_ne_top_of_nonneg he (measure_ne_top _ _))
      calc (eLpNorm (f : EuclideanSpace ℝ (Fin d) → ℝ) (q : ℝ≥0∞) (volume.restrict Ω)).toReal
          ≤ (eLpNorm (f : EuclideanSpace ℝ (Fin d) → ℝ) 2 (volume.restrict Ω)
              * (volume.restrict Ω) Set.univ
                ^ (1 / (q : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)).toReal :=
            ENNReal.toReal_mono hfin hb
        _ = ((volume.restrict Ω) Set.univ).toReal
              ^ (1 / (q : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)
            * (eLpNorm (f : EuclideanSpace ℝ (Fin d) → ℝ) 2 (volume.restrict Ω)).toReal := by
            rw [ENNReal.toReal_mul, ENNReal.toReal_rpow, mul_comm])

/-- **Compactness at every exponent up to `2`.** Below the `L²` exponent the embedding factors
through `embL2`, the finite measure supplying the inclusion, so compactness is inherited rather
than interpolated. Together with `rellichEmbL_isCompact` this covers Guo's range `1 ≤ q < 2⋆`. -/
theorem rellichEmbL_isCompact_of_le (hΩm : MeasurableSet Ω) (hΩb : IsBounded Ω) (hd : 2 < d)
    (hq : ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) (hq2 : (q : ℝ≥0∞) ≤ 2) :
    IsCompactOperator (rellichEmbL hΩm hΩb hd hq) := by
  have : IsFiniteMeasure (volume.restrict Ω) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact hΩb.measure_lt_top
  have hfun : ⇑(rellichEmbL hΩm hΩb hd hq) = ⇑(lqOfL2 (Ω := Ω) hq2) ∘ ⇑(embL2 Ω) := by
    funext U
    rw [Function.comp_apply, embL2_apply]
    exact MemLp.toLp_congr
      (memLp_of_mem_H01 (eLpNorm_le_of_mem_H01_of_isBounded hΩm hΩb hd hq U.2))
      ((Lp.memLp ((U : H1amb Ω) 0)).mono_exponent hq2) Filter.EventuallyEq.rfl
  rw [hfun]
  exact (embL2_isCompact hΩm hΩb).clm_comp (lqOfL2 (Ω := Ω) hq2)

/-- **Rellich-Kondrachov in Guo's range.** On a bounded measurable domain in dimension greater than
two, the embedding `H₀¹(Ω) ↪ L^q(Ω)` is compact at every exponent `q` strictly below the Sobolev
conjugate `2⋆`.

The two halves are proved differently: up to `2` the embedding factors through `embL2`, and above
it the `L²` net is refined by interpolation. The interpolation parameter of the second half is
recovered here from `q < 2⋆` rather than assumed. -/
theorem rellichEmbL_isCompact_of_lt (hΩm : MeasurableSet Ω) (hΩb : IsBounded Ω) (hd : 2 < d)
    (hq : ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) (hq0 : q ≠ 0)
    (hp' : (p' : ℝ)⁻¹ = ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹) (hp'0 : p' ≠ 0) (hqlt : q < p') :
    IsCompactOperator (rellichEmbL hΩm hΩb hd hq) := by
  rcases le_or_gt q 2 with hle | hgt
  · exact rellichEmbL_isCompact_of_le hΩm hΩb hd hq (by exact_mod_cast hle)
  -- Above `2` the interpolation parameter is read off the two reciprocals.
  have hd0 : (0 : ℝ) < (d : ℝ) := by positivity
  have hq0' : (0 : ℝ) < (q : ℝ) := by
    have : (0 : ℝ≥0) < q := lt_of_lt_of_le two_pos hgt.le
    exact_mod_cast this
  have hp'0' : (0 : ℝ) < (p' : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hp'0)
  have hba : (p' : ℝ)⁻¹ < ((2 : ℝ≥0) : ℝ)⁻¹ := by
    rw [hp']
    have : (0 : ℝ) < (d : ℝ)⁻¹ := by positivity
    linarith
  have hxb : (p' : ℝ)⁻¹ < (q : ℝ)⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_lt_one_div_of_lt hq0' (by exact_mod_cast hqlt)
  have hxa : (q : ℝ)⁻¹ < ((2 : ℝ≥0) : ℝ)⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_lt_one_div_of_lt (by norm_num) (by exact_mod_cast hgt)
  have hab0 : (0 : ℝ) < ((2 : ℝ≥0) : ℝ)⁻¹ - (p' : ℝ)⁻¹ := by linarith
  refine rellichEmbL_isCompact hΩm hΩb hd hq hq0 hp' hp'0
    (θ := ((q : ℝ)⁻¹ - (p' : ℝ)⁻¹) / (((2 : ℝ≥0) : ℝ)⁻¹ - (p' : ℝ)⁻¹))
    (div_pos (by linarith) hab0) ((div_lt_one hab0).mpr (by linarith)) ?_
  have key : ∀ A B X : ℝ, A - B ≠ 0 →
      X = (X - B) / (A - B) * A + (1 - (X - B) / (A - B)) * B := by
    intro A B X h
    field_simp
    ring
  exact key _ _ _ (ne_of_gt hab0)

end LowExponent

end EllipticPdes.Embedding
