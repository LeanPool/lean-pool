/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Embedding.RellichLq
public import LeanPool.EllipticPDE.Embedding.SobolevSharp
public import LeanPool.EllipticPDE.Analysis.WeakCompactness
public import LeanPool.EllipticPDE.Analysis.LqEulerLagrange


/-!
# Direct method under a subcritical constraint

Minimising the `H₀¹` norm over the functions of unit `L^q(Ω)` norm has a solution when
`q < 2⋆`. This is the direct method of the calculus of variations, and it is where the two
halves of the compactness chapter meet: `EllipticPdes.Analysis.exists_weakLimit` supplies a
weak limit of a minimising sequence, and
`EllipticPdes.Embedding.rellichEmbL_isCompact_of_lt` supplies the strong `L^q` convergence
that takes the constraint to that limit.

At `q = 2⋆` the second half fails, which `EllipticPdes.Embedding.not_isCompactOperator_critEmb`
records, and the minimum need not be attained. That is the exponent restriction Guo writes as
`p + 1 < 2⋆` for the semilinear problem `-Δu = u^p`, whose Euler-Lagrange equation this
minimiser solves once the constraint is differentiated.

## Main declarations

* `EllipticPdes.Embedding.exists_minimiser_of_lt`: the minimiser exists.
* `EllipticPdes.Embedding.exists_weakSolution_semilinear_of_lt`: it solves the equation.

## References

Y. Guo, *Partial Differential Equations*, Section IX.1; L. C. Evans, *Partial Differential
Equations* (2nd ed.), §8.2.
-/

@[expose] public section

open MeasureTheory Metric Filter Topology Bornology
open scoped NNReal ENNReal RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Embedding

open EllipticPdes.Sobolev EllipticPdes.Analysis

variable {d : ℕ} {p' q : ℝ≥0}

section

variable [Fact (1 ≤ (q : ℝ≥0∞))]

/-- The unit ball of `ℝ^d`, where the argument runs. -/
local notation "B1" => ball (0 : EuclideanSpace ℝ (Fin d)) 1

/-- The `L^q` seminorm of a graph coordinate is the seminorm of the function it represents. -/
private lemma norm_rellichEmbL_eq (hΩb : IsBounded (ball (0 : EuclideanSpace ℝ (Fin d)) 1))
    (hd : 2 < d) (hq : ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) (U : H01 B1) :
    ‖rellichEmbL measurableSet_ball hΩb hd hq U‖
      = (eLpNorm (((U : H1amb B1)) 0) (q : ℝ≥0∞) (volume.restrict B1)).toReal := by
  have hcoe : ⇑(rellichEmbL measurableSet_ball hΩb hd hq U)
      =ᵐ[volume.restrict B1] ⇑((U : H1amb B1) 0) := coeFn_sobolevEmbL _ U
  rw [Lp.norm_def, eLpNorm_congr_ae hcoe]

/-- **Direct method.** Below the critical exponent the `H₀¹` norm attains its minimum on the
functions of unit `L^q` norm. -/
theorem exists_minimiser_of_lt (hΩb : IsBounded (ball (0 : EuclideanSpace ℝ (Fin d)) 1))
    (hd : 2 < d) (hq : ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) (hq0 : q ≠ 0)
    (hp' : (p' : ℝ)⁻¹ = ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹) (hp'0 : p' ≠ 0) (hqlt : q < p')
    (hq2 : (2 : ℝ≥0) ≤ q)
    (hne : ∃ V : H01 B1, ‖rellichEmbL measurableSet_ball hΩb hd hq V‖ = 1) :
    ∃ U : H01 B1, ‖rellichEmbL measurableSet_ball hΩb hd hq U‖ = 1 ∧
      ∀ V : H01 B1, ‖rellichEmbL measurableSet_ball hΩb hd hq V‖ = 1 → ‖U‖ ≤ ‖V‖ := by
  set T := rellichEmbL measurableSet_ball hΩb hd hq with hTdef
  set C : Set (H01 B1) := {U | ‖T U‖ = 1} with hCdef
  set E : Set ℝ := (fun U : H01 B1 => ‖U‖) '' C with hEdef
  have hEne : E.Nonempty := by
    obtain ⟨V, hV⟩ := hne
    exact ⟨‖V‖, V, hV, rfl⟩
  have hEbdd : BddBelow E := ⟨0, by rintro _ ⟨V, -, rfl⟩; exact norm_nonneg _⟩
  set m : ℝ := sInf E with hmdef
  have hm0 : 0 ≤ m := le_csInf hEne (by rintro _ ⟨V, -, rfl⟩; exact norm_nonneg _)
  -- A minimising sequence.
  have hchoice : ∀ n : ℕ, ∃ U : H01 B1, ‖T U‖ = 1 ∧ ‖U‖ < m + 1 / (n + 1) := by
    intro n
    have hlt : m < m + 1 / ((n : ℝ) + 1) := by
      have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    obtain ⟨r, hrE, hr⟩ := exists_lt_of_csInf_lt hEne hlt
    obtain ⟨U, hU, rfl⟩ := hrE
    exact ⟨U, hU, hr⟩
  choose U hUC hUlt using hchoice
  have hUbound : ∀ n, ‖U n‖ ≤ m + 1 := by
    intro n
    have h1 : (1 : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    linarith [hUlt n]
  have hUnorm : Tendsto (fun n => ‖U n‖) atTop (𝓝 m) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le (g := fun _ : ℕ => m)
      (h := fun n => m + 1 / ((n : ℝ) + 1)) tendsto_const_nhds ?_ ?_ ?_
    · have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      simpa using tendsto_const_nhds.add this
    · intro n
      exact le_csInf hEne (by rintro _ ⟨V, hV, rfl⟩; exact csInf_le hEbdd ⟨V, hV, rfl⟩) |>.trans
        (le_of_eq rfl) |>.trans (csInf_le hEbdd ⟨U n, hUC n, rfl⟩)
    · exact fun n => (hUlt n).le
  -- Weak compactness gives a limit, and it stays in `H₀¹`.
  obtain ⟨w, φ, hφ, hweak⟩ :=
    exists_weakLimit (u := fun n => ((U n : H01 B1) : H1amb B1)) (M := m + 1) hUbound
  have hwH01 : w ∈ H01 B1 :=
    mem_of_weakLimit (Submodule.isClosed_topologicalClosure _) (fun k => (U (φ k)).2) hweak
  have hwnorm : ‖w‖ ≤ m :=
    norm_weakLimit_le_of_tendsto (hUnorm.comp hφ.tendsto_atTop) hweak
  -- Rellich gives a further subsequence converging strongly in `L^q`.
  have hm1 : (0 : ℝ) < m + 1 := by linarith
  have hTL : IsCompactOperator (T.toLinearMap) :=
    rellichEmbL_isCompact_of_lt measurableSet_ball hΩb hd hq hq0 hp' hp'0 hqlt
  have hcl := (isCompactOperator_iff_isCompact_closure_image_closedBall T.toLinearMap hm1).mp hTL
  have hmemcl : ∀ k, T (U (φ k)) ∈ closure (⇑T.toLinearMap '' closedBall (0 : H01 B1) (m + 1)) :=
    fun k => subset_closure ⟨U (φ k), by
      simpa [mem_closedBall, dist_zero_right] using hUbound (φ k), rfl⟩
  obtain ⟨z, -, ψ, hψ, hψtend⟩ := hcl.tendsto_subseq hmemcl
  -- The strong limit has norm one.
  have hznorm : ‖z‖ = 1 := by
    have h1 : Tendsto (fun j => ‖T (U (φ (ψ j)))‖) atTop (𝓝 ‖z‖) := by
      have hc := (continuous_norm.tendsto z).comp hψtend
      simpa [Function.comp_def] using hc
    have h2 : Tendsto (fun j => ‖T (U (φ (ψ j)))‖) atTop (𝓝 1) := by
      simp only [hUC]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  -- It is the function coordinate of the weak limit.
  have : IsFiniteMeasure (volume.restrict (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  have h2q : (2 : ℝ≥0∞) ≤ (q : ℝ≥0∞) := by exact_mod_cast hq2
  have hz2 : MemLp (⇑z) 2 (volume.restrict B1) := (Lp.memLp z).mono_exponent h2q
  set z2 : L2D B1 := hz2.toLp _ with hz2def
  have hz2coe : ⇑z2 =ᵐ[volume.restrict B1] ⇑z := hz2.coeFn_toLp
  have hL2conv : Tendsto (fun j => ‖((U (φ (ψ j)) : H01 B1) : H1amb B1) 0 - z2‖) atTop (𝓝 0) := by
    have hbnd : ∀ j, ‖((U (φ (ψ j)) : H01 B1) : H1amb B1) 0 - z2‖
        ≤ ((volume.restrict B1) Set.univ ^ (1 / (2 : ℝ≥0∞).toReal - 1 / ((q : ℝ≥0∞)).toReal)).toReal
          * ‖T (U (φ (ψ j))) - z‖ := by
      intro j
      have hTcoe : ⇑(T (U (φ (ψ j))))
          =ᵐ[volume.restrict B1] ⇑(((U (φ (ψ j)) : H01 B1) : H1amb B1) 0) :=
        coeFn_sobolevEmbL _ (U (φ (ψ j)))
      have hcoe : ⇑(((U (φ (ψ j)) : H01 B1) : H1amb B1) 0 - z2)
          =ᵐ[volume.restrict B1] ⇑(T (U (φ (ψ j))) - z) := by
        filter_upwards [Lp.coeFn_sub (((U (φ (ψ j)) : H01 B1) : H1amb B1) 0) z2,
          Lp.coeFn_sub (T (U (φ (ψ j)))) z, hz2coe, hTcoe] with x h1 h2 h3 h4
        rw [h1, h2, Pi.sub_apply, Pi.sub_apply, h3, h4]
      rw [Lp.norm_def, eLpNorm_congr_ae hcoe, Lp.norm_def]
      rw [← ENNReal.toReal_mul]
      refine ENNReal.toReal_mono ?_ ?_
      · exact ENNReal.mul_ne_top
          (ENNReal.rpow_ne_top_of_nonneg (by
            have h2R : (2 : ℝ≥0∞).toReal = 2 := by simp
            have hqR : ((q : ℝ≥0∞)).toReal = (q : ℝ) := by simp
            have hq2R : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
            rw [h2R, hqR, sub_nonneg]
            exact one_div_le_one_div_of_le (by norm_num) hq2R)
            (by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top.ne))
          (Lp.memLp _).eLpNorm_ne_top
      · rw [mul_comm]
        exact eLpNorm_le_eLpNorm_mul_rpow_measure_univ h2q (Lp.aestronglyMeasurable _)
    have hto : Tendsto (fun j => ‖T (U (φ (ψ j))) - z‖) atTop (𝓝 0) := by
      have hsub : Tendsto (fun j => T (U (φ (ψ j))) - z) atTop
          (𝓝 (0 : Lp ℝ (q : ℝ≥0∞) (volume.restrict B1))) := by
        have h := hψtend.sub (tendsto_const_nhds (x := z))
        simpa [Function.comp_def] using h
      simpa using hsub.norm
    refine squeeze_zero (fun j => norm_nonneg _) hbnd ?_
    simpa using hto.const_mul _
  -- Weak and strong limits of the same subsequence agree.
  have hzw : z2 = ((w : H1amb B1)) 0 := by
    refine ext_inner_right ℝ (fun a => ?_)
    have hstrong : Tendsto
        (fun j => ⟪((U (φ (ψ j)) : H01 B1) : H1amb B1) 0, a⟫) atTop (𝓝 ⟪z2, a⟫) := by
      have hdiff : ∀ j, |⟪((U (φ (ψ j)) : H01 B1) : H1amb B1) 0, a⟫ - ⟪z2, a⟫|
          ≤ ‖((U (φ (ψ j)) : H01 B1) : H1amb B1) 0 - z2‖ * ‖a‖ := by
        intro j
        rw [← inner_sub_left]
        exact abs_real_inner_le_norm _ _
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le
        (g := fun j => ⟪z2, a⟫ - ‖((U (φ (ψ j)) : H01 B1) : H1amb B1) 0 - z2‖ * ‖a‖)
        (h := fun j => ⟪z2, a⟫ + ‖((U (φ (ψ j)) : H01 B1) : H1amb B1) 0 - z2‖ * ‖a‖)
        ?_ ?_ (fun j => by linarith [abs_le.mp (hdiff j)]) (fun j => by
          linarith [abs_le.mp (hdiff j)])
      · simpa using tendsto_const_nhds.sub (hL2conv.mul_const ‖a‖)
      · simpa using tendsto_const_nhds.add (hL2conv.mul_const ‖a‖)
    have hweak0 : Tendsto
        (fun j => ⟪((U (φ (ψ j)) : H01 B1) : H1amb B1) 0, a⟫) atTop (𝓝 ⟪(w : H1amb B1) 0, a⟫) := by
      have hs := (hweak (PiLp.single 2 (0 : Fin (d + 1)) a)).comp hψ.tendsto_atTop
      simp only [Function.comp_def] at hs
      have hrw : ∀ V : H1amb B1, ⟪V, PiLp.single 2 (0 : Fin (d + 1)) a⟫ = ⟪V 0, a⟫ := by
        intro V
        rw [real_inner_comm, inner_single_left, real_inner_comm]
      simpa only [hrw] using hs
    exact tendsto_nhds_unique hstrong hweak0
  refine ⟨⟨w, hwH01⟩, ?_, fun V hV => le_trans hwnorm (csInf_le hEbdd ⟨V, hV, rfl⟩)⟩
  rw [hTdef, norm_rellichEmbL_eq]
  have : eLpNorm (((⟨w, hwH01⟩ : H01 B1) : H1amb B1) 0) (q : ℝ≥0∞) (volume.restrict B1)
      = eLpNorm (⇑z) (q : ℝ≥0∞) (volume.restrict B1) := by
    refine eLpNorm_congr_ae ?_
    rw [← hzw]
    exact hz2coe
  rw [this, ← Lp.norm_def, hznorm]


/-- The constraint set is inhabited: a renormalised bump sits on it. -/
theorem exists_norm_rellichEmbL_eq_one
    (hΩb : IsBounded (ball (0 : EuclideanSpace ℝ (Fin d)) 1)) (hd : 2 < d) (hq0 : q ≠ 0)
    (hq : ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) :
    ∃ V : H01 B1, ‖rellichEmbL measurableSet_ball hΩb hd hq V‖ = 1 := by
  set V0 : H01 B1 := sharpElt d (show (0 : ℝ) < 1 / 2 by norm_num) le_rfl with hV0
  have hfin : eLpNorm (⇑(sharpBump d)) (q : ℝ≥0∞) volume ≠ ⊤ :=
    ((sharpBump d).continuous.memLp_of_hasCompactSupport
      (μ := volume) (p := (q : ℝ≥0∞)) (sharpBump d).hasCompactSupport).eLpNorm_ne_top
  have hne : eLpNorm (⇑(sharpBump d)) (q : ℝ≥0∞) volume ≠ 0 :=
    eLpNorm_sharpBump_ne_zero (by simpa using hq0)
  have hnorm : ‖rellichEmbL measurableSet_ball hΩb hd hq V0‖
      = (ENNReal.ofReal ((1 / 2 : ℝ) ^ (1 - (d : ℝ) / 2 + (d : ℝ) * (1 / ((q : ℝ≥0∞)).toReal)))
          * eLpNorm (⇑(sharpBump d)) (q : ℝ≥0∞) volume).toReal := by
    rw [norm_rellichEmbL_eq, hV0, eLpNorm_sharpElt_zero,
      eLpNorm_sharpFamily (by norm_num) (by simpa using hq0) (by simp)]
  have hpos : 0 < ‖rellichEmbL measurableSet_ball hΩb hd hq V0‖ := by
    rw [hnorm, ENNReal.toReal_pos_iff]
    refine ⟨ENNReal.mul_pos ?_ hne, ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_top_iff_ne_top.mpr hfin)⟩
    exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _)).ne'
  refine ⟨(‖rellichEmbL measurableSet_ball hΩb hd hq V0‖)⁻¹ • V0, ?_⟩
  rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos),
    inv_mul_cancel₀ hpos.ne']

/-- **Minimiser as a weak solution.** Differentiating the constraint through
`EllipticPdes.Analysis.euler_lagrange_of_norm_min` turns the subcritical minimiser into a weak
solution of `-Δu + u = λ|u|^{q-2}u` on the unit ball, with `λ = ‖u‖²_{H₀¹}`: the graph inner
product `⟪U, V⟫` is `∫ uv + ∫ ∇u · ∇v`, so the identity below is the weak form of that equation.
The multiplier is the square of the minimum, so no unknown constant survives. -/
theorem exists_weakSolution_semilinear_of_lt
    (hΩb : IsBounded (ball (0 : EuclideanSpace ℝ (Fin d)) 1))
    (hd : 2 < d) (hq : ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹ ≤ (q : ℝ)⁻¹) (hq0 : q ≠ 0)
    (hp' : (p' : ℝ)⁻¹ = ((2 : ℝ≥0) : ℝ)⁻¹ - (d : ℝ)⁻¹) (hp'0 : p' ≠ 0) (hqlt : q < p')
    (hq2 : (2 : ℝ≥0) ≤ q) :
    ∃ U : H01 B1, ‖rellichEmbL measurableSet_ball hΩb hd hq U‖ = 1 ∧
      ∀ V : H01 B1, ⟪U, V⟫
        = ‖U‖ ^ 2 * ∫ x, |(rellichEmbL measurableSet_ball hΩb hd hq U) x| ^ ((q : ℝ) - 2)
            * (rellichEmbL measurableSet_ball hΩb hd hq U) x
            * (rellichEmbL measurableSet_ball hΩb hd hq V) x ∂(volume.restrict B1) := by
  obtain ⟨U, hU, hmin⟩ := exists_minimiser_of_lt hΩb hd hq hq0 hp' hp'0 hqlt hq2
    (exists_norm_rellichEmbL_eq_one hΩb hd hq0 hq)
  refine ⟨U, hU, fun V => ?_⟩
  have hq2R : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq2
  have hp1 : 1 < ((q : ℝ≥0∞)).toReal := by
    rw [ENNReal.coe_toReal]
    linarith
  have h := euler_lagrange_of_norm_min (p := (q : ℝ≥0∞))
    (by simpa using hq0) ENNReal.coe_ne_top hp1
    (rellichEmbL measurableSet_ball hΩb hd hq) hU hmin V
  simpa using h

end

end EllipticPdes.Embedding
