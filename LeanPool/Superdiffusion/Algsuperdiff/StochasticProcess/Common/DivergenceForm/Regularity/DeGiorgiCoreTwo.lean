/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Sobolev.CubeEmbedding.LimitFiniteP
public import LeanPool.HighContrastHomogenization.Support.Sobolev.W1p.FiniteMeasureDowngrade
public import LeanPool.Superdiffusion.Support.Sobolev.MatchedPair.Core

/-!
# DeGiorgiCoreTwo

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The two-dimensional Sobolev input for De Giorgi iteration

In dimension two the critical `H¹` Sobolev exponent is infinite, so the
`d ≥ 3` cube embedding used by the pinned De Giorgi core is unavailable.  This
file uses the finite-exponent route instead: first lower `H¹` to `W¹,⁴⁄³` on
the finite square and then apply the pinned finite-`p` cube embedding into
`L⁴`.  The resulting factor is `L¹⁄²`, as required by scaling.
-/

namespace DivergenceFormProcess.Regularity

open HCPolySupport MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- The finite exponent `4 / 3` used in the De Giorgi iteration. -/
noncomputable def fourThirds : FiniteLpExponent where
  exponent := ENNReal.ofReal (4 / 3 : ℝ)
  one_lt := by
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_lt_ofReal_iff]
    · norm_num
    · positivity
  lt_top := ENNReal.ofReal_lt_top

/-- The finite exponent `4` used in the De Giorgi iteration. -/
noncomputable def four : FiniteLpExponent where
  exponent := 4
  one_lt := by norm_num
  lt_top := by norm_num

private theorem fourThirds_le_two : fourThirds.exponent ≤ 2 := by
  rw [fourThirds, ← ENNReal.ofReal_ofNat]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

private theorem fourThirds_toReal : fourThirds.exponent.toReal = 4 / 3 := by
  rw [fourThirds, ENNReal.toReal_ofReal (by norm_num)]

private theorem four_toReal : four.exponent.toReal = 4 := by
  norm_num [four]

private theorem four_sobolev_relation :
    (four.exponent.toReal)⁻¹ =
      (fourThirds.exponent.toReal)⁻¹ - ((2 : ℕ) : ℝ)⁻¹ := by
  rw [four_toReal, fourThirds_toReal]
  norm_num

private theorem squareDowngradeFactor_eq_sqrt (z : Vec 2) {L : ℝ} (hL : 0 < L) :
    ((volumeMeasureOn (axisCube z L)) Set.univ ^
      (1 / fourThirds.exponent.toReal - 1 / (2 : ℝ≥0∞).toReal)).toReal =
      Real.sqrt L := by
  have hab : (z : Vec 2) ≤ fun i => z i + L :=
    fun _ => le_add_of_nonneg_right hL.le
  have hvol : (volume (axisCube z L)).toReal = L ^ (2 : ℕ) := by
    rw [axisCube, Real.volume_pi_Ioo_toReal hab,
      show (fun i => (z i + L) - z i) = (fun _ : Fin 2 => L) from by
        funext i
        ring,
      Finset.prod_const]
    norm_num
  rw [Measure.restrict_apply_univ, ← ENNReal.toReal_rpow, hvol, fourThirds_toReal]
  · norm_num
    rw [← Real.rpow_natCast L 2, ← Real.rpow_mul hL.le]
    norm_num [← Real.sqrt_eq_rpow]

/-- The two-dimensional square Sobolev embedding `H¹ ↪ L⁴`, obtained through
the finite-exponent `W¹,⁴⁄³ ↪ L⁴` embedding.  The right side is left in its
natural `L⁴⁄³` form; the finite-measure comparison to `L²` is performed in the
next analytic step, where its scale factor is used exactly once. -/
theorem cube_sobolev_embedding_two :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (z : Vec 2) (L : ℝ), 0 < L → ∀ u : H1Function (axisCube z L),
        eLpNorm u.toFun 4 (volumeMeasureOn (axisCube z L)) ≤
          (C : ℝ≥0∞) *
            ((∑ i : Fin 2,
                eLpNorm (fun x => u.grad x i) (ENNReal.ofReal (4 / 3 : ℝ))
                  (volumeMeasureOn (axisCube z L))) +
              ENNReal.ofReal L⁻¹ *
                eLpNorm u.toFun (ENNReal.ofReal (4 / 3 : ℝ))
                  (volumeMeasureOn (axisCube z L))) := by
  obtain ⟨C, hC, hEmb⟩ :=
    cubeSobolevEmbedding_finiteLp (d := 2) (by omega) fourThirds
      (by rw [fourThirds_toReal]; norm_num)
  refine ⟨C, hC, ?_⟩
  intro z L hL u
  have : IsFiniteMeasure (volumeMeasureOn (axisCube z L)) :=
    (isOpenBoundedConvexDomain_axisCube z L).isFiniteMeasure_restrict_volume
  have h := hEmb four four_sobolev_relation z L hL
    (u.toW1pOfExponentLETwo fourThirds fourThirds_le_two)
  simpa only [four, fourThirds, H1Function.toW1pOfExponentLETwo_toFun,
    H1Function.toW1pOfExponentLETwo_grad] using! h

/-- The two-dimensional matched-pair Sobolev inequality.  The scale factor is
written as the exact finite-measure downgrade factor `|U|^(1/4)`; on a square
of side `L` this is `sqrt L`. -/
theorem matchedPair_sobolev_two :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (z : Vec 2) (L : ℝ), 0 < L →
        ∀ (f g : H1Function (axisCube z L)),
          Measurable f.toFun → Measurable g.toFun →
          MemH10 (axisCube z L) (fun x => f.toFun x - g.toFun x) →
          volume {x | x ∈ axisCube z L ∧ f.toFun x ≠ 0} +
              volume {x | x ∈ axisCube z L ∧ g.toFun x ≠ 0} ≤
            volume (axisCube z L) →
          (eLpNorm f.toFun 4 (volumeMeasureOn (axisCube z L))).toReal +
              (eLpNorm g.toFun 4 (volumeMeasureOn (axisCube z L))).toReal ≤
            C *
              ((volumeMeasureOn (axisCube z L)) Set.univ ^
                (1 / fourThirds.exponent.toReal -
                  1 / (2 : ℝ≥0∞).toReal)).toReal *
              ((∑ i : Fin 2,
                  (eLpNorm (fun x => f.grad x i) 2
                    (volumeMeasureOn (axisCube z L))).toReal) +
                ∑ i : Fin 2,
                  (eLpNorm (fun x => g.grad x i) 2
                    (volumeMeasureOn (axisCube z L))).toReal) := by
  let : NeZero 2 := ⟨by omega⟩
  obtain ⟨CE, hCEpos, hEmb⟩ := cube_sobolev_embedding_two
  let C : ℝ := (CE : ℝ) * (1 + matchedPairPoincareConst 2)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (le_of_lt hCEpos) (add_nonneg zero_le_one
      (matchedPairPoincareConst_nonneg 2))
  refine ⟨C, hC, ?_⟩
  intro z L hL f g hfm hgm hfg hzero
  have : IsFiniteMeasure (volumeMeasureOn (axisCube z L)) :=
    (isOpenBoundedConvexDomain_axisCube z L).isFiniteMeasure_restrict_volume
  let F : ℝ :=
    ((volumeMeasureOn (axisCube z L)) Set.univ ^
      (1 / fourThirds.exponent.toReal - 1 / (2 : ℝ≥0∞).toReal)).toReal
  have hF : 0 ≤ F := ENNReal.toReal_nonneg
  have hpow_ne :
      (volumeMeasureOn (axisCube z L)) Set.univ ^
          (1 / fourThirds.exponent.toReal - 1 / (2 : ℝ≥0∞).toReal) ≠ ∞ := by
    apply ENNReal.rpow_ne_top_of_nonneg
    · rw [fourThirds_toReal]
      norm_num
    · exact (measure_lt_top (volumeMeasureOn (axisCube z L)) Set.univ).ne
  have downgrade (v : Vec 2 → ℝ)
      (hv : AEStronglyMeasurable v (volumeMeasureOn (axisCube z L)))
      (hv2 : MemLp v 2 (volumeMeasureOn (axisCube z L))) :
      (eLpNorm v fourThirds.exponent
          (volumeMeasureOn (axisCube z L))).toReal ≤
        (eLpNorm v 2 (volumeMeasureOn (axisCube z L))).toReal * F := by
    have h := eLpNorm_finiteMeasure_downgrade_le
      fourThirds fourThirds_le_two v hv
    have htwo_ne : eLpNorm v 2 (volumeMeasureOn (axisCube z L)) ≠ ∞ :=
      hv2.eLpNorm_lt_top.ne
    calc
      (eLpNorm v fourThirds.exponent
          (volumeMeasureOn (axisCube z L))).toReal ≤
          (eLpNorm v 2 (volumeMeasureOn (axisCube z L)) *
            (volumeMeasureOn (axisCube z L)) Set.univ ^
              (1 / fourThirds.exponent.toReal -
                1 / (2 : ℝ≥0∞).toReal)).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top htwo_ne hpow_ne) h
      _ = (eLpNorm v 2 (volumeMeasureOn (axisCube z L))).toReal * F := by
        rw [ENNReal.toReal_mul]
  have e1real (u : H1Function (axisCube z L)) :
      (eLpNorm u.toFun 4 (volumeMeasureOn (axisCube z L))).toReal ≤
        (CE : ℝ) * F *
          ((∑ i : Fin 2,
              (eLpNorm (fun x => u.grad x i) 2
                (volumeMeasureOn (axisCube z L))).toReal) +
            L⁻¹ *
              (eLpNorm u.toFun 2
                (volumeMeasureOn (axisCube z L))).toReal) := by
    have hEu := hEmb z L hL u
    have hgrad_ne : ∀ i : Fin 2,
        eLpNorm (fun x => u.grad x i) (ENNReal.ofReal (4 / 3 : ℝ))
          (volumeMeasureOn (axisCube z L)) ≠ ∞ :=
      fun i => (u.gradMemL2 i).mono_exponent fourThirds_le_two |>.eLpNorm_lt_top.ne
    have hval_ne :
        eLpNorm u.toFun (ENNReal.ofReal (4 / 3 : ℝ))
          (volumeMeasureOn (axisCube z L)) ≠ ∞ :=
      (u.memL2.mono_exponent fourThirds_le_two).eLpNorm_lt_top.ne
    have hrhs_ne :
        (CE : ℝ≥0∞) *
          ((∑ i : Fin 2,
              eLpNorm (fun x => u.grad x i) (ENNReal.ofReal (4 / 3 : ℝ))
                (volumeMeasureOn (axisCube z L))) +
            ENNReal.ofReal L⁻¹ *
              eLpNorm u.toFun (ENNReal.ofReal (4 / 3 : ℝ))
                (volumeMeasureOn (axisCube z L))) ≠ ∞ :=
      ENNReal.mul_ne_top ENNReal.coe_ne_top
        (ENNReal.add_ne_top.2
          ⟨(ENNReal.sum_lt_top.2 fun i _ => (hgrad_ne i).lt_top).ne,
            ENNReal.mul_ne_top ENNReal.ofReal_ne_top hval_ne⟩)
    have hdgrad : ∀ i : Fin 2,
        (eLpNorm (fun x => u.grad x i) fourThirds.exponent
          (volumeMeasureOn (axisCube z L))).toReal ≤
        (eLpNorm (fun x => u.grad x i) 2
          (volumeMeasureOn (axisCube z L))).toReal * F :=
      fun i => downgrade _ (u.gradMemL2 i).aestronglyMeasurable (u.gradMemL2 i)
    have hdval := downgrade u.toFun u.memL2.aestronglyMeasurable u.memL2
    calc
      (eLpNorm u.toFun 4 (volumeMeasureOn (axisCube z L))).toReal ≤
          ((CE : ℝ≥0∞) *
            ((∑ i : Fin 2,
                eLpNorm (fun x => u.grad x i) (ENNReal.ofReal (4 / 3 : ℝ))
                  (volumeMeasureOn (axisCube z L))) +
              ENNReal.ofReal L⁻¹ *
                eLpNorm u.toFun (ENNReal.ofReal (4 / 3 : ℝ))
                  (volumeMeasureOn (axisCube z L)))).toReal :=
        ENNReal.toReal_mono hrhs_ne hEu
      _ = (CE : ℝ) *
          ((∑ i : Fin 2,
              (eLpNorm (fun x => u.grad x i) fourThirds.exponent
                (volumeMeasureOn (axisCube z L))).toReal) +
            L⁻¹ *
              (eLpNorm u.toFun fourThirds.exponent
                (volumeMeasureOn (axisCube z L))).toReal) := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_add,
          ENNReal.toReal_sum, ENNReal.toReal_mul,
          ENNReal.toReal_ofReal (by positivity), ENNReal.coe_toReal]
        · rfl
        · exact fun i _ => hgrad_ne i
        · exact (ENNReal.sum_lt_top.2 fun i _ => (hgrad_ne i).lt_top).ne
        · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hval_ne
      _ ≤ (CE : ℝ) *
          ((∑ i : Fin 2,
              (eLpNorm (fun x => u.grad x i) 2
                (volumeMeasureOn (axisCube z L))).toReal * F) +
            L⁻¹ *
              ((eLpNorm u.toFun 2
                (volumeMeasureOn (axisCube z L))).toReal * F)) := by
        exact mul_le_mul_of_nonneg_left
          (add_le_add (Finset.sum_le_sum fun i _ => hdgrad i)
            (mul_le_mul_of_nonneg_left hdval (by positivity)))
          (by positivity)
      _ = (CE : ℝ) * F *
          ((∑ i : Fin 2,
              (eLpNorm (fun x => u.grad x i) 2
                (volumeMeasureOn (axisCube z L))).toReal) +
            L⁻¹ *
              (eLpNorm u.toFun 2
                (volumeMeasureOn (axisCube z L))).toReal) := by
        rw [← Finset.sum_mul]
        ring
  have hEf := e1real f
  have hEg := e1real g
  have hP := matchedPair_poincare z hL f g hfm hgm hfg hzero
  rw [norm_toScalarL2_eq, norm_toScalarL2_eq,
    gradientCoordL2NormSum_eq_sum_eLpNorm f,
    gradientCoordL2NormSum_eq_sum_eLpNorm g] at hP
  set Gf := ∑ i : Fin 2,
    (eLpNorm (fun x => f.grad x i) 2
      (volumeMeasureOn (axisCube z L))).toReal with hGf
  set Gg := ∑ i : Fin 2,
    (eLpNorm (fun x => g.grad x i) 2
      (volumeMeasureOn (axisCube z L))).toReal with hGg
  set nf := (eLpNorm f.toFun 2 (volumeMeasureOn (axisCube z L))).toReal with hnf
  set ng := (eLpNorm g.toFun 2 (volumeMeasureOn (axisCube z L))).toReal with hng
  have hstep : L⁻¹ * (nf + ng) ≤ matchedPairPoincareConst 2 * (Gf + Gg) := by
    have hmul := mul_le_mul_of_nonneg_left hP (inv_nonneg.mpr hL.le)
    calc
      L⁻¹ * (nf + ng) ≤
          L⁻¹ * (matchedPairPoincareConst 2 * L * (Gf + Gg)) := hmul
      _ = matchedPairPoincareConst 2 * (Gf + Gg) := by
        rw [show matchedPairPoincareConst 2 * L * (Gf + Gg) =
          L * (matchedPairPoincareConst 2 * (Gf + Gg)) by ring,
          ← mul_assoc, inv_mul_cancel₀ hL.ne', one_mul]
  calc
    (eLpNorm f.toFun 4 (volumeMeasureOn (axisCube z L))).toReal +
        (eLpNorm g.toFun 4 (volumeMeasureOn (axisCube z L))).toReal ≤
      (CE : ℝ) * F * (Gf + L⁻¹ * nf) +
        (CE : ℝ) * F * (Gg + L⁻¹ * ng) := add_le_add hEf hEg
    _ = (CE : ℝ) * F * ((Gf + Gg) + L⁻¹ * (nf + ng)) := by ring
    _ ≤ (CE : ℝ) * F *
        ((Gf + Gg) + matchedPairPoincareConst 2 * (Gf + Gg)) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add_right hstep (Gf + Gg)) (mul_nonneg (by positivity) hF)
    _ = C * F * (Gf + Gg) := by
      dsimp [C]
      ring

/-- The two-dimensional matched-pair Sobolev inequality in its scale-normalized
form.  This is the analytic input used by the two-dimensional level recurrence. -/
theorem matchedPair_sobolev_two_sqrt :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (z : Vec 2) (L : ℝ), 0 < L →
        ∀ (f g : H1Function (axisCube z L)),
          Measurable f.toFun → Measurable g.toFun →
          MemH10 (axisCube z L) (fun x => f.toFun x - g.toFun x) →
          volume {x | x ∈ axisCube z L ∧ f.toFun x ≠ 0} +
              volume {x | x ∈ axisCube z L ∧ g.toFun x ≠ 0} ≤
            volume (axisCube z L) →
          (eLpNorm f.toFun 4 (volumeMeasureOn (axisCube z L))).toReal +
              (eLpNorm g.toFun 4 (volumeMeasureOn (axisCube z L))).toReal ≤
            C * Real.sqrt L *
              ((∑ i : Fin 2,
                  (eLpNorm (fun x => f.grad x i) 2
                    (volumeMeasureOn (axisCube z L))).toReal) +
                ∑ i : Fin 2,
                  (eLpNorm (fun x => g.grad x i) 2
                    (volumeMeasureOn (axisCube z L))).toReal) := by
  obtain ⟨C, hC, h⟩ := matchedPair_sobolev_two
  refine ⟨C, hC, ?_⟩
  intro z L hL f g hfm hgm hfg hzero
  rw [← squareDowngradeFactor_eq_sqrt z hL]
  exact h z L hL f g hfm hgm hfg hzero

end

end DivergenceFormProcess.Regularity
