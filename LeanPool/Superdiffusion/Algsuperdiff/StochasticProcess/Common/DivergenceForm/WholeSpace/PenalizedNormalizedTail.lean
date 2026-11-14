/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.PenalizedTail
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.LocalizedTailData

/-!
# PenalizedNormalizedTail

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Shift-normalized tails for exterior penalization

An exterior-penalized equation can be read as a constant-shift equation at
mass `mu + n`.  After multiplication by `mu / (mu + n)`, its zero-trace
solution has the sharp maximum-principle normalization required by the
scale-free resolvent-tail theorem.  The resulting bound is uniform in the
outer cube and decays with `sqrt (mu + n)` away from the data cube.
-/

namespace DivergenceFormProcess.Form

open Filter HCPolySupport MeasureTheory Set Topology
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open MarkovProcess.Semigroup
open scoped ENNReal RealInnerProductSpace

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- Scalar multiplication preserves a scalar-forced weak equation. -/
private theorem isScalarForcedWeakSolution_smul
    {U : Set (Vec d)} {a : CoeffField d} {g : Vec d → ℝ}
    (u : H10Function U) (c : ℝ)
    (hu : IsScalarForcedWeakSolution a U g u.toH1Function) :
    IsScalarForcedWeakSolution a U (fun x ↦ c * g x)
      (c • u).toH1Function := by
  refine ⟨?_, ?_⟩
  · have h := hu.1.const_smul c
    simpa only [Pi.smul_apply, smul_eq_mul] using! h
  · intro phi
    have h := hu.2 phi
    have hflux :
        (∫ x in U, vecDot (matVecMul (a x) ((c • u).toH1Function.grad x))
            (phi.toH1Function.grad x) ∂volume) =
          c * ∫ x in U, vecDot (matVecMul (a x) (u.toH1Function.grad x))
            (phi.toH1Function.grad x) ∂volume := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      change vecDot (matVecMul (a x) (c • u.toH1Function.grad x))
          (phi.toH1Function.grad x) =
        c * vecDot (matVecMul (a x) (u.toH1Function.grad x))
          (phi.toH1Function.grad x)
      rw [matVecMul_smul, vecDot_smul_left]
    have hforce :
        (∫ x in U, (c * g x) * phi.toH1Function.toFun x ∂volume) =
          c * ∫ x in U, g x * phi.toH1Function.toFun x ∂volume := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring
    rw [hflux, hforce, h]

namespace WholeSpaceAnalyticData

variable (A : WholeSpaceAnalyticData d)

/-- Away from the data cube, the local exterior-penalized resolvent satisfies
the localized split-skew tail at the enlarged mass `mu + n`.  The rough and
smooth-divergence constants are read only on the displayed source-free ball. -/
theorem mul_abs_analyticPenalizedCubeResolvent_le_localizedTail
    (L : WholeSpaceLocalizedSplitData A)
    {V : Set (Vec d)} (hV : IsOpen V) (n : ℕ) (mu : PositiveShift)
    {f : Vec d → ℝ} (hf : Measurable f) (hf1 : ∀ x, |f x| ≤ 1)
    (hfsupp : ∀ᵐ x ∂volume, x ∉ V → f x = 0)
    (m : ℕ) {x : Vec d} {r : ℝ}
    (hr : 0 < r) (hball : euclideanBall x r ⊆ wholeSpaceCube d m)
    (hdisjoint : Disjoint (euclideanBall x r) V) :
    (mu : ℝ) * |A.analyticPenalizedCubeResolvent hV n mu f hf hf1 m x| ≤
      L.tail ⟨(mu : ℝ) + n, Set.mem_Ioi.mpr
        (add_pos_of_pos_of_nonneg mu.property (Nat.cast_nonneg n))⟩ x r := by
  let hU := isOpenBoundedConvexDomain_wholeSpaceCube d m
  let mass : ℝ := (mu : ℝ) + n
  have hmass : 0 < mass := add_pos_of_pos_of_nonneg mu.property (Nat.cast_nonneg n)
  have hmu0 : (mu : ℝ) ≠ 0 := ne_of_gt (show 0 < (mu : ℝ) from mu.property)
  let massShift : PositiveShift := ⟨mass, Set.mem_Ioi.mpr hmass⟩
  let c : ℝ := (mu : ℝ) / mass
  have hc : 0 < c := div_pos mu.property hmass
  let F : ScalarL2 (wholeSpaceCube d m) :=
    boundedMeasurableToScalarL2 hU (hf.comp measurable_subtype_coe)
      (fun y ↦ hf1 y)
  let z := A.penalizedCubeResolventH10 hV n mu hf hf1 m
  let z' : H10Function (wholeSpaceCube d m) := c • z
  let g : Vec d → ℝ := fun y ↦ c *
    (F y + n * V.indicator (fun _ ↦ (1 : ℝ)) y * z.toH1Function.toFun y)
  have hz := A.penalizedCubeResolventH10_isScalarForcedWeakSolution
    hV n mu hf hf1 m
  have hzscaled := isScalarForcedWeakSolution_smul z c hz
  have hforcing : (fun y ↦ c *
      (F y - ((mu : ℝ) + wholeSpacePenalizationPotential V n y) *
        z.toH1Function.toFun y)) =
      fun y ↦ g y - mass * z'.toH1Function.toFun y := by
    funext y
    classical
    change c * (F y - ((mu : ℝ) + wholeSpacePenalizationPotential V n y) *
        z.toH1Function.toFun y) =
      c * (F y + n * V.indicator (fun _ ↦ (1 : ℝ)) y *
        z.toH1Function.toFun y) - mass * (c * z.toH1Function.toFun y)
    by_cases hy : y ∈ V
    · rw [wholeSpacePenalizationPotential_eq_zero n hy,
        Set.indicator_of_mem hy]
      dsimp only [mass]
      ring
    · have hyc : y ∈ Vᶜ := hy
      rw [wholeSpacePenalizationPotential, Set.indicator_of_mem hyc,
        Set.indicator_of_notMem hy]
      change c * (F y - ((mu : ℝ) + n) * z.toH1Function.toFun y) =
        c * (F y + n * 0 * z.toH1Function.toFun y) -
          mass * (c * z.toH1Function.toFun y)
      dsimp only [mass]
      ring
  have hz' : IsScalarForcedWeakSolution A.a (wholeSpaceCube d m)
      (fun y ↦ g y - mass * z'.toH1Function.toFun y) z'.toH1Function := by
    rw [← hforcing]
    exact hzscaled
  have hzBound := A.penalizedCubeResolventH10_abs_le hV n mu hf
    (by norm_num) hf1 m
  have hz'Bound : ∀ᵐ y ∂volumeMeasureOn (wholeSpaceCube d m),
      |z'.toH1Function.toFun y| ≤ 1 / mass := by
    filter_upwards [hzBound] with y hy
    change |c * z.toH1Function.toFun y| ≤ 1 / mass
    rw [abs_mul, abs_of_pos hc]
    calc
      c * |z.toH1Function.toFun y| ≤ c * (1 / (mu : ℝ)) :=
        mul_le_mul_of_nonneg_left hy hc.le
      _ = 1 / mass := by
        dsimp only [c]
        field_simp [hmu0, ne_of_gt hmass]
  have hFcoe := boundedMeasurableToScalarL2_coeFn hU
    (hf.comp measurable_subtype_coe) (fun y ↦ hf1 y)
  have hFball := ae_restrict_of_ae_restrict_of_subset hball hFcoe
  have hFball' : ∀ᵐ y ∂volume,
      y ∈ euclideanBall x r → F y = f y := by
    have h := (ae_restrict_iff'
      (isOpen_euclideanBall x r).measurableSet).1 hFball
    filter_upwards [h] with y hy hyball
    rw [hy hyball, domainExtension_of_mem (hball hyball)]
    rfl
  have hgzero : ∀ᵐ y ∂volume,
      y ∈ euclideanBall x r → g y = 0 := by
    filter_upwards [hFball', hfsupp] with y hFy hfy0 hyball
    have hyV : y ∉ V := fun hyMem ↦ Set.disjoint_left.1 hdisjoint hyball hyMem
    change c * (F y + n * V.indicator (fun _ ↦ (1 : ℝ)) y *
      z.toH1Function.toFun y) = 0
    rw [hFy hyball, hfy0 hyV, Set.indicator_of_notMem hyV]
    ring
  let r₀ := L.clippedFreezingRadius x r
  have hr₀ : 0 < r₀ := L.clippedFreezingRadius_pos x hr
  have hr₀r : r₀ ≤ r / 2 := L.clippedFreezingRadius_le_half x r
  have hsmallBall : euclideanBall x (r₀ / 2) ⊆ wholeSpaceCube d m :=
    (Algsuperdiff.Section4.Provider.Schauder.euclideanBall_mono
      (by positivity : 0 ≤ r₀ / 2)
      (show r₀ / 2 ≤ r by
        calc
          r₀ / 2 ≤ (r / 2) / 2 := by gcongr
          _ ≤ r := by linarith only [hr])).trans hball
  have hrepCont : ContinuousOn
      (fun y ↦ c * A.analyticPenalizedCubeResolvent hV n mu f hf hf1 m y)
      (euclideanBall x (r₀ / 2)) := by
    exact continuousOn_const.mul
      ((A.continuousOn_analyticPenalizedCubeResolvent hV n mu hf hf1 m).mono
        hsmallBall)
  have hrepAe : (fun y ↦ c *
      A.analyticPenalizedCubeResolvent hV n mu f hf hf1 m y) =ᵐ[
        volume.restrict (euclideanBall x (r₀ / 2))] z'.toH1Function.toFun := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsmallBall
        (A.analyticPenalizedCubeResolvent_ae hV n mu hf hf1 m),
      ae_restrict_of_ae_restrict_of_subset hsmallBall
        z.toH1Function.coeFn_toScalarL2] with y hrep hzcoe
    have hvalue : z.toH1Function.toScalarL2 y =
        potentialResolvent A.a mu.property A.hnu (A.cubeEllipticity m)
          (wholeSpacePenalizationPotential V n)
          (wholeSpacePenalizationPotential_isBounded hV n m) F y := by
      simpa only [z, F, hU] using congrArg
        (fun w : ScalarL2 (wholeSpaceCube d m) ↦ w y)
        (A.penalizedCubeResolventH10_value hV n mu hf hf1 m)
    rw [hrep, ← hvalue, hzcoe]
    rfl
  have htail := Decay.resolventTail_localized_representative hU.isOpen
    hU.isBoundedDomain A.hd L.holderExponent_mem L.delta_nonneg L.delta_le
    A.hnu (L.roughBound_nonneg x r hr.le)
    (L.smoothDivBound_nonneg x r hr.le) hmass A.hameas
    (L.roughEllipticity m) L.split L.ksSkew L.klSkew L.klContDiff hz'
    hz'Bound hr hr₀ hr₀r hball (L.roughBound_spec x r hr.le)
    (L.smoothDivBound_spec x r hr.le) (L.smallContrast_clipped x hr)
    hgzero hrepCont hrepAe
  change mass * |c * A.analyticPenalizedCubeResolvent hV n mu f hf hf1 m x| ≤ _
    at htail
  have hmassc : mass * c = (mu : ℝ) := by
    dsimp only [c]
    field_simp [ne_of_gt hmass]
  rw [abs_mul, abs_of_pos hc, ← mul_assoc, hmassc] at htail
  simpa only [WholeSpaceLocalizedSplitData.tail, massShift, mass, r₀] using htail

end WholeSpaceAnalyticData

end

end DivergenceFormProcess.Form
