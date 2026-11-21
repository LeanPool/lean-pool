/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.GibbsSobolev
public import LeanPool.CutoffRigidity.EigenfunctionWeakBochner

/-! # Actual weak derivatives of the closed Gibbs Sobolev gradient

The closed gradient is constructed by closing the actual compact C² graph.
Weighted integration by parts against compact tests passes to that closure
through continuous L² pairings. These are genuine distribution identities;
local Rellich compactness and spectral attainment are separate steps.
-/

public section

namespace CutoffRigidity

open MeasureTheory

variable {d : ℕ}

/-- A compact scalar test times a coordinate vector lies in actual Gibbs L². -/
theorem gibbs_coordinate_test_memLp
    {V ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (i : Fin d) :
    MemLp (fun x => ψ x • EuclideanSpace.single i (1 : ℝ)) 2 (gibbsMeasure volume V) := by
  let := hprob
  have hc : HasCompactSupport (fun x => ψ x • EuclideanSpace.single i (1 : ℝ)) :=
    hψc.comp_left (g := fun r : ℝ => r • EuclideanSpace.single i (1 : ℝ)) (by simp)
  exact (hψ.smul continuous_const).memLp_of_hasCompactSupport hc

/-- The actual coordinate weighted-adjoint compact test belongs to Gibbs L². -/
theorem gibbs_adjoint_test_memLp
    {V ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) (i : Fin d) :
    MemLp (coordinateWeightedAdjoint i V ψ) 2 (gibbsMeasure volume V) := by
  let := hprob
  exact (c1_coordinateWeightedAdjoint hV hψ i).continuous.memLp_of_hasCompactSupport
    (hasCompactSupport_coordinateWeightedAdjoint hψc i)

/-- Compact graph elements satisfy the actual weighted weak-derivative
pairing identity, as a genuine Hilbert L² identity. -/
theorem compactGibbsGradient_weak_pairing
    {V ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) (i : Fin d)
    (u : compactGibbsGeneratorDomain V) :
    inner ℝ (compactGibbsGradient hV.continuous hprob u)
        ((gibbs_coordinate_test_memLp hprob hψ.continuous hψc i).toLp
          (fun x => ψ x • EuclideanSpace.single i (1 : ℝ))) =
      -inner ℝ (u : EuclideanSpace ℝ (Fin d) →₂[gibbsMeasure volume V] ℝ)
        ((gibbs_adjoint_test_memLp hV hprob hψ hψc i).toLp (coordinateWeightedAdjoint i V ψ)) := by
  let f := compactGibbsRepresentative V u
  have hf := (compactGibbsRepresentative_spec V u).1
  have heq := (compactGibbsRepresentative_spec V u).2.2
  have hpair := compact_directional_gibbs_ibp hV (hψ.of_le (by norm_num)) (hf.of_le
    (by norm_num)) hψc i
  have hleft : inner ℝ (compactGibbsGradient hV.continuous hprob u)
      ((gibbs_coordinate_test_memLp hprob hψ.continuous hψc i).toLp
        (fun x => ψ x • EuclideanSpace.single i (1 : ℝ))) =
      ∫ x, ψ x * coordinateDerivative i f x ∂gibbsMeasure volume V := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(compactGibbsGradient_memLp hprob u).coeFn_toLp,
      (gibbs_coordinate_test_memLp hprob hψ.continuous hψc i).coeFn_toLp] with x hu hT
    change inner ℝ ((compactGibbsGradient_memLp hprob u).toLp _ x) _ = _
    rw [hu, hT, inner_smul_right]
    rw [EuclideanSpace.inner_single_right]
    simp only [starRingEnd_apply, star_trivial, one_mul]
    change ψ x * gradient f x i = ψ x * fderiv ℝ f x (EuclideanSpace.single i 1)
    rw [fderiv_single_eq_gradient_coordinate]
  have hright : inner ℝ (u : EuclideanSpace ℝ (Fin d) →₂[gibbsMeasure volume V] ℝ)
      ((gibbs_adjoint_test_memLp hV hprob hψ hψc i).toLp (coordinateWeightedAdjoint i V ψ)) =
      ∫ x, coordinateWeightedAdjoint i V ψ x * f x ∂gibbsMeasure volume V := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [heq, (gibbs_adjoint_test_memLp hV hprob hψ hψc i).coeFn_toLp] with x hu hA
    rw [← hu, hA]
    simp only [Real.inner_apply, f]
    ring
  rw [hleft, hright]
  exact hpair

/-- The weighted weak-derivative pairing passes to the actual closed graph,
using a closed L² pairing relation rather than a regularity premise. -/
theorem gibbsSobolev_weak_pairing
    {V ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) (i : Fin d)
    (u : gibbsSobolevGraph hV hprob) :
    inner ℝ (gibbsSobolevDerivative hV hprob u)
        ((gibbs_coordinate_test_memLp hprob hψ.continuous hψc i).toLp
          (fun x => ψ x • EuclideanSpace.single i (1 : ℝ))) =
      -inner ℝ (gibbsSobolevInclusion hV hprob u)
        ((gibbs_adjoint_test_memLp hV hprob hψ hψc i).toLp (coordinateWeightedAdjoint i V ψ)) := by
  let G := compactGibbsGradient hV.continuous hprob
  let T := (gibbs_coordinate_test_memLp hprob hψ.continuous hψc i).toLp
    (fun x => ψ x • EuclideanSpace.single i (1 : ℝ))
  let A := (gibbs_adjoint_test_memLp hV hprob hψ hψc i).toLp (coordinateWeightedAdjoint i V ψ)
  let S := {p : (EuclideanSpace ℝ (Fin d) →₂[gibbsMeasure volume V] ℝ) ×
      (EuclideanSpace ℝ (Fin d) →₂[gibbsMeasure volume V] EuclideanSpace ℝ (Fin d)) |
    inner ℝ p.2 T = -inner ℝ p.1 A}
  have hS : IsClosed S := isClosed_eq (continuous_snd.inner continuous_const)
    ((continuous_fst.inner continuous_const).neg)
  have hcore : (G.graph : Set _) ⊆ S := by
    intro p hp
    obtain ⟨v, hv1, hv2⟩ := G.mem_graph_iff.mp hp
    change inner ℝ p.2 T = -inner ℝ p.1 A
    rw [← hv1, ← hv2]
    exact compactGibbsGradient_weak_pairing hV hprob hψ hψc i v
  exact closure_minimal hcore hS
    (gibbsSobolev_mem_closure_compactGradient hV hprob u)

/-- The actual closed gradient satisfies weighted coordinate distributional
integration by parts against every compact C² test. -/
theorem gibbsSobolev_coordinate_weak_derivative
    {V ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) (i : Fin d)
    (u : gibbsSobolevGraph hV hprob) :
    (∫ x, ψ x * (gibbsSobolevDerivative hV hprob u x) i ∂gibbsMeasure volume V) =
      -(∫ x, (coordinateDerivative i ψ x - ψ x * coordinateDerivative i V x) *
        gibbsSobolevInclusion hV hprob u x ∂gibbsMeasure volume V) := by
  have h := gibbsSobolev_weak_pairing hV hprob hψ hψc i u
  rw [L2.inner_def, L2.inner_def] at h
  have hleft : (∫ x, inner ℝ (gibbsSobolevDerivative hV hprob u x)
      ((gibbs_coordinate_test_memLp hprob hψ.continuous hψc i).toLp
        (fun x => ψ x • EuclideanSpace.single i (1 : ℝ)) x) ∂gibbsMeasure volume V) =
      ∫ x, ψ x * (gibbsSobolevDerivative hV hprob u x) i ∂gibbsMeasure volume V := by
    apply integral_congr_ae
    filter_upwards [(gibbs_coordinate_test_memLp hprob hψ.continuous hψc i).coeFn_toLp] with x hT
    rw [hT, inner_smul_right]
    simp [EuclideanSpace.inner_single_right]
  have hright : (∫ x, inner ℝ (gibbsSobolevInclusion hV hprob u x)
      ((gibbs_adjoint_test_memLp hV hprob hψ hψc i).toLp (coordinateWeightedAdjoint i V ψ) x)
        ∂gibbsMeasure volume V) =
      ∫ x, coordinateWeightedAdjoint i V ψ x * gibbsSobolevInclusion hV hprob u x
        ∂gibbsMeasure volume V := by
    apply integral_congr_ae
    filter_upwards [(gibbs_adjoint_test_memLp hV hprob hψ hψc i).coeFn_toLp] with x hA
    rw [hA]
    simp only [Real.inner_apply]
    ring
  exact hleft.symm.trans (h.trans (congrArg Neg.neg hright))


/-- A compact continuous test times an actual Gibbs L² function is genuinely
Lebesgue integrable. Positive density is canceled explicitly. -/
theorem integrable_compact_test_mul_gibbsLp_volume
    {V χ : EuclideanSpace ℝ (Fin d) → ℝ} (hV : Continuous V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (u : EuclideanSpace ℝ (Fin d) →₂[gibbsMeasure volume V] ℝ) :
    Integrable (fun x => χ x * u x) volume := by
  let := hprob
  let ψ := fun x => Real.exp (V x) * χ x
  have hψ : Continuous ψ := (Real.continuous_exp.comp hV).mul hχ
  have hψc : HasCompactSupport ψ := by
    simpa only [ψ, Pi.mul_def] using hχc.mul_left (f := fun x => Real.exp (V x))
  have hψL : MemLp ψ 2 (gibbsMeasure volume V) := hψ.memLp_of_hasCompactSupport hψc
  have hint := hψL.integrable_mul (Lp.memLp u)
  have hi := (integrable_gibbsMeasure_iff volume hV.measurable _).mp hint
  convert! hi using 1
  funext x
  change χ x * u x = Real.exp (-V x) * (Real.exp (V x) * χ x * u x)
  have he : Real.exp (-V x) * Real.exp (V x) = 1 := by rw [← Real.exp_add]; simp
  calc
    _ = (Real.exp (-V x) * Real.exp (V x)) * (χ x * u x) := by rw [he, one_mul]
    _ = _ := by ring

/-- Multiplying by the inverse Gibbs density converts the actual integral
to ordinary volume, including the Bochner undefined-integral conventions. -/
theorem integral_exp_potential_mul_gibbs_eq_volume
    {V : EuclideanSpace ℝ (Fin d) → ℝ} (hV : Measurable V)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) :
    (∫ x, Real.exp (V x) * f x ∂gibbsMeasure volume V) = ∫ x, f x ∂volume := by
  rw [integral_gibbsMeasure volume hV]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    change Real.exp (-V x) * (Real.exp (V x) * f x) = f x
    rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul])

/-- The weighted adjoint of an inverse-density compact test has exactly the
ordinary test derivative, with the drift canceled by the product rule. -/
theorem coordinateWeightedAdjoint_exp_mul
    {V φ : EuclideanSpace ℝ (Fin d) → ℝ} (hV : Differentiable ℝ V)
    (hφ : Differentiable ℝ φ) (i : Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    coordinateWeightedAdjoint i V (fun y => Real.exp (V y) * φ y) x =
      Real.exp (V x) * coordinateDerivative i φ x := by
  have he := (hV x).hasFDerivAt.exp
  have hp := he.mul (hφ x).hasFDerivAt
  have hfd : fderiv ℝ (fun y => Real.exp (V y) * φ y) x =
      Real.exp (V x) • fderiv ℝ φ x + φ x • Real.exp (V x) • fderiv ℝ V x := by
    convert! hp.fderiv using 1
  unfold coordinateWeightedAdjoint coordinateDerivative
  rw [hfd]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- The actual closed weighted gradient is an ordinary distributional
gradient locally: the inverse-density test cancels the Gibbs drift. -/
theorem gibbsSobolev_coordinate_weak_derivative_volume
    {V φ : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) (i : Fin d)
    (u : gibbsSobolevGraph hV hprob) :
    (∫ x, φ x * (gibbsSobolevDerivative hV hprob u x) i ∂volume) =
      -(∫ x, coordinateDerivative i φ x * gibbsSobolevInclusion hV hprob u x ∂volume) := by
  let ψ := fun x => Real.exp (V x) * φ x
  have hψ : ContDiff ℝ 2 ψ := hV.exp.mul hφ
  have hψc : HasCompactSupport ψ := by
    simpa only [ψ, Pi.mul_def] using hφc.mul_left (f := fun x => Real.exp (V x))
  let G := gibbsSobolevDerivative hV hprob u
  let U := gibbsSobolevInclusion hV hprob u
  have h := gibbsSobolev_coordinate_weak_derivative hV hprob hψ hψc i u
  change (∫ x, ψ x * (G x) i ∂gibbsMeasure volume V) =
    -(∫ x, coordinateWeightedAdjoint i V ψ x * U x ∂gibbsMeasure volume V) at h
  have hadj := coordinateWeightedAdjoint_exp_mul (hV.differentiable (by norm_num))
    (hφ.differentiable (by norm_num)) i
  simp_rw [show ∀ x, coordinateWeightedAdjoint i V ψ x =
    Real.exp (V x) * coordinateDerivative i φ x from hadj] at h
  have hl : (fun x => ψ x * (G x) i) = fun x => Real.exp (V x) * (φ x * (G x) i) := by
    funext x
    dsimp only [ψ]
    ring
  have hr : (fun x => Real.exp (V x) * coordinateDerivative i φ x * U x) =
      fun x => Real.exp (V x) * (coordinateDerivative i φ x * U x) := by
    funext x
    ring
  rw [hl, hr, integral_exp_potential_mul_gibbs_eq_volume hV.continuous.measurable,
    integral_exp_potential_mul_gibbs_eq_volume hV.continuous.measurable] at h
  exact h

/-- Compact localization of an actual weighted L² class belongs to ordinary
Lebesgue L². This proves the local measure comparison needed for Rellich. -/
theorem compact_cutoff_gibbsLp_memLp_volume
    {V χ : EuclideanSpace ℝ (Fin d) → ℝ} (hV : Continuous V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (u : EuclideanSpace ℝ (Fin d) →₂[gibbsMeasure volume V] ℝ) :
    MemLp (fun x => χ x * u x) 2 volume := by
  let := hprob
  let H := fun x => Real.exp (V x / 2) * χ x
  have hH : Continuous H := (Real.continuous_exp.comp (hV.div_const 2)).mul hχ
  have hHc : HasCompactSupport H := by
    simpa only [H, Pi.mul_def] using hχc.mul_left (f := fun x => Real.exp (V x / 2))
  have hHL : MemLp H ⊤ (gibbsMeasure volume V) := hH.memLp_of_hasCompactSupport hHc
  have hmul : MemLp (fun x => H x * u x) 2 (gibbsMeasure volume V) := hHL.fun_mul (Lp.memLp u)
  have hmeas : AEStronglyMeasurable (fun x => χ x * u x) volume :=
    hχ.aestronglyMeasurable.mul (AEStronglyMeasurable.mono_ac
      (absolutelyContinuous_gibbsMeasure volume hV.measurable) (Lp.memLp u).aestronglyMeasurable)
  apply (memLp_two_iff_integrable_sq hmeas).mpr
  have hi := (integrable_gibbsMeasure_iff volume hV.measurable _).mp hmul.integrable_sq
  have heq (x : EuclideanSpace ℝ (Fin d)) :
      Real.exp (-V x) • (H x * u x) ^ 2 = (χ x * u x) ^ 2 := by
    have he : Real.exp (-V x) * Real.exp (V x / 2) ^ 2 = 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      have hz : -V x + (2 : ℝ) * (V x / 2) = 0 := by ring
      simpa only [Nat.cast_ofNat, hz] using Real.exp_zero
    change Real.exp (-V x) * ((Real.exp (V x / 2) * χ x) * u x) ^ 2 = _
    calc
      _ = (Real.exp (-V x) * Real.exp (V x / 2) ^ 2) * (χ x * u x) ^ 2 := by ring
      _ = _ := by rw [he, one_mul]
  simp_rw [heq] at hi
  exact hi

/-- Both ordinary-volume pairings in the weak-derivative formula are
actual integrable functions, so the identity does not rely on undefined
Bochner integrals. -/
theorem gibbsSobolev_coordinate_pairings_integrable_volume
    {V φ : EuclideanSpace ℝ (Fin d) → ℝ} (hV : ContDiff ℝ 2 V)
    (hprob : IsProbabilityMeasure (gibbsMeasure volume V))
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) (i : Fin d)
    (u : gibbsSobolevGraph hV hprob) :
    Integrable (fun x => φ x * (gibbsSobolevDerivative hV hprob u x) i) volume ∧
      Integrable (fun x => coordinateDerivative i φ x * gibbsSobolevInclusion hV hprob u x) volume
        := by
  have hcoord : MemLp (fun x => (gibbsSobolevDerivative hV hprob u x) i) 2
      (gibbsMeasure volume V) := by
    apply (Lp.memLp (gibbsSobolevDerivative hV hprob u)).of_le_mul (c := 1) (by fun_prop)
    filter_upwards with x
    simpa only [one_mul] using (PiLp.norm_apply_le (gibbsSobolevDerivative hV hprob u x) i)
  have hi := integrable_compact_test_mul_gibbsLp_volume hV.continuous hprob hφ.continuous hφc
    (hcoord.toLp (fun x => (gibbsSobolevDerivative hV hprob u x) i))
  have heq := (gibbsMeasure_ae_eq_iff volume hV.continuous.measurable).mp hcoord.coeFn_toLp
  refine ⟨hi.congr ?_, ?_⟩
  · filter_upwards [heq] with x hx
    rw [hx]
  · exact integrable_compact_test_mul_gibbsLp_volume hV.continuous hprob
      (c1_coordinateDerivative_of_c2 hφ i).continuous
      (hφc.fderiv_apply ℝ (EuclideanSpace.single i 1)) (gibbsSobolevInclusion hV hprob u)

end CutoffRigidity
