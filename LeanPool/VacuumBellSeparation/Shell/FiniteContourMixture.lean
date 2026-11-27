/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Shell.NormalizedTargetLocalDomination
public import LeanPool.VacuumBellSeparation.Shell.FiniteTaggedProbability

/-!
# One actual probability and one constant for the finite shell cover

The tagged carrier has finitely many copies of the six real Lorentz
parameters. The probability is independent of mass, and its physical
momentum product has the exact uniform-mixture integral formula.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Set
open scoped ENNReal

variable {θ : ℝ} {N : ℕ}

/-- Contour mixture probability defined as `finiteTaggedProbability (fun i => smoothBallProbability
(Fin 6 → ℝ) (D i).radius (D i).radius_pos)`. -/
noncomputable def contourMixtureProbability (D : Fin N → ControlledContourPatch θ) :
    Measure (Fin N × (Fin 6 → ℝ)) :=
  finiteTaggedProbability (fun i =>
    smoothBallProbability (Fin 6 → ℝ) (D i).radius (D i).radius_pos)

instance contourMixtureProbability_isProbability [NeZero N]
    (D : Fin N → ControlledContourPatch θ) : IsProbabilityMeasure (contourMixtureProbability D) :=
  finiteTaggedProbability_isProbability _

/-- Contour mixture family obtained from `prefixedLorentzFamily`. -/
noncomputable def contourMixtureFamily (D : Fin N → ControlledContourPatch θ)
    (a : Fin N × (Fin 6 → ℝ)) : Spacetime ≃L[ℝ] Spacetime :=
  prefixedLorentzFamily (D a.1).frame a.2

theorem contourMixtureFamily_isProper (D : Fin N → ControlledContourPatch θ)
    (a : Fin N × (Fin 6 → ℝ)) : IsProperLorentzMap (contourMixtureFamily D a) :=
  prefixedLorentzFamily_isProper (D a.1).proper a.2

theorem contourMixtureFamily_isOrthochronous (D : Fin N → ControlledContourPatch θ)
    (a : Fin N × (Fin 6 → ℝ)) : IsOrthochronousMap (contourMixtureFamily D a) :=
  prefixedLorentzFamily_isOrthochronous (D a.1).proper.1 (D a.1).future a.2

theorem continuous_contourMixtureFamily_apply (D : Fin N → ControlledContourPatch θ)
    (x : Spacetime) : Continuous (fun a => contourMixtureFamily D a x) :=
  continuous_prod_of_discrete_left.mpr
    (fun i => continuous_prefixedLorentzFamily_apply (D i).frame x)

theorem contourMixtureProbability_ae_norm_bounds (D : Fin N → ControlledContourPatch θ) :
    ∀ᵐ a ∂contourMixtureProbability D,
      spacetimeEuclideanOperatorNorm (contourMixtureFamily D a) < 32 / Real.sin θ ∧
      spacetimeEuclideanOperatorNorm (contourMixtureFamily D a).symm < 32 / Real.sin θ := by
  have hc := continuous_spacetimeEuclideanOperatorNorm_family
    (contourMixtureFamily D) (continuous_contourMixtureFamily_apply D)
  have hi := continuous_lorentzInverse_operatorNorm_family
    (contourMixtureFamily D) (fun a => (contourMixtureFamily_isProper D a).1)
    (continuous_contourMixtureFamily_apply D)
  apply finiteTaggedProbability_ae
    (fun i => smoothBallProbability (Fin 6 → ℝ) (D i).radius (D i).radius_pos)
    (((isOpen_lt hc continuous_const).inter (isOpen_lt hi continuous_const)).measurableSet)
  intro i
  exact (smoothBallProbability_ae_norm_lt (D i).radius (D i).radius_pos).mono
    (fun s hs => (D i).norm_bound s hs.le)

/-- The joint parameter and shell neighborhood used to glue the local contour estimates. -/
def contourMixtureNeighborhood (D : Fin N → ControlledContourPatch θ) :
    Set (ℝ × ComplexSpacetime) := ⋃ i, (D i).neighborhood

theorem isOpen_contourMixtureNeighborhood (D : Fin N → ControlledContourPatch θ) :
    IsOpen (contourMixtureNeighborhood D) := isOpen_iUnion (fun i => (D i).isOpen_neighborhood)

/-- Contour mixture point defined as `complexifiedSpacetimeMap (contourMixtureFamily D y.1)
(complexShellBoost t ((θ : ℂ) * Complex.I) y.2)`. -/
noncomputable def contourMixturePoint (t : ℝ) (D : Fin N → ControlledContourPatch θ)
    (y : (Fin N × (Fin 6 → ℝ)) × EuclideanSpace ℝ (Fin 3)) : ComplexSpacetime :=
  complexifiedSpacetimeMap (contourMixtureFamily D y.1)
    (complexShellBoost t ((θ : ℂ) * Complex.I) y.2)

theorem continuous_contourMixturePoint (t : ℝ) (D : Fin N → ControlledContourPatch θ) :
    Continuous (contourMixturePoint t D) := by
  have hpair : Continuous (fun q : (Fin N × (Fin 6 → ℝ)) × EuclideanSpace ℝ (Fin 3) =>
      (q.1, complexShellBoost t ((θ : ℂ) * Complex.I) q.2)) :=
    (continuous_fst : Continuous (Prod.fst :
      (Fin N × (Fin 6 → ℝ)) × EuclideanSpace ℝ (Fin 3) → Fin N × (Fin 6 → ℝ))).prodMk
      ((continuous_complexShellBoost t ((θ : ℂ) * Complex.I)).comp continuous_snd)
  exact Continuous.comp'
    (f := fun q : (Fin N × (Fin 6 → ℝ)) × EuclideanSpace ℝ (Fin 3) =>
      (q.1, complexShellBoost t ((θ : ℂ) * Complex.I) q.2))
    (g := fun q : (Fin N × (Fin 6 → ℝ)) × ComplexSpacetime =>
      complexifiedSpacetimeMap (contourMixtureFamily D q.1) q.2)
    (continuous_complexifiedSpacetimeMap_family (contourMixtureFamily D)
      (continuous_contourMixtureFamily_apply D)) hpair

/-- Contour mixture cutoff weight. -/
noncomputable def contourMixtureCutoffWeight (t : ℝ) (D : Fin N → ControlledContourPatch θ)
    (F : ComplexSpacetime → ℝ≥0∞) :
    (Fin N × (Fin 6 → ℝ)) × EuclideanSpace ℝ (Fin 3) → ℝ≥0∞ :=
  {y | dispersion t y.2 ≤ 32 / Real.sin θ}.indicator (fun y => F (contourMixturePoint t D y))

theorem measurable_contourMixtureCutoffWeight (t : ℝ) (D : Fin N → ControlledContourPatch θ)
    {F : ComplexSpacetime → ℝ≥0∞} (hF : Measurable F) :
    Measurable (contourMixtureCutoffWeight t D F) :=
  (hF.comp (continuous_contourMixturePoint t D).measurable).indicator
    (isClosed_le ((continuous_dispersion t).comp continuous_snd) continuous_const).measurableSet

theorem contourMixture_integral_formula (t : ℝ) (D : Fin N → ControlledContourPatch θ)
    {F : ComplexSpacetime → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y, contourMixtureCutoffWeight t D F y
      ∂(contourMixtureProbability D).prod (oneParticleMeasure t)) =
      (N : ℝ≥0∞)⁻¹ * ∑ i, ∫⁻ y, physicalContourCutoffWeight t θ (32 / Real.sin θ) (D i).frame F y
        ∂(smoothBallProbability (Fin 6 → ℝ) (D i).radius (D i).radius_pos).prod
          (oneParticleMeasure t) := by
  let _ : SigmaFinite (oneParticleMeasure t) := by unfold oneParticleMeasure; infer_instance
  simpa only [contourMixtureProbability, Fintype.card_fin, contourMixtureCutoffWeight,
    contourMixturePoint, contourMixtureFamily, physicalContourCutoffWeight, physicalContourPoint,
    Set.indicator_apply, Set.mem_ofPred_eq]
    using finiteTaggedProbability_prod_lintegral
      (fun i => smoothBallProbability (Fin 6 → ℝ) (D i).radius (D i).radius_pos)
      (oneParticleMeasure t) (measurable_contourMixtureCutoffWeight t D hF)

theorem contourMixture_uniform_integral_bound [NeZero N]
    (D : Fin N → ControlledContourPatch θ) :
    ∃ k : ℝ≥0∞, 0 < k ∧ k < ∞ ∧
      ∀ t : ℝ, ∀ F : ComplexSpacetime → ℝ≥0∞, Measurable F →
        k * (∫⁻ z in {z : complexShell t | (t, z.1) ∈ contourMixtureNeighborhood D},
          F z.1 ∂inducedRegularShellVolume t) ≤
          ∫⁻ y, contourMixtureCutoffWeight t D F y
            ∂(contourMixtureProbability D).prod (oneParticleMeasure t) := by
  classical
  let c : ℝ≥0∞ := Finset.univ.inf' Finset.univ_nonempty (fun i => (D i).coefficient)
  have hc : 0 < c := (Finset.lt_inf'_iff _).mpr (fun i _ => (D i).coefficient_pos)
  have hcle (i : Fin N) : c ≤ (D i).coefficient := Finset.inf'_le _ (Finset.mem_univ i)
  have hct : c < ∞ := (hcle (Classical.arbitrary (Fin N))).trans_lt
    (D (Classical.arbitrary (Fin N))).coefficient_lt_top
  have hN : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (NeZero.ne N)
  have ha : 0 < (N : ℝ≥0∞)⁻¹ := ENNReal.inv_pos.mpr (by simp)
  have hat : (N : ℝ≥0∞)⁻¹ ≠ ∞ := by simp [hN]
  refine ⟨(N : ℝ≥0∞)⁻¹ * c, pos_iff_ne_zero.mpr (mul_ne_zero ha.ne' hc.ne'),
    lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top hat hct.ne), ?_⟩
  intro t F hF
  rw [contourMixture_integral_formula t D hF]
  have hfiber : {z : complexShell t | (t, z.1) ∈ contourMixtureNeighborhood D} =
      ⋃ i, {z : complexShell t | (t, z.1) ∈ (D i).neighborhood} := by
    ext z
    simp only [contourMixtureNeighborhood, mem_ofPred_eq, mem_iUnion]
  rw [hfiber]
  exact finite_union_lintegral_domination (inducedRegularShellVolume t)
    (fun i => {z : complexShell t | (t, z.1) ∈ (D i).neighborhood}) (fun z => F z.1)
    (fun i => (D i).coefficient) _ (N : ℝ≥0∞)⁻¹ c hcle
    (fun i => (D i).integral_bound t F hF)

end VacuumBellSeparation
