/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticPotential.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.LogSobolevInequality
public import Mathlib.Analysis.Normed.Module.Convex
public import LeanPool.GinibrePoincare.Analysis.GlobalPhaseAction
public import LeanPool.GinibrePoincare.Analysis.EquilibriumFactorization
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticRadialConvexity
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticSmoothPoincare
public import LeanPool.GinibrePoincare.Endgame.ConcreteTheoremOneNine

/-!
# Concrete nonquadratic log gases

Definitions for the exact density and inequalities of Theorem 1.14, and
normalization and radial convexity lemmas. The unconditional Poincaré and radial
logarithmic Sobolev inequalities are assembled in
`GinibrePoincare.Endgame.FullNonQuadraticPotential`.
-/

@[expose] public section

open MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace GinibrePoincare
noncomputable section

/-- A planar external potential, a real-valued function on `ℂ`. -/
abbrev Potential := ℂ → ℝ

/-- The Lebesgue density in Theorem 1.14, before normalization. -/
def potentialWeight (n : ℕ) (V : Potential) (z : Configuration n) : ℝ :=
  Real.exp (-(n : ℝ) * ∑ i, V (z i)) * vandermondeWeight z

/-- The actual unnormalized measure, relative to Euclidean volume. -/
def rawPotentialMeasure (n : ℕ) (V : Potential) : Measure (Configuration n) :=
  (configurationVolume n).withDensity (fun z => ENNReal.ofReal (potentialWeight n V z))

/-- The actual partition integral, with no assumed normalization constant. -/
def potentialPartition (n : ℕ) (V : Potential) : ℝ≥0∞ :=
  rawPotentialMeasure n V Set.univ

/-- The Boltzmann–Gibbs measure of Theorem 1.14. -/
def potentialMeasure (n : ℕ) (V : Potential) : Measure (Configuration n) :=
  (potentialPartition n V)⁻¹ • rawPotentialMeasure n V

/-- Rotation invariance of a planar potential. -/
def IsRotationalPotential (V : Potential) : Prop :=
  ∀ u z : ℂ, ‖u‖ = 1 → V (u * z) = V z

/-- Strong convexity in the exact normalization of the paper. -/
def IsRhoConvexPotential (ρ : ℝ) (V : Potential) : Prop :=
  ConvexOn ℝ Set.univ (fun z => V z - ρ / 2 * Complex.normSq z)

/-- For a C² potential the subharmonicity hypothesis is the Laplacian bound
`ΔV ≥ 2ρ`. The directions `1` and `I` are the Euclidean coordinate directions. -/
def IsRhoSubharmonicPotential (ρ : ℝ) (V : Potential) : Prop :=
  ∀ z, fderiv ℝ (fun w => fderiv ℝ V w (1 : ℂ)) z (1 : ℂ) +
    fderiv ℝ (fun w => fderiv ℝ V w Complex.I) z Complex.I ≥ 2 * ρ

/-- Literal variance for the nonquadratic gas. -/
def potentialVariance (n : ℕ) (V : Potential) (f : Configuration n → ℝ) : ℝ :=
  ∫ z, (f z - ∫ w, f w ∂potentialMeasure n V) ^ 2 ∂potentialMeasure n V

/-- Euclidean gradient energy, before division by `ρ n`. -/
def potentialGradientEnergy (n : ℕ) (V : Potential) (f : Configuration n → ℝ) : ℝ :=
  ∫ z, realGradientNormSq f z ∂potentialMeasure n V

/-- Exact analytic conclusions of Theorem 1.14. The unconditional instance for
positive particle number is exported by `Endgame.FullNonQuadraticPotential`. -/
structure NonQuadraticPotentialTheorem (n : ℕ) : Prop where
  poincareInequality : ∀ (V : Potential) (ρ : ℝ),
    ContDiff ℝ 2 V → IsRotationalPotential V →
    potentialPartition n V < ⊤ →
    0 < ρ → IsRhoSubharmonicPotential ρ V →
    ∀ f : Configuration n → ℝ, IsSmoothCompactSymmetric f →
      potentialVariance n V f ≤ (1 / (ρ * n)) * potentialGradientEnergy n V f
  logSobolevInequality : ∀ (V : Potential) (ρ : ℝ),
    ContDiff ℝ 2 V → IsRotationalPotential V →
    potentialPartition n V < ⊤ →
    0 < ρ → IsRhoConvexPotential ρ V →
    ∀ f : Configuration n → ℝ, IsSmoothCompactSymmetric f →
      IsRadialFunctionLSI f →
      squareEntropy (potentialMeasure n V) f ≤
        (2 / (ρ * n)) * potentialGradientEnergy n V f

theorem potentialWeight_nonneg (n : ℕ) (V : Potential) (z : Configuration n) :
    0 ≤ potentialWeight n V z :=
  mul_nonneg (Real.exp_pos _).le (vandermondeWeight_nonneg z)

/-- The density specializes exactly to the existing quadratic weight. -/
@[simp] theorem potentialWeight_quadratic (n : ℕ) (z : Configuration n) :
    potentialWeight n Complex.normSq z = ginibreWeight n z := by
  rfl

/-- Stronger confinement decreases the unnormalized density pointwise. -/
theorem potentialWeight_antitone (n : ℕ) {V W : Potential}
    (hVW : ∀ z, V z ≤ W z) (z : Configuration n) :
    potentialWeight n W z ≤ potentialWeight n V z := by
  apply mul_le_mul_of_nonneg_right _ (vandermondeWeight_nonneg z)
  apply Real.exp_le_exp.mpr
  have hs : (∑ i : Fin n, V (z i)) ≤ ∑ i : Fin n, W (z i) :=
    Finset.sum_le_sum fun i _ => hVW (z i)
  exact mul_le_mul_of_nonpos_left hs (neg_nonpos.mpr (Nat.cast_nonneg n))

/-- In particular a potential above the quadratic one has a density bounded
by the concrete Gaussian–Vandermonde density. -/
theorem potentialWeight_le_ginibre (n : ℕ) {V : Potential}
    (hV : ∀ z, Complex.normSq z ≤ V z) (z : Configuration n) :
    potentialWeight n V z ≤ ginibreWeight n z := by
  simpa using potentialWeight_antitone n hV z

/-- The general potential retains exactly the original collision locus. -/
theorem potentialWeight_eq_zero_iff (n : ℕ) (V : Potential)
    (z : Configuration n) :
    potentialWeight n V z = 0 ↔ z ∈ collisionSet n := by
  rw [potentialWeight, mul_eq_zero]
  simp only [Real.exp_ne_zero, false_or]
  exact vandermondeWeight_eq_zero_iff z

/-- The partition function is exactly the density integral in the paper. -/
theorem potentialPartition_eq_lintegral (n : ℕ) (V : Potential) :
    potentialPartition n V =
      ∫⁻ z, ENNReal.ofReal (potentialWeight n V z) ∂configurationVolume n := by
  simp [potentialPartition, rawPotentialMeasure, withDensity_apply]

/-- The partition integral inherits the density comparison without any
regularity assumptions on the potentials. -/
theorem potentialPartition_antitone (n : ℕ) {V W : Potential}
    (hVW : ∀ z, V z ≤ W z) : potentialPartition n W ≤ potentialPartition n V := by
  rw [potentialPartition_eq_lintegral, potentialPartition_eq_lintegral]
  exact lintegral_mono fun z => ENNReal.ofReal_le_ofReal (potentialWeight_antitone n hVW z)

/-- Normalization uses the actual partition integral. This lemma asserts no
Poincaré or logarithmic Sobolev estimate. -/
theorem potentialMeasure_univ (n : ℕ) (V : Potential)
    (hpos : 0 < potentialPartition n V) (hfin : potentialPartition n V < ⊤) :
    potentialMeasure n V Set.univ = 1 := by
  change (potentialPartition n V)⁻¹ * potentialPartition n V = 1
  exact ENNReal.inv_mul_cancel (ne_of_gt hpos) (ne_of_lt hfin)

/-- Scalar convexity and monotonicity lift a radial profile to every real
normed space. This is the dimension-independent convexity step of the LSI
argument; deriving these hypotheses from planar convexity is separate. -/
theorem convexOn_radial_lift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ψ : ℝ → ℝ} (hc : ConvexOn ℝ (Set.Ici 0) ψ)
    (hm : MonotoneOn ψ (Set.Ici 0)) :
    ConvexOn ℝ (Set.univ : Set E) (fun x => ψ ‖x‖) := by
  have hnorm := convexOn_norm (convex_univ : Convex ℝ (Set.univ : Set E))
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have ht : 0 ≤ a * ‖x‖ + b * ‖y‖ :=
    add_nonneg (mul_nonneg ha (norm_nonneg x)) (mul_nonneg hb (norm_nonneg y))
  exact (hm (norm_nonneg _) ht (hnorm.2 hx hy ha hb hab)).trans
    (hc.2 (norm_nonneg x) (norm_nonneg y) ha hb hab)

/-- Continuous confinement gives a measurable concrete density. -/
theorem measurable_potentialDensity (n : ℕ) {V : Potential} (hV : Continuous V) :
    Measurable (fun z : Configuration n => ENNReal.ofReal (potentialWeight n V z)) := by
  apply Measurable.ennreal_ofReal
  apply Continuous.measurable
  unfold potentialWeight vandermondeWeight
  apply Continuous.mul
  · apply Real.continuous_exp.comp
    apply Continuous.mul continuous_const
    exact continuous_finsetSum _ fun i _ => hV.comp (continuous_apply i)
  · exact Complex.continuous_normSq.comp continuous_vandermonde

/-- Every continuous potential has a strictly positive actual partition
integral: the Vandermonde vanishes only on a Lebesgue-null collision set. -/
theorem potentialPartition_pos (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) : 0 < potentialPartition n V := by
  apply pos_iff_ne_zero.mpr
  intro hz
  rw [potentialPartition_eq_lintegral] at hz
  have hd := (lintegral_eq_zero_iff (measurable_potentialDensity n hV)).mp hz
  have hfree : ∀ᵐ z ∂configurationVolume n, z ∉ collisionSet n := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_mem_eq] using configurationVolume_collisionSet hn
  have hfalse : ∀ᵐ z ∂configurationVolume n, False := by
    filter_upwards [hd, hfree] with z hzero hnoncoll
    have hnonpos : potentialWeight n V z ≤ 0 := ENNReal.ofReal_eq_zero.mp hzero
    have hweight : potentialWeight n V z = 0 :=
      le_antisymm hnonpos (potentialWeight_nonneg n V z)
    exact hnoncoll ((potentialWeight_eq_zero_iff n V z).mp hweight)
  have hzvol : configurationVolume n Set.univ = 0 := by
    simpa using ae_iff.mp hfalse
  have hpos : 0 < configurationVolume n Set.univ := by
    unfold configurationVolume
    exact isOpen_univ.measure_pos volume Set.univ_nonempty
  exact (ne_of_gt hpos) hzvol

/-- The general continuous finite-partition gas is an actual probability
measure, with positivity discharged rather than assumed. -/
theorem potentialMeasure_isProbabilityMeasure (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤) :
    IsProbabilityMeasure (potentialMeasure n V) :=
  ⟨potentialMeasure_univ n V (potentialPartition_pos n hn hV) hfin⟩

/-- Volume is invariant under a common unit complex rotation. -/
theorem measurePreserving_globalPhase_configurationVolume (n : ℕ)
    (u : ℂ) (hu : ‖u‖ = 1) :
    MeasurePreserving (globalPhase u) (configurationVolume n) (configurationVolume n) := by
  unfold configurationVolume
  rw [volume_pi]
  exact measurePreserving_pi _ _ fun _ => measurePreserving_complex_mul_of_norm_one u hu

/-- The full interacting density retains rotational invariance. -/
theorem potentialDensity_globalPhase (n : ℕ) {V : Potential}
    (hV : IsRotationalPotential V) (u : ℂ) (hu : ‖u‖ = 1) (z : Configuration n) :
    ENNReal.ofReal (potentialWeight n V (globalPhase u z)) =
      ENNReal.ofReal (potentialWeight n V z) := by
  have hs : (∑ i : Fin n, V (globalPhase u z i)) = ∑ i : Fin n, V (z i) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hV u (z i) hu
  simp only [potentialWeight, hs, ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact congrArg (fun t => ENNReal.ofReal (Real.exp (-(n : ℝ) * ∑ i, V (z i))) * t)
    (vandermondeDensity_globalPhase n u hu z)

/-- Rotation invariance of the actual normalized nonquadratic gas. -/
theorem measurePreserving_globalPhase_potentialMeasure (n : ℕ) {V : Potential}
    (hVc : Continuous V) (hVr : IsRotationalPotential V) (u : ℂ) (hu : ‖u‖ = 1) :
    MeasurePreserving (globalPhase u) (potentialMeasure n V) (potentialMeasure n V) := by
  have hu0 : u ≠ 0 := by intro h; subst u; simp at hu
  let e := globalPhaseMeasurableEquiv (n := n) u hu0
  refine ⟨e.measurable, ?_⟩
  unfold potentialMeasure rawPotentialMeasure
  have hm : Measurable (globalPhase (n := n) u) := e.measurable
  rw [Measure.map_smul _ hm.aemeasurable]
  congr 1
  have hd : (fun z => ENNReal.ofReal (potentialWeight n V z)) ∘ e =
      (fun z => ENNReal.ofReal (potentialWeight n V z)) := by
    funext z
    exact potentialDensity_globalPhase n hVr u hu z
  nth_rw 1 [← hd]
  exact MeasurePreserving.map_withDensity_comp e
    (measurePreserving_globalPhase_configurationVolume n u hu) (measurable_potentialDensity n hVc)

/-- Relabeling invariance of the full nonquadratic density. -/
theorem potentialDensity_permute (n : ℕ) (V : Potential) (σ : ParticlePermutation n)
    (z : Configuration n) :
    ENNReal.ofReal (potentialWeight n V (permute σ z)) =
      ENNReal.ofReal (potentialWeight n V z) := by
  have hs : (∑ i : Fin n, V (permute σ z i)) = ∑ i : Fin n, V (z i) := by
    simpa [permute] using Equiv.sum_comp σ (fun i => V (z i))
  simp only [potentialWeight, hs, ENNReal.ofReal_mul (Real.exp_pos _).le]
  exact congrArg (fun t => ENNReal.ofReal (Real.exp (-(n : ℝ) * ∑ i, V (z i))) * t)
    (vandermondeDensity_permute σ z)

/-- Relabeling invariance of the actual normalized nonquadratic gas. -/
theorem measurePreserving_permute_potentialMeasure (n : ℕ) {V : Potential}
    (hV : Continuous V) (σ : ParticlePermutation n) :
    MeasurePreserving (permute σ) (potentialMeasure n V) (potentialMeasure n V) := by
  have hbase : MeasurePreserving (permutationMeasurableEquiv σ)
      (configurationVolume n) (configurationVolume n) := by
    unfold configurationVolume
    rw [volume_pi]
    exact measurePreserving_piCongrLeft (fun _ : Fin n => (volume : Measure ℂ)) σ.symm
  have heq : ⇑(permutationMeasurableEquiv σ) = permute σ := by
    funext z
    exact permutationMeasurableEquiv_apply σ z
  refine ⟨heq ▸ hbase.measurable, ?_⟩
  unfold potentialMeasure rawPotentialMeasure
  rw [Measure.map_smul _ (heq ▸ hbase.measurable).aemeasurable]
  congr 1
  have hd : (fun z => ENNReal.ofReal (potentialWeight n V z)) ∘ permutationMeasurableEquiv σ =
      (fun z => ENNReal.ofReal (potentialWeight n V z)) := by
    funext z
    simpa only [Function.comp_apply, permutationMeasurableEquiv_apply] using
        potentialDensity_permute n V σ z
  nth_rw 1 [← hd]
  rw [← heq]
  exact MeasurePreserving.map_withDensity_comp (permutationMeasurableEquiv σ)
    hbase (measurable_potentialDensity n hV)

/-- The raw quadratic Lebesgue gas differs from the Gaussian-reference
construction only by its explicit Gaussian normalizing scalar. -/
theorem rawGinibreMeasure_eq_scalar_rawPotential (n : ℕ) (hn : 0 < n) :
    rawGinibreMeasure n = ENNReal.ofReal (((n : ℝ) / Real.pi) ^ n) •
      rawPotentialMeasure n Complex.normSq := by
  rw [rawGinibreMeasure_eq_equilibriumDensity n hn]
  unfold rawPotentialMeasure
  rw [← withDensity_smul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext z
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp [rawGinibreDensity', ginibreLebesgueDensityReal, gaussianWeight, potentialWeight,
    vandermondeWeight, configurationNormSq]
  ring

/-- Actual mass normalization cancels the Gaussian-reference scalar, so the
quadratic specialization is exactly the existing Ginibre probability measure. -/
theorem potentialMeasure_quadratic (n : ℕ) (hn : 0 < n) :
    potentialMeasure n Complex.normSq = ginibreMeasure n := by
  let c := ENNReal.ofReal (((n : ℝ) / Real.pi) ^ n)
  have hc0 : c ≠ 0 := by
    apply ne_of_gt
    exact ENNReal.ofReal_pos.mpr (by positivity)
  have hct : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hm : ginibreNormalizingMass n = c * potentialPartition n Complex.normSq := by
    unfold ginibreNormalizingMass
    rw [rawGinibreMeasure_eq_scalar_rawPotential n hn]
    rfl
  unfold ginibreMeasure
  rw [hm, rawGinibreMeasure_eq_scalar_rawPotential n hn]
  change _ = (c * potentialPartition n Complex.normSq)⁻¹ •
    (c • rawPotentialMeasure n Complex.normSq)
  rw [ENNReal.mul_inv (Or.inl hc0) (Or.inl hct), smul_smul]
  have hcancel : (c⁻¹ * (potentialPartition n Complex.normSq)⁻¹) * c =
      (potentialPartition n Complex.normSq)⁻¹ := by
    rw [mul_right_comm, ENNReal.inv_mul_cancel hc0 hct, one_mul]
  rw [hcancel]
  rfl

/-- The actual quadratic Lebesgue partition integral is positive and finite. -/
theorem potentialPartition_quadratic_valid (n : ℕ) (hn : 0 < n) :
    0 < potentialPartition n Complex.normSq ∧ potentialPartition n Complex.normSq < ⊤ := by
  let c := ENNReal.ofReal (((n : ℝ) / Real.pi) ^ n)
  have hc0 : c ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
  have hct : c ≠ ⊤ := ENNReal.ofReal_ne_top
  have hm : ginibreNormalizingMass n = c * potentialPartition n Complex.normSq := by
    unfold ginibreNormalizingMass
    rw [rawGinibreMeasure_eq_scalar_rawPotential n hn]
    rfl
  have heq : potentialPartition n Complex.normSq = c⁻¹ * ginibreNormalizingMass n := by
    rw [hm, ENNReal.inv_mul_cancel_left hc0 hct]
  rw [heq]
  constructor
  · exact ENNReal.mul_pos_iff.mpr ⟨ENNReal.inv_pos.mpr hct, ginibreNormalizingMass_pos hn⟩
  · exact ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr (pos_iff_ne_zero.mpr hc0))
      (ginibreNormalizingMass_lt_top n)

/-- Quadratic lower confinement is sufficient for finiteness of the actual
nonquadratic partition integral. -/
theorem potentialPartition_lt_top_of_quadratic_lower_bound (n : ℕ) (hn : 0 < n)
    {V : Potential} (hV : ∀ z, Complex.normSq z ≤ V z) :
    potentialPartition n V < ⊤ :=
  lt_of_le_of_lt (potentialPartition_antitone n hV) (potentialPartition_quadratic_valid n hn).2

/-- The planar convexity hypothesis lifts without any extra scalar-profile
hypothesis to every real normed space. -/
theorem convexOn_radial_lift_of_planar {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {ψ : ℝ → ℝ}
    (hc : ConvexOn ℝ Set.univ (fun z : ℂ => ψ ‖z‖)) :
    ConvexOn ℝ (Set.univ : Set E) (fun x => ψ ‖x‖) := by
  obtain ⟨hc', hm⟩ := radial_profile_convex_monotone hc
  exact convexOn_radial_lift hc' hm

/-- The paper's strongly convex planar radial potential gives a strongly
convex radial potential in every real normed space, with the same parameter. -/
theorem rhoConvex_radial_lift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ρ : ℝ) (Q : ℝ → ℝ)
    (hc : IsRhoConvexPotential ρ (fun z : ℂ => Q ‖z‖)) :
    ConvexOn ℝ (Set.univ : Set E) (fun x => Q ‖x‖ - ρ / 2 * ‖x‖ ^ 2) := by
  apply convexOn_radial_lift_of_planar (ψ := fun r => Q r - ρ / 2 * r ^ 2)
  simpa only [IsRhoConvexPotential, Complex.sq_norm] using hc

/-- The exact `ρ = 2` inequality under the new potential-measure definitions,
on the collision-free smooth symmetric core of Theorem 1.9. -/
theorem potential_quadratic_core_poincare {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    potentialVariance n Complex.normSq f ≤
      (1 / (2 * (n : ℝ))) * potentialGradientEnergy n Complex.normSq f := by
  have hid := (concrete_theoremOneNine hn f hf).1
  have hm : ∀ k : ℕ, 0 ≤ concretePositiveHermiteModeMass hn f hf k :=
    fun k => sq_nonneg _
  have ht := modeTail_nonneg (concretePositiveHermiteModeMass hn f hf) hm
  have hi : smoothGinibreVariance n f ≤ smoothGinibreEnergy n f / 2 := by
    nlinarith [hid, ht, sq_nonneg (‖centeredObservableL2 hn f hf -
      (ginibreHolomorphicAmbientClosedSpan n hn).starProjection
        (centeredObservableL2 hn f hf) - star
          ((ginibreHolomorphicAmbientClosedSpan n hn).starProjection
            (centeredObservableL2 hn f hf))‖)]
  simpa only [potentialVariance, potentialGradientEnergy, potentialMeasure_quadratic n hn,
    smoothGinibreVariance, smoothGinibreMean, smoothGinibreEnergy,
    div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using hi

/-- The exact `ρ = 2` Poincaré inequality for the entire smooth compact
symmetric class under the nonquadratic gas definitions. -/
theorem potential_quadratic_poincare {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsSmoothCompactSymmetric f) :
    potentialVariance n Complex.normSq f ≤
      (1 / (2 * (n : ℝ))) * potentialGradientEnergy n Complex.normSq f := by
  have h := smoothGinibrePoincare_unconditional hn f hf
  simpa only [potentialVariance, potentialGradientEnergy, potentialMeasure_quadratic n hn,
    smoothGinibreVariance, smoothGinibreMean, smoothGinibreEnergy,
    div_eq_mul_inv, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm] using h

/-- The exact `ρ = 2` radial LSI on the entire smooth compact symmetric radial
class, transported to the new concrete potential measure. -/
theorem potential_quadratic_radial_lsi {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsSmoothCompactSymmetric f)
    (hr : IsRadialFunctionLSI f) :
    squareEntropy (potentialMeasure n Complex.normSq) f ≤
      (2 / (2 * (n : ℝ))) * potentialGradientEnergy n Complex.normSq f := by
  have h := radial_core_lsi n hn f ⟨hf, hr⟩
  have hcoef : (2 : ℝ) / (2 * (n : ℝ)) = 1 / (n : ℝ) := by ring
  simpa [potentialMeasure_quadratic n hn, potentialGradientEnergy,
    ginibreSquareEntropy, smoothGinibreEnergy, hcoef] using h

end
end GinibrePoincare
