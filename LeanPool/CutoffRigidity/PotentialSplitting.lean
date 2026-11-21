/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Tactic

/-!
# Splitting a translation-invariant interaction

These are the orthogonal-decomposition and density-factorization calculations
preceding Theorem `thm_bg_convex_inter` in Section 1 of `cutcur-lean.tex`.
They use actual inner products, exponentials, and measures, and prove the
normalized Gibbs Gaussian factorization by a volume-preserving orthogonal
change of coordinates. The spectral-gap theorem remains separate.
-/

public section

namespace CutoffRigidity

open MeasureTheory
open scoped ENNReal

section OrthogonalDecomposition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The component orthogonal to the unit direction `v`. -/
@[expose] noncomputable def perpendicularPart (v x : E) : E :=
  x - inner ℝ v x • v

/-- The residual component is orthogonal to the unit direction. -/
theorem inner_perpendicularPart {v : E} (hv : ‖v‖ = 1) (x : E) :
    inner ℝ v (perpendicularPart v x) = 0 := by
  rw [perpendicularPart, inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hv]
  ring

/-- The parallel and perpendicular components reconstruct the original vector. -/
theorem parallel_add_perpendicularPart (v x : E) :
    inner ℝ v x • v + perpendicularPart v x = x := by
  simp [perpendicularPart]

/-- Pythagoras in the unit invariant direction. -/
theorem norm_sq_split_unit {v : E} (hv : ‖v‖ = 1) (x : E) :
    ‖x‖ ^ 2 = (inner ℝ v x) ^ 2 + ‖perpendicularPart v x‖ ^ 2 := by
  rw [perpendicularPart, norm_sub_sq_real, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    hv, real_inner_smul_right, real_inner_comm x v]
  ring

/-- Translation invariance removes the parallel component from the interaction. -/
theorem interaction_eq_perpendicularPart (W : E → ℝ) (v x : E)
    (hinv : ∀ y : E, ∀ u : ℝ, W (y + u • v) = W y) :
    W x = W (perpendicularPart v x) := by
  simpa only [perpendicularPart, neg_smul, sub_eq_add_neg] using
    (hinv x (-inner ℝ v x)).symm

/-- Exact additive splitting of the quadratic-plus-interaction potential. -/
theorem potential_split_unit (W : E → ℝ) {v : E} (hv : ‖v‖ = 1)
    (hinv : ∀ y : E, ∀ u : ℝ, W (y + u • v) = W y) (ρ : ℝ) (x : E) :
    ρ / 2 * ‖x‖ ^ 2 + W x =
      ρ / 2 * (inner ℝ v x) ^ 2 +
        (W (perpendicularPart v x) + ρ / 2 * ‖perpendicularPart v x‖ ^ 2) := by
  rw [norm_sq_split_unit hv x, interaction_eq_perpendicularPart W v x hinv]
  ring

/-- The pointwise Gibbs density factorization displayed in Section 1. -/
theorem exp_neg_potential_split_unit (W : E → ℝ) {v : E} (hv : ‖v‖ = 1)
    (hinv : ∀ y : E, ∀ u : ℝ, W (y + u • v) = W y) (ρ : ℝ) (x : E) :
    Real.exp (-(ρ / 2 * ‖x‖ ^ 2 + W x)) =
      Real.exp (-(ρ / 2 * (inner ℝ v x) ^ 2)) *
        Real.exp (-(W (perpendicularPart v x) + ρ / 2 * ‖perpendicularPart v x‖ ^ 2)) := by
  rw [potential_split_unit W hv hinv ρ x, neg_add, Real.exp_add]

end OrthogonalDecomposition

section ProductMeasures

variable {F : Type*} [MeasurableSpace F]

/-- Once written in orthogonal product coordinates, a separated Gibbs density
is the product of the corresponding actual weighted measures. -/
theorem separated_gibbs_product (μ : Measure ℝ) (ν : Measure F) [SFinite ν]
    (ρ : ℝ) (U : F → ℝ) (hU : Measurable U) :
    (μ.prod ν).withDensity (fun z => ENNReal.ofReal (Real.exp (-(ρ / 2 * z.1 ^ 2 + U z.2)))) =
      (μ.withDensity (fun r => ENNReal.ofReal (Real.exp (-(ρ / 2 * r ^ 2))))).prod
        (ν.withDensity (fun y => ENNReal.ofReal (Real.exp (-U y)))) := by
  rw [prod_withDensity (by fun_prop) (by fun_prop)]
  congr 1
  ext z
  rw [neg_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _)]

end ProductMeasures

section CoordinateMeasures

/-- Transporting a density that depends only on the mapped coordinate commutes
with taking the actual image measure. -/
theorem map_withDensity_comp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (f : X → Y) (g : Y → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    (μ.withDensity (fun x => g (f x))).map f = (μ.map f).withDensity g := by
  ext s hs
  rw [Measure.map_apply hf hs, withDensity_apply _ (hf hs), withDensity_apply _ hs,
    setLIntegral_map hs hg hf]

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

section OrthogonalProduct

variable {U : Type*}
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U]

theorem orthogonalProductCoordinates_measurePreserving
    (A : E ≃ₗᵢ[ℝ] WithLp 2 (U × F)) :
    MeasurePreserving (fun x => (A x).ofLp) (volume : Measure E) ((volume : Measure U).prod volume)
      :=
  (WithLp.volume_preserving_ofLp U F).comp (LinearIsometryEquiv.measurePreserving A)

theorem separated_gibbs_map_orthogonal_product
    (A : E ≃ₗᵢ[ℝ] WithLp 2 (U × F)) (V : E → ℝ)
    (m : E) (Q : U → ℝ) (hQ : Measurable Q) (W : F → ℝ) (hW : Measurable W)
    (hsplit : ∀ u w, V (A.symm (WithLp.toLp 2 (u, w)) + m) = Q u + W w) :
    ((volume : Measure E).withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))).map
      (fun x => (A (x-m)).ofLp) =
        ((volume : Measure U).withDensity (fun u => ENNReal.ofReal (Real.exp (-Q u)))).prod
          ((volume : Measure F).withDensity (fun w => ENNReal.ofReal (Real.exp (-W w)))) := by
  let g := fun z : U × F => ENNReal.ofReal (Real.exp (-(Q z.1+W z.2)))
  have hg : Measurable g := by fun_prop
  have hf : Measurable (fun x : E => (A x).ofLp) := by fun_prop
  have hsplit' (y : E) : ENNReal.ofReal (Real.exp (-V (y+m)))=g (A y).ofLp := by
    have hh := hsplit (A y).ofLp.1 (A y).ofLp.2
    have he : WithLp.toLp 2 ((A y).ofLp.1,(A y).ofLp.2)=A y := rfl
    rw [he,A.symm_apply_apply] at hh
    rw [hh]
  have htrans : ((volume : Measure E).withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))).map
      (fun x => x-m) = (volume : Measure E).withDensity (fun y => g (A y).ofLp) := by
    have hh := map_withDensity_comp (volume : Measure E) (fun x => x+(-m))
      (fun y => g (A y).ofLp) (by fun_prop) (hg.comp hf)
    rw [(measurePreserving_add_right (volume : Measure E) (-m)).map_eq] at hh
    have hdensity : (fun x : E => ENNReal.ofReal (Real.exp (-V x))) =
        fun x => g (A (x+(-m))).ofLp := by
      funext x
      rw [← hsplit']
      simp
    rw [← hdensity] at hh
    simpa only [sub_eq_add_neg] using hh
  calc
    _ = (((volume : Measure E).withDensity (fun x => ENNReal.ofReal (Real.exp (-V x)))).map
        (fun x => x-m)).map (fun y => (A y).ofLp) := by
      rw [Measure.map_map hf (by fun_prop)]
      rfl
    _ = ((volume : Measure E).withDensity (fun y => g (A y).ofLp)).map (fun y => (A y).ofLp)
      := by rw [htrans]
    _ = ((volume : Measure E).map (fun y => (A y).ofLp)).withDensity g
      := map_withDensity_comp _ _ _ hf hg
    _ = ((volume : Measure U).prod (volume : Measure F)).withDensity g := by
      rw [(orthogonalProductCoordinates_measurePreserving A).map_eq]
    _ = _ := by
      rw [prod_withDensity (by fun_prop : Measurable (fun u => ENNReal.ofReal (Real.exp (-Q u))))
        (by fun_prop : Measurable (fun w => ENNReal.ofReal (Real.exp (-W w))))]
      congr 1
      funext z
      dsimp only [g]
      rw [neg_add,Real.exp_add,ENNReal.ofReal_mul (Real.exp_nonneg _)]

end OrthogonalProduct

/-- An orthogonal splitting supplies product coordinates preserving actual Lebesgue volume. -/
theorem orthogonalCoordinates_measurePreserving (A : E ≃ₗᵢ[ℝ] WithLp 2 (ℝ × F)) :
    MeasurePreserving (fun x => (A x).ofLp)
      (volume : Measure E) ((volume : Measure ℝ).prod (volume : Measure F)) :=
  orthogonalProductCoordinates_measurePreserving A


omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] in
/-- In orthogonal product coordinates, invariance in the first direction removes
that coordinate from the interaction, exactly as in the displayed paper proof. -/
theorem interaction_in_orthogonalCoordinates
    (A : E ≃ₗᵢ[ℝ] WithLp 2 (ℝ × F)) (W : E → ℝ)
    (hinv : ∀ x : E, ∀ u : ℝ,
      W (x + u • A.symm (WithLp.toLp 2 (1, (0 : F)))) = W x)
    (r : ℝ) (y : F) :
    W (A.symm (WithLp.toLp 2 (r, y))) = W (A.symm (WithLp.toLp 2 (0, y))) := by
  have hvec : A.symm (WithLp.toLp 2 (r, y)) =
      A.symm (WithLp.toLp 2 (0, y)) + r • A.symm (WithLp.toLp 2 (1, (0 : F))) := by
    apply A.injective
    simp only [map_add, map_smul, A.apply_symm_apply]
    apply WithLp.ofLp_injective
    ext <;> simp
  rw [hvec]
  exact hinv _ _

/-- The Gibbs measure really becomes a product under orthogonal coordinates.
The one-dimensional quadratic factor is left unnormalized here. -/
theorem gibbs_map_orthogonalCoordinates
    (A : E ≃ₗᵢ[ℝ] WithLp 2 (ℝ × F)) (W : E → ℝ) (hW : Measurable W)
    (hinv : ∀ x : E, ∀ u : ℝ,
      W (x + u • A.symm (WithLp.toLp 2 (1, (0 : F)))) = W x) (ρ : ℝ) :
    ((volume : Measure E).withDensity (fun x =>
        ENNReal.ofReal (Real.exp (-(ρ / 2 * ‖x‖ ^ 2 + W x))))).map
          (fun x => (A x).ofLp) =
      ((volume : Measure ℝ).withDensity (fun r =>
        ENNReal.ofReal (Real.exp (-(ρ / 2 * r ^ 2))))).prod
      ((volume : Measure F).withDensity (fun y =>
        ENNReal.ofReal (Real.exp (-(W (A.symm (WithLp.toLp 2 (0, y))) + ρ / 2 * ‖y‖ ^ 2))))) := by
  let U : F → ℝ := fun y => W (A.symm (WithLp.toLp 2 (0, y))) + ρ / 2 * ‖y‖ ^ 2
  have hU : Measurable U := by fun_prop
  have hsplit (r : ℝ) (y : F) :
      ρ / 2 * ‖A.symm (WithLp.toLp 2 (r, y)) + (0 : E)‖ ^ 2 +
        W (A.symm (WithLp.toLp 2 (r, y)) + (0 : E)) = ρ / 2 * r ^ 2 + U y := by
    rw [add_zero, interaction_in_orthogonalCoordinates A W hinv]
    have hnorm : ‖A.symm (WithLp.toLp 2 (r, y))‖ ^ 2 = r ^ 2 + ‖y‖ ^ 2 := by
      rw [A.symm.norm_map, WithLp.prod_norm_sq_eq_of_L2]
      simp [Real.norm_eq_abs, sq_abs]
    rw [hnorm]
    dsimp only [U]
    ring
  simpa only [sub_zero] using separated_gibbs_map_orthogonal_product A
    (fun x : E => ρ / 2 * ‖x‖ ^ 2 + W x) (0 : E) (fun r : ℝ => ρ / 2 * r ^ 2)
      (by fun_prop) U hU hsplit

/-- The one-dimensional quadratic Gibbs factor is a scalar multiple of the
actual Gaussian probability measure with variance `1/ρ`. -/
theorem quadratic_gibbs_eq_smul_gaussian {ρ : ℝ} (hρ : 0 < ρ) :
    (volume : Measure ℝ).withDensity (fun r => ENNReal.ofReal (Real.exp (-(ρ / 2 * r ^ 2)))) =
      ENNReal.ofReal (Real.sqrt (2 * Real.pi * ρ⁻¹)) •
        ProbabilityTheory.gaussianReal 0 (ρ⁻¹).toNNReal := by
  have hv : (ρ⁻¹).toNNReal ≠ 0 := by
    exact ne_of_gt (Real.toNNReal_pos.mpr (inv_pos.mpr hρ))
  have hC : 0 < Real.sqrt (2 * Real.pi * ρ⁻¹) := by positivity
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero _ hv,
    ← withDensity_smul _ (ProbabilityTheory.measurable_gaussianPDF _ _)]
  congr 1
  ext r
  simp only [Pi.smul_apply, smul_eq_mul, ProbabilityTheory.gaussianPDF,
    ProbabilityTheory.gaussianPDFReal, Real.coe_toNNReal _ (inv_nonneg.mpr hρ.le), sub_zero]
  rw [← ENNReal.ofReal_mul hC.le]
  congr 1
  have hexp : -(r ^ 2) / (2 * ρ⁻¹) = -(ρ / 2 * r ^ 2) := by
    field_simp
  rw [hexp]
  field_simp

/-- The product factorization in orthogonal coordinates, with its first factor
identified as the genuine Gaussian probability measure. -/
theorem gibbs_map_gaussian_product
    (A : E ≃ₗᵢ[ℝ] WithLp 2 (ℝ × F)) (W : E → ℝ) (hW : Measurable W)
    (hinv : ∀ x : E, ∀ u : ℝ,
      W (x + u • A.symm (WithLp.toLp 2 (1, (0 : F)))) = W x)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ((volume : Measure E).withDensity (fun x =>
        ENNReal.ofReal (Real.exp (-(ρ / 2 * ‖x‖ ^ 2 + W x))))).map
          (fun x => (A x).ofLp) =
      (ProbabilityTheory.gaussianReal 0 (ρ⁻¹).toNNReal).prod
        (ENNReal.ofReal (Real.sqrt (2 * Real.pi * ρ⁻¹)) •
          (volume : Measure F).withDensity (fun y =>
            ENNReal.ofReal (Real.exp
              (-(W (A.symm (WithLp.toLp 2 (0, y))) + ρ / 2 * ‖y‖ ^ 2))))) := by
  rw [gibbs_map_orthogonalCoordinates A W hW hinv ρ,
    quadratic_gibbs_eq_smul_gaussian hρ, Measure.prod_smul_left, Measure.prod_smul_right]

/-- A normalized Gibbs measure with a translation-invariant interaction has a
Gaussian probability factor after the orthogonal change of coordinates.
Normalization is exactly the paper's probability-measure assumption. -/
theorem normalized_gibbs_has_gaussian_factor
    (A : E ≃ₗᵢ[ℝ] WithLp 2 (ℝ × F)) (W : E → ℝ) (hW : Measurable W)
    (hinv : ∀ x : E, ∀ u : ℝ,
      W (x + u • A.symm (WithLp.toLp 2 (1, (0 : F)))) = W x)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hprob : IsProbabilityMeasure ((volume : Measure E).withDensity (fun x =>
      ENNReal.ofReal (Real.exp (-(ρ / 2 * ‖x‖ ^ 2 + W x)))))) :
    ∃ ν : Measure F, IsProbabilityMeasure ν ∧
      ((volume : Measure E).withDensity (fun x =>
        ENNReal.ofReal (Real.exp (-(ρ / 2 * ‖x‖ ^ 2 + W x))))).map
          (fun x => (A x).ofLp) =
        (ProbabilityTheory.gaussianReal 0 (ρ⁻¹).toNNReal).prod ν := by
  let ν : Measure F := ENNReal.ofReal (Real.sqrt (2 * Real.pi * ρ⁻¹)) •
    (volume : Measure F).withDensity (fun y =>
      ENNReal.ofReal (Real.exp (-(W (A.symm (WithLp.toLp 2 (0, y))) + ρ / 2 * ‖y‖ ^ 2))))
  have hfactor := gibbs_map_gaussian_product A W hW hinv hρ
  change _ = (ProbabilityTheory.gaussianReal 0 (ρ⁻¹).toNNReal).prod ν at hfactor
  refine ⟨ν, ?_, hfactor⟩
  have hproduct : IsProbabilityMeasure
      ((ProbabilityTheory.gaussianReal 0 (ρ⁻¹).toNNReal).prod ν) := by
    rw [← hfactor]
    exact (Measure.isProbabilityMeasure_map_iff (by fun_prop)).2 hprob
  have hsecond : IsProbabilityMeasure
      (((ProbabilityTheory.gaussianReal 0 (ρ⁻¹).toNNReal).prod ν).map Prod.snd) :=
    (Measure.isProbabilityMeasure_map_iff measurable_snd.aemeasurable).2 hproduct
  simpa using hsecond

/-- Canonical orthogonal coordinates along a specified unit vector and its
actual orthogonal complement. -/
noncomputable def unitDirectionCoordinates (v : E) (hv : ‖v‖ = 1) :
    E ≃ₗᵢ[ℝ] WithLp 2 (ℝ × (Submodule.span ℝ {v})ᗮ) :=
  (Submodule.span ℝ {v}).orthogonalDecomposition.trans
    (LinearIsometryEquiv.withLpProdCongr 2
      (LinearIsometryEquiv.toSpanUnitSingleton v hv).symm
      (LinearIsometryEquiv.refl ℝ (Submodule.span ℝ {v})ᗮ))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The first coordinate direction is exactly the specified unit vector. -/
theorem unitDirectionCoordinates_symm_one_zero (v : E) (hv : ‖v‖ = 1) :
    (unitDirectionCoordinates v hv).symm
      (WithLp.toLp 2 (1, (0 : (Submodule.span ℝ {v})ᗮ))) = v := by
  simp [unitDirectionCoordinates, Submodule.orthogonalDecomposition_symm_apply]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The inverse of the canonical orthogonal coordinates recombines the two components. -/
theorem unitDirectionCoordinates_symm_apply (v : E) (hv : ‖v‖ = 1) (t : ℝ)
    (w : (Submodule.span ℝ {v})ᗮ) :
    (unitDirectionCoordinates v hv).symm (WithLp.toLp 2 (t, w)) = t • v + (w : E) := by
  simp [unitDirectionCoordinates, Submodule.orthogonalDecomposition_symm_apply]
  rfl

/-- The Gaussian factorization for an arbitrary specified unit invariant
direction, with the orthogonal coordinate isometry constructed explicitly. -/
theorem normalized_gibbs_unit_direction_factor
    (v : E) (hv : ‖v‖ = 1) (W : E → ℝ) (hW : Measurable W)
    (hinv : ∀ x : E, ∀ u : ℝ, W (x + u • v) = W x)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hprob : IsProbabilityMeasure ((volume : Measure E).withDensity (fun x =>
      ENNReal.ofReal (Real.exp (-(ρ / 2 * ‖x‖ ^ 2 + W x)))))) :
    ∃ ν : Measure (Submodule.span ℝ {v})ᗮ, IsProbabilityMeasure ν ∧
      ((volume : Measure E).withDensity (fun x =>
        ENNReal.ofReal (Real.exp (-(ρ / 2 * ‖x‖ ^ 2 + W x))))).map
          (fun x => (unitDirectionCoordinates v hv x).ofLp) =
        (ProbabilityTheory.gaussianReal 0 (ρ⁻¹).toNNReal).prod ν := by
  apply normalized_gibbs_has_gaussian_factor (unitDirectionCoordinates v hv) W hW _ hρ hprob
  intro x u
  rw [unitDirectionCoordinates_symm_one_zero]
  exact hinv x u

end CoordinateMeasures

end CutoffRigidity
