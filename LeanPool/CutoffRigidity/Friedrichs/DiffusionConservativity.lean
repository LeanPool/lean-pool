/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.Friedrichs.DiffusionPositivity
import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedCutoffs

/-! # Conservativity of the weighted diffusion semigroup -/

@[expose] public section

open Bundle Filter MeasureTheory Set
open scoped ContDiff InnerProductSpace Manifold NNReal Topology

namespace CutoffRigidity.Riemann.Diff

open CutCur

namespace FormData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  (S : FormData H)

/-- A vector of zero closed energy is fixed by the unit-parameter resolvent. -/
theorem R_apply_of_energy_eq_zero (u : S.Q) (hu : S.E u u = 0) : S.R (u : H) = u := by
  obtain ⟨v, rfl⟩ := S.qEquiv.surjective u
  rw [E_eq, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, sub_eq_zero] at hu
  have hadj : ContinuousLinearMap.adjoint S.ι (S.ι v) = v := by
    have hnorm := S.norm_adjoint_ι_le (S.ι v)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hdiff : ‖v - ContinuousLinearMap.adjoint S.ι (S.ι v)‖ ^ 2 ≤ 0 := by
      rw [norm_sub_sq_real, ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq,
        hu]
      linarith only [hsq]
    exact (sub_eq_zero.mp (norm_eq_zero.mp ((sq_nonpos_iff _).mp hdiff))).symm
  rw [qEquiv_apply, R_apply, hadj]

end FormData

section Constants

variable {M : Type} [MeasurableSpace M]

/-- The constant function with value one as a vector in `L²(μ)`. -/
noncomputable def oneL2 (μ : Measure M) [IsFiniteMeasure μ] : M →₂[μ] ℝ :=
  Lp.const 2 μ (1 : ℝ)

/-- The constant `L²` vector is represented by the pointwise constant one almost everywhere. -/
theorem coeFn_oneL2 (μ : Measure M) [IsFiniteMeasure μ] :
    (oneL2 μ : M → ℝ) =ᵐ[μ] fun _ => (1 : ℝ) :=
  Lp.coeFn_const 2 μ (1 : ℝ)

private theorem inner_oneL2 {μ : Measure M} [IsFiniteMeasure μ] (u : M →₂[μ] ℝ) :
    inner ℝ u (oneL2 μ) = ∫ x, u x ∂μ := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_oneL2 μ] with x hx
  simp [hx]

end Constants

section CutoffConvergence

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [MeasurableSpace M] [BorelSpace M]
  {μ : Measure M} [IsFiniteMeasure μ]

private theorem tendsto_cutoffs_testToL2 (χ : ℕ → testSub F M)
    (bounds : ∀ n x, 0 ≤ (χ n : M → ℝ) x ∧ (χ n : M → ℝ) x ≤ 1)
    (eventual : ∀ x, ∀ᶠ n in atTop, (χ n : M → ℝ) x = 1) :
    Tendsto (fun n => testToL2 F μ (χ n)) atTop (𝓝 (oneL2 μ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsq (n : ℕ) : ‖testToL2 F μ (χ n) - oneL2 μ‖ ^ 2 =
      ∫ x, ((χ n : M → ℝ) x - 1) ^ 2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub (testToL2 F μ (χ n)) (oneL2 μ), coeFn_oneL2 μ,
      coeFn_testToL2 F μ (χ n)] with x hsub hone hχ
    rw [hsub, Pi.sub_apply, hone, hχ]
    simp [sq]
  have hint : Tendsto (fun n => ∫ x, ((χ n : M → ℝ) x - 1) ^ 2 ∂μ) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence (μ := μ) (fun _ => (1 : ℝ))
      (F := fun n x => ((χ n : M → ℝ) x - 1) ^ 2) (f := fun _ => 0)
      (fun n => ((χ n).2.1.continuous.sub continuous_const).pow 2 |>.aestronglyMeasurable)
      (integrable_const _) (fun n => Eventually.of_forall fun x => by
        obtain ⟨hzero, hone⟩ := bounds n x
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), sq_le_one_iff_abs_le_one,
          abs_of_nonpos (sub_nonpos.mpr hone), neg_sub]
        exact sub_le_self 1 hzero)
      (Eventually.of_forall fun x => by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventual x] with n hn
        simp [hn])
    simpa using h
  have h := (Real.continuous_sqrt.tendsto 0).comp (show
    Tendsto (fun n => ‖testToL2 F μ (χ n) - oneL2 μ‖ ^ 2) atTop (𝓝 0) by
      simpa only [hsq] using hint)
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using h

end CutoffConvergence

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M] [BorelSpace M]
  {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsFiniteMeasure μ]
  (hμ : IsWeightedVolume F μ V)

/-- The weighted diffusion semigroup is order-preserving. -/
theorem diffusion_semigroup_monotone (time : ℝ≥0) :
    Monotone ((diffFormData F hV hμ).semigroup time) := by
  refine (monotone_iff_map_nonneg _).mpr fun u hu => (Lp.coeFn_nonneg _).mp ?_
  exact diffusion_semigroup_nonneg F hV hμ time u ((Lp.coeFn_nonneg u).mpr hu)

variable [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]

/-- On a complete connected manifold the constant one belongs to the closed form domain
and has zero energy. -/
theorem oneL2_mem_diffusion_form_zero_energy :
    ∃ u : (diffFormData F hV hμ).Q, (u : M →₂[μ] ℝ) = oneL2 μ ∧
      (diffFormData F hV hμ).E u u = 0 := by
  let S := diffFormData F hV hμ
  obtain ⟨χ, hχ, hlim⟩ := weightedCutoffs_of_complete F (M := M)
  let a (n : ℕ) : testSub F M := ⟨χ n, (hχ n).1, (hχ n).2.1⟩
  let core (n : ℕ) : S.Dom := ⟨testToL2 F μ (a n), a n, rfl⟩
  let seq (n : ℕ) : S.Q := ⟨S.emb (core n), S.emb_mem_Q (core n)⟩
  have hconv : Tendsto (fun n => (seq n : M →₂[μ] ℝ)) atTop (𝓝 (oneL2 μ)) :=
    tendsto_cutoffs_testToL2 F a (fun n x => ⟨((hχ n).2.2 x).1, ((hχ n).2.2 x).2.1⟩) hlim
  have hle (n : ℕ) : S.E (seq n) (seq n) ≤ (1 / ((n : ℝ) + 1)) ^ 2 * μ.real univ := by
    rw [S.E_emb (core n) (core n)]
    change (inner ℝ (S.opA (core n)) (testToL2 F μ (a n))) ≤ _
    rw [en_diffFormData F hV hμ (a n) (a n)]
    calc
      _ ≤ ∫ _ : M, (1 / ((n : ℝ) + 1)) ^ 2 ∂μ := by
        refine integral_mono (integrable_carre F (a n) (a n)) (integrable_const _) fun x => ?_
        rw [carre_self_eq]
        exact pow_le_pow_left₀ (norm_nonneg _) ((hχ n).2.2 x).2.2 2
      _ = _ := by simp [mul_comm]
  have hupper : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) ^ 2 * μ.real univ) atTop (𝓝 0) := by
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat.pow 2).mul_const (μ.real univ)
  have bound (ε : ℝ) (hε : 0 < ε) :
      ∃ u : S.Q, (u : M →₂[μ] ℝ) = oneL2 μ ∧ S.E u u ≤ ε :=
    S.energy_le_of_tendsto hconv ((hupper.eventually_lt_const hε).mono fun n hn =>
      (hle n).trans hn.le)
  obtain ⟨u, hu, _⟩ := bound 1 one_pos
  refine ⟨u, hu, le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) (S.E_nonneg u)⟩
  obtain ⟨v, hv, hve⟩ := bound ε hε
  have huv : u = v := Subtype.ext (hu.trans hv.symm)
  simpa only [huv, zero_add] using hve

private theorem diffusion_R_one :
    (diffFormData F hV hμ).R (oneL2 μ) = oneL2 μ := by
  obtain ⟨u, hu, he⟩ := oneL2_mem_diffusion_form_zero_energy F hV hμ
  rw [← hu]
  exact (diffFormData F hV hμ).R_apply_of_energy_eq_zero u he

/-- The weighted diffusion resolvent sends one to the inverse parameter times one. -/
theorem diffusion_resolvent_one {parameter : ℝ} (hparameter : 0 < parameter) :
    (diffFormData F hV hμ).resolvent parameter (oneL2 μ) = parameter⁻¹ • oneL2 μ := by
  simpa [FormData.resolvent] using resolventLam_apply_eigen
    (diffFormData F hV hμ).R_unitOp hparameter one_pos le_rfl
    (by simpa using diffusion_R_one F hV hμ)

/-- The weighted diffusion semigroup fixes the constant one at every nonnegative time. -/
theorem diffusion_semigroup_one (time : ℝ≥0) :
    (diffFormData F hV hμ).semigroup time (oneL2 μ) = oneL2 μ := by
  simpa using (diffFormData F hV hμ).semigroup_eigen (c := 0) le_rfl
    (by simpa using diffusion_R_one F hV hμ) time

/-- The weighted diffusion semigroup preserves the order interval from zero to one. -/
theorem diffusion_semigroup_mapsTo_zero_one (time : ℝ≥0) :
    MapsTo ((diffFormData F hV hμ).semigroup time) (Icc 0 (oneL2 μ)) (Icc 0 (oneL2 μ)) := by
  intro u hu
  have h := diffusion_semigroup_monotone F hV hμ time
  exact ⟨by simpa only [map_zero] using h hu.1,
    by simpa only [diffusion_semigroup_one F hV hμ] using h hu.2⟩

/-- The weighted diffusion semigroup preserves the integral of every `L²(μ)` vector. -/
theorem diffusion_semigroup_preserves_integral (time : ℝ≥0) (u : M →₂[μ] ℝ) :
    ∫ x, (diffFormData F hV hμ).semigroup time u x ∂μ = ∫ x, u x ∂μ := by
  let S := diffFormData F hV hμ
  rw [← inner_oneL2, ← inner_oneL2]
  calc
    _ = inner ℝ u (S.semigroup time (oneL2 μ)) :=
      ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (S.semigroup_isSelfAdjoint time) _ _
    _ = _ := congrArg (inner ℝ u) (diffusion_semigroup_one F hV hμ time)

end CutoffRigidity.Riemann.Diff
