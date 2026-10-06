/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Comparison.AdmissibleWeakDivergence
public import LeanPool.CIVAxisymmetric.Comparison.MollifiedEquation
public import LeanPool.CIVAxisymmetric.Comparison.SliceBounds
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Const
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# A constant is a distributional solution of the drift-diffusion equation

For every admissible drift `(B, div B)` (`IsAdmissibleDrift`) and every constant `c`, the
constant function is a distributional solution of `eq:aniso:comparison:equation` on
`Vec m × I` (`IsDistributionalDriftDiffusion`): against any test function `φ`, each of the
three pairings `∫ timeDeriv φ`, `∫ partialLaplacian φ`, and `∫ (gradPair φ (B·) + div B · φ)`
vanishes over the whole space, the first two because a compactly supported smooth function's
directional derivative integrates to zero, the third by Fubini together with the admissible
drift's weak-divergence identity `isAdmissibleDrift_weak_divergence`.
-/

public section

open MeasureTheory Measure Set CKN Filter

noncomputable section
namespace CIV

/-! ### Bridging the frozen slice derivatives to the joint `fderiv` -/

/-- The spatial slice derivative of a joint function at a fixed time is the joint derivative
paired with a spatial direction. -/
theorem fderiv_slice_fst_eq {m : ℕ} {ψ : Vec m × ℝ → ℝ} {z : Vec m × ℝ}
    (hψ : DifferentiableAt ℝ ψ z) (v : Vec m) :
    fderiv ℝ (fun x : Vec m => ψ (x, z.2)) z.1 v = fderiv ℝ ψ z (v, 0) := by
  have he : HasFDerivAt (fun x : Vec m => ((x, z.2) : Vec m × ℝ))
      (ContinuousLinearMap.id ℝ (Vec m) |>.prod 0) z.1 :=
    (hasFDerivAt_id z.1).prodMk (hasFDerivAt_const z.2 z.1)
  have hcomp : HasFDerivAt (fun x : Vec m => ψ (x, z.2))
      ((fderiv ℝ ψ z).comp (ContinuousLinearMap.id ℝ (Vec m) |>.prod 0)) z.1 :=
    (hψ.hasFDerivAt).comp z.1 he
  have := hcomp.fderiv
  rw [this]; simp

/-- The time slice derivative of a joint function at a fixed point is the joint derivative
paired with the time direction. -/
theorem fderiv_slice_snd_eq {m : ℕ} {ψ : Vec m × ℝ → ℝ} {z : Vec m × ℝ}
    (hψ : DifferentiableAt ℝ ψ z) (h : ℝ) :
    fderiv ℝ (fun τ : ℝ => ψ (z.1, τ)) z.2 h = fderiv ℝ ψ z (0, h) := by
  have he : HasFDerivAt (fun τ : ℝ => ((z.1, τ) : Vec m × ℝ))
      ((0 : ℝ →L[ℝ] Vec m).prod (ContinuousLinearMap.id ℝ ℝ)) z.2 :=
    (hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2)
  have hcomp : HasFDerivAt (fun τ : ℝ => ψ (z.1, τ))
      ((fderiv ℝ ψ z).comp ((0 : ℝ →L[ℝ] Vec m).prod (ContinuousLinearMap.id ℝ ℝ))) z.2 :=
    (hψ.hasFDerivAt).comp z.2 he
  have := hcomp.fderiv
  rw [this]; simp

theorem timeDeriv_eq_fderiv_apply {m : ℕ} {φ : Vec m × ℝ → ℝ} {z : Vec m × ℝ}
    (hφ : DifferentiableAt ℝ φ z) : timeDeriv m φ z = fderiv ℝ φ z (0, 1) :=
  fderiv_slice_snd_eq hφ 1

theorem gradPair_eq_fderiv_apply {m : ℕ} {ψ : Vec m × ℝ → ℝ} {z : Vec m × ℝ}
    (hψ : DifferentiableAt ℝ ψ z) (v : Vec m) :
    gradPair m ψ z v = fderiv ℝ ψ z (v, 0) :=
  fderiv_slice_fst_eq hψ v

/-! ### Compact support and continuity of the spatial slice and its gradient pairing -/

theorem hasCompactSupport_slice_fst {m : ℕ} {φ : Vec m × ℝ → ℝ}
    (hsupp : HasCompactSupport φ) (τ : ℝ) :
    HasCompactSupport (fun x : Vec m => φ (x, τ)) := by
  have hcont : Continuous (fun x : Vec m => ((x, τ) : Vec m × ℝ)) :=
    continuous_id.prodMk continuous_const
  have hsub : tsupport (fun x : Vec m => φ (x, τ)) ⊆
      (fun x : Vec m => ((x, τ) : Vec m × ℝ)) ⁻¹' tsupport φ :=
    tsupport_comp_subset_preimage φ hcont
  have hcpt : IsCompact (Prod.fst '' tsupport φ) := hsupp.image continuous_fst
  refine IsCompact.of_isClosed_subset hcpt (isClosed_tsupport _) ?_
  refine hsub.trans ?_
  rintro x hx
  exact ⟨(x, τ), hx, rfl⟩

theorem continuous_gradPair_joint {m : ℕ} {φ : Vec m × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (v : Vec m) : Continuous (fun z : Vec m × ℝ => gradPair m φ z v) := by
  have heq : (fun z : Vec m × ℝ => gradPair m φ z v) = fun z => fderiv ℝ φ z (v, 0) := by
    funext z; exact gradPair_eq_fderiv_apply (hφ.differentiable (by simp) z) v
  rw [heq]
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ φ) := hφ.fderiv_right (by simp)
  exact h1.continuous.clm_apply continuous_const

theorem hasCompactSupport_gradPair_joint {m : ℕ} {φ : Vec m × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsupp : HasCompactSupport φ) (v : Vec m) :
    HasCompactSupport (fun z : Vec m × ℝ => gradPair m φ z v) := by
  have heq : (fun z : Vec m × ℝ => gradPair m φ z v) = fun z => fderiv ℝ φ z (v, 0) := by
    funext z; exact gradPair_eq_fderiv_apply (hφ.differentiable (by simp) z) v
  rw [heq]
  exact hsupp.fderiv_apply (𝕜 := ℝ) (v, 0)

theorem tsupport_gradPair_joint_subset {m : ℕ} {φ : Vec m × ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (v : Vec m) : tsupport (fun z : Vec m × ℝ => gradPair m φ z v) ⊆ tsupport φ := by
  have heq : (fun z : Vec m × ℝ => gradPair m φ z v) = fun z => fderiv ℝ φ z (v, 0) := by
    funext z; exact gradPair_eq_fderiv_apply (hφ.differentiable (by simp) z) v
  rw [heq]
  exact tsupport_fderiv_apply_subset ℝ (v, 0)

/-! ### From a slicewise a.e. property to the product-measure a.e. property -/

theorem ae_prod_of_ae_forall {m : ℕ} {J : Set ℝ} {P : ℝ → Prop} {Q : Vec m → ℝ → Prop}
    (hP : ∀ᵐ τ ∂(volume.restrict J), P τ) (hQ : ∀ τ, P τ → ∀ x, Q x τ) :
    ∀ᵐ z ∂((volume : Measure (Vec m)).prod (volume.restrict J)), Q z.1 z.2 := by
  rw [ae_iff] at hP ⊢
  have hsub : {z : Vec m × ℝ | ¬ Q z.1 z.2} ⊆ (univ : Set (Vec m)) ×ˢ {τ | ¬ P τ} := by
    rintro ⟨x, τ⟩ (hxτ : ¬ Q x τ)
    exact ⟨mem_univ _, fun hPτ => hxτ (hQ τ hPτ x)⟩
  refine measure_mono_null hsub ?_
  rw [Measure.prod_prod, hP, mul_zero]

theorem isLocallyBoundedOn_divB_of_isAdmissibleDrift {m : ℕ} {I : Set ℝ}
    {B : Vec m × ℝ → Vec m} {divB : Vec m × ℝ → ℝ} (hB : IsAdmissibleDrift m I B divB) :
    IsLocallyBoundedOn m I divB := by
  refine ⟨hB.2.1.aestronglyMeasurable, ?_⟩
  intro J hJ hJI
  obtain ⟨Λ, hΛ⟩ := hB.ae_slice hJ hJI
  refine ⟨(Λ : ℝ), ?_⟩
  have heq : (volume : Measure (Vec m)).prod (volume.restrict J) =
      volume.restrict ((univ : Set (Vec m)) ×ˢ J) := by
    rw [← Measure.restrict_univ (μ := (volume : Measure (Vec m))), Measure.prod_restrict,
      ← Measure.volume_eq_prod]
  rw [← heq]
  exact ae_prod_of_ae_forall hΛ (fun τ hτ x => hτ.2.2 x)

theorem isLocallyBoundedOn_component_of_isAdmissibleDrift {m : ℕ} {I : Set ℝ}
    {B : Vec m × ℝ → Vec m} {divB : Vec m × ℝ → ℝ} (hB : IsAdmissibleDrift m I B divB)
    (i : Fin m) : IsLocallyBoundedOn m I (fun z => B z i) := by
  refine ⟨((measurable_pi_apply i).comp hB.1).aestronglyMeasurable, ?_⟩
  intro J hJ hJI
  obtain ⟨Λ, hΛ⟩ := hB.ae_slice hJ hJI
  refine ⟨(Λ : ℝ), ?_⟩
  have heq : (volume : Measure (Vec m)).prod (volume.restrict J) =
      volume.restrict ((univ : Set (Vec m)) ×ˢ J) := by
    rw [← Measure.restrict_univ (μ := (volume : Measure (Vec m))), Measure.prod_restrict,
      ← Measure.volume_eq_prod]
  rw [← heq]
  refine ae_prod_of_ae_forall (Q := fun x τ => |B (x, τ) i| ≤ (Λ : ℝ)) hΛ (fun τ hτ x => ?_)
  exact (norm_le_pi_norm (B (x, τ)) i).trans (hτ.1 x)

/-! ### A compactly supported smooth function's directional derivative integrates to zero -/

theorem isAddHaarMeasure_volume_prod (m : ℕ) :
    (volume : Measure (Vec m × ℝ)).IsAddHaarMeasure := by
  rw [Measure.volume_eq_prod]; infer_instance

/-- A directional derivative of a compactly supported smooth function is globally
integrable against any additive Haar measure. -/
theorem integrable_fderiv_apply_of_hasCompactSupport {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {k : E → ℝ} (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hsupp : HasCompactSupport k) (v : E) :
    Integrable (fun x => fderiv ℝ k x v) μ := by
  have hdc : Continuous (fun x => fderiv ℝ k x v) := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ k) := hk.fderiv_right (by simp)
    exact h1.continuous.clm_apply continuous_const
  have hdsupp : HasCompactSupport (fun x => fderiv ℝ k x v) := hsupp.fderiv_apply (𝕜 := ℝ) v
  exact hdc.integrable_of_hasCompactSupport hdsupp

/-- A compactly supported smooth function's directional derivative integrates to zero over the
whole space, for any additive Haar measure. This is the divergence theorem for a single
direction, with no boundary term since `k` vanishes outside a compact set. -/
theorem integral_fderiv_apply_eq_zero_of_hasCompactSupport {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {k : E → ℝ} (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hsupp : HasCompactSupport k) (v : E) :
    ∫ x, fderiv ℝ k x v ∂μ = 0 := by
  have hkc : Continuous k := hk.continuous
  have hd : Integrable (fun x => fderiv ℝ k x v) μ :=
    integrable_fderiv_apply_of_hasCompactSupport hk hsupp v
  have hfg' : Integrable (fun x => (1 : ℝ) * fderiv ℝ k x v) μ := by simpa using hd
  have hfg : Integrable (fun x => (1 : ℝ) * k x) μ := by
    simpa using hkc.integrable_of_hasCompactSupport hsupp
  have hf'g : Integrable (fun x => fderiv ℝ (fun _ : E => (1 : ℝ)) x v * k x) μ := by
    simp
  have hf : ∀ x ∈ tsupport k, DifferentiableAt ℝ (fun _ : E => (1 : ℝ)) x :=
    fun x _ => differentiableAt_const _
  have hg : ∀ x ∈ tsupport (fun _ : E => (1 : ℝ)), DifferentiableAt ℝ k x :=
    fun x _ => hk.differentiable (by simp) x
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hf'g hfg' hfg hf hg
  simpa using h

/-! ### The time-derivative and Laplacian pairings vanish over the whole space -/

/-- The time derivative of a test function is globally integrable. -/
theorem integrable_timeDeriv_of_testFunction {m : ℕ} {I : Set ℝ} {φ : Vec m × ℝ → ℝ}
    (hφ : φ ∈ testFunctions m I) : Integrable (fun z : Vec m × ℝ => timeDeriv m φ z) volume := by
  obtain ⟨hφ1, hφ2, -⟩ := hφ
  have := isAddHaarMeasure_volume_prod m
  have heq : (fun z : Vec m × ℝ => timeDeriv m φ z) = fun z => fderiv ℝ φ z (0, 1) := by
    funext z; exact timeDeriv_eq_fderiv_apply (hφ1.differentiable (by simp) z)
  rw [heq]
  exact integrable_fderiv_apply_of_hasCompactSupport hφ1 hφ2 (0, 1)

/-- The integral over the whole space of a test function's time derivative vanishes. -/
theorem integral_timeDeriv_eq_zero {m : ℕ} {I : Set ℝ} {φ : Vec m × ℝ → ℝ}
    (hφ : φ ∈ testFunctions m I) : ∫ z : Vec m × ℝ, timeDeriv m φ z = 0 := by
  obtain ⟨hφ1, hφ2, -⟩ := hφ
  have := isAddHaarMeasure_volume_prod m
  have heq : (fun z : Vec m × ℝ => timeDeriv m φ z) = fun z => fderiv ℝ φ z (0, 1) := by
    funext z; exact timeDeriv_eq_fderiv_apply (hφ1.differentiable (by simp) z)
  rw [heq]
  exact integral_fderiv_apply_eq_zero_of_hasCompactSupport hφ1 hφ2 (0, 1)

/-- The partial Laplacian of a test function is, term by term, a second full-space directional
derivative of `φ`; this packages the common construction feeding both its integrability and
its vanishing integral. -/
private theorem partialLaplacian_integrable_and_zero {m : ℕ} (d : ℕ) {I : Set ℝ}
    {φ : Vec m × ℝ → ℝ} (hφ : φ ∈ testFunctions m I) :
    Integrable (fun z : Vec m × ℝ => partialLaplacian m d φ z) volume ∧
      ∫ z : Vec m × ℝ, partialLaplacian m d φ z = 0 := by
  obtain ⟨hφ1, hφ2, -⟩ := hφ
  have haar := isAddHaarMeasure_volume_prod m
  set Ψ : Fin m → Vec m × ℝ → ℝ := fun i z => fderiv ℝ φ z (basisVec i, 0) with hΨdef
  have hΨcont : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (Ψ i) := by
    intro i
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ φ) := hφ1.fderiv_right (by simp)
    exact (ContinuousLinearMap.apply ℝ ℝ (basisVec i, (0 : ℝ))).contDiff.comp h1
  have hΨsupp : ∀ i, HasCompactSupport (Ψ i) := fun i => hφ2.fderiv_apply (𝕜 := ℝ) (basisVec i, 0)
  have hterm : ∀ z : Vec m × ℝ, ∀ i : Fin m,
      fderiv ℝ (fun x : Vec m => fderiv ℝ (fun y : Vec m => φ (y, z.2)) x (basisVec i))
        z.1 (basisVec i) = fderiv ℝ (Ψ i) z (basisVec i, 0) := by
    intro z i
    have hinner : (fun x : Vec m => fderiv ℝ (fun y : Vec m => φ (y, z.2)) x (basisVec i))
        = fun x : Vec m => Ψ i (x, z.2) := by
      funext x
      exact gradPair_eq_fderiv_apply (hφ1.differentiable (by simp) (x, z.2)) (basisVec i)
    rw [hinner]
    exact fderiv_slice_fst_eq ((hΨcont i).differentiable (by simp) z) (basisVec i)
  have hpl : (fun z : Vec m × ℝ => partialLaplacian m d φ z) = fun z =>
      ∑ i : Fin m, if (i : ℕ) < d then fderiv ℝ (Ψ i) z (basisVec i, 0) else 0 := by
    funext z
    show (∑ i : Fin m, if (i : ℕ) < d then
        fderiv ℝ (fun x : Vec m => fderiv ℝ (fun y : Vec m => φ (y, z.2)) x (basisVec i))
          z.1 (basisVec i) else 0) = _
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs with hi
    · exact hterm z i
    · rfl
  have hint : ∀ i : Fin m, Integrable (fun z : Vec m × ℝ =>
      if (i : ℕ) < d then fderiv ℝ (Ψ i) z (basisVec i, 0) else 0) volume := by
    intro i
    by_cases hi : (i : ℕ) < d
    · simpa [hi] using integrable_fderiv_apply_of_hasCompactSupport (hΨcont i) (hΨsupp i)
        (basisVec i, 0)
    · simp [hi]
  refine ⟨by rw [hpl]; exact integrable_finsetSum Finset.univ (fun i _ => hint i), ?_⟩
  rw [hpl, integral_finsetSum Finset.univ (fun i _ => hint i)]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  by_cases hi : (i : ℕ) < d
  · simp only [ite_eq_left hi]
    exact integral_fderiv_apply_eq_zero_of_hasCompactSupport (hΨcont i) (hΨsupp i) (basisVec i, 0)
  · simp [hi]

/-- The partial Laplacian of a test function is globally integrable. -/
theorem integrable_partialLaplacian_of_testFunction {m : ℕ} (d : ℕ) {I : Set ℝ}
    {φ : Vec m × ℝ → ℝ} (hφ : φ ∈ testFunctions m I) :
    Integrable (fun z : Vec m × ℝ => partialLaplacian m d φ z) volume :=
  (partialLaplacian_integrable_and_zero d hφ).1

/-- The integral over the whole space of a test function's partial Laplacian vanishes. -/
theorem integral_partialLaplacian_eq_zero {m : ℕ} (d : ℕ) {I : Set ℝ} {φ : Vec m × ℝ → ℝ}
    (hφ : φ ∈ testFunctions m I) : ∫ z : Vec m × ℝ, partialLaplacian m d φ z = 0 :=
  (partialLaplacian_integrable_and_zero d hφ).2

/-! ### The drift pairing is globally integrable and its total pairing vanishes -/

theorem integrable_divB_mul_of_isAdmissibleDrift {m : ℕ} {I : Set ℝ}
    {B : Vec m × ℝ → Vec m} {divB : Vec m × ℝ → ℝ} {φ : Vec m × ℝ → ℝ}
    (hB : IsAdmissibleDrift m I B divB) (hφ : φ ∈ testFunctions m I) :
    Integrable (fun z : Vec m × ℝ => divB z * φ z) volume := by
  obtain ⟨hφ1, hφ2, hφ3⟩ := hφ
  have h := integrable_mul_of_isLocallyBoundedOn
    (isLocallyBoundedOn_divB_of_isAdmissibleDrift hB) hφ1.continuous hφ2 hφ3
  simpa [mul_comm] using h

theorem integrable_gradPair_mul_of_isAdmissibleDrift {m : ℕ} {I : Set ℝ}
    {B : Vec m × ℝ → Vec m} {divB : Vec m × ℝ → ℝ} {φ : Vec m × ℝ → ℝ}
    (hB : IsAdmissibleDrift m I B divB) (hφ : φ ∈ testFunctions m I) :
    Integrable (fun z : Vec m × ℝ => gradPair m φ z (B z)) volume := by
  obtain ⟨hφ1, hφ2, hφ3⟩ := hφ
  have hsum : (fun z : Vec m × ℝ => gradPair m φ z (B z))
      = fun z => ∑ i : Fin m, B z i * gradPair m φ z (basisVec i) := by
    funext z
    exact apply_eq_sum_basisVec (fderiv ℝ (fun x : Vec m => φ (x, z.2)) z.1) (B z)
  rw [hsum]
  refine integrable_finsetSum Finset.univ (fun i _ => ?_)
  have h := integrable_mul_of_isLocallyBoundedOn
    (isLocallyBoundedOn_component_of_isAdmissibleDrift hB i)
    (continuous_gradPair_joint hφ1 (basisVec i))
    (hasCompactSupport_gradPair_joint hφ1 hφ2 (basisVec i))
    ((tsupport_gradPair_joint_subset hφ1 (basisVec i)).trans hφ3)
  simpa [mul_comm] using h

/-- The two commutator-drift terms of the distributional pairing, integrated jointly against
a test function, cancel: the divergence theorem for the truncated Laplacian's first-order
sibling. -/
theorem integral_gradPair_add_divB_mul_eq_zero {m : ℕ} {I : Set ℝ}
    {B : Vec m × ℝ → Vec m} {divB : Vec m × ℝ → ℝ} {φ : Vec m × ℝ → ℝ}
    (hB : IsAdmissibleDrift m I B divB) (hφ : φ ∈ testFunctions m I) :
    ∫ z : Vec m × ℝ, (gradPair m φ z (B z) + divB z * φ z) = 0 := by
  obtain ⟨hφ1, hφ2, hφ3⟩ := hφ
  have hJ : IsCompact (Prod.snd '' tsupport φ) := hφ2.image continuous_snd
  have hJI : (Prod.snd '' tsupport φ) ⊆ I := by
    rintro τ ⟨z, hz, rfl⟩; exact (hφ3 hz).2
  have hGint : Integrable (fun z : Vec m × ℝ => gradPair m φ z (B z)) volume :=
    integrable_gradPair_mul_of_isAdmissibleDrift hB ⟨hφ1, hφ2, hφ3⟩
  have hHint : Integrable (fun z : Vec m × ℝ => divB z * φ z) volume :=
    integrable_divB_mul_of_isAdmissibleDrift hB ⟨hφ1, hφ2, hφ3⟩
  have hvol : (volume : Measure (Vec m × ℝ)) =
      (volume : Measure (Vec m)).prod (volume : Measure ℝ) := Measure.volume_eq_prod _ _
  have hGint' : Integrable (fun z : Vec m × ℝ => gradPair m φ z (B z))
      ((volume : Measure (Vec m)).prod (volume : Measure ℝ)) := by rwa [hvol] at hGint
  have hHint' : Integrable (fun z : Vec m × ℝ => divB z * φ z)
      ((volume : Measure (Vec m)).prod (volume : Measure ℝ)) := by rwa [hvol] at hHint
  rw [hvol, integral_add hGint' hHint', integral_prod_symm _ hGint',
    integral_prod_symm _ hHint', ← integral_add hGint'.integral_prod_right
      hHint'.integral_prod_right]
  have hzero : ∀ᵐ τ ∂(volume : Measure ℝ),
      (∫ x : Vec m, gradPair m φ (x, τ) (B (x, τ))) + (∫ x : Vec m, divB (x, τ) * φ (x, τ)) = 0
        := by
    have hΛ : ∀ᵐ τ ∂(volume.restrict (Prod.snd '' tsupport φ)), ∀ ψ : Vec m → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          ∫ x, divB (x, τ) * ψ x = -∫ x, ∑ i, B (x, τ) i * fderiv ℝ ψ x (basisVec i) :=
      isAdmissibleDrift_weak_divergence hB hJ hJI
    have hΛ' : ∀ᵐ τ ∂(volume : Measure ℝ), τ ∈ Prod.snd '' tsupport φ → ∀ ψ : Vec m → ℝ,
        ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          ∫ x, divB (x, τ) * ψ x = -∫ x, ∑ i, B (x, τ) i * fderiv ℝ ψ x (basisVec i) :=
      (ae_restrict_iff' hJ.measurableSet).mp hΛ
    filter_upwards [hΛ'] with τ hτ
    by_cases hmem : τ ∈ Prod.snd '' tsupport φ
    · have hsl : ∫ x : Vec m, divB (x, τ) * φ (x, τ)
          = -∫ x : Vec m, ∑ i, B (x, τ) i * fderiv ℝ (fun y => φ (y, τ)) x (basisVec i) :=
        hτ hmem (fun x => φ (x, τ)) (hφ1.comp (contDiff_id.prodMk contDiff_const))
          (hasCompactSupport_slice_fst hφ2 τ)
      have hsl2 : ∫ x : Vec m, ∑ i, B (x, τ) i * fderiv ℝ (fun y => φ (y, τ)) x (basisVec i)
          = ∫ x : Vec m, gradPair m φ (x, τ) (B (x, τ)) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        exact (apply_eq_sum_basisVec
          (fderiv ℝ (fun y : Vec m => φ (y, τ)) x) (B (x, τ))).symm
      rw [hsl2] at hsl
      linarith only [hsl]
    · have hz1 : ∀ x : Vec m, gradPair m φ (x, τ) (B (x, τ)) = 0 := by
        intro x
        exact gradPair_eq_zero_of_notMem_tsupport (fun hc => hmem ⟨(x, τ), hc, rfl⟩) (B (x, τ))
      have hz2 : ∀ x : Vec m, divB (x, τ) * φ (x, τ) = 0 := by
        intro x
        rw [image_eq_zero_of_notMem_tsupport (fun hc => hmem ⟨(x, τ), hc, rfl⟩), mul_zero]
      simp [hz1, hz2]
  rw [integral_congr_ae hzero]
  simp

/-! ### The main theorem -/

/-- A constant is a distributional solution of `eq:aniso:comparison:equation` for every
admissible drift. Against any test function `φ`, the pairing splits into the time derivative,
the Laplacian, and the drift terms, each of which integrates to zero over the whole space
(`integral_timeDeriv_eq_zero`, `integral_partialLaplacian_eq_zero`,
`integral_gradPair_add_divB_mul_eq_zero`), so the total pairing against the constant `c`
vanishes as well. -/
theorem isDistributionalDriftDiffusion_const {m d : ℕ} {I : Set ℝ} {B : Vec m × ℝ → Vec m}
    {divB : Vec m × ℝ → ℝ} (hB : IsAdmissibleDrift m I B divB) (c : ℝ) :
    IsDistributionalDriftDiffusion m d I B divB (fun _ => c) := by
  intro φ hφ
  have htD : Integrable (fun z : Vec m × ℝ => timeDeriv m φ z) volume :=
    integrable_timeDeriv_of_testFunction hφ
  have hpL : Integrable (fun z : Vec m × ℝ => partialLaplacian m d φ z) volume :=
    integrable_partialLaplacian_of_testFunction d hφ
  have hGB : Integrable (fun z : Vec m × ℝ => gradPair m φ z (B z)) volume :=
    integrable_gradPair_mul_of_isAdmissibleDrift hB hφ
  have hHB : Integrable (fun z : Vec m × ℝ => divB z * φ z) volume :=
    integrable_divB_mul_of_isAdmissibleDrift hB hφ
  -- The pointwise-conclusion combinators (`fun_neg`/`fun_add`/`sub'`) are used throughout so
  -- every integrability fact below is literally a function *lambda*, matching the goal's own
  -- shape term-for-term rather than an unapplied `Pi`-algebra combination.
  have hAI : Integrable (fun z : Vec m × ℝ => -(timeDeriv m φ z)) volume := htD.fun_neg
  have hBCI : Integrable (fun z : Vec m × ℝ => gradPair m φ z (B z) + divB z * φ z) volume :=
    hGB.fun_add hHB
  have hsum : Integrable (fun z : Vec m × ℝ => ((-(timeDeriv m φ z)) -
      (gradPair m φ z (B z) + divB z * φ z)) - partialLaplacian m d φ z) volume :=
    (hAI.sub' hBCI).sub' hpL
  have h1 : ∫ z : Vec m × ℝ, timeDeriv m φ z = 0 := integral_timeDeriv_eq_zero hφ
  have h2 : ∫ z : Vec m × ℝ, partialLaplacian m d φ z = 0 :=
    integral_partialLaplacian_eq_zero d hφ
  have h3 : ∫ z : Vec m × ℝ, (gradPair m φ z (B z) + divB z * φ z) = 0 :=
    integral_gradPair_add_divB_mul_eq_zero hB hφ
  have hzero : ∫ z : Vec m × ℝ, (((-(timeDeriv m φ z)) -
      (gradPair m φ z (B z) + divB z * φ z)) - partialLaplacian m d φ z) = 0 := by
    rw [integral_sub (hAI.sub' hBCI) hpL, integral_sub hAI hBCI, integral_neg, h1, h3, h2]
    ring
  have heqpt : ∀ z : Vec m × ℝ, -(timeDeriv m φ z) - gradPair m φ z (B z) - divB z * φ z -
      partialLaplacian m d φ z = ((-(timeDeriv m φ z)) -
      (gradPair m φ z (B z) + divB z * φ z)) - partialLaplacian m d φ z := fun z => by ring
  refine ⟨?_, ?_⟩
  · simp only [heqpt]
    exact (hsum.const_mul c).integrableOn
  · simp only [heqpt]
    rw [integral_const_mul, hzero, mul_zero]

end CIV
