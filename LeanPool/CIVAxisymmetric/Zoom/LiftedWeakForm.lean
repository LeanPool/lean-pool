/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Reduction.ClassicalIBPIntegrability
public import LeanPool.CIVAxisymmetric.Statements.TimeDeriv
public import LeanPool.CIVAxisymmetric.Statements.GradPair
public import LeanPool.CIVAxisymmetric.Statements.PartialLaplacian

/-!
# The weak form of a drift-diffusion equation on `Vec 5 × ℝ` off a closed set

The operators `timeDeriv`, `gradPair` and `partialLaplacian` acting on a smooth test function are
full Fréchet derivatives in the corresponding directions (`timeDeriv_eq_fderiv`,
`gradPair_eq_fderiv`, `partialLaplacian_eq_fderiv`).

If a scalar `q`, a drift `B` with divergence divB, a flux `F` and a source `G` are smooth on an
open set `S` of the lifted variables `(X, Z, τ) ∈ ℝ⁴ × ℝ × ℝ` and satisfy there, pointwise,
`∂_τ q + B · ∇q = Δ_X q + κ ∂_ZZ q + ∂_Z F + G`, then against every test function supported
in `S` the pairing of `q` with the adjoint operator of `eq:aniso:zoom:finite:limit` equals
`κ ∫ q ∂_ZZ ψ - ∫ F ∂_Z ψ + ∫ G ψ` (`integral_liftedResidual_eq`). This is the integration by
parts of the passage to the limit (deviation D17), performed off the axis.
-/

public section

open Set MeasureTheory
open CKN

noncomputable section
namespace CIV

/-- The derivative of the spatial slice of a function of `Vec m × ℝ` is its full derivative in
the corresponding spatial direction. -/
theorem fderiv_slice_fst_apply {m : ℕ} {φ : Vec m × ℝ → ℝ} {x : Vec m} {t : ℝ}
    (hφ : DifferentiableAt ℝ φ (x, t)) (v : Vec m) :
    fderiv ℝ (fun y : Vec m => φ (y, t)) x v = fderiv ℝ φ (x, t) (v, 0) := by
  have hline : HasFDerivAt (fun y : Vec m => (y, t))
      ((ContinuousLinearMap.id ℝ (Vec m)).prod (0 : Vec m →L[ℝ] ℝ)) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const t x)
  have hc : HasFDerivAt (fun y => φ (y, t))
      ((fderiv ℝ φ (x, t)).comp ((ContinuousLinearMap.id ℝ (Vec m)).prod 0)) x :=
    hφ.hasFDerivAt.comp x hline
  rw [hc.fderiv]
  simp

/-- The time derivative of a test function is its full derivative in the direction `(0, 1)`. -/
theorem timeDeriv_eq_fderiv {m : ℕ} {φ : Vec m × ℝ → ℝ} {z : Vec m × ℝ}
    (hφ : DifferentiableAt ℝ φ z) : timeDeriv m φ z = fderiv ℝ φ z (0, 1) := by
  have hline : HasFDerivAt (fun τ : ℝ => (z.1, τ))
      ((0 : ℝ →L[ℝ] Vec m).prod (ContinuousLinearMap.id ℝ ℝ)) z.2 :=
    (hasFDerivAt_const z.1 z.2).prodMk (hasFDerivAt_id z.2)
  have hφ' : DifferentiableAt ℝ φ (z.1, z.2) := hφ
  unfold timeDeriv
  have hc : HasFDerivAt (fun τ => φ (z.1, τ))
      ((fderiv ℝ φ (z.1, z.2)).comp ((0 : ℝ →L[ℝ] Vec m).prod (ContinuousLinearMap.id ℝ ℝ))) z.2 :=
    hφ'.hasFDerivAt.comp z.2 hline
  rw [hc.fderiv]
  simp

/-- The spatial gradient pairing of a test function is its full derivative in the direction
`(v, 0)`. -/
theorem gradPair_eq_fderiv {m : ℕ} {φ : Vec m × ℝ → ℝ} {z : Vec m × ℝ}
    (hφ : DifferentiableAt ℝ φ z) (v : Vec m) : gradPair m φ z v = fderiv ℝ φ z (v, 0) :=
  fderiv_slice_fst_apply (x := z.1) (t := z.2) hφ v

/-- The gradient pairing expands along the coordinate basis. -/
theorem fderiv_apply_eq_sum_basisVec {m : ℕ} (L : Vec m × ℝ →L[ℝ] ℝ) (v : Vec m) :
    L (v, 0) = ∑ i, v i * L (basisVec i, 0) := by
  have hv : ((v, (0 : ℝ)) : Vec m × ℝ) = ∑ i, v i • ((basisVec i, (0 : ℝ)) : Vec m × ℝ) := by
    rw [Prod.ext_iff]
    refine ⟨?_, ?_⟩
    · rw [Prod.fst_sum]
      simp only [Prod.smul_fst]
      exact (sum_smul_basisVec v).symm
    · rw [Prod.snd_sum]
      simp
  rw [hv, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, smul_eq_mul]

/-- The partial Laplacian of a `C²` test function in terms of full second derivatives. -/
theorem partialLaplacian_eq_fderiv {m d : ℕ} {φ : Vec m × ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (z : Vec m × ℝ) :
    partialLaplacian m d φ z = ∑ i : Fin m, if (i : ℕ) < d then
      fderiv ℝ (fun w => fderiv ℝ φ w (basisVec i, 0)) z (basisVec i, 0) else 0 := by
  unfold partialLaplacian
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · have hdiff : ∀ w, DifferentiableAt ℝ φ w := fun w =>
      (hφ.differentiable (by norm_num)) w
    have hin : (fun x : Vec m => fderiv ℝ (fun y : Vec m => φ (y, z.2)) x (basisVec i))
        = fun x : Vec m => (fun w => fderiv ℝ φ w (basisVec i, 0)) (x, z.2) := by
      funext x
      exact fderiv_slice_fst_apply (hdiff (x, z.2)) _
    have hG : DifferentiableAt ℝ (fun w => fderiv ℝ φ w (basisVec i, 0)) (z.1, z.2) := by
      have h1 : ContDiff ℝ 1 (fderiv ℝ φ) := hφ.fderiv_right (by norm_num)
      exact ((h1.clm_apply contDiff_const).differentiable (by norm_num)) _
    rw [hin]
    exact fderiv_slice_fst_apply hG _
  · rfl

/-- Directional derivatives of a function smooth on an open set are smooth there. -/
theorem contDiffOn_fderiv_apply_of_isOpen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} (hS : IsOpen S) {h : E → ℝ} (hh : ContDiffOn ℝ (⊤ : ℕ∞) h S) (v : E) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ h z v) S :=
  (hh.fderiv_of_isOpen hS (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffOn_const

/-- Directional derivatives of a smooth function are smooth. -/
theorem contDiff_fderiv_apply_top {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {h : E → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (v : E) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ h z v) :=
  (hh.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

/-- A function continuous on an open set `S` and vanishing off a compact `K ⊆ S` is
integrable. -/
theorem integrable_of_continuousOn_of_forall_notMem {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [OpensMeasurableSpace E] [T2Space E] {μ : Measure E}
    [IsFiniteMeasureOnCompacts μ] {S K : Set E} (hK : IsCompact K) (hKS : K ⊆ S)
    {f : E → ℝ} (hf : ContinuousOn f S) (h0 : ∀ z, z ∉ K → f z = 0) : Integrable f μ :=
  ((hf.mono hKS).integrableOn_compact hK).integrable_of_forall_notMem_eq_zero h0

/-- One integration by parts, as a pair of integrable terms with vanishing total integral. -/
theorem integrable_and_integral_ibpPair_eq_zero {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    [FiniteDimensional ℝ E] {μ : Measure E} [μ.IsAddHaarMeasure] {S K : Set E}
    (hS : IsOpen S) (hK : IsCompact K) (hKS : K ⊆ S) {h χ : E → ℝ}
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h S) (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχK : tsupport χ ⊆ K) (v : E) :
    Integrable (fun z => h z * fderiv ℝ χ z v + fderiv ℝ h z v * χ z) μ ∧
      ∫ z, (h z * fderiv ℝ χ z v + fderiv ℝ h z v * χ z) ∂μ = 0 := by
  have h1 : Integrable (fun z => h z * fderiv ℝ χ z v) μ :=
    integrable_mul_fderiv_of_continuousOn hK hKS hh.continuousOn hχ hχc hχK
  have h2 : Integrable (fun z => fderiv ℝ h z v * χ z) μ :=
    integrableOn_mul_of_continuousOn_of_tsupport_subset hK hKS
      (contDiffOn_fderiv_apply_of_isOpen hS hh v).continuousOn hχ.continuous hχK
  refine ⟨h1.add h2, ?_⟩
  rw [integral_add h1 h2, integral_mul_fderiv_eq_neg_fderiv_mul_of_continuousOn hS hK hKS hh hχ
    hχc hχK]
  ring

/-- Functions that are integrable with vanishing integral are closed under finite sums. -/
theorem integrable_and_integral_finset_sum_eq_zero {E ι : Type*} [MeasurableSpace E]
    {μ : Measure E} (s : Finset ι) {f : ι → E → ℝ}
    (hf : ∀ i ∈ s, Integrable (f i) μ ∧ ∫ z, f i z ∂μ = 0) :
    Integrable (fun z => ∑ i ∈ s, f i z) μ ∧ ∫ z, ∑ i ∈ s, f i z ∂μ = 0 := by
  refine ⟨integrable_finsetSum s fun i hi => (hf i hi).1, ?_⟩
  rw [integral_finsetSum s fun i hi => (hf i hi).1]
  exact Finset.sum_eq_zero fun i hi => (hf i hi).2

/-- Functions that are integrable with vanishing integral are closed under addition. -/
theorem integrable_and_integral_add_eq_zero {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {f g : E → ℝ} (hf : Integrable f μ ∧ ∫ z, f z ∂μ = 0) (hg : Integrable g μ ∧ ∫ z, g z ∂μ = 0) :
    Integrable (fun z => f z + g z) μ ∧ ∫ z, (f z + g z) ∂μ = 0 :=
  ⟨hf.1.add hg.1, by rw [integral_add hf.1 hg.1, hf.2, hg.2, add_zero]⟩

/-- Functions that are integrable with vanishing integral are closed under subtraction. -/
theorem integrable_and_integral_sub_eq_zero {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {f g : E → ℝ} (hf : Integrable f μ ∧ ∫ z, f z ∂μ = 0) (hg : Integrable g μ ∧ ∫ z, g z ∂μ = 0) :
    Integrable (fun z => f z - g z) μ ∧ ∫ z, (f z - g z) ∂μ = 0 :=
  ⟨hf.1.sub hg.1, by rw [integral_sub hf.1 hg.1, hf.2, hg.2, sub_zero]⟩

/-- Functions that are integrable with vanishing integral are closed under negation. -/
theorem integrable_and_integral_neg_eq_zero {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {f : E → ℝ} (hf : Integrable f μ ∧ ∫ z, f z ∂μ = 0) :
    Integrable (fun z => -f z) μ ∧ ∫ z, -f z ∂μ = 0 :=
  ⟨hf.1.neg, by rw [integral_neg, hf.2, neg_zero]⟩

/-- Functions that are integrable with vanishing integral are closed under scaling. -/
theorem integrable_and_integral_const_mul_eq_zero {E : Type*} [MeasurableSpace E]
    {μ : Measure E} {f : E → ℝ} (c : ℝ) (hf : Integrable f μ ∧ ∫ z, f z ∂μ = 0) :
    Integrable (fun z => c * f z) μ ∧ ∫ z, c * f z ∂μ = 0 :=
  ⟨hf.1.const_mul c, by rw [integral_const_mul, hf.2, mul_zero]⟩

/-- The sum of the first four of five terms, written as the masked sum of `partialLaplacian`. -/
theorem sum_fin_five_ite_lt_four (a : Fin 5 → ℝ) :
    (∑ i : Fin 5, if (i : ℕ) < 4 then a i else 0) = a 0 + a 1 + a 2 + a 3 := by
  rw [Fin.sum_univ_five]
  simp

/-- A derivative of a test function vanishes off its topological support. -/
theorem fderiv_apply_eq_zero_of_notMem_tsupport {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ψ : E → ℝ} {z : E} (hz : z ∉ tsupport ψ) (v : E) :
    fderiv ℝ ψ z v = 0 :=
  image_eq_zero_of_notMem_tsupport (f := fun w => fderiv ℝ ψ w v)
    fun h => hz (tsupport_fderiv_apply_subset ℝ v h)

/-- The integration by parts of the passage to the limit off the axis: if `q`, the drift `B`,
the flux `F` and the source `G` satisfy `∂_τ q + B · ∇q = Δ_X q + κ ∂_ZZ q + ∂_Z F + G`
pointwise on an open set `S`, with divB the divergence of B there, then against every test
function supported in a compact subset of `S` the residual of `eq:aniso:zoom:finite:limit` is
`κ ∫ q ∂_ZZ ψ - ∫ F ∂_Z ψ + ∫ G ψ`. -/
theorem integral_liftedResidual_eq {S K : Set (Vec 5 × ℝ)} (hS : IsOpen S) (hK : IsCompact K)
    (hKS : K ⊆ S) {q Fz G divB : Vec 5 × ℝ → ℝ} {B : Vec 5 × ℝ → Vec 5} (κ : ℝ)
    (hq : ContDiffOn ℝ (⊤ : ℕ∞) q S) (hB : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fun z => B z i) S)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) Fz S) (hG : ContinuousOn G S)
    (hdiv : ∀ z ∈ S, ∑ i, fderiv ℝ (fun w => B w i) z (basisVec i, 0) = divB z)
    (hpde : ∀ z ∈ S, fderiv ℝ q z (0, 1) + ∑ i, B z i * fderiv ℝ q z (basisVec i, 0)
      = (∑ i : Fin 5, if (i : ℕ) < 4 then
          fderiv ℝ (fun w => fderiv ℝ q w (basisVec i, 0)) z (basisVec i, 0) else 0)
        + κ * fderiv ℝ (fun w => fderiv ℝ q w (basisVec 4, 0)) z (basisVec 4, 0)
        + fderiv ℝ Fz z (basisVec 4, 0) + G z)
    {ψ : Vec 5 × ℝ → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψK : tsupport ψ ⊆ K) :
    ∫ z, q z * (-(timeDeriv 5 ψ z) - gradPair 5 ψ z (B z) - divB z * ψ z
        - partialLaplacian 5 4 ψ z)
      = ∫ z, (κ * q z * fderiv ℝ (fun w => fderiv ℝ ψ w (basisVec 4, 0)) z (basisVec 4, 0)
        - Fz z * fderiv ℝ ψ z (basisVec 4, 0) + G z * ψ z) := by
  have : (volume : Measure (Vec 5 × ℝ)).IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  set e : Fin 5 → Vec 5 × ℝ := fun i => (basisVec i, 0) with he
  have hψd : ∀ z, DifferentiableAt ℝ ψ z := fun z => hψ.differentiable (by simp) z
  have hψ2 : ContDiff ℝ 2 ψ := hψ.of_le (by simp)
  -- the partial derivatives of `ψ` are test functions supported in `K`
  have hψ' : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun w => fderiv ℝ ψ w (e i)) := fun i =>
    contDiff_fderiv_apply_top hψ (e i)
  have hψ'c : ∀ i, HasCompactSupport (fun w => fderiv ℝ ψ w (e i)) := fun i =>
    hψc.fderiv_apply ℝ (e i)
  have hψ'K : ∀ i, tsupport (fun w => fderiv ℝ ψ w (e i)) ⊆ K := fun i =>
    (tsupport_fderiv_apply_subset ℝ (e i)).trans hψK
  have hq' : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fun w => fderiv ℝ q w (e i)) S := fun i =>
    contDiffOn_fderiv_apply_of_isOpen hS hq (e i)
  have hqB : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fun w => q w * B w i) S := fun i => hq.mul (hB i)
  -- the integration-by-parts pairs
  have hPt := integrable_and_integral_ibpPair_eq_zero (E := Vec 5 × ℝ) (μ := volume) hS hK hKS
    hq hψ hψc hψK
    ((0 : Vec 5), (1 : ℝ))
  have hPB := fun i => integrable_and_integral_ibpPair_eq_zero (E := Vec 5 × ℝ) (μ := volume) hS
    hK hKS (hqB i)
    hψ hψc hψK (e i)
  have hQ := fun i => integrable_and_integral_ibpPair_eq_zero (E := Vec 5 × ℝ) (μ := volume) hS
    hK hKS hq
    (hψ' i) (hψ'c i) (hψ'K i) (e i)
  have hQ' := fun i => integrable_and_integral_ibpPair_eq_zero (E := Vec 5 × ℝ) (μ := volume) hS
    hK hKS (hq' i)
    hψ hψc hψK (e i)
  have hPF := integrable_and_integral_ibpPair_eq_zero (E := Vec 5 × ℝ) (μ := volume) hS hK hKS
    hF hψ hψc hψK
    (e 4)
  set P : Vec 5 × ℝ → ℝ := fun z =>
    -(q z * fderiv ℝ ψ z ((0 : Vec 5), (1 : ℝ)) + fderiv ℝ q z ((0 : Vec 5), (1 : ℝ)) * ψ z)
      - (∑ i, (q z * B z i * fderiv ℝ ψ z (e i)
          + fderiv ℝ (fun w => q w * B w i) z (e i) * ψ z))
      - (∑ i : Fin 5, if (i : ℕ) < 4 then
          ((q z * fderiv ℝ (fun w => fderiv ℝ ψ w (e i)) z (e i)
              + fderiv ℝ q z (e i) * fderiv ℝ ψ z (e i))
            - (fderiv ℝ q z (e i) * fderiv ℝ ψ z (e i)
              + fderiv ℝ (fun w => fderiv ℝ q w (e i)) z (e i) * ψ z)) else 0)
      - κ * ((q z * fderiv ℝ (fun w => fderiv ℝ ψ w (e 4)) z (e 4)
              + fderiv ℝ q z (e 4) * fderiv ℝ ψ z (e 4))
            - (fderiv ℝ q z (e 4) * fderiv ℝ ψ z (e 4)
              + fderiv ℝ (fun w => fderiv ℝ q w (e 4)) z (e 4) * ψ z))
      + (Fz z * fderiv ℝ ψ z (e 4) + fderiv ℝ Fz z (e 4) * ψ z) with hP_def
  have hPint : Integrable P ∧ ∫ z, P z = 0 := by
    have hsumB := integrable_and_integral_finset_sum_eq_zero (μ := volume) Finset.univ
      (f := fun i z => q z * B z i * fderiv ℝ ψ z (e i)
          + fderiv ℝ (fun w => q w * B w i) z (e i) * ψ z)
      fun i _ => hPB i
    have hsumQ := integrable_and_integral_finset_sum_eq_zero (μ := volume) Finset.univ
      (f := fun (i : Fin 5) z => if (i : ℕ) < 4 then
          ((q z * fderiv ℝ (fun w => fderiv ℝ ψ w (e i)) z (e i)
              + fderiv ℝ q z (e i) * fderiv ℝ ψ z (e i))
            - (fderiv ℝ q z (e i) * fderiv ℝ ψ z (e i)
              + fderiv ℝ (fun w => fderiv ℝ q w (e i)) z (e i) * ψ z)) else 0)
      fun i _ => by
        by_cases hi : (i : ℕ) < 4
        · simp only [hi, ↓reduceIte]
          exact integrable_and_integral_sub_eq_zero (hQ i) (hQ' i)
        · simp only [hi, ↓reduceIte]
          exact ⟨integrable_zero _ _ _, integral_zero _ _⟩
    exact integrable_and_integral_add_eq_zero
      (integrable_and_integral_sub_eq_zero
        (integrable_and_integral_sub_eq_zero
          (integrable_and_integral_sub_eq_zero (integrable_and_integral_neg_eq_zero hPt) hsumB)
          hsumQ)
        (integrable_and_integral_const_mul_eq_zero κ
          (integrable_and_integral_sub_eq_zero (hQ 4) (hQ' 4))))
      hPF
  -- the equation, multiplied by `ψ`, vanishes everywhere
  have hbr : ∀ z, ψ z * (fderiv ℝ q z ((0 : Vec 5), (1 : ℝ))
      + ∑ i, fderiv ℝ (fun w => q w * B w i) z (e i) - q z * divB z
      - (∑ i : Fin 5, if (i : ℕ) < 4 then fderiv ℝ (fun w => fderiv ℝ q w (e i)) z (e i) else 0)
      - κ * fderiv ℝ (fun w => fderiv ℝ q w (e 4)) z (e 4) - fderiv ℝ Fz z (e 4) - G z) = 0 := by
    intro z
    by_cases hz : z ∈ S
    · have hqd : DifferentiableAt ℝ q z :=
        (hq.differentiableOn (by simp) z hz).differentiableAt (hS.mem_nhds hz)
      have hBd : ∀ i, DifferentiableAt ℝ (fun w => B w i) z := fun i =>
        ((hB i).differentiableOn (by simp) z hz).differentiableAt (hS.mem_nhds hz)
      have hprod : ∑ i, fderiv ℝ (fun w => q w * B w i) z (e i)
          = ∑ i, B z i * fderiv ℝ q z (e i)
            + q z * ∑ i, fderiv ℝ (fun w => B w i) z (e i) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hm : HasFDerivAt (fun w => q w * B w i)
            (q z • fderiv ℝ (fun w => B w i) z + B z i • fderiv ℝ q z) z :=
          hqd.hasFDerivAt.mul (hBd i).hasFDerivAt
        rw [hm.fderiv]
        simp only [add_apply, smul_apply, smul_eq_mul]
        ring
      have h1 := hpde z hz
      have h2 := hdiv z hz
      rw [hprod]
      linear_combination ψ z * h1 + ψ z * q z * h2
    · have : ψ z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (hKS (hψK h))
      rw [this, zero_mul]
  -- the pointwise identity
  have hpt : ∀ z, q z * (-(timeDeriv 5 ψ z) - gradPair 5 ψ z (B z) - divB z * ψ z
        - partialLaplacian 5 4 ψ z)
      = (κ * q z * fderiv ℝ (fun w => fderiv ℝ ψ w (basisVec 4, 0)) z (basisVec 4, 0)
        - Fz z * fderiv ℝ ψ z (basisVec 4, 0) + G z * ψ z) + P z := by
    intro z
    have hb := hbr z
    rw [timeDeriv_eq_fderiv (hψd z), gradPair_eq_fderiv (hψd z),
      fderiv_apply_eq_sum_basisVec, partialLaplacian_eq_fderiv hψ2]
    simp only [hP_def, he, sum_fin_five_ite_lt_four] at hb ⊢
    simp only [Fin.sum_univ_five] at hb ⊢
    linear_combination hb
  -- the right side is integrable
  have hRint : Integrable (fun z => κ * q z * fderiv ℝ (fun w => fderiv ℝ ψ w (basisVec 4, 0)) z
      (basisVec 4, 0) - Fz z * fderiv ℝ ψ z (basisVec 4, 0) + G z * ψ z) := by
    refine integrable_of_continuousOn_of_forall_notMem hK hKS ?_ ?_
    · have c1 : ContinuousOn (fun z => fderiv ℝ (fun w => fderiv ℝ ψ w (basisVec 4, 0)) z
          (basisVec 4, 0)) S :=
        (contDiff_fderiv_apply_top (hψ' 4) (e 4)).continuous.continuousOn
      have c2 : ContinuousOn (fun z => fderiv ℝ ψ z (basisVec 4, 0)) S :=
        (hψ' 4).continuous.continuousOn
      exact ((continuousOn_const.mul hq.continuousOn).mul c1).sub (hF.continuousOn.mul c2)
        |>.add (hG.mul hψ.continuous.continuousOn)
    · intro z hz
      have hz' : z ∉ tsupport ψ := fun h => hz (hψK h)
      have hz'' : z ∉ tsupport (fun w => fderiv ℝ ψ w (basisVec 4, 0)) := fun h =>
        hz' (tsupport_fderiv_apply_subset ℝ _ h)
      rw [fderiv_apply_eq_zero_of_notMem_tsupport hz'', fderiv_apply_eq_zero_of_notMem_tsupport hz',
        image_eq_zero_of_notMem_tsupport hz']
      ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hRint hPint.1, hPint.2,
    add_zero]

end CIV
