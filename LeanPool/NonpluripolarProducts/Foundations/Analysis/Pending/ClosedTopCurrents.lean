/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.TopBidimensionCurrents
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ZeroDerivativeMeasure
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.SmoothCurrentClosedness
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.SmoothDDCForm
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.SlotTestForms
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.CurrentRestriction

/-!
# Closed positive currents of top bidimension are multiples of `[X]`

Let `X` be a compact connected complex manifold of dimension `n = m + 1` with a Kähler form `ω`.
A closed positive current `S` of bidimension `(n, n)` is a constant multiple of the integration
current: `S = c [X]` with `c ≥ 0` (`eq_smul_integrationCurrent_of_isClosedCurrent`;
`demailly-cadg:III.2.13` for a point, step (S4) of the support theorem on the diagonal,
TN.4 step B4.4, `bou:diagonal-support`).

*Proof.*  By `TopBidimensionCurrents.apply_eq_integral_topRatio` it suffices to show that the trace
measure `σ_S` is `c` times the Kähler volume.

* **The flat identity** (`topDensity_slot_eq`).  In a chart, with `ω₀ = ddᶜ|z|²` in the `m` closed
  slots and `G = Im ⟨v, ·⟩` (real-linear), the density of `Π₁₁ (dF ∧ dG) ∧ ω₀ᵐ` is
  `(m! / πᵐ) dF(v)`: the coefficient matrix of `Π₁₁ (dF ∧ dG)` is `-2πi (∂ⱼF ∂barₖG - ∂ⱼG ∂barₖF)`
  (`SmoothCurrentClosedness.normalizedHermitianMatrix_pi11_eq`), that of `ω₀` is the identity,
  and the mixed coefficient `C(K, 1, …, 1)` is `m! tr K` (`mixedCoefficient_cons_one`).
* **The chart step** (`exists_local_const`).  Closedness tested with `f = F` (supported in a ball)
  and the cut-off `g = χ G` says that the measure `ν = (σ_S / ωⁿ)` read in the chart has
  vanishing distributional derivatives; hence it is a constant multiple of Lebesgue measure
  (`ZeroDerivativeMeasure.exists_integral_eq_const_mul`), i.e. `σ_S = c_x kahlerVolume` near
  every point `x`.
* **Gluing** (`eq_smul_kahlerVolume_of_isClosedCurrent`).  The constants `c_x` are locally
  constant (the Kähler volume charges every nonempty open set), hence constant on the connected
  `X`; a chart-smooth partition of unity gives `σ_S = c kahlerVolume`.
-/

@[expose] public section

noncomputable section

open Set Filter Topology MeasureTheory Metric
open scoped ContDiff

namespace SGPT.Foundations.Analysis.Pending.ClosedTopCurrents

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere FirstPass.PositiveClasses
  StronglyPositiveForms ProductTestForms PositiveProductCurrents ClosedProductCurrents
  CurrentTraceMeasure IntegrationCurrent TopDegreeDensity TopBidimensionCurrents
  SmoothCurrentClosedness SmoothDDCForm ChartPartition

/-! ### The flat identity -/

section Flat

variable {m : ℕ}

/-- **`C(K, 1, …, 1) = m! tr K`.** -/
theorem mixedCoefficient_cons_one (A : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) :
    mixedCoefficient (Fin.cons A (fun _ : Fin m => (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) :
        Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) =
      (m.factorial : ℂ) * A.trace := by
  classical
  set H : Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ :=
    Fin.cons A (fun _ : Fin m => (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) with hH
  have hrow : ∀ σ : Equiv.Perm (Fin (m + 1)),
      Matrix.det (fun j k => H (σ j) j k) = A (σ.symm 0) (σ.symm 0) := by
    intro σ
    set j₀ := σ.symm 0 with hj₀
    have hM : (Matrix.of fun j k => H (σ j) j k) =
        (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ).updateRow j₀
          (∑ k, A j₀ k • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) k) := by
      ext j k
      by_cases hj : j = j₀
      · subst hj
        have hσ : σ j₀ = 0 := σ.apply_symm_apply 0
        simp only [Matrix.of_apply, hσ, hH, Fin.cons_zero, Matrix.updateRow_self,
          Finset.sum_apply, Pi.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one,
          mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      · have hne : σ j ≠ 0 := fun h => hj (by rw [hj₀, ← h, Equiv.symm_apply_apply])
        obtain ⟨i, hi⟩ := Fin.exists_succ_eq.mpr hne
        simp only [Matrix.of_apply, Matrix.updateRow_ne hj, ← hi, hH, Fin.cons_succ]
    have hdet : Matrix.det (fun j k => H (σ j) j k) = Matrix.det (Matrix.of fun j k => H (σ j)
      j k) :=
      rfl
    rw [hdet, hM, Matrix.det_updateRow_sum, Matrix.det_one, smul_eq_mul, mul_one]
  rw [mixedCoefficient]
  simp_rw [hrow]
  have hinv : (∑ σ : Equiv.Perm (Fin (m + 1)), A (σ.symm 0) (σ.symm 0)) =
      ∑ σ : Equiv.Perm (Fin (m + 1)), A (σ 0) (σ 0) :=
    Equiv.sum_comp (Equiv.inv (Equiv.Perm (Fin (m + 1)))) (fun σ => A (σ 0) (σ 0))
  rw [hinv, ← Equiv.sum_comp Equiv.Perm.decomposeFin.symm, Fintype.sum_prod_type]
  simp only [Equiv.Perm.decomposeFin_symm_apply_zero, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul, Matrix.trace, Matrix.diag,
    Finset.mul_sum]

/-- The trace of the first-order matrix: `Re(-2πi tr (∂ⱼF ∂barₖG - ∂ⱼG ∂barₖF))
= π ∑ⱼ (dF(eⱼ) dG(ieⱼ) - dF(ieⱼ) dG(eⱼ))`. -/
theorem re_trace_pairMatrix {F G : ComplexModel (m + 1) → ℝ} {z : ComplexModel (m + 1)}
    (hF : DifferentiableAt ℝ F z) (hG : DifferentiableAt ℝ G z) :
    ((-2 * (Real.pi : ℂ) * Complex.I) * (pairMatrix F G z).trace).re =
      Real.pi * ∑ j, (fderiv ℝ F z (coordinateVector j) *
          fderiv ℝ G z (Complex.I • coordinateVector j) -
        fderiv ℝ F z (Complex.I • coordinateVector j) * fderiv ℝ G z (coordinateVector j)) := by
  simp only [Matrix.trace, Matrix.diag, pairMatrix, wirt_ofReal_apply hF, wirt_ofReal_apply hG,
    Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.div_re,
    Complex.div_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.neg_re, Complex.neg_im, Complex.re_ofNat,
    Complex.im_ofNat, Complex.normSq_ofNat]
  ring

/-- The real-linear functional `G_v = Im ⟨v, ·⟩`. -/
def imInner (v : ComplexModel (m + 1)) : ComplexModel (m + 1) →L[ℝ] ℝ :=
  Complex.imCLM.comp ((innerSL ℂ v).restrictScalars ℝ)

theorem imInner_apply (v y : ComplexModel (m + 1)) : imInner v y = (inner ℂ v y).im := rfl

/-- **`∑ⱼ (a(eⱼ) G_v(ieⱼ) - a(ieⱼ) G_v(eⱼ)) = a(v)`** for every real one-form `a`. -/
theorem sum_imInner (a : ComplexModel (m + 1) →L[ℝ] ℝ) (v : ComplexModel (m + 1)) :
    ∑ j, (a (coordinateVector j) * imInner v (Complex.I • coordinateVector j) -
      a (Complex.I • coordinateVector j) * imInner v (coordinateVector j)) = a v := by
  have hv : v = ∑ j, ((v j).re • coordinateVector j + (v j).im • (Complex.I • coordinateVector j))
    := by
    have h1 : v = ∑ j, v j • coordinateVector j := by
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin (m + 1)) ℂ).sum_repr v]
      simp only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply, coordinateVector]
    conv_lhs => rw [h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Complex.coe_smul, ← Complex.coe_smul, smul_smul, ← add_smul,
      Complex.re_add_im]
  have he : ∀ j, imInner v (coordinateVector j) = -(v j).im := fun j => by
    rw [imInner_apply, coordinateVector, EuclideanSpace.inner_single_right, one_mul,
      Complex.conj_im]
  have hie : ∀ j, imInner v (Complex.I • coordinateVector j) = (v j).re := fun j => by
    rw [imInner_apply, inner_smul_right, coordinateVector, EuclideanSpace.inner_single_right,
      one_mul, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.conj_re, zero_mul, one_mul,
      zero_add]
  conv_rhs => rw [hv]
  simp only [map_sum, map_add, map_smul, smul_eq_mul, he, hie]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **The flat identity**: the density of `Π₁₁ (dF ∧ dG) ∧ (ddᶜ|z|²)ᵐ` is
`(m! / πᵐ) ∑ⱼ (dF(eⱼ) dG(ieⱼ) - dF(ieⱼ) dG(eⱼ))`. -/
theorem topDensity_slot_eq {F G : ComplexModel (m + 1) → ℝ} {z : ComplexModel (m + 1)}
    (hF : DifferentiableAt ℝ F z) (hG : DifferentiableAt ℝ G z) {A : RealForm (m + 1) 2}
    (hA : ∀ u v, A ![u, v] =
      fderiv ℝ F z u * fderiv ℝ G z v - fderiv ℝ F z v * fderiv ℝ G z u) :
    topDensity (wedgeProd (m + 1) (Fin.cons (pi11 A)
        (fun _ : Fin m => smoothDDC (fun y : ComplexModel (m + 1) => ‖y‖ ^ 2) z))) =
      (m.factorial / Real.pi ^ m) * ∑ j, (fderiv ℝ F z (coordinateVector j) *
          fderiv ℝ G z (Complex.I • coordinateVector j) -
        fderiv ℝ F z (Complex.I • coordinateVector j) * fderiv ℝ G z (coordinateVector j)) := by
  have hq : ContDiffAt ℝ 2 (fun y : ComplexModel (m + 1) => ‖y‖ ^ 2) z :=
    contDiff_norm_sq ℝ |>.contDiffAt
  have hslots : ∀ i, IsOneOne ((Fin.cons (pi11 A)
      (fun _ : Fin m => smoothDDC (fun y : ComplexModel (m + 1) => ‖y‖ ^ 2) z) :
        Fin (m + 1) → RealForm (m + 1) 2) i) := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [Fin.cons_zero] using isOneOne_pi11 A
    · simp only [Fin.cons_succ]
      exact fun u v => smoothDDC_isOneOne hq u v
  rw [topDensity_wedgeProd, actualMixedTopDensity_eq_normalizedMixedTopDensity _ hslots,
    normalizedMixedTopDensity]
  have hfun : (fun i => normalizedHermitianMatrix ((Fin.cons (pi11 A)
      (fun _ : Fin m => smoothDDC (fun y : ComplexModel (m + 1) => ‖y‖ ^ 2) z) :
        Fin (m + 1) → RealForm (m + 1) 2) i)) =
      (Fin.cons ((-2 * (Real.pi : ℂ) * Complex.I) • pairMatrix F G z)
        (fun _ : Fin m => (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)) :
          Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero]
      exact normalizedHermitianMatrix_pi11_eq hF hG hA
    · simp only [Fin.cons_succ]
      rw [normalizedHermitianMatrix_smoothDDC hq, complexHessian_norm_sq]
  rw [hfun, mixedCoefficient_cons_one, Matrix.trace_smul, smul_eq_mul, Complex.mul_re,
    Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero, re_trace_pairMatrix hF hG,
    pow_succ]
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp

end Flat

/-! ### The density of a closed test form in a chart -/

section ChartDensity

variable {m : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X]

/-- **The density of `Π₁₁ d(f dg) ∧ ω₀ᵐ` in a chart** where `g = Im ⟨v, ·⟩` near the point and the
slots are `ddᶜ|z|²` at the point: `(m! / πᵐ) df(v)`. -/
theorem topDensity_closedTestForm_eq {f g : X → ℝ} (hf : ChartSmooth (n := m + 1) f)
    (hg : ChartSmooth (n := m + 1) g) (β : Fin m → ClosedRealOneOneForm (m + 1) X)
    (e : ComplexChart (m + 1) X) {z : ComplexModel (m + 1)} (hz : z ∈ e.val.target)
    (v : ComplexModel (m + 1))
    (hgv : (fun y => g (e.val.symm y)) =ᶠ[𝓝 z] fun y => imInner v y)
    (hβ : ∀ j, (β j).val.coeff e z = smoothDDC (fun y : ComplexModel (m + 1) => ‖y‖ ^ 2) z) :
    topDensity (((closedTestForm f g hf hg m β : testSpace (m + 1) X (m + 1)) :
        SmoothRealForm (m + 1) X (2 * (m + 1))).coeff e z) =
      (m.factorial / Real.pi ^ m) * fderiv ℝ (fun y => f (e.val.symm y)) z v := by
  have hnhds : e.val.target ∈ 𝓝 z := e.val.open_target.mem_nhds hz
  have hF : DifferentiableAt ℝ (fun y => f (e.val.symm y)) z :=
    ((hf e).contDiffAt hnhds).differentiableAt (by simp)
  have hG : DifferentiableAt ℝ (fun y => g (e.val.symm y)) z :=
    ((hg e).contDiffAt hnhds).differentiableAt (by simp)
  have hdG : fderiv ℝ (fun y => g (e.val.symm y)) z = imInner v := by
    rw [hgv.fderiv_eq]
    exact (imInner v).fderiv
  have hβ' : (fun j => (β j).val.coeff e z) =
      fun _ : Fin m => smoothDDC (fun y : ComplexModel (m + 1) => ‖y‖ ^ 2) z := funext hβ
  rw [closedTestForm_coeff hf hg m β e z, hβ',
    topDensity_slot_eq hF hG (exactPair_coeff_apply f g hf hg e hz), hdG, sum_imInner]

end ChartDensity

/-! ### The trace measure read in a chart -/

section Measure

open SmoothMixedMeasureDensity GlobalNonPluripolar SlotTestForms

variable {m : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X]

/-- The density of `ωⁿ` in a chart. -/
def volDensity (w : KahlerBackground (m + 1) X) (e : ComplexChart (m + 1) X)
    (z : ComplexModel (m + 1)) : ℝ :=
  topDensity ((formPow w.form.val (m + 1)).coeff e z)

theorem volDensity_pos (w : KahlerBackground (m + 1) X) (e : ComplexChart (m + 1) X)
    {z : ComplexModel (m + 1)} (hz : z ∈ e.val.target) : 0 < volDensity w e z :=
  topDensity_formPow_pos w.isKahler.1 hz

theorem contDiffOn_volDensity (w : KahlerBackground (m + 1) X) (e : ComplexChart (m + 1) X) :
    ContDiffOn ℝ ∞ (volDensity w e) e.val.target := by
  have := realForm_finiteDimensional (n := m + 1) (2 * (m + 1))
  exact (topDensityLM (n := m + 1)).toContinuousLinearMap.contDiff.comp_contDiffOn
    ((formPow w.form.val (m + 1)).smooth e)

theorem continuousOn_volDensity (w : KahlerBackground (m + 1) X) (e : ComplexChart (m + 1) X) :
    ContinuousOn (volDensity w e) e.val.target :=
  (contDiffOn_volDensity w e).continuousOn

variable [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- **The Kähler volume in a chart.** -/
theorem setIntegral_kahlerVolume_image (w : KahlerBackground (m + 1) X)
    (e : ComplexChart (m + 1) X) {K : Set (ComplexModel (m + 1))} (hK : MeasurableSet K)
    (hKe : K ⊆ e.val.target) {G : X → ℝ} (hG : Continuous G) :
    ∫ x in e.val.symm '' K, G x ∂(kahlerVolume w) =
      ∫ z in K, volDensity w e z * G (e.val.symm z) := by
  have hω : ∀ _ : Fin (m + 1), ThetaPlurisubharmonic w.form.val (fun _ => 0) := fun _ =>
    ((LocalPotentials.isThetaPshPotential_zero_iff w.form).mpr w.isSemipositive).1
  have hvol : kahlerVolume w =
      globalMixedMeasure (fun _ : Fin (m + 1) => w.form) (fun _ _ => 0) hω := rfl
  rw [hvol, setIntegral_image_eq hω e hK hKe hG]
  refine setIntegral_congr_fun hK fun z hz => ?_
  have hden : volDensity w e z = actualMixedTopDensity fun _ => w.form.val.coeff e z := by
    rw [volDensity, formPow_coeff, topDensity_formPower, actualMixedTopDensity_const]
  simp only [chartDensity]
  rw [← hden, ENNReal.toReal_ofReal (volDensity_pos w e (hKe hz)).le]

variable (w : KahlerBackground (m + 1) X) {S : ProductCurrent (m + 1) X (m + 1)}
  (hS : IsPositive S)

/-- The measure `σ_S / ωⁿ` on a compact piece `K` of a chart, read in the chart. -/
def chartMeasure (e : ComplexChart (m + 1) X) (K : Set (ComplexModel (m + 1))) :
    Measure (ComplexModel (m + 1)) :=
  (Measure.map e.val ((traceMeasure w S hS).restrict (e.val.symm '' K))).withDensity
    fun z => ENNReal.ofReal (K.indicator (fun z => (volDensity w e z)⁻¹) z)

omit [CompactSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem measurable_indicator_inv_volDensity (e : ComplexChart (m + 1) X)
    {K : Set (ComplexModel (m + 1))} (hK : MeasurableSet K) (hKe : K ⊆ e.val.target) :
    Measurable (fun z => K.indicator (fun z => (volDensity w e z)⁻¹) z) := by
  classical
  have h : (fun z => K.indicator (fun z => (volDensity w e z)⁻¹) z) =
      K.piecewise (fun z => (volDensity w e z)⁻¹) 0 := by
    rw [Set.piecewise_eq_indicator]
  rw [h]
  exact ContinuousOn.measurable_piecewise (((continuousOn_volDensity w e).mono hKe).inv₀
    fun z hz => (volDensity_pos w e (hKe hz)).ne') continuousOn_const hK

theorem isFiniteMeasure_chartMeasure (e : ComplexChart (m + 1) X)
    {K : Set (ComplexModel (m + 1))} (hK : IsCompact K) (hKe : K ⊆ e.val.target) :
    IsFiniteMeasure (chartMeasure w hS e K) := by
  have hcont : ContinuousOn (fun z => (volDensity w e z)⁻¹) K :=
    ((continuousOn_volDensity w e).mono hKe).inv₀ fun z hz => (volDensity_pos w e (hKe hz)).ne'
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont
  refine isFiniteMeasure_withDensity_ofReal (HasFiniteIntegral.of_bounded (C := max C 0)
    (Eventually.of_forall fun z => ?_))
  by_cases hz : z ∈ K
  · rw [Set.indicator_of_mem hz]
    exact (hC z hz).trans (le_max_left _ _)
  · rw [Set.indicator_of_notMem hz, norm_zero]
    exact le_max_right _ _

/-- **Integration against the chart measure.** -/
theorem integral_chartMeasure (e : ComplexChart (m + 1) X) {K : Set (ComplexModel (m + 1))}
    (hK : IsCompact K) (hKe : K ⊆ e.val.target) {Ψ : ComplexModel (m + 1) → ℝ}
    (hΨ : Continuous Ψ) :
    ∫ z, Ψ z ∂(chartMeasure w hS e K) =
      ∫ x in e.val.symm '' K, (volDensity w e (e.val x))⁻¹ * Ψ (e.val x) ∂(traceMeasure w S hS)
        := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hAm : MeasurableSet (e.val.symm '' K) := measurableSet_chartSymm_image e hKm hKe
  have hae : AEMeasurable e.val ((traceMeasure w S hS).restrict (e.val.symm '' K)) :=
    (e.val.continuousOn.mono (image_symm_subset_source hKe)).aemeasurable hAm
  have hdm := measurable_indicator_inv_volDensity w e hKm hKe
  rw [chartMeasure, integral_withDensity_eq_integral_toReal_smul₀ hdm.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    integral_map (f := fun z => (ENNReal.ofReal (K.indicator (fun z => (volDensity w e z)⁻¹)
      z)).toReal •
      Ψ z) hae ((hdm.ennreal_ofReal.ennreal_toReal.smul hΨ.measurable).aestronglyMeasurable)]
  refine setIntegral_congr_fun hAm fun x hx => ?_
  obtain ⟨z, hz, rfl⟩ := hx
  rw [e.val.right_inv (hKe hz), Set.indicator_of_mem hz,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (volDensity_pos w e (hKe hz)).le), smul_eq_mul]

end Measure

/-! ### The chart step -/

section Local

open SmoothMixedMeasureDensity SlotTestForms ZeroDerivativeMeasure CurrentRestriction
  SmoothCurrentTraceMeasure

variable {m : ℕ} {X : Type*} [TopologicalSpace X] [ChartedSpace (ComplexModel (m + 1)) X]
  [IsComplexManifold (m + 1) X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  (w : KahlerBackground (m + 1) X) {S : ProductCurrent (m + 1) X (m + 1)} (hS : IsPositive S)

/-- **Closedness forces vanishing distributional derivatives**: the chart measure `σ_S / ωⁿ` of a
closed positive current of top bidimension, on `BBar(z₀, 3r)`, has vanishing distributional
derivatives on `B(z₀, 3r)`. -/
theorem hasZeroDerivOn_chartMeasure (hSc : IsClosedCurrent S) (e : ComplexChart (m + 1) X)
    {z₀ : ComplexModel (m + 1)} {r : ℝ} (hr : 0 < r)
    (hball : closedBall z₀ (5 * r) ⊆ e.val.target) :
    HasZeroDerivOn (chartMeasure w hS e (closedBall z₀ (3 * r))) (ball z₀ (3 * r)) := by
  set K := closedBall z₀ (3 * r) with hKdef
  have hKc : IsCompact K := isCompact_closedBall z₀ _
  have hKe : K ⊆ e.val.target := (closedBall_subset_closedBall (by linarith)).trans hball
  have hAm : MeasurableSet (e.val.symm '' K) :=
    measurableSet_chartSymm_image e hKc.isClosed.measurableSet hKe
  let χ : ContDiffBump z₀ := ⟨4 * r, 5 * r, by positivity, by linarith⟩
  have hχt : tsupport χ ⊆ e.val.target := by rw [χ.tsupport_eq]; exact hball
  have hχc : IsCompact (tsupport χ) := χ.hasCompactSupport
  have hχ1 : ∀ z ∈ K, (fun y => (χ : ComplexModel (m + 1) → ℝ) y) =ᶠ[𝓝 z] fun _ => 1 := by
    intro z hz
    have hz' : ball z₀ (4 * r) ∈ 𝓝 z := isOpen_ball.mem_nhds (by
      rw [mem_closedBall] at hz
      rw [mem_ball]
      linarith)
    filter_upwards [hz'] with y hy
    exact χ.one_of_mem_closedBall (ball_subset_closedBall hy)
  intro ψ hψ hψc hψs v
  have hψK : tsupport ψ ⊆ K := hψs.trans ball_subset_closedBall
  have hF := chartSmooth_chartExtend e hψ hψc (hψK.trans hKe)
  have hβ : ContDiff ℝ ∞ (fun y => χ y * imInner v y) := χ.contDiff.mul (imInner v).contDiff
  have hβs : tsupport (fun y => χ y * imInner v y) ⊆ tsupport χ := tsupport_mul_subset_left
  have hG := chartSmooth_chartExtend e hβ (hχc.of_isClosed_subset (isClosed_tsupport _) hβs)
    (hβs.trans hχt)
  have hρ : ContDiff ℝ ∞ (fun y : ComplexModel (m + 1) => χ y * ‖y‖ ^ 2) :=
    χ.contDiff.mul (contDiff_norm_sq ℝ)
  have hρs : tsupport (fun y : ComplexModel (m + 1) => χ y * ‖y‖ ^ 2) ⊆ tsupport χ :=
    tsupport_mul_subset_left
  have hρ' := chartSmooth_chartExtend e hρ (hχc.of_isClosed_subset (isClosed_tsupport _) hρs)
    (hρs.trans hχt)
  set ω₀ := ddcClosedForm _ hρ' with hω₀
  have hclosed := (isClosedCurrent_succ_iff S).mp hSc _ _ hF hG (fun _ : Fin m => ω₀)
  rw [apply_eq_integral_topRatio w hS] at hclosed
  set cm : ℝ := m.factorial / Real.pi ^ m with hcm
  have hpt : ∀ y, topRatio w.form.val ((closedTestForm _ _ hF hG m fun _ => ω₀ :
      testSpace (m + 1) X (m + 1)) : SmoothRealForm (m + 1) X (2 * (m + 1))) y =
      (e.val.symm '' K).indicator
        (fun y => (volDensity w e (e.val y))⁻¹ * (cm * fderiv ℝ ψ (e.val y) v)) y := by
    intro y
    by_cases hy : y ∈ e.val.symm '' K
    · rw [Set.indicator_of_mem hy]
      obtain ⟨z, hz, rfl⟩ := hy
      have hzt := hKe hz
      rw [topRatio_eq_chartRatio w.isKahler.1 _ (e.val.map_target hzt), e.val.right_inv hzt,
        chartRatio]
      have hgv : (fun y => chartExtend e (fun y => χ y * imInner v y) (e.val.symm y)) =ᶠ[𝓝 z]
          fun y => imInner v y := by
        filter_upwards [chartExtend_eventuallyEq hzt, hχ1 z hz] with y h1 h2
        rw [h1, h2, one_mul]
      have hω : ∀ _ : Fin m, ω₀.val.coeff e z =
          smoothDDC (fun y : ComplexModel (m + 1) => ‖y‖ ^ 2) z := by
        intro _
        rw [hω₀, ddcClosedForm_coeff]
        apply smoothDDC_congr
        filter_upwards [chartExtend_eventuallyEq hzt, hχ1 z hz] with y h1 h2
        rw [h1, h2, one_mul]
      rw [topDensity_closedTestForm_eq hF hG _ e hzt v hgv hω,
        (chartExtend_eventuallyEq hzt).fderiv_eq]
      change cm * fderiv ℝ ψ z v / volDensity w e z = _
      rw [div_eq_inv_mul]
    · rw [Set.indicator_of_notMem hy]
      have hyF : y ∉ tsupport (chartExtend e ψ) := fun h =>
        hy (tsupport_chartExtend_subset hKc hKe hψK h)
      have hys := mem_complexChartAt_source (n := m + 1) y
      have hz0 := (complexChartAt (n := m + 1) y).val.map_source hys
      change chartRatio _ _ (complexChartAt (n := m + 1) y)
        ((complexChartAt (n := m + 1) y).val y) = 0
      rw [chartRatio, closedTestForm_coeff, exactPair_coeff_eq_zero hF hG hz0
        (chart_eventuallyEq_zero hyF hys), pi11_zero, wedgeProd_cons_zero, topDensity_zero,
        zero_div]
  have hcont : Continuous fun z => cm * fderiv ℝ ψ z v :=
    continuous_const.mul ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_indicator hAm,
    ← integral_chartMeasure w hS e hKc hKe hcont, integral_const_mul] at hclosed
  have hcm : cm ≠ 0 := by
    rw [hcm]
    exact div_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m))
      (pow_ne_zero _ Real.pi_ne_zero)
  exact (mul_eq_zero.mp hclosed).resolve_left hcm

/-- **The chart step**: near every point the trace measure of a closed positive current of top
bidimension is a constant multiple of the Kähler volume (tested with chart-smooth functions). -/
theorem exists_local_const (hSc : IsClosedCurrent S) (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∃ c : ℝ, ∀ h : X → ℝ, ChartSmooth (n := m + 1) h →
      tsupport h ⊆ U → ∫ y, h y ∂(traceMeasure w S hS) = c * ∫ y, h y ∂(kahlerVolume w) := by
  set e := complexChartAt (n := m + 1) x with he
  have hx : x ∈ e.val.source := mem_complexChartAt_source x
  set z₀ := e.val x with hz₀def
  have hz₀ : z₀ ∈ e.val.target := e.val.map_source hx
  obtain ⟨ε, hε, hεt⟩ := Metric.isOpen_iff.mp e.val.open_target z₀ hz₀
  set r := ε / 6 with hrdef
  have hr : 0 < r := by positivity
  have hball : closedBall z₀ (5 * r) ⊆ e.val.target :=
    (closedBall_subset_ball (by rw [hrdef]; linarith)).trans hεt
  set K := closedBall z₀ (3 * r) with hKdef
  have hKc : IsCompact K := isCompact_closedBall z₀ _
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hKe : K ⊆ e.val.target := (closedBall_subset_closedBall (by linarith)).trans hball
  have := isFiniteMeasure_chartMeasure w hS e hKc hKe
  obtain ⟨c, hc⟩ := exists_integral_eq_const_mul (volume : Measure (ComplexModel (m + 1)))
    (chartMeasure w hS e K) hr (hasZeroDerivOn_chartMeasure w hS hSc e hr hball)
  have hBK : ball z₀ r ⊆ K := ball_subset_closedBall.trans (closedBall_subset_closedBall (by
    linarith))
  have hBt : ball z₀ r ⊆ e.val.target := hBK.trans hKe
  refine ⟨e.val.symm '' ball z₀ r, e.val.symm.isOpen_image_of_subset_source isOpen_ball
    (by simpa using hBt), ⟨z₀, mem_ball_self hr, e.val.left_inv hx⟩, c, fun h hh hhU => ?_⟩
  let χ' : ContDiffBump z₀ := ⟨r, 2 * r, hr, by linarith⟩
  have hχ't : tsupport χ' ⊆ e.val.target := by
    rw [χ'.tsupport_eq]
    exact (closedBall_subset_closedBall (by linarith)).trans hball
  set ψh : ComplexModel (m + 1) → ℝ := fun z => χ' z * (h (e.val.symm z) * volDensity w e z)
    with hψhdef
  have hψh : ContDiff ℝ ∞ ψh := contDiff_mul_of_tsupport_subset e.val.open_target χ'.contDiff
    hχ't ((hh e).mul (contDiffOn_volDensity w e))
  have hhK : IsCompact (tsupport h) :=
    isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (subset_univ _)
  have hhs : tsupport h ⊆ e.val.source := hhU.trans (image_symm_subset_source hBt)
  have hL : IsCompact (e.val '' tsupport h) :=
    hhK.image_of_continuousOn (e.val.continuousOn.mono hhs)
  have hLB : e.val '' tsupport h ⊆ ball z₀ r := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hhU hy
    rw [e.val.right_inv (hBt hz)]
    exact hz
  have hsupp : Function.support ψh ⊆ e.val '' tsupport h := by
    intro z hz
    have h1 : χ' z ≠ 0 := left_ne_zero_of_mul hz
    have h2 : h (e.val.symm z) ≠ 0 := left_ne_zero_of_mul (right_ne_zero_of_mul hz)
    have hzt : z ∈ e.val.target := hχ't (subset_tsupport _ h1)
    exact ⟨e.val.symm z, subset_tsupport _ h2, e.val.right_inv hzt⟩
  have hts : tsupport ψh ⊆ e.val '' tsupport h := closure_minimal hsupp hL.isClosed
  have hψhc : HasCompactSupport ψh := hL.of_isClosed_subset (isClosed_tsupport _) hts
  have hval : ∀ z ∈ e.val.target, ψh z = h (e.val.symm z) * volDensity w e z := by
    intro z hz
    by_cases h0 : h (e.val.symm z) = 0
    · simp [hψhdef, h0]
    · have hzB : z ∈ ball z₀ r := hLB ⟨e.val.symm z, subset_tsupport _ h0, e.val.right_inv hz⟩
      rw [hψhdef]
      simp only [χ'.one_of_mem_closedBall (ball_subset_closedBall hzB), one_mul]
  have hhzero : ∀ y ∉ e.val.symm '' K, h y = 0 := by
    intro y hy
    by_contra h0
    exact hy (image_mono hBK (hhU (subset_tsupport _ h0)))
  have hAm : MeasurableSet (e.val.symm '' K) := measurableSet_chartSymm_image e hKm hKe
  have hσ : ∫ y, h y ∂(traceMeasure w S hS) = ∫ z, ψh z ∂(chartMeasure w hS e K) := by
    rw [integral_chartMeasure w hS e hKc hKe hψh.continuous,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero hhzero]
    refine setIntegral_congr_fun hAm fun y hy => ?_
    obtain ⟨z, hz, rfl⟩ := hy
    rw [e.val.right_inv (hKe hz), hval z (hKe hz)]
    field_simp [(volDensity_pos w e (hKe hz)).ne']
  have hψzero : ∀ z ∉ K, ψh z = 0 := by
    intro z hz
    by_contra h0
    exact hz (hBK (hLB (hsupp h0)))
  have hV : ∫ y, h y ∂(kahlerVolume w) = ∫ z, ψh z := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hhzero,
      setIntegral_kahlerVolume_image w e hKm hKe (chartSmooth_continuous hh),
      ← setIntegral_eq_integral_of_forall_compl_eq_zero hψzero]
    refine setIntegral_congr_fun hKm fun z hz => ?_
    rw [hval z (hKe hz), mul_comm]
  rw [hσ, hc ψh hψh hψhc (hts.trans hLB), hV]

/-- **The Kähler volume charges every point's neighbourhood**: `∫ h ωⁿ > 0` for a nonnegative
chart-smooth `h` positive somewhere. -/
theorem integral_kahlerVolume_pos {h : X → ℝ} (hh : ChartSmooth (n := m + 1) h)
    (h0 : ∀ y, 0 ≤ h y) {x : X} (hx : 0 < h x) : 0 < ∫ y, h y ∂(kahlerVolume w) := by
  set e := complexChartAt (n := m + 1) x with he
  have hxs : x ∈ e.val.source := mem_complexChartAt_source x
  set z₀ := e.val x with hz₀def
  have hz₀ : z₀ ∈ e.val.target := e.val.map_source hxs
  obtain ⟨ε, hε, hεt⟩ := Metric.isOpen_iff.mp e.val.open_target z₀ hz₀
  let χ' : ContDiffBump z₀ := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  set K := closedBall z₀ (ε / 2) with hKdef
  have hKe : K ⊆ e.val.target := (closedBall_subset_ball (by linarith)).trans hεt
  have hKm : MeasurableSet K := isClosed_closedBall.measurableSet
  have hχ't : tsupport χ' ⊆ e.val.target := by rw [χ'.tsupport_eq]; exact hKe
  set φ : ComplexModel (m + 1) → ℝ := fun z => χ' z * (volDensity w e z * h (e.val.symm z))
    with hφdef
  have hφ : ContDiff ℝ ∞ φ := contDiff_mul_of_tsupport_subset e.val.open_target χ'.contDiff hχ't
    ((contDiffOn_volDensity w e).mul (hh e))
  have hφc : HasCompactSupport φ := χ'.hasCompactSupport.mul_right
  have hφ0 : 0 ≤ φ := fun z => by
    by_cases hz : z ∈ e.val.target
    · exact mul_nonneg χ'.nonneg (mul_nonneg (volDensity_pos w e hz).le (h0 _))
    · have : χ' z = 0 := image_eq_zero_of_notMem_tsupport fun h' => hz (hχ't h')
      simp [hφdef, this]
  have hφz : φ z₀ ≠ 0 := by
    have h1 : χ' z₀ = 1 := χ'.one_of_mem_closedBall (mem_closedBall_self (by positivity))
    change χ' z₀ * (volDensity w e z₀ * h (e.val.symm z₀)) ≠ 0
    rw [h1, one_mul, hz₀def, e.val.left_inv hxs]
    exact (mul_pos (volDensity_pos w e (e.val.map_source hxs)) hx).ne'
  have hpos : 0 < ∫ z, φ z :=
    hφ.continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero hφc hφ0 hφz
  have hφK : ∀ z ∉ K, φ z = 0 := by
    intro z hz
    have : χ' z = 0 := by
      refine Function.notMem_support.mp fun h' => hz ?_
      rw [χ'.support_eq] at h'
      exact ball_subset_closedBall h'
    simp [hφdef, this]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hφK] at hpos
  have hcont : ContinuousOn (fun z => volDensity w e z * h (e.val.symm z)) K :=
    ((continuousOn_volDensity w e).mono hKe).mul
      ((chartSmooth_continuous hh).comp_continuousOn (e.val.continuousOn_symm.mono hKe))
  have hle : ∫ z in K, φ z ≤ ∫ z in K, volDensity w e z * h (e.val.symm z) := by
    refine setIntegral_mono_on (hφ.continuous.integrable_of_hasCompactSupport hφc).integrableOn
      (hcont.integrableOn_compact (isCompact_closedBall _ _)) hKm fun z hz => ?_
    have hW : 0 ≤ volDensity w e z * h (e.val.symm z) :=
      mul_nonneg (volDensity_pos w e (hKe hz)).le (h0 _)
    calc φ z = χ' z * (volDensity w e z * h (e.val.symm z)) := rfl
      _ ≤ 1 * (volDensity w e z * h (e.val.symm z)) := mul_le_mul_of_nonneg_right χ'.le_one hW
      _ = _ := one_mul _
  rw [← setIntegral_kahlerVolume_image w e hKm hKe (chartSmooth_continuous hh)] at hle
  have hsub : ∫ y in e.val.symm '' K, h y ∂(kahlerVolume w) ≤ ∫ y, h y ∂(kahlerVolume w) :=
    setIntegral_le_integral (integrable_of_chartSmooth _ hh) (Eventually.of_forall h0)
  linarith

/-- **Gluing**: on a connected `X` the trace measure of a closed positive current of top
bidimension is `c ωⁿ` with `c ≥ 0`. -/
theorem eq_smul_kahlerVolume_of_isClosedCurrent [ConnectedSpace X] (hSc : IsClosedCurrent S) :
    ∃ c : ℝ, 0 ≤ c ∧ traceMeasure w S hS = ENNReal.ofReal c • kahlerVolume w := by
  classical
  choose U hU hxU c hc using exists_local_const w hS hSc
  have hloc : IsLocallyConstant c := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    refine ⟨U x, hU x, hxU x, fun x' hx' => ?_⟩
    obtain ⟨g, hg, hg0, -, hgS, -, hg1⟩ := exists_chartSmooth_bump (n := m + 1) x'
      ⟨U x ∩ U x', (hU x).inter (hU x')⟩ ⟨hx', hxU x'⟩
    have hgpos : 0 < g x' := by
      rw [hg1.self_of_nhds]
      exact one_pos
    have hpos := integral_kahlerVolume_pos w hg hg0 (x := x') hgpos
    have e1 := hc x g hg (hgS.trans inter_subset_left)
    have e2 := hc x' g hg (hgS.trans inter_subset_right)
    exact mul_right_cancel₀ hpos.ne' (e2.symm.trans e1)
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  have hconst : ∀ x, c x = c x₀ := fun x => hloc.apply_eq_of_preconnectedSpace x x₀
  have hint : ∀ g : X → ℝ, ChartSmooth (n := m + 1) g →
      ∫ y, g y ∂(traceMeasure w S hS) = c x₀ * ∫ y, g y ∂(kahlerVolume w) := by
    intro g hg
    obtain ⟨N, χ, idx, hχs, -, hχS, -, hsum⟩ := exists_chartSmooth_partitionOfUnity (n := m + 1)
      (fun x => (⟨U x, hU x⟩ : TopologicalSpace.Opens X)) fun x => ⟨x, hxU x⟩
    have hsplit : ∀ μ : Measure X, IsFiniteMeasure μ →
        ∫ y, g y ∂μ = ∑ a, ∫ y, χ a y * g y ∂μ := by
      intro μ _
      rw [← integral_finsetSum _ fun a _ => integrable_of_chartSmooth μ (chartSmooth_mul (hχs a)
        hg)]
      congr 1
      funext y
      rw [← Finset.sum_mul, hsum, one_mul]
    rw [hsplit _ inferInstance, hsplit _ inferInstance, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hc (idx a) _ (chartSmooth_mul (hχs a) hg) (tsupport_mul_subset_left.trans (hχS a)),
      hconst]
  have hV1 : 0 < ∫ _y, (1 : ℝ) ∂(kahlerVolume w) :=
    integral_kahlerVolume_pos w (chartSmooth_const 1) (fun _ => zero_le_one) (x := x₀) one_pos
  have hc0 : 0 ≤ c x₀ := by
    have h1 : 0 ≤ ∫ _y, (1 : ℝ) ∂(traceMeasure w S hS) := integral_nonneg fun _ => zero_le_one
    rw [hint _ (chartSmooth_const 1)] at h1
    exact nonneg_of_mul_nonneg_left h1 hV1
  have : IsFiniteMeasure (ENNReal.ofReal (c x₀) • kahlerVolume w) :=
    ⟨by
      rw [smul_apply, smul_eq_mul]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  refine ⟨c x₀, hc0, measure_eq_of_integral_chartSmooth_eq (N := m + 1) fun g hg => ?_⟩
  rw [hint g hg, integral_smul_measure, ENNReal.toReal_ofReal hc0, smul_eq_mul]

include hS in
/-- **A closed positive current of top bidimension on a compact connected complex manifold is a
nonnegative multiple of the integration current** (`demailly-cadg:III.2.13` for a point; step (S4)
of `bou:diagonal-support`). -/
theorem eq_smul_integrationCurrent_of_isClosedCurrent [ConnectedSpace X]
    (hSc : IsClosedCurrent S) : ∃ c : ℝ, 0 ≤ c ∧ S = c • integrationCurrent w := by
  obtain ⟨c, hc0, hσ⟩ := eq_smul_kahlerVolume_of_isClosedCurrent w hS hSc
  exact ⟨c, hc0, eq_smul_integrationCurrent w hS hc0 hσ⟩

end Local

end SGPT.Foundations.Analysis.Pending.ClosedTopCurrents
