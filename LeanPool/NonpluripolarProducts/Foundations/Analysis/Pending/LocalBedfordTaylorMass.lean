/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorProducts

/-!
# The Chern--Levine--Nirenberg estimate for recursive Bedford--Taylor products

For a positive current `R` on an open `U ⊆ ℂⁿ` write `M_A(R) = σ_R(A)` for its trace measure
(`LocalProductCurrents.IsPositive.traceMeasure`, the Riesz measure of `R(ω₀^r)`,
    `ω₀ = π dd^c|z|²`).
For compact `L ⊆ K° ⊆ K ⊆ U`:

* `abs_density_le_of_orderUnit` — the density `f_γ` of a coefficient is bounded by ANY order-unit
  constant of `γ` (`C ω₀^q ± γ` strongly positive), almost everywhere for `σ_R`; the bound does not
  depend on `R`.
* `exists_mass_ddcMul_le` — one factor: `M_L(dd^c(u R)) ≤ C sup_K |u| M_K(R)` for `R` positive
  closed, `u` locally bounded PSH, `C` depending only on `K, L, n` and the bidimension.
* `exists_mass_btProduct_le` — **Chern--Levine--Nirenberg** (`demailly-cadg:III.3.3`,
  `bt:compact-mass`): `M_L(B(u₁, …, u_q; T)) ≤ C M_K(T) ∏ sup_K |u_j|`.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff Manifold CompactlySupported

namespace SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorMass

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts

variable {n : ℕ}

local notation "E" => ComplexModel n

variable {U : Opens (ComplexModel n)}

theorem integrable_testFunction_on (μ : Measure U) [IsLocallyFiniteMeasure μ] (φ : 𝓓(U, ℝ)) :
    Integrable (fun x : U => φ x) μ := by
  let _ : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  let g : C_c(U, ℝ) := testFunctionToCompactlySupportedLM U φ
  exact (g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport).congr
    (Eventually.of_forall fun x => by simp [g])

/-- **The densities are bounded by every order-unit constant**, uniformly in the current. -/
theorem abs_density_le_of_orderUnit {k : ℕ} {T : LocalProductCurrent n U k} (hT : IsPositive T)
    (γ : formSpan n k) {C : ℝ}
    (h₁ : C • formPower (standardHermitianTwoForm n) k - (γ : RealForm n (2 * k)) ∈ spCone k)
    (h₂ : C • formPower (standardHermitianTwoForm n) k + (γ : RealForm n (2 * k)) ∈ spCone k) :
    ∀ᵐ x ∂hT.traceMeasure, |hT.density γ x| ≤ C := by
  let _ : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  have hloc := hT.isLocallyFiniteMeasure_traceMeasureOn
  obtain ⟨Cf, -, hCf⟩ := hT.exists_abs_density_le γ
  set σU := hT.traceMeasureOn
  have hfm : Measurable (fun x : U => hT.density γ x) :=
    (hT.measurable_density γ).comp measurable_subtype_coe
  have key : ∀ (s : ℝ),
      C • formPower (standardHermitianTwoForm n) k + s • (γ : RealForm n (2 * k)) ∈ spCone k →
      ∀ᵐ x : U ∂σU, 0 ≤ C + s * hT.density γ (x : E) := by
    intro s hmem
    let γs : formSpan n k := C • kahlerPower n k + s • γ
    have hγs : (γs : RealForm n (2 * k)) ∈ spCone k := by
      simpa [γs, kahlerPower] using hmem
    have hpos := hT.positiveDistribution hγs
    have hmeas : Measurable (fun x : U => C + s * hT.density γ x) :=
      measurable_const.add (measurable_const.mul hfm)
    have hint : LocallyIntegrable (fun x : U => C + s * hT.density γ x) σU := by
      intro x
      obtain ⟨V, hVc, hV⟩ := exists_compact_mem_nhds x
      refine ⟨V, hV, Measure.integrableOn_of_bounded (M := |C| + |s| * Cf)
        (hVc.measure_lt_top).ne hmeas.aestronglyMeasurable (Eventually.of_forall fun y => ?_)⟩
      rw [Real.norm_eq_abs]
      refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hCf _) (abs_nonneg _)
    refine Pending.ae_nonneg_of_positiveDistribution_integral hpos σU hmeas hint fun φ => ?_
    have hφ := integrable_testFunction_on σU φ
    have hφf : Integrable (fun x : U => φ x * hT.density γ x) σU := by
      have := hφ.bdd_mul (c := Cf) hfm.aestronglyMeasurable
        (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hCf x)
      simpa [mul_comm] using this
    have e : T γs = C • T (kahlerPower n k) + s • T γ := by
      simp only [γs, map_add, map_smul]
    calc T γs φ = C * T (kahlerPower n k) φ + s * T γ φ := by
          rw [e, _root_.add_apply, _root_.smul_apply, _root_.smul_apply, smul_eq_mul,
            smul_eq_mul]
      _ = C * ∫ x : U, φ x ∂σU + s * ∫ x : U, φ x * hT.density γ x ∂σU := by
          rw [← hT.integral_traceMeasureOn φ, hT.apply_eq_integral_density γ φ,
            hT.integral_traceMeasure_eq]
      _ = ∫ x : U, (C * φ x + s * (φ x * hT.density γ x)) ∂σU := by
          rw [integral_add (hφ.const_mul C) (hφf.const_mul s), integral_const_mul,
            integral_const_mul]
      _ = ∫ x : U, φ x * (C + s * hT.density γ x) ∂σU := by
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          simp only
          ring
  have hp := key 1 (by simpa using h₂)
  have hm := key (-1) (by convert h₁ using 1; module)
  rw [IsPositive.traceMeasure, (IsPositive.measurableEmbedding_val (U := U)).ae_map_iff]
  filter_upwards [hp, hm] with x hx1 hx2
  rw [abs_le]
  constructor <;> linarith

/-- A smooth cutoff with values in `[0,1]`, equal to one on a compact set and supported in an open
neighbourhood of it. -/
theorem exists_cutoff_unit {K W : Set E} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ (∀ x ∈ K, χ x = 1) ∧ tsupport χ ⊆ W ∧
      ∀ x, 0 ≤ χ x ∧ χ x ≤ 1 := by
  obtain ⟨χ, hχ, hone, hsupp, h01⟩ := exists_cutoff_with_bounds hK hW hKW
  exact ⟨χ, hχ, fun x hx ↦ (hone x hx).self_of_nhds, hsupp, h01⟩

/-- **One factor of the Chern--Levine--Nirenberg estimate**: for compact `L ⊆ K° ⊆ K ⊆ U` there is
`C ≥ 0` with `M_L(dd^c(u R)) ≤ C M M_K(R)` for every positive closed `R` of bidimension
`(m+1, m+1)` and every locally bounded PSH `u` with `|u| ≤ M` on `K`. -/
theorem exists_mass_ddcMul_le {K L : Set E} (hK : IsCompact K) (hKU : K ⊆ U) (hL : IsCompact L)
    (hLK : L ⊆ interior K) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : LocalProductCurrent n U (m + 1)) (hR : IsPositive R)
      (hRc : IsClosedCurrent R) (u : E → ℝ) (hu : IsLocallyBoundedPshOn U u) (M : ℝ),
      (∀ x ∈ K, |u x| ≤ M) →
      ((isPositive_ddcMul hR hRc hu).1.traceMeasure L).toReal ≤
        C * M * (hR.traceMeasure K).toReal := by
  classical
  obtain ⟨χ, hχ, hχ1, hχW, hχ01⟩ := exists_cutoff_unit hL isOpen_interior hLK
  have hχc : HasCompactSupport χ :=
    hK.of_isClosed_subset (isClosed_tsupport χ) (hχW.trans interior_subset)
  let χt : 𝓓(U, ℝ) := ⟨χ, hχ, hχc, (hχW.trans interior_subset).trans hKU⟩
  let ψ : Fin (n * 2) → Fin (n * 2) → 𝓓(U, ℝ) := fun a b =>
    dTest (realBasis n b) (dTest (realBasis n a) χt)
  have hψK : ∀ a b, tsupport (ψ a b) ⊆ K := fun a b =>
    ((tsupport_dTest_subset _ _).trans (tsupport_dTest_subset _ _)).trans
      (hχW.trans interior_subset)
  have hψb : ∀ a b, ∃ Cψ : ℝ, ∀ x, |ψ a b x| ≤ Cψ := fun a b => by
    obtain ⟨C, hC⟩ := (ψ a b).continuous.bounded_above_of_compact_support (ψ a b).hasCompactSupport
    exact ⟨C, fun x => by simpa [Real.norm_eq_abs] using hC x⟩
  choose Cψ hCψ using hψb
  let γ : Fin (n * 2) → Fin (n * 2) → formSpan n (m + 1) := fun a b =>
    wedgeLM m (isOneOne_coeffForm a b) (kahlerPower n m)
  have hord : ∀ a b, ∃ C : ℝ, 0 ≤ C ∧
      C • formPower (standardHermitianTwoForm n) (m + 1) - (γ a b : RealForm n (2 * (m + 1))) ∈
        spCone (m + 1) ∧
      C • formPower (standardHermitianTwoForm n) (m + 1) + (γ a b : RealForm n (2 * (m + 1))) ∈
        spCone (m + 1) := fun a b => exists_orderUnit (γ a b).2
  choose Cγ hCγ0 hCγ1 hCγ2 using hord
  refine ⟨(1 / (4 * Real.pi)) * ∑ a, ∑ b, Cψ a b * Cγ a b, ?_, ?_⟩
  · refine mul_nonneg (by positivity) (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ =>
      mul_nonneg ((abs_nonneg _).trans (hCψ a b 0)) (hCγ0 a b))
  intro R hR hRc u hu M hM
  have hS := (isPositive_ddcMul hR hRc hu).1
  have hum := measurable_indicator_of_isLocallyBoundedPshOn hu
  have hub := isLocallyBoundedOn_indicator hu
  -- `M_L(S) ≤ ∫ χ dσ_S`
  have hLfin : hS.traceMeasure L < ⊤ :=
    hS.traceMeasure_lt_top hL ((hLK.trans interior_subset).trans hKU)
  have hχint : Integrable χ hS.traceMeasure := by
    have := hS.integrable_mul_of_bounded hχ.continuous hχc ((hχW.trans interior_subset).trans hKU)
      (aestronglyMeasurable_const (b := (1 : ℝ))) ⟨1, fun _ _ => by simp⟩
    simpa using this
  have h1 : (hS.traceMeasure L).toReal ≤ ∫ x, χ x ∂hS.traceMeasure := by
    rw [← Measure.real, ← integral_indicator_one hL.measurableSet]
    refine integral_mono ((integrable_indicator_iff hL.measurableSet).mpr
      (integrableOn_const hLfin.ne)) hχint fun x => ?_
    by_cases hx : x ∈ L
    · simp [hx, hχ1 x hx]
    · simp [hx, (hχ01 x).1]
  -- `∫ χ dσ_S` through the coefficients of `R`
  have h2 : ∫ x, χ x ∂hS.traceMeasure = ∑ a, ∑ b, (-(1 / (4 * Real.pi))) *
      ∫ x, ψ a b x * ((U : Set E).indicator u x * hR.density (γ a b) x) ∂hR.traceMeasure := by
    rw [show (∫ x, χ x ∂hS.traceMeasure) = ∫ x, χt x ∂hS.traceMeasure from rfl,
      hS.integral_traceMeasure χt, ddcMul, ddc_apply_apply]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [mulBorel_apply hR hum hub]
  -- each integral is bounded by `Cψ M Cγ M_K(R)`
  have h3 : ∀ a b, |∫ x, ψ a b x * ((U : Set E).indicator u x * hR.density (γ a b) x)
      ∂hR.traceMeasure| ≤ Cψ a b * (M * Cγ a b) * (hR.traceMeasure K).toReal := by
    intro a b
    have hKfin : hR.traceMeasure K < ⊤ := hR.traceMeasure_lt_top hK hKU
    have hbd := abs_density_le_of_orderUnit hR (γ a b) (hCγ1 a b) (hCγ2 a b)
    have hI : ∫ x, K.indicator (fun _ => Cψ a b * (M * Cγ a b)) x ∂hR.traceMeasure =
        Cψ a b * (M * Cγ a b) * (hR.traceMeasure K).toReal := by
      rw [integral_indicator_const _ hK.measurableSet, smul_eq_mul, Measure.real, mul_comm]
    rw [← Real.norm_eq_abs, ← hI]
    refine norm_integral_le_of_norm_le ((integrable_indicator_iff hK.measurableSet).mpr
      (integrableOn_const hKfin.ne)) ?_
    filter_upwards [hbd] with x hx
    by_cases hxK : x ∈ K
    · rw [Set.indicator_of_mem hxK, Set.indicator_of_mem (hKU hxK), norm_mul, norm_mul,
        Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs]
      have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x hxK)
      exact mul_le_mul (hCψ a b x) (mul_le_mul (hM x hxK) hx (abs_nonneg _) hM0)
        (mul_nonneg (abs_nonneg _) (abs_nonneg _)) ((abs_nonneg _).trans (hCψ a b x))
    · have hψ0 : ψ a b x = 0 := image_eq_zero_of_notMem_tsupport fun h => hxK (hψK a b h)
      simp [hψ0, Set.indicator_of_notMem hxK]
  calc (hS.traceMeasure L).toReal ≤ ∫ x, χ x ∂hS.traceMeasure := h1
    _ ≤ |∫ x, χ x ∂hS.traceMeasure| := le_abs_self _
    _ ≤ ∑ a, ∑ b, (1 / (4 * Real.pi)) * (Cψ a b * (M * Cγ a b) *
          (hR.traceMeasure K).toReal) := by
        rw [h2]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ =>
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_))
        rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / (4 * Real.pi))]
        exact mul_le_mul_of_nonneg_left (h3 a b) (by positivity)
    _ = (1 / (4 * Real.pi)) * (∑ a, ∑ b, Cψ a b * Cγ a b) * M *
          (hR.traceMeasure K).toReal := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        ring

/-- **The Chern--Levine--Nirenberg estimate** (`demailly-cadg:III.3.3`): for compact
`L ⊆ K° ⊆ K ⊆ U` there is `C ≥ 0`, depending only on `K, L, n, q, r`, with
`M_L(B(u₁, …, u_q; T)) ≤ C (∏ M_j) M_K(T)` whenever `T` is positive closed of bidimension
`(r+q, r+q)`, the `u_j` are locally bounded PSH and `0 ≤ |u_j| ≤ M_j` on `K`. -/
theorem exists_mass_btProduct_le : ∀ (q r : ℕ) {K L : Set E}, IsCompact K → K ⊆ U →
    IsCompact L → L ⊆ interior K →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : Fin q → E → ℝ) (T : LocalProductCurrent n U (r + q))
      (hT : IsPositive T) (hTc : IsClosedAny (r + q) T) (hu : ∀ i, IsLocallyBoundedPshOn U (u i))
      (M : Fin q → ℝ), (∀ j, 0 ≤ M j) → (∀ j, ∀ x ∈ K, |u j x| ≤ M j) →
      ((isPositive_btProduct q r u T hT hTc hu).1.traceMeasure L).toReal ≤
        C * (∏ j, M j) * (hT.traceMeasure K).toReal
  | 0, r, K, L, hK, hKU, hL, hLK => by
    refine ⟨1, zero_le_one, fun u T hT hTc hu M _ _ => ?_⟩
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one, one_mul]
    exact ENNReal.toReal_mono (hT.traceMeasure_lt_top hK hKU).ne
      (measure_mono (hLK.trans interior_subset))
  | q + 1, r, K, L, hK, hKU, hL, hLK => by
    obtain ⟨K', hK', hLK', hK'K⟩ := exists_compact_between hL isOpen_interior hLK
    obtain ⟨C₁, hC₁, h₁⟩ := exists_mass_btProduct_le q r hK'
      (hK'K.trans (interior_subset.trans hKU)) hL hLK'
    obtain ⟨C₂, hC₂, h₂⟩ := exists_mass_ddcMul_le hK hKU hK' hK'K (r + q)
    refine ⟨C₁ * C₂, mul_nonneg hC₁ hC₂, fun u T hT hTc hu M hM0 hM => ?_⟩
    have hS := isPositive_ddcMul (m := r + q) hT hTc (hu (Fin.last q))
    have hB := h₁ (Fin.init u) (ddcMul T (u (Fin.last q))) hS.1 hS.2 (fun i => hu _)
      (Fin.init M) (fun j => hM0 _) (fun j x hx => hM _ x (hK'K.trans interior_subset hx))
    have hSm := h₂ T hT hTc (u (Fin.last q)) (hu _) (M (Fin.last q)) (hM _)
    have hP0 : 0 ≤ C₁ * ∏ j, Fin.init M j :=
      mul_nonneg hC₁ (Finset.prod_nonneg fun j _ => hM0 _)
    calc _ ≤ C₁ * (∏ j, Fin.init M j) * (hS.1.traceMeasure K').toReal := hB
      _ ≤ C₁ * (∏ j, Fin.init M j) * (C₂ * M (Fin.last q) * (hT.traceMeasure K).toReal) :=
          mul_le_mul_of_nonneg_left hSm hP0
      _ = C₁ * C₂ * (∏ j, M j) * (hT.traceMeasure K).toReal := by
          rw [Fin.prod_univ_castSucc]
          simp only [Fin.init]
          ring

end SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorMass
