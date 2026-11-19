/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.Convex.Legendre.AffineMaximum
public import LeanPool.KLS.FunctionalInequalities.Probability.Support.Convex
public import LeanPool.KLS.FunctionalInequalities.Probability.MomentMeasure.ConjugateMass
public import LeanPool.KLS.FunctionalInequalities.Probability.MomentMeasure.Affine
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Coercivity of the CEK functional

Haar scaling of exponential mass, a polynomial bound on conjugate mass with the constant chosen
before the potential,
and the resulting functional and integral bounds for centered probability measures with
full-dimensional support.
This route does not establish the particular constant of CEK Lemma 15.

Supporting infrastructure for Cordero-Erausquin–Klartag, Proposition 12.
-/

@[expose] public section

noncomputable section

namespace FunctionalInequalities.Probability.MomentMeasure

open FunctionalInequalities.Analysis

section
-- Lower integrals of nonnegative potentials.

open MeasureTheory Filter Set
open scoped ENNReal Topology
section Integral
variable {E : Type*} [MeasurableSpace E] {μ : Measure E}
/-- Source admissibility and nonnegativity identify the actual extended integral,
including its a.e. finite guard; infinity is never totalized before this step. -/
theorem lintegral_nonneg_potential (φ : E → EReal) (hφ : PotentialIntegrable φ μ)
    (hnn : ∀ x, 0 ≤ φ x) :
    AEMeasurable (fun x => (φ x).toENNReal) μ ∧
      (∫⁻ x, (φ x).toENNReal ∂μ) = ENNReal.ofReal (∫ x, (φ x).toReal ∂μ) ∧
      0 ≤ ∫ x, (φ x).toReal ∂μ := by
  have heq : (fun x => (φ x).toENNReal) =ᵐ[μ] (fun x => ENNReal.ofReal (φ x).toReal) := by
    filter_upwards [hφ.2.1] with x hx
    exact EReal.toENNReal_of_ne_top hx
  have hm := hφ.2.2.aemeasurable.ennreal_ofReal
  refine ⟨hm.congr heq.symm, ?_, integral_nonneg (fun x => EReal.toReal_nonneg (hnn x))⟩
  rw [lintegral_congr_ae heq]
  exact (ofReal_integral_eq_lintegral_ofReal hφ.2.2
    (Eventually.of_forall fun x => EReal.toReal_nonneg (hnn x))).symm
end Integral
section Geometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
omit [BorelSpace E] in
/-- Constants are chosen from the measure and one fixed finite simplex before
any potential. Lemma16 produces every vertex bound, and the actual affine
maximum converts it to linear growth of the actual conjugate. -/
theorem exists_uniform_legendre_lower (μ : Measure E) [IsFiniteMeasure μ]
    (h0 : (0 : E) ∈ interior (convexHull ℝ μ.support)) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ φ : E → EReal,
      (∀ x, 0 ≤ φ x) → φ 0 = 0 → ConvexPotential φ → PotentialIntegrable φ μ →
      ∀ y, 0 ≤ legendre φ y ∧
        ((c * ‖y‖ - C * (∫ x, (φ x).toReal ∂μ) : ℝ) : EReal) ≤ legendre φ y := by
  classical
  let K := interior (convexHull ℝ μ.support)
  obtain ⟨s, hs, hsK, hs0⟩ := exists_finite_hull_neighborhood (K := K) isOpen_interior h0
  obtain ⟨c, hc, hcoerc⟩ := affineMaximum_coercive s hs hs0
  have hp : ∀ x : {x : E // x ∈ s}, ∃ C : ℝ, 0 < C ∧ ∀ φ : E → EReal,
      (∀ y, 0 ≤ φ y) → Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)} →
      AEMeasurable (fun y => (φ y).toENNReal) μ → (∫⁻ y, (φ y).toENNReal ∂μ) ≠ ⊤ →
        φ x ≤ ((C * (∫⁻ y, (φ y).toENNReal ∂μ).toReal : ℝ) : EReal) := by
    intro x
    exact FunctionalInequalities.Probability.exists_pos_le_mul_lintegral_toReal_of_convex_epigraph
      μ x (hsK x.2)
  choose Cs hCs hpoint using hp
  let C : ℝ := ∑ x ∈ s.attach, Cs x
  have hCle (x : {x : E // x ∈ s}) : Cs x ≤ C :=
    Finset.single_le_sum (fun i _ => (hCs i).le) (s.mem_attach x)
  have hs_copy := hs
  obtain ⟨x0, hx0⟩ := hs_copy
  have hC : 0 < C := (hCs ⟨x0, hx0⟩).trans_le (hCle ⟨x0, hx0⟩)
  refine ⟨c, C, hc, hC, ?_⟩
  intro φ hnn hφ0 hconv hφ
  obtain ⟨hm, hlin, hM⟩ := lintegral_nonneg_potential φ hφ hnn
  have hfinite : (∫⁻ x, (φ x).toENNReal ∂μ) ≠ ⊤ := by rw [hlin]; exact ENNReal.ofReal_ne_top
  have hvertex : ∀ x ∈ s, φ x ≤ ((C * (∫ z, (φ z).toReal ∂μ) : ℝ) : EReal) := by
    intro x hx
    have hp := hpoint ⟨x, hx⟩ φ hnn hconv.2 hm hfinite
    rw [hlin, ENNReal.toReal_ofReal hM] at hp
    exact hp.trans (EReal.coe_le_coe_iff.mpr
      (mul_le_mul_of_nonneg_right (hCle ⟨x, hx⟩) hM))
  have hfs : ∀ x ∈ s, φ x ≠ ⊤ ∧ φ x ≠ ⊥ := by
    intro x hx
    exact ⟨ne_of_lt ((hvertex x hx).trans_lt (EReal.coe_lt_top _)), hφ.1 x⟩
  have hreal : ∀ x ∈ s, (φ x).toReal ≤ C * (∫ z, (φ z).toReal ∂μ) := by
    intro x hx
    simpa only [EReal.toReal_coe] using
      EReal.toReal_le_toReal (hvertex x hx) (hφ.1 x) (EReal.coe_ne_top _)
  intro y
  refine ⟨?_, ?_⟩
  · simpa only [inner_zero_left, EReal.coe_zero, hφ0, sub_zero, legendre] using
      (le_iSup (fun x : E => (inner ℝ x y : EReal) - φ x) 0)
  · exact (EReal.coe_le_coe_iff.mpr (hcoerc _ _ hreal y)).trans
      (affineMaximum_le_legendre φ s hs hfs y)
omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Nonnegativity plus the actual linear lower bound controls the density after
scaling by max(M,1). This is where the small-integral protection is used. -/
theorem density_scaled_le_exp (φ : E → EReal) {c C M a : ℝ}
    (hC : 0 ≤ C) (ha : 1 ≤ a) (hMa : M ≤ a)
    (hlower : ∀ y, 0 ≤ legendre φ y ∧ ((c * ‖y‖ - C * M : ℝ) : EReal) ≤ legendre φ y)
    (y : E) : density (legendre φ) (a • y) ≤ ENNReal.ofReal (Real.exp (C - c * ‖y‖)) := by
  have hb : ((c * ‖y‖ - C : ℝ) : EReal) ≤ legendre φ (a • y) := by
    by_cases h : c * ‖y‖ - C ≤ 0
    · exact (EReal.coe_nonpos.mpr h).trans (hlower (a • y)).1
    · have hpos : 0 ≤ c * ‖y‖ - C := (lt_of_not_ge h).le
      have hs := mul_le_mul_of_nonneg_right ha hpos
      have hm := mul_le_mul_of_nonneg_left hMa hC
      have hnorm : ‖a • y‖ = a * ‖y‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ a)]
      apply (EReal.coe_le_coe_iff.mpr (show c * ‖y‖ - C ≤ c * ‖a • y‖ - C * M by
        rw [hnorm]
        nlinarith)).trans (hlower (a • y)).2
  have he := EReal.exp_monotone (EReal.neg_le_neg_iff.mpr hb)
  simpa only [density, ← EReal.coe_neg, EReal.exp_coe, neg_sub] using he
/-- Genuine Haar change of variables for nonnegative integrals, retaining
infinite integrals. There is no integrability or finite-mass premise. -/
theorem lintegral_eq_pow_mul_smul (dx : Measure E) [dx.IsAddHaarMeasure]
    (f : E → ℝ≥0∞) (hf : Measurable f) {a : ℝ} (ha : 0 < a) :
    (∫⁻ y, f y ∂dx) = ENNReal.ofReal (a ^ Module.finrank ℝ E) * ∫⁻ y, f (a • y) ∂dx := by
  have hm := lintegral_map hf (measurable_const_smul a) (μ := dx)
  rw [Measure.map_addHaar_smul dx ha.ne', lintegral_smul_measure, smul_eq_mul,
    abs_of_pos (inv_pos.mpr (pow_pos ha _)), ENNReal.ofReal_inv_of_pos (pow_pos ha _)] at hm
  calc
    (∫⁻ y, f y ∂dx) = ENNReal.ofReal (a ^ Module.finrank ℝ E) *
        ((ENNReal.ofReal (a ^ Module.finrank ℝ E))⁻¹ * ∫⁻ y, f y ∂dx) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel
        (ne_of_gt (ENNReal.ofReal_pos.mpr (pow_pos ha _))) ENNReal.ofReal_ne_top, one_mul]
    _ = _ := by rw [hm]
/-- A genuine polynomial bound, with A selected before the potential.
The fixed dominator and its finite Haar integral are derived from Lemma16 and
the actual finite simplex. max(M,1) retains the small-M regime. -/
theorem exists_uniform_mass_bound (dx μ : Measure E) [dx.IsAddHaarMeasure] [IsFiniteMeasure μ]
    (h0 : (0 : E) ∈ interior (convexHull ℝ μ.support)) :
    ∃ A : ℝ, 0 < A ∧ ∀ φ : E → EReal,
      (∀ x, 0 ≤ φ x) → φ 0 = 0 → ConvexPotential φ → PotentialIntegrable φ μ →
      mass dx (legendre φ) ≤ ENNReal.ofReal
        (A * (max (∫ x, (φ x).toReal ∂μ) 1) ^ Module.finrank ℝ E) := by
  obtain ⟨c, C, hc, hC, hlower⟩ := exists_uniform_legendre_lower μ h0
  let D : E → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (C - c * ‖y‖))
  let Z : ℝ≥0∞ := ∫⁻ y, D y ∂dx
  have hZ : Z ≠ ⊤ := (lintegral_ofReal_ne_top_iff_integrable
    (integrable_exp_sub_norm dx hc C).aestronglyMeasurable
    (Eventually.of_forall fun _ => (Real.exp_pos _).le)).mpr (integrable_exp_sub_norm dx hc C)
  let A : ℝ := max Z.toReal 1
  have hA : 0 < A := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hZA : Z ≤ ENNReal.ofReal A := by
    rw [← ENNReal.ofReal_toReal hZ]
    exact ENNReal.ofReal_le_ofReal (le_max_left _ _)
  refine ⟨A, hA, ?_⟩
  intro φ hnn hφ0 hconv hφ
  let M : ℝ := ∫ x, (φ x).toReal ∂μ
  let a : ℝ := max M 1
  have ha : 0 < a := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hscaled : (∫⁻ y, density (legendre φ) (a • y) ∂dx) ≤ Z :=
    lintegral_mono (density_scaled_le_exp φ hC.le (le_max_right _ _) (le_max_left _ _)
      (hlower φ hnn hφ0 hconv hφ))
  calc
    mass dx (legendre φ) = ENNReal.ofReal (a ^ Module.finrank ℝ E) *
        ∫⁻ y, density (legendre φ) (a • y) ∂dx :=
      lintegral_eq_pow_mul_smul dx _ (measurable_density_legendre φ) ha
    _ ≤ ENNReal.ofReal (a ^ Module.finrank ℝ E) * ENNReal.ofReal A :=
      mul_le_mul' le_rfl (hscaled.trans hZA)
    _ = _ := by rw [← ENNReal.ofReal_mul (pow_pos ha _).le, mul_comm]
omit [FiniteDimensional ℝ E] [BorelSpace E] in
/-- The actual extended logarithm gives the functional bound even at zero mass.
No finite logarithm is supplied or totalized. -/
theorem functional_le_of_mass_bound (dx μ : Measure E) (φ : E → EReal)
    {A : ℝ} (hA : 0 < A)
    (hbound : mass dx (legendre φ) ≤ ENNReal.ofReal
      (A * (max (∫ x, (φ x).toReal ∂μ) 1) ^ Module.finrank ℝ E)) :
    variationalFunctional dx μ φ ≤
      ((Real.log A + (Module.finrank ℝ E : ℝ) * Real.log (max (∫ x, (φ x).toReal ∂μ) 1) -
        (∫ x, (φ x).toReal ∂μ) : ℝ) : EReal) := by
  have ha : 0 < max (∫ x, (φ x).toReal ∂μ) 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hlog := ENNReal.log_le_log hbound
  rw [ENNReal.log_ofReal_of_pos (mul_pos hA (pow_pos ha _)),
    Real.log_mul hA.ne' (pow_pos ha _).ne', Real.log_pow] at hlog
  simpa only [variationalFunctional, ← EReal.coe_sub] using
    EReal.sub_le_sub hlog (le_refl ((∫ x, (φ x).toReal ∂μ : ℝ) : EReal))
/-- The source probability, first moment, centering and full-dimensional support
produce the needed geometry. The constant is quantified before every phi;
this is new P12 coercivity support, not source Lemma15's particular constant. -/
theorem exists_coercivity_of_centered_probability (dx μ : Measure E) [dx.IsAddHaarMeasure]
    [IsProbabilityMeasure μ] (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hint : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) :
    ∃ A : ℝ,
      0 < A ∧
        ∀ φ : E → EReal,
          (∀ x, 0 ≤ φ x) →
            φ 0 = 0 →
              ConvexPotential φ →
                PotentialIntegrable φ μ →
                  (mass dx (legendre φ) ≤
                      ENNReal.ofReal
                        (A * (max (∫ x, (φ x).toReal ∂μ) 1) ^ Module.finrank ℝ E)) ∧
                    variationalFunctional dx μ φ ≤
                      ((Real.log A +
                              (Module.finrank ℝ E : ℝ) *
                                Real.log (max (∫ x, (φ x).toReal ∂μ) 1) -
                            (∫ x, (φ x).toReal ∂μ) :
                          ℝ) :
                        EReal) := by
  have hμ : μ ≠ 0 := by
    intro hz
    have hu : μ Set.univ = 1 := measure_univ
    simp only [hz, FunLike.coe_zero, Pi.zero_apply, zero_ne_one] at hu
  have h0 :=
    FunctionalInequalities.Probability.zero_mem_interior_convexHull_support_of_integral_eq_zero
      μ hμ hsub hint hbar
  obtain ⟨A, hA, hmass⟩ := exists_uniform_mass_bound dx μ h0
  refine ⟨A, hA, ?_⟩
  intro φ hnn hφ0 hconv hφ
  have h := hmass φ hnn hφ0 hconv hφ
  exact ⟨h, functional_le_of_mass_bound dx μ φ hA h⟩
end Geometry
/-- Elementary logarithmic coercivity. The bound is constructed from A,n,b;
no asymptotic growth or desired integral bound is passed as a premise. -/
theorem exists_bound_of_log_lower (A : ℝ) (n : ℕ) (b : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℝ, 0 ≤ M →
      b ≤ Real.log A + (n : ℝ) * Real.log (max M 1) - M → M ≤ B := by
  let d : ℝ := 2 * ((n : ℝ) + 1)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd : 0 < d := by dsimp [d]; positivity
  let B : ℝ := max 1 (2 * (Real.log A + (n : ℝ) * Real.log d - b))
  refine ⟨B, zero_le_one.trans (le_max_left _ _), ?_⟩
  intro M hM hb
  by_cases hsmall : M ≤ 1
  · exact hsmall.trans (le_max_left _ _)
  have hMpos : 0 < M := by linarith
  have hq := Real.log_le_sub_one_of_pos (div_pos hMpos hd)
  rw [Real.log_div hMpos.ne' hd.ne'] at hq
  have hmul := mul_le_mul_of_nonneg_left hq hn
  have hfraction : (n : ℝ) * (M / d) ≤ M / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
    have hcancel : d * (M / d) = M := mul_div_cancel₀ _ hd.ne'
    have hqpos : 0 ≤ M / d := div_nonneg hM hd.le
    dsimp [d] at hcancel
    nlinarith
  rw [max_eq_left (le_of_not_ge hsmall)] at hb
  have hB : M ≤ 2 * (Real.log A + (n : ℝ) * Real.log d - b) := by nlinarith
  exact hB.trans (le_max_right _ _)

section FiniteDimensional

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E]
/-- Actual normalized-sequence integral control from a finite eventual
functional lower bound, as in CEK (62). The finite prefix is handled by the
proved bounded-range theorem; no desired sequence bound is supplied. -/
theorem exists_integral_bound_of_eventual_functional_lower (dx μ : Measure E)
    [dx.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hint : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0) (φ : ℕ → E → EReal)
    (hnn : ∀ j x, 0 ≤ φ j x) (hφ0 : ∀ j, φ j 0 = 0) (hconv : ∀ j, ConvexPotential (φ j))
    (hφ : ∀ j, PotentialIntegrable (φ j) μ) (b : ℝ)
    (hlower : ∀ᶠ j in atTop, (b : EReal) ≤ variationalFunctional dx μ (φ j)) :
    ∃ B : ℝ,
      0 ≤ B ∧ (∀ j, (∫ x, (φ j x).toReal ∂μ) ≤ B) ∧ (⨆ j, ∫⁻ x, (φ j x).toENNReal ∂μ) ≠ ⊤ := by
  obtain ⟨A, _hA, hc⟩ := exists_coercivity_of_centered_probability dx μ hsub hint hbar
  obtain ⟨B, _hB, hlogbound⟩ := exists_bound_of_log_lower A (Module.finrank ℝ E) b
  have hev : ∀ᶠ j in atTop, (∫ x, (φ j x).toReal ∂μ) ≤ B := by
    filter_upwards [hlower] with j hj
    apply hlogbound _ (lintegral_nonneg_potential (φ j) (hφ j) (hnn j)).2.2
    exact EReal.coe_le_coe_iff.mp (hj.trans (hc (φ j) (hnn j) (hφ0 j) (hconv j) (hφ j)).2)
  have hbu : IsBoundedUnder (fun a b : ℝ => a ≤ b) atTop (fun j => ∫ x, (φ j x).toReal ∂μ) :=
    ⟨B, hev⟩
  obtain ⟨B', hB'⟩ := hbu.bddAbove_range
  refine ⟨max B' 0, le_max_right _ _, ?_, ?_⟩
  · intro j
    exact (hB' (mem_range_self j)).trans (le_max_left _ _)
  · apply ne_top_of_le_ne_top (b := ENNReal.ofReal (max B' 0)) ENNReal.ofReal_ne_top
    apply iSup_le
    intro j
    rw [(lintegral_nonneg_potential (φ j) (hφ j) (hnn j)).2.1]
    exact ENNReal.ofReal_le_ofReal ((hB' (mem_range_self j)).trans (le_max_left _ _))
/-- A normalized maximizing sequence whose extended functional limit lies
above a known finite level supplies (62). An infinite candidate limit is allowed. -/
theorem exists_integral_bound_of_tendsto_functional_above
    (dx μ : Measure E) [dx.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (hsub : ∀ V : Submodule ℝ E, μ (V : Set E)ᶜ = 0 → V = ⊤)
    (hint : Integrable (fun x : E => x) μ) (hbar : ∫ x, x ∂μ = 0)
    (φ : ℕ → E → EReal) (hnn : ∀ j x, 0 ≤ φ j x) (hφ0 : ∀ j, φ j 0 = 0)
    (hconv : ∀ j, ConvexPotential (φ j)) (hφ : ∀ j, PotentialIntegrable (φ j) μ)
    (L : EReal) (b : ℝ) (hb : (b : EReal) < L)
    (hlim : Tendsto (fun j => variationalFunctional dx μ (φ j)) atTop (𝓝 L)) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ j, (∫ x, (φ j x).toReal ∂μ) ≤ B) ∧
      (⨆ j, ∫⁻ x, (φ j x).toENNReal ∂μ) ≠ ⊤ := by
  apply exists_integral_bound_of_eventual_functional_lower dx μ hsub hint hbar φ hnn hφ0 hconv hφ b
  exact (hlim.eventually (Ioi_mem_nhds hb)).mono fun _ h => h.le

end FiniteDimensional

end

section
-- A uniform real coercivity bound.

open MeasureTheory Filter Set
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- A finite real ceiling for the normalized coercivity expression. -/
theorem real_coercivity_le_uniform (A : ℝ) (n : ℕ) (M : ℝ) (hM : 0 ≤ M) :
    Real.log A + (n : ℝ) * Real.log (max M 1) - M ≤
      Real.log A + (n : ℝ) * Real.log (2 * ((n : ℝ) + 1)) := by
  let d : ℝ := 2 * ((n : ℝ) + 1)
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hd1 : 1 ≤ d := by dsimp [d]; linarith
  have hd : 0 < d := zero_lt_one.trans_le hd1
  by_cases hs : M ≤ 1
  · rw [max_eq_right hs, Real.log_one, mul_zero]
    have hlog : 0 ≤ (n : ℝ) * Real.log d := mul_nonneg hn (Real.log_nonneg hd1)
    change Real.log A + 0 - M ≤ Real.log A + (n : ℝ) * Real.log d
    linarith
  · have hMp : 0 < M := by linarith
    have hq := Real.log_le_sub_one_of_pos (div_pos hMp hd)
    rw [Real.log_div hMp.ne' hd.ne'] at hq
    have hmul := mul_le_mul_of_nonneg_left hq hn
    have hfrac : (n : ℝ) * (M / d) ≤ M := by
      have hcancel : d * (M / d) = M := mul_div_cancel₀ _ hd.ne'
      have hqp : 0 ≤ M / d := div_nonneg hM hd.le
      dsimp [d] at hcancel
      nlinarith [mul_nonneg hn hqp]
    rw [max_eq_left (le_of_not_ge hs)]
    change Real.log A + (n : ℝ) * Real.log M - M ≤ Real.log A + (n : ℝ) * Real.log d
    nlinarith

end

end FunctionalInequalities.Probability.MomentMeasure
