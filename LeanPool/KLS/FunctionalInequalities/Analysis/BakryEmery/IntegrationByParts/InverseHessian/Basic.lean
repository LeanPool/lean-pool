/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.MongeAmpere
public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.Basic
public import LeanPool.KLS.FunctionalInequalities.Analysis.Cutoff.Conservativity

/-!
# Integration by parts for the inverse-Hessian operator (Letwin (2.2), compact tests)

Letwin arXiv:2607.24164v1, pp. 6–7: for a given smooth potential `φ` with everywhere positive
definite
Hessian, `∫ e^{−φ} = 1` and the zero-order Monge–Ampère equation `log det ∇²φ = −φ + V ∘ ∇φ` with
`V`
smooth on an open set containing the gradient range (the source has `V` smooth near the closure of
the
bounded convex `K = ∇φ(ℝⁿ)`), the operator `L f = Σ_{ij} A_{ij} ∂_{ij}f − Σ_i ∂_iV(∇φ) ∂_if`, `A =
(∇²φ)⁻¹`,
satisfies the weighted integration by parts `∫ (Lf) g dν = −∫ Σ_{ij} A_{ij} ∂_if ∂_jg dν`, `dν =
e^{−φ}dx`,
for smooth `f`, `g` with one of them compactly supported; hence `∫ Lf dν = 0` and the integrated
symmetry
`∫ (Lf) g dν = ∫ f (Lg) dν` on compact smooth tests. Haar integrability comes from the compact test;
the
normalisation gives integrability of `e^{−φ}` and the probability property of `ν`. Lemma A.5 holds
for given cutoffs
with the conclusions of Lemma A.4
(`integrable_and_integral_hessianInverseOperator_eq_zero_of_cutoffs`, through the
generic `integrable_and_integral_eq_zero_of_cutoff_defect`). The cutoffs themselves (Lemma A.4) are
constructed
downstream in `IntegrationByParts/InverseHessian/Cutoff.lean`:
`exists_scaled_cutoffs_hessianInverseOperator` for real
`R ≥ 1` and its natural-index form `exists_cutoffs_hessianInverseOperator`, whose conclusions are
exactly the cutoff
premises of Lemma A.5 here. Not provided: a moment map for an arbitrary law, a closed `L²`
generator, Brascamp–Lieb
(A.6), Theorem 2.5 or Proposition 2.8.
-/

@[expose] public section

noncomputable section
open MeasureTheory
open scoped ContDiff RealInnerProductSpace

namespace FunctionalInequalities.Analysis.BakryEmery

/-- A unit normalisation `∫ e^{−φ} = 1` forces integrability of `e^{−φ}`. -/
theorem integrable_exp_neg_of_integral_eq_one {α : Type*} [MeasurableSpace α] (m : Measure α)
    (φ : α → ℝ) (hnorm : ∫ x, Real.exp (-φ x) ∂m = 1) :
    Integrable (fun x => Real.exp (-φ x)) m := by
  by_contra hh
  rw [integral_undef hh] at hnorm
  norm_num at hnorm

/-- The normalised tilt `e^{−φ} dm` is a probability measure. -/
theorem isProbabilityMeasure_tilted_neg_of_integral_eq_one {α : Type*} [MeasurableSpace α]
    (m : Measure α) (φ : α → ℝ) (hnorm : ∫ x, Real.exp (-φ x) ∂m = 1) :
    IsProbabilityMeasure (m.tilted (-φ)) := by
  have : NeZero m := ⟨by intro hm; rw [hm] at hnorm; simp at hnorm⟩
  exact isProbabilityMeasure_tilted (integrable_exp_neg_of_integral_eq_one m φ hnorm)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/--
**Weighted integration by parts for `L`** (Letwin (2.2)) with `V` smooth on an open set containing
the
gradient range and one of the two smooth tests compactly supported. -/
theorem integral_hessianInverseOperator_mul_eq_neg (m : Measure E) [m.IsAddHaarMeasure]
    {φ V f g : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport f ∨ HasCompactSupport g) {U : Set E} (hU : IsOpen U)
    (hV : ContDiffOn ℝ ∞ V U) (hRange : Set.range (gradient φ) ⊆ U)
    (hMA : ∀ y, logDetHessian φ (stdOrthonormalBasis ℝ E) y = -φ y + V (gradient φ y))
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v)
    (hnorm : ∫ x, Real.exp (-φ x) ∂m = 1) :
    (∫ x, hessianInverseOperator φ V f x * g x ∂(m.tilted (-φ))) =
      -∫ x,
          ∑ i,
            ∑ j,
              inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x i j *
                  fderiv ℝ f x (stdOrthonormalBasis ℝ E i) *
                fderiv ℝ g x (stdOrthonormalBasis ℝ E j) ∂(m.tilted (-φ)) := by
  let b := stdOrthonormalBasis ℝ E
  let F (i j : Fin (Module.finrank ℝ E)) : E → ℝ := fun x =>
    Real.exp (-φ x) * inverseHessianEntry φ b x i j * fderiv ℝ f x (b j)
  have hF (i j : Fin (Module.finrank ℝ E)) : ContDiff ℝ ∞ (F i j) := by
    exact
      ((hφ.neg.exp).mul (contDiff_inverseHessianEntry b hφ hPD i j)).mul
        (contDiff_fderiv_apply hf (by simp) (b j))
  have hFc (i j : Fin (Module.finrank ℝ E)) : HasCompactSupport (F i j) ∨ HasCompactSupport g := by
    rcases hc with hfc | hgc
    · left
      exact (hfc.fderiv_apply ℝ (b j)).mul_left
    · exact Or.inr hgc
  have hi (i j : Fin (Module.finrank ℝ E)) :=
    integrable_fderiv_mul_of_hasCompactSupport m (hF i j) hg (hFc i j) (b i)
  have hRow1 (i : Fin (Module.finrank ℝ E)) :
    Integrable (fun x => ∑ j, fderiv ℝ (F i j) x (b i) * g x) m :=
    integrable_finsetSum Finset.univ (fun j _ => (hi i j).1)
  have hRow2 (i : Fin (Module.finrank ℝ E)) :
    Integrable (fun x => ∑ j, F i j x * fderiv ℝ g x (b i)) m :=
    integrable_finsetSum Finset.univ (fun j _ => (hi i j).2.1)
  have hHaar :
    (∫ x, Real.exp (-φ x) * (hessianInverseOperator φ V f x * g x) ∂m) =
      -∫ x,
          Real.exp (-φ x) *
            (∑ i,
              ∑ j,
                inverseHessianEntry φ b x i j * fderiv ℝ f x (b i) * fderiv ℝ g x (b j)) ∂m := by
    calc
      _ = ∫ x, ∑ i, ∑ j, fderiv ℝ (F i j) x (b i) * g x ∂m := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [← mul_assoc, ←
          density_hessianInverseOperator_flux hφ hf hU hV hMA (hRange (Set.mem_range_self x))
            (hPD x)]
        simp only [Finset.sum_mul, F]
        ring
      _ = ∑ i, ∑ j, ∫ x, fderiv ℝ (F i j) x (b i) * g x ∂m := by
        rw [integral_finsetSum _ (fun i _ => hRow1 i)]
        apply Finset.sum_congr rfl; intro i _hi
        exact integral_finsetSum _ (fun j _ => (hi i j).1)
      _ = ∑ i, ∑ j, -∫ x, F i j x * fderiv ℝ g x (b i) ∂m := by
        apply Finset.sum_congr rfl; intro i _hi
        apply Finset.sum_congr rfl; intro j _hj
        exact integral_fderiv_mul_eq_neg_of_hasCompactSupport m (hF i j) hg (hFc i j) (b i)
      _ = -∫ x, ∑ i, ∑ j, F i j x * fderiv ℝ g x (b i) ∂m := by
        rw [integral_finsetSum _ (fun i _ => hRow2 i)]
        simp_rw [integral_finsetSum _ (fun j _ => (hi _ j).2.1)]
        simp only [Finset.sum_neg_distrib]
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [] with x
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _hi
        apply Finset.sum_congr rfl; intro j _hj
        dsimp [F]
        rw [inverseHessianEntry_symm b (hφ.of_le (WithTop.coe_le_coe.mpr le_top)) x j i]
        ring
  rw [integral_tilted, integral_tilted]
  simp only [Pi.neg_apply, hnorm, div_one, smul_eq_mul]
  exact hHaar

/-- Letwin (2.2) in the source form: `V` smooth on an open neighbourhood of `closure K` and
`∇φ(ℝⁿ) ⊆ K`. -/
theorem integral_hessianInverseOperator_mul_eq_neg_on_range (m : Measure E) [m.IsAddHaarMeasure]
    {φ V f g : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport f ∨ HasCompactSupport g)
    {K U : Set E} (hU : IsOpen U) (hKU : closure K ⊆ U) (hV : ContDiffOn ℝ ∞ V U)
    (hRange : Set.range (gradient φ) ⊆ K)
    (hMA : ∀ y, logDetHessian φ (stdOrthonormalBasis ℝ E) y = -φ y + V (gradient φ y))
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v)
    (hnorm : ∫ x, Real.exp (-φ x) ∂m = 1) :
    (∫ x, hessianInverseOperator φ V f x * g x ∂(m.tilted (-φ))) =
      -∫ x, ∑ i, ∑ j, inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x i j *
        fderiv ℝ f x (stdOrthonormalBasis ℝ E i) *
        fderiv ℝ g x (stdOrthonormalBasis ℝ E j) ∂(m.tilted (-φ)) :=
  integral_hessianInverseOperator_mul_eq_neg m hφ hf hg hc hU hV
    (fun _ hx => hKU (subset_closure (hRange hx))) hMA hPD hnorm

/-- `∫ Lf dν = 0` for compactly supported smooth `f` (invariance of `ν`). -/
theorem integral_hessianInverseOperator_eq_zero (m : Measure E) [m.IsAddHaarMeasure]
    {φ V f : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    {U : Set E} (hU : IsOpen U) (hV : ContDiffOn ℝ ∞ V U)
    (hRange : Set.range (gradient φ) ⊆ U)
    (hMA : ∀ y, logDetHessian φ (stdOrthonormalBasis ℝ E) y = -φ y + V (gradient φ y))
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v)
    (hnorm : ∫ x, Real.exp (-φ x) ∂m = 1) :
    (∫ x, hessianInverseOperator φ V f x ∂(m.tilted (-φ))) = 0 := by
  simpa using integral_hessianInverseOperator_mul_eq_neg m hφ hf (g := fun _ => (1 : ℝ))
    contDiff_const (Or.inl hfc) hU hV hRange hMA hPD hnorm

/-- Integrated symmetry of `L` on two compactly supported smooth tests (not a closed `L²`
self-adjointness statement). -/
theorem integral_hessianInverseOperator_mul_comm (m : Measure E) [m.IsAddHaarMeasure]
    {φ V f g : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    {U : Set E} (hU : IsOpen U) (hV : ContDiffOn ℝ ∞ V U)
    (hRange : Set.range (gradient φ) ⊆ U)
    (hMA : ∀ y, logDetHessian φ (stdOrthonormalBasis ℝ E) y = -φ y + V (gradient φ y))
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v)
    (hnorm : ∫ x, Real.exp (-φ x) ∂m = 1) :
    (∫ x, hessianInverseOperator φ V f x * g x ∂(m.tilted (-φ))) =
      ∫ x, f x * hessianInverseOperator φ V g x ∂(m.tilted (-φ)) := by
  have h1 := integral_hessianInverseOperator_mul_eq_neg m hφ hf hg (Or.inl hfc) hU hV hRange hMA
    hPD hnorm
  have h2 := integral_hessianInverseOperator_mul_eq_neg m hφ hg hf (Or.inl hgc) hU hV hRange hMA
    hPD hnorm
  calc
    _ = _ := h1
    _ = -∫ x, ∑ i, ∑ j, inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x i j *
        fderiv ℝ g x (stdOrthonormalBasis ℝ E i) * fderiv ℝ f x (stdOrthonormalBasis ℝ E j)
        ∂(m.tilted (-φ)) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with x
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl; intro i _hi
      apply Finset.sum_congr rfl; intro j _hj
      rw [inverseHessianEntry_symm _ (hφ.of_le (WithTop.coe_le_coe.mpr le_top)) x j i]
      ring
    _ = ∫ x, hessianInverseOperator φ V g x * f x ∂(m.tilted (-φ)) := h2.symm
    _ = _ := by apply integral_congr_ae; filter_upwards [] with x; ring

/--
**Letwin Lemma A.5 for the inverse-Hessian operator, given cutoffs** (p. 18): for a given potential
as in (2.2),
smooth bounded `f` with `Lf + c f ≥ 0`, `c > 0`, and smooth compactly supported cutoffs with the
conclusions of
Lemma A.4 (`0 ≤ χ_n ≤ 1`, `χ_n → 1`, `‖Lχ_n‖_{L¹(ν)} → 0`), `Lf ∈ L¹(ν)` and `∫ Lf dν = 0`. The
symmetry and the
cutoff-product integrability are derived from (2.2) and continuity. The cutoffs are a premise here;
for a potential in
the Lemma A.4 source class they are supplied by `exists_cutoffs_hessianInverseOperator`
(`IntegrationByParts/InverseHessian/Cutoff.lean`).
-/
theorem integrable_and_integral_hessianInverseOperator_eq_zero_of_cutoffs (m : Measure E)
    [m.IsAddHaarMeasure] {φ V f : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hf : ContDiff ℝ ∞ f) {U : Set E}
    (hU : IsOpen U) (hV : ContDiffOn ℝ ∞ V U) (hRange : Set.range (gradient φ) ⊆ U)
    (hMA : ∀ y, logDetHessian φ (stdOrthonormalBasis ℝ E) y = -φ y + V (gradient φ y))
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v)
    (hnorm : ∫ x, Real.exp (-φ x) ∂m = 1) (C : ℝ) (hfBound : ∀ x, |f x| ≤ C) (c : ℝ)
    (hc : 0 < c) (hLower : ∀ x, 0 ≤ hessianInverseOperator φ V f x + c * f x) (chi : ℕ → E → ℝ)
    (hChiSmooth : ∀ n, ContDiff ℝ ∞ (chi n)) (hChiSupport : ∀ n, HasCompactSupport (chi n))
    (hChiBounds : ∀ n x, 0 ≤ chi n x ∧ chi n x ≤ 1)
    (hChiLim : ∀ x, Filter.Tendsto (fun n => chi n x) Filter.atTop (nhds 1))
    (hDefect : ∀ n, Integrable (hessianInverseOperator φ V (chi n)) (m.tilted (-φ)))
    (hDefectLim :
      Filter.Tendsto (fun n => ∫ x, |hessianInverseOperator φ V (chi n) x| ∂(m.tilted (-φ)))
        Filter.atTop (nhds 0)) :
    Integrable (hessianInverseOperator φ V f) (m.tilted (-φ)) ∧
      (∫ x, hessianInverseOperator φ V f x ∂(m.tilted (-φ))) = 0 := by
  have := isProbabilityMeasure_tilted_neg_of_integral_eq_one m φ hnorm
  let mu : ProbabilityMeasure E :=
    ⟨m.tilted (-φ), isProbabilityMeasure_tilted_neg_of_integral_eq_one m φ hnorm⟩
  have hC : 0 ≤ C := (abs_nonneg (f 0)).trans (hfBound 0)
  have hLf : Continuous (hessianInverseOperator φ V f) := by
    have hgrad : Continuous (gradient φ) :=
      continuous_gradient (hφ.of_le (WithTop.coe_le_coe.mpr le_top))
    have hdV : ContinuousOn (fderiv ℝ V) U :=
      hV.continuousOn_fderiv_of_isOpen hU (WithTop.coe_le_coe.mpr le_top)
    have hdVg : Continuous (fun y => fderiv ℝ V (gradient φ y)) :=
      hdV.comp_continuous hgrad (fun y => hRange ⟨y, rfl⟩)
    unfold hessianInverseOperator nondivergenceOperator
    refine
      (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_).sub
        (continuous_finsetSum _ fun i _ => ?_)
    · exact
        (contDiff_inverseHessianEntry _ hφ hPD i j).continuous.mul
          (contDiff_bilinearIteratedFDerivTwo_apply hf _ _).continuous
    · exact
        (hdVg.clm_apply continuous_const).mul
          (contDiff_fderiv_apply (m := 0)
              (hf.of_le (WithTop.coe_le_coe.mpr le_top) : ContDiff ℝ 1 f) (by norm_num)
              _).continuous
  have hCutoffG (n : ℕ) :
    Integrable (fun x => chi n x * hessianInverseOperator φ V f x) (m.tilted (-φ)) :=
    ((hChiSmooth n).continuous.mul hLf).integrable_of_hasCompactSupport
      (hChiSupport n).mul_right
  have hSym (n : ℕ) :
    (∫ x, chi n x * hessianInverseOperator φ V f x ∂(m.tilted (-φ))) =
      ∫ x, f x * hessianInverseOperator φ V (chi n) x ∂(m.tilted (-φ)) := by
    have h1 :=
      integral_hessianInverseOperator_mul_eq_neg m hφ hf (hChiSmooth n) (Or.inr (hChiSupport n))
        hU hV hRange hMA hPD hnorm
    have h2 :=
      integral_hessianInverseOperator_mul_eq_neg m hφ (hChiSmooth n) hf (Or.inl (hChiSupport n))
        hU hV hRange hMA hPD hnorm
    calc
      (∫ x, chi n x * hessianInverseOperator φ V f x ∂(m.tilted (-φ))) =
          ∫ x, hessianInverseOperator φ V f x * chi n x ∂(m.tilted (-φ)) := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = _ := h1
      _ =
          -∫ x,
              ∑ i,
                ∑ j,
                  inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x i j *
                      fderiv ℝ (chi n) x (stdOrthonormalBasis ℝ E i) *
                    fderiv ℝ f x (stdOrthonormalBasis ℝ E j) ∂(m.tilted (-φ)) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [] with x
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _hi
        apply Finset.sum_congr rfl
        intro j _hj
        rw [inverseHessianEntry_symm _ (hφ.of_le (WithTop.coe_le_coe.mpr le_top)) x j i]
        ring
      _ = ∫ x, hessianInverseOperator φ V (chi n) x * f x ∂(m.tilted (-φ)) := h2.symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
  exact
    integrable_and_integral_eq_zero_of_cutoff_defect mu f (hessianInverseOperator φ V f)
      hf.continuous.aestronglyMeasurable hLf.aestronglyMeasurable C hC
      (Filter.Eventually.of_forall hfBound) c hc (Filter.Eventually.of_forall hLower) chi
      (fun n => hessianInverseOperator φ V (chi n))
      (fun n => (hChiSmooth n).continuous.aestronglyMeasurable)
      (fun n => Filter.Eventually.of_forall (hChiBounds n))
      (Filter.Eventually.of_forall hChiLim) hDefect hDefectLim hCutoffG hSym

/--
**Energy identity** (Letwin Lemma A.4, p. 17: (2.2) with `f = φ`, `g = h ∘ φ`): for a given
potential as in (2.2)
and smooth `h` with `h ∘ φ` compactly supported, `∫ (Lφ) h(φ) dν = −∫ h′(φ) Σ_ij A_ij ∂_iφ ∂_jφ dν`.
No minimum,
cutoff or bound is a premise.
-/
theorem integral_hessianInverseOperator_self_mul_comp_eq_neg (m : Measure E)
    [m.IsAddHaarMeasure] {φ V : E → ℝ} {h : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hh : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport (fun x => h (φ x))) {U : Set E} (hU : IsOpen U)
    (hV : ContDiffOn ℝ ∞ V U) (hRange : Set.range (gradient φ) ⊆ U)
    (hMA : ∀ y, logDetHessian φ (stdOrthonormalBasis ℝ E) y = -φ y + V (gradient φ y))
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v)
    (hnorm : ∫ x, Real.exp (-φ x) ∂m = 1) :
    (∫ x, hessianInverseOperator φ V φ x * h (φ x) ∂(m.tilted (-φ))) =
      -∫ x,
          deriv h (φ x) *
            ∑ i,
              ∑ j,
                inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x i j *
                    fderiv ℝ φ x (stdOrthonormalBasis ℝ E i) *
                  fderiv ℝ φ x (stdOrthonormalBasis ℝ E j) ∂(m.tilted (-φ)) := by
  have hg : ContDiff ℝ ∞ (fun x => h (φ x)) := by
    simpa only [Function.comp_def] using hh.comp hφ
  calc
    (∫ x, hessianInverseOperator φ V φ x * h (φ x) ∂(m.tilted (-φ))) =
        -∫ x,
            ∑ i,
              ∑ j,
                inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x i j *
                    fderiv ℝ φ x (stdOrthonormalBasis ℝ E i) *
                  fderiv ℝ (fun y => h (φ y)) x (stdOrthonormalBasis ℝ E j) ∂(m.tilted (-φ)) := by
      apply integral_hessianInverseOperator_mul_eq_neg <;>
        first
        | assumption
        | exact Or.inr hc
    _ = _ := by
      simp_rw [sum_inverseHessianEntry_mul_fderiv_comp (stdOrthonormalBasis ℝ E) hφ hh]

/--
**Weighted energy bound** (Letwin Lemma A.4, p. 17: `R⁻² ∫ w(W/R) Γ dν = ∫ q_R(W) LW dν ≤ ‖q_R‖_∞
‖LW‖_{L¹}`): under
the hypotheses of the energy identity, `|Lφ| ≤ D` and `|h| ≤ M`, the energy integrand `h′(φ) Γφ` is
integrable and
`−∫ h′(φ) Γφ dν ≤ D M`. No energy inequality or global integrability of `Γφ` is a premise.
-/
theorem integrable_and_neg_integral_deriv_comp_mul_le (m : Measure E) [m.IsAddHaarMeasure]
    {φ V : E → ℝ} {h : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hh : ContDiff ℝ ∞ h)
    (hc : HasCompactSupport (fun x => h (φ x))) {U : Set E} (hU : IsOpen U)
    (hV : ContDiffOn ℝ ∞ V U) (hRange : Set.range (gradient φ) ⊆ U)
    (hMA : ∀ y, logDetHessian φ (stdOrthonormalBasis ℝ E) y = -φ y + V (gradient φ y))
    (hPD : ∀ x v : E, v ≠ 0 → 0 < bilinearIteratedFDerivTwo ℝ φ x v v)
    (hnorm : ∫ x, Real.exp (-φ x) ∂m = 1) {D M : ℝ}
    (hD : ∀ x, |hessianInverseOperator φ V φ x| ≤ D) (hM : ∀ t, |h t| ≤ M) :
    Integrable
        (fun x =>
          deriv h (φ x) *
            ∑ i,
              ∑ j,
                inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x i j *
                    fderiv ℝ φ x (stdOrthonormalBasis ℝ E i) *
                  fderiv ℝ φ x (stdOrthonormalBasis ℝ E j))
        (m.tilted (-φ)) ∧
      -(∫ x,
            deriv h (φ x) *
              ∑ i,
                ∑ j,
                  inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x i j *
                      fderiv ℝ φ x (stdOrthonormalBasis ℝ E i) *
                    fderiv ℝ φ x (stdOrthonormalBasis ℝ E j) ∂(m.tilted (-φ))) ≤
        D * M := by
  let μ : Measure E := m.tilted (-φ)
  let b := stdOrthonormalBasis ℝ E
  let _ : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact isProbabilityMeasure_tilted_neg_of_integral_eq_one m φ hnorm
  have hcomp : ContDiff ℝ ∞ (fun x => h (φ x)) := by
    simpa only [Function.comp_def] using hh.comp hφ
  have hInv (i j : Fin (Module.finrank ℝ E)) :
    Continuous (fun x => inverseHessianEntry φ b x i j) := by
    exact
      (contDiff_iff_contDiffAt.mpr
          (fun x => contDiffAt_inverseHessianEntry b hφ x (hPD x) i j)).continuous
  have hφcoord (i : Fin (Module.finrank ℝ E)) : Continuous (fun x => (fderiv ℝ φ x) (b i)) := by
    exact
      (hφ.continuous_fderiv (by norm_num)).clm_apply
        (continuous_const : Continuous (fun _ : E => b i))
  have hcoord (j : Fin (Module.finrank ℝ E)) :
    Continuous (fun x => (fderiv ℝ (fun y => h (φ y)) x) (b j)) := by
    exact
      (hcomp.continuous_fderiv (by norm_num)).clm_apply
        (continuous_const : Continuous (fun _ : E => b j))
  have hchain (x : E) (v : E) :
    (fderiv ℝ (fun y => h (φ y)) x) v = deriv h (φ x) * (fderiv ℝ φ x) v := by
    have hd :=
      ((hh.differentiable (by simp)) (φ x)).hasDerivAt.comp_hasFDerivAt x
        ((hφ.differentiable (by simp)) x).hasFDerivAt
    have hv := congrArg (fun L : E →L[ℝ] ℝ => L v) hd.fderiv
    simpa only [Function.comp_def, smul_apply, smul_eq_mul] using hv
  have hterm (i j : Fin (Module.finrank ℝ E)) :
    Integrable
      (fun x =>
        deriv h (φ x) * inverseHessianEntry φ b x i j * (fderiv ℝ φ x) (b i) *
          (fderiv ℝ φ x) (b j))
      μ := by
    have ht :
      Continuous
        (fun x =>
          (inverseHessianEntry φ b x i j * (fderiv ℝ φ x) (b i)) *
            (fderiv ℝ (fun y => h (φ y)) x) (b j)) := by
      exact ((hInv i j).mul (hφcoord i)).mul (hcoord j)
    have hs :
      HasCompactSupport
        (fun x =>
          (inverseHessianEntry φ b x i j * (fderiv ℝ φ x) (b i)) *
            (fderiv ℝ (fun y => h (φ y)) x) (b j)) := by
      exact HasCompactSupport.mul_left (hc.fderiv_apply ℝ (b j))
    have hi := ht.integrable_of_hasCompactSupport (μ := μ) hs
    convert hi using 1
    funext x
    rw [hchain x (b j)]
    ring
  have hsumj (i : Fin (Module.finrank ℝ E)) :
    Integrable
      (fun x =>
        ∑ j,
          deriv h (φ x) * inverseHessianEntry φ b x i j * (fderiv ℝ φ x) (b i) *
            (fderiv ℝ φ x) (b j))
      μ := by
    apply integrable_finsetSum Finset.univ
    intro j hj
    exact hterm i j
  have henergy' :
    Integrable
      (fun x =>
        ∑ i,
          ∑ j,
            deriv h (φ x) * inverseHessianEntry φ b x i j * (fderiv ℝ φ x) (b i) *
              (fderiv ℝ φ x) (b j))
      μ := by
    apply integrable_finsetSum Finset.univ
    intro i hi
    exact hsumj i
  have henergy :
    Integrable
      (fun x =>
        deriv h (φ x) *
          ∑ i, ∑ j, inverseHessianEntry φ b x i j * (fderiv ℝ φ x) (b i) * (fderiv ℝ φ x) (b j))
      μ := by
    convert henergy' using 1
    funext x
    rw [← sum_inverseHessianEntry_mul_fderiv_comp b hφ hh x]
    simp_rw [hchain]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hV1 : ContDiffOn ℝ 1 V U := by exact hV.of_le (by simp)
  have hφ2 : ContDiff ℝ 2 φ := by exact hφ.of_le (WithTop.coe_le_coe.mpr le_top)
  have hLcont : Continuous (hessianInverseOperator φ V φ) := by
    exact continuous_hessianInverseOperator hφ hPD hU hV1 hRange hφ2
  have hAcont : Continuous (fun x => hessianInverseOperator φ V φ x * h (φ x)) := by
    exact hLcont.mul hcomp.continuous
  have hAint : Integrable (fun x => hessianInverseOperator φ V φ x * h (φ x)) μ := by
    apply hAcont.integrable_of_hasCompactSupport
    exact HasCompactSupport.mul_left hc
  have hD0 : 0 ≤ D := by
    exact le_trans (abs_nonneg (hessianInverseOperator φ V φ (0 : E))) (hD 0)
  have hM0 : 0 ≤ M := by exact le_trans (abs_nonneg (h 0)) (hM 0)
  have habs (x : E) : |hessianInverseOperator φ V φ x * h (φ x)| ≤ D * M := by
    rw [abs_mul]
    exact mul_le_mul (hD x) (hM (φ x)) (abs_nonneg (h (φ x))) hD0
  have hpoint (x : E) : hessianInverseOperator φ V φ x * h (φ x) ≤ D * M := by
    exact (abs_le.mp (habs x)).2
  have hconst : Integrable (fun _ : E => D * M) μ := by exact integrable_const _
  have hmono : (∫ x : E, hessianInverseOperator φ V φ x * h (φ x) ∂μ) ≤ ∫ x : E, D * M ∂μ := by
    apply integral_mono hAint hconst
    intro x
    exact hpoint x
  have hconstint : (∫ x : E, D * M ∂μ) = D * M := by
    rw [integral_const, probReal_univ]
    simp
  have hid :
    (∫ x : E, hessianInverseOperator φ V φ x * h (φ x) ∂μ) =
      -∫ x : E,
          deriv h (φ x) *
            ∑ i,
              ∑ j,
                inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x i j *
                    (fderiv ℝ φ x) (stdOrthonormalBasis ℝ E i) *
                  (fderiv ℝ φ x) (stdOrthonormalBasis ℝ E j) ∂μ := by
    simpa [μ] using
      (integral_hessianInverseOperator_self_mul_comp_eq_neg m hφ hh hc hU hV hRange hMA hPD
        hnorm)
  have hineq :
    -∫ x : E,
          deriv h (φ x) *
            ∑ i,
              ∑ j,
                inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x i j *
                    (fderiv ℝ φ x) (stdOrthonormalBasis ℝ E i) *
                  (fderiv ℝ φ x) (stdOrthonormalBasis ℝ E j) ∂μ ≤
      D * M := by
    calc
      -∫ x : E,
              deriv h (φ x) *
                ∑ i,
                  ∑ j,
                    inverseHessianEntry φ (stdOrthonormalBasis ℝ E) x i j *
                        (fderiv ℝ φ x) (stdOrthonormalBasis ℝ E i) *
                      (fderiv ℝ φ x) (stdOrthonormalBasis ℝ E j) ∂μ =
          ∫ x : E, hessianInverseOperator φ V φ x * h (φ x) ∂μ :=
        hid.symm
      _ ≤ ∫ x : E, D * M ∂μ := hmono
      _ = D * M := hconstint
  constructor
  · simpa [μ, b] using henergy
  · simpa [μ] using hineq

end FunctionalInequalities.Analysis.BakryEmery
