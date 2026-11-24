/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MaximalPshPeanoObstacle
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorCollarSymmetry

/-!
# Radial mollifications of a semiconcave plurisubharmonic function

On a relatively compact subdomain `A ⋐ Ω` we build the explicit radial mollifications
`F j = u ∗ ρ_j` of a locally bounded plurisubharmonic function `u`, together with all the data
needed for the `C^{1,1}` estimates:

* `F j` is globally smooth, the family is a decreasing approximation of `u` on `A`, and each
  `F j` has nonnegative Levi form there;
* `F j` inherits the second-difference bound `u(z+h) + u(z-h) - 2u(z) ≤ K‖h‖²` of `u`;
* the smooth pointwise estimate below gives `‖D²(F j)‖ ≤ 2K` on `A`.

The estimate is a variant of the Hessian argument in the proof of
[Błocki's Proposition 2.3.3](https://gamma.im.uj.edu.pl/~blocki/publ/ln/wykl.pdf#page=51).
The proposition derives `C^{1,1}` regularity and a Hessian bound of `K` for the original
plurisubharmonic function. Here the functions are already `C²` and the bound is `2K`.
-/

@[expose] public section

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ContDiff

namespace SGPT.Foundations.Analysis.Pending.SemiconcaveHessian

open FirstPass FirstPass.MongeAmpere SGPT.Foundations.Analysis.Pending.HolomorphicPullback

variable {n : ℕ}

/-- The explicit radial mollifications of a locally bounded plurisubharmonic function on a
relatively compact subdomain, with a kernel radius as small as desired. -/
theorem exists_mollifier_family {Ω A : Opens (ComplexModel n)} (hA : RelativelyCompactIn A Ω)
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    ∃ (R : ℝ) (hR : 0 < R) (g : ComplexModel n → ℝ), R ≤ δ₀ ∧
      LocallyIntegrable g volume ∧
      (∀ z ∈ A, closedBall z (2 * R) ⊆ (Ω : Set (ComplexModel n))) ∧
      (∀ z ∈ A, ∀ x ∈ closedBall z (2 * R), g x = u x) ∧
      BedfordTaylor.IsDecApprox A u (fun j ↦ translationPairing volume g (explicitRadialKernel R
        hR j)) ∧
      (∀ j, ContDiff ℝ 2 (translationPairing volume g (explicitRadialKernel R hR j))) ∧
      (∀ j, ∀ z ∈ A, ∀ v,
        0 ≤ leviForm (translationPairing volume g (explicitRadialKernel R hR j)) z v) := by
  classical
  let _ : ProperSpace (ComplexModel n) := FiniteDimensional.proper ℝ _
  obtain ⟨R₀, hR₀, N, Kc, hN, hclAN, hNK, hKc, hKcΩ, hball₀⟩ :=
    exists_open_compact_closedBall_neighborhood hA.1 Ω.isOpen hA.2
  set R := min (R₀ / 2) δ₀ with hRdef
  have hR : 0 < R := lt_min (by linarith) hδ₀
  have hRδ : R ≤ δ₀ := min_le_right _ _
  have hR2 : 2 * R ≤ R₀ := by
    have : R ≤ R₀ / 2 := min_le_left _ _
    linarith
  have hball : ∀ x ∈ N, closedBall x R ⊆ Kc := fun x hx ↦
    (closedBall_subset_closedBall (by linarith [min_le_left (R₀ / 2) δ₀])).trans (hball₀ x hx)
  have hball2 : ∀ x ∈ N, closedBall x (2 * R) ⊆ Kc := fun x hx ↦
    (closedBall_subset_closedBall hR2).trans (hball₀ x hx)
  have hAN : (A : Set (ComplexModel n)) ⊆ N := subset_closure.trans hclAN
  have hAΩ : (A : Set (ComplexModel n)) ⊆ Ω := subset_closure.trans hA.2
  have hpL : LocallyIntegrableOn u Ω volume :=
    locallyIntegrableOn_of_plurisubharmonicOn_real hu.1
  have hpLevi : HasNonnegativeDistributionalLevi (regularDistribution volume u hpL) :=
    hasNonnegativeDistributionalLevi_of_plurisubharmonicOn_real hu.1
  obtain ⟨S, hSk⟩ :=
    exists_explicitRadialConvolutionSystem_of_locallyBoundedPsh hu hR hN
      hKc hKcΩ hball
  have hker : ∀ j, S.kernel j = explicitRadialKernel R hR j := fun j ↦ funext (hSk j)
  set g : ComplexModel n → ℝ := Kc.indicator u with hgdef
  set f : ℕ → ComplexModel n → ℝ := fun j ↦ translationPairing volume g (S.kernel j) with hfdef
  have hg : LocallyIntegrable g volume :=
    (integrable_indicator_of_locallyIntegrableOn_isCompact hpL hKc hKcΩ).locallyIntegrable
  have hfDisc : ∀ j, DiscPshOn (fun x ↦ (f j x : EReal)) N := fun j ↦
    discPshOn_translationPairing_indicator hpL hpLevi
      (S.kernel_hasCompactSupport j) (S.kernel_contDiff j)
      (S.kernel_nonneg j) hKc hKcΩ (S.translated_tsupport j)
  have hfPsh : ∀ j, PlurisubharmonicOn (fun x ↦ (f j x : EReal)) A := fun j ↦
    ((hfDisc j).plurisubharmonicOn hN).mono hAN
  have hfContDiff : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j) := fun j ↦
    contDiff_translationPairing hg (S.kernel_hasCompactSupport j) (S.kernel_contDiff j)
  have hfSmooth : ∀ j, IsSmoothPshOn A (f j) := fun j ↦
    isSmoothPshOn_of_psh (hfContDiff j).contDiffOn (hfPsh j)
  have hanti : ∀ x ∈ A, Antitone fun j ↦ f j x := fun x hx ↦ S.antitone_pairing x (hAN hx)
  have hae : ∀ᵐ x ∂volume.restrict (A : Set (ComplexModel n)),
      Tendsto (fun j ↦ f j x) atTop (𝓝 (u x)) := by
    have haeN := S.ae_tendsto_pairing
    change ∀ᵐ x ∂volume.restrict N, Tendsto (fun j ↦ f j x) atTop (𝓝 (u x)) at haeN
    exact ae_mono (Measure.restrict_mono hAN le_rfl) haeN
  have hpoint : ∀ x ∈ A, Tendsto (fun j ↦ f j x) atTop (𝓝 (u x)) :=
    tendsto_everywhere_of_ae_of_antitone_psh (hu.1.mono hAΩ) hfPsh hanti hae
  have hdec : IsDecreasingApproximation A u f := ⟨hfSmooth, hanti, hpoint⟩
  have hdecApprox : BedfordTaylor.IsDecApprox A u f :=
    BedfordTaylor.isDecApprox_of_isDecreasingApproximation hu hAΩ hdec
  have hfun : ∀ j, f j = translationPairing volume g (explicitRadialKernel R hR j) := by
    intro j
    change translationPairing volume g (S.kernel j) = _
    rw [hker j]
  have hlevi : ∀ j, ∀ z ∈ A, ∀ v, 0 ≤ leviForm (f j) z v := fun j z hz v ↦
    leviForm_nonneg_of_contDiffOn_plurisubharmonicOn (hfContDiff j).contDiffOn (hfPsh j) hz v
  refine ⟨R, hR, g, hRδ, hg, fun z hz ↦ (hball2 z (hAN hz)).trans hKcΩ, fun z hz x hx ↦ ?_,
    ?_, ?_, ?_⟩
  · exact indicator_of_mem (hball2 z (hAN hz) hx) u
  · have hfe : (fun j ↦ translationPairing volume g (explicitRadialKernel R hR j)) = f :=
      funext fun j ↦ (hfun j).symm
    rw [hfe]
    exact hdecApprox
  · intro j
    rw [← hfun j]
    exact (hfContDiff j).of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  · intro j z hz v
    rw [← hfun j]
    exact hlevi j z hz v

/-- The second derivative of a `C²` function is symmetric. -/
theorem fderiv_fderiv_symm {F : ComplexModel n → ℝ} (hF : ContDiff ℝ 2 F) (z v w : ComplexModel n)
    :
    fderiv ℝ (fderiv ℝ F) z v w = fderiv ℝ (fderiv ℝ F) z w v := by
  have hd1 : ∀ y : ComplexModel n, HasFDerivAt F (fderiv ℝ F y) y := fun y ↦
    (hF.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have hcd : ContDiff ℝ 1 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hd2 : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) z) z :=
    ((hcd.differentiable (by norm_num)).differentiableAt).hasFDerivAt
  exact second_derivative_symmetric_of_eventually (Eventually.of_forall hd1) hd2 v w

/-- A smooth pointwise variant of the Hessian estimate in the proof of Błocki's
Proposition 2.3.3. For a `C²` function, a one-sided second-difference bound and a
nonnegative Levi form at the point give a bound of `2K` on the second derivative. -/
theorem norm_fderiv_fderiv_le_of_secondDifference {F : ComplexModel n → ℝ} (hF : ContDiff ℝ 2 F)
    {z : ComplexModel n} {K : ℝ} (hK0 : 0 ≤ K)
    (hsd : ∀ᶠ h in 𝓝 (0 : ComplexModel n), F (z + h) + F (z - h) - 2 * F z ≤ K * ‖h‖ ^ 2)
    (hlevi : ∀ v, 0 ≤ leviForm F z v) : ‖fderiv ℝ (fderiv ℝ F) z‖ ≤ 2 * K := by
  refine norm_le_of_abs_apply_self_le (fderiv_fderiv_symm hF z) hK0 fun v ↦ ?_
  have := abs_realHessian_le_of_secondDifference_le hF hsd hlevi v
  rwa [realHessian_eq_fderiv] at this

/-- The mollifications inherit a uniform one-sided second-difference bound. -/
theorem secondDifference_translationPairing {R : ℝ} (hR : 0 < R) {g u : ComplexModel n → ℝ}
    (hg : LocallyIntegrable g volume) {z : ComplexModel n} {K : ℝ}
    (hgu : ∀ x ∈ closedBall z (2 * R), g x = u x)
    (hsd : ∀ y ∈ closedBall z R, ∀ h : ComplexModel n, ‖h‖ ≤ R →
      u (y + h) + u (y - h) - 2 * u y ≤ K * ‖h‖ ^ 2)
    (j : ℕ) {h : ComplexModel n} (hh : ‖h‖ ≤ R) :
    translationPairing volume g (explicitRadialKernel R hR j) (z + h)
        + translationPairing volume g (explicitRadialKernel R hR j) (z - h)
        - 2 * translationPairing volume g (explicitRadialKernel R hR j) z ≤ K * ‖h‖ ^ 2 := by
  classical
  set κ : ComplexModel n → ℝ := explicitRadialKernel R hR j with hκdef
  have hκs : HasCompactSupport κ := explicitRadialKernel_hasCompactSupport R hR j
  have hκc : Continuous κ := (explicitRadialKernel_contDiff R hR j).continuous
  have hκnn : ∀ x, 0 ≤ κ x := explicitRadialKernel_nonneg R hR j
  have hκ1 : ∫ y, κ y = 1 := explicitRadialKernel_integral_one R hR j
  have hκsupp : ∀ x : ComplexModel n, R < ‖x‖ → κ x = 0 := by
    intro x hx
    have hxt : x ∉ tsupport κ := by
      rw [hκdef, explicitRadialKernel_tsupport R hR j]
      simp only [mem_closedBall, dist_zero_right, not_le]
      refine lt_of_le_of_lt ?_ hx
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hR.le, Nat.cast_nonneg (α := ℝ) j]
    exact image_eq_zero_of_notMem_tsupport hxt
  -- integrability of the three translated integrands
  have hint : ∀ w : ComplexModel n, Integrable (fun x ↦ g x * κ (x - w)) volume := fun w ↦
    integrable_translationPairing hg hκs hκc w
  have hshift : ∀ w : ComplexModel n,
      translationPairing volume g κ (z + w) = ∫ y, g (y + w) * κ (y - z) := by
    intro w
    rw [translationPairing, ← integral_add_right_eq_self
      (fun x : ComplexModel n ↦ g x * κ (x - (z + w))) w]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    abel_nf
  have hshift0 : translationPairing volume g κ z = ∫ y, g y * κ (y - z) := rfl
  have hintshift : ∀ w : ComplexModel n, Integrable (fun y ↦ g (y + w) * κ (y - z)) volume := by
    intro w
    have h := (hint (z + w)).comp_add_right w
    refine h.congr (Eventually.of_forall fun y ↦ ?_)
    abel_nf
  have hzm : z - h = z + (-h) := by abel
  have hintm : Integrable (fun y ↦ g (y - h) * κ (y - z)) volume := by
    refine (hintshift (-h)).congr (Eventually.of_forall fun y ↦ ?_)
    simp only [← sub_eq_add_neg]
  have hshiftm : translationPairing volume g κ (z - h) = ∫ y, g (y - h) * κ (y - z) := by
    rw [hzm, hshift (-h)]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    simp only [← sub_eq_add_neg]
  have hsum : translationPairing volume g κ (z + h) + translationPairing volume g κ (z - h)
      - 2 * translationPairing volume g κ z
      = ∫ y, (g (y + h) + g (y - h) - 2 * g y) * κ (y - z) := by
    have e : ∀ y : ComplexModel n, (g (y + h) + g (y - h) - 2 * g y) * κ (y - z)
        = (g (y + h) * κ (y - z) + g (y - h) * κ (y - z)) - 2 * (g y * κ (y - z)) :=
      fun y ↦ by ring
    calc translationPairing volume g κ (z + h) + translationPairing volume g κ (z - h)
          - 2 * translationPairing volume g κ z
        = (∫ y, g (y + h) * κ (y - z)) + (∫ y, g (y - h) * κ (y - z))
            - 2 * ∫ y, g y * κ (y - z) := by rw [hshift h, hshiftm, hshift0]
      _ = (∫ y, (g (y + h) * κ (y - z) + g (y - h) * κ (y - z)))
            - ∫ y, 2 * (g y * κ (y - z)) := by
          rw [integral_add (hintshift h) hintm, integral_const_mul]
      _ = ∫ y, ((g (y + h) * κ (y - z) + g (y - h) * κ (y - z)) - 2 * (g y * κ (y - z))) :=
          (integral_sub ((hintshift h).add hintm) (Integrable.const_mul (hint z) 2)).symm
      _ = ∫ y, (g (y + h) + g (y - h) - 2 * g y) * κ (y - z) :=
          integral_congr_ae (Eventually.of_forall fun y ↦ (e y).symm)
  have hpt : ∀ y : ComplexModel n,
      (g (y + h) + g (y - h) - 2 * g y) * κ (y - z) ≤ (K * ‖h‖ ^ 2) * κ (y - z) := by
    intro y
    by_cases hy : ‖y - z‖ ≤ R
    · have hyR : y ∈ closedBall z R := by
        simpa [mem_closedBall, dist_eq_norm] using hy
      have hy2 : ∀ w : ComplexModel n, ‖w‖ ≤ R → y + w ∈ closedBall z (2 * R) := by
        intro w hw
        simp only [mem_closedBall, dist_eq_norm]
        calc ‖y + w - z‖ = ‖(y - z) + w‖ := by congr 1; abel
          _ ≤ ‖y - z‖ + ‖w‖ := norm_add_le _ _
          _ ≤ R + R := by linarith
          _ = 2 * R := by ring
      have hgy : g y = u y := by
        refine hgu y ?_
        simp only [mem_closedBall, dist_eq_norm]
        linarith [hy, hR.le]
      have hgyh : g (y + h) = u (y + h) := hgu _ (hy2 h hh)
      have hgymh : g (y - h) = u (y - h) := by
        have : y - h = y + (-h) := by abel
        rw [this]
        exact hgu _ (hy2 (-h) (by simpa using hh))
      rw [hgy, hgyh, hgymh]
      exact mul_le_mul_of_nonneg_right (hsd y hyR h hh) (hκnn _)
    · rw [hκsupp (y - z) (by linarith [not_le.mp hy])]
      simp
  have hintR : Integrable (fun y : ComplexModel n ↦ (K * ‖h‖ ^ 2) * κ (y - z)) volume := by
    have h0 : Integrable κ (volume : Measure (ComplexModel n)) :=
      hκc.integrable_of_hasCompactSupport hκs
    have h1 : Integrable (fun y : ComplexModel n ↦ κ (y - z)) volume := h0.comp_sub_right z
    exact h1.const_mul _
  have hintL : Integrable (fun y : ComplexModel n ↦ (g (y + h) + g (y - h) - 2 * g y) * κ (y - z))
      volume := by
    refine Integrable.congr
      (((hintshift h).add hintm).sub (Integrable.const_mul (hint z) 2)) ?_
    refine Eventually.of_forall fun y ↦ ?_
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hmono := integral_mono hintL hintR hpt
  rw [hsum]
  refine le_trans hmono ?_
  have hkint : (∫ y : ComplexModel n, κ (y - z)) = 1 := by
    rw [← hκ1]
    exact integral_sub_right_eq_self κ z
  rw [integral_const_mul, hkint, mul_one]

end SGPT.Foundations.Analysis.Pending.SemiconcaveHessian
