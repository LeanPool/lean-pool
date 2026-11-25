/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.DistributionTranslationSeminormRemainder

/-!
# Schwarz symmetry and seminorm control for translated distribution kernels

For a smooth scalar kernel, Schwarz symmetry moves the derivative in the
translation direction past any prescribed number of spatial derivatives.
Consequently every spatial derivative of the first translation remainder is
the ordinary first-order Taylor remainder of the corresponding spatial
derivative of the kernel.  Uniform Taylor control on a compact support then
gives the little-o estimates needed to differentiate the distribution pairing.
-/

@[expose] public section

noncomputable section

open Set TopologicalSpace Filter Asymptotics
open scoped ContDiff Distributions Topology

namespace SGPT.Foundations.Analysis.Pending

/-- For a `C∞` map, differentiating in a fixed direction commutes with every
iterated Fréchet derivative, after the cyclic permutation supplied by Schwarz
symmetry. -/
theorem iteratedFDeriv_fderiv_apply_cyclic
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x h : E) (r : ℕ) :
    iteratedFDeriv ℝ r (fun y ↦ fderiv ℝ f y h) x =
      fderiv ℝ (iteratedFDeriv ℝ r f) x h := by
  induction r generalizing x with
  | zero =>
      ext v
      rw [fderiv_iteratedFDeriv]
      simp
  | succ r ihr =>
      ext m
      have hDf : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) :=
        hf.fderiv_right (by simp)
      have hg : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ fderiv ℝ f y h) :=
        hDf.clm_apply contDiff_const
      have hDrg : DifferentiableAt ℝ
          (iteratedFDeriv ℝ r (fun y ↦ fderiv ℝ f y h)) x :=
        (hg.differentiable_iteratedFDeriv (by
          exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top r))).differentiableAt
      rw [hDrg.iteratedFDeriv_succ_apply_left']
      have heqLeft :
          (fun y ↦ iteratedFDeriv ℝ r (fun q ↦ fderiv ℝ f q h) y (Fin.tail m)) =
            (fun y ↦ fderiv ℝ (iteratedFDeriv ℝ r f) y h (Fin.tail m)) := by
        funext y
        rw [ihr y]
      rw [heqLeft]
      have hDrsucc : DifferentiableAt ℝ (iteratedFDeriv ℝ (r + 1) f) x :=
        (hf.differentiable_iteratedFDeriv (by
          exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top (r + 1)))).differentiableAt
      rw [← fderiv_continuousMultilinear_apply_const_apply hDrsucc m h]
      have heqRight :
          (fun y ↦ iteratedFDeriv ℝ (r + 1) f y m) =
            (fun y ↦ fderiv ℝ (iteratedFDeriv ℝ r f) y (m 0) (Fin.tail m)) := by
        funext y
        exact iteratedFDeriv_succ_apply_left (𝕜 := ℝ) (f := f) (x := y) m
      rw [heqRight]
      let G : E → (E [×r]→L[ℝ] F) := iteratedFDeriv ℝ r f
      have hG2 : ContDiff ℝ 2 G :=
        hf.iteratedFDeriv_right (by
          change ((↑(2 + r) : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
          exact WithTop.coe_le_coe.mpr le_top)
      have hDG1 : ContDiff ℝ 1 (fderiv ℝ G) :=
        hG2.fderiv_right (by norm_num)
      have hDGdiff : DifferentiableAt ℝ (fderiv ℝ G) x :=
        hDG1.differentiable one_ne_zero |>.differentiableAt
      have hDGappliedH : DifferentiableAt ℝ (fun y ↦ fderiv ℝ G y h) x :=
        hDGdiff.clm_apply (differentiableAt_const h)
      have hDGappliedM : DifferentiableAt ℝ (fun y ↦ fderiv ℝ G y (m 0)) x :=
        hDGdiff.clm_apply (differentiableAt_const (m 0))
      change
        fderiv ℝ (fun y ↦ fderiv ℝ G y h (Fin.tail m)) x (m 0) =
          fderiv ℝ (fun y ↦ fderiv ℝ G y (m 0) (Fin.tail m)) x h
      rw [fderiv_continuousMultilinear_apply_const_apply
        hDGappliedH (Fin.tail m) (m 0)]
      rw [fderiv_continuousMultilinear_apply_const_apply
        hDGappliedM (Fin.tail m) h]
      have hleft :
          fderiv ℝ (fun y ↦ fderiv ℝ G y h) x (m 0) =
            fderiv ℝ (fderiv ℝ G) x (m 0) h := by
        rw [fderiv_clm_apply hDGdiff (differentiableAt_const h)]
        simp
      have hright :
          fderiv ℝ (fun y ↦ fderiv ℝ G y (m 0)) x h =
            fderiv ℝ (fderiv ℝ G) x h (m 0) := by
        rw [fderiv_clm_apply hDGdiff (differentiableAt_const (m 0))]
        simp
      rw [hleft, hright]
      exact congrArg (fun L : E [×r]→L[ℝ] F ↦ L (Fin.tail m))
        ((hG2.contDiffAt.isSymmSndFDerivAt (by norm_num)) (m 0) h)

/-- Spatial differentiation of the first translation jet is the directional
derivative of the corresponding spatial derivative of the kernel. -/
theorem iteratedFDeriv_translationFirstJet
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (κ : E → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (z h y : E) (r : ℕ) :
    iteratedFDeriv ℝ r (fun x ↦ fderiv ℝ κ (x - z) (-h)) y =
      fderiv ℝ (iteratedFDeriv ℝ r κ) (y - z) (-h) := by
  rw [iteratedFDeriv_comp_sub
    (f := fun q ↦ fderiv ℝ κ q (-h)) r z y]
  exact iteratedFDeriv_fderiv_apply_cyclic κ hκ (y - z) (-h) r

/-- Every spatial derivative of the first translation remainder is exactly
the first-order Taylor remainder of the corresponding spatial derivative of
the kernel. -/
theorem iteratedFDeriv_translationFirstRemainder
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (κ : E → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (z h y : E) (r : ℕ) :
    iteratedFDeriv ℝ r (translationFirstRemainder κ z h) y =
      iteratedFDeriv ℝ r κ (y - (z + h)) -
        iteratedFDeriv ℝ r κ (y - z) -
        fderiv ℝ (iteratedFDeriv ℝ r κ) (y - z) (-h) := by
  change iteratedFDeriv ℝ r
      ((fun q ↦ κ (q - (z + h))) - (fun q ↦ κ (q - z)) -
        (fun q ↦ fderiv ℝ κ (q - z) (-h))) y = _
  have hκzh : ContDiff ℝ (⊤ : ℕ∞) (fun q ↦ κ (q - (z + h))) :=
    hκ.comp (contDiff_id.sub contDiff_const)
  have hκz : ContDiff ℝ (⊤ : ℕ∞) (fun q ↦ κ (q - z)) :=
    hκ.comp (contDiff_id.sub contDiff_const)
  have hjet : ContDiff ℝ (⊤ : ℕ∞)
      (fun q ↦ fderiv ℝ κ (q - z) (-h)) :=
    ((hκ.fderiv_right (by simp)).comp
      (contDiff_id.sub contDiff_const)).clm_apply contDiff_const
  have hrle : ((r : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) :=
    WithTop.coe_le_coe.mpr le_top
  rw [iteratedFDeriv_sub
      (f := (fun q ↦ κ (q - (z + h))) - (fun q ↦ κ (q - z)))
      (g := fun q ↦ fderiv ℝ κ (q - z) (-h))
      ((hκzh.sub hκz).of_le hrle) (hjet.of_le hrle),
    iteratedFDeriv_sub
      (f := fun q ↦ κ (q - (z + h))) (g := fun q ↦ κ (q - z))
      (hκzh.of_le hrle) (hκz.of_le hrle)]
  simp only [Pi.sub_apply]
  rw [
    iteratedFDeriv_comp_sub (f := κ) r (z + h) y,
    iteratedFDeriv_comp_sub (f := κ) r z y,
    iteratedFDeriv_translationFirstJet κ hκ z h y r]

/-- A nonnegative upper bound for the norm of a continuous map on a compact
set.  The outer maximum also gives the intended value when the compact set is
empty. -/
noncomputable def compactNormSup
    {E F : Type*} [TopologicalSpace E] [SeminormedAddCommGroup F]
    (K : Compacts E) (f : E → F) : ℝ :=
  max 0 (⨆ y : (K : Set E), ‖f y‖)

theorem compactNormSup_nonneg
    {E F : Type*} [TopologicalSpace E] [SeminormedAddCommGroup F]
    (K : Compacts E) (f : E → F) :
    0 ≤ compactNormSup K f :=
  le_max_left _ _

/-- Every point of the compact set is bounded by `compactNormSup`. -/
theorem norm_le_compactNormSup
    {E F : Type*} [TopologicalSpace E] [SeminormedAddCommGroup F]
    (K : Compacts E) (f : E → F) (hf : Continuous f)
    {y : E} (hy : y ∈ (K : Set E)) :
    ‖f y‖ ≤ compactNormSup K f := by
  have hbddImage : BddAbove ((fun q : E ↦ ‖f q‖) '' (K : Set E)) :=
    K.isCompact.bddAbove_image hf.norm.continuousOn
  have hbddRange : BddAbove
      (range (fun q : (K : Set E) ↦ ‖f q‖)) := by
    obtain ⟨C, hC⟩ := hbddImage
    refine ⟨C, ?_⟩
    rintro _ ⟨q, rfl⟩
    exact hC ⟨q, q.property, rfl⟩
  exact (le_ciSup hbddRange ⟨y, hy⟩).trans (le_max_right _ _)

/-- The uniform size on `K` of the `r`-th spatial derivative of the first
translation remainder. -/
noncomputable def translationDerivativeRemainderSup
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (κ : E → ℝ) (K : Compacts E) (z : E) (r : ℕ) (h : E) : ℝ :=
  compactNormSup K
    (fun y ↦ iteratedFDeriv ℝ r (translationFirstRemainder κ z h) y)

theorem translationDerivativeRemainderSup_nonneg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (κ : E → ℝ) (K : Compacts E) (z : E) (r : ℕ) (h : E) :
    0 ≤ translationDerivativeRemainderSup κ K z r h :=
  compactNormSup_nonneg K _

/-- The raw uniform remainder bound for every fixed spatial derivative order
is little-o of the translation increment. -/
theorem translationDerivativeRemainderSup_isLittleO
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (κ : E → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (K : Compacts E) (z : E) (r : ℕ) :
    (translationDerivativeRemainderSup κ K z r) =o[𝓝 0]
      (fun h : E ↦ h) := by
  rw [isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hbound⟩ :=
    exists_uniform_iteratedFDeriv_translation_remainder_bound
      κ hκ K z r c hc
  filter_upwards [Metric.ball_mem_nhds (0 : E) hδ] with h hh
  have hhδ : ‖h‖ < δ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hh
  have hsup :
      (⨆ y : (K : Set E),
        ‖iteratedFDeriv ℝ r (translationFirstRemainder κ z h) y‖) ≤
          c * ‖h‖ := by
    by_cases hK : (K : Set E).Nonempty
    · let _ : Nonempty (K : Set E) := Set.nonempty_coe_sort.mpr hK
      apply ciSup_le
      intro y
      rw [iteratedFDeriv_translationFirstRemainder κ hκ z h y r]
      exact hbound y y.property h hhδ
    · let _ : IsEmpty (K : Set E) :=
        ⟨fun y ↦ hK ⟨y, y.property⟩⟩
      simpa using mul_nonneg hc.le (norm_nonneg h)
  have hnon : 0 ≤ c * ‖h‖ := mul_nonneg hc.le (norm_nonneg h)
  have hle : translationDerivativeRemainderSup κ K z r h ≤ c * ‖h‖ := by
    exact max_le hnon hsup
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (translationDerivativeRemainderSup_nonneg κ K z r h)] using hle

/-- A canonical uniform compact bound for a spatial derivative of the fixed
cutoff. -/
noncomputable def cutoffDerivativeSup
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (K : Compacts E) (r : ℕ) : ℝ :=
  compactNormSup K (fun y ↦ iteratedFDeriv ℝ r (χ : E → ℝ) y)

/-- The cutoff translation remainder is little-o in every individual
fixed-support seminorm, with all derivative bounds constructed internally. -/
theorem cutoffTranslationFirstRemainder_seminorm_isLittleO_actual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (z : E) (r : ℕ) :
    (fun h : E ↦
      ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K r
        (cutoffTranslationFirstRemainderSupportedIn χ κ hκ K hχK z h))
      =o[𝓝 0] (fun h : E ↦ h) := by
  apply cutoffTranslationFirstRemainder_seminorm_isLittleO
    χ κ hκ K hχK z r
    (cutoffDerivativeSup χ K)
    (translationDerivativeRemainderSup κ K z)
  · intro i _hi
    exact compactNormSup_nonneg K _
  · intro i _hi y hy
    have hiTop : ((i : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) :=
      WithTop.coe_le_coe.mpr le_top
    exact norm_le_compactNormSup K _
      ((χ.contDiff.of_le hiTop).continuous_iteratedFDeriv') hy
  · intro j _hj h
    exact translationDerivativeRemainderSup_nonneg κ K z j h
  · intro j _hj h y hy
    have hjTop : ((j : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω) :=
      WithTop.coe_le_coe.mpr le_top
    have hcontinuous : Continuous
        (iteratedFDeriv ℝ j (translationFirstRemainder κ z h)) :=
      ((translationFirstRemainder_contDiff κ hκ z h).of_le hjTop)
        |>.continuous_iteratedFDeriv'
    exact norm_le_compactNormSup K _ hcontinuous hy
  · intro j _hj
    exact translationDerivativeRemainderSup_isLittleO κ hκ K z j

/-- The supremum of all fixed-support seminorms through any prescribed finite
order is little-o of the translation increment. -/
theorem cutoffTranslationFirstRemainder_finiteOrderSeminorm_isLittleO_actual
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Ω : Opens E} (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (z : E) (m : ℕ) :
    (fun h : E ↦
      ((Finset.Iic m).sup
        (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K))
        (cutoffTranslationFirstRemainderSupportedIn χ κ hκ K hχK z h))
      =o[𝓝 0] (fun h : E ↦ h) := by
  let R : E → ContDiffMapSupportedIn E ℝ ⊤ K :=
    fun h ↦ cutoffTranslationFirstRemainderSupportedIn
      χ κ hκ K hχK z h
  let S : E → ℝ := fun h ↦ ∑ i ∈ Finset.Iic m,
    ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K i (R h)
  have hterms : ∀ i ∈ Finset.Iic m,
      (fun h : E ↦ ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K i (R h))
        =o[𝓝 0] (fun h : E ↦ h) := by
    intro i _hi
    exact cutoffTranslationFirstRemainder_seminorm_isLittleO_actual
      χ κ hκ K hχK z i
  have hSo : S =o[𝓝 0] (fun h : E ↦ h) := by
    dsimp only [S]
    refine (IsLittleO.sum hterms).congr ?_ (fun _ ↦ rfl)
    intro h
    simp
  have hdom :
      (fun h : E ↦
        ((Finset.Iic m).sup
          (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)) (R h))
        =O[𝓝 0] S := by
    apply (IsBigOWith.of_bound (c := (1 : ℝ)) ?_).isBigO
    filter_upwards with h
    have hle :
        ((Finset.Iic m).sup
          (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)) (R h) ≤ S h := by
      simpa [S] using (Seminorm.finset_sup_le_sum
        (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)
        (Finset.Iic m)) (R h)
    have hS0 : 0 ≤ S h := by
      dsimp only [S]
      positivity
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (apply_nonneg
        ((Finset.Iic m).sup
          (ContDiffMapSupportedIn.seminorm ℝ E ℝ ⊤ K)) (R h)),
      abs_of_nonneg hS0, one_mul] using hle
  exact hdom.trans_isLittleO hSo

/-- Pairing a distribution with a smooth cutoff-translated kernel is
Fréchet differentiable in the translation parameter, with derivative given
by the first translation jet. -/
theorem distributionPairing_hasFDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Ω : Opens E} (T : 𝓓'(Ω, ℝ)) (χ : 𝓓(Ω, ℝ)) (κ : E → ℝ)
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (K : Compacts E)
    (hχK : tsupport χ ⊆ K) (hKΩ : (K : Set E) ⊆ Ω) (z : E) :
    HasFDerivAt
      (fun w ↦ distributionOnSupportedInCLM T K hKΩ
        (cutoffTranslatedKernelSupportedIn χ κ hκ K hχK w))
      ⟨(distributionOnSupportedInCLM T K hKΩ).toLinearMap.comp
          (cutoffTranslatedKernelFirstJetLM χ κ hκ K hχK z),
        ((distributionOnSupportedInCLM T K hKΩ).toLinearMap.comp
          (cutoffTranslatedKernelFirstJetLM χ κ hκ K hχK z)).continuous_of_finiteDimensional⟩
            z := by
  apply distributionPairing_hasFDerivAt_of_supSeminorm_remainder
    T χ κ hκ K hχK hKΩ z
  intro m
  simpa only [cutoffTranslationFirstRemainderSupportedIn] using
    cutoffTranslationFirstRemainder_finiteOrderSeminorm_isLittleO_actual
      χ κ hκ K hχK z m

end SGPT.Foundations.Analysis.Pending
