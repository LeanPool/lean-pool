/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorSlotStokes

/-!
# Symmetric integration by parts for compactly supported differences

Let `R` be a Bedford–Taylor tuple of locally bounded plurisubharmonic functions in
the slots other than `i₀`, let `g` be smooth with positive semidefinite complex
Hessian, and let `u₀, u₁` be locally bounded plurisubharmonic functions equal to
`g` off a compact subset `K` of the domain. Writing `μ(w)` for the Bedford–Taylor
limit of the tuple with `w` in slot `i₀`, we prove

  `∫ (u₀ - g) dμ(u₁) - ∫ (u₀ - g) dμ(g) = ∫ (u₁ - g) dμ(u₀) - ∫ (u₁ - g) dμ(g)`,

that is `∫ a ddᶜb ∧ R = ∫ b ddᶜa ∧ R` for the compactly supported differences
`a = u₀ - g`, `b = u₁ - g` (Błocki, *The complex Monge–Ampère operator in
pluripotential theory*, Prop. 2.1.3).

Proof. All three functions are regularized by one radial mollifier. The
regularizations decrease to `u₀`, `u₁`, `g`, and, the kernel having support in a
ball of radius `δ`, the regularized differences vanish outside the closed
`δ`-thickening of `K`. For smooth slots the identity is linearity of the mixed
density in one slot followed by the smooth integration by parts
`integral_mul_mixedDensity_update_swap`. Each side is a sum of four weighted
integrals of decreasing smooth weights against mixed densities of decreasing
smooth families, which converge to the Bedford–Taylor weighted integrals by the
weighted convergence theorem `wClaim_of_pClaim pClaim_all`, with a cutoff equal
to one on the thickening.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff ComplexOrder Distributions

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

variable {n : ℕ}

/-- A smooth function with positive semidefinite complex Hessian on an open set
is plurisubharmonic there: the Levi form is the quadratic form of the Hessian. -/
theorem IsSmoothPsdOn.plurisubharmonicOn {U : Opens (ComplexModel n)}
    {f : ComplexModel n → ℝ} (hf : IsSmoothPsdOn U f) :
    PlurisubharmonicOn (fun z ↦ (f z : EReal)) U := by
  have hlevi : ∀ y ∈ (U : Set (ComplexModel n)), ∀ v : ComplexModel n,
      0 ≤ leviForm f y v := by
    intro y hy v
    have hf2 : ContDiffAt ℝ 2 f y := ((hf.1 y hy).contDiffAt (U.isOpen.mem_nhds hy)).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    set x : Fin n → ℂ := fun j ↦ star (v j) with hx
    have h := complexHessian_dotProduct_mulVec_eq_leviForm hf2 x
    have hv : (∑ j, ((x j).re • coordinateVector j -
        (x j).im • (Complex.I • coordinateVector j)) : ComplexModel n) = v := by
      ext i
      simp only [hx, coordinateVector, WithLp.ofLp_sub, WithLp.ofLp_sum, WithLp.ofLp_smul,
        Finset.sum_apply, Pi.sub_apply, Pi.smul_apply]
      rw [Finset.sum_eq_single i (fun b _ hb ↦ by simp [Ne.symm hb])
        (by simp)]
      simp [Complex.re_add_im]
    have h' : star x ⬝ᵥ ((complexHessian f y).mulVec x) =
        ((leviForm f y (∑ j, ((x j).re • coordinateVector j -
          (x j).im • (Complex.I • coordinateVector j))) : ℝ) : ℂ) := h
    rw [hv] at h'
    have hpos := (hf.2 y hy).dotProduct_mulVec_nonneg x
    rw [h'] at hpos
    exact_mod_cast hpos
  intro y hy
  obtain ⟨g, hg, heq⟩ := exists_contDiff_eventuallyEq_of_contDiffOn U.isOpen hf.1 hy
  have hmem : {x | f x = g x} ∩ U ∈ 𝓝 y := inter_mem heq (U.isOpen.mem_nhds hy)
  obtain ⟨W, hWsub, hW, hyW⟩ := _root_.mem_nhds_iff.mp hmem
  have hWU : W ⊆ U := fun x hx ↦ (hWsub hx).2
  have heqW : EqOn f g W := fun x hx ↦ (hWsub hx).1
  have hgLevi : ∀ x ∈ W, ∀ v : ComplexModel n, 0 ≤ leviForm g x v := by
    intro x hx v
    have hlocal : f =ᶠ[𝓝 x] g := by
      filter_upwards [hW.mem_nhds hx] with t ht
      exact heqW ht
    have hsecond : fderiv ℝ (fderiv ℝ f) x = fderiv ℝ (fderiv ℝ g) x :=
      hlocal.fderiv.fderiv_eq
    have hl : leviForm f x v = leviForm g x v := by
      simp only [leviForm, realHessian_eq_fderiv, hsecond]
    rw [← hl]
    exact hlevi x (hWU hx) v
  have hgPsh : PlurisubharmonicOn (fun x ↦ (g x : EReal)) W :=
    plurisubharmonicOn_of_levi_nonneg
      (hg.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hW hgLevi
  apply (hgPsh y hyW).congr
  filter_upwards [hW.mem_nhds hyW] with x hx
  exact congrArg (fun t : ℝ ↦ (t : EReal)) (heqW hx).symm

theorem IsSmoothPsdOn.isLocallyBoundedPshOn {Ω : Opens (ComplexModel n)}
    {g : ComplexModel n → ℝ} (hg : IsSmoothPsdOn Ω g) : IsLocallyBoundedPshOn Ω g := by
  refine ⟨hg.plurisubharmonicOn, fun z hz ↦ ?_⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp Ω.isOpen z hz
  have hcb : closedBall z (r / 2) ⊆ (Ω : Set (ComplexModel n)) :=
    (closedBall_subset_ball (by linarith)).trans hball
  obtain ⟨D, hD⟩ := (isCompact_closedBall z (r / 2)).exists_bound_of_continuousOn
    (hg.1.continuousOn.mono hcb)
  refine ⟨⟨ball z (r / 2), isOpen_ball⟩, mem_ball_self (by linarith),
    fun w hw ↦ hcb (ball_subset_closedBall hw), D, fun w hw ↦ ?_⟩
  simpa [Real.norm_eq_abs] using hD w (ball_subset_closedBall hw)

/-- **A common mollifier.** On a relatively compact subdomain, one radial
mollifier with kernel support of radius at most `δ` regularizes every locally
bounded plurisubharmonic function to a decreasing smooth approximation, by
globally smooth functions whose value at `z` only depends on the function on
the closed ball of radius `δ` about `z`. -/
theorem exists_common_mollifier {Ω A : Opens (ComplexModel n)} (hA : RelativelyCompactIn A Ω)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℕ → (ComplexModel n → ℝ) → ComplexModel n → ℝ,
      (∀ p, IsLocallyBoundedPshOn Ω p → IsDecApprox A p fun j ↦ M j p) ∧
      (∀ p, IsLocallyBoundedPshOn Ω p → ∀ j, ContDiff ℝ ∞ (M j p)) ∧
      ∀ j p q z, (∀ x ∈ closedBall z δ, p x = q x) → M j p z = M j q z := by
  let _ : ProperSpace (ComplexModel n) := FiniteDimensional.proper ℝ _
  obtain ⟨R₀, hR₀, N, Kc, hN, hclAN, hNK, hKc, hKcΩ, hball₀⟩ :=
    exists_open_compact_closedBall_neighborhood hA.1 Ω.isOpen hA.2
  have hR : 0 < min R₀ δ := lt_min hR₀ hδ
  have hball : ∀ x ∈ N, closedBall x (min R₀ δ) ⊆ Kc := fun x hx ↦
    (closedBall_subset_closedBall (min_le_left _ _)).trans (hball₀ x hx)
  have hAN : (A : Set (ComplexModel n)) ⊆ N := subset_closure.trans hclAN
  have hAΩ : (A : Set (ComplexModel n)) ⊆ Ω := subset_closure.trans hA.2
  refine ⟨fun j p ↦ translationPairing volume (Kc.indicator p)
      (HolomorphicPullback.explicitRadialKernel (min R₀ δ) hR j), fun p hp ↦ ?_,
    fun p hp j ↦ ?_, fun j p q z hpq ↦ ?_⟩
  · have hpL : LocallyIntegrableOn p Ω volume :=
      locallyIntegrableOn_of_plurisubharmonicOn_real hp.1
    have hpLevi : HasNonnegativeDistributionalLevi (regularDistribution volume p hpL) :=
      hasNonnegativeDistributionalLevi_of_plurisubharmonicOn_real hp.1
    obtain ⟨S, hSk⟩ :=
      HolomorphicPullback.exists_explicitRadialConvolutionSystem_of_locallyBoundedPsh
        hp hR hN (hNK.trans hKcΩ) hKc hKcΩ hball
    have hker : S.kernel = fun j ↦ HolomorphicPullback.explicitRadialKernel (min R₀ δ) hR j :=
      funext fun j ↦ funext (hSk j)
    let f : ℕ → ComplexModel n → ℝ := fun j ↦
      translationPairing volume (Kc.indicator p) (S.kernel j)
    have hg : LocallyIntegrable (Kc.indicator p) volume :=
      (integrable_indicator_of_locallyIntegrableOn_isCompact hpL hKc hKcΩ).locallyIntegrable
    have hfDisc (j : ℕ) : DiscPshOn (fun x ↦ (f j x : EReal)) N :=
      discPshOn_translationPairing_indicator hpL hpLevi
        (S.kernel_hasCompactSupport j) (S.kernel_contDiff j)
        (S.kernel_nonneg j) hKc hKcΩ (S.translated_tsupport j)
    have hfPsh (j : ℕ) : PlurisubharmonicOn (fun x ↦ (f j x : EReal)) A :=
      ((hfDisc j).plurisubharmonicOn hN).mono hAN
    have hfSmooth (j : ℕ) : IsSmoothPshOn A (f j) :=
      isSmoothPshOn_of_psh
        (contDiff_translationPairing hg (S.kernel_hasCompactSupport j)
          (S.kernel_contDiff j)).contDiffOn (hfPsh j)
    have hanti : ∀ x ∈ A, Antitone (fun j ↦ f j x) :=
      fun x hx ↦ S.antitone_pairing x (hAN hx)
    have hae : ∀ᵐ x ∂volume.restrict (A : Set (ComplexModel n)),
        Tendsto (fun j ↦ f j x) atTop (𝓝 (p x)) := by
      have haeN := S.ae_tendsto_pairing
      change ∀ᵐ x ∂volume.restrict N,
        Tendsto (fun j ↦ f j x) atTop (𝓝 (p x)) at haeN
      exact ae_mono (Measure.restrict_mono hAN le_rfl) haeN
    have hpoint : ∀ x ∈ A, Tendsto (fun j ↦ f j x) atTop (𝓝 (p x)) :=
      tendsto_everywhere_of_ae_of_antitone_psh (hp.1.mono hAΩ) hfPsh hanti hae
    have hdec : IsDecreasingApproximation A p f := ⟨hfSmooth, hanti, hpoint⟩
    simp only [f, hker] at hdec
    exact isDecApprox_of_isDecreasingApproximation hp hAΩ hdec
  · have hpL : LocallyIntegrableOn p Ω volume :=
      locallyIntegrableOn_of_plurisubharmonicOn_real hp.1
    have hg : LocallyIntegrable (Kc.indicator p) volume :=
      (integrable_indicator_of_locallyIntegrableOn_isCompact hpL hKc hKcΩ).locallyIntegrable
    exact contDiff_translationPairing hg
      (HolomorphicPullback.explicitRadialKernel_hasCompactSupport _ hR j)
      (HolomorphicPullback.explicitRadialKernel_contDiff _ hR j)
  · unfold translationPairing
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    by_cases hx : HolomorphicPullback.explicitRadialKernel (min R₀ δ) hR j (x - z) = 0
    · simp [hx]
    · have hxz : x ∈ closedBall z (min R₀ δ) :=
        closedBall_subset_closedBall (shrinkingBump_rOut_le _ hR j)
          (HolomorphicPullback.tsupport_explicitRadialKernel_translate_subset _ hR j z
            (subset_tsupport _ hx))
      have hxδ : x ∈ closedBall z δ := closedBall_subset_closedBall (min_le_right _ _) hxz
      have e : Kc.indicator p x = Kc.indicator q x := by
        by_cases hK : x ∈ Kc
        · rw [indicator_of_mem hK, indicator_of_mem hK, hpq x hxδ]
        · rw [indicator_of_notMem hK, indicator_of_notMem hK]
      change Kc.indicator p x * HolomorphicPullback.explicitRadialKernel (min R₀ δ) hR j (x - z) =
        Kc.indicator q x * HolomorphicPullback.explicitRadialKernel (min R₀ δ) hR j (x - z)
      rw [e]

/-- **Smooth symmetric integration by parts.** For smooth slot functions `a`, `b`,
`c` on `U` with `a - c` and `b - c` supported in a compact subset of `U`,
`∫ (a - c) (ddᶜb - ddᶜc) ∧ R = ∫ (b - c) (ddᶜa - ddᶜc) ∧ R`. -/
theorem integral_sub_mul_mixedDensity_update_sub_symm {U : Opens (ComplexModel n)}
    {f : Fin n → ComplexModel n → ℝ} (hf : ∀ i, ContDiffOn ℝ ∞ (f i) U) (i₀ : Fin n)
    {a b c : ComplexModel n → ℝ} (ha : ContDiffOn ℝ ∞ a U) (hb : ContDiffOn ℝ ∞ b U)
    (hc : ContDiffOn ℝ ∞ c U) (hac : HasCompactSupport fun z ↦ a z - c z)
    (hacU : tsupport (fun z ↦ a z - c z) ⊆ U) (hbcU : tsupport (fun z ↦ b z - c z) ⊆ U) :
    ∫ z, (a z - c z) * (mixedDensity (Function.update f i₀ b) z -
        mixedDensity (Function.update f i₀ c) z) =
      ∫ z, (b z - c z) * (mixedDensity (Function.update f i₀ a) z -
        mixedDensity (Function.update f i₀ c) z) := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have key : ∀ {p q : ComplexModel n → ℝ}, tsupport (fun z ↦ p z - c z) ⊆ U →
      ContDiffOn ℝ ∞ q U →
      (fun z ↦ (p z - c z) * (mixedDensity (Function.update f i₀ q) z -
        mixedDensity (Function.update f i₀ c) z)) =
        fun z ↦ (p z - c z) * mixedDensity (Function.update f i₀ fun y ↦ q y - c y) z := by
    intro p q hpU hq
    funext z
    by_cases hz : z ∈ (U : Set (ComplexModel n))
    · have hc2 : ContDiffAt ℝ 2 c z := ((hc z hz).contDiffAt (U.isOpen.mem_nhds hz)).of_le h2
      have hqc2 : ContDiffAt ℝ 2 (fun y ↦ q y - c y) z :=
        (((hq.sub hc) z hz).contDiffAt (U.isOpen.mem_nhds hz)).of_le h2
      have h := mixedDensity_update_add_smul (f := f) i₀ hc2 hqc2 1
      have hfun : (fun y ↦ c y + 1 * (q y - c y)) = q := by funext y; ring
      rw [hfun] at h
      rw [h]; ring
    · have h0 : p z - c z = 0 :=
        image_eq_zero_of_notMem_tsupport (f := fun z ↦ p z - c z) fun h ↦ hz (hpU h)
      simp [h0]
  rw [key hacU hb, key hbcU ha]
  exact integral_mul_mixedDensity_update_swap hf i₀ (ha.sub hc) (hb.sub hc) hac hacU

theorem update_apply_seq_update {F : Fin n → ℕ → ComplexModel n → ℝ} (i₀ : Fin n)
    (c : ℕ → ComplexModel n → ℝ) (k : ℕ) :
    (fun i ↦ Function.update F i₀ c i k) = Function.update (fun i ↦ F i k) i₀ (c k) := by
  funext i
  by_cases h : i = i₀
  · subst h; simp
  · simp [Function.update_of_ne h]

/-- **Symmetric integration by parts** for Bedford–Taylor measures (Błocki,
Prop. 2.1.3): if `u₀`, `u₁` agree with the smooth PSD function `g` off a compact
subset of `Ω`, then `∫ (u₀ - g) ddᶜ(u₁ - g) ∧ R = ∫ (u₁ - g) ddᶜ(u₀ - g) ∧ R`,
where `R` is the Bedford–Taylor product of the other slots. -/
theorem integral_sub_eq_integral_sub_of_eqOn_compl
    {Ω : Opens (ComplexModel n)} {v : Fin n → ComplexModel n → ℝ} (i₀ : Fin n)
    {u₀ u₁ g : ComplexModel n → ℝ} (hu₀ : IsLocallyBoundedPshOn Ω u₀)
    (hu₁ : IsLocallyBoundedPshOn Ω u₁) (hg : IsSmoothPsdOn Ω g)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (h₀ : ∀ z, z ∉ K → u₀ z = g z) (h₁ : ∀ z, z ∉ K → u₁ z = g z)
    {μ₀ μ₁ μg : Measure (ComplexModel n)}
    (hμ₀ : IsBTLimit Ω (Function.update v i₀ u₀) μ₀)
    (hμ₁ : IsBTLimit Ω (Function.update v i₀ u₁) μ₁)
    (hμg : IsBTLimit Ω (Function.update v i₀ g) μg) :
    (∫ z, (u₀ z - g z) ∂μ₁) - ∫ z, (u₀ z - g z) ∂μg =
      (∫ z, (u₁ z - g z) ∂μ₀) - ∫ z, (u₁ z - g z) ∂μg := by
  classical
  let _ : ProperSpace (ComplexModel n) := FiniteDimensional.proper ℝ _
  -- geometry: `K ⊆ L = cthickening δ K ⊆ A = thickening 2δ K ⋐ Ω`
  obtain ⟨ε, hε, hεΩ⟩ := hK.exists_cthickening_subset_open Ω.isOpen hKΩ
  have hδ : 0 < ε / 3 := by positivity
  let A : Opens (ComplexModel n) := ⟨thickening (2 * (ε / 3)) K, isOpen_thickening⟩
  have hclA : closure (A : Set (ComplexModel n)) ⊆ cthickening (2 * (ε / 3)) K :=
    closure_thickening_subset_cthickening _ _
  have hA : RelativelyCompactIn A Ω :=
    ⟨hK.cthickening.of_isClosed_subset isClosed_closure hclA,
      hclA.trans ((cthickening_mono (by linarith) K).trans hεΩ)⟩
  have hAΩ : (A : Set (ComplexModel n)) ⊆ Ω := subset_closure.trans hA.2
  have hL : IsCompact (cthickening (ε / 3) K) := hK.cthickening
  have hLA : cthickening (ε / 3) K ⊆ A :=
    cthickening_subset_thickening' (by positivity) (by linarith) K
  have hKL : K ⊆ cthickening (ε / 3) K := self_subset_cthickening K
  -- one mollifier for all three functions
  obtain ⟨M, hMdec, hMsm, hMloc⟩ := exists_common_mollifier hA hδ
  have hgb := hg.isLocallyBoundedPshOn
  have hvanish : ∀ {u : ComplexModel n → ℝ}, (∀ z, z ∉ K → u z = g z) →
      ∀ j z, z ∉ cthickening (ε / 3) K → M j u z = M j g z := by
    intro u hu j z hz
    refine hMloc j u g z fun x hx ↦ hu x fun hxK ↦ hz ?_
    exact mem_cthickening_of_dist_le z x (ε / 3) K hxK
      (by rw [dist_comm]; exact mem_closedBall.1 hx)
  have hsupp : ∀ {u : ComplexModel n → ℝ}, (∀ z, z ∉ K → u z = g z) → ∀ j,
      HasCompactSupport (fun z ↦ M j u z - M j g z) ∧
        tsupport (fun z ↦ M j u z - M j g z) ⊆ A := by
    intro u hu j
    have hs : Function.support (fun z ↦ M j u z - M j g z) ⊆ cthickening (ε / 3) K := fun z hz ↦
      by_contra fun hzL ↦ hz (by simp [hvanish hu j z hzL])
    have ht : tsupport (fun z ↦ M j u z - M j g z) ⊆ cthickening (ε / 3) K :=
      closure_minimal hs hL.isClosed
    exact ⟨hL.of_isClosed_subset (isClosed_tsupport _) ht, ht.trans hLA⟩
  -- the cutoff
  obtain ⟨χ, hχ1, -⟩ := exists_testFunction_eq_one_nhds_compact (Ω := A) hL hLA
  have hχL : ∀ z ∈ cthickening (ε / 3) K, χ z = 1 := fun z hz ↦
    (hχ1.filter_mono (nhds_le_nhdsSet hz)).self_of_nhds
  have hχA : tsupport (χ : ComplexModel n → ℝ) ⊆ A := χ.tsupport_subset
  have hcut : ∀ {u : ComplexModel n → ℝ}, (∀ z, z ∉ K → u z = g z) → ∀ j z,
      M j u z - M j g z = χ z * M j u z - χ z * M j g z := by
    intro u hu j z
    by_cases hz : z ∈ cthickening (ε / 3) K
    · rw [hχL z hz]; ring
    · rw [hvanish hu j z hz]; ring
  -- the families
  obtain ⟨F, hF, -⟩ := hμg.2.2 A hA
  have hadm : ∀ {u : ComplexModel n → ℝ} {c : ℕ → ComplexModel n → ℝ}, IsDecApprox A u c →
      IsAdmissible n A (Function.update v i₀ u) (Function.update F i₀ c) := by
    intro u c hc
    refine ⟨fun i ↦ ?_, fun i hi ↦ absurd i.isLt (not_lt.mpr hi)⟩
    by_cases h : i = i₀
    · subst h; simpa using hc
    · simpa [Function.update_of_ne h] using hF.1 i
  have hsmF : ∀ {c : ℕ → ComplexModel n → ℝ}, (∀ k, ContDiffOn ℝ ∞ (c k) A) → ∀ k i,
      ContDiffOn ℝ ∞ (Function.update (fun i ↦ F i k) i₀ (c k) i) A := by
    intro c hc k i
    by_cases h : i = i₀
    · subst h; simpa using hc k
    · simpa [Function.update_of_ne h] using ((hF.1 i).1 k).1
  have hW : WClaim n n := wClaim_of_pClaim pClaim_all
  have hrestrict : ∀ (w : ComplexModel n → ℝ) (ρ : Measure (ComplexModel n)),
      ∫ z, χ z * w z ∂(ρ.restrict A) = ∫ z, χ z * w z ∂ρ := fun w ρ ↦
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ by
      rw [image_eq_zero_of_notMem_tsupport fun h ↦ hz (hχA h), zero_mul]
  have hlim : ∀ {u w : ComplexModel n → ℝ} {μ : Measure (ComplexModel n)}
      {c G : ℕ → ComplexModel n → ℝ},
      IsBTLimit Ω (Function.update v i₀ u) μ → IsDecApprox A u c → IsDecApprox A w G →
      Tendsto (fun k ↦ ∫ z, χ z * G k z *
          mixedDensity (Function.update (fun i ↦ F i k) i₀ (c k)) z) atTop
        (𝓝 (∫ z, χ z * w z ∂μ)) := by
    intro u w μ c G hμ hc hG
    have h := hW A (Function.update v i₀ u) (μ.restrict A)
      (by rw [Measure.restrict_apply' A.isOpen.measurableSet]; simp)
      (fun K hK hKA ↦ lt_of_le_of_lt (Measure.restrict_le_self K)
        (hμ.2.1 K hK (hKA.trans hAΩ)))
      (fun F hF ↦ hμ.tendstoMixed_restrict hA hF) _ (hadm hc) w G hG χ χ.continuous
      χ.hasCompactSupport hχA
    rw [hrestrict] at h
    simpa only [update_apply_seq_update] using h
  -- expanding the smooth pairings into weighted integrals
  have hint : ∀ {W c : ℕ → ComplexModel n → ℝ}, (∀ k, ContDiffOn ℝ ∞ (W k) A) →
      (∀ k, ContDiffOn ℝ ∞ (c k) A) → ∀ k,
      Integrable fun z ↦ χ z * W k z *
        mixedDensity (Function.update (fun i ↦ F i k) i₀ (c k)) z := by
    intro W c hWs hcs k
    have := integrable_mul_of_continuousOn
      (D := fun z ↦ W k z * mixedDensity (Function.update (fun i ↦ F i k) i₀ (c k)) z)
      ((hWs k).continuousOn.mul (continuousOn_mixedDensity (hsmF hcs k))) χ.continuous
      χ.hasCompactSupport hχA
    simpa only [mul_assoc] using this
  have hsm : ∀ {u : ComplexModel n → ℝ}, IsLocallyBoundedPshOn Ω u → ∀ k,
      ContDiffOn ℝ ∞ (M k u) A := fun hu k ↦ (hMsm _ hu k).contDiffOn
  have hexp : ∀ {p q : ComplexModel n → ℝ}, IsLocallyBoundedPshOn Ω p →
      (∀ z, z ∉ K → p z = g z) → IsLocallyBoundedPshOn Ω q → ∀ k,
      ∫ z, (M k p z - M k g z) *
          (mixedDensity (Function.update (fun i ↦ F i k) i₀ (M k q)) z -
            mixedDensity (Function.update (fun i ↦ F i k) i₀ (M k g)) z) =
        ((∫ z, χ z * M k p z * mixedDensity (Function.update (fun i ↦ F i k) i₀ (M k q)) z) -
          ∫ z, χ z * M k g z * mixedDensity (Function.update (fun i ↦ F i k) i₀ (M k q)) z) -
        ((∫ z, χ z * M k p z * mixedDensity (Function.update (fun i ↦ F i k) i₀ (M k g)) z) -
          ∫ z, χ z * M k g z * mixedDensity (Function.update (fun i ↦ F i k) i₀ (M k g)) z) := by
    intro p q hp hpg hq k
    have i12 : Integrable fun z ↦
        χ z * M k p z * mixedDensity (Function.update (fun i ↦ F i k) i₀ (M k q)) z -
          χ z * M k g z * mixedDensity (Function.update (fun i ↦ F i k) i₀ (M k q)) z :=
      (hint (hsm hp) (hsm hq) k).sub (hint (hsm hgb) (hsm hq) k)
    have i34 : Integrable fun z ↦
        χ z * M k p z * mixedDensity (Function.update (fun i ↦ F i k) i₀ (M k g)) z -
          χ z * M k g z * mixedDensity (Function.update (fun i ↦ F i k) i₀ (M k g)) z :=
      (hint (hsm hp) (hsm hgb) k).sub (hint (hsm hgb) (hsm hgb) k)
    rw [← integral_sub (hint (hsm hp) (hsm hq) k) (hint (hsm hgb) (hsm hq) k),
      ← integral_sub (hint (hsm hp) (hsm hgb) k) (hint (hsm hgb) (hsm hgb) k),
      ← integral_sub i12 i34]
    refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
    simp only [hcut hpg k z]
    ring
  have hsmooth : ∀ k,
      ∫ z, (M k u₀ z - M k g z) *
          (mixedDensity (Function.update (fun i ↦ F i k) i₀ (M k u₁)) z -
            mixedDensity (Function.update (fun i ↦ F i k) i₀ (M k g)) z) =
        ∫ z, (M k u₁ z - M k g z) *
          (mixedDensity (Function.update (fun i ↦ F i k) i₀ (M k u₀)) z -
            mixedDensity (Function.update (fun i ↦ F i k) i₀ (M k g)) z) := fun k ↦
    integral_sub_mul_mixedDensity_update_sub_symm (fun i ↦ ((hF.1 i).1 k).1) i₀
      (hsm hu₀ k) (hsm hu₁ k) (hsm hgb k) (hsupp h₀ k).1 (hsupp h₀ k).2 (hsupp h₁ k).2
  have hL₀ := ((hlim hμ₁ (hMdec u₁ hu₁) (hMdec u₀ hu₀)).sub
    (hlim hμ₁ (hMdec u₁ hu₁) (hMdec g hgb))).sub
    ((hlim hμg (hMdec g hgb) (hMdec u₀ hu₀)).sub (hlim hμg (hMdec g hgb) (hMdec g hgb)))
  have hL₁ := ((hlim hμ₀ (hMdec u₀ hu₀) (hMdec u₁ hu₁)).sub
    (hlim hμ₀ (hMdec u₀ hu₀) (hMdec g hgb))).sub
    ((hlim hμg (hMdec g hgb) (hMdec u₁ hu₁)).sub (hlim hμg (hMdec g hgb) (hMdec g hgb)))
  simp only [← hexp hu₀ h₀ hu₁, hsmooth, hexp hu₁ h₁ hu₀] at hL₀
  have heq := tendsto_nhds_unique hL₀ hL₁
  -- removing the cutoff
  have hfin : ∀ {μ : Measure (ComplexModel n)}, (∀ K, IsCompact K → K ⊆ Ω → μ K < ⊤) →
      ∀ K, IsCompact K → K ⊆ A → μ K < ⊤ := fun hμ K hK hKA ↦ hμ K hK (hKA.trans hAΩ)
  have hdrop : ∀ {u : ComplexModel n → ℝ} {μ : Measure (ComplexModel n)},
      IsLocallyBoundedPshOn Ω u → (∀ z, z ∉ K → u z = g z) →
      (∀ K, IsCompact K → K ⊆ Ω → μ K < ⊤) →
      ∫ z, (u z - g z) ∂μ = (∫ z, χ z * u z ∂μ) - ∫ z, χ z * g z ∂μ := by
    intro u μ hu hug hμ
    rw [← integral_sub ((hMdec u hu).integrable_mul (hfin hμ) χ.continuous χ.hasCompactSupport
      hχA) ((hMdec g hgb).integrable_mul (hfin hμ) χ.continuous χ.hasCompactSupport hχA)]
    refine integral_congr_ae (Eventually.of_forall fun z ↦ ?_)
    by_cases hz : z ∈ K
    · simp only [hχL z (hKL hz)]; ring
    · simp only [hug z hz]; ring
  rw [hdrop hu₀ h₀ hμ₁.2.1, hdrop hu₀ h₀ hμg.2.1, hdrop hu₁ h₁ hμ₀.2.1, hdrop hu₁ h₁ hμg.2.1]
  linarith

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
