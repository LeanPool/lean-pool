/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorBall

/-!
# The Chern–Levine–Nirenberg estimate for smooth mixed densities

For smooth plurisubharmonic slots that are uniformly bounded on a closed ball,
and a smooth plurisubharmonic weight `g` bounded above by `S` on the ball, the
integral of `S - g` against the mixed density over the half ball is bounded by
a constant times the Lebesgue integral of `S - g` over the ball. The constant
depends only on the bound of the slots and the radius.

The proof raises every slot to a common collar potential near the sphere
(regularized maximum), then integrates by parts slot by slot: raising a slot
compactly raises the weighted integral against a plurisubharmonic weight.

This is the local smooth top-degree version of the weighted estimate in
[Demailly, Proposition III.3.11](https://www-fourier.univ-grenoble-alpes.fr/~demailly/source_files/analgeom/agbook.pdf#page=149),
which allows locally bounded plurisubharmonic slots and an unbounded
plurisubharmonic weight.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

variable {n : ℕ}

theorem mixedDensity_collar (z₀ : ComplexModel n) (A R : ℝ) (z : ComplexModel n) :
    mixedDensity (fun _ ↦ collar z₀ A R) z = (n.factorial : ℝ) / Real.pi ^ n * A ^ n := by
  rw [mixedDensity_diagonal, smoothDensity, complexHessian_collar, Matrix.det_smul]
  simp [← Complex.ofReal_pow]

open SmoothMax in
/-- **Chern–Levine–Nirenberg estimate for smooth densities.** The constant only
depends on the center, the radius and the uniform bound of the slots. -/
theorem exists_cln_constant (z₀ : ComplexModel n) {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Opens (ComplexModel n)) (F : Fin n → ComplexModel n → ℝ)
      (g : ComplexModel n → ℝ) (S : ℝ), closedBall z₀ (2 * R) ⊆ U →
      (∀ i, IsSmoothPsdOn U (F i)) → (∀ i, ∀ z ∈ closedBall z₀ (2 * R), |F i z| ≤ M) →
      IsSmoothPsdOn U g → (∀ z ∈ ball z₀ R, g z ≤ S) →
      ∫ z in ball z₀ (R / 2), (S - g z) * mixedDensity F z ≤
        C * ∫ z in ball z₀ R, (S - g z) := by
  classical
  obtain ⟨A, ρ, hA, hρ1, hρ2, hin, hout⟩ :=
    exists_collar_constants z₀ hR (by linarith : (0 : ℝ) ≤ 2 * M + 2)
  refine ⟨(n.factorial : ℝ) / Real.pi ^ n * A ^ n, by positivity, ?_⟩
  intro U F g S hball hF hFM hg hgS
  set V : Opens (ComplexModel n) := ⟨ball z₀ (2 * R), isOpen_ball⟩ with hV
  have hVU : V ≤ U := fun z hz ↦ hball (ball_subset_closedBall hz)
  set W : Set (ComplexModel n) := ball z₀ R with hW
  have hWo : IsOpen W := isOpen_ball
  have hWc : IsCompact (closure W) :=
    (isCompact_closedBall z₀ R).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall
  have hWV : closure W ⊆ V := closure_ball_subset_closedBall.trans
    (closedBall_subset_ball (by linarith))
  have hWV' : W ⊆ V := subset_closure.trans hWV
  have hsmallW : ball z₀ (R / 2) ⊆ W := ball_subset_ball (by linarith)
  set h := collar z₀ A R with hh_def
  have hhs : IsSmoothPsdOn V h := isSmoothPsdOn_collar V z₀ hA.le R
  set K := closedBall z₀ ρ
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKW : K ⊆ W := closedBall_subset_ball hρ2
  set c : ℝ := M + 2
  have hFV (i : Fin n) : IsSmoothPsdOn V (F i) :=
    ⟨(hF i).1.mono hVU, fun z hz ↦ (hF i).2 z (hVU hz)⟩
  have hgV : IsSmoothPsdOn V g := ⟨hg.1.mono hVU, fun z hz ↦ hg.2 z (hVU hz)⟩
  set b : Fin n → ComplexModel n → ℝ := fun i ↦ smoothMax (fun y ↦ F i y - c) h with hb_def
  have hbs (i : Fin n) : IsSmoothPsdOn V (b i) :=
    ((isDecApprox_const (hFV i)).smoothMax_sub c hhs).1 0
  have hVb (z : ComplexModel n) (hz : z ∈ (V : Set (ComplexModel n))) :
      z ∈ closedBall z₀ (2 * R) := ball_subset_closedBall hz
  -- the cutoff
  obtain ⟨θ, hθ1, -⟩ := exists_testFunction_eq_one_nhds_compact hWc hWV
  have hθs : ContDiff ℝ ∞ (θ : ComplexModel n → ℝ) := θ.contDiff
  have hglob {f : ComplexModel n → ℝ} (hf : ContDiffOn ℝ ∞ f V) :
      ContDiff ℝ ∞ (fun y ↦ θ y • f y) :=
    _root_.SGPT.Foundations.Analysis.SmoothCutoff.contDiff_smul_of_tsupport_subset
      V.isOpen hθs θ.tsupport_subset hf
  have hθW (z : ComplexModel n) (hz : z ∈ W) (f : ComplexModel n → ℝ) :
      (fun y ↦ θ y • f y) =ᶠ[𝓝 z] f :=
    eventuallyEq_smul_of_eq_one hθ1 (subset_closure hz) f
  have hθz (z : ComplexModel n) (hz : z ∈ W) : θ z = 1 :=
    (hθ1.filter_mono (nhds_le_nhdsSet (subset_closure hz))).self_of_nhds
  have hθ0 (z : ComplexModel n) (hz : z ∉ (V : Set (ComplexModel n))) : θ z = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hz (θ.tsupport_subset h)
  have hgSs : ContDiffOn ℝ ∞ (fun y ↦ g y - S) V := hgV.1.sub contDiffOn_const
  -- collar comparison over `W`
  have hmain := setIntegral_mul_mixedDensity_le_of_compact (a := fun y ↦ θ y • (g y - S))
    (hglob hgSs) hK hKW hWo.measurableSet hWc
    (fun z hz ↦ by
      rw [MixedHessian.complexHessian_congr (hθW z hz _), complexHessian_sub_const]
      exact (hg.2 z (hVU (hWV' hz))))
    Finset.univ (fun _ y ↦ θ y • h y) (fun i y ↦ θ y • b i y)
    (fun _ ↦ hglob hhs.1) (fun i ↦ hglob (hbs i).1) (fun i hi ↦ absurd (Finset.mem_univ i) hi)
    (fun i _ z hz ↦ by
      by_cases hzV : z ∈ (V : Set (ComplexModel n))
      · have hbz : b i z = h z := by
          refine smoothMax_eq_right ?_
          have h1 := hout z (by simpa [K, mem_closedBall, dist_eq_norm] using hz)
          have h2 := (abs_le.mp (hFM i z (hVb z hzV))).2
          simp only [c]; linarith
        simp [hbz]
      · simp [hθ0 z hzV])
    (fun _ z hz ↦ by
      rw [MixedHessian.complexHessian_congr (hθW z hz _)]; exact hhs.2 z (hWV' hz))
    (fun i z hz ↦ by
      rw [MixedHessian.complexHessian_congr (hθW z hz _)]; exact (hbs i).2 z (hWV' hz))
    (fun i _ z hz ↦ by
      simp only [hθz z hz, one_smul]
      exact le_smoothMax_right _ _ z)
  have hmain' : ∫ z in W, (g z - S) * mixedDensity (fun _ ↦ h) z ≤
      ∫ z in W, (g z - S) * mixedDensity b z := by
    refine (setIntegral_congr_fun hWo.measurableSet fun z hz ↦ ?_).trans_le
      (hmain.trans_eq (setIntegral_congr_fun hWo.measurableSet fun z hz ↦ ?_))
    · simp only [hθz z hz, one_smul]
      rw [mixedDensity_congr fun _ ↦ hθW z hz h]
    · simp only [hθz z hz, one_smul]
      rw [mixedDensity_congr fun i ↦ hθW z hz (b i)]
  -- near the center the modified slots have the original Hessians
  have hnear (i : Fin n) (z : ComplexModel n) (hz : z ∈ ball z₀ (R / 2)) :
      complexHessian (b i) z = complexHessian (F i) z := by
    have hev : b i =ᶠ[𝓝 z] fun y ↦ F i y - c := by
      filter_upwards [isOpen_ball.mem_nhds hz] with y hy
      refine smoothMax_eq_left ?_
      have h1 := hin y (by simpa [mem_ball, dist_eq_norm] using hy)
      have h2 := (abs_le.mp (hFM i y (hVb y (hWV' (hsmallW hy))))).1
      simp only [c]; linarith
    rw [MixedHessian.complexHessian_congr hev, complexHessian_sub_const]
  have hcont : ContinuousOn (fun z ↦ (S - g z) * mixedDensity b z) V :=
    (continuousOn_const.sub hgV.1.continuousOn).mul
      (continuousOn_mixedDensity fun i ↦ (hbs i).1)
  have hIW : IntegrableOn (fun z ↦ (S - g z) * mixedDensity b z) W :=
    integrableOn_of_continuousOn_closure hWc hWV hcont
  have hstep1 : ∫ z in ball z₀ (R / 2), (S - g z) * mixedDensity F z =
      ∫ z in ball z₀ (R / 2), (S - g z) * mixedDensity b z := by
    refine setIntegral_congr_fun isOpen_ball.measurableSet fun z hz ↦ ?_
    rw [mixedDensity_congr_hessian fun i ↦ (hnear i z hz).symm]
  have hstep2 : ∫ z in ball z₀ (R / 2), (S - g z) * mixedDensity b z ≤
      ∫ z in W, (S - g z) * mixedDensity b z := by
    refine setIntegral_mono_set hIW ?_ (Eventually.of_forall hsmallW)
    filter_upwards [ae_restrict_mem hWo.measurableSet] with z hz
    exact mul_nonneg (sub_nonneg.2 (hgS z hz))
      (mixedDensity_nonneg fun i ↦ (hbs i).2 z (hWV' hz))
  have hstep3 : ∫ z in W, (S - g z) * mixedDensity b z ≤
      ∫ z in W, (S - g z) * mixedDensity (fun _ ↦ h) z := by
    have e1 : ∫ z in W, (S - g z) * mixedDensity b z = -∫ z in W, (g z - S) * mixedDensity b z :=
      by
      rw [← integral_neg]; congr 1; funext z; ring
    have e2 : ∫ z in W, (S - g z) * mixedDensity (fun _ ↦ h) z =
        -∫ z in W, (g z - S) * mixedDensity (fun _ ↦ h) z := by
      rw [← integral_neg]; congr 1; funext z; ring
    rw [e1, e2]
    exact neg_le_neg hmain'
  have hstep4 : ∫ z in W, (S - g z) * mixedDensity (fun _ ↦ h) z =
      (n.factorial : ℝ) / Real.pi ^ n * A ^ n * ∫ z in W, (S - g z) := by
    rw [← integral_const_mul]
    congr 1; funext z
    rw [hh_def, mixedDensity_collar]; ring
  rw [hstep1]
  exact hstep2.trans (hstep3.trans hstep4.le)

theorem IsDecApprox.abs_le_of_mem {U : Opens (ComplexModel n)} {w : ComplexModel n → ℝ}
    {G : ℕ → ComplexModel n → ℝ} (hG : IsDecApprox U w G) {C : ℝ} {K : Set (ComplexModel n)}
    (hKU : K ⊆ U) (hC : ∀ k, ∀ z ∈ K, |G k z| ≤ C) {z : ComplexModel n} (hz : z ∈ K) :
    |w z| ≤ C :=
  le_of_tendsto' ((continuous_abs.tendsto _).comp (hG.2.2.1 z (hKU hz))) fun k ↦ hC k z hz

/-- Weighted decreasing approximations share an integrable limit and a dominated integral limit. -/
theorem IsDecApprox.weighted_sub_mul_limits {U : Opens (ComplexModel n)}
    {w : ComplexModel n → ℝ} {G : ℕ → ComplexModel n → ℝ} (hG : IsDecApprox U w G)
    {B : Set (ComplexModel n)} (hBm : MeasurableSet B) (hBc : IsCompact (closure B))
    (hBU : closure B ⊆ U) {D : ComplexModel n → ℝ} (hD : ContinuousOn D U) (S : ℝ) :
    IntegrableOn (fun z ↦ (S - w z) * D z) B ∧
      Tendsto (fun l ↦ ∫ z in B, (S - G l z) * D z) atTop
        (𝓝 (∫ z in B, (S - w z) * D z)) := by
  have hBU' : B ⊆ U := subset_closure.trans hBU
  obtain ⟨C, hC⟩ := hG.exists_abs_le hBc hBU
  obtain ⟨CD, hCD⟩ := (hBc.image_of_continuousOn (hD.mono hBU)).isBounded.exists_norm_le
  have : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr
    ((measure_mono subset_closure).trans_lt hBc.measure_lt_top).ne
  have hmeas (l : ℕ) :
      AEStronglyMeasurable (fun z ↦ (S - G l z) * D z) (volume.restrict B) :=
    (((continuousOn_const.sub (hG.1 l).1.continuousOn).mul hD).mono
      hBU').aestronglyMeasurable hBm
  have hlim : ∀ᵐ z ∂volume.restrict B,
      Tendsto (fun l ↦ (S - G l z) * D z) atTop (𝓝 ((S - w z) * D z)) := by
    filter_upwards [ae_restrict_mem hBm] with z hz
    exact ((tendsto_const_nhds.sub (hG.2.2.1 z (hBU' hz))).mul_const _)
  have hbound (l : ℕ) : ∀ᵐ z ∂volume.restrict B, ‖(S - G l z) * D z‖ ≤ (|S| + C) * CD := by
    filter_upwards [ae_restrict_mem hBm] with z hz
    rw [norm_mul]
    refine mul_le_mul ?_ (hCD _ ⟨z, subset_closure hz, rfl⟩) (norm_nonneg _) (by
      linarith [abs_nonneg S, (abs_nonneg _).trans (hC 0 z (subset_closure hz))])
    exact (norm_sub_le _ _).trans (by
      simp only [Real.norm_eq_abs]; linarith [hC l z (subset_closure hz)])
  refine ⟨Integrable.of_bound (aestronglyMeasurable_of_tendsto_ae atTop hmeas hlim)
    ((|S| + C) * CD) ?_, ?_⟩
  · filter_upwards [hlim, ae_all_iff.mpr hbound] with z hz hzb
    exact le_of_tendsto' (continuous_norm.continuousAt.tendsto.comp hz) hzb
  · exact tendsto_integral_of_dominated_convergence _ hmeas (integrable_const _) hbound hlim

/-- Dominated convergence for the weighted integrals over a relatively compact set. -/
theorem IsDecApprox.tendsto_setIntegral_sub_mul {U : Opens (ComplexModel n)}
    {w : ComplexModel n → ℝ} {G : ℕ → ComplexModel n → ℝ} (hG : IsDecApprox U w G)
    {B : Set (ComplexModel n)} (hBm : MeasurableSet B) (hBc : IsCompact (closure B))
    (hBU : closure B ⊆ U) {D : ComplexModel n → ℝ} (hD : ContinuousOn D U) (S : ℝ) :
    Tendsto (fun l ↦ ∫ z in B, (S - G l z) * D z) atTop (𝓝 (∫ z in B, (S - w z) * D z)) := by
  exact (hG.weighted_sub_mul_limits hBm hBc hBU hD S).2

/-- A decreasing continuous approximation of a function strictly below `S` on
a compact set is eventually at most `S` there (Dini-type argument). -/
theorem IsDecApprox.eventually_le_of_lt {U : Opens (ComplexModel n)} {w : ComplexModel n → ℝ}
    {G : ℕ → ComplexModel n → ℝ} (hG : IsDecApprox U w G) {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKU : K ⊆ U) {S : ℝ} (hS : ∀ z ∈ K, w z < S) :
    ∃ l₀, ∀ l, l₀ ≤ l → ∀ z ∈ K, G l z ≤ S := by
  classical
  have hloc : ∀ z ∈ K, ∃ N ∈ 𝓝 z, ∃ l : ℕ, ∀ y ∈ N ∩ U, G l y < S := by
    intro z hz
    obtain ⟨l, hl⟩ := ((hG.2.2.1 z (hKU hz)).eventually (gt_mem_nhds (hS z hz))).exists
    have hc : ContinuousAt (G l) z := (hG.1 l).1.continuousOn.continuousAt
      (U.isOpen.mem_nhds (hKU hz))
    exact ⟨_, hc.preimage_mem_nhds (gt_mem_nhds hl), l, fun y hy ↦ hy.1⟩
  choose! N hN l hl using hloc
  obtain ⟨t, htK, hcover⟩ := hK.elim_nhds_subcover N hN
  refine ⟨t.sup l, fun l' hl' z hz ↦ ?_⟩
  obtain ⟨x, hxt, hzx⟩ := mem_iUnion₂.mp (hcover hz)
  have hle : l x ≤ l' := (Finset.le_sup (f := l) hxt).trans hl'
  exact ((hG.2.1 z (hKU hz) hle).trans (hl x (htK x hxt) z ⟨hzx, hKU hz⟩).le)

/-- **Chern–Levine–Nirenberg estimate for bounded plurisubharmonic weights.** -/
theorem exists_cln_constant_weight (z₀ : ComplexModel n) {R M : ℝ} (hR : 0 < R) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (U : Opens (ComplexModel n)) (F : Fin n → ComplexModel n → ℝ)
      (w : ComplexModel n → ℝ) (G : ℕ → ComplexModel n → ℝ) (S : ℝ),
      closedBall z₀ (2 * R) ⊆ U →
      (∀ i, IsSmoothPsdOn U (F i)) → (∀ i, ∀ z ∈ closedBall z₀ (2 * R), |F i z| ≤ M) →
      IsDecApprox U w G → (∀ z ∈ closedBall z₀ R, w z < S) →
      ∫ z in ball z₀ (R / 2), (S - w z) * mixedDensity F z ≤
        C * ∫ z in ball z₀ R, (S - w z) := by
  obtain ⟨C, hC0, hC⟩ := exists_cln_constant z₀ hR hM
  refine ⟨C, hC0, fun U F w G S hball hF hFM hG hwS ↦ ?_⟩
  have hsub (r : ℝ) (hr : r ≤ R) : closure (ball z₀ r) ⊆ U :=
    closure_ball_subset_closedBall.trans ((closedBall_subset_closedBall (by linarith)).trans hball)
  have hcpt (r : ℝ) : IsCompact (closure (ball z₀ r)) :=
    (isCompact_closedBall z₀ r).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall
  obtain ⟨l₀, hl₀⟩ := hG.eventually_le_of_lt (isCompact_closedBall z₀ R)
    ((closedBall_subset_closedBall (by linarith)).trans hball) hwS
  have hL := hG.tendsto_setIntegral_sub_mul isOpen_ball.measurableSet (hcpt _)
    (hsub (R / 2) (by linarith)) (continuousOn_mixedDensity fun i ↦ (hF i).1) S
  have hR' := hG.tendsto_setIntegral_sub_mul isOpen_ball.measurableSet (hcpt R) (hsub R le_rfl)
    (continuousOn_const (c := (1 : ℝ))) S
  simp only [mul_one] at hR'
  refine le_of_tendsto_of_tendsto hL (hR'.const_mul C) (eventually_atTop.2 ⟨l₀, fun l hl ↦ ?_⟩)
  exact hC U F (G l) S hball hF hFM (hG.1 l) fun z hz ↦ hl₀ l hl z (ball_subset_closedBall hz)

end SGPT.Foundations.Analysis.Pending.BedfordTaylor
