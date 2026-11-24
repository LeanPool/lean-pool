/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorCapacity

/-!
# Błocki's inequality for the Monge–Ampère operator

Let `u₁, …, uₙ` be bounded plurisubharmonic functions with `-1 ≤ uᵢ ≤ 0`, and let
`v ≤ w` be bounded plurisubharmonic functions with `w - v` vanishing off a compact
subset of the domain. Then (Błocki, *The complex Monge–Ampère operator in
pluripotential theory*, lecture notes, Theorem 2.1.8, inequality (2.1.5) with
`p = n + 1`)

  `∫ (w - v)ⁿ⁺¹ ddᶜu₁ ∧ ⋯ ∧ ddᶜuₙ ≤ (n + 1)! ∫ (w - v) (ddᶜv)ⁿ`.

**Smooth case.** For `f = w - v ≥ 0` compactly supported and `T` a product of
smooth semipositive forms, integration by parts gives
`∫ fᵖ ddᶜu ∧ T = ∫ u ddᶜ(fᵖ) ∧ T`, and
`ddᶜ(fᵖ) + p fᵖ⁻¹ ddᶜv = p(p-1) fᵖ⁻² df ∧ dᶜf + p fᵖ⁻¹ ddᶜw ≥ 0`, so for
`c - M ≤ u ≤ c` on the support, `∫ fᵖ ddᶜu ∧ T ≤ M p ∫ fᵖ⁻¹ ddᶜv ∧ T`. Iterating
over the slots gives the inequality with the factor `Mⁿ (n+1)!`.

**Bedford–Taylor case.** The slots `uᵢ` are replaced by their decreasing smooth
approximations, which are eventually `≤ ε` on the support (Dini); the weak
convergence of the mixed densities passes the inequality to the limit, and
`ε → 0`. The function `v` is replaced by `v_k ↓ v` with `w = v_j` (`k ≥ j`), the
left side converging by dominated convergence and the right side by the weighted
Bedford–Taylor convergence theorem.

In the form proved here `w` is a member `G j` of a decreasing smooth approximation
`G` of `v` all of whose members agree off a fixed compact set (a collar), which is
the form used for the quasi-continuity of plurisubharmonic functions (Błocki,
Proposition 2.2.4).
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff ComplexOrder Nat

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

variable {n : ℕ}

/-! ## Pointwise algebra -/

theorem complexHessian_sub_eq {w v : ComplexModel n → ℝ} {z : ComplexModel n}
    (hw : ContDiffAt ℝ 2 w z) (hv : ContDiffAt ℝ 2 v z) :
    complexHessian (fun y ↦ w y - v y) z = complexHessian w z - complexHessian v z := by
  rw [show (fun y ↦ w y - v y) = w + (-1 : ℝ) • v by funext x; simp [sub_eq_add_neg],
    complexHessian_add (v := (-1 : ℝ) • v) hw (hv.const_smul (-1 : ℝ)), complexHessian_smul hv]
  simp [sub_eq_add_neg]

/-- `ddᶜ(fᵖ⁺¹) + (p+1) f(z)ᵖ ddᶜv ≥ 0` at `z` for `f = w - v ≥ 0` near `z`, `w` psh. -/
theorem complexHessian_pow_add_posSemidef {f w v : ComplexModel n → ℝ} {z : ComplexModel n}
    (hw : ContDiffAt ℝ 2 w z) (hv : ContDiffAt ℝ 2 v z) (hf : f =ᶠ[𝓝 z] fun y ↦ w y - v y)
    (hf0 : 0 ≤ f z) (hHw : (complexHessian w z).PosSemidef) (p : ℕ) :
    (complexHessian (fun y ↦ f y ^ (p + 1) + ((p + 1 : ℝ) * f z ^ p) * v y) z).PosSemidef := by
  have hfc : ContDiffAt ℝ 2 f z := (hw.sub hv).congr_of_eventuallyEq hf
  have hφ : ContDiff ℝ ∞ (fun t : ℝ ↦ t ^ (p + 1)) := contDiff_id.pow _
  have hd1 : deriv (fun t : ℝ ↦ t ^ (p + 1)) = fun t ↦ (p + 1 : ℝ) * t ^ p := by
    funext t; rw [(hasDerivAt_pow (p + 1) t).deriv]; push_cast; simp
  have hd2 : deriv (deriv (fun t : ℝ ↦ t ^ (p + 1))) (f z) =
      (p + 1 : ℝ) * ((p : ℝ) * f z ^ (p - 1)) := by
    rw [hd1, ((hasDerivAt_pow p (f z)).const_mul ((p : ℝ) + 1)).deriv]
  have hsplit : (fun y ↦ f y ^ (p + 1) + ((p + 1 : ℝ) * f z ^ p) * v y) =
      ((fun t : ℝ ↦ t ^ (p + 1)) ∘ f) + ((p + 1 : ℝ) * f z ^ p) • v := by
    funext y; simp
  have hHf : complexHessian f z = complexHessian w z - complexHessian v z := by
    rw [MixedHessian.complexHessian_congr hf, complexHessian_sub_eq hw hv]
  have hcomp : ContDiffAt ℝ 2 ((fun t : ℝ ↦ t ^ (p + 1)) ∘ f) z := hfc.pow (p + 1)
  rw [hsplit, complexHessian_add hcomp
      (show ContDiffAt ℝ 2 (((p + 1 : ℝ) * f z ^ p) • v) z from hv.const_smul ((p + 1 : ℝ)
        * f z ^ p)),
    complexHessian_smul hv,
    SmoothMax.complexHessian_comp hφ hfc, hd2, hd1, hHf, Complex.coe_smul]
  beta_reduce
  set c : ℝ := (p + 1 : ℝ) * f z ^ p with hc
  have hc0 : 0 ≤ c := by positivity
  have hd0 : 0 ≤ (p + 1 : ℝ) * ((p : ℝ) * f z ^ (p - 1)) := by positivity
  have e : c • (complexHessian w z - complexHessian v z) +
      ((p + 1 : ℝ) * ((p : ℝ) * f z ^ (p - 1))) •
        Matrix.vecMulVec (SmoothMax.delGrad f z) (star (SmoothMax.delGrad f z)) +
      c • complexHessian v z = c • complexHessian w z +
      ((p + 1 : ℝ) * ((p : ℝ) * f z ^ (p - 1))) •
        Matrix.vecMulVec (SmoothMax.delGrad f z) (star (SmoothMax.delGrad f z)) := by
    rw [smul_sub]; abel
  rw [e]
  exact (hHw.smul hc0).add ((Matrix.posSemidef_vecMulVec_self_star _).smul hd0)

/-! ## The smooth inequality -/

/-- **One step of Błocki's inequality**, smooth case. -/
theorem integral_pow_mul_mixedDensity_le {W : Opens (ComplexModel n)} {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKW : K ⊆ W) {f w v : ComplexModel n → ℝ} (hf : ContDiffOn ℝ ∞ f W)
    (hfK : ∀ z ∉ K, f z = 0) (hf0 : ∀ z, 0 ≤ f z) (hw : IsSmoothPsdOn W w)
    (hv : IsSmoothPsdOn W v) (hfwv : ∀ z ∈ W, f z = w z - v z)
    {s : Fin n → ComplexModel n → ℝ} (hs : ∀ i, IsSmoothPsdOn W (s i)) (i₀ : Fin n)
    {c M : ℝ} (hM : ∀ z ∈ K, c - M ≤ s i₀ z ∧ s i₀ z ≤ c) (q : ℕ) :
    ∫ z, f z ^ (q + 2) * mixedDensity s z ≤
      M * ((q : ℝ) + 2) * ∫ z, f z ^ (q + 1) * mixedDensity (Function.update s i₀ v) z := by
  classical
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  set g : ComplexModel n → ℝ := fun z ↦ f z ^ (q + 2) with hg_def
  have hgK : ∀ z ∉ K, g z = 0 := fun z hz ↦ by simp [hg_def, hfK z hz]
  have hgsupp : tsupport g ⊆ K :=
    closure_minimal (fun z hz ↦ by_contra fun h ↦ hz (hgK z h)) hK.isClosed
  have hgc : HasCompactSupport g := HasCompactSupport.intro hK hgK
  have hg : ContDiffOn ℝ ∞ g W := hf.pow (q + 2)
  set a : ComplexModel n → ℝ := fun y ↦ s i₀ y - c with ha_def
  have ha : ContDiffOn ℝ ∞ a W := (hs i₀).1.sub contDiffOn_const
  have hupd_smooth (b : ComplexModel n → ℝ) (hb : ContDiffOn ℝ ∞ b W) (i : Fin n) :
      ContDiffOn ℝ ∞ (Function.update s i₀ b i) W := by
    by_cases h : i = i₀
    · subst h; simpa using hb
    · simpa [Function.update_of_ne h] using (hs i).1
  -- replacing `s i₀` by `a` does not change the density
  have hstep1 : ∀ z, mixedDensity s z = mixedDensity (Function.update s i₀ a) z := by
    intro z
    refine mixedDensity_congr_hessian fun i ↦ ?_
    by_cases h : i = i₀
    · subst h; simp [ha_def, complexHessian_sub_const]
    · simp [Function.update_of_ne h]
  have hibp := integral_mul_mixedDensity_update_swap (U := W) (fun i ↦ (hs i).1) i₀ hg ha hgc
    (hgsupp.trans hKW)
  simp only [← hstep1] at hibp
  rw [hibp, ← integral_const_mul]
  -- integrability
  have hI1 : Integrable fun z ↦ a z * mixedDensity (Function.update s i₀ g) z := by
    have h0 : ∀ z ∉ K, a z * mixedDensity (Function.update s i₀ g) z = 0 := fun z hz ↦ by
      rw [mixedDensity_update_eq_zero_of_notMem_tsupport i₀ fun h ↦ hz (hgsupp h), mul_zero]
    exact (continuous_of_continuousOn_of_eq_zero W.isOpen hK.isClosed hKW
      (ha.continuousOn.mul (continuousOn_mixedDensity (hupd_smooth g hg)))
        h0).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hK h0)
  have hI2 : Integrable fun z ↦
      M * ((q : ℝ) + 2) * (f z ^ (q + 1) * mixedDensity (Function.update s i₀ v) z) := by
    have h0 : ∀ z ∉ K, M * ((q : ℝ) + 2) *
        (f z ^ (q + 1) * mixedDensity (Function.update s i₀ v) z) = 0 := fun z hz ↦ by
      simp [hfK z hz]
    exact (continuous_of_continuousOn_of_eq_zero W.isOpen hK.isClosed hKW
      (continuousOn_const.mul ((hf.continuousOn.pow _).mul
        (continuousOn_mixedDensity (hupd_smooth v hv.1)))) h0).integrable_of_hasCompactSupport
      (HasCompactSupport.intro hK h0)
  refine integral_mono hI1 hI2 fun z ↦ ?_
  by_cases hzK : z ∈ K
  · have hzW := hKW hzK
    obtain ⟨hlo, hhi⟩ := hM z hzK
    have hwz : ContDiffAt ℝ 2 w z := (hw.1.contDiffAt (W.isOpen.mem_nhds hzW)).of_le h2
    have hvz : ContDiffAt ℝ 2 v z := (hv.1.contDiffAt (W.isOpen.mem_nhds hzW)).of_le h2
    have hfz : ContDiffAt ℝ 2 f z := (hf.contDiffAt (W.isOpen.mem_nhds hzW)).of_le h2
    have hev : f =ᶠ[𝓝 z] fun y ↦ w y - v y :=
      Filter.eventually_of_mem (W.isOpen.mem_nhds hzW) fun y hy ↦ hfwv y hy
    have hpsd := complexHessian_pow_add_posSemidef hwz hvz hev (hf0 z) (hw.2 z hzW) (q + 1)
    have hslots (b : ComplexModel n → ℝ) (hb : (complexHessian b z).PosSemidef) (i : Fin n) :
        (complexHessian (Function.update s i₀ b i) z).PosSemidef := by
      by_cases h : i = i₀
      · subst h; simpa using hb
      · simpa [Function.update_of_ne h] using (hs i).2 z hzW
    have hD := mixedDensity_nonneg (hslots _ hpsd)
    rw [mixedDensity_update_add_smul i₀ (hfz.pow _) hvz] at hD
    have hP := mixedDensity_nonneg (hslots v (hv.2 z hzW))
    set D := mixedDensity (Function.update s i₀ fun y ↦ f y ^ (q + 1 + 1)) z
    set P := mixedDensity (Function.update s i₀ v) z
    have hc' : 0 ≤ ((q + 1 : ℕ) + 1 : ℝ) * f z ^ (q + 1) := by have := hf0 z; positivity
    have ha0 : a z ≤ 0 := by simp only [ha_def]; linarith
    have haM : -M ≤ a z := by simp only [ha_def]; linarith
    have hgz : mixedDensity (Function.update s i₀ g) z = D := rfl
    have e1 := mul_nonneg (neg_nonneg.2 ha0) hD
    have e2 := mul_nonneg (show 0 ≤ M + a z by linarith) (mul_nonneg hc' hP)
    push_cast at e1 e2 ⊢
    nlinarith
  · have hgz : z ∉ tsupport g := fun h ↦ hzK (hgsupp h)
    rw [mixedDensity_update_eq_zero_of_notMem_tsupport i₀ hgz]
    simp [hfK z hzK]

/-- **Błocki's inequality, smooth case**: iteration over the slots. -/
theorem integral_pow_mul_mixedDensity_le_iterate {W : Opens (ComplexModel n)}
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKW : K ⊆ W) {f w v : ComplexModel n → ℝ}
    (hf : ContDiffOn ℝ ∞ f W) (hfK : ∀ z ∉ K, f z = 0) (hf0 : ∀ z, 0 ≤ f z)
    (hw : IsSmoothPsdOn W w) (hv : IsSmoothPsdOn W v) (hfwv : ∀ z ∈ W, f z = w z - v z)
    {u : Fin n → ComplexModel n → ℝ} (hu : ∀ i, IsSmoothPsdOn W (u i)) {c : Fin n → ℝ} {M : ℝ}
    (hM0 : 0 ≤ M) (huM : ∀ i, ∀ z ∈ K, c i - M ≤ u i z ∧ u i z ≤ c i) :
    ∫ z, f z ^ (n + 1) * mixedDensity u z ≤
      M ^ n * (n + 1)! * ∫ z, f z * mixedDensity (fun _ ↦ v) z := by
  classical
  set S : ℕ → Fin n → ComplexModel n → ℝ := fun k i ↦ if i.val < k then v else u i with hS
  have hSs (k : ℕ) (i : Fin n) : IsSmoothPsdOn W (S k i) := by
    by_cases h : i.val < k <;> simp [hS, h, hv, hu i]
  have key : ∀ k, k ≤ n → ∫ z, f z ^ (n + 1) * mixedDensity u z ≤
      M ^ k * ((n + 1).descFactorial k : ℝ) * ∫ z, f z ^ (n + 1 - k) * mixedDensity (S k) z := by
    intro k
    induction k with
    | zero =>
      intro _
      have : S 0 = u := by funext i; simp [hS]
      simp [this]
    | succ k ih =>
      intro hk
      set i₀ : Fin n := ⟨k, hk⟩
      have hb : ∀ z ∈ K, c i₀ - M ≤ S k i₀ z ∧ S k i₀ z ≤ c i₀ := by
        intro z hz; simpa [hS, i₀] using huM i₀ z hz
      have hstep := integral_pow_mul_mixedDensity_le hK hKW hf hfK hf0 hw hv hfwv (hSs k) i₀ hb
        (n - 1 - k)
      have e1 : n - 1 - k + 2 = n + 1 - k := by omega
      have e2 : n - 1 - k + 1 = n + 1 - (k + 1) := by omega
      have hupd : Function.update (S k) i₀ v = S (k + 1) := by
        funext i
        by_cases h : i = i₀
        · subst h; simp [hS, i₀]
        · have hne : i.val ≠ k := fun h' ↦ h (Fin.ext h')
          simp only [Function.update_of_ne h, hS]
          by_cases hlt : i.val < k
          · simp [hlt, show i.val < k + 1 by omega]
          · simp [hlt, show ¬ i.val < k + 1 by omega]
      rw [e1, e2, hupd] at hstep
      have hq : ((n - 1 - k : ℕ) : ℝ) + 2 = ((n + 1 - k : ℕ) : ℝ) := by
        rw [← e1]; push_cast; ring
      rw [hq] at hstep
      have hD : ((n + 1).descFactorial (k + 1) : ℝ) =
          ((n + 1 - k : ℕ) : ℝ) * ((n + 1).descFactorial k : ℝ) := by
        rw [Nat.descFactorial_succ]; push_cast; ring
      have hnn : 0 ≤ M ^ k * ((n + 1).descFactorial k : ℝ) := by positivity
      calc _ ≤ _ := ih (by omega)
        _ ≤ M ^ k * ((n + 1).descFactorial k : ℝ) * (M * ((n + 1 - k : ℕ) : ℝ) *
            ∫ z, f z ^ (n + 1 - (k + 1)) * mixedDensity (S (k + 1)) z) :=
          mul_le_mul_of_nonneg_left hstep hnn
        _ = _ := by rw [hD, pow_succ]; ring
  have h := key n le_rfl
  have hSn : S n = fun _ ↦ v := by funext i; simp [hS, i.isLt]
  have hfac : ((n + 1).descFactorial n : ℝ) = ((n + 1)! : ℝ) := by
    have := Nat.factorial_mul_descFactorial (show n ≤ n + 1 by omega)
    rw [show n + 1 - n = 1 by omega, Nat.factorial_one, one_mul] at this
    exact_mod_cast this
  rw [hSn, hfac, show n + 1 - n = 1 by omega] at h
  simpa using h

/-! ## Passage to Bedford–Taylor limits -/

/-- **Dini's theorem** for a decreasing sequence of continuous functions whose pointwise
limit stays below `ε` on a compact set. -/
theorem eventually_forall_lt_of_antitone {X : Type*} [TopologicalSpace X] [T2Space X]
    {K : Set X} (hK : IsCompact K) {g : ℕ → X → ℝ} (hg : ∀ k, ContinuousOn (g k) K)
    (hmono : ∀ z ∈ K, Antitone fun k ↦ g k z) {ε : ℝ}
    (hlim : ∀ z ∈ K, ∀ᶠ k in atTop, g k z < ε) : ∀ᶠ k in atTop, ∀ z ∈ K, g k z < ε := by
  by_contra h
  rw [not_eventually, frequently_atTop] at h
  set t : ℕ → Set X := fun k ↦ K ∩ g k ⁻¹' Ici ε with ht
  have hne : ∀ k, (t k).Nonempty := by
    intro k
    obtain ⟨b, hb, hb'⟩ := h k
    push Not at hb'
    obtain ⟨z, hz, hzε⟩ := hb'
    exact ⟨z, hz, hzε.trans (hmono z hz hb)⟩
  have hcl : ∀ k, IsClosed (t k) := fun k ↦
    (hg k).preimage_isClosed_of_isClosed hK.isClosed isClosed_Ici
  have hanti : Antitone t := fun k l hkl z hz ↦ ⟨hz.1, le_trans hz.2 (hmono z hz.1 hkl)⟩
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t
    hanti.directed_ge hne (fun k ↦ hK.of_isClosed_subset (hcl k) inter_subset_left) hcl
  rw [mem_iInter] at hz
  obtain ⟨k, hk⟩ := (hlim z (hz 0).1).exists
  exact absurd (hz k).2 (not_le.2 hk)

/-- **Błocki's inequality with Bedford–Taylor slots** and smooth `v ≤ w`. -/
theorem integral_pow_le_of_isBTLimit_of_smooth {V W : Opens (ComplexModel n)}
    (hW : RelativelyCompactIn W V) {K : Set (ComplexModel n)} (hK : IsCompact K) (hKW : K ⊆ W)
    {u : Fin n → ComplexModel n → ℝ} {μ : Measure (ComplexModel n)} (hμ : IsBTLimit V u μ)
    (hu : ∀ i, ∀ z ∈ K, -1 ≤ u i z ∧ u i z ≤ 0) {f w v : ComplexModel n → ℝ}
    (hf : ContDiffOn ℝ ∞ f W) (hfK : ∀ z ∉ K, f z = 0) (hf0 : ∀ z, 0 ≤ f z)
    (hw : IsSmoothPsdOn W w) (hv : IsSmoothPsdOn W v) (hfwv : ∀ z ∈ W, f z = w z - v z) :
    ∫ z, f z ^ (n + 1) ∂μ ≤ (n + 1)! * ∫ z, f z * mixedDensity (fun _ ↦ v) z := by
  obtain ⟨F, hF, hFT⟩ := hμ.2.2 W hW
  set R := ∫ z, f z * mixedDensity (fun _ ↦ v) z
  have hfc : Continuous f :=
    continuous_of_continuousOn_of_eq_zero W.isOpen hK.isClosed hKW hf.continuousOn hfK
  have hpK : ∀ z ∉ K, f z ^ (n + 1) = 0 := fun z hz ↦ by simp [hfK z hz]
  have hpsupp : tsupport (fun z ↦ f z ^ (n + 1)) ⊆ K :=
    closure_minimal (fun z hz ↦ by_contra fun h ↦ hz (hpK z h)) hK.isClosed
  have hlim := hFT (fun z ↦ f z ^ (n + 1)) (hfc.pow _) (HasCompactSupport.intro hK hpK)
    (hpsupp.trans hKW)
  have hε : ∀ ε : ℝ, 0 < ε → ∫ z, f z ^ (n + 1) ∂μ ≤ (1 + ε) ^ n * (n + 1)! * R := by
    intro ε hε
    have hev : ∀ᶠ k in atTop, ∀ i, ∀ z ∈ K, F i k z < ε := by
      rw [eventually_all]
      intro i
      exact eventually_forall_lt_of_antitone hK
        (fun k ↦ ((hF.1 i).1 k).1.continuousOn.mono hKW) (fun z hz ↦ (hF.1 i).2.1 z (hKW hz))
        fun z hz ↦ ((hF.1 i).2.2.1 z (hKW hz)).eventually_lt_const (by linarith [(hu i z hz).2])
    refine le_of_tendsto hlim (hev.mono fun k hk ↦ ?_)
    have := integral_pow_mul_mixedDensity_le_iterate hK hKW hf hfK hf0 hw hv hfwv
      (u := fun i ↦ F i k) (fun i ↦ (hF.1 i).1 k) (c := fun _ ↦ ε) (M := 1 + ε) (by linarith)
      fun i z hz ↦ ⟨by linarith [(hu i z hz).1, (hF.1 i).le_of_mem (hKW hz) k], (hk i z hz).le⟩
    exact this
  have ht : Tendsto (fun ε : ℝ ↦ (1 + ε) ^ n * (n + 1)! * R) (𝓝[>] 0)
      (𝓝 ((1 + 0) ^ n * (n + 1)! * R)) :=
    ((((continuous_const.add continuous_id).pow n).mul continuous_const).mul
      continuous_const).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  simp only [add_zero, one_pow, one_mul] at ht
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε' ↦ hε ε hε')

/-- **Błocki's inequality** (Theorem 2.1.8, (2.1.5) with `p = n + 1`). Let `μ` be the
Bedford–Taylor limit of a tuple with `-1 ≤ uᵢ ≤ 0` on the compact set `K`, and `G` a
decreasing smooth approximation of `v` whose members all agree off `K`, with `ν` the
Bedford–Taylor limit of `(v, …, v)`. Then for every `j`,
`∫_K (G_j - v)ⁿ⁺¹ dμ ≤ (n + 1)! ∫_K (G_j - v) dν`. -/
theorem blocki_inequality {V : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → ℝ}
    {μ : Measure (ComplexModel n)} (hμ : IsBTLimit V u μ) {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKV : K ⊆ V) (hu : ∀ i, ∀ z ∈ K, -1 ≤ u i z ∧ u i z ≤ 0)
    {v : ComplexModel n → ℝ} {G : ℕ → ComplexModel n → ℝ} (hG : IsDecApprox V v G)
    (hGK : ∀ k, ∀ z ∈ V, z ∉ K → G k z = G 0 z) {ν : Measure (ComplexModel n)}
    (hν : IsBTLimit V (fun _ ↦ v) ν) (j : ℕ) :
    ∫ z in K, (G j z - v z) ^ (n + 1) ∂μ ≤ (n + 1)! * ∫ z in K, (G j z - v z) ∂ν := by
  classical
  obtain ⟨W0, hW0o, hKW0, hW0V, hW0c⟩ :=
    exists_open_between_and_isCompact_closure hK V.isOpen hKV
  set W : Opens (ComplexModel n) := ⟨W0, hW0o⟩ with hW_def
  have hW : RelativelyCompactIn W V := ⟨hW0c, hW0V⟩
  have hWV : W ≤ V := subset_closure.trans hW0V
  have hKW : K ⊆ W := hKW0
  have hGW : IsDecApprox W v G := hG.mono hWV
  have hvK : ∀ z ∈ V, z ∉ K → v z = G 0 z := fun z hz hzK ↦
    tendsto_nhds_unique (hG.2.2.1 z hz)
      (tendsto_const_nhds.congr fun k ↦ (hGK k z hz hzK).symm)
  -- the smooth comparison functions
  set f : ℕ → ComplexModel n → ℝ := fun k z ↦ if z ∈ W then G j z - G k z else 0 with hf_def
  have hineq (k : ℕ) (hk : j ≤ k) :
      ∫ z, f k z ^ (n + 1) ∂μ ≤ (n + 1)! * ∫ z, f k z * mixedDensity (fun _ ↦ G k) z := by
    refine integral_pow_le_of_isBTLimit_of_smooth hW hK hKW hμ hu (w := G j) ?_ ?_ ?_
      (hGW.1 j) (hGW.1 k) fun z hz ↦ ite_eq_left hz
    · exact ((hGW.1 j).1.sub (hGW.1 k).1).congr fun z hz ↦ ite_eq_left hz
    · intro z hzK
      by_cases hzW : z ∈ W
      · simp only [hf_def, ite_eq_left hzW, hGK j z (hWV hzW) hzK, hGK k z (hWV hzW) hzK, sub_self]
      · simp [hf_def, hzW]
    · intro z
      by_cases hzW : z ∈ W
      · simp only [hf_def, ite_eq_left hzW, sub_nonneg]; exact hG.2.1 z (hWV hzW) hk
      · simp [hf_def, hzW]
  -- the left side
  have hLeq (k : ℕ) : ∫ z, f k z ^ (n + 1) ∂μ = ∫ z in K, (G j z - G k z) ^ (n + 1) ∂μ := by
    rw [← integral_indicator hK.measurableSet]
    congr 1; funext z
    by_cases hzK : z ∈ K
    · simp [hf_def, hzK, show z ∈ W from hKW hzK]
    · rw [indicator_of_notMem hzK]
      by_cases hzW : z ∈ W
      · simp [hf_def, hzW, hGK j z (hWV hzW) hzK, hGK k z (hWV hzW) hzK]
      · simp [hf_def, hzW]
  obtain ⟨C, hC⟩ := hG.exists_abs_le hK hKV
  have : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.2 (hμ.2.1 K hK hKV).ne
  have hL : Tendsto (fun k ↦ ∫ z, f k z ^ (n + 1) ∂μ) atTop
      (𝓝 (∫ z in K, (G j z - v z) ^ (n + 1) ∂μ)) := by
    simp only [hLeq]
    refine tendsto_integral_of_dominated_convergence (fun _ ↦ (2 * C) ^ (n + 1)) (fun k ↦ ?_)
      (integrable_const _) (fun k ↦ ?_) ?_
    · exact ((((hG.1 j).1.continuousOn.mono hKV).sub ((hG.1 k).1.continuousOn.mono hKV)).pow
        _).aestronglyMeasurable hK.measurableSet
    · filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
      rw [norm_pow, Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans
        (by linarith [hC j z hz, hC k z hz])) _
    · filter_upwards [ae_restrict_mem hK.measurableSet] with z hz
      exact (tendsto_const_nhds.sub (hG.2.2.1 z (hKV hz))).pow _
  -- the right side
  obtain ⟨χ, hχ1, hχ01⟩ := exists_testFunction_eq_one_nhds_compact (Ω := W) hK hKW
  have hχK : ∀ z ∈ K, χ z = 1 := fun z hz ↦ (hχ1.filter_mono (nhds_le_nhdsSet hz)).self_of_nhds
  have hχW : ∀ z ∉ W, χ z = 0 := fun z hz ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ hz (χ.tsupport_subset h)
  have hDc (k : ℕ) : ContinuousOn (mixedDensity fun _ : Fin n ↦ G k) W :=
    continuousOn_mixedDensity fun _ ↦ (hGW.1 k).1
  have hIk (a k : ℕ) : Integrable fun z ↦ χ z * G a z * mixedDensity (fun _ ↦ G k) z := by
    have := integrable_mul_of_continuousOn (D := fun z ↦ G a z * mixedDensity (fun _ ↦ G k) z)
      ((hGW.1 a).1.continuousOn.mul (hDc k)) χ.continuous χ.hasCompactSupport χ.tsupport_subset
    simpa only [mul_assoc] using this
  have hReq (k : ℕ) : ∫ z, f k z * mixedDensity (fun _ ↦ G k) z =
      (∫ z, χ z * G j z * mixedDensity (fun _ ↦ G k) z) -
        ∫ z, χ z * G k z * mixedDensity (fun _ ↦ G k) z := by
    rw [← integral_sub (hIk j k) (hIk k k)]
    congr 1; funext z
    by_cases hzW : z ∈ W
    · by_cases hzK : z ∈ K
      · simp only [hf_def, ite_eq_left hzW, hχK z hzK]; ring
      · have e : G j z = G k z := by rw [hGK j z (hWV hzW) hzK, hGK k z (hWV hzW) hzK]
        simp only [hf_def, ite_eq_left hzW, e]; ring
    · simp [hf_def, hzW, hχW z hzW]
  have hadm : IsAdmissible n W (fun _ ↦ v) (fun _ ↦ G) :=
    ⟨fun _ ↦ hGW, fun i hi ↦ absurd i.isLt (not_lt.mpr hi)⟩
  have hφ : Continuous fun z ↦ χ z * G j z :=
    continuous_of_continuousOn_of_eq_zero W.isOpen (isClosed_tsupport χ) χ.tsupport_subset
      (χ.continuous.continuousOn.mul (hGW.1 j).1.continuousOn)
      fun z hz ↦ by simp [image_eq_zero_of_notMem_tsupport hz]
  have hT1 := hν.tendstoMixed hW hadm (fun z ↦ χ z * G j z) hφ χ.hasCompactSupport.mul_right
    ((tsupport_mul_subset_left).trans χ.tsupport_subset)
  have hWc : (ν.restrict W) (W : Set (ComplexModel n))ᶜ = 0 := by
    rw [Measure.restrict_apply' W.isOpen.measurableSet]; simp
  have hWf : ∀ K', IsCompact K' → K' ⊆ W → (ν.restrict W) K' < ⊤ := fun K' hK' hK'W ↦
    (Measure.restrict_apply_le _ _).trans_lt (hν.2.1 K' hK' (hK'W.trans hWV))
  have hT2 := wClaim_of_pClaim (pClaim_all (n := n)) W (fun _ ↦ v) (ν.restrict W) hWc hWf
    (fun F hF ↦ hν.tendstoMixed_restrict hW hF) _ hadm v G hGW χ χ.continuous
    χ.hasCompactSupport χ.tsupport_subset
  have hνfin : ∀ K', IsCompact K' → K' ⊆ W → ν K' < ⊤ := fun K' hK' hK'W ↦
    hν.2.1 K' hK' (hK'W.trans hWV)
  have hlimR : (∫ z, χ z * G j z ∂ν) - ∫ z, χ z * v z ∂(ν.restrict W) =
      ∫ z in K, (G j z - v z) ∂ν := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ by simp [hχW z hz],
      ← integral_sub (integrable_of_tsupport_subset hνfin hφ χ.hasCompactSupport.mul_right
        ((tsupport_mul_subset_left).trans χ.tsupport_subset))
        (hGW.integrable_mul hνfin χ.continuous χ.hasCompactSupport χ.tsupport_subset),
      ← integral_indicator hK.measurableSet]
    congr 1; funext z
    by_cases hzK : z ∈ K
    · simp [hzK, hχK z hzK]
    · rw [indicator_of_notMem hzK]
      by_cases hzW : z ∈ W
      · rw [hvK z (hWV hzW) hzK, hGK j z (hWV hzW) hzK]; ring
      · simp [hχW z hzW]
  have hR : Tendsto (fun k ↦ (n + 1)! * ∫ z, f k z * mixedDensity (fun _ ↦ G k) z) atTop
      (𝓝 ((n + 1)! * ∫ z in K, (G j z - v z) ∂ν)) := by
    simp only [hReq]
    rw [← hlimR]
    exact (hT1.sub hT2).const_mul _
  exact le_of_tendsto_of_tendsto hL hR (eventually_atTop.2 ⟨j, fun k hk ↦ hineq k hk⟩)

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
