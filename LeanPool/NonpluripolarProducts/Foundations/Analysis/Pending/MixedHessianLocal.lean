/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MixedHessianDivergence
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.DistributionRegularization
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalTwoFormPoincare
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MixedCoefficientPositivity

/-!
# Localized integration by parts for mixed complex Hessians

The global identity `∫ a·C(ddᶜb, ddᶜg…) = ∫ b·C(ddᶜa, ddᶜg…)` holds as soon as
all functions are smooth on an open set containing the compact support of `a`:
a cutoff equal to one near that support makes everything global without
changing either integrand.
-/

@[expose] public section

open Set Filter Complex MeasureTheory TopologicalSpace
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.MixedHessian

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

noncomputable section

variable {m : ℕ}

/-- The mixed coefficient with first slot `ddᶜ a` and remaining slots `ddᶜ gᵢ`. -/
def mixedC (a : ComplexModel (m + 1) → ℝ) (g : Fin m → ComplexModel (m + 1) → ℝ)
    (z : ComplexModel (m + 1)) : ℂ :=
  mixedCoefficient (Fin.cons (complexHessian a z) (fun i ↦ complexHessian (g i) z) :
    Fin (m + 1) → Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ)

theorem complexHessian_congr {n : ℕ} {f g : ComplexModel n → ℝ} {z : ComplexModel n}
    (h : f =ᶠ[𝓝 z] g) : complexHessian f z = complexHessian g z := by
  have h2 : iteratedFDeriv ℝ 2 f z = iteratedFDeriv ℝ 2 g z := (h.iteratedFDeriv ℝ 2).self_of_nhds
  ext j k
  simp [complexHessian, realHessian, h2]

theorem mixedC_congr {a a' : ComplexModel (m + 1) → ℝ} {g g' : Fin m → ComplexModel (m + 1) → ℝ}
    {z : ComplexModel (m + 1)} (ha : a =ᶠ[𝓝 z] a') (hg : ∀ i, g i =ᶠ[𝓝 z] g' i) :
    mixedC a g z = mixedC a' g' z := by
  simp only [mixedC, complexHessian_congr ha, fun i ↦ complexHessian_congr (hg i)]

theorem mixedC_eq_zero_of_notMem_tsupport {a : ComplexModel (m + 1) → ℝ}
    {g : Fin m → ComplexModel (m + 1) → ℝ} {z : ComplexModel (m + 1)} (hz : z ∉ tsupport a) :
    mixedC a g z = 0 :=
  mixedCoefficient_cons_eq_zero_of_notMem_tsupport hz

theorem contDiff_of_contDiffOn_of_tsupport_subset {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {V : Set E} (hV : IsOpen V) {a : E → ℝ} (ha : ContDiffOn ℝ ∞ a V)
    (haV : tsupport a ⊆ V) : ContDiff ℝ ∞ a := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ V
  · exact ha.contDiffAt (hV.mem_nhds hx)
  · have hx' : x ∉ tsupport a := fun h ↦ hx (haV h)
    have hev : a =ᶠ[𝓝 x] fun _ ↦ 0 := by
      filter_upwards [(isClosed_tsupport a).isOpen_compl.mem_nhds hx'] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- **Localized integration by parts.** All functions smooth on an open set
`V` containing the compact support of `a`. -/
theorem integral_mul_mixedC_swap_of_contDiffOn {V : Set (ComplexModel (m + 1))} (hV : IsOpen V)
    {g : Fin m → ComplexModel (m + 1) → ℝ} (hg : ∀ i, ContDiffOn ℝ ∞ (g i) V)
    {a b : ComplexModel (m + 1) → ℝ} (ha : ContDiffOn ℝ ∞ a V) (hb : ContDiffOn ℝ ∞ b V)
    (hac : HasCompactSupport a) (haV : tsupport a ⊆ V) :
    ∫ z, (a z : ℂ) * mixedC b g z = ∫ z, (b z : ℂ) * mixedC a g z := by
  obtain ⟨χ, hχ1, -⟩ := exists_testFunction_eq_one_nhds_compact (Ω := ⟨V, hV⟩) hac haV
  have hχs : ContDiff ℝ ∞ (χ : ComplexModel (m + 1) → ℝ) := χ.contDiff
  have hχV : tsupport (χ : ComplexModel (m + 1) → ℝ) ⊆ V := χ.tsupport_subset
  have ha' : ContDiff ℝ ∞ a := contDiff_of_contDiffOn_of_tsupport_subset hV ha haV
  have hb' : ContDiff ℝ ∞ (fun y ↦ χ y • b y) :=
    _root_.SGPT.Foundations.Analysis.Pending.LocalPotentials.contDiff_smul_of_tsupport_subset
      hV hχs hχV hb
  have hg' (i : Fin m) : ContDiff ℝ ∞ (fun y ↦ χ y • g i y) :=
    _root_.SGPT.Foundations.Analysis.Pending.LocalPotentials.contDiff_smul_of_tsupport_subset
      hV hχs hχV (hg i)
  have h := integral_mul_mixedCoefficient_swap (g := fun i y ↦ χ y • g i y) hg' ha' hb' hac
  have hev (z : ComplexModel (m + 1)) (hz : z ∈ tsupport a) (f : ComplexModel (m + 1) → ℝ) :
      (fun y ↦ χ y • f y) =ᶠ[𝓝 z] f := by
    have : ∀ᶠ y in 𝓝 z, χ y = 1 := (hχ1.filter_mono (nhds_le_nhdsSet hz))
    filter_upwards [this] with y hy
    simp [hy]
  have hL : (fun z ↦ (a z : ℂ) * mixedC (fun y ↦ χ y • b y) (fun i y ↦ χ y • g i y) z) =
      fun z ↦ (a z : ℂ) * mixedC b g z := by
    funext z
    by_cases hz : z ∈ tsupport a
    · rw [mixedC_congr (hev z hz b) fun i ↦ hev z hz (g i)]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  have hR : (fun z ↦ ((χ z • b z : ℝ) : ℂ) * mixedC a (fun i y ↦ χ y • g i y) z) =
      fun z ↦ (b z : ℂ) * mixedC a g z := by
    funext z
    by_cases hz : z ∈ tsupport a
    · have hχz : χ z = 1 := (hχ1.filter_mono (nhds_le_nhdsSet hz)).self_of_nhds
      rw [mixedC_congr (EventuallyEq.refl _ a) fun i ↦ hev z hz (g i), hχz, one_smul]
    · simp [mixedC_eq_zero_of_notMem_tsupport hz]
  simp only [mixedC] at hL hR
  exact (congrArg _ hL).symm.trans (h.trans (congrArg _ hR))

theorem mixedC_add_left {a b : ComplexModel (m + 1) → ℝ} {g : Fin m → ComplexModel (m + 1) → ℝ}
    {z : ComplexModel (m + 1)} (ha : ContDiffAt ℝ 2 a z) (hb : ContDiffAt ℝ 2 b z) :
    mixedC (a + b) g z = mixedC a g z + mixedC b g z := by
  simp only [mixedC, mixedCoefficient_cons, complexHessian_add ha hb, Matrix.add_apply, add_mul,
    Finset.sum_add_distrib]

theorem integrableOn_of_continuous_of_isCompact_closure {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
    {f : E → ℂ} (hf : Continuous f) {W : Set E} (hW : IsCompact (closure W)) :
    IntegrableOn f W μ :=
  (hf.continuousOn.integrableOn_compact hW).mono_set subset_closure

/-- **Integration by parts over a region with a common collar.** If `a` and `b`
agree with `h` off a compact set `K ⊆ W`, then the two integrals over `W`
coincide; no boundary term appears. -/
theorem setIntegral_mul_mixedC_swap_collar {g : Fin m → ComplexModel (m + 1) → ℝ}
    (hg : ∀ i, ContDiff ℝ ∞ (g i)) {a b h : ComplexModel (m + 1) → ℝ} (ha : ContDiff ℝ ∞ a)
    (hb : ContDiff ℝ ∞ b) (hh : ContDiff ℝ ∞ h) {K W : Set (ComplexModel (m + 1))}
    (hK : IsCompact K) (hKW : K ⊆ W) (hWc : IsCompact (closure W))
    (hah : ∀ z ∉ K, a z = h z) (hbh : ∀ z ∉ K, b z = h z) :
    ∫ z in W, (a z : ℂ) * mixedC b g z = ∫ z in W, (b z : ℂ) * mixedC a g z := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  set s : ComplexModel (m + 1) → ℝ := a - h with hs
  set t : ComplexModel (m + 1) → ℝ := b - h with ht
  have hsm : ContDiff ℝ ∞ s := ha.sub hh
  have htm : ContDiff ℝ ∞ t := hb.sub hh
  have hsK : tsupport s ⊆ K := closure_minimal (fun z hz ↦ by
    by_contra hzK
    exact hz (by simp [hs, hah z hzK])) hK.isClosed
  have htK : tsupport t ⊆ K := closure_minimal (fun z hz ↦ by
    by_contra hzK
    exact hz (by simp [ht, hbh z hzK])) hK.isClosed
  have hsc : HasCompactSupport s := hK.of_isClosed_subset (isClosed_tsupport s) hsK
  have htc : HasCompactSupport t := hK.of_isClosed_subset (isClosed_tsupport t) htK
  have hMa (z) : mixedC a g z = mixedC s g z + mixedC h g z := by
    rw [← mixedC_add_left (hsm.contDiffAt.of_le h2) (hh.contDiffAt.of_le h2)]
    simp [hs]
  have hMb (z) : mixedC b g z = mixedC t g z + mixedC h g z := by
    rw [← mixedC_add_left (htm.contDiffAt.of_le h2) (hh.contDiffAt.of_le h2)]
    simp [ht]
  have hcont (f : ComplexModel (m + 1) → ℝ) (hf : ContDiff ℝ ∞ f) :
      Continuous (mixedC f g) := continuous_mixedCoefficient_cons hg hf
  have hco (f : ComplexModel (m + 1) → ℝ) (hf : ContDiff ℝ ∞ f) :
      Continuous (fun z ↦ (f z : ℂ)) := continuous_ofReal.comp hf.continuous
  have hI (f k : ComplexModel (m + 1) → ℝ) (hf : ContDiff ℝ ∞ f) (hk : ContDiff ℝ ∞ k) :
      IntegrableOn (fun z ↦ (f z : ℂ) * mixedC k g z) W :=
    integrableOn_of_continuous_of_isCompact_closure ((hco f hf).mul (hcont k hk)) hWc
  -- integrals of terms vanishing off `K` may be taken over the whole space
  have hglob {F : ComplexModel (m + 1) → ℂ} (hF : ∀ z ∉ K, F z = 0) :
      ∫ z in W, F z = ∫ z, F z :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ hF z fun hzK ↦ hz (hKW hzK)
  have hs0 (z) (hz : z ∉ K) : s z = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hz (hsK h)
  have ht0 (z) (hz : z ∉ K) : t z = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ hz (htK h)
  have hMs0 (z) (hz : z ∉ K) : mixedC s g z = 0 :=
    mixedC_eq_zero_of_notMem_tsupport fun h ↦ hz (hsK h)
  have hMt0 (z) (hz : z ∉ K) : mixedC t g z = 0 :=
    mixedC_eq_zero_of_notMem_tsupport fun h ↦ hz (htK h)
  have e1 : ∫ z in W, (s z : ℂ) * mixedC t g z = ∫ z in W, (t z : ℂ) * mixedC s g z := by
    rw [hglob fun z hz ↦ by simp [hs0 z hz], hglob fun z hz ↦ by simp [ht0 z hz]]
    exact integral_mul_mixedCoefficient_swap hg hsm htm hsc
  have e2 : ∫ z in W, (s z : ℂ) * mixedC h g z = ∫ z in W, (h z : ℂ) * mixedC s g z := by
    rw [hglob fun z hz ↦ by simp [hs0 z hz], hglob fun z hz ↦ by simp [hMs0 z hz]]
    exact integral_mul_mixedCoefficient_swap hg hsm hh hsc
  have e3 : ∫ z in W, (h z : ℂ) * mixedC t g z = ∫ z in W, (t z : ℂ) * mixedC h g z := by
    rw [hglob fun z hz ↦ by simp [hMt0 z hz], hglob fun z hz ↦ by simp [ht0 z hz]]
    exact (integral_mul_mixedCoefficient_swap hg htm hh htc).symm
  have hA : (fun z ↦ (a z : ℂ) * mixedC b g z) = fun z ↦
      ((s z : ℂ) * mixedC t g z + (s z : ℂ) * mixedC h g z) +
        ((h z : ℂ) * mixedC t g z + (h z : ℂ) * mixedC h g z) := by
    funext z; rw [hMb]; simp only [hs, Pi.sub_apply, ofReal_sub]; ring
  have hB : (fun z ↦ (b z : ℂ) * mixedC a g z) = fun z ↦
      ((t z : ℂ) * mixedC s g z + (h z : ℂ) * mixedC s g z) +
        ((t z : ℂ) * mixedC h g z + (h z : ℂ) * mixedC h g z) := by
    funext z; rw [hMa]; simp only [ht, Pi.sub_apply, ofReal_sub]; ring
  have hadd4 (F1 F2 F3 F4 : ComplexModel (m + 1) → ℂ) (h1 : IntegrableOn F1 W)
      (h2 : IntegrableOn F2 W) (h3 : IntegrableOn F3 W) (h4 : IntegrableOn F4 W) :
      ∫ z in W, (F1 z + F2 z) + (F3 z + F4 z) =
        ((∫ z in W, F1 z) + ∫ z in W, F2 z) + ((∫ z in W, F3 z) + ∫ z in W, F4 z) := by
    rw [integral_add (f := fun z ↦ F1 z + F2 z) (g := fun z ↦ F3 z + F4 z) (h1.add h2) (h3.add h4),
      integral_add h1 h2, integral_add h3 h4]
  rw [hA, hB, hadd4 _ _ _ _ (hI s t hsm htm) (hI s h hsm hh) (hI h t hh htm) (hI h h hh hh),
    hadd4 _ _ _ _ (hI t s htm hsm) (hI h s hh hsm) (hI t h htm hh) (hI h h hh hh), e1, e2, e3]

theorem mixedC_re_nonneg {a : ComplexModel (m + 1) → ℝ} {g : Fin m → ComplexModel (m + 1) → ℝ}
    {z : ComplexModel (m + 1)} (ha : (complexHessian a z).PosSemidef)
    (hg : ∀ i, (complexHessian (g i) z).PosSemidef) : 0 ≤ (mixedC a g z).re := by
  refine MixedMongeAmpere.mixedCoefficient_re_nonneg _ fun i ↦ ?_
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · simpa using ha
  · simpa using hg i

/-- **Comparison with a common collar.** Increasing the first Hessian slot
increases the weighted integral against a positive semidefinite weight: after
swapping the weight into the slot, positivity of the mixed coefficient applies. -/
theorem setIntegral_mul_mixedC_re_mono_collar {g : Fin m → ComplexModel (m + 1) → ℝ}
    (hg : ∀ i, ContDiff ℝ ∞ (g i)) {a b b' h : ComplexModel (m + 1) → ℝ}
    (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) (hb' : ContDiff ℝ ∞ b') (hh : ContDiff ℝ ∞ h)
    {K W : Set (ComplexModel (m + 1))} (hK : IsCompact K) (hKW : K ⊆ W) (hWm : MeasurableSet W)
    (hWc : IsCompact (closure W)) (hah : ∀ z ∉ K, a z = h z) (hbh : ∀ z ∉ K, b z = h z)
    (hb'h : ∀ z ∉ K, b' z = h z)
    (hapsd : ∀ z ∈ W, (complexHessian a z).PosSemidef)
    (hgpsd : ∀ i, ∀ z ∈ W, (complexHessian (g i) z).PosSemidef)
    (hle : ∀ z ∈ W, b z ≤ b' z) :
    ∫ z in W, a z * (mixedC b g z).re ≤ ∫ z in W, a z * (mixedC b' g z).re := by
  have hcont (f : ComplexModel (m + 1) → ℝ) (hf : ContDiff ℝ ∞ f) :
      Continuous (mixedC f g) := continuous_mixedCoefficient_cons hg hf
  have hI (f k : ComplexModel (m + 1) → ℝ) (hf : ContDiff ℝ ∞ f) (hk : ContDiff ℝ ∞ k) :
      IntegrableOn (fun z ↦ (f z : ℂ) * mixedC k g z) W :=
    integrableOn_of_continuous_of_isCompact_closure
      ((continuous_ofReal.comp hf.continuous).mul (hcont k hk)) hWc
  have hre (f k : ComplexModel (m + 1) → ℝ) (hf : ContDiff ℝ ∞ f) (hk : ContDiff ℝ ∞ k) :
      ∫ z in W, f z * (mixedC k g z).re = (∫ z in W, (f z : ℂ) * mixedC k g z).re := by
    have h1 := integral_re (hI f k hf hk)
    simpa [RCLike.re_to_complex, Complex.mul_re] using h1
  rw [hre a b ha hb, hre a b' ha hb', setIntegral_mul_mixedC_swap_collar hg ha hb hh hK hKW hWc
    hah hbh, setIntegral_mul_mixedC_swap_collar hg ha hb' hh hK hKW hWc hah hb'h,
    ← hre b a hb ha, ← hre b' a hb' ha]
  refine setIntegral_mono_on ?_ ?_ hWm fun z hz ↦ ?_
  · exact ((hI b a hb ha).re).congr (Eventually.of_forall fun z ↦ by simp)
  · exact ((hI b' a hb' ha).re).congr (Eventually.of_forall fun z ↦ by simp)
  · exact mul_le_mul_of_nonneg_right (hle z hz)
      (mixedC_re_nonneg (hapsd z hz) fun i ↦ hgpsd i z hz)

end

end SGPT.Foundations.Analysis.Pending.MixedHessian
