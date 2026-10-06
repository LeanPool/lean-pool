/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblyPressureScaling
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitAssemblySourceAE
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupTimeAE
public import LeanPool.EscauriazaSereginSverak.Endpoint.PressureSplitRemainder
public import LeanPool.CaffarelliKohnNirenberg.Leray.RieszPressurePackageDistribution
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Harmonic.Liouville

/-!
# The rescaled whole-space pressure is the pressure of the rescaled tensor

The rescaled fixed pressure p₁^k of `prop:blowup-limit` equals the
whole-space Riesz pressure of the rescaled velocity tensor v^k ⊗ v^k
(`lem:pressure-split`). On almost every time slice both solve the same
Poisson equation in all of space and lie in L^(3/2), so their difference
is a harmonic L^(3/2) function and vanishes by the Liouville theorem.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

private instance blowupLimitAssemblyPressure_holder :
    ENNReal.HolderTriple (ENNReal.ofReal (3 / 2 : ℝ)) 3 1 := by
  have hreal : Real.HolderTriple (3 / 2) 3 1 := ⟨by norm_num, by norm_num, by norm_num⟩
  simpa only [ENNReal.ofReal_ofNat, ENNReal.ofReal_one] using hreal.ennrealOfReal

/-- Slicewise almost-everywhere equality of a strongly measurable and a
measurable scalar space-time field gives space-time almost-everywhere
equality. -/
theorem blowupLimitAssemblyPressure_ae_eq_of_slices
    {A B : Vec3 × ℝ → ℝ} (hA : AEStronglyMeasurable A volume) (hB : Measurable B)
    (h : ∀ᵐ t ∂(volume : Measure ℝ),
      (fun x => A (x, t)) =ᵐ[(volume : Measure Vec3)] (fun x => B (x, t))) :
    A =ᵐ[volume] B := by
  have hvol : (volume : Measure (Vec3 × ℝ)) =
      (volume : Measure Vec3).prod (volume : Measure ℝ) := Measure.volume_eq_prod _ _
  obtain ⟨Am, hAmMeas, hAm⟩ : ∃ Am : Vec3 × ℝ → ℝ, Measurable Am ∧ A =ᵐ[volume] Am :=
    ⟨hA.mk A, hA.stronglyMeasurable_mk.measurable, hA.ae_eq_mk⟩
  have hslices : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ x ∂(volume : Measure Vec3),
      A (x,t) = Am (x,t) := by
    have hprod : ∀ᵐ z ∂((volume : Measure Vec3).prod (volume : Measure ℝ)),
        A z = Am z := by
      rw [← hvol]
      exact hAm
    exact blowupLimitAssembly_ae_ae_of_ae_prod_swap hprod
  have hset : MeasurableSet {z : Vec3 × ℝ | Am z = B z} :=
    measurableSet_eq_fun hAmMeas hB
  have hmB : Am =ᵐ[volume] B := by
    rw [Filter.EventuallyEq, hvol, Measure.ae_prod_iff_ae_ae hset]
    refine (Measure.ae_ae_comm (p := fun x t => Am (x,t) = B (x,t)) hset).2 ?_
    filter_upwards [h, hslices] with t ht hts
    filter_upwards [ht, hts] with x hx hxs
    rw [← hxs, hx]
  exact hAm.trans hmB

/-- An L^p function composed with a positive spatial dilation and
translation stays in L^p. -/
theorem blowupLimitAssemblyPressure_memLp_comp_affine
    {g : Vec3 → ℝ} {p : ℝ≥0∞} (hg : MemLp g p volume) (x₀ : Vec3) {r : ℝ}
    (hr : 0 < r) :
    MemLp (fun x : Vec3 => g (x₀ + r • x)) p volume := by
  have hmap := map_scalingSpace r hr x₀
  have hmeas : Measurable (scalingSpace r x₀) := by
    change Measurable (fun y : Vec3 => x₀ + r • y)
    fun_prop
  have hgmap : MemLp g p (Measure.map (scalingSpace r x₀) volume) := by
    rw [hmap]
    exact hg.smul_measure ENNReal.ofReal_ne_top
  exact hgmap.comp_of_map hmeas.aemeasurable

/-- A scalar field in L^(3/2) of space pairs integrably with the Laplacian
of a compactly supported smooth test. -/
theorem blowupLimitAssemblyPressure_integrable_mul_laplacian
    {h : Vec3 → ℝ} (hh : MemLp h (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    Integrable (fun x => h x * CKN.spatialLaplacian ψ x) := by
  have hlapSmooth : ContDiff ℝ (⊤ : ℕ∞) (CKN.spatialLaplacian ψ) := by
    unfold CKN.spatialLaplacian
    apply ContDiff.sum
    intro i _
    exact CKN.contDiff_spatialDeriv_smooth (CKN.contDiff_spatialDeriv_smooth hψ i) i
  have hlapc : HasCompactSupport (CKN.spatialLaplacian ψ) := by
    have hdc : ∀ {f : Vec3 → ℝ}, HasCompactSupport f → ∀ k : Fin 3,
        HasCompactSupport (CKN.spatialDeriv f k) :=
      fun hf k => hf.fderiv_apply (𝕜 := ℝ) (CKN.basisVec k)
    change HasCompactSupport (fun x => ∑ k : Fin 3,
      CKN.spatialDeriv (CKN.spatialDeriv ψ k) k x)
    convert (hdc (hdc hψc 0) 0).add ((hdc (hdc hψc 1) 1).add (hdc (hdc hψc 2) 2))
      using 1
    funext x
    simp [Fin.sum_univ_succ, Pi.add_apply]
  have hlapLp : MemLp (CKN.spatialLaplacian ψ) 3 volume :=
    hlapSmooth.continuous.memLp_of_hasCompactSupport hlapc
  exact hh.integrable_mul hlapLp

/-- Two L^(3/2) solutions of the same whole-space pressure Poisson
equation agree almost everywhere. -/
theorem blowupLimitAssemblyPressure_poisson_unique
    {A B : Vec3 → ℝ} {F : Fin 3 → Fin 3 → Vec3 → ℝ}
    (hA : MemLp A (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (hB : MemLp B (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (hAeq : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ x, A x * (-CKN.spatialLaplacian ψ x) =
        ∑ i : Fin 3, ∑ j : Fin 3, ∫ x, F i j x * CKN.mixedSecond ψ i j x)
    (hBeq : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ x, B x * (-CKN.spatialLaplacian ψ x) =
        ∑ i : Fin 3, ∑ j : Fin 3, ∫ x, F i j x * CKN.mixedSecond ψ i j x) :
    A =ᵐ[volume] B := by
  let H : Vec3 → ℝ := fun x => A x - B x
  have hH : MemLp H (ENNReal.ofReal (3 / 2 : ℝ)) volume := hA.sub hB
  have hweak : CKN.Foundation.Heat.WeaklyHarmonicOn Set.univ H := by
    intro ψ hψ hψc _
    rw [Measure.restrict_univ]
    have hIA := blowupLimitAssemblyPressure_integrable_mul_laplacian hA hψ hψc
    have hIB := blowupLimitAssemblyPressure_integrable_mul_laplacian hB hψ hψc
    have h1 := hAeq ψ hψ hψc
    have h2 := hBeq ψ hψ hψc
    have hnegA : ∫ x, A x * (-CKN.spatialLaplacian ψ x) =
        -∫ x, A x * CKN.spatialLaplacian ψ x := by
      rw [← integral_neg]
      congr 1
      funext x
      ring
    have hnegB : ∫ x, B x * (-CKN.spatialLaplacian ψ x) =
        -∫ x, B x * CKN.spatialLaplacian ψ x := by
      rw [← integral_neg]
      congr 1
      funext x
      ring
    have hsub : ∫ x, H x * CKN.spatialLaplacian ψ x =
        (∫ x, A x * CKN.spatialLaplacian ψ x) -
          ∫ x, B x * CKN.spatialLaplacian ψ x := by
      rw [← integral_sub hIA hIB]
      congr 1
      funext x
      simp only [H]
      ring
    rw [hsub]
    linarith only [h1, h2, hnegA, hnegB]
  set C : ℝ := lpNorm H (ENNReal.ofReal (3 / 2 : ℝ)) volume
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  have hzero := CKN.Foundation.Heat.weaklyHarmonicOn_eq_zero_of_lpNorm_linear_growth
    hC (fun ρ _ => hH.restrict _) hweak (by
      intro ρ hρ
      have hle : lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (CKN.euclideanBall (0 : Vec3) ρ)) ≤ C := by
        unfold lpNorm
        exact ENNReal.toReal_mono hH.eLpNorm_ne_top
          (eLpNorm_mono_measure _ Measure.restrict_le_self)
      calc
        lpNorm H (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (CKN.euclideanBall (0 : Vec3) ρ)) ≤ C := hle
        _ = C * 1 := (mul_one C).symm
        _ ≤ C * (1 + ρ) := mul_le_mul_of_nonneg_left (by linarith only [hρ]) hC)
  filter_upwards [hzero] with x hx
  have hx' : A x - B x = 0 := hx
  linarith only [hx']

/-- The rescaled fixed whole-space pressure is, almost everywhere, the
whole-space Riesz pressure of the tensor of the rescaled zero-extended
velocity (`lem:pressure-split`, used in `prop:blowup-limit`). -/
theorem blowupLimitAssemblyPressure_riesz_rescale
    (u : ParabolicPoint → Vec3)
    (hF : ∀ i j, MemLp (pressureSplitTensor u i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)))
    (hp₁ : AEStronglyMeasurable (pressureSplitRieszPressure (pressureSplitTensor u) hF)
      (volume.restrict (Set.univ ×ˢ Ioo (-1 : ℝ) 0)))
    (Mₚ : ℝ≥0∞) (hMₚ : Mₚ < ⊤)
    (hsourceP : ∀ᵐ s ∂volume.restrict (Ioo (-1 : ℝ) 0),
      AEStronglyMeasurable (fun x : Vec3 =>
        pressureSplitRieszPressure (pressureSplitTensor u) hF (x,s)) volume ∧
      eLpNorm (fun x : Vec3 =>
        pressureSplitRieszPressure (pressureSplitTensor u) hF (x,s))
        (3 / 2 : ℝ≥0∞) volume ≤ Mₚ)
    (x₀ : Vec3) (t₀ r : ℝ) (hr : 0 < r)
    (hv : ∀ i j, MemLp (fun z : Vec3 × ℝ =>
      blowupVelocity x₀ t₀ r u z i * blowupVelocity x₀ t₀ r u z j)
      (ENNReal.ofReal (3 / 2 : ℝ)) volume) :
    (fun z : Vec3 × ℝ => blowupRieszPressure x₀ t₀ r
        (pressureSplitRieszPressure (pressureSplitTensor u) hF) z) =ᵐ[volume]
      CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num)
        (fun i j z => blowupVelocity x₀ t₀ r u z i * blowupVelocity x₀ t₀ r u z j) hv := by
  set F := pressureSplitTensor u with hFdef0
  set P0 := CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) F hF with hP0def
  set v := blowupVelocity x₀ t₀ r u with hvdef
  set Fr : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j z => v z i * v z j with hFrdef
  set Pr := CKN.Leray.rieszPressureSpaceTime (3 / 2 : ℝ) (by norm_num) Fr hv with hPrdef
  have hFdef : ∀ i j (z : Vec3 × ℝ), F i j z =
      goodPointDomain.indicator (fun q : ParabolicPoint => u q i * u q j) z :=
    fun i j z => rfl
  have hFr : ∀ (x : Vec3) (t : ℝ) (i j : Fin 3),
      Fr i j (x,t) = r ^ 2 * F i j (x₀ + r • x, t₀ + r ^ 2 * t) := by
    intro x t i j
    let w : ParabolicPoint := (x₀ + r • x, t₀ + r ^ 2 * t)
    have hvw : v (x,t) = r • goodPointDomain.indicator u w := rfl
    have hFw : F i j (x₀ + r • x, t₀ + r ^ 2 * t) =
        goodPointDomain.indicator (fun q : ParabolicPoint => u q i * u q j) w := rfl
    change v (x,t) i * v (x,t) j = r ^ 2 * F i j (x₀ + r • x, t₀ + r ^ 2 * t)
    rw [hvw, hFw]
    by_cases hmem : w ∈ goodPointDomain
    · rw [indicator_of_mem hmem, indicator_of_mem hmem]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    · rw [indicator_of_notMem hmem, indicator_of_notMem hmem]
      simp
  have hAin : ∀ (x : Vec3) (t : ℝ), t₀ + r ^ 2 * t ∈ Ioo (-1 : ℝ) 0 →
      blowupRieszPressure x₀ t₀ r (pressureSplitRieszPressure F hF) (x,t) =
        r ^ 2 * P0 (x₀ + r • x, t₀ + r ^ 2 * t) := by
    intro x t hτ
    simp only [blowupRieszPressure, parabolicRescalePressure, blowupTimeExtendedPressure,
      parabolicTranslate, parabolicScale]
    rw [indicator_of_mem hτ]
    rfl
  have hAout : ∀ (x : Vec3) (t : ℝ), t₀ + r ^ 2 * t ∉ Ioo (-1 : ℝ) 0 →
      blowupRieszPressure x₀ t₀ r (pressureSplitRieszPressure F hF) (x,t) = 0 := by
    intro x t hτ
    simp only [blowupRieszPressure, parabolicRescalePressure, blowupTimeExtendedPressure,
      parabolicTranslate, parabolicScale]
    rw [indicator_of_notMem hτ, mul_zero]
  let Q : ℝ → Prop := fun τ =>
    (τ ∈ Ioo (-1 : ℝ) 0 → MemLp (fun x : Vec3 => P0 (x,τ)) (ENNReal.ofReal (3 / 2 : ℝ))
      volume) ∧
    (∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∫ x, P0 (x,τ) * (-CKN.spatialLaplacian ψ x) =
        ∑ i : Fin 3, ∑ j : Fin 3, ∫ x, F i j (x,τ) * CKN.mixedSecond ψ i j x)
  have hQ : ∀ᵐ τ ∂(volume : Measure ℝ), Q τ := by
    have h1 := (ae_restrict_iff' measurableSet_Ioo).1 hsourceP
    have h2 := CKN.Leray.rieszPressureSpaceTime_slice_laplacian_identity
      (3 / 2 : ℝ) (by norm_num) F hF
    filter_upwards [h1, h2] with τ hτ1 hτ2
    refine ⟨fun hmem => ?_, hτ2⟩
    rw [memLp_iff, CKN.ofReal_threeHalves]
    exact lt_of_le_of_lt (hτ1 hmem).2 hMₚ
  have hQt : ∀ᵐ t ∂(volume : Measure ℝ), Q (t₀ + r ^ 2 * t) := by
    have hQ' : ∀ᵐ τ ∂(volume.restrict (Set.univ : Set ℝ)), Q τ := by
      rw [Measure.restrict_univ]
      exact hQ
    have h := blowup_ae_time_pullback r t₀ hr Set.univ MeasurableSet.univ Q hQ'
    have huniv : CKN.rescaledTime r t₀ (Set.univ : Set ℝ) = Set.univ := preimage_univ
    rw [huniv, Measure.restrict_univ] at h
    exact h
  have hIr := CKN.Leray.rieszPressureSpaceTime_slice_laplacian_identity
    (3 / 2 : ℝ) (by norm_num) Fr hv
  have hSr := CKN.Leray.rieszPressureSpaceTime_slice_ae_eq (3 / 2 : ℝ) (by norm_num) Fr hv
  have hAaesm : AEStronglyMeasurable (fun z : Vec3 × ℝ =>
      blowupRieszPressure x₀ t₀ r (pressureSplitRieszPressure F hF) z) volume :=
    blowupRieszPressure_aestronglyMeasurable _ hp₁ x₀ t₀ r hr
  apply blowupLimitAssemblyPressure_ae_eq_of_slices hAaesm
    (CKN.Leray.rieszPressureSpaceTime_measurable _ _ Fr hv)
  filter_upwards [hQt, hIr, hSr] with t hQ' hIr' hSr'
  obtain ⟨hFt, hPrSlice⟩ := hSr'
  have hBmem : MemLp (fun x : Vec3 => Pr (x,t)) (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
    (Lp.memLp _).ae_eq hPrSlice.symm
  by_cases hτ : t₀ + r ^ 2 * t ∈ Ioo (-1 : ℝ) 0
  · have hAt : (fun x : Vec3 =>
        blowupRieszPressure x₀ t₀ r (pressureSplitRieszPressure F hF) (x,t)) =
        fun x => r ^ 2 * P0 (x₀ + r • x, t₀ + r ^ 2 * t) := by
      funext x
      exact hAin x t hτ
    rw [hAt]
    have hPmem : MemLp (fun x : Vec3 => P0 (x₀ + r • x, t₀ + r ^ 2 * t))
        (ENNReal.ofReal (3 / 2 : ℝ)) volume :=
      blowupLimitAssemblyPressure_memLp_comp_affine (g := fun y => P0 (y, t₀ + r ^ 2 * t))
        (hQ'.1 hτ) x₀ hr
    apply blowupLimitAssemblyPressure_poisson_unique (F := fun i j x => Fr i j (x,t))
      (hPmem.const_mul (r ^ 2)) hBmem
    · intro ψ hψ hψc
      have hres := blowupLimitAssemblyPressure_poisson_rescale
        (P := fun y => P0 (y, t₀ + r ^ 2 * t))
        (F := fun i j y => F i j (y, t₀ + r ^ 2 * t)) hQ'.2 x₀ hr ψ hψ hψc
      simp only [hFr]
      exact hres
    · exact hIr'
  · have hAt : (fun x : Vec3 =>
        blowupRieszPressure x₀ t₀ r (pressureSplitRieszPressure F hF) (x,t)) =
        fun _ => (0 : ℝ) := by
      funext x
      exact hAout x t hτ
    have hF0 : ∀ i j (x : Vec3), Fr i j (x,t) = 0 := by
      intro i j x
      let w : ParabolicPoint := (x₀ + r • x, t₀ + r ^ 2 * t)
      have hFw : F i j (x₀ + r • x, t₀ + r ^ 2 * t) =
          goodPointDomain.indicator (fun q : ParabolicPoint => u q i * u q j) w := rfl
      have hnot : w ∉ goodPointDomain := fun hmem => hτ hmem.2
      rw [hFr, hFw, indicator_of_notMem hnot, mul_zero]
    rw [hAt]
    apply blowupLimitAssemblyPressure_poisson_unique (F := fun i j x => Fr i j (x,t))
      (by simp) hBmem
    · intro ψ _ _
      simp [hF0]
    · exact hIr'

end ESS

end
