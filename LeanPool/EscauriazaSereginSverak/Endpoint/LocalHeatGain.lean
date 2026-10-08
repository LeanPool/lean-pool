/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalHeatGainCutoffs

/-!
# `lem:local-heat-gain`

Let `B_r ⋐ B_R` be concentric balls, `a < s < b`, and `m ∈ {1, 2}`. If
`z ∈ L²((a, b); H^m(B_R))` solves `∂ₜ z - Δ z = G` in distributions on
`B_R × (a, b)` with `G ∈ L²((a, b); H^{m-1}(B_R))`, then
`z ∈ C([s, b]; H^m(B_r)) ∩ L²((s, b); H^{m+1}(B_r))` with the estimate
`‖z‖_{C([s,b];H^m(B_r))} + ‖z‖_{L²((s,b);H^{m+1}(B_r))} ≤
  C (‖z‖_{L²((a,b);H^m(B_R))} + ‖G‖_{L²((a,b);H^{m-1}(B_R))})`,
where `C` depends only on `m`, `r`, `R`, `s - a` and `b - a`.

The proof multiplies by a cutoff `η` vanishing near `t = a` and outside a
compact subset of `B_R`. Each spatial derivative `∂^β (ηz)`, `|β| ≤ m`, solves
the heat equation on `ℝ³ × (a, b)` with a square-integrable source in source
or divergence form and has zero initial trace, so the energy estimate of
`lem:localized-vorticity-energy` applies. It gives a curve continuous in `L²`
and a square-integrable weak gradient. On `B_r × [s, b]` the cutoff equals
one.
-/

public section

open MeasureTheory Set Filter
open scoped Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

theorem real_sqrt_add_le_add_sqrt {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have h : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    have h1 := Real.sq_sqrt hx
    have h2 := Real.sq_sqrt hy
    nlinarith only [h1, h2, Real.sqrt_nonneg x, Real.sqrt_nonneg y,
      mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
  calc
    Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt x + Real.sqrt y :=
      Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- Almost everywhere equality on `B × I` gives almost everywhere equality of
almost every time slice. -/
theorem ae_slices_of_ae_prod {B : Set Vec3} {I : Set ℝ} {f g : Vec3 × ℝ → ℝ}
    (h : f =ᵐ[volume.restrict (B ×ˢ I)] g) :
    ∀ᵐ t ∂(volume.restrict I), (fun x => f (x, t)) =ᵐ[volume.restrict B] fun x => g (x, t) := by
  have hμ : (volume : Measure (Vec3 × ℝ)).restrict (B ×ˢ I) =
      (volume.restrict B).prod (volume.restrict I) := by
    rw [Measure.volume_eq_prod, Measure.prod_restrict]
  rw [hμ] at h
  have hs := (Measure.measurePreserving_swap (μ := volume.restrict I)
    (ν := volume.restrict B)).quasiMeasurePreserving.ae h
  exact Measure.ae_ae_of_ae_prod hs

/-- Distributional derivatives are insensitive to modification of the
function almost everywhere. -/
theorem IsSpaceTimeWeakPartial.congr_left {W : Set (Vec3 × ℝ)} {j : Fin 3}
    {f f' g : Vec3 × ℝ → ℝ} (h : IsSpaceTimeWeakPartial W j f g)
    (hf : f =ᵐ[volume.restrict W] f') : IsSpaceTimeWeakPartial W j f' g := by
  intro φ hφ hφc hφW
  rw [← h φ hφ hφc hφW]
  exact integral_congr_ae (hf.mono fun p hp => by simp only [hp])

private theorem localHeatGain_measurableFamilyRepresentative
    {n : ℕ} {W : Set (Vec3 × ℝ)} {F : List (Fin 3) → Vec3 × ℝ → ℝ}
    (hF : IsSpaceTimeFamily n W F) :
    ∃ Fm : List (Fin 3) → Vec3 × ℝ → ℝ,
      (∀ α, α.length ≤ n → F α =ᵐ[volume.restrict W] Fm α) ∧
      (∀ α, StronglyMeasurable (Fm α)) ∧ IsSpaceTimeFamily n W Fm := by
  let Fm : List (Fin 3) → Vec3 × ℝ → ℝ := fun α =>
    if h : α.length ≤ n then (hF.memL2 α h).aestronglyMeasurable.mk (F α) else fun _ => 0
  have hEq : ∀ α, α.length ≤ n → F α =ᵐ[volume.restrict W] Fm α := by
    intro α hα
    simp only [Fm, hα, ↓reduceDIte]
    exact (hF.memL2 α hα).aestronglyMeasurable.ae_eq_mk
  have hsm : ∀ α, StronglyMeasurable (Fm α) := by
    intro α
    by_cases hα : α.length ≤ n
    · simp only [Fm, hα, ↓reduceDIte]
      exact (hF.memL2 α hα).aestronglyMeasurable.stronglyMeasurable_mk
    · simp only [Fm, hα, ↓reduceDIte]
      exact stronglyMeasurable_const
  exact ⟨Fm, hEq, hsm, hF.congr_ae hEq⟩

private theorem localHeatGain_curveEnergy_sum_bound
    {a b : ℝ} {B : Set Vec3} (F : Finset (List (Fin 3)))
    (Zc : List (Fin 3) → Icc a b → Lp ℝ 2 (volume : Measure Vec3))
    (Dg : List (Fin 3) → Fin 3 → Vec3 × ℝ → ℝ) (t : Icc a b) (Q : ℝ)
    (hword : ∀ α ∈ F, ‖Zc α t‖ ^ 2 +
      ∑ j : Fin 3, ∫ p in vlSlab a b, Dg α j p ^ 2 ≤ Q) :
    ∑ α ∈ F, ∫ x in B, (Zc α t : Vec3 → ℝ) x ^ 2 ≤ (F.card : ℝ) * Q := by
  calc
    _ ≤ ∑ α ∈ F, Q := by
      refine Finset.sum_le_sum fun α hα => ?_
      have hL2 := Lp.memLp (Zc α t)
      have h1 : ∫ x in B, (Zc α t : Vec3 → ℝ) x ^ 2 ≤
          ∫ x, (Zc α t : Vec3 → ℝ) x ^ 2 :=
        setIntegral_le_integral hL2.integrable_sq (ae_of_all _ fun x => sq_nonneg _)
      have h2 : ∫ x, (Zc α t : Vec3 → ℝ) x ^ 2 = ‖Zc α t‖ ^ 2 := by
        rw [vl_integral_sq_eq hL2, Lp.norm_def]
      have h3 := hword α hα
      have h4 : 0 ≤ ∑ j : Fin 3, ∫ p in vlSlab a b, Dg α j p ^ 2 :=
        Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
      linarith only [h1, h2, h3, h4]
    _ = (F.card : ℝ) * Q := by rw [Finset.sum_const, nsmul_eq_mul]

private theorem localHeatGain_gradientEnergy_sum_bound
    {m : ℕ} {a b : ℝ} {B : Set (Vec3 × ℝ)} {Q NDw NDH : ℝ}
    (hab : a ≤ b)
    (Dz' Dw : List (Fin 3) → Vec3 × ℝ → ℝ)
    (Dg : List (Fin 3) → Fin 3 → Vec3 × ℝ → ℝ)
    (Zc : List (Fin 3) → Icc a b → Lp ℝ 2 (volume : Measure Vec3))
    (hDgmem : ∀ α, α ∈ sobolevWords m → ∀ j,
      MemLp (Dg α j) 2 (volume.restrict (vlSlab a b)))
    (hDwmem : ∀ α, α.length ≤ m → MemLp (Dw α) 2 (volume.restrict (vlSlab a b)))
    (hDlow : ∀ α, α.length ≤ m → Dz' α =ᵐ[volume.restrict B] Dw α)
    (hDhigh : ∀ α, ¬ α.length ≤ m → Dz' α = Dg α.dropLast (α.getLastD 0))
    (hBslab : B ⊆ vlSlab a b)
    (hNDw_ge : ∀ α, α ∈ sobolevWords m →
      ∫ p in vlSlab a b, Dw α p ^ 2 ≤ NDw)
    (hword : ∀ α, α ∈ sobolevWords m →
      ‖Zc α ⟨b, right_mem_Icc.2 hab⟩‖ ^ 2 +
        ∑ j : Fin 3, ∫ p in vlSlab a b, Dg α j p ^ 2 ≤ Q)
    (hQ : 2 * (NDH + NDw) ≤ Q) (hNDH : 0 ≤ NDH) :
    ∑ γ ∈ sobolevWords (m + 1), ∫ p in B, Dz' γ p ^ 2 ≤
      (sobolevWords (m + 1)).card * Q := by
  calc
    _ ≤ ∑ γ ∈ sobolevWords (m + 1), Q := by
      refine Finset.sum_le_sum fun γ hγ => ?_
      by_cases hγm : γ.length ≤ m
      · have h1 : ∫ p in B, Dz' γ p ^ 2 = ∫ p in B, Dw γ p ^ 2 :=
          integral_congr_ae ((hDlow γ hγm).mono fun p hp => by simp only [hp])
        have h2 : ∫ p in B, Dw γ p ^ 2 ≤ ∫ p in vlSlab a b, Dw γ p ^ 2 :=
          setIntegral_mono_set (hDwmem γ hγm).integrable_sq
            (ae_of_all _ fun p => sq_nonneg _) (ae_of_all _ hBslab)
        have hγword : γ ∈ sobolevWords m := mem_sobolevWords.2 hγm
        have h3 := hNDw_ge γ hγword
        have h4 : 2 * NDw ≤ Q := by linarith only [hQ, hNDH]
        rw [h1]
        have h5 : 0 ≤ ∫ p in vlSlab a b, Dw γ p ^ 2 :=
          integral_nonneg fun _ => sq_nonneg _
        linarith only [h2, h3, h4, h5]
      · rw [hDhigh γ hγm]
        have hβ : γ.dropLast ∈ sobolevWords m := mem_sobolevWords.2 (by
          have hγlen := mem_sobolevWords.1 hγ
          simp only [List.length_dropLast]; omega)
        have h1 : ∫ p in B, Dg γ.dropLast (γ.getLastD 0) p ^ 2 ≤
            ∫ p in vlSlab a b, Dg γ.dropLast (γ.getLastD 0) p ^ 2 :=
          setIntegral_mono_set (hDgmem γ.dropLast hβ (γ.getLastD 0)).integrable_sq
            (ae_of_all _ fun p => sq_nonneg _) (ae_of_all _ hBslab)
        have h2 : ∫ p in vlSlab a b, Dg γ.dropLast (γ.getLastD 0) p ^ 2 ≤
            ∑ j : Fin 3, ∫ p in vlSlab a b, Dg γ.dropLast j p ^ 2 :=
          Finset.single_le_sum (f := fun j => ∫ p in vlSlab a b, Dg γ.dropLast j p ^ 2)
            (fun _ _ => integral_nonneg fun _ => sq_nonneg _) (Finset.mem_univ _)
        have h3 := hword γ.dropLast hβ
        have h4 : 0 ≤ ‖Zc γ.dropLast ⟨b, right_mem_Icc.2 hab⟩‖ ^ 2 := sq_nonneg _
        linarith only [h1, h2, h3, h4]
    _ = (sobolevWords (m + 1)).card * Q := by
      rw [Finset.sum_const, nsmul_eq_mul]

private theorem localHeatGain_cutoffFamilyFacts
    {a σ r : ℝ} {x₀ : Vec3} {η : Vec3 × ℝ → ℝ}
    (Dzm DGm : List (Fin 3) → Vec3 × ℝ → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hζ : ContDiff ℝ (⊤ : ℕ∞) (localHeatGainZeta η))
    (hgrad : ∀ j : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun q : Vec3 × ℝ => spatialPartial η j q))
    (hη0 : ∀ γ p, p.2 ≤ a + σ / 2 → spaceTimeWord γ η p = 0)
    (hη1 : ∀ p, p.1 ∈ vec3Ball x₀ r → a + σ ≤ p.2 →
      spaceTimeWord [] η p = 1 ∧
        ∀ γ : List (Fin 3), γ ≠ [] → spaceTimeWord γ η p = 0)
    (hDzm : ∀ α, StronglyMeasurable (Dzm α))
    (hDGm : ∀ α, StronglyMeasurable (DGm α)) :
    (∀ α, StronglyMeasurable (localHeatGainDw η Dzm α)) ∧
      (∀ α, StronglyMeasurable (localHeatGainDH η Dzm DGm α)) ∧
      (∀ α p, p.2 < a + σ / 2 → localHeatGainDw η Dzm α p = 0) ∧
      (∀ α p, p.1 ∈ vec3Ball x₀ r → a + σ ≤ p.2 →
        localHeatGainDw η Dzm α p = Dzm α p) := by
  have hAsm (θ : Vec3 × ℝ → ℝ) (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (γ : List (Fin 3)) :
      StronglyMeasurable (spaceTimeWord γ θ) :=
    (contDiff_spaceTimeWord γ hθ).continuous.stronglyMeasurable
  refine ⟨fun α => stLeibniz_stronglyMeasurable α (hAsm η hη) hDzm, ?_, ?_, ?_⟩
  · intro α
    exact (stLeibniz_stronglyMeasurable α (hAsm η hη) hDGm).add
      ((stLeibniz_stronglyMeasurable α (hAsm (localHeatGainZeta η) hζ) hDzm).add
        (stronglyMeasurable_const.mul (Finset.stronglyMeasurable_fun_sum _ fun j _ =>
          stLeibniz_stronglyMeasurable α (hAsm (fun q => spatialPartial η j q) (hgrad j))
            fun γ => hDzm (j :: γ))))
  · intro α p hp
    exact stLeibniz_eq_zero_of_forall α fun γ => hη0 γ p hp.le
  · intro α p hp1 hp2
    exact stLeibniz_eq_of_unit α (hη1 p hp1 hp2).1 (hη1 p hp1 hp2).2

private theorem localHeatGain_ae_timeSlice
    {a b s : ℝ} {B U : Set Vec3}
    (Zc : Icc a b → Lp ℝ 2 (volume : Measure Vec3))
    (Z : ℝ → Vec3 → ℝ) (f Fm Dw : Vec3 × ℝ → ℝ)
    (hsub : Ioo s b ⊆ Ioo a b)
    (hcurve : ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      ∀ ht : t ∈ Icc a b, (Zc ⟨t, ht⟩ : Vec3 → ℝ) =ᵐ[volume] fun x => Dw (x, t))
    (hdata : f =ᵐ[volume.restrict (U ×ˢ Ioo a b)] Fm)
    (hU : B ⊆ U) (hBm : MeasurableSet B)
    (hZ : ∀ t (ht : t ∈ Icc a b), Z t = (Zc ⟨t, ht⟩ : Vec3 → ℝ))
    (hcut : ∀ p, p.1 ∈ B → s ≤ p.2 → Dw p = Fm p) :
    ∀ᵐ t ∂(volume.restrict (Ioo s b)),
      Z t =ᵐ[volume.restrict B] fun x => f (x, t) := by
  have h1 := ae_restrict_of_ae_restrict_of_subset hsub hcurve
  have h2 := ae_restrict_of_ae_restrict_of_subset hsub (ae_slices_of_ae_prod hdata)
  filter_upwards [h1, h2, ae_restrict_mem measurableSet_Ioo] with t ht1 ht2 htm
  have htab : t ∈ Icc a b := Ioo_subset_Icc_self (hsub htm)
  have h3 : (Zc ⟨t, htab⟩ : Vec3 → ℝ) =ᵐ[volume.restrict B] fun x => Dw (x, t) :=
    ae_restrict_of_ae (ht1 htab)
  have h4 : (fun x => f (x, t)) =ᵐ[volume.restrict B] fun x => Fm (x, t) :=
    ae_restrict_of_ae_restrict_of_subset hU ht2
  filter_upwards [h3, h4, ae_restrict_mem hBm]
    with x hx3 hx4 hxB
  rw [hZ t htab, hx3, hx4]
  exact hcut (x, t) hxB htm.1.le

private theorem localHeatGain_highOrderFamily
    {m : ℕ} {x₀ : Vec3} {r a s b : ℝ} {U : Set Vec3} {I : Set ℝ}
    {W : Set (Vec3 × ℝ)} {z : Vec3 × ℝ → ℝ}
    {Dz Dw Dz' : List (Fin 3) → Vec3 × ℝ → ℝ}
    {Dg : List (Fin 3) → Fin 3 → Vec3 × ℝ → ℝ}
    (hz : IsL2SobolevFamilyOn m U I z Dz)
    (hDgmem : ∀ α, α ∈ sobolevWords m → ∀ j,
      MemLp (Dg α j) 2 (volume.restrict (vlSlab a b)))
    (hDgweak : ∀ α, α ∈ sobolevWords m → ∀ j,
      IsSpaceTimeWeakPartial (vlSlab a b) j (Dw α) (Dg α j))
    (hDwW : ∀ α, α.length ≤ m → Dw α =ᵐ[volume.restrict W] Dz α)
    (hUmeas : MeasurableSet (U ×ˢ I)) (hWV : W ⊆ U ×ˢ I)
    (hSlabMeas : MeasurableSet (vlSlab a b)) (hWslab : W ⊆ vlSlab a b)
    (hWdef : W = vec3Ball x₀ r ×ˢ Ioo s b)
    (hzero : Dz' [] = Dz [])
    (hlow : ∀ α, α.length ≤ m → Dz' α = Dz α)
    (hhigh : ∀ α, ¬ α.length ≤ m → Dz' α = Dg α.dropLast (α.getLastD 0)) :
    IsL2SobolevFamilyOn (m + 1) (vec3Ball x₀ r) (Ioo s b) z Dz' := by
  subst W
  refine ⟨?_, ?_, ?_⟩
  · intro α hα
    by_cases hαm : α.length ≤ m
    · rw [hlow α hαm]
      exact (hz.memL2 α hαm).mono_measure
        (Measure.restrict_mono hWV le_rfl)
    · have hβ : α.dropLast ∈ sobolevWords m := mem_sobolevWords.2 (by
        have hlen := hα
        simp only [List.length_dropLast]; omega)
      rw [hhigh α hαm]
      exact (hDgmem α.dropLast hβ (α.getLastD 0)).mono_measure
        (Measure.restrict_mono hWslab le_rfl)
  · rw [hzero]
    exact ae_restrict_of_ae_restrict_of_subset hWV hz.zero
  · intro α j hαlt
    have hαm : α.length ≤ m := by omega
    rw [hlow α hαm]
    by_cases hαltm : α.length < m
    · have hαj : (α ++ [j]).length ≤ m := by
        simp only [List.length_append, List.length_singleton]; omega
      rw [hlow (α ++ [j]) hαj]
      exact IsSpaceTimeWeakPartial.mono (hz.weak α j hαltm) hUmeas hWV
    · have hαmem : α ∈ sobolevWords m := mem_sobolevWords.2 hαm
      have hαj : ¬ (α ++ [j]).length ≤ m := by
        simp only [List.length_append, List.length_singleton]; omega
      have hlast : Dz' (α ++ [j]) = Dg α j := by
        simpa only [List.dropLast_concat, List.getLastD_concat] using hhigh (α ++ [j]) hαj
      rw [hlast]
      have hweak := (hDgweak α hαmem j).mono hSlabMeas hWslab
      exact hweak.congr_left (hDwW α hαm)

private theorem localHeatGain_curveSobolevFamily
    {m : ℕ} {a b : ℝ} (hab : a < b) (B : Set Vec3)
    {Dw : List (Fin 3) → Vec3 × ℝ → ℝ}
    (hDw : IsSpaceTimeFamily m (vlSlab a b) Dw)
    (Zc : List (Fin 3) → Icc a b → Lp ℝ 2 (volume : Measure Vec3))
    (hcontinuous : ∀ α, α ∈ sobolevWords m → Continuous (Zc α))
    (hcurve : ∀ α, α ∈ sobolevWords m →
      ∀ᵐ t ∂(volume.restrict (Ioo a b)), ∀ ht : t ∈ Icc a b,
        (Zc α ⟨t, ht⟩ : Vec3 → ℝ) =ᵐ[volume] fun x => Dw α (x, t))
    (t : Icc a b) (g : List (Fin 3) → Vec3 → ℝ)
    (hlink : ∀ α, α ∈ sobolevWords m → g α = (Zc α t : Vec3 → ℝ)) :
    IsSobolevFamilyOn m B (g []) g := by
  refine ⟨Filter.EventuallyEq.rfl, fun α hα => ?_, fun α j hα => ?_⟩
  · rw [hlink α (mem_sobolevWords.2 hα)]
    exact (Lp.memLp _).restrict _
  · have hαm : α ∈ sobolevWords m := mem_sobolevWords.2 hα.le
    have hαj : α ++ [j] ∈ sobolevWords m := mem_sobolevWords.2 (by
      simp only [List.length_append, List.length_singleton]; omega)
    rw [hlink α hαm, hlink _ hαj]
    intro ψ hψ hψc hψB
    have hcw := curve_weakPartial_of_slab hab
      (hDw.memL2 α hα.le) (hDw.memL2 (α ++ [j]) (mem_sobolevWords.1 hαj))
      (hDw.weak α j hα) (hcontinuous α hαm) (hcontinuous _ hαj)
      (hcurve α hαm) (hcurve _ hαj)
      ψ hψ hψc t
    have e1 : ∫ x in B, (Zc α t : Vec3 → ℝ) x *
        (fderiv ℝ ψ x) (basisVec j) =
        ∫ x, (Zc α t : Vec3 → ℝ) x * spatialDeriv ψ j x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        have hx' : x ∉ tsupport ψ := fun h => hx (hψB h)
        change _ * spatialDeriv ψ j x = 0
        rw [image_eq_zero_of_notMem_tsupport (f := spatialDeriv ψ j) (fun h => hx'
          (tsupport_fderiv_apply_subset ℝ (basisVec j) h)), mul_zero]
    have e2 : ∫ x in B, (Zc (α ++ [j]) t : Vec3 → ℝ) x * ψ x =
        ∫ x, (Zc (α ++ [j]) t : Vec3 → ℝ) x * ψ x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
        rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hψB h)), mul_zero]
    rw [e1, e2]
    exact hcw

private theorem localHeatGain_lpCurve_restrict_continuous
    {a b s : ℝ} (B : Set Vec3)
    (F : ℝ → Lp ℝ 2 (volume : Measure Vec3)) (g : ℝ → Vec3 → ℝ)
    (hFc : ContinuousOn F (Icc a b))
    (hlink : ∀ t, t ∈ Icc a b → g t = (F t : Vec3 → ℝ))
    (hsub : Icc s b ⊆ Icc a b) (t : ℝ) (ht : t ∈ Icc s b) :
    Tendsto (fun t' => eLpNorm (g t' - g t) 2 (volume.restrict B))
      (𝓝[Icc s b] t) (𝓝 0) := by
  have hFt : Tendsto (fun t' => ‖F t' - F t‖) (𝓝[Icc s b] t) (𝓝 0) := by
    have h := ((hFc.mono hsub) t ht).sub (continuousWithinAt_const (b := F t))
    simpa using h.norm.tendsto
  have hbound : ∀ᶠ t' in 𝓝[Icc s b] t,
      eLpNorm (g t' - g t) 2 (volume.restrict B) ≤ ENNReal.ofReal ‖F t' - F t‖ := by
    filter_upwards [self_mem_nhdsWithin] with t' ht'
    have ht'ab := hsub ht'
    have htab := hsub ht
    rw [hlink t' ht'ab, hlink t htab, ofReal_norm, Lp.enorm_def]
    calc
      eLpNorm ((F t' : Vec3 → ℝ) - (F t : Vec3 → ℝ)) 2 (volume.restrict B) ≤
          eLpNorm ((F t' : Vec3 → ℝ) - (F t : Vec3 → ℝ)) 2 volume :=
        eLpNorm_mono_measure _ Measure.restrict_le_self
      _ = eLpNorm (⇑(F t' - F t)) 2 volume := eLpNorm_congr_ae (Lp.coeFn_sub _ _).symm
  have hlim : Tendsto (fun t' => ENNReal.ofReal ‖F t' - F t‖)
      (𝓝[Icc s b] t) (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hFt
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) hbound

private theorem localHeatGain_singleTerm_le_sum
    {α : Type} (F : Finset α) (f : α → ℝ) (hf : ∀ a ∈ F, 0 ≤ f a) :
    ∀ a ∈ F, f a ≤ ∑ b ∈ F, f b := by
  intro a ha
  exact Finset.single_le_sum (f := f) hf ha

private theorem localHeatGain_sum_integrals_ae_eq
    {α : Type} {F : Finset α} {W : Set (Vec3 × ℝ)}
    {f g : α → Vec3 × ℝ → ℝ}
    (hfg : ∀ i, i ∈ F → f i =ᵐ[volume.restrict W] g i) :
    ∑ i ∈ F, ∫ p in W, f i p ^ 2 = ∑ i ∈ F, ∫ p in W, g i p ^ 2 := by
  apply Finset.sum_congr rfl
  intro i hi
  exact integral_congr_ae ((hfg i hi).mono fun p hp => congrArg (fun v : ℝ => v ^ 2) hp)

private theorem localHeatGain_combineCutoffEnergy
    {K L A B NDw NDH : ℝ}
    (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hNw : NDw ≤ K * L ^ 2 * A)
    (hNH : NDH ≤ K * L ^ 2 * (A + B)) :
    2 * (NDH + NDw) ≤ (4 * K * L ^ 2) * (A + B) := by
  have h1 : K * L ^ 2 * A ≤ K * L ^ 2 * (A + B) :=
    mul_le_mul_of_nonneg_left (by linarith only [hB]) (by positivity)
  nlinarith only [hNw, hNH, h1]

private theorem localHeatGain_individualEnergyBound
    {m : ℕ} {a b : ℝ} {Q NDw NDH : ℝ}
    (Dg : List (Fin 3) → Fin 3 → Vec3 × ℝ → ℝ)
    (Zc : List (Fin 3) → Icc a b → Lp ℝ 2 (volume : Measure Vec3))
    (hQ : 2 * (NDH + NDw) ≤ Q)
    (Dw : List (Fin 3) → Vec3 × ℝ → ℝ)
    (hNDw : ∀ α, α ∈ sobolevWords m →
      ∫ p in vlSlab a b, Dw α p ^ 2 ≤ NDw)
    (hbase : ∀ α, α ∈ sobolevWords m → ∀ t : Icc a b,
      ‖Zc α t‖ ^ 2 + ∑ j : Fin 3, ∫ p in vlSlab a b, Dg α j p ^ 2 ≤
        2 * (NDH + ∫ p in vlSlab a b, Dw α p ^ 2)) :
    ∀ α, α ∈ sobolevWords m → ∀ t : Icc a b,
      ‖Zc α t‖ ^ 2 + ∑ j : Fin 3, ∫ p in vlSlab a b, Dg α j p ^ 2 ≤ Q := by
  intro α hα t
  have h1 := hbase α hα t
  have h2 := hNDw α hα
  linarith only [h1, h2, hQ]

private theorem localHeatGain_sqrt_energy_estimate
    {A B N₁ N₂ Q₀ S X Y : ℝ}
    (hA : A ≤ N₁ * Q₀ * S) (hB : B ≤ N₂ * Q₀ * S)
    (hN₁ : 0 ≤ N₁) (hN₂ : 0 ≤ N₂) (hQ₀ : 0 ≤ Q₀)
    (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hSXY : S = X + Y) :
    Real.sqrt A + Real.sqrt B ≤
      (Real.sqrt (N₁ * Q₀) + Real.sqrt (N₂ * Q₀)) *
        (Real.sqrt X + Real.sqrt Y) := by
  have hsA : Real.sqrt A ≤ Real.sqrt (N₁ * Q₀) * Real.sqrt S := by
    rw [← Real.sqrt_mul (mul_nonneg hN₁ hQ₀)]
    exact Real.sqrt_le_sqrt (by nlinarith only [hA])
  have hsB : Real.sqrt B ≤ Real.sqrt (N₂ * Q₀) * Real.sqrt S := by
    rw [← Real.sqrt_mul (mul_nonneg hN₂ hQ₀)]
    exact Real.sqrt_le_sqrt (by nlinarith only [hB])
  have hsS : Real.sqrt S ≤ Real.sqrt X + Real.sqrt Y := by
    rw [hSXY]
    exact real_sqrt_add_le_add_sqrt hX hY
  calc
    _ ≤ Real.sqrt (N₁ * Q₀) * Real.sqrt S +
        Real.sqrt (N₂ * Q₀) * Real.sqrt S := add_le_add hsA hsB
    _ = (Real.sqrt (N₁ * Q₀) + Real.sqrt (N₂ * Q₀)) * Real.sqrt S :=
      (add_mul _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hsS
      (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

/-- `lem:local-heat-gain`. -/
theorem localHeatGain (m : ℕ) (hm : m = 1 ∨ m = 2) {r R σ β : ℝ}
    (hr : 0 < r) (hrR : r < R) (hσ : 0 < σ) (hσβ : σ < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x₀ : Vec3) (a : ℝ) (z G : Vec3 × ℝ → ℝ)
      (Dz DG : List (Fin 3) → Vec3 × ℝ → ℝ),
      IsL2SobolevFamilyOn m (vec3Ball x₀ R) (Ioo a (a + β)) z Dz →
      IsL2SobolevFamilyOn (m - 1) (vec3Ball x₀ R) (Ioo a (a + β)) G DG →
      IsHeatSolutionOn (vec3Ball x₀ R) (Ioo a (a + β)) z G →
      ∃ (Z : ℝ → List (Fin 3) → Vec3 → ℝ) (Dz' : List (Fin 3) → Vec3 × ℝ → ℝ),
        (∀ t ∈ Icc (a + σ) (a + β),
          IsSobolevFamilyOn m (vec3Ball x₀ r) (Z t []) (Z t)) ∧
        (∀ α : List (Fin 3), α.length ≤ m → ∀ t ∈ Icc (a + σ) (a + β),
          Tendsto (fun t' => eLpNorm (Z t' α - Z t α) 2 (volume.restrict (vec3Ball x₀ r)))
            (𝓝[Icc (a + σ) (a + β)] t) (𝓝 0)) ∧
        (∀ᵐ t ∂(volume.restrict (Ioo (a + σ) (a + β))),
          Z t [] =ᵐ[volume.restrict (vec3Ball x₀ r)] fun x => z (x, t)) ∧
        IsL2SobolevFamilyOn (m + 1) (vec3Ball x₀ r) (Ioo (a + σ) (a + β)) z Dz' ∧
        ∀ t ∈ Icc (a + σ) (a + β),
          Real.sqrt (sobolevNormSqOn m (vec3Ball x₀ r) (Z t)) +
              Real.sqrt (l2SobolevNormSqOn (m + 1) (vec3Ball x₀ r)
                (Ioo (a + σ) (a + β)) Dz') ≤
            C * (Real.sqrt (l2SobolevNormSqOn m (vec3Ball x₀ R) (Ioo a (a + β)) Dz) +
              Real.sqrt (l2SobolevNormSqOn (m - 1) (vec3Ball x₀ R) (Ioo a (a + β)) DG)) := by
  have hm1 : 1 ≤ m := by rcases hm with h | h <;> omega
  obtain ⟨L, hL0, hcut⟩ := localHeatGain_cutoffs m hr hrR hσ
  obtain ⟨Kc, hKc, hnorm⟩ := localHeatGain_normBounds m hm1
  set N₁ : ℝ := ((sobolevWords m).card : ℝ) with hN₁
  set N₂ : ℝ := ((sobolevWords (m + 1)).card : ℝ) with hN₂
  set Q₀ : ℝ := 4 * Kc * L ^ 2 with hQ₀
  have hQ₀0 : 0 ≤ Q₀ := by positivity
  refine ⟨Real.sqrt (N₁ * Q₀) + Real.sqrt (N₂ * Q₀), by positivity, ?_⟩
  intro x₀ a z G Dz DG hz hG hheat
  set b : ℝ := a + β with hb
  set s : ℝ := a + σ with hs
  have hab : a < b := by rw [hb]; linarith only [hσ, hσβ]
  have has : a < s := by rw [hs]; linarith only [hσ]
  have hsb : s < b := by rw [hs, hb]; linarith only [hσβ]
  set U : Set Vec3 := vec3Ball x₀ R with hU
  set I : Set ℝ := Ioo a b with hI
  have hUm : MeasurableSet U := (isOpen_vec3Ball x₀ R).measurableSet
  have hIm : MeasurableSet I := measurableSet_Ioo
  have hVm : MeasurableSet (U ×ˢ I) := hUm.prod hIm
  obtain ⟨η, K, N, κ, hη, hN, hKN, hκ, hκc, hκR, hκN, hLη, hLζ, hLg, hη0, hη1⟩ := hcut x₀ a
  -- measurable modifications of the data
  have hDzF : IsSpaceTimeFamily m (U ×ˢ I) Dz := ⟨hz.memL2, hz.weak⟩
  have hDGF : IsSpaceTimeFamily (m - 1) (U ×ˢ I) DG := ⟨hG.memL2, hG.weak⟩
  obtain ⟨Dzm, hDzm_eq, hDzm_sm, hDzmF⟩ :=
    localHeatGain_measurableFamilyRepresentative hDzF
  obtain ⟨DGm, hDGm_eq, hDGm_sm, hDGmF⟩ :=
    localHeatGain_measurableFamilyRepresentative hDGF
  have hheat' : IsHeatSolutionOn U I (Dzm []) (DGm []) :=
    CKN.IsHeatSolutionOn.congr_ae hheat (hz.zero.symm.trans (hDzm_eq [] (Nat.zero_le _)))
      (hG.zero.symm.trans (hDGm_eq [] (Nat.zero_le _)))
  -- the cutoff solution
  obtain ⟨hDwU, hDHU, hDw0, hDH0⟩ := localHeatGain_families hm1 hUm hIm hη hN hKN hκ hκc hκR
    hκN hDzmF hDGmF
  have hheatU := localHeatGain_heat hIm hη hm1 hDzmF hDGmF hheat'
  let Dw := localHeatGainDw η Dzm
  let DH := localHeatGainDH η Dzm DGm
  obtain ⟨hDw_sm, hDH_sm, hvan, hone⟩ :=
    localHeatGain_cutoffFamilyFacts Dzm DGm hη.smooth hη.smooth_zeta hη.smooth_grad
      (fun γ p hp => hη0 γ p hp) (fun p hp1 hp2 => hη1 p hp1 hp2)
      hDzm_sm hDGm_sm
  -- the energy estimates for each word
  have hall : ∀ β' : List (Fin 3), ∃ (Zc : Icc a b → Lp ℝ 2 (volume : Measure Vec3))
      (Dg : Fin 3 → Vec3 × ℝ → ℝ), β' ∈ sobolevWords m →
      Continuous Zc ∧
      (∀ᵐ t ∂(volume.restrict (Ioo a b)), ∀ ht : t ∈ Icc a b,
        (Zc ⟨t, ht⟩ : Vec3 → ℝ) =ᵐ[volume] fun x => Dw β' (x, t)) ∧
      (∀ j, MemLp (Dg j) 2 (volume.restrict (vlSlab a b))) ∧
      (∀ j, IsSpaceTimeWeakPartial (vlSlab a b) j (Dw β') (Dg j)) ∧
      ∀ t, ‖Zc t‖ ^ 2 + ∑ j : Fin 3, ∫ p in vlSlab a b, Dg j p ^ 2 ≤
        2 * ((∑ α ∈ sobolevWords (m - 1), ∫ p in vlSlab a b, DH α p ^ 2) +
          ∫ p in vlSlab a b, Dw β' p ^ 2) := by
    intro β'
    by_cases hβ' : β' ∈ sobolevWords m
    · obtain ⟨Zc, Dg, h⟩ := localHeatGain_wordEnergy hm1 hab (half_pos hσ) hDwU hDHU hheatU
        hDw_sm hDH_sm (fun α p hp => hvan α p (by linarith only [hp])) β' hβ'
      exact ⟨Zc, Dg, fun _ => h⟩
    · exact ⟨fun _ => 0, fun _ _ => 0, fun h => absurd h hβ'⟩
  choose Zc Dg hZD using hall
  -- the norm bounds
  obtain ⟨hNw, hNH⟩ := hnorm U K I η L Dzm DGm hUm hIm hη hLη hLζ hLg hDzmF hDGmF
  set NDz := l2SobolevNormSqOn m (vec3Ball x₀ R) (Ioo a (a + β)) Dz with hNDz
  set NDG := l2SobolevNormSqOn (m - 1) (vec3Ball x₀ R) (Ioo a (a + β)) DG with hNDG
  have hNDz0 : 0 ≤ NDz := Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
  have hNDG0 : 0 ≤ NDG := Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
  have hNDzm : ∑ α ∈ sobolevWords m, ∫ p in U ×ˢ I, Dzm α p ^ 2 = NDz :=
    localHeatGain_sum_integrals_ae_eq (F := sobolevWords m)
      (fun α hα => (hDzm_eq α (mem_sobolevWords.1 hα)).symm)
  have hNDGm : ∑ α ∈ sobolevWords (m - 1), ∫ p in U ×ˢ I, DGm α p ^ 2 = NDG :=
    localHeatGain_sum_integrals_ae_eq (F := sobolevWords (m - 1))
      (fun α hα => (hDGm_eq α (mem_sobolevWords.1 hα)).symm)
  rw [hNDzm] at hNw hNH
  rw [hNDGm] at hNH
  set NDw := ∑ α ∈ sobolevWords m, ∫ p in vlSlab a b, Dw α p ^ 2 with hNDw
  set NDH := ∑ α ∈ sobolevWords (m - 1), ∫ p in vlSlab a b, DH α p ^ 2 with hNDH
  have hNw' : NDw ≤ Kc * L ^ 2 * NDz := hNw
  have hNH' : NDH ≤ Kc * L ^ 2 * (NDz + NDG) := hNH
  set S : ℝ := NDz + NDG with hS
  have hQ : 2 * (NDH + NDw) ≤ Q₀ * S := by
    rw [hQ₀, hS]
    exact localHeatGain_combineCutoffEnergy hKc hNDG0 hNw' hNH'
  have hNDw_ge (β' : List (Fin 3)) (hβ' : β' ∈ sobolevWords m) :
      ∫ p in vlSlab a b, Dw β' p ^ 2 ≤ NDw :=
    localHeatGain_singleTerm_le_sum (sobolevWords m)
      (fun α => ∫ p in vlSlab a b, Dw α p ^ 2)
      (fun _ _ => integral_nonneg fun _ => sq_nonneg _) β' hβ'
  have hword : ∀ β' : List (Fin 3), β' ∈ sobolevWords m → ∀ t : Icc a b,
      ‖Zc β' t‖ ^ 2 + ∑ j : Fin 3, ∫ p in vlSlab a b, Dg β' j p ^ 2 ≤ Q₀ * S :=
    localHeatGain_individualEnergyBound Dg Zc hQ Dw hNDw_ge
      (fun β' hβ' t => (hZD β' hβ').2.2.2.2 t)
  -- the witnesses
  let Z : ℝ → List (Fin 3) → Vec3 → ℝ := fun t α x =>
    if hα : α ∈ sobolevWords m then
      (if ht : t ∈ Icc a b then (Zc α ⟨t, ht⟩ : Vec3 → ℝ) x else 0) else 0
  let Dz' : List (Fin 3) → Vec3 × ℝ → ℝ := fun α =>
    if α.length ≤ m then Dz α else Dg α.dropLast (α.getLastD 0)
  have hIccsub : Icc s b ⊆ Icc a b := Icc_subset_Icc_left has.le
  have hZt (t : ℝ) (ht : t ∈ Icc a b) (α : List (Fin 3)) (hα : α ∈ sobolevWords m) :
      Z t α = (Zc α ⟨t, ht⟩ : Vec3 → ℝ) := by
    funext x
    simp only [Z, hα, ht, ↓reduceDIte]
  have hrR' : vec3Ball x₀ r ⊆ U := fun y hy => lt_trans hy hrR
  set W : Set (Vec3 × ℝ) := vec3Ball x₀ r ×ˢ Ioo s b with hW
  have hWm : MeasurableSet W := (isOpen_vec3Ball x₀ r).measurableSet.prod measurableSet_Ioo
  have hWV : W ⊆ U ×ˢ I := prod_mono hrR' (Ioo_subset_Ioo_left has.le)
  have hWS : W ⊆ vlSlab a b := fun p hp => ⟨mem_univ _, (hWV hp).2⟩
  have hSm : MeasurableSet (vlSlab a b) := MeasurableSet.univ.prod measurableSet_Ioo
  -- on `W` the cutoff solution is `Dz`
  have hDwW (α : List (Fin 3)) (hα : α.length ≤ m) :
      Dw α =ᵐ[volume.restrict W] Dz α := by
    have h1 : Dzm α =ᵐ[volume.restrict W] Dz α :=
      ae_restrict_of_ae_restrict_of_subset hWV (hDzm_eq α hα).symm
    filter_upwards [h1, ae_restrict_mem hWm] with p hp hpW
    exact (hone α p hpW.1 hpW.2.1.le).trans hp
  refine ⟨Z, Dz', ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact localHeatGain_curveSobolevFamily hab (vec3Ball x₀ r) hDwU Zc
      (fun α hα => (hZD α hα).1) (fun α hα => (hZD α hα).2.1)
      ⟨t, hIccsub ht⟩ (Z t) (hZt t (hIccsub ht))
  · -- continuity in `L²(B_r)`
    intro α hα t ht
    have hαm : α ∈ sobolevWords m := mem_sobolevWords.2 hα
    let F : ℝ → Lp ℝ 2 (volume : Measure Vec3) := fun t' =>
      if h : t' ∈ Icc a b then Zc α ⟨t', h⟩ else 0
    have hFc : ContinuousOn F (Icc a b) := by
      rw [continuousOn_iff_continuous_domRestrict]
      refine (hZD α hαm).1.congr fun t' => ?_
      simp only [F, Set.domRestrict_apply, t'.2, ↓reduceDIte]
    exact localHeatGain_lpCurve_restrict_continuous (vec3Ball x₀ r) F
      (fun t' => Z t' α) hFc
      (fun t' ht' => by
        simp only [F, ht', ↓reduceDIte]
        exact hZt t' ht' α hαm)
      hIccsub t ht
  · -- the time slices
    exact localHeatGain_ae_timeSlice (Zc []) (fun t => Z t []) z (Dzm []) (Dw [])
      (Ioo_subset_Ioo_left has.le)
      (hZD [] (mem_sobolevWords.2 (Nat.zero_le _))).2.1
      (hz.zero.symm.trans (hDzm_eq [] (Nat.zero_le _))) hrR'
      (isOpen_vec3Ball x₀ r).measurableSet
      (fun t ht => hZt t ht [] (mem_sobolevWords.2 (Nat.zero_le _)))
      (fun p hp1 hp2 => hone [] p hp1 hp2)
  · -- the `L²_t H^{m+1}_x` family
    exact localHeatGain_highOrderFamily hz
      (fun α hα j => (hZD α hα).2.2.1 j)
      (fun α hα j => (hZD α hα).2.2.2.1 j)
      (fun α hα => hDwW α hα) hVm hWV hSm hWS rfl
      (by simp [Dz'])
      (by intro α hα; simp only [Dz', hα, ite_true])
      (by intro α hα; simp only [Dz', hα, ite_false])
  · -- the estimate
    intro t ht
    have htab := hIccsub ht
    -- The energy estimate controls the finite family of time-slice norms.
    have hA : sobolevNormSqOn m (vec3Ball x₀ r) (Z t) ≤ N₁ * (Q₀ * S) := by
      unfold sobolevNormSqOn
      calc
        _ = ∑ α ∈ sobolevWords m, ∫ x in vec3Ball x₀ r,
            (Zc α ⟨t, htab⟩ : Vec3 → ℝ) x ^ 2 := by
          refine Finset.sum_congr rfl fun α hα => ?_
          exact congrArg (fun f : Vec3 → ℝ => ∫ x in vec3Ball x₀ r, f x ^ 2)
            (hZt t htab α hα)
        _ ≤ (sobolevWords m).card * (Q₀ * S) :=
          localHeatGain_curveEnergy_sum_bound (sobolevWords m) Zc Dg ⟨t, htab⟩ (Q₀ * S)
            (fun α hα => hword α hα ⟨t, htab⟩)
        _ = N₁ * (Q₀ * S) := by rw [hN₁]
    have hB : l2SobolevNormSqOn (m + 1) (vec3Ball x₀ r) (Ioo s b) Dz' ≤ N₂ * (Q₀ * S) := by
      unfold l2SobolevNormSqOn
      calc
        _ ≤ (sobolevWords (m + 1)).card * (Q₀ * S) :=
          localHeatGain_gradientEnergy_sum_bound hab.le Dz' Dw Dg Zc
            (fun α hα j => (hZD α hα).2.2.1 j)
            (fun α hα => hDwU.memL2 α hα)
            (fun α hα => by
              simpa only [Dz', hα, ite_true] using (hDwW α hα).symm)
            (fun α hα => by simp only [Dz', hα, ite_false]) hWS hNDw_ge
            (fun α hα => hword α hα ⟨b, right_mem_Icc.2 hab.le⟩)
            hQ (Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _)
        _ = N₂ * (Q₀ * S) := by rw [hN₂]
    have hN₁0 : 0 ≤ N₁ := Nat.cast_nonneg _
    have hN₂0 : 0 ≤ N₂ := Nat.cast_nonneg _
    apply localHeatGain_sqrt_energy_estimate (S := S)
      (by simpa only [mul_assoc] using hA) (by simpa only [mul_assoc] using hB) hN₁0 hN₂0 hQ₀0
      hNDz0 hNDG0 rfl

end ESS
