/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingWholeHeatGainCutoff

/-!
# Whole-space heat gain of every order

The whole-space form of `lem:local-heat-gain`, for every order `m ≥ 1`, as
used in `prop:lps-smoothing`. Let `a < a + σ < a + β`. If
`z ∈ L²((a, a + β); H^m(ℝ³))` solves `∂ₜ z - Δ z = G` in distributions on
`ℝ³ × (a, a + β)` with `G ∈ L²((a, a + β); H^{m-1}(ℝ³))`, then
`z ∈ C([a + σ, a + β]; H^m(ℝ³)) ∩ L²((a + σ, a + β); H^{m+1}(ℝ³))` with
`‖z‖_{C H^m} + ‖z‖_{L² H^{m+1}} ≤ C (‖z‖_{L² H^m} + ‖G‖_{L² H^{m-1}})`,
where `C` depends only on `m`, `σ` and `β`.

The proof multiplies by a time cutoff `c(t)` vanishing for `t ≤ a + σ/2` and
equal to one for `t ≥ a + σ`. Each spatial derivative `∂^γ (c z)`, `|γ| ≤ m`,
solves the heat equation on `ℝ³ × (a, a + β)` with a square-integrable source
in source or divergence form built from `c ∂^γ G + c' ∂^γ z`, and has zero
initial trace, so the energy estimate of `lem:localized-vorticity-energy`
applies.
-/

public section

open MeasureTheory Set Filter
open scoped Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private lemma lps_sobolev_family_measurable_version
    {m : ℕ} {a b : ℝ} {z : Vec3 × ℝ → ℝ} {D : List (Fin 3) → Vec3 × ℝ → ℝ}
    (h : IsL2SobolevFamilyOn m (Set.univ : Set Vec3) (Ioo a b) z D) :
    ∃ Dm : List (Fin 3) → Vec3 × ℝ → ℝ,
      (∀ α, α.length ≤ m → D α =ᵐ[volume.restrict ((univ : Set Vec3) ×ˢ Ioo a b)] Dm α) ∧
      ∀ α, StronglyMeasurable (Dm α) := by
  let Dm : List (Fin 3) → Vec3 × ℝ → ℝ := fun α =>
    if hα : α.length ≤ m then (h.memL2 α hα).aestronglyMeasurable.mk (D α) else fun _ => 0
  refine ⟨Dm, ?_, ?_⟩
  · intro α hα
    simp only [Dm, hα, ↓reduceDIte]
    exact (h.memL2 α hα).aestronglyMeasurable.ae_eq_mk
  · intro α
    by_cases hα : α.length ≤ m
    · simp only [Dm, hα, ↓reduceDIte]
      exact (h.memL2 α hα).aestronglyMeasurable.stronglyMeasurable_mk
    · simp only [Dm, hα, ↓reduceDIte]
      exact stronglyMeasurable_const

private lemma lps_l2_curve_representative_continuity
    {a b s : ℝ} (has : a < s)
    (Zc : Icc a b → Lp ℝ 2 (volume : Measure Vec3)) (hZc : Continuous Zc)
    (Z : ℝ → Vec3 → ℝ)
    (hZt : ∀ t (ht : t ∈ Icc a b), Z t = (Zc ⟨t, ht⟩ : Vec3 → ℝ))
    (t : ℝ) (ht : t ∈ Icc s b) :
    Tendsto (fun t' => eLpNorm (Z t' - Z t) 2 volume)
      (nhdsWithin t (Icc s b)) (nhds 0) := by
  have hIccsub : Icc s b ⊆ Icc a b := Icc_subset_Icc_left has.le
  let F : ℝ → Lp ℝ 2 (volume : Measure Vec3) := fun t' =>
    if h : t' ∈ Icc a b then Zc ⟨t', h⟩ else 0
  have hFc : ContinuousOn F (Icc a b) := by
    rw [continuousOn_iff_continuous_domRestrict]
    refine hZc.congr fun t' => ?_
    simp only [F, Set.domRestrict_apply, t'.2, ↓reduceDIte]
  have hFt : Tendsto (fun t' => ‖F t' - F t‖) (𝓝[Icc s b] t) (𝓝 0) := by
    have h := ((hFc t (hIccsub ht)).mono hIccsub).sub
      (continuousWithinAt_const (b := F t))
    have h2 := h.norm.tendsto
    simpa using h2
  have hbound : ∀ᶠ t' in 𝓝[Icc s b] t,
      eLpNorm (Z t' - Z t) 2 volume ≤ ENNReal.ofReal ‖F t' - F t‖ := by
    filter_upwards [self_mem_nhdsWithin] with t' ht'
    have ht'ab := hIccsub ht'
    have htab := hIccsub ht
    have hF' : F t' = Zc ⟨t', ht'ab⟩ := by simp only [F, ht'ab, ↓reduceDIte]
    have hF : F t = Zc ⟨t, htab⟩ := by simp only [F, htab, ↓reduceDIte]
    rw [hZt t' ht'ab, hZt t htab, hF', hF, ofReal_norm, Lp.enorm_def]
    exact le_of_eq (eLpNorm_congr_ae (Lp.coeFn_sub _ _).symm)
  have hlim : Tendsto (fun t' => ENNReal.ofReal ‖F t' - F t‖) (𝓝[Icc s b] t) (𝓝 0) := by
    have h := (ENNReal.tendsto_ofReal hFt)
    simpa using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => bot_le) hbound

private lemma lps_extended_family_energy_bound
    {m : ℕ} {a b s : ℝ} {Dz Dw Dz' : List (Fin 3) → Vec3 × ℝ → ℝ}
    {Dg : List (Fin 3) → Fin 3 → Vec3 × ℝ → ℝ}
    {NDw NDH Q : ℝ} (hNDH0 : 0 ≤ NDH) (hQ0 : 0 ≤ Q)
    (hQ : 2 * (NDH + NDw) ≤ Q)
    (hLow : ∀ γ, γ.length ≤ m → Dz' γ = Dz γ)
    (hHigh : ∀ γ, ¬γ.length ≤ m → Dz' γ = Dg γ.dropLast (γ.getLastD 0))
    (hWS : ((univ : Set Vec3) ×ˢ Ioo s b) ⊆ vlSlab a b)
    (hDwMem : ∀ α, α.length ≤ m → MemLp (Dw α) 2 (volume.restrict (vlSlab a b)))
    (hDgMem : ∀ α, α ∈ sobolevWords m → ∀ j, MemLp (Dg α j) 2 (volume.restrict (vlSlab a b)))
    (hDwW : ∀ α, α.length ≤ m → Dw α =ᵐ[volume.restrict ((univ : Set Vec3) ×ˢ Ioo s b)] Dz α)
    (hNDw_ge : ∀ α, α ∈ sobolevWords m → ∫ p in vlSlab a b, Dw α p ^ 2 ≤ NDw)
    (hGradBound : ∀ α, α ∈ sobolevWords m → ∑ j : Fin 3, ∫ p in vlSlab a b, Dg α j p ^ 2 ≤ Q) :
    l2SobolevNormSqOn (m + 1) (Set.univ : Set Vec3) (Ioo s b) Dz' ≤
      ((sobolevWords (m + 1)).card : ℝ) * Q := by
  let W : Set (Vec3 × ℝ) := (univ : Set Vec3) ×ˢ Ioo s b
  unfold l2SobolevNormSqOn
  calc
    ∑ γ ∈ sobolevWords (m + 1), ∫ p in W, Dz' γ p ^ 2 ≤
        ∑ γ ∈ sobolevWords (m + 1), Q := by
      refine Finset.sum_le_sum fun γ hγ => ?_
      by_cases hγm : γ.length ≤ m
      · have e0 : Dz' γ = Dz γ := hLow γ hγm
        rw [e0]
        have hγmem : γ ∈ sobolevWords m := mem_sobolevWords.2 hγm
        have h1 : ∫ p in W, Dz γ p ^ 2 = ∫ p in W, Dw γ p ^ 2 :=
          integral_congr_ae ((hDwW γ hγm).mono fun p hp => by simp only [hp])
        have h2 : ∫ p in W, Dw γ p ^ 2 ≤ ∫ p in vlSlab a b, Dw γ p ^ 2 :=
          setIntegral_mono_set (hDwMem γ hγm).integrable_sq
            (ae_of_all _ fun p => sq_nonneg _) (ae_of_all _ hWS)
        have h3 := hNDw_ge γ hγmem
        have h4 := hQ
        have h5 : 0 ≤ NDH := hNDH0
        have h6 : 0 ≤ Q := hQ0
        rw [h1]
        linarith only [h2, h3, h4, h5, h6]
      · have hβ' : γ.dropLast ∈ sobolevWords m := mem_sobolevWords.2 (by
          have := mem_sobolevWords.1 hγ
          simp only [List.length_dropLast]; omega)
        have e0 : Dz' γ = Dg γ.dropLast (γ.getLastD 0) := hHigh γ hγm
        rw [e0]
        have hDgL := hDgMem γ.dropLast hβ'
        have h1 : ∫ p in W, Dg γ.dropLast (γ.getLastD 0) p ^ 2 ≤
            ∫ p in vlSlab a b, Dg γ.dropLast (γ.getLastD 0) p ^ 2 :=
          setIntegral_mono_set (hDgL _).integrable_sq (ae_of_all _ fun p => sq_nonneg _)
            (ae_of_all _ hWS)
        have h2 : ∫ p in vlSlab a b, Dg γ.dropLast (γ.getLastD 0) p ^ 2 ≤
            ∑ j : Fin 3, ∫ p in vlSlab a b, Dg γ.dropLast j p ^ 2 :=
          Finset.single_le_sum (f := fun j => ∫ p in vlSlab a b, Dg γ.dropLast j p ^ 2)
            (fun _ _ => integral_nonneg fun _ => sq_nonneg _) (Finset.mem_univ _)
        have h3 := hGradBound γ.dropLast hβ'
        linarith only [h1, h2, h3]
    _ = ((sobolevWords (m + 1)).card : ℝ) * (Q) := by rw [Finset.sum_const, nsmul_eq_mul]

private lemma lps_heat_gain_square_root_bound
    {A B N₁ N₂ Q₀ NDz NDG : ℝ}
    (hN₁0 : 0 ≤ N₁) (hN₂0 : 0 ≤ N₂) (hQ₀0 : 0 ≤ Q₀)
    (hNDz0 : 0 ≤ NDz) (hNDG0 : 0 ≤ NDG)
    (hA : A ≤ N₁ * (Q₀ * (NDz + NDG)))
    (hB : B ≤ N₂ * (Q₀ * (NDz + NDG))) :
    Real.sqrt A + Real.sqrt B ≤ (Real.sqrt (N₁ * Q₀) + Real.sqrt (N₂ * Q₀)) *
      (Real.sqrt NDz + Real.sqrt NDG) := by
  have hsA : Real.sqrt (A) ≤
      Real.sqrt (N₁ * Q₀) * Real.sqrt (NDz + NDG) := by
    rw [← Real.sqrt_mul (mul_nonneg hN₁0 hQ₀0)]
    exact Real.sqrt_le_sqrt (by linarith only [hA])
  have hsB : Real.sqrt (B) ≤
      Real.sqrt (N₂ * Q₀) * Real.sqrt (NDz + NDG) := by
    rw [← Real.sqrt_mul (mul_nonneg hN₂0 hQ₀0)]
    exact Real.sqrt_le_sqrt (by linarith only [hB])
  have hsS : Real.sqrt (NDz + NDG) ≤ Real.sqrt NDz + Real.sqrt NDG :=
    real_sqrt_add_le_add_sqrt hNDz0 hNDG0
  calc
    _ ≤ Real.sqrt (N₁ * Q₀) * Real.sqrt (NDz + NDG) + Real.sqrt (N₂ * Q₀) * Real.sqrt (NDz + NDG) :=
      add_le_add hsA hsB
    _ = (Real.sqrt (N₁ * Q₀) + Real.sqrt (N₂ * Q₀)) * Real.sqrt (NDz + NDG) := (add_mul _ _ _).symm
    _ ≤ (Real.sqrt (N₁ * Q₀) + Real.sqrt (N₂ * Q₀)) * (Real.sqrt NDz + Real.sqrt NDG) :=
      mul_le_mul_of_nonneg_left hsS (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

private lemma lps_curve_family_energy_bound
    {m : ℕ} {a b : ℝ} {Z : List (Fin 3) → Vec3 → ℝ}
    {Zc : List (Fin 3) → Lp ℝ 2 (volume : Measure Vec3)}
    {Dg : List (Fin 3) → Fin 3 → Vec3 × ℝ → ℝ} {Q : ℝ}
    (hZt : ∀ α, α ∈ sobolevWords m → Z α = (Zc α : Vec3 → ℝ))
    (hword : ∀ α, α ∈ sobolevWords m →
      ‖Zc α‖ ^ 2 + ∑ j : Fin 3, ∫ p in vlSlab a b, Dg α j p ^ 2 ≤ Q) :
    sobolevNormSqOn m (Set.univ : Set Vec3) Z ≤ ((sobolevWords m).card : ℝ) * Q := by
  unfold sobolevNormSqOn
  calc
    ∑ α ∈ sobolevWords m, ∫ x in (Set.univ : Set Vec3), Z α x ^ 2 ≤
        ∑ α ∈ sobolevWords m, Q := by
      refine Finset.sum_le_sum fun α hα => ?_
      rw [hZt α hα, Measure.restrict_univ]
      have hL2 := Lp.memLp (Zc α)
      have h2 : ∫ x, (Zc α : Vec3 → ℝ) x ^ 2 = ‖Zc α‖ ^ 2 := by
        rw [vl_integral_sq_eq hL2, Lp.norm_def]
      have h3 := hword α hα
      have h4 : 0 ≤ ∑ j : Fin 3, ∫ p in vlSlab a b, Dg α j p ^ 2 :=
        Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
      linarith only [h2, h3, h4]
    _ = ((sobolevWords m).card : ℝ) * (Q) := by rw [Finset.sum_const, nsmul_eq_mul]

private lemma lps_extended_family_sobolev
    {m : ℕ} {a b s : ℝ} {z : Vec3 × ℝ → ℝ}
    {Dz Dw Dz' : List (Fin 3) → Vec3 × ℝ → ℝ}
    {Dg : List (Fin 3) → Fin 3 → Vec3 × ℝ → ℝ}
    (hz : IsL2SobolevFamilyOn m (Set.univ : Set Vec3) (Ioo a b) z Dz)
    (hVm : MeasurableSet ((univ : Set Vec3) ×ˢ Ioo a b))
    (hWV : ((univ : Set Vec3) ×ˢ Ioo s b) ⊆ ((univ : Set Vec3) ×ˢ Ioo a b))
    (hLow : ∀ α, α.length ≤ m → Dz' α = Dz α)
    (hHigh : ∀ α, ¬α.length ≤ m → Dz' α = Dg α.dropLast (α.getLastD 0))
    (hDgMem : ∀ α, α ∈ sobolevWords m → ∀ j, MemLp (Dg α j) 2 (volume.restrict (vlSlab a b)))
    (hDgWeak : ∀ α, α ∈ sobolevWords m → ∀ j,
      IsSpaceTimeWeakPartial (vlSlab a b) j (Dw α) (Dg α j))
    (hDwW : ∀ α, α.length ≤ m → Dw α =ᵐ[volume.restrict ((univ : Set Vec3) ×ˢ Ioo s b)] Dz α) :
    IsL2SobolevFamilyOn (m + 1) (Set.univ : Set Vec3) (Ioo s b) z Dz' := by
  refine ⟨fun α hα => ?_, ?_, fun α j hα => ?_⟩
  · by_cases hαm : α.length ≤ m
    · rw [hLow α hαm]
      exact (hz.memL2 α hαm).mono_measure (Measure.restrict_mono hWV le_rfl)
    · have hβ' : α.dropLast ∈ sobolevWords m := mem_sobolevWords.2 (by
        simp only [List.length_dropLast]; omega)
      rw [hHigh α hαm]
      exact (hDgMem α.dropLast hβ' (α.getLastD 0)).mono_measure (Measure.restrict_mono hWV le_rfl)
  · rw [hLow [] (Nat.zero_le _)]
    exact ae_restrict_of_ae_restrict_of_subset hWV hz.zero
  · have hαm : α.length ≤ m := by omega
    have e0 : Dz' α = Dz α := by rw [hLow α hαm]
    rw [e0]
    by_cases hαlt : α.length < m
    · have hαj : (α ++ [j]).length ≤ m := by
        simp only [List.length_append, List.length_singleton]; omega
      have e1 : Dz' (α ++ [j]) = Dz (α ++ [j]) := hLow (α ++ [j]) hαj
      rw [e1]
      exact IsSpaceTimeWeakPartial.mono (hz.weak α j hαlt) hVm hWV
    · have hαj : ¬ (α ++ [j]).length ≤ m := by
        simp only [List.length_append, List.length_singleton]; omega
      have hαmem : α ∈ sobolevWords m := mem_sobolevWords.2 hαm
      have e1 : Dz' (α ++ [j]) = Dg α j := by
        rw [hHigh (α ++ [j]) hαj]
        simp only [List.dropLast_concat, List.getLastD_concat]
      rw [e1]
      exact ((hDgWeak α hαmem j).mono hVm hWV).congr_left (hDwW α hαm)

private lemma lps_sobolev_normsq_congr
    {m : ℕ} {a b : ℝ} {D E : List (Fin 3) → Vec3 × ℝ → ℝ}
    (hEq : ∀ α, α.length ≤ m →
      D α =ᵐ[volume.restrict ((univ : Set Vec3) ×ˢ Ioo a b)] E α) :
    (∑ α ∈ sobolevWords m, ∫ p in vlSlab a b, E α p ^ 2) =
      l2SobolevNormSqOn m (Set.univ : Set Vec3) (Ioo a b) D := by
  refine Finset.sum_congr rfl fun α hα => integral_congr_ae ?_
  filter_upwards [hEq α (mem_sobolevWords.1 hα)] with p hp
  rw [hp]

/-- `lem:local-heat-gain` on the whole space and for every order `m ≥ 1`
(`prop:lps-smoothing`). The family `Dz'` of the gained regularity agrees with
the given family `Dz` through order `m`. -/
theorem lps_wholeHeatGain (m : ℕ) (hm : 1 ≤ m) {σ β : ℝ} (hσ : 0 < σ) (hσβ : σ < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℝ) (z G : Vec3 × ℝ → ℝ) (Dz DG : List (Fin 3) → Vec3 × ℝ → ℝ),
      IsL2SobolevFamilyOn m (Set.univ : Set Vec3) (Ioo a (a + β)) z Dz →
      IsL2SobolevFamilyOn (m - 1) (Set.univ : Set Vec3) (Ioo a (a + β)) G DG →
      IsHeatSolutionOn (Set.univ : Set Vec3) (Ioo a (a + β)) z G →
      ∃ (Z : ℝ → List (Fin 3) → Vec3 → ℝ) (Dz' : List (Fin 3) → Vec3 × ℝ → ℝ),
        (∀ t ∈ Icc (a + σ) (a + β),
          IsSobolevFamilyOn m (Set.univ : Set Vec3) (Z t []) (Z t)) ∧
        (∀ α : List (Fin 3), α.length ≤ m → ∀ t ∈ Icc (a + σ) (a + β),
          Tendsto (fun t' => eLpNorm (Z t' α - Z t α) 2 volume)
            (nhdsWithin t (Icc (a + σ) (a + β))) (nhds 0)) ∧
        (∀ᵐ t ∂(volume.restrict (Ioo (a + σ) (a + β))),
          Z t [] =ᵐ[volume] fun x => z (x, t)) ∧
        IsL2SobolevFamilyOn (m + 1) (Set.univ : Set Vec3) (Ioo (a + σ) (a + β)) z Dz' ∧
        (∀ α : List (Fin 3), α.length ≤ m → ∀ᵐ p ∂(volume.restrict
          ((Set.univ : Set Vec3) ×ˢ Ioo (a + σ) (a + β))), Dz' α p = Dz α p) ∧
        ∀ t ∈ Icc (a + σ) (a + β),
          Real.sqrt (sobolevNormSqOn m (Set.univ : Set Vec3) (Z t)) +
              Real.sqrt (l2SobolevNormSqOn (m + 1) (Set.univ : Set Vec3)
                (Ioo (a + σ) (a + β)) Dz') ≤
            C * (Real.sqrt (l2SobolevNormSqOn m (Set.univ : Set Vec3) (Ioo a (a + β)) Dz) +
              Real.sqrt (l2SobolevNormSqOn (m - 1) (Set.univ : Set Vec3)
                (Ioo a (a + β)) DG)) := by
  obtain ⟨θ₀, hθ₀, hθ₀0, hθ₀1, hθ₀nn, hθ₀le, Lθ, hLθ0, hLθ⟩ := vorticityTimeCutoff_exists hσ
  set N₁ : ℝ := ((sobolevWords m).card : ℝ) with hN₁
  set N₂ : ℝ := ((sobolevWords (m + 1)).card : ℝ) with hN₂
  set Q₀ : ℝ := 4 * (1 + Lθ ^ 2) with hQ₀
  have hQ₀0 : 0 ≤ Q₀ := by positivity
  refine ⟨Real.sqrt (N₁ * Q₀) + Real.sqrt (N₂ * Q₀), by positivity, ?_⟩
  intro a z G Dz DG hz hG hheat
  set b : ℝ := a + β with hb
  set s : ℝ := a + σ with hs
  have hab : a < b := by rw [hb]; linarith only [hσ, hσβ]
  have has : a < s := by rw [hs]; linarith only [hσ]
  have hVm : MeasurableSet ((univ : Set Vec3) ×ˢ Ioo a b) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  -- measurable modifications of the data
  obtain ⟨Dzm, hDzm_eq, hDzm_sm⟩ := lps_sobolev_family_measurable_version hz
  obtain ⟨DGm, hDGm_eq, hDGm_sm⟩ := lps_sobolev_family_measurable_version hG
  have hDzF : IsSpaceTimeFamily m (vlSlab a b) Dz := ⟨hz.memL2, hz.weak⟩
  have hDGF : IsSpaceTimeFamily (m - 1) (vlSlab a b) DG := ⟨hG.memL2, hG.weak⟩
  have hDzmF : IsSpaceTimeFamily m (vlSlab a b) Dzm := hDzF.congr_ae hDzm_eq
  have hDGmF : IsSpaceTimeFamily (m - 1) (vlSlab a b) DGm := hDGF.congr_ae hDGm_eq
  have hheat' : IsHeatSolutionOn univ (Ioo a b) (Dzm []) (DGm []) :=
    hheat.congr_ae (hz.zero.symm.trans (hDzm_eq [] (Nat.zero_le _)))
      (hG.zero.symm.trans (hDGm_eq [] (Nat.zero_le _)))
  -- the time cutoff
  let c : ℝ → ℝ := fun t => θ₀ (t - a)
  have hc : ContDiff ℝ (⊤ : ℕ∞) c := hθ₀.comp (contDiff_id.sub contDiff_const)
  have hcb : ∀ t, |c t| ≤ 1 := fun t => by
    rw [abs_le]; exact ⟨by linarith only [hθ₀nn (t - a)], hθ₀le _⟩
  have hdc : ∀ t, deriv c t = deriv θ₀ (t - a) := fun t =>
    deriv_comp_sub_const (f := θ₀) (a := a) (x := t)
  have hdcb : ∀ t, |deriv c t| ≤ Lθ := fun t => by rw [hdc]; exact hLθ _
  have hc' : ContDiff ℝ (⊤ : ℕ∞) (deriv c) := (contDiff_infty_iff_deriv.mp hc).2
  have hc0 (t : ℝ) (ht : t < a + σ / 2) : c t = 0 := hθ₀0 _ (by linarith only [ht])
  have hc1 (t : ℝ) (ht : s ≤ t) : c t = 1 := hθ₀1 _ (by rw [hs] at ht; linarith only [ht])
  -- the cutoff solution
  let Dw : List (Fin 3) → Vec3 × ℝ → ℝ := fun α p => c p.2 * Dzm α p
  let DH : List (Fin 3) → Vec3 × ℝ → ℝ := fun α p => c p.2 * DGm α p + deriv c p.2 * Dzm α p
  have hDwU : IsSpaceTimeFamily m (vlSlab a b) Dw := hDzmF.time_mul hc hcb
  have hDHU : IsSpaceTimeFamily (m - 1) (vlSlab a b) DH :=
    (hDGmF.time_mul hc hcb).add ((hDzmF.mono_order (Nat.sub_le m 1)).time_mul hc' hdcb)
  have hheatU : IsHeatSolutionOn univ (Ioo a b) (Dw []) (DH []) :=
    hheat'.time_mul (hDzmF.memL2 [] (Nat.zero_le _)) (hDGmF.memL2 [] (Nat.zero_le _)) hc
  have hcm : StronglyMeasurable (fun p : Vec3 × ℝ => c p.2) :=
    (hc.continuous.comp continuous_snd).stronglyMeasurable
  have hc'm : StronglyMeasurable (fun p : Vec3 × ℝ => deriv c p.2) :=
    (hc'.continuous.comp continuous_snd).stronglyMeasurable
  have hDw_sm (α : List (Fin 3)) : StronglyMeasurable (Dw α) := hcm.mul (hDzm_sm α)
  have hDH_sm (α : List (Fin 3)) : StronglyMeasurable (DH α) :=
    (hcm.mul (hDGm_sm α)).add (hc'm.mul (hDzm_sm α))
  have hvan (α : List (Fin 3)) (p : Vec3 × ℝ) (hp : p.2 < a + σ / 2) : Dw α p = 0 := by
    simp only [Dw, hc0 p.2 hp, zero_mul]
  have hone (α : List (Fin 3)) (p : Vec3 × ℝ) (hp : s ≤ p.2) : Dw α p = Dzm α p := by
    simp only [Dw, hc1 p.2 hp, one_mul]
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
    · obtain ⟨Zc, Dg, h⟩ := localHeatGain_wordEnergy hm hab (half_pos hσ) hDwU hDHU hheatU
        hDw_sm hDH_sm hvan β' hβ'
      exact ⟨Zc, Dg, fun _ => h⟩
    · exact ⟨fun _ => 0, fun _ _ => 0, fun h => absurd h hβ'⟩
  choose Zc Dg hZD using hall
  -- the norm bounds
  set NDz := l2SobolevNormSqOn m (Set.univ : Set Vec3) (Ioo a b) Dz with hNDz
  set NDG := l2SobolevNormSqOn (m - 1) (Set.univ : Set Vec3) (Ioo a b) DG with hNDG
  have hNDz0 : 0 ≤ NDz := Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
  have hNDG0 : 0 ≤ NDG := Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
  have hNDzm : ∑ α ∈ sobolevWords m, ∫ p in vlSlab a b, Dzm α p ^ 2 = NDz :=
    lps_sobolev_normsq_congr hDzm_eq
  have hNDGm : ∑ α ∈ sobolevWords (m - 1), ∫ p in vlSlab a b, DGm α p ^ 2 = NDG :=
    lps_sobolev_normsq_congr hDGm_eq
  set NDw := ∑ α ∈ sobolevWords m, ∫ p in vlSlab a b, Dw α p ^ 2 with hNDw
  set NDH := ∑ α ∈ sobolevWords (m - 1), ∫ p in vlSlab a b, DH α p ^ 2 with hNDH
  have hNw' : NDw ≤ NDz := by
    rw [← hNDzm]
    exact Finset.sum_le_sum fun α hα =>
      integral_sq_time_mul_le (hDzmF.memL2 α (mem_sobolevWords.1 hα)) hc.continuous hcb
  have hNzm1 : ∑ α ∈ sobolevWords (m - 1), ∫ p in vlSlab a b, Dzm α p ^ 2 ≤ NDz := by
    rw [← hNDzm]
    exact Finset.sum_le_sum_of_subset_of_nonneg (sobolevWords_mono (Nat.sub_le m 1))
      fun _ _ _ => integral_nonneg fun _ => sq_nonneg _
  have hNH' : NDH ≤ 2 * NDG + 2 * Lθ ^ 2 * NDz := by
    have h1 : NDH ≤ ∑ α ∈ sobolevWords (m - 1), (2 * (∫ p in vlSlab a b, DGm α p ^ 2) +
        2 * Lθ ^ 2 * ∫ p in vlSlab a b, Dzm α p ^ 2) :=
      Finset.sum_le_sum fun α hα => integral_sq_time_mul_add_le
        (hDzmF.memL2 α ((mem_sobolevWords.1 hα).trans (Nat.sub_le m 1)))
        (hDGmF.memL2 α (mem_sobolevWords.1 hα)) hc.continuous hc'.continuous hcb hdcb
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hNDGm] at h1
    have h2 : 0 ≤ 2 * Lθ ^ 2 := by positivity
    have h3 := mul_le_mul_of_nonneg_left hNzm1 h2
    linarith only [h1, h3]
  set S : ℝ := NDz + NDG with hS
  have hS0 : 0 ≤ S := add_nonneg hNDz0 hNDG0
  have hQ : 2 * (NDH + NDw) ≤ Q₀ * S := by
    rw [hQ₀, hS]
    nlinarith only [hNw', hNH', hNDz0, hNDG0, mul_nonneg (sq_nonneg Lθ) hNDG0]
  have hNDw_ge (β' : List (Fin 3)) (hβ' : β' ∈ sobolevWords m) :
      ∫ p in vlSlab a b, Dw β' p ^ 2 ≤ NDw :=
    Finset.single_le_sum (f := fun α => ∫ p in vlSlab a b, Dw α p ^ 2)
      (fun _ _ => integral_nonneg fun _ => sq_nonneg _) hβ'
  have hword (β' : List (Fin 3)) (hβ' : β' ∈ sobolevWords m) (t : Icc a b) :
      ‖Zc β' t‖ ^ 2 + ∑ j : Fin 3, ∫ p in vlSlab a b, Dg β' j p ^ 2 ≤ Q₀ * S := by
    have h := (hZD β' hβ').2.2.2.2 t
    have h2 := hNDw_ge β' hβ'
    linarith only [h, h2, hQ]
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
  set W : Set (Vec3 × ℝ) := (univ : Set Vec3) ×ˢ Ioo s b with hW
  have hWm : MeasurableSet W := MeasurableSet.univ.prod measurableSet_Ioo
  have hWV : W ⊆ (univ : Set Vec3) ×ˢ Ioo a b := prod_mono subset_rfl (Ioo_subset_Ioo_left has.le)
  have hWS : W ⊆ vlSlab a b := hWV
  have hSm : MeasurableSet (vlSlab a b) := hVm
  -- on `W` the cutoff solution is `Dz`
  have hDwW (α : List (Fin 3)) (hα : α.length ≤ m) :
      Dw α =ᵐ[volume.restrict W] Dz α := by
    have h1 : Dzm α =ᵐ[volume.restrict W] Dz α :=
      ae_restrict_of_ae_restrict_of_subset hWV (hDzm_eq α hα).symm
    filter_upwards [h1, ae_restrict_mem hWm] with p hp hpW
    rw [hone α p hpW.2.1.le, hp]
  refine ⟨Z, Dz', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `H^m` families at every time
    intro t ht
    have htab := hIccsub ht
    refine ⟨Filter.EventuallyEq.rfl, fun α hα => ?_, fun α j hα => ?_⟩
    · rw [hZt t htab α (mem_sobolevWords.2 hα)]
      exact (Lp.memLp _).restrict _
    · have hαm : α ∈ sobolevWords m := mem_sobolevWords.2 hα.le
      have hαj : α ++ [j] ∈ sobolevWords m := mem_sobolevWords.2 (by
        simp only [List.length_append, List.length_singleton]; omega)
      rw [hZt t htab α hαm, hZt t htab _ hαj]
      intro ψ hψ hψc _
      have hcw := curve_weakPartial_of_slab hab
        (hDwU.memL2 α hα.le) (hDwU.memL2 (α ++ [j]) (mem_sobolevWords.1 hαj))
        (hDwU.weak α j hα) (hZD α hαm).1 (hZD _ hαj).1 (hZD α hαm).2.1 (hZD _ hαj).2.1
        ψ hψ hψc ⟨t, htab⟩
      rw [Measure.restrict_univ]
      exact hcw
  · -- continuity in `L²(ℝ³)`
    intro α hα t ht
    exact lps_l2_curve_representative_continuity has (Zc α)
      (hZD α (mem_sobolevWords.2 hα)).1 (fun t' => Z t' α)
      (fun t' ht' => hZt t' ht' α (mem_sobolevWords.2 hα)) t ht
  · -- the time slices
    have hsub : Ioo s b ⊆ Ioo a b := Ioo_subset_Ioo_left has.le
    have h1 := ae_restrict_of_ae_restrict_of_subset hsub
      (hZD [] (mem_sobolevWords.2 (Nat.zero_le _))).2.1
    have h2 := ae_restrict_of_ae_restrict_of_subset hsub
      (ae_slices_of_ae_prod (B := univ) (I := Ioo a b) (hz.zero.symm.trans
        (hDzm_eq [] (Nat.zero_le _))))
    filter_upwards [h1, h2, ae_restrict_mem measurableSet_Ioo] with t ht1 ht2 htmem
    have htab : t ∈ Icc a b := Ioo_subset_Icc_self (hsub htmem)
    rw [hZt t htab [] (mem_sobolevWords.2 (Nat.zero_le _))]
    rw [Measure.restrict_univ] at ht2
    filter_upwards [ht1 htab, ht2] with x hx3 hx4
    rw [hx3, hx4]
    exact hone [] (x, t) htmem.1.le
  · -- the `L²_t H^{m+1}_x` family
    exact lps_extended_family_sobolev hz hVm hWV
      (fun α hα => by simp only [Dz', hα, ite_true])
      (fun α hα => by simp only [Dz', hα, ite_false])
      (fun α hα => (hZD α hα).2.2.1)
      (fun α hα => (hZD α hα).2.2.2.1) hDwW
  · -- agreement with the given family through order `m`
    intro α hα
    exact ae_of_all _ fun p => by simp only [Dz', hα, ite_true]
  · -- the estimate
    intro t ht
    have htab := hIccsub ht
    -- the curve part
    have hA : sobolevNormSqOn m (Set.univ : Set Vec3) (Z t) ≤ N₁ * (Q₀ * S) :=
      lps_curve_family_energy_bound (fun α hα => hZt t htab α hα)
        (fun α hα => hword α hα ⟨t, htab⟩)
    -- the gradient part
    have hB : l2SobolevNormSqOn (m + 1) (Set.univ : Set Vec3) (Ioo s b) Dz' ≤
        N₂ * (Q₀ * S) :=
      lps_extended_family_energy_bound
        (Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _)
        (mul_nonneg hQ₀0 hS0) hQ
        (fun γ hγ => by simp only [Dz', hγ, ite_true])
        (fun γ hγ => by simp only [Dz', hγ, ite_false]) hWS hDwU.memL2
        (fun α hα => (hZD α hα).2.2.1) hDwW hNDw_ge (by
          intro α hα
          have h := hword α hα ⟨b, right_mem_Icc.2 hab.le⟩
          have hnonneg := sq_nonneg ‖Zc α ⟨b, right_mem_Icc.2 hab.le⟩‖
          linarith only [h, hnonneg])
    exact lps_heat_gain_square_root_bound (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      hQ₀0 hNDz0 hNDG0 hA hB

end ESS
