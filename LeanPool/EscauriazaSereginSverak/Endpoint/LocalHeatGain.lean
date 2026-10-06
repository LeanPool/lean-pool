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
  let Dzm : List (Fin 3) → Vec3 × ℝ → ℝ := fun α =>
    if h : α.length ≤ m then (hz.memL2 α h).aestronglyMeasurable.mk (Dz α) else fun _ => 0
  let DGm : List (Fin 3) → Vec3 × ℝ → ℝ := fun α =>
    if h : α.length ≤ m - 1 then (hG.memL2 α h).aestronglyMeasurable.mk (DG α) else fun _ => 0
  have hDzm_eq (α : List (Fin 3)) (hα : α.length ≤ m) :
      Dz α =ᵐ[volume.restrict (U ×ˢ I)] Dzm α := by
    simp only [Dzm, hα, ↓reduceDIte]
    exact (hz.memL2 α hα).aestronglyMeasurable.ae_eq_mk
  have hDGm_eq (α : List (Fin 3)) (hα : α.length ≤ m - 1) :
      DG α =ᵐ[volume.restrict (U ×ˢ I)] DGm α := by
    simp only [DGm, hα, ↓reduceDIte]
    exact (hG.memL2 α hα).aestronglyMeasurable.ae_eq_mk
  have hDzm_sm (α : List (Fin 3)) : StronglyMeasurable (Dzm α) := by
    by_cases hα : α.length ≤ m
    · simp only [Dzm, hα, ↓reduceDIte]
      exact (hz.memL2 α hα).aestronglyMeasurable.stronglyMeasurable_mk
    · simp only [Dzm, hα, ↓reduceDIte]
      exact stronglyMeasurable_const
  have hDGm_sm (α : List (Fin 3)) : StronglyMeasurable (DGm α) := by
    by_cases hα : α.length ≤ m - 1
    · simp only [DGm, hα, ↓reduceDIte]
      exact (hG.memL2 α hα).aestronglyMeasurable.stronglyMeasurable_mk
    · simp only [DGm, hα, ↓reduceDIte]
      exact stronglyMeasurable_const
  have hDzF : IsSpaceTimeFamily m (U ×ˢ I) Dz := ⟨hz.memL2, hz.weak⟩
  have hDGF : IsSpaceTimeFamily (m - 1) (U ×ˢ I) DG := ⟨hG.memL2, hG.weak⟩
  have hDzmF : IsSpaceTimeFamily m (U ×ˢ I) Dzm := hDzF.congr_ae hDzm_eq
  have hDGmF : IsSpaceTimeFamily (m - 1) (U ×ˢ I) DGm := hDGF.congr_ae hDGm_eq
  have hheat' : IsHeatSolutionOn U I (Dzm []) (DGm []) :=
    CKN.IsHeatSolutionOn.congr_ae hheat (hz.zero.symm.trans (hDzm_eq [] (Nat.zero_le _)))
      (hG.zero.symm.trans (hDGm_eq [] (Nat.zero_le _)))
  -- the cutoff solution
  obtain ⟨hDwU, hDHU, hDw0, hDH0⟩ := localHeatGain_families hm1 hUm hIm hη hN hKN hκ hκc hκR
    hκN hDzmF hDGmF
  have hheatU := localHeatGain_heat hIm hη hm1 hDzmF hDGmF hheat'
  set Dw := localHeatGainDw η Dzm with hDw
  set DH := localHeatGainDH η Dzm DGm with hDH
  have hAsm (ζ : Vec3 × ℝ → ℝ) (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (γ : List (Fin 3)) :
      StronglyMeasurable (spaceTimeWord γ ζ) :=
    (contDiff_spaceTimeWord γ hζ).continuous.stronglyMeasurable
  have hDw_sm (α : List (Fin 3)) : StronglyMeasurable (Dw α) :=
    stLeibniz_stronglyMeasurable α (hAsm η hη.smooth) hDzm_sm
  have hDH_sm (α : List (Fin 3)) : StronglyMeasurable (DH α) := by
    refine (stLeibniz_stronglyMeasurable α (hAsm η hη.smooth) hDGm_sm).add
      ((stLeibniz_stronglyMeasurable α (hAsm _ hη.smooth_zeta) hDzm_sm).add
        (stronglyMeasurable_const.mul (Finset.stronglyMeasurable_fun_sum _ fun j _ =>
          stLeibniz_stronglyMeasurable α (hAsm _ (hη.smooth_grad j))
            fun γ => hDzm_sm (j :: γ))))
  have hvan (α : List (Fin 3)) (p : Vec3 × ℝ) (hp : p.2 < a + σ / 2) : Dw α p = 0 :=
    stLeibniz_eq_zero_of_forall α fun γ => hη0 γ p hp.le
  have hone (α : List (Fin 3)) (p : Vec3 × ℝ) (hp1 : p.1 ∈ vec3Ball x₀ r) (hp2 : s ≤ p.2) :
      Dw α p = Dzm α p :=
    stLeibniz_eq_of_unit α (hη1 p hp1 hp2).1 (hη1 p hp1 hp2).2
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
  have hNDzm : ∑ α ∈ sobolevWords m, ∫ p in U ×ˢ I, Dzm α p ^ 2 = NDz := by
    refine Finset.sum_congr rfl fun α hα => integral_congr_ae ?_
    filter_upwards [hDzm_eq α (mem_sobolevWords.1 hα)] with p hp
    rw [hp]
  have hNDGm : ∑ α ∈ sobolevWords (m - 1), ∫ p in U ×ˢ I, DGm α p ^ 2 = NDG := by
    refine Finset.sum_congr rfl fun α hα => integral_congr_ae ?_
    filter_upwards [hDGm_eq α (mem_sobolevWords.1 hα)] with p hp
    rw [hp]
  rw [hNDzm] at hNw hNH
  rw [hNDGm] at hNH
  set NDw := ∑ α ∈ sobolevWords m, ∫ p in vlSlab a b, Dw α p ^ 2 with hNDw
  set NDH := ∑ α ∈ sobolevWords (m - 1), ∫ p in vlSlab a b, DH α p ^ 2 with hNDH
  have hNw' : NDw ≤ Kc * L ^ 2 * NDz := hNw
  have hNH' : NDH ≤ Kc * L ^ 2 * (NDz + NDG) := hNH
  set S : ℝ := NDz + NDG with hS
  have hS0 : 0 ≤ S := add_nonneg hNDz0 hNDG0
  have hQ : 2 * (NDH + NDw) ≤ Q₀ * S := by
    have h1 : Kc * L ^ 2 * NDz ≤ Kc * L ^ 2 * S :=
      mul_le_mul_of_nonneg_left (by linarith only [hNDG0]) (by positivity)
    rw [hQ₀]
    nlinarith only [hNw', hNH', h1]
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
    rw [hone α p hpW.1 hpW.2.1.le, hp]
  refine ⟨Z, Dz', ?_, ?_, ?_, ?_, ?_⟩
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
      intro ψ hψ hψc hψB
      have hcw := curve_weakPartial_of_slab hab
        (hDwU.memL2 α hα.le) (hDwU.memL2 (α ++ [j]) (mem_sobolevWords.1 hαj))
        (hDwU.weak α j hα) (hZD α hαm).1 (hZD _ hαj).1 (hZD α hαm).2.1 (hZD _ hαj).2.1
        ψ hψ hψc ⟨t, htab⟩
      have e1 : ∫ x in vec3Ball x₀ r, (Zc α ⟨t, htab⟩ : Vec3 → ℝ) x *
          (fderiv ℝ ψ x) (basisVec j) =
          ∫ x, (Zc α ⟨t, htab⟩ : Vec3 → ℝ) x * spatialDeriv ψ j x :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
          have hx' : x ∉ tsupport ψ := fun h => hx (hψB h)
          change _ * spatialDeriv ψ j x = 0
          rw [image_eq_zero_of_notMem_tsupport (f := spatialDeriv ψ j) (fun h => hx'
            (tsupport_fderiv_apply_subset ℝ (basisVec j) h)), mul_zero]
      have e2 : ∫ x in vec3Ball x₀ r, (Zc (α ++ [j]) ⟨t, htab⟩ : Vec3 → ℝ) x * ψ x =
          ∫ x, (Zc (α ++ [j]) ⟨t, htab⟩ : Vec3 → ℝ) x * ψ x :=
        setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
          rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hψB h)), mul_zero]
      rw [e1, e2]
      exact hcw
  · -- continuity in `L²(B_r)`
    intro α hα t ht
    have hαm : α ∈ sobolevWords m := mem_sobolevWords.2 hα
    let F : ℝ → Lp ℝ 2 (volume : Measure Vec3) := fun t' =>
      if h : t' ∈ Icc a b then Zc α ⟨t', h⟩ else 0
    have hFc : ContinuousOn F (Icc a b) := by
      rw [continuousOn_iff_continuous_domRestrict]
      refine (hZD α hαm).1.congr fun t' => ?_
      simp only [F, Set.domRestrict_apply, t'.2, ↓reduceDIte]
    have hFt : Tendsto (fun t' => ‖F t' - F t‖) (𝓝[Icc s b] t) (𝓝 0) := by
      have h := ((hFc t (hIccsub ht)).mono hIccsub).sub
        (continuousWithinAt_const (b := F t))
      have h2 := h.norm.tendsto
      simpa using h2
    have hbound : ∀ᶠ t' in 𝓝[Icc s b] t,
        eLpNorm (Z t' α - Z t α) 2 (volume.restrict (vec3Ball x₀ r)) ≤
          ENNReal.ofReal ‖F t' - F t‖ := by
      filter_upwards [self_mem_nhdsWithin] with t' ht'
      have ht'ab := hIccsub ht'
      have htab := hIccsub ht
      have hF' : F t' = Zc α ⟨t', ht'ab⟩ := by simp only [F, ht'ab, ↓reduceDIte]
      have hF : F t = Zc α ⟨t, htab⟩ := by simp only [F, htab, ↓reduceDIte]
      rw [hZt t' ht'ab α hαm, hZt t htab α hαm, hF', hF, ofReal_norm, Lp.enorm_def]
      calc
        eLpNorm ((Zc α ⟨t', ht'ab⟩ : Vec3 → ℝ) - (Zc α ⟨t, htab⟩ : Vec3 → ℝ)) 2
            (volume.restrict (vec3Ball x₀ r)) ≤
            eLpNorm ((Zc α ⟨t', ht'ab⟩ : Vec3 → ℝ) - (Zc α ⟨t, htab⟩ : Vec3 → ℝ)) 2 volume :=
          eLpNorm_mono_measure _ Measure.restrict_le_self
        _ = eLpNorm (⇑(Zc α ⟨t', ht'ab⟩ - Zc α ⟨t, htab⟩)) 2 volume :=
          eLpNorm_congr_ae (Lp.coeFn_sub _ _).symm
    have hlim : Tendsto (fun t' => ENNReal.ofReal ‖F t' - F t‖) (𝓝[Icc s b] t) (𝓝 0) := by
      have h := (ENNReal.tendsto_ofReal hFt)
      simpa using h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => bot_le) hbound
  · -- the time slices
    have hsub : Ioo s b ⊆ Ioo a b := Ioo_subset_Ioo_left has.le
    have h1 := ae_restrict_of_ae_restrict_of_subset hsub
      (hZD [] (mem_sobolevWords.2 (Nat.zero_le _))).2.1
    have h2 := ae_restrict_of_ae_restrict_of_subset hsub
      (ae_slices_of_ae_prod (B := U) (I := I) (hz.zero.symm.trans
        (hDzm_eq [] (Nat.zero_le _))))
    filter_upwards [h1, h2, ae_restrict_mem measurableSet_Ioo] with t ht1 ht2 htmem
    have htab : t ∈ Icc a b := Ioo_subset_Icc_self (hsub htmem)
    rw [hZt t htab [] (mem_sobolevWords.2 (Nat.zero_le _))]
    have h3 : (Zc [] ⟨t, htab⟩ : Vec3 → ℝ) =ᵐ[volume.restrict (vec3Ball x₀ r)]
        fun x => Dw [] (x, t) := ae_restrict_of_ae (ht1 htab)
    have h4 : (fun x => z (x, t)) =ᵐ[volume.restrict (vec3Ball x₀ r)]
        fun x => Dzm [] (x, t) := ae_restrict_of_ae_restrict_of_subset hrR' ht2
    filter_upwards [h3, h4, ae_restrict_mem (isOpen_vec3Ball x₀ r).measurableSet]
      with x hx3 hx4 hxr
    rw [hx3, hx4]
    exact hone [] (x, t) hxr htmem.1.le
  · -- the `L²_t H^{m+1}_x` family
    refine ⟨fun α hα => ?_, ?_, fun α j hα => ?_⟩
    · by_cases hαm : α.length ≤ m
      · simp only [Dz', hαm, ite_true]
        exact (hz.memL2 α hαm).mono_measure (Measure.restrict_mono hWV le_rfl)
      · have hne : α ≠ [] := fun h => hαm (by simp [h])
        have hβ' : α.dropLast ∈ sobolevWords m := mem_sobolevWords.2 (by
          simp only [List.length_dropLast]; omega)
        simp only [Dz', hαm, ite_false]
        exact ((hZD _ hβ').2.2.1 _).mono_measure (Measure.restrict_mono hWS le_rfl)
    · simp only [Dz', Nat.zero_le, ite_true, List.length_nil]
      exact ae_restrict_of_ae_restrict_of_subset hWV hz.zero
    · have hαm : α.length ≤ m := by omega
      have e0 : Dz' α = Dz α := by simp only [Dz', hαm, ite_true]
      rw [e0]
      by_cases hαlt : α.length < m
      · have hαj : (α ++ [j]).length ≤ m := by
          simp only [List.length_append, List.length_singleton]; omega
        have e1 : Dz' (α ++ [j]) = Dz (α ++ [j]) := by simp only [Dz', hαj, ite_true]
        rw [e1]
        exact IsSpaceTimeWeakPartial.mono (hz.weak α j hαlt) hVm hWV
      · have hαj : ¬ (α ++ [j]).length ≤ m := by
          simp only [List.length_append, List.length_singleton]; omega
        have hαmem : α ∈ sobolevWords m := mem_sobolevWords.2 hαm
        have e1 : Dz' (α ++ [j]) = Dg α j := by
          simp only [Dz', hαj, ite_false, List.dropLast_concat, List.getLastD_concat]
        rw [e1]
        exact (((hZD α hαmem).2.2.2.1 j).mono hSm hWS).congr_left (hDwW α hαm)
  · -- the estimate
    intro t ht
    have htab := hIccsub ht
    -- the curve part
    have hA : sobolevNormSqOn m (vec3Ball x₀ r) (Z t) ≤ N₁ * (Q₀ * S) := by
      unfold sobolevNormSqOn
      calc
        ∑ α ∈ sobolevWords m, ∫ x in vec3Ball x₀ r, Z t α x ^ 2 ≤
            ∑ α ∈ sobolevWords m, Q₀ * S := by
          refine Finset.sum_le_sum fun α hα => ?_
          rw [hZt t htab α hα]
          have hL2 := Lp.memLp (Zc α ⟨t, htab⟩)
          have h1 : ∫ x in vec3Ball x₀ r, (Zc α ⟨t, htab⟩ : Vec3 → ℝ) x ^ 2 ≤
              ∫ x, (Zc α ⟨t, htab⟩ : Vec3 → ℝ) x ^ 2 :=
            setIntegral_le_integral hL2.integrable_sq (ae_of_all _ fun x => sq_nonneg _)
          have h2 : ∫ x, (Zc α ⟨t, htab⟩ : Vec3 → ℝ) x ^ 2 = ‖Zc α ⟨t, htab⟩‖ ^ 2 := by
            rw [vl_integral_sq_eq hL2, Lp.norm_def]
          have h3 := hword α hα ⟨t, htab⟩
          have h4 : 0 ≤ ∑ j : Fin 3, ∫ p in vlSlab a b, Dg α j p ^ 2 :=
            Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
          linarith only [h1, h2, h3, h4]
        _ = N₁ * (Q₀ * S) := by rw [Finset.sum_const, nsmul_eq_mul]
    -- the gradient part
    have hB : l2SobolevNormSqOn (m + 1) (vec3Ball x₀ r) (Ioo s b) Dz' ≤ N₂ * (Q₀ * S) := by
      unfold l2SobolevNormSqOn
      calc
        ∑ γ ∈ sobolevWords (m + 1), ∫ p in W, Dz' γ p ^ 2 ≤
            ∑ γ ∈ sobolevWords (m + 1), Q₀ * S := by
          refine Finset.sum_le_sum fun γ hγ => ?_
          by_cases hγm : γ.length ≤ m
          · have e0 : Dz' γ = Dz γ := by simp only [Dz', hγm, ite_true]
            rw [e0]
            have hγmem : γ ∈ sobolevWords m := mem_sobolevWords.2 hγm
            have h1 : ∫ p in W, Dz γ p ^ 2 = ∫ p in W, Dw γ p ^ 2 :=
              integral_congr_ae ((hDwW γ hγm).mono fun p hp => by simp only [hp])
            have h2 : ∫ p in W, Dw γ p ^ 2 ≤ ∫ p in vlSlab a b, Dw γ p ^ 2 :=
              setIntegral_mono_set (hDwU.memL2 γ hγm).integrable_sq
                (ae_of_all _ fun p => sq_nonneg _) (ae_of_all _ hWS)
            have h3 := hNDw_ge γ hγmem
            have h4 := hQ
            have h5 : 0 ≤ NDH := Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => sq_nonneg _
            have h6 : 0 ≤ Q₀ * S := mul_nonneg hQ₀0 hS0
            rw [h1]
            linarith only [h2, h3, h4, h5, h6]
          · have hne : γ ≠ [] := fun h => hγm (by simp [h])
            have hβ' : γ.dropLast ∈ sobolevWords m := mem_sobolevWords.2 (by
              have := mem_sobolevWords.1 hγ
              simp only [List.length_dropLast]; omega)
            have e0 : Dz' γ = Dg γ.dropLast (γ.getLastD 0) := by simp only [Dz', hγm, ite_false]
            rw [e0]
            have hDgL := (hZD _ hβ').2.2.1
            have h1 : ∫ p in W, Dg γ.dropLast (γ.getLastD 0) p ^ 2 ≤
                ∫ p in vlSlab a b, Dg γ.dropLast (γ.getLastD 0) p ^ 2 :=
              setIntegral_mono_set (hDgL _).integrable_sq (ae_of_all _ fun p => sq_nonneg _)
                (ae_of_all _ hWS)
            have h2 : ∫ p in vlSlab a b, Dg γ.dropLast (γ.getLastD 0) p ^ 2 ≤
                ∑ j : Fin 3, ∫ p in vlSlab a b, Dg γ.dropLast j p ^ 2 :=
              Finset.single_le_sum (f := fun j => ∫ p in vlSlab a b, Dg γ.dropLast j p ^ 2)
                (fun _ _ => integral_nonneg fun _ => sq_nonneg _) (Finset.mem_univ _)
            have h3 := hword _ hβ' ⟨b, right_mem_Icc.2 hab.le⟩
            have h4 : 0 ≤ ‖Zc γ.dropLast ⟨b, right_mem_Icc.2 hab.le⟩‖ ^ 2 := sq_nonneg _
            linarith only [h1, h2, h3, h4]
        _ = N₂ * (Q₀ * S) := by rw [Finset.sum_const, nsmul_eq_mul]
    -- square roots
    have hN₁0 : 0 ≤ N₁ := Nat.cast_nonneg _
    have hN₂0 : 0 ≤ N₂ := Nat.cast_nonneg _
    have hsA : Real.sqrt (sobolevNormSqOn m (vec3Ball x₀ r) (Z t)) ≤
        Real.sqrt (N₁ * Q₀) * Real.sqrt S := by
      rw [← Real.sqrt_mul (mul_nonneg hN₁0 hQ₀0)]
      exact Real.sqrt_le_sqrt (by linarith only [hA])
    have hsB : Real.sqrt (l2SobolevNormSqOn (m + 1) (vec3Ball x₀ r) (Ioo s b) Dz') ≤
        Real.sqrt (N₂ * Q₀) * Real.sqrt S := by
      rw [← Real.sqrt_mul (mul_nonneg hN₂0 hQ₀0)]
      exact Real.sqrt_le_sqrt (by linarith only [hB])
    have hsS : Real.sqrt S ≤ Real.sqrt NDz + Real.sqrt NDG :=
      real_sqrt_add_le_add_sqrt hNDz0 hNDG0
    calc
      _ ≤ Real.sqrt (N₁ * Q₀) * Real.sqrt S + Real.sqrt (N₂ * Q₀) * Real.sqrt S :=
        add_le_add hsA hsB
      _ = (Real.sqrt (N₁ * Q₀) + Real.sqrt (N₂ * Q₀)) * Real.sqrt S := (add_mul _ _ _).symm
      _ ≤ (Real.sqrt (N₁ * Q₀) + Real.sqrt (N₂ * Q₀)) * (Real.sqrt NDz + Real.sqrt NDG) :=
        mul_le_mul_of_nonneg_left hsS (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

end ESS
