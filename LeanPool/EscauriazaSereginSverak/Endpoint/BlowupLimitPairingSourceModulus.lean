/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitPairingSpatialChange
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitPairingFlux

/-!
# Endpoint pairing moduli from the source momentum equation

The all-time source trace formula, affine spatial change, and local momentum
flux bounds give the time modulus on every closed rescaled interval.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Uniform local flux bounds and the source momentum formula control all
rescaled trace pairings, including pairings at time zero. -/
theorem blowup_limit_rescaled_trace_pairing_modulus_of_source_flux
    (v : Icc (-(3 / 4 : ℝ) ^ 2) 0 →
      Lp L2Vec3 3 (volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))))
    (W : Vec3 × Icc (-(3 / 4 : ℝ) ^ 2) 0 → Vec3)
    (hW : ∀ t,
      (fun x => W (x,t)) =ᵐ[volume.restrict
        (vec3Ball (0 : Vec3) (3 / 4 : ℝ))]
        (fun x => weakContL3OfLp (v t x)))
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    {x₀ : Vec3}
    (hsourceFormula : ∀ ψ : Vec3 → Vec3,
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball (0 : Vec3) (3 / 4 : ℝ) →
      ∀ s t : Icc (-(3 / 4 : ℝ) ^ 2) 0,
        (∫ y in vec3Ball (0 : Vec3) (3 / 4 : ℝ),
          ∑ i : Fin 3, v t y i * ψ y i) -
        (∫ y in vec3Ball (0 : Vec3) (3 / 4 : ℝ),
          ∑ i : Fin 3, v s y i * ψ y i) =
        ∫ τ in s.1..t.1, ∫ y in vec3Ball (0 : Vec3) 1,
          (∑ i : Fin 3, ∑ j : Fin 3,
            u (y,τ) i * u (y,τ) j * spatialDeriv (fun z => ψ z i) j y)
          - (∑ i : Fin 3, ∑ j : Fin 3,
            Du (y,τ) i j * spatialDeriv (fun z => ψ z i) j y)
          + p (y,τ) * ∑ i : Fin 3, spatialDeriv (fun z => ψ z i) i y
          ∂volume)
    {C : Set Vec3} (hC : IsCompact C)
    (a b : ℝ) (hb : b ≤ 0)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (himage : ∀ n,
      (fun x : Vec3 => x₀ + r n • x) '' C ⊆
        vec3Ball (0 : Vec3) (3 / 4 : ℝ))
    (t₀ : ℝ) (ht₀ : t₀ ≤ 0)
    (htime : ∀ n τ, τ ∈ Icc a b →
      t₀ + (r n) ^ 2 * τ ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0)
    (Mvel Mgrad Mpress Mtest Mdiv : ℝ≥0∞)
    (hMvel : Mvel < ⊤) (hMgrad : Mgrad < ⊤)
    (hMpress : Mpress < ⊤) (hMtest : Mtest < ⊤)
    (hMdiv : Mdiv < ⊤)
    (hU : ∀ n i,
      MemLp (fun z => blowupVelocity x₀ t₀ (r n) u z i) 3
        (volume.restrict (C ×ˢ Icc a b)) ∧
      eLpNorm (fun z => blowupVelocity x₀ t₀ (r n) u z i) 3
        (volume.restrict (C ×ˢ Icc a b)) ≤ Mvel)
    (hDU : ∀ n i j,
      MemLp (fun z => blowupGradient x₀ t₀ (r n) Du z i j) 2
        (volume.restrict (C ×ˢ Icc a b)) ∧
      eLpNorm (fun z => blowupGradient x₀ t₀ (r n) Du z i j) 2
        (volume.restrict (C ×ˢ Icc a b)) ≤ Mgrad)
    (hP : ∀ n,
      MemLp (blowupPressure x₀ t₀ (r n) p) (3 / 2 : ℝ≥0∞)
        (volume.restrict (C ×ˢ Icc a b)) ∧
      eLpNorm (blowupPressure x₀ t₀ (r n) p) (3 / 2 : ℝ≥0∞)
        (volume.restrict (C ×ˢ Icc a b)) ≤ Mpress)
    (w : Vec3 → L2Vec3) (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hwsupport : tsupport w ⊆ C)
    (hDw : ∀ i j,
      MemLp (fun z : ParabolicPoint => spatialDeriv (fun x => w x i) j z.1)
        ⊤ (volume.restrict (C ×ˢ Icc a b)) ∧
      eLpNorm (fun z : ParabolicPoint => spatialDeriv (fun x => w x i) j z.1)
        ⊤ (volume.restrict (C ×ˢ Icc a b)) ≤ Mtest)
    (hdivw : MemLp (fun z : ParabolicPoint =>
        ∑ i : Fin 3, spatialDeriv (fun x => w x i) i z.1)
        ⊤ (volume.restrict (C ×ˢ Icc a b)) ∧
      eLpNorm (fun z : ParabolicPoint =>
        ∑ i : Fin 3, spatialDeriv (fun x => w x i) i z.1)
        ⊤ (volume.restrict (C ×ˢ Icc a b)) ≤ Mdiv) :
    ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
      ∀ n s t, s ∈ Icc a b → t ∈ Icc a b →
        |(∫ x : Vec3, ∑ i : Fin 3,
            blowupLimitTraceRescaling W x₀ t₀ (r n) (x,t) i * w x i)
          - (∫ x : Vec3, ∑ i : Fin 3,
            blowupLimitTraceRescaling W x₀ t₀ (r n) (x,s) i * w x i)| ≤
          A * dist t s + B * (dist t s) ^ θ := by
  let Dw : Fin 3 → Fin 3 → ParabolicPoint → ℝ := fun i j z =>
    spatialDeriv (fun x => w x i) j z.1
  let divw : ParabolicPoint → ℝ := fun z =>
    ∑ i : Fin 3, spatialDeriv (fun x => w x i) i z.1
  let U : ℕ → ParabolicPoint → Vec3 := fun n z =>
    blowupVelocity x₀ t₀ (r n) u z
  let DU : ℕ → ParabolicPoint → Fin 3 → Fin 3 → ℝ := fun n z i j =>
    blowupGradient x₀ t₀ (r n) Du z i j
  let P : ℕ → ParabolicPoint → ℝ := fun n z =>
    blowupPressure x₀ t₀ (r n) p z
  let G : ℕ → ℝ → ℝ := fun n t =>
    ∫ x : Vec3, ∑ i : Fin 3,
      blowupLimitTraceRescaling W x₀ t₀ (r n) (x,t) i * w x i
  have hDwn : ∀ i j,
      MemLp (Dw i j) ⊤ (volume.restrict (C ×ˢ Icc a b)) ∧
      eLpNorm (Dw i j) ⊤ (volume.restrict (C ×ˢ Icc a b)) ≤ Mtest := by
    intro i j
    exact hDw i j
  have hformula : ∀ n s t, s ∈ Icc a b → t ∈ Icc a b → s ≤ t →
      G n t - G n s = ∫ z in C ×ˢ Ioc s t,
        (∑ i : Fin 3, ∑ j : Fin 3,
          U n z i * U n z j * Dw i j z) -
        (∑ i : Fin 3, ∑ j : Fin 3,
          DU n z i j * Dw i j z) + P n z * divw z := by
    intro n s t hs ht hst
    let ψ : Vec3 → Vec3 := blowupLimitPairingSpatialPullback x₀ (r n) w
    have hsource := blowup_limit_rescaled_trace_pairing_source_time_formula
      v W hW hsourceFormula hw hwsupport hC x₀ t₀ (r n) (hr n)
      (himage n) a b (fun τ hτ => htime n τ hτ)
    have htimeFormula := hsource ⟨s,hs⟩ ⟨t,ht⟩
    have htimeFormula' : G n t - G n s =
        ∫ τ in s..t, ∫ y in vec3Ball (0 : Vec3) 1,
          (∑ i : Fin 3, ∑ j : Fin 3,
            u (y, t₀ + (r n) ^ 2 * τ) i * u (y, t₀ + (r n) ^ 2 * τ) j *
              spatialDeriv (fun z => ψ z i) j y)
          - (∑ i : Fin 3, ∑ j : Fin 3,
            Du (y, t₀ + (r n) ^ 2 * τ) i j *
              spatialDeriv (fun z => ψ z i) j y)
          + p (y, t₀ + (r n) ^ 2 * τ) *
              ∑ i : Fin 3, spatialDeriv (fun z => ψ z i) i y := by
      with_unfolding_all
        exact htimeFormula
    change G n t - G n s = _
    let F : ParabolicPoint → ℝ := fun z =>
      (∑ i : Fin 3, ∑ j : Fin 3,
        U n z i * U n z j * Dw i j z) -
      (∑ i : Fin 3, ∑ j : Fin 3,
        DU n z i j * Dw i j z) + P n z * divw z
    have hμclosed : IsFiniteMeasure (volume.restrict (C ×ˢ Icc a b)) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply_univ]
      exact (hC.prod isCompact_Icc).measure_lt_top
    let : IsFiniteMeasure (volume.restrict (C ×ˢ Icc a b)) := hμclosed
    have hflux := @blowup_limit_momentum_flux_memLp_three_halves
      (volume.restrict (C ×ˢ Icc a b)) hμclosed U DU P Dw divw
      Mvel Mgrad Mpress Mtest Mdiv
      hU hDU hP hDwn hdivw
    have hF : MemLp (F) (3 / 2 : ℝ≥0∞)
        (volume.restrict (C ×ˢ Icc a b)) := by
      simpa [F, U, DU, P, Dw] using (hflux n).1
    have hsubset : C ×ˢ Ioc s t ⊆ C ×ˢ Icc a b := by
      intro z hz
      exact ⟨hz.1, le_trans hs.1 (le_of_lt hz.2.1),
        le_trans hz.2.2 ht.2⟩
    have hμsub : IsFiniteMeasure (volume.restrict (C ×ˢ Ioc s t)) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply_univ]
      calc
        volume (C ×ˢ Ioc s t) ≤ volume (C ×ˢ Icc a b) := measure_mono hsubset
        _ < ⊤ := (hC.prod isCompact_Icc).measure_lt_top
    have : IsFiniteMeasure (volume.restrict (C ×ˢ Ioc s t)) := hμsub
    have hFsub : Integrable F (volume.restrict (C ×ˢ Ioc s t)) := by
      have hmem := hF.mono_measure (Measure.restrict_mono_set volume hsubset)
      have hlow : (1 : ℝ≥0∞) ≤ (3 / 2 : ℝ≥0∞) := by
        rw [← CKN.ofReal_threeHalves]
        exact ENNReal.one_le_ofReal.mpr (by norm_num)
      exact MeasureTheory.MemLp.integrable
        (μ := volume.restrict (C ×ˢ Ioc s t)) hlow hmem
    have hprod : Integrable F
        ((volume.restrict C).prod (volume.restrict (Ioc s t))) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod Vec3 ℝ]
      exact hFsub
    have hnotzero : ∀ᵐ τ ∂(volume.restrict (Ioc s t)), τ ≠ 0 := by
      filter_upwards [ae_mono (Measure.restrict_le_self :
        volume.restrict (Ioc s t) ≤ volume) (Measure.ae_ne volume 0)] with τ hτ
      exact hτ
    have hspace : ∀ᵐ τ ∂(volume.restrict (Ioc s t)),
        (∫ y in vec3Ball (0 : Vec3) 1,
          (∑ i : Fin 3, ∑ j : Fin 3,
            u ((y, t₀ + (r n) ^ 2 * τ) : ParabolicPoint) i *
              u ((y, t₀ + (r n) ^ 2 * τ) : ParabolicPoint) j *
              spatialDeriv (fun z => ψ z i) j y)
          - (∑ i : Fin 3, ∑ j : Fin 3,
            Du ((y, t₀ + (r n) ^ 2 * τ) : ParabolicPoint) i j *
              spatialDeriv (fun z => ψ z i) j y)
          + p ((y, t₀ + (r n) ^ 2 * τ) : ParabolicPoint) *
              ∑ i : Fin 3, spatialDeriv (fun z => ψ z i) i y) =
        ∫ x in C, F ((x,τ) : ParabolicPoint) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc, hnotzero] with τ hτ hτne
      have hτI : τ ∈ Icc a b := by
        exact ⟨le_trans hs.1 hτ.1.le, le_trans hτ.2 ht.2⟩
      have hτle : τ ≤ 0 := le_trans hτ.2 (le_trans ht.2 hb)
      have hτlt : τ < 0 := lt_of_le_of_ne hτle hτne
      have hsourceTime : t₀ + (r n) ^ 2 * τ ∈ Ioo (-1 : ℝ) 0 := by
        have hlow := (htime n τ hτI).1
        have hupper : t₀ + (r n) ^ 2 * τ < 0 := by
          have hmul : (r n) ^ 2 * τ < 0 :=
            mul_neg_of_pos_of_neg (sq_pos_of_pos (hr n)) hτlt
          linarith only [ht₀, hmul]
        constructor
        · linarith only [hlow]
        · exact hupper
      have hchange := blowup_limit_rescaled_momentum_flux_spatial_integral
        (u := u) (Du := Du) (p := p) (w := w) (C := C)
        hwsupport hC x₀ t₀ (r n) τ (hr n) (himage n) hsourceTime
      simpa only [F, U, DU, P, Dw, ψ,
        blowupLimitPairingSpatialPullback] using hchange
    have hinterval :
        (∫ τ in Ioc s t,
          ∫ y in vec3Ball (0 : Vec3) 1,
            (∑ i : Fin 3, ∑ j : Fin 3,
            u ((y, t₀ + (r n) ^ 2 * τ) : ParabolicPoint) i *
              u ((y, t₀ + (r n) ^ 2 * τ) : ParabolicPoint) j *
                spatialDeriv (fun z => ψ z i) j y)
            - (∑ i : Fin 3, ∑ j : Fin 3,
            Du ((y, t₀ + (r n) ^ 2 * τ) : ParabolicPoint) i j *
                spatialDeriv (fun z => ψ z i) j y)
          + p ((y, t₀ + (r n) ^ 2 * τ) : ParabolicPoint) *
                ∑ i : Fin 3, spatialDeriv (fun z => ψ z i) i y) =
          ∫ τ in Ioc s t, ∫ x in C, F (x,τ) := by
      apply integral_congr_ae
      exact hspace
    have hprodEq :
        (∫ τ in Ioc s t, ∫ x in C, F ((x,τ) : ParabolicPoint)) =
          ∫ z in C ×ˢ Ioc s t, F z := by
      calc
        _ = ∫ z : ParabolicPoint, F z
            ∂((volume.restrict C).prod (volume.restrict (Ioc s t))) :=
          (integral_prod_symm _ hprod).symm
        _ = ∫ z in C ×ˢ Ioc s t, F z := by
          have hmeasure :
              (volume.restrict C).prod (volume.restrict (Ioc s t)) =
                (volume : Measure ParabolicPoint).restrict (C ×ˢ Ioc s t) := by
            have hvolume : (volume : Measure ParabolicPoint) =
                (volume : Measure Vec3).prod (volume : Measure ℝ) := rfl
            rw [Measure.prod_restrict, ← hvolume]
            rfl
          change (∫ z : ParabolicPoint, F z
              ∂((volume.restrict C).prod (volume.restrict (Ioc s t)))) = _
          rw [hmeasure]
          rfl
    calc
      G n t - G n s =
          ∫ τ in Ioc s t,
            ∫ y in vec3Ball (0 : Vec3) 1,
              (∑ i : Fin 3, ∑ j : Fin 3,
              u ((y, t₀ + (r n) ^ 2 * τ) : ParabolicPoint) i *
                u ((y, t₀ + (r n) ^ 2 * τ) : ParabolicPoint) j *
                  spatialDeriv (fun z => ψ z i) j y)
              - (∑ i : Fin 3, ∑ j : Fin 3,
              Du ((y, t₀ + (r n) ^ 2 * τ) : ParabolicPoint) i j *
                  spatialDeriv (fun z => ψ z i) j y)
            + p ((y, t₀ + (r n) ^ 2 * τ) : ParabolicPoint) *
                  ∑ i : Fin 3, spatialDeriv
                    (fun z => ψ z i) i y := by
            rw [htimeFormula', intervalIntegral.integral_of_le hst]
      _ = ∫ τ in Ioc s t, ∫ x in C, F (x,τ) := by
            exact hinterval
      _ = ∫ z in C ×ˢ Ioc s t, F z := hprodEq
      _ = _ := by rfl
  exact blowup_limit_pairing_modulus_of_momentum_flux hC a b U DU P
    Dw divw G Mvel Mgrad Mpress Mtest Mdiv
    hMvel hMgrad hMpress hMtest hMdiv hU hDU hP hDwn hdivw hformula

end ESS

end
