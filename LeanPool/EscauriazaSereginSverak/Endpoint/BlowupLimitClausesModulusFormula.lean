/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitPairingSpatialChange

/-!
# The rescaled momentum-flux formula

The pairing identity used for clause (b) of `prop:blowup-limit`, for one
scale: the change between two times of the pairing of the rescaled
`L³(B_{3/4})` trace representative with a smooth test carried by a compact set
is the space-time integral of the rescaled momentum flux over that set.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The rescaled momentum-flux formula for the pairings of the rescaled trace
representative with a smooth vector test carried by a compact set
(`prop:blowup-limit`, clause (b)). -/
theorem blowupLimitClauses_rescaled_flux_formula
    (v : Icc (-(3 / 4 : ℝ) ^ 2) 0 →
      Lp L2Vec3 3 (volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))))
    (W : Vec3 × Icc (-(3 / 4 : ℝ) ^ 2) 0 → Vec3)
    (hW : ∀ t,
      (fun x => W (x, t)) =ᵐ[volume.restrict
        (vec3Ball (0 : Vec3) (3 / 4 : ℝ))]
        (fun x => weakContL3OfLp (v t x)))
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
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
    {x₀ : Vec3} {t₀ r : ℝ} (hr : 0 < r) (ht₀ : t₀ ≤ 0)
    (himage : (fun x : Vec3 => x₀ + r • x) '' C ⊆ vec3Ball (0 : Vec3) (3 / 4 : ℝ))
    (htime : ∀ τ, τ ∈ Icc a b → t₀ + r ^ 2 * τ ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0)
    {w : Vec3 → Vec3} (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hwsupport : tsupport w ⊆ C)
    (hF : Integrable (fun z : ParabolicPoint =>
        (∑ i : Fin 3, ∑ j : Fin 3, blowupVelocity x₀ t₀ r u z i *
          blowupVelocity x₀ t₀ r u z j * spatialDeriv (fun x => w x i) j z.1) -
        (∑ i : Fin 3, ∑ j : Fin 3, blowupGradient x₀ t₀ r Du z i j *
          spatialDeriv (fun x => w x i) j z.1) +
        blowupPressure x₀ t₀ r p z * ∑ i : Fin 3, spatialDeriv (fun x => w x i) i z.1)
      (volume.restrict (C ×ˢ Icc a b))) :
    ∀ s t, s ∈ Icc a b → t ∈ Icc a b → s ≤ t →
      (∫ x : Vec3, ∑ i : Fin 3, blowupLimitTraceRescaling W x₀ t₀ r (x,t) i * w x i) -
        (∫ x : Vec3, ∑ i : Fin 3, blowupLimitTraceRescaling W x₀ t₀ r (x,s) i * w x i) =
      ∫ z in C ×ˢ Ioc s t,
        (∑ i : Fin 3, ∑ j : Fin 3, blowupVelocity x₀ t₀ r u z i *
          blowupVelocity x₀ t₀ r u z j * spatialDeriv (fun x => w x i) j z.1) -
        (∑ i : Fin 3, ∑ j : Fin 3, blowupGradient x₀ t₀ r Du z i j *
          spatialDeriv (fun x => w x i) j z.1) +
        blowupPressure x₀ t₀ r p z * ∑ i : Fin 3, spatialDeriv (fun x => w x i) i z.1 := by
  intro s t hs ht hst
  set wL : Vec3 → L2Vec3 := fun x => WithLp.toLp 2 (w x) with hwLdef
  have hwL : ContDiff ℝ (⊤ : ℕ∞) wL :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.contDiff.comp hw
  have hwLsupport : tsupport wL ⊆ C :=
    (tsupport_comp_subset (by simp) w).trans hwsupport
  let ψ : Vec3 → Vec3 := blowupLimitPairingSpatialPullback x₀ r wL
  let F : ParabolicPoint → ℝ := fun z =>
    (∑ i : Fin 3, ∑ j : Fin 3, blowupVelocity x₀ t₀ r u z i *
      blowupVelocity x₀ t₀ r u z j * spatialDeriv (fun x => w x i) j z.1) -
    (∑ i : Fin 3, ∑ j : Fin 3, blowupGradient x₀ t₀ r Du z i j *
      spatialDeriv (fun x => w x i) j z.1) +
    blowupPressure x₀ t₀ r p z * ∑ i : Fin 3, spatialDeriv (fun x => w x i) i z.1
  have hsource := blowup_limit_rescaled_trace_pairing_source_time_formula
    v W hW hsourceFormula hwL hwLsupport hC x₀ t₀ r hr himage a b htime
  have htimeFormula := hsource ⟨s, hs⟩ ⟨t, ht⟩
  have htimeFormula' :
      (∫ x : Vec3, ∑ i : Fin 3, blowupLimitTraceRescaling W x₀ t₀ r (x,t) i * w x i) -
        (∫ x : Vec3, ∑ i : Fin 3, blowupLimitTraceRescaling W x₀ t₀ r (x,s) i * w x i) =
      ∫ τ in s..t, ∫ y in vec3Ball (0 : Vec3) 1,
        (∑ i : Fin 3, ∑ j : Fin 3,
          u (y, t₀ + r ^ 2 * τ) i * u (y, t₀ + r ^ 2 * τ) j *
            spatialDeriv (fun z => ψ z i) j y)
        - (∑ i : Fin 3, ∑ j : Fin 3,
          Du (y, t₀ + r ^ 2 * τ) i j * spatialDeriv (fun z => ψ z i) j y)
        + p (y, t₀ + r ^ 2 * τ) * ∑ i : Fin 3, spatialDeriv (fun z => ψ z i) i y := by
    with_unfolding_all
      exact htimeFormula
  have hsubset : C ×ˢ Ioc s t ⊆ C ×ˢ Icc a b := fun z hz =>
    ⟨hz.1, le_trans hs.1 (le_of_lt hz.2.1), le_trans hz.2.2 ht.2⟩
  have hFsub : Integrable F (volume.restrict (C ×ˢ Ioc s t)) :=
    hF.mono_measure (Measure.restrict_mono_set volume hsubset)
  have hprod : Integrable F ((volume.restrict C).prod (volume.restrict (Ioc s t))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod Vec3 ℝ]
    exact hFsub
  have hnotzero : ∀ᵐ τ ∂(volume.restrict (Ioc s t)), τ ≠ 0 := by
    filter_upwards [ae_mono (Measure.restrict_le_self :
      volume.restrict (Ioc s t) ≤ volume) (Measure.ae_ne volume 0)] with τ hτ
    exact hτ
  have hspace : ∀ᵐ τ ∂(volume.restrict (Ioc s t)),
      (∫ y in vec3Ball (0 : Vec3) 1,
        (∑ i : Fin 3, ∑ j : Fin 3,
          u ((y, t₀ + r ^ 2 * τ) : ParabolicPoint) i *
            u ((y, t₀ + r ^ 2 * τ) : ParabolicPoint) j *
            spatialDeriv (fun z => ψ z i) j y)
        - (∑ i : Fin 3, ∑ j : Fin 3,
          Du ((y, t₀ + r ^ 2 * τ) : ParabolicPoint) i j *
            spatialDeriv (fun z => ψ z i) j y)
        + p ((y, t₀ + r ^ 2 * τ) : ParabolicPoint) *
            ∑ i : Fin 3, spatialDeriv (fun z => ψ z i) i y) =
      ∫ x in C, F ((x,τ) : ParabolicPoint) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc, hnotzero] with τ hτ hτne
    have hτI : τ ∈ Icc a b := ⟨le_trans hs.1 hτ.1.le, le_trans hτ.2 ht.2⟩
    have hτle : τ ≤ 0 := le_trans hτ.2 (le_trans ht.2 hb)
    have hτlt : τ < 0 := lt_of_le_of_ne hτle hτne
    have hsourceTime : t₀ + r ^ 2 * τ ∈ Ioo (-1 : ℝ) 0 := by
      have hlow := (htime τ hτI).1
      have hmul : r ^ 2 * τ < 0 := mul_neg_of_pos_of_neg (sq_pos_of_pos hr) hτlt
      constructor
      · linarith only [hlow]
      · linarith only [ht₀, hmul]
    have hchange := blowup_limit_rescaled_momentum_flux_spatial_integral
      (u := u) (Du := Du) (p := p) (w := wL) (C := C)
      hwLsupport hC x₀ t₀ r τ hr himage hsourceTime
    simpa only [F, ψ, blowupLimitPairingSpatialPullback] using hchange
  have hinterval :
      (∫ τ in Ioc s t, ∫ y in vec3Ball (0 : Vec3) 1,
        (∑ i : Fin 3, ∑ j : Fin 3,
          u ((y, t₀ + r ^ 2 * τ) : ParabolicPoint) i *
            u ((y, t₀ + r ^ 2 * τ) : ParabolicPoint) j *
            spatialDeriv (fun z => ψ z i) j y)
        - (∑ i : Fin 3, ∑ j : Fin 3,
          Du ((y, t₀ + r ^ 2 * τ) : ParabolicPoint) i j *
            spatialDeriv (fun z => ψ z i) j y)
        + p ((y, t₀ + r ^ 2 * τ) : ParabolicPoint) *
            ∑ i : Fin 3, spatialDeriv (fun z => ψ z i) i y) =
        ∫ τ in Ioc s t, ∫ x in C, F (x,τ) :=
    integral_congr_ae hspace
  have hprodEq : (∫ τ in Ioc s t, ∫ x in C, F ((x,τ) : ParabolicPoint)) =
      ∫ z in C ×ˢ Ioc s t, F z := by
    calc
      _ = ∫ z : ParabolicPoint, F z
          ∂((volume.restrict C).prod (volume.restrict (Ioc s t))) :=
        (integral_prod_symm _ hprod).symm
      _ = ∫ z in C ×ˢ Ioc s t, F z := by
        have hmeasure : (volume.restrict C).prod (volume.restrict (Ioc s t)) =
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
    _ = ∫ τ in Ioc s t, ∫ y in vec3Ball (0 : Vec3) 1,
          (∑ i : Fin 3, ∑ j : Fin 3,
            u ((y, t₀ + r ^ 2 * τ) : ParabolicPoint) i *
              u ((y, t₀ + r ^ 2 * τ) : ParabolicPoint) j *
              spatialDeriv (fun z => ψ z i) j y)
          - (∑ i : Fin 3, ∑ j : Fin 3,
            Du ((y, t₀ + r ^ 2 * τ) : ParabolicPoint) i j *
              spatialDeriv (fun z => ψ z i) j y)
          + p ((y, t₀ + r ^ 2 * τ) : ParabolicPoint) *
              ∑ i : Fin 3, spatialDeriv (fun z => ψ z i) i y := by
      rw [htimeFormula', intervalIntegral.integral_of_le hst]
    _ = ∫ τ in Ioc s t, ∫ x in C, F (x,τ) := hinterval
    _ = ∫ z in C ×ˢ Ioc s t, F z := hprodEq

end ESS

end
