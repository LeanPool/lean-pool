/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Comparison.Direct.EnergyWindow

/-!
# The barrier bound on a working interval: the limit `ε ↓ 0`

From the energy bound of `CIV.ae_integral_comparisonProfile_le` along the mollification radii
`ε_n = 1/(n+1)`, the commutator term tends to zero (`CIV.tendsto_integral_commutatorL2Sq`) and
`q_ε(·, τ) → q(·, τ)` in `L²` of every ball (`CIV.tendsto_integral_sq_mollifySlice_sub`); hence
`∫_{B_R} G(q(·, τ) - Ψ_σ(·, τ)) = 0` for almost every `τ ∈ [τ₀, b]`, that is `q ≤ Ψ_σ` almost
everywhere on `B_R`, and off `B_R` the barrier exceeds the bound of `q`. This is the conclusion
`q ≤ Ψ_σ` of the energy argument of `lem:aniso:comparison`, before `σ ↓ 0`.
-/

public section

open MeasureTheory Set Filter Topology
open CKN

noncomputable section
namespace CIV

variable {m : ℕ}

theorem comparisonProfile_le_posPart (y : ℝ) : comparisonProfile y ≤ max y 0 := by
  rcases le_or_gt y 0 with hy | hy
  · rw [comparisonProfile_eq_zero_of_nonpos hy]; exact le_max_right _ _
  · have h := abs_comparisonProfile_sub_le y 0
    rw [comparisonProfile_eq_zero_of_nonpos le_rfl, sub_zero, sub_zero, abs_of_pos hy] at h
    exact le_trans (le_abs_self _) (le_trans h (le_max_left _ _))

theorem tendsto_one_div_succ_nhdsGT :
    Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) :=
  tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
    Eventually.of_forall fun n => Set.mem_Ioi.mpr (by positivity)⟩

/-- **The barrier bound on a working interval**, from a reference time `τ₀`. -/
theorem ae_ae_le_barrier_of_referenceTime {d : ℕ} {I : Set ℝ} (hI : IsOpen I)
    (hIoc : I.OrdConnected) {B : Vec m × ℝ → Vec m} {divB q : Vec m × ℝ → ℝ}
    (hB : IsAdmissibleDrift m I B divB) (hq : IsLocallyBoundedOn m I q)
    (heq : IsDistributionalDriftDiffusion m d I B divB q)
    {M σ Mq τ₀ b : ℝ} {Λ : NNReal} (hσ : 0 < σ) (hM : 0 ≤ M) (hMq : 0 ≤ Mq)
    (hτ₀b : τ₀ ≤ b) (hsub : Icc τ₀ b ⊆ I)
    (hgood : ∀ᵐ s ∂(volume.restrict (Icc τ₀ b)),
      AEStronglyMeasurable (fun y => q (y, s)) volume ∧ (∀ᵐ y ∂volume, |q (y, s)| ≤ Mq) ∧
      (∀ x, ‖B (x, s)‖ ≤ Λ) ∧ LipschitzWith Λ (fun x => B (x, s)) ∧
      (∀ x, |divB (x, s)| ≤ Λ) ∧
      (∀ ψ : Vec m → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        ∫ x, divB (x, s) * ψ x = -∫ x, ∑ i, B (x, s) i * fderiv ℝ ψ x (basisVec i)))
    (hτ₀m : AEStronglyMeasurable (fun y => q (y, τ₀)) volume)
    (hτ₀M : ∀ᵐ y ∂volume, |q (y, τ₀)| ≤ M)
    (href : ∀ n : ℕ,
      (∀ᵐ x : Vec m, ∀ᵐ τ ∂(volume.restrict I),
        mollifySlice m (1 / ((n : ℝ) + 1)) q (x, τ) - mollifySlice m (1 / ((n : ℝ) + 1)) q (x, τ₀)
          = ∫ s in τ₀..τ, mollifiedRHS m d (1 / ((n : ℝ) + 1)) B divB q x s) ∧
      (∀ᵐ τ ∂(volume.restrict I), ∀ᵐ x : Vec m,
        mollifySlice m (1 / ((n : ℝ) + 1)) q (x, τ) - mollifySlice m (1 / ((n : ℝ) + 1)) q (x, τ₀)
          = ∫ s in τ₀..τ, mollifiedRHS m d (1 / ((n : ℝ) + 1)) B divB q x s)) :
    ∀ᵐ τ ∂(volume.restrict (Icc τ₀ b)), ∀ᵐ x : Vec m,
      q (x, τ) ≤ barrier m M σ (barrierRate m d Λ) τ₀ (x, τ) := by
  set K : ℝ := barrierRate m d Λ with hKdef
  have hK : 0 ≤ K := barrierRate_nonneg m d Λ.coe_nonneg
  set εs : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hεsdef
  have hεs : ∀ n, 0 < εs n := fun n => by positivity
  set Bl : Set (Vec m) := Metric.closedBall (0 : Vec m) (Mq / σ) with hBl
  set V : ℝ := (volume Bl).toReal with hVdef
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hfin : volume Bl ≠ ⊤ := measure_closedBall_lt_top.ne
  set A : ℝ := Real.exp (Λ * (b - τ₀)) with hAdef
  have hA : 0 ≤ A := (Real.exp_pos _).le
  set cn : ℕ → ℝ := fun n => ∫ s in τ₀..b, commutatorL2Sq m (εs n) (Mq / σ) B divB q s
    with hcndef
  have hcn : Tendsto cn atTop (𝓝 0) :=
    (tendsto_integral_commutatorL2Sq (Rb := Mq / σ) hτ₀b hB hq hsub).comp
      tendsto_one_div_succ_nhdsGT
  -- the energy bounds, for every `n`
  have hE : ∀ᵐ τ ∂(volume.restrict (Icc τ₀ b)), ∀ n : ℕ, ∀ δ : ℝ, 0 < δ →
      ∫ x, comparisonProfile (mollifySlice m (εs n) q (x, τ) - barrier m M σ K τ₀ (x, τ))
        ≤ (δ * V * (b - τ₀) + (1 / (4 * δ)) * cn n) * A := by
    rw [ae_all_iff]
    intro n
    have hq0 : ∀ x, mollifySlice m (εs n) q (x, τ₀) ≤ M := fun x =>
      (abs_le.mp (abs_mollifySlice_le (hεs n) hτ₀m hτ₀M x)).2
    exact ae_integral_comparisonProfile_le hI hIoc hB hq heq (hεs n) hσ hM hMq hτ₀b hsub hgood
      hq0 (href n).1 (href n).2
  filter_upwards [hE, hgood, ae_restrict_mem measurableSet_Icc] with τ hEτ hgτ hτmem
  obtain ⟨hmeas, hbdd, -, -, -, -⟩ := hgτ
  set f : Vec m → ℝ := fun x => q (x, τ) - barrier m M σ K τ₀ (x, τ) with hfdef
  have hbar_nn : ∀ x, M + σ * ‖x‖ ≤ barrier m M σ K τ₀ (x, τ) :=
    fun x => le_barrier M K τ₀ τ x hσ.le hK hτmem.1
  -- the profile of the excess is integrable on the ball
  have hbarc : Continuous fun x : Vec m => barrier m M σ K τ₀ (x, τ) :=
    (contDiff_barrier M σ K τ₀).continuous.comp (continuous_id.prodMk continuous_const)
  have hGfm : AEStronglyMeasurable (fun x => comparisonProfile (f x)) volume :=
    contDiff_comparisonProfile.continuous.comp_aestronglyMeasurable
      (hmeas.sub hbarc.aestronglyMeasurable)
  have hGfb : ∀ᵐ x ∂volume, ‖comparisonProfile (f x)‖ ≤ Mq := by
    filter_upwards [hbdd] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (comparisonProfile_nonneg _)]
    have h1 := comparisonProfile_le_posPart (f x)
    have h2 := hbar_nn x
    have h3 : 0 ≤ σ * ‖x‖ := mul_nonneg hσ.le (norm_nonneg x)
    have h4 := (abs_le.mp hx).2
    refine le_trans h1 (max_le ?_ hMq)
    simp only [hfdef]
    linarith only [h2, h3, h4, hM]
  have hGfint : IntegrableOn (fun x => comparisonProfile (f x)) Bl volume :=
    Measure.integrableOn_of_bounded hfin hGfm (ae_restrict_of_ae hGfb)
  -- the integral of the profile over the ball vanishes
  have hX : ∫ x in Bl, comparisonProfile (f x) ≤ 0 := by
    set X : ℝ := ∫ x in Bl, comparisonProfile (f x) with hXdef
    have hstep : ∀ δ : ℝ, 0 < δ → X ≤ δ * (V * (b - τ₀) * A + V) := by
      intro δ hδ
      set dn : ℕ → ℝ := fun n => ∫ x in Bl, (mollifySlice m (εs n) q (x, τ) - q (x, τ)) ^ 2
        with hdndef
      have hdn : Tendsto dn atTop (𝓝 0) :=
        (tendsto_integral_sq_mollifySlice_sub (R := Mq / σ) hbdd hmeas).comp
          tendsto_one_div_succ_nhdsGT
      have hn : ∀ n : ℕ, X ≤ (δ * V * (b - τ₀) + (1 / (4 * δ)) * cn n) * A
          + (δ * V + (1 / (4 * δ)) * dn n) := by
        intro n
        set fn : Vec m → ℝ := fun x => mollifySlice m (εs n) q (x, τ)
          - barrier m M σ K τ₀ (x, τ) with hfndef
        -- the mollified excess is negative off the ball
        have hneg : ∀ x, x ∉ Bl → fn x < 0 := fun x hx =>
          mollifySlice_sub_barrier_neg (hεs n) hσ hM hK hτmem.1 hmeas hbdd hx
        have hQc : Continuous fun x : Vec m => mollifySlice m (εs n) q (x, τ) :=
          (contDiff_mollifySlice (hεs n) τ q Mq hmeas hbdd).continuous
        have hGfnc : Continuous fun x => comparisonProfile (fn x) :=
          contDiff_comparisonProfile.continuous.comp (hQc.sub hbarc)
        have hGfnsupp : HasCompactSupport fun x => comparisonProfile (fn x) :=
          HasCompactSupport.intro (isCompact_closedBall _ _) fun x hx =>
            comparisonProfile_eq_zero_of_nonpos (hneg x hx).le
        have hGfnint : Integrable (fun x => comparisonProfile (fn x)) volume :=
          hGfnc.integrable_of_hasCompactSupport hGfnsupp
        have hball : ∫ x in Bl, comparisonProfile (fn x) = ∫ x, comparisonProfile (fn x) :=
          setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
            comparisonProfile_eq_zero_of_nonpos (hneg x hx).le
        -- pointwise comparison of the profiles
        have hdiffm : AEStronglyMeasurable
            (fun x => mollifySlice m (εs n) q (x, τ) - q (x, τ)) volume :=
          hQc.aestronglyMeasurable.sub hmeas
        have hdiffb : ∀ᵐ x ∂volume, |mollifySlice m (εs n) q (x, τ) - q (x, τ)| ≤ 2 * Mq := by
          filter_upwards [hbdd] with x hx
          have h1 := abs_mollifySlice_le (hεs n) hmeas hbdd x
          have h2 := abs_sub (mollifySlice m (εs n) q (x, τ)) (q (x, τ))
          linarith only [h1, h2, hx]
        have hsplit := integral_mul_abs_le_of_support (m := m) (ρ := Mq / σ) hδ
          (f := Bl.indicator fun _ => (1 : ℝ))
          (R := fun x => mollifySlice m (εs n) q (x, τ) - q (x, τ)) (Cr := 2 * Mq)
          (fun x => indicator_nonneg (fun _ _ => zero_le_one) x)
          (fun x => indicator_le_self' (fun _ _ => zero_le_one) x)
          (fun x hx => indicator_of_notMem hx _) hdiffm hdiffb
        have habsint : IntegrableOn
            (fun x => |mollifySlice m (εs n) q (x, τ) - q (x, τ)|) Bl volume :=
          Measure.integrableOn_of_bounded hfin hdiffm.norm
            (ae_restrict_of_ae (hdiffb.mono fun x hx => by rwa [Real.norm_eq_abs, abs_abs]))
        have hleft : ∫ x, Bl.indicator (fun _ => (1 : ℝ)) x
              * |mollifySlice m (εs n) q (x, τ) - q (x, τ)|
            = ∫ x in Bl, |mollifySlice m (εs n) q (x, τ) - q (x, τ)| := by
          rw [← integral_indicator measurableSet_closedBall]
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          dsimp only
          by_cases hx : x ∈ Bl
          · have hx' : x ∈ Metric.closedBall (0 : Vec m) (Mq / σ) := hx
            rw [indicator_of_mem hx', indicator_of_mem hx', one_mul]
          · have hx' : x ∉ Metric.closedBall (0 : Vec m) (Mq / σ) := hx
            rw [indicator_of_notMem hx', indicator_of_notMem hx', zero_mul]
        rw [hleft] at hsplit
        have hGfnle : ∫ x in Bl, comparisonProfile (f x)
            ≤ ∫ x in Bl, (comparisonProfile (fn x)
              + |mollifySlice m (εs n) q (x, τ) - q (x, τ)|) := by
          refine setIntegral_mono_on hGfint (hGfnint.integrableOn.add habsint)
            measurableSet_closedBall fun x _ => ?_
          have h := abs_comparisonProfile_sub_le (f x) (fn x)
          have heqd : f x - fn x = -(mollifySlice m (εs n) q (x, τ) - q (x, τ)) := by
            simp only [hfdef, hfndef]; ring
          rw [heqd, abs_neg] at h
          linarith only [h, le_abs_self (comparisonProfile (f x) - comparisonProfile (fn x))]
        rw [integral_add hGfnint.integrableOn habsint, hball] at hGfnle
        have hEn := hEτ n δ hδ
        have hdnn : dn n = ∫ x in Bl, (mollifySlice m (εs n) q (x, τ) - q (x, τ)) ^ 2 := rfl
        rw [← hdnn] at hsplit
        linarith only [hGfnle, hEn, hsplit]
      have hlim : Tendsto (fun n : ℕ => (δ * V * (b - τ₀) + (1 / (4 * δ)) * cn n) * A
          + (δ * V + (1 / (4 * δ)) * dn n)) atTop
          (𝓝 ((δ * V * (b - τ₀) + (1 / (4 * δ)) * 0) * A + (δ * V + (1 / (4 * δ)) * 0))) :=
        (((tendsto_const_nhds.add (hcn.const_mul _)).mul_const A).add
          (tendsto_const_nhds.add (hdn.const_mul _)))
      have hle := ge_of_tendsto' hlim hn
      linarith only [hle]
    have hδlim : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1) * (V * (b - τ₀) * A + V)) atTop
        (𝓝 (0 * (V * (b - τ₀) * A + V))) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.mul_const _
    have hle := ge_of_tendsto' hδlim fun k => hstep _ (by positivity)
    linarith only [hle]
  have hzero : ∀ᵐ x ∂(volume.restrict Bl), comparisonProfile (f x) = 0 := by
    have hnn : 0 ≤ᵐ[volume.restrict Bl] fun x => comparisonProfile (f x) :=
      Eventually.of_forall fun x => comparisonProfile_nonneg _
    have h0 : ∫ x in Bl, comparisonProfile (f x) = 0 :=
      le_antisymm hX (integral_nonneg fun x => comparisonProfile_nonneg _)
    exact (integral_eq_zero_iff_of_nonneg_ae hnn hGfint).mp h0
  have hzero' : ∀ᵐ x ∂volume, x ∈ Bl → comparisonProfile (f x) = 0 :=
    (ae_restrict_iff' measurableSet_closedBall).mp hzero
  filter_upwards [hzero', hbdd] with x hx hxb
  by_cases hxB : x ∈ Bl
  · have h := comparisonProfile_eq_zero_iff.mp (hx hxB)
    simp only [hfdef] at h
    linarith only [h]
  · have hxn : Mq / σ < ‖x‖ := by
      rw [hBl, Metric.mem_closedBall, dist_zero_right, not_le] at hxB
      exact hxB
    have hσx : Mq < σ * ‖x‖ := by
      rw [div_lt_iff₀ hσ] at hxn
      linarith only [hxn]
    have h2 := hbar_nn x
    have h4 := (abs_le.mp hxb).2
    linarith only [h2, hσx, h4, hM]

end CIV
