/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Regularity.DeGiorgiIterationTwo
public import LeanPool.Superdiffusion.Support.HighContrast.Coupled.Stampacchia.Iteration

/-!
# DeGiorgiOneSidedTwo

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The two-dimensional one-sided De Giorgi core

The endpoint recurrence has coefficient `C² L E₀²`.  The additional factor
`L` exactly cancels against the square volume and a threshold of size
`Cd L E₀` in the iteration admissibility condition.
-/

namespace DivergenceFormProcess.Regularity

open HCPolySupport MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- The direct endpoint admissibility calculation.  It replaces the
dimension-dependent calculation used by the `d ≥ 3` core. -/
theorem deGiorgi_admissible_two {C Cd L E₀ : ℝ}
    (hC : 0 ≤ C) (hCd : 0 < Cd) (hchoice : 4 * C ≤ Cd)
    (hL : 0 < L) (hE₀ : 0 < E₀) :
    (((C ^ 2 * L * E₀ ^ 2) / (Cd * L * E₀) ^ 2) ^ (2 : ℝ)) * 16 *
        (L ^ 2) ^ (1 : ℝ) ≤
      (16 : ℝ) ^ (-(1 / (1 : ℝ))) := by
  rw [Real.rpow_two, Real.rpow_one]
  have hratio : C / Cd ≤ (1 / 4 : ℝ) := by
    rw [div_le_iff₀ hCd]
    linarith only [hchoice]
  have hratio_nonneg : 0 ≤ C / Cd := div_nonneg hC hCd.le
  have hpow : (C / Cd) ^ 4 ≤ (1 / 4 : ℝ) ^ 4 := by
    exact pow_le_pow_left₀ hratio_nonneg hratio 4
  have heq :
      ((C ^ 2 * L * E₀ ^ 2) / (Cd * L * E₀) ^ 2) ^ 2 * 16 * L ^ 2 =
        (C / Cd) ^ 4 * 16 := by
    field_simp
  rw [heq]
  calc
    (C / Cd) ^ 4 * 16 ≤ (1 / 4 : ℝ) ^ 4 * 16 :=
      mul_le_mul_of_nonneg_right hpow (by norm_num)
    _ = (16 : ℝ) ^ (-(1 / (1 : ℝ))) := by norm_num

/-- The dimension-two one-sided De Giorgi core. -/
theorem deGiorgi_one_sided_core_two :
    ∃ Cd : ℝ, 0 ≤ Cd ∧
      ∀ (z : Vec 2) (L : ℝ), 0 < L →
        ∀ (w₁ w₂ : H1Function (axisCube z L)),
          Measurable w₁.toFun → Measurable w₂.toFun →
          MemH10 (axisCube z L) (fun x => w₁.toFun x - w₂.toFun x) →
          ∀ (m₀ E₀ : ℝ), 0 ≤ E₀ →
          volume {x | x ∈ axisCube z L ∧ m₀ < w₁.toFun x} +
              volume {x | x ∈ axisCube z L ∧ m₀ < w₂.toFun x} ≤
            volume (axisCube z L) →
          (∀ k : ℝ, 0 ≤ k →
            (∑ i : Fin 2, (eLpNorm
                ({x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x}.indicator
                  (fun x => w₁.grad x i)) 2
                (volumeMeasureOn (axisCube z L))).toReal) +
              ∑ i : Fin 2, (eLpNorm
                ({x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x}.indicator
                  (fun x => w₂.grad x i)) 2
                (volumeMeasureOn (axisCube z L))).toReal ≤
              E₀ * Real.sqrt
                ((volume {x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x}).toReal +
                  (volume
                    {x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x}).toReal)) →
          ∀ᵐ x ∂(volumeMeasureOn (axisCube z L)),
            w₁.toFun x ≤ m₀ + Cd * L * E₀ := by
  classical
  obtain ⟨C, hC, hrecurrence⟩ := deGiorgi_levelRecursion_two
  set Cd : ℝ := 4 * C + 1 with hCd_def
  have hCd : 0 < Cd := by
    rw [hCd_def]
    exact add_pos_of_nonneg_of_pos (mul_nonneg (by norm_num) hC) one_pos
  have hchoice : 4 * C ≤ Cd := by rw [hCd_def]; linarith only
  refine ⟨Cd, hCd.le, ?_⟩
  intro z L hL w₁ w₂ hw₁meas hw₂meas hmatch m₀ E₀ hE₀ hmedian hlevel
  have hUmeas : MeasurableSet (axisCube z L) := (isOpen_axisCube z L).measurableSet
  have hab : (z : Vec 2) ≤ fun i => z i + L :=
    fun _ => le_add_of_nonneg_right hL.le
  have hVolU : (volume (axisCube z L)).toReal = L ^ 2 := by
    rw [axisCube, Real.volume_pi_Ioo_toReal hab,
      show (fun i => z i + L - z i) = (fun _ : Fin 2 => L) from by
        funext i
        ring,
      Finset.prod_const]
    norm_num
  have hVolU_top : volume (axisCube z L) ≠ ⊤ := by
    rw [axisCube, Real.volume_pi_Ioo]
    exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top
  have hSub_top : ∀ (S : Set (Vec 2)), S ⊆ axisCube z L → volume S ≠ ⊤ :=
    fun S hSU => ne_top_of_le_ne_top hVolU_top (measure_mono hSU)
  let a : ℝ → ℝ := fun k =>
    (volume {x | x ∈ axisCube z L ∧ m₀ + k < w₁.toFun x}).toReal +
      (volume {x | x ∈ axisCube z L ∧ m₀ + k < w₂.toFun x}).toReal
  have ha : ∀ k, 0 ≤ a k := fun _ => add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hrec : ∀ k l : ℝ, 0 ≤ k → k < l →
      (l - k) ^ 2 * (a l) ^ (1 / 2 : ℝ) ≤
        (C ^ 2 * L * E₀ ^ 2) * a k :=
    hrecurrence z L hL w₁ w₂ hw₁meas hw₂meas hmatch m₀ E₀ hE₀
      hmedian hlevel
  rcases eq_or_lt_of_le hE₀ with rfl | hE₀pos
  · have hnull : ∀ n : ℕ, volume
        {x | x ∈ axisCube z L ∧ m₀ + 1 / ((n + 1 : ℕ) : ℝ) < w₁.toFun x} = 0 := by
      intro n
      set ε : ℝ := 1 / ((n + 1 : ℕ) : ℝ) with hε_def
      have hε : 0 < ε := by rw [hε_def]; positivity
      have hr := hrec 0 ε le_rfl hε
      norm_num at hr
      have hprod_nonneg : 0 ≤ ε ^ 2 * (a ε) ^ (1 / 2 : ℝ) :=
        mul_nonneg (sq_nonneg ε) (Real.rpow_nonneg (ha ε) _)
      have hprod : ε ^ 2 * (a ε) ^ (1 / 2 : ℝ) = 0 :=
        le_antisymm hr hprod_nonneg
      have hsqrt : (a ε) ^ (1 / 2 : ℝ) = 0 :=
        (mul_eq_zero.mp hprod).resolve_left (pow_ne_zero 2 hε.ne')
      have haε : a ε = 0 := by
        rw [← Real.sqrt_eq_rpow] at hsqrt
        exact (Real.sqrt_eq_zero (ha ε)).mp hsqrt
      have hfirst :
          (volume {x | x ∈ axisCube z L ∧ m₀ + ε < w₁.toFun x}).toReal = 0 := by
        apply le_antisymm
        · calc
            (volume {x | x ∈ axisCube z L ∧ m₀ + ε < w₁.toFun x}).toReal ≤
                a ε := le_add_of_nonneg_right ENNReal.toReal_nonneg
            _ = 0 := haε
        · exact ENNReal.toReal_nonneg
      rw [hε_def]
      exact (ENNReal.toReal_eq_zero_iff _).mp hfirst |>.resolve_right
        (hSub_top _ fun x hx => hx.1)
    have hbad : volume {x | x ∈ axisCube z L ∧ m₀ < w₁.toFun x} = 0 := by
      let S : ℕ → Set (Vec 2) := fun n =>
        {x | x ∈ axisCube z L ∧ m₀ + 1 / ((n + 1 : ℕ) : ℝ) < w₁.toFun x}
      have hsub : {x | x ∈ axisCube z L ∧ m₀ < w₁.toFun x} ⊆ ⋃ n, S n := by
        rintro x ⟨hxU, hx⟩
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
        have hn' : m₀ + 1 / (((n + 1 : ℕ) : ℝ)) < w₁.toFun x := by
          rw [Nat.cast_add, Nat.cast_one]
          linarith only [hn]
        exact Set.mem_iUnion.2 ⟨n, hxU, hn'⟩
      exact measure_mono_null hsub (measure_iUnion_null fun n => hnull n)
    refine (MeasureTheory.ae_iff).mpr ?_
    simp only [mul_zero, add_zero, not_le]
    rw [Measure.restrict_apply' hUmeas]
    have hset : {x | m₀ < w₁.toFun x} ∩ axisCube z L =
        {x | x ∈ axisCube z L ∧ m₀ < w₁.toFun x} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
      tauto
    rw [hset]
    exact hbad
  · set K : ℝ := Cd * L * E₀ with hK_def
    have hK : 0 < K := by rw [hK_def]; positivity
    have hLd : 0 < L ^ 2 := sq_pos_of_pos hL
    have ha0 : a (deGiorgiLevel K 0) ≤ L ^ 2 := by
      rw [deGiorgiLevel_zero, hVolU.symm]
      have hmedian' :
          volume {x | x ∈ axisCube z L ∧ m₀ + 0 < w₁.toFun x} +
              volume {x | x ∈ axisCube z L ∧ m₀ + 0 < w₂.toFun x} ≤
            volume (axisCube z L) := by
        simpa only [add_zero] using hmedian
      have hm := ENNReal.toReal_mono hVolU_top hmedian'
      rw [ENNReal.toReal_add (hSub_top _ fun x hx => hx.1)
        (hSub_top _ fun x hx => hx.1)] at hm
      exact hm
    have hKcond :
        (((C ^ 2 * L * E₀ ^ 2) / K ^ 2) ^ (2 : ℝ)) * 16 *
            (L ^ 2) ^ (1 : ℝ) ≤
          (16 : ℝ) ^ (-(1 / (1 : ℝ))) := by
      rw [hK_def]
      exact deGiorgi_admissible_two hC hCd hchoice hL hE₀pos
    have hlimit := deGiorgi_levelVolume_tendsto_zero
      (a := a) (Ld := L ^ 2) (Crec := C ^ 2 * L * E₀ ^ 2) (K := K)
      (α := 2) (β := 1) (γ := 1 / 2) (B := 16)
      ha hLd (by positivity) hK (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) ha0 hrec hKcond
    set T : Set (Vec 2) := {x | x ∈ axisCube z L ∧ m₀ + K < w₁.toFun x}
    have hTtop : volume T ≠ ⊤ := hSub_top _ fun x hx => hx.1
    have hTzero : volume T = 0 := by
      refine measure_eq_zero_of_toReal_tendsto hTtop ?_ hlimit
      intro n
      have hsub : T ⊆
          {x | x ∈ axisCube z L ∧ m₀ + deGiorgiLevel K n < w₁.toFun x} := by
        rintro x ⟨hxU, hx⟩
        exact ⟨hxU, by
          have hn := deGiorgiLevel_lt hK n
          linarith only [hx, hn]⟩
      have hfirst := ENNReal.toReal_mono
        (hSub_top _ fun x hx => hx.1) (measure_mono hsub)
      exact le_trans hfirst (le_add_of_nonneg_right ENNReal.toReal_nonneg)
    refine (MeasureTheory.ae_iff).mpr ?_
    have hset : {x | ¬w₁.toFun x ≤ m₀ + Cd * L * E₀} =
        {x | m₀ + K < w₁.toFun x} := by
      ext x
      rw [hK_def]
      simp only [Set.mem_ofPred_eq, not_le]
    rw [hset, Measure.restrict_apply' hUmeas]
    have hinter : {x | m₀ + K < w₁.toFun x} ∩ axisCube z L = T := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, T]
      tauto
    rw [hinter]
    exact hTzero

end

end DivergenceFormProcess.Regularity
