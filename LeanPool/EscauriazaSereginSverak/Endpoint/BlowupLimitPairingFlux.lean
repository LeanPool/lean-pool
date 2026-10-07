/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitFluxEstimates
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitPairingModulus

/-!
# Momentum flux moduli on rescaled cylinders

Uniform velocity, gradient, and pressure bounds give the endpoint-compatible
pairing modulus on each compact spacetime cylinder.
-/

public section


open MeasureTheory Set
open scoped ENNReal
open CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The momentum formula and uniform component bounds give the time modulus
for a smooth spatial pairing on a compact cylinder, through both endpoints. -/
theorem blowup_limit_pairing_modulus_of_momentum_flux
    {C : Set Vec3} (hC : IsCompact C)
    (a b : ℝ) (U : ℕ → ParabolicPoint → Vec3)
    (DU : ℕ → ParabolicPoint → Fin 3 → Fin 3 → ℝ)
    (P : ℕ → ParabolicPoint → ℝ)
    (Dw : Fin 3 → Fin 3 → ParabolicPoint → ℝ)
    (divw : ParabolicPoint → ℝ) (G : ℕ → ℝ → ℝ)
    (Mvel Mgrad Mpress Mtest Mdiv : ℝ≥0∞)
    (hMvel : Mvel < ⊤) (hMgrad : Mgrad < ⊤)
    (hMpress : Mpress < ⊤) (hMtest : Mtest < ⊤)
    (hMdiv : Mdiv < ⊤)
    (hU : ∀ n i,
      MemLp (fun z => U n z i) 3
        (volume.restrict (C ×ˢ Icc a b)) ∧
      eLpNorm (fun z => U n z i) 3
        (volume.restrict (C ×ˢ Icc a b)) ≤ Mvel)
    (hDU : ∀ n i j,
      MemLp (fun z => DU n z i j) 2
        (volume.restrict (C ×ˢ Icc a b)) ∧
      eLpNorm (fun z => DU n z i j) 2
        (volume.restrict (C ×ˢ Icc a b)) ≤ Mgrad)
    (hP : ∀ n, MemLp (P n) (3 / 2 : ℝ≥0∞)
        (volume.restrict (C ×ˢ Icc a b)) ∧
      eLpNorm (P n) (3 / 2 : ℝ≥0∞)
        (volume.restrict (C ×ˢ Icc a b)) ≤ Mpress)
    (hDw : ∀ i j,
      MemLp (Dw i j) ⊤ (volume.restrict (C ×ˢ Icc a b)) ∧
      eLpNorm (Dw i j) ⊤ (volume.restrict (C ×ˢ Icc a b)) ≤ Mtest)
    (hdivw : MemLp divw ⊤ (volume.restrict (C ×ˢ Icc a b)) ∧
      eLpNorm divw ⊤ (volume.restrict (C ×ˢ Icc a b)) ≤ Mdiv)
    (hformula : ∀ n s t, s ∈ Icc a b → t ∈ Icc a b → s ≤ t →
      G n t - G n s = ∫ z in C ×ˢ Ioc s t,
        (∑ i : Fin 3, ∑ j : Fin 3,
          U n z i * U n z j * Dw i j z) -
        (∑ i : Fin 3, ∑ j : Fin 3,
          DU n z i j * Dw i j z) + P n z * divw z) :
    ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
      ∀ n s t, s ∈ Icc a b → t ∈ Icc a b →
        |G n t - G n s| ≤ A * dist t s + B * (dist t s) ^ θ := by
  let μ : Measure ParabolicPoint := volume.restrict (C ×ˢ Icc a b)
  have : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    change (volume.restrict (C ×ˢ Icc a b)) Set.univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact IsCompact.measure_lt_top (hC.prod isCompact_Icc)
  let F : ℕ → ParabolicPoint → ℝ := fun n z =>
    (∑ i : Fin 3, ∑ j : Fin 3,
      U n z i * U n z j * Dw i j z) -
    (∑ i : Fin 3, ∑ j : Fin 3,
      DU n z i j * Dw i j z) + P n z * divw z
  let K : ℝ≥0∞ :=
    (∑ _i : Fin 3, ∑ _j : Fin 3, Mvel * Mvel * Mtest) +
    (∑ _i : Fin 3, ∑ _j : Fin 3,
      Mgrad * μ Set.univ ^ (1 / 6 : ℝ) * Mtest) + Mpress * Mdiv
  have hK : K < ⊤ := by
    have hμ : μ Set.univ < ⊤ := by
      change (volume.restrict (C ×ˢ Icc a b)) Set.univ < ⊤
      rw [Measure.restrict_apply_univ]
      exact IsCompact.measure_lt_top (hC.prod isCompact_Icc)
    have hμpow : μ Set.univ ^ (1 / 6 : ℝ) < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg (by norm_num) hμ.ne
    have hconv : Mvel * Mvel * Mtest < ⊤ :=
      ENNReal.mul_lt_top (ENNReal.mul_lt_top hMvel hMvel) hMtest
    have hdiff : Mgrad * μ Set.univ ^ (1 / 6 : ℝ) * Mtest < ⊤ :=
      ENNReal.mul_lt_top (ENNReal.mul_lt_top hMgrad hμpow) hMtest
    have hpres : Mpress * Mdiv < ⊤ := ENNReal.mul_lt_top hMpress hMdiv
    dsimp [K]
    apply ENNReal.add_lt_top.mpr
    constructor
    · apply ENNReal.add_lt_top.mpr
      constructor
      · exact ENNReal.sum_lt_top.2 fun _ _ =>
          ENNReal.sum_lt_top.2 fun _ _ => hconv
      · exact ENNReal.sum_lt_top.2 fun _ _ =>
          ENNReal.sum_lt_top.2 fun _ _ => hdiff
    · exact hpres
  let M : ℝ := K.toReal
  have hM : 0 ≤ M := ENNReal.toReal_nonneg
  have hflux := blowup_limit_momentum_flux_memLp_three_halves
    U DU P Dw divw Mvel Mgrad Mpress Mtest Mdiv
    hU hDU hP hDw hdivw
  have hF : ∀ n,
      MemLp (F n) (3 / 2 : ℝ≥0∞) μ ∧
      eLpNorm (F n) (3 / 2 : ℝ≥0∞) μ ≤ ENNReal.ofReal M := by
    intro n
    have hn := hflux n
    change MemLp (F n) (3 / 2 : ℝ≥0∞) μ ∧ _
    refine ⟨?_, ?_⟩
    · simpa [F, μ] using hn.1
    · have hbound : eLpNorm (F n) (3 / 2 : ℝ≥0∞) μ ≤ K := by
        simpa [F, μ, K] using hn.2
      simpa [M, ENNReal.ofReal_toReal hK.ne] using hbound
  have hformula' : ∀ n s t, s ∈ Icc a b → t ∈ Icc a b →
      s ≤ t → G n t - G n s = ∫ z in C ×ˢ Ioc s t, F n z := by
    intro n s t hs ht hst
    simpa [F] using hformula n s t hs ht hst
  have hmod := blowup_limit_interval_pairing_modulus_of_spacetime_flux
    hC a b M hM F G hF hformula'
  refine ⟨0, M * (volume C).toReal ^ (1 / 3 : ℝ),
    (1 / 3 : ℝ), by norm_num, by positivity, by norm_num, ?_⟩
  intro n s t hs ht
  have hvol : 0 ≤ (volume C).toReal := ENNReal.toReal_nonneg
  have hdist : 0 ≤ dist t s := dist_nonneg
  have hpow := hmod n s t hs ht
  rw [Real.mul_rpow hvol hdist] at hpow
  change |G n t - G n s| ≤
    0 * dist t s + (M * (volume C).toReal ^ (1 / 3 : ℝ)) *
      (dist t s) ^ (1 / 3 : ℝ)
  simpa [mul_assoc] using hpow

end ESS

end
