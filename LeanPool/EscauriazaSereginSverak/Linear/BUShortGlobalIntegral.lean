/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortShiftedEarlyLimit
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortWeightedComparison

/-!
# Integrating phase and shell errors

An integrable Gaussian majorant controls the negative-phase error,
while a fixed-parameter weighted energy controls the spatial shell.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

attribute [local instance] Classical.propDecidable

/-- A phase-gap majorant and an integrable global energy bound control
the phase and shell terms on any smaller cutoff support. -/
theorem bu_short_split_integral_le_global
    (K G H : Set ParabolicPoint)
    (hK : MeasurableSet K) (hG : MeasurableSet G)
    (hH : MeasurableSet H)
    (hKH : K ⊆ H) (hGH : G ⊆ H)
    (W T P Q B : ParabolicPoint → ℝ)
    (C₁ C₂ e : ℝ)
    (hW : ∀ z ∈ H, 0 ≤ W z)
    (hP : ∀ z ∈ H, 0 ≤ P z)
    (hQ : ∀ z ∈ H, 0 ≤ Q z)
    (hgap : ∀ z ∈ G, W z ≤ e * T z)
    (hWP : IntegrableOn (fun z => W z * P z * Q z) H volume)
    (hWQ : IntegrableOn (fun z => W z * Q z) H volume)
    (hTPQ : IntegrableOn (fun z => T z * P z * Q z) G volume)
    (hB : IntegrableOn (fun z => W z * B z ^ 2) K volume) :
    (∫ z in K,
      4 * W z * (if z ∈ G then C₁ ^ 2 * P z else C₂ ^ 2) * Q z +
      2 * W z * B z ^ 2 ∂(volume : Measure ParabolicPoint)) ≤
      4 * C₁ ^ 2 * e *
        (∫ z in G, T z * P z * Q z
          ∂(volume : Measure ParabolicPoint)) +
      4 * C₂ ^ 2 *
        (∫ z in H, W z * Q z
          ∂(volume : Measure ParabolicPoint)) +
      2 * (∫ z in K, W z * B z ^ 2
          ∂(volume : Measure ParabolicPoint)) := by
  let F : ParabolicPoint → ℝ := fun z => W z * P z * Q z
  let S : ParabolicPoint → ℝ := fun z => W z * Q z
  let J : ParabolicPoint → ℝ := fun z => T z * P z * Q z
  let E : ParabolicPoint → ℝ := fun z => W z * B z ^ 2
  have hFK : IntegrableOn F K volume := hWP.mono_set hKH
  have hSK : IntegrableOn S K volume := hWQ.mono_set hKH
  have hFG : IntegrableOn F G volume := hWP.mono_set hGH
  have hFI : IntegrableOn (G.indicator F) K volume :=
    hFK.indicator hG
  have hSI : IntegrableOn (Gᶜ.indicator S) K volume :=
    hSK.indicator hG.compl
  have hfirst : IntegrableOn (fun z =>
      4 * C₁ ^ 2 * G.indicator F z +
        4 * C₂ ^ 2 * Gᶜ.indicator S z) K volume :=
    (hFI.const_mul _).add (hSI.const_mul _)
  have htotal : IntegrableOn (fun z =>
      4 * C₁ ^ 2 * G.indicator F z +
        4 * C₂ ^ 2 * Gᶜ.indicator S z + 2 * E z) K volume :=
    hfirst.add (hB.const_mul 2)
  have hpoint (z : ParabolicPoint) :
      4 * W z * (if z ∈ G then C₁ ^ 2 * P z else C₂ ^ 2) * Q z +
        2 * W z * B z ^ 2 =
      4 * C₁ ^ 2 * G.indicator F z +
        4 * C₂ ^ 2 * Gᶜ.indicator S z + 2 * E z := by
    by_cases hz : z ∈ G
    · simp only [hz, ite_true, Set.indicator, Set.mem_compl_iff,
        not_true_eq_false, ite_false]
      dsimp [F, S, E]
      ring
    · simp only [hz, ite_false, Set.indicator, Set.mem_compl_iff,
        not_false_eq_true, ite_true]
      dsimp [F, S, E]
      ring
  have hphase : (∫ z in K, G.indicator F z
        ∂(volume : Measure ParabolicPoint)) ≤
      e * (∫ z in G, J z
        ∂(volume : Measure ParabolicPoint)) := by
    have hFglobal : Integrable (G.indicator F) volume :=
      hFG.integrable_indicator hG
    have hFI0 : 0 ≤ᵐ[(volume : Measure ParabolicPoint)]
        G.indicator F := by
      filter_upwards [] with z
      by_cases hz : z ∈ G
      · have hzH := hGH hz
        simp only [Set.indicator, hz, ite_true]
        dsimp [F]
        exact mul_nonneg (mul_nonneg (hW z hzH) (hP z hzH))
          (hQ z hzH)
      · simp [Set.indicator, hz]
    have hsmall : (∫ z in K, G.indicator F z
        ∂(volume : Measure ParabolicPoint)) ≤
        ∫ z in G, F z ∂(volume : Measure ParabolicPoint) := by
      calc
        _ ≤ ∫ z, G.indicator F z
            ∂(volume : Measure ParabolicPoint) :=
          setIntegral_le_integral hFglobal hFI0
        _ = _ := integral_indicator hG
    have hJscaled : IntegrableOn (fun z => e * J z) G volume :=
      hTPQ.const_mul e
    have hcompare : (∫ z in G, F z
        ∂(volume : Measure ParabolicPoint)) ≤
        ∫ z in G, e * J z
          ∂(volume : Measure ParabolicPoint) := by
      apply setIntegral_mono_on hFG hJscaled hG
      intro z hz
      have hzH := hGH hz
      have hPQ : 0 ≤ P z * Q z := mul_nonneg (hP z hzH) (hQ z hzH)
      have h := mul_le_mul_of_nonneg_right (hgap z hz) hPQ
      dsimp [F, J]
      nlinarith only [h]
    rw [integral_const_mul] at hcompare
    exact hsmall.trans hcompare
  have hshell : (∫ z in K, Gᶜ.indicator S z
        ∂(volume : Measure ParabolicPoint)) ≤
      ∫ z in H, S z ∂(volume : Measure ParabolicPoint) := by
    have hfirst' : (∫ z in K, Gᶜ.indicator S z
        ∂(volume : Measure ParabolicPoint)) ≤
        ∫ z in K, S z ∂(volume : Measure ParabolicPoint) := by
      apply setIntegral_mono_on hSI hSK hK
      intro z hz
      have hS0 : 0 ≤ S z := by
        dsimp [S]
        exact mul_nonneg (hW z (hKH hz)) (hQ z (hKH hz))
      by_cases hzG : z ∈ G
      · simpa [Set.indicator, hzG] using hS0
      · simp [Set.indicator, hzG]
    have hsecond : (∫ z in K, S z
        ∂(volume : Measure ParabolicPoint)) ≤
        ∫ z in H, S z ∂(volume : Measure ParabolicPoint) := by
      apply setIntegral_mono_set hWQ
      · filter_upwards [ae_restrict_mem hH] with z hz
        exact mul_nonneg (hW z hz) (hQ z hz)
      · exact ae_of_all _ hKH
    exact hfirst'.trans hsecond
  have hmain : (∫ z in K,
      4 * C₁ ^ 2 * G.indicator F z +
        4 * C₂ ^ 2 * Gᶜ.indicator S z + 2 * E z
        ∂(volume : Measure ParabolicPoint)) =
      4 * C₁ ^ 2 * (∫ z in K, G.indicator F z
        ∂(volume : Measure ParabolicPoint)) +
      4 * C₂ ^ 2 * (∫ z in K, Gᶜ.indicator S z
        ∂(volume : Measure ParabolicPoint)) +
      2 * (∫ z in K, E z
        ∂(volume : Measure ParabolicPoint)) := by
    rw [integral_add hfirst (hB.const_mul 2),
      integral_add (hFI.const_mul _) (hSI.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul]
  calc
    (∫ z in K,
      4 * W z * (if z ∈ G then C₁ ^ 2 * P z else C₂ ^ 2) * Q z +
      2 * W z * B z ^ 2 ∂(volume : Measure ParabolicPoint)) =
        ∫ z in K,
          4 * C₁ ^ 2 * G.indicator F z +
            4 * C₂ ^ 2 * Gᶜ.indicator S z + 2 * E z
          ∂(volume : Measure ParabolicPoint) := by
        exact setIntegral_congr_fun hK (fun z _ => hpoint z)
    _ = _ := hmain
    _ ≤ 4 * C₁ ^ 2 * (e * ∫ z in G, J z
          ∂(volume : Measure ParabolicPoint)) +
        4 * C₂ ^ 2 * (∫ z in H, S z
          ∂(volume : Measure ParabolicPoint)) +
        2 * ∫ z in K, E z
          ∂(volume : Measure ParabolicPoint) := by
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_left hphase (by positivity))
          (mul_le_mul_of_nonneg_left hshell (by positivity)))
        le_rfl
    _ = _ := by ring

end ESS
