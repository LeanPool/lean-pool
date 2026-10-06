/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Comparison.Direct.BarrierBound
public import LeanPool.CIVAxisymmetric.Comparison.ComparisonSigmaLimit
public import LeanPool.CIVAxisymmetric.Comparison.ELpNormBridge
public import LeanPool.CIVAxisymmetric.Comparison.SliceBounds
public import LeanPool.CIVAxisymmetric.Comparison.AdmissibleWeakDivergence
public import Mathlib.Data.Rat.Denumerable
public import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Assembly of `lem:aniso:comparison`

On each compact working interval `[a, b] ⊆ I` the drift is bounded and Lipschitz with one
constant `Λ` and `q` is bounded by one constant; for almost every `τ₀ ∈ [a, b]` which is a
reference time of the mollified equation for every radius `1/(n+1)`, the barrier bound
`q ≤ Ψ_σ` of `CIV.ae_ae_le_barrier_of_referenceTime` holds on `[τ₀, b]` for every `σ > 0`, and
`σ ↓ 0` gives `q ≤ ‖q(·, τ₀)‖_{L^∞}` there. Countably many rational working intervals exhaust
`I`, the same argument for `-q` gives the two-sided bound, and the essential supremum bridge
turns it into `eq:aniso:comparison:conclusion`.
-/

public section

open MeasureTheory Set Filter Topology
open CKN
open scoped ENNReal

noncomputable section
namespace CIV

variable {m : ℕ}

/-- **The upper bound on one working interval.** For almost every `τ₀ ∈ [a, b]`, every
nonnegative essential bound `M` of `q(·, τ₀)` bounds `q` from above at almost every time of
`[τ₀, b]`. -/
theorem ae_ae_le_of_window {d : ℕ} {I : Set ℝ} (hI : IsOpen I) (hIoc : I.OrdConnected)
    {B : Vec m × ℝ → Vec m} {divB q : Vec m × ℝ → ℝ}
    (hB : IsAdmissibleDrift m I B divB) (hq : IsLocallyBoundedOn m I q)
    (heq : IsDistributionalDriftDiffusion m d I B divB q) {a b : ℝ} (hab : Icc a b ⊆ I) :
    ∀ᵐ τ₀ ∂(volume.restrict I), τ₀ ∈ Icc a b → ∀ M : ℝ, 0 ≤ M →
      (∀ᵐ x : Vec m, |q (x, τ₀)| ≤ M) →
        ∀ᵐ τ ∂(volume.restrict (Icc τ₀ b)), ∀ᵐ x : Vec m, q (x, τ) ≤ M := by
  obtain ⟨Λ, hΛ⟩ := hB.2.2 (Icc a b) isCompact_Icc hab
  obtain ⟨Mq, hMq, hMqb⟩ := hq.ae_slice_bound isCompact_Icc hab
  have hmeasI := hq.ae_slice_measurable
  have hgoodab : ∀ᵐ s ∂(volume.restrict (Icc a b)),
      AEStronglyMeasurable (fun y => q (y, s)) volume ∧ (∀ᵐ y ∂volume, |q (y, s)| ≤ Mq) ∧
      (∀ x, ‖B (x, s)‖ ≤ Λ) ∧ LipschitzWith Λ (fun x => B (x, s)) ∧
      (∀ x, |divB (x, s)| ≤ Λ) ∧
      (∀ ψ : Vec m → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        ∫ x, divB (x, s) * ψ x = -∫ x, ∑ i, B (x, s) i * fderiv ℝ ψ x (basisVec i)) := by
    filter_upwards [hΛ, hMqb, ae_restrict_of_ae_restrict_of_subset hab hmeasI]
      with s hs1 hs2 hs3
    exact ⟨hs3, hs2, hs1.1, hs1.2.1, hs1.2.2.1, hs1.2.2.2⟩
  have hεs : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  filter_upwards [ae_isReferenceTime_mollifySlice (d := d) hI hIoc hB hq heq hεs, hmeasI]
    with τ₀ href hτ₀m hτ₀ab M hM hτ₀M
  have hsubτ : Icc τ₀ b ⊆ Icc a b := Icc_subset_Icc hτ₀ab.1 le_rfl
  have hgood := ae_restrict_of_ae_restrict_of_subset hsubτ hgoodab
  have hσ : ∀ σ : ℝ, 0 < σ → ∀ᵐ τ ∂(volume.restrict (Icc τ₀ b)), τ₀ ≤ τ →
      ∀ᵐ x ∂(volume : Measure (Vec m)), q (x, τ) ≤ barrier m M σ (barrierRate m d Λ) τ₀ (x, τ) := by
    intro σ hσpos
    filter_upwards [ae_ae_le_barrier_of_referenceTime hI hIoc hB hq heq hσpos hM hMq
      hτ₀ab.2 (hsubτ.trans hab) hgood hτ₀m hτ₀M href] with τ hτ _
    exact hτ
  filter_upwards [ae_ae_le_of_forall_pos_ae_ae_le_barrier hσ, ae_restrict_mem measurableSet_Icc]
    with τ hτ hτmem
  exact hτ hτmem.1

/-- **The upper bound on `I`.** For almost every `τ₀ ∈ I`, every nonnegative essential bound
of `q(·, τ₀)` bounds `q` from above at almost every later time of `I`. -/
theorem ae_ae_le_of_isDistributionalDriftDiffusion {d : ℕ} {I : Set ℝ} (hI : IsOpen I)
    (hIoc : I.OrdConnected) {B : Vec m × ℝ → Vec m} {divB q : Vec m × ℝ → ℝ}
    (hB : IsAdmissibleDrift m I B divB) (hq : IsLocallyBoundedOn m I q)
    (heq : IsDistributionalDriftDiffusion m d I B divB q) :
    ∀ᵐ τ₀ ∂(volume.restrict I), ∀ M : ℝ, 0 ≤ M → (∀ᵐ x : Vec m, |q (x, τ₀)| ≤ M) →
      ∀ᵐ τ ∂(volume.restrict I), τ₀ < τ → ∀ᵐ x : Vec m, q (x, τ) ≤ M := by
  classical
  have hwin : ∀ p : ℚ × ℚ, ∀ᵐ τ₀ ∂(volume.restrict I), Icc (p.1 : ℝ) p.2 ⊆ I →
      τ₀ ∈ Icc (p.1 : ℝ) p.2 → ∀ M : ℝ, 0 ≤ M → (∀ᵐ x : Vec m, |q (x, τ₀)| ≤ M) →
        ∀ᵐ τ ∂(volume.restrict (Icc τ₀ p.2)), ∀ᵐ x : Vec m, q (x, τ) ≤ M := by
    intro p
    by_cases hp : Icc (p.1 : ℝ) p.2 ⊆ I
    · filter_upwards [ae_ae_le_of_window hI hIoc hB hq heq hp] with τ₀ h _
      exact h
    · exact Eventually.of_forall fun τ₀ h => absurd h hp
  rw [← ae_all_iff] at hwin
  filter_upwards [hwin, ae_restrict_mem hI.measurableSet] with τ₀ hτ₀ hτ₀I M hM hτ₀M
  -- a rational left endpoint below `τ₀`
  obtain ⟨l, u, ⟨hlτ, hτu⟩, hIoo⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hI.mem_nhds hτ₀I)
  obtain ⟨a, hla, haτ⟩ := exists_rat_btwn hlτ
  have haI : (a : ℝ) ∈ I := hIoo ⟨hla, lt_trans haτ hτu⟩
  -- the countable family of right endpoints
  have hall : ∀ᵐ τ ∂volume, ∀ b : ℚ, Icc (a : ℝ) b ⊆ I → τ₀ ≤ b → τ ∈ Icc τ₀ (b : ℝ) →
      ∀ᵐ x : Vec m, q (x, τ) ≤ M := by
    rw [ae_all_iff]
    intro b
    by_cases hb : Icc (a : ℝ) b ⊆ I ∧ τ₀ ≤ b
    · have h := hτ₀ (a, b) hb.1 ⟨haτ.le, hb.2⟩ M hM hτ₀M
      rw [ae_restrict_iff' measurableSet_Icc] at h
      filter_upwards [h] with τ hτ _ _ hτmem
      exact hτ hτmem
    · exact Eventually.of_forall fun τ h1 h2 => absurd ⟨h1, h2⟩ hb
  filter_upwards [ae_restrict_of_ae hall, ae_restrict_mem hI.measurableSet] with τ hτ hτI hlt
  obtain ⟨l', u', ⟨hlτ', hτu'⟩, hIoo'⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hI.mem_nhds hτI)
  obtain ⟨b, hτb, hbu⟩ := exists_rat_btwn hτu'
  have hbI : (b : ℝ) ∈ I := hIoo' ⟨lt_trans hlτ' hτb, hbu⟩
  exact hτ b (hIoc.out haI hbI) (le_of_lt (lt_trans hlt hτb)) ⟨hlt.le, hτb.le⟩

/-- **The two-sided transfer of essential bounds.** For almost every `τ₀ ∈ I` and almost every
later `τ ∈ I`, every essential bound of `|q(·, τ₀)|` is an essential bound of `|q(·, τ)|`. The
canonical bound `‖q(·, τ₀)‖_{L^∞}` is used for `q` and for `-q`, so that the exceptional set of
times does not depend on the bound. -/
theorem ae_ae_abs_le_of_isDistributionalDriftDiffusion {d : ℕ} {I : Set ℝ} (hI : IsOpen I)
    (hIoc : I.OrdConnected) {B : Vec m × ℝ → Vec m} {divB q : Vec m × ℝ → ℝ}
    (hB : IsAdmissibleDrift m I B divB) (hq : IsLocallyBoundedOn m I q)
    (heq : IsDistributionalDriftDiffusion m d I B divB q) :
    ∀ᵐ τ₀ ∂(volume.restrict I), ∀ᵐ τ ∂(volume.restrict I), τ₀ < τ →
      ∀ M : ℝ, (∀ᵐ x : Vec m, |q (x, τ₀)| ≤ M) → ∀ᵐ x : Vec m, |q (x, τ)| ≤ M := by
  obtain ⟨G, -, hGvol, hGprop⟩ := exists_good_time_set hI hq
  have hGae : ∀ᵐ τ₀ ∂(volume.restrict I), τ₀ ∈ G := by
    rw [ae_restrict_iff' hI.measurableSet, ae_iff]
    refine measure_mono_null (fun τ hτ => ?_) hGvol
    simp only [mem_ofPred_eq, not_imp] at hτ
    exact hτ
  have hpos := ae_ae_le_of_isDistributionalDriftDiffusion hI hIoc hB hq heq
  have hneg := ae_ae_le_of_isDistributionalDriftDiffusion hI hIoc hB hq.neg heq.neg
  filter_upwards [hGae, hpos, hneg] with τ₀ hτ₀G hτ₀pos hτ₀neg
  obtain ⟨-, M', hM'bound⟩ := hGprop τ₀ hτ₀G
  have hM'bound' : ∀ᵐ x : Vec m, ‖q (x, τ₀)‖ ≤ M' := by
    filter_upwards [hM'bound] with x hx
    rwa [Real.norm_eq_abs]
  have hnetop : eLpNormEssSup (fun x => q (x, τ₀)) volume ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (eLpNormEssSup_le_of_ae_bound hM'bound')
  set M0 : ℝ := (eLpNormEssSup (fun x => q (x, τ₀)) volume).toReal with hM0def
  have hM0nonneg : 0 ≤ M0 := ENNReal.toReal_nonneg
  have hM0bound : ∀ᵐ x : Vec m, |q (x, τ₀)| ≤ M0 := by
    have h1 : ∀ᵐ x : Vec m, ‖q (x, τ₀)‖ₑ ≤ eLpNormEssSup (fun x => q (x, τ₀)) volume :=
      ae_le_eLpNormEssSup
    filter_upwards [h1] with x hx
    have hxreal : ‖q (x, τ₀)‖ₑ.toReal ≤ M0 := ENNReal.toReal_mono hnetop hx
    rwa [toReal_enorm, Real.norm_eq_abs] at hxreal
  have hM0bound_neg : ∀ᵐ x : Vec m, |(fun z => -q z) (x, τ₀)| ≤ M0 := by
    simpa using hM0bound
  filter_upwards [hτ₀pos M0 hM0nonneg hM0bound, hτ₀neg M0 hM0nonneg hM0bound_neg]
    with τ hτ1 hτ2 hlt M hMbound
  by_cases hM0le : (0 : ℝ) ≤ M
  · have hMbound' : ∀ᵐ x : Vec m, ‖q (x, τ₀)‖ ≤ M := by
      filter_upwards [hMbound] with x hx
      rwa [Real.norm_eq_abs]
    have hle : eLpNormEssSup (fun x => q (x, τ₀)) volume ≤ ENNReal.ofReal M :=
      eLpNormEssSup_le_of_ae_bound hMbound'
    have hMge : M0 ≤ M := by
      have h3 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      rwa [ENNReal.toReal_ofReal hM0le] at h3
    filter_upwards [hτ1 hlt, hτ2 hlt] with x hx1 hx2
    have hx2' : -q (x, τ) ≤ M0 := hx2
    rw [abs_le]
    exact ⟨by linarith only [hx2', hMge], by linarith only [hx1, hMge]⟩
  · have hMneg : M < 0 := not_le.mp hM0le
    filter_upwards [hMbound] with x hx
    exact absurd hx (by linarith only [abs_nonneg (q (x, τ₀)), hMneg])

/-- **`lem:aniso:comparison`, first assertion** (`eq:aniso:comparison:conclusion`). -/
theorem comparison_of_isDistributionalDriftDiffusion {d : ℕ} {I : Set ℝ} (hI : IsOpen I)
    (hIoc : I.OrdConnected) {B : Vec m × ℝ → Vec m} {divB q : Vec m × ℝ → ℝ}
    (hB : IsAdmissibleDrift m I B divB) (hq : IsLocallyBoundedOn m I q)
    (heq : IsDistributionalDriftDiffusion m d I B divB q) :
    ∀ᵐ τ₀ ∂(volume.restrict I), ∀ᵐ τ ∂(volume.restrict I), τ₀ < τ →
      eLpNorm (fun x => q (x, τ)) ⊤ volume ≤ eLpNorm (fun x => q (x, τ₀)) ⊤ volume :=
  comparison_eLpNorm_top_of_ae_dominance hq
    (ae_ae_abs_le_of_isDistributionalDriftDiffusion hI hIoc hB hq heq)

end CIV
