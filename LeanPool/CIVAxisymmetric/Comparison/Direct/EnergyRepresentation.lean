/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Comparison.Direct.Profile
public import LeanPool.CIVAxisymmetric.Comparison.Direct.AnchorFubini
public import LeanPool.CIVAxisymmetric.Comparison.Barrier

/-!
# The energy at almost every time is a time integral from the reference time

Fix a reference time `τ₀` of the mollified equation (`CIV.ae_isReferenceTime_mollifySlice`) at
which the mollified slice lies below `M`. For each spatial point `x`, the function
`L(x, τ) = q_ε(x, τ₀) + ∫_{τ₀}^τ H(x, r) dr` is absolutely continuous in `τ` and agrees with
`q_ε(x, τ)` at almost every `τ` for almost every `x` (this is the time representative of the
manuscript, the sentence after `eq:aniso:comparison:mollified`); at `τ₀` it is the mollified slice
itself. The chain rule for the comparison profile `G` along `L - Ψ_σ` then gives, for almost every
later time `τ` and almost every `x`,

`G(q_ε(x, τ) - Ψ_σ(x, τ)) = ∫_{τ₀}^τ G'(q_ε - Ψ_σ)(x, s) (H(x, s) - ∂_τΨ_σ) ds`,

since `G(q_ε - Ψ_σ)` vanishes at `τ₀`.
-/

public section

open MeasureTheory Set Filter Topology
open CKN

noncomputable section
namespace CIV

variable {m : ℕ}

theorem barrier_time_shift (M σ K τ₀ s : ℝ) (x : Vec m) :
    barrier m M σ K τ₀ (x, s) = barrier m M σ K τ₀ (x, τ₀) + σ * K * (s - τ₀) := by
  unfold barrier
  ring

theorem le_barrier_at_anchor (M K τ₀ : ℝ) {σ : ℝ} (hσ : 0 ≤ σ) (x : Vec m) :
    M ≤ barrier m M σ K τ₀ (x, τ₀) := by
  unfold barrier
  have h := one_le_japaneseBracket x
  have h2 : 0 ≤ σ * (japaneseBracket m x + K * (τ₀ - τ₀)) := by
    rw [sub_self, mul_zero, add_zero]
    exact mul_nonneg hσ (by linarith only [h])
  linarith only [h2]

/-- The time integrability of the right side of the mollified equation at a fixed point. -/
theorem intervalIntegrable_mollifiedRHS {d : ℕ} {I : Set ℝ} (hI : IsOpen I)
    (hIoc : I.OrdConnected) {B : Vec m × ℝ → Vec m} {divB q : Vec m × ℝ → ℝ}
    (hB : IsAdmissibleDrift m I B divB) (hq : IsLocallyBoundedOn m I q)
    (heq : IsDistributionalDriftDiffusion m d I B divB q) {ε : ℝ} (hε : 0 < ε) (x : Vec m)
    {τ₁ τ₂ : ℝ} (hτ₁ : τ₁ ∈ I) (hτ₂ : τ₂ ∈ I) :
    IntervalIntegrable (fun s => mollifiedRHS m d ε B divB q x s) volume τ₁ τ₂ := by
  have hLoc := locallyIntegrableOn_mollifiedRHS (d := d) hε x hI hB hq heq
  have hIcc : IntegrableOn (fun s => mollifiedRHS m d ε B divB q x s) (uIcc τ₁ τ₂) volume :=
    hLoc.integrableOn_compact_subset (hIoc.uIcc_subset hτ₁ hτ₂) isCompact_uIcc
  exact intervalIntegrable_iff.mpr (hIcc.mono_set uIoc_subset_uIcc)

/-- **The energy density along the time representative, at one spatial point.** -/
theorem comparisonProfile_representative_eq {d : ℕ} {I : Set ℝ} (hI : IsOpen I)
    (hIoc : I.OrdConnected) {B : Vec m × ℝ → Vec m} {divB q : Vec m × ℝ → ℝ}
    (hB : IsAdmissibleDrift m I B divB) (hq : IsLocallyBoundedOn m I q)
    (heq : IsDistributionalDriftDiffusion m d I B divB q) {ε : ℝ} (hε : 0 < ε)
    {M σ K τ₀ τ : ℝ} (hσ : 0 ≤ σ) (hτ₀ : τ₀ ∈ I) (hτ : τ ∈ I) (x : Vec m)
    (hq0 : mollifySlice m ε q (x, τ₀) ≤ M)
    (hx : ∀ᵐ s ∂(volume.restrict I), mollifySlice m ε q (x, s) - mollifySlice m ε q (x, τ₀)
      = ∫ r in τ₀..s, mollifiedRHS m d ε B divB q x r) :
    comparisonProfile (mollifySlice m ε q (x, τ₀) + (∫ r in τ₀..τ, mollifiedRHS m d ε B divB q x r)
        - barrier m M σ K τ₀ (x, τ))
      = ∫ s in τ₀..τ, Real.smoothTransition
          (mollifySlice m ε q (x, s) - barrier m M σ K τ₀ (x, s))
          * (mollifiedRHS m d ε B divB q x s - σ * K) := by
  set H : ℝ → ℝ := fun s => mollifiedRHS m d ε B divB q x s with hHdef
  set c : ℝ := mollifySlice m ε q (x, τ₀) - barrier m M σ K τ₀ (x, τ₀) with hcdef
  have hHint : ∀ s ∈ I, IntervalIntegrable H volume τ₀ s :=
    fun s hs => intervalIntegrable_mollifiedRHS hI hIoc hB hq heq hε x hτ₀ hs
  have hshift : ∀ s ∈ I, mollifySlice m ε q (x, τ₀) + (∫ r in τ₀..s, H r)
      - barrier m M σ K τ₀ (x, s) = c + ∫ r in τ₀..s, (H r - σ * K) := by
    intro s hs
    rw [intervalIntegral.integral_sub (hHint s hs) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul, barrier_time_shift M σ K τ₀ s x, hcdef]
    ring
  have hc0 : c ≤ 0 := by
    have h := le_barrier_at_anchor M K τ₀ hσ x
    rw [hcdef]
    linarith only [h, hq0]
  have hhint : IntervalIntegrable (fun r => H r - σ * K) volume τ₀ τ :=
    (hHint τ hτ).sub intervalIntegrable_const
  rw [hshift τ hτ, comparisonProfile_add_intervalIntegral hhint c,
    comparisonProfile_eq_zero_of_nonpos hc0, zero_add]
  refine intervalIntegral.integral_congr_ae ?_
  have hxI : ∀ᵐ s, s ∈ I → mollifySlice m ε q (x, s) - mollifySlice m ε q (x, τ₀)
      = ∫ r in τ₀..s, H r := (ae_restrict_iff' hI.measurableSet).mp hx
  filter_upwards [hxI] with s hs hsmem
  have hsI : s ∈ I := hIoc.uIcc_subset hτ₀ hτ (uIoc_subset_uIcc hsmem)
  have hrep : c + ∫ r in τ₀..s, (H r - σ * K)
      = mollifySlice m ε q (x, s) - barrier m M σ K τ₀ (x, s) := by
    rw [← hshift s hsI]
    have h := hs hsI
    linarith only [h]
  rw [hrep]

/-- **The energy density at almost every later time, for almost every point**, is the time
integral from the reference time `τ₀` of `G'(q_ε - Ψ_σ)(H - ∂_τΨ_σ)`. -/
theorem ae_ae_comparisonProfile_eq_intervalIntegral {d : ℕ} {I : Set ℝ} (hI : IsOpen I)
    (hIoc : I.OrdConnected) {B : Vec m × ℝ → Vec m} {divB q : Vec m × ℝ → ℝ}
    (hB : IsAdmissibleDrift m I B divB) (hq : IsLocallyBoundedOn m I q)
    (heq : IsDistributionalDriftDiffusion m d I B divB q) {ε : ℝ} (hε : 0 < ε)
    {M σ K τ₀ : ℝ} (hσ : 0 ≤ σ) (hτ₀ : τ₀ ∈ I)
    (hq0 : ∀ x, mollifySlice m ε q (x, τ₀) ≤ M)
    (hA1 : ∀ᵐ x : Vec m, ∀ᵐ τ ∂(volume.restrict I),
      mollifySlice m ε q (x, τ) - mollifySlice m ε q (x, τ₀)
        = ∫ s in τ₀..τ, mollifiedRHS m d ε B divB q x s)
    (hA2 : ∀ᵐ τ ∂(volume.restrict I), ∀ᵐ x : Vec m,
      mollifySlice m ε q (x, τ) - mollifySlice m ε q (x, τ₀)
        = ∫ s in τ₀..τ, mollifiedRHS m d ε B divB q x s) :
    ∀ᵐ τ ∂(volume.restrict I), ∀ᵐ x : Vec m,
      comparisonProfile (mollifySlice m ε q (x, τ) - barrier m M σ K τ₀ (x, τ))
        = ∫ s in τ₀..τ, Real.smoothTransition
            (mollifySlice m ε q (x, s) - barrier m M σ K τ₀ (x, s))
            * (mollifiedRHS m d ε B divB q x s - σ * K) := by
  filter_upwards [hA2, ae_restrict_mem hI.measurableSet] with τ hτ hτI
  filter_upwards [hτ, hA1] with x hx1 hx2
  rw [← comparisonProfile_representative_eq hI hIoc hB hq heq hε hσ hτ₀ hτI x (hq0 x) hx2]
  congr 1
  linarith only [hx1]

end CIV
