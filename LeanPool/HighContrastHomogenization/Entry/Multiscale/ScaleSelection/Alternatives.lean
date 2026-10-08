/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.ScaleSelection.InputStatements

/-!
# High-contrast homogenization: Entry.Multiscale.ScaleSelection.Alternatives

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The startup, service and obstruction alternatives

Group D of the printed proof (`p.scale.selection`), first part:
alternative 1 in its start-up case `k = n` and its service case `k < n`, and the two
determinant-obstruction clauses of alternative 3, each stated at the literal selection
data so that its conclusion is the corresponding clause of `SelectionData.Selects`.

Part of the proof of the statement in
`HCPoly/Entry/Statements/ScaleSelection.lean`.  Conventions of the group: `q = 𝒬(𝔪)` is
`Geometry.explicitRoundedGrid jStar m`; the printed data are `h = 2Q`, `c = c₀`,
`L(ε,σ) = selectionLength L₀ σ` and
`B₀(ε,σ) = max 1 (max (B₀^bridge (√ε σ) L) (2 C_tr (L+1)))`; `√ε` is the printed
`ε^{1/2}`; the source lower scale `e.source.lower.scale` is carried wherever
`j_*` appears with the law, and no integrability, finiteness or
measurability premise is added anywhere.  Unused hypothesis binders of a statement are
underscore-prefixed; the tree compiles with `-DwarningAsError=true`.

The declaration text of this file is the closed skeleton's, copied unchanged; only this
header, the imports and the namespace frame are new.
-/

open HCPolySupport.HighContrast (CoeffSpace aspectRatio)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ### Group D — the five alternatives (`p.scale.selection`)

Every alternative lemma is stated at the concrete data `h = 2Q`, `L = selectionLength L₀ σ`,
`η = c₀ ε σ`, with the target constant `C` bounded below explicitly, so that its conclusion is
literally the corresponding clause of `SelectionData.Selects`. -/

/-- Alternative 1, `k = n` (`p.scale.selection`): startup from the one-grid fixed-span propagation
at span `h = 2Q`, together with the two output conditions of Step 3. -/
theorem startup_alternative (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (Csrc C₁ : ℝ) (hC₁ : 0 < C₁) (hone : OneGridBody d γ Csrc C₁)
    (C : ℝ) (hC : 2 * (bigQ d γ : ℝ) * C₁ ≤ C) (L₀ : ℕ) (ε σ B : ℝ)
    (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hP : IsProbabilityMeasure P) (hstat : IsStationaryLaw P) (hunit : IsUnitRangeLaw P)
    (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (hsrc : ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ))
    (m : Mat d) (hm : m.PosDef) (k n : ℤ) (hjk : (jStar : ℤ) ≤ k) (hkn : k ≤ n)
    (hecc : 1 / 2 * Real.log (‖m‖ * ‖m⁻¹‖) ≤
      ε / (selectionLength L₀ σ : ℝ) *
        ((k : ℝ) - (jStar : ℝ) - (⌈B * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ)))
    (hin1 : k = n →
      profile P γ (Geometry.explicitRoundedGrid jStar m) jStar n n +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n ≤ 1)
    (hk : k = n) :
    (k = n ∧
        profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k (n + ((2 * bigQ d γ : ℕ) : ℤ)) +
            determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar
              (n + ((2 * bigQ d γ : ℕ) : ℤ)) ≤
          C *
            (profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
              determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n +
              Real.exp ((bigQ d γ : ℝ) *
                detIncrement P (Geometry.explicitRoundedGrid jStar m) n
                  (n + ((2 * bigQ d γ : ℕ) : ℤ))) - 1)) ∧
      1 / 2 * Real.log (‖m‖ * ‖m⁻¹‖) ≤
        ε / (selectionLength L₀ σ : ℝ) *
          ((k : ℝ) - (jStar : ℝ) - (⌈B * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ)) ∧
      (k = n + ((2 * bigQ d γ : ℕ) : ℤ) →
        profile P γ (Geometry.explicitRoundedGrid jStar m) jStar
              (n + ((2 * bigQ d γ : ℕ) : ℤ)) (n + ((2 * bigQ d γ : ℕ) : ℤ)) +
            determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar
              (n + ((2 * bigQ d γ : ℕ) : ℤ)) ≤ 1) ∧
      (k < n + ((2 * bigQ d γ : ℕ) : ℤ) →
        k + ((2 * bigQ d γ : ℕ) : ℤ) ≤ n + ((2 * bigQ d γ : ℕ) : ℤ)) := by
  have hQpos : 0 < bigQ d γ := bigQ_pos d γ hγ
  have hstep_nat : 1 ≤ 2 * bigQ d γ := by
    exact Nat.succ_le_of_lt (Nat.mul_pos (by norm_num) hQpos)
  have hstep_int : 1 ≤ ((2 * bigQ d γ : ℕ) : ℤ) := by
    exact_mod_cast hstep_nat
  refine ⟨⟨hk, ?_⟩, hecc, ?_, ?_⟩
  · obtain ⟨_, _, _, _, _, _, _, hshort⟩ :=
      hone P E Ψ K S hP hstat hunit hdag (2 * bigQ d γ) le_rfl
        ((2 * bigQ d γ : ℕ) : ℤ) hstep_int jStar hj hsrc m hm k n hjk hkn
    have hstart :
        profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k
              (n + ((2 * bigQ d γ : ℕ) : ℤ)) +
            determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar
              (n + ((2 * bigQ d γ : ℕ) : ℤ)) ≤
          C₁ * (((2 * bigQ d γ : ℕ) : ℤ) : ℝ) *
            (profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
              determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n +
              Real.exp ((bigQ d γ : ℝ) *
                detIncrement P (Geometry.explicitRoundedGrid jStar m) n
                  (n + ((2 * bigQ d γ : ℕ) : ℤ))) - 1) := by
      simpa [hk] using hshort (Or.inl hk.symm) (by simpa [hk] using hin1 hk)
    have hbase :
        0 ≤ profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
          determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n :=
      add_nonneg
        (Annealed.bridge_profile_nonneg d hd P γ E Ψ K S hstat hdag jStar hj m hm k n hjk hkn)
        (Annealed.bridge_determinantDrift_nonneg d hd P γ E Ψ K S hstat hdag jStar hj m hm n)
    have hloss :
        0 ≤ detIncrement P (Geometry.explicitRoundedGrid jStar m) n
          (n + ((2 * bigQ d γ : ℕ) : ℤ)) :=
      HCPolySupport.HighContrast.Annealed.logDetLoss_nonneg d hd P γ E Ψ K S hstat hdag
        jStar hj m hm n (n + ((2 * bigQ d γ : ℕ) : ℤ)) (hjk.trans hkn) (by omega)
    have harg :
        0 ≤ (bigQ d γ : ℝ) *
          detIncrement P (Geometry.explicitRoundedGrid jStar m) n
            (n + ((2 * bigQ d γ : ℕ) : ℤ)) :=
      mul_nonneg (le_of_lt (bigQ_real_pos d γ hγ)) hloss
    have hexp :
        0 ≤ Real.exp ((bigQ d γ : ℝ) *
          detIncrement P (Geometry.explicitRoundedGrid jStar m) n
            (n + ((2 * bigQ d γ : ℕ) : ℤ))) - 1 := by
      linarith only [harg, Real.add_one_le_exp ((bigQ d γ : ℝ) *
        detIncrement P (Geometry.explicitRoundedGrid jStar m) n
          (n + ((2 * bigQ d γ : ℕ) : ℤ)))]
    have hbracket :
        0 ≤ profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
          determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n +
          Real.exp ((bigQ d γ : ℝ) *
            detIncrement P (Geometry.explicitRoundedGrid jStar m) n
              (n + ((2 * bigQ d γ : ℕ) : ℤ))) - 1 := by
      linarith only [hbase, hexp]
    have hcoef : C₁ * (((2 * bigQ d γ : ℕ) : ℤ) : ℝ) ≤ C := by
      by_cases hc : 0 < C₁
      · rw [Int.cast_natCast, Nat.cast_mul]
        calc
          C₁ * ((2 : ℝ) * ↑(bigQ d γ)) = 2 * ↑(bigQ d γ) * C₁ := by ring
          _ ≤ C := hC
      · exact False.elim (hc hC₁)
    exact hstart.trans (mul_le_mul_of_nonneg_right hcoef hbracket)
  · intro hbad
    have hpos : 0 < ((2 * bigQ d γ : ℕ) : ℤ) := by
      exact_mod_cast Nat.mul_pos (by norm_num : 0 < 2) hQpos
    omega
  · intro _
    omega

/-- Alternative 1, `k < n`, synchronized test passed (`p.scale.selection`): service from the
one-grid synchronized propagation, `Q Δ̂ ≤ Qdσ ≤ Qdε₀ ≤ log 2`, and Step 3. -/
theorem service_alternative (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (Csrc C₁ : ℝ) (hC₁ : 0 < C₁) (hone : OneGridBody d γ Csrc C₁)
    (C : ℝ) (hC : 2 * (bigQ d γ : ℝ) * C₁ ≤ C) (L₀ : ℕ) (c₀ ε σ B : ℝ)
    (hσ : σ ∈ Set.Ioc (0 : ℝ) ε)
    (hQε : (bigQ d γ : ℝ) * (d : ℝ) * ε ≤ Real.log 2)
    (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hP : IsProbabilityMeasure P) (hstat : IsStationaryLaw P) (hunit : IsUnitRangeLaw P)
    (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (hsrc : ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ))
    (m : Mat d) (hm : m.PosDef) (k n : ℤ) (hjk : (jStar : ℤ) ≤ k) (hkn : k ≤ n)
    (hecc : 1 / 2 * Real.log (‖m‖ * ‖m⁻¹‖) ≤
      ε / (selectionLength L₀ σ : ℝ) *
        ((k : ℝ) - (jStar : ℝ) - (⌈B * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ)))
    (hin2 : k < n → k + ((2 * bigQ d γ : ℕ) : ℤ) ≤ n)
    (hk : k < n)
    (hη : profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n > c₀ * ε * σ)
    (hsync : (d : ℝ)⁻¹ *
        synchCharge P (Geometry.explicitRoundedGrid jStar m) ((2 * bigQ d γ : ℕ) : ℤ) n ≤ σ) :
    (k < n ∧
        profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
            determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n > c₀ * ε * σ ∧
        (d : ℝ)⁻¹ *
            synchCharge P (Geometry.explicitRoundedGrid jStar m)
              ((2 * bigQ d γ : ℕ) : ℤ) n ≤ σ ∧
        profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k (n + ((2 * bigQ d γ : ℕ) : ℤ)) +
            determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar
              (n + ((2 * bigQ d γ : ℕ) : ℤ)) ≤
          1 / 4 *
              (profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
                determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n) +
            C *
              synchCharge P (Geometry.explicitRoundedGrid jStar m)
                ((2 * bigQ d γ : ℕ) : ℤ) n) ∧
      1 / 2 * Real.log (‖m‖ * ‖m⁻¹‖) ≤
        ε / (selectionLength L₀ σ : ℝ) *
          ((k : ℝ) - (jStar : ℝ) - (⌈B * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ)) ∧
      (k = n + ((2 * bigQ d γ : ℕ) : ℤ) →
        profile P γ (Geometry.explicitRoundedGrid jStar m) jStar
              (n + ((2 * bigQ d γ : ℕ) : ℤ)) (n + ((2 * bigQ d γ : ℕ) : ℤ)) +
            determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar
              (n + ((2 * bigQ d γ : ℕ) : ℤ)) ≤ 1) ∧
      (k < n + ((2 * bigQ d γ : ℕ) : ℤ) →
        k + ((2 * bigQ d γ : ℕ) : ℤ) ≤ n + ((2 * bigQ d γ : ℕ) : ℤ)) := by
  let : IsProbabilityMeasure P := hP
  have hQpos : 0 < bigQ d γ := bigQ_pos d γ hγ
  have hspan_pos : 0 < ((2 * bigQ d γ : ℕ) : ℤ) := by
    exact_mod_cast Nat.mul_pos (by norm_num : 0 < 2) hQpos
  have hspan_one : 1 ≤ ((2 * bigQ d γ : ℕ) : ℤ) := by omega
  have hspan_nonneg : 0 ≤ ((2 * bigQ d γ : ℕ) : ℤ) := le_of_lt hspan_pos
  have hng : k + ((2 * bigQ d γ : ℕ) : ℤ) ≤ n := hin2 hk
  refine ⟨⟨hk, hη, hsync, ?_⟩, hecc, ?_, ?_⟩
  · obtain ⟨_, _, _, _, _, hone_service, _, _⟩ :=
      hone P E Ψ K S hP hstat hunit hdag (2 * bigQ d γ) le_rfl
        ((2 * bigQ d γ : ℕ) : ℤ) hspan_one jStar hj hsrc m hm k n hjk hkn
    have hΔ0 :
        0 ≤ synchCharge P (Geometry.explicitRoundedGrid jStar m)
          ((2 * bigQ d γ : ℕ) : ℤ) n := by
      apply synchronizedLogDetLoss_nonneg d hd P γ E Ψ K S hstat hdag jStar hj m hm
      · exact hspan_nonneg
      · omega
    have hb0 :
        0 ≤ profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
          determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n := by
      exact profile_add_determinantDrift_nonneg d hd P γ E Ψ K S hstat hdag
        jStar hj m hm k n hjk hkn
    have hdpos : (0 : ℝ) < (d : ℝ) := by
      exact_mod_cast (by omega : 0 < d)
    have hΔσ :
        synchCharge P (Geometry.explicitRoundedGrid jStar m)
            ((2 * bigQ d γ : ℕ) : ℤ) n ≤
          (d : ℝ) * σ :=
      (inv_mul_le_iff₀ hdpos).mp hsync
    have hQnonneg : 0 ≤ (bigQ d γ : ℝ) :=
      le_of_lt (bigQ_real_pos d γ hγ)
    have hx0 :
        0 ≤ (bigQ d γ : ℝ) *
          synchCharge P (Geometry.explicitRoundedGrid jStar m)
            ((2 * bigQ d γ : ℕ) : ℤ) n :=
      mul_nonneg hQnonneg hΔ0
    have hxlog :
        (bigQ d γ : ℝ) *
            synchCharge P (Geometry.explicitRoundedGrid jStar m)
              ((2 * bigQ d γ : ℕ) : ℤ) n ≤
          Real.log 2 := by
      have hδε :
          synchCharge P (Geometry.explicitRoundedGrid jStar m)
              ((2 * bigQ d γ : ℕ) : ℤ) n ≤
            (d : ℝ) * ε :=
        hΔσ.trans (mul_le_mul_of_nonneg_left hσ.2 hdpos.le)
      calc
        (bigQ d γ : ℝ) *
            synchCharge P (Geometry.explicitRoundedGrid jStar m)
              ((2 * bigQ d γ : ℕ) : ℤ) n ≤
            (bigQ d γ : ℝ) * ((d : ℝ) * ε) :=
          mul_le_mul_of_nonneg_left hδε hQnonneg
        _ = (bigQ d γ : ℝ) * (d : ℝ) * ε := by ring
        _ ≤ Real.log 2 := hQε
    have hraw :=
      hone_service hng
    have hred :
        profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k
              (n + ((2 * bigQ d γ : ℕ) : ℤ)) +
            determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar
              (n + ((2 * bigQ d γ : ℕ) : ℤ)) ≤
          1 / 4 *
              (profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
                determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n) +
            2 * C₁ *
              ((bigQ d γ : ℝ) *
                synchCharge P (Geometry.explicitRoundedGrid jStar m)
                  ((2 * bigQ d γ : ℕ) : ℤ) n) :=
      service_reduction
        (profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k
              (n + ((2 * bigQ d γ : ℕ) : ℤ)) +
            determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar
              (n + ((2 * bigQ d γ : ℕ) : ℤ)))
        (profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
          determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n)
        ((bigQ d γ : ℝ) *
          synchCharge P (Geometry.explicitRoundedGrid jStar m)
            ((2 * bigQ d γ : ℕ) : ℤ) n)
        C₁ hb0 hC₁.le hx0 hxlog hraw
    have hterm :
        2 * C₁ *
              ((bigQ d γ : ℝ) *
                synchCharge P (Geometry.explicitRoundedGrid jStar m)
                  ((2 * bigQ d γ : ℕ) : ℤ) n) ≤
          C *
              synchCharge P (Geometry.explicitRoundedGrid jStar m)
                ((2 * bigQ d γ : ℕ) : ℤ) n := by
      calc
        2 * C₁ *
              ((bigQ d γ : ℝ) *
                synchCharge P (Geometry.explicitRoundedGrid jStar m)
                  ((2 * bigQ d γ : ℕ) : ℤ) n)
            = (2 * (bigQ d γ : ℝ) * C₁) *
                synchCharge P (Geometry.explicitRoundedGrid jStar m)
                  ((2 * bigQ d γ : ℕ) : ℤ) n := by ring
        _ ≤ C *
              synchCharge P (Geometry.explicitRoundedGrid jStar m)
                ((2 * bigQ d γ : ℕ) : ℤ) n :=
          mul_le_mul_of_nonneg_right hC hΔ0
    linarith only [hred, hterm]
  · intro hbad
    omega
  · intro _
    omega

/-- Alternative 3, synchronized obstruction (`p.scale.selection`): pure bookkeeping. -/
theorem obstruction_sync_alternative (d : ℕ) (γ : ℝ) (L₀ : ℕ) (c₀ ε σ B : ℝ)
    (P : Measure (CoeffSpace d)) (E : BlockMat d)
    (jStar : ℕ) (m : Mat d) (k n : ℤ)
    (hecc : 1 / 2 * Real.log (‖m‖ * ‖m⁻¹‖) ≤
      ε / (selectionLength L₀ σ : ℝ) *
        ((k : ℝ) - (jStar : ℝ) - (⌈B * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ)))
    (hk : k < n)
    (hη : profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n > c₀ * ε * σ)
    (hsync : (d : ℝ)⁻¹ *
        synchCharge P (Geometry.explicitRoundedGrid jStar m) ((2 * bigQ d γ : ℕ) : ℤ) n > σ) :
    (k < n ∧
        profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
            determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n > c₀ * ε * σ ∧
        (d : ℝ)⁻¹ *
            synchCharge P (Geometry.explicitRoundedGrid jStar m)
              ((2 * bigQ d γ : ℕ) : ℤ) n > σ) ∧
      1 / 2 * Real.log (‖m‖ * ‖m⁻¹‖) ≤
        ε / (selectionLength L₀ σ : ℝ) *
          ((k : ℝ) - (jStar : ℝ) - (⌈B * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ)) ∧
      (k = n + ((2 * bigQ d γ : ℕ) : ℤ) →
        profile P γ (Geometry.explicitRoundedGrid jStar m) jStar
              (n + ((2 * bigQ d γ : ℕ) : ℤ)) (n + ((2 * bigQ d γ : ℕ) : ℤ)) +
            determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar
              (n + ((2 * bigQ d γ : ℕ) : ℤ)) ≤ 1) ∧
      (k < n + ((2 * bigQ d γ : ℕ) : ℤ) →
        k + ((2 * bigQ d γ : ℕ) : ℤ) ≤ n + ((2 * bigQ d γ : ℕ) : ℤ)) := by
  refine ⟨⟨hk, hη, hsync⟩, hecc, ?_, ?_⟩
  · intro h
    have hpos := Int.natCast_nonneg (2 * bigQ d γ)
    omega
  · intro _
    linarith only [hk]

/-- Alternative 3, long obstruction (`p.scale.selection`): pure bookkeeping. -/
theorem obstruction_long_alternative (d : ℕ) (γ : ℝ) (L₀ : ℕ) (c₀ ε σ B : ℝ)
    (P : Measure (CoeffSpace d)) (E : BlockMat d)
    (jStar : ℕ) (m : Mat d) (k n : ℤ)
    (hecc : 1 / 2 * Real.log (‖m‖ * ‖m⁻¹‖) ≤
      ε / (selectionLength L₀ σ : ℝ) *
        ((k : ℝ) - (jStar : ℝ) - (⌈B * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ)))
    (hin2 : k < n → k + ((2 * bigQ d γ : ℕ) : ℤ) ≤ n)
    (hk : k < n)
    (hη : profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n ≤ c₀ * ε * σ)
    (hlong : (d : ℝ)⁻¹ *
        detIncrement P (Geometry.explicitRoundedGrid jStar m) n (n + 2 * (selectionLength L₀ σ :
          ℤ)) >
      ε * σ) :
    (k < n ∧
        profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
            determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n ≤ c₀ * ε * σ ∧
        (d : ℝ)⁻¹ *
            detIncrement P (Geometry.explicitRoundedGrid jStar m) n
              (n + 2 * (selectionLength L₀ σ : ℤ)) > ε * σ) ∧
      1 / 2 * Real.log (‖m‖ * ‖m⁻¹‖) ≤
        ε / (selectionLength L₀ σ : ℝ) *
          ((k : ℝ) - (jStar : ℝ) - (⌈B * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ)) ∧
      (k = n + 2 * (selectionLength L₀ σ : ℤ) →
        profile P γ (Geometry.explicitRoundedGrid jStar m) jStar
              (n + 2 * (selectionLength L₀ σ : ℤ)) (n + 2 * (selectionLength L₀ σ : ℤ)) +
            determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar
              (n + 2 * (selectionLength L₀ σ : ℤ)) ≤ 1) ∧
      (k < n + 2 * (selectionLength L₀ σ : ℤ) →
        k + ((2 * bigQ d γ : ℕ) : ℤ) ≤ n + 2 * (selectionLength L₀ σ : ℤ)) := by
  refine ⟨⟨hk, hη, hlong⟩, hecc, ?_, ?_⟩
  · intro _
    have : 0 ≤ (selectionLength L₀ σ : ℤ) := Int.natCast_nonneg (selectionLength L₀ σ)
    omega
  · intro _
    have : 0 ≤ (selectionLength L₀ σ : ℤ) := Int.natCast_nonneg (selectionLength L₀ σ)
    omega

end

end HCPolySupport.HighContrast.Multiscale
