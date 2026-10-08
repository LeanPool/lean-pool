/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.ScaleSelection.TransportAlternative

/-!
# High-contrast homogenization: Entry.ScaleSelection

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Scale selection

The type repeats the `p.scale.selection` statement
(`HCPoly/Entry/Statements/ScaleSelection.lean`, `p.scale.selection`): same binders, same binder
kinds and order, the same conclusion `∃ S : SelectionData, S.Selects d γ`, and no
additional hypothesis.

The five guarded alternatives are proved in `HCPoly/Entry/Multiscale/ScaleSelection/`, one printed
step per file; this file only chooses the selection data and the two outermost constants
`C(d,γ)` and `C_src(d,γ)` before the law, the geometry, `ε`, `σ` and `B`, as the statement
requires, and dispatches the five cases of `alternatives_exhaustive`.  It consumes the
two applications of `Entry.fixed_geometry_one_grid_propagation`
(`HCPoly/Entry/OneGridPropagation.lean`) and `Entry.two_grid_transport`
(`HCPoly/Entry/TwoGridTransport.lean`), together with
`Entry.successful_short_bridge`.
-/

open HCPolySupport.HighContrast (adaptedMean aspectRatio)
namespace HCPolySupport.HighContrast.Entry

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- **Proof of `p.scale.selection`**, repeating the type of
`HCPolySupport.HighContrast.scale_selection` (`HCPoly/Entry/Statements/ScaleSelection.lean`,
`p.scale.selection`)
byte for byte. Assembled from the five alternative lemmas with `h = 2Q`, `c = c₀`,
`L(ε,σ) = selectionLength L₀ σ`, `B₀(ε,σ) = max 1 (max (B₀^bridge (√ε σ) L) (2 C_tr (L+1)))`,
`C` above `2Q C₁` and `2 C_tr`, `Csrc := max Csrc₁ (max Csrc₂ Csrc₃)` of the three
immediately consumed source constants, and `ε₀` from `exists_eps0`. -/
theorem scale_selection
    (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ S : SelectionData, S.Selects d γ := by
  classical
  obtain ⟨Csrc₁, hCsrc₁, C₁, hC₁, hone₀⟩ := Multiscale.one_grid_body_input d hd γ hγ
  obtain ⟨Ctr, hCtr, Csrc₂, hCsrc₂, htr₀⟩ := Multiscale.two_grid_transport_body_input d hd γ hγ
  obtain ⟨L₀b, c₀, hc₀, Csrc₃, hCsrc₃, B₀b, hbr₀⟩ := Multiscale.bridge_skolem d hd γ hγ
  have hQ0 : (0 : ℝ) ≤ (bigQ d γ : ℝ) := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
  have hCtr0 : (0 : ℝ) ≤ Ctr := by linarith only [hCtr]
  have hCtrpos : (0 : ℝ) < Ctr := by linarith only [hCtr]
  set Csrc : ℝ := max Csrc₁ (max Csrc₂ Csrc₃) with hCsrcdef
  have hCsrc : 0 < Csrc := lt_of_lt_of_le hCsrc₁ (le_max_left _ _)
  have hone : Multiscale.OneGridBody d γ Csrc C₁ :=
    Multiscale.oneGridBody_mono_src d γ Csrc₁ Csrc C₁ (le_max_left _ _) hone₀
  have htr : Multiscale.TransportBody d γ Ctr Csrc :=
    Multiscale.transportBody_mono_src d γ Ctr Csrc₂ Csrc
      (le_trans (le_max_left _ _) (le_max_right _ _)) htr₀
  have hbrb : Multiscale.BridgeBody d γ L₀b c₀ Csrc B₀b :=
    Multiscale.bridgeBody_mono_src d γ L₀b c₀ Csrc₃ Csrc B₀b
      (le_trans (le_max_right _ _) (le_max_right _ _)) hbr₀
  set L₀ : ℕ := max L₀b (max ⌈Ctr⌉₊ 1) with hL₀def
  have hL₀ : 1 ≤ L₀ := le_trans (le_max_right ⌈Ctr⌉₊ 1) (le_max_right L₀b _)
  have hL₀b : L₀b ≤ L₀ := le_max_left _ _
  have hCtrL₀ : Ctr ≤ (L₀ : ℝ) := by
    refine le_trans (Nat.le_ceil Ctr) ?_
    exact_mod_cast le_trans (le_max_left ⌈Ctr⌉₊ 1) (le_max_right L₀b _)
  have hbr : Multiscale.BridgeBody d γ L₀ c₀ Csrc B₀b := by
    intro s hs L hL
    have hcast : ((L₀b : ℕ) : ℤ) ≤ ((L₀ : ℕ) : ℤ) := by exact_mod_cast hL₀b
    exact hbrb s hs L (by omega)
  set C : ℝ := max (2 * (bigQ d γ : ℝ) * C₁) (2 * Ctr) with hCdef
  have hCone : 2 * (bigQ d γ : ℝ) * C₁ ≤ C := le_max_left _ _
  have hCtwo : 2 * Ctr ≤ C := le_max_right _ _
  have hCpos : 0 < C := lt_of_lt_of_le (by linarith only [hCtrpos]) hCtwo
  have hbrack : (0 : ℝ) < 1 + 2 * (bigQ d γ : ℝ) * (d : ℝ) := by
    have h2Qd : 0 ≤ 2 * (bigQ d γ : ℝ) * (d : ℝ) :=
      mul_nonneg (mul_nonneg (by norm_num) hQ0) hd0
    linarith only [h2Qd]
  obtain ⟨ε₁, hε₁pos, _hε₁le, hsmall⟩ :=
    Multiscale.old_grid_smallness_arith (2 * C₁ * (1 + 2 * (bigQ d γ : ℝ) * (d : ℝ)))
      (mul_pos (by linarith only [hC₁]) hbrack) L₀ γ hγ
  obtain ⟨ε₀, hε₀mem, hε₀q, hε₀c, hε₀Q, hε₀C, hε₀1, hε₀L⟩ :=
    Multiscale.exists_eps0 d hd γ hγ C Ctr c₀ ε₁ L₀ hCpos hCtrpos hc₀ hε₁pos hL₀
  refine ⟨⟨2 * bigQ d γ, ε₀, c₀, fun _ s => Multiscale.selectionLength L₀ s,
      fun e s => max 1 (max (B₀b (Real.sqrt e * s) (Multiscale.selectionLength L₀ s))
        (2 * Ctr * ((Multiscale.selectionLength L₀ s : ℝ) + 1))),
      hε₀mem, hc₀, fun _ _ _ _ => le_max_left _ _⟩, ?_⟩
  refine ⟨⟨C, hCpos, Csrc, hCsrc, ?_, ?_⟩, le_rfl,
    fun _ s _ _ => Multiscale.one_le_selectionLength L₀ hL₀ s,
    ⟨L₀, fun e s he hs => Multiscale.selectionLength_bridge_condition L₀ e s
      ⟨he.1, le_trans he.2 hε₀mem.2.le⟩ hs⟩⟩
  focus
    intro ε σ hε hσ B hB P E Ψ K Src hP hstat hunit hdag jStar hj hsrc m hm k n hjk hkn
      hecc hin1 hin2 mStar mPlus hcont
    have hε0 : 0 < ε := hε.1
    have hεle : ε ≤ ε₀ := hε.2
    have hε4 : ε ∈ Set.Ioc (0 : ℝ) (1 / 4) := ⟨hε0, le_trans hεle hε₀q⟩
    have hεc : ε ≤ (c₀ / ((d : ℝ) + 1)) ^ 2 := le_trans hεle hε₀c
    have hεε₁ : ε ≤ ε₁ := le_trans hεle hε₀1
    have hQε : (bigQ d γ : ℝ) * (d : ℝ) * ε ≤ Real.log 2 :=
      le_trans (mul_le_mul_of_nonneg_left hεle (mul_nonneg hQ0 hd0)) hε₀Q
    have hCε : C * ε ^ ((1 - γ) / 8) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hε0.le hεle (by linarith only [hγ.2])) hCpos.le) hε₀C
    have hLε : 2 * Ctr * ε ≤ (L₀ : ℝ) * Real.log 3 :=
      le_trans (mul_le_mul_of_nonneg_left hεle (by linarith only [hCtrpos])) hε₀L
    have hBmax : max (1 : ℝ)
        (max (B₀b (Real.sqrt ε * σ) (Multiscale.selectionLength L₀ σ))
          (2 * Ctr * ((Multiscale.selectionLength L₀ σ : ℝ) + 1))) ≤ B := hB
    have hB1 : B₀b (Real.sqrt ε * σ) (Multiscale.selectionLength L₀ σ) ≤ B :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hBmax
    have hB2 : 2 * Ctr * ((Multiscale.selectionLength L₀ σ : ℝ) + 1) ≤ B :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hBmax
    have hecc2 : 1 / 2 * Real.log (‖m‖ * ‖m⁻¹‖) ≤
        ε / (Multiscale.selectionLength L₀ σ : ℝ) *
          ((k : ℝ) - (jStar : ℝ) - (⌈B * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ)) := hecc
    have hin1b : k = n →
        profile P γ (Geometry.explicitRoundedGrid jStar m) jStar n n +
          determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n ≤ 1 := hin1
    have hin2b : k < n → k + ((2 * bigQ d γ : ℕ) : ℤ) ≤ n := hin2
    have hcontb : HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m)
          (n + 2 * (Multiscale.selectionLength L₀ σ : ℤ)) ∪
        HighContrast.adaptedCell
          (Geometry.explicitRoundedGrid jStar
            (geometryUpdate ε m
              (explicitCanonicalMetric
                (adaptedMean P (Geometry.explicitRoundedGrid jStar m)
                  (n + 2 * (Multiscale.selectionLength L₀ σ : ℤ))))))
          (n + (Multiscale.selectionLength L₀ σ : ℤ)) ⊆
        HighContrast.centeredCube d (2 * (jStar : ℤ)) := hcont
    rcases Multiscale.alternatives_exhaustive k n hkn
        (profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
          determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n)
        (c₀ * ε * σ)
        ((d : ℝ)⁻¹ *
          synchCharge P (Geometry.explicitRoundedGrid jStar m) ((2 * bigQ d γ : ℕ) : ℤ) n)
        σ
        ((d : ℝ)⁻¹ *
          detIncrement P (Geometry.explicitRoundedGrid jStar m) n
            (n + 2 * (Multiscale.selectionLength L₀ σ : ℤ)))
        (ε * σ) with hk | ⟨hk, hη, hx⟩ | ⟨hk, hη, hy⟩ | ⟨hk, hη, hx⟩ | ⟨hk, hη, hy⟩
    · exact Or.inl (Multiscale.startup_alternative d hd γ hγ Csrc C₁ hC₁ hone C hCone L₀ ε σ B
        P E Ψ K Src hP hstat hunit hdag jStar hj hsrc m hm k n hjk hkn hecc2 hin1b hk)
    · exact Or.inr (Or.inl (Multiscale.service_alternative d hd γ hγ Csrc C₁ hC₁ hone C hCone
        L₀ c₀ ε σ B hσ hQε P E Ψ K Src hP hstat hunit hdag jStar hj hsrc m hm k n hjk hkn
        hecc2 hin2b hk hη hx))
    · exact Or.inr (Or.inr (Or.inl (Multiscale.transport_alternative d hd γ hγ Csrc C₁ hC₁ hone
        Ctr hCtr htr C hCtwo L₀ hL₀ hCtrL₀ c₀ hc₀ B₀b hbr ε₁ hsmall ε σ B hε4 hεc hεε₁ hQε hCε
        hLε hσ hB1 hB2 P E Ψ K Src hP hstat hunit hdag jStar hj hsrc m hm k n hjk hkn hecc2
        hin2b hcontb hk hη hy)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (Multiscale.obstruction_sync_alternative d γ L₀ c₀
        ε σ B P E jStar m k n hecc2 hk hη hx))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Multiscale.obstruction_long_alternative d γ L₀ c₀
        ε σ B P E jStar m k n hecc2 hin2b hk hη hy))))
  -- **C3 of the successor `Selects` (defect 85)**: the short bridge applied at the tolerance
  -- `δ = ε^{1/2}σ` with the chosen length unchanged (`p.scale.selection`), from the
  -- same `BridgeBody` input and the same four thresholds as `Multiscale.bridge_application`,
  -- but for an arbitrary comparison geometry `𝔪₊` with `d_pr(𝔪,𝔪₊) ≤ 1`.
  intro ε σ hε hσ B hB P E Ψ K Src hP hstat hunit hdag jStar hj hsrc m mPlus hm hmP k n
    hjk hkn hcont hecc hgapQ hproj hsmall
  let : NeZero d := ⟨by omega⟩
  let : IsProbabilityMeasure P := hP
  have hε0 : 0 < ε := hε.1
  have hε1 : ε ∈ Set.Ioc (0 : ℝ) 1 := ⟨hε0, le_trans hε.2 hε₀mem.2.le⟩
  have hεc2 : ε ≤ (c₀ / ((d : ℝ) + 1)) ^ 2 := le_trans hε.2 hε₀c
  have hσtol : Real.sqrt ε * σ ∈ Set.Ioc (0 : ℝ) 1 := Multiscale.bridge_tolerance_mem ε σ hε1 hσ
  have hlen : (L₀ : ℤ) + ⌈Real.logb 3 (Real.sqrt ε * σ)⁻¹⌉ ≤
      (Multiscale.selectionLength L₀ σ : ℤ) :=
    Multiscale.selectionLength_bridge_condition L₀ ε σ hε1 hσ
  obtain ⟨_, hbody⟩ := hbr (Real.sqrt ε * σ) hσtol (Multiscale.selectionLength L₀ σ) hlen
  have hBm : max (1 : ℝ)
      (max (B₀b (Real.sqrt ε * σ) (Multiscale.selectionLength L₀ σ))
        (2 * Ctr * ((Multiscale.selectionLength L₀ σ : ℝ) + 1))) ≤ B := hB
  have hBbr : B₀b (Real.sqrt ε * σ) (Multiscale.selectionLength L₀ σ) ≤ B :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hBm
  have hLpos : (0 : ℝ) < (Multiscale.selectionLength L₀ σ : ℝ) := by
    have h1 : 1 ≤ Multiscale.selectionLength L₀ σ := Multiscale.one_le_selectionLength L₀ hL₀ σ
    have h2 : (1 : ℝ) ≤ (Multiscale.selectionLength L₀ σ : ℝ) := by exact_mod_cast h1
    linarith only [h2]
  have hdR2 : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h2ε : 2 * ε ≤ c₀ := by
    have hden : (0 : ℝ) < (d : ℝ) + 1 := by linarith only [hdR2]
    have ht : c₀ / ((d : ℝ) + 1) * ((d : ℝ) + 1) = c₀ := div_mul_cancel₀ c₀ hden.ne'
    have ht0 : 0 ≤ c₀ / ((d : ℝ) + 1) := div_nonneg hc₀.1.le hden.le
    have h3t : 3 * (c₀ / ((d : ℝ) + 1)) ≤ c₀ := by nlinarith only [ht, ht0, hdR2]
    have hhalf : (c₀ / ((d : ℝ) + 1)) ^ 2 ≤ c₀ / 2 := by
      nlinarith only [h3t, ht0, hc₀.1, hc₀.2]
    linarith only [hεc2, hhalf]
  have heccBridge : Real.log (‖m‖ * ‖m⁻¹‖) ≤
      c₀ / (Multiscale.selectionLength L₀ σ : ℝ) *
        ((k : ℝ) - (jStar : ℝ) -
          (⌈B₀b (Real.sqrt ε * σ) (Multiscale.selectionLength L₀ σ) *
            Real.logb 3 (2 + aspectRatio E)⌉ : ℤ)) :=
    Multiscale.bridge_eccentricity_arith (Real.log (‖m‖ * ‖m⁻¹‖)) ε c₀
      (Multiscale.selectionLength L₀ σ : ℝ) (k : ℝ) (jStar : ℝ)
      (Real.logb 3 (2 + aspectRatio E))
      (B₀b (Real.sqrt ε * σ) (Multiscale.selectionLength L₀ σ)) B
      (Geometry.log_norm_mul_norm_inv_nonneg hm) hε0 h2ε hLpos
      (Multiscale.logb_two_add_aspectRatio_nonneg E) hBbr hecc
  have hsmallBr : profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n +
        detIncrement P (Geometry.explicitRoundedGrid jStar m) n
          (n + 2 * (Multiscale.selectionLength L₀ σ : ℤ)) ≤ c₀ * (Real.sqrt ε * σ) :=
    Multiscale.bridge_smallness_arith_combined d hd c₀ c₀ ε σ _ hc₀ hc₀ hε0 hεc2 hσ.1 hsmall
  exact hbody P E Ψ K Src hP hstat hunit hdag jStar hj hsrc m mPlus hm hmP k n hjk hkn hcont
    heccBridge hgapQ hproj hsmallBr

end

end HCPolySupport.HighContrast.Entry
