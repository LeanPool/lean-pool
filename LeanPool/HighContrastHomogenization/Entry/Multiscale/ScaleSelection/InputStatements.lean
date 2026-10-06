/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.ScaleSelection.ParameterArithmetic

/-!
# High-contrast homogenization: Entry.Multiscale.ScaleSelection.InputStatements

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The two input statements and the law-side support

Groups B and C of the printed proof: nonnegativity of the synchronized log-determinant
loss, defined near `e.scale.selection.logdet.loss`, and — as a consequence proved by the cited
bridge support lemmas below — of `𝒫 + D` (profile plus determinant drift, defined
near `e.scale.selection.fluctuation.history`), the Skolemized short-bridge statement
(`p.successful.short.bridge`), the three source-constant monotonicity lemmas, and the
two input statements repeated at their exact types and applied.

Part of the proof of `p.scale.selection` (`HCPoly/Entry/Statements/ScaleSelection.lean`).
Conventions of the group: `q = 𝒬(𝔪)` is
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

open HCPolySupport.HighContrast (CoeffSpace adaptedMean aspectRatio blockScale)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ### Group B — support with the law -/

/-- `Δ̂^q_h(n) ≥ 0` when every increment starts at or above `j_*`
(near `e.scale.selection.logdet.loss`, via `Annealed.logDetLoss_nonneg`). -/
theorem synchronizedLogDetLoss_nonneg (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (h n : ℤ) (h0 : 0 ≤ h) (hn : (jStar : ℤ) + h ≤ n + 1) :
    0 ≤ synchCharge P (Geometry.explicitRoundedGrid jStar m) h n := by
  unfold synchCharge
  apply Finset.sum_nonneg
  intro a ha
  rw [Finset.mem_Icc] at ha
  exact HCPolySupport.HighContrast.Annealed.logDetLoss_nonneg d hd P γ E Ψ K S hstat hdag jStar
    hjStar m hm
    (a - h) a (by omega) (sub_le_self a h0)

theorem profile_add_determinantDrift_nonneg (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (S : CoeffSpace d → ℝ) (hstat : IsStationaryLaw P) (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (k n : ℤ) (hk : (jStar : ℤ) ≤ k) (hkn : k ≤ n) :
    0 ≤ profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n := by exact add_nonneg
        (Annealed.bridge_profile_nonneg d hd P γ E Ψ K S hstat hdag jStar hj m hm k n hk hkn)
        (Annealed.bridge_determinantDrift_nonneg d hd P γ E Ψ K S hstat hdag jStar hj m hm n)

/-- `p.successful.short.bridge`: the short-bridge statement with its `B₀(σ,L)` Skolemized. -/
theorem bridge_skolem (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ (L₀ : ℕ) (c₀ : ℝ), c₀ ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∃ Csrc : ℝ, 0 < Csrc ∧ ∃ B₀ : ℝ → ℕ → ℝ, BridgeBody d γ L₀ c₀ Csrc B₀ := by
  classical
  obtain ⟨L₀, c₀, hc₀, Csrc, hCsrc, hbr⟩ :=
    HCPolySupport.HighContrast.Entry.successful_short_bridge d hd γ hγ
  refine ⟨L₀, c₀, hc₀, Csrc, hCsrc,
    fun σ L =>
      if h : σ ∈ Set.Ioc (0 : ℝ) 1 ∧ (L₀ : ℤ) + ⌈Real.logb 3 σ⁻¹⌉ ≤ (L : ℤ) then
        Classical.choose (hbr σ h.1 L h.2)
      else 1,
    ?_⟩
  intro σ hσ L hL
  simp only [dite_eq_left (And.intro hσ hL)]
  exact Classical.choose_spec (hbr σ hσ L hL)

/-- Monotonicity in `Csrc`: a body at a smaller `Csrc` is a body at a larger one (`1 < K` gives
`log₃(2K) ≥ 0`). -/
theorem oneGridBody_mono_src (d : ℕ) (γ Csrc Csrc' C : ℝ) (hle : Csrc ≤ Csrc')
    (hbody : OneGridBody d γ Csrc C) : OneGridBody d γ Csrc' C := by
  intro P E Ψ K S hP hstat hunit hdag h hh L hL jStar hj hsrc
  exact hbody P E Ψ K S hP hstat hunit hdag h hh L hL jStar hj ((ceil_mul_le_ceil_mul _ _ _ hle
    (logb_two_mul_nonneg K hdag.one_lt_growthWitness)).trans hsrc)

theorem transportBody_mono_src (d : ℕ) (γ C Csrc Csrc' : ℝ) (hle : Csrc ≤ Csrc')
    (hbody : TransportBody d γ C Csrc) : TransportBody d γ C Csrc' := by
  intro ρ hρ δ hδ P E Ψ K S hP hstat hunit hdag jStar hj hsrc
  exact hbody ρ hρ δ hδ P E Ψ K S hP hstat hunit hdag jStar hj ((ceil_mul_le_ceil_mul _ _ _ hle
    (logb_two_mul_nonneg K hdag.one_lt_growthWitness)).trans hsrc)

theorem bridgeBody_mono_src (d : ℕ) (γ : ℝ) (L₀ : ℕ) (c₀ Csrc Csrc' : ℝ) (B₀ : ℝ → ℕ → ℝ)
    (hle : Csrc ≤ Csrc') (hbody : BridgeBody d γ L₀ c₀ Csrc B₀) :
    BridgeBody d γ L₀ c₀ Csrc' B₀ := by
  intro σ hσ L hL
  refine ⟨(hbody σ hσ L hL).1, ?_⟩
  intro P E Ψ K S hP hstat hunit hdag jStar hj hsrc
  exact (hbody σ hσ L hL).2 P E Ψ K S hP hstat hunit hdag jStar hj ((ceil_mul_le_ceil_mul _ _ _
    hle (logb_two_mul_nonneg K hdag.one_lt_growthWitness)).trans hsrc)

/-! ### Group C — the two input statements, repeated at their exact types -/

/-- The exact type of `p.fixed.geometry.one.grid.propagation`
(`HCPoly/Entry/Statements/OneGridPropagation.lean`), applied from
`Entry.fixed_geometry_one_grid_propagation_full` (`HCPoly/Entry/OneGridPropagation.lean`). -/
theorem one_grid_provider_input
    (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
    ∃ C : ℝ, 0 < C ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (S : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        IsStationaryLaw P →
        IsUnitRangeLaw P →
        CoarseEllipticityDagger P γ E Ψ K S →
        ∀ (h : ℕ), 2 * bigQ d γ ≤ h →
          ∀ L : ℤ, 1 ≤ L →
            ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
              ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
              ∀ (metric : Mat d), metric.PosDef →
                ∀ n m : ℤ, (jStar : ℤ) ≤ n → n ≤ m →
                  history P γ (Geometry.explicitRoundedGrid jStar metric) jStar m ≤
                      C * profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m ∧
                    (n + (h : ℤ) ≤ m →
                      profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (m + (h :
                        ℤ)) ≤
                        1 / 8 *
                            Real.exp ((bigQ d γ : ℝ) *
                              synchCharge P (Geometry.explicitRoundedGrid jStar metric)
                                (h : ℤ) m) *
                            profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                          C *
                            (Real.exp ((bigQ d γ : ℝ) *
                                synchCharge P (Geometry.explicitRoundedGrid jStar metric)
                                  (h : ℤ) m) - 1)) ∧
                    (n + (h : ℤ) ≤ m →
                      profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m ≤ 1 →
                        profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (m + L) ≤
                          C * (L : ℝ) *
                            (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                              Real.exp ((bigQ d γ : ℝ) *
                                detIncrement P (Geometry.explicitRoundedGrid jStar metric) m (m
                                  + L)) - 1)) ∧
                    (m = n →
                      history P γ (Geometry.explicitRoundedGrid jStar metric) jStar n ≤ 1 →
                        profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (n + L) ≤
                          C * (L : ℝ) *
                            (history P γ (Geometry.explicitRoundedGrid jStar metric) jStar n +
                              Real.exp ((bigQ d γ : ℝ) *
                                detIncrement P (Geometry.explicitRoundedGrid jStar metric) n (n
                                  + L)) - 1)) ∧
                    fluctuationHistory P γ (Geometry.explicitRoundedGrid jStar metric) jStar m +
                          meanHistory P γ (Geometry.explicitRoundedGrid jStar metric) (jStar :
                            ℤ) m +
                          determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m ≤
                        C * (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                          determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar
                            m) ∧
                    (n + (h : ℤ) ≤ m →
                      profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (m + (h :
                        ℤ)) +
                          determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar
                            (m + (h : ℤ)) ≤
                        1 / 8 *
                            Real.exp ((bigQ d γ : ℝ) *
                              synchCharge P (Geometry.explicitRoundedGrid jStar metric)
                                (h : ℤ) m) *
                            (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                              determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric)
                                jStar m) +
                          C *
                            (Real.exp ((bigQ d γ : ℝ) *
                                synchCharge P (Geometry.explicitRoundedGrid jStar metric)
                                  (h : ℤ) m) - 1)) ∧
                    (∀ m₀ : ℤ, (jStar : ℤ) + (h : ℤ) ≤ m₀ →
                      ∀ Ksteps : ℕ, 1 ≤ Ksteps →
                        ∑ k ∈ Finset.range Ksteps,
                            synchCharge P (Geometry.explicitRoundedGrid jStar metric) (h : ℤ)
                              (m₀ + (k : ℤ) * (h : ℤ)) ≤
                          (h : ℝ) *
                            detIncrement P (Geometry.explicitRoundedGrid jStar metric)
                              (m₀ + 1 - (h : ℤ)) (m₀ + (Ksteps : ℤ) * (h : ℤ))) ∧
                    ((m = n ∨ n + (h : ℤ) ≤ m) →
                      profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                          determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar
                            m ≤ 1 →
                        profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (m + L) +
                            determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric)
                              jStar (m + L) ≤
                          C * (L : ℝ) *
                            (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                              determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric)
                                jStar m +
                              Real.exp ((bigQ d γ : ℝ) *
                                detIncrement P (Geometry.explicitRoundedGrid jStar metric) m
                                  (m + L)) - 1)) :=
  Entry.fixed_geometry_one_grid_propagation_full d hd γ hγ

/-- The exact type of `p.two.grid.transport` (`HCPoly/Entry/Statements/TwoGridTransport.lean`),
applied from `Entry.two_grid_transport`
(`HCPoly/Entry/TwoGridTransport.lean`). -/
theorem two_grid_transport_provider_input
    (d : ℕ) (hd : 2 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∃ Csrc : ℝ, 0 < Csrc ∧
        ∀ ρ : ℝ, ρ ∈ Set.Ioc (0 : ℝ) 1 →
        ∀ δ : ℝ, δ ∈ Set.Icc (0 : ℝ) (1 / 4) →
          ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
            (S : CoeffSpace d → ℝ),
            IsProbabilityMeasure P →
            IsStationaryLaw P →
            IsUnitRangeLaw P →
            CoarseEllipticityDagger P γ E Ψ K S →
            ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
              ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
              ∀ (m mPlus : Mat d), m.PosDef → mPlus.PosDef →
                ∀ k n : ℤ, (jStar : ℤ) ≤ k → k ≤ n →
                  ∀ L : ℕ,
                    HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m) (n + 2 * (L
                      : ℤ)) ∪
                        HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar mPlus) (n +
                          (L : ℤ)) ⊆
                      HighContrast.centeredCube d (2 * (jStar : ℤ)) →
                    C * ((L : ℝ) +
                        Real.logb 3 ((2 + aspectRatio E) * (‖m‖ * ‖m⁻¹‖))) ≤
                      (n : ℝ) - (jStar : ℝ) →
                    projectiveDistance m mPlus ≤ 1 →
                    C + Real.logb 3 ρ⁻¹ ≤ (L : ℝ) →
                    profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k (n + 2 * (L : ℤ)) +
                        determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar
                          (n + 2 * (L : ℤ)) ≤
                      (3 : ℝ) ^ (-(1 / 2) * (1 - γ) * (L : ℝ)) * ρ →
                    BlockMatLoewnerLE
                        (blockScale (1 - δ)
                          (adaptedMean P (Geometry.explicitRoundedGrid jStar m) (n + 2 * (L : ℤ))))
                        (adaptedMean P (Geometry.explicitRoundedGrid jStar mPlus) (n + (L : ℤ))) →
                    BlockMatLoewnerLE
                        (adaptedMean P (Geometry.explicitRoundedGrid jStar mPlus) (n + (L : ℤ)))
                        (blockScale (1 + δ)
                          (adaptedMean P (Geometry.explicitRoundedGrid jStar m) (n + 2 * (L :
                            ℤ)))) →
                    profile P γ (Geometry.explicitRoundedGrid jStar mPlus) jStar (n + (L : ℤ))
                          (n + (L : ℤ)) +
                        determinantDrift P γ (Geometry.explicitRoundedGrid jStar mPlus) jStar
                          (n + (L : ℤ)) ≤
                      C * (δ + ρ) :=
  Entry.two_grid_transport d hd γ hγ

/-- The one-grid input as a `OneGridBody`, one term conversion of `one_grid_provider_input`. -/
theorem one_grid_body_input (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧ ∃ C : ℝ, 0 < C ∧ OneGridBody d γ Csrc C :=
  one_grid_provider_input d hd γ hγ

/-- The transport input as a `TransportBody`, one term conversion of
`two_grid_transport_provider_input`. -/
theorem two_grid_transport_body_input (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ Csrc : ℝ, 0 < Csrc ∧ TransportBody d γ C Csrc :=
  two_grid_transport_provider_input d hd γ hγ

end

end HCPolySupport.HighContrast.Multiscale
