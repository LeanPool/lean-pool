/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.Global.RunStop
public import LeanPool.HighContrastHomogenization.Entry.OneGridPropagation
public import LeanPool.HighContrastHomogenization.Entry.SuccessfulShortBridge

/-!
# High-contrast homogenization: Entry.Multiscale.Global.RunStepAny

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The `Selects` projections the run needs and the per-step case analysis

This module serves the scale-selection proposition `p.scale.selection`. The run quantifies
over a selection datum `S : SelectionData` with `S.Selects d γ`, and the module extracts from
`Selects` the three inequalities the run needs: `selects_two_bigQ_le_h` (`2 * bigQ d γ ≤ S.h`,
the generation gap consumed by `Entry.fixed_geometry_one_grid_propagation_full`),
`selects_one_le_L` (`1 ≤ S.L ε σ`, the scale gap needed by `long_step_decrease.hL`), and the
bridge sandwich at `δ = √ε σ`, `L = S.L ε σ` under the run's source threshold. It then proves
`run_step_any`, the five-way case analysis of `Selects` at a run state, which derives the
containment `hcont` and step `hstep` binders of `run_exists_stop`; the remaining assembly is
in `HCPoly.Entry.Multiscale.Global.RunAssembly`.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean aspectRatio matPow matSqrt)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section


/-! ## §1 The three facts the run needs, carried by `Selects` -/

/-- **C1 of `SelectionData.Selects`** (near `p.scale.selection`, `s.polynomial.entry.proof`): the
generation gap is at
least `2Q`, so `Entry.fixed_geometry_one_grid_propagation_full` applies at the step length. -/
theorem selects_two_bigQ_le_h (d : ℕ) (_hd : 2 ≤ d) (γ : ℝ) (_hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (S : SelectionData) (hS : S.Selects d γ) :
    2 * bigQ d γ ≤ S.h := hS.2.1

/-- **C2a of `SelectionData.Selects`** (`p.scale.selection`, `e.bridge.length.choice`): the scale
gap is a
length, as `long_step_decrease.hL` needs. -/
theorem selects_one_le_L (d : ℕ) (_hd : 2 ≤ d) (γ : ℝ) (_hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (S : SelectionData) (hS : S.Selects d γ) (ε σ : ℝ)
    (hε : ε ∈ Set.Ioc (0 : ℝ) S.eps0) (hσ : σ ∈ Set.Ioc (0 : ℝ) ε) :
    1 ≤ S.L ε σ := hS.2.2.1 ε σ hε hσ

/-! ## §2 The per-step case analysis -/

/-- `matPow 1` is the identity on positive definite matrices. -/
private theorem matPow_one_of_posDef {d : ℕ} {A : Mat d} (hA : A.PosDef) :
    matPow (1 : ℝ) A = A := by
  have h : matPow (1 : ℝ) A = cfc (fun x : ℝ => x) A := by
    unfold matPow
    simp only [Real.rpow_one]
  rw [h]
  simpa using! cfc_id ℝ A hA.isHermitian

/-- Inside the prescribed step the geometry update reaches the target exactly. -/
private theorem geometryUpdate_eq_of_le {d : ℕ} [NeZero d] {m mStar : Mat d}
    (hm : m.PosDef) (hStar : mStar.PosDef) {ε : ℝ} (_hε : 0 < ε)
    (hle : projectiveDistance m mStar ≤ ε) :
    geometryUpdate ε m mStar = mStar := by
  by_cases hEq : ProjectiveEq m mStar
  · exact Geometry.geometryUpdate_of_projectiveEq hEq ε
  · have hδ : 0 < projectiveDistance m mStar :=
      Geometry.projectiveDistance_pos_of_not_projectiveEq hm hStar hEq
    have hθ : min (ε / projectiveDistance m mStar) 1 = 1 :=
      min_eq_right ((one_le_div hδ).mpr hle)
    have hN : (normalizedMat m mStar).PosDef := Geometry.normalizedMat_posDef hm hStar
    have h1 : matSqrt m * matSqrt m⁻¹ = 1 := HCPolySupport.HighContrast.matSqrt_mul_matSqrt_inv hm
    have h2 : matSqrt m⁻¹ * matSqrt m = 1 := HCPolySupport.HighContrast.matSqrt_inv_mul_matSqrt hm
    rw [geometryUpdate, ite_eq_right hEq, hθ, matPow_one_of_posDef hN, normalizedMat]
    calc matSqrt m * (matSqrt m⁻¹ * mStar * matSqrt m⁻¹) * matSqrt m
        = matSqrt m * matSqrt m⁻¹ * mStar * (matSqrt m⁻¹ * matSqrt m) := by noncomm_ring
      _ = mStar := by rw [h1, h2, one_mul, mul_one]

private theorem run_span_propagation_monotone {d : ℕ} (hd : 2 ≤ d) (γ : ℝ)
    (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hce : CoarseEllipticityDagger P γ E Ψ K Src)
    (S : SelectionData) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (Cprop C : ℝ) (hCpropC : Cprop ≤ C)
    (hspan :
    ∀ Lz : ℤ, 1 ≤ Lz → ∀ metric : Mat d, metric.PosDef → ∀ n m : ℤ,
      (jStar : ℤ) ≤ n → n ≤ m → (m = n ∨ n + (S.h : ℤ) ≤ m) →
      profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
          determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m ≤ 1 →
      profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (m + Lz) +
          determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar (m + Lz) ≤
        Cprop * (Lz : ℝ) *
          (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
            determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m +
            (Real.exp ((bigQ d γ : ℝ) *
              detIncrement P (Geometry.explicitRoundedGrid jStar metric) m (m + Lz)) - 1))) :
    ∀ Lz : ℤ, 1 ≤ Lz → ∀ metric : Mat d, metric.PosDef → ∀ n m : ℤ,
      (jStar : ℤ) ≤ n → n ≤ m → (m = n ∨ n + (S.h : ℤ) ≤ m) →
      profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
          determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m ≤ 1 →
      profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (m + Lz) +
          determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar (m + Lz) ≤
        C * (Lz : ℝ) *
          (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
            determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m +
            (Real.exp ((bigQ d γ : ℝ) *
              detIncrement P (Geometry.explicitRoundedGrid jStar metric) m (m + Lz)) - 1)) := by
  intro Lz hLz metric hmetric n m hn hnm hguard hone
  have hraw := hspan Lz hLz metric hmetric n m hn hnm hguard hone
  have hx0 : 0 ≤ profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m :=
    profile_add_determinantDrift_nonneg d hd P γ E Ψ K Src hstat hce jStar hjStar
      metric hmetric n m hn hnm
  have hD0 : 0 ≤ detIncrement P (Geometry.explicitRoundedGrid jStar metric) m (m + Lz) :=
    Annealed.logDetLoss_nonneg d hd P γ E Ψ K Src hstat hce jStar hjStar metric hmetric
      m (m + Lz) (le_trans hn hnm) (by omega)
  have hexp : (1 : ℝ) ≤ Real.exp ((bigQ d γ : ℝ) *
      detIncrement P (Geometry.explicitRoundedGrid jStar metric) m (m + Lz)) :=
    Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) hD0)
  have hLzR : (0 : ℝ) ≤ (Lz : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) ≤ Lz)
  have hB0 : 0 ≤ profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m +
      Real.exp ((bigQ d γ : ℝ) *
        detIncrement P (Geometry.explicitRoundedGrid jStar metric) m (m + Lz)) - 1 := by
    linarith only [hx0, hexp]
  have hmono : Cprop * (Lz : ℝ) *
      (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m +
        Real.exp ((bigQ d γ : ℝ) *
          detIncrement P (Geometry.explicitRoundedGrid jStar metric) m (m + Lz)) - 1) ≤
      C * (Lz : ℝ) *
      (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m +
        Real.exp ((bigQ d γ : ℝ) *
          detIncrement P (Geometry.explicitRoundedGrid jStar metric) m (m + Lz)) - 1) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCpropC hLzR) hB0
  linarith only [hraw, hmono]

private theorem run_state_entry_containment {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (γ : ℝ) (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hce : CoarseEllipticityDagger P γ E Ψ K Src)
    (S : SelectionData) (ε σ B : ℝ) (H jStar : ℕ) (n₀ : ℤ) (J : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (hεpos : 0 < ε) (hε1 : ε ≤ 1)
    (hH4 : 4 ≤ H) (hh1 : 1 ≤ S.h) (hlog3 : 1 < Real.log 3)
    (hcontA : ∀ j : ℤ,
      j ≤ n₀ + (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * ((J : ℤ) + 2) →
      (j : ℝ) + (Real.logb 3 (2 * Real.sqrt (4 * (d : ℝ))) +
        ε * ((J : ℝ) + 1) / Real.log 3) ≤ 2 * (jStar : ℝ)) :
    ∀ st : RunState P γ S ε σ B E H jStar n₀, st.i ≤ J →
      HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar st.m)
            (st.n + 2 * (S.L ε σ : ℤ)) ∪
          HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
            (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
              (st.n + 2 * (S.L ε σ : ℤ)))))) (st.n + (S.L ε σ : ℤ)) ⊆
        HighContrast.centeredCube d (2 * (jStar : ℤ)) := by
  intro st hiJ
  have hmStar := Geometry.explicitCanonicalMetric_adaptedMean_posDef d hd P γ E Ψ K Src hstat hce
    jStar hjStar st.m st.hm (st.n + 2 * (S.L ε σ : ℤ))
  have hmPlusPD := Geometry.geometryUpdate_posDef st.hm hmStar ε
  have hstepd := Geometry.projectiveDistance_geometryUpdate_le st.hm hmStar hεpos
  have hprm := st.hpr
  rw [Geometry.projectiveDistance_one_eq_log_eccentricity st.hm] at hprm
  have hiR : ((st.i : ℝ)) ≤ (J : ℝ) := by exact_mod_cast hiJ
  have hslack : 0 ≤ ε * ((J : ℝ) - (st.i : ℝ)) := mul_nonneg hεpos.le (by linarith only [hiR])
  have htri := Geometry.projectiveDistance_triangle
    (Matrix.PosDef.one : (1 : Mat d).PosDef) st.hm hmPlusPD
  rw [Geometry.projectiveDistance_one_eq_log_eccentricity st.hm,
    Geometry.projectiveDistance_one_eq_log_eccentricity hmPlusPD] at htri
  have hDnn : (0 : ℤ) ≤ 2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ) := by positivity
  have hiZ : ((st.i : ℤ) + 1) ≤ ((J : ℤ) + 1) := by exact_mod_cast Nat.succ_le_succ hiJ
  have hgrow := mul_le_mul_of_nonneg_left hiZ hDnn
  have hgen1 : st.n ≤ n₀ + (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * ((J : ℤ) + 1) := by
    have h := st.hgen
    linarith only [h, hgrow]
  have hexp2 : (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * ((J : ℤ) + 2)
      = (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * ((J : ℤ) + 1) +
        (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) := by ring
  have hHz : (4 : ℤ) ≤ (H : ℤ) := by exact_mod_cast hH4
  have hhz : (1 : ℤ) ≤ (S.h : ℤ) := by exact_mod_cast hh1
  have hLzz : (0 : ℤ) ≤ (S.L ε σ : ℤ) := Int.natCast_nonneg _
  have hbudget : ∀ j : ℤ,
      j + 1 ≤ n₀ + (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * ((J : ℤ) + 2) →
      (j : ℝ) + (Real.logb 3 (2 * Real.sqrt (4 * (d : ℝ))) +
        ε * ((J : ℝ) + 2) / Real.log 3) ≤ 2 * (jStar : ℝ) := by
    intro j hj
    have h := hcontA (j + 1) hj
    have hc1 : (((j + 1 : ℤ)) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
    rw [hc1] at h
    have hlog3pos : (0 : ℝ) < Real.log 3 := by linarith only [hlog3]
    have he1 : ε / Real.log 3 ≤ 1 := by rw [div_le_one hlog3pos]; linarith only [hε1, hlog3]
    have he2 : ε * ((J : ℝ) + 2) / Real.log 3
        = ε * ((J : ℝ) + 1) / Real.log 3 + ε / Real.log 3 := by
      field_simp; ring
    linarith only [h, he1, he2]
  exact run_entry_containment hd jStar hjStar st.m _ st.hm hmPlusPD
    (st.n + 2 * (S.L ε σ : ℤ)) (st.n + (S.L ε σ : ℤ)) (ε * ((J : ℝ) + 2))
    (by positivity) (by linarith only [hprm, hslack, hεpos])
      (by linarith only [htri, hprm, hstepd, hslack, hεpos])
    (hbudget _ (by linarith only [hgen1, hexp2, hHz, hhz]))
      (hbudget _ (by linarith only [hgen1, hexp2, hHz, hhz, hLzz]))

/-- **The five-way case analysis of `Selects` at a run state** — the `hcont` and `hstep`
binders of `run_exists_stop`, as one theorem.

Route. Fix a state `st` with `st.i ≤ J`.

* **Containment** (`hcont`): `run_entry_containment` at `m := st.m`, `mP := 𝔪₊`,
  `j := st.n + 2L`, `jP := st.n + L`, `e := ε * (J + 1)`; the two eccentricity premises come
  from `st.hecc` (and, for `𝔪₊`, from `st.hpr` through
  `Geometry.projectiveDistance_geometryUpdate_le`), and `hj`/`hjP` are `hcontA`, the
  `containment_arith` instance at its free real argument `d := 4d`, fed by `st.hgen`.
* **Step** (`hstep`): apply `hS` at `st.m`, `st.k`, `st.n`, with entry premises
  the source threshold at the `Selects` source constant, `st.hecc`,
  `st.hone`, `st.hgap` and the containment just built; then case-split on the five disjuncts:
  Alt-1 start-up is vacuous by `st.hlt`, Alt-1 service is `run_step_service`, Alt-2 with
  `𝔪₊ ≠ 𝔪⋆` is `run_step_change`, Alt-2 with `𝔪₊ = 𝔪⋆` is `run_step_failed_test` when the
  determinant test fails and the RIGHT disjunct (the stop) when it succeeds, Alt-3
  synchronized is `run_step_sync` and Alt-3 long is `run_step_long`. The propagation clauses
  `hprop1`/`hspan` of `run_step_sync`/`run_step_failed_test`/`run_step_long` come from
  `Entry.fixed_geometry_one_grid_propagation_full` under `hh`, and the bridge sandwiches
  `hbr₁`/`hbr₂` of `run_step_change`/`run_step_failed_test` from `Selects`' conjunct C3; both source
  thresholds are discharged by `hsrc`.

`Csrc` is existential because the `Selects`, propagation and bridge source constants are
Skolem constants of their own statements: the theorem chooses their maximum.

The existential `∃ Cbase` and the binder `Cbase ≤ C` are present because the `Selects`
transport constant and the one-grid propagation constant must both sit below the run's `C`;
neither follows from `1 ≤ C`, `(d : ℝ) ≤ C`. The `scales_arith` and `eccentricity_arith`
hypotheses are not assumed: they are unused by this conclusion, contradictory with the
`comparison_choice` binder at the same `C`, and needed only by `run_stop_output` at the output
constant. The stop disjunct is `RunStopData … Cbase`, which carries the Alternative-2 bridge
sandwich and output bound. -/
theorem run_step_any {d : ℕ} (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (S : SelectionData) (hS : S.Selects d γ)
    (hh : 2 * bigQ d γ ≤ S.h)
    (hL : ∀ ε σ : ℝ, ε ∈ Set.Ioc (0 : ℝ) S.eps0 → σ ∈ Set.Ioc (0 : ℝ) ε → 1 ≤ S.L ε σ) :
    ∃ Csrc : ℝ, 0 < Csrc ∧ ∃ Cbase : ℝ, 0 < Cbase ∧
      ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
        (Src : CoeffSpace d → ℝ),
        IsProbabilityMeasure P →
        IsStationaryLaw P →
        IsUnitRangeLaw P →
        CoarseEllipticityDagger P γ E Ψ K Src →
        ∀ ε σ B : ℝ, ε ∈ Set.Ioc (0 : ℝ) S.eps0 → σ ∈ Set.Ioc (0 : ℝ) ε → S.B0 ε σ ≤ B →
          ∀ H jStar : ℕ, max 4 S.h ≤ H → 2 * d ≤ 3 ^ jStar →
            (∀ C' : ℝ, 0 < C' → C' ≤ Csrc → ⌈C' * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ)) →
            ∀ n₀ : ℤ, (jStar : ℤ) + ⌈B * Real.logb 3 (2 + aspectRatio E)⌉ ≤ n₀ →
              ∀ Cinit : ℝ, 0 ≤ Cinit →
                n₀ ≤ (jStar : ℤ) + ⌈B * Real.logb 3 (2 + aspectRatio E)⌉ +
                  ⌈Cinit * Real.logb 3 (2 + aspectRatio E)⌉ →
              ∀ a c C w : ℝ, 1 ≤ C → (d : ℝ) ≤ C → Cbase ≤ C → 1 ≤ a → (d : ℝ) ≤ a →
                w = a * C / d →
                c = 1 / 2 * S.eta ε σ * Real.log (16 / 9) →
                -- `weight_choice_ge_d`, all three conjuncts
                4 * (bigQ d γ : ℝ) * max 1 C ≤ a * C / d →
                Real.log (1 + C * (S.h : ℝ)) + c ≤ a * ε / 2 →
                4 * (Real.log (1 + 2 * C * (S.L ε σ : ℝ)) + Real.log (1 + C * (H : ℝ)) + c) ≤
                  a * C * ε * σ →
                0 ≤ Real.log (1 + C * (H : ℝ)) →
                -- `comparison_choice` at `δ = √ε σ`
                1 / 2 * Real.log ((1 + Real.sqrt ε * σ) / (1 - Real.sqrt ε * σ)) +
                    2 * C * ((S.h : ℝ) + 2) * Real.log (1 + Real.sqrt ε * σ) ≤
                  min (ε / 2) (C * σ / 4) →
                ∀ J : ℕ,
                  -- `containment_arith` at its free real argument `d := 4d`
                  (∀ j : ℤ,
                      j ≤ n₀ + (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * ((J : ℤ) + 2) →
                      (j : ℝ) +
                          (Real.logb 3 (2 * Real.sqrt (4 * (d : ℝ))) +
                            ε * ((J : ℝ) + 1) / Real.log 3) ≤
                        2 * (jStar : ℝ)) →
                  (∀ st : RunState P γ S ε σ B E H jStar n₀, st.i ≤ J →
                      HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar st.m)
                            (st.n + 2 * (S.L ε σ : ℤ)) ∪
                          HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar
                            (geometryUpdate ε st.m
                            (explicitCanonicalMetric (adaptedMean P
                              (Geometry.explicitRoundedGrid jStar st.m)
                              (st.n + 2 * (S.L ε σ : ℤ)))))) (st.n + (S.L ε σ : ℤ)) ⊆
                        HighContrast.centeredCube d (2 * (jStar : ℤ))) ∧
                    (∀ st : RunState P γ S ε σ B E H jStar n₀, st.i ≤ J →
                      (∃ st' : RunState P γ S ε σ B E H jStar n₀, st'.i = st.i + 1 ∧
                          runGauge P γ jStar (S.eta ε σ) a w S.h st'.m st'.k st'.n -
                            runGauge P γ jStar (S.eta ε σ) a w S.h st.m st.k st.n ≤ -c) ∨
                        RunStopData P γ S ε σ B E H jStar n₀ Cbase st) := by
  classical
  have : NeZero d := ⟨by omega⟩
  obtain ⟨⟨Csel, hCsel, Cssrc, hCssrc, hsel, hbrC3⟩, -, -, -⟩ := hS
  obtain ⟨Cps, hCps, Cprop, hCprop, hprovider⟩ :=
    Entry.fixed_geometry_one_grid_propagation_full d hd γ hγ
  refine ⟨max Cssrc Cps, lt_max_of_lt_left hCssrc,
    max Csel Cprop, lt_max_of_lt_left hCsel, ?_⟩
  intro P E Ψ K Src hP hstat hunit hce ε σ B hε hσ hB H jStar hH hjStar hsrcAll
    n₀ hn₀ Cinit hCinit hn₀' a c C w hC hCd hCbase ha1 ha hw hcc hwq hwh hwL hlogH hcomp
    J hcontA
  let : IsProbabilityMeasure P := hP
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have hεpos : (0 : ℝ) < ε := hε.1
  have hσpos : (0 : ℝ) < σ := hσ.1
  have hε1 : ε ≤ 1 := le_trans hε.2 S.eps0_mem.2.le
  have hL1 : 1 ≤ S.L ε σ := hL ε σ hε hσ
  have hLR : (0 : ℝ) < (S.L ε σ : ℝ) := by
    have h1 : (1 : ℝ) ≤ (S.L ε σ : ℝ) := by exact_mod_cast hL1
    linarith only [h1]
  have hQ2 : 2 ≤ bigQ d γ := bigQ_two_le d γ hγ
  have hh1 : 1 ≤ S.h := by omega
  have hH4 : 4 ≤ H := le_trans (le_max_left 4 S.h) hH
  have hCselC : Csel ≤ C := le_trans (le_max_left _ _) hCbase
  have hCpropC : Cprop ≤ C := le_trans (le_max_right _ _) hCbase
  have hsrcS : ⌈Cssrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) :=
    hsrcAll Cssrc hCssrc (le_max_left _ _)
  have hsrcP : ⌈Cps * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) :=
    hsrcAll Cps hCps (le_max_right _ _)
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    have h9 := Real.exp_one_lt_d9
    have h3 : Real.exp 1 < 3 := by linarith only [h9]
    have h4 := Real.log_lt_log (Real.exp_pos 1) h3
    rwa [Real.log_exp] at h4
  -- the conjunct-8 span propagation, at the run's own constant `C`
  have hspanC : ∀ Lz : ℤ, 1 ≤ Lz → ∀ metric : Mat d, metric.PosDef → ∀ n m : ℤ,
      (jStar : ℤ) ≤ n → n ≤ m → (m = n ∨ n + (S.h : ℤ) ≤ m) →
      profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
          determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m ≤ 1 →
      profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (m + Lz) +
          determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar (m + Lz) ≤
        C * (Lz : ℝ) *
          (profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
            determinantDrift P γ (Geometry.explicitRoundedGrid jStar metric) jStar m +
            (Real.exp ((bigQ d γ : ℝ) *
              detIncrement P (Geometry.explicitRoundedGrid jStar metric) m (m + Lz)) - 1)) :=
    run_span_propagation_monotone hd γ P E Ψ K Src hstat hce S jStar hjStar Cprop C hCpropC
      (fun Lz hLz metric hmetric n m hn hnm hguard hone =>
        (hprovider P E Ψ K Src hP hstat hunit hce S.h hh Lz hLz jStar hjStar hsrcP
          metric hmetric n m hn hnm).2.2.2.2.2.2.2 hguard hone)
  -- (1) the containment clause
  have hcontFull : ∀ st : RunState P γ S ε σ B E H jStar n₀, st.i ≤ J →
      HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar st.m)
            (st.n + 2 * (S.L ε σ : ℤ)) ∪
          HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
            (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
              (st.n + 2 * (S.L ε σ : ℤ)))))) (st.n + (S.L ε σ : ℤ)) ⊆
        HighContrast.centeredCube d (2 * (jStar : ℤ)) :=
    run_state_entry_containment hd γ P E Ψ K Src hstat hce S ε σ B H jStar n₀ J
      hjStar hεpos hε1 hH4 hh1 hlog3 hcontA
  refine ⟨hcontFull, ?_⟩
  -- (2) the five-way step analysis
  intro st hiJ
  have hmStar := Geometry.explicitCanonicalMetric_adaptedMean_posDef d hd P γ E Ψ K Src hstat hce
    jStar hjStar st.m st.hm (st.n + 2 * (S.L ε σ : ℤ))
  have hmPlusPD := Geometry.geometryUpdate_posDef st.hm hmStar ε
  have hjn : (jStar : ℤ) ≤ st.n := le_trans st.hk st.hkn
  have hkh : st.k + (S.h : ℤ) ≤ st.n := st.hgap st.hlt
  have hsge : (jStar : ℤ) ≤ st.n + (S.L ε σ : ℤ) := by
    have h1 : (0 : ℤ) ≤ (S.L ε σ : ℤ) := Int.natCast_nonneg _
    omega
  have hdisj := hsel ε σ hε hσ B hB P E Ψ K Src hP hstat hunit hce jStar hjStar hsrcS
    st.m st.hm st.k st.n st.hk st.hkn st.hecc st.hone st.hgap (hcontFull st hiJ)
  rcases hdisj with h1 | h2 | h3 | h4 | h5
  · exact absurd h1.1.1 (ne_of_lt st.hlt)
  · -- Alternative 1, service
    obtain ⟨⟨hlt2, hbig2, hobst2, hprop2⟩, _hecc2, hone2, hgap2⟩ := h2
    have hDh0 : 0 ≤ synchCharge P (Geometry.explicitRoundedGrid jStar st.m) (S.h : ℤ) st.n :=
      synchronizedLogDetLoss_nonneg d hd P γ E Ψ K Src hstat hce jStar hjStar st.m st.hm
        (S.h : ℤ) st.n (Nat.cast_nonneg _) (by have h1 := st.hk; omega)
    obtain ⟨st', -, -, -, hi', hg'⟩ := run_step_service hd γ hγ P E Ψ K Src hP hstat hunit hce
      S ε σ B hε hσ H jStar hjStar n₀ a c C w hC ha hw hcc st st.hlt hbig2
      (by linarith only [hprop2, mul_le_mul_of_nonneg_right hCselC hDh0]) hone2 hgap2
    exact Or.inl ⟨st', hi', hg'⟩
  · -- Alternative 2, change of geometry
    obtain ⟨⟨hlt3, hsmall3, hlong3, houtP3⟩, heccP3, honeP3, hgapP3⟩ := h3
    have honeP := honeP3 rfl
    have hgapQ : st.k + 2 * (bigQ d γ : ℤ) ≤ st.n := by
      have h2 : 2 * ((bigQ d γ : ℕ) : ℤ) ≤ (S.h : ℤ) := by exact_mod_cast hh
      omega
    have hprojle : projectiveDistance st.m (geometryUpdate ε st.m
        (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
          (st.n + 2 * (S.L ε σ : ℤ))))) ≤ 1 :=
      le_trans (Geometry.projectiveDistance_geometryUpdate_le st.hm hmStar hεpos) hε1
    -- the smallness premise of C3 in its printed `(c+d)εσ` form (`p.scale.selection`)
    have hsmallBr : profile P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.k st.n +
          determinantDrift P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.n +
          detIncrement P (Geometry.explicitRoundedGrid jStar st.m) st.n
            (st.n + 2 * (S.L ε σ : ℤ)) ≤ (S.c + (d : ℝ)) * ε * σ := by
      have hD : detIncrement P (Geometry.explicitRoundedGrid jStar st.m) st.n
          (st.n + 2 * (S.L ε σ : ℤ)) ≤ (d : ℝ) * (ε * σ) := (inv_mul_le_iff₀ hdR).mp hlong3
      have h3' : profile P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.k st.n +
          determinantDrift P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.n ≤
          S.c * ε * σ := hsmall3
      have hexp : (S.c + (d : ℝ)) * ε * σ = S.c * ε * σ + (d : ℝ) * (ε * σ) := by ring
      rw [hexp]
      linarith only [hD, h3']
    obtain ⟨hbr₁, hbr₂⟩ := hbrC3 ε σ hε hσ B hB P E Ψ K Src hP hstat hunit hce jStar hjStar
      hsrcS st.m _ st.hm hmPlusPD st.k st.n st.hk st.hkn (hcontFull st hiJ) st.hecc hgapQ
      hprojle hsmallBr
    by_cases heq : geometryUpdate ε st.m
        (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
          (st.n + 2 * (S.L ε σ : ℤ)))) =
        explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
          (st.n + 2 * (S.L ε σ : ℤ)))
    · by_cases htest : (d : ℝ)⁻¹ *
          detIncrement P (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
            (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
              (st.n + 2 * (S.L ε σ : ℤ)))))) (st.n + (S.L ε σ : ℤ))
            (st.n + (S.L ε σ : ℤ) + (H : ℤ)) < σ
      · refine Or.inr ⟨st.hlt, hsmall3, heq, htest, hbr₁, hbr₂, ?_, honeP⟩
        have hσnn : (0 : ℝ) ≤ σ ^ ((1 - γ) / 8) := Real.rpow_nonneg hσpos.le _
        exact le_trans houtP3 (mul_le_mul_of_nonneg_right (le_max_left Csel Cprop) hσnn)
      · have hHz1 : (1 : ℤ) ≤ (H : ℤ) := by
          have : (4 : ℤ) ≤ (H : ℤ) := by exact_mod_cast hH4
          omega
        have hspanH := hspanC (H : ℤ) hHz1 _ hmPlusPD (st.n + (S.L ε σ : ℤ))
          (st.n + (S.L ε σ : ℤ)) hsge le_rfl (Or.inl rfl) honeP
        obtain ⟨st', -, -, -, hi', hg'⟩ := run_step_failed_test hd γ hγ P E Ψ K Src hP hstat
          hunit hce S ε σ B hε hσ H jStar hH hjStar n₀ Cssrc hsrcS a c C w hC ha1 ha hw hcc
          hL1 hwL (le_trans hcomp (min_le_right _ _)) st st.hlt hsmall3 heq hbr₁ hbr₂ honeP
          heccP3 htest hwq (by simpa using hspanH)
        exact Or.inl ⟨st', hi', hg'⟩
    · have hfar : ε < projectiveDistance st.m
          (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
            (st.n + 2 * (S.L ε σ : ℤ)))) := by
        by_contra hcon
        push Not at hcon
        exact heq (geometryUpdate_eq_of_le st.hm hmStar hεpos hcon)
      have hhz1 : (1 : ℤ) ≤ (S.h : ℤ) := by exact_mod_cast hh1
      have hspanh := hspanC (S.h : ℤ) hhz1 _ hmPlusPD (st.n + (S.L ε σ : ℤ))
        (st.n + (S.L ε σ : ℤ)) hsge le_rfl (Or.inl rfl) honeP
      have hmono : BlockMatLoewnerLE
          (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) (st.n + 2 * (S.L ε σ : ℤ)))
          (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) st.k) :=
        Annealed.adaptedMean_antitone d hd P γ E Ψ K Src hstat hce jStar hjStar st.m st.hm
          st.k (st.n + 2 * (S.L ε σ : ℤ)) st.hk
          (by have h1 := st.hkn; have h2 : (0 : ℤ) ≤ (S.L ε σ : ℤ) := Int.natCast_nonneg _;
              omega)
      obtain ⟨st', -, -, -, hi', hg'⟩ := run_step_change hd γ hγ P E Ψ K Src hP hstat hunit hce
        S ε σ B hε hσ H jStar hjStar n₀ a c C w hC hCd ha1 ha hw hcc hh1 hL1 hwh
        (le_trans hcomp (min_le_left _ _)) st st.hlt hsmall3 heq hfar hbr₁ hbr₂ hmono honeP
        heccP3 (by simpa using hspanh) hwq
      exact Or.inl ⟨st', hi', hg'⟩
  · -- Alternative 3, synchronized
    obtain ⟨⟨hlt4, hbig4, hobst4⟩, _hecc4, hone4, hgap4⟩ := h4
    obtain ⟨st', -, -, -, hi', hg'⟩ := run_step_sync hd γ hγ P E Ψ K Src hP hstat hunit hce
      S ε σ B hε hσ H jStar hjStar n₀ hh Cps hsrcP Cprop hCprop
      (fun metric hmetric n m hn hnm hgapnm =>
        (hprovider P E Ψ K Src hP hstat hunit hce S.h hh 1 le_rfl jStar hjStar hsrcP
          metric hmetric n m hn hnm).2.2.2.2.2.1 hgapnm)
      a c C w hC hCpropC ha hw hwq hcc st st.hlt hbig4 hobst4 hone4 hgap4
    exact Or.inl ⟨st', hi', hg'⟩
  · -- Alternative 3, long
    obtain ⟨⟨hlt5, hsmall5, hobst5⟩, _hecc5, hone5, hgap5⟩ := h5
    have hone1 : profile P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.k st.n +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.n ≤ 1 :=
      le_trans hsmall5 (selectionData_eta_le_one S ε σ hε hσ)
    have hLz1 : (1 : ℤ) ≤ 2 * (S.L ε σ : ℤ) := by
      have h1 : (1 : ℤ) ≤ (S.L ε σ : ℤ) := by exact_mod_cast hL1
      omega
    have hspanL := hspanC (2 * (S.L ε σ : ℤ)) hLz1 st.m st.hm st.k st.n st.hk st.hkn
      (Or.inr hkh) hone1
    obtain ⟨st', -, -, -, hi', hg'⟩ := run_step_long hd γ hγ P E Ψ K Src hP hstat hunit hce
      S ε σ B hε hσ H jStar hjStar n₀ hh hL1 a c C w hC ha1 ha hw hcc hwq hwL hlogH
      st st.hlt hsmall5 hobst5 (by simpa using hspanL) hone5 hgap5
    exact Or.inl ⟨st', hi', hg'⟩


end

end HCPolySupport.HighContrast.Multiscale
