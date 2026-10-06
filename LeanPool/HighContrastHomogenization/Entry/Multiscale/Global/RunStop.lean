/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.Global.RunStepsChange
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedCellMeasurability

/-!
# High-contrast homogenization: Entry.Multiscale.Global.RunStop

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The stop of the run and the stopping argument

`run_stop_output` is the Alternative-2 stop (`𝔪₊ = 𝔪⋆`, the determinant test succeeds) and
extracts `SelectedOutput`; `run_exists_stop` runs the gauge down and produces a stopping
state. Both serve the global selection result `p.global.selection`. `run_exists_stop` takes
the per-step alternative `hstep` and the containment `hcont` as binders; they are discharged
by `run_step_any` in `HCPoly.Entry.Multiscale.Global.RunAssembly`.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean aspectRatio blockScale)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

/-- **The stop configuration of the run at a state**: the Alternative-2 stop data, i.e.
exactly the per-state package `run_stop_output` consumes (beyond the state's own fields and
the scalar binders).  Named because it occurs five times — in `run_step_any`'s conclusion, in
`run_exists_stop`'s step hypothesis and conclusion, and in the residue.

Besides the four clauses of the stop predicate (`k < n`, the smallness
`𝒫 + D ≤ η`, the fixed point `𝔪₊ = 𝔪⋆` and the determinant test), it carries the bridge
sandwich at the retained block and the Alternative-2 output bound at `(𝒬(𝔪₊), n + L)`.
Those four are produced in the Alternative-2 branch of `run_step_any` and are **not**
recoverable from the other four (Alternative 2 and Alternative-3-long are separated by a
guard on which the first four clauses say nothing), which is why they are part of the stop
data. -/
@[expose]
def RunStopData {d : ℕ} (P : Measure (CoeffSpace d)) (γ : ℝ) (S : SelectionData)
    (ε σ B : ℝ) (E : BlockMat d) (H jStar : ℕ) (n₀ : ℤ) (Cout : ℝ)
    (st : RunState P γ S ε σ B E H jStar n₀) : Prop :=
  st.k < st.n ∧
    profile P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.k st.n +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar st.m) jStar st.n ≤ S.eta ε σ ∧
    geometryUpdate ε st.m
        (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
          (st.n + 2 * (S.L ε σ : ℤ)))) =
      explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
        (st.n + 2 * (S.L ε σ : ℤ))) ∧
    (d : ℝ)⁻¹ * detIncrement P (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
      (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
        (st.n + 2 * (S.L ε σ : ℤ)))))) (st.n + (S.L ε σ : ℤ))
      (st.n + (S.L ε σ : ℤ) + (H : ℤ)) < σ ∧
    BlockMatLoewnerLE
      (blockScale (1 - Real.sqrt ε * σ)
        (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) (st.n + 2 * (S.L ε σ : ℤ))))
      (adaptedMean P (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
        (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
          (st.n + 2 * (S.L ε σ : ℤ)))))) (st.n + (S.L ε σ : ℤ))) ∧
    BlockMatLoewnerLE
      (adaptedMean P (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
        (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
          (st.n + 2 * (S.L ε σ : ℤ)))))) (st.n + (S.L ε σ : ℤ)))
      (blockScale (1 + Real.sqrt ε * σ)
        (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) (st.n + 2 * (S.L ε σ : ℤ)))) ∧
    profile P γ (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
          (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
            (st.n + 2 * (S.L ε σ : ℤ)))))) jStar
          (st.n + (S.L ε σ : ℤ)) (st.n + (S.L ε σ : ℤ)) +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
          (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
            (st.n + 2 * (S.L ε σ : ℤ)))))) jStar (st.n + (S.L ε σ : ℤ)) ≤
      Cout * σ ^ ((1 - γ) / 8) ∧
    profile P γ (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
          (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
            (st.n + 2 * (S.L ε σ : ℤ)))))) jStar
          (st.n + (S.L ε σ : ℤ)) (st.n + (S.L ε σ : ℤ)) +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
          (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
            (st.n + 2 * (S.L ε σ : ℤ)))))) jStar (st.n + (S.L ε σ : ℤ)) ≤ 1


/-- **Alternative 2, `𝔪₊ = 𝔪⋆`, the test succeeds — the stop**
(`p.global.selection`). Retain `F = 𝐀_{n+2L, q}`, `s = n+L`, `t = s+H`. The output
fields: symmetry/positivity of `F` from `Recurrence.isSymmetricBlockMat_adaptedMean` and
`run_adaptedMean_blockPosDef`; `s < t` and `t = s + H` from `1 ≤ H`; the two scale bounds
from `st.hgen`, `hn₀` and `scales_arith`; the containment of `adaptedCell QF t` from
`run_entry_containment`; the two Loewner bounds are the bridge sandwich `hbr₁`/`hbr₂`
transported along `heq` (`explicitCanonicalMetric F = 𝔪⋆ = 𝔪₊`, so `QF = q₊`); the determinant test
is `htest`; the profile bound is `run_output_profile` / `output_profile_bound` fed by the
Alternative-2 transport output `houtP` and `exp_sub_one_le_rpow`; the eccentricity output
`(‖𝔪‖‖𝔪⁻¹‖)^{1/2} ≤ (2+Π)^C` is `eccentricity_arith` applied to `st.hpr` + `hpr'`. -/
theorem run_stop_output {d : ℕ} (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (Src : CoeffSpace d → ℝ) (hP : IsProbabilityMeasure P) (hst : IsStationaryLaw P)
    (hur : IsUnitRangeLaw P) (hce : CoarseEllipticityDagger P γ E Ψ K Src)
    (S : SelectionData) (ε σ B : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) S.eps0)
    (hσ : σ ∈ Set.Ioc (0 : ℝ) ε) (H jStar : ℕ) (hH : max 4 S.h ≤ H)
    (hjStar : 2 * d ≤ 3 ^ jStar) (n₀ : ℤ)
    (hn₀ : (jStar : ℤ) + ⌈B * Real.logb 3 (2 + aspectRatio E)⌉ ≤ n₀)
    (Cinit : ℝ) (hn₀' : n₀ ≤ (jStar : ℤ) + ⌈B * Real.logb 3 (2 + aspectRatio E)⌉ +
      ⌈Cinit * Real.logb 3 (2 + aspectRatio E)⌉)
    (Csrc : ℝ) (hsrc : ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ))
    (Cout Cprof C : ℝ) (hCout : 0 < Cout) (hCprof : 0 < Cprof) (hC : 0 < C)
    (hL1 : 1 ≤ S.L ε σ) (J : ℕ)
    (st : RunState P γ S ε σ B E H jStar n₀) (hiJ : st.i ≤ J)
    (hscales : ⌈B * Real.logb 3 (2 + aspectRatio E)⌉ +
        ⌈Cinit * Real.logb 3 (2 + aspectRatio E)⌉ +
        (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * ((J : ℤ) + 2) + (S.L ε σ : ℤ) + (H : ℤ) ≤
      ⌈(B + C) * Real.logb 3 (2 + aspectRatio E)⌉)
    (hcont : HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
        (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
          (st.n + 2 * (S.L ε σ : ℤ)))))) (st.n + (S.L ε σ : ℤ) + (H : ℤ)) ⊆
      HighContrast.centeredCube d (2 * (jStar : ℤ)))
    (hecc' : (‖explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
          (st.n + 2 * (S.L ε σ : ℤ)))‖ *
        ‖(explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
          (st.n + 2 * (S.L ε σ : ℤ))))⁻¹‖) ^ ((1 : ℝ) / 2) ≤ (2 + aspectRatio E) ^ C)
    (heq : geometryUpdate ε st.m
        (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
          (st.n + 2 * (S.L ε σ : ℤ)))) =
      explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
        (st.n + 2 * (S.L ε σ : ℤ))))
    (hbr₁ : BlockMatLoewnerLE
      (blockScale (1 - Real.sqrt ε * σ)
        (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) (st.n + 2 * (S.L ε σ : ℤ))))
      (adaptedMean P (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
        (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
          (st.n + 2 * (S.L ε σ : ℤ)))))) (st.n + (S.L ε σ : ℤ))))
    (hbr₂ : BlockMatLoewnerLE
      (adaptedMean P (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
        (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
          (st.n + 2 * (S.L ε σ : ℤ)))))) (st.n + (S.L ε σ : ℤ)))
      (blockScale (1 + Real.sqrt ε * σ)
        (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) (st.n + 2 * (S.L ε σ : ℤ)))))
    (houtP : profile P γ (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
          (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
            (st.n + 2 * (S.L ε σ : ℤ)))))) jStar
          (st.n + (S.L ε σ : ℤ)) (st.n + (S.L ε σ : ℤ)) +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
          (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
            (st.n + 2 * (S.L ε σ : ℤ)))))) jStar (st.n + (S.L ε σ : ℤ)) ≤
      Cout * σ ^ ((1 - γ) / 8))
    (honeP : profile P γ (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
          (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
            (st.n + 2 * (S.L ε σ : ℤ)))))) jStar
          (st.n + (S.L ε σ : ℤ)) (st.n + (S.L ε σ : ℤ)) +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
          (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
            (st.n + 2 * (S.L ε σ : ℤ)))))) jStar (st.n + (S.L ε σ : ℤ)) ≤ 1)
    (hprof : ∀ (m : Mat d), m.PosDef → ∀ s : ℤ, (jStar : ℤ) ≤ s →
      profile P γ (Geometry.explicitRoundedGrid jStar m) jStar s s +
          determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar s ≤
        Cout * σ ^ ((1 - γ) / 8) →
      profile P γ (Geometry.explicitRoundedGrid jStar m) jStar s s +
          determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar s ≤ 1 →
      (d : ℝ)⁻¹ * detIncrement P (Geometry.explicitRoundedGrid jStar m) s (s + H) < σ →
      max (max (profile P γ (Geometry.explicitRoundedGrid jStar m) jStar s s)
            (profile P γ (Geometry.explicitRoundedGrid jStar m) jStar s (s + H)))
          (profile P γ (Geometry.explicitRoundedGrid jStar m) jStar (s + H) (s + H)) +
          determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar s +
          determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar (s + H) ≤
        Cprof * σ ^ ((1 - γ) / 8))
    (htest : (d : ℝ)⁻¹ *
      detIncrement P (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
        (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
          (st.n + 2 * (S.L ε σ : ℤ)))))) (st.n + (S.L ε σ : ℤ))
        (st.n + (S.L ε σ : ℤ) + (H : ℤ)) < σ) :
    SelectedOutput P γ ε σ Cprof C E H jStar B := by
  classical
  let : NeZero d := ⟨by omega⟩
  have _ := hγ
  have _ := hσ
  have _ := hn₀
  have _ := hsrc
  have _ := hCout
  have _ := hCprof
  have _ := hC
  have _ := hur
  -- The retained output block `F = 𝐀_{n+2L, 𝒬(𝔪)}` and its metric `𝔪⋆ = explicitCanonicalMetric F`.
  have hFsym : IsSymmetricBlockMat
      (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) (st.n + 2 * (S.L ε σ : ℤ))) :=
    Recurrence.isSymmetricBlockMat_adaptedMean P _ _
  have hFpos : Book.Ch02.BlockPosDef
      (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) (st.n + 2 * (S.L ε σ : ℤ))) :=
    run_adaptedMean_blockPosDef hd P γ E Ψ K Src hP hst hce jStar hjStar st.m st.hm _
  have hStarPD : (explicitCanonicalMetric
      (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) (st.n + 2 * (S.L ε σ :
        ℤ)))).PosDef :=
    explicitCanonicalMetric_posDef _ hFsym hFpos
  have hPlusPD : (geometryUpdate ε st.m (explicitCanonicalMetric
      (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) (st.n + 2 * (S.L ε σ :
        ℤ))))).PosDef := by
    rw [heq]; exact hStarPD
  -- Scalar bookkeeping.
  have hH4 : 4 ≤ H := le_trans (le_max_left 4 S.h) hH
  have hLZ : (1 : ℤ) ≤ (S.L ε σ : ℤ) := by exact_mod_cast hL1
  have hjStar0 : (0 : ℤ) ≤ (jStar : ℤ) := Int.natCast_nonneg _
  have hsge : (jStar : ℤ) ≤ st.n + (S.L ε σ : ℤ) := by
    have h1 := st.hk
    have h2 := st.hkn
    linarith only [h1, h2, hLZ]
  -- The eccentricity clause forces `j_* + ⌈B log₃(2+Π)⌉ ≤ k`.
  have hεpos : (0 : ℝ) < ε := hε.1
  have hLR : (0 : ℝ) < (S.L ε σ : ℝ) := by
    have : (1 : ℝ) ≤ (S.L ε σ : ℝ) := by exact_mod_cast hL1
    linarith only [this]
  have hratio : (0 : ℝ) < ε / (S.L ε σ : ℝ) := div_pos hεpos hLR
  have hlogm : (0 : ℝ) ≤ 1 / 2 * Real.log (‖st.m‖ * ‖st.m⁻¹‖) := by
    have h := Real.log_nonneg (Geometry.one_le_norm_mul_norm_inv st.hm)
    linarith only [h]
  have hX : (0 : ℝ) ≤ (st.k : ℝ) - (jStar : ℝ) -
      ((⌈B * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ) : ℝ) := by
    have h0 := le_trans hlogm st.hecc
    by_contra hcon
    push Not at hcon
    have hneg := mul_neg_of_pos_of_neg hratio hcon
    linarith only [h0, hneg, hlogm]
  have hkge : (jStar : ℤ) + ⌈B * Real.logb 3 (2 + aspectRatio E)⌉ ≤ st.k := by
    have hR : (((jStar : ℤ) + ⌈B * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ) : ℝ) ≤ ((st.k : ℤ) : ℝ)
      := by
      push_cast
      linarith only [hX]
    exact_mod_cast hR
  -- The upper scale bound.
  have hstepnn : (0 : ℤ) ≤ 2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ) := by omega
  have hiJZ : ((st.i : ℤ) + 1) ≤ ((J : ℤ) + 2) := by
    have : (st.i : ℤ) ≤ (J : ℤ) := by exact_mod_cast hiJ
    linarith only [this]
  have hmul : (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * ((st.i : ℤ) + 1) ≤
      (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * ((J : ℤ) + 2) :=
    mul_le_mul_of_nonneg_left hiJZ hstepnn
  have hgen := st.hgen
  have hkn := st.hkn
  -- The profile bound at the retained metric.
  have hprofile := hprof _ hPlusPD (st.n + (S.L ε σ : ℤ)) hsge houtP honeP htest
  refine ⟨adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) (st.n + 2 * (S.L ε σ : ℤ)),
    st.n + (S.L ε σ : ℤ), st.n + (S.L ε σ : ℤ) + (H : ℤ),
    hFsym, hFpos, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hecc'⟩
  · have hHZ : (4 : ℤ) ≤ (H : ℤ) := by exact_mod_cast hH4
    linarith only [hHZ]
  · linarith only [hkge, hkn, hLZ]
  · linarith only [hgen, hn₀', hmul, hscales]
  · rw [← heq]; exact hcont
  · rw [← heq]; exact hbr₁
  · rw [← heq]; exact hbr₂
  · rw [← heq]; exact htest
  · rw [← heq]; exact hprofile

/-! ## Generic finite-run scaffolding

An abstract state space with an index, a gauge and a stop predicate.  The run is built by
`Nat.rec` with classical choice on the successor supplied by the step disjunction, and the
stopping index is extracted with `exists_stop_of_potential` (`FiniteRun.lean`) at
`charge = 0`, `Bud = 0`. -/

open Classical in
@[expose]
public def runSucc {α : Type*} (idx : α → ℕ) (G : α → ℝ) (c : ℝ) (x : α) : α :=
  if h : ∃ y : α, idx y = idx x + 1 ∧ G y - G x ≤ -c then h.choose else x

@[expose]
public def runIter {α : Type*} (idx : α → ℕ) (G : α → ℝ) (c : ℝ) (x₀ : α) : ℕ → α :=
  fun i => Nat.rec x₀ (fun _ x => runSucc idx G c x) i

private theorem runSucc_spec {α : Type*} (idx : α → ℕ) (G : α → ℝ) (c : ℝ) (x : α)
    (h : ∃ y : α, idx y = idx x + 1 ∧ G y - G x ≤ -c) :
    idx (runSucc idx G c x) = idx x + 1 ∧ G (runSucc idx G c x) - G x ≤ -c := by
  have heq : runSucc idx G c x = h.choose := by
    unfold runSucc
    exact dite_eq_left h
  rw [heq]
  exact h.choose_spec

/-- The abstract stopping argument: a nonnegative gauge, at most `c * J` at the initial
state, decreasing by `c` at every non-stopping state of index at most `J`, reaches a
stopping state of index at most `J`. -/
private theorem run_exists_stop_abstract {α : Type*} (idx : α → ℕ) (G : α → ℝ)
    (Stp : α → Prop) (c : ℝ) (hc : 0 < c) (J : ℕ) (x₀ : α) (hx₀ : idx x₀ = 0)
    (hnn : ∀ x, 0 ≤ G x) (hbnd : G x₀ ≤ c * (J : ℝ))
    (hstep : ∀ x, idx x ≤ J →
      (∃ y : α, idx y = idx x + 1 ∧ G y - G x ≤ -c) ∨ Stp x) :
    ∃ x : α, idx x ≤ J ∧ Stp x := by
  classical
  have hRs : ∀ i : ℕ,
      runIter idx G c x₀ (i + 1) = runSucc idx G c (runIter idx G c x₀ i) := fun _ => rfl
  have hidx : ∀ i : ℕ,
      (∀ j : ℕ, j < i → ¬ (Stp (runIter idx G c x₀ j) ∨ J < j)) →
      idx (runIter idx G c x₀ i) = i := by
    intro i
    induction i with
    | zero => intro _; exact hx₀
    | succ n ih =>
      intro hno
      have hn : idx (runIter idx G c x₀ n) = n := ih (fun j hj => hno j (by omega))
      have hnos : ¬ (Stp (runIter idx G c x₀ n) ∨ J < n) := hno n (by omega)
      have hnJ : n ≤ J := by
        by_contra hcon
        exact hnos (Or.inr (by omega))
      have hns : ¬ Stp (runIter idx G c x₀ n) := fun hs => hnos (Or.inl hs)
      rcases hstep (runIter idx G c x₀ n) (by rw [hn]; exact hnJ) with hex | hs
      · rw [hRs n, (runSucc_spec idx G c _ hex).1, hn]
      · exact absurd hs hns
  have hdec : ∀ i : ℕ,
      (∀ j : ℕ, j ≤ i → ¬ (Stp (runIter idx G c x₀ j) ∨ J < j)) →
      G (runIter idx G c x₀ (i + 1)) - G (runIter idx G c x₀ i) ≤ -c + (0 : ℝ) := by
    intro i hno
    have hi : idx (runIter idx G c x₀ i) = i := hidx i (fun j hj => hno j (by omega))
    have hnos : ¬ (Stp (runIter idx G c x₀ i) ∨ J < i) := hno i (le_refl i)
    have hiJ : i ≤ J := by
      by_contra hcon
      exact hnos (Or.inr (by omega))
    have hns : ¬ Stp (runIter idx G c x₀ i) := fun hs => hnos (Or.inl hs)
    rcases hstep (runIter idx G c x₀ i) (by rw [hi]; exact hiJ) with hex | hs
    · have hd2 := (runSucc_spec idx G c _ hex).2
      rw [hRs i]
      linarith only [hd2]
    · exact absurd hs hns
  obtain ⟨i, hile, hstopi⟩ :=
    exists_stop_of_potential (fun i => G (runIter idx G c x₀ i)) (fun _ => (0 : ℝ))
      (fun i => Stp (runIter idx G c x₀ i) ∨ J < i) c 0 hc (fun i => hnn _) hdec
      (by intro M _; simp)
  have hceil : ⌈(G (runIter idx G c x₀ 0) + 0) / c⌉₊ ≤ J := by
    have h0 : G (runIter idx G c x₀ 0) = G x₀ := rfl
    rw [h0]
    refine Nat.ceil_le.mpr ?_
    rw [div_le_iff₀ hc]
    linarith only [hbnd]
  have hiJ : i ≤ J := le_trans hile hceil
  have hex2 : ∃ i : ℕ, Stp (runIter idx G c x₀ i) ∨ J < i := ⟨i, hstopi⟩
  have hfle : Nat.find hex2 ≤ J := le_trans (Nat.find_le hstopi) hiJ
  refine ⟨runIter idx G c x₀ (Nat.find hex2), ?_, ?_⟩
  · rw [hidx (Nat.find hex2) (fun j hj => Nat.find_min hex2 hj)]
    exact hfle
  · rcases Nat.find_spec hex2 with hs | hs
    · exact hs
    · exact absurd hs (by omega)

/-! ## The run and its stopping step -/

/-- **The run and its stopping step** (`p.global.selection`). Build
`run : ℕ → RunState …` by `Nat.rec` (classical choice) from `run_initial`: at each step,
apply `hS` at `(run i).m, (run i).k, (run i).n` — its premises are the source threshold
`⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ)`, `(run i).hecc`, `(run i).hone`, `(run i).hgap`,
and `run_entry_containment` fed by
`(run i).hpr`, `(run i).hgen`, `hcont` — and case-split on the five disjuncts, using
`run_step_service`, `run_step_change`, `run_step_failed_test`, `run_step_sync`,
`run_step_long`, with `stop i` the Alternative-2 case `𝔪₊ = 𝔪⋆` whose test succeeds. Then
`exists_stop_of_potential` (`FiniteRun.lean`) with
`Φ i := runGauge … (run i).m (run i).k (run i).n`, `charge ≡ 0`, `Bud := 0`, `hΦ` from
`run_potential_nonneg` + `run_reserve_rounded_nonneg`, `hstep` from the five step cases; the
index bound `⌈(Φ 0 + 0)/c⌉₊ ≤ J` comes from `run_initial` + `run_initial_reserve` and the
choice of `J := ⌈C₁ · log₃(2+Π)⌉₊`. -/
theorem run_exists_stop {d : ℕ} (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (Src : CoeffSpace d → ℝ) (hP : IsProbabilityMeasure P) (hst : IsStationaryLaw P)
    (hur : IsUnitRangeLaw P) (hce : CoarseEllipticityDagger P γ E Ψ K Src)
    (S : SelectionData) (hS : S.Selects d γ) (ε σ B : ℝ)
    (hε : ε ∈ Set.Ioc (0 : ℝ) S.eps0) (hσ : σ ∈ Set.Ioc (0 : ℝ) ε) (hB : S.B0 ε σ ≤ B)
    (H jStar : ℕ) (hH : max 4 S.h ≤ H) (hjStar : 2 * d ≤ 3 ^ jStar)
    (hh : 2 * bigQ d γ ≤ S.h) (hL1 : 1 ≤ S.L ε σ) (n₀ : ℤ)
    (hn₀ : (jStar : ℤ) + ⌈B * Real.logb 3 (2 + aspectRatio E)⌉ ≤ n₀)
    (a c C Cout w : ℝ) (hC : 1 ≤ C) (hc : c = 1 / 2 * S.eta ε σ * Real.log (16 / 9))
    (hcpos : 0 < c) (hw : w = a * C / d) (ha : (d : ℝ) ≤ a) (ha1 : 1 ≤ a) (J : ℕ)
    (st₀ : RunState P γ S ε σ B E H jStar n₀)
    (hst₀ : st₀.i = 0)
    (hbound : runGauge P γ jStar (S.eta ε σ) a w S.h st₀.m st₀.k st₀.n ≤ c * (J : ℝ))
    (hcont : ∀ st : RunState P γ S ε σ B E H jStar n₀, st.i ≤ J →
      HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar st.m) (st.n + 2 * (S.L ε σ :
        ℤ)) ∪
          HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar (geometryUpdate ε st.m
            (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
              (st.n + 2 * (S.L ε σ : ℤ)))))) (st.n + (S.L ε σ : ℤ)) ⊆
        HighContrast.centeredCube d (2 * (jStar : ℤ)))
    (hstep : ∀ st : RunState P γ S ε σ B E H jStar n₀, st.i ≤ J →
      (∃ st' : RunState P γ S ε σ B E H jStar n₀, st'.i = st.i + 1 ∧
          runGauge P γ jStar (S.eta ε σ) a w S.h st'.m st'.k st'.n -
            runGauge P γ jStar (S.eta ε σ) a w S.h st.m st.k st.n ≤ -c) ∨
        RunStopData P γ S ε σ B E H jStar n₀ Cout st) :
    ∃ st : RunState P γ S ε σ B E H jStar n₀, st.i ≤ J ∧
      RunStopData P γ S ε σ B E H jStar n₀ Cout st := by
  classical
  have _ := hS
  have _ := hε
  have _ := hσ
  have _ := hB
  have _ := hH
  have _ := hh
  have _ := hL1
  have _ := hn₀
  have _ := ha
  have _ := hcont
  have hlog : 0 < Real.log (16 / 9) := Real.log_pos (by norm_num)
  have hη : 0 < S.eta ε σ := by
    by_contra hcon
    push Not at hcon
    have h1 : 0 ≤ (-(S.eta ε σ)) * Real.log (16 / 9) := mul_nonneg (by linarith only [hcon]) hlog.le
    rw [hc] at hcpos
    linarith only [h1, hcpos]
  have hdR : (0 : ℝ) < (d : ℝ) := by
    have h2 : (0 : ℕ) < d := by omega
    exact_mod_cast h2
  have hw0 : (0 : ℝ) ≤ w := by
    rw [hw]
    exact div_nonneg (mul_nonneg (by linarith only [ha1]) (by linarith only [hC])) hdR.le
  have hgauge : ∀ st : RunState P γ S ε σ B E H jStar n₀,
      0 ≤ runGauge P γ jStar (S.eta ε σ) a w S.h st.m st.k st.n := by
    intro st
    have h1 := run_potential_nonneg hd P γ hγ E Ψ K Src hP hst hur hce jStar hjStar
      st.m st.hm st.k st.n st.hk st.hkn (S.eta ε σ) a hη (by linarith only [ha1])
    have h2 := run_reserve_rounded_nonneg hd P γ E Ψ K Src hP hst hur hce jStar hjStar
      st.m st.hm S.h st.k st.n
    unfold runGauge
    exact add_nonneg h1 (mul_nonneg hw0 h2)
  exact run_exists_stop_abstract (fun st : RunState P γ S ε σ B E H jStar n₀ => st.i)
    (fun st => runGauge P γ jStar (S.eta ε σ) a w S.h st.m st.k st.n)
    (fun st => RunStopData P γ S ε σ B E H jStar n₀ Cout st)
    c hcpos J st₀ hst₀ hgauge hbound hstep
end

end HCPolySupport.HighContrast.Multiscale
