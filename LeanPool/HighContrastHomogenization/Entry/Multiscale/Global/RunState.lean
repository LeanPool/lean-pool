/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.Global.Run
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedCellMeasurability

/-!
# High-contrast homogenization: Entry.Multiscale.Global.RunState

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The finite run of `p.scale.selection`: the state and the entry/initialization lemmas

This file carries the continuing datum of the run that closes `global_run`
(`p.global.selection`) and the three landed lemmas that do not mention a step:

* `RunState` is the continuing datum `(𝔪_i, k_i, n_i)` together with the invariants that
  every application of `SelectionData.Selects` needs at entry: positivity of the metric,
  `j_* ≤ k < n`, the eccentricity clause `e.renormalization.eccentricity.output`, the two
  entry implications `k = n → 𝒫 + D ≤ 1` and `k < n → k + h ≤ n`, and the two *run* fields
  the tail clauses do not re-establish — the accumulated projective displacement
  `d_pr(Id, 𝔪_i) ≤ ε(i+1)` and the generation budget `n_i ≤ n₀ + (2L+H+h)(i+1)`. Those last
  two buy the containment premise at step `i+1` (`R1`).
* `runGauge` is the transferred Lyapunov function `Φ̃ = Φ + w·R` of `run_energy_transfer`:
  the determinant charges are paid out of the reserve `run_reserve` as they are made, so
  `exists_stop_of_potential` is applied with `charge ≡ 0` and `Bud = 0`, and the paper's
  budget `Φ₁ + aC(h+2)log(24Π)` appears as the initial bound `R4` + `R5`.
* `run_entry_containment` (R1), `run_initial` (R4) and
  `run_initial_reserve` (R5) are **landed with complete proofs** (standard axioms only).

The steps are in `HCPoly.Entry.Multiscale.Global.RunSteps` and
`HCPoly.Entry.Multiscale.Global.RunStepsChange`, the stop and the stopping argument in
`HCPoly.Entry.Multiscale.Global.RunStop`, and the assembly with the two `Selects` projections in
`HCPoly.Entry.Multiscale.Global.RunAssembly`.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean aspectRatio aspectRatio_nonneg
  blockLogDet blockScale)
open HCPolySupport.HighContrast (aspectRatio_nonneg)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## §1 The run state -/

/-- The continuing datum of the run (`p.global.selection`) together with the entry
invariants of `SelectionData.Selects`. `i` is the step index; `n₀` is the entry generation
of `initial_provider_input`. -/
structure RunState {d : ℕ} (P : Measure (CoeffSpace d)) (γ : ℝ) (S : SelectionData)
    (ε σ B : ℝ) (E : BlockMat d) (H jStar : ℕ) (n₀ : ℤ) where
  /-- The retained metric `𝔪_i`. -/
  m : Mat d
  /-- The retained generation `k_i` of the geometry. -/
  k : ℤ
  /-- The current generation `n_i`. -/
  n : ℤ
  /-- The step index `i`. -/
  i : ℕ
  /-- `𝔪_i > 0`. -/
  hm : m.PosDef
  /-- `j_* ≤ k_i`. -/
  hk : (jStar : ℤ) ≤ k
  /-- `k_i ≤ n_i`. -/
  hkn : k ≤ n
  /-- `e.renormalization.eccentricity.output` at `(𝔪_i, k_i)`. -/
  hecc : 1 / 2 * Real.log (‖m‖ * ‖m⁻¹‖) ≤
    ε / (S.L ε σ : ℝ) *
      ((k : ℝ) - (jStar : ℝ) - (⌈B * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ))
  /-- `e.renormalization.output`, first clause. -/
  hone : k = n →
    profile P γ (Geometry.explicitRoundedGrid jStar m) jStar n n +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n ≤ 1
  /-- `e.renormalization.output`, second clause. -/
  hgap : k < n → k + (S.h : ℤ) ≤ n
  /-- Accumulated projective displacement (`p.global.selection`). -/
  hpr : projectiveDistance (1 : Mat d) m ≤ ε * ((i : ℝ) + 1)
  /-- Generation budget (`p.global.selection`). -/
  hgen : n ≤ n₀ + (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * ((i : ℤ) + 1)
  /-- `k_i < n_i`.  Every step lemma
  needs `k < n`, and the stop configuration asserts it; at `k = n` the only clause
  `SelectionData.Selects` offers is the Alternative-1 start-up, which by design is not a
  counted step.  `run_initial` produces `k = n₀ < n₀ + S.h` and every step output keeps it. -/
  hlt : k < n

/-- The transferred Lyapunov gauge `Φ̃ = Φ + w·R` of `run_energy_transfer`: the potential
plus `w` times the determinant reserve of the retained grid. -/
@[expose]
def runGauge {d : ℕ} (P : Measure (CoeffSpace d)) (γ : ℝ) (jStar : ℕ) (η a w : ℝ) (h : ℕ)
    (m : Mat d) (k n : ℤ) : ℝ :=
  potential P γ jStar η a m k n +
    w * run_reserve (fun r => blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar m) r)) h k n

/-! ## §2 Entry premises of `Selects` (landed) -/

/-- `√(4d) = 2 √d`. -/
private theorem sqrt_four_mul (x : ℝ) (_hx : 0 ≤ x) :
    Real.sqrt (4 * x) = 2 * Real.sqrt x := by
  rw [show (4 : ℝ) * x = 2 ^ 2 * x by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]

/-- The containment argument `2 √d · (2 e^e) = (2 √(4d)) · e^e`, in logarithms. -/
private theorem logb_containment_arg (x e : ℝ) (hx : 0 < x) :
    Real.logb 3 (2 * Real.sqrt x * (2 * Real.exp e)) =
      Real.logb 3 (2 * Real.sqrt (4 * x)) + e / Real.log 3 := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have h4 : Real.sqrt (4 * x) = 2 * Real.sqrt x := sqrt_four_mul x hx.le
  have harg : 2 * Real.sqrt x * (2 * Real.exp e)
      = (2 * Real.sqrt (4 * x)) * Real.exp e := by rw [h4]; ring
  have hA : (2 : ℝ) * Real.sqrt (4 * x) ≠ 0 := by rw [h4]; positivity
  rw [harg]
  simp only [Real.logb]
  rw [Real.log_mul hA (Real.exp_ne_zero e), Real.log_exp]
  ring

/-- Operator-norm bound for the rounded grid from the eccentricity clause. -/
private theorem explicitRoundedGrid_opNorm_le_two_exp {d : ℕ} [NeZero d] (jStar : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef) (e : ℝ)
    (hecc : 1 / 2 * Real.log (‖m‖ * ‖m⁻¹‖) ≤ e) :
    ‖Geometry.explicitRoundedGrid jStar m‖ ≤ 2 * Real.exp e := by
  have h1 := explicitRoundedGrid_opNorm_le (d := d) (jStar := jStar) (m := m) hjStar hm
  rw [← Real.sqrt_eq_rpow] at h1
  have h2 : Real.sqrt (‖m‖ * ‖m⁻¹‖) ≤ Real.exp e := by
    rw [Geometry.eccentricity_eq_exp_half_log hm]
    exact Real.exp_le_exp.mpr hecc
  linarith only [h1, h2]

/-- **(R1) Entry containment.** The containment premise of `Selects`, for two grids whose
metrics both have eccentricity at most `e`. Route: `explicitRoundedGrid_opNorm_le` gives
`‖𝒬(𝔪)‖ ≤ 2(‖𝔪‖‖𝔪⁻¹‖)^{1/2} ≤ 2 e^{e}`, and `adaptedCell_subset_centeredCube_of_opNorm` at
`ρ := 2 * Real.exp e` needs `(j:ℝ) + logb 3 (2√d · 2e^{e}) ≤ 2 j_*`; since
`2√d · 2 = 2√(4d)`, that is the hypothesis `hj` (the factor `2` of `explicitRoundedGrid_opNorm_le`
absorbed by instantiating `containment_arith` at `d := 4d`), and
`logb 3 (2√(4d) · e^{e}) = logb 3 (2√(4d)) + e / log 3`. -/
theorem run_entry_containment {d : ℕ} (hd : 2 ≤ d) (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (m mP : Mat d) (hm : m.PosDef) (hmP : mP.PosDef) (j jP : ℤ) (e : ℝ) (he : 0 ≤ e)
    (hecc : 1 / 2 * Real.log (‖m‖ * ‖m⁻¹‖) ≤ e)
    (heccP : 1 / 2 * Real.log (‖mP‖ * ‖mP⁻¹‖) ≤ e)
    (hj : (j : ℝ) + (Real.logb 3 (2 * Real.sqrt (4 * d)) + e / Real.log 3) ≤ 2 * (jStar : ℝ))
    (hjP : (jP : ℝ) + (Real.logb 3 (2 * Real.sqrt (4 * d)) + e / Real.log 3) ≤
      2 * (jStar : ℝ)) :
    HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m) j ∪
        HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar mP) jP ⊆
      HighContrast.centeredCube d (2 * (jStar : ℤ)) := by
  have : NeZero d := ⟨by omega⟩
  have hdR : (0 : ℝ) < (d : ℝ) := by
    have : 0 < d := by omega
    exact_mod_cast this
  have hexp : (1 : ℝ) ≤ Real.exp e := Real.one_le_exp he
  have hρ : (0 : ℝ) < 2 * Real.exp e := by linarith only [hexp]
  have hlog := logb_containment_arg (d : ℝ) e hdR
  refine Set.union_subset ?_ ?_
  · refine adaptedCell_subset_centeredCube_of_opNorm _ (2 * Real.exp e) j jStar
      (explicitRoundedGrid_opNorm_le_two_exp jStar hjStar m hm e hecc) hρ ?_
    rw [hlog]
    linarith only [hj]
  · refine adaptedCell_subset_centeredCube_of_opNorm _ (2 * Real.exp e) jP jStar
      (explicitRoundedGrid_opNorm_le_two_exp jStar hjStar mP hmP e heccP) hρ ?_
    rw [hlog]
    linarith only [hjP]

/-! ## §3 Initialization (landed) -/

/-- **(R4) The initial state and the initial potential**
(`p.global.selection`). `initial_provider_input` gives `n₀` with
`𝒫 + D ≤ ηinit = 1` at `(Id, n₀, n₀)` and `d_pr(Id, m(𝐀_{n₀,Id})) ≤ Cgeom log(2+4Π)`; the
Alt-1 start-up disjunct of `Selects` at that tuple (`hstart`) advances to
`(Id, n₀, n₀ + h)`, which is the paper's `(𝔪₁, 𝔮₁, k₁, n₁)`. The potential bound is
`scalar_span` (`ScalarLemmas.lean`, `ℓ = 1`) followed by the arithmetic comparison of
the logarithmic terms supplied by `harith`, whose premise `Δ ≤ Cdet log(2+Π)` at `n₀` is `hdet`,
obtained from `blockLogDet_le_of_initial_sandwich` + `refBlock_le_six_aspect` applied to the
sandwich `hsand₁`/`hsand₂`. The invariants: `hm` is `Matrix.PosDef.one`;
`hecc` is `‖1‖‖1⁻¹‖ = 1` and `hn₀`; `hone` is vacuous for `1 ≤ S.h`; `hgap` is `rfl`-level;
`hpr` is `projectiveDistance_self`; `hgen` is `hn₀`. -/
theorem run_initial {d : ℕ} (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (Src : CoeffSpace d → ℝ) (hP : IsProbabilityMeasure P) (hst : IsStationaryLaw P)
    (hur : IsUnitRangeLaw P) (hce : CoarseEllipticityDagger P γ E Ψ K Src)
    (S : SelectionData) (ε σ B : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) S.eps0)
    (hσ : σ ∈ Set.Ioc (0 : ℝ) ε) (hB : 1 ≤ B) (H jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar)
    (hh1 : 1 ≤ S.h) (hL1 : 1 ≤ S.L ε σ) (n₀ : ℤ)
    (hn₀ : (jStar : ℤ) + ⌈B * Real.logb 3 (2 + aspectRatio E)⌉ ≤ n₀)
    (a C C' Cdet Cgeom : ℝ) (hC : 1 ≤ C) (ha1 : 1 ≤ a) (hCdet : 0 ≤ Cdet)
    (hCgeom : 0 < Cgeom)
    (hgeo : projectiveDistance (1 : Mat d)
        (explicitCanonicalMetric (adaptedMean P (1 : Mat d) n₀)) ≤
      Cgeom * Real.log (2 + 4 * aspectRatio E))
    (hdet : detIncrement P (Geometry.explicitRoundedGrid jStar (1 : Mat d)) n₀ (n₀ + (S.h : ℤ)) ≤
      Cdet * Real.log (2 + aspectRatio E))
    (harith : ∀ AR Δ : ℝ, 0 ≤ AR → 0 ≤ Δ → Δ ≤ Cdet * Real.log (2 + AR) →
      Real.log (1 + C * (S.h : ℝ)) + (bigQ d γ : ℝ) * Δ +
          a * Cgeom * Real.log (2 + 4 * AR) ≤ C' * Real.logb 3 (2 + AR))
    (hinit : profile P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar n₀ n₀ +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar n₀ ≤ 1)
    (hstart : profile P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar n₀
          (n₀ + (S.h : ℤ)) +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar
          (n₀ + (S.h : ℤ)) ≤
      C * (profile P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar n₀ n₀ +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar n₀ +
        Real.exp ((bigQ d γ : ℝ) *
          detIncrement P (Geometry.explicitRoundedGrid jStar (1 : Mat d)) n₀ (n₀ + (S.h : ℤ))) - 1))
    (hone' : n₀ = n₀ + (S.h : ℤ) →
      profile P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar (n₀ + (S.h : ℤ))
          (n₀ + (S.h : ℤ)) +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar
          (n₀ + (S.h : ℤ)) ≤ 1) :
    ∃ st : RunState P γ S ε σ B E H jStar n₀,
      st.m = (1 : Mat d) ∧ st.k = n₀ ∧ st.n = n₀ + (S.h : ℤ) ∧ st.i = 0 ∧
        potential P γ jStar (S.eta ε σ) a st.m st.k st.n ≤
          C' * Real.logb 3 (2 + aspectRatio E) := by
  let := hP
  let : NeZero d := ⟨by omega⟩
  have _ := hγ
  have _ := hur
  have _ := hCdet
  have _ := hCgeom
  have hε0 : 0 < ε := hε.1
  have hσ0 : 0 < σ := hσ.1
  have hAR0 : 0 ≤ aspectRatio E := aspectRatio_nonneg E
  have hlogb0 : 0 ≤ B * Real.logb 3 (2 + aspectRatio E) :=
    mul_nonneg (by linarith only [hB]) (Real.logb_nonneg (by norm_num) (by linarith only [hAR0]))
  have hceil0 : (0 : ℤ) ≤ ⌈B * Real.logb 3 (2 + aspectRatio E)⌉ := Int.ceil_nonneg hlogb0
  have hjn₀ : (jStar : ℤ) ≤ n₀ := by omega
  have hgrid : Geometry.explicitRoundedGrid jStar (1 : Mat d) = (1 : Mat d) :=
    Geometry.explicitRoundedGrid_one (d := d) jStar
  have hecc : 1 / 2 * Real.log (‖(1 : Mat d)‖ * ‖(1 : Mat d)⁻¹‖) ≤
      ε / (S.L ε σ : ℝ) *
        ((n₀ : ℝ) - (jStar : ℝ) - ((⌈B * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ) : ℝ)) := by
    have hlhs : 1 / 2 * Real.log (‖(1 : Mat d)‖ * ‖(1 : Mat d)⁻¹‖) = 0 := by
      rw [inv_one, norm_one, mul_one, Real.log_one, mul_zero]
    rw [hlhs]
    have hL0 : (0 : ℝ) < (S.L ε σ : ℝ) := by
      have h1 : (1 : ℝ) ≤ (S.L ε σ : ℝ) := by exact_mod_cast hL1
      linarith only [h1]
    have hfrac : 0 ≤ ε / (S.L ε σ : ℝ) := le_of_lt (div_pos hε0 hL0)
    have hcast : ((jStar : ℤ) : ℝ) + ((⌈B * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ) : ℝ) ≤
        (n₀ : ℝ) := by exact_mod_cast hn₀
    have hnn : 0 ≤ (n₀ : ℝ) - (jStar : ℝ) -
        ((⌈B * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ) : ℝ) := by
      push_cast at hcast ⊢
      linarith only [hcast]
    exact mul_nonneg hfrac hnn
  have hprself : projectiveDistance (1 : Mat d) (1 : Mat d) = 0 :=
    (Geometry.projectiveDistance_eq_zero_iff (Geometry.one_posDef d)
      (Geometry.one_posDef d)).2 ⟨1, one_pos, (one_smul ℝ (1 : Mat d)).symm⟩
  refine ⟨{ m := (1 : Mat d), k := n₀, n := n₀ + (S.h : ℤ), i := 0,
            hm := Geometry.one_posDef d, hk := hjn₀, hkn := by omega, hlt := by omega,
            hecc := hecc, hone := hone', hgap := fun _ => le_rfl,
            hpr := by rw [hprself]; positivity,
            hgen := by
              have hnn : (0 : ℤ) ≤ 2 * (S.L ε σ : ℤ) + (H : ℤ) := by positivity
              omega },
          rfl, rfl, rfl, rfl, ?_⟩
  show potential P γ jStar (S.eta ε σ) a (1 : Mat d) n₀ (n₀ + (S.h : ℤ)) ≤
    C' * Real.logb 3 (2 + aspectRatio E)
  set x : ℝ := profile P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar n₀ n₀ +
    determinantDrift P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar n₀ with hxdef
  set x' : ℝ := profile P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar n₀
      (n₀ + (S.h : ℤ)) +
    determinantDrift P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar (n₀ + (S.h : ℤ))
    with hx'def
  set y : ℝ := detIncrement P (Geometry.explicitRoundedGrid jStar (1 : Mat d)) n₀ (n₀ + (S.h : ℤ))
    with hydef
  have hx0 : 0 ≤ x := by
    rw [hxdef]
    exact profile_add_determinantDrift_nonneg d hd P γ E Ψ K Src hst hce jStar hjStar
      (1 : Mat d) (Geometry.one_posDef d) n₀ n₀ hjn₀ le_rfl
  have hx'0 : 0 ≤ x' := by
    rw [hx'def]
    exact profile_add_determinantDrift_nonneg d hd P γ E Ψ K Src hst hce jStar hjStar
      (1 : Mat d) (Geometry.one_posDef d) n₀ (n₀ + (S.h : ℤ)) hjn₀ (by omega)
  have hy0 : 0 ≤ y := by
    rw [hydef]
    exact Annealed.logDetLoss_nonneg d hd P γ E Ψ K Src hst hce jStar hjStar
      (1 : Mat d) (Geometry.one_posDef d) n₀ (n₀ + (S.h : ℤ)) hjn₀ (by omega)
  have hηmem : S.eta ε σ ∈ Set.Ioc (0 : ℝ) 1 := by
    refine ⟨?_, selectionData_eta_le_one S ε σ hε hσ⟩
    have hc0 : 0 < S.c := S.c_mem.1
    have hpos : 0 < S.c * ε * σ := by positivity
    simpa [SelectionData.eta] using hpos
  have hQ0 : (0 : ℝ) ≤ (bigQ d γ : ℝ) := Nat.cast_nonneg _
  have hspan := scalar_span (S.eta ε σ) (bigQ d γ : ℝ) C 1 x x' y hηmem (by linarith only [hC])
    le_rfl hQ0 hx0 hinit hy0 hx'0 (by rw [mul_one]; linarith only [hstart])
  have hmetric : projectiveDistance (1 : Mat d)
      (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar (1 : Mat d)) n₀)) ≤
      Cgeom * Real.log (2 + 4 * aspectRatio E) := by rw [hgrid]; exact hgeo
  have ha0 : (0 : ℝ) ≤ a := by linarith only [ha1]
  have hmetric' : a * projectiveDistance (1 : Mat d)
      (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar (1 : Mat d)) n₀)) ≤
      a * Cgeom * Real.log (2 + 4 * aspectRatio E) := by
    have hm2 := mul_le_mul_of_nonneg_left hmetric ha0
    linarith only [hm2]
  have hlogmono : Real.log (1 + C * 1) ≤ Real.log (1 + C * (S.h : ℝ)) := by
    have hh : (1 : ℝ) ≤ (S.h : ℝ) := by exact_mod_cast hh1
    have hC0 : (0 : ℝ) < C := by linarith only [hC]
    exact Real.log_le_log (by linarith only [hC0]) (by nlinarith only [hC0, hh])
  have hfin := harith (aspectRatio E) y hAR0 hy0 (by rw [hydef]; exact hdet)
  have hpot : potential P γ jStar (S.eta ε σ) a (1 : Mat d) n₀ (n₀ + (S.h : ℤ)) =
      S.eta ε σ * Real.log (1 + x' / S.eta ε σ) +
        a * projectiveDistance (1 : Mat d)
          (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar (1 : Mat d)) n₀)) := rfl
  rw [hpot]
  linarith only [hspan, hmetric', hlogmono, hfin]

/-- **(R5) The charge budget, as the initial reserve bound** (`p.global.selection`).
The determinant charges are transferred into the reserve step by step
(`run_energy_transfer`), so `exists_stop_of_potential` runs with `charge ≡ 0` and `Bud = 0`
and the paper's budget `Φ₁ + aC(h+2)log(24Π)` is exactly
`potential ≤ C' log₃(2+Π)` (R4) plus this bound on the initial reserve. Route:
`run_reserve_initial` (with the extra binder `hjn₀ : (jStar : ℤ) ≤ n₀`) with monotonicity of `r ↦
blockLogDet (adaptedMean P (𝒬 Id) r)` from
the annealed order, then `blockLogDet_le_of_initial_sandwich` (whose `hsix` is
`refBlock_le_six_aspect`) at the sandwich `hsand₁`/`hsand₂` of `initial_provider_input`. -/
theorem run_initial_reserve {d : ℕ} (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (Src : CoeffSpace d → ℝ) (hP : IsProbabilityMeasure P) (hst : IsStationaryLaw P)
    (hur : IsUnitRangeLaw P) (hce : CoarseEllipticityDagger P γ E Ψ K Src)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (h : ℕ) (n₀ : ℤ)
    (hjn₀ : (jStar : ℤ) ≤ n₀)
    (hEs : IsSymmetricBlockMat E) (hE : Book.Ch02.BlockPosDef E)
    (hAR : 0 < aspectRatio E)
    (hsand₁ : BlockMatLoewnerLE
      (blockScale (1 / 2)
        (ofFullBlockMat (toFullBlockMat (blockSwap d) * (toFullBlockMat E)⁻¹ *
          toFullBlockMat (blockSwap d))))
      (adaptedMean P (1 : Mat d) n₀))
    (hsand₂ : BlockMatLoewnerLE (adaptedMean P (1 : Mat d) n₀) (blockScale 2 E)) :
    run_reserve
        (fun r => blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar (1 : Mat d)) r)) h n₀
        (n₀ + (h : ℤ)) ≤
      ((h : ℝ) + 2) * ((d : ℝ) * Real.log (24 * aspectRatio E)) := by
  let := hP
  let : NeZero d := ⟨by omega⟩
  have _ := hγ
  have _ := hur
  have _ := hsand₁
  have hgrid : Geometry.explicitRoundedGrid jStar (1 : Mat d) = (1 : Mat d) :=
    Geometry.explicitRoundedGrid_one (d := d) jStar
  have hmono : ∀ r : ℤ, n₀ ≤ r →
      blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar (1 : Mat d)) r) ≤
        blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar (1 : Mat d)) n₀) := by
    intro r hr
    have hloss := Annealed.logDetLoss_nonneg d hd P γ E Ψ K Src hst hce jStar hjStar
      (1 : Mat d) (Geometry.one_posDef d) n₀ r hjn₀ hr
    simp only [detIncrement] at hloss
    linarith only [hloss]
  have hres := run_reserve_initial
    (fun r => blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar (1 : Mat d)) r)) h n₀ hmono
  have hApos : Book.Ch02.BlockPosDef (adaptedMean P (1 : Mat d) n₀) := by
    have := run_adaptedMean_blockPosDef hd P γ E Ψ K Src hP hst hce jStar hjStar
      (1 : Mat d) (Geometry.one_posDef d) n₀
    rwa [hgrid] at this
  have hdet : blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar (1 : Mat d)) n₀) ≤
      (d : ℝ) * Real.log (24 * aspectRatio E) := by
    rw [hgrid]
    exact blockLogDet_le_of_initial_sandwich E (adaptedMean P (1 : Mat d) n₀) hEs hE
      (Recurrence.isSymmetricBlockMat_adaptedMean P (1 : Mat d) n₀) hApos hAR
      (refBlock_le_six_aspect E hEs hE) hsand₂
  have hh2 : (0 : ℝ) ≤ (h : ℝ) + 2 := by positivity
  calc run_reserve
        (fun r => blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar (1 : Mat d)) r)) h n₀
        (n₀ + (h : ℤ))
      ≤ ((h : ℝ) + 2) *
          blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar (1 : Mat d)) n₀) := hres
    _ ≤ ((h : ℝ) + 2) * ((d : ℝ) * Real.log (24 * aspectRatio E)) :=
        mul_le_mul_of_nonneg_left hdet hh2
end

end HCPolySupport.HighContrast.Multiscale
