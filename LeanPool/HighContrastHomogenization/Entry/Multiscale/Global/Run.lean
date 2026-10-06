/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.Global.OutputAndRun
public import LeanPool.HighContrastHomogenization.Entry.Analysis.InverseJensen
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedCellMeasurability

/-!
# High-contrast homogenization: Entry.Multiscale.Global.Run

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# EccentricityScaleDecay lemmas for `global_run`

This file collects the sixteen `run_*` helper lemmas behind `global_run` — the
reserve, potential and service-decrease machinery — and the quarter-step
potential-decrease lemma `potential_step_sub_le_of_quarter_bound`.  It also proves four small
lemmas the
assembly needs: a `weight_choice` variant whose witness also dominates `d`, an upper bound
`S.eta ε σ ≤ 1` on the selection step, and two algebraic bridges between the `(d:ℝ)⁻¹ * Δ` test
form and the `d * ε * σ` / `d * σ` form.  This is the per-step machinery of
`p.global.selection`, and through it part of the assembly of `t.polynomial.entry`.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean blockLogDet blockPosDef_annealedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## §1 The sixteen `run_*` lemmas -/

-- Local versions of the authorized rounded-grid restatements. These never use
-- the old arbitrary-grid declarations in DeterminantBounds.
/-- The adapted mean at a rounded grid has nonnegative block log-determinant. -/
theorem run_blockLogDet_adaptedMean_nonneg {d : ℕ} (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ)
    (K : ℝ) (Src : CoeffSpace d → ℝ) (hP : IsProbabilityMeasure P)
    (hst : IsStationaryLaw P) (_hur : IsUnitRangeLaw P)
    (hce : CoarseEllipticityDagger P γ E Ψ K Src)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef) (j : ℤ) :
    0 ≤ blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar m) j) := by
  let := hP
  exact Real.log_nonneg
    (Analysis.one_le_det_adaptedMean hd P γ E Ψ K Src hst hce jStar hjStar m hm j)

/-- The adapted mean at a rounded grid is block positive-definite. -/
theorem run_adaptedMean_blockPosDef {d : ℕ} (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ)
    (K : ℝ) (Src : CoeffSpace d → ℝ) (hP : IsProbabilityMeasure P)
    (hst : IsStationaryLaw P)
    (hce : CoarseEllipticityDagger P γ E Ψ K Src)
    (jStar : ℕ) (hjStar : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef) (j : ℤ) :
    Book.Ch02.BlockPosDef (adaptedMean P (Geometry.explicitRoundedGrid jStar m) j) := by
  let := hP
  let : NeZero d := ⟨by omega⟩
  have hint := Annealed.hasIntegrableCoarseBlock_adapted d hd P γ E Ψ K Src hst hce
    jStar hjStar m hm j 0
  have hpos := blockPosDef_annealedBlock hint (fun a =>
    Annealed.blockPosDef_coarseBlock_adapted (Geometry.explicitRoundedGrid jStar m)
      (Geometry.isUnit_roundedGrid hjStar hm) j 0 a)
  simpa only [adaptedMean, HighContrast.adaptedCellTranslate, zero_add, Set.image_id',
    HighContrast.adaptedCell, HighContrast.centeredCube] using hpos

-- The additive error in the Selects service clause is handled directly.

-- Step 5, with the source constant chosen before H and the profile constant
-- chosen before σ. The equal-parameter span needs no lower bound on H by S.h.
/-- The selected output profile bound, with the source and profile constants furnished
before `H` and `σ` are fixed. -/
theorem run_output_profile (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧ ∀ Cout : ℝ, 0 < Cout →
      ∀ H : ℕ, 1 ≤ H → ∃ Cprof : ℝ, 0 < Cprof ∧
        ∀ σ : ℝ, σ ∈ Set.Ioc (0 : ℝ) 1 →
          ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ)
            (K : ℝ) (Src : CoeffSpace d → ℝ),
            IsProbabilityMeasure P → IsStationaryLaw P → IsUnitRangeLaw P →
            CoarseEllipticityDagger P γ E Ψ K Src →
            ∀ jStar : ℕ, 2 * d ≤ 3 ^ jStar →
              ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
              ∀ m : Mat d, m.PosDef → ∀ s : ℤ, (jStar : ℤ) ≤ s →
                profile P γ (Geometry.explicitRoundedGrid jStar m) jStar s s +
                    determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar s ≤
                  Cout * σ ^ ((1 - γ) / 8) →
                profile P γ (Geometry.explicitRoundedGrid jStar m) jStar s s +
                  determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar s ≤ 1 →
                (d : ℝ)⁻¹ * detIncrement P (Geometry.explicitRoundedGrid jStar m) s (s + H) < σ →
                max
                    (max (profile P γ (Geometry.explicitRoundedGrid jStar m) jStar s s)
                      (profile P γ (Geometry.explicitRoundedGrid jStar m) jStar s (s + H)))
                    (profile P γ (Geometry.explicitRoundedGrid jStar m) jStar (s + H) (s + H)) +
                    determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar s +
                    determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar (s + H) ≤
                  Cprof * σ ^ ((1 - γ) / 8) := by
  obtain ⟨Csrc, hCs, C, hC, hone⟩ :=
    Entry.fixed_geometry_one_grid_propagation_full d hd γ hγ
  refine ⟨Csrc, hCs, ?_⟩
  intro Cout hCout H hH
  let Q : ℝ := bigQ d γ
  let Cexp := Q * d * Real.exp (Q * d)
  have hQ : 0 ≤ Q := Nat.cast_nonneg _
  have hCx : 0 ≤ Cexp := mul_nonneg (mul_nonneg hQ (Nat.cast_nonneg _)) (Real.exp_pos _).le
  refine ⟨2 * Cout + (2 + C) * C * H * (Cout + Cexp), by positivity, ?_⟩
  intro σ hσ P E Ψ K Src hP hst hur hce jStar hj hsrc m hm s hs hout hsmall htest
  let := hP
  have hHR : (0 : ℝ) ≤ H := Nat.cast_nonneg _
  have hHI : (1 : ℤ) ≤ H := by exact_mod_cast hH
  have hst' : s ≤ s + (H : ℤ) := by omega
  have hs' : (jStar : ℤ) ≤ s + (H : ℤ) := hs.trans hst'
  have hbase := hone P E Ψ K Src hP hst hur hce (2 * bigQ d γ) le_rfl
    H hHI jStar hj hsrc m hm s s hs le_rfl
  obtain ⟨_, _, _, _, _, _, _, hspan⟩ := hbase
  have hspan' := hspan (Or.inl rfl) hsmall
  have hmajor := (hone P E Ψ K Src hP hst hur hce (2 * bigQ d γ) le_rfl
    H hHI jStar hj hsrc m hm s (s + H) hs hst').1
  rw [← profile_diagonal_eq_history d hd γ hγ P E Ψ K Src hP hst hur hce
    jStar hj m hm (s + H)] at hmajor
  have hp := Annealed.bridge_profile_nonneg d hd P γ E Ψ K Src hst hce jStar hj m hm
  have hD := Annealed.bridge_determinantDrift_nonneg d hd P γ E Ψ K Src hst hce jStar hj m hm
  have hΔ0 := Annealed.logDetLoss_nonneg d hd P γ E Ψ K Src hst hce
    jStar hj m hm s (s + H) hs hst'
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hΔ : detIncrement P (Geometry.explicitRoundedGrid jStar m) s (s + H) < (d : ℝ) * σ := by
    have hh := (div_lt_iff₀ hdR).1 (show
      detIncrement P (Geometry.explicitRoundedGrid jStar m) s (s + H) / (d : ℝ) < σ by
      simpa only [div_eq_mul_inv, mul_comm] using htest)
    simpa only [mul_comm] using hh
  apply output_profile_bound Cout C C Cexp Q (σ ^ ((1 - γ) / 8)) σ H d
    _ _ _ _ _ _ (Real.rpow_nonneg hσ.1.le _) hCout.le hC.le hC.le hCx hHR hQ
    (Nat.cast_nonneg _) hσ.1.le (hp s s hs le_rfl) (hD s)
    (hp s (s + H) hs hst') (hD (s + H)) (hp (s + H) (s + H) hs' le_rfl)
    hΔ0 hΔ hout _ (exp_sub_one_le_rpow Q d σ γ hQ (Nat.cast_nonneg _) hσ hγ) hmajor
  simpa only [Q, add_sub_assoc] using! hspan'

-- The determinant reserve counts the h trailing generations, the current
-- generation, and the initial generation of the retained geometry.
/-- The determinant reserve: the sum of `h` trailing generations plus the current and initial
generations. -/
@[expose]
def run_reserve (D : ℤ → ℝ) (h : ℕ) (k n : ℤ) : ℝ :=
  (∑ i ∈ Finset.range h, D (n - (i : ℤ))) + D n + D k

/-- The reserve's drop across one `h`-step matches the synchronized plus one-step loss. -/
theorem run_reserve_sync {d : ℕ} (P : Measure (CoeffSpace d)) (q : Mat d)
    (h : ℕ) (k n : ℤ) :
    run_reserve (fun r => blockLogDet (adaptedMean P q r)) h k n -
      run_reserve (fun r => blockLogDet (adaptedMean P q r)) h k (n + h) =
      synchCharge P q h n + detIncrement P q n (n + h) := by
  have hs : (∑ i ∈ Finset.range h,
      detIncrement P q (n - (i : ℤ)) (n + h - (i : ℤ))) =
      synchCharge P q h n := by
    unfold synchCharge
    refine Finset.sum_bij (fun i _ => n + (h : ℤ) - (i : ℤ)) ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_range] at hi
      simp only [Finset.mem_Icc]
      omega
    · intro i hi j hj hij
      omega
    · intro a ha
      simp only [Finset.mem_Icc] at ha
      refine ⟨(n + (h : ℤ) - a).toNat, ?_, ?_⟩
      · simp only [Finset.mem_range]
        omega
      · omega
    · intro i _
      congr 1
      omega
  simp only [detIncrement, Finset.sum_sub_distrib] at hs
  unfold run_reserve detIncrement
  linarith only [hs]

/-- The reserve is nonnegative when `D` is. -/
theorem run_reserve_nonneg (D : ℤ → ℝ) (h : ℕ) (k n : ℤ)
    (hD : ∀ r, 0 ≤ D r) : 0 ≤ run_reserve D h k n := by
  exact add_nonneg (add_nonneg (Finset.sum_nonneg fun _ _ => hD _) (hD n)) (hD k)

/-- The reserve's drop over an advancing window bounds `D`'s drop. -/
theorem run_reserve_advance (D : ℤ → ℝ) (h : ℕ) (j k n t : ℤ)
    (hmono : ∀ r s, j ≤ r → r ≤ s → D s ≤ D r)
    (_hjn : j ≤ n) (hwindow : j + (h : ℤ) ≤ n + 1) (hnt : n ≤ t) :
    D n - D t ≤ run_reserve D h k n - run_reserve D h k t := by
  have hs : (∑ i ∈ Finset.range h, D (t - (i : ℤ))) ≤
      ∑ i ∈ Finset.range h, D (n - (i : ℤ)) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' := Finset.mem_range.mp hi
    exact hmono _ _ (by omega) (by omega)
  unfold run_reserve
  linarith only [hs]

/-- The reserve's change across a geometry change, up to a `(h+2)Λ` jump term. -/
theorem run_reserve_change (D D' : ℤ → ℝ) (h : ℕ) (j k n u s t : ℤ) (Λ : ℝ)
    (hmono : ∀ r r', j ≤ r → r ≤ r' → D r' ≤ D r)
    (hmono' : ∀ r r', j ≤ r → r ≤ r' → D' r' ≤ D' r)
    (hjn : j ≤ n) (hwindow : j + (h : ℤ) ≤ n + 1) (hnu : n ≤ u)
    (hjs : j ≤ s) (hst : s + (h : ℤ) ≤ t)
    (hjump : D' s ≤ D u + Λ) :
    (D k - D u) + (D' s - D' t) - ((h : ℝ) + 2) * Λ ≤
      run_reserve D h k n - run_reserve D' h s t := by
  have hlo : (h : ℝ) * D u ≤ ∑ i ∈ Finset.range h, D (n - (i : ℤ)) := by
    have hh : (∑ _i ∈ Finset.range h, D u) ≤
        ∑ i ∈ Finset.range h, D (n - (i : ℤ)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_range.mp hi
      exact hmono _ _ (by omega) (by omega)
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hh
  have hhi : (∑ i ∈ Finset.range h, D' (t - (i : ℤ))) ≤ (h : ℝ) * D' s := by
    have hh : (∑ i ∈ Finset.range h, D' (t - (i : ℤ))) ≤
        ∑ _i ∈ Finset.range h, D' s := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_range.mp hi
      exact hmono' _ _ hjs (by omega)
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hh
  have hn := hmono n u hjn hnu
  have hjump' := mul_le_mul_of_nonneg_left hjump
    (show 0 ≤ (h : ℝ) + 2 by positivity)
  unfold run_reserve
  nlinarith only [hlo, hhi, hn, hjump']

/-- The reserve at the initial generation is bounded by `(h+2) D k`. -/
theorem run_reserve_initial (D : ℤ → ℝ) (h : ℕ) (k : ℤ)
    (hmono : ∀ r, k ≤ r → D r ≤ D k) :
    run_reserve D h k (k + h) ≤ ((h : ℝ) + 2) * D k := by
  have hh : (∑ i ∈ Finset.range h, D (k + h - (i : ℤ))) ≤ (h : ℝ) * D k := by
    have hh' : (∑ i ∈ Finset.range h, D (k + h - (i : ℤ))) ≤
        ∑ _i ∈ Finset.range h, D k := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_range.mp hi
      exact hmono _ (by omega)
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hh'
  have hn := hmono (k + h) (by omega)
  unfold run_reserve
  linarith only [hh, hn]

/-- The potential is nonnegative on the retained geometry. -/
theorem run_potential_nonneg {d : ℕ} (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) (γ : ℝ) (_hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (Src : CoeffSpace d → ℝ)
    (hP : IsProbabilityMeasure P) (hst : IsStationaryLaw P) (_hur : IsUnitRangeLaw P)
    (hce : CoarseEllipticityDagger P γ E Ψ K Src)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (k n : ℤ) (hk : (jStar : ℤ) ≤ k) (hkn : k ≤ n)
    (η a : ℝ) (hη : 0 < η) (ha : 0 ≤ a) :
    0 ≤ potential P γ jStar η a m k n := by
  let := hP
  let : NeZero d := ⟨by omega⟩
  have hx := profile_add_determinantDrift_nonneg d hd P γ E Ψ K Src
    hst hce jStar hj m hm k n hk hkn
  have hF := run_adaptedMean_blockPosDef hd P γ E Ψ K Src hP hst hce
    jStar hj m hm k
  have hmetric := Geometry.projectiveDistance_nonneg hm
    (explicitCanonicalMetric_posDef _ (Recurrence.isSymmetricBlockMat_adaptedMean P _ k) hF)
  unfold potential
  exact add_nonneg (mul_nonneg hη.le (Real.log_nonneg
    (le_add_of_nonneg_right (div_nonneg hx hη.le)))) (mul_nonneg ha hmetric)

/-- The reserve built from the rounded-grid adapted mean is nonnegative. -/
theorem run_reserve_rounded_nonneg {d : ℕ} (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ)
    (K : ℝ) (Src : CoeffSpace d → ℝ) (hP : IsProbabilityMeasure P)
    (hst : IsStationaryLaw P) (hur : IsUnitRangeLaw P)
    (hce : CoarseEllipticityDagger P γ E Ψ K Src)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar) (m : Mat d) (hm : m.PosDef)
    (h : ℕ) (k n : ℤ) :
    0 ≤ run_reserve (fun r => blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar m) r))
      h k n :=
  run_reserve_nonneg _ h k n
    (run_blockLogDet_adaptedMean_nonneg hd P γ E Ψ K Src hP hst hur hce jStar hj m hm)

-- Apply with J = 0 on a fixed geometry, and J = (h+2)·2d·log(1+δ)
-- on a geometry change. The reserve supplies the determinant budget locally.
/-- Transferring a charge against the reserve preserves the potential-plus-reserve decrease. -/
theorem run_energy_transfer (φ φ' R R' c w charge J : ℝ) (hw : 0 ≤ w)
    (hstep : φ' - φ ≤ -c - w * J + w * charge)
    (hreserve : charge - J ≤ R - R') :
    (φ' + w * R') - (φ + w * R) ≤ -c := by
  nlinarith only [hstep, mul_le_mul_of_nonneg_left hreserve hw]

/-! ## §2 The quarter-step potential decrease -/

/-- For abstract reals with `p ≤ 2q` and `η ≥ 0`, `½ η p ≤ η q`.  The logarithms of the
quarter-step estimate are kept abstract here so that no arithmetic closer inspects them. -/
private lemma half_mul_le_mul_of_le_two_mul (η p q : ℝ) (hη : 0 ≤ η) (h : p ≤ 2 * q) :
    (1 / 2 : ℝ) * η * p ≤ η * q := by
  have hpq : (1 / 2 : ℝ) * p ≤ q := by linarith only [h]
  calc (1 / 2 : ℝ) * η * p = η * ((1 / 2 : ℝ) * p) := by ring
    _ ≤ η * q := mul_le_mul_of_nonneg_left hpq hη

/-- Scalar core of `potential_step_sub_le_of_quarter_bound`: for `x > η > 0` and `x' ≤ x/4 + K`
with `K ≥ 0`,
`η log (1 + x'/η) ≤ η log (1 + x/η) - η log (8/5) + K`. The contraction factor is `5/8`
(not the `9/16` of `scalar_contraction`, which is tuned to the `1/8` premise). -/
private theorem scalar_quarter (η x x' K : ℝ) (hη : 0 < η) (hx : η < x) (hx'0 : 0 ≤ x')
    (hK : 0 ≤ K) (hprop : x' ≤ 1 / 4 * x + K) :
    η * Real.log (1 + x' / η) ≤ η * Real.log (1 + x / η) - η * Real.log (8 / 5) + K := by
  have hηne : η ≠ 0 := hη.ne'
  have hx0 : 0 < x := lt_trans hη hx
  set A : ℝ := 1 + x / (4 * η) with hA
  have hA1 : 1 ≤ A := by
    have hpos : 0 < x / (4 * η) := by positivity
    rw [hA]; linarith only [hpos]
  have hA0 : 0 < A := lt_of_lt_of_le one_pos hA1
  have ht0 : 0 ≤ K / η := div_nonneg hK hη.le
  have hstep1 : 1 + x' / η ≤ A + K / η := by
    have h1 : x' / η ≤ (1 / 4 * x + K) / η := by gcongr
    have h2 : (1 / 4 * x + K) / η = x / (4 * η) + K / η := by field_simp
    rw [h2] at h1
    rw [hA]; linarith only [h1]
  have hstep2 : Real.log (A + K / η) ≤ Real.log A + K / η := by
    have hpos : 0 < (A + K / η) / A := div_pos (by linarith only [hA0, ht0]) hA0
    have h3 := Real.log_le_sub_one_of_pos hpos
    rw [Real.log_div (by linarith only [hA0, ht0]) hA0.ne'] at h3
    have h4 : (A + K / η) / A - 1 = K / η / A := by field_simp; ring
    rw [h4] at h3
    have h5 : K / η / A ≤ K / η := div_le_self ht0 hA1
    linarith only [h3, h5]
  have hx'η : 0 ≤ x' / η := div_nonneg hx'0 hη.le
  have hstep3 : Real.log (1 + x' / η) ≤ Real.log (A + K / η) :=
    Real.log_le_log (by linarith only [hx'η]) hstep1
  have hu : 1 < x / η := (one_lt_div hη).mpr hx
  have hA_le : A ≤ (1 + x / η) * (5 / 8) := by
    have hxa : x / (4 * η) = x / η / 4 := by field_simp
    rw [hA, hxa]; linarith only [hu]
  have hstep4 : Real.log A ≤ Real.log (1 + x / η) - Real.log (8 / 5) := by
    have h6 : Real.log A ≤ Real.log ((1 + x / η) * (5 / 8)) := Real.log_le_log hA0 hA_le
    have h7 : Real.log ((1 + x / η) * (5 / 8))
        = Real.log (1 + x / η) - Real.log (8 / 5) := by
      rw [Real.log_mul (by positivity) (by norm_num)]
      rw [show (5 / 8 : ℝ) = ((8 / 5 : ℝ))⁻¹ by norm_num, Real.log_inv]
      ring
    rw [h7] at h6; exact h6
  have hfin : Real.log (1 + x' / η) ≤ Real.log (1 + x / η) - Real.log (8 / 5) + K / η := by
    linarith only [hstep3, hstep2, hstep4]
  have h8 := mul_le_mul_of_nonneg_left hfin hη.le
  have h9 : η * (Real.log (1 + x / η) - Real.log (8 / 5) + K / η)
      = η * Real.log (1 + x / η) - η * Real.log (8 / 5) + K := by field_simp
  rw [h9] at h8; exact h8

/-- **Local variant of `potential_step_sub_le_of_exp_bound`** matching the premise that
`SelectionData.Selects`
supplies in its Alternative-1 service disjunct (`SelectionData.lean`):
`x' ≤ 1/4 * x + C * Δ̂_h(n)`.  Conclusion is the SAME shape as
`potential_step_sub_le_of_exp_bound`'s, so it plugs
into `exists_stop_of_potential` with the same `c` and the same charge.  Needs `d ≤ a` (the
weight already satisfies `4 Q max 1 C ≤ a C / d`; `d ≤ a` is an extra, freely enforceable
requirement on `weight_choice`'s `a`).  No `Q` and no growth bound are needed. -/
theorem potential_step_sub_le_of_quarter_bound {d : ℕ} (P : Measure (CoeffSpace d)) (γ : ℝ)
  (jStar : ℕ)
    (η a c C : ℝ) (m : Mat d) (k n : ℤ) (h : ℕ) (hd : 0 < d) (hη : 0 < η) (hC : 1 ≤ C)
    (ha : (d : ℝ) ≤ a) (hc : c = 1 / 2 * η * Real.log (16 / 9))
    (hx : η < profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n)
    (hx' : 0 ≤ profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k (n + h) +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar (n + h))
    (hΔ : 0 ≤ synchCharge P (Geometry.explicitRoundedGrid jStar m) (h : ℤ) n)
    (hprop : profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k (n + h) +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar (n + h) ≤
      1 / 4 * (profile P γ (Geometry.explicitRoundedGrid jStar m) jStar k n +
          determinantDrift P γ (Geometry.explicitRoundedGrid jStar m) jStar n) +
        C * synchCharge P (Geometry.explicitRoundedGrid jStar m) (h : ℤ) n) :
    potential P γ jStar η a m k (n + h) - potential P γ jStar η a m k n ≤
      -c + a * C / d * synchCharge P (Geometry.explicitRoundedGrid jStar m) (h : ℤ) n := by
  unfold potential
  set q := Geometry.explicitRoundedGrid jStar m with hq
  set x := profile P γ q jStar k n + determinantDrift P γ q jStar n with hxdef
  set x' := profile P γ q jStar k (n + h) + determinantDrift P γ q jStar (n + h) with hx'def
  set Δ := synchCharge P q (h : ℤ) n with hΔdef
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hC0 : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC
  have hCΔ : 0 ≤ C * Δ := mul_nonneg hC0.le hΔ
  have hscal := scalar_quarter η x x' (C * Δ) hη hx hx' hCΔ hprop
  have hlog : c ≤ η * Real.log (8 / 5) := by
    have h1 : Real.log (16 / 9 : ℝ) ≤ Real.log ((8 / 5 : ℝ) ^ (2 : ℕ)) := by
      apply Real.log_le_log (by norm_num); norm_num
    rw [Real.log_pow] at h1
    push_cast at h1
    rw [hc]
    exact half_mul_le_mul_of_le_two_mul η (Real.log (16 / 9)) (Real.log (8 / 5)) hη.le h1
  have hcoef : C * Δ ≤ a * C / d * Δ := by
    have hle : C ≤ a * C / d := by
      rw [le_div_iff₀ hdR]
      calc C * d ≤ C * a := mul_le_mul_of_nonneg_left ha hC0.le
        _ = a * C := by ring
    exact mul_le_mul_of_nonneg_right hle hΔ
  linarith only [hscal, hlog, hcoef]

/-! ## §3 Four new lemmas -/

/-- `weight_choice` strengthened so the witness weight also dominates `d` (as a real number):
replace the witness by `max a d`, using that each of the three conclusions is monotone
increasing in `a` when `C, ε, σ > 0`. -/
theorem weight_choice_ge_d (d : ℕ) (hd : 0 < d) (C Q ε σ c L H h : ℝ) (hC : 0 < C) (hε : 0 < ε)
    (hσ : 0 < σ) :
    ∃ a : ℝ, 1 ≤ a ∧ (d : ℝ) ≤ a ∧ 4 * Q * max 1 C ≤ a * C / d ∧
      Real.log (1 + C * h) + c ≤ a * ε / 2 ∧
      4 * (Real.log (1 + 2 * C * L) + Real.log (1 + C * H) + c) ≤ a * C * ε * σ := by
  obtain ⟨a, ha1, ha2, ha3, ha4⟩ := weight_choice d hd C Q ε σ c L H h hC hε hσ
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  refine ⟨max a d, ha1.trans (le_max_left _ _), le_max_right _ _, ?_, ?_, ?_⟩
  · have hCd : 0 ≤ C / d := div_nonneg hC.le hdR.le
    calc 4 * Q * max 1 C ≤ a * C / d := ha2
      _ = a * (C / d) := by ring
      _ ≤ max a (d : ℝ) * (C / d) := mul_le_mul_of_nonneg_right (le_max_left _ _) hCd
      _ = max a (d : ℝ) * C / d := by ring
  · calc Real.log (1 + C * h) + c ≤ a * ε / 2 := ha3
      _ = a * (ε / 2) := by ring
      _ ≤ max a (d : ℝ) * (ε / 2) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = max a (d : ℝ) * ε / 2 := by ring
  · calc 4 * (Real.log (1 + 2 * C * L) + Real.log (1 + C * H) + c) ≤ a * C * ε * σ := ha4
      _ = a * (C * ε * σ) := by ring
      _ ≤ max a (d : ℝ) * (C * ε * σ) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ = max a (d : ℝ) * C * ε * σ := by ring

/-- The selection step `η = S.eta ε σ = S.c * ε * σ` never exceeds `1`, since `S.c < 1` and
`ε, σ ≤ 1`. -/
theorem selectionData_eta_le_one (S : SelectionData) (ε σ : ℝ)
    (hε : ε ∈ Set.Ioc (0 : ℝ) S.eps0) (hσ : σ ∈ Set.Ioc (0 : ℝ) ε) :
    S.eta ε σ ≤ 1 := by
  obtain ⟨hε0, hεle⟩ := hε
  obtain ⟨hσ0, hσle⟩ := hσ
  obtain ⟨_, hc1⟩ := S.c_mem
  obtain ⟨_, heps1⟩ := S.eps0_mem
  have hεle1 : ε ≤ 1 := hεle.trans heps1.le
  have hσle1 : σ ≤ 1 := hσle.trans hεle1
  have h1 : S.c * ε ≤ 1 := by
    have h := mul_le_mul hc1.le hεle1 hε0.le zero_le_one
    simpa using h
  unfold SelectionData.eta
  calc S.c * ε * σ ≤ 1 * σ := mul_le_mul_of_nonneg_right h1 hσ0.le
    _ = σ := one_mul σ
    _ ≤ 1 := hσle1

/-- If `(d:ℝ)⁻¹ * Δ > ε * σ` then `d * ε * σ < Δ`. -/
theorem det_bridge_gt (d : ℕ) (hd : 0 < d) (ε σ Δ : ℝ) (h : (d : ℝ)⁻¹ * Δ > ε * σ) :
    (d : ℝ) * ε * σ < Δ := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have h' : ε * σ < (d : ℝ)⁻¹ * Δ := h
  calc (d : ℝ) * ε * σ = (d : ℝ) * (ε * σ) := by ring
    _ < (d : ℝ) * ((d : ℝ)⁻¹ * Δ) := mul_lt_mul_of_pos_left h' hdR
    _ = Δ := mul_inv_cancel_left₀ hdR.ne' Δ

/-- If `¬((d:ℝ)⁻¹ * Δ < σ)` then `d * σ ≤ Δ`. -/
theorem det_bridge_not_lt (d : ℕ) (hd : 0 < d) (σ Δ : ℝ) (h : ¬ ((d : ℝ)⁻¹ * Δ < σ)) :
    (d : ℝ) * σ ≤ Δ := by
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have h' : σ ≤ (d : ℝ)⁻¹ * Δ := not_lt.mp h
  calc (d : ℝ) * σ ≤ (d : ℝ) * ((d : ℝ)⁻¹ * Δ) := mul_le_mul_of_nonneg_left h' hdR.le
    _ = Δ := mul_inv_cancel_left₀ hdR.ne' Δ

end

end HCPolySupport.HighContrast.Multiscale
