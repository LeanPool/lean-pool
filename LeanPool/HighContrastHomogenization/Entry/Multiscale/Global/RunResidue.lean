/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.Global.RunStepAny
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.AdaptedCellMeasurability

/-!
# High-contrast homogenization: Entry.Multiscale.Global.RunResidue

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The residue of the run assembly

`GlobalRunGapObligation` is everything in the global selection run below the two constant
choices: for every horizon `H` and scale `σ` it asks for a positive profile constant and a
positive lower scale budget such that every coefficient law with the dagger ellipticity and
every admissible `jStar` satisfies the `SelectedOutput` estimate. Its discharge
`global_run_residue` produces the constant `CS` of `comparison_choice` and the source
constant `Csrc`, and hands each consumer the source threshold at every constant at most
`Csrc`. This is the residue of the run that establishes Proposition `p.global.selection`, and
through that proposition it is part of the assembly of Theorem `t.polynomial.entry`. The
assembly of `global_run` from it is in `HCPoly.Entry.Multiscale.Global.RunAssembly`; the two
`Selects` projections the run needs and the per-step case analysis `run_step_any` are in
`HCPoly.Entry.Multiscale.Global.RunStepAny`.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean aspectRatio blockLogDet)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator

noncomputable section

/-! ## §3 The residue of `global_run_of_gap` below the constant choices -/

/-- Everything in `global_run_of_gap` downstream of the choice of `ε` by `comparison_choice`
and of the source constant `Csrc`, as ONE named obligation. Its user is handed, at every
consumer, the discharged source threshold for EVERY constant `≤ Csrc`. -/
@[expose]
def GlobalRunGapObligation (d : ℕ) (γ : ℝ) (S : SelectionData) (ε Csrc : ℝ) : Prop :=
  ∀ H : ℕ, max 4 S.h ≤ H →
    ∃ Cprof : ℝ, 0 < Cprof ∧
      ∀ σ : ℝ, σ ∈ Set.Ioc (0 : ℝ) ε →
        ∃ C : ℝ, 0 < C ∧
          ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
            (Src : CoeffSpace d → ℝ),
            IsProbabilityMeasure P →
            IsStationaryLaw P →
            IsUnitRangeLaw P →
            CoarseEllipticityDagger P γ E Ψ K Src →
            ∀ B : ℝ, S.B0 ε σ ≤ B →
              ∀ jStar : ℕ, 2 * d ≤ 3 ^ jStar →
                ⌈C * (B + 1) * Real.logb 3 (2 + aspectRatio E) +
                    Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
                  (∀ C' : ℝ, 0 < C' → C' ≤ Csrc → ⌈C' * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ)) →
                    SelectedOutput P γ ε σ Cprof C E H jStar B

/-! ### Scalar inputs of the assembly -/

/-- `1/2 ≤ log₃(2+Π)`. -/
private theorem half_le_logb_three_two_add (AR : ℝ) (hAR : 0 ≤ AR) :
    1 / 2 ≤ Real.logb 3 (2 + AR) := by
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  rw [← Real.log_div_log, le_div_iff₀ hl3]
  have h1 : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
  have h2 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have h3 : Real.log 2 ≤ Real.log (2 + AR) :=
    Real.log_le_log (by norm_num) (by linarith only [hAR])
  linarith only [h1, h2, h3]

private theorem logb_three_mul (AR : ℝ) :
    Real.log 3 * Real.logb 3 (2 + AR) = Real.log (2 + AR) := by
  have h3 : Real.log 3 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [Real.logb]
  field_simp

private theorem log_three_le_two : Real.log 3 ≤ 2 := by
  have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 3 by norm_num)
  linarith only [h]

/-- `log(24Π) ≤ 48 log₃(2+Π)` for every positive aspect ratio. -/
private theorem log24_le (AR : ℝ) (hAR : 0 < AR) :
    Real.log (24 * AR) ≤ 48 * Real.logb 3 (2 + AR) := by
  have hy : 1 / 2 ≤ Real.logb 3 (2 + AR) := half_le_logb_three_two_add AR hAR.le
  have h24 : Real.log 24 ≤ 23 := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 24 by norm_num); linarith only [h]
  have hsplit : Real.log (24 * AR) = Real.log 24 + Real.log AR :=
    Real.log_mul (by norm_num) (ne_of_gt hAR)
  have hlAR : Real.log AR ≤ Real.log (2 + AR) :=
    Real.log_le_log hAR (by linarith only [hAR])
  have hmul := logb_three_mul AR
  have h3 := log_three_le_two
  nlinarith only [hy, h24, hsplit, hlAR, hmul, h3]

/-- `log(2+4Π) ≤ 8 log₃(2+Π)`. -/
private theorem log_two_add_four_le (AR : ℝ) (hAR : 0 ≤ AR) :
    Real.log (2 + 4 * AR) ≤ 8 * Real.logb 3 (2 + AR) := by
  have hy : 1 / 2 ≤ Real.logb 3 (2 + AR) := half_le_logb_three_two_add AR hAR
  have hle : Real.log (2 + 4 * AR) ≤ Real.log (4 * (2 + AR)) :=
    Real.log_le_log (by linarith only [hAR]) (by linarith only [hAR])
  have hsplit : Real.log (4 * (2 + AR)) = Real.log 4 + Real.log (2 + AR) :=
    Real.log_mul (by norm_num) (by positivity)
  have h4 : Real.log 4 ≤ 3 := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < 4 by norm_num); linarith only [h]
  have hmul := logb_three_mul AR
  have h3 := log_three_le_two
  nlinarith only [hy, hle, hsplit, h4, hmul, h3]

/-- `0 ≤ log₃(2K)` from `1 < K`. -/
private theorem logb_three_two_mul_nonneg (K : ℝ) (hK : 1 < K) :
    0 ≤ Real.logb 3 (2 * K) :=
  Real.logb_nonneg (by norm_num) (by linarith only [hK])

/-- The bundled lower scale of `global_run` at the residue's `C` implies the
`containment_arith` threshold at every `Ccont ≤ C`. -/
private theorem containment_threshold_of_bundled (C Ccont Csrc B K AR : ℝ) (jStar : ℕ)
    (_hCcont : 0 ≤ Ccont) (hCcC : Ccont ≤ C) (hB : 1 ≤ B) (hAR : 0 ≤ AR) (hK : 1 < K)
    (hCsrc : 0 < Csrc)
    (hj : ⌈C * (B + 1) * Real.logb 3 (2 + AR) + Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ)) :
    ⌈Ccont * (B + 1) * Real.logb 3 (2 + AR)⌉ ≤ (jStar : ℤ) := by
  have hx : 0 ≤ Real.logb 3 (2 + AR) :=
    Real.logb_nonneg (by norm_num) (by linarith only [hAR])
  have hKl : 0 ≤ Real.logb 3 (2 * K) := logb_three_two_mul_nonneg K hK
  have hsrc0 : 0 ≤ Csrc * Real.logb 3 (2 * K) := mul_nonneg hCsrc.le hKl
  have hmono : Ccont * (B + 1) * Real.logb 3 (2 + AR) ≤
      C * (B + 1) * Real.logb 3 (2 + AR) + Csrc * Real.logb 3 (2 * K) := by
    have hB1 : 0 ≤ B + 1 := by linarith only [hB]
    have hstep : Ccont * (B + 1) ≤ C * (B + 1) :=
      mul_le_mul_of_nonneg_right hCcC hB1
    exact le_trans (mul_le_mul_of_nonneg_right hstep hx) (le_add_of_nonneg_right hsrc0)
  exact le_trans (Int.ceil_le_ceil hmono) hj

/-- `run_initial`'s `harith`, uniformly in the aspect ratio. -/
private theorem initial_harith (Q Cdet ag t : ℝ) (hQ : 0 ≤ Q) (hCdet : 0 ≤ Cdet)
    (hag : 0 ≤ ag) (ht : 0 ≤ t) :
    ∀ AR Δ : ℝ, 0 ≤ AR → 0 ≤ Δ → Δ ≤ Cdet * Real.log (2 + AR) →
      t + Q * Δ + ag * Real.log (2 + 4 * AR) ≤
        (2 * t + 2 * (Q * Cdet) + 8 * ag) * Real.logb 3 (2 + AR) := by
  intro AR Δ hAR hΔ hΔle
  have hy : 1 / 2 ≤ Real.logb 3 (2 + AR) := half_le_logb_three_two_add AR hAR
  have hmul := logb_three_mul AR
  have h3 := log_three_le_two
  have h4 := log_two_add_four_le AR hAR
  have hQC : 0 ≤ Q * Cdet := mul_nonneg hQ hCdet
  have hy0 : (0:ℝ) ≤ Real.logb 3 (2 + AR) := le_trans (by norm_num) hy
  have hstep1 : Q * Δ ≤ Q * Cdet * Real.log (2 + AR) :=
    calc Q * Δ ≤ Q * (Cdet * Real.log (2 + AR)) := mul_le_mul_of_nonneg_left hΔle hQ
      _ = Q * Cdet * Real.log (2 + AR) := by ring
  have hlog2 : Real.log (2 + AR) ≤ 2 * Real.logb 3 (2 + AR) :=
    calc Real.log (2 + AR) = Real.log 3 * Real.logb 3 (2 + AR) := hmul.symm
      _ ≤ 2 * Real.logb 3 (2 + AR) := mul_le_mul_of_nonneg_right h3 hy0
  have hstep2 : Q * Cdet * Real.log (2 + AR) ≤ 2 * (Q * Cdet) * Real.logb 3 (2 + AR) :=
    calc Q * Cdet * Real.log (2 + AR) ≤ Q * Cdet * (2 * Real.logb 3 (2 + AR)) :=
          mul_le_mul_of_nonneg_left hlog2 hQC
      _ = 2 * (Q * Cdet) * Real.logb 3 (2 + AR) := by ring
  have hstep3 : ag * Real.log (2 + 4 * AR) ≤ 8 * ag * Real.logb 3 (2 + AR) :=
    calc ag * Real.log (2 + 4 * AR) ≤ ag * (8 * Real.logb 3 (2 + AR)) :=
          mul_le_mul_of_nonneg_left h4 hag
      _ = 8 * ag * Real.logb 3 (2 + AR) := by ring
  have hstep0 : t ≤ 2 * t * Real.logb 3 (2 + AR) :=
    calc t = 2 * t * (1 / 2) := by ring
      _ ≤ 2 * t * Real.logb 3 (2 + AR) :=
          mul_le_mul_of_nonneg_left hy (by linarith only [ht])
  have hmain : t + Q * Δ + ag * Real.log (2 + 4 * AR) ≤
      2 * t * Real.logb 3 (2 + AR) + 2 * (Q * Cdet) * Real.logb 3 (2 + AR) +
        8 * ag * Real.logb 3 (2 + AR) :=
    add_le_add (add_le_add hstep0 (le_trans hstep1 hstep2)) hstep3
  calc t + Q * Δ + ag * Real.log (2 + 4 * AR)
      ≤ 2 * t * Real.logb 3 (2 + AR) + 2 * (Q * Cdet) * Real.logb 3 (2 + AR) +
          8 * ag * Real.logb 3 (2 + AR) := hmain
    _ = (2 * t + 2 * (Q * Cdet) + 8 * ag) * Real.logb 3 (2 + AR) := by ring

/-- Shifting the containment budget by one generation costs `ε / log 3 ≤ 1`. -/
private theorem shift_budget (u v e Lg t jS : ℝ) (hLg : 1 < Lg) (he : 0 < e) (he1 : e ≤ 1)
    (h : u + 1 + (v + e * (t + 1) / Lg) ≤ 2 * jS) :
    u + (v + e * (t + 2) / Lg) ≤ 2 * jS := by
  have hLg0 : 0 < Lg := by linarith only [hLg]
  have he1' : e / Lg ≤ 1 := by rw [div_le_one hLg0]; linarith only [he1, hLg]
  have he2 : e * (t + 2) / Lg = e * (t + 1) / Lg + e / Lg := by field_simp; ring
  linarith only [h, he1', he2]

private theorem run_horizon_ceiling_properties (A x : ℝ) (hA : 0 ≤ A) (hx : 0 ≤ x) :
    let J : ℕ := ⌈A * x⌉₊
    (J : ℤ) = ⌈A * x⌉ ∧ (J : ℝ) = ((⌈A * x⌉ : ℤ) : ℝ) ∧ A * x ≤ (J : ℝ) := by
  intro J
  have hJZ : (J : ℤ) = ⌈A * x⌉ := Int.natCast_ceil_eq_ceil (mul_nonneg hA hx)
  have hJR : (J : ℝ) = ((⌈A * x⌉ : ℤ) : ℝ) := by rw [← hJZ]; push_cast; ring
  exact ⟨hJZ, hJR, Nat.le_ceil _⟩

private theorem run_selection_charge_positive (S : SelectionData) (ε σ : ℝ)
    (hε : 0 < ε) (hσ : 0 < σ) :
    0 < 1 / 2 * S.eta ε σ * Real.log (16 / 9) := by
  have hc : 0 < S.c := S.c_mem.1
  have hlog : 0 < Real.log (16 / 9) := Real.log_pos (by norm_num)
  unfold SelectionData.eta
  positivity

private theorem run_containment_budget {d : ℕ} (S : SelectionData) (ε σ B Cini x : ℝ)
    (H jStar : ℕ) (n₀ : ℤ) (J : ℕ)
    (hn₀' : n₀ ≤ (jStar : ℤ) + ⌈B * x⌉ + ⌈Cini * x⌉)
    (hctRaw : (jStar : ℝ) + ((⌈B * x⌉ : ℤ) : ℝ) + ((⌈Cini * x⌉ : ℤ) : ℝ) +
      (2 * (S.L ε σ : ℝ) + (H : ℝ) + (S.h : ℝ)) * ((J : ℝ) + 2) +
      ((⌈Real.logb 3 (2 * Real.sqrt (4 * (d : ℝ))) +
        ε * ((J : ℝ) + 1) / Real.log 3⌉ : ℤ) : ℝ) ≤ 2 * (jStar : ℝ)) :
    ∀ j : ℤ,
      j ≤ n₀ + (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * ((J : ℤ) + 2) →
      (j : ℝ) + (Real.logb 3 (2 * Real.sqrt (4 * (d : ℝ))) + ε * ((J : ℝ) + 1) / Real.log 3) ≤
        2 * (jStar : ℝ) := by
  intro j hj
  have hjR : (j : ℝ) ≤ (n₀ : ℝ) +
      (2 * (S.L ε σ : ℝ) + (H : ℝ) + (S.h : ℝ)) * ((J : ℝ) + 2) := by
    have := hj
    have hc2 : ((n₀ + (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * ((J : ℤ) + 2) : ℤ) : ℝ)
        = (n₀ : ℝ) + (2 * (S.L ε σ : ℝ) + (H : ℝ) + (S.h : ℝ)) * ((J : ℝ) + 2) := by
      push_cast; ring
    have h3 : ((j : ℤ) : ℝ) ≤
        ((n₀ + (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * ((J : ℤ) + 2) : ℤ) : ℝ) := by
      exact_mod_cast hj
    rw [hc2] at h3; exact h3
  have hn₀R : (n₀ : ℝ) ≤ (jStar : ℝ) + ((⌈B * x⌉ : ℤ) : ℝ) + ((⌈Cini * x⌉ : ℤ) : ℝ) := by
    have h3 : ((n₀ : ℤ) : ℝ) ≤
        (((jStar : ℤ) + ⌈B * x⌉ + ⌈Cini * x⌉ : ℤ) : ℝ) := by exact_mod_cast hn₀'
    push_cast at h3 ⊢; linarith only [h3]
  have hceil := Int.le_ceil
    (Real.logb 3 (2 * Real.sqrt (4 * (d : ℝ))) +
      ε * ((J : ℝ) + 1) / Real.log 3)
  linarith only [hctRaw, hceil, hjR, hn₀R]

private theorem run_integer_scale_budget (S : SelectionData) (ε σ B Cini Csc C x : ℝ)
    (H J : ℕ) (hx0 : 0 ≤ x) (hCscC : Csc ≤ C)
    (hsc : ((⌈B * x⌉ : ℤ) : ℝ) + ((⌈Cini * x⌉ : ℤ) : ℝ) +
      (2 * (S.L ε σ : ℝ) + (H : ℝ) + (S.h : ℝ)) * ((J : ℝ) + 2) +
        (S.L ε σ : ℝ) + (H : ℝ) ≤ ((⌈(B + Csc) * x⌉ : ℤ) : ℝ)) :
    ⌈B * x⌉ + ⌈Cini * x⌉ +
      (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * ((J : ℤ) + 2) + (S.L ε σ : ℤ) + (H : ℤ) ≤
    ⌈(B + C) * x⌉ := by
  have hmono : ⌈(B + Csc) * x⌉ ≤ ⌈(B + C) * x⌉ :=
    Int.ceil_le_ceil (mul_le_mul_of_nonneg_right (by linarith only [hCscC] : B + Csc ≤ B + C) hx0)
  have hZ : ⌈B * x⌉ + ⌈Cini * x⌉ +
      (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * ((J : ℤ) + 2) + (S.L ε σ : ℤ) + (H : ℤ) ≤
      ⌈(B + Csc) * x⌉ := by
    have hR : (((⌈B * x⌉ + ⌈Cini * x⌉ +
        (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * ((J : ℤ) + 2) + (S.L ε σ : ℤ) +
        (H : ℤ) : ℤ)) : ℝ) ≤ ((⌈(B + Csc) * x⌉ : ℤ) : ℝ) := by
      push_cast
      linarith only [hsc]
    exact_mod_cast hR
  omega

private theorem run_initial_budget_constants (d Q h : ℕ) (a Csel Cgeom w c : ℝ)
    (ha1 : 1 ≤ a) (hCgeom : 0 < Cgeom) (hw0 : 0 ≤ w) (hcpos : 0 < c) (hh1 : 1 ≤ h) :
    let Cdet := 48 * (d : ℝ) / Real.log 3
    let Ctop := Real.log (1 + max 1 Csel * (h : ℝ))
    let Cpot := 2 * Ctop + 2 * ((Q : ℝ) * Cdet) + 8 * (a * Cgeom)
    let C₁ := (Cpot + 48 * w * ((h : ℝ) + 2) * (d : ℝ)) / c
    0 ≤ Cdet ∧ 0 ≤ Ctop ∧ 0 ≤ Cpot ∧ 0 ≤ C₁ := by
  intro Cdet Ctop Cpot C₁
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hQ0 : (0 : ℝ) ≤ (Q : ℝ) := Nat.cast_nonneg _
  have hhR0 : (0 : ℝ) ≤ (h : ℝ) := Nat.cast_nonneg _
  have hdR : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
  have hCdetdef : Cdet = 48 * (d : ℝ) / Real.log 3 := rfl
  have hCdet0 : 0 ≤ Cdet := by
    rw [hCdetdef]; exact div_nonneg (by positivity) hlog3pos.le
  have hCtopdef : Ctop = Real.log (1 + max 1 Csel * (h : ℝ)) := rfl
  have hCtop0 : 0 ≤ Ctop := by
    have hM : (1 : ℝ) ≤ max 1 Csel := le_max_left _ _
    have hhR : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh1
    have hmul : (0 : ℝ) ≤ max 1 Csel * (h : ℝ) :=
      mul_nonneg (by linarith only [hM]) (by linarith only [hhR])
    rw [hCtopdef]
    exact Real.log_nonneg (by linarith only [hmul])
  have hCpotdef : Cpot = 2 * Ctop + 2 * ((Q : ℝ) * Cdet) + 8 * (a * Cgeom) := rfl
  have hCpot0 : 0 ≤ Cpot := by
    rw [hCpotdef]
    have h1 : 0 ≤ (Q : ℝ) * Cdet := mul_nonneg hQ0 hCdet0
    have h2 : 0 ≤ a * Cgeom := mul_nonneg (by linarith only [ha1]) hCgeom.le
    linarith only [hCtop0, h1, h2]
  have hC₁def : C₁ = (Cpot + 48 * w * ((h : ℝ) + 2) * (d : ℝ)) / c := rfl
  have hC₁0 : 0 ≤ C₁ := by
    rw [hC₁def]
    refine div_nonneg ?_ hcpos.le
    have h1 : 0 ≤ 48 * w * ((h : ℝ) + 2) * (d : ℝ) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 48) hw0)
        (by linarith only [hhR0])) hdR
    linarith only [hCpot0, h1]
  exact ⟨hCdet0, hCtop0, hCpot0, hC₁0⟩

private theorem run_stopping_geometry_bounds {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (γ : ℝ) (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hce : CoarseEllipticityDagger P γ E Ψ K Src)
    (S : SelectionData) (ε σ B C Cec : ℝ) (H jStar : ℕ) (n₀ : ℤ) (J : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (hH4 : 4 ≤ H) (hh1 : 1 ≤ S.h)
    (hL1 : 1 ≤ S.L ε σ) (hεpos : 0 < ε) (hCecC : Cec ≤ C)
    (hExponential : Real.exp (2 * ε * ((J : ℝ) + 1)) ≤ (2 + aspectRatio E) ^ Cec)
    (hbudget : ∀ j : ℤ,
      j + 1 ≤ n₀ + (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * ((J : ℤ) + 2) →
      (j : ℝ) + (Real.logb 3 (2 * Real.sqrt (4 * (d : ℝ))) +
        ε * ((J : ℝ) + 2) / Real.log 3) ≤ 2 * (jStar : ℝ))
    (st : RunState P γ S ε σ B E H jStar n₀) (hiJ : st.i ≤ J)
    (heq : geometryUpdate ε st.m (explicitCanonicalMetric
      (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
        (st.n + 2 * (S.L ε σ : ℤ)))) =
      explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
        (st.n + 2 * (S.L ε σ : ℤ)))) :
    ((‖explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
          (st.n + 2 * (S.L ε σ : ℤ)))‖ *
      ‖(explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
        (st.n + 2 * (S.L ε σ : ℤ))))⁻¹‖) ^ ((1 : ℝ) / 2) ≤ (2 + aspectRatio E) ^ C) ∧
      (HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar (geometryUpdate ε
    st.m
        (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
          (st.n + 2 * (S.L ε σ : ℤ)))))) (st.n + (S.L ε σ : ℤ) + (H : ℤ)) ⊆
      HighContrast.centeredCube d (2 * (jStar : ℤ))) := by
  have hAR0 : 0 < aspectRatio E := (Annealed.aspectRatio_pos_and_three_le hce).1
  have hJ0 : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg _
  have hLz : (1 : ℤ) ≤ (S.L ε σ : ℤ) := by exact_mod_cast hL1
  have hHz : (4 : ℤ) ≤ (H : ℤ) := by exact_mod_cast hH4
  have hhz : (1 : ℤ) ≤ (S.h : ℤ) := by exact_mod_cast hh1
  have hDnn : (0 : ℤ) ≤ 2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ) := by omega
  have hexpD : (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * ((J : ℤ) + 2)
      = (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * ((J : ℤ) + 1) +
        (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) := by ring
  have hmStar := Geometry.explicitCanonicalMetric_adaptedMean_posDef d hd P γ E Ψ K Src hstat hce
    jStar hjStar st.m st.hm (st.n + 2 * (S.L ε σ : ℤ))
  have hmPlus := Geometry.geometryUpdate_posDef st.hm hmStar ε
  have hprJ : projectiveDistance (1 : Mat d)
      (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
        (st.n + 2 * (S.L ε σ : ℤ)))) ≤ ε * ((J : ℝ) + 2) := by
    have htri := Geometry.projectiveDistance_triangle
      (Matrix.PosDef.one : (1 : Mat d).PosDef) st.hm hmStar
    have hstep := Geometry.projectiveDistance_geometryUpdate_le st.hm hmStar hεpos
    rw [heq] at hstep
    have hiR : ((st.i : ℝ)) ≤ (J : ℝ) := by exact_mod_cast hiJ
    have hpr := st.hpr
    have hmul : ε * ((st.i : ℝ)) ≤ ε * (J : ℝ) := mul_le_mul_of_nonneg_left hiR hεpos.le
    linarith only [htri, hstep, hpr, hmul]
  have heccStar : 1 / 2 * Real.log (‖explicitCanonicalMetric (adaptedMean P
        (Geometry.explicitRoundedGrid jStar st.m) (st.n + 2 * (S.L ε σ : ℤ)))‖ *
      ‖(explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
        (st.n + 2 * (S.L ε σ : ℤ))))⁻¹‖) ≤ ε * ((J : ℝ) + 2) := by
    rwa [Geometry.projectiveDistance_one_eq_log_eccentricity hmStar] at hprJ
  have hecc' : (‖explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
          (st.n + 2 * (S.L ε σ : ℤ)))‖ *
      ‖(explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
        (st.n + 2 * (S.L ε σ : ℤ))))⁻¹‖) ^ ((1 : ℝ) / 2) ≤ (2 + aspectRatio E) ^ C := by
    have hsq := Geometry.eccentricity_eq_exp_half_log hmStar
    have hle1 : Real.exp (1 / 2 * Real.log (‖explicitCanonicalMetric (adaptedMean P
          (Geometry.explicitRoundedGrid jStar st.m) (st.n + 2 * (S.L ε σ : ℤ)))‖ *
        ‖(explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
          (st.n + 2 * (S.L ε σ : ℤ))))⁻¹‖)) ≤ Real.exp (2 * ε * ((J : ℝ) + 1)) :=
      Real.exp_le_exp.mpr (by
        have hεJ : (0 : ℝ) ≤ ε * (J : ℝ) := mul_nonneg hεpos.le hJ0
        linarith only [heccStar, hεJ])
    have hec := hExponential
    have hmono : ((2 : ℝ) + aspectRatio E) ^ Cec ≤ (2 + aspectRatio E) ^ C :=
      Real.rpow_le_rpow_of_exponent_le (by linarith only [hAR0]) hCecC
    rw [← Real.sqrt_eq_rpow, hsq]
    calc Real.exp (1 / 2 * Real.log (‖explicitCanonicalMetric (adaptedMean P
            (Geometry.explicitRoundedGrid jStar st.m) (st.n + 2 * (S.L ε σ : ℤ)))‖ *
          ‖(explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
            (st.n + 2 * (S.L ε σ : ℤ))))⁻¹‖)) ≤ Real.exp (2 * ε * ((J : ℝ) + 1)) := hle1
      _ ≤ (2 + aspectRatio E) ^ Cec := hec
      _ ≤ (2 + aspectRatio E) ^ C := hmono
  -- the output containment
  have heccPlus : 1 / 2 * Real.log (‖geometryUpdate ε st.m (explicitCanonicalMetric
        (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m) (st.n + 2 * (S.L ε σ : ℤ))))‖ *
      ‖(geometryUpdate ε st.m (explicitCanonicalMetric
        (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
          (st.n + 2 * (S.L ε σ : ℤ)))))⁻¹‖) ≤ ε * ((J : ℝ) + 2) := by
    rw [heq]; exact heccStar
  have hgenJ : st.n ≤ n₀ + (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * ((J : ℤ) + 1) := by
    have hg := st.hgen
    have hiZ : ((st.i : ℤ) + 1) ≤ ((J : ℤ) + 1) := by
      have : (st.i : ℤ) ≤ (J : ℤ) := by exact_mod_cast hiJ
      omega
    linarith only [hg, mul_le_mul_of_nonneg_left hiZ hDnn]
  have hstepbound : st.n + (S.L ε σ : ℤ) + (H : ℤ) + 1 ≤
      n₀ + (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * ((J : ℤ) + 2) := by
    rw [hexpD]
    linarith only [hgenJ, hLz, hHz, hhz]
  have hcontOut : HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar (geometryUpdate ε
    st.m
        (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar st.m)
          (st.n + 2 * (S.L ε σ : ℤ)))))) (st.n + (S.L ε σ : ℤ) + (H : ℤ)) ⊆
      HighContrast.centeredCube d (2 * (jStar : ℤ)) := by
    have hfull := run_entry_containment hd jStar hjStar _ _ hmPlus hmPlus
      (st.n + (S.L ε σ : ℤ) + (H : ℤ)) (st.n + (S.L ε σ : ℤ) + (H : ℤ))
      (ε * ((J : ℝ) + 2)) (mul_nonneg hεpos.le (by linarith only [hJ0])) heccPlus heccPlus
      (hbudget _ hstepbound) (hbudget _ hstepbound)
    exact le_trans Set.subset_union_left hfull
  exact ⟨hecc', hcontOut⟩

private theorem run_initial_startup_bound {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (γ : ℝ) (P : Measure (CoeffSpace d)) [IsProbabilityMeasure P]
    (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (Src : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hce : CoarseEllipticityDagger P γ E Ψ K Src)
    (S : SelectionData) (ε σ B Csel : ℝ) (H jStar : ℕ) (n₀ : ℤ) (J : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (hH4 : 4 ≤ H) (hh1 : 1 ≤ S.h)
    (hL1 : 1 ≤ S.L ε σ) (hεpos : 0 < ε) (hLR : 0 < (S.L ε σ : ℝ))
    (hB1 : 1 ≤ B) (hx0 : 0 ≤ Real.logb 3 (2 + aspectRatio E))
    (hn₀ : (jStar : ℤ) + ⌈B * Real.logb 3 (2 + aspectRatio E)⌉ ≤ n₀)
    (hbudget : ∀ j : ℤ,
      j + 1 ≤ n₀ + (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * ((J : ℤ) + 2) →
      (j : ℝ) + (Real.logb 3 (2 * Real.sqrt (4 * (d : ℝ))) +
        ε * ((J : ℝ) + 2) / Real.log 3) ≤ 2 * (jStar : ℝ))
    (hselection : (jStar : ℤ) ≤ n₀ →
      (1 / 2 * Real.log (‖(1 : Mat d)‖ * ‖(1 : Mat d)⁻¹‖) ≤
      ε / (S.L ε σ : ℝ) * ((n₀ : ℝ) - (jStar : ℝ) -
        ((⌈B * Real.logb 3 (2 + aspectRatio E)⌉ : ℤ) : ℝ))) →
      (HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar (1 : Mat d))
        (n₀ + 2 * (S.L ε σ : ℤ)) ∪
      HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar (geometryUpdate ε (1 : Mat d)
        (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar (1 : Mat d))
          (n₀ + 2 * (S.L ε σ : ℤ)))))) (n₀ + (S.L ε σ : ℤ)) ⊆
      HighContrast.centeredCube d (2 * (jStar : ℤ))) →
      ((profile P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar n₀
          (n₀ + (S.h : ℤ)) +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar (n₀ + (S.h :
          ℤ)) ≤
      Csel * (profile P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar n₀ n₀ +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar n₀ +
        Real.exp ((bigQ d γ : ℝ) *
          detIncrement P (Geometry.explicitRoundedGrid jStar (1 : Mat d)) n₀ (n₀ + (S.h : ℤ))) -
            1)) ∧
      (n₀ = n₀ + (S.h : ℤ) →
        profile P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar (n₀ + (S.h : ℤ))
            (n₀ + (S.h : ℤ)) +
          determinantDrift P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar
            (n₀ + (S.h : ℤ)) ≤ 1))) :
    (profile P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar n₀
          (n₀ + (S.h : ℤ)) +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar (n₀ + (S.h :
          ℤ)) ≤
      max 1 Csel * (profile P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar n₀ n₀ +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar n₀ +
        Real.exp ((bigQ d γ : ℝ) *
          detIncrement P (Geometry.explicitRoundedGrid jStar (1 : Mat d)) n₀ (n₀ + (S.h : ℤ))) -
            1)) ∧
      (n₀ = n₀ + (S.h : ℤ) →
        profile P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar
            (n₀ + (S.h : ℤ)) (n₀ + (S.h : ℤ)) +
          determinantDrift P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar
            (n₀ + (S.h : ℤ)) ≤ 1) := by
  have hlog3pos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hJ0 : (0 : ℝ) ≤ (J : ℝ) := Nat.cast_nonneg _
  have hQ0 : (0 : ℝ) ≤ (bigQ d γ : ℝ) := Nat.cast_nonneg _
  let x := Real.logb 3 (2 + aspectRatio E)
  have hjn₀ : (jStar : ℤ) ≤ n₀ := by
    have hceil0 : (0 : ℤ) ≤ ⌈B * x⌉ := Int.ceil_nonneg (mul_nonneg (by linarith only [hB1]) hx0)
    omega
  have hone1 : (1 : Mat d).PosDef := Geometry.one_posDef d
  have hecc1 : 1 / 2 * Real.log (‖(1 : Mat d)‖ * ‖(1 : Mat d)⁻¹‖) ≤
      ε / (S.L ε σ : ℝ) * ((n₀ : ℝ) - (jStar : ℝ) - ((⌈B * x⌉ : ℤ) : ℝ)) := by
    have hlhs : 1 / 2 * Real.log (‖(1 : Mat d)‖ * ‖(1 : Mat d)⁻¹‖) = 0 := by
      rw [inv_one, norm_one, mul_one, Real.log_one, mul_zero]
    rw [hlhs]
    have hcast : ((jStar : ℤ) : ℝ) + ((⌈B * x⌉ : ℤ) : ℝ) ≤ (n₀ : ℝ) := by exact_mod_cast hn₀
    have hnn : 0 ≤ (n₀ : ℝ) - (jStar : ℝ) - ((⌈B * x⌉ : ℤ) : ℝ) := by
      push_cast at hcast ⊢; linarith only [hcast]
    exact mul_nonneg (le_of_lt (div_pos hεpos hLR)) hnn
  have hmS1 := Geometry.explicitCanonicalMetric_adaptedMean_posDef d hd P γ E Ψ K Src hstat hce
    jStar hjStar (1 : Mat d) hone1 (n₀ + 2 * (S.L ε σ : ℤ))
  have hmP1 := Geometry.geometryUpdate_posDef hone1 hmS1 ε
  have hecc1P : 1 / 2 * Real.log (‖geometryUpdate ε (1 : Mat d)
        (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar (1 : Mat d))
          (n₀ + 2 * (S.L ε σ : ℤ))))‖ *
      ‖(geometryUpdate ε (1 : Mat d)
        (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar (1 : Mat d))
          (n₀ + 2 * (S.L ε σ : ℤ)))))⁻¹‖) ≤ ε := by
    have hstep := Geometry.projectiveDistance_geometryUpdate_le hone1 hmS1 hεpos
    rwa [Geometry.projectiveDistance_one_eq_log_eccentricity hmP1] at hstep
  have hLz : (1 : ℤ) ≤ (S.L ε σ : ℤ) := by exact_mod_cast hL1
  have hHz : (4 : ℤ) ≤ (H : ℤ) := by exact_mod_cast hH4
  have hhz : (1 : ℤ) ≤ (S.h : ℤ) := by exact_mod_cast hh1
  have hDnn : (0 : ℤ) ≤ 2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ) := by omega
  have hecc1id : 1 / 2 * Real.log (‖(1 : Mat d)‖ * ‖(1 : Mat d)⁻¹‖) ≤ ε := by
    rw [inv_one, norm_one, mul_one, Real.log_one, mul_zero]
    exact hεpos.le
  have hepsJ : ε / Real.log 3 ≤ ε * ((J : ℝ) + 2) / Real.log 3 := by
    have he2 : ε * ((J : ℝ) + 2) / Real.log 3 = ε / Real.log 3 * ((J : ℝ) + 2) :=
      (div_mul_eq_mul_div ε (Real.log 3) ((J : ℝ) + 2)).symm
    have ht0 : (0 : ℝ) ≤ ε / Real.log 3 := div_nonneg hεpos.le hlog3pos.le
    have hprod : (0 : ℝ) ≤ ε / Real.log 3 * ((J : ℝ) + 1) := mul_nonneg ht0 (by linarith only [hJ0])
    rw [he2]
    linarith only [hprod]
  have hDJ1 : (0 : ℤ) ≤ (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * ((J : ℤ) + 1) :=
    mul_nonneg hDnn (by positivity)
  have hexpD : (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * ((J : ℤ) + 2)
      = (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * ((J : ℤ) + 1) +
        (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) := by ring
  have hb2L : n₀ + 2 * (S.L ε σ : ℤ) + 1 ≤
      n₀ + (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * ((J : ℤ) + 2) := by
    rw [hexpD]; linarith only [hDJ1, hHz, hhz]
  have hbL : n₀ + (S.L ε σ : ℤ) + 1 ≤
      n₀ + (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * ((J : ℤ) + 2) := by
    rw [hexpD]; linarith only [hDJ1, hHz, hhz, hLz]
  have hcont1 : HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar (1 : Mat d))
        (n₀ + 2 * (S.L ε σ : ℤ)) ∪
      HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar (geometryUpdate ε (1 : Mat d)
        (explicitCanonicalMetric (adaptedMean P (Geometry.explicitRoundedGrid jStar (1 : Mat d))
          (n₀ + 2 * (S.L ε σ : ℤ)))))) (n₀ + (S.L ε σ : ℤ)) ⊆
      HighContrast.centeredCube d (2 * (jStar : ℤ)) := by
    refine run_entry_containment hd jStar hjStar (1 : Mat d) _ hone1 hmP1
      (n₀ + 2 * (S.L ε σ : ℤ)) (n₀ + (S.L ε σ : ℤ)) ε hεpos.le hecc1id hecc1P ?_ ?_
    · have hb := hbudget (n₀ + 2 * (S.L ε σ : ℤ)) hb2L
      linarith only [hb, hepsJ]
    · have hb := hbudget (n₀ + (S.L ε σ : ℤ)) hbL
      linarith only [hb, hepsJ]
  obtain ⟨hstartS, hone0⟩ := hselection hjn₀ hecc1 hcont1
  have hxnn : 0 ≤ profile P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar n₀ n₀ +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar n₀ :=
    profile_add_determinantDrift_nonneg d hd P γ E Ψ K Src hstat hce jStar hjStar
      (1 : Mat d) hone1 n₀ n₀ hjn₀ le_rfl
  have hDnn0 : 0 ≤ detIncrement P (Geometry.explicitRoundedGrid jStar (1 : Mat d)) n₀ (n₀ + (S.h
    : ℤ)) :=
    Annealed.logDetLoss_nonneg d hd P γ E Ψ K Src hstat hce jStar hjStar (1 : Mat d) hone1
      n₀ (n₀ + (S.h : ℤ)) hjn₀ (by omega)
  have hstart : profile P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar n₀
          (n₀ + (S.h : ℤ)) +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar (n₀ + (S.h :
          ℤ)) ≤
      max 1 Csel * (profile P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar n₀ n₀ +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar n₀ +
        Real.exp ((bigQ d γ : ℝ) *
          detIncrement P (Geometry.explicitRoundedGrid jStar (1 : Mat d)) n₀ (n₀ + (S.h : ℤ))) -
            1) := by
    have hexp : (1 : ℝ) ≤ Real.exp ((bigQ d γ : ℝ) *
        detIncrement P (Geometry.explicitRoundedGrid jStar (1 : Mat d)) n₀ (n₀ + (S.h : ℤ))) :=
      Real.one_le_exp (mul_nonneg hQ0 hDnn0)
    have hbr : 0 ≤ profile P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar n₀ n₀ +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar n₀ +
        Real.exp ((bigQ d γ : ℝ) *
          detIncrement P (Geometry.explicitRoundedGrid jStar (1 : Mat d)) n₀ (n₀ + (S.h : ℤ))) -
            1 := by
      linarith only [hexp, hxnn]
    exact le_trans hstartS (mul_le_mul_of_nonneg_right (le_max_right 1 Csel) hbr)
  -- the determinant input of `run_initial`
  exact ⟨hstart, hone0⟩

private theorem run_initial_gauge_state {d : ℕ} [NeZero d] (hd : 2 ≤ d)
    (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
    (Src : CoeffSpace d → ℝ) (hP : IsProbabilityMeasure P) (hstat : IsStationaryLaw P)
    (hunit : IsUnitRangeLaw P) (hce : CoarseEllipticityDagger P γ E Ψ K Src)
    (S : SelectionData) (ε σ B : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) S.eps0)
    (hσ : σ ∈ Set.Ioc (0 : ℝ) ε) (hB1 : 1 ≤ B) (H jStar : ℕ)
    (hjStar : 2 * d ≤ 3 ^ jStar) (hh1 : 1 ≤ S.h) (hL1 : 1 ≤ S.L ε σ)
    (n₀ : ℤ) (hn₀ : (jStar : ℤ) + ⌈B * Real.logb 3 (2 + aspectRatio E)⌉ ≤ n₀)
    (a Csel Cgeom Cdet Ctop Cpot C₁ c w x : ℝ) (J : ℕ)
    (ha1 : 1 ≤ a) (hCgeom : 0 < Cgeom) (hw0 : 0 ≤ w) (hcpos : 0 < c)
    (hCdetdef : Cdet = 48 * (d : ℝ) / Real.log 3)
    (hCtopdef : Ctop = Real.log (1 + max 1 Csel * (S.h : ℝ)))
    (hCpotdef : Cpot = 2 * Ctop + 2 * ((bigQ d γ : ℝ) * Cdet) + 8 * (a * Cgeom))
    (hC₁def : C₁ = (Cpot + 48 * w * ((S.h : ℝ) + 2) * (d : ℝ)) / c)
    (hxdef : x = Real.logb 3 (2 + aspectRatio E)) (hJge : C₁ * x ≤ (J : ℝ))
    (hgeo : projectiveDistance (1 : Mat d)
      (explicitCanonicalMetric (adaptedMean P (1 : Mat d) n₀)) ≤
        Cgeom * Real.log (2 + 4 * aspectRatio E))
    (hsand₁ : BlockMatLoewnerLE
      (blockScale (1 / 2)
        (ofFullBlockMat (toFullBlockMat (blockSwap d) * (toFullBlockMat E)⁻¹ *
          toFullBlockMat (blockSwap d)))) (adaptedMean P (1 : Mat d) n₀))
    (hsand₂ : BlockMatLoewnerLE (adaptedMean P (1 : Mat d) n₀) (blockScale 2 E))
    (hinitG : profile P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar n₀ n₀ +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar n₀ ≤ 1)
    (hstart : profile P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar n₀
          (n₀ + (S.h : ℤ)) +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar
          (n₀ + (S.h : ℤ)) ≤
      max 1 Csel * (profile P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar n₀ n₀ +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar n₀ +
        Real.exp ((bigQ d γ : ℝ) *
          detIncrement P (Geometry.explicitRoundedGrid jStar (1 : Mat d)) n₀ (n₀ + (S.h : ℤ))) - 1))
    (hone0 : n₀ = n₀ + (S.h : ℤ) →
      profile P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar (n₀ + (S.h : ℤ))
          (n₀ + (S.h : ℤ)) +
        determinantDrift P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar
          (n₀ + (S.h : ℤ)) ≤ 1) :
    ∃ st₀ : RunState P γ S ε σ B E H jStar n₀,
      st₀.m = (1 : Mat d) ∧ st₀.k = n₀ ∧ st₀.n = n₀ + (S.h : ℤ) ∧ st₀.i = 0 ∧
        runGauge P γ jStar (S.eta ε σ) a w S.h st₀.m st₀.k st₀.n ≤ c * (J : ℝ) := by
  let : IsProbabilityMeasure P := hP
  have hone1 : (1 : Mat d).PosDef := Geometry.one_posDef d
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
  have hQ0 : (0 : ℝ) ≤ (bigQ d γ : ℝ) := Nat.cast_nonneg _
  have hhR0 : (0 : ℝ) ≤ (S.h : ℝ) := Nat.cast_nonneg _
  have hAR0 : 0 < aspectRatio E := (Annealed.aspectRatio_pos_and_three_le hce).1
  have hCdet0 : 0 ≤ Cdet := by
    rw [hCdetdef]
    exact div_nonneg (by positivity) (Real.log_pos (by norm_num)).le
  have hCtop0 : 0 ≤ Ctop := by
    rw [hCtopdef]
    apply Real.log_nonneg
    have hhR : 0 ≤ (S.h : ℝ) := Nat.cast_nonneg _
    have hM : 0 ≤ max 1 Csel := zero_le_one.trans (le_max_left _ _)
    linarith only [mul_nonneg hM hhR]
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hjn₀ : (jStar : ℤ) ≤ n₀ := by
    have hAR := HCPolySupport.HighContrast.aspectRatio_nonneg E
    have hlog : 0 ≤ Real.logb 3 (2 + aspectRatio E) :=
      Real.logb_nonneg (by norm_num) (by linarith only [hAR])
    have hceil : (0 : ℤ) ≤ ⌈B * Real.logb 3 (2 + aspectRatio E)⌉ :=
      Int.ceil_nonneg (mul_nonneg (zero_le_one.trans hB1) hlog)
    omega
  have hApos : Book.Ch02.BlockPosDef (adaptedMean P (1 : Mat d) n₀) := by
    have hg := run_adaptedMean_blockPosDef hd P γ E Ψ K Src hP hstat hce jStar hjStar
      (1 : Mat d) hone1 n₀
    rwa [Geometry.explicitRoundedGrid_one] at hg
  have hdetB : detIncrement P (Geometry.explicitRoundedGrid jStar (1 : Mat d)) n₀ (n₀ + (S.h : ℤ)) ≤
      Cdet * Real.log (2 + aspectRatio E) := by
    have h1 : blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar (1 : Mat d)) n₀) ≤
        (d : ℝ) * Real.log (24 * aspectRatio E) := by
      rw [Geometry.explicitRoundedGrid_one]
      exact blockLogDet_le_of_initial_sandwich E (adaptedMean P (1 : Mat d) n₀)
        hce.refBlock_isSymm hce.refBlock_posDef (Recurrence.isSymmetricBlockMat_adaptedMean P _
          _) hApos hAR0
        (refBlock_le_six_aspect E hce.refBlock_isSymm hce.refBlock_posDef) hsand₂
    have h2 : 0 ≤ blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar (1 : Mat d))
        (n₀ + (S.h : ℤ))) :=
      run_blockLogDet_adaptedMean_nonneg hd P γ E Ψ K Src hP hstat hunit hce jStar hjStar
        (1 : Mat d) hone1 _
    have h3 : Real.log (24 * aspectRatio E) ≤ 48 * x := log24_le _ hAR0
    have h4 : Cdet * Real.log (2 + aspectRatio E) = 48 * (d : ℝ) * x := by
      rw [hCdetdef, ← logb_three_mul (aspectRatio E), ← hxdef]
      field_simp
    have h5 : (d : ℝ) * Real.log (24 * aspectRatio E) ≤ (d : ℝ) * (48 * x) :=
      mul_le_mul_of_nonneg_left h3 hdR.le
    have h6 : (d : ℝ) * (48 * x) = 48 * (d : ℝ) * x := by ring
    simp only [detIncrement]
    rw [h4]
    linarith only [h1, h2, h5, h6]
  have harithB := initial_harith (bigQ d γ : ℝ) Cdet (a * Cgeom) Ctop hQ0 hCdet0
    (mul_nonneg (by linarith only [ha1]) hCgeom.le) hCtop0
  obtain ⟨st₀, hm₀, hk₀, hn₀eq, hi₀, hpot⟩ :=
    run_initial hd γ hγ P E Ψ K Src hP hstat hunit hce S ε σ B hε hσ hB1 H jStar hjStar
      hh1 hL1 n₀ hn₀ a (max 1 Csel) Cpot Cdet Cgeom (le_max_left _ _) ha1 hCdet0 hCgeom
      hgeo hdetB
      (by
        intro AR Δ hAR hΔ hΔle
        have := harithB AR Δ hAR hΔ hΔle
        rw [hCpotdef, hCtopdef]
        rw [hCtopdef] at this
        calc Real.log (1 + max 1 Csel * (S.h : ℝ)) + (bigQ d γ : ℝ) * Δ +
              a * Cgeom * Real.log (2 + 4 * AR) ≤
            (2 * Real.log (1 + max 1 Csel * (S.h : ℝ)) + 2 * ((bigQ d γ : ℝ) * Cdet) +
              8 * (a * Cgeom)) * Real.logb 3 (2 + AR) := this
          _ = (2 * Real.log (1 + max 1 Csel * (S.h : ℝ)) + 2 * ((bigQ d γ : ℝ) * Cdet) +
              8 * (a * Cgeom)) * Real.logb 3 (2 + AR) := rfl)
      hinitG hstart hone0
  rw [← hxdef] at hpot
  -- the initial gauge bound
  have hres : run_reserve
      (fun r => blockLogDet (adaptedMean P (Geometry.explicitRoundedGrid jStar st₀.m) r)) S.h st₀.k
      st₀.n ≤ ((S.h : ℝ) + 2) * ((d : ℝ) * Real.log (24 * aspectRatio E)) := by
    rw [hm₀, hk₀, hn₀eq]
    exact run_initial_reserve hd γ hγ P E Ψ K Src hP hstat hunit hce jStar hjStar S.h n₀
      hjn₀ hce.refBlock_isSymm hce.refBlock_posDef hAR0 hsand₁ hsand₂
  have hbound : runGauge P γ jStar (S.eta ε σ) a w S.h st₀.m st₀.k st₀.n ≤ c * (J : ℝ) := by
    have hg : runGauge P γ jStar (S.eta ε σ) a w S.h st₀.m st₀.k st₀.n =
        potential P γ jStar (S.eta ε σ) a st₀.m st₀.k st₀.n +
          w * run_reserve (fun r => blockLogDet
            (adaptedMean P (Geometry.explicitRoundedGrid jStar st₀.m) r)) S.h st₀.k st₀.n := rfl
    have h3 : Real.log (24 * aspectRatio E) ≤ 48 * x := log24_le _ hAR0
    have hwr : w * run_reserve (fun r => blockLogDet
        (adaptedMean P (Geometry.explicitRoundedGrid jStar st₀.m) r)) S.h st₀.k st₀.n ≤
        w * (((S.h : ℝ) + 2) * ((d : ℝ) * Real.log (24 * aspectRatio E))) :=
      mul_le_mul_of_nonneg_left hres hw0
    have hk : (0 : ℝ) ≤ w * (((S.h : ℝ) + 2) * (d : ℝ)) :=
      mul_nonneg hw0 (mul_nonneg (by linarith only [hhR0]) hdR.le)
    have hwr2 : w * (((S.h : ℝ) + 2) * ((d : ℝ) * Real.log (24 * aspectRatio E))) ≤
        48 * w * ((S.h : ℝ) + 2) * (d : ℝ) * x := by
      have e1 : w * (((S.h : ℝ) + 2) * ((d : ℝ) * Real.log (24 * aspectRatio E)))
          = w * (((S.h : ℝ) + 2) * (d : ℝ)) * Real.log (24 * aspectRatio E) := by ring
      have e2 : 48 * w * ((S.h : ℝ) + 2) * (d : ℝ) * x
          = w * (((S.h : ℝ) + 2) * (d : ℝ)) * (48 * x) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left h3 hk
    have hc' : c * C₁ = Cpot + 48 * w * ((S.h : ℝ) + 2) * (d : ℝ) := by
      rw [hC₁def, mul_comm]
      exact div_mul_cancel₀ _ hcne
    have hCx : c * C₁ * x = (Cpot + 48 * w * ((S.h : ℝ) + 2) * (d : ℝ)) * x := by rw [hc']
    have hJx : c * (C₁ * x) ≤ c * (J : ℝ) := mul_le_mul_of_nonneg_left hJge hcpos.le
    rw [hg]
    have hsum : potential P γ jStar (S.eta ε σ) a st₀.m st₀.k st₀.n +
        w * run_reserve (fun r => blockLogDet
          (adaptedMean P (Geometry.explicitRoundedGrid jStar st₀.m) r)) S.h st₀.k st₀.n ≤
        Cpot * x + 48 * w * ((S.h : ℝ) + 2) * (d : ℝ) * x := by
      linarith only [hpot, hwr, hwr2]
    have hfin : Cpot * x + 48 * w * ((S.h : ℝ) + 2) * (d : ℝ) * x ≤ c * (J : ℝ) := by
      have e3 : Cpot * x + 48 * w * ((S.h : ℝ) + 2) * (d : ℝ) * x
          = (Cpot + 48 * w * ((S.h : ℝ) + 2) * (d : ℝ)) * x := by ring
      have e4 : c * C₁ * x = c * (C₁ * x) := by ring
      rw [e3, ← hCx, e4]
      exact hJx
    linarith only [hsum, hfin]
  exact ⟨st₀, hm₀, hk₀, hn₀eq, hi₀, hbound⟩

/-- **The run, assembled.** The residue of `global_run_of_gap`: the constants `CS`
(for `comparison_choice`) and `Csrc` are produced here, because both are maxima over Skolem
constants of `hS`, `initial_provider_input`, `Entry.fixed_geometry_one_grid_propagation_full`
and `Entry.successful_short_bridge`, which only this proof can name.

Route, given `H`, then `σ`, then the law and `jStar`:

1. `initial_provider_input` produces the entry generation `n₀` and the initial sandwich;
   `Geometry.explicitRoundedGrid_one` identifies its grid `𝒬(Id)` with `Id`, so its output
   `profile P γ (1 : Mat d) …` is `run_initial`'s `profile P γ (Geometry.explicitRoundedGrid jStar
   1) …`.
2. `C := max` of the `weight_choice_ge_d`, `scales_arith`, `eccentricity_arith` and
   `containment_arith` constants (the last at its free real argument `d := 4d`);
   `Cprof` from `run_output_profile` at `Cout := C_S`; `J := ⌈C₁ logb 3 (2+Π)⌉₊`.
3. `run_initial` (potential) and `run_initial_reserve` (reserve; its binder
   `hjn₀ : (jStar : ℤ) ≤ n₀` comes from `hn₀`) bound `runGauge` at step `0` by `c * J`.
4. `run_step_any` supplies the `hcont` and `hstep` binders of `run_exists_stop`.
5. `run_exists_stop` produces the stopping state, and `run_stop_output` turns it into
   `SelectedOutput`. Every source threshold is the bound `⌈C' * Real.logb 3 (2 * K)⌉ ≤
   (jStar : ℤ)` at a constant `0 < C' ≤ Csrc`. -/
theorem global_run_residue (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (S : SelectionData) (hS : S.Selects d γ)
    (hh : 2 * bigQ d γ ≤ S.h)
    (hL : ∀ ε σ : ℝ, ε ∈ Set.Ioc (0 : ℝ) S.eps0 → σ ∈ Set.Ioc (0 : ℝ) ε → 1 ≤ S.L ε σ) :
    ∃ CS : ℝ, 1 ≤ CS ∧
      ∃ Csrc : ℝ, 0 < Csrc ∧
        ∀ ε : ℝ, ε ∈ Set.Ioc (0 : ℝ) S.eps0 →
          (∀ σ : ℝ, σ ∈ Set.Ioc (0 : ℝ) ε →
            1 / 2 * Real.log ((1 + Real.sqrt ε * σ) / (1 - Real.sqrt ε * σ)) +
                2 * CS * ((S.h : ℝ) + 2) * Real.log (1 + Real.sqrt ε * σ) ≤
              min (ε / 2) (CS * σ / 4)) →
            GlobalRunGapObligation d γ S ε Csrc := by
  classical
  have : NeZero d := ⟨by omega⟩
  have hd0 : 0 < d := by omega
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd0
  have hQ2 : 2 ≤ bigQ d γ := bigQ_two_le d γ hγ
  have hh1 : 1 ≤ S.h := by omega
  have hd2R : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hlog3one : (1 : ℝ) < Real.log 3 := by
    have h9 := Real.exp_one_lt_d9
    have h3 : Real.exp 1 < 3 := by linarith only [h9]
    have h4 := Real.log_lt_log (Real.exp_pos 1) h3
    rwa [Real.log_exp] at h4
  obtain ⟨Csel, hCsel, CsrcS, hCsrcS, hsel, -⟩ := id hS.1
  obtain ⟨Cstep, hCstep, Cbase, hCbase, hstepany⟩ :=
    run_step_any hd γ hγ S hS hh hL
  obtain ⟨Cgeom, hCgeom, hip1⟩ := initial_provider_input d hd
  obtain ⟨CsrcI, hCsrcI, hip2⟩ := hip1 γ hγ S hS
  obtain ⟨Cini, hCini, hip3⟩ := hip2 1 ⟨one_pos, le_rfl⟩
  obtain ⟨CsrcP, hCsrcP, hprofAll⟩ := run_output_profile d hd γ hγ
  clear hip1 hip2
  refine ⟨max (max 1 (d : ℝ)) Cbase, le_trans (le_max_left _ _) (le_max_left _ _),
    max (max Cstep CsrcI) (max CsrcP CsrcS),
    lt_max_of_lt_left (lt_max_of_lt_left hCstep), ?_⟩
  set CS : ℝ := max (max 1 (d : ℝ)) Cbase with hCSdef
  set Csrc : ℝ := max (max Cstep CsrcI) (max CsrcP CsrcS) with hCsrcdef
  have hCS1 : (1 : ℝ) ≤ CS := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCSd : (d : ℝ) ≤ CS := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCSbase : Cbase ≤ CS := le_max_right _ _
  have hCS0 : (0 : ℝ) < CS := by linarith only [hCS1]
  clear_value CS
  intro ε hε hcmp H hH
  have hH4 : 4 ≤ H := le_trans (le_max_left _ _) hH
  have hH1 : 1 ≤ H := by omega
  obtain ⟨Cprof, hCprof, hprof⟩ := hprofAll Cbase hCbase H hH1
  clear hprofAll
  refine ⟨Cprof, hCprof, ?_⟩
  intro σ hσ
  have hεpos : (0 : ℝ) < ε := hε.1
  have hσpos : (0 : ℝ) < σ := hσ.1
  have hε1 : ε ≤ 1 := le_trans hε.2 S.eps0_mem.2.le
  have hσ1 : σ ≤ 1 := le_trans hσ.2 hε1
  have hL1 : 1 ≤ S.L ε σ := hL ε σ hε hσ
  have hLR : (0 : ℝ) < (S.L ε σ : ℝ) := by
    have h1 : (1 : ℝ) ≤ (S.L ε σ : ℝ) := by exact_mod_cast hL1
    linarith only [h1]
  set c : ℝ := 1 / 2 * S.eta ε σ * Real.log (16 / 9) with hcdef
  have hcpos : 0 < c := by
    rw [hcdef]
    exact run_selection_charge_positive S ε σ hεpos hσpos
  clear_value c
  obtain ⟨a, ha1, ha, hwq, hwh, hwL⟩ :=
    weight_choice_ge_d d hd0 CS (bigQ d γ : ℝ) ε σ c (S.L ε σ : ℝ) (H : ℝ) (S.h : ℝ)
      hCS0 hεpos hσpos
  set w : ℝ := a * CS / (d : ℝ) with hwdef
  have hw0 : (0 : ℝ) ≤ w := by
    rw [hwdef]; exact div_nonneg (mul_nonneg (by linarith only [ha1]) (by linarith only [hCS1]))
      hdR.le
  clear_value w
  have hLR0 : (0 : ℝ) ≤ (S.L ε σ : ℝ) := le_of_lt hLR
  have hHR0 : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg _
  have hhR0 : (0 : ℝ) ≤ (S.h : ℝ) := Nat.cast_nonneg _
  have hlogH : 0 ≤ Real.log (1 + CS * (H : ℝ)) := by
    have hHR : (0 : ℝ) ≤ (H : ℝ) := Nat.cast_nonneg _
    have hmul : (0 : ℝ) ≤ CS * (H : ℝ) := mul_nonneg (by linarith only [hCS1]) hHR
    exact Real.log_nonneg (by linarith only [hmul])
  -- the scalar constants of the initialization
  set Cdet : ℝ := 48 * (d : ℝ) / Real.log 3 with hCdetdef
  clear_value Cdet
  set Ctop : ℝ := Real.log (1 + max 1 Csel * (S.h : ℝ)) with hCtopdef
  clear_value Ctop
  set Cpot : ℝ := 2 * Ctop + 2 * ((bigQ d γ : ℝ) * Cdet) + 8 * (a * Cgeom) with hCpotdef
  clear_value Cpot
  set C₁ : ℝ := (Cpot + 48 * w * ((S.h : ℝ) + 2) * (d : ℝ)) / c with hC₁def
  clear_value C₁
  have hC₁0 : 0 ≤ C₁ := by
    rw [hC₁def, hCpotdef, hCtopdef, hCdetdef]
    exact (run_initial_budget_constants d (bigQ d γ) S.h a Csel Cgeom w c
      ha1 hCgeom hw0 hcpos hh1).2.2.2
  obtain ⟨Csc, hCsc, hscA⟩ :=
    scales_arith Cini C₁ (S.L ε σ : ℝ) (H : ℝ) (S.h : ℝ) hCini.le hC₁0 hLR0 hHR0 hhR0
  obtain ⟨Cec, hCec, heccA⟩ := eccentricity_arith (2 * ε) C₁ (by linarith only [hεpos]) hC₁0
  obtain ⟨Cct, hCct, hctA⟩ :=
    containment_arith Cini C₁ (S.L ε σ : ℝ) (H : ℝ) (S.h : ℝ) ε (4 * (d : ℝ))
      hCini.le hC₁0 hLR0 hHR0 hhR0 hεpos.le (by linarith only [hd2R])
  refine ⟨max (max Csc Cec) (max Cct 1), by positivity, ?_⟩
  set C : ℝ := max (max Csc Cec) (max Cct 1) with hCdef
  have hCscC : Csc ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCecC : Cec ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCctC : Cct ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC1 : (1 : ℝ) ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  clear_value C
  intro P E Ψ K Src hP hstat hunit hce B hB jStar hjStar hthr hsrcAll
  let : IsProbabilityMeasure P := hP
  set x : ℝ := Real.logb 3 (2 + aspectRatio E) with hxdef
  have hAR0 : 0 < aspectRatio E := (Annealed.aspectRatio_pos_and_three_le hce).1
  have hx : 1 / 2 ≤ x := half_le_logb_three_two_add _ hAR0.le
  have hx0 : (0 : ℝ) ≤ x := by linarith only [hx]
  have hKgt : 1 < K := hce.one_lt_growthWitness
  have hB1 : (1 : ℝ) ≤ B := le_trans (S.one_le_B0 ε σ hε hσ) hB
  have hsrcStep : ∀ C' : ℝ, 0 < C' → C' ≤ Cstep → ⌈C' * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) :=
    fun C' h0 hle => hsrcAll C' h0 (le_trans hle (le_trans (le_max_left _ _) (le_max_left _ _)))
  have hsrcI : ⌈CsrcI * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) :=
    hsrcAll CsrcI hCsrcI (le_trans (le_max_right _ _) (le_max_left _ _))
  have hsrcPth : ⌈CsrcP * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) :=
    hsrcAll CsrcP hCsrcP (le_trans (le_max_left _ _) (le_max_right _ _))
  have hsrcSth : ⌈CsrcS * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) :=
    hsrcAll CsrcS hCsrcS (le_trans (le_max_right _ _) (le_max_right _ _))
  have hprofArg := hprof σ ⟨hσpos, hσ1⟩ P E Ψ K Src hP hstat hunit hce jStar hjStar hsrcPth
  clear hprof hsrcAll
  obtain ⟨n₀, hn₀, hn₀', hinitP, hsand₁, hsand₂, hgeo⟩ :=
    hip3 ε σ hσpos hσ.2 hε.2 P E Ψ K Src hP hstat hunit hce jStar hjStar hsrcI B hB
  rw [← hxdef] at hn₀ hn₀'
  clear hip3
  -- the run length
  set J : ℕ := ⌈C₁ * x⌉₊ with hJdef
  obtain ⟨hJZ, hJR, hJge⟩ := run_horizon_ceiling_properties C₁ x hC₁0 hx0
  clear_value J
  -- the containment budget
  have hctThr : ⌈Cct * (B + 1) * x⌉ ≤ (jStar : ℤ) :=
    containment_threshold_of_bundled C Cct Csrc B K (aspectRatio E) jStar hCct.le hCctC hB1
      hAR0.le hKgt (lt_max_of_lt_left (lt_max_of_lt_left hCstep)) hthr
  have hctRaw := hctA x hx B (by linarith only [hB1]) (jStar : ℤ) hctThr
  have hcontA : ∀ j : ℤ,
      j ≤ n₀ + (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * ((J : ℤ) + 2) →
      (j : ℝ) + (Real.logb 3 (2 * Real.sqrt (4 * (d : ℝ))) + ε * ((J : ℝ) + 1) / Real.log 3) ≤
        2 * (jStar : ℝ) :=
    run_containment_budget S ε σ B Cini x H jStar n₀ J hn₀' (by
      rw [← hJR] at hctRaw
      push_cast at hctRaw
      exact hctRaw)
  have hbudget : ∀ j : ℤ,
      j + 1 ≤ n₀ + (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * ((J : ℤ) + 2) →
      (j : ℝ) + (Real.logb 3 (2 * Real.sqrt (4 * (d : ℝ))) + ε * ((J : ℝ) + 2) / Real.log 3) ≤
        2 * (jStar : ℝ) := by
    intro j hj
    have h := hcontA (j + 1) hj
    have hc1 : (((j + 1 : ℤ)) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
    rw [hc1] at h
    exact shift_budget (j : ℝ) (Real.logb 3 (2 * Real.sqrt (4 * (d : ℝ)))) ε (Real.log 3)
      (J : ℝ) (jStar : ℝ) hlog3one hεpos hε1 h
  -- the step alternative
  obtain ⟨hcontRun, hstepRun⟩ :=
    hstepany P E Ψ K Src hP hstat hunit hce ε σ B hε hσ hB H jStar hH hjStar hsrcStep
      n₀ hn₀ Cini hCini.le hn₀' a c CS w hCS1 hCSd hCSbase ha1 ha hwdef hcdef
      (by rw [← hwdef]; exact hwq) hwh hwL
      hlogH (hcmp σ hσ) J hcontA
  clear hstepany hcmp hcontA hctA hctRaw hsrcStep hsrcI
  -- the initial state
  obtain ⟨hstart, hone0⟩ :=
    run_initial_startup_bound hd γ P E Ψ K Src hstat hce S ε σ B Csel H jStar n₀ J
      hjStar hH4 hh1 hL1 hεpos hLR hB1 (by rwa [hxdef] at hx0)
      (by rwa [hxdef] at hn₀) hbudget (by
        intro hjn₀ hecc1 hcont1
        have hinitG : profile P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar n₀ n₀ +
            determinantDrift P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar n₀ ≤ 1 := by
          rw [Geometry.explicitRoundedGrid_one]
          exact hinitP
        have hdisj0 := hsel ε σ hε hσ B hB P E Ψ K Src hP hstat hunit hce jStar hjStar hsrcSth
          (1 : Mat d) (Geometry.one_posDef d) n₀ n₀ hjn₀ le_rfl hecc1 (fun _ => hinitG)
          (fun hlt => absurd hlt (lt_irrefl n₀)) hcont1
        rcases hdisj0 with h1 | h2 | h3 | h4 | h5
        · exact ⟨h1.1.2, h1.2.2.1⟩
        · exact absurd h2.1.1 (lt_irrefl n₀)
        · exact absurd h3.1.1 (lt_irrefl n₀)
        · exact absurd h4.1.1 (lt_irrefl n₀)
        · exact absurd h5.1.1 (lt_irrefl n₀))
  have hinitG : profile P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar n₀ n₀ +
      determinantDrift P γ (Geometry.explicitRoundedGrid jStar (1 : Mat d)) jStar n₀ ≤ 1 := by
    rw [Geometry.explicitRoundedGrid_one]
    exact hinitP
  obtain ⟨st₀, hm₀, hk₀, hn₀eq, hi₀, hbound⟩ :=
    run_initial_gauge_state hd γ hγ P E Ψ K Src hP hstat hunit hce S ε σ B hε hσ hB1
      H jStar hjStar hh1 hL1 n₀ (by rwa [hxdef] at hn₀) a Csel Cgeom Cdet Ctop Cpot C₁ c w x J
      ha1 hCgeom hw0 hcpos hCdetdef hCtopdef hCpotdef hC₁def hxdef hJge hgeo hsand₁ hsand₂
      hinitG hstart hone0
  -- the stopping state
  obtain ⟨st, hiJ, hstop⟩ :=
    run_exists_stop hd γ hγ P E Ψ K Src hP hstat hunit hce S hS ε σ B hε hσ hB H jStar hH
      hjStar hh hL1 n₀ hn₀ a c CS Cbase w hCS1 hcdef hcpos hwdef ha ha1 J st₀ hi₀ hbound
      hcontRun hstepRun
  clear hcontRun hstepRun hbound hstart hinitG hgeo hsand₁ hsand₂
  clear hS hh hL
  clear hm₀ hk₀ hn₀eq hi₀
  obtain ⟨hlt, hsmall, heq, htest, hbr₁, hbr₂, houtP, honeP⟩ := hstop
  clear hlt hsmall
  -- the eccentricity of the retained metric
  obtain ⟨hecc', hcontOut⟩ :=
    run_stopping_geometry_bounds hd γ P E Ψ K Src hstat hce S ε σ B C Cec H jStar n₀ J
      hjStar hH4 hh1 hL1 hεpos hCecC (by
        have hec := heccA (aspectRatio E) hAR0.le
        rwa [← hxdef, ← hJR] at hec) hbudget st hiJ heq
  -- the upper scale bound
  have hscales : ⌈B * x⌉ + ⌈Cini * x⌉ +
      (2 * (S.L ε σ : ℤ) + (H : ℤ) + (S.h : ℤ)) * ((J : ℤ) + 2) + (S.L ε σ : ℤ) + (H : ℤ) ≤
    ⌈(B + C) * x⌉ :=
    run_integer_scale_budget S ε σ B Cini Csc C x H J hx0 hCscC (by
      have hsc := hscA x hx B
      rwa [← hJR] at hsc)
  -- assemble
  have hC0' : (0 : ℝ) < C := by linarith only [hC1]
  exact run_stop_output hd γ hγ P E Ψ K Src hP hstat hunit hce S ε σ B hε hσ H jStar hH
    hjStar n₀ hn₀ Cini hn₀' CsrcP hsrcPth Cbase Cprof C hCbase hCprof hC0' hL1 J
    st hiJ hscales hcontOut hecc' heq hbr₁ hbr₂ houtP honeP hprofArg htest

end

end HCPolySupport.HighContrast.Multiscale
