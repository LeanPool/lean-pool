/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.UnitRangeRenormalizedBadEvent
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SuperGeometricTail

/-!
# High-contrast homogenization: Provider.Quenched.UnitRangeRenormalizedScale

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The renormalized minimal scale and its tail

The renormalization of ellipticity produces, at each base generation, a random
minimal scale above which the additive comparison with the reference block holds
at every generation of the window.  The scale is the supremum of the bad
generations, and its tail is the sum of the bad-generation estimates over the
generations above.

That sum is super-geometric: the floor of the single-cell parameter grows by the
fixed triadic factor `3^μ` at each generation, so the Gaussian gauge is
iterated at a geometrically growing argument and the whole sum is at most twice
its first term.  The prefactor left by the two union bounds over the window is
then absorbed by halving the exponent.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The base value of the parameter floor -/

/-- The value of the parameter floor at the base generation. -/
@[expose]
def renormBase (gamma nu mu delta Gain : ℝ) (l0 h : ℕ) : ℝ :=
  Gain⁻¹ * delta * (3 : ℝ) ^ ((gamma - nu) + mu * ((l0 : ℝ) - (h : ℝ)))

theorem renormFloor_eq_base_mul (gamma nu mu delta Gain : ℝ) (n l0 h : ℕ) (m : ℤ) :
    renormFloor gamma nu mu delta Gain n l0 h m =
      renormBase gamma nu mu delta Gain l0 h * (3 : ℝ) ^ (mu * ((m : ℝ) - (n : ℝ))) := by
  rw [renormFloor, renormBase]

/-- The bad-generation bound, written as a Gaussian tail in the base value. -/
theorem inv_frGauge_renormFloor (d : ℕ) (gamma nu mu delta Gain : ℝ) (n l0 h : ℕ)
    (m : ℤ) :
    (frGauge d (renormFloor gamma nu mu delta Gain n l0 h m))⁻¹ =
      Real.exp (-(frGaugeConst d * renormBase gamma nu mu delta Gain l0 h ^ 2 *
        (3 : ℝ) ^ (2 * mu * ((m : ℝ) - (n : ℝ))))) := by
  rw [renormFloor_eq_base_mul, inv_frGauge]
  congr 2
  rw [mul_pow, ← Real.rpow_natCast ((3 : ℝ) ^ (mu * ((m : ℝ) - (n : ℝ)))) 2,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  push_cast
  ring_nf

/-! ## Countable subadditivity in the real-valued measure -/

private theorem measureReal_iUnion_nat_le_tsum {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} [IsFiniteMeasure mu] {A : ℕ → Set Omega}
    (hA : Summable fun q => mu.real (A q)) :
    mu.real (⋃ q, A q) ≤ ∑' q, mu.real (A q) := by
  let nu : FiniteMeasure Omega := ⟨mu, inferInstance⟩
  have hAnn : Summable fun q => nu (A q) := by
    rw [← NNReal.summable_coe]
    simpa only [nu, Measure.real] using! hA
  have hnu := FiniteMeasure.apply_iUnion_le (μ := nu) (f := A) hAnn
  have hnur : (nu (⋃ q, A q) : ℝ) ≤ ∑' q, (nu (A q) : ℝ) := by exact_mod_cast hnu
  simpa only [nu, Measure.real] using! hnur

/-! ## The minimal scale -/

/-- The renormalized minimal scale of the base generation `n`: the supremum of
the bad generations above `n`. -/
@[expose]
def renormScale (S : CoeffSpace d → ℝ) (Ahat : BlockMat d) (delta rho : ℝ)
    (h n : ℕ) (a : CoeffSpace d) : ℝ≥0∞ :=
  ⨆ (m : ℤ) (_ : (n : ℤ) ≤ m ∧ a ∈ renormBadGeneration S Ahat delta rho h m),
    ENNReal.ofReal ((3 : ℝ) ^ m)

/-- The renormalized minimal scale with the endpoint buffer of the endgame:
`R_n = 3 max{1, R_n^{(0)}}`. -/
@[expose]
def renormRadius (S : CoeffSpace d → ℝ) (Ahat : BlockMat d) (delta rho : ℝ)
    (h n : ℕ) (a : CoeffSpace d) : ℝ :=
  3 * max 1 (renormScale S Ahat delta rho h n a).toReal

/-- Above a generation, the minimal scale is witnessed by a bad generation
strictly above it. -/
theorem renormScale_gt_subset {S : CoeffSpace d → ℝ} {Ahat : BlockMat d}
    {delta rho : ℝ} {h n : ℕ} {N : ℤ} :
    {a : CoeffSpace d | ENNReal.ofReal ((3 : ℝ) ^ N) <
        renormScale S Ahat delta rho h n a} ⊆
      ⋃ j : ℕ, renormBadGeneration S Ahat delta rho h (N + 1 + (j : ℤ)) := by
  intro a ha
  simp only [Set.mem_ofPred_eq, renormScale, lt_iSup_iff] at ha
  obtain ⟨m, ⟨hnm, hbad⟩, hlt⟩ := ha
  have hpos : (0 : ℝ) < (3 : ℝ) ^ m := by positivity
  have hreal : (3 : ℝ) ^ N < (3 : ℝ) ^ m :=
    (ENNReal.ofReal_lt_ofReal_iff hpos).1 hlt
  have hNm : N < m := by
    by_contra hcon
    push Not at hcon
    exact absurd (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hcon) (not_le.2 hreal)
  refine Set.mem_iUnion.2 ⟨(m - N - 1).toNat, ?_⟩
  have hidx : N + 1 + ((m - N - 1).toNat : ℤ) = m := by omega
  rw [hidx]
  exact hbad

/-! ## The tail of the minimal scale -/

/-- **The tail of the renormalized minimal scale.**  Summing the bad-generation
estimates over the generations above `N` gives a Gaussian tail whose argument is
the parameter floor at generation `N + 1`. -/
theorem measureReal_renormScale_gt_le {P : Measure (CoeffSpace d)}
    [IsFiniteMeasure P] {S : CoeffSpace d → ℝ} {Ahat : BlockMat d}
    {gamma nu mu rho delta Gain : ℝ} {n l0 h : ℕ}
    (hAhat : Book.Ch02.BlockPosDef Ahat) (hGain : 0 < Gain) (hdelta : 0 ≤ delta)
    (hmu : mu = nu - gamma) (hmupos : 0 < mu) (hgn : gamma ≤ nu) (hrg : gamma ≤ rho)
    (hl0 : 1 ≤ renormBase gamma nu mu delta Gain l0 h)
    (hthr : Real.log 2 ≤
      frGaugeConst d * renormBase gamma nu mu delta Gain l0 h ^ 2 *
        ((3 : ℝ) ^ (2 * mu) - 1))
    (hcell : HasCellRenormalization P S Ahat gamma nu Gain n l0 h)
    {N : ℤ} (hnN : (n : ℤ) ≤ N) :
    P.real {a : CoeffSpace d | ENNReal.ofReal ((3 : ℝ) ^ N) <
        renormScale S Ahat delta rho h n a} ≤
      renormCellCount d h * (2 * Real.exp (-(frGaugeConst d *
        renormBase gamma nu mu delta Gain l0 h ^ 2 *
        (3 : ℝ) ^ (2 * mu * ((N : ℝ) + 1 - (n : ℝ)))))) := by
  classical
  set B : ℝ := renormBase gamma nu mu delta Gain l0 h with hBdef
  set A : ℝ := frGaugeConst d * B ^ 2 *
    (3 : ℝ) ^ (2 * mu * ((N : ℝ) + 1 - (n : ℝ))) with hAdef
  have hBpos : (0 : ℝ) < B := lt_of_lt_of_le zero_lt_one hl0
  have hcfr : (0 : ℝ) < frGaugeConst d := frGaugeConst_pos d
  have hmu2 : (0 : ℝ) < 2 * mu := by linarith only [hmupos]
  have hshift : (1 : ℝ) ≤ (3 : ℝ) ^ (2 * mu * ((N : ℝ) + 1 - (n : ℝ))) := by
    have hnNR : (n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
    have hstep : (3 : ℝ) ^ (0 : ℝ) ≤
        (3 : ℝ) ^ (2 * mu * ((N : ℝ) + 1 - (n : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_nonneg hmu2.le (by linarith only [hnNR]))
    simpa using hstep
  have hApos : (0 : ℝ) < A := by
    rw [hAdef]
    have hX : (0 : ℝ) < (3 : ℝ) ^ (2 * mu * ((N : ℝ) + 1 - (n : ℝ))) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hsq : (0 : ℝ) < B ^ 2 := by positivity
    exact mul_pos (mul_pos hcfr hsq) hX
  -- the per-generation bound, reindexed
  have hgen : ∀ j : ℕ,
      P.real (renormBadGeneration S Ahat delta rho h (N + 1 + (j : ℤ))) ≤
        renormCellCount d h * Real.exp (-(A * (3 : ℝ) ^ (2 * mu * (j : ℝ)))) := by
    intro j
    have hnm : (n : ℤ) ≤ N + 1 + (j : ℤ) := by omega
    have hbound := measureReal_renormBadGeneration_le (rho := rho) hAhat hGain hdelta
      hmu hmupos hgn hrg hl0 hcell hnm
    rw [inv_frGauge_renormFloor] at hbound
    refine hbound.trans (le_of_eq ?_)
    congr 2
    rw [hAdef, ← hBdef]
    have hsplit : (3 : ℝ) ^ (2 * mu * (((N + 1 + (j : ℤ) : ℤ) : ℝ) - (n : ℝ)))
        = (3 : ℝ) ^ (2 * mu * ((N : ℝ) + 1 - (n : ℝ))) *
          (3 : ℝ) ^ (2 * mu * (j : ℝ)) := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      push_cast
      ring
    rw [hsplit]
    ring
  -- summability and the super-geometric sum
  have hsummable : Summable fun j : ℕ =>
      P.real (renormBadGeneration S Ahat delta rho h (N + 1 + (j : ℤ))) := by
    refine Summable.of_nonneg_of_le (fun j => measureReal_nonneg) hgen ?_
    exact (summable_exp_neg_triadic hApos hmu2).mul_left _
  have hsub := renormScale_gt_subset (S := S) (Ahat := Ahat) (delta := delta)
    (rho := rho) (h := h) (n := n) (N := N)
  have hcount : (0 : ℝ) ≤ renormCellCount d h := by
    rw [renormCellCount]
    positivity
  calc P.real {a : CoeffSpace d | ENNReal.ofReal ((3 : ℝ) ^ N) <
        renormScale S Ahat delta rho h n a}
      ≤ P.real (⋃ j : ℕ, renormBadGeneration S Ahat delta rho h (N + 1 + (j : ℤ))) :=
        measureReal_mono hsub
    _ ≤ ∑' j : ℕ, P.real (renormBadGeneration S Ahat delta rho h (N + 1 + (j : ℤ))) :=
        measureReal_iUnion_nat_le_tsum hsummable
    _ ≤ ∑' j : ℕ, renormCellCount d h *
          Real.exp (-(A * (3 : ℝ) ^ (2 * mu * (j : ℝ)))) :=
        hsummable.tsum_le_tsum hgen ((summable_exp_neg_triadic hApos hmu2).mul_left _)
    _ = renormCellCount d h *
          ∑' j : ℕ, Real.exp (-(A * (3 : ℝ) ^ (2 * mu * (j : ℝ)))) := tsum_mul_left
    _ ≤ renormCellCount d h * (2 * Real.exp (-A)) := by
        refine mul_le_mul_of_nonneg_left ?_ hcount
        refine tsum_exp_neg_triadic_le_two_mul hApos.le hmu2.le ?_
        have hstep : frGaugeConst d * B ^ 2 * ((3 : ℝ) ^ (2 * mu) - 1) ≤
            A * ((3 : ℝ) ^ (2 * mu) - 1) := by
          have hfac : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * mu) - 1 := by
            have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ (2 * mu) := by
              have hstep2 : (3 : ℝ) ^ (0 : ℝ) ≤ (3 : ℝ) ^ (2 * mu) :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) hmu2.le
              simpa using hstep2
            linarith only [h1]
          have hAge : frGaugeConst d * B ^ 2 ≤ A := by
            rw [hAdef]
            have hsq : (0 : ℝ) ≤ frGaugeConst d * B ^ 2 :=
              mul_nonneg hcfr.le (sq_nonneg B)
            nlinarith only [hsq, hshift]
          exact mul_le_mul_of_nonneg_right hAge hfac
        linarith only [hthr, hstep]


/-! ## The buffer absorbs the union-bound prefactor -/

/-- A prefactor is absorbed by a triadic buffer in the exponent. -/
theorem buffer_absorb (d : ℕ) {mu Cnt : ℝ} (hmu : 0 < mu) (hCnt : 0 < Cnt) {b q : ℕ}
    (hb : Real.log Cnt ≤ frGaugeConst d * ((3 : ℝ) ^ (2 * mu * (b : ℝ)) - 1)) :
    Cnt * Real.exp (-(frGaugeConst d *
        (3 : ℝ) ^ (2 * mu * ((q : ℝ) + (b : ℝ))))) ≤
      Real.exp (-(frGaugeConst d * (3 : ℝ) ^ (2 * mu * (q : ℝ)))) := by
  have hmu2 : (0 : ℝ) < 2 * mu := by linarith only [hmu]
  have hcfr : (0 : ℝ) < frGaugeConst d := frGaugeConst_pos d
  have hq1 : (1 : ℝ) ≤ (3 : ℝ) ^ (2 * mu * (q : ℝ)) := by
    have hstep : (3 : ℝ) ^ (0 : ℝ) ≤ (3 : ℝ) ^ (2 * mu * (q : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_nonneg hmu2.le (Nat.cast_nonneg q))
    simpa using hstep
  have hb1 : (1 : ℝ) ≤ (3 : ℝ) ^ (2 * mu * (b : ℝ)) := by
    have hstep : (3 : ℝ) ^ (0 : ℝ) ≤ (3 : ℝ) ^ (2 * mu * (b : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_nonneg hmu2.le (Nat.cast_nonneg b))
    simpa using hstep
  have hsplit : (3 : ℝ) ^ (2 * mu * ((q : ℝ) + (b : ℝ)))
      = (3 : ℝ) ^ (2 * mu * (q : ℝ)) * (3 : ℝ) ^ (2 * mu * (b : ℝ)) := by
    rw [← Real.rpow_add (by norm_num)]
    congr 1
    ring
  set L : ℝ := Real.log Cnt with hLdef
  set Q : ℝ := (3 : ℝ) ^ (2 * mu * (q : ℝ)) with hQdef
  set Bp : ℝ := (3 : ℝ) ^ (2 * mu * (b : ℝ)) with hBpdef
  clear_value L Q Bp
  have hgain : (0 : ℝ) ≤ frGaugeConst d * (Bp - 1) :=
    mul_nonneg hcfr.le (by linarith only [hb1])
  have hkey : L - frGaugeConst d * (Q * Bp) ≤ -(frGaugeConst d * Q) := by
    nlinarith only [hb, hgain, hq1]
  have hrw : Cnt * Real.exp (-(frGaugeConst d * (Q * Bp)))
      = Real.exp (L - frGaugeConst d * (Q * Bp)) := by
    have hexpand : Real.exp (L - frGaugeConst d * (Q * Bp))
        = Real.exp L * Real.exp (-(frGaugeConst d * (Q * Bp))) := by
      rw [← Real.exp_add]
      congr 1
    rw [hexpand, hLdef, Real.exp_log hCnt]
  rw [hsplit, hrw]
  exact Real.exp_le_exp.2 hkey

/-! ## The shifted tail in the shape the engine consumes -/

/-- **The shifted tail of the renormalized minimal scale.**  With a buffer
absorbing the union-bound prefactor, the renormalized minimal scale obeys exactly
the shifted tail the bad-tail engine consumes, at the dimensional constant
`c_fr(d)`. -/
theorem measureReal_renormRadius_gt_le {P : Measure (CoeffSpace d)}
    [IsFiniteMeasure P] {S : CoeffSpace d → ℝ} {Ahat : BlockMat d}
    {gamma nu mu rho delta Gain : ℝ} {n l0 h b : ℕ}
    (hAhat : Book.Ch02.BlockPosDef Ahat) (hGain : 0 < Gain) (hdelta : 0 ≤ delta)
    (hmu : mu = nu - gamma) (hmupos : 0 < mu) (hgn : gamma ≤ nu) (hrg : gamma ≤ rho)
    (hl0 : 1 ≤ renormBase gamma nu mu delta Gain l0 h)
    (hthr : Real.log 2 ≤
      frGaugeConst d * renormBase gamma nu mu delta Gain l0 h ^ 2 *
        ((3 : ℝ) ^ (2 * mu) - 1))
    (hcell : HasCellRenormalization P S Ahat gamma nu Gain n l0 h)
    (hb1 : 1 ≤ b) (hh1 : 1 ≤ h)
    (hbuf : Real.log (2 * renormCellCount d h) ≤
      frGaugeConst d * ((3 : ℝ) ^ (2 * mu * (b : ℝ)) - 1)) (q : ℕ) :
    P.real {a : CoeffSpace d |
        (3 : ℝ) ^ (n + q + b) < renormRadius S Ahat delta rho h n a} ≤
      Real.exp (-(frGaugeConst d * (3 : ℝ) ^ (2 * mu * (q : ℝ)))) := by
  set N : ℤ := ((n + q + b : ℕ) : ℤ) - 1 with hNdef
  have hnN : (n : ℤ) ≤ N := by omega
  have hpowsplit : (3 : ℝ) ^ (n + q + b) = 3 * (3 : ℝ) ^ N := by
    rw [hNdef, ← zpow_natCast (3 : ℝ) (n + q + b),
      show ((n + q + b : ℕ) : ℤ) = 1 + (((n + q + b : ℕ) : ℤ) - 1) by ring,
      zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]
    ring_nf
  have hNone : (1 : ℝ) ≤ (3 : ℝ) ^ N := by
    have hN0 : (0 : ℤ) ≤ N := by omega
    calc (1 : ℝ) = (3 : ℝ) ^ (0 : ℤ) := by norm_num
      _ ≤ (3 : ℝ) ^ N := zpow_le_zpow_right₀ (by norm_num) hN0
  have hsub : {a : CoeffSpace d |
      (3 : ℝ) ^ (n + q + b) < renormRadius S Ahat delta rho h n a} ⊆
      {a : CoeffSpace d | ENNReal.ofReal ((3 : ℝ) ^ N) <
        renormScale S Ahat delta rho h n a} := by
    intro a ha
    simp only [Set.mem_ofPred_eq, renormRadius, hpowsplit] at ha
    have hmax : (3 : ℝ) ^ N < max 1 (renormScale S Ahat delta rho h n a).toReal := by
      linarith only [ha]
    have htoReal : (3 : ℝ) ^ N < (renormScale S Ahat delta rho h n a).toReal := by
      rcases max_cases 1 (renormScale S Ahat delta rho h n a).toReal with
        ⟨heq, -⟩ | ⟨heq, -⟩
      · rw [heq] at hmax
        linarith only [hmax, hNone]
      · rwa [heq] at hmax
    simp only [Set.mem_ofPred_eq]
    by_cases htop : renormScale S Ahat delta rho h n a = ⊤
    · rw [htop]
      exact ENNReal.ofReal_lt_top
    · exact (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) htop).2 htoReal
  have htail := measureReal_renormScale_gt_le (rho := rho) hAhat hGain hdelta hmu
    hmupos hgn hrg hl0 hthr hcell hnN
  have hshiftEq : (3 : ℝ) ^ (2 * mu * ((N : ℝ) + 1 - (n : ℝ)))
      = (3 : ℝ) ^ (2 * mu * ((q : ℝ) + (b : ℝ))) := by
    congr 1
    have hcast : ((N : ℤ) : ℝ) = (n : ℝ) + (q : ℝ) + (b : ℝ) - 1 := by
      rw [hNdef]
      push_cast
      ring
    rw [hcast]
    ring
  have hBase : (1 : ℝ) ≤ renormBase gamma nu mu delta Gain l0 h := hl0
  have hdrop : Real.exp (-(frGaugeConst d *
        renormBase gamma nu mu delta Gain l0 h ^ 2 *
        (3 : ℝ) ^ (2 * mu * ((q : ℝ) + (b : ℝ)))))
      ≤ Real.exp (-(frGaugeConst d *
        (3 : ℝ) ^ (2 * mu * ((q : ℝ) + (b : ℝ))))) := by
    refine Real.exp_le_exp.2 (neg_le_neg ?_)
    have hcfr : (0 : ℝ) < frGaugeConst d := frGaugeConst_pos d
    have hY : (0 : ℝ) < (3 : ℝ) ^ (2 * mu * ((q : ℝ) + (b : ℝ))) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hsq : (1 : ℝ) ≤ renormBase gamma nu mu delta Gain l0 h ^ 2 := by
      nlinarith only [hBase]
    have hcB : frGaugeConst d ≤
        frGaugeConst d * renormBase gamma nu mu delta Gain l0 h ^ 2 := by
      nlinarith only [hcfr, hsq]
    have hstep := mul_le_mul_of_nonneg_right hcB hY.le
    linarith only [hstep]
  have hcntpos : (0 : ℝ) < 2 * renormCellCount d h := by
    rw [renormCellCount]
    have hh : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh1
    positivity
  calc P.real {a : CoeffSpace d |
        (3 : ℝ) ^ (n + q + b) < renormRadius S Ahat delta rho h n a}
      ≤ P.real {a : CoeffSpace d | ENNReal.ofReal ((3 : ℝ) ^ N) <
          renormScale S Ahat delta rho h n a} := measureReal_mono hsub
    _ ≤ renormCellCount d h * (2 * Real.exp (-(frGaugeConst d *
          renormBase gamma nu mu delta Gain l0 h ^ 2 *
          (3 : ℝ) ^ (2 * mu * ((N : ℝ) + 1 - (n : ℝ)))))) := htail
    _ = 2 * renormCellCount d h * Real.exp (-(frGaugeConst d *
          renormBase gamma nu mu delta Gain l0 h ^ 2 *
          (3 : ℝ) ^ (2 * mu * ((q : ℝ) + (b : ℝ))))) := by
        rw [hshiftEq]
        ring
    _ ≤ 2 * renormCellCount d h * Real.exp (-(frGaugeConst d *
          (3 : ℝ) ^ (2 * mu * ((q : ℝ) + (b : ℝ))))) :=
        mul_le_mul_of_nonneg_left hdrop hcntpos.le
    _ ≤ Real.exp (-(frGaugeConst d * (3 : ℝ) ^ (2 * mu * (q : ℝ)))) :=
        buffer_absorb d hmupos hcntpos hbuf

end

end Quenched
end HighContrast
end HCPolySupport
