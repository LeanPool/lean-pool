/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.ScaleAverageSeminorm
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.TerminalDefectDepthZeroBound
public import LeanPool.HighContrastHomogenization.Provider.Response.WeakNorm

/-!
# High-contrast homogenization: Entry.Response.Kernel.IntegratedWeakEnergyBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The integrated weak-norm estimate

This file integrates the pathwise weak bound over the coefficient law to assemble the weak-norm
estimate `e.response.weak.estimate` for one family of response maximizers. The pathwise bound
`3^{-t/2}[M_0^{1/2}(X_t - Y)]` splits into three summands - the recent cell and averaged-defect
sums, the old-scale tail carrying the optimizer energy, and the random-to-annealed recentring
correction - each squared and integrated separately: the recent sums against the `η^{1/Q}` bound
on the cell defects, the tail against the `Q`-th moment of the all-scale maximum through its
good/bad branches, and the recentring against the `Q`-th moment of the two-sided all-scale
maximum. The purely arithmetic composition of the three resulting constants into the printed
bound is isolated as a single lemma independent of matrices, cells or measures.
-/

section
/-!
## The squared scale-average seminorm bound

The scale-average seminorm `[X]` of AK.HC (2.130) is defined in `ResponseBlockObjects.lean` as a
real
`tsum`; this file records its nonnegativity and the nonnegativity of the squared `L²` cell mean. The
Jensen/partition bound, in squared form, bounds the seminorm itself (rather than `3^{-t/2}` times
it)
by the `L²(U_t)` mean of the field.

-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
/-- The scale-average seminorm `[X]` of AK.HC (2.130) is nonnegative, the junk value of a
divergent defining series being `0`. -/
theorem besovSeminorm_nonneg (t : ℤ) (avg : ℕ → (Fin d → ℤ) → BlockVec d) :
    0 ≤ besovSeminorm t avg := by
  unfold besovSeminorm
  exact tsum_nonneg fun n =>
    mul_nonneg (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _) (Real.sqrt_nonneg _)

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The per-family integrated weak energy

This module integrates the pathwise weak bound over the coefficient law and assembles the
weak-norm estimate `e.response.weak.estimate` for one family of response maximizers.

The pathwise bound splits `3^{-t/2}[M_0^{1/2}(X_t - Y)]` into three summands: the recent
cell and averaged-defect sums, the old-scale tail carrying the optimizer energy, and the
correction from the random cell average to the annealed centre.  Squaring costs a factor
three, and each square is then integrated separately: the recent sums against the
`η^{1/Q}` bound on the cell defects, the tail against the `Q`-th moment of the all-scale
maximum through the good/bad split at the cutoff `1`, and the recentring against the
`Q`-th moment bound on the two-sided all-scale maximum.

The arithmetic of the three constants is isolated in `weakEstimate_arith_engine`, which knows
nothing
about matrices or cells: it is the statement that an integral of a square dominated by
three such terms is bounded by `K_0^2 (L^±)^2 (A_H η^{1/Q} + B (3^{-αH})^2)`.
-/

open HCPolySupport.HighContrast (CoeffSpace HasIntegrableCoarseBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-! ## Elementary nonnegativity of the pathwise carriers -/

/-- The pathwise optimizer energy is a square root. -/
theorem weakOptimizerEnergy_nonneg (U : Set (Vec d)) (b : CoeffField d)
    (u : AHarmonicFunction b U) : 0 ≤ weakOptimizerEnergy U b u := Real.sqrt_nonneg _

/-- The raw response output is antitone in the source threshold constant. -/
theorem RawOutput.of_le_csrc {γ : ℝ} {S : SelectionData}
    {ε σ Cglob Cprof Csrc Csrc' : ℝ} {H : ℕ} {Bresp : ℝ} {P : Measure (CoeffSpace d)}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {Kg : ℝ} {Src : CoeffSpace d → ℝ} {B : ℝ} {jStar : ℕ}
    {F : BlockMat d} {s t : ℤ}
    (raw : RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t)
    (h : Csrc' ≤ Csrc) :
    RawOutput d γ S ε σ Cglob Cprof Csrc' H Bresp P E Ψ Kg Src B jStar F s t := by
  refine ⟨raw.prob, raw.stat, raw.unit, raw.ell, raw.hB, raw.hj, ?_, raw.symm, raw.pos, raw.hst,
    raw.ht, raw.hs_lo, raw.ht_hi, raw.cube, raw.calib_lo, raw.calib_hi, raw.det, raw.prof,
    raw.ecc⟩
  have hK : 1 < Kg := raw.ell.one_lt_growthWitness
  have hlog : 0 ≤ Real.logb 3 (2 * Kg) :=
    Real.logb_nonneg (by norm_num) (by linarith only [hK])
  refine le_trans (Int.ceil_mono ?_) raw.hsrc
  have := mul_le_mul_of_nonneg_right h hlog
  linarith only [this]

/-! ## The integration engine -/

/-- The measure-theoretic core of the weak-norm estimate, with every geometric carrier
replaced by a bare real function.

`f` is the pathwise scale-average seminorm, `S` the sum of the two recent finite sums, `M`
the all-scale maximum, `E` the pathwise optimizer energy, and `c` the squared length of the
recentring vector.  The hypothesis `hpt` is the pathwise three-term split, `hEsq` the block
energy formula `ℰ^2 ≤ (1 + M) (L^±)^2`, and the three pairs `hSint`/`hSle`,
`hMint`/`hMle`, `hcint`/`hcle` are the integrability and the moment bound of each summand.

The good/bad split at the cutoff `1` is `energy_split_pointwise`; squaring the three-term
sum costs the factor `3` of `Quenched.sq_add_three_le`. -/
private theorem weakEstimate_arith_engine {α : Type*} [MeasurableSpace α] (P : Measure α)
    [IsProbabilityMeasure P] (Q : ℕ) (hQ : 2 ≤ Q)
    (f S M E c : α → ℝ) (K0 L θ zz cc kk DH Cm C10 : ℝ)
    (hK0 : 0 ≤ K0) (hL : 0 ≤ L) (hθ : 0 ≤ θ) (hcc : 0 ≤ cc) (hkk : 0 ≤ kk)
    (hf : ∀ a, 0 ≤ f a) (hS : ∀ a, 0 ≤ S a) (hM : ∀ a, 0 ≤ M a) (hE : ∀ a, 0 ≤ E a)
    (hc : ∀ a, 0 ≤ c a)
    (hpt : ∀ᵐ a ∂P, f a ≤ 16 * Real.sqrt K0 * Real.sqrt L * S a
        + cc * Real.sqrt K0 * (if 1 < M a then Real.sqrt (M a) else θ) * E a
        + kk * Real.sqrt (c a))
    (hEsq : ∀ᵐ a ∂P, E a ^ 2 ≤ (1 + M a) * L)
    (hSint : Integrable (fun a => S a ^ 2) P) (hSle : ∫ a, S a ^ 2 ∂P ≤ DH * zz)
    (hMint : Integrable (fun a => M a ^ Q) P) (hMle : ∫ a, M a ^ Q ∂P ≤ Cm * zz)
    (hcint : Integrable c P) (hcle : ∫ a, c a ∂P ≤ C10 * (K0 * L) * zz) :
    ∫ a, f a ^ 2 ∂P ≤ (K0 * L) *
      ((3 * (256 * DH + 2 * cc ^ 2 * Cm + kk ^ 2 * C10)) * zz + (6 * cc ^ 2) * θ ^ 2) := by
  classical
  have hKL : (0 : ℝ) ≤ K0 * L := mul_nonneg hK0 hL
  have hA0 : (0 : ℝ) ≤ 3 * 256 * (K0 * L) := by positivity
  have hB0 : (0 : ℝ) ≤ 6 * cc ^ 2 * (K0 * L) := by positivity
  have hC0 : (0 : ℝ) ≤ 3 * kk ^ 2 := by positivity
  -- the majorant is integrable
  have hint1 : Integrable (fun a => (3 * 256 * (K0 * L)) * S a ^ 2) P :=
    hSint.const_mul _
  have hint2 : Integrable (fun a => (6 * cc ^ 2 * (K0 * L)) * M a ^ Q) P :=
    hMint.const_mul _
  have hint3 : Integrable (fun _ : α => (6 * cc ^ 2 * (K0 * L)) * θ ^ 2) P :=
    integrable_const _
  have hint4 : Integrable (fun a => (3 * kk ^ 2) * c a) P := hcint.const_mul _
  have hint12 : Integrable (fun a => (3 * 256 * (K0 * L)) * S a ^ 2
      + (6 * cc ^ 2 * (K0 * L)) * M a ^ Q) P := hint1.add hint2
  have hint123 : Integrable (fun a => (3 * 256 * (K0 * L)) * S a ^ 2
      + (6 * cc ^ 2 * (K0 * L)) * M a ^ Q
      + (6 * cc ^ 2 * (K0 * L)) * θ ^ 2) P := hint12.add hint3
  have hgint : Integrable (fun a => (3 * 256 * (K0 * L)) * S a ^ 2
      + (6 * cc ^ 2 * (K0 * L)) * M a ^ Q
      + (6 * cc ^ 2 * (K0 * L)) * θ ^ 2
      + (3 * kk ^ 2) * c a) P := hint123.add hint4
  -- the pathwise majorization
  have hmaj : ∀ᵐ a ∂P, f a ^ 2 ≤ (3 * 256 * (K0 * L)) * S a ^ 2
      + (6 * cc ^ 2 * (K0 * L)) * M a ^ Q
      + (6 * cc ^ 2 * (K0 * L)) * θ ^ 2
      + (3 * kk ^ 2) * c a := by
    filter_upwards [hpt, hEsq] with a hpt_a hEsq_a
    set X : ℝ := if 1 < M a then Real.sqrt (M a) else θ with hX
    have hX0 : 0 ≤ X := by
      rw [hX]; split_ifs with h
      · exact Real.sqrt_nonneg _
      · exact hθ
    set t1 : ℝ := 16 * Real.sqrt K0 * Real.sqrt L * S a with ht1
    set t2 : ℝ := cc * Real.sqrt K0 * X * E a with ht2
    set t3 : ℝ := kk * Real.sqrt (c a) with ht3
    have ht10 : 0 ≤ t1 := by
      rw [ht1]
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
        (Real.sqrt_nonneg _)) (hS a)
    have ht20 : 0 ≤ t2 := by
      rw [ht2]
      exact mul_nonneg (mul_nonneg (mul_nonneg hcc (Real.sqrt_nonneg _)) hX0) (hE a)
    have ht30 : 0 ≤ t3 := mul_nonneg hkk (Real.sqrt_nonneg _)
    have hsq : f a ^ 2 ≤ (t1 + t2 + t3) ^ 2 := by
      refine pow_le_pow_left₀ (hf a) ?_ 2
      rw [ht1, ht2, ht3, hX]
      exact hpt_a
    have hcube : (t1 + t2 + t3) ^ 2 ≤ 3 * (t1 ^ 2 + t2 ^ 2 + t3 ^ 2) := Quenched.sq_add_three_le
      t1 t2 t3
    have e1 : t1 ^ 2 = 256 * (K0 * L) * S a ^ 2 := by
      rw [ht1, sqrt_mul_sq 16 K0 L (S a) hK0 hL]; ring
    have hrootK : Real.sqrt K0 ^ 2 = K0 := Real.sq_sqrt hK0
    have ht2sq : t2 ^ 2 = cc ^ 2 * K0 * (X * E a) ^ 2 := by
      rw [ht2]
      have hexp : (cc * Real.sqrt K0 * X * E a) ^ 2
          = cc ^ 2 * Real.sqrt K0 ^ 2 * (X * E a) ^ 2 := by ring
      rw [hexp, hrootK]
    have hsplit : (X * E a) ^ 2 ≤ 2 * L * (M a ^ Q + θ ^ 2) := by
      rw [hX]
      exact energy_split_pointwise (M a) (E a) L θ Q hQ hL (hM a) hEsq_a
    have e2 : t2 ^ 2 ≤ cc ^ 2 * K0 * (2 * L * (M a ^ Q + θ ^ 2)) := by
      rw [ht2sq]
      exact mul_le_mul_of_nonneg_left hsplit (by positivity)
    have e3 : t3 ^ 2 = kk ^ 2 * c a := scaled_sqrt_sq kk (c a) (hc a)
    have hstep : 3 * (t1 ^ 2 + t2 ^ 2 + t3 ^ 2)
        ≤ 3 * (256 * (K0 * L) * S a ^ 2 + cc ^ 2 * K0 * (2 * L * (M a ^ Q + θ ^ 2))
            + kk ^ 2 * c a) := by
      rw [e1, e3]; linarith only [e2]
    have hfin : 3 * (256 * (K0 * L) * S a ^ 2 + cc ^ 2 * K0 * (2 * L * (M a ^ Q + θ ^ 2))
        + kk ^ 2 * c a)
        = (3 * 256 * (K0 * L)) * S a ^ 2 + (6 * cc ^ 2 * (K0 * L)) * M a ^ Q
          + (6 * cc ^ 2 * (K0 * L)) * θ ^ 2 + (3 * kk ^ 2) * c a := by ring
    linarith only [hsq, hcube, hstep, hfin.le, hfin.ge]
  -- integrate the majorization
  have hmono : ∫ a, f a ^ 2 ∂P ≤ ∫ a, ((3 * 256 * (K0 * L)) * S a ^ 2
      + (6 * cc ^ 2 * (K0 * L)) * M a ^ Q
      + (6 * cc ^ 2 * (K0 * L)) * θ ^ 2
      + (3 * kk ^ 2) * c a) ∂P :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun a => sq_nonneg (f a)) hgint hmaj
  -- evaluate the majorant's integral
  have hgval : ∫ a, ((3 * 256 * (K0 * L)) * S a ^ 2
      + (6 * cc ^ 2 * (K0 * L)) * M a ^ Q
      + (6 * cc ^ 2 * (K0 * L)) * θ ^ 2
      + (3 * kk ^ 2) * c a) ∂P
      = (3 * 256 * (K0 * L)) * (∫ a, S a ^ 2 ∂P)
        + (6 * cc ^ 2 * (K0 * L)) * (∫ a, M a ^ Q ∂P)
        + (6 * cc ^ 2 * (K0 * L)) * θ ^ 2
        + (3 * kk ^ 2) * (∫ a, c a ∂P) := by
    rw [integral_add hint123 hint4, integral_add hint12 hint3, integral_add hint1 hint2,
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
    simp
  rw [hgval] at hmono
  have hbound : (3 * 256 * (K0 * L)) * (∫ a, S a ^ 2 ∂P)
      + (6 * cc ^ 2 * (K0 * L)) * (∫ a, M a ^ Q ∂P)
      + (6 * cc ^ 2 * (K0 * L)) * θ ^ 2
      + (3 * kk ^ 2) * (∫ a, c a ∂P)
      ≤ (3 * 256 * (K0 * L)) * (DH * zz) + (6 * cc ^ 2 * (K0 * L)) * (Cm * zz)
        + (6 * cc ^ 2 * (K0 * L)) * θ ^ 2 + (3 * kk ^ 2) * (C10 * (K0 * L) * zz) :=
    add_le_add (add_le_add (add_le_add (mul_le_mul_of_nonneg_left hSle hA0)
      (mul_le_mul_of_nonneg_left hMle hB0)) le_rfl) (mul_le_mul_of_nonneg_left hcle hC0)
  have hlast : (3 * 256 * (K0 * L)) * (DH * zz) + (6 * cc ^ 2 * (K0 * L)) * (Cm * zz)
      + (6 * cc ^ 2 * (K0 * L)) * θ ^ 2 + (3 * kk ^ 2) * (C10 * (K0 * L) * zz)
      = (K0 * L) *
        ((3 * (256 * DH + 2 * cc ^ 2 * Cm + kk ^ 2 * C10)) * zz + (6 * cc ^ 2) * θ ^ 2) := by
    ring
  linarith only [hmono, hbound, hlast.le, hlast.ge]

/-! ## The per-family integrated bound, minus sign -/

/-- **`e.response.weak.estimate`, one maximizer family, minus sign.**  For a single family `u`
of response maximizers,
`3^{-t} E[[M_0^{1/2}(X_t^- - Y^-)]^2] ≤ (C (3^{-αH} + C_H η^{1/(2Q)}) κ_s^{1/2})^2`.

The pathwise three-term split is integrated by `weakEstimate_arith_engine`: the recent finite sums
carry
`η^{1/Q}`, the old-scale tail carries `E[M^Q] + 3^{-2αH}` through the good/bad split at the
cutoff `1`, and the random-to-annealed recentring carries `η^{2/Q}`; the product
`K_0^2 (L^-)^2` is then turned into `C κ_s` by the calibrated-block and load bounds. -/
theorem respWeakEnergyOf_minus_le (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (S : SelectionData) (hS : S.Selects d γ) (Cc Ce Cl Cm Cs : ℝ) (hCc : 0 < Cc)
    (hCe : 0 < Ce) (hCl : 0 < Cl) (hCm : 0 < Cm) (hCs : 0 < Cs) :
    ∃ Csrc : ℝ, 0 < Csrc ∧ ∃ (C : ℝ) (CH : ℕ → ℝ), 0 < C ∧ (∀ n : ℕ, 0 < CH n) ∧
      ∀ (ε σ : ℝ), ε ∈ Set.Ioc (0 : ℝ) S.eps0 → σ ∈ Set.Ioc (0 : ℝ) ε →
        ∀ (Cglob Cprof Bresp : ℝ), 0 ≤ Cglob →
          ∀ (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ)
            (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d) (s t : ℤ),
            RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t →
            RespCalibrated Cc P jStar F s t →
            ∀ η : ℝ, η ∈ Set.Ioo (0 : ℝ) (1 / 2) →
              Cprof * σ ^ ((1 - γ) / 8) ≤ η →
              RespSourceSmall d γ Cs η E F jStar s t →
              ∫ a, respAllScaleAbs P γ jStar F t a ^ bigQ d γ ∂P ≤ Cm * η →
              ∀ e : Vec d, vecDot e e = 1 →
                RespEnergyDefect Ce P jStar F s t e →
                RespLoadMean Cl P jStar F s t e →
                ∀ (u : (a : CoeffSpace d) →
                    AHarmonicFunction (respCoeffMinus F a)
                      (HighContrast.adaptedCell (respGrid jStar F) t)),
                  (∀ a, IsResponseMaximizer (HighContrast.adaptedCell (respGrid jStar F) t)
                    (respP (respMean P jStar F t) e) (respqMinus P jStar F t e)
                    (respCoeffMinus F a) (u a)) →
                  respWeakEnergyOf P (respGrid jStar F) t (respM0 F) (respCoeffMinus F)
                      (respYMinus P jStar F t e) u ≤
                    (C * ((3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) +
                        CH H * η ^ ((1 : ℝ) / (2 * (bigQ d γ : ℝ)))) *
                      Real.sqrt (respKappa P jStar F s)) ^ 2 := by
  classical
  let : NeZero d := ⟨by omega⟩
  have hQ2 : 2 ≤ bigQ d γ := bigQ_two_le d γ hγ
  have hQR : (0 : ℝ) < (bigQ d γ : ℝ) := by
    have : 0 < bigQ d γ := lt_of_lt_of_le (by norm_num) hQ2
    exact_mod_cast this
  have hrho0 : (0 : ℝ) ≤ Quenched.contrastRho γ := by
    have : Quenched.contrastRho γ = (1 + γ) / 2 := rfl
    rw [this]; linarith only [hγ.1]
  have hrho1 : Quenched.contrastRho γ < 1 := by
    have : Quenched.contrastRho γ = (1 + γ) / 2 := rfl
    rw [this]; linarith only [hγ.2]
  obtain ⟨Csrc7, hCsrc7, h7⟩ := respAllScaleMax_aestronglyMeasurable_integrable d hd γ hγ S hS
  obtain ⟨CsrcA, hCsrcA, hA⟩ := respAllScaleAbs_aestronglyMeasurable_integrable d hd γ hγ S hS
  obtain ⟨Csrc8, hCsrc8, K, hK, h8⟩ :=
    integral_recentDefect_sq_le_of_rawOutput_minus d hd γ hγ S hS Cc hCc Cs hCs
  obtain ⟨DD, hDD, h9⟩ :=
    integral_weakSums_sq_le (d := d) (Quenched.contrastRho γ) hrho0 K hK (bigQ d γ) (le_trans
      one_le_two hQ2)
  obtain ⟨C10, hC10, h10⟩ := integral_respRecentre_sq_le_minus d hd γ hγ S hS Cc Cm hCc hCm
  obtain ⟨C11, hC11, h11⟩ := respK0Sq_mul_Lsq_le_kappa d hd γ hγ S hS Cc Ce Cl hCc hCe hCl
  set cc : ℝ := 16 / (1 - Quenched.contrastRho γ) with hccdef
  set kk : ℝ := 1 / (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ))) with hkkdef
  have hcc0 : 0 ≤ cc := by
    rw [hccdef]; exact le_of_lt (div_pos (by norm_num) (by linarith only [hrho1]))
  have hkk0 : 0 ≤ kk := by
    rw [hkkdef]; exact le_of_lt (div_pos one_pos one_sub_rpow_pos)
  refine ⟨max (max Csrc7 CsrcA) Csrc8, lt_max_of_lt_left (lt_max_of_lt_left hCsrc7), ?_⟩
  refine ⟨Real.sqrt (C11 * (6 * cc ^ 2) + 1),
    fun n => Real.sqrt (C11 * (3 * (256 * DD n + 2 * cc ^ 2 * Cm + kk ^ 2 * C10)) + 1), ?_, ?_, ?_⟩
  · refine Real.sqrt_pos.mpr ?_
    have : (0 : ℝ) ≤ C11 * (6 * cc ^ 2) := mul_nonneg hC11.le (by positivity)
    linarith only [this]
  · intro n
    refine Real.sqrt_pos.mpr ?_
    have hn : (0 : ℝ) ≤ 3 * (256 * DD n + 2 * cc ^ 2 * Cm + kk ^ 2 * C10) := by
      have h1 : (0 : ℝ) ≤ 256 * DD n := mul_nonneg (by norm_num) (hDD n).le
      have h2 : (0 : ℝ) ≤ 2 * cc ^ 2 * Cm := mul_nonneg (by positivity) hCm.le
      have h3 : (0 : ℝ) ≤ kk ^ 2 * C10 := mul_nonneg (by positivity) hC10.le
      linarith only [h1, h2, h3]
    have : (0 : ℝ) ≤ C11 * (3 * (256 * DD n + 2 * cc ^ 2 * Cm + kk ^ 2 * C10)) :=
      mul_nonneg hC11.le hn
    linarith only [this]
  intro ε σ hε hσ Cglob Cprof Bresp hCglob H P E Ψ Kg Src B jStar F s t raw hcal η hη hprof
    hsrc hMQ e he hED hLM u hu
  have := raw.prob
  have raw7 := RawOutput.of_le_csrc raw (le_trans (le_max_left _ _) (le_max_left _ _))
  have rawA := RawOutput.of_le_csrc raw (le_trans (le_max_right _ _) (le_max_left _ _))
  have raw8 := RawOutput.of_le_csrc raw (le_max_right _ _)
  have hm : (explicitCanonicalMetric F).PosDef := Geometry.explicitCanonicalMetric_posDef
    raw.symm raw.pos
  have hgrid : IsUnit (respGrid jStar F) := isUnit_respGrid_of_rawOutput raw
  have hint : HasIntegrableCoarseBlock P (respCell jStar F t) := by
    have h := Annealed.hasIntegrableCoarseBlock_adapted d hd P γ E Ψ Kg Src raw.stat raw.ell
      jStar raw.hj (explicitCanonicalMetric F) hm t 0
    rwa [Annealed.adaptedCellTranslate_zero] at h
  have hη1 : η ≤ 1 := by linarith only [hη.2]
  -- the three constants of the statement
  set θ : ℝ := (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) with hθdef
  set zz : ℝ := η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) with hzzdef
  have hθ0 : 0 ≤ θ := Real.rpow_nonneg (by norm_num) _
  have hzz0 : 0 ≤ zz := Real.rpow_nonneg hη.1.le _
  have hηzz : η ≤ zz := by
    have h1 : (1 : ℝ) / (bigQ d γ : ℝ) ≤ 1 := by
      rw [div_le_one hQR]
      have : (2 : ℝ) ≤ (bigQ d γ : ℝ) := by exact_mod_cast hQ2
      linarith only [this]
    have := Real.rpow_le_rpow_of_exponent_ge hη.1 hη1 h1
    rw [hzzdef]
    simpa using this
  -- the pathwise ingredients
  have hK00 : 0 ≤ respK0SqMinus P jStar F t := (respK0Sq_nonneg P jStar F t).1
  obtain ⟨-, hL0, -, -, hprod, -⟩ :=
    h11 ε σ Cglob Cprof (max (max Csrc7 CsrcA) Csrc8) Bresp H P E Ψ Kg Src B jStar F s t hε hσ
      raw hcal e he hED hLM
  have hEsq := weakOptimizerEnergy_sq_le_minus d hd γ hγ S hS ε σ Cglob Cprof
    (max (max Csrc7 CsrcA) Csrc8) Bresp H P E Ψ Kg Src B jStar F s t raw e he u hu
  have hMint := (h7 ε σ hε hσ Cglob Cprof Bresp hCglob H P E Ψ Kg Src B jStar F s t raw7).2
  have hAint := (hA ε σ hε hσ Cglob Cprof Bresp hCglob H P E Ψ Kg Src B jStar F s t rawA).2
  have h8' := h8 ε σ hε hσ Cglob Cprof Bresp hCglob H P E Ψ Kg Src B jStar F s t raw8 hcal η hη
    hprof hsrc
  obtain ⟨hSint, hSle⟩ :=
    h9 P (respGrid jStar F) t H (respEhatMinus P jStar F t) (respCoeffMinus F) η hη
      (fun n _ w hw => h8' n w hw)
  obtain ⟨hcint, hcle0⟩ :=
    h10 ε σ Cglob Cprof (max (max Csrc7 CsrcA) Csrc8) Bresp H P E Ψ Kg Src B jStar F s t raw hcal
      η hη hAint hMQ e he u hu
  -- the moment bound for the one-sided all-scale maximum
  have hMabs := respAllScaleMax_le_respAllScaleAbs_ae hd γ P E Ψ Kg Src raw.stat raw.ell
    jStar raw.hj F hm t
  have hMle : ∫ a, respAllScaleMax P γ jStar F t a ^ bigQ d γ ∂P ≤ Cm * zz := by
    have hpow : ∀ᵐ a ∂P, respAllScaleMax P γ jStar F t a ^ bigQ d γ
        ≤ respAllScaleAbs P γ jStar F t a ^ bigQ d γ := by
      filter_upwards [hMabs] with a hle
      exact pow_le_pow_left₀ (respAllScaleMax_nonneg P γ jStar F t a) hle _
    have hcmp := integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun a =>
        pow_nonneg (respAllScaleMax_nonneg P γ jStar F t a) (bigQ d γ)) hAint hpow
    have : Cm * η ≤ Cm * zz := mul_le_mul_of_nonneg_left hηzz hCm.le
    linarith only [hcmp, hMQ, this]
  -- the recentring bound at the exponent `1/Q`
  have hcle : ∫ a, blockVecDot (respRecentreMinus P jStar F t e a (u a))
      (respRecentreMinus P jStar F t e a (u a)) ∂P
      ≤ C10 * (respK0SqMinus P jStar F t * respLsqMinus P jStar F t e) * zz := by
    have hstep : C10 * (respK0SqMinus P jStar F t * respLsqMinus P jStar F t e) *
        η ^ ((2 : ℝ) / (bigQ d γ : ℝ))
        ≤ C10 * (respK0SqMinus P jStar F t * respLsqMinus P jStar F t e) * zz :=
      mul_le_mul_of_nonneg_left
        (rpow_two_le_one η hη.1 hη1 (bigQ d γ : ℝ) hQR)
        (by positivity)
    linarith only [hcle0, hstep]
  -- the engine
  have heng := weakEstimate_arith_engine P (bigQ d γ) hQ2
    (fun a => (3 : ℝ) ^ (-((t : ℝ) / 2)) *
      besovSeminorm t (fun n z =>
        blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
            (optimizerField (respCoeffMinus F a) (u a)) - respYMinus P jStar F t e)))
    (fun a => weakCellSum (respGrid jStar F) t H (respEhatMinus P jStar F t)
        (respCoeffMinus F a) +
      weakAverageSum (respGrid jStar F) t H (Quenched.contrastRho γ) (respEhatMinus P jStar F t)
        (respCoeffMinus F a))
    (fun a => respAllScaleMax P γ jStar F t a)
    (fun a => weakOptimizerEnergy (respCell jStar F t) (respCoeffMinus F a) (u a))
    (fun a => blockVecDot (respRecentreMinus P jStar F t e a (u a))
      (respRecentreMinus P jStar F t e a (u a)))
    (respK0SqMinus P jStar F t) (respLsqMinus P jStar F t e) θ zz cc kk (DD H) Cm C10
    hK00 hL0 hθ0 hcc0 hkk0
    (fun a => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (besovSeminorm_nonneg _ _))
    (fun a => add_nonneg (weakCellSum_nonneg _ _ _ _ _)
      (weakAverageSum_nonneg _ _ _ _ _ _))
    (fun a => respAllScaleMax_nonneg P γ jStar F t a)
    (fun a => weakOptimizerEnergy_nonneg _ _ _)
    (fun a => Response.blockVecDot_self_nonneg _)
    ((pathwise_envelope hd γ P E Ψ Kg Src raw.stat raw.ell jStar raw.hj F hm t).mono
      fun a ha => by
        obtain ⟨Cenv, _hCenv0, _hCenvL, hterms⟩ := ha
        exact besov_pathwise_le_minus P γ hγ jStar H F t e hgrid hint a
          (respAllScaleMax_bddAbove_of_envelope P γ jStar F t a hterms) (u a) (hu a))
    hEsq hSint hSle hMint hMle hcint hcle
  -- identify the integral with the per-family weak energy
  have hEq : respWeakEnergyOf P (respGrid jStar F) t (respM0 F) (respCoeffMinus F)
      (respYMinus P jStar F t e) u
      = ∫ a, ((3 : ℝ) ^ (-((t : ℝ) / 2)) *
          besovSeminorm t (fun n z =>
            blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
                (optimizerField (respCoeffMinus F a) (u a)) -
                respYMinus P jStar F t e))) ^ 2 ∂P := by
    have hpt : ∀ a : CoeffSpace d,
        ((3 : ℝ) ^ (-((t : ℝ) / 2)) *
          besovSeminorm t (fun n z =>
            blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
                (optimizerField (respCoeffMinus F a) (u a)) -
                respYMinus P jStar F t e))) ^ 2
        = (3 : ℝ) ^ (-(t : ℝ)) *
          besovSeminorm t (fun n z =>
            blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
                (optimizerField (respCoeffMinus F a) (u a)) -
                respYMinus P jStar F t e)) ^ 2 := by
      intro a
      rw [mul_pow, rpow_half_sq]
    simp only [hpt]
    rw [integral_const_mul]
    rfl
  rw [hEq]
  -- the final constant bookkeeping
  have hκ1 := (respKappa_persistence_of_raw d hd γ hγ S hS ε σ hε hσ Cglob Cprof
    (max (max Csrc7 CsrcA) Csrc8) Bresp H P E Ψ Kg Src B jStar F s t raw)
  have hκ0 : 0 ≤ respKappa P jStar F s := le_trans zero_le_one (le_trans hκ1.1 hκ1.2)
  have hz2 : (η ^ ((1 : ℝ) / (2 * (bigQ d γ : ℝ)))) ^ 2 = zz :=
    rpow_sq_eq η hη.1.le (bigQ d γ : ℝ) hQR
  have hAH : (0 : ℝ) ≤ 3 * (256 * DD H + 2 * cc ^ 2 * Cm + kk ^ 2 * C10) := by
    have h1 : (0 : ℝ) ≤ 256 * DD H := mul_nonneg (by norm_num) (hDD H).le
    have h2 : (0 : ℝ) ≤ 2 * cc ^ 2 * Cm := mul_nonneg (by positivity) hCm.le
    have h3 : (0 : ℝ) ≤ kk ^ 2 * C10 := mul_nonneg (by positivity) hC10.le
    linarith only [h1, h2, h3]
  have hbr : (0 : ℝ) ≤ (3 * (256 * DD H + 2 * cc ^ 2 * Cm + kk ^ 2 * C10)) * zz
      + (6 * cc ^ 2) * θ ^ 2 := by
    have h1 : (0 : ℝ) ≤ (3 * (256 * DD H + 2 * cc ^ 2 * Cm + kk ^ 2 * C10)) * zz :=
      mul_nonneg hAH hzz0
    have h2 : (0 : ℝ) ≤ (6 * cc ^ 2) * θ ^ 2 := by positivity
    linarith only [h1, h2]
  have hlift : (respK0SqMinus P jStar F t * respLsqMinus P jStar F t e) *
      ((3 * (256 * DD H + 2 * cc ^ 2 * Cm + kk ^ 2 * C10)) * zz + (6 * cc ^ 2) * θ ^ 2)
      ≤ (C11 * respKappa P jStar F s) *
        ((3 * (256 * DD H + 2 * cc ^ 2 * Cm + kk ^ 2 * C10)) * zz + (6 * cc ^ 2) * θ ^ 2) :=
    mul_le_mul_of_nonneg_right hprod hbr
  refine constant_arith (C11 * (3 * (256 * DD H + 2 * cc ^ 2 * Cm + kk ^ 2 * C10)))
    (C11 * (6 * cc ^ 2)) θ (η ^ ((1 : ℝ) / (2 * (bigQ d γ : ℝ))))
    (respKappa P jStar F s) _ (mul_nonneg hC11.le hAH) (mul_nonneg hC11.le (by positivity))
    hθ0 (Real.rpow_nonneg hη.1.le _) hκ0 ?_
  rw [hz2]
  exact le_trans heng (le_trans hlift (le_of_eq (by ring)))

/-! ## The per-family integrated bound, plus sign -/

/-- **`e.response.weak.estimate`, one maximizer family, plus sign.**  The plus twin of
`respWeakEnergyOf_minus_le`, on the adjoint recentred sample.  For a single family `u`
of response maximizers,
`3^{-t} E[[M_0^{1/2}(X_t^+ - Y^+)]^2] ≤ (C (3^{-αH} + C_H η^{1/(2Q)}) κ_s^{1/2})^2`.

The pathwise three-term split is integrated by `weakEstimate_arith_engine`: the recent finite sums
carry
`η^{1/Q}`, the old-scale tail carries `E[M^Q] + 3^{-2αH}` through the good/bad split at the
cutoff `1`, and the random-to-annealed recentring carries `η^{2/Q}`; the product
`K_0^2 (L^+)^2` is then turned into `C κ_s` by the calibrated-block and load bounds. -/
theorem respWeakEnergyOf_plus_le (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1)
    (S : SelectionData) (hS : S.Selects d γ) (Cc Ce Cl Cm Cs : ℝ) (hCc : 0 < Cc)
    (hCe : 0 < Ce) (hCl : 0 < Cl) (hCm : 0 < Cm) (hCs : 0 < Cs) :
    ∃ Csrc : ℝ, 0 < Csrc ∧ ∃ (C : ℝ) (CH : ℕ → ℝ), 0 < C ∧ (∀ n : ℕ, 0 < CH n) ∧
      ∀ (ε σ : ℝ), ε ∈ Set.Ioc (0 : ℝ) S.eps0 → σ ∈ Set.Ioc (0 : ℝ) ε →
        ∀ (Cglob Cprof Bresp : ℝ), 0 ≤ Cglob →
          ∀ (H : ℕ) (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (Kg : ℝ)
            (Src : CoeffSpace d → ℝ) (B : ℝ) (jStar : ℕ) (F : BlockMat d) (s t : ℤ),
            RawOutput d γ S ε σ Cglob Cprof Csrc H Bresp P E Ψ Kg Src B jStar F s t →
            RespCalibrated Cc P jStar F s t →
            ∀ η : ℝ, η ∈ Set.Ioo (0 : ℝ) (1 / 2) →
              Cprof * σ ^ ((1 - γ) / 8) ≤ η →
              RespSourceSmall d γ Cs η E F jStar s t →
              ∫ a, respAllScaleAbs P γ jStar F t a ^ bigQ d γ ∂P ≤ Cm * η →
              ∀ e : Vec d, vecDot e e = 1 →
                RespEnergyDefect Ce P jStar F s t e →
                RespLoadMean Cl P jStar F s t e →
                ∀ (u : (a : CoeffSpace d) →
                    AHarmonicFunction (respCoeffPlus F a)
                      (HighContrast.adaptedCell (respGrid jStar F) t)),
                  (∀ a, IsResponseMaximizer (HighContrast.adaptedCell (respGrid jStar F) t)
                    (respP (respMean P jStar F t) e) (respqPlus P jStar F t e)
                    (respCoeffPlus F a) (u a)) →
                  respWeakEnergyOf P (respGrid jStar F) t (respM0 F) (respCoeffPlus F)
                      (respYPlus P jStar F t e) u ≤
                    (C * ((3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) +
                        CH H * η ^ ((1 : ℝ) / (2 * (bigQ d γ : ℝ)))) *
                      Real.sqrt (respKappa P jStar F s)) ^ 2 := by
  classical
  let : NeZero d := ⟨by omega⟩
  have hQ2 : 2 ≤ bigQ d γ := bigQ_two_le d γ hγ
  have hQR : (0 : ℝ) < (bigQ d γ : ℝ) := by
    have : 0 < bigQ d γ := lt_of_lt_of_le (by norm_num) hQ2
    exact_mod_cast this
  have hrho0 : (0 : ℝ) ≤ Quenched.contrastRho γ := by
    have : Quenched.contrastRho γ = (1 + γ) / 2 := rfl
    rw [this]; linarith only [hγ.1]
  have hrho1 : Quenched.contrastRho γ < 1 := by
    have : Quenched.contrastRho γ = (1 + γ) / 2 := rfl
    rw [this]; linarith only [hγ.2]
  obtain ⟨Csrc7, hCsrc7, h7⟩ := respAllScaleMax_aestronglyMeasurable_integrable d hd γ hγ S hS
  obtain ⟨CsrcA, hCsrcA, hA⟩ := respAllScaleAbs_aestronglyMeasurable_integrable d hd γ hγ S hS
  obtain ⟨Csrc8, hCsrc8, K, hK, h8⟩ :=
    integral_recentDefect_sq_le_of_rawOutput_plus d hd γ hγ S hS Cc hCc Cs hCs
  obtain ⟨DD, hDD, h9⟩ :=
    integral_weakSums_sq_le (d := d) (Quenched.contrastRho γ) hrho0 K hK (bigQ d γ) (le_trans
      one_le_two hQ2)
  obtain ⟨C10, hC10, h10⟩ := integral_respRecentre_sq_le_plus d hd γ hγ S hS Cc Cm hCc hCm
  obtain ⟨C11, hC11, h11⟩ := respK0Sq_mul_Lsq_le_kappa d hd γ hγ S hS Cc Ce Cl hCc hCe hCl
  set cc : ℝ := 16 / (1 - Quenched.contrastRho γ) with hccdef
  set kk : ℝ := 1 / (1 - (3 : ℝ) ^ (-(1 / 2 : ℝ))) with hkkdef
  have hcc0 : 0 ≤ cc := by
    rw [hccdef]; exact le_of_lt (div_pos (by norm_num) (by linarith only [hrho1]))
  have hkk0 : 0 ≤ kk := by
    rw [hkkdef]; exact le_of_lt (div_pos one_pos one_sub_rpow_pos)
  refine ⟨max (max Csrc7 CsrcA) Csrc8, lt_max_of_lt_left (lt_max_of_lt_left hCsrc7), ?_⟩
  refine ⟨Real.sqrt (C11 * (6 * cc ^ 2) + 1),
    fun n => Real.sqrt (C11 * (3 * (256 * DD n + 2 * cc ^ 2 * Cm + kk ^ 2 * C10)) + 1), ?_, ?_, ?_⟩
  · refine Real.sqrt_pos.mpr ?_
    have : (0 : ℝ) ≤ C11 * (6 * cc ^ 2) := mul_nonneg hC11.le (by positivity)
    linarith only [this]
  · intro n
    refine Real.sqrt_pos.mpr ?_
    have hn : (0 : ℝ) ≤ 3 * (256 * DD n + 2 * cc ^ 2 * Cm + kk ^ 2 * C10) := by
      have h1 : (0 : ℝ) ≤ 256 * DD n := mul_nonneg (by norm_num) (hDD n).le
      have h2 : (0 : ℝ) ≤ 2 * cc ^ 2 * Cm := mul_nonneg (by positivity) hCm.le
      have h3 : (0 : ℝ) ≤ kk ^ 2 * C10 := mul_nonneg (by positivity) hC10.le
      linarith only [h1, h2, h3]
    have : (0 : ℝ) ≤ C11 * (3 * (256 * DD n + 2 * cc ^ 2 * Cm + kk ^ 2 * C10)) :=
      mul_nonneg hC11.le hn
    linarith only [this]
  intro ε σ hε hσ Cglob Cprof Bresp hCglob H P E Ψ Kg Src B jStar F s t raw hcal η hη hprof
    hsrc hMQ e he hED hLM u hu
  have := raw.prob
  have raw7 := RawOutput.of_le_csrc raw (le_trans (le_max_left _ _) (le_max_left _ _))
  have rawA := RawOutput.of_le_csrc raw (le_trans (le_max_right _ _) (le_max_left _ _))
  have raw8 := RawOutput.of_le_csrc raw (le_max_right _ _)
  have hm : (explicitCanonicalMetric F).PosDef := Geometry.explicitCanonicalMetric_posDef
    raw.symm raw.pos
  have hgrid : IsUnit (respGrid jStar F) := isUnit_respGrid_of_rawOutput raw
  have hint : HasIntegrableCoarseBlock P (respCell jStar F t) := by
    have h := Annealed.hasIntegrableCoarseBlock_adapted d hd P γ E Ψ Kg Src raw.stat raw.ell
      jStar raw.hj (explicitCanonicalMetric F) hm t 0
    rwa [Annealed.adaptedCellTranslate_zero] at h
  have hη1 : η ≤ 1 := by linarith only [hη.2]
  -- the three constants of the statement
  set θ : ℝ := (3 : ℝ) ^ (-(Quenched.contrastAlpha γ * (H : ℝ))) with hθdef
  set zz : ℝ := η ^ ((1 : ℝ) / (bigQ d γ : ℝ)) with hzzdef
  have hθ0 : 0 ≤ θ := Real.rpow_nonneg (by norm_num) _
  have hzz0 : 0 ≤ zz := Real.rpow_nonneg hη.1.le _
  have hηzz : η ≤ zz := by
    have h1 : (1 : ℝ) / (bigQ d γ : ℝ) ≤ 1 := by
      rw [div_le_one hQR]
      have : (2 : ℝ) ≤ (bigQ d γ : ℝ) := by exact_mod_cast hQ2
      linarith only [this]
    have := Real.rpow_le_rpow_of_exponent_ge hη.1 hη1 h1
    rw [hzzdef]
    simpa using this
  -- the pathwise ingredients
  have hK00 : 0 ≤ respK0SqPlus P jStar F t := (respK0Sq_nonneg P jStar F t).2
  obtain ⟨-, -, -, hL0, -, hprod⟩ :=
    h11 ε σ Cglob Cprof (max (max Csrc7 CsrcA) Csrc8) Bresp H P E Ψ Kg Src B jStar F s t hε hσ
      raw hcal e he hED hLM
  have hEsq := weakOptimizerEnergy_sq_le_plus d hd γ hγ S hS ε σ Cglob Cprof
    (max (max Csrc7 CsrcA) Csrc8) Bresp H P E Ψ Kg Src B jStar F s t raw e he u hu
  have hMint := (h7 ε σ hε hσ Cglob Cprof Bresp hCglob H P E Ψ Kg Src B jStar F s t raw7).2
  have hAint := (hA ε σ hε hσ Cglob Cprof Bresp hCglob H P E Ψ Kg Src B jStar F s t rawA).2
  have h8' := h8 ε σ hε hσ Cglob Cprof Bresp hCglob H P E Ψ Kg Src B jStar F s t raw8 hcal η hη
    hprof hsrc
  obtain ⟨hSint, hSle⟩ :=
    h9 P (respGrid jStar F) t H (respEhatPlus P jStar F t) (respCoeffPlus F) η hη
      (fun n _ w hw => h8' n w hw)
  obtain ⟨hcint, hcle0⟩ :=
    h10 ε σ Cglob Cprof (max (max Csrc7 CsrcA) Csrc8) Bresp H P E Ψ Kg Src B jStar F s t raw hcal
      η hη hAint hMQ e he u hu
  -- the moment bound for the one-sided all-scale maximum
  have hMabs := respAllScaleMax_le_respAllScaleAbs_ae hd γ P E Ψ Kg Src raw.stat raw.ell
    jStar raw.hj F hm t
  have hMle : ∫ a, respAllScaleMax P γ jStar F t a ^ bigQ d γ ∂P ≤ Cm * zz := by
    have hpow : ∀ᵐ a ∂P, respAllScaleMax P γ jStar F t a ^ bigQ d γ
        ≤ respAllScaleAbs P γ jStar F t a ^ bigQ d γ := by
      filter_upwards [hMabs] with a hle
      exact pow_le_pow_left₀ (respAllScaleMax_nonneg P γ jStar F t a) hle _
    have hcmp := integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun a =>
        pow_nonneg (respAllScaleMax_nonneg P γ jStar F t a) (bigQ d γ)) hAint hpow
    have : Cm * η ≤ Cm * zz := mul_le_mul_of_nonneg_left hηzz hCm.le
    linarith only [hcmp, hMQ, this]
  -- the recentring bound at the exponent `1/Q`
  have hcle : ∫ a, blockVecDot (respRecentrePlus P jStar F t e a (u a))
      (respRecentrePlus P jStar F t e a (u a)) ∂P
      ≤ C10 * (respK0SqPlus P jStar F t * respLsqPlus P jStar F t e) * zz := by
    have hstep : C10 * (respK0SqPlus P jStar F t * respLsqPlus P jStar F t e) *
        η ^ ((2 : ℝ) / (bigQ d γ : ℝ))
        ≤ C10 * (respK0SqPlus P jStar F t * respLsqPlus P jStar F t e) * zz :=
      mul_le_mul_of_nonneg_left
        (rpow_two_le_one η hη.1 hη1 (bigQ d γ : ℝ) hQR)
        (by positivity)
    linarith only [hcle0, hstep]
  -- the engine
  have heng := weakEstimate_arith_engine P (bigQ d γ) hQ2
    (fun a => (3 : ℝ) ^ (-((t : ℝ) / 2)) *
      besovSeminorm t (fun n z =>
        blockMatVecMul (blockSqrt (respM0 F))
          (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
            (optimizerField (respCoeffPlus F a) (u a)) - respYPlus P jStar F t e)))
    (fun a => weakCellSum (respGrid jStar F) t H (respEhatPlus P jStar F t)
        (respCoeffPlus F a) +
      weakAverageSum (respGrid jStar F) t H (Quenched.contrastRho γ) (respEhatPlus P jStar F t)
        (respCoeffPlus F a))
    (fun a => respAllScaleMax P γ jStar F t a)
    (fun a => weakOptimizerEnergy (respCell jStar F t) (respCoeffPlus F a) (u a))
    (fun a => blockVecDot (respRecentrePlus P jStar F t e a (u a))
      (respRecentrePlus P jStar F t e a (u a)))
    (respK0SqPlus P jStar F t) (respLsqPlus P jStar F t e) θ zz cc kk (DD H) Cm C10
    hK00 hL0 hθ0 hcc0 hkk0
    (fun a => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (besovSeminorm_nonneg _ _))
    (fun a => add_nonneg (weakCellSum_nonneg _ _ _ _ _)
      (weakAverageSum_nonneg _ _ _ _ _ _))
    (fun a => respAllScaleMax_nonneg P γ jStar F t a)
    (fun a => weakOptimizerEnergy_nonneg _ _ _)
    (fun a => Response.blockVecDot_self_nonneg _)
    ((pathwise_envelope hd γ P E Ψ Kg Src raw.stat raw.ell jStar raw.hj F hm t).mono
      fun a ha => by
        obtain ⟨Cenv, _hCenv0, _hCenvL, hterms⟩ := ha
        exact besov_pathwise_le_plus P γ hγ jStar H F t e hgrid hint a
          (respAllScaleMax_bddAbove_of_envelope P γ jStar F t a hterms) (u a) (hu a))
    hEsq hSint hSle hMint hMle hcint hcle
  -- identify the integral with the per-family weak energy
  have hEq : respWeakEnergyOf P (respGrid jStar F) t (respM0 F) (respCoeffPlus F)
      (respYPlus P jStar F t e) u
      = ∫ a, ((3 : ℝ) ^ (-((t : ℝ) / 2)) *
          besovSeminorm t (fun n z =>
            blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
                (optimizerField (respCoeffPlus F a) (u a)) -
                respYPlus P jStar F t e))) ^ 2 ∂P := by
    have hpt : ∀ a : CoeffSpace d,
        ((3 : ℝ) ^ (-((t : ℝ) / 2)) *
          besovSeminorm t (fun n z =>
            blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
                (optimizerField (respCoeffPlus F a) (u a)) -
                respYPlus P jStar F t e))) ^ 2
        = (3 : ℝ) ^ (-(t : ℝ)) *
          besovSeminorm t (fun n z =>
            blockMatVecMul (blockSqrt (respM0 F))
              (cellAverage (adaptedCellAtCenter (respGrid jStar F) (t - (n : ℤ)) z)
                (optimizerField (respCoeffPlus F a) (u a)) -
                respYPlus P jStar F t e)) ^ 2 := by
      intro a
      rw [mul_pow, rpow_half_sq]
    simp only [hpt]
    rw [integral_const_mul]
    rfl
  rw [hEq]
  -- the final constant bookkeeping
  have hκ1 := (respKappa_persistence_of_raw d hd γ hγ S hS ε σ hε hσ Cglob Cprof
    (max (max Csrc7 CsrcA) Csrc8) Bresp H P E Ψ Kg Src B jStar F s t raw)
  have hκ0 : 0 ≤ respKappa P jStar F s := le_trans zero_le_one (le_trans hκ1.1 hκ1.2)
  have hz2 : (η ^ ((1 : ℝ) / (2 * (bigQ d γ : ℝ)))) ^ 2 = zz :=
    rpow_sq_eq η hη.1.le (bigQ d γ : ℝ) hQR
  have hAH : (0 : ℝ) ≤ 3 * (256 * DD H + 2 * cc ^ 2 * Cm + kk ^ 2 * C10) := by
    have h1 : (0 : ℝ) ≤ 256 * DD H := mul_nonneg (by norm_num) (hDD H).le
    have h2 : (0 : ℝ) ≤ 2 * cc ^ 2 * Cm := mul_nonneg (by positivity) hCm.le
    have h3 : (0 : ℝ) ≤ kk ^ 2 * C10 := mul_nonneg (by positivity) hC10.le
    linarith only [h1, h2, h3]
  have hbr : (0 : ℝ) ≤ (3 * (256 * DD H + 2 * cc ^ 2 * Cm + kk ^ 2 * C10)) * zz
      + (6 * cc ^ 2) * θ ^ 2 := by
    have h1 : (0 : ℝ) ≤ (3 * (256 * DD H + 2 * cc ^ 2 * Cm + kk ^ 2 * C10)) * zz :=
      mul_nonneg hAH hzz0
    have h2 : (0 : ℝ) ≤ (6 * cc ^ 2) * θ ^ 2 := by positivity
    linarith only [h1, h2]
  have hlift : (respK0SqPlus P jStar F t * respLsqPlus P jStar F t e) *
      ((3 * (256 * DD H + 2 * cc ^ 2 * Cm + kk ^ 2 * C10)) * zz + (6 * cc ^ 2) * θ ^ 2)
      ≤ (C11 * respKappa P jStar F s) *
        ((3 * (256 * DD H + 2 * cc ^ 2 * Cm + kk ^ 2 * C10)) * zz + (6 * cc ^ 2) * θ ^ 2) :=
    mul_le_mul_of_nonneg_right hprod hbr
  refine constant_arith (C11 * (3 * (256 * DD H + 2 * cc ^ 2 * Cm + kk ^ 2 * C10)))
    (C11 * (6 * cc ^ 2)) θ (η ^ ((1 : ℝ) / (2 * (bigQ d γ : ℝ))))
    (respKappa P jStar F s) _ (mul_nonneg hC11.le hAH) (mul_nonneg hC11.le (by positivity))
    hθ0 (Real.rpow_nonneg hη.1.le _) hκ0 ?_
  rw [hz2]
  exact le_trans heng (le_trans hlift (le_of_eq (by ring)))

end

end HCPolySupport.HighContrast.Multiscale
end
