/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.DimensionFloor
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.ProfileConstants
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.BadEventLemmaUmbrella
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.ObservableSwapPayoff
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.ErrorComparison.CubeMonotonicity

/-!
# BadEventCoarseAssemblyFloor

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Centered bad-event assembly at the floor-normalized coarse constant

This ordinary Provider module is the floor-normalized twin of
`BadEvents.BadEventCoarseAssembly`.  It specializes
`CoarseEllipticity.coarse_ellipticity_bounds_dim_floor` -- the constant
selection that clears the dimension floor `(d : ℝ) ^ 6` as well as `1` -- at
the two parameters used by the bad-event argument, and feeds those
specializations into
`BadEventLemmaUmbrella.measureReal_compl_goodLocalEvent_le_full_reassembled`.
It removes that conditional A's three proof-side inputs exactly as the
unnormalized assembly does:

* the centered high-branch comparison comes from
  `ErrorComparison.lambdaSq_originCube_eighth_le` by inversion;
* the high-branch lower-family estimate is the floor-normalized coarse theorem
  at `s = 1/8`;
* the low-branch family of translated estimates comes from the same theorem at
  `s = 1/16` through
  `ObservableSwapPayoff.isLowerIntegerFamilyOrlicz_cubeLowerEllipticityInv_forall_descendant`.

The output is centered at `originCube d m`, carries the extra conjunct `(d : ℝ)
^ 6 ≤ Cbase`, and retains precisely the two branch implications of the
non-linear-term bound.  Translation of the whole good-local-event probability to
the paper's arbitrary spatial translate is outside this module: it is performed
by the frozen successor `Algsuperdiff.Frozen.Section3.bad_event_estimate`,
whose proof engine this module is.

## References

* ABK26, `l.bad.event.lemma`, statement; `e.good.local.events`;
  `p.cg.ellipticity.bounds`.
-/

namespace Algsuperdiff.Section3.Provider.BadEvents

open MeasureTheory
open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3.Cutoff

variable {d : ℕ}

/-- A source-admissibility choice large enough for both the full oscillation
argument and the two floor-normalized coarse-ellipticity specializations.  The
factor `3 / 2` is the model-independent upper bound for `cstar`; the two
entries in the inner maximum respectively open the frozen maximum gate at
`sigma = 1/2` and make the rare scale at most `1/64`. -/
noncomputable def badEventCoarseAdmissibleConstFloor (d : ℕ) (Ccg : ℝ) : ℝ :=
  max (badEventOscLowAdmissibleConst d (2 * Ccg))
    ((3 / 2 : ℝ) * max (Real.exp (2 * Ccg)) (64 * Ccg))

/-- Positivity of the combined admissibility constant. -/
theorem badEventCoarseAdmissibleConstFloor_pos (d : ℕ) {Ccg : ℝ}
    (hCcg : 0 < Ccg) : 0 < badEventCoarseAdmissibleConstFloor d Ccg := by
  have hinner : 0 < max (Real.exp (2 * Ccg)) (64 * Ccg) :=
    (mul_pos (by norm_num) hCcg).trans_le (le_max_right _ _)
  exact (mul_pos (by norm_num) hinner).trans_le (le_max_right _ _)

/-- The integer-power upper gate `gamma ≤ E⁻⁵` implies the fifth-root gate
consumed by the frozen coarse-ellipticity theorem. -/
private theorem le_rpow_neg_fifth_of_gamma_le_zpow_neg_five
    {E gamma : ℝ} (hE : 1 ≤ E) (hgamma : 0 < gamma)
    (hgammaE : gamma ≤ E ^ (-5 : ℤ)) :
    E ≤ gamma ^ (-(1 / 5 : ℝ)) := by
  have hE0 : 0 ≤ E := le_trans (by norm_num) hE
  have hEpos : 0 < E := lt_of_lt_of_le zero_lt_one hE
  have hEpow : E ^ (-5 : ℤ) = (E ^ (5 : ℕ))⁻¹ := by
    rw [zpow_neg]
    norm_cast
  have hgammaE' : gamma ≤ (E ^ (5 : ℕ))⁻¹ := by
    rw [← hEpow]
    exact hgammaE
  have hE5 : E ^ (5 : ℕ) ≤ gamma⁻¹ := by
    rw [le_inv_comm₀ (pow_pos hEpos 5) hgamma]
    exact hgammaE'
  have hroot : E ≤ (gamma⁻¹) ^ (5 : ℝ)⁻¹ := by
    rw [Real.le_rpow_inv_iff_of_pos hE0 (inv_pos.mpr hgamma).le (by norm_num)]
    exact (Real.rpow_natCast E 5).trans_le hE5
  calc
    E ≤ (gamma⁻¹) ^ (5 : ℝ)⁻¹ := hroot
    _ = (gamma⁻¹) ^ (1 / 5 : ℝ) := by norm_num
    _ = (gamma ^ (-1 : ℝ)) ^ (1 / 5 : ℝ) := by rw [Real.rpow_neg_one]
    _ = gamma ^ ((-1 : ℝ) * (1 / 5 : ℝ)) := (Real.rpow_mul hgamma.le _ _).symm
    _ = gamma ^ (-(1 / 5 : ℝ)) := by ring_nf

/-- The explicit source-admissibility choice opens every hypothesis needed to
specialize the floor-normalized frozen coarse theorem at `sigma = 1/2`, first at
`s = 1/8` and then at `s = 1/16`. -/
private theorem frozenCoarseSpecializationGatesFloor
    (M : ABKModel d) {Ccg E : ℝ} (hCcg : 1 ≤ Ccg) (hE : 1 ≤ E)
    (hadm : badEventCoarseAdmissibleConstFloor d Ccg ≤
      E * Algsuperdiff.Section3.Disorder.cstar M)
    (hgammaE : M.gamma ≤ E ^ (-5 : ℤ)) :
    max (Real.exp (Ccg / (1 / 2 : ℝ)))
        (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ E ∧
      E ≤ M.gamma ^ (-(1 / 5 : ℝ)) ∧
      (1 / 8 : ℝ) ∈ Set.Icc
        (M.gamma / 2 + Real.exp
          (-(Ccg⁻¹ * E⁻¹ ^ 2 * M.gamma⁻¹))) 1 ∧
      (1 / 16 : ℝ) ∈ Set.Icc
        (M.gamma / 2 + Real.exp
          (-(Ccg⁻¹ * E⁻¹ ^ 2 * M.gamma⁻¹))) 1 := by
  have hCcg0 : 0 < Ccg := lt_of_lt_of_le zero_lt_one hCcg
  have hE0 : 0 < E := lt_of_lt_of_le zero_lt_one hE
  have hcstar0 : 0 < Algsuperdiff.Section3.Disorder.cstar M :=
    (Algsuperdiff.Section3.Disorder.cstar_characterization M).1
  have hcstar_le : Algsuperdiff.Section3.Disorder.cstar M ≤ 3 / 2 :=
    Algsuperdiff.Section3.Provider.Disorder.cstar_le_three_halves M
  have hadmOsc : badEventOscLowAdmissibleConst d (2 * Ccg) ≤
      E * Algsuperdiff.Section3.Disorder.cstar M :=
    (le_max_left _ _).trans hadm
  have hadmBase : badEventOscAdmissibleConst d (2 * Ccg) ≤
      E * Algsuperdiff.Section3.Disorder.cstar M :=
    (badEventOscAdmissibleConst_le_badEventOscLowAdmissibleConst d
      (by linarith : 0 < 2 * Ccg)).trans hadmOsc
  let A : ℝ := max (Real.exp (2 * Ccg)) (64 * Ccg)
  have hA0 : 0 ≤ A := by
    dsimp only [A]
    exact le_trans (Real.exp_pos _).le (le_max_left _ _)
  have hscaled : (3 / 2 : ℝ) * A ≤
      E * Algsuperdiff.Section3.Disorder.cstar M := by
    exact (le_max_right _ _).trans hadm
  have hA : A ≤ E := by
    have hmul : A * Algsuperdiff.Section3.Disorder.cstar M ≤
        E * Algsuperdiff.Section3.Disorder.cstar M := by
      calc
      A * Algsuperdiff.Section3.Disorder.cstar M ≤ A * (3 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_left hcstar_le hA0
      _ = (3 / 2 : ℝ) * A := by ring
      _ ≤ E * Algsuperdiff.Section3.Disorder.cstar M := hscaled
    exact le_of_mul_le_mul_right hmul hcstar0
  have hexp : Real.exp (2 * Ccg) ≤ E :=
    (le_max_left _ _).trans hA
  have h64C : 64 * Ccg ≤ E :=
    (le_max_right _ _).trans hA
  have hcstarInv : (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ E := by
    rw [inv_le_iff_one_le_mul₀ hcstar0]
    have hthree : (3 : ℝ) ≤ E * Algsuperdiff.Section3.Disorder.cstar M :=
      (le_max_left _ _).trans hadmBase
    nlinarith
  have hmax : max (Real.exp (Ccg / (1 / 2 : ℝ)))
      (Algsuperdiff.Section3.Disorder.cstar M)⁻¹ ≤ E := by
    apply max_le
    · rw [show Ccg / (1 / 2 : ℝ) = 2 * Ccg by ring]
      exact hexp
    · exact hcstarInv
  have hEgamma : E ≤ M.gamma ^ (-(1 / 5 : ℝ)) :=
    le_rpow_neg_fifth_of_gamma_le_zpow_neg_five hE M.shellPrefix.gamma_pos hgammaE
  have hEpow : E ^ (-5 : ℤ) = (E ^ (5 : ℕ))⁻¹ := by
    rw [zpow_neg]
    norm_cast
  have hgammaE' : M.gamma ≤ (E ^ (5 : ℕ))⁻¹ := by
    rw [← hEpow]
    exact hgammaE
  have hE5 : E ^ (5 : ℕ) ≤ M.gamma⁻¹ := by
    rw [le_inv_comm₀ (pow_pos hE0 5) M.shellPrefix.gamma_pos]
    exact hgammaE'
  have h64 : (64 : ℝ) ≤ Ccg⁻¹ * E := by
    have hmul := mul_le_mul_of_nonneg_left h64C (inv_pos.mpr hCcg0).le
    have hcancel : Ccg⁻¹ * (64 * Ccg) = 64 := by
      calc
        Ccg⁻¹ * (64 * Ccg) = 64 * (Ccg⁻¹ * Ccg) := by ring
        _ = 64 := by rw [inv_mul_cancel₀ hCcg0.ne', mul_one]
    rwa [hcancel] at hmul
  have hE3 : E ≤ E ^ (3 : ℕ) := by
    nlinarith [sq_nonneg E, mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1) hE]
  have h64E3 : (64 : ℝ) ≤ Ccg⁻¹ * E ^ (3 : ℕ) :=
    h64.trans (mul_le_mul_of_nonneg_left hE3 (inv_pos.mpr hCcg0).le)
  have hrateMul := mul_le_mul_of_nonneg_left hE5
    (mul_nonneg (inv_pos.mpr hCcg0).le (sq_nonneg E⁻¹))
  have hEinvSq : E⁻¹ ^ 2 * E ^ 2 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hE0.ne', one_pow]
  have hrateIdentity :
      Ccg⁻¹ * E⁻¹ ^ 2 * E ^ (5 : ℕ) = Ccg⁻¹ * E ^ (3 : ℕ) := by
    calc
      Ccg⁻¹ * E⁻¹ ^ 2 * E ^ (5 : ℕ) =
          Ccg⁻¹ * (E⁻¹ ^ 2 * E ^ 2) * E ^ (3 : ℕ) := by ring
      _ = Ccg⁻¹ * E ^ (3 : ℕ) := by rw [hEinvSq, mul_one]
  have hrate : (64 : ℝ) ≤ Ccg⁻¹ * E⁻¹ ^ 2 * M.gamma⁻¹ := by
    exact h64E3.trans (by simpa only [hrateIdentity] using hrateMul)
  have hexpRare : Real.exp (-(Ccg⁻¹ * E⁻¹ ^ 2 * M.gamma⁻¹)) ≤ 1 / 64 := by
    calc
      Real.exp (-(Ccg⁻¹ * E⁻¹ ^ 2 * M.gamma⁻¹)) ≤ Real.exp (-64) :=
        Real.exp_le_exp.2 (neg_le_neg hrate)
      _ = (Real.exp 64)⁻¹ := by rw [Real.exp_neg]
      _ ≤ (64 : ℝ)⁻¹ := by
        exact inv_anti₀ (by norm_num)
          (by nlinarith [Real.add_one_le_exp (64 : ℝ)])
      _ = 1 / 64 := by norm_num
  have hgamma16 : M.gamma ≤ 1 / 16 :=
    gamma_le_one_sixteenth_of_admissible M hadmBase hgammaE
  have hwindow16 : (1 / 16 : ℝ) ∈ Set.Icc
      (M.gamma / 2 + Real.exp
        (-(Ccg⁻¹ * E⁻¹ ^ 2 * M.gamma⁻¹))) 1 := by
    constructor
    · nlinarith
    · norm_num
  have hwindow8 : (1 / 8 : ℝ) ∈ Set.Icc
      (M.gamma / 2 + Real.exp
        (-(Ccg⁻¹ * E⁻¹ ^ 2 * M.gamma⁻¹))) 1 := by
    constructor
    · exact hwindow16.1.trans (by norm_num)
    · norm_num
  exact ⟨hmax, hEgamma, hwindow8, hwindow16⟩

/-- The centered weighted comparison required by the high ellipticity branch,
obtained by applying the descendant inequality to `lambdaSq` and inverting its
two positive sides. -/
private theorem cubeLowerEllipticityInv_originCube_eighth_le_floor
    (M : ABKModel d) {m n : ℤ} (hmn : m ≤ n) (omega : CutoffSample d) :
    cubeLowerEllipticityInv M (originCube d m) n (1 / 8) (by norm_num)
        exponentTwo omega ≤
      (3 : ℝ) ^ ((1 / 4 : ℝ) * scaleGapPos m n) *
        Algsuperdiff.Section3.Observable.cutoffLowerEllipticityInv
          M n n (1 / 8) (by norm_num) exponentTwo omega := by
  let : NeZero d := neZeroOfModel M
  let F : Ch02.TriadicCoeffFamily d :=
    coefficientCutoffTriadicCoeffFamily M n omega
  have hlambda :=
    Algsuperdiff.Section3.Provider.ErrorComparison.lambdaSq_originCube_eighth_le
      F hmn
  have hmpos : 0 < Ch02.lambdaSq (originCube d m) (1 / 8) (.finite 2) F :=
    Ch02.lambdaSq_pos _ F (by norm_num) (by norm_num)
  have hnpos : 0 < Ch02.lambdaSq (originCube d n) (1 / 8) (.finite 2) F :=
    Ch02.lambdaSq_pos _ F (by norm_num) (by norm_num)
  have hinv :
      (Ch02.lambdaSq (originCube d m) (1 / 8) (.finite 2) F)⁻¹ ≤
        (3 : ℝ) ^ (((n : ℝ) - (m : ℝ)) / 4) *
          (Ch02.lambdaSq (originCube d n) (1 / 8) (.finite 2) F)⁻¹ := by
    rw [inv_le_iff_one_le_mul₀' hmpos]
    have hmul := mul_le_mul_of_nonneg_right hlambda (inv_pos.mpr hnpos).le
    have hone : (1 : ℝ) ≤
        ((3 : ℝ) ^ (((n : ℝ) - (m : ℝ)) / 4) *
          Ch02.lambdaSq (originCube d m) (1 / 8) (.finite 2) F) *
            (Ch02.lambdaSq (originCube d n) (1 / 8) (.finite 2) F)⁻¹ := by
      rwa [mul_inv_cancel₀ hnpos.ne'] at hmul
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hone
  rw [congrFun (cubeLowerEllipticityInv_eq_literal M (originCube d m) n
      (1 / 8) (by norm_num) exponentTwo) omega,
    congrFun (Algsuperdiff.Section3.Observable.cutoffLowerEllipticityInv_eq_literal
      M n n (1 / 8) (by norm_num) exponentTwo) omega]
  rw [show cubeLowerEllipticityInvLiteral M (originCube d m) n (1 / 8)
      exponentTwo omega =
        (Ch02.lambdaSq (originCube d m) (1 / 8) (.finite 2) F)⁻¹ by
    simp only [F]
    rw [← exponentTwo_val,
      ← cubeLowerEllipticityInvLiteral_inv_eq_lambdaSq, inv_inv]]
  rw [show Algsuperdiff.Section3.Observable.cutoffLowerEllipticityInvLiteral
      M n n (1 / 8) exponentTwo omega =
        (Ch02.lambdaSq (originCube d n) (1 / 8) (.finite 2) F)⁻¹ by
    rw [← cubeLowerEllipticityInvLiteral_originCube]
    simp only [F]
    rw [← exponentTwo_val,
      ← cubeLowerEllipticityInvLiteral_inv_eq_lambdaSq, inv_inv]]
  rw [scaleGapPos_of_le hmn]
  rw [show (1 / 4 : ℝ) * ((n : ℝ) - (m : ℝ)) =
    ((n : ℝ) - (m : ℝ)) / 4 by ring]
  exact hinv

/-- **The centered bad-event umbrella at the floor-normalized constant.**  The
floor-normalized coarse theorem supplies both ellipticity branches, and the
selected constant `Cbase` carries `1 ≤ Cbase` together with the dimension floor
`(d : ℝ) ^ 6 ≤ Cbase`.  The only branch-specific assumptions left to the caller
are the two non-linear-term implications. -/
theorem
    exists_measureReal_compl_goodLocalEvent_originCube_le_of_frozenCoarse_dimFloor
    (d : ℕ) :
    ∃ Cbase : ℝ, 1 ≤ Cbase ∧ (d : ℝ) ^ 6 ≤ Cbase ∧
      ∀ (M : ABKModel d) (m n m0 : ℤ)
        (E : {E : ℝ // 1 ≤ E}),
        Algsuperdiff.Frozen.Section3.inductionState M (m0 - 1) E →
        n ≤ m0 - 1 →
        badEventCoarseAdmissibleConstFloor d Cbase ≤
          (E : ℝ) * Algsuperdiff.Section3.Disorder.cstar M →
        M.gamma ≤ (E : ℝ) ^ (-5 : ℤ) →
        (n < m →
          1 ≤ badEventOscFullRate M (2 * Cbase) (originCube d m) n) →
        (n < m →
          (d : ℝ) * ((m : ℝ) - (n : ℝ)) * Real.log 3 +
              Real.exp ((1 / 8 : ℝ) *
                (Cbase⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹)) ≤
            Real.exp ((1 / 4 : ℝ) *
              (Cbase⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) →
        (cutoffSampleLaw M).toMeasure.real
            (goodLocalEvent M (2 * Cbase) (originCube d m) n)ᶜ ≤
          Real.exp
              (-(badEventOscFullRate M (2 * Cbase) (originCube d m) n)) +
            Real.exp (-Real.exp ((1 / 8 : ℝ) *
              (Cbase⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) := by
  obtain ⟨Cbase, hCbase1, hCbased, hcoarse⟩ :=
    Algsuperdiff.Section3.Provider.CoarseEllipticity.coarse_ellipticity_bounds_dim_floor d
  refine ⟨Cbase, hCbase1, hCbased, ?_⟩
  intro M m n m0 E hS hn hadm hgammaE hrestrict hgap
  obtain ⟨hmax, hEgamma, hwindow8, hwindow16⟩ :=
    frozenCoarseSpecializationGatesFloor M hCbase1 E.property hadm hgammaE
  have hSlocal : Algsuperdiff.Frozen.Section3.inductionState M (n - 1) E :=
    ⟨fun j hj => hS.1 j (by omega), fun j hj => hS.2 j (by omega)⟩
  have hcg8 :=
    (hcoarse M n E hSlocal (1 / 2) (by constructor <;> norm_num)
      hmax hEgamma exponentTwo (1 / 8) hwindow8).1
  have hcg16 :=
    (hcoarse M n E hSlocal (1 / 2) (by constructor <;> norm_num)
      hmax hEgamma exponentTwo (1 / 16) hwindow16).1
  apply measureReal_compl_goodLocalEvent_le_full_reassembled M hCbase1
    (originCube d m) hS hn
  · exact (le_max_left _ _).trans hadm
  · exact hgammaE
  · intro hnm
    exact hrestrict (by simpa only [originCube] using hnm)
  · intro hmn omega
    exact cubeLowerEllipticityInv_originCube_eighth_le_floor M
      (by simpa only [originCube] using hmn) omega
  · intro _hmn
    exact hcg8
  · intro hnm
    exact isLowerIntegerFamilyOrlicz_cubeLowerEllipticityInv_forall_descendant
      M _ (originCube d m) (by simpa only [originCube] using le_of_lt hnm)
      (n - 1) (1 / 16) (by norm_num) exponentTwo
      (Algsuperdiff.Section3.Annealed.sigmaBar M (n - 1) : ℝ)
      (Algsuperdiff.Section3.lowerEllipticityProfile Cbase M.gamma (1 / 16)
        exponentTwo)
      (Real.exp (-(Cbase⁻¹ * ((E : ℝ)⁻¹) ^ 2 * M.gamma⁻¹))) hcg16
  · intro hnm
    exact hgap (by simpa only [originCube] using hnm)

end Algsuperdiff.Section3.Provider.BadEvents
