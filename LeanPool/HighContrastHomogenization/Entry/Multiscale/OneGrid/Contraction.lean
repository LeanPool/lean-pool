/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Multiscale.OneGrid.ContractionSums

/-!
# High-contrast homogenization: Entry.Multiscale.OneGrid.Contraction

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Step 2 — profile contraction

Group E of the printed proof (`p.fixed.geometry.one.grid.propagation`), third part: the contraction
reduction and **conjunct 2**, `e.fixed.geometry.profile.contraction`.

Part of the proof of the result stated in
`HCPoly/Entry/Statements/OneGridPropagation.lean`.  Conventions of this group:
`q = 𝒬(𝔪)` is `Geometry.explicitRoundedGrid jStar metric` at every loss, history, profile and drift;
`metric` (not `m`) names the positive matrix, because `m`, `n`, `m₀` are generations; the
source lower scale `e.source.lower.scale` is carried exactly by the
source-facing file `HCPoly/Entry/OneGridPropagation.lean`; this group's stronger internal
algebraic and history lemmas omit an unused threshold, and this group's generic
integration helpers take finiteness, integrability or measurability inputs that are proved
at their actual use sites, not extra premises of the printed proposition.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- The first inequality of `e.fixed.geometry.profile.contraction.reduction`
(`p.fixed.geometry.one.grid.propagation`): add the new fluctuations, the mean terms and the
transported
initial-history term. -/
theorem profile_contraction_reduction (d : ℕ) (hd : 2 ≤ d) (γ : ℝ)
    (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
          (S : CoeffSpace d → ℝ),
          IsProbabilityMeasure P →
          IsStationaryLaw P →
          IsUnitRangeLaw P →
          CoarseEllipticityDagger P γ E Ψ K S →
          ∀ (h : ℕ), 2 * bigQ d γ ≤ h →
            ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
              ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
                ∀ (metric : Mat d), metric.PosDef →
                  ∀ n m : ℤ, (jStar : ℤ) ≤ n → n + (h : ℤ) ≤ m →
                    profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (m + (h : ℤ)) ≤
                      ((3 : ℝ) ^ (-((1 - γ) / 4) * (h : ℝ)) +
                              (2 : ℝ) ^ (bigQ d γ - 1) *
                                ((3 : ℝ) ^ d * (bigQ d γ : ℝ)) ^ bigQ d γ *
                                (3 : ℝ) ^ (-((bigQ d γ : ℝ) * (d : ℝ) / 2) * (h : ℝ))) *
                            Real.exp ((bigQ d γ : ℝ) *
                              synchCharge P
                                (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m) *
                            profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                          C * (Real.exp ((bigQ d γ : ℝ) *
                            synchCharge P
                              (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m) - 1) := by
  obtain ⟨Csrc, hCsrc, C3, hC3, hnew⟩ := new_fluctuation_sum_le d hd γ hγ
  obtain ⟨C1, hC1, htr⟩ := meanHistory_transport_le d hd γ hγ
  obtain ⟨C2, hC2, hup⟩ := meanPenalty_upper_block_sum_le d hd γ hγ
  refine ⟨Csrc, hCsrc, C1 + C2 + C3, by linarith only [hC1, hC2, hC3], ?_⟩
  intro P E Ψ K S hP hstat hunit hdag h hh jStar hjStar hsrc metric hmetric n m hn hnm
  let := hP
  set q := Geometry.explicitRoundedGrid jStar metric with hq
  have hQ2 : 2 ≤ bigQ d γ := bigQ_two_le d γ hγ
  have hh1 : 1 ≤ h := by omega
  have hnm' : n ≤ m := by omega
  let w : ℝ → ℝ := fun x => (3 : ℝ) ^ (-((1 - γ) / 4) * x)
  let p : ℤ → ℤ → ℝ := fun j k => meanPenalty (bigQ d γ) (relMean P q j k)
  let v : ℤ → ℝ := fun j => ∫ a, absSchattenNorm (bigQ d γ : ℝ)
    (normalizedFluctuationSelf P q j a) ^ bigQ d γ ∂P
  have hw (x : ℝ) : 0 ≤ w x := Real.rpow_nonneg (by norm_num) _
  let e0 : ℝ := Real.exp ((bigQ d γ : ℝ) * detIncrement P q m (m + (h : ℤ)))
  let bigE : ℝ := Real.exp ((bigQ d γ : ℝ) * synchCharge P q (h : ℤ) m)
  let AH : ℝ := (2 : ℝ) ^ (bigQ d γ - 1) * ((3 : ℝ) ^ d * (bigQ d γ : ℝ)) ^ bigQ d γ *
      (3 : ℝ) ^ (-((bigQ d γ : ℝ) * (d : ℝ) / 2) * (h : ℝ))
  change profile P γ q jStar n (m + (h : ℤ)) ≤
      (w (h : ℝ) + AH) * bigE * profile P γ q jStar n m + (C1 + C2 + C3) * (bigE - 1)
  have hsync : detIncrement P q m (m + (h : ℤ)) ≤ synchCharge P q (h : ℤ) m := by
    have hbound := logDetLoss_le_synchronizedLogDetLoss d hd γ hγ P E Ψ K S hP hstat hunit hdag
      h hh1 jStar hjStar metric hmetric m (m + (h : ℤ)) (by omega) (by omega) le_rfl
    simpa only [add_sub_cancel_right] using hbound
  have hΔnonneg : 0 ≤ detIncrement P q m (m + (h : ℤ)) :=
    Annealed.logDetLoss_nonneg d hd P γ E Ψ K S hstat hdag jStar hjStar metric hmetric
      m (m + (h : ℤ)) (by omega) (by omega)
  have he0_ge1 : 1 ≤ e0 := Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) hΔnonneg)
  have hEge1 : 1 ≤ bigE := Real.one_le_exp (mul_nonneg (Nat.cast_nonneg _) (hΔnonneg.trans hsync))
  have he0_le_E : e0 ≤ bigE :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsync (Nat.cast_nonneg _))
  -- nonnegativity facts
  have hmean0 := meanHistory_nonneg d hd γ hγ P E Ψ K S hP hstat hunit hdag
    jStar hjStar metric hmetric (jStar : ℤ) n le_rfl hn
  have hfluc : 0 ≤ fluctuationHistory P γ q jStar n := by
    apply integral_nonneg
    intro a
    apply Real.iSup_nonneg
    intro j
    apply Real.iSup_nonneg
    intro _hj
    apply mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    apply Real.iSup_nonneg
    intro z
    apply Real.iSup_nonneg
    intro _hz
    exact (bigQ_even d γ).pow_nonneg _
  have hhistory : 0 ≤ history P γ q jStar n := add_nonneg hfluc hmean0
  have hp_nm := (Annealed.adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag
    jStar hjStar metric hmetric n m hn hnm').2.2.2.2.2
  have hprof0 : 0 ≤ profile P γ q jStar n m := by
    unfold profile
    apply add_nonneg
    · exact add_nonneg (mul_nonneg (mul_nonneg (hw _) (by linarith only [hp_nm])) hhistory)
        (meanHistory_nonneg d hd γ hγ P E Ψ K S hP hstat hunit hdag
          jStar hjStar metric hmetric n m hn hnm')
    · exact Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (hw _) (Real.exp_nonneg _))
        (integral_nonneg fun _ => (bigQ_even d γ).pow_nonneg _)
  -- weight-splitting helper
  have hsplit (x : ℝ) : w (((h : ℤ) : ℝ) + x) = w (h : ℝ) * w x := by
    dsimp only [w]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  -- initial-history term
  have hadv_n : 1 + p n (m + (h : ℤ)) ≤ e0 * (1 + p n m) := by
    have hh' := meanPenalty_normalizedMean_advance d hd γ hγ P E Ψ K S hP hstat hunit hdag
      jStar hjStar metric hmetric n m (m + (h : ℤ)) hn hnm' (by omega)
    change p n (m + (h : ℤ)) ≤ e0 * p n m + e0 - 1 at hh'
    linarith only [hh']
  have hfirst : w (((m + (h : ℤ) : ℤ) : ℝ) - (n : ℝ)) * (1 + p n (m + (h : ℤ))) *
      history P γ q jStar n ≤
      w (h : ℝ) * e0 * (w ((m : ℝ) - (n : ℝ)) * (1 + p n m) * history P γ q jStar n) := by
    have hweight : w (((m + (h : ℤ) : ℤ) : ℝ) - (n : ℝ)) =
        w (h : ℝ) * w ((m : ℝ) - (n : ℝ)) := by
      have heq := hsplit ((m : ℝ) - (n : ℝ))
      rw [show (((m + (h : ℤ) : ℤ) : ℝ) - (n : ℝ)) = ((h : ℤ) : ℝ) + ((m : ℝ) - (n : ℝ)) by
        push_cast; ring]
      exact heq
    rw [hweight]
    have h' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hadv_n (mul_nonneg (hw (h : ℝ)) (hw ((m : ℝ) - (n : ℝ)))))
      hhistory
    nlinarith only [h']
  -- old fluctuation sum: exact rewrite via additivity of detIncrement
  have hsumFold : (∑ j ∈ Finset.Icc (n + 1) m,
      w (((m + (h : ℤ) : ℤ) : ℝ) - (j : ℝ)) *
        Real.exp ((bigQ d γ : ℝ) * detIncrement P q j (m + (h : ℤ))) * v j) =
      w (h : ℝ) * e0 * ∑ j ∈ Finset.Icc (n + 1) m,
        w ((m : ℝ) - (j : ℝ)) * Real.exp ((bigQ d γ : ℝ) * detIncrement P q j m) * v j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hweight : w (((m + (h : ℤ) : ℤ) : ℝ) - (j : ℝ)) =
        w (h : ℝ) * w ((m : ℝ) - (j : ℝ)) := by
      have heq := hsplit ((m : ℝ) - (j : ℝ))
      rw [show (((m + (h : ℤ) : ℤ) : ℝ) - (j : ℝ)) = ((h : ℤ) : ℝ) + ((m : ℝ) - (j : ℝ)) by
        push_cast; ring]
      exact heq
    rw [hweight, ← logDetLoss_add P q j m (m + (h : ℤ)), mul_add, Real.exp_add]
    dsimp only [e0]
    ring
  -- old / new mean sums via the black-box siblings
  have hmeanOld : (∑ j ∈ Finset.Ico n m,
      w (((m + (h : ℤ) : ℤ) : ℝ) - 1 - (j : ℝ)) * p j (m + (h : ℤ))) ≤
      w (h : ℝ) * e0 * meanHistory P γ q n m + C1 * (e0 - 1) :=
    htr P E Ψ K S hP hstat hunit hdag h hh jStar hjStar metric hmetric n m hn hnm
  have hmeanNew : (∑ j ∈ Finset.Ico m (m + (h : ℤ)),
      w (((m + (h : ℤ) : ℤ) : ℝ) - 1 - (j : ℝ)) * p j (m + (h : ℤ))) ≤
      C2 * (bigE - 1) :=
    hup P E Ψ K S hP hstat hunit hdag h hh jStar hjStar metric hmetric n m hn hnm
  -- new fluctuation sum via new_fluctuation_sum_le
  have hFnew_le : (∑ j ∈ Finset.Icc (m + 1) (m + (h : ℤ)),
      w (((m + (h : ℤ) : ℤ) : ℝ) - (j : ℝ)) *
        Real.exp ((bigQ d γ : ℝ) * detIncrement P q j (m + (h : ℤ))) * v j) ≤
      AH * bigE * profile P γ q jStar n m + C3 * (bigE - 1) :=
    hnew P E Ψ K S hP hstat hunit hdag h hh jStar hjStar hsrc metric hmetric n m hn hnm
  -- decompose profile at m + h and at m
  have hLHSeq : profile P γ q jStar n (m + (h : ℤ)) =
      w (((m + (h : ℤ) : ℤ) : ℝ) - (n : ℝ)) * (1 + p n (m + (h : ℤ))) * history P γ q jStar n +
        (∑ j ∈ Finset.Ico n (m + (h : ℤ)),
          w (((m + (h : ℤ) : ℤ) : ℝ) - 1 - (j : ℝ)) * p j (m + (h : ℤ))) +
        ∑ j ∈ Finset.Icc (n + 1) (m + (h : ℤ)),
          w (((m + (h : ℤ) : ℤ) : ℝ) - (j : ℝ)) *
            Real.exp ((bigQ d γ : ℝ) * detIncrement P q j (m + (h : ℤ))) * v j := by
    unfold profile meanHistory
    rfl
  have hRHSeq : profile P γ q jStar n m =
      w ((m : ℝ) - (n : ℝ)) * (1 + p n m) * history P γ q jStar n +
        meanHistory P γ q n m +
        ∑ j ∈ Finset.Icc (n + 1) m,
          w ((m : ℝ) - (j : ℝ)) * Real.exp ((bigQ d γ : ℝ) * detIncrement P q j m) * v j := by
    unfold profile
    rfl
  have hMunion : Finset.Ico n m ∪ Finset.Ico m (m + (h : ℤ)) = Finset.Ico n (m + (h : ℤ)) :=
    Finset.Ico_union_Ico_eq_Ico hnm' (by omega)
  have hMdisj : Disjoint (Finset.Ico n m) (Finset.Ico m (m + (h : ℤ))) :=
    Finset.Ico_disjoint_Ico_consecutive n m (m + (h : ℤ))
  have hMsplit : (∑ j ∈ Finset.Ico n (m + (h : ℤ)),
      w (((m + (h : ℤ) : ℤ) : ℝ) - 1 - (j : ℝ)) * p j (m + (h : ℤ))) =
      (∑ j ∈ Finset.Ico n m,
        w (((m + (h : ℤ) : ℤ) : ℝ) - 1 - (j : ℝ)) * p j (m + (h : ℤ))) +
      (∑ j ∈ Finset.Ico m (m + (h : ℤ)),
        w (((m + (h : ℤ) : ℤ) : ℝ) - 1 - (j : ℝ)) * p j (m + (h : ℤ))) := by
    rw [← hMunion, Finset.sum_union hMdisj]
  have hFunion : Finset.Icc (n + 1) m ∪ Finset.Icc (m + 1) (m + (h : ℤ)) =
      Finset.Icc (n + 1) (m + (h : ℤ)) := by
    ext x
    simp only [Finset.mem_union, Finset.mem_Icc]
    omega
  have hFdisj : Disjoint (Finset.Icc (n + 1) m) (Finset.Icc (m + 1) (m + (h : ℤ))) :=
    Finset.disjoint_left.2 (by
      intro x hx hx'
      simp only [Finset.mem_Icc] at hx hx'
      omega)
  have hFsplit : (∑ j ∈ Finset.Icc (n + 1) (m + (h : ℤ)),
      w (((m + (h : ℤ) : ℤ) : ℝ) - (j : ℝ)) *
        Real.exp ((bigQ d γ : ℝ) * detIncrement P q j (m + (h : ℤ))) * v j) =
      (∑ j ∈ Finset.Icc (n + 1) m,
        w (((m + (h : ℤ) : ℤ) : ℝ) - (j : ℝ)) *
          Real.exp ((bigQ d γ : ℝ) * detIncrement P q j (m + (h : ℤ))) * v j) +
      (∑ j ∈ Finset.Icc (m + 1) (m + (h : ℤ)),
        w (((m + (h : ℤ) : ℤ) : ℝ) - (j : ℝ)) *
          Real.exp ((bigQ d γ : ℝ) * detIncrement P q j (m + (h : ℤ))) * v j) := by
    rw [← hFunion, Finset.sum_union hFdisj]
  have hdistrib : w (h : ℝ) * e0 * (w ((m : ℝ) - (n : ℝ)) * (1 + p n m) * history P γ q jStar n) +
      w (h : ℝ) * e0 * meanHistory P γ q n m +
      w (h : ℝ) * e0 * (∑ j ∈ Finset.Icc (n + 1) m,
        w ((m : ℝ) - (j : ℝ)) * Real.exp ((bigQ d γ : ℝ) * detIncrement P q j m) * v j) =
      w (h : ℝ) * e0 * profile P γ q jStar n m := by
    rw [hRHSeq]; ring
  have hstepE : w (h : ℝ) * e0 * profile P γ q jStar n m ≤
      w (h : ℝ) * bigE * profile P γ q jStar n m :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he0_le_E (hw _)) hprof0
  have hstepC1 : C1 * (e0 - 1) ≤ C1 * (bigE - 1) :=
    mul_le_mul_of_nonneg_left (by linarith only [he0_le_E]) hC1.le
  have hdistrib2 : (w (h : ℝ) + AH) * bigE * profile P γ q jStar n m =
      w (h : ℝ) * bigE * profile P γ q jStar n m + AH * bigE * profile P γ q jStar n m := by
    ring
  rw [hLHSeq, hMsplit, hFsplit]
  linarith only [hfirst, hmeanOld, hmeanNew, hsumFold, hFnew_le, hdistrib, hstepE, hstepC1,
    hdistrib2]

/-- **Conjunct 2**, `e.fixed.geometry.profile.contraction`
(`p.fixed.geometry.one.grid.propagation`): the contraction constant is `1/8` for **every** natural
`h ≥ 2Q`. -/
theorem profile_contraction (d : ℕ) (hd : 2 ≤ d) (γ : ℝ) (hγ : γ ∈ Set.Ico (0 : ℝ) 1) :
    ∃ Csrc : ℝ, 0 < Csrc ∧
      ∃ C : ℝ, 0 < C ∧
        ∀ (P : Measure (CoeffSpace d)) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ)
          (S : CoeffSpace d → ℝ),
          IsProbabilityMeasure P →
          IsStationaryLaw P →
          IsUnitRangeLaw P →
          CoarseEllipticityDagger P γ E Ψ K S →
          ∀ (h : ℕ), 2 * bigQ d γ ≤ h →
            ∀ (jStar : ℕ), 2 * d ≤ 3 ^ jStar →
              ⌈Csrc * Real.logb 3 (2 * K)⌉ ≤ (jStar : ℤ) →
                ∀ (metric : Mat d), metric.PosDef →
                  ∀ n m : ℤ, (jStar : ℤ) ≤ n → n + (h : ℤ) ≤ m →
                    profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (m + (h : ℤ)) ≤
                      1 / 8 *
                          Real.exp ((bigQ d γ : ℝ) *
                            synchCharge P
                              (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m) *
                          profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
                        C * (Real.exp ((bigQ d γ : ℝ) *
                          synchCharge P
                            (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m) - 1) := by
  obtain ⟨Csrc, hCsrc, C, hC, hred⟩ := profile_contraction_reduction d hd γ hγ
  refine ⟨Csrc, hCsrc, C, hC, ?_⟩
  intro P E Ψ K S hP hstat hunit hdag h hh jStar hjStar hsrc metric hmetric n m hn hnm
  let := hP
  have hnm2 : n ≤ m := by omega
  have hmean0 := meanHistory_nonneg d hd γ hγ P E Ψ K S hP hstat hunit hdag
    jStar hjStar metric hmetric (jStar : ℤ) n le_rfl hn
  have hfluc : 0 ≤ fluctuationHistory P γ (Geometry.explicitRoundedGrid jStar metric) jStar n := by
    apply integral_nonneg
    intro a
    apply Real.iSup_nonneg
    intro j
    apply Real.iSup_nonneg
    intro _hj
    apply mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    apply Real.iSup_nonneg
    intro z
    apply Real.iSup_nonneg
    intro _hz
    exact (bigQ_even d γ).pow_nonneg _
  have hhistory : 0 ≤ history P γ (Geometry.explicitRoundedGrid jStar metric) jStar n :=
    add_nonneg hfluc hmean0
  have hw (x : ℝ) : 0 ≤ (3 : ℝ) ^ (-((1 - γ) / 4) * x) := Real.rpow_nonneg (by norm_num) _
  have hprof0 : 0 ≤ profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m := by
    have hp := (Annealed.adaptedMean_order_consequences d hd P γ E Ψ K S hstat hdag
      jStar hjStar metric hmetric n m hn hnm2).2.2.2.2.2
    unfold profile
    apply add_nonneg
    · exact add_nonneg (mul_nonneg (mul_nonneg (hw _) (by linarith only [hp])) hhistory)
        (meanHistory_nonneg d hd γ hγ P E Ψ K S hP hstat hunit hdag
          jStar hjStar metric hmetric n m hn hnm2)
    · exact Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (hw _) (Real.exp_nonneg _))
        (integral_nonneg fun _ => (bigQ_even d γ).pow_nonneg _)
  have hcoef := contraction_coefficient_lt d hd γ hγ h hh
  have hE : 0 ≤ Real.exp ((bigQ d γ : ℝ) *
      synchCharge P (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m) :=
    Real.exp_nonneg _
  calc profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n (m + (h : ℤ))
      ≤ ((3 : ℝ) ^ (-((1 - γ) / 4) * (h : ℝ)) +
              (2 : ℝ) ^ (bigQ d γ - 1) * ((3 : ℝ) ^ d * (bigQ d γ : ℝ)) ^ bigQ d γ *
                (3 : ℝ) ^ (-((bigQ d γ : ℝ) * (d : ℝ) / 2) * (h : ℝ))) *
            Real.exp ((bigQ d γ : ℝ) *
              synchCharge P (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m) *
            profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
          C * (Real.exp ((bigQ d γ : ℝ) *
            synchCharge P (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m) - 1) :=
        hred P E Ψ K S hP hstat hunit hdag h hh jStar hjStar hsrc metric hmetric n m hn hnm
    _ ≤ 1 / 8 *
            Real.exp ((bigQ d γ : ℝ) *
              synchCharge P (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m) *
            profile P γ (Geometry.explicitRoundedGrid jStar metric) jStar n m +
          C * (Real.exp ((bigQ d γ : ℝ) *
            synchCharge P (Geometry.explicitRoundedGrid jStar metric) (h : ℤ) m) - 1) :=
        by
          have hstep := mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcoef.le hE) hprof0
          linarith only [hstep]


end

end HCPolySupport.HighContrast.Multiscale
