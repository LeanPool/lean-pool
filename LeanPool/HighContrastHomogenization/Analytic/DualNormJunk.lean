/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Setup.AnalyticCarriers

/-!
# High-contrast homogenization: Analytic.DualNormJunk

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The dual norms where the printed pairing diverges

The dual norms `negSobolevNorm` and `negOneNorm` of
`e.physical.negative.norm` are suprema of per-test normalized pairings.
A pairing that is not absolutely convergent has no printed value; a totalized
Bochner integral returns `0` for it, and a supremum built on that convention can
fall below the printed supremum, so an estimate bounding it can be satisfied by
the divergence itself.  `dualPairing` returns `⊤` off the integrable branch
instead, and the first two sections record what that does: a single admissible
test with a divergent pairing sends the whole dual norm to `⊤`, so such an
estimate is false rather than satisfiable.

The third section checks that the index family of each supremum is nonempty — the
zero test field is admissible — so neither norm is `0` through an empty supremum.
The fourth gives the characterization a consumer needs: each dual norm dominates
the absolute value of the normalized pairing against every admissible test, the
absolute value costing nothing because the admissible family is closed under
negation.  The last section checks that on the absolutely convergent branch the
values are exactly the printed ones.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The convention the `⊤` branch replaces

`negSobolevNorm` and `negOneNorm` are suprema of per-test pairings.  Under a
totalized Bochner integral a pairing that is not absolutely convergent
contributes the value `0` to the supremum, so a field with a divergent pairing
against an admissible test is assigned a dual norm no larger than the supremum
over the remaining tests: the norm is underestimated and the estimates that
bound it are satisfied by that failure.  The first lemma is that mechanism; the
rest is what `dualPairing` does instead. -/

/-- The mechanism: on a pairing that is not absolutely convergent, the
totalized real average vanishes. -/
theorem volumeAverage_eq_zero_of_not_integrableOn (V : Set (Vec d))
    {f : Vec d → ℝ} (h : ¬ IntegrableOn f V volume) :
    volumeAverage V f = 0 := by
  unfold volumeAverage
  rw [integral_undef h, mul_zero]

/-- The mechanism, in the form in which it entered the dual norm: the discarded
per-test contribution of the previous encoding. -/
theorem ofReal_volumeAverage_vecDot_eq_zero_of_not_integrableOn
    (V : Set (Vec d)) (F ψ : Vec d → Vec d)
    (h : ¬ IntegrableOn (fun x => vecDot (F x) (ψ x)) V volume) :
    ENNReal.ofReal (volumeAverage V fun x => vecDot (F x) (ψ x)) = 0 := by
  rw [volumeAverage_eq_zero_of_not_integrableOn V h, ENNReal.ofReal_zero]

/-! ## The pairing -/

/-- A divergent pairing is `∞`. -/
theorem dualPairing_eq_top_of_not_integrableOn (V : Set (Vec d))
    (F ψ : Vec d → Vec d)
    (h : ¬ IntegrableOn (fun x => vecDot (F x) (ψ x)) V volume) :
    dualPairing V F ψ = ⊤ := by
  unfold dualPairing
  rw [ite_eq_right h]

/-- On an absolutely convergent pairing the value is the printed normalized
pairing: no value that the reference text writes is changed. -/
theorem dualPairing_eq_ofReal (V : Set (Vec d)) (F ψ : Vec d → Vec d)
    (h : IntegrableOn (fun x => vecDot (F x) (ψ x)) V volume) :
    dualPairing V F ψ =
      ENNReal.ofReal (volumeAverage V fun x => vecDot (F x) (ψ x)) := by
  unfold dualPairing
  rw [ite_eq_left h]

/-- Fail-closed: a single admissible test with a divergent pairing sends the
whole dual norm to `∞`, so an estimate bounding it by a finite quantity is
false rather than satisfiable. -/
theorem negSobolevNorm_eq_top_of_not_integrableOn (V : Set (Vec d)) (s : ℝ)
    (F ψ : Vec d → Vec d) (hψ : IsLocalVecTest V ψ) (hnorm : hsNormSq V s ψ ≤ 1)
    (h : ¬ IntegrableOn (fun x => vecDot (F x) (ψ x)) V volume) :
    negSobolevNorm V s F = ⊤ :=
  eq_top_iff.2 <|
    le_trans (le_of_eq (dualPairing_eq_top_of_not_integrableOn V F ψ h).symm)
      (le_iSup (fun ψ' : {ψ' : Vec d → Vec d //
          IsLocalVecTest V ψ' ∧ hsNormSq V s ψ' ≤ 1} => dualPairing V F ψ'.1)
        ⟨ψ, hψ, hnorm⟩)

/-- The same for the `H_underlined^{-1}` dual norm. -/
theorem negOneNorm_eq_top_of_not_integrableOn (V : Set (Vec d))
    (F ψ : Vec d → Vec d) (hψ : IsLocalVecTest V ψ) (hnorm : h1NormSq V ψ ≤ 1)
    (h : ¬ IntegrableOn (fun x => vecDot (F x) (ψ x)) V volume) :
    negOneNorm V F = ⊤ :=
  eq_top_iff.2 <|
    le_trans (le_of_eq (dualPairing_eq_top_of_not_integrableOn V F ψ h).symm)
      (le_iSup (fun ψ' : {ψ' : Vec d → Vec d //
          IsLocalVecTest V ψ' ∧ h1NormSq V ψ' ≤ 1} => dualPairing V F ψ'.1)
        ⟨ψ, hψ, hnorm⟩)

/-! ## The index family is nonempty (no empty-supremum junk) -/

theorem vecNormSq_zero_vec : vecNormSq (0 : Vec d) = 0 := by
  simp [vecNormSq, vecDot]

/-- The zero test field is admissible. -/
theorem isLocalVecTest_zero (V : Set (Vec d)) :
    IsLocalVecTest V (fun _ => (0 : Vec d)) where
  contDiff := contDiff_const
  hasCompactSupport := by
    simpa using (hasCompactSupport_def (f := fun _ : Vec d => (0 : Vec d))).2 (by
      simp [Function.support])
  tsupport_subset := by
    simp [tsupport, Function.support]

theorem isLocalTest_zero (V : Set (Vec d)) :
    IsLocalTest V (fun _ => (0 : ℝ)) where
  contDiff := contDiff_const
  hasCompactSupport := by
    simpa using (hasCompactSupport_def (f := fun _ : Vec d => (0 : ℝ))).2 (by
      simp [Function.support])
  tsupport_subset := by
    simp [tsupport, Function.support]

theorem eVolumeAverage_zero (V : Set (Vec d)) :
    eVolumeAverage V (fun _ => (0 : ℝ≥0∞)) = 0 := by
  simp [eVolumeAverage]

theorem fracSeminormSq_zero (V : Set (Vec d)) (s : ℝ) :
    fracSeminormSq V s (fun _ => (0 : Vec d)) = 0 := by
  unfold fracSeminormSq
  simp [vecNormSq_zero_vec, eVolumeAverage]

theorem hsNormSq_zero (V : Set (Vec d)) (s : ℝ) :
    hsNormSq V s (fun _ => (0 : Vec d)) = 0 := by
  unfold hsNormSq
  rw [fracSeminormSq_zero]
  simp [vecNormSq_zero_vec, eVolumeAverage]

theorem smoothGrad_zero (x : Vec d) :
    smoothGrad (fun _ => (0 : ℝ)) x = (0 : Vec d) := by
  funext i
  simp [smoothGrad]

theorem h1NormSq_zero (V : Set (Vec d)) :
    h1NormSq V (fun _ => (0 : Vec d)) = 0 := by
  unfold h1NormSq
  have h1 : (fun x : Vec d =>
      ENNReal.ofReal (vecNormSq ((fun _ => (0 : Vec d)) x))) = fun _ => (0 : ℝ≥0∞) := by
    funext x
    simp [vecNormSq_zero_vec]
  have h2 : (fun x : Vec d => ENNReal.ofReal
        (∑ j : Fin d,
          vecNormSq (smoothGrad (fun y : Vec d => (fun _ => (0 : Vec d)) y j) x)))
      = fun _ => (0 : ℝ≥0∞) := by
    funext x
    have hj : ∀ j : Fin d,
        vecNormSq (smoothGrad (fun y : Vec d => (fun _ => (0 : Vec d)) y j) x) = 0 := by
      intro j
      have hcast : (fun y : Vec d => (fun _ => (0 : Vec d)) y j)
          = fun _ : Vec d => (0 : ℝ) := rfl
      rw [hcast, smoothGrad_zero, vecNormSq_zero_vec]
    rw [Finset.sum_congr rfl fun j _ => hj j]
    simp
  rw [h1, h2, eVolumeAverage_zero, mul_zero, add_zero]

/-- The dual norm of the zero field is zero: the supremum is over a nonempty
family and the estimates are not junk-true through an empty index. -/
theorem negSobolevNorm_zero (V : Set (Vec d)) (s : ℝ) :
    negSobolevNorm V s (fun _ => (0 : Vec d)) = 0 := by
  unfold negSobolevNorm
  have h : ∀ ψ : {ψ : Vec d → Vec d // IsLocalVecTest V ψ ∧ hsNormSq V s ψ ≤ 1},
      dualPairing V (fun _ => (0 : Vec d)) ψ.1 = 0 := by
    intro ψ
    have hint : IntegrableOn
        (fun x => vecDot ((fun _ => (0 : Vec d)) x) (ψ.1 x)) V volume := by
      simp [vecDot]
    rw [dualPairing_eq_ofReal V _ _ hint]
    simp [volumeAverage, vecDot]
  simp [h]

theorem negOneNorm_zero (V : Set (Vec d)) :
    negOneNorm V (fun _ => (0 : Vec d)) = 0 := by
  unfold negOneNorm
  have h : ∀ ψ : {ψ : Vec d → Vec d // IsLocalVecTest V ψ ∧ h1NormSq V ψ ≤ 1},
      dualPairing V (fun _ => (0 : Vec d)) ψ.1 = 0 := by
    intro ψ
    have hint : IntegrableOn
        (fun x => vecDot ((fun _ => (0 : Vec d)) x) (ψ.1 x)) V volume := by
      simp [vecDot]
    rw [dualPairing_eq_ofReal V _ _ hint]
    simp [volumeAverage, vecDot]
  simp [h]

/-! ## The dual norms dominate every admissible pairing

This is the characterization a consumer needs: bounding the dual norm bounds
the absolute value of the normalized pairing against every admissible test.
The absolute value costs nothing because the admissible family is closed under
negation, so the supremum of the signed pairings is already the supremum of
their absolute values. -/

private theorem vecDot_neg_right_aux (x y : Vec d) :
    vecDot x (-y) = -vecDot x y := by
  simp [vecDot, Finset.sum_neg_distrib]

private theorem volumeAverage_neg_aux (V : Set (Vec d)) (f : Vec d → ℝ) :
    volumeAverage V (fun x => -f x) = -volumeAverage V f := by
  unfold volumeAverage
  rw [integral_neg, mul_neg]

private theorem vecNormSq_neg_aux (x : Vec d) : vecNormSq (-x) = vecNormSq x := by
  simp [vecNormSq, vecDot]

theorem isLocalVecTest_neg {V : Set (Vec d)} {ψ : Vec d → Vec d}
    (h : IsLocalVecTest V ψ) : IsLocalVecTest V (-ψ) where
  contDiff := h.contDiff.neg
  hasCompactSupport := HasCompactSupport.neg h.hasCompactSupport
  tsupport_subset := by
    rw [tsupport, Function.support_neg]
    exact h.tsupport_subset

theorem hsNormSq_neg (V : Set (Vec d)) (s : ℝ) (ψ : Vec d → Vec d) :
    hsNormSq V s (-ψ) = hsNormSq V s ψ := by
  unfold hsNormSq fracSeminormSq
  have h1 : ∀ x : Vec d, vecNormSq ((-ψ) x) = vecNormSq (ψ x) := by
    intro x
    exact vecNormSq_neg_aux (ψ x)
  have h2 : ∀ x y : Vec d, vecNormSq ((-ψ) x - (-ψ) y) = vecNormSq (ψ x - ψ y) := by
    intro x y
    have hz : ((-ψ) x - (-ψ) y) = -(ψ x - ψ y) := by
      funext i
      show -ψ x i - -ψ y i = -(ψ x i - ψ y i)
      ring
    rw [hz]
    exact vecNormSq_neg_aux (ψ x - ψ y)
  simp only [h1, h2]

/-- The `H^{-s}` dual norm dominates the absolute value of the normalized
pairing against every admissible test. -/
theorem ofReal_abs_pairing_le_negSobolevNorm (V : Set (Vec d)) (s : ℝ)
    (F ψ : Vec d → Vec d) (hψ : IsLocalVecTest V ψ) (hnorm : hsNormSq V s ψ ≤ 1) :
    ENNReal.ofReal |volumeAverage V fun x => vecDot (F x) (ψ x)| ≤
      negSobolevNorm V s F := by
  classical
  by_cases hint : IntegrableOn (fun x => vecDot (F x) (ψ x)) V volume
  · set p : ℝ := volumeAverage V (fun x => vecDot (F x) (ψ x)) with hp
    have hswap : (fun x => vecDot (F x) ((-ψ) x)) = fun x => -vecDot (F x) (ψ x) := by
      funext x
      exact vecDot_neg_right_aux (F x) (ψ x)
    have hle : ENNReal.ofReal p ≤ negSobolevNorm V s F := by
      refine le_trans (le_of_eq ?_)
        (le_iSup (fun ψ' : {ψ' : Vec d → Vec d //
            IsLocalVecTest V ψ' ∧ hsNormSq V s ψ' ≤ 1} => dualPairing V F ψ'.1)
          ⟨ψ, hψ, hnorm⟩)
      exact (dualPairing_eq_ofReal V F ψ hint).symm
    have hneg_int : IntegrableOn (fun x => vecDot (F x) ((-ψ) x)) V volume := by
      rw [hswap]
      exact hint.neg
    have hle' : ENNReal.ofReal (-p) ≤ negSobolevNorm V s F := by
      have hval : dualPairing V F (-ψ) = ENNReal.ofReal (-p) := by
        rw [dualPairing_eq_ofReal V F _ hneg_int]
        congr 1
        rw [hswap, volumeAverage_neg_aux, hp]
      refine le_trans (le_of_eq hval.symm)
        (le_iSup (fun ψ' : {ψ' : Vec d → Vec d //
            IsLocalVecTest V ψ' ∧ hsNormSq V s ψ' ≤ 1} => dualPairing V F ψ'.1)
          ⟨-ψ, isLocalVecTest_neg hψ, by rw [hsNormSq_neg]; exact hnorm⟩)
    rcases abs_cases p with ⟨habs, _⟩ | ⟨habs, _⟩
    · rw [habs]; exact hle
    · rw [habs]; exact hle'
  · rw [volumeAverage_eq_zero_of_not_integrableOn V hint]
    simp

/-! ## The energies agree with the printed values

Where the quantity the reference text writes is finite, the Lebesgue-integral
encoding returns exactly it.  No value the reference text writes is changed; the
encoding only replaces the totalized `0` by `∞` where the printed quantity is
infinite. -/

/-- On an absolutely convergent, nonnegative energy the value is the printed
one. -/
theorem sEnergyOn_eq_ofReal_integral (b : CoeffField d) (V : Set (Vec d))
    (F : Vec d → Vec d)
    (hnonneg : 0 ≤ᵐ[volume.restrict V]
      fun x => vecDot (F x) (matVecMul (symmPart (b x)) (F x)))
    (hint : IntegrableOn
      (fun x => vecDot (F x) (matVecMul (symmPart (b x)) (F x))) V volume) :
    sEnergyOn b V F =
      ENNReal.ofReal
        (∫ x in V, vecDot (F x) (matVecMul (symmPart (b x)) (F x)) ∂volume) := by
  unfold sEnergyOn
  exact (ofReal_integral_eq_lintegral_ofReal hint hnonneg).symm

/-- The same for the normalized `L²` average of a square. -/
theorem eVolumeAverage_ofReal_eq (V : Set (Vec d)) (f : Vec d → ℝ)
    (hnonneg : 0 ≤ᵐ[volume.restrict V] f) (hint : IntegrableOn f V volume) :
    (∫⁻ x in V, ENNReal.ofReal (f x) ∂volume)
      = ENNReal.ofReal (∫ x in V, f x ∂volume) :=
  (ofReal_integral_eq_lintegral_ofReal hint hnonneg).symm

end

end HighContrast
end HCPolySupport
