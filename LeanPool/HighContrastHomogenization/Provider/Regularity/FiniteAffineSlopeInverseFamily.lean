/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineSlopeTerminalInverse

/-!
# High-contrast homogenization: Provider.Regularity.FiniteAffineSlopeInverseFamily

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Joint proof-gated finite affine inverse slope family

This module constructs a single total matrix family whose values on the good
finite interval are the proof-gated inverses of the canonical best-fit slope
maps. The arbitrary extension outside the interval is never characterized or
used.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

/-- A sufficiently small GoodMax row admits one joint family of proof-gated
inverse best-fit slope matrices on all interval scales, with the source
terminal operator bound. -/
theorem exists_scalarIdentityFiniteAffineSlopeInverseFamilyConstants
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ C c : ℝ, 1 ≤ C ∧ c ∈ Set.Ioc (0 : ℝ) ((2 * C)⁻¹) ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n m : ℤ),
        n < m → delta ∈ Set.Ioc (0 : ℝ) c →
          ScalarIdentityGoodMaxOnInterval a s delta n m →
          ∃ Q : ℤ → Mat d,
            (∀ (k : ℤ) (hk : k ∈ Finset.Icc n m),
              IsUnit (Q k).det ∧
              finiteAffineBestFitSlopeMatrix a k m
                    (Finset.mem_Icc.mp hk).2 * Q k = 1 ∧
              Q k * finiteAffineBestFitSlopeMatrix a k m
                    (Finset.mem_Icc.mp hk).2 = 1) ∧
            Book.Ch02.matrixNorm (Q m - 1) ≤ C * delta ∧
            C * delta ≤ (1 / 2 : ℝ) := by
  obtain ⟨B, cb, hB, hcb, hbijective⟩ :=
    exists_scalarIdentityFiniteAffineSlopeBijectiveConstants d s hs hs_lt
  obtain ⟨T, ct, hT, hct, hterminal⟩ :=
    exists_scalarIdentityFiniteAffineSlopeTerminalInverseConstants d s hs hs_lt
  let C : ℝ := 1 + B + T
  let c : ℝ := min cb (min ct ((2 * C)⁻¹))
  have hC : 1 ≤ C := by dsimp [C]; linarith only [hB, hT]
  have hCpos : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hTC : T ≤ C := by dsimp [C]; linarith only [hB]
  have hcpos : 0 < c := by
    dsimp [c]
    exact lt_min hcb.1 (lt_min hct.1
      (inv_pos.mpr (mul_pos (by norm_num) hCpos)))
  have hcC : c ≤ (2 * C)⁻¹ := by
    dsimp [c]
    exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨C, c, hC, ⟨hcpos, hcC⟩, ?_⟩
  intro a delta n m hnm hdelta hgood
  have hdeltaB : delta ∈ Set.Ioc (0 : ℝ) cb :=
    ⟨hdelta.1, hdelta.2.trans (min_le_left _ _)⟩
  have hdeltaT : delta ∈ Set.Ioc (0 : ℝ) ct :=
    ⟨hdelta.1, hdelta.2.trans
      ((min_le_right _ _).trans (min_le_left _ _))⟩
  have hbijAt : ∀ (k : ℤ) (hk : k ∈ Finset.Icc n m),
      Function.Bijective
        (finiteAffineBestFitSlope a k m (Finset.mem_Icc.mp hk).2) :=
    fun k hk ↦ (hbijective a delta n m hnm hdeltaB hgood k hk).1
  let Q : ℤ → Mat d := fun k ↦
    if hk : k ∈ Finset.Icc n m then
      finiteAffineBestFitSlopeInverseMatrix a k m
        (Finset.mem_Icc.mp hk).2 (hbijAt k hk)
    else 1
  have hm : m ∈ Finset.Icc n m := Finset.mem_Icc.mpr ⟨hnm.le, le_rfl⟩
  obtain ⟨hbijTerminal, hterminalBound⟩ :=
    hterminal a delta n m hnm hdeltaT hgood
  have hsmall : C * delta ≤ (1 / 2 : ℝ) := by
    have hd : delta ≤ (2 * C)⁻¹ := hdelta.2.trans hcC
    calc
      C * delta ≤ C * (2 * C)⁻¹ :=
        mul_le_mul_of_nonneg_left hd hCpos.le
      _ = 1 / 2 := by field_simp
  refine ⟨Q, ?_, ?_, hsmall⟩
  · intro k hk
    have hkm : k ≤ m := (Finset.mem_Icc.mp hk).2
    simp only [Q, dite_eq_left hk]
    exact ⟨finiteAffineBestFitSlopeInverseMatrix_isUnit_det
        a k m hkm (hbijAt k hk),
      finiteAffineBestFitSlopeMatrix_mul_inverseMatrix
        a k m hkm (hbijAt k hk),
      finiteAffineBestFitSlopeInverseMatrix_mul_matrix
        a k m hkm (hbijAt k hk)⟩
  · have hQm : Q m =
        finiteAffineBestFitSlopeInverseMatrix a m m le_rfl hbijTerminal := by
      simp only [Q, dite_eq_left hm]
    rw [hQm]
    exact hterminalBound.trans
      (mul_le_mul_of_nonneg_right hTC hdelta.1.le)

end

end HighContrast
end HCPolySupport
