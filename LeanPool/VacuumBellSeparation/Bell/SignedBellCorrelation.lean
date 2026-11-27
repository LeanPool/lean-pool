/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.SignedBellCorrelationDefs
public import LeanPool.VacuumBellSeparation.Bell.GenericBellCorrelationContinuity

/-! Exact signed/absolute Bell bridge on the original joint algebra.
Negating both Alice observables reverses the CHSH sign without changing the
admissible class. No maximizing quartet, normality or ambient extension is used. -/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite.HC00
open scoped ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem stateFunctional_isSelfAdjoint (M : VonNeumannAlgebra H)
    (φ : StateSpace M) {T : M.toStarSubalgebra} (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (φ.1 T) := by
  let : IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) :=
    isClosed_vonNeumannAlgebra M
  obtain ⟨ψ, hψ1, hψ⟩ := φ.2
  rw [← hψ T]
  exact hT.map' ψ

theorem stateFunctional_norm_eq_abs_re (M : VonNeumannAlgebra H)
    (φ : StateSpace M) {T : M.toStarSubalgebra} (hT : IsSelfAdjoint T) :
    ‖φ.1 T‖ = |(φ.1 T).re| := by
  have hr : ((φ.1 T).re : ℂ) = φ.1 T :=
    Complex.conj_eq_iff_re.mp (stateFunctional_isSelfAdjoint M φ hT).star_eq
  calc
    ‖φ.1 T‖ = ‖((φ.1 T).re : ℂ)‖ := congrArg norm hr.symm
    _ = |(φ.1 T).re| := by rw [Complex.norm_real, Real.norm_eq_abs]

theorem jointSignedBellValues_nonempty (A B : VonNeumannAlgebra H)
    (f : (jointAlgebra A B).toStarSubalgebra → ℂ) :
    (jointSignedBellValues A B f).Nonempty := by
  refine ⟨(1 / 2 : ℝ) * (f 0).re, 0, 0, 0, 0, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨A.zero_mem, IsSelfAdjoint.zero _, by simp⟩
  · exact ⟨A.zero_mem, IsSelfAdjoint.zero _, by simp⟩
  · exact ⟨B.zero_mem, IsSelfAdjoint.zero _, by simp⟩
  · exact ⟨B.zero_mem, IsSelfAdjoint.zero _, by simp⟩
  · simp

theorem jointSignedBellValues_bddAbove (A B : VonNeumannAlgebra H)
    (φ : StrongDual ℂ (jointAlgebra A B).toStarSubalgebra) :
    BddAbove (jointSignedBellValues A B φ) := by
  obtain ⟨C, hC⟩ := jointBellValues_bddAbove_of_bound A B φ ‖φ‖
    (norm_nonneg _) (fun T => φ.le_opNorm T)
  refine ⟨C, ?_⟩
  rintro r ⟨X₀, X₁, Y₀, Y₁, hX₀, hX₁, hY₀, hY₁, rfl⟩
  exact (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (by norm_num)).trans
    (hC ⟨X₀, X₁, Y₀, Y₁, hX₀, hX₁, hY₀, hY₁, rfl⟩)

theorem jointSignedBellCorrelation_le (A B : VonNeumannAlgebra H)
    (φ : StrongDual ℂ (jointAlgebra A B).toStarSubalgebra) :
    jointSignedBellCorrelation A B φ ≤ jointBellCorrelation A B φ := by
  apply csSup_le (jointSignedBellValues_nonempty A B φ)
  rintro r ⟨X₀, X₁, Y₀, Y₁, hX₀, hX₁, hY₀, hY₁, rfl⟩
  exact (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (by norm_num)).trans
    (le_csSup (jointBellValues_bddAbove_of_bound A B φ ‖φ‖
      (norm_nonneg _) (fun T => φ.le_opNorm T))
      ⟨X₀, X₁, Y₀, Y₁, hX₀, hX₁, hY₀, hY₁, rfl⟩)

theorem jointBellValues_subset_signed (A B : VonNeumannAlgebra H)
    (hcomm : Commuting A B) (φ : StateSpace (jointAlgebra A B)) :
    jointBellValues A B φ.1 ⊆ jointSignedBellValues A B φ.1 := by
  rintro r ⟨X₀, X₁, Y₀, Y₁, hX₀, hX₁, hY₀, hY₁, rfl⟩
  let T : (jointAlgebra A B).toStarSubalgebra :=
    X₀ * (Y₀ + Y₁) + X₁ * (Y₀ - Y₁)
  have hT : IsSelfAdjoint T := by
    apply Subtype.ext
    exact (chshOp_isSelfAdjoint hcomm hX₀ hX₁ hY₀ hY₁).star_eq
  have hn := stateFunctional_norm_eq_abs_re (jointAlgebra A B) φ hT
  by_cases hp : 0 ≤ (φ.1 T).re
  · refine ⟨X₀, X₁, Y₀, Y₁, hX₀, hX₁, hY₀, hY₁, ?_⟩
    change (1 / 2 : ℝ) * ‖φ.1 T‖ = (1 / 2 : ℝ) * (φ.1 T).re
    rw [hn, abs_of_nonneg hp]
  · have hneg₀ : ((-X₀ : (jointAlgebra A B).toStarSubalgebra) : H →L[ℂ] H) ∈
        saContractions A :=
      ⟨A.neg_mem hX₀.1, hX₀.2.1.neg, by
        change ‖-(X₀ : H →L[ℂ] H)‖ ≤ 1
        simpa only [norm_neg] using hX₀.2.2⟩
    have hneg₁ : ((-X₁ : (jointAlgebra A B).toStarSubalgebra) : H →L[ℂ] H) ∈
        saContractions A :=
      ⟨A.neg_mem hX₁.1, hX₁.2.1.neg, by
        change ‖-(X₁ : H →L[ℂ] H)‖ ≤ 1
        simpa only [norm_neg] using hX₁.2.2⟩
    refine ⟨-X₀, -X₁, Y₀, Y₁, hneg₀, hneg₁, hY₀, hY₁, ?_⟩
    have he : (-X₀) * (Y₀ + Y₁) + (-X₁) * (Y₀ - Y₁) = -T := by
      simp only [T, neg_mul, neg_add]
    change (1 / 2 : ℝ) * ‖φ.1 T‖ = _
    rw [he, map_neg, Complex.neg_re, hn, abs_of_neg (lt_of_not_ge hp)]

/-- SW88 p.219 signed normalization equals the literal absolute convention,
for every original joint state on commuting algebras. -/
theorem jointSignedBellCorrelation_eq (A B : VonNeumannAlgebra H)
    (hcomm : Commuting A B) (φ : StateSpace (jointAlgebra A B)) :
    jointSignedBellCorrelation A B φ.1 = jointBellCorrelation A B φ.1 := by
  apply le_antisymm (jointSignedBellCorrelation_le A B φ.1)
  apply csSup_le (jointBellValues_nonempty A B φ.1)
  intro r hr
  exact le_csSup (jointSignedBellValues_bddAbove A B φ.1)
    (jointBellValues_subset_signed A B hcomm φ hr)

end VacuumBellSeparation.Bipartite.HC00
