/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.Algebra.ProjectiveSection
public import LeanPool.CCDN.Height.ProjectiveBox
public import LeanPool.CCDN.Hilbert.FilteredHilbertPolynomial
import LeanPool.CCDN.Plane.ProjectivePlaneLinearCount
import LeanPool.CCDN.Projection.BoundedBirationalHypersurfaceProjection
import LeanPool.CCDN.Projection.BoundedDegreeNormalizationFiber
import LeanPool.CCDN.Projection.ProjectiveLinearCountTransfer

/-! The plane curve estimate gives a smaller degree exponent for curves
specified by their filtered Hilbert polynomial. The construction of
the finite birational projection and its integer matrix is internal. -/

@[expose] public section
namespace CCDN
noncomputable section
open MvPolynomial

/-- Dimension growth for projective curves in `ℙⁿ` over `ℚ`, specified by their Hilbert
polynomial: there is a constant `C > 0`, depending only on `n ≥ 1`, such that every homogeneous
prime ideal `I` of projective dimension `1` and degree `d ≥ 5` has at most
`C * d ^ (3 * (n + 1) + 4) * B` rational points of height at most `B` for all `B ≥ 1`. -/
theorem projective_hilbert_curve_dimension_growth (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 < C ∧
      ∀ I : Ideal (MvPolynomial (Fin (n + 1)) ℚ), I.IsPrime →
      IsHomogeneousIdeal I →
      ∀ d : ℕ, 5 ≤ d → HasProjectiveDimensionDegree I 1 d →
      ∀ B : ℝ, 1 ≤ B →
      (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
        C * (d : ℝ) ^ (3 * (n + 1) + 4) * B := by
  let T : ℝ := (n + 1) * birationalProjectionHeightConstant (n + 1)
  have hT : 0 < T := by
    dsimp only [T]
    exact mul_pos (by positivity)
      (by exact_mod_cast birationalProjectionHeightConstant_pos (n + 1))
  refine ⟨projectivePlaneAbsoluteConstant * T,
    mul_pos projectivePlaneAbsoluteConstant_pos hT, ?_⟩
  intro I hprime hI d hd hdimdeg B hB
  have : I.IsPrime := hprime
  obtain ⟨b, f, hb, hN, hP, hfhom, hfdeg⟩ :=
    exists_bounded_birational_hypersurface_projection_of_le 1 (n + 1)
      (by omega) I hI d hdimdeg
  have hf := hP.irreducible
  have hrel := hP.aeval_mem
  have hfiber (z : Fin 3 → ℚ) (s : Finset (Fin (n + 1) → ℚ))
      (hzero : ∀ x ∈ s, x ∈ idealZeroLocus I)
      (hproj : ∀ x ∈ s, ∀ i, eval x (integerLinearForm (b i)) = z i) :
      s.card ≤ d ^ (n + 1) := by
    exact (linear_normalization_fiber_card_le I
      (fun i : Fin 2 => integerLinearForm (b i.succ))
      (fun i => linearForm_totalDegree_le _) hN.injective hN.integral d hdimdeg
      (fun i => z i.succ) s hzero (fun x hx i => hproj x hx i.succ)).trans
      (Nat.le_self_pow (Nat.succ_ne_zero n) d)
  let H : ℝ := birationalProjectionHeightConstant (n + 1) * (d : ℝ) ^ (2 * (n + 1))
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hH : 1 ≤ H := by
    have hconst : (1 : ℝ) ≤ birationalProjectionHeightConstant (n + 1) := by
      exact_mod_cast Nat.succ_le_of_lt (birationalProjectionHeightConstant_pos (n + 1))
    exact one_le_mul_of_one_le_of_one_le hconst (one_le_pow₀ hd1)
  have hbH (i j) : |(b i j : ℝ)| ≤ H := by
    have hh : |(b i j : ℝ)| ≤ integerBirationalProjectionHeight (n + 1) d := by
      exact_mod_cast hb i j
    apply hh.trans
    dsimp only [H]
    exact_mod_cast integerBirationalProjectionHeight_le (n + 1) d (by omega)
  have hbound := projective_integer_linear_count_transfer
    I b f (by rwa [hfdeg]) hrel (d ^ (n + 1)) hfiber H B (by linarith) hbH
  have hheight : 1 ≤ (n + 1 : ℝ) * H * B :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (by exact_mod_cast (show 1 ≤ n + 1 by omega)) hH) hB
  have hC := projectivePlaneAbsoluteConstant_pos
  have htarget := projective_plane_equation_bound f hfhom (by omega) hf hheight
  have hpow : ((n + 1 : ℝ) * H * B) ^ (2 / (d : ℝ)) ≤ (n + 1) * H * B := by
    calc
      _ ≤ ((n + 1 : ℝ) * H * B) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hheight
          ((div_le_one (by positivity)).mpr (by exact_mod_cast (show 2 ≤ d by omega)))
      _ = _ := Real.rpow_one _
  have hh : (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
      (d : ℝ) ^ (n + 1) *
        (projectivePlaneAbsoluteConstant * (d : ℝ) ^ 4 * ((n + 1) * H * B)) := by
    apply (show (projectiveCount (projectiveIdealZeroLocus I) B : ℝ) ≤
      (d : ℝ) ^ (n + 1) * projectiveCount (projectiveZeroLocus f) ((n + 1) * H * B) by
      exact_mod_cast hbound).trans
    exact mul_le_mul_of_nonneg_left
      (htarget.trans (mul_le_mul_of_nonneg_left hpow (by positivity))) (by positivity)
  convert hh using 1
  dsimp only [H, T]
  rw [show 3 * (n + 1) + 4 = (n + 1) + 4 + 2 * (n + 1) by omega]
  simp only [pow_add]
  ring

end
end CCDN
