/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.SquareSummableFamily
public import Mathlib.Analysis.InnerProductSpace.Reproducing

/-!
# Actual Hilbert-space features of an arbitrary positive matrix

The input positivity is the ordinary finitely supported matrix quadratic
form. Mathlib's reproducing-kernel Hilbert-space construction supplies
actual vectors whose Gram matrix is the input matrix. Their squared norms
are exactly its real diagonal entries.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open Matrix
open scoped ComplexConjugate ComplexOrder

variable {ι : Type*}

/-- Scalar operator kernel given by `fun i j => K i j • (1 : ℂ →L[ℂ] ℂ)`. -/
def scalarOperatorKernel (K : Matrix ι ι ℂ) : Matrix ι ι (ℂ →L[ℂ] ℂ) :=
  fun i j => K i j • (1 : ℂ →L[ℂ] ℂ)

theorem scalarOperatorKernel_posSemidef (K : Matrix ι ι ℂ) (hK : K.PosSemidef) :
    (scalarOperatorKernel K).PosSemidef := by
  have hconj (i j : ι) : conj (K j i) = K i j := hK.isHermitian.apply i j
  rw [RKHS.posSemidef_iff_re_sum_kernel']
  refine ⟨?_, fun c => ?_⟩
  · apply Matrix.IsHermitian.ext
    intro i j
    simp only [scalarOperatorKernel, star_smul, star_one]
    rw [show star (K j i) = conj (K j i) from rfl, hconj]
  · have h := (Complex.nonneg_iff.mp (hK.2 c)).1
    rw [RCLike.re_to_complex]
    convert h using 2
    refine Finsupp.sum_congr fun i _ => Finsupp.sum_congr fun j _ => ?_
    simp only [scalarOperatorKernel, smul_apply, one_apply_eq_self,
      smul_eq_mul, RCLike.inner_apply', map_mul, hconj]
    change K i j * conj (c i) * c j = conj (c i) * K i j * c j
    ring

instance scalarOperatorKernel_fact (K : Matrix ι ι ℂ) [Fact K.PosSemidef] :
    Fact (scalarOperatorKernel K).PosSemidef :=
  ⟨scalarOperatorKernel_posSemidef K Fact.out⟩

/-- Positive matrix space with underlying type `RKHS.OfKernel (scalarOperatorKernel K)`. -/
abbrev PositiveMatrixSpace (K : Matrix ι ι ℂ) [Fact K.PosSemidef] :=
  RKHS.OfKernel (scalarOperatorKernel K)

/-- Positive matrix feature obtained from `RKHS.kerFun`. -/
def positiveMatrixFeature (K : Matrix ι ι ℂ) [Fact K.PosSemidef] (i : ι) :
    PositiveMatrixSpace K := RKHS.kerFun (PositiveMatrixSpace K) i 1

theorem inner_positiveMatrixFeature (K : Matrix ι ι ℂ) [Fact K.PosSemidef] (i j : ι) :
    inner ℂ (positiveMatrixFeature K i) (positiveMatrixFeature K j) = K i j := by
  have hconj : conj (K j i) = K i j := (Fact.out : K.PosSemidef).isHermitian.apply i j
  rw [positiveMatrixFeature, positiveMatrixFeature, ← RKHS.kernel_inner,
    RKHS.OfKernel.kernel_ofKernel]
  simp only [scalarOperatorKernel, smul_apply, one_apply_eq_self,
    smul_eq_mul, mul_one, RCLike.inner_apply', hconj]

theorem norm_positiveMatrixFeature_sq (K : Matrix ι ι ℂ) [Fact K.PosSemidef] (i : ι) :
    ‖positiveMatrixFeature K i‖ ^ 2 = (K i i).re := by
  have h := congrArg Complex.re (inner_positiveMatrixFeature K i i)
  change RCLike.re (inner ℂ (positiveMatrixFeature K i)
    (positiveMatrixFeature K i)) = (K i i).re at h
  rw [inner_self_eq_norm_sq] at h
  exact h

theorem summable_positiveMatrixFeature_norm_sq (K : Matrix ι ι ℂ) [Fact K.PosSemidef]
    (hdiag : Summable fun i => (K i i).re) :
    Summable fun i => ‖positiveMatrixFeature K i‖ ^ 2 := by
  simpa only [norm_positiveMatrixFeature_sq] using hdiag

end VacuumBellSeparation.Gaussian
