/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteCorrectorLocalSequence

/-!
# High-contrast homogenization: Provider.Regularity.CorrectorLocalSequenceAlgebra

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Local class algebra for finite correctors

Restriction and fixed-unit normalization act linearly on scalar and
Hilbert-vector `L²` classes.  Consequently the normalized local pairs of the
finite zero-trace correctors are linear in the boundary slope.  No equality of
raw `H1Function` representatives is asserted.
-/

namespace HCPolySupport
namespace HighContrast

noncomputable section

open MeasureTheory

private instance localSequenceCubeFiniteMeasure (d n : ℕ) :
    IsFiniteMeasure (volumeMeasureOn (localGradientCube d n)) := by
  simpa [localGradientCube, volumeMeasureOn] using
    (isOpenBoundedConvexDomain_openCubeSet
      (originCube d (n : ℤ))).isFiniteMeasure_restrict_volume

/-- Restricting an `H¹` function and restricting its scalar `L²` class give
the same local class. -/
theorem localValueRestrict_toScalarL2_restrictLocalH1 {d m n : ℕ}
    (hmn : m ≤ n) (u : H1Function (localGradientCube d n)) :
    localValueRestrict hmn u.toScalarL2 =
      (restrictLocalH1 hmn u).toScalarL2 := by
  apply Lp.ext
  let hmu : volumeMeasureOn (localGradientCube d m) ≤
      volumeMeasureOn (localGradientCube d n) :=
    Measure.restrict_mono_set volume (localGradientCube_mono hmn)
  exact
    (localValueRestrict_coeFn_ae hmn u.toScalarL2).trans
    ((u.coeFn_toScalarL2.filter_mono (ae_mono hmu)).trans
      (restrictLocalH1 hmn u).coeFn_toScalarL2.symm)

/-- Restricting an `H¹` function and restricting its Hilbert-vector gradient
class give the same local class. -/
theorem localGradientRestrict_gradToHilbertVectorL2_restrictLocalH1
    {d m n : ℕ} (hmn : m ≤ n)
    (u : H1Function (localGradientCube d n)) :
    localGradientRestrict hmn u.gradToHilbertVectorL2 =
      (restrictLocalH1 hmn u).gradToHilbertVectorL2 := by
  apply Lp.ext
  let hmu : volumeMeasureOn (localGradientCube d m) ≤
      volumeMeasureOn (localGradientCube d n) :=
    Measure.restrict_mono_set volume (localGradientCube_mono hmn)
  exact
    (localGradientRestrict_coeFn_ae hmn u.gradToHilbertVectorL2).trans
    ((u.coeFn_gradToHilbertVectorL2.filter_mono (ae_mono hmu)).trans
      (restrictLocalH1 hmn u).coeFn_gradToHilbertVectorL2.symm)

/-- Scalar restriction preserves the constant-one class. -/
theorem localValueRestrict_oneScalarL2_eq {d m n : ℕ} (hmn : m ≤ n) :
    localValueRestrict hmn (oneScalarL2 (U := localGradientCube d n)) =
      oneScalarL2 (U := localGradientCube d m) := by
  apply Lp.ext
  let hmu : volumeMeasureOn (localGradientCube d m) ≤
      volumeMeasureOn (localGradientCube d n) :=
    Measure.restrict_mono_set volume (localGradientCube_mono hmn)
  exact
    (localValueRestrict_coeFn_ae hmn
      (oneScalarL2 (U := localGradientCube d n))).trans
    (((coeFn_oneScalarL2 (U := localGradientCube d n)).filter_mono
      (ae_mono hmu)).trans
      (coeFn_oneScalarL2 (U := localGradientCube d m)).symm)

/-- Fixed-unit normalization is a linear formula on scalar local classes. -/
theorem normalizeOnUnitCube_toScalarL2_eq {d n : ℕ}
    (u : H1Function (localGradientCube d n)) :
    (normalizeOnUnitCube u).toScalarL2 =
      u.toScalarL2 -
        (integralAverageCLM (U := localGradientCube d 0)
          (localValueRestrict (Nat.zero_le n) u.toScalarL2)) •
            oneScalarL2 (U := localGradientCube d n) := by
  rw [normalizeOnUnitCube]
  change
    (u + H1Function.const
      (U := localGradientCube d n)
      (-integralAverage (localGradientCube d 0)
        (restrictLocalH1 (Nat.zero_le n) u))).toScalarL2 = _
  rw [H1Function.toScalarL2_add, H1Function.toScalarL2_const,
    H1Function.integralAverage_eq_integralAverageCLM_toScalarL2,
    ← localValueRestrict_toScalarL2_restrictLocalH1]
  module

/-- Fixed-unit normalization leaves the Hilbert-vector gradient class
unchanged. -/
theorem normalizeOnUnitCube_gradToHilbertVectorL2_eq {d n : ℕ}
    (u : H1Function (localGradientCube d n)) :
    (normalizeOnUnitCube u).gradToHilbertVectorL2 =
      u.gradToHilbertVectorL2 := by
  apply Lp.ext
  filter_upwards
      [(normalizeOnUnitCube u).coeFn_gradToHilbertVectorL2,
        u.coeFn_gradToHilbertVectorL2]
    with x hx hu
  rw [hx, hu, normalizeOnUnitCube_grad]

/-- The value component of a normalized local pair is the corresponding
restricted class with its fixed-unit average removed. -/
theorem normalizedLocalPair_value_eq {d : ℕ}
    (u : ∀ q, H1Function (localGradientCube d q)) (n k : ℕ) :
    (normalizedLocalPair u n k).1 =
      localValueRestrict (Nat.le_add_right n k) (u (n + k)).toScalarL2 -
        (integralAverageCLM (U := localGradientCube d 0)
          (localValueRestrict (Nat.zero_le (n + k))
            (u (n + k)).toScalarL2)) •
          oneScalarL2 (U := localGradientCube d n) := by
  rw [normalizedLocalPair, normalizedLocalH1,
    ← localValueRestrict_toScalarL2_restrictLocalH1,
    normalizeOnUnitCube_toScalarL2_eq, map_sub, map_smul,
    localValueRestrict_oneScalarL2_eq]

/-- The gradient component of a normalized local pair is the restricted
Hilbert-vector gradient class. -/
theorem normalizedLocalPair_gradient_eq {d : ℕ}
    (u : ∀ q, H1Function (localGradientCube d q)) (n k : ℕ) :
    (normalizedLocalPair u n k).2 =
      localGradientRestrict (Nat.le_add_right n k)
        (u (n + k)).gradToHilbertVectorL2 := by
  rw [normalizedLocalPair, normalizedLocalH1,
    ← localGradientRestrict_gradToHilbertVectorL2_restrictLocalH1,
    normalizeOnUnitCube_gradToHilbertVectorL2_eq]

/-- Scalar local classes of finite correctors are additive in the slope. -/
theorem finiteAffineCorrectionLocalSequence_toScalarL2_add {d : ℕ}
    [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d) (e e' : Vec d)
    (q : ℕ) :
    (finiteAffineCorrectionLocalSequence a (e + e') q).toScalarL2 =
      (finiteAffineCorrectionLocalSequence a e q).toScalarL2 +
        (finiteAffineCorrectionLocalSequence a e' q).toScalarL2 := by
  rw [← H1Function.toScalarL2_add]
  apply (HCPolySupport.toScalarL2_eq_toScalarL2_iff
    (finiteAffineCorrectionLocalSequence a (e + e') q).memL2
    (finiteAffineCorrectionLocalSequence a e q +
      finiteAffineCorrectionLocalSequence a e' q).memL2).2
  simpa only [finiteAffineCorrectionLocalSequence, localGradientCube,
    Book.Ch02.cubeDomain_coe, H1Function.add_toFun] using!
      finiteAffineCorrection_toFun_add_ae a (q : ℤ) e e'

/-- Scalar local classes of finite correctors are homogeneous in the slope. -/
theorem finiteAffineCorrectionLocalSequence_toScalarL2_smul {d : ℕ}
    [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d) (c : ℝ) (e : Vec d)
    (q : ℕ) :
    (finiteAffineCorrectionLocalSequence a (c • e) q).toScalarL2 =
      c • (finiteAffineCorrectionLocalSequence a e q).toScalarL2 := by
  rw [← H1Function.toScalarL2_smul]
  apply (HCPolySupport.toScalarL2_eq_toScalarL2_iff
    (finiteAffineCorrectionLocalSequence a (c • e) q).memL2
    (c • finiteAffineCorrectionLocalSequence a e q).memL2).2
  simpa only [finiteAffineCorrectionLocalSequence, localGradientCube,
    Book.Ch02.cubeDomain_coe, H1Function.smul_toFun] using!
      finiteAffineCorrection_toFun_smul_ae a (q : ℤ) c e

/-- Hilbert-vector gradient classes of finite correctors are additive in the
slope. -/
theorem finiteAffineCorrectionLocalSequence_gradient_add {d : ℕ}
    [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d) (e e' : Vec d)
    (q : ℕ) :
    (finiteAffineCorrectionLocalSequence a (e + e') q).gradToHilbertVectorL2 =
      (finiteAffineCorrectionLocalSequence a e q).gradToHilbertVectorL2 +
        (finiteAffineCorrectionLocalSequence a e' q).gradToHilbertVectorL2 := by
  rw [← H1Function.gradToHilbertVectorL2_add]
  apply Lp.ext
  filter_upwards
      [(finiteAffineCorrectionLocalSequence a (e + e') q).coeFn_gradToHilbertVectorL2,
        (finiteAffineCorrectionLocalSequence a e q +
          finiteAffineCorrectionLocalSequence a e' q).coeFn_gradToHilbertVectorL2,
        finiteAffineCorrection_grad_add_ae a (q : ℤ) e e']
    with x hleft hright hgrad
  rw [hleft, hright]
  simp only [hilbertifyVecField, finiteAffineCorrectionLocalSequence,
    localGradientCube, Book.Ch02.cubeDomain_coe, id_eq, hgrad]
  rfl

/-- Hilbert-vector gradient classes of finite correctors are homogeneous in
the slope. -/
theorem finiteAffineCorrectionLocalSequence_gradient_smul {d : ℕ}
    [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d) (c : ℝ) (e : Vec d)
    (q : ℕ) :
    (finiteAffineCorrectionLocalSequence a (c • e) q).gradToHilbertVectorL2 =
      c • (finiteAffineCorrectionLocalSequence a e q).gradToHilbertVectorL2 := by
  rw [← H1Function.gradToHilbertVectorL2_smul]
  apply Lp.ext
  filter_upwards
      [(finiteAffineCorrectionLocalSequence a (c • e) q).coeFn_gradToHilbertVectorL2,
        (c • finiteAffineCorrectionLocalSequence a e q).coeFn_gradToHilbertVectorL2,
        finiteAffineCorrection_grad_smul_ae a (q : ℤ) c e]
    with x hleft hright hgrad
  rw [hleft, hright]
  simp only [hilbertifyVecField, finiteAffineCorrectionLocalSequence,
    localGradientCube, Book.Ch02.cubeDomain_coe, id_eq, hgrad]
  rfl

/-- Normalized local value-gradient pairs of finite correctors are additive
in the slope. -/
theorem normalizedLocalPair_finiteAffineCorrection_add {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (e e' : Vec d) (n k : ℕ) :
    normalizedLocalPair
        (finiteAffineCorrectionLocalSequence a (e + e')) n k =
      normalizedLocalPair (finiteAffineCorrectionLocalSequence a e) n k +
        normalizedLocalPair (finiteAffineCorrectionLocalSequence a e') n k := by
  apply Prod.ext
  · simp only [Prod.fst_add, normalizedLocalPair_value_eq,
      finiteAffineCorrectionLocalSequence_toScalarL2_add, map_add]
    rw [add_smul]
    abel
  · simp only [Prod.snd_add, normalizedLocalPair_gradient_eq,
      finiteAffineCorrectionLocalSequence_gradient_add, map_add]

/-- Normalized local value-gradient pairs of finite correctors are homogeneous
in the slope. -/
theorem normalizedLocalPair_finiteAffineCorrection_smul {d : ℕ} [NeZero d]
    (a : Book.Ch02.TriadicCoeffFamily d) (c : ℝ) (e : Vec d) (n k : ℕ) :
    normalizedLocalPair
        (finiteAffineCorrectionLocalSequence a (c • e)) n k =
      c • normalizedLocalPair (finiteAffineCorrectionLocalSequence a e) n k := by
  apply Prod.ext
  · simp only [normalizedLocalPair_value_eq,
      finiteAffineCorrectionLocalSequence_toScalarL2_smul, map_smul]
    change _ = c •
      (normalizedLocalPair (finiteAffineCorrectionLocalSequence a e) n k).1
    rw [normalizedLocalPair_value_eq]
    simp only [smul_eq_mul]
    module
  · simp only [normalizedLocalPair_gradient_eq,
      finiteAffineCorrectionLocalSequence_gradient_smul, map_smul]
    change _ = c •
      (normalizedLocalPair (finiteAffineCorrectionLocalSequence a e) n k).2
    rw [normalizedLocalPair_gradient_eq]

end


end HighContrast
end HCPolySupport
