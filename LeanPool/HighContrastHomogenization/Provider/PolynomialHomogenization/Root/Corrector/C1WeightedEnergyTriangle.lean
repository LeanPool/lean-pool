/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1CanonicalProjectionInverseControl
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1FixedProjectionIncrement

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.C1WeightedEnergyTriangle

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Triangle inequalities for normalized coefficient energy

On a centered cube, the public weighted gradient norm is the real square
root of the positive symmetric coefficient form.  This gives the triangle
and sign identities needed to combine two comparison errors.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem sqrt_normalizedEnergy_grad_eq_h1EnergyNormOnCube_triangle
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (q : ℤ) (u : H1Function (openCubeSet (originCube d q))) :
    Real.sqrt (normalizedLocalSymmetricEnergy
        (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
          (originCube d q) a) u.gradToHilbertVectorL2) =
      Book.Ch03.h1EnergyNormOnCube (originCube d q) a u := by
  rw [sqrt_normalizedEnergy_grad_eq_weightedGradNorm_toReal]
  rw [weightedGradNorm_congr_coeff_ae_on _
    (Book.Ch03.publicCoeffField_ae_eq_openCubeSet (originCube d q) a)]
  erw [weightedGradNorm_eq_ofReal_h1EnergyNormOnCube]
  rw [ENNReal.toReal_ofReal]
  unfold Book.Ch03.h1EnergyNormOnCube
  exact Real.sqrt_nonneg _

private theorem h1EnergyNormOnCube_sub_comm
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d) (q : ℤ)
    (u v : H1Function (openCubeSet (originCube d q))) :
    Book.Ch03.h1EnergyNormOnCube (originCube d q) a (u - v) =
      Book.Ch03.h1EnergyNormOnCube (originCube d q) a (v - u) := by
  let hEll := Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
    (originCube d q) a
  unfold Book.Ch03.h1EnergyNormOnCube Book.Ch03.localizedCoeffEnergyValue
  have hgrad : (u - v).gradToHilbertVectorL2 =
      -((v - u).gradToHilbertVectorL2) := by
    apply MeasureTheory.Lp.ext
    filter_upwards [(u - v).coeFn_gradToHilbertVectorL2,
      (v - u).coeFn_gradToHilbertVectorL2,
      MeasureTheory.Lp.coeFn_neg (v - u).gradToHilbertVectorL2]
      with x huv hvu hneg
    rw [huv, hneg, Pi.neg_apply, hvu]
    simp only [H1Function.sub_grad]
    change WithLp.toLp 2 _ = -WithLp.toLp 2 _
    rw [← WithLp.toLp_neg]
    congr 1
    funext i
    simp only [Pi.sub_apply, Pi.neg_apply]
    ring
  calc
    Book.Ch03.h1EnergyNormOnCube (originCube d q) a (u - v) =
        Real.sqrt (normalizedLocalSymmetricEnergy hEll
          (u - v).gradToHilbertVectorL2) :=
      (sqrt_normalizedEnergy_grad_eq_h1EnergyNormOnCube_triangle
        a q (u - v)).symm
    _ = Real.sqrt (normalizedLocalSymmetricEnergy hEll
          (-((v - u).gradToHilbertVectorL2))) := by rw [hgrad]
    _ = Real.sqrt (normalizedLocalSymmetricEnergy hEll
          (v - u).gradToHilbertVectorL2) := by
      rw [normalizedLocalSymmetricEnergy_neg_increment]
    _ = Book.Ch03.h1EnergyNormOnCube (originCube d q) a (v - u) :=
      sqrt_normalizedEnergy_grad_eq_h1EnergyNormOnCube_triangle a q (v - u)

/-- The normalized coefficient-energy norm of one difference is invariant
under reversing the two fields. -/
theorem weightedGradNorm_sub_comm_h1
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d) (q : ℤ)
    (u v : H1Function (openCubeSet (originCube d q))) :
    weightedGradNorm (a.coeffOn (originCube d q)).toCoeffField
        (openCubeSet (originCube d q))
        (fun x ↦ u.grad x - v.grad x) =
      weightedGradNorm (a.coeffOn (originCube d q)).toCoeffField
        (openCubeSet (originCube d q))
        (fun x ↦ v.grad x - u.grad x) := by
  have huv : (u - v).grad = fun x ↦ u.grad x - v.grad x :=
    H1Function.sub_grad u v
  have hvu : (v - u).grad = fun x ↦ v.grad x - u.grad x :=
    H1Function.sub_grad v u
  erw [← huv, ← hvu, weightedGradNorm_eq_ofReal_h1EnergyNormOnCube,
    weightedGradNorm_eq_ofReal_h1EnergyNormOnCube,
    h1EnergyNormOnCube_sub_comm]

/-- The normalized coefficient-energy norm obeys the triangle inequality
along three local Sobolev fields. -/
theorem weightedGradNorm_sub_le_add_sub_h1
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d) (q : ℤ)
    (u v w : H1Function (openCubeSet (originCube d q))) :
    weightedGradNorm (a.coeffOn (originCube d q)).toCoeffField
        (openCubeSet (originCube d q))
        (fun x ↦ u.grad x - w.grad x) ≤
      weightedGradNorm (a.coeffOn (originCube d q)).toCoeffField
          (openCubeSet (originCube d q))
          (fun x ↦ u.grad x - v.grad x) +
        weightedGradNorm (a.coeffOn (originCube d q)).toCoeffField
          (openCubeSet (originCube d q))
          (fun x ↦ v.grad x - w.grad x) := by
  let hEll := Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
    (originCube d q) a
  have hvol : 0 < volume (openCubeSet (originCube d q)) :=
    (ENNReal.toReal_pos_iff.mp
      (volume_openCubeSet_originCube_toReal_pos (d := d) q)).1
  have hvoltop : volume (openCubeSet (originCube d q)) ≠ ⊤ :=
    (volume_openCubeSet_lt_top (originCube d q)).ne
  let uv : H1Function (openCubeSet (originCube d q)) := u - v
  let vw : H1Function (openCubeSet (originCube d q)) := v - w
  let uw : H1Function (openCubeSet (originCube d q)) := u - w
  have hclass : uw.gradToHilbertVectorL2 =
      uv.gradToHilbertVectorL2 + vw.gradToHilbertVectorL2 := by
    apply MeasureTheory.Lp.ext
    filter_upwards [uw.coeFn_gradToHilbertVectorL2,
      uv.coeFn_gradToHilbertVectorL2, vw.coeFn_gradToHilbertVectorL2,
      MeasureTheory.Lp.coeFn_add uv.gradToHilbertVectorL2
        vw.gradToHilbertVectorL2] with x huw huv hvw hadd
    rw [huw, hadd, Pi.add_apply, huv, hvw]
    simp only [uw, uv, vw, H1Function.sub_grad]
    change WithLp.toLp 2 _ = WithLp.toLp 2 _ + WithLp.toLp 2 _
    rw [← WithLp.toLp_add]
    congr 1
    funext i
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  have htri := sqrt_normalizedLocalSymmetricEnergy_add_le hEll hvol hvoltop
    uv.gradToHilbertVectorL2 vw.gradToHilbertVectorL2
  rw [← hclass] at htri
  have hreal : Book.Ch03.h1EnergyNormOnCube (originCube d q) a uw ≤
      Book.Ch03.h1EnergyNormOnCube (originCube d q) a uv +
        Book.Ch03.h1EnergyNormOnCube (originCube d q) a vw := by
    simpa only [hEll,
      sqrt_normalizedEnergy_grad_eq_h1EnergyNormOnCube_triangle]
      using htri
  have huwGrad : uw.grad = fun x ↦ u.grad x - w.grad x := by
    exact H1Function.sub_grad u w
  have huvGrad : uv.grad = fun x ↦ u.grad x - v.grad x := by
    exact H1Function.sub_grad u v
  have hvwGrad : vw.grad = fun x ↦ v.grad x - w.grad x := by
    exact H1Function.sub_grad v w
  erw [← huwGrad, ← huvGrad, ← hvwGrad,
    weightedGradNorm_eq_ofReal_h1EnergyNormOnCube,
    weightedGradNorm_eq_ofReal_h1EnergyNormOnCube,
    weightedGradNorm_eq_ofReal_h1EnergyNormOnCube]
  rw [← ENNReal.ofReal_add
    (by unfold Book.Ch03.h1EnergyNormOnCube; positivity)
    (by unfold Book.Ch03.h1EnergyNormOnCube; positivity)]
  exact ENNReal.ofReal_le_ofReal hreal

end


end Root
end HighContrast
end HCPolySupport
