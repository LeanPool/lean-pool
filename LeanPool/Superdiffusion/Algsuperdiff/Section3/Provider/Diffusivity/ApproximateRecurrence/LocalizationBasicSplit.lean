/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.Path.Densities
public import LeanPool.Superdiffusion.Support.Book.Ch02.Theorems.BlockMatrixField
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.DoubledMu
public import LeanPool.HighContrastHomogenization.Support.CoarseGraining.QuadraticStability.CauchySchwarz

/-!
# LocalizationBasicSplit

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the localization cell algebra of `e.lower.bound.basic.split`

Source display in ABK26:

* `e.lower.bound.basic.split` (label; display):
  ```
  P . bfA_m(cu_K) P
    <=  avsum_{z} fint_{z+cu_n} X_z . bfA_m X_z
     =  avsum_{z} ( P_z . bfA_m(z+cu_n) P_z
                    + 2 P_z . fint_{z+cu_n} bfA_m tilde S_z
                    + fint_{z+cu_n} tilde S_z . bfA_m tilde S_z ) ,
  ```
  where `X_z = S_z + tilde S_z`, `S_z` is the minimizer of
  `e.variational.mu.U.P` (label) on `z + cu_n` at the constant load `P_z` of
  `e.Pz.def`, and `tilde S_z` is the minimizer of the same energy over the
  affine class based at the mean-zero field `F_z` of `e.Fz.def`.

This module supplies the *cell* algebra of that display: everything that
happens inside one localization cube, with the localization cube entering only
as a free `Domain`.  The mesh average `avsum_{z in 3^n Z^d cap cu_K}` and the
gluing of the cell fields into one competitor on `cu_K` are **not** treated
here; see the disclosure below.

## What is proved

* `isDoubledTestField_sub_constantDoubledField` -- an admissible field minus
  its constant load is a test field.
* `doubledMuValue_add` -- the exact quadratic expansion `E(S + T) = E(S) + E(T)
  + fint S. bfA T` (the three summands of the middle line of the display).
* `volumeAverage_doubledBlockPairingIntegrand_of_isDoubledResponseField` -- the
  cross term collapses to `P . fint bfA T`, which is the Euler--Lagrange
  equation of `T` tested against `S - P`.
* `isDoubledResponseField_of_forall_le_add_isDoubledTestField` -- the first
  variation: a field minimizing the doubled energy against all test-field
  perturbations *is* a doubled response field.  This is what makes the previous
  item applicable to `tilde S_z`, whose defining variational problem is based
  at the field `F_z` rather than at a constant, so that CoarseGraining's
  `DoubledMuTheory.minimizer_first_variation` does not apply to it directly.
* `two_mul_doubledMuValue_add_eq` -- the cell form of the equality line of
  `e.lower.bound.basic.split`.
* `blockVecDot_coarseBlockMatrix_le_two_mul_doubledMuValue` -- the cell form of
  the *inequality* line, i.e. competitor insertion into `e.variational.mu.U.P`.

## Divergences from the printed statement

* `blockVecDot_coarseBlockMatrix_le_two_mul_doubledMuValue` below is stated
  with `<=`, and no declaration in this module asserts the reverse.
* **The factor two.**  The manuscript's `fint_U X . bfA X` is twice
  CoarseGraining's `doubledMuValue`, whose integrand is `1/2 X . bfA X`;
  correspondingly `mu(U,P) = 1/2 P . bfA(U) P`.  Every statement below carries
  the factor `2` explicitly rather than renormalizing either object.
* **The mesh average and the gluing are absent.**  `e.lower.bound.basic.split`
  additionally uses that `sum_z X_z 1_{z+cu_n}` is admissible on `cu_K` and
  that `fint_{cu_K}` is the mesh average of the `fint_{z+cu_n}`.  Neither is
  proved here; the cell statements below are the input those two steps consume.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section24.Sensitivity.Provider.Path

noncomputable section

variable {d : ℕ}

/-! ## The constant doubled field of a load -/

/-- The constant doubled field with value `P`.  In `e.lower.bound.basic.split`
this is the affine background `P_z` of `e.Pz.def` viewed as a field on the
localization cube. -/
def constantDoubledField (P : BlockVec d) : DoubledField d where
  potential := fun _ => P.1
  flux := fun _ => P.2

/-- An admissible field for `e.variational.mu.U.P` at load `P` differs from the
constant field `P` by a test field. -/
theorem isDoubledTestField_sub_constantDoubledField {U : Domain d} {P : BlockVec d}
    {X : DoubledField d} (hX : IsDoubledMuAdmissible U P X) :
    IsDoubledTestField U (X - constantDoubledField P) :=
  ⟨hX.1, hX.2⟩

/-! ## Integrability of the pairing density -/

/-- The block pairing density of two vector-`L²` doubled fields is integrable. -/
theorem integrableOn_doubledBlockPairingIntegrand {U : Domain d} (a : CoeffOn U)
    {S T : DoubledField d}
    (hSpot : MemVectorL2 (U : Set (Vec d)) S.potential)
    (hSflux : MemVectorL2 (U : Set (Vec d)) S.flux)
    (hTpot : MemVectorL2 (U : Set (Vec d)) T.potential)
    (hTflux : MemVectorL2 (U : Set (Vec d)) T.flux) :
    IntegrableOn (doubledBlockPairingIntegrand U a S T) (U : Set (Vec d)) := by
  have h1 := integrableOn_vecDot_of_memVectorL2 hSpot
    (memVectorL2_blockMatrixField_fst a hTpot hTflux)
  have h2 := integrableOn_vecDot_of_memVectorL2 hSflux
    (memVectorL2_blockMatrixField_snd a hTpot hTflux)
  exact h1.add h2

/-! ## The exact quadratic expansion of the doubled energy -/

/-- Pointwise expansion of the doubled energy density of a sum, a.e. on the
domain.  The cross term is the block pairing density, which is where the a.e.
symmetry of `bfA(x)` is used. -/
private theorem blockEnergyDensityAt_add_ae {U : Domain d} (a : CoeffOn U)
    (S T : DoubledField d) :
    (fun x => blockEnergyDensityAt a ((S + T).eval x) x)
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
        ((fun x => blockEnergyDensityAt a (S.eval x) x)
            + fun x => blockEnergyDensityAt a (T.eval x) x)
          + doubledBlockPairingIntegrand U a S T := by
  filter_upwards [(blockMatrixFieldAlgebraTheory U a).field_symmetric] with x hx
  have hexp := blockVecDot_blockMatVecMul_add_smul_of_isSymmetricBlockMat hx
    (S.eval x) (T.eval x) 1
  rw [one_smul] at hexp
  change blockEnergyDensityAt a (S.eval x + T.eval x) x = _
  change (1 / 2 : ℝ) * blockVecDot (S.eval x + T.eval x)
      (blockMatVecMul (blockMatrixField a x) (S.eval x + T.eval x)) = _
  change _ = ((1 / 2 : ℝ) * blockVecDot (S.eval x)
        (blockMatVecMul (blockMatrixField a x) (S.eval x))
      + (1 / 2 : ℝ) * blockVecDot (T.eval x)
        (blockMatVecMul (blockMatrixField a x) (T.eval x)))
    + blockVecDot (S.eval x) (blockMatVecMul (blockMatrixField a x) (T.eval x))
  rw [hexp]
  ring

/-- **The exact quadratic expansion of the doubled energy**: `fint (S+T).bfA(S+T) =
fint S.bfA S + fint T.bfA T + 2 fint S.bfA T`, written with CoarseGraining's
half-normalized energy value. -/
theorem doubledMuValue_add {U : Domain d} (a : CoeffOn U) {S T : DoubledField d}
    (hSpot : MemVectorL2 (U : Set (Vec d)) S.potential)
    (hSflux : MemVectorL2 (U : Set (Vec d)) S.flux)
    (hTpot : MemVectorL2 (U : Set (Vec d)) T.potential)
    (hTflux : MemVectorL2 (U : Set (Vec d)) T.flux) :
    doubledMuValue U a (S + T) =
      doubledMuValue U a S + doubledMuValue U a T
        + volumeAverage (U : Set (Vec d)) (doubledBlockPairingIntegrand U a S T) := by
  have hES := integrableOn_blockEnergyDensity a hSpot hSflux
  have hET := integrableOn_blockEnergyDensity a hTpot hTflux
  have hcross := integrableOn_doubledBlockPairingIntegrand a hSpot hSflux hTpot hTflux
  change volumeAverage (U : Set (Vec d))
      (fun x => blockEnergyDensityAt a ((S + T).eval x) x) = _
  rw [volumeAverage_congr_ae (blockEnergyDensityAt_add_ae a S T),
    volumeAverage_add (hES.add hET) hcross, volumeAverage_add hES hET]
  rfl

/-! ## The Euler--Lagrange collapse of the cross term -/

/-- **The cross term of `e.lower.bound.basic.split`.**  When the second field is a
doubled response field on `U`, the block pairing against a `mu`-admissible
field collapses to the pairing against its constant load: `fint_U S. bfA T = P.
fint_U bfA T`.  This is the Euler--Lagrange equation of `T` tested against the
test field `S - P`. -/
theorem volumeAverage_doubledBlockPairingIntegrand_of_isDoubledResponseField
    {U : Domain d} {a : CoeffOn U} {P : BlockVec d} {S T : DoubledField d}
    (hS : IsDoubledMuAdmissible U P S) (hT : IsDoubledResponseField U a T) :
    volumeAverage (U : Set (Vec d)) (doubledBlockPairingIntegrand U a S T) =
      volumeAverage (U : Set (Vec d))
        (fun x => blockVecDot P (blockMatVecMul (blockMatrixField a x) (T.eval x))) := by
  have hTpot : MemVectorL2 (U : Set (Vec d)) T.potential := hT.1.1.1
  have hTflux : MemVectorL2 (U : Set (Vec d)) T.flux := hT.1.2.1
  have hconstpot : MemVectorL2 (U : Set (Vec d)) (constantDoubledField P).potential :=
    memVectorL2_const P.1
  have hconstflux : MemVectorL2 (U : Set (Vec d)) (constantDoubledField P).flux :=
    memVectorL2_const P.2
  have hdiffpot : MemVectorL2 (U : Set (Vec d)) (S - constantDoubledField P).potential :=
    hS.1.1
  have hdiffflux : MemVectorL2 (U : Set (Vec d)) (S - constantDoubledField P).flux :=
    hS.2.1
  have hconst := integrableOn_doubledBlockPairingIntegrand a hconstpot hconstflux hTpot hTflux
  have hdiff := integrableOn_doubledBlockPairingIntegrand a hdiffpot hdiffflux hTpot hTflux
  have hsplit : doubledBlockPairingIntegrand U a S T =
      doubledBlockPairingIntegrand U a (constantDoubledField P) T
        + doubledBlockPairingIntegrand U a (S - constantDoubledField P) T := by
    funext x
    change blockVecDot (S.eval x) (blockMatVecMul (blockMatrixField a x) (T.eval x)) =
      blockVecDot P (blockMatVecMul (blockMatrixField a x) (T.eval x))
        + blockVecDot ((S - constantDoubledField P).eval x)
            (blockMatVecMul (blockMatrixField a x) (T.eval x))
    have hdec : S.eval x = P + (S - constantDoubledField P).eval x := by
      refine Prod.ext ?_ ?_
      · change S.potential x = P.1 + (S.potential x - P.1)
        ring
      · change S.flux x = P.2 + (S.flux x - P.2)
        ring
    rw [hdec, blockVecDot_add_left]
  have hzero : volumeAverage (U : Set (Vec d))
      (doubledBlockPairingIntegrand U a (S - constantDoubledField P) T) = 0 :=
    volumeAverage_eq_zero_of_integral_eq_zero
      (hT.2 (S - constantDoubledField P) (isDoubledTestField_sub_constantDoubledField hS))
  rw [hsplit, volumeAverage_add hconst hdiff, hzero, add_zero]
  rfl

/-! ## Two elementary facts about the normalized average on a domain -/

/-- On a `Domain` the normalizing factor of `volumeAverage` is nonzero, because
the carrier is open, nonempty and bounded. -/
private theorem volume_toReal_inv_ne_zero (U : Domain d) :
    ((volume (U : Set (Vec d))).toReal)⁻¹ ≠ 0 := by
  have hpos : 0 < volume (U : Set (Vec d)) :=
    U.isOpen.measure_pos volume U.nonempty
  have hfin : volume (U : Set (Vec d)) < ⊤ := by
    have := measure_lt_top (volumeMeasureOn (U : Set (Vec d))) Set.univ
    rwa [volumeMeasureOn, Measure.restrict_apply_univ] at this
  refine inv_ne_zero (ENNReal.toReal_ne_zero.2 ⟨ne_of_gt hpos, ne_of_lt hfin⟩)

/-- A vanishing normalized average on a `Domain` forces a vanishing integral. -/
private theorem integral_eq_zero_of_volumeAverage_eq_zero {U : Domain d} {f : Vec d → ℝ}
    (h : volumeAverage (U : Set (Vec d)) f = 0) :
    ∫ x in (U : Set (Vec d)), f x ∂volume = 0 :=
  (mul_eq_zero.mp h).resolve_left (volume_toReal_inv_ne_zero U)

/-- The block pairing density is a.e. symmetric in its two fields, because
`bfA(x)` is a.e. a symmetric block matrix. -/
private theorem doubledBlockPairingIntegrand_comm_ae {U : Domain d} (a : CoeffOn U)
    (X Y : DoubledField d) :
    doubledBlockPairingIntegrand U a X Y
      =ᵐ[volumeMeasureOn (U : Set (Vec d))] doubledBlockPairingIntegrand U a Y X := by
  filter_upwards [(blockMatrixFieldAlgebraTheory U a).field_symmetric] with x hx
  exact blockVecDot_blockMatVecMul_comm_of_isSymmetricBlockMat hx (X.eval x) (Y.eval x)

/-! ## The first variation -/

/-- Scaling a test field by a real number gives a test field. -/
theorem isDoubledTestField_smul {U : Domain d} {Y : DoubledField d}
    (hY : IsDoubledTestField U Y) (t : ℝ) : IsDoubledTestField U (t • Y) := by
  obtain ⟨⟨hpotL2, u, hu⟩, hfluxL2, hflux⟩ := hY
  refine ⟨⟨hpotL2.const_smul t, t • u, ?_⟩, hfluxL2.const_smul t, ?_⟩
  · filter_upwards [hu] with x hx
    change t • Y.potential x = (t • u).toH1Function.grad x
    rw [hx]
    rfl
  · intro phi
    have h := hflux phi
    have hrw : ∀ x : Vec d, vecDot ((t • Y).flux x) (phi.grad x) =
        t * vecDot (Y.flux x) (phi.grad x) := by
      intro x
      change vecDot (t • Y.flux x) (phi.grad x) = t * vecDot (Y.flux x) (phi.grad x)
      simp [vecDot, Finset.mul_sum, mul_assoc]
    calc
      ∫ x in (U : Set (Vec d)), vecDot ((t • Y).flux x) (phi.grad x) ∂volume
          = ∫ x in (U : Set (Vec d)), t * vecDot (Y.flux x) (phi.grad x) ∂volume := by
            exact integral_congr_ae (Filter.Eventually.of_forall hrw)
      _ = t * ∫ x in (U : Set (Vec d)), vecDot (Y.flux x) (phi.grad x) ∂volume :=
            integral_const_mul _ _
      _ = 0 := by rw [h, mul_zero]

/-- **The first variation of the doubled energy.**  A vector-`L²` doubled field
whose energy does not decrease under any test-field perturbation satisfies the
Euler--Lagrange equation, i.e. it is a doubled response field on `U`.

This is what applies to the perturbation `tilde S_z`: its variational class is
based at the field `F_z` of `e.Fz.def`, not at a constant load, so
CoarseGraining's `DoubledMuTheory.minimizer_first_variation` -- which is stated
for `IsDoubledMuMinimizer`, i.e. for a constant base -- does not apply to it. -/
theorem isDoubledResponseField_of_forall_le_add_isDoubledTestField {U : Domain d}
    {a : CoeffOn U} {T : DoubledField d} (hamb : IsDoubledAmbientField U T)
    (hmin : ∀ Y : DoubledField d, IsDoubledTestField U Y →
      doubledMuValue U a T ≤ doubledMuValue U a (T + Y)) :
    IsDoubledResponseField U a T := by
  refine ⟨hamb, ?_⟩
  intro Y hY
  have hTpot : MemVectorL2 (U : Set (Vec d)) T.potential := hamb.1.1
  have hTflux : MemVectorL2 (U : Set (Vec d)) T.flux := hamb.2.1
  set L : ℝ := volumeAverage (U : Set (Vec d)) (doubledBlockPairingIntegrand U a T Y) with hL
  set Q : ℝ := doubledMuValue U a Y with hQ
  have hstep : ∀ t : ℝ, 0 ≤ t * L + t ^ 2 * Q := by
    intro t
    have hYt := isDoubledTestField_smul hY t
    have hYtpot : MemVectorL2 (U : Set (Vec d)) (t • Y).potential := hYt.1.1
    have hYtflux : MemVectorL2 (U : Set (Vec d)) (t • Y).flux := hYt.2.1
    have hsum := doubledMuValue_add a hTpot hTflux hYtpot hYtflux
    have hcross : volumeAverage (U : Set (Vec d))
        (doubledBlockPairingIntegrand U a T (t • Y)) = t * L := by
      have hpt : doubledBlockPairingIntegrand U a T (t • Y) =
          t • doubledBlockPairingIntegrand U a T Y := by
        funext x
        change blockVecDot (T.eval x) (blockMatVecMul (blockMatrixField a x) ((t • Y).eval x)) =
          t * blockVecDot (T.eval x) (blockMatVecMul (blockMatrixField a x) (Y.eval x))
        have hev : (t • Y).eval x = t • Y.eval x := rfl
        rw [hev, blockMatVecMul_smul, blockVecDot_smul_right]
      rw [hpt, volumeAverage_smul]
    have hQt : doubledMuValue U a (t • Y) = t ^ 2 * Q := by
      have hpt : (fun x => blockEnergyDensityAt a ((t • Y).eval x) x) =
          (t ^ 2) • fun x => blockEnergyDensityAt a (Y.eval x) x := by
        funext x
        change (1 / 2 : ℝ) * blockVecDot ((t • Y).eval x)
            (blockMatVecMul (blockMatrixField a x) ((t • Y).eval x)) =
          (t ^ 2) • ((1 / 2 : ℝ) * blockVecDot (Y.eval x)
            (blockMatVecMul (blockMatrixField a x) (Y.eval x)))
        have hev : (t • Y).eval x = t • Y.eval x := rfl
        rw [hev, blockMatVecMul_smul, blockVecDot_smul_left, blockVecDot_smul_right]
        simp only [smul_eq_mul]
        ring
      change volumeAverage (U : Set (Vec d))
        (fun x => blockEnergyDensityAt a ((t • Y).eval x) x) = _
      rw [hpt, volumeAverage_smul]
      rfl
    have hmin' := hmin (t • Y) hYt
    rw [hsum, hcross, hQt] at hmin'
    linarith
  have hquad : ∀ t : ℝ, 0 ≤ Q * (t * t) + L * t + 0 := by
    intro t
    have h := hstep t
    have hrw : Q * (t * t) + L * t + 0 = t * L + t ^ 2 * Q := by ring
    rw [hrw]
    exact h
  have hL2 : L ^ 2 ≤ 0 := by
    have hdisc := discrim_le_zero hquad
    simpa [discrim] using hdisc
  have hLzero : L = 0 := by nlinarith [sq_nonneg L]
  have hzero : volumeAverage (U : Set (Vec d)) (doubledBlockPairingIntegrand U a Y T) = 0 := by
    rw [volumeAverage_congr_ae (doubledBlockPairingIntegrand_comm_ae a Y T), ← hL, hLzero]
  exact integral_eq_zero_of_volumeAverage_eq_zero hzero

/-! ## The two lines of `e.lower.bound.basic.split` -/

/-- **The inequality line of `e.lower.bound.basic.split`.** Inserting any
admissible competitor into `e.variational.mu.U.P` bounds the coarse block form
from above: `P . bfA(U) P <= fint_U X . bfA X`. -/
theorem blockVecDot_coarseBlockMatrix_le_two_mul_doubledMuValue {U : Domain d}
    (a : CoeffOn U) (P : BlockVec d) {X : DoubledField d}
    (hX : IsDoubledMuAdmissible U P X) :
    blockVecDot P (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) P) ≤
      2 * doubledMuValue U a X := by
  obtain ⟨Y, hY⟩ := (doubledMuTheory U a).minimizer_exists P
  have hle : doubledMu U a P ≤ doubledMuValue U a X := by
    have h := hY.2 X hX
    rwa [hY.doubledMuValue_eq_doubledMu] at h
  rw [(doubledMuTheory U a).mu_quadratic P] at hle
  linarith

/-- **The equality line of `e.lower.bound.basic.split` at one localization cube.**
With `S` a minimizer of `e.variational.mu.U.P` at the constant load `P` and `T`
any doubled response field on `U`,

```
fint_U (S+T) . bfA (S+T)
  = P . bfA(U) P + 2 P . fint_U bfA T + fint_U T . bfA T .
```

At the manuscript's carriers `U = z + cu_n`, `P = P_z` (`e.Pz.def`), `S = S_z`,
`T = tilde S_z`, and `S + T = X_z`; the response-field hypothesis on `T` is
discharged from minimality by
`isDoubledResponseField_of_forall_le_add_isDoubledTestField`. -/
theorem two_mul_doubledMuValue_add_eq {U : Domain d} (a : CoeffOn U) (P : BlockVec d)
    {S T : DoubledField d} (hS : IsDoubledMuMinimizer U a P S)
    (hT : IsDoubledResponseField U a T) :
    2 * doubledMuValue U a (S + T) =
      blockVecDot P (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) P)
        + 2 * volumeAverage (U : Set (Vec d))
            (fun x => blockVecDot P (blockMatVecMul (blockMatrixField a x) (T.eval x)))
        + 2 * doubledMuValue U a T := by
  have hSpot := memVectorL2_potential_of_isDoubledMuAdmissible hS.1
  have hSflux := memVectorL2_flux_of_isDoubledMuAdmissible hS.1
  have hTpot : MemVectorL2 (U : Set (Vec d)) T.potential := hT.1.1.1
  have hTflux : MemVectorL2 (U : Set (Vec d)) T.flux := hT.1.2.1
  have hsum := doubledMuValue_add a hSpot hSflux hTpot hTflux
  have hcross := volumeAverage_doubledBlockPairingIntegrand_of_isDoubledResponseField hS.1 hT
  have hSval : doubledMuValue U a S =
      (1 / 2 : ℝ) * blockVecDot P (blockMatVecMul (Book.Ch02.coarseBlockMatrix U a) P) := by
    rw [hS.doubledMuValue_eq_doubledMu, (doubledMuTheory U a).mu_quadratic P]
  rw [hsum, hcross, hSval]
  ring

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
