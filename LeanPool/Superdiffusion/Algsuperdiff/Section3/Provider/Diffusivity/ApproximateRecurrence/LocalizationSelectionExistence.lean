/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.DoubledMu
public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.DoubledResponse.ResponseSpace
public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.MatrixExtraction
public import LeanPool.HighContrastHomogenization.Support.Internal.Ch02.Representatives

/-!
# LocalizationSelectionExistence

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the field-slope doubled minimizer of the localization split

Source displays in ABK26:

* `e.Pz.def`, `e.Fz.def`;
* `e.lower.bound.basic.split`.

Both `X_z` and `tilde S_z` are minimizers of the doubled energy over a class
whose slope datum is a **field**, not a constant:

```
X_z      = argmin { fint_{z+cu_n} (1/2) X . bfA_m X :
              X in bfAhom^{-1/2}(e'+grad w_D, e+grad w_N+shom^{-1} h e')
                     + (L^2_{pot,0} x Lsolo)(z+cu_n) }
tilde S_z = argmin { fint_{z+cu_n} (1/2) X . bfA_m X :
              X in bfF_z + (L^2_{pot,0} x Lsolo)(z+cu_n) }
```

The upstream repository provides the doubled variational theory only for the
constant-slope class (`Homogenization.Book.Ch02.IsDoubledMuAdmissible`,
`doubledMuTheory`), and upstream may not be edited.  This module supplies the
field-slope layer at the same carriers.

## What is proved

* `IsDoubledMuAdmissibleField` / `IsDoubledMuMinimizerField` -- the field-slope
  admissible class and its `argmin` predicate, definitionally the
  test-field-difference class `IsDoubledTestField U (X - F)` used by the
  localization gluing modules.
* `exists_isDoubledMuMinimizerField` -- **existence**: for every `Domain`, every
  Chapter-2 coefficient `a : CoeffOn U` and every vector-`L^2` slope field `F`,
  the `argmin` above exists; moreover any competitor whose energy does not
  exceed the minimizer's agrees with it a.e., which is the strict-convexity
  uniqueness.
* `sameAE_of_isDoubledMuMinimizerField` -- **uniqueness a.e.** of the field-slope
  minimizer, so that the manuscript's `tilde S_z` and `X_z` are well defined up
  to a null set.
* `isDoubledMuAdmissibleField_self`, `isDoubledMuAdmissibleField_add` and the
  `MemVectorL2` accessors used by the downstream modules.

## Method

The analytic engine is upstream's coercive affine Hilbert projection
`Homogenization.affineMinimizerMap` on `L^2(U; R^{2d})`, which is already
stated at an *arbitrary* ambient anchor; only its wrapper
`MuHilbertProblem.minimizerMap` specializes it to a constant `BlockVec d`.  The
closed correction space `L^2_{pot,0}(U) x Lsolo(U)` together with pointwise
representatives of its elements is upstream's
`PotentialSolenoidalL2RecoveryData`, produced on every open bounded convex
domain by `exists_recoveryData_of_mu_eq_muCandidate_of_isOpenBoundedConvexDomain`;
the identification of the Hilbert quadratic energy with `doubledMuValue` is
upstream's `quadraticEnergy_eq_blockEnergyAverage_of_blockState`.  No analytic
fact is reproved here.

## Divergences from the printed statement

* Here the carrier is Chapter 2's `DoubledField d` over `Domain d`; the
  identity `doubledMuValue = blockEnergyAverage . blockStateOfDoubled` holds by
  `rfl` (`doubledMuValue_eq_blockEnergyAverage` below) and the constant-slope
  class is recovered definitionally.
* **Pointwise vs a.e. coefficient.**  `CoeffOn U` carries only a.e.
  ellipticity, while the upstream recovery machinery consumes a pointwise
  `IsEllipticFieldOn` witness.  The proof therefore runs on upstream's
  pointwise representative `pointwiseCoeffOn U a` and transports the conclusion
  along `CoeffOn.AEEq`, exactly as upstream's own `doubledMuTheory` does.  No
  statement below mentions the representative.
* **`d = 0`.**  In dimension zero every doubled energy vanishes identically and
  the slope field itself is a minimizer; the theorem is stated uniformly in `d`
  and discharges that case separately, again as upstream does.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory
open HCPolySupport.Internal.Ch02.BookCh02

noncomputable section

variable {d : ℕ}

/-! ## The field-slope admissible class -/

/-- **The field-slope doubled admissible class**: `X ∈ F + (L^2_{pot,0} ×
Lsolo)(U)` for a slope datum `F` that is a *field*.  This is the field-slope
analogue of Chapter 2's `IsDoubledMuAdmissible`, which is the special case of a
constant slope. -/
def IsDoubledMuAdmissibleField (U : Domain d) (F X : DoubledField d) : Prop :=
  Book.Ch01.PotentialZeroTraceFieldOn (U : Set (Vec d))
      (fun x => X.potential x - F.potential x) ∧
    Book.Ch01.SolenoidalZeroNormalTraceFieldOn (U : Set (Vec d))
      (fun x => X.flux x - F.flux x)

/-- The field-slope class is the difference-is-a-test-field class used by the
localization gluing modules. -/
theorem isDoubledMuAdmissibleField_iff_isDoubledTestField_sub (U : Domain d)
    (F X : DoubledField d) :
    IsDoubledMuAdmissibleField U F X ↔ IsDoubledTestField U (X - F) :=
  Iff.rfl

/-- **The field-slope doubled minimizer predicate**, i.e. the `argmin` of the two
displays. -/
def IsDoubledMuMinimizerField (U : Domain d) (a : CoeffOn U) (F X : DoubledField d) :
    Prop :=
  IsDoubledMuAdmissibleField U F X ∧
    ∀ Y : DoubledField d, IsDoubledMuAdmissibleField U F Y →
      doubledMuValue U a X ≤ doubledMuValue U a Y

/-- The Chapter-2 doubled energy value is the block energy average of the
corresponding block state. -/
theorem doubledMuValue_eq_blockEnergyAverage (U : Domain d) (a : CoeffOn U)
    (X : DoubledField d) :
    doubledMuValue U a X =
      blockEnergyAverage (U : Set (Vec d)) a.toCoeffField (blockStateOfDoubled X) :=
  rfl

/-- The slope field lies in its own class. -/
theorem isDoubledMuAdmissibleField_self (U : Domain d) (F : DoubledField d) :
    IsDoubledMuAdmissibleField U F F := by
  have hp : (fun x => F.potential x - F.potential x) = (0 : Vec d → Vec d) := by
    funext x
    exact sub_self _
  have hf : (fun x => F.flux x - F.flux x) = (0 : Vec d → Vec d) := by
    funext x
    exact sub_self _
  constructor
  · rw [hp]
    exact Book.Ch01.potentialZeroTraceFieldOn_of_h10
      (0 : H10Function (U : Set (Vec d)))
  · rw [hf]
    refine ⟨MeasureTheory.MemLp.zero, fun phi => ?_⟩
    simp [vecDot]

/-- Adding a test field to an admissible field keeps it admissible. -/
theorem isDoubledMuAdmissibleField_add {U : Domain d} {F X Y : DoubledField d}
    (hX : IsDoubledMuAdmissibleField U F X) (hY : IsDoubledTestField U Y) :
    IsDoubledMuAdmissibleField U F (X + Y) := by
  obtain ⟨⟨hXpL2, u, hu⟩, hXfL2, hXf⟩ := hX
  obtain ⟨⟨hYpL2, v, hv⟩, hYfL2, hYf⟩ := hY
  have hpsum : (fun x => (X + Y).potential x - F.potential x)
      = (fun x => X.potential x - F.potential x) + Y.potential := by
    funext x
    change X.potential x + Y.potential x - F.potential x
      = (X.potential x - F.potential x) + Y.potential x
    abel
  have hfsum : (fun x => (X + Y).flux x - F.flux x)
      = (fun x => X.flux x - F.flux x) + Y.flux := by
    funext x
    change X.flux x + Y.flux x - F.flux x = (X.flux x - F.flux x) + Y.flux x
    abel
  constructor
  · rw [hpsum]
    refine ⟨hXpL2.add hYpL2, u + v, ?_⟩
    filter_upwards [hu, hv] with x hx hy
    change (X.potential x - F.potential x) + Y.potential x = _
    rw [hx, hy]
    rfl
  · rw [hfsum]
    refine ⟨hXfL2.add hYfL2, fun phi => ?_⟩
    have hint1 := integrableOn_vecDot_of_memVectorL2 hXfL2 phi.grad_memVectorL2
    have hint2 := integrableOn_vecDot_of_memVectorL2 hYfL2 phi.grad_memVectorL2
    have hpt : ∀ x : Vec d,
        vecDot (((fun y => X.flux y - F.flux y) + Y.flux) x) (phi.grad x)
          = vecDot (X.flux x - F.flux x) (phi.grad x)
            + vecDot (Y.flux x) (phi.grad x) := by
      intro x
      change vecDot ((X.flux x - F.flux x) + Y.flux x) (phi.grad x) = _
      simp [vecDot, Finset.sum_add_distrib, add_mul]
    calc
      ∫ x in (U : Set (Vec d)),
            vecDot (((fun y => X.flux y - F.flux y) + Y.flux) x) (phi.grad x) ∂volume
          = ∫ x in (U : Set (Vec d)),
              (vecDot (X.flux x - F.flux x) (phi.grad x)
                + vecDot (Y.flux x) (phi.grad x)) ∂volume :=
            integral_congr_ae (Filter.Eventually.of_forall hpt)
      _ = (∫ x in (U : Set (Vec d)), vecDot (X.flux x - F.flux x) (phi.grad x) ∂volume)
            + ∫ x in (U : Set (Vec d)), vecDot (Y.flux x) (phi.grad x) ∂volume :=
            integral_add hint1 hint2
      _ = 0 := by rw [hXf phi, hYf phi, add_zero]

/-- An admissible competitor over a vector-`L²` slope field is itself
vector-`L²`. -/
theorem memVectorL2_potential_of_isDoubledMuAdmissibleField {U : Domain d}
    {F X : DoubledField d} (hF : MemVectorL2 (U : Set (Vec d)) F.potential)
    (hX : IsDoubledMuAdmissibleField U F X) :
    MemVectorL2 (U : Set (Vec d)) X.potential := by
  have hfun : F.potential + (fun x => X.potential x - F.potential x) = X.potential := by
    funext x
    change F.potential x + (X.potential x - F.potential x) = X.potential x
    abel
  exact hfun ▸ hF.add hX.1.1

/-- An admissible competitor over a vector-`L²` slope field is itself
vector-`L²`. -/
theorem memVectorL2_flux_of_isDoubledMuAdmissibleField {U : Domain d}
    {F X : DoubledField d} (hF : MemVectorL2 (U : Set (Vec d)) F.flux)
    (hX : IsDoubledMuAdmissibleField U F X) :
    MemVectorL2 (U : Set (Vec d)) X.flux := by
  have hfun : F.flux + (fun x => X.flux x - F.flux x) = X.flux := by
    funext x
    change F.flux x + (X.flux x - F.flux x) = X.flux x
    abel
  exact hfun ▸ hF.add hX.2.1

/-! ## The `L²` bookkeeping of the affine class -/

/-- The `L²` class of a block field splits along an explicit pointwise
decomposition into slope plus correction.  Field-slope analogue of upstream's
`IsBlockMuAdmissible.toHilbertBlockL2OfBlockField_eq_blockVecToHilbertBlockL2Const_add`. -/
private theorem hilbert_eq_add_of_components {U : Set (Vec d)}
    {F W : Vec d → BlockVec d} (hF : MemBlockL2 U F) (hW : MemBlockL2 U W)
    {p q : Vec d → Vec d} (hp : MemVectorL2 U p) (hq : MemVectorL2 U q)
    (hpe : ∀ x, (W x).1 = (F x).1 + p x) (hqe : ∀ x, (W x).2 = (F x).2 + q x) :
    toHilbertBlockL2OfBlockField hW
      = toHilbertBlockL2OfBlockField hF + toHilbertBlockL2OfComponents hp hq := by
  apply MeasureTheory.Lp.ext
  filter_upwards
      [coeFn_toHilbertBlockL2OfBlockField (U := U) (F := W) hW,
       coeFn_toHilbertBlockL2OfBlockField (U := U) (F := F) hF,
       coeFn_toHilbertBlockL2OfComponents (U := U) hp hq,
       MeasureTheory.Lp.coeFn_add
         (toHilbertBlockL2OfBlockField (U := U) hF)
         (toHilbertBlockL2OfComponents (U := U) hp hq)]
    with x hWx hFx hCx hsum
  rw [hWx, hsum]
  change hilbertifyBlockField W x
      = (toHilbertBlockL2OfBlockField (U := U) hF) x
        + (toHilbertBlockL2OfComponents (U := U) hp hq) x
  rw [hFx, hCx]
  apply HilbertBlockVec.ext
  · ext i
    simp [hilbertifyBlockField, hilbertBlockField, blockField, hpe x]
  · ext i
    simp [hilbertifyBlockField, hilbertBlockField, blockField, hqe x]

/-- Two doubled fields with the same `L²` class agree a.e. on the domain. -/
private theorem sameAE_of_toHilbertBlockL2OfBlockField_eq {U : Domain d}
    {X Y : DoubledField d}
    (hX : MemBlockL2 (U : Set (Vec d)) (blockStateOfDoubled X).eval)
    (hY : MemBlockL2 (U : Set (Vec d)) (blockStateOfDoubled Y).eval)
    (h : toHilbertBlockL2OfBlockField hX = toHilbertBlockL2OfBlockField hY) :
    DoubledField.SameAE (U := U) X Y := by
  have hae : hilbertifyBlockField (blockStateOfDoubled X).eval
      =ᵐ[volumeMeasureOn (U : Set (Vec d))]
        hilbertifyBlockField (blockStateOfDoubled Y).eval := by
    have h1 := coeFn_toHilbertBlockL2OfBlockField (U := (U : Set (Vec d)))
      (F := (blockStateOfDoubled X).eval) hX
    have h2 := coeFn_toHilbertBlockL2OfBlockField (U := (U : Set (Vec d)))
      (F := (blockStateOfDoubled Y).eval) hY
    exact h1.symm.trans (h ▸ h2)
  constructor
  · filter_upwards [hae] with x hx
    have hb := congrArg HilbertBlockVec.toBlockVec hx
    simpa [hilbertifyBlockField, BlockState.eval, blockStateOfDoubled] using
      congrArg Prod.fst hb
  · filter_upwards [hae] with x hx
    have hb := congrArg HilbertBlockVec.toBlockVec hx
    simpa [hilbertifyBlockField, BlockState.eval, blockStateOfDoubled] using
      congrArg Prod.snd hb

/-! ## Existence and uniqueness of the field-slope minimizer -/

/-- The pointwise-elliptic core of `exists_isDoubledMuMinimizerField`. -/
private theorem exists_isDoubledMuMinimizerField_of_isEllipticFieldOn [NeZero d]
    (U : Domain d) (a : CoeffOn U)
    (hEll : IsEllipticFieldOn a.lam a.Lam (U : Set (Vec d)) a.toCoeffField)
    {F : DoubledField d}
    (hFpot : MemVectorL2 (U : Set (Vec d)) F.potential)
    (hFflux : MemVectorL2 (U : Set (Vec d)) F.flux) :
    ∃ X : DoubledField d, IsDoubledMuMinimizerField U a F X ∧
      ∀ W : DoubledField d, IsDoubledMuAdmissibleField U F W →
        doubledMuValue U a W ≤ doubledMuValue U a X →
          DoubledField.SameAE (U := U) W X := by
  classical
  have hvol : 0 < (volume (U : Set (Vec d))).toReal := domain_volume_pos U
  obtain ⟨R, -⟩ :=
    exists_recoveryData_of_mu_eq_muCandidate_of_isOpenBoundedConvexDomain
      (U := (U : Set (Vec d))) U.isDomain hEll hvol
  let system : MuOperatorSystemData (U : Set (Vec d)) a.toCoeffField :=
    R.toMuOperatorSystemDataOfIsEllipticFieldOn hEll hvol
  let M : MuOperatorRealization (U : Set (Vec d)) a.toCoeffField :=
    system.toMuOperatorRealization
  let Rc : MuCorrectionSpaceRecoveryData (U : Set (Vec d)) :=
    R.toMuCorrectionSpaceRecoveryData
  let K : ClosedSubmodule ℝ (HilbertBlockL2 (U : Set (Vec d))) := Rc.correctionSpace
  let B := energyBilinOfOperator M.operator
  have hB : IsCoercive B := M.operatorCoercive
  have hsymm : ∀ u v, B u v = B v u := energyBilinOfOperator_symm M.operator M.operatorSymm
  have hFL2 : MemBlockL2 (U : Set (Vec d)) (blockStateOfDoubled F).eval :=
    memBlockL2_blockField hFpot hFflux
  let x0 := toHilbertBlockL2OfBlockField hFL2
  have hmem : affineMinimizerMap K B hB x0 - x0 ∈ K :=
    sub_affineMinimizerMap_apply_mem K B hB x0
  let Ydat : CorrectionFieldData (U : Set (Vec d)) :=
    Rc.repr ⟨affineMinimizerMap K B hB x0 - x0, hmem⟩
  have hYrepr : Ydat.toHilbertBlockL2 = affineMinimizerMap K B hB x0 - x0 :=
    Rc.repr_eq ⟨affineMinimizerMap K B hB x0 - x0, hmem⟩
  set X : DoubledField d :=
    ⟨fun x => F.potential x + Ydat.potential x, fun x => F.flux x + Ydat.flux x⟩ with hXdef
  have hXadm : IsDoubledMuAdmissibleField U F X := by
    constructor
    · have hpz : Book.Ch01.PotentialZeroTraceFieldOn (U : Set (Vec d)) Ydat.potential := by
        obtain ⟨u, hu⟩ := Ydat.isPotentialZeroTrace
        rw [← hu]
        exact Book.Ch01.potentialZeroTraceFieldOn_of_h10 u
      have hfun : (fun x => X.potential x - F.potential x) = Ydat.potential := by
        funext x
        change F.potential x + Ydat.potential x - F.potential x = Ydat.potential x
        abel
      rw [hfun]
      exact hpz
    · have hfun : (fun x => X.flux x - F.flux x) = Ydat.flux := by
        funext x
        change F.flux x + Ydat.flux x - F.flux x = Ydat.flux x
        abel
      rw [hfun]
      exact ⟨Ydat.flux_memL2, Ydat.isSolenoidalZeroNormalTrace⟩
  have hXL2 : MemBlockL2 (U : Set (Vec d)) (blockStateOfDoubled X).eval :=
    memBlockL2_blockField (hFpot.add Ydat.potential_memL2) (hFflux.add Ydat.flux_memL2)
  have hsplitX : toHilbertBlockL2OfBlockField hXL2 = affineMinimizerMap K B hB x0 := by
    rw [hilbert_eq_add_of_components hFL2 hXL2 Ydat.potential_memL2 Ydat.flux_memL2
      (fun _ => rfl) (fun _ => rfl)]
    change x0 + Ydat.toHilbertBlockL2 = affineMinimizerMap K B hB x0
    rw [hYrepr]
    abel
  have hclassW : ∀ W : DoubledField d, IsDoubledMuAdmissibleField U F W →
      ∃ hW : MemBlockL2 (U : Set (Vec d)) (blockStateOfDoubled W).eval,
        toHilbertBlockL2OfBlockField hW - x0 ∈ K := by
    intro W hW
    have hWpot : MemVectorL2 (U : Set (Vec d)) W.potential :=
      memVectorL2_potential_of_isDoubledMuAdmissibleField hFpot hW
    have hWflux : MemVectorL2 (U : Set (Vec d)) W.flux :=
      memVectorL2_flux_of_isDoubledMuAdmissibleField hFflux hW
    have hWL2 : MemBlockL2 (U : Set (Vec d)) (blockStateOfDoubled W).eval :=
      memBlockL2_blockField hWpot hWflux
    refine ⟨hWL2, ?_⟩
    rw [hilbert_eq_add_of_components hFL2 hWL2
      hW.1.1 hW.2.1
      (fun x => by
        change W.potential x = F.potential x + (W.potential x - F.potential x)
        abel)
      (fun x => by
        change W.flux x = F.flux x + (W.flux x - F.flux x)
        abel)]
    have hcancel : x0 + toHilbertBlockL2OfComponents hW.1.1 hW.2.1 - x0
        = toHilbertBlockL2OfComponents hW.1.1 hW.2.1 := by abel
    rw [hcancel]
    exact Rc.mem_correctionSpace hW.1.1 hW.2.1
      (isPotentialZeroTraceOn_of_potentialZeroTraceFieldOn hW.1) hW.2.2
  have hqX : quadraticEnergy B (toHilbertBlockL2OfBlockField hXL2) = doubledMuValue U a X :=
    M.quadraticEnergy_eq_blockEnergyAverage_of_blockState hXL2
  refine ⟨X, ⟨hXadm, ?_⟩, ?_⟩
  · intro W hW
    obtain ⟨hWL2, hWclass⟩ := hclassW W hW
    have hqW : quadraticEnergy B (toHilbertBlockL2OfBlockField hWL2) = doubledMuValue U a W :=
      M.quadraticEnergy_eq_blockEnergyAverage_of_blockState hWL2
    have hmin := affineMinimizerMap_minimizes_quadraticEnergy K hB hsymm x0
      (toHilbertBlockL2OfBlockField hWL2) hWclass
    rw [← hqX, ← hqW, hsplitX]
    exact hmin
  · intro W hW hle
    obtain ⟨hWL2, hWclass⟩ := hclassW W hW
    have hqW : quadraticEnergy B (toHilbertBlockL2OfBlockField hWL2) = doubledMuValue U a W :=
      M.quadraticEnergy_eq_blockEnergyAverage_of_blockState hWL2
    have hleQ : quadraticEnergy B (toHilbertBlockL2OfBlockField hWL2)
        ≤ quadraticEnergy B (affineMinimizerMap K B hB x0) := by
      rw [hqW, ← hsplitX, hqX]
      exact hle
    have heq : toHilbertBlockL2OfBlockField hWL2 = affineMinimizerMap K B hB x0 :=
      eq_affineMinimizerMap_of_quadraticEnergy_le K hB hsymm x0
        (toHilbertBlockL2OfBlockField hWL2) hWclass hleQ
    refine sameAE_of_toHilbertBlockL2OfBlockField_eq hWL2 hXL2 ?_
    rw [heq, hsplitX]

/-- **Existence of the field-slope doubled minimizer**.

For every Chapter-2 domain `U`, coefficient `a : CoeffOn U` and vector-`L²`
slope field `F`, the variational problem of `e.variational.mu.U.P` posed over
the affine class `F + (L^2_{pot,0} × Lsolo)(U)` attains its infimum.  The second
clause is the strict-convexity uniqueness: any competitor whose energy does not
exceed the minimizer's agrees with it a.e. on `U`.

At the manuscript's carriers this produces `tilde S_z` (slope `bfF_z` of
`e.Fz.def`) and `X_z` (slope `bfAhom^{-1/2}(e'+grad w_D, e+grad w_N + shom^{-1}
h e')`), both on `U = z + cu_n`. -/
theorem exists_isDoubledMuMinimizerField (U : Domain d) (a : CoeffOn U)
    {F : DoubledField d}
    (hFpot : MemVectorL2 (U : Set (Vec d)) F.potential)
    (hFflux : MemVectorL2 (U : Set (Vec d)) F.flux) :
    ∃ X : DoubledField d, IsDoubledMuMinimizerField U a F X ∧
      ∀ W : DoubledField d, IsDoubledMuAdmissibleField U F W →
        doubledMuValue U a W ≤ doubledMuValue U a X →
          DoubledField.SameAE (U := U) W X := by
  by_cases hd : d = 0
  · subst hd
    have hzero : ∀ W : DoubledField 0, doubledMuValue U a W = 0 := by
      intro W
      have hfun : (fun x : Vec 0 => blockEnergyDensityAt a (W.eval x) x) = 0 := by
        funext x
        change (1 / 2 : ℝ) * blockVecDot (W.eval x)
          (blockMatVecMul (blockMatrixField a x) (W.eval x)) = 0
        simp [blockVecDot, vecDot]
      change volumeAverage (U : Set (Vec 0)) (fun x => blockEnergyDensityAt a (W.eval x) x) = 0
      rw [hfun]
      simp [volumeAverage]
    refine ⟨F, ⟨isDoubledMuAdmissibleField_self U F, ?_⟩, ?_⟩
    · intro Y _
      rw [hzero F, hzero Y]
    · intro W _ _
      exact ⟨Filter.Eventually.of_forall fun _ => Subsingleton.elim _ _,
        Filter.Eventually.of_forall fun _ => Subsingleton.elim _ _⟩
  · let : NeZero d := ⟨hd⟩
    set b : CoeffOn U := pointwiseCoeffOn U a with hbdef
    have hba : CoeffOn.AEEq b a := by
      simpa [hbdef] using pointwiseCoeffOn_ae_eq U a
    have hval : ∀ X : DoubledField d, doubledMuValue U b X = doubledMuValue U a X :=
      fun X => doubledMuValue_eq_ofAEEq hba X
    obtain ⟨X, ⟨hXadm, hXmin⟩, hXuniq⟩ :=
      exists_isDoubledMuMinimizerField_of_isEllipticFieldOn U b
        (by simpa [hbdef] using pointwiseCoeffOn_isEllipticFieldOn U a) hFpot hFflux
    refine ⟨X, ⟨hXadm, ?_⟩, ?_⟩
    · intro Y hY
      have := hXmin Y hY
      rwa [hval X, hval Y] at this
    · intro W hW hle
      refine hXuniq W hW ?_
      rwa [hval X, hval W]

/-- **Uniqueness a.e. of the field-slope minimizer.**  Any two minimizers of the
doubled energy over the same affine class agree almost everywhere on `U`, so
the manuscript's `argmin` notation denotes a well-defined object up to a null
set. -/
theorem sameAE_of_isDoubledMuMinimizerField {U : Domain d} {a : CoeffOn U}
    {F X Y : DoubledField d}
    (hFpot : MemVectorL2 (U : Set (Vec d)) F.potential)
    (hFflux : MemVectorL2 (U : Set (Vec d)) F.flux)
    (hX : IsDoubledMuMinimizerField U a F X)
    (hY : IsDoubledMuMinimizerField U a F Y) :
    DoubledField.SameAE (U := U) X Y := by
  obtain ⟨Z, hZ, hZuniq⟩ := exists_isDoubledMuMinimizerField U a hFpot hFflux
  have hXZ : DoubledField.SameAE (U := U) X Z := hZuniq X hX.1 (hX.2 Z hZ.1)
  have hYZ : DoubledField.SameAE (U := U) Y Z := hZuniq Y hY.1 (hY.2 Z hZ.1)
  exact ⟨hXZ.1.trans hYZ.1.symm, hXZ.2.trans hYZ.2.symm⟩

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
