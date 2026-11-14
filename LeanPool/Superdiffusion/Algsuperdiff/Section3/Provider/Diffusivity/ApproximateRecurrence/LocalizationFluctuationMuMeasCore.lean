/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationSelectValue

/-!
# LocalizationFluctuationMuMeasCore

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The field-slope doubled minimum as a countable infimum

Internal Provider infrastructure for the Step-2 endpoint of
`l.approximate.recurrence.formula`.

## The problem

`LocalizationFluctuationSelectValue.doubledMuField U a F` is an `sInf` over the
*uncountable* affine class `F + (L^2_{pot,0} x Lsolo)(U)`.  The Step-2 endpoint
integrates it in the sample, so it has to be measurable in the sample; but the
sample enters through **both** the coefficient `a` and the slope field `F`, and
an `sInf` over an uncountable family carries no measurability by itself.

## What this module does

It replaces the uncountable infimum by a **countable** one, at a family of
competitors that depends on the domain only:

`exists_countable_doubledMuFieldCompetitors` produces one sequence
`D : ℕ → DoubledField d` of test fields on `U` such that for *every*
Chapter-2 coefficient `a : CoeffOn U` and *every* vector-`L^2` slope field `F`,

```
  doubledMuField U a F  =  ⨅ n, doubledMuValue U a (F + D n) .
```

The sequence is produced once and for all from the second countability of
`L^2(U; R^{2d})`; the identity then holds pointwise in `(a, F)`, so composing
with a sample gives an `iInf` of countably many sample functions.  Measurability
of the field-slope minimum therefore reduces to measurability of the
**fixed-competitor** energies, which is the shape of upstream's own
`FixedCompetitorEnergyMeasurability` layer.

No measurable selection of a minimizer occurs, and nothing below asserts that a
minimizer exists: the statement is an identity between an `sInf` and a countable
`sInf`, valid whether or not the infimum is attained.  The choice used to name
the sequence is choice on a countable dense subset of an `L^2` ball of test
fields --- an internal object that occurs in no source-facing statement.

## Method

For a fixed `U` the affine class is `F + T(U)` with `T(U)` the (sample- and
coefficient-independent) set `IsDoubledTestField U`.  Upstream's Hilbert layer
identifies the doubled energy of a field with the quadratic energy of its `L^2`
class under a coercive symmetric bilinear form
(`MuOperatorRealization.quadraticEnergy_eq_blockEnergyAverage_of_blockState`),
which is continuous on `L^2` and nonnegative.  `L^2(U; R^{2d})` is
second countable (`MeasureTheory.Lp.SecondCountableTopology`), hence so is the
set of `L^2` classes of test fields, which therefore has a countable dense
subset; pulling representatives back gives `D`.  Continuity of the energy along
the `L^2` class transfers the infimum.

## References

* ABK26, `l.approximate.recurrence.formula`, the two `argmin` displays, Step 2,
  `e.variational.mu.U.P`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory
open HCPolySupport.Internal.Ch02.BookCh02

noncomputable section

variable {d : ℕ}

/-! ## `L²` bookkeeping -/

/-- The zero doubled field is a test field. -/
theorem isDoubledTestField_zero (U : Domain d) : IsDoubledTestField U (0 : DoubledField d) := by
  constructor
  · exact Book.Ch01.potentialZeroTraceFieldOn_of_h10 (0 : H10Function (U : Set (Vec d)))
  · refine ⟨MeasureTheory.MemLp.zero, fun phi => ?_⟩
    have hz : (fun x : Vec d =>
        vecDot ((0 : DoubledField d).flux x) (phi.grad x)) = fun _ : Vec d => (0 : ℝ) := by
      funext x
      have hzero : (0 : DoubledField d).flux x = (0 : Vec d) := rfl
      simp [vecDot, hzero]
    simp [hz]

/-- The `L²` class of a pointwise sum of block fields is the sum of the classes. -/
theorem toHilbertBlockL2OfBlockField_add {U : Set (Vec d)}
    {F G H : Vec d → BlockVec d} (hF : MemBlockL2 U F) (hG : MemBlockL2 U G)
    (hH : MemBlockL2 U H) (hpt : ∀ x, H x = F x + G x) :
    toHilbertBlockL2OfBlockField hH =
      toHilbertBlockL2OfBlockField hF + toHilbertBlockL2OfBlockField hG := by
  apply MeasureTheory.Lp.ext
  filter_upwards
      [coeFn_toHilbertBlockL2OfBlockField (U := U) (F := H) hH,
       coeFn_toHilbertBlockL2OfBlockField (U := U) (F := F) hF,
       coeFn_toHilbertBlockL2OfBlockField (U := U) (F := G) hG,
       MeasureTheory.Lp.coeFn_add
         (toHilbertBlockL2OfBlockField (U := U) hF)
         (toHilbertBlockL2OfBlockField (U := U) hG)]
    with x hHx hFx hGx hsum
  rw [hHx, hsum]
  change hilbertifyBlockField H x
      = (toHilbertBlockL2OfBlockField (U := U) hF) x
        + (toHilbertBlockL2OfBlockField (U := U) hG) x
  rw [hFx, hGx]
  apply HilbertBlockVec.ext
  · ext i
    simp [hilbertifyBlockField, hpt x]
  · ext i
    simp [hilbertifyBlockField, hpt x]

/-- Adding a test field to the slope field returns to the affine class. -/
theorem add_sub_cancel_doubledField (F X : DoubledField d) : F + (X - F) = X := by
  refine HCPolySupport.Internal.Ch02.BookCh02.doubledField_ext ?_ ?_
  · funext x
    change F.potential x + (X.potential x - F.potential x) = X.potential x
    abel
  · funext x
    change F.flux x + (X.flux x - F.flux x) = X.flux x
    abel

/-! ## Nonnegativity and the two elementary bounds on the field-slope minimum

Reproved here from the a.e. ellipticity of the Chapter-2 coefficient; the same
two steps occur in the proved local provider
`Provider.Whitney.SubadditivityCountable.{blockEnergyDensityAt_nonneg_ae,
doubledMuValue_nonneg}`, which is a different cone and is deliberately not
imported. -/

/-- The doubled energy density is a.e. nonnegative on the domain, because the
coefficient is a.e. elliptic there. -/
theorem blockEnergyDensityAt_nonneg_ae' {U : Domain d} (a : CoeffOn U)
    (Z : Vec d → BlockVec d) :
    ∀ᵐ x ∂(volume.restrict (U : Set (Vec d))), 0 ≤ blockEnergyDensityAt a (Z x) x := by
  filter_upwards [a.aeElliptic] with x hx
  have hfield : blockMatrixField a x = blockMatrixOfCoeff (a.toCoeffField x) := rfl
  have hpos : ∀ W : BlockVec d,
      0 ≤ blockVecDot W (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) W) := by
    rintro ⟨u, v⟩
    rcases eq_or_ne ((u, v) : BlockVec d) 0 with hz | hz
    · rw [hz]
      simp [blockVecDot, vecDot]
    · exact (blockMatrixOfCoeff_quadratic_pos_of_isEllipticMatrix hx hz).le
  have hquad : 0 ≤ blockVecDot (Z x) (blockMatVecMul (blockMatrixField a x) (Z x)) := by
    rw [hfield]
    exact hpos (Z x)
  rw [blockEnergyDensityAt]
  linarith

/-- Every doubled energy value is nonnegative. -/
theorem doubledMuValue_nonneg' {U : Domain d} (a : CoeffOn U) (X : DoubledField d) :
    0 ≤ doubledMuValue U a X := by
  have hint : (0 : ℝ) ≤ ∫ x in (U : Set (Vec d)), blockEnergyDensityAt a (X.eval x) x ∂volume :=
    MeasureTheory.integral_nonneg_of_ae (blockEnergyDensityAt_nonneg_ae' a X.eval)
  rw [doubledMuValue, HCPolySupport.Book.Ch02.average]
  exact mul_nonneg (by positivity) hint

/-- The field-slope value set is bounded below by `0` and nonempty. -/
theorem bddBelow_doubledMuFieldValueSet (U : Domain d) (a : CoeffOn U) (F : DoubledField d) :
    BddBelow (doubledMuFieldValueSet U a F) := by
  refine ⟨0, ?_⟩
  rintro m ⟨X, -, rfl⟩
  exact doubledMuValue_nonneg' a X

/-- The field-slope value set is nonempty: the slope field is its own
competitor. -/
theorem nonempty_doubledMuFieldValueSet (U : Domain d) (a : CoeffOn U) (F : DoubledField d) :
    (doubledMuFieldValueSet U a F).Nonempty :=
  ⟨doubledMuValue U a F, ⟨F, isDoubledMuAdmissibleField_self U F, rfl⟩⟩

/-- **The lower bound on the field-slope minimum.**  Unconditional. -/
theorem doubledMuField_nonneg (U : Domain d) (a : CoeffOn U) (F : DoubledField d) :
    0 ≤ doubledMuField U a F := by
  refine le_csInf (nonempty_doubledMuFieldValueSet U a F) ?_
  rintro m ⟨X, -, rfl⟩
  exact doubledMuValue_nonneg' a X

/-- **The upper bound on the field-slope minimum by any competitor's energy.**
Unconditional; the competitor is supplied by the caller as a member of the
affine class. -/
theorem doubledMuField_le_doubledMuValue {U : Domain d} {a : CoeffOn U} {F X : DoubledField d}
    (hX : IsDoubledMuAdmissibleField U F X) :
    doubledMuField U a F ≤ doubledMuValue U a X :=
  csInf_le (bddBelow_doubledMuFieldValueSet U a F) ⟨X, hX, rfl⟩

/-- **The upper bound at the slope field itself.**  Unconditional. -/
theorem doubledMuField_le_self (U : Domain d) (a : CoeffOn U) (F : DoubledField d) :
    doubledMuField U a F ≤ doubledMuValue U a F :=
  doubledMuField_le_doubledMuValue (isDoubledMuAdmissibleField_self U F)

/-! ## The countable competitor family -/

/-- **The field-slope doubled minimum is a countable infimum.**

For every Chapter-2 domain `U` there is one sequence `D` of test fields on `U`,
depending on `U` alone, such that for *every* coefficient `a : CoeffOn U` and
*every* vector-`L^2` slope field `F` the canonical number
`doubledMuField U a F` is the greatest lower bound of the countable set of
energies `doubledMuValue U a (F + D n)`.

No minimizer is selected and none is assumed to exist: this is an identity
between the `sInf` of an uncountable value set and the `sInf` of a countable
subset of it. -/
theorem exists_countable_doubledMuFieldCompetitors (U : Domain d) :
    ∃ D : ℕ → DoubledField d,
      (∀ n, IsDoubledTestField U (D n)) ∧
        ∀ (a : CoeffOn U) (F : DoubledField d),
          MemVectorL2 (U : Set (Vec d)) F.potential →
          MemVectorL2 (U : Set (Vec d)) F.flux →
            IsGLB (Set.range fun n => doubledMuValue U a (F + D n))
              (doubledMuField U a F) := by
  classical
  by_cases hd : d = 0
  · subst hd
    have hzero : ∀ (a : CoeffOn U) (W : DoubledField 0), doubledMuValue U a W = 0 := by
      intro a W
      have hfun : (fun x : Vec 0 => blockEnergyDensityAt a (W.eval x) x) = 0 := by
        funext x
        change (1 / 2 : ℝ) * blockVecDot (W.eval x)
          (blockMatVecMul (blockMatrixField a x) (W.eval x)) = 0
        simp [blockVecDot, vecDot]
      change volumeAverage (U : Set (Vec 0)) (fun x => blockEnergyDensityAt a (W.eval x) x) = 0
      rw [hfun]
      simp [volumeAverage]
    refine ⟨fun _ => 0, fun _ => isDoubledTestField_zero U, ?_⟩
    intro a F _ _
    have hset : doubledMuFieldValueSet U a F = {0} := by
      ext m
      constructor
      · rintro ⟨X, -, rfl⟩
        exact hzero a X
      · rintro rfl
        exact ⟨F, isDoubledMuAdmissibleField_self U F, (hzero a F).symm⟩
    have hmu : doubledMuField U a F = 0 := by
      change sInf (doubledMuFieldValueSet U a F) = 0
      rw [hset]
      exact csInf_singleton 0
    have hrange : (Set.range fun n : ℕ => doubledMuValue U a (F + (0 : DoubledField 0)))
        = {(0 : ℝ)} := by
      ext m
      simp [hzero]
    rw [hmu, hrange]
    exact isGLB_singleton
  · let : NeZero d := ⟨hd⟩
    let : Fact ((1 : ENNReal) ≤ (2 : ENNReal)) := ⟨by norm_num⟩
    let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
    have : SecondCountableTopology (HilbertBlockL2 (U : Set (Vec d))) := inferInstance
    set E : {Y : DoubledField d // IsDoubledTestField U Y} → HilbertBlockL2 (U : Set (Vec d)) :=
      fun Y => toHilbertBlockL2OfBlockField (memBlockL2_blockField Y.2.1.1 Y.2.2.1) with hEdef
    set A : Set (HilbertBlockL2 (U : Set (Vec d))) := Set.range E with hAdef
    have : Nonempty A := ⟨⟨E ⟨0, isDoubledTestField_zero U⟩, Set.mem_range_self _⟩⟩
    have hchoose : ∀ n : ℕ, ∃ Y : {Y : DoubledField d // IsDoubledTestField U Y},
        E Y = ((TopologicalSpace.denseSeq A n : A) : HilbertBlockL2 (U : Set (Vec d))) :=
      fun n => (TopologicalSpace.denseSeq A n).2
    choose theta htheta using hchoose
    refine ⟨fun n => (theta n).1, fun n => (theta n).2, ?_⟩
    intro a F hFpot hFflux
    -- the pointwise coefficient representative and its Hilbert energy form
    set b : CoeffOn U := pointwiseCoeffOn U a with hbdef
    have hba : CoeffOn.AEEq b a := by
      simpa [hbdef] using pointwiseCoeffOn_ae_eq U a
    have hval : ∀ X : DoubledField d, doubledMuValue U b X = doubledMuValue U a X :=
      fun X => doubledMuValue_eq_ofAEEq hba X
    have hEll : IsEllipticFieldOn b.lam b.Lam (U : Set (Vec d)) b.toCoeffField := by
      simpa [hbdef] using pointwiseCoeffOn_isEllipticFieldOn U a
    let Rdat : PotentialSolenoidalL2RecoveryData (U : Set (Vec d)) :=
      potentialSolenoidalL2RecoveryDataOfClosureRealization
        (PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_convexDomain
          U.isDomain)
    let Mr : MuOperatorRealization (U : Set (Vec d)) b.toCoeffField :=
      (Rdat.toMuOperatorSystemDataOfIsEllipticFieldOn hEll
        (domain_volume_pos U)).toMuOperatorRealization
    set B := energyBilinOfOperator Mr.operator with hBdef
    have henergy : ∀ (W : DoubledField d)
        (hW : MemBlockL2 (U : Set (Vec d)) (blockStateOfDoubled W).eval),
        quadraticEnergy B (toHilbertBlockL2OfBlockField hW) = doubledMuValue U a W := by
      intro W hW
      rw [hBdef, Mr.quadraticEnergy_eq_blockEnergyAverage_of_blockState hW,
        ← doubledMuValue_eq_blockEnergyAverage U b W]
      exact hval W
    have hFL2 : MemBlockL2 (U : Set (Vec d)) (blockStateOfDoubled F).eval :=
      memBlockL2_blockField hFpot hFflux
    set x0 := toHilbertBlockL2OfBlockField hFL2 with hx0def
    set g : HilbertBlockL2 (U : Set (Vec d)) → ℝ := fun v => quadraticEnergy B (x0 + v) with hgdef
    have hgcont : Continuous g :=
      (quadraticEnergy_continuous B).comp (continuous_const.add continuous_id)
    have hgE : ∀ Y : {Y : DoubledField d // IsDoubledTestField U Y},
        g (E Y) = doubledMuValue U a (F + Y.1) := by
      intro Y
      have hFYpot : MemVectorL2 (U : Set (Vec d)) (F + Y.1).potential := hFpot.add Y.2.1.1
      have hFYflux : MemVectorL2 (U : Set (Vec d)) (F + Y.1).flux := hFflux.add Y.2.2.1
      have hFY : MemBlockL2 (U : Set (Vec d)) (blockStateOfDoubled (F + Y.1)).eval :=
        memBlockL2_blockField hFYpot hFYflux
      have hsplit : toHilbertBlockL2OfBlockField hFY = x0 + E Y :=
        toHilbertBlockL2OfBlockField_add hFL2 (memBlockL2_blockField Y.2.1.1 Y.2.2.1) hFY
          fun _ => rfl
      have h := henergy (F + Y.1) hFY
      rw [hsplit] at h
      exact h
    -- the value set, its lower bound and the countable subfamily
    have htne : (doubledMuFieldValueSet U a F).Nonempty :=
      ⟨doubledMuValue U a F, ⟨F, isDoubledMuAdmissibleField_self U F, rfl⟩⟩
    have htlb : ∀ m ∈ doubledMuFieldValueSet U a F, (0 : ℝ) ≤ m := by
      rintro m ⟨X, hX, rfl⟩
      have hXL2 : MemBlockL2 (U : Set (Vec d)) (blockStateOfDoubled X).eval :=
        memBlockL2_blockField (memVectorL2_potential_of_isDoubledMuAdmissibleField hFpot hX)
          (memVectorL2_flux_of_isDoubledMuAdmissibleField hFflux hX)
      rw [← henergy X hXL2]
      exact quadraticEnergy_nonneg Mr.operatorCoercive _
    have htbdd : BddBelow (doubledMuFieldValueSet U a F) := ⟨0, htlb⟩
    have hsub : (Set.range fun n : ℕ => doubledMuValue U a (F + (theta n).1)) ⊆
        doubledMuFieldValueSet U a F := by
      rintro m ⟨n, rfl⟩
      exact ⟨F + (theta n).1,
        isDoubledMuAdmissibleField_add (isDoubledMuAdmissibleField_self U F) (theta n).2, rfl⟩
    have happrox : ∀ m ∈ doubledMuFieldValueSet U a F, ∀ ε > (0 : ℝ),
        ∃ n : ℕ, doubledMuValue U a (F + (theta n).1) < m + ε := by
      rintro m ⟨X, hX, rfl⟩ ε hε
      set Y : {Y : DoubledField d // IsDoubledTestField U Y} :=
        ⟨X - F, (isDoubledMuAdmissibleField_iff_isDoubledTestField_sub U F X).1 hX⟩ with hYdef
      have hgY : g (E Y) = doubledMuValue U a X := by
        rw [hgE Y]
        change doubledMuValue U a (F + (X - F)) = _
        rw [add_sub_cancel_doubledField]
      obtain ⟨delta, hdelta, hball⟩ := Metric.continuousAt_iff.1 hgcont.continuousAt ε hε
      obtain ⟨n, hn⟩ :=
        Metric.denseRange_iff.1 (TopologicalSpace.denseRange_denseSeq A)
          (⟨E Y, Set.mem_range_self Y⟩ : A) delta hdelta
      refine ⟨n, ?_⟩
      have hdist : dist (E (theta n)) (E Y) < delta := by
        rw [htheta n]
        rw [Subtype.dist_eq] at hn
        exact dist_comm (E Y) _ ▸ hn
      have hlt := hball hdist
      rw [Real.dist_eq, abs_sub_lt_iff] at hlt
      have h1 : g (E (theta n)) = doubledMuValue U a (F + (theta n).1) := hgE (theta n)
      rw [h1, hgY] at hlt
      linarith [hlt.1]
    refine ⟨?_, ?_⟩
    · rintro m ⟨n, rfl⟩
      exact csInf_le htbdd (hsub ⟨n, rfl⟩)
    · intro w hw
      refine le_csInf htne ?_
      intro m hm
      by_contra hcon
      push Not at hcon
      obtain ⟨n, hn⟩ := happrox m hm (w - m) (by linarith)
      have hwn : w ≤ doubledMuValue U a (F + (theta n).1) := hw ⟨n, rfl⟩
      linarith

/-! ## The named competitor family and the measurability reduction -/

/-- **The canonical countable competitor family of the field-slope problem on
`U`.**  A sequence of test fields depending on the domain only; it names the
sequence produced by `exists_countable_doubledMuFieldCompetitors`.  It occurs in
no source-facing statement: it is an internal index for the countable infimum
below. -/
def doubledMuFieldCompetitor (U : Domain d) (n : ℕ) : DoubledField d :=
  (exists_countable_doubledMuFieldCompetitors U).choose n

/-- Each canonical competitor is a test field on `U`. -/
theorem isDoubledTestField_doubledMuFieldCompetitor (U : Domain d) (n : ℕ) :
    IsDoubledTestField U (doubledMuFieldCompetitor U n) :=
  (exists_countable_doubledMuFieldCompetitors U).choose_spec.1 n

/-- **The field-slope minimum is the greatest lower bound of the canonical
countable family of competitor energies.** -/
theorem isGLB_doubledMuField (U : Domain d) (a : CoeffOn U) (F : DoubledField d)
    (hpot : MemVectorL2 (U : Set (Vec d)) F.potential)
    (hflux : MemVectorL2 (U : Set (Vec d)) F.flux) :
    IsGLB (Set.range fun n => doubledMuValue U a (F + doubledMuFieldCompetitor U n))
      (doubledMuField U a F) :=
  (exists_countable_doubledMuFieldCompetitors U).choose_spec.2 a F hpot hflux

/-- **The field-slope minimum as a countable infimum.**  This is the identity
that makes the Step-2 endpoint integrand measurable in the sample. -/
theorem doubledMuField_eq_ciInf (U : Domain d) (a : CoeffOn U) (F : DoubledField d)
    (hpot : MemVectorL2 (U : Set (Vec d)) F.potential)
    (hflux : MemVectorL2 (U : Set (Vec d)) F.flux) :
    doubledMuField U a F =
      ⨅ n : ℕ, doubledMuValue U a (F + doubledMuFieldCompetitor U n) :=
  ((isGLB_doubledMuField U a F hpot hflux).ciInf_eq).symm

/-- **The measurability reduction.**  If the sample-dependent coefficient and
slope field make every *fixed-competitor* energy measurable, then the
field-slope minimum is measurable.  No minimizer is selected anywhere: the
conclusion is obtained from the countable-infimum identity. -/
theorem aemeasurable_doubledMuField {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} (U : Domain d) (a : Omega → CoeffOn U) (F : Omega → DoubledField d)
    (hpot : ∀ omega, MemVectorL2 (U : Set (Vec d)) (F omega).potential)
    (hflux : ∀ omega, MemVectorL2 (U : Set (Vec d)) (F omega).flux)
    (hcomp : ∀ n : ℕ, AEMeasurable
      (fun omega => doubledMuValue U (a omega) (F omega + doubledMuFieldCompetitor U n)) mu) :
    AEMeasurable (fun omega => doubledMuField U (a omega) (F omega)) mu := by
  have hrw : (fun omega => doubledMuField U (a omega) (F omega)) =
      fun omega =>
        ⨅ n : ℕ, doubledMuValue U (a omega) (F omega + doubledMuFieldCompetitor U n) := by
    funext omega
    exact doubledMuField_eq_ciInf U (a omega) (F omega) (hpot omega) (hflux omega)
  rw [hrw]
  exact AEMeasurable.iInf hcomp

/-- **The integrability reduction.**  The field-slope minimum is squeezed
between `0` and the energy of the slope field itself, so it is sample-integrable
as soon as it is measurable and that one *fixed* competitor's energy is
integrable.  No estimate on the minimum is used. -/
theorem integrable_doubledMuField {Omega : Type*} [MeasurableSpace Omega]
    {mu : Measure Omega} (U : Domain d) (a : Omega → CoeffOn U) (F : Omega → DoubledField d)
    (hpot : ∀ omega, MemVectorL2 (U : Set (Vec d)) (F omega).potential)
    (hflux : ∀ omega, MemVectorL2 (U : Set (Vec d)) (F omega).flux)
    (hcomp : ∀ n : ℕ, AEMeasurable
      (fun omega => doubledMuValue U (a omega) (F omega + doubledMuFieldCompetitor U n)) mu)
    (hbackground : Integrable (fun omega => doubledMuValue U (a omega) (F omega)) mu) :
    Integrable (fun omega => doubledMuField U (a omega) (F omega)) mu := by
  refine Integrable.mono' hbackground
    ((aemeasurable_doubledMuField U a F hpot hflux hcomp).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun omega => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (doubledMuField_nonneg U (a omega) (F omega))]
  exact doubledMuField_le_self U (a omega) (F omega)

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
