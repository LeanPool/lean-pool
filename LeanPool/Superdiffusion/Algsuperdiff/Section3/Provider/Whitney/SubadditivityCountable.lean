/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Whitney.SubadditivityBetter

/-!
# SubadditivityCountable

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: variational simplex subadditivity over a countable dissection

This file provides a countable-carrier candidate implementation for Lemma
`l.subadd.betterer` and its display `e.subadd.betterer` of ABK26 by removing the
finiteness restriction of
`Algsuperdiff.Section3.Provider.Whitney.bfA_quadratic_le_simplex_weighted_sum`.

The paper's own Whitney partition `W(cu_m)`, hence its simplicial refinement
`SW(cu_m)`, is countably infinite, and the consumer `e.sum-of-a-decomp` sums
over that infinite family.

```
  ENNReal.ofReal ((p,q) . bfA(cu_m; a) (p,q))
    <= sum'_{s in SW} ENNReal.ofReal ((|s| / |cu_m|)
         (grad hat-linear_p (s), div hat-D_q (s))
           . bfA(s; a) (grad hat-linear_p (s), div hat-D_q (s))).
```

No summability hypothesis is carried: when the series diverges the statement is
trivially true, exactly as the tex inequality is.  A real-valued corollary
carrying an explicit `Summable` binder is provided separately as a convenience
for consumers that have already established summability.  The `[0,∞]` theorem
is the principal countable provider here, but neither declaration is an exact
frozen node export.

## Proof route

The paper's one-line variational comparison is proved locally by gluing exact cell
minimizers into a single competitor for `Q`.  With infinitely many cells only
finitely many corrections can be inserted at a time, so the glue is performed
over an arbitrary `J : Finset ι` and leaves the remainder

```
  |Q|^{-1} ( int_Q E(F,G) - sum_{i in J} int_{S i} E(F,G) )
```

where `E(F,G)` is the block energy density of the competitor pair itself — an
integrable function on `Q` because `F - p in L^2_pot,0(Q)` and `G - q in
L^2_sol,0(Q)`.
-/

namespace Algsuperdiff
namespace Section3
namespace Provider
namespace Whitney

open HCPolySupport
open MeasureTheory
open scoped NNReal ENNReal

variable {d : ℕ}

/-! ## Integrability and sign of the block energy density -/

/-- The block energy density of a block-`L²` doubled field is integrable on the
domain.  This is the ellipticity-free route already used for the cell energies
in `SubadditivityBetter.lean`: pass to CoarseGraining's pointwise elliptic
representative of the coefficient field, which is a.e. equal to the given one. -/
theorem blockEnergyDensityAt_integrableOn {U : Book.Ch02.Domain d} (a : Book.Ch02.CoeffOn U)
    (X : Book.Ch02.DoubledField d)
    (hX : MemBlockL2 (U : Set (Vec d)) fun x => ((X.potential x, X.flux x) : BlockVec d)) :
    MeasureTheory.IntegrableOn
      (fun x => Book.Ch02.blockEnergyDensityAt a (X.eval x) x) (U : Set (Vec d)) volume := by
  have : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (U : Set (Vec d))) :=
    U.isDomain.isFiniteMeasure_restrict_volume
  have hbInt :
      MeasureTheory.IntegrableOn
        (blockEnergyDensity
          (HCPolySupport.Internal.Ch02.BookCh02.pointwiseCoeffOn U a).toCoeffField
          ({ potential := X.potential, flux := X.flux } : BlockState d))
        (U : Set (Vec d)) volume :=
    blockEnergyDensity_integrableOn_of_memBlockL2_of_isEllipticFieldOn hX
      (HCPolySupport.Internal.Ch02.BookCh02.pointwiseCoeffOn_isEllipticFieldOn U a)
  refine hbInt.congr ?_
  refine (Book.Ch02.blockMatrixField_ae_eq_ofAEEq
    (HCPolySupport.Internal.Ch02.BookCh02.pointwiseCoeffOn_ae_eq U a)).mono ?_
  intro x hx
  show Book.Ch02.blockEnergyDensityAt
      (HCPolySupport.Internal.Ch02.BookCh02.pointwiseCoeffOn U a) (X.eval x) x =
    Book.Ch02.blockEnergyDensityAt a (X.eval x) x
  rw [Book.Ch02.blockEnergyDensityAt, Book.Ch02.blockEnergyDensityAt, hx]

/-- The doubled block energy density is a.e. nonnegative on the domain, because
the coefficient field is a.e. elliptic there. -/
theorem blockEnergyDensityAt_nonneg_ae {U : Book.Ch02.Domain d} (a : Book.Ch02.CoeffOn U)
    (Z : Vec d → BlockVec d) :
    ∀ᵐ x ∂(volume.restrict (U : Set (Vec d))),
      0 ≤ Book.Ch02.blockEnergyDensityAt a (Z x) x := by
  filter_upwards [a.aeElliptic] with x hx
  have hfield : Book.Ch02.blockMatrixField a x = blockMatrixOfCoeff (a.toCoeffField x) := rfl
  have hpos : ∀ W : BlockVec d,
      0 ≤ blockVecDot W (blockMatVecMul (blockMatrixOfCoeff (a.toCoeffField x)) W) := by
    rintro ⟨u, v⟩
    rcases eq_or_ne ((u, v) : BlockVec d) 0 with hz | hz
    · rw [hz]
      simp [blockVecDot, vecDot]
    · exact (blockMatrixOfCoeff_quadratic_pos_of_isEllipticMatrix hx hz).le
  have hquad : 0 ≤ blockVecDot (Z x) (blockMatVecMul (Book.Ch02.blockMatrixField a x) (Z x)) := by
    rw [hfield]
    exact hpos (Z x)
  rw [Book.Ch02.blockEnergyDensityAt]
  linarith

/-- Every admissible energy value is nonnegative. -/
theorem doubledMuValue_nonneg {U : Book.Ch02.Domain d} (a : Book.Ch02.CoeffOn U)
    (X : Book.Ch02.DoubledField d) : 0 ≤ Book.Ch02.doubledMuValue U a X := by
  have hint : (0 : ℝ) ≤
      ∫ x in (U : Set (Vec d)), Book.Ch02.blockEnergyDensityAt a (X.eval x) x ∂volume :=
    MeasureTheory.integral_nonneg_of_ae (blockEnergyDensityAt_nonneg_ae a X.eval)
  rw [Book.Ch02.doubledMuValue, Book.Ch02.average]
  exact mul_nonneg (by positivity) hint

/-- `mu(U,P;a) >= 0`. -/
theorem doubledMu_nonneg {U : Book.Ch02.Domain d} (a : Book.Ch02.CoeffOn U)
    (P : BlockVec d) : 0 ≤ Book.Ch02.doubledMu U a P := by
  refine le_csInf ⟨Book.Ch02.doubledMuValue U a { potential := fun _ => P.1, flux := fun _ => P.2 },
    ⟨{ potential := fun _ => P.1, flux := fun _ => P.2 }, ⟨?_, ?_⟩, rfl⟩⟩ ?_
  · simpa using (potentialZeroTraceFieldOn_zero (U := (U : Set (Vec d))))
  · simpa using (solenoidalZeroNormalTraceFieldOn_zero (U := (U : Set (Vec d))))
  · rintro b ⟨X, -, rfl⟩
    exact doubledMuValue_nonneg a X

/-! ## The glue over a finite subfamily, with remainder -/

/-- **Variational subadditivity over a finite subfamily of the dissection.**

Gluing the exact cell minimizers of the cells indexed by `J` into the
competitor pair `(F, G)` produces an admissible competitor for `Q` whose energy
is the weighted sum of the cell energies plus the energy of `(F, G)` on the part
of `Q` not covered by `J`.  The remainder below is exactly
`|Q|^{-1} int_{Q \ Union_{i in J} S i} E(F,G)`.

No covering hypothesis is needed here, and `ι` is unrestricted. -/
theorem doubledMu_le_finset_weighted_sum_add_remainder
    {ι : Type} {Q : Book.Ch02.Domain d} {S : ι → Book.Ch02.Domain d}
    (a : Book.Ch02.CoeffOn Q) (aS : ∀ i, Book.Ch02.CoeffOn (S i))
    (haS : ∀ i, (aS i).toCoeffField = a.toCoeffField)
    (hsub : ∀ i, (S i : Set (Vec d)) ⊆ (Q : Set (Vec d)))
    (hdisj : Pairwise fun i j => Disjoint (S i : Set (Vec d)) (S j : Set (Vec d)))
    (p q : Vec d) (F G : Vec d → Vec d) (Fc Gc : ι → Vec d)
    (hF : Book.Ch01.PotentialZeroTraceFieldOn (Q : Set (Vec d)) fun x => F x - p)
    (hG : Book.Ch01.SolenoidalZeroNormalTraceFieldOn (Q : Set (Vec d)) fun x => G x - q)
    (hFc : ∀ i, ∀ x ∈ (S i : Set (Vec d)), F x = Fc i)
    (hGc : ∀ i, ∀ x ∈ (S i : Set (Vec d)), G x = Gc i)
    (J : Finset ι) :
    Book.Ch02.doubledMu Q a (p, q) ≤
      (∑ i ∈ J, ((volume (S i : Set (Vec d))).toReal / (volume (Q : Set (Vec d))).toReal) *
          Book.Ch02.doubledMu (S i) (aS i) (Fc i, Gc i)) +
        (volume (Q : Set (Vec d))).toReal⁻¹ *
          ((∫ x in (Q : Set (Vec d)),
              Book.Ch02.blockEnergyDensityAt a ((F x, G x) : BlockVec d) x ∂volume) -
            ∑ i ∈ J, ∫ x in (S i : Set (Vec d)),
              Book.Ch02.blockEnergyDensityAt a ((F x, G x) : BlockVec d) x ∂volume) := by
  classical
  have : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (Q : Set (Vec d))) :=
    Q.isDomain.isFiniteMeasure_restrict_volume
  have hQopen : IsOpen (Q : Set (Vec d)) := Q.isDomain.isOpen
  have hSopen : ∀ i, IsOpen (S i : Set (Vec d)) := fun i => (S i).isDomain.isOpen
  have hvolQ : (0 : ℝ) < (volume (Q : Set (Vec d))).toReal :=
    HCPolySupport.Internal.Ch02.BookCh02.domain_volume_pos Q
  have hvolS : ∀ i, (0 : ℝ) < (volume (S i : Set (Vec d))).toReal := fun i =>
    HCPolySupport.Internal.Ch02.BookCh02.domain_volume_pos (S i)
  -- the competitor pair, as a doubled field, is block `L²` on `Q`
  have hWL2 : MemBlockL2 (Q : Set (Vec d)) fun x => ((F x, G x) : BlockVec d) :=
    memBlockL2_pair (memVectorL2_of_sub_const (c := p) hF.1)
      (memVectorL2_of_sub_const (c := q) hG.1)
  have hIntW : MeasureTheory.IntegrableOn
      (fun x => Book.Ch02.blockEnergyDensityAt a ((F x, G x) : BlockVec d) x)
      (Q : Set (Vec d)) volume :=
    blockEnergyDensityAt_integrableOn a { potential := F, flux := G } hWL2
  -- exact minimizers on the cells
  choose X hX using fun i => (Book.Ch02.doubledMuTheory (S i) (aS i)).minimizer_exists (Fc i, Gc i)
  -- the glued competitor over the cells indexed by `J`
  set cPot : ι → Vec d → Vec d := fun i =>
    (S i : Set (Vec d)).indicator fun y => (X i).potential y - Fc i with hcPot
  set cFlux : ι → Vec d → Vec d := fun i =>
    (S i : Set (Vec d)).indicator fun y => (X i).flux y - Gc i with hcFlux
  set Y : Book.Ch02.DoubledField d :=
    { potential := fun x => F x + ∑ i ∈ J, cPot i x
      flux := fun x => G x + ∑ i ∈ J, cFlux i x } with hY
  have hYadm : Book.Ch02.IsDoubledMuAdmissible Q (p, q) Y := by
    constructor
    · have hterm : ∀ i ∈ J,
          Book.Ch01.PotentialZeroTraceFieldOn (Q : Set (Vec d)) (cPot i) := by
        intro i _
        exact potentialZeroTraceFieldOn_indicator_of_subset hQopen
          (hSopen i).measurableSet (hsub i) (hX i).1.1
      have hsum := potentialZeroTraceFieldOn_sum J (U := (Q : Set (Vec d))) cPot hterm
      have := potentialZeroTraceFieldOn_add hF hsum
      simpa [hY, add_sub_right_comm] using this
    · have hterm : ∀ i ∈ J,
          Book.Ch01.SolenoidalZeroNormalTraceFieldOn (Q : Set (Vec d)) (cFlux i) := by
        intro i _
        exact solenoidalZeroNormalTraceFieldOn_indicator_of_subset (hSopen i) (hsub i) (hX i).1.2
      have hsum := solenoidalZeroNormalTraceFieldOn_sum J (U := (Q : Set (Vec d))) cFlux hterm
      have := solenoidalZeroNormalTraceFieldOn_add hG hsum
      simpa [hY, add_sub_right_comm] using this
  -- on a glued cell the competitor is that cell's minimizer
  have hYeq : ∀ i ∈ J, ∀ x ∈ (S i : Set (Vec d)), Y.eval x = (X i).eval x := by
    intro i hi x hx
    have hPot : ∑ j ∈ J, cPot j x = (X i).potential x - Fc i := by
      rw [Finset.sum_eq_single i]
      · simp [hcPot, Set.indicator_of_mem hx]
      · intro j _ hj
        have hxj : x ∉ (S j : Set (Vec d)) :=
          Set.disjoint_left.mp (hdisj (Ne.symm hj)) hx
        simp [hcPot, Set.indicator_of_notMem hxj]
      · intro hmem
        exact absurd hi hmem
    have hFlux : ∑ j ∈ J, cFlux j x = (X i).flux x - Gc i := by
      rw [Finset.sum_eq_single i]
      · simp [hcFlux, Set.indicator_of_mem hx]
      · intro j _ hj
        have hxj : x ∉ (S j : Set (Vec d)) :=
          Set.disjoint_left.mp (hdisj (Ne.symm hj)) hx
        simp [hcFlux, Set.indicator_of_notMem hxj]
      · intro hmem
        exact absurd hi hmem
    have hFx : F x = Fc i := hFc i x hx
    have hGx : G x = Gc i := hGc i x hx
    show ((Y.potential x, Y.flux x) : BlockVec d) = ((X i).potential x, (X i).flux x)
    simp [hY, hPot, hFlux, hFx, hGx]
  -- off the glued cells the competitor is the original pair
  have hYoff : ∀ x ∈ (Q : Set (Vec d)) \ ⋃ i ∈ J, (S i : Set (Vec d)),
      Y.eval x = ((F x, G x) : BlockVec d) := by
    intro x hx
    have hxJ : ∀ i ∈ J, x ∉ (S i : Set (Vec d)) := fun i hi hmem =>
      hx.2 (Set.mem_biUnion hi hmem)
    have hPot : ∑ i ∈ J, cPot i x = 0 :=
      Finset.sum_eq_zero fun i hi => by simp [hcPot, Set.indicator_of_notMem (hxJ i hi)]
    have hFlux : ∑ i ∈ J, cFlux i x = 0 :=
      Finset.sum_eq_zero fun i hi => by simp [hcFlux, Set.indicator_of_notMem (hxJ i hi)]
    show ((Y.potential x, Y.flux x) : BlockVec d) = (F x, G x)
    simp [hY, hPot, hFlux]
  -- the coefficient field is the same on each cell
  have hblock : ∀ i, ∀ x : Vec d,
      Book.Ch02.blockMatrixField (aS i) x = Book.Ch02.blockMatrixField a x := by
    intro i x
    simp only [Book.Ch02.blockMatrixField, haS i]
  have hEnergyEq : ∀ i ∈ J, ∀ x ∈ (S i : Set (Vec d)),
      Book.Ch02.blockEnergyDensityAt a (Y.eval x) x =
        Book.Ch02.blockEnergyDensityAt (aS i) ((X i).eval x) x := by
    intro i hi x hx
    rw [Book.Ch02.blockEnergyDensityAt, Book.Ch02.blockEnergyDensityAt, hYeq i hi x hx, hblock i x]
  -- integrability of the cell energies and of the glued energy
  have hIntCell : ∀ i,
      MeasureTheory.IntegrableOn
        (fun x => Book.Ch02.blockEnergyDensityAt (aS i) ((X i).eval x) x)
        (S i : Set (Vec d)) volume := by
    intro i
    have : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (S i : Set (Vec d))) :=
      (S i).isDomain.isFiniteMeasure_restrict_volume
    exact blockEnergyDensityAt_integrableOn (aS i) (X i)
      (memBlockL2_pair (memVectorL2_of_sub_const (c := Fc i) (hX i).1.1.1)
        (memVectorL2_of_sub_const (c := Gc i) (hX i).1.2.1))
  have hIntY : MeasureTheory.IntegrableOn
      (fun x => Book.Ch02.blockEnergyDensityAt a (Y.eval x) x) (Q : Set (Vec d)) volume :=
    blockEnergyDensityAt_integrableOn a Y
      (memBlockL2_pair (memVectorL2_of_sub_const (c := p) hYadm.1.1)
        (memVectorL2_of_sub_const (c := q) hYadm.2.1))
  have hIntGlue : ∀ i ∈ J,
      MeasureTheory.IntegrableOn
        (fun x => Book.Ch02.blockEnergyDensityAt a (Y.eval x) x)
        (S i : Set (Vec d)) volume := by
    intro i hi
    refine (hIntCell i).congr_fun ?_ (hSopen i).measurableSet
    intro x hx
    exact (hEnergyEq i hi x hx).symm
  -- measure-theoretic bookkeeping for the covered part
  have hAmeas : MeasurableSet (⋃ i ∈ J, (S i : Set (Vec d))) :=
    Finset.measurableSet_biUnion J fun i _ => (hSopen i).measurableSet
  have hAsub : (⋃ i ∈ J, (S i : Set (Vec d))) ⊆ (Q : Set (Vec d)) :=
    Set.iUnion₂_subset fun i _ => hsub i
  have hinter : (Q : Set (Vec d)) ∩ ⋃ i ∈ J, (S i : Set (Vec d)) =
      ⋃ i ∈ J, (S i : Set (Vec d)) :=
    Set.inter_eq_self_of_subset_right hAsub
  have hdisjJ : Set.Pairwise (↑J : Set ι)
      (Function.onFun Disjoint fun i => (S i : Set (Vec d))) :=
    fun _ _ _ _ hij => hdisj hij
  -- splitting the glued energy
  have hsplitGlue :
      ∫ x in (Q : Set (Vec d)), Book.Ch02.blockEnergyDensityAt a (Y.eval x) x ∂volume =
        (∑ i ∈ J, ∫ x in (S i : Set (Vec d)),
            Book.Ch02.blockEnergyDensityAt (aS i) ((X i).eval x) x ∂volume) +
          ∫ x in (Q : Set (Vec d)) \ ⋃ i ∈ J, (S i : Set (Vec d)),
            Book.Ch02.blockEnergyDensityAt a ((F x, G x) : BlockVec d) x ∂volume := by
    have hsplit := MeasureTheory.integral_inter_add_sdiff (μ := volume)
      (f := fun x => Book.Ch02.blockEnergyDensityAt a (Y.eval x) x) hAmeas hIntY
    rw [hinter] at hsplit
    rw [← hsplit]
    congr 1
    · rw [MeasureTheory.integral_biUnion_finset J (fun i _ => (hSopen i).measurableSet)
        hdisjJ hIntGlue]
      refine Finset.sum_congr rfl fun i hi => ?_
      exact MeasureTheory.setIntegral_congr_fun (hSopen i).measurableSet
        fun x hx => hEnergyEq i hi x hx
    · exact MeasureTheory.setIntegral_congr_fun (Q.measurableSet.diff hAmeas)
        fun x hx => by rw [hYoff x hx]
  -- splitting the pair energy
  have hdiffW :
      ∫ x in (Q : Set (Vec d)) \ ⋃ i ∈ J, (S i : Set (Vec d)),
          Book.Ch02.blockEnergyDensityAt a ((F x, G x) : BlockVec d) x ∂volume =
        (∫ x in (Q : Set (Vec d)),
            Book.Ch02.blockEnergyDensityAt a ((F x, G x) : BlockVec d) x ∂volume) -
          ∑ i ∈ J, ∫ x in (S i : Set (Vec d)),
            Book.Ch02.blockEnergyDensityAt a ((F x, G x) : BlockVec d) x ∂volume := by
    have hsplit := MeasureTheory.integral_inter_add_sdiff (μ := volume)
      (f := fun x => Book.Ch02.blockEnergyDensityAt a ((F x, G x) : BlockVec d) x) hAmeas hIntW
    rw [hinter, MeasureTheory.integral_biUnion_finset J (fun i _ => (hSopen i).measurableSet)
      hdisjJ fun i _ => hIntW.mono_set (hsub i)] at hsplit
    linarith
  -- the glued competitor's energy value
  have hvalue :
      Book.Ch02.doubledMuValue Q a Y =
        (∑ i ∈ J, ((volume (S i : Set (Vec d))).toReal / (volume (Q : Set (Vec d))).toReal) *
            Book.Ch02.doubledMuValue (S i) (aS i) (X i)) +
          (volume (Q : Set (Vec d))).toReal⁻¹ *
            ((∫ x in (Q : Set (Vec d)),
                Book.Ch02.blockEnergyDensityAt a ((F x, G x) : BlockVec d) x ∂volume) -
              ∑ i ∈ J, ∫ x in (S i : Set (Vec d)),
                Book.Ch02.blockEnergyDensityAt a ((F x, G x) : BlockVec d) x ∂volume) := by
    rw [Book.Ch02.doubledMuValue, Book.Ch02.average, hsplitGlue, hdiffW, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Book.Ch02.doubledMuValue, Book.Ch02.average]
    have hv : (volume (S i : Set (Vec d))).toReal ≠ 0 := (hvolS i).ne'
    have hw : (volume (Q : Set (Vec d))).toReal ≠ 0 := hvolQ.ne'
    field_simp
  obtain ⟨Z, hZ⟩ := (Book.Ch02.doubledMuTheory Q a).minimizer_exists (p, q)
  calc
    Book.Ch02.doubledMu Q a (p, q) = Book.Ch02.doubledMuValue Q a Z :=
      hZ.doubledMuValue_eq_doubledMu.symm
    _ ≤ Book.Ch02.doubledMuValue Q a Y := hZ.2 Y hYadm
    _ = (∑ i ∈ J, ((volume (S i : Set (Vec d))).toReal / (volume (Q : Set (Vec d))).toReal) *
            Book.Ch02.doubledMuValue (S i) (aS i) (X i)) +
          (volume (Q : Set (Vec d))).toReal⁻¹ *
            ((∫ x in (Q : Set (Vec d)),
                Book.Ch02.blockEnergyDensityAt a ((F x, G x) : BlockVec d) x ∂volume) -
              ∑ i ∈ J, ∫ x in (S i : Set (Vec d)),
                Book.Ch02.blockEnergyDensityAt a ((F x, G x) : BlockVec d) x ∂volume) := hvalue
    _ = (∑ i ∈ J, ((volume (S i : Set (Vec d))).toReal / (volume (Q : Set (Vec d))).toReal) *
            Book.Ch02.doubledMu (S i) (aS i) (Fc i, Gc i)) +
          (volume (Q : Set (Vec d))).toReal⁻¹ *
            ((∫ x in (Q : Set (Vec d)),
                Book.Ch02.blockEnergyDensityAt a ((F x, G x) : BlockVec d) x ∂volume) -
              ∑ i ∈ J, ∫ x in (S i : Set (Vec d)),
                Book.Ch02.blockEnergyDensityAt a ((F x, G x) : BlockVec d) x ∂volume) := by
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [(hX i).doubledMuValue_eq_doubledMu]

/-! ## The `mu`-form over a countable dissection -/

/-- **Variational simplex subadditivity over a countable dissection, `mu`-form.**

`mu(Q, (p,q)) ≤ ∑' (|S i| / |Q|) mu(S i, (Fc i, Gc i))` in `[0, ∞]`, whenever
the countably many cells `S i` tile `Q` up to a null set and the competitor pair
`(F, G)` is admissible for `(p,q)` on `Q` and is constant, with values
`(Fc i, Gc i)`, on each cell. -/
theorem ofReal_doubledMu_le_tsum_of_dissection
    {ι : Type} [Countable ι] {Q : Book.Ch02.Domain d} {S : ι → Book.Ch02.Domain d}
    (a : Book.Ch02.CoeffOn Q) (aS : ∀ i, Book.Ch02.CoeffOn (S i))
    (haS : ∀ i, (aS i).toCoeffField = a.toCoeffField)
    (hsub : ∀ i, (S i : Set (Vec d)) ⊆ (Q : Set (Vec d)))
    (hdisj : Pairwise fun i j => Disjoint (S i : Set (Vec d)) (S j : Set (Vec d)))
    (hcover : volume ((Q : Set (Vec d)) \ ⋃ i, (S i : Set (Vec d))) = 0)
    (p q : Vec d) (F G : Vec d → Vec d) (Fc Gc : ι → Vec d)
    (hF : Book.Ch01.PotentialZeroTraceFieldOn (Q : Set (Vec d)) fun x => F x - p)
    (hG : Book.Ch01.SolenoidalZeroNormalTraceFieldOn (Q : Set (Vec d)) fun x => G x - q)
    (hFc : ∀ i, ∀ x ∈ (S i : Set (Vec d)), F x = Fc i)
    (hGc : ∀ i, ∀ x ∈ (S i : Set (Vec d)), G x = Gc i) :
    ENNReal.ofReal (Book.Ch02.doubledMu Q a (p, q)) ≤
      ∑' i, ENNReal.ofReal
        (((volume (S i : Set (Vec d))).toReal / (volume (Q : Set (Vec d))).toReal) *
          Book.Ch02.doubledMu (S i) (aS i) (Fc i, Gc i)) := by
  classical
  have : MeasureTheory.IsFiniteMeasure (volumeMeasureOn (Q : Set (Vec d))) :=
    Q.isDomain.isFiniteMeasure_restrict_volume
  have hvolQ : (0 : ℝ) < (volume (Q : Set (Vec d))).toReal :=
    HCPolySupport.Internal.Ch02.BookCh02.domain_volume_pos Q
  have hvolS : ∀ i, (0 : ℝ) < (volume (S i : Set (Vec d))).toReal := fun i =>
    HCPolySupport.Internal.Ch02.BookCh02.domain_volume_pos (S i)
  have hWL2 : MemBlockL2 (Q : Set (Vec d)) fun x => ((F x, G x) : BlockVec d) :=
    memBlockL2_pair (memVectorL2_of_sub_const (c := p) hF.1)
      (memVectorL2_of_sub_const (c := q) hG.1)
  have hIntW : MeasureTheory.IntegrableOn
      (fun x => Book.Ch02.blockEnergyDensityAt a ((F x, G x) : BlockVec d) x)
      (Q : Set (Vec d)) volume :=
    blockEnergyDensityAt_integrableOn a { potential := F, flux := G } hWL2
  -- the cells exhaust `Q` up to a null set
  have haeSet : (Q : Set (Vec d)) =ᵐ[volume] ⋃ i, (S i : Set (Vec d)) := by
    refine (MeasureTheory.ae_eq_set).2 ⟨hcover, ?_⟩
    have hempty : (⋃ i, (S i : Set (Vec d))) \ (Q : Set (Vec d)) = ∅ := by
      rw [Set.sdiff_eq_empty]
      exact Set.iUnion_subset hsub
    rw [hempty]
    simp
  have hHasSum :
      HasSum (fun i => ∫ x in (S i : Set (Vec d)),
          Book.Ch02.blockEnergyDensityAt a ((F x, G x) : BlockVec d) x ∂volume)
        (∫ x in (Q : Set (Vec d)),
          Book.Ch02.blockEnergyDensityAt a ((F x, G x) : BlockVec d) x ∂volume) := by
    have h := MeasureTheory.hasSum_integral_iUnion (μ := volume)
      (f := fun x => Book.Ch02.blockEnergyDensityAt a ((F x, G x) : BlockVec d) x)
      (fun i => (S i).measurableSet) (fun _ _ hij => hdisj hij)
      (hIntW.mono_set (Set.iUnion_subset hsub))
    rwa [← MeasureTheory.setIntegral_congr_set haeSet] at h
  -- the remainder tends to zero along the `Finset` filter
  have hrem : Filter.Tendsto (fun J : Finset ι =>
      (volume (Q : Set (Vec d))).toReal⁻¹ *
        ((∫ x in (Q : Set (Vec d)),
            Book.Ch02.blockEnergyDensityAt a ((F x, G x) : BlockVec d) x ∂volume) -
          ∑ i ∈ J, ∫ x in (S i : Set (Vec d)),
            Book.Ch02.blockEnergyDensityAt a ((F x, G x) : BlockVec d) x ∂volume))
      Filter.atTop (nhds 0) := by
    have h := ((tendsto_const_nhds (x :=
        ∫ x in (Q : Set (Vec d)),
          Book.Ch02.blockEnergyDensityAt a ((F x, G x) : BlockVec d) x ∂volume)
      (f := Filter.atTop (α := Finset ι))).sub hHasSum).const_mul
      (volume (Q : Set (Vec d))).toReal⁻¹
    simpa using h
  refine ENNReal.le_of_forall_pos_le_add ?_
  intro ε hε _
  have hεR : (0 : ℝ) < (ε : ℝ) := hε
  obtain ⟨J, hJ⟩ := (hrem.eventually (gt_mem_nhds hεR)).exists
  have hnn : ∀ i ∈ J,
      (0 : ℝ) ≤ ((volume (S i : Set (Vec d))).toReal / (volume (Q : Set (Vec d))).toReal) *
        Book.Ch02.doubledMu (S i) (aS i) (Fc i, Gc i) := fun i _ =>
    mul_nonneg (div_nonneg (hvolS i).le hvolQ.le) (doubledMu_nonneg (aS i) (Fc i, Gc i))
  have hglue := doubledMu_le_finset_weighted_sum_add_remainder a aS haS hsub hdisj
    p q F G Fc Gc hF hG hFc hGc J
  have hle : Book.Ch02.doubledMu Q a (p, q) ≤
      (∑ i ∈ J, ((volume (S i : Set (Vec d))).toReal / (volume (Q : Set (Vec d))).toReal) *
        Book.Ch02.doubledMu (S i) (aS i) (Fc i, Gc i)) + (ε : ℝ) := by
    linarith
  calc
    ENNReal.ofReal (Book.Ch02.doubledMu Q a (p, q))
        ≤ ENNReal.ofReal
            ((∑ i ∈ J, ((volume (S i : Set (Vec d))).toReal /
                (volume (Q : Set (Vec d))).toReal) *
              Book.Ch02.doubledMu (S i) (aS i) (Fc i, Gc i)) + (ε : ℝ)) :=
          ENNReal.ofReal_le_ofReal hle
    _ ≤ ENNReal.ofReal
          (∑ i ∈ J, ((volume (S i : Set (Vec d))).toReal / (volume (Q : Set (Vec d))).toReal) *
            Book.Ch02.doubledMu (S i) (aS i) (Fc i, Gc i)) + ENNReal.ofReal (ε : ℝ) :=
        ENNReal.ofReal_add_le
    _ = (∑ i ∈ J, ENNReal.ofReal
            (((volume (S i : Set (Vec d))).toReal / (volume (Q : Set (Vec d))).toReal) *
              Book.Ch02.doubledMu (S i) (aS i) (Fc i, Gc i))) + (ε : ℝ≥0∞) := by
        rw [ENNReal.ofReal_sum_of_nonneg hnn, ENNReal.ofReal_coe_nnreal]
    _ ≤ (∑' i, ENNReal.ofReal
            (((volume (S i : Set (Vec d))).toReal / (volume (Q : Set (Vec d))).toReal) *
              Book.Ch02.doubledMu (S i) (aS i) (Fc i, Gc i))) + (ε : ℝ≥0∞) :=
        add_le_add (ENNReal.sum_le_tsum J) le_rfl

/-! ## The countable-carrier provider statement -/

/-- **Countable-carrier provider for `l.subadd.betterer`, display
`e.subadd.betterer`.**

For a countable partition of the cube `Q` into cells `S i` and a
potential-solenoidal competitor pair `(F, G) ∈ (p + L²_pot,0(Q)) × (q +
L²_sol,0(Q))` which is constant on each cell with values `(Fc i, Gc i)`,

`(p,q) . bfA(Q; a) (p,q) ≤ ∑' (|S i| / |Q|) (Fc i, Gc i) . bfA(S i; a) (Fc i, Gc i)`

as an inequality in `[0, ∞]`. -/
theorem ofReal_bfA_quadratic_le_simplex_weighted_tsum
    {ι : Type} [Countable ι] {Q : Book.Ch02.Domain d} {S : ι → Book.Ch02.Domain d}
    (a : Book.Ch02.CoeffOn Q) (aS : ∀ i, Book.Ch02.CoeffOn (S i))
    (haS : ∀ i, (aS i).toCoeffField = a.toCoeffField)
    (hsub : ∀ i, (S i : Set (Vec d)) ⊆ (Q : Set (Vec d)))
    (hdisj : Pairwise fun i j => Disjoint (S i : Set (Vec d)) (S j : Set (Vec d)))
    (hcover : volume ((Q : Set (Vec d)) \ ⋃ i, (S i : Set (Vec d))) = 0)
    (p q : Vec d) (F G : Vec d → Vec d) (Fc Gc : ι → Vec d)
    (hF : Book.Ch01.PotentialZeroTraceFieldOn (Q : Set (Vec d)) fun x => F x - p)
    (hG : Book.Ch01.SolenoidalZeroNormalTraceFieldOn (Q : Set (Vec d)) fun x => G x - q)
    (hFc : ∀ i, ∀ x ∈ (S i : Set (Vec d)), F x = Fc i)
    (hGc : ∀ i, ∀ x ∈ (S i : Set (Vec d)), G x = Gc i) :
    ENNReal.ofReal
        (blockVecDot (p, q) (blockMatVecMul (Book.Ch02.coarseBlockMatrix Q a) (p, q))) ≤
      ∑' i, ENNReal.ofReal
        (((volume (S i : Set (Vec d))).toReal / (volume (Q : Set (Vec d))).toReal) *
          blockVecDot (Fc i, Gc i)
            (blockMatVecMul (Book.Ch02.coarseBlockMatrix (S i) (aS i)) (Fc i, Gc i))) := by
  have hmu := ofReal_doubledMu_le_tsum_of_dissection a aS haS hsub hdisj hcover
    p q F G Fc Gc hF hG hFc hGc
  have hQ : blockVecDot (p, q) (blockMatVecMul (Book.Ch02.coarseBlockMatrix Q a) (p, q)) =
      2 * Book.Ch02.doubledMu Q a (p, q) := by
    rw [(Book.Ch02.doubledMuTheory Q a).mu_quadratic (p, q)]
    ring
  have hS : ∀ i,
      ((volume (S i : Set (Vec d))).toReal / (volume (Q : Set (Vec d))).toReal) *
          blockVecDot (Fc i, Gc i)
            (blockMatVecMul (Book.Ch02.coarseBlockMatrix (S i) (aS i)) (Fc i, Gc i)) =
        2 * (((volume (S i : Set (Vec d))).toReal / (volume (Q : Set (Vec d))).toReal) *
          Book.Ch02.doubledMu (S i) (aS i) (Fc i, Gc i)) := by
    intro i
    rw [(Book.Ch02.doubledMuTheory (S i) (aS i)).mu_quadratic (Fc i, Gc i)]
    ring
  have hdouble : ∀ r : ℝ, ENNReal.ofReal (2 * r) = 2 * ENNReal.ofReal r := by
    intro r
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  rw [hQ]
  simp only [hS, hdouble]
  calc
    2 * ENNReal.ofReal (Book.Ch02.doubledMu Q a (p, q))
        ≤ 2 * ∑' i, ENNReal.ofReal
            (((volume (S i : Set (Vec d))).toReal / (volume (Q : Set (Vec d))).toReal) *
              Book.Ch02.doubledMu (S i) (aS i) (Fc i, Gc i)) := by gcongr
    _ = ∑' i, 2 * ENNReal.ofReal
            (((volume (S i : Set (Vec d))).toReal / (volume (Q : Set (Vec d))).toReal) *
              Book.Ch02.doubledMu (S i) (aS i) (Fc i, Gc i)) := ENNReal.tsum_mul_left.symm

end Whitney
end Provider
end Section3
end Algsuperdiff
