/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.OscillationDecayMinkowski
public import LeanPool.HighContrastHomogenization.Support.Sobolev.PotentialSolenoidalL2Recovery

/-!
# HarmonicReplaceMinkowski

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The `L^2` triangle inequality for normalized mean-square deviation

`OscillationDecayMinkowski` proves the two-term triangle inequality for the
normalized `L^2` deviation on a cube under **continuity** of the two fields, which
is what a smooth Weyl representative supplies.  The nested-recentring telescope,
however, splits the fine-scale gradient into finitely many harmonic increments
whose gradients are only `L^2`: continuity is unavailable, and the number of terms
is the number of scales, not two.

This module supplies both generalizations.  The quadratic core --
`OscillationDecayMinkowski.sq_sum_setIntegral_mul_le`, the Cauchy-Schwarz
inequality for the coordinate-summed bilinear form -- is already stated with
integrability hypotheses rather than continuity ones, so it is reused verbatim;
only the integrability side conditions have to be re-derived from `L^2`
membership, and the finite-sum form is a routine induction on top of the two-term
form.

## Contents

* `memScalarL2_coord_sub_const`, `memVectorL2_finsetSum` -- the `L^2` bookkeeping.
* `meanSquareDeviationVecOn_zero` -- the base case of the induction.
* `sqrt_meanSquareDeviationVecOn_add_le_of_memVectorL2` -- **the two-term triangle
  inequality** on an arbitrary finite-measure set, for `L^2` fields.
* `sqrt_meanSquareDeviationVecOn_finsetSum_le_of_memVectorL2` -- **the finite-sum
  triangle inequality**.
* `sqrt_meanSquareOscillationVecOn_finsetSum_le_of_memVectorL2` -- the form the
  telescope consumes as its `hsplit` hypothesis: the oscillation of a finite sum
  on the fine set is bounded by the sum of the deviations of the summands from
  arbitrary centres.

## Portability

This file depends only on **Mathlib**, on **CoarseGraining**
(`Homogenization.*`) and on the oscillation layer of this same directory.  It
mentions no object of the manuscript: no model, no cutoff, no shell, no
corrector, no `sigmaBar`.  It is intended to be portable into CoarseGraining by
a single mechanical namespace rename.

## References

* ABK26, `e.nablaw.oscillations` (the eventual consumer).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport MeasureTheory

variable {d : ℕ}

/-- A coordinate of a recentred `L^2` vector field is a scalar `L^2` function. -/
theorem memScalarL2_coord_sub_const {V : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn V)] {f : Vec d → Vec d}
    (hf : MemVectorL2 V f) (a : Vec d) (i : Fin d) :
    MemScalarL2 V (fun x => f x i - a i) :=
  (memScalarL2_coord_of_memVectorL2 hf i).sub
    (memScalarL2_coord_of_memVectorL2 (memVectorL2_const a) i)

/-- A finite sum of `L^2` vector fields is `L^2`. -/
theorem memVectorL2_finsetSum {ι : Type*} {V : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn V)] (s : Finset ι) {F : ι → Vec d → Vec d}
    (hF : ∀ j ∈ s, MemVectorL2 V (F j)) :
    MemVectorL2 V (fun x => ∑ j ∈ s, F j x) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      have hrw : (fun x : Vec d => ∑ j ∈ (∅ : Finset ι), F j x) = fun _ => (0 : Vec d) := by
        funext x
        rw [Finset.sum_empty]
      rw [hrw]
      exact memVectorL2_const (0 : Vec d)
  | cons j s hj ih =>
      have hj' : MemVectorL2 V (F j) := hF j (Finset.mem_cons_self j s)
      have hs : MemVectorL2 V (fun x => ∑ i ∈ s, F i x) :=
        ih fun i hi => hF i (Finset.mem_cons_of_mem hi)
      have hsum : MemVectorL2 V (fun x => F j x + ∑ i ∈ s, F i x) := hj'.add hs
      have hrw : (fun x => ∑ i ∈ Finset.cons j s hj, F i x)
          = fun x => F j x + ∑ i ∈ s, F i x := by
        funext x
        rw [Finset.sum_cons]
      rw [hrw]
      exact hsum

/-- The mean-square deviation of the zero field from zero vanishes. -/
theorem meanSquareDeviationVecOn_zero (V : Set (Vec d)) :
    Book.Ch01.meanSquareDeviationVecOn V (fun _ => (0 : Vec d)) 0 = 0 := by
  refine Finset.sum_eq_zero fun k _ => ?_
  show volumeAverage V (fun _ => ((0 : Vec d) k - (0 : Vec d) k) ^ 2) = 0
  simp [volumeAverage]

/-- **The two-term triangle inequality for `L^2` fields.**

`|| (f + g) - (a + b) ||_{L2bar (V)} <= || f - a ||_{L2bar (V)} +
|| g - b ||_{L2bar (V)}` on any finite-measure set, with no continuity hypothesis:
square integrability of the two fields is enough.  The proof is the expansion of
the normalized square together with Cauchy-Schwarz for the coordinate-summed
bilinear form. -/
theorem sqrt_meanSquareDeviationVecOn_add_le_of_memVectorL2 {V : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn V)] {f g : Vec d → Vec d}
    (hf : MemVectorL2 V f) (hg : MemVectorL2 V g) (a b : Vec d) :
    Real.sqrt (Book.Ch01.meanSquareDeviationVecOn V (fun x => f x + g x) (a + b))
      ≤ Real.sqrt (Book.Ch01.meanSquareDeviationVecOn V f a)
        + Real.sqrt (Book.Ch01.meanSquareDeviationVecOn V g b) := by
  have hvinv : (0 : ℝ) ≤ (volume V).toReal⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
  have hp2 : ∀ i : Fin d, IntegrableOn (fun x => (f x i - a i) ^ 2) V volume :=
    fun i => Book.Ch01.integrableOn_coord_sub_const_sq_of_memVectorL2 hf a i
  have hq2 : ∀ i : Fin d, IntegrableOn (fun x => (g x i - b i) ^ 2) V volume :=
    fun i => Book.Ch01.integrableOn_coord_sub_const_sq_of_memVectorL2 hg b i
  have hpq : ∀ i : Fin d,
      IntegrableOn (fun x => (f x i - a i) * (g x i - b i)) V volume := fun i =>
    (memScalarL2_coord_sub_const hf a i).integrable_mul
      (memScalarL2_coord_sub_const hg b i)
  obtain ⟨A, hA⟩ : ∃ r : ℝ, r = ∑ i : Fin d, ∫ x in V, (f x i - a i) ^ 2 ∂volume :=
    ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ r : ℝ, r = ∑ i : Fin d, ∫ x in V, (g x i - b i) ^ 2 ∂volume :=
    ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ r : ℝ,
      r = ∑ i : Fin d, ∫ x in V, (f x i - a i) * (g x i - b i) ∂volume := ⟨_, rfl⟩
  have hAnn : 0 ≤ A := by
    rw [hA]
    exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _
  have hBnn : 0 ≤ B := by
    rw [hB]
    exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _
  have hCS : X ≤ Real.sqrt A * Real.sqrt B := by
    have hsq : X ^ 2 ≤ A * B := by
      rw [hA, hB, hX]
      exact sq_sum_setIntegral_mul_le hp2 hq2 hpq
    calc X ≤ |X| := le_abs_self X
      _ = Real.sqrt (X ^ 2) := (Real.sqrt_sq_eq_abs X).symm
      _ ≤ Real.sqrt (A * B) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt A * Real.sqrt B := Real.sqrt_mul hAnn B
  have hnormA : Book.Ch01.meanSquareDeviationVecOn V f a = (volume V).toReal⁻¹ * A := by
    rw [hA, Finset.mul_sum]
    rfl
  have hnormB : Book.Ch01.meanSquareDeviationVecOn V g b = (volume V).toReal⁻¹ * B := by
    rw [hB, Finset.mul_sum]
    rfl
  have hsumexp : ∀ i : Fin d,
      (fun x : Vec d => ((fun y => f y + g y) x i - (a + b) i) ^ 2)
        = fun x : Vec d => ((f x i - a i) ^ 2
            + 2 * ((f x i - a i) * (g x i - b i))) + (g x i - b i) ^ 2 := by
    intro i
    funext x
    show (f x i + g x i - (a i + b i)) ^ 2 = _
    ring
  have hnormC : Book.Ch01.meanSquareDeviationVecOn V (fun x => f x + g x) (a + b)
      = (volume V).toReal⁻¹ * (A + 2 * X + B) := by
    have hcoord : ∀ i : Fin d,
        ∫ x in V, ((fun y => f y + g y) x i - (a + b) i) ^ 2 ∂volume
          = ((∫ x in V, (f x i - a i) ^ 2 ∂volume)
              + 2 * ∫ x in V, (f x i - a i) * (g x i - b i) ∂volume)
            + ∫ x in V, (g x i - b i) ^ 2 ∂volume := by
      intro i
      have h1 : IntegrableOn (fun x => 2 * ((f x i - a i) * (g x i - b i))) V volume :=
        (hpq i).const_mul _
      have h2 : IntegrableOn (fun x => (f x i - a i) ^ 2
          + 2 * ((f x i - a i) * (g x i - b i))) V volume := (hp2 i).add h1
      rw [hsumexp i, integral_add h2 (hq2 i), integral_add (hp2 i) h1, integral_const_mul]
    have hsum : ∑ i : Fin d,
        ∫ x in V, ((fun y => f y + g y) x i - (a + b) i) ^ 2 ∂volume = A + 2 * X + B := by
      rw [hA, hB, hX, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => hcoord i
    rw [← hsum, Finset.mul_sum]
    rfl
  rw [hnormA, hnormB, hnormC]
  have hle : A + 2 * X + B ≤ (Real.sqrt A + Real.sqrt B) ^ 2 := by
    have hA' : Real.sqrt A ^ 2 = A := Real.sq_sqrt hAnn
    have hB' : Real.sqrt B ^ 2 = B := Real.sq_sqrt hBnn
    nlinarith [hCS, hA', hB']
  calc Real.sqrt ((volume V).toReal⁻¹ * (A + 2 * X + B))
      = Real.sqrt ((volume V).toReal⁻¹) * Real.sqrt (A + 2 * X + B) :=
        Real.sqrt_mul hvinv _
    _ ≤ Real.sqrt ((volume V).toReal⁻¹) * Real.sqrt ((Real.sqrt A + Real.sqrt B) ^ 2) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle) (Real.sqrt_nonneg _)
    _ = Real.sqrt ((volume V).toReal⁻¹) * (Real.sqrt A + Real.sqrt B) := by
        rw [Real.sqrt_sq (by positivity)]
    _ = Real.sqrt ((volume V).toReal⁻¹ * A) + Real.sqrt ((volume V).toReal⁻¹ * B) := by
        rw [Real.sqrt_mul hvinv, Real.sqrt_mul hvinv]
        ring

/-- **The finite-sum triangle inequality for `L^2` fields.**

The normalized `L^2` deviation of a finite sum of `L^2` fields from the sum of
arbitrary centres is at most the sum of the individual deviations.  This is the
`N`-term form the nested-recentring telescope needs, `N` being the number of
scales; the proved two-term form is its `N = 2` case. -/
theorem sqrt_meanSquareDeviationVecOn_finsetSum_le_of_memVectorL2 {ι : Type*}
    {V : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn V)] (s : Finset ι)
    {F : ι → Vec d → Vec d} (hF : ∀ j ∈ s, MemVectorL2 V (F j)) (a : ι → Vec d) :
    Real.sqrt (Book.Ch01.meanSquareDeviationVecOn V
        (fun x => ∑ j ∈ s, F j x) (∑ j ∈ s, a j))
      ≤ ∑ j ∈ s, Real.sqrt (Book.Ch01.meanSquareDeviationVecOn V (F j) (a j)) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      simp [meanSquareDeviationVecOn_zero V]
  | cons j s hj ih =>
      have hj' : MemVectorL2 V (F j) := hF j (Finset.mem_cons_self j s)
      have hs : ∀ i ∈ s, MemVectorL2 V (F i) := fun i hi => hF i (Finset.mem_cons_of_mem hi)
      have hsum : MemVectorL2 V (fun x => ∑ i ∈ s, F i x) := memVectorL2_finsetSum s hs
      have htwo := sqrt_meanSquareDeviationVecOn_add_le_of_memVectorL2
        hj' hsum (a j) (∑ i ∈ s, a i)
      have hrest := ih hs
      have hcongr : Book.Ch01.meanSquareDeviationVecOn V
          (fun x => ∑ i ∈ Finset.cons j s hj, F i x) (∑ i ∈ Finset.cons j s hj, a i)
          = Book.Ch01.meanSquareDeviationVecOn V
            (fun x => F j x + ∑ i ∈ s, F i x) (a j + ∑ i ∈ s, a i) := by
        congr 1
        · funext x
          rw [Finset.sum_cons]
        · rw [Finset.sum_cons]
      rw [hcongr, Finset.sum_cons]
      linarith

/-- **The splitting inequality in oscillation form, for `L^2` fields.**

This is the shape consumed as `hsplit` by
`OscillationTelescope.le_zpow_mul_add_nsmul_of_nested_decomposition` once the
summands are the harmonic increments of the nested-recentring decomposition,
whose gradients are only square integrable. -/
theorem sqrt_meanSquareOscillationVecOn_finsetSum_le_of_memVectorL2 {ι : Type*}
    {V : Set (Vec d)} (hfin : volume V ≠ ⊤) (hpos : 0 < (volume V).toReal)
    [IsFiniteMeasure (volumeMeasureOn V)] (s : Finset ι) {F : ι → Vec d → Vec d}
    (hF : ∀ j ∈ s, MemVectorL2 V (F j)) (a : ι → Vec d) :
    Real.sqrt (Book.Ch01.meanSquareOscillationVecOn V (fun x => ∑ j ∈ s, F j x))
      ≤ ∑ j ∈ s, Real.sqrt (Book.Ch01.meanSquareDeviationVecOn V (F j) (a j)) := by
  have hsum : MemVectorL2 V (fun x => ∑ j ∈ s, F j x) := memVectorL2_finsetSum s hF
  have hint : ∀ i : Fin d, IntegrableOn (fun x => (∑ j ∈ s, F j x) i) V volume :=
    fun i => (memScalarL2_coord_of_memVectorL2 hsum i).integrable (by norm_num)
  have hint2 : ∀ i : Fin d, IntegrableOn (fun x => ((∑ j ∈ s, F j x) i) ^ 2) V volume := by
    intro i
    have hcoord : MemScalarL2 V (fun x => (∑ j ∈ s, F j x) i) :=
      memScalarL2_coord_of_memVectorL2 hsum i
    have hmul : IntegrableOn (fun x => (∑ j ∈ s, F j x) i * (∑ j ∈ s, F j x) i) V volume :=
      hcoord.integrable_mul hcoord
    simpa [pow_two] using hmul
  have hosc : Book.Ch01.meanSquareOscillationVecOn V (fun x => ∑ j ∈ s, F j x) ≤
      Book.Ch01.meanSquareDeviationVecOn V (fun x => ∑ j ∈ s, F j x) (∑ j ∈ s, a j) :=
    meanSquareOscillationVecOn_le_meanSquareDeviationVecOn hfin hpos _ hint hint2
  exact le_trans (Real.sqrt_le_sqrt hosc)
    (sqrt_meanSquareDeviationVecOn_finsetSum_le_of_memVectorL2 s hF a)

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
