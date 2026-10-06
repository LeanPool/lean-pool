/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.AdaptedCellFoundations
public import LeanPool.HighContrastHomogenization.Entry.Response.Cutoff.ResponseTransferFromCutoffBound
public import LeanPool.HighContrastHomogenization.Entry.Response.Kernel.BesovScaleSummationToolkit
public import LeanPool.HighContrastHomogenization.Entry.Response.Rows.TerminalEnergyMeasurability

/-!
# High-contrast homogenization: Entry.Response.Direct.TriadicRefinementIncrement

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Refining the cutoff's oscillation split by one triadic generation

A flat average, over the depth-`m` triadic subcells of the terminal cell, of a weight `c·w` against
the cell average of an integrable function, is unchanged when each depth-`m` cell is refined into
its own triadic subcells one generation further; this is the bookkeeping that the descendant
telescoping of `p.response.transfer` sums generation by generation. Exact partition averaging turns
the `(φ-1)`-weighted average of a density `D` on a cell into the normalized average, over its own
triadic subcells, of the per-subcell means of `φ-1` and of `D`, so replacing each subcell's mean of
`φ-1` by that of the coarser cell containing it leaves only a `3^{-n}` remainder. Because a response
cutoff of scale `3^t` is Lipschitz with constant `32 d^2 Θ 3^{-t}`, the increment of the cutoff's
cell average between a cell and the coarser cell of the previous generation containing it is bounded
by that constant times the finer cell's diameter, read off at the depth `H + n + 1` the descendant
sum of `p.response.transfer` actually uses.
-/

section
/-!
## Refining a weighted flat cell average by one triadic generation

The descendant telescoping of `p.response.transfer` compares the cutoff cell averages at two
consecutive generations.  The bookkeeping it needs is that a flat average over the depth-`m`
subcells of the terminal cell, of a weight `c w` against the cell average of a fixed integrable
function `f`, is unchanged when each depth-`m` cell is refined into its `3 ^ d` children: the
weight is then read at the parent index.

```
avg_{w ∈ box m}  c w · ⨍_{V^m_w} f  =  avg_{W ∈ box (m+1)}  c (parent W) · ⨍_{V^{m+1}_W} f.
```

The proof uses only the landed partition of the centred terminal cell
(`avsum_volumeAverage_eq`), applied once at depth `m` and once at depth `m + 1`.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory Geometry

noncomputable section

/-- **The parent of a cell of the triadic box lies in the coarser box.**  If `W` indexes a cell
of depth `m + 1` inside the terminal cell, its parent index of depth `m` indexes a cell of the
same terminal cell. -/
theorem parentIndex_mem_triadicIndexBox {d m : ℕ} {W : Fin d → ℤ}
    (hW : W ∈ triadicIndexBox d (m + 1)) :
    Transport.gridParent W ∈ triadicIndexBox d m := by
  rw [triadicIndexBox, Fintype.mem_piFinset] at hW ⊢
  intro i
  have hWi := hW i
  rw [Finset.mem_Icc] at hWi ⊢
  simp only [Transport.gridParent]
  obtain ⟨k, hk⟩ : Odd ((3 : ℕ) ^ m) := Odd.pow (by decide)
  have hkdiv : ((3 : ℕ) ^ m - 1) / 2 = k := by
    have hm1 : (3 : ℕ) ^ m - 1 = 2 * k := by omega
    rw [hm1, Nat.mul_div_cancel_left k (by norm_num : 0 < 2)]
  have hk1 : (3 : ℕ) ^ (m + 1) = 2 * (3 * k + 1) + 1 := by
    rw [pow_succ, hk]; ring
  have hk1div : ((3 : ℕ) ^ (m + 1) - 1) / 2 = 3 * k + 1 := by
    have hm1 : (3 : ℕ) ^ (m + 1) - 1 = 2 * (3 * k + 1) := by omega
    rw [hm1, Nat.mul_div_cancel_left (3 * k + 1) (by norm_num : 0 < 2)]
  have hbm : ((((3 : ℕ) ^ m - 1) / 2 : ℕ) : ℤ) = (k : ℤ) := by exact_mod_cast hkdiv
  have hbm1 : ((((3 : ℕ) ^ (m + 1) - 1) / 2 : ℕ) : ℤ) = ((3 * k + 1 : ℕ) : ℤ) := by
    exact_mod_cast hk1div
  rw [hbm1] at hWi
  rw [hbm] at ⊢
  constructor
  · rw [Int.le_ediv_iff_mul_le (by norm_num : (0 : ℤ) < 3)]
    omega
  · rw [Int.ediv_le_iff_le_mul (by norm_num : (0 : ℤ) < 3)]
    omega

/-- **A triadic cell sits in its parent.**  The aligned adapted cell of generation `k` at index
`W` is contained in the aligned adapted cell of generation `k + 1` at the parent index. -/
theorem adaptedCellAtCenter_subset_parent {d : ℕ} (q : Mat d) (k : ℤ) (W : Fin d → ℤ) :
    adaptedCellAtCenter q k W ⊆ adaptedCellAtCenter q (k + 1) (Transport.gridParent W) := by
  simp only [Geometry.adaptedCellAtCenter_eq_affine_standardCell]
  exact Set.image_mono (Transport.standardCell_subset_parent k W)

/-- **The children of one triadic cell carry its cell average.**  Summing the cell averages of
`f` over the depth-`(m+1)` cells whose parent index is `w`, normalised by the number of
depth-`(m+1)` cells, gives the cell average of `f` over the depth-`m` cell at `w`, normalised by
the number of depth-`m` cells. -/
theorem avsum_fiber_volumeAverage_eq {d : ℕ} [NeZero d] {q : Mat d} (hq : IsUnit q)
    (t : ℤ) (m : ℕ) (w : Fin d → ℤ) (hw : w ∈ triadicIndexBox d m) {f : Vec d → ℝ}
    (hf : IntegrableOn f (HighContrast.adaptedCell q t)) :
    ((triadicIndexBox d (m + 1)).card : ℝ)⁻¹ *
        ∑ W ∈ (triadicIndexBox d (m + 1)).filter
            (fun W => Transport.gridParent W = w),
          volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f
      = ((triadicIndexBox d m).card : ℝ)⁻¹ *
          volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) w) f := by
  classical
  set g : Vec d → ℝ := Set.indicator (adaptedCellAtCenter q (t - (m : ℤ)) w) f with hgdef
  have hVmeas : MeasurableSet (adaptedCellAtCenter q (t - (m : ℤ)) w) :=
    (isOpen_adaptedCellAtCenter_of_isUnit hq (t - (m : ℤ)) w).measurableSet
  have hg : IntegrableOn g (HighContrast.adaptedCell q t) := by
    rw [hgdef]
    exact hf.indicator hVmeas
  have hpart_m := avsum_volumeAverage_eq q hq t m hg
  have hpart_m1 := avsum_volumeAverage_eq q hq t (m + 1) hg
  have hpart := hpart_m.trans hpart_m1.symm
  have hzero_V : ∀ v : Fin d → ℤ, v ≠ w →
      volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) v) g = 0 := by
    intro v hv
    rw [volumeAverage]
    have hzero : ∫ x in adaptedCellAtCenter q (t - (m : ℤ)) v, g x = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      rw [hgdef]
      exact Set.indicator_of_notMem
        (Set.disjoint_left.mp (Geometry.adaptedCellAtCenter_disjoint_of_ne hq (t - (m : ℤ)) hv) hx) f
    rw [hzero, mul_zero]
  have hcollapse_m : (∑ v ∈ triadicIndexBox d m,
        volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) v) g)
      = volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) w) f := by
    calc ∑ v ∈ triadicIndexBox d m, volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) v) g
        = volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) w) g :=
          Finset.sum_eq_single (s := triadicIndexBox d m)
            (f := fun v => volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) v) g)
            w (fun v _ hvne => hzero_V v hvne) (fun hnot => absurd hw hnot)
      _ = volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) w) f := by
          rw [volumeAverage, volumeAverage]
          congr 1
          apply setIntegral_congr_fun hVmeas
          intro x hx
          rw [hgdef]
          exact Set.indicator_of_mem hx f
  have heq_W : ∀ W ∈ triadicIndexBox d (m + 1), Transport.gridParent W = w →
      volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) g
        = volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f := by
    intro W _ hp
    rw [volumeAverage, volumeAverage]
    congr 1
    apply setIntegral_congr_fun (isOpen_adaptedCellAtCenter_of_isUnit hq _ W).measurableSet
    intro x hx
    rw [hgdef]
    refine Set.indicator_of_mem ?_ f
    have hsub : adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W ⊆
        adaptedCellAtCenter q (t - (m : ℤ)) w := by
      have h := adaptedCellAtCenter_subset_parent q (t - ((m + 1 : ℕ) : ℤ)) W
      rw [hp] at h
      rw [show t - ((m + 1 : ℕ) : ℤ) + 1 = t - (m : ℤ) by push_cast; ring] at h
      exact h
    exact hsub hx
  have hzero_W : ∀ W ∈ triadicIndexBox d (m + 1), Transport.gridParent W ≠ w →
      volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) g = 0 := by
    intro W hW hne
    rw [volumeAverage]
    have hzero : ∫ x in adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W, g x = 0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro x hx
      rw [hgdef]
      refine Set.indicator_of_notMem ?_ f
      have hsub : adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W ⊆
          adaptedCellAtCenter q (t - (m : ℤ)) (Transport.gridParent W) := by
        have h := adaptedCellAtCenter_subset_parent q (t - ((m + 1 : ℕ) : ℤ)) W
        rw [show t - ((m + 1 : ℕ) : ℤ) + 1 = t - (m : ℤ) by push_cast; ring] at h
        exact h
      exact Set.disjoint_left.mp
        (Geometry.adaptedCellAtCenter_disjoint_of_ne hq (t - (m : ℤ)) hne) (hsub hx)
    rw [hzero, mul_zero]
  have hfilter := Finset.sum_filter_of_ne
      (s := triadicIndexBox d (m + 1))
      (p := fun W => Transport.gridParent W = w)
      (f := fun W => volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) g)
      (fun W hW hne => by
        by_contra hp
        exact hne (hzero_W W hW hp))
  have hcollapse_m1 : (∑ W ∈ triadicIndexBox d (m + 1),
        volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) g)
      = ∑ W ∈ (triadicIndexBox d (m + 1)).filter (fun W => Transport.gridParent W = w),
          volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f := by
    calc ∑ W ∈ triadicIndexBox d (m + 1),
          volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) g
        = ∑ W ∈ (triadicIndexBox d (m + 1)).filter (fun W => Transport.gridParent W = w),
            volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) g := hfilter.symm
      _ = ∑ W ∈ (triadicIndexBox d (m + 1)).filter (fun W => Transport.gridParent W = w),
            volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f := by
          refine Finset.sum_congr rfl ?_
          intro W hW
          exact heq_W W (Finset.mem_filter.mp hW).1 (Finset.mem_filter.mp hW).2
  calc ((triadicIndexBox d (m + 1)).card : ℝ)⁻¹ *
        (∑ W ∈ (triadicIndexBox d (m + 1)).filter (fun W => Transport.gridParent W = w),
          volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f)
      = ((triadicIndexBox d (m + 1)).card : ℝ)⁻¹ *
          (∑ W ∈ triadicIndexBox d (m + 1),
            volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) g) := by
        rw [← hcollapse_m1]
    _ = ((triadicIndexBox d m).card : ℝ)⁻¹ *
          (∑ v ∈ triadicIndexBox d m,
            volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) v) g) := hpart.symm
    _ = ((triadicIndexBox d m).card : ℝ)⁻¹ *
          volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) w) f := by rw [hcollapse_m]

/-- **Refining a weighted flat cell average by one generation.**  The flat average over the
depth-`m` subcells of a weight against the cell average of `f` equals the flat average over the
depth-`(m+1)` subcells of the same weight read at the parent index. -/
theorem avsum_weighted_volumeAverage_succ_eq {d : ℕ} [NeZero d] {q : Mat d} (hq : IsUnit q)
    (t : ℤ) (m : ℕ) (c : (Fin d → ℤ) → ℝ) {f : Vec d → ℝ}
    (hf : IntegrableOn f (HighContrast.adaptedCell q t)) :
    ((triadicIndexBox d m).card : ℝ)⁻¹ * ∑ w ∈ triadicIndexBox d m,
        c w * volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) w) f
      = ((triadicIndexBox d (m + 1)).card : ℝ)⁻¹ * ∑ W ∈ triadicIndexBox d (m + 1),
          c (Transport.gridParent W)
            * volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f := by
  classical
  set A : ℝ := ((triadicIndexBox d m).card : ℝ)⁻¹ with hA
  set B : ℝ := ((triadicIndexBox d (m + 1)).card : ℝ)⁻¹ with hB
  have hfiber : (∑ w ∈ triadicIndexBox d m,
        ∑ W ∈ (triadicIndexBox d (m + 1)).filter (fun W => Transport.gridParent W = w),
          c (Transport.gridParent W)
            * volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f)
      = ∑ W ∈ triadicIndexBox d (m + 1),
          c (Transport.gridParent W)
            * volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f :=
    Finset.sum_fiberwise_of_maps_to
      (s := triadicIndexBox d (m + 1)) (t := triadicIndexBox d m)
      (g := Transport.gridParent)
      (fun W hW => parentIndex_mem_triadicIndexBox hW)
      (fun W => c (Transport.gridParent W)
        * volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f)
  have hstep3 : ∀ w ∈ triadicIndexBox d m,
      B * (∑ W ∈ (triadicIndexBox d (m + 1)).filter (fun W => Transport.gridParent W = w),
            volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f)
        = A * volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) w) f := by
    intro w hw
    have h := avsum_fiber_volumeAverage_eq (q := q) hq t m w hw (f := f) hf
    rw [hB, hA]
    exact h
  have hfilter_eq : ∀ w ∈ triadicIndexBox d m,
      (∑ W ∈ (triadicIndexBox d (m + 1)).filter (fun W => Transport.gridParent W = w),
          c (Transport.gridParent W)
            * volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f)
        = c w * (∑ W ∈ (triadicIndexBox d (m + 1)).filter
              (fun W => Transport.gridParent W = w),
            volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f) := by
    intro w _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro W hW
    rw [(Finset.mem_filter.mp hW).2]
  calc A * ∑ w ∈ triadicIndexBox d m,
        c w * volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) w) f
      = ∑ w ∈ triadicIndexBox d m,
          c w * (A * volumeAverage (adaptedCellAtCenter q (t - (m : ℤ)) w) f) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun w _ => by ring)
    _ = ∑ w ∈ triadicIndexBox d m,
          c w * (B * (∑ W ∈ (triadicIndexBox d (m + 1)).filter
                (fun W => Transport.gridParent W = w),
              volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f)) := by
        refine Finset.sum_congr rfl ?_
        intro w hw
        rw [← hstep3 w hw]
    _ = B * ∑ w ∈ triadicIndexBox d m,
          c w * (∑ W ∈ (triadicIndexBox d (m + 1)).filter
                (fun W => Transport.gridParent W = w),
              volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun w _ => by ring)
    _ = B * ∑ w ∈ triadicIndexBox d m,
          ∑ W ∈ (triadicIndexBox d (m + 1)).filter (fun W => Transport.gridParent W = w),
            c (Transport.gridParent W)
              * volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f := by
        congr 1
        refine Finset.sum_congr rfl ?_
        intro w hw
        rw [← hfilter_eq w hw]
    _ = B * ∑ W ∈ triadicIndexBox d (m + 1),
          c (Transport.gridParent W)
            * volumeAverage (adaptedCellAtCenter q (t - ((m + 1 : ℕ) : ℤ)) W) f := by
        rw [hfiber]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The cutoff fluctuation splits into cell means plus a `3^{-n}` remainder

The scale gain of the cutoff estimate of `p.response.transfer`.  Exact partition averaging over the
generation-`(t - n)` triadic subdivision writes the `(φ - 1)`-weighted average of a density `D` as
the normalized average of the per-cell weighted averages of `φ - 1` and `D`.  On each descendant
cell `V`, replacing `φ - 1` by its own `V`-mean costs only the oscillation of `φ` on `V`, which is
at most `32 d² responseCutoffProfileConst 3^{-n}`.  Summing back gives the stated remainder bound;
the remaining cell-mean term is the one cancelled in expectation by stationarity.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- Across a descendant adapted cell `adaptedCellAtCenter qq (t - n) w`, a cutoff `φ` of the
response
class `IsResponseCutoff qq t φ` deviates from its cell mean by at most
`32 d² responseCutoffProfileConst 3^{-n}`.  This is the oscillation input to the scale gain of the
cutoff estimate of `p.response.transfer`. -/
theorem abs_sub_volumeAverage_le_of_isResponseCutoff {d : ℕ} {qq : Mat d} (hq : IsUnit qq)
    {t : ℤ} {φ : Vec d → ℝ} (h : IsResponseCutoff qq t φ) (n : ℕ) (w : Fin d → ℤ)
    (hvol : (volume (adaptedCellAtCenter qq (t - (n : ℤ)) w)).toReal ≠ 0)
    (hfin : volume (adaptedCellAtCenter qq (t - (n : ℤ)) w) ≠ ⊤)
    (hint : IntegrableOn φ (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    {x : Vec d} (hx : x ∈ adaptedCellAtCenter qq (t - (n : ℤ)) w) :
    |φ x - volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) φ|
      ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ)) := by
  set V : Set (Vec d) := adaptedCellAtCenter qq (t - (n : ℤ)) w with hV
  set K : ℝ := 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ)) with hK
  have hVmeas : MeasurableSet V :=
    (isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w).measurableSet
  have hvolV : (volume V).toReal ≠ 0 := by rw [hV]; exact hvol
  have : IsFiniteMeasure (volumeMeasureOn V) := by
    rw [volumeMeasureOn, hV]
    exact isFiniteMeasure_restrict.mpr hfin
  have hupper : volumeAverage V φ ≤ φ x + K := by
    refine volumeAverage_le_of_le_on hVmeas hint hvolV ?_
    intro y hy
    have hb := abs_sub_le_of_mem_adaptedCellAtCenter hq h n w hy hx
    have h2 : φ y - φ x ≤ K := (abs_le.mp hb).2
    linarith only [h2]
  have hlower : φ x - K ≤ volumeAverage V φ := by
    have hle : ∀ y ∈ V, φ x - K ≤ φ y := by
      intro y hy
      have hb := abs_sub_le_of_mem_adaptedCellAtCenter hq h n w hy hx
      have h1 : -K ≤ φ y - φ x := (abs_le.mp hb).1
      linarith only [h1]
    have hcomp := volumeAverage_le_volumeAverage_of_le_on hVmeas
      (integrable_const (φ x - K)) hint hle
    rwa [volumeAverage_const hvolV] at hcomp
  exact abs_le.mpr ⟨by linarith only [hupper], by linarith only [hlower]⟩

/-- On a single descendant cell, the average of `(φ - 1) D` minus the product of the cell means of
`φ - 1` and `D` is the cell average of `(φ - (φ)_V) D`.  This is the exact per-cell identity
behind the scale gain of `p.response.transfer`. -/
private theorem volumeAverage_mul_sub_mul_volumeAverage_eq
    {d : ℕ} {qq : Mat d} (t : ℤ) (n : ℕ) (w : Fin d → ℤ) {φ D : Vec d → ℝ}
    (hvol : (volume (adaptedCellAtCenter qq (t - (n : ℤ)) w)).toReal ≠ 0)
    (hfin : volume (adaptedCellAtCenter qq (t - (n : ℤ)) w) ≠ ⊤)
    (hDat : IntegrableOn D (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    (hφat : IntegrableOn φ (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    (hφDat : IntegrableOn (fun x => (φ x - 1) * D x) (adaptedCellAtCenter qq (t - (n : ℤ)) w)) :
    volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) (fun x => (φ x - 1) * D x)
      - (volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) (fun x => φ x - 1))
        * volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) D
      = volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w)
          (fun x => (φ x - volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) φ) * D x) := by
  have : IsFiniteMeasure (volumeMeasureOn (adaptedCellAtCenter qq (t - (n : ℤ)) w)) := by
    rw [volumeMeasureOn]
    exact isFiniteMeasure_restrict.mpr hfin
  set mw : ℝ := volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) φ with hmw
  have h1 : IntegrableOn (fun _ : Vec d => (1 : ℝ)) (adaptedCellAtCenter qq (t - (n : ℤ)) w) :=
    integrable_const 1
  have hc : volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) (fun x => φ x - 1) = mw - 1 := by
    rw [show (fun x : Vec d => φ x - 1) = φ - fun _ => (1 : ℝ) by funext x; simp]
    rw [volumeAverage_sub hφat h1, volumeAverage_const hvol, ← hmw]
  have hconst : IntegrableOn
      (fun x => (mw - 1) * D x) (adaptedCellAtCenter qq (t - (n : ℤ)) w) := hDat.const_mul _
  have hsubeq : volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) (fun x => (mw - 1) * D x)
      = (mw - 1) * volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) D :=
    volumeAverage_smul _ (mw - 1) D
  have hfun : ((fun x : Vec d => (φ x - 1) * D x) - fun x => (mw - 1) * D x)
      = fun x => (φ x - mw) * D x := by
    funext x
    change (φ x - 1) * D x - (mw - 1) * D x = (φ x - mw) * D x
    ring
  rw [hc, ← hsubeq, ← volumeAverage_sub hφDat hconst, hfun]

/-- On a single descendant cell, the cell average of `(φ - (φ)_V) D` is bounded by
`32 d² responseCutoffProfileConst 3^{-n}` times the cell average of `D`, using the oscillation of
`φ` on the cell and the nonnegativity of `D`. -/
private theorem abs_volumeAverage_sub_cellAverage_mul_le
    {d : ℕ} {qq : Mat d} (hq : IsUnit qq) {t : ℤ} {φ : Vec d → ℝ}
    (hφ : IsResponseCutoff qq t φ) (n : ℕ) (w : Fin d → ℤ) {D : Vec d → ℝ}
    (hD : ∀ x, 0 ≤ D x)
    (hvol : (volume (adaptedCellAtCenter qq (t - (n : ℤ)) w)).toReal ≠ 0)
    (hfin : volume (adaptedCellAtCenter qq (t - (n : ℤ)) w) ≠ ⊤)
    (hDat : IntegrableOn D (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    (hφat : IntegrableOn φ (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    (hφDat : IntegrableOn (fun x => (φ x - 1) * D x) (adaptedCellAtCenter qq (t - (n : ℤ)) w)) :
    |volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w)
        (fun x => (φ x - volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) φ) * D x)|
      ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ))
          * volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) D := by
  set Vw : Set (Vec d) := adaptedCellAtCenter qq (t - (n : ℤ)) w with hVw
  set K : ℝ := 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ)) with hK
  set mw : ℝ := volumeAverage Vw φ with hmw
  have hVmeas : MeasurableSet Vw :=
    (isOpen_adaptedCellAtCenter_of_isUnit hq (t - (n : ℤ)) w).measurableSet
  have : IsFiniteMeasure (volumeMeasureOn Vw) := by
    rw [volumeMeasureOn, hVw]
    exact isFiniteMeasure_restrict.mpr hfin
  have hvolV : (volume Vw).toReal ≠ 0 := by rw [hVw]; exact hvol
  have hgint : IntegrableOn (fun x => (φ x - mw) * D x) Vw := by
    refine MeasureTheory.IntegrableOn.congr_fun
      (hφDat.sub (hDat.const_mul (mw - 1))) ?_ hVmeas
    intro x _
    change (φ x - 1) * D x - (mw - 1) * D x = (φ x - mw) * D x
    ring
  have hKint : IntegrableOn (fun x => K * D x) Vw := hDat.const_mul K
  have hnKint : IntegrableOn (fun x => -K * D x) Vw := hDat.const_mul (-K)
  have hbound : ∀ x ∈ Vw, |φ x - mw| ≤ K := by
    intro x hx
    have h := abs_sub_volumeAverage_le_of_isResponseCutoff hq hφ n w hvol hfin hφat hx
    have hmw' : mw = volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) φ := by rw [hmw, hVw]
    rw [hmw', hK]
    exact h
  have hup : ∀ x ∈ Vw, (φ x - mw) * D x ≤ K * D x := by
    intro x hx
    exact mul_le_mul_of_nonneg_right (abs_le.mp (hbound x hx)).2 (hD x)
  have hlo : ∀ x ∈ Vw, -K * D x ≤ (φ x - mw) * D x := by
    intro x hx
    exact mul_le_mul_of_nonneg_right (abs_le.mp (hbound x hx)).1 (hD x)
  have hUb : volumeAverage Vw (fun x => (φ x - mw) * D x)
      ≤ volumeAverage Vw (fun x => K * D x) :=
    volumeAverage_le_volumeAverage_of_le_on hVmeas hgint hKint hup
  have hLb : volumeAverage Vw (fun x => -K * D x)
      ≤ volumeAverage Vw (fun x => (φ x - mw) * D x) :=
    volumeAverage_le_volumeAverage_of_le_on hVmeas hnKint hgint hlo
  have hKavg : volumeAverage Vw (fun x => K * D x) = K * volumeAverage Vw D :=
    volumeAverage_smul Vw K D
  have hnKavg : volumeAverage Vw (fun x => -K * D x) = -(K * volumeAverage Vw D) := by
    rw [show (fun x : Vec d => -K * D x) = (-K) • D by funext x; simp]
    rw [volumeAverage_smul, neg_mul]
  rw [hKavg] at hUb
  rw [hnKavg] at hLb
  exact abs_le.mpr ⟨hLb, hUb⟩

/-- The exact partition average of the `(φ - 1)`-weighted density over the adapted parent cell
differs from the normalized sum of the products of the per-cell means of `φ - 1` and of `D` by at
most `32 d² responseCutoffProfileConst 3^{-n}` times the parent average of `D`.  This is the scale
gain of the cutoff estimate of `p.response.transfer`. -/
theorem abs_volumeAverage_sub_one_mul_sub_avsum_le {d : ℕ} [NeZero d] {qq : Mat d}
    (hq : IsUnit qq) (t : ℤ) (n : ℕ) {φ : Vec d → ℝ} (hφ : IsResponseCutoff qq t φ)
    {D : Vec d → ℝ} (hD : ∀ x, 0 ≤ D x)
    (hDint : IntegrableOn D (HighContrast.adaptedCell qq t))
    (hφDint : IntegrableOn (fun x => (φ x - 1) * D x) (HighContrast.adaptedCell qq t))
    (hDat : ∀ w ∈ triadicIndexBox d n, IntegrableOn D (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    (hφat : ∀ w ∈ triadicIndexBox d n, IntegrableOn φ (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    (hφDat : ∀ w ∈ triadicIndexBox d n,
      IntegrableOn (fun x => (φ x - 1) * D x) (adaptedCellAtCenter qq (t - (n : ℤ)) w))
    (hvol : ∀ w ∈ triadicIndexBox d n,
      (volume (adaptedCellAtCenter qq (t - (n : ℤ)) w)).toReal ≠ 0)
    (hfin : ∀ w ∈ triadicIndexBox d n, volume (adaptedCellAtCenter qq (t - (n : ℤ)) w) ≠ ⊤) :
    |volumeAverage (HighContrast.adaptedCell qq t) (fun x => (φ x - 1) * D x)
        - (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n,
            (volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) (fun x => φ x - 1)) *
              volumeAverage (adaptedCellAtCenter qq (t - (n : ℤ)) w) D|
      ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ))
          * volumeAverage (HighContrast.adaptedCell qq t) D := by
  let V : (Fin d → ℤ) → Set (Vec d) := fun w => adaptedCellAtCenter qq (t - (n : ℤ)) w
  let c : (Fin d → ℤ) → ℝ := fun w => volumeAverage (V w) (fun x => φ x - 1)
  let dbar : (Fin d → ℤ) → ℝ := fun w => volumeAverage (V w) D
  let K : ℝ := 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(n : ℝ))
  let f : Vec d → ℝ := fun x => (φ x - 1) * D x
  change |volumeAverage (HighContrast.adaptedCell qq t) f
      - (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n, c w * dbar w|
    ≤ K * volumeAverage (HighContrast.adaptedCell qq t) D
  have hpartf : (((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, volumeAverage (V w) f
      = volumeAverage (HighContrast.adaptedCell qq t) f :=
    avsum_volumeAverage_eq (d := d) qq hq t n (f := f) hφDint
  have hpartD : (((triadicIndexBox d n).card : ℝ))⁻¹ *
      ∑ w ∈ triadicIndexBox d n, dbar w = volumeAverage (HighContrast.adaptedCell qq t) D :=
    avsum_volumeAverage_eq (d := d) qq hq t n (f := D) hDint
  have hcell : ∀ w ∈ triadicIndexBox d n,
      volumeAverage (V w) f - c w * dbar w
        = volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * D x) := by
    intro w hw
    exact volumeAverage_mul_sub_mul_volumeAverage_eq t n w (hvol w hw) (hfin w hw)
      (hDat w hw) (hφat w hw) (hφDat w hw)
  have hboundw : ∀ w ∈ triadicIndexBox d n,
      |volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * D x)| ≤ K * dbar w := by
    intro w hw
    exact abs_volumeAverage_sub_cellAverage_mul_le (d := d) (qq := qq) hq hφ n w hD
      (hvol w hw) (hfin w hw) (hDat w hw) (hφat w hw) (hφDat w hw)
  have hsumcell : (∑ w ∈ triadicIndexBox d n, (volumeAverage (V w) f - c w * dbar w))
      = ∑ w ∈ triadicIndexBox d n,
          volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * D x) :=
    Finset.sum_congr rfl (fun w hw => hcell w hw)
  have hsumabs : |∑ w ∈ triadicIndexBox d n,
        volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * D x)|
      ≤ ∑ w ∈ triadicIndexBox d n, K * dbar w := by
    calc |∑ w ∈ triadicIndexBox d n,
            volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * D x)|
        ≤ ∑ w ∈ triadicIndexBox d n,
            |volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * D x)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ w ∈ triadicIndexBox d n, K * dbar w :=
          Finset.sum_le_sum (fun w hw => hboundw w hw)
  calc |volumeAverage (HighContrast.adaptedCell qq t) f
        - (((triadicIndexBox d n).card : ℝ))⁻¹ * ∑ w ∈ triadicIndexBox d n, c w * dbar w|
      = |(((triadicIndexBox d n).card : ℝ))⁻¹ *
          (∑ w ∈ triadicIndexBox d n, volumeAverage (V w) f
            - ∑ w ∈ triadicIndexBox d n, c w * dbar w)| := by
            rw [← hpartf, ← mul_sub]
      _ = |(((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, (volumeAverage (V w) f - c w * dbar w)| := by
            rw [← Finset.sum_sub_distrib]
      _ = |(((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n,
            volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * D x)| := by
            rw [hsumcell]
      _ = (((triadicIndexBox d n).card : ℝ))⁻¹ *
          |∑ w ∈ triadicIndexBox d n,
            volumeAverage (V w) (fun x => (φ x - volumeAverage (V w) φ) * D x)| := by
            rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))]
      _ ≤ (((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, K * dbar w :=
            mul_le_mul_of_nonneg_left hsumabs (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ = K * ((((triadicIndexBox d n).card : ℝ))⁻¹ *
          ∑ w ∈ triadicIndexBox d n, dbar w) := by
            rw [← Finset.mul_sum (triadicIndexBox d n) dbar K]
            ring
      _ = K * volumeAverage (HighContrast.adaptedCell qq t) D := by rw [hpartD]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The cutoff cell averages of a cell and of a coarser cell containing it

The descendant telescoping of `p.response.transfer` needs, at the passage from generation `t - m`
to generation `t - m - 1`, the increment of the cutoff cell averages over a subcell `W` of the
generation-`(t - m)` aligned cell.  Because the cutoff class `IsResponseCutoff qq t φ` carries
derivatives at the scale `3^t`, `φ` varies over the cell by at most `32 d² Θ 3^{-m}`; the two
averages of `φ` over `W` and over the cell therefore differ by at most that oscillation.  This is
the weight that makes the descendant sum converge with the printed weights `3^{3(k-s)/2}`.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The cutoff cell average of a subcell differs from that of the cell by the cutoff
oscillation.**  If `V` is the aligned adapted cell of generation `t - m` at the index `v` and
`W ⊆ V` has positive finite volume, the cutoff cell averages of `φ - 1` over `W` and over `V`
differ by at most `32 d² Θ 3^{-m}`.  This is the weight of the generation-`(t-m-1)` term of the
descendant sum of `p.response.transfer`. -/
theorem abs_volumeAverage_sub_one_sub_volumeAverage_sub_one_le {d : ℕ} {qq : Mat d}
    (hq : IsUnit qq) {t : ℤ} {φ : Vec d → ℝ} (hφ : IsResponseCutoff qq t φ) (m : ℕ)
    (v : Fin d → ℤ) {W : Set (Vec d)}
    (hsub : W ⊆ adaptedCellAtCenter qq (t - (m : ℤ)) v)
    (hvol : (volume (adaptedCellAtCenter qq (t - (m : ℤ)) v)).toReal ≠ 0)
    (hfin : volume (adaptedCellAtCenter qq (t - (m : ℤ)) v) ≠ ⊤)
    (hint : IntegrableOn φ (adaptedCellAtCenter qq (t - (m : ℤ)) v))
    (hWvol : (volume W).toReal ≠ 0) (hWfin : volume W ≠ ⊤)
    (hWint : IntegrableOn φ W) :
    |volumeAverage W (fun x => φ x - 1)
        - volumeAverage (adaptedCellAtCenter qq (t - (m : ℤ)) v) (fun x => φ x - 1)|
      ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(m : ℝ)) := by
  set V : Set (Vec d) := adaptedCellAtCenter qq (t - (m : ℤ)) v with hV
  set K : ℝ := 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(m : ℝ)) with hK
  have : IsFiniteMeasure (volumeMeasureOn W) := by
    rw [volumeMeasureOn]
    exact isFiniteMeasure_restrict.mpr hWfin
  have : IsFiniteMeasure (volumeMeasureOn V) := by
    rw [volumeMeasureOn, hV]
    exact isFiniteMeasure_restrict.mpr hfin
  have hvolV : (volume V).toReal ≠ 0 := by rw [hV]; exact hvol
  have hintV : IntegrableOn φ V := by rw [hV]; exact hint
  have h1W : IntegrableOn (fun _ : Vec d => (1 : ℝ)) W := integrable_const 1
  have h1V : IntegrableOn (fun _ : Vec d => (1 : ℝ)) V := integrable_const 1
  have hWpos : 0 < (volume W).toReal :=
    lt_of_le_of_ne ENNReal.toReal_nonneg (Ne.symm hWvol)
  have hWsub : volumeAverage W (fun x => φ x - 1) = volumeAverage W φ - 1 := by
    rw [show (fun x : Vec d => φ x - 1) = φ - fun _ => (1 : ℝ) by funext x; simp]
    rw [volumeAverage_sub hWint h1W, volumeAverage_const hWvol]
  have hVsub : volumeAverage V (fun x => φ x - 1) = volumeAverage V φ - 1 := by
    rw [show (fun x : Vec d => φ x - 1) = φ - fun _ => (1 : ℝ) by funext x; simp]
    rw [volumeAverage_sub hintV h1V, volumeAverage_const hvolV]
  have hWc : volumeAverage W (fun x => φ x - volumeAverage V φ)
      = volumeAverage W φ - volumeAverage V φ := by
    rw [show (fun x : Vec d => φ x - volumeAverage V φ)
        = φ - fun _ => volumeAverage V φ by funext x; simp]
    rw [volumeAverage_sub hWint (integrable_const (volumeAverage V φ)), volumeAverage_const hWvol]
  have hdiff : volumeAverage W (fun x => φ x - 1) - volumeAverage V (fun x => φ x - 1)
      = volumeAverage W (fun x => φ x - volumeAverage V φ) := by
    rw [hWsub, hVsub, hWc]
    ring
  have hbound : ∀ x ∈ W, |φ x - volumeAverage V φ| ≤ K := by
    intro x hx
    have hxV : x ∈ adaptedCellAtCenter qq (t - (m : ℤ)) v := hsub hx
    have h := abs_sub_volumeAverage_le_of_isResponseCutoff hq hφ m v hvol hfin hint hxV
    rw [hK, hV]
    exact h
  have hInt : |∫ x in W, (φ x - volumeAverage V φ) ∂volume| ≤ K * (volume W).toReal := by
    have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := volume)
      (s := W) (f := fun x => φ x - volumeAverage V φ) (C := K)
      (lt_top_iff_ne_top.mpr hWfin) (fun x hx => by
        rw [Real.norm_eq_abs]
        exact hbound x hx)
    simpa only [Real.norm_eq_abs, MeasureTheory.measureReal_def] using h
  calc
    |volumeAverage W (fun x => φ x - 1) - volumeAverage V (fun x => φ x - 1)|
        = |volumeAverage W (fun x => φ x - volumeAverage V φ)| := by rw [hdiff]
    _ = |(volume W).toReal⁻¹ * ∫ x in W, (φ x - volumeAverage V φ) ∂volume| := by
          rw [volumeAverage]
    _ = (volume W).toReal⁻¹ * |∫ x in W, (φ x - volumeAverage V φ) ∂volume| := by
          rw [abs_mul, abs_of_pos (inv_pos.mpr hWpos)]
    _ ≤ (volume W).toReal⁻¹ * (K * (volume W).toReal) :=
          mul_le_mul_of_nonneg_left hInt (inv_pos.mpr hWpos).le
    _ = K := by
          rw [mul_comm K (volume W).toReal, ← mul_assoc, inv_mul_cancel₀ hWvol, one_mul]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## The descendant weight of the cutoff-mean row at the carriers

The descendant sum of `p.response.transfer` runs over the generations below the scale-`s` cells,
i.e. over the depths `H + n + 1` of the terminal cell.  Its weight at depth `H + n + 1` is the
increment of the cutoff cell averages between a cell and the cell of the previous generation
containing it.  The cutoff class bounds that increment by `32 d² Θ 3^{-(H+n)}`, which is the shape
`K · 3^{-n}` the descendant row consumes, with `K = 32 d² Θ 3^{-H}` carrying the printed factor
`3^{-H}`.
-/

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory

noncomputable section

/-- **The descendant weight of the cutoff-mean row.**  At the generation `t - (H + n + 1)` the
increment of the cutoff cell averages between a cell and its parent is at most
`(32 d² Θ 3^{-H}) · 3^{-n}`.  This is the weight of the depth-`n` term of the descendant sum of
`p.response.transfer`. -/
theorem abs_cutoff_weight_increment_le {d : ℕ} [NeZero d] {qq : Mat d} (hq : IsUnit qq) {t : ℤ}
    {φ : Vec d → ℝ} (hφ : IsResponseCutoff qq t φ) (H n : ℕ) (W : Fin d → ℤ) :
    |volumeAverage (adaptedCellAtCenter qq (t - ((H + n + 1 : ℕ) : ℤ)) W) (fun x => φ x - 1)
        - volumeAverage (adaptedCellAtCenter qq (t - ((H + n : ℕ) : ℤ)) (Transport.gridParent W))
            (fun x => φ x - 1)|
      ≤ (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
          * (3 : ℝ) ^ (-(n : ℝ)) := by
  have hsub : adaptedCellAtCenter qq (t - ((H + n + 1 : ℕ) : ℤ)) W ⊆
      adaptedCellAtCenter qq (t - ((H + n : ℕ) : ℤ)) (Transport.gridParent W) := by
    have h := adaptedCellAtCenter_subset_parent qq (t - ((H + n + 1 : ℕ) : ℤ)) W
    simpa only [show t - ((H + n + 1 : ℕ) : ℤ) + 1 = t - ((H + n : ℕ) : ℤ) by
      push_cast; ring] using h
  have hPpos :
      0 < (volume (adaptedCellAtCenter qq (t - ((H + n : ℕ) : ℤ))
        (Transport.gridParent W))).toReal := by
    rw [Geometry.volume_adaptedCellAtCenter, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (abs_nonneg _),
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ (t - ((H + n : ℕ) : ℤ)))]
    exact mul_pos
      (abs_pos.mpr (IsUnit.ne_zero ((Matrix.isUnit_iff_isUnit_det qq).mp hq)))
      (pow_pos (by positivity : (0 : ℝ) < (3 : ℝ) ^ (t - ((H + n : ℕ) : ℤ))) d)
  have hWpos :
      0 < (volume (adaptedCellAtCenter qq (t - ((H + n + 1 : ℕ) : ℤ)) W)).toReal := by
    rw [Geometry.volume_adaptedCellAtCenter, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (abs_nonneg _),
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ (t - ((H + n + 1 : ℕ) : ℤ)))]
    exact mul_pos
      (abs_pos.mpr (IsUnit.ne_zero ((Matrix.isUnit_iff_isUnit_det qq).mp hq)))
      (pow_pos (by positivity : (0 : ℝ) < (3 : ℝ) ^ (t - ((H + n + 1 : ℕ) : ℤ))) d)
  have hmain := abs_volumeAverage_sub_one_sub_volumeAverage_sub_one_le (d := d) (qq := qq)
    hq (t := t) (φ := φ) hφ (H + n) (Transport.gridParent W)
    (W := adaptedCellAtCenter qq (t - ((H + n + 1 : ℕ) : ℤ)) W)
    hsub (ne_of_gt hPpos) (Geometry.volume_adaptedCellAtCenter_ne_top qq _ _)
    (integrableOn_isResponseCutoff hq hφ _ _)
    (ne_of_gt hWpos) (Geometry.volume_adaptedCellAtCenter_ne_top qq _ _)
    (integrableOn_isResponseCutoff hq hφ _ _)
  have hpow : (3 : ℝ) ^ (-(((H + n : ℕ) : ℝ))) =
      (3 : ℝ) ^ (-(H : ℝ)) * (3 : ℝ) ^ (-(n : ℝ)) := by
    rw [show -(((H + n : ℕ) : ℝ)) = -(H : ℝ) + -(n : ℝ) by push_cast; ring]
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  calc
    |volumeAverage (adaptedCellAtCenter qq (t - ((H + n + 1 : ℕ) : ℤ)) W) (fun x => φ x - 1)
        - volumeAverage (adaptedCellAtCenter qq (t - ((H + n : ℕ) : ℤ)) (Transport.gridParent W))
            (fun x => φ x - 1)|
        ≤ 32 * (d : ℝ) ^ 2 * responseCutoffProfileConst *
            (3 : ℝ) ^ (-(((H + n : ℕ) : ℝ))) := hmain
    _ = (32 * (d : ℝ) ^ 2 * responseCutoffProfileConst * (3 : ℝ) ^ (-(H : ℝ)))
          * (3 : ℝ) ^ (-(n : ℝ)) := by
        rw [hpow]; ring

end

end HCPolySupport.HighContrast.Multiscale
end
