/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.EdBridgeInteriorClause

/-!
# EdFinalInputs

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The interior branch's three carried inputs, discharged

The interior route (`EdBridgeInteriorClause`) delivers the two-leg one-step
contraction off the harmonic-approximation anchor, but carries three items as
binders:

* the frozen statement's **frontier-empty gate** on the bare parent image `(z+□_n) ∩ ∂□_m = ∅`,
  together with the one-step's own interior inclusion `(x+□_{n-2}) ⊆ □_m`;
* the **harmonic replacement pair** `(v, w)` on the moved replacement cube, at every scale;

This module discharges all three.

## 1. The gate, from `z ∈ □_{m-1}`

`image_add_subset_openCubeSet_of_mem_inner`: for `z ∈ □_{m-1}` and `j ≤ m-1`
the translated cube `z + □_j` sits inside `□_m` — the coordinates satisfy
`|z_i| < 3^{m-1}/2` and `|w_i| < 3^j/2 ≤ 3^{m-1}/2`, so `|z_i + w_i| < 3^{m-1}
= 3^m/3 < 3^m/2`.  Since `□_m` is open it is disjoint from its own frontier, so
the frozen statement's gate follows (`inter_frontier_eq_empty_of_subset`), and
so does the one-step's interior inclusion (the same lemma at `j - 2`).  This is
exactly the implication disclosed as "the terminal consumer supplies it from `z
∈ □_{m-1}`", now formalized: the connectedness detour is not needed, the
coordinate computation is direct.

## 2. The harmonic replacement pair, at every scale

`exists_harmonicReplacementPair`: on any open bounded convex nonempty window `V` and for any
`H¹(V)` datum `Φ` there are `v : H¹(V)` weakly harmonic and `w : H¹₀(V)` with

```text
   v = Φ − w      and      ∇v = ∇Φ − ∇w        (both POINTWISE, as the anchor demands) .
```

The construction is the proved `ResidualCorrectorExistence` route run at the
datum's own force `+∇Φ` (rather than `−∇Φ`), so that the solution enters with
the sign the anchor's clauses want and both clauses are `H1Function.sub_toFun`
/ `H1Function.sub_grad`.  Reading the packaged
`ResidualCorrectorExistence.exists_weaklyHarmonicOn_of_datum` instead would
deliver only the `toFun` clause: its `MemH10` witness is existentially bound,
and pointwise gradient equality does not follow from pointwise value equality.

`exists_harmonicReplacementPair_movedCube` instantiates it at the anchor's own moved replacement
cube `y + □_{n-2}`, `y = wellPlacedCentre z m (n-2)`, using the identity
`(y + □_{n-2}) = truncatedWindow y m (n-2)` (the clamped cube already sits inside `□_m`).

## 3. The contraction absorption at the interior ratio

`exists_edFinalStep` is `EdBridgeFolds.exists_edBridgeStep` read on the
interior branch: there is no `W' → U_0` re-index there, so the
quasi-monotonicity price `κ(d,1)` is not paid and the target ratio is `θ^k =
3^{-k/4}` rather than `θ^{k+1}`.  Both simplifications are strict weakenings of
the proved statement (`1 ≤ κ(d,1)` and `3^{-(k+1)/4} ≤ 3^{-k/4}`), so the
interior step size is the proved `k₀(d)` unchanged.

## References

* ABK26, `l.harmonic.approximation.good.scales`, (the interior clause and its
  gate); `t.regularity` Step 4, (the indicator `1_{z ∉ □_{m-1}}`).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

/-! ## 1. The gate from `z ∈ □_{m-1}` -/

/-- **The interior gate, from the printed indicator's own condition.**  For `z ∈ □_{m-1}` and
`j ≤ m-1` the translated cube `z + □_j` sits inside `□_m`. -/
theorem image_add_subset_openCubeSet_of_mem_inner {m j : ℤ} {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d (m - 1))) (hj : j ≤ m - 1) :
    (fun y => z + y) '' openCubeSet (originCube d j) ⊆
      openCubeSet (originCube d m) := by
  rintro p ⟨w, hw, rfl⟩
  rw [HCPolySupport.mem_openCubeSet_originCube_iff] at hz hw ⊢
  intro i
  have hzi := hz i
  have hwi := hw i
  have hmono : (3 : ℝ) ^ j ≤ (3 : ℝ) ^ (m - 1) :=
    zpow_le_zpow_right₀ (by norm_num) hj
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (m - 1) := zpow_pos (by norm_num) _
  have hstep : (3 : ℝ) ^ (m - 1) * 3 = (3 : ℝ) ^ m := by
    rw [← zpow_add_one₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    ring
  simp only [Pi.add_apply]
  constructor
  · linarith only [hzi.1, hwi.1, hmono, hpos, hstep]
  · linarith only [hzi.2, hwi.2, hmono, hpos, hstep]

/-- **The frozen interior clause's frontier-empty gate**, from any inclusion in `□_m`: an open
set is disjoint from its own frontier. -/
theorem inter_frontier_eq_empty_of_subset {m : ℤ} {A : Set (Vec d)}
    (h : A ⊆ openCubeSet (originCube d m)) :
    A ∩ frontier (openCubeSet (originCube d m)) = ∅ := by
  have hopen : IsOpen (openCubeSet (originCube d m)) := isOpen_openCubeSet _
  have hdisj : (openCubeSet (originCube d m)) ∩
      frontier (openCubeSet (originCube d m)) = ∅ := hopen.inter_frontier_eq
  exact Set.eq_empty_of_subset_empty fun p hp => hdisj ▸ ⟨h hp.1, hp.2⟩

/-- **The frozen interior clause's gate at the printed indicator's own condition.** -/
theorem frontier_gate_of_mem_inner {m j : ℤ} {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d (m - 1))) (hj : j ≤ m - 1) :
    ((fun y => z + y) '' openCubeSet (originCube d j)) ∩
        frontier (openCubeSet (originCube d m)) = ∅ :=
  inter_frontier_eq_empty_of_subset (image_add_subset_openCubeSet_of_mem_inner hz hj)

/-! ## 2. The harmonic replacement pair -/

/-- **The harmonic replacement pair exists on every admissible window.**

`v` weakly harmonic, `w ∈ H¹₀(V)`, and BOTH clauses the anchor's interior slot
demands: `v = Φ − w` and `∇v = ∇Φ − ∇w`, pointwise.  The Dirichlet solve is run
at the datum's own force `+∇Φ`, so the pair is `(Φ − ρ, ρ)` with `ρ` the
zero-trace solution. -/
theorem exists_harmonicReplacementPair [NeZero d] {V : Set (Vec d)}
    (hV : IsOpenBoundedConvexDomain V) (hne : V.Nonempty) (Phi : H1Function V) :
    ∃ (v : H1Function V) (w : H10Function V),
      IsWeaklyHarmonicOn V v ∧
        (∀ y, v.toFun y = Phi.toFun y - w.toH1Function.toFun y) ∧
        (∀ y, v.grad y = Phi.grad y - w.toH1Function.grad y) := by
  have : IsFiniteMeasure (volumeMeasureOn V) := hV.isFiniteMeasure_restrict_volume
  have hgrad : MemVectorL2 V Phi.grad := Phi.grad_memVectorL2
  have hrealize :
      PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization V :=
    PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_convexDomain
      hV
  obtain ⟨rho, hrho⟩ :=
    exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
      (a := unitCoeffField d) (U := V) (g := Phi.grad) (lam := 1) (Lam := 1)
      hgrad hrealize hne (isEllipticFieldOn_unitCoeffField hV.isOpen.measurableSet)
  refine ⟨Phi - rho.toH1Function, rho, ?_, ?_, ?_⟩
  · intro phi
    have hrhomem : MemVectorL2 V rho.toH1Function.grad := rho.toH1Function.grad_memVectorL2
    have hsplit := integral_vecDot_sub_left_split (U := V) hgrad hrhomem
      (H := (Phi - rho.toH1Function).grad)
      (fun x => by rw [H1Function.sub_grad]) phi
    have hid := hrho phi
    have hcongr : ∫ x in V, vecDot (matVecMul (unitCoeffField d x)
          (rho.toH1Function.grad x)) (phi.toH1Function.grad x) ∂volume =
        ∫ x in V, vecDot (rho.toH1Function.grad x) (phi.toH1Function.grad x) ∂volume :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        change vecDot (matVecMul (unitCoeffField d x) (rho.toH1Function.grad x))
            (phi.toH1Function.grad x) =
          vecDot (rho.toH1Function.grad x) (phi.toH1Function.grad x)
        rw [matVecMul_unitCoeffField])
    rw [hcongr] at hid
    rw [hsplit, hid]
    ring
  · intro y
    rw [H1Function.sub_toFun]
  · intro y
    rw [H1Function.sub_grad]

/-- The anchor's moved replacement cube IS a truncated window at the clamped centre. -/
theorem movedCube_eq_truncatedWindow {m n : ℤ} (z : Vec d) (hnm : n - 2 ≤ m) :
    ((fun y => wellPlacedCentre z m (n - 2) + y) '' openCubeSet (originCube d (n - 2)))
      = truncatedWindow (wellPlacedCentre z m (n - 2)) m (n - 2) := by
  rw [truncatedWindow]
  exact (Set.inter_eq_self_of_subset_left
    (image_add_wellPlacedCentre_subset_openCubeSet z hnm)).symm

/-- **The harmonic replacement pair at the anchor's own moved replacement cube**,
at every scale `n` with `n - 2 ≤ m`: the interior route's carried item (c),
discharged from the solution `u` alone. -/
theorem exists_harmonicReplacementPair_movedCube [NeZero d] {m n : ℤ} {z : Vec d}
    (hnm : n - 2 ≤ m) (u : H1Function (openCubeSet (originCube d m))) :
    ∃ (v : H1Function ((fun y => wellPlacedCentre z m (n - 2) + y) ''
          openCubeSet (originCube d (n - 2))))
      (w : H10Function ((fun y => wellPlacedCentre z m (n - 2) + y) ''
          openCubeSet (originCube d (n - 2)))),
      IsWeaklyHarmonicOn ((fun y => wellPlacedCentre z m (n - 2) + y) ''
          openCubeSet (originCube d (n - 2))) v ∧
        (∀ y, v.toFun y = u.toFun y - w.toH1Function.toFun y) ∧
        (∀ y, v.grad y = u.grad y - w.toH1Function.grad y) := by
  have hsub : ((fun y => wellPlacedCentre z m (n - 2) + y) ''
      openCubeSet (originCube d (n - 2))) ⊆ openCubeSet (originCube d m) :=
    image_add_wellPlacedCentre_subset_openCubeSet z hnm
  have hdom : IsOpenBoundedConvexDomain ((fun y => wellPlacedCentre z m (n - 2) + y) ''
      openCubeSet (originCube d (n - 2))) := by
    rw [movedCube_eq_truncatedWindow (m := m) (n := n) z hnm]
    exact isOpenBoundedConvexDomain_truncatedWindow _ m (n - 2)
  have hne : (((fun y => wellPlacedCentre z m (n - 2) + y) ''
      openCubeSet (originCube d (n - 2)))).Nonempty :=
    ⟨wellPlacedCentre z m (n - 2) + 0,
      ⟨0, zero_mem_openCubeSet_originCube d (n - 2), rfl⟩⟩
  exact exists_harmonicReplacementPair hdom hne (u.restrict hdom.isOpen hsub)

/-! ## 3. The contraction absorption at the interior ratio -/

/-- `1 ≤ κ(d,j)` for `j ≥ -1`: the volume-ratio constant is at least one. -/
theorem one_le_windowRatioConst (d : ℕ) [NeZero d] {j : ℤ} (hj : -1 ≤ j) :
    1 ≤ windowRatioConst d j := by
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
  have hexp : (0 : ℝ) ≤ (d : ℝ)⁻¹ + 1 / 2 := by
    have := inv_nonneg.mpr hdR.le
    linarith only [this]
  have hbase : (1 : ℝ) ≤ ((3 : ℝ) ^ (j + 2)) ^ d := by
    have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ (j + 2) := by
      rw [show (1 : ℝ) = (3 : ℝ) ^ (0 : ℤ) from (zpow_zero (3 : ℝ)).symm]
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    exact one_le_pow₀ h1
  have h := Real.rpow_le_rpow_of_exponent_le hbase hexp
  rw [Real.rpow_zero] at h
  exact h

/-- **The contraction absorption on the interior branch.**  There is a step size `k₀(d) ≥ 3`
beyond which the one-step's contraction prefactor is absorbed into HALF of the iteration
anchor's own ratio `θ^k = 3^{-k/4}` — no `κ(d,1)`, and no shift to `θ^{k+1}`, because the
interior clause reads its oscillation on the contraction's own window. -/
theorem exists_edFinalStep (d : ℕ) [NeZero d] :
    ∃ k₀ : ℕ, 3 ≤ k₀ ∧ ∀ k : ℕ, k₀ ≤ k →
      taylorContractionConst d * schauderWindowConst d * windowRatioConst d 2
            * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ)
        ≤ (1 / 2 : ℝ) * (3 : ℝ) ^ (-(1 / 4 : ℝ) * (k : ℝ)) := by
  obtain ⟨k₀, hk₀, habsorb⟩ := exists_edBridgeStep d
  refine ⟨k₀, hk₀, fun k hk => ?_⟩
  have hbase := habsorb k hk
  have hkappa : 1 ≤ windowRatioConst d 1 := one_le_windowRatioConst d (by omega)
  have hpre : (0 : ℝ) ≤ taylorContractionConst d * schauderWindowConst d *
      windowRatioConst d 2 * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (taylorContractionConst_nonneg d)
      (schauderWindowConst_nonneg d)) (windowRatioConst_nonneg d 2))
      (Real.rpow_nonneg (zpow_pos (by norm_num) _).le _)
  have hgrow : taylorContractionConst d * schauderWindowConst d * windowRatioConst d 2
      * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) ≤
      taylorContractionConst d * schauderWindowConst d * windowRatioConst d 2
        * windowRatioConst d 1 * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) := by
    have h := mul_le_mul_of_nonneg_left hkappa hpre
    have hid : taylorContractionConst d * schauderWindowConst d * windowRatioConst d 2 *
          ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) * windowRatioConst d 1
        = taylorContractionConst d * schauderWindowConst d * windowRatioConst d 2 *
          windowRatioConst d 1 * ((3 : ℝ) ^ (-(k : ℤ))) ^ (1 / 2 : ℝ) := by ring
    linarith only [h, hid]
  have hratio : (3 : ℝ) ^ (-(1 / 4 : ℝ) * ((k : ℝ) + 1)) ≤
      (3 : ℝ) ^ (-(1 / 4 : ℝ) * (k : ℝ)) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    linarith only []
  linarith only [hbase, hgrow, hratio]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
