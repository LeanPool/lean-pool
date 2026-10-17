/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.IncrementGaugeTwoIndex
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Events

/-!
# GaugeBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The Section 4 shell gauges and the Section 3 oscillation gauge

ABK26 weighs the stream increments in two notations that differ only by where
the scale factor sits.

* Section 4 (`d.good.event.for.lambda`, and `p.mathcalE.annular.decomp`)
  writes the **volume-normalized** gauge `‖∇j‖_{W^{1,∞}(z+□_l)}` and
  multiplies it by `3^{(2−γ)l}` in the displays.  This is
  `Section4.Support.shellW1InfGradNorm` at the translate: the maximum of
  `‖∇²j‖_{L^∞}` and `3^{−l}‖∇j‖_{L^∞}`.
* Section 3 (`e.Bosc.def`, `e.BoscL.def`) writes the same quantity with the
  factor `3^{2l}` **already distributed inside the maximum**, as
  `Provider.BadEvents.cubeOscGauge`: the maximum of `3^{2l}‖∇²j‖_{L^∞}` and
  `3^{l}‖∇j‖_{L^∞}`.

The two are literally the same number up to the factor `3^{2l}`:

```
cubeOscGauge Q h = 3^(2 Q.scale) * shellW1InfGradNorm Q.scale
                     (ShellField.translate (cubeBasePoint Q) h) .
```

This module records that identity and the three consequences the Section 4
chains need, none of which is stated anywhere else in the repository:

* `shellW1InfGradNorm_translate_sum_le` -- the **triangle inequality over a
  layer sum** at the Section 4 gauge, transported from `cubeOscGauge_sum_le`.
  This is the Lean form of the manuscript's repeated step `∇(k_b − k_a) = Σ_{l
  ∈ (a,b]} ∇j_l` followed by the triangle inequality.
* `shellW1InfGradNorm_translate_shellIncrement_le` -- the same at the literal
  cutoff increment `k_b − k_a`.
* `shellW1InfGradNorm_le_zpow_mul_of_le` -- the **same-centre cube-scale
  comparison** `W(n) ≤ 3^{k−n} W(k)` for `n ≤ k`, which is exactly the
  manuscript's auxiliary display once the two `3^{(2−γ)·}` prefactors are
  restored (see the docstring).

## Scope

The lattice-max enlargement (replacing the maximum over the scale-`n` lattice
by the maximum over the scale-`k` lattice) is a covering statement about
`latticeCubeSet` and is NOT proved here; the comparison below is at a fixed
common centre.
-/

namespace Algsuperdiff.Section4.Support

open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Stream
open Algsuperdiff.Section3.Provider.BadEvents

variable {d : ℕ}

/-! ## The gauge identity -/

/-- **The Section 4 / Section 3 gauge identity.**

`cubeOscGauge` is the Section 4 gauge with the factor `3^{2l}` pulled inside the
maximum: `3^{2l} max(S, 3^{−l} D) = max(3^{2l} S, 3^{l} D)`. -/
theorem cubeOscGauge_eq_zpow_mul_shellW1InfGradNorm (Q : TriadicCube d)
    (h : ShellField d) :
    cubeOscGauge Q h
      = (3 : ℝ) ^ (2 * Q.scale)
        * shellW1InfGradNorm Q.scale (ShellField.translate (cubeBasePoint Q) h) := by
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (2 * Q.scale) := by positivity
  have hleg : (3 : ℝ) ^ (2 * Q.scale) * ((3 : ℝ) ^ (-Q.scale)) = (3 : ℝ) ^ Q.scale := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    ring
  rw [cubeOscGauge, shellW1InfGradNorm_def, mul_max_of_nonneg _ _ hpos.le]
  congr 1
  rw [← mul_assoc, hleg]

/-- The inverse form: the Section 4 gauge is the Section 3 gauge discounted by
`3^{−2l}`. -/
theorem shellW1InfGradNorm_translate_eq_zpow_mul_cubeOscGauge (Q : TriadicCube d)
    (h : ShellField d) :
    shellW1InfGradNorm Q.scale (ShellField.translate (cubeBasePoint Q) h)
      = (3 : ℝ) ^ (-(2 * Q.scale)) * cubeOscGauge Q h := by
  rw [cubeOscGauge_eq_zpow_mul_shellW1InfGradNorm Q h, ← mul_assoc,
    ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), neg_add_cancel, zpow_zero, one_mul]

/-- The base point of the triadic cube `⟨k, v⟩` is the lattice point
`3^k v` used by the Section 4 events. -/
theorem cubeBasePoint_mk (k : ℤ) (v : Fin d → ℤ) :
    cubeBasePoint (⟨k, v⟩ : TriadicCube d) = triadicLatticePoint k v := by
  funext i
  simp only [cubeBasePoint, triadicLatticePoint]
  ring

/-- **The gauge identity at a lattice centre**, in the exact spelling of the
Section 4 good events. -/
theorem cubeOscGauge_mk_eq_zpow_mul_shellW1InfGradNorm (k : ℤ) (v : Fin d → ℤ)
    (h : ShellField d) :
    cubeOscGauge (⟨k, v⟩ : TriadicCube d) h
      = (3 : ℝ) ^ (2 * k)
        * shellW1InfGradNorm k
            (ShellField.translate (triadicLatticePoint k v) h) := by
  rw [cubeOscGauge_eq_zpow_mul_shellW1InfGradNorm, cubeBasePoint_mk]

/-! ## The triangle inequality over a layer sum, at the Section 4 gauge -/

/-- **The layer-sum triangle inequality at the Section 4 gauge.**

The Lean form of the manuscript's repeated step: expand `∇(k_b − k_a)` as the
finite sum of `∇j_l` (tex `e.infrared.cutoff.def`) and apply the triangle
inequality. -/
theorem shellW1InfGradNorm_translate_sum_le {iota : Type*} (k : ℤ) (v : Fin d → ℤ)
    (s : Finset iota) (f : iota → ShellField d) :
    shellW1InfGradNorm k
        (ShellField.translate (triadicLatticePoint k v) (ShellField.sum s f))
      ≤ ∑ i ∈ s,
          shellW1InfGradNorm k (ShellField.translate (triadicLatticePoint k v) (f i)) := by
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (-(2 * k)) := by positivity
  have hbase := cubeOscGauge_sum_le (⟨k, v⟩ : TriadicCube d) s f
  have hlhs : shellW1InfGradNorm k
      (ShellField.translate (triadicLatticePoint k v) (ShellField.sum s f))
      = (3 : ℝ) ^ (-(2 * k)) * cubeOscGauge (⟨k, v⟩ : TriadicCube d)
          (ShellField.sum s f) := by
    rw [← cubeBasePoint_mk k v]
    exact shellW1InfGradNorm_translate_eq_zpow_mul_cubeOscGauge
      (⟨k, v⟩ : TriadicCube d) (ShellField.sum s f)
  have hrhs : ∀ i : iota,
      shellW1InfGradNorm k (ShellField.translate (triadicLatticePoint k v) (f i))
        = (3 : ℝ) ^ (-(2 * k)) * cubeOscGauge (⟨k, v⟩ : TriadicCube d) (f i) := by
    intro i
    rw [← cubeBasePoint_mk k v]
    exact shellW1InfGradNorm_translate_eq_zpow_mul_cubeOscGauge
      (⟨k, v⟩ : TriadicCube d) (f i)
  rw [hlhs, Finset.sum_congr rfl (fun i _ => hrhs i), ← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left hbase hpos.le

/-- **The layer-sum triangle inequality at the literal cutoff increment.**

`k_b − k_a = Σ_{l ∈ (a,b]} j_l` is `Cutoff.shellIncrement`, so the previous
lemma reads on the genuine increment. -/
theorem shellW1InfGradNorm_translate_shellIncrement_le (k : ℤ) (v : Fin d → ℤ)
    (omega : ShellSeq d) (a b : ℤ) :
    shellW1InfGradNorm k
        (ShellField.translate (triadicLatticePoint k v) (shellIncrement omega a b))
      ≤ ∑ l ∈ Finset.Ioc a b,
          shellW1InfGradNorm k
            (ShellField.translate (triadicLatticePoint k v) (omega l)) :=
  shellW1InfGradNorm_translate_sum_le k v (Finset.Ioc a b) omega

/-- **The `m`-vs-`L` index bridge, with its tail made explicit.**

The clause-(i) chain carries `grad (k_L - k_{n-2})` in
`e.mathcalE.annular.decomp.pre.zero`'s third term but `grad (k_m - k_{n-2})` in
the Step-3 gradient display; the source performs the substitution silently.

The proved increment calculus does support the bridge, but not as a substitution:
splitting the layer range `(a, c]` at `b` produces the head block `(a, b]` --
the `k in [n-1, m]` block the Step-3 display resums -- plus a genuine **tail**
`(b, c]`, which is the `k > m` block that `d.good.event.for.lambda`'s first
`G_1` condition bounds and that becomes `pre.zero`'s fifth term.  A caller must
route the tail there; it cannot be absorbed into the head block. -/
theorem shellW1InfGradNorm_translate_shellIncrement_split (k : ℤ) (v : Fin d → ℤ)
    (omega : ShellSeq d) {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) :
    shellW1InfGradNorm k
        (ShellField.translate (triadicLatticePoint k v) (shellIncrement omega a c))
      ≤ (∑ l ∈ Finset.Ioc a b,
            shellW1InfGradNorm k
              (ShellField.translate (triadicLatticePoint k v) (omega l)))
        + ∑ l ∈ Finset.Ioc b c,
            shellW1InfGradNorm k
              (ShellField.translate (triadicLatticePoint k v) (omega l)) := by
  classical
  have hdisj : Disjoint (Finset.Ioc a b) (Finset.Ioc b c) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rw [Finset.mem_Ioc] at hx hx'
    omega
  have hunion : Finset.Ioc a b ∪ Finset.Ioc b c = Finset.Ioc a c :=
    Finset.Ioc_union_Ioc_eq_Ioc hab hbc
  have hsplit : (∑ l ∈ Finset.Ioc a b,
        shellW1InfGradNorm k
          (ShellField.translate (triadicLatticePoint k v) (omega l)))
      + ∑ l ∈ Finset.Ioc b c,
          shellW1InfGradNorm k
            (ShellField.translate (triadicLatticePoint k v) (omega l))
      = ∑ l ∈ Finset.Ioc a c,
          shellW1InfGradNorm k
            (ShellField.translate (triadicLatticePoint k v) (omega l)) := by
    rw [← Finset.sum_union hdisj, hunion]
  rw [hsplit]
  exact shellW1InfGradNorm_translate_shellIncrement_le k v omega a c

/-! ## The same-centre cube-scale comparison -/

/-- **The same-centre cube-scale comparison** `W(n) ≤ 3^{k−n} W(k)` for
`n ≤ k`, at the origin cube.

This is the content of the manuscript's auxiliary display once its two
prefactors are restored: multiplying both sides by `3^{(2−γ)n}` turns it into

```
3^{(2−γ)n} W(n) ≤ 3^{(1−γ)(n−k)} · 3^{(2−γ)k} W(k) ,
```

because `(1−γ)(n−k) + (2−γ)k − (2−γ)n = k − n`. -/
theorem shellW1InfGradNorm_le_zpow_mul_of_le {n k : ℤ} (hnk : n ≤ k)
    (j : ShellField d) :
    shellW1InfGradNorm n j ≤ (3 : ℝ) ^ (k - n) * shellW1InfGradNorm k j := by
  have hone : (1 : ℝ) ≤ (3 : ℝ) ^ (k - n) :=
    one_le_zpow₀ (by norm_num : (1 : ℝ) ≤ 3) (by omega)
  have hmaxk : 0 ≤ shellW1InfGradNorm k j := shellW1InfGradNorm_nonneg k j
  have hS : localCubeSecondDerivNorm n j ≤ localCubeSecondDerivNorm k j :=
    localCubeSecondDerivNorm_mono hnk j
  have hD : localCubeDerivNorm n j ≤ localCubeDerivNorm k j :=
    localCubeDerivNorm_mono hnk j
  have hlegS : localCubeSecondDerivNorm n j
      ≤ (3 : ℝ) ^ (k - n) * shellW1InfGradNorm k j := by
    refine hS.trans ((localCubeSecondDerivNorm_le_shellW1InfGradNorm k j).trans ?_)
    calc shellW1InfGradNorm k j = 1 * shellW1InfGradNorm k j := (one_mul _).symm
      _ ≤ (3 : ℝ) ^ (k - n) * shellW1InfGradNorm k j :=
          mul_le_mul_of_nonneg_right hone hmaxk
  have hlegD : (3 : ℝ) ^ (-n) * localCubeDerivNorm n j
      ≤ (3 : ℝ) ^ (k - n) * shellW1InfGradNorm k j := by
    have hpn : (0 : ℝ) < (3 : ℝ) ^ (-n) := by positivity
    have hstep : (3 : ℝ) ^ (-n) * localCubeDerivNorm n j
        ≤ (3 : ℝ) ^ (-n) * localCubeDerivNorm k j :=
      mul_le_mul_of_nonneg_left hD hpn.le
    have hrw : (3 : ℝ) ^ (-n) * localCubeDerivNorm k j
        = (3 : ℝ) ^ (k - n) * ((3 : ℝ) ^ (-k) * localCubeDerivNorm k j) := by
      rw [← mul_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      congr 2
      ring
    refine hstep.trans ?_
    rw [hrw]
    exact mul_le_mul_of_nonneg_left
      (three_zpow_mul_localCubeDerivNorm_le_shellW1InfGradNorm k j)
      (by positivity)
  rw [shellW1InfGradNorm_def]
  exact max_le hlegS hlegD

end Algsuperdiff.Section4.Support
