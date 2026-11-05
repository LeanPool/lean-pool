/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.DisplaySlots
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.GaugeBridge

/-!
# LatticeCover

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The scale-`k` lattice tiling of `cu_m`, and the shell gauge it dominates

ABK26, Section 4.1, the two Step-2 budget displays.  Both perform the same
unremarked move: a shell norm read on the *annulus* cube `z + cu_n` (with `z` a
scale-`n` lattice point) is replaced by the maximum of the `W^{2,infinity}`
shell gauge over the scale-`k` lattice cubes of `cu_m` -- the very family the
good event `Support.eventG1`'s second condition, and the frozen clause-(i)
fourth term, are written with.

`Support.GaugeBridge`'s scope note records that this "lattice-max enlargement"
is NOT proved there (only the same-centre cube-scale comparison is).

Recorded here, because it fixes the route taken below: the *naive* reading --
first enlarge `z + cu_n` to `z + cu_k` at the same centre by
`Support.shellW1InfGradNorm_le_zpow_mul_of_le`, then look for a scale-`k`
lattice cube of `cu_m` containing the enlarged cube -- does NOT close.  For
`k > n` and `z` at the outer edge of the annulus the enlarged cube leaves
`cu_m`: `z = 3^n v` with `|z_i| <= (3^m - 3^n)/2` only gives
`|z_i| + 3^k/2 <= 3^m/2 + (3^k - 3^n)/2`, which exceeds `3^m/2` as soon as
`k > n`.

This module proves the move by the *other* route, which needs no enlargement:

* the annulus cube stays inside the observation cube --
  `translate_openCubeSet_originCube_subset`: `z + cu_n` is contained in
  `cu_m` (**openly**) for every scale-`n` lattice point `z` of `cu_m`; and
* the scale-`k` lattice cubes **tile** `cu_m` in CoarseGraining's half-open
  realization `cubeSet` -- `exists_mem_latticeCubeSet_sub_mem_cubeSet`.

Only the half-open tiling is exact, so a point of `z + cu_n` may land on a
tile face, which the *open*-cube sup gauges of the shell layer do not see.
The gap is closed by continuity: the frozen `ShellField` carries continuous
first and second derivatives, so the sup over an open triadic cube already
bounds the value at every point of its half-open closure
(`..._le_localCubeSecondDerivNorm_cubeSet` and its two siblings).

## Main results

* `exists_mem_latticeCubeSet_sub_mem_cubeSet` -- the tiling.
* `translate_openCubeSet_originCube_subset` -- the containment.
* `shellW2InfLatticeMaxOf` -- the lattice maximum of `DisplaySlots`, read at an
  abstract shell field.
* `shellW1InfGradNorm_translate_le_shellW2InfLatticeMaxOf` -- the enlargement
  at the `W^{1,infinity}` gauge, at the honest factor `max 1 3^{k-n}`.

* `localCubeControl_translate_le_shellW2InfLatticeMaxOf` -- the same at the
  `L^infinity` value gauge, at the factor `3^{2k}`.
* `localCubeControl_le_of_forall` and `localCubeControl_sum_le` -- the two
  missing pieces of the proved `Cutoff.localCubeControl` A (its minimality
  characterization and its layer-sum triangle inequality), re-proved here
  because the in-repo versions are `private` / absent.  They are what makes the
  value leg available at all.

## References

* ABK26, `p.mathcalE.annular.decomp` Step 2.
* ABK26, `d.good.event.for.lambda`, (the `3^k Z^d ∩ cu_m` family).
-/

namespace Algsuperdiff.Section4.Provider.Annular

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Section3
open Algsuperdiff.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-! ## Part A -- the half-open tiling of `cu_m` by scale-`k` lattice cubes -/

private theorem three_pow_odd_int (t : ℕ) : ∃ jj : ℤ, (3 : ℤ) ^ t = 2 * jj + 1 := by
  induction t with
  | zero => exact ⟨0, by norm_num⟩
  | succ p ih =>
      obtain ⟨jj, hjj⟩ := ih
      exact ⟨3 * jj + 1, by rw [pow_succ, hjj]; ring⟩

private theorem three_zpow_add_toNat {k m : ℤ} (hkm : k ≤ m) :
    (3 : ℝ) ^ m = (3 : ℝ) ^ k * (3 : ℝ) ^ ((m - k).toNat : ℕ) := by
  have hmk : m = k + ((m - k).toNat : ℤ) := by
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  calc (3 : ℝ) ^ m = (3 : ℝ) ^ (k + ((m - k).toNat : ℤ)) := by rw [← hmk]
    _ = (3 : ℝ) ^ k * (3 : ℝ) ^ (((m - k).toNat : ℕ) : ℤ) :=
        zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0) _ _
    _ = (3 : ℝ) ^ k * (3 : ℝ) ^ ((m - k).toNat : ℕ) := by rw [zpow_natCast]

/-- **The scale-`k` lattice cubes tile `cu_m`.**

Every point of the open cube `cu_m` lies in the half-open realization
`cubeSet` of exactly one scale-`k` lattice cube `3^k w + cu_k` with
`w ∈ 3^k Z^d ∩ cu_m` -- the index family of the good event's second condition
and of the frozen clause-(i) fourth term.  The index is the coordinatewise
rounding `w_i = floor(x_i 3^{-k} + 1/2)`, and it stays inside the balanced box
because `3^{m-k}` is odd. -/
theorem exists_mem_latticeCubeSet_sub_mem_cubeSet {k m : ℤ} (hkm : k ≤ m)
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d m)) :
    ∃ w ∈ Support.latticeCubeSet d k m,
      x - Support.triadicLatticePoint k w ∈ cubeSet (originCube d k) := by
  classical
  have hA : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  have hpow := three_zpow_add_toNat hkm
  have hcoord : ∀ i : Fin d,
      (((⌊x i / (3 : ℝ) ^ k + 1 / 2⌋ : ℤ) : ℝ) ≤ x i / (3 : ℝ) ^ k + 1 / 2 ∧
        x i / (3 : ℝ) ^ k + 1 / 2 < ((⌊x i / (3 : ℝ) ^ k + 1 / 2⌋ : ℤ) : ℝ) + 1) := by
    intro i
    exact ⟨Int.floor_le _, Int.lt_floor_add_one _⟩
  refine ⟨fun i => ⌊x i / (3 : ℝ) ^ k + 1 / 2⌋, ?_, ?_⟩
  · refine (mem_latticeCubeSet_iff hkm _).mpr ?_
    intro i
    obtain ⟨hlo, hhi⟩ := hcoord i
    have hxi := (mem_openCubeSet_originCube_iff.mp hx) i
    have hxlo : -(1 / 2 : ℝ) * ((3 : ℝ) ^ k * (3 : ℝ) ^ ((m - k).toNat : ℕ)) < x i := by
      rw [← hpow]; exact hxi.1
    have hxhi : x i < (1 / 2 : ℝ) * ((3 : ℝ) ^ k * (3 : ℝ) ^ ((m - k).toNat : ℕ)) := by
      rw [← hpow]; exact hxi.2
    have hidlo : -(1 / 2 : ℝ) * (3 : ℝ) ^ ((m - k).toNat : ℕ) * (3 : ℝ) ^ k
        = -(1 / 2 : ℝ) * ((3 : ℝ) ^ k * (3 : ℝ) ^ ((m - k).toNat : ℕ)) := by ring
    have hidhi : (1 / 2 : ℝ) * (3 : ℝ) ^ ((m - k).toNat : ℕ) * (3 : ℝ) ^ k
        = (1 / 2 : ℝ) * ((3 : ℝ) ^ k * (3 : ℝ) ^ ((m - k).toNat : ℕ)) := by ring
    have hdivlo : -(1 / 2 : ℝ) * (3 : ℝ) ^ ((m - k).toNat : ℕ) < x i / (3 : ℝ) ^ k := by
      rw [lt_div_iff₀ hA, hidlo]
      exact hxlo
    have hdivhi : x i / (3 : ℝ) ^ k < (1 / 2 : ℝ) * (3 : ℝ) ^ ((m - k).toNat : ℕ) := by
      rw [div_lt_iff₀ hA, hidhi]
      exact hxhi
    have hcast : (((3 : ℤ) ^ ((m - k).toNat : ℕ) : ℤ) : ℝ)
        = (3 : ℝ) ^ ((m - k).toNat : ℕ) := by push_cast; ring
    have hupper : (2 : ℝ) * ((⌊x i / (3 : ℝ) ^ k + 1 / 2⌋ : ℤ) : ℝ)
        < (((3 : ℤ) ^ ((m - k).toNat : ℕ) : ℤ) : ℝ) + 1 := by
      rw [hcast]; linarith only [hlo, hdivhi]
    have hlower : -((((3 : ℤ) ^ ((m - k).toNat : ℕ) : ℤ) : ℝ) + 1)
        < (2 : ℝ) * ((⌊x i / (3 : ℝ) ^ k + 1 / 2⌋ : ℤ) : ℝ) := by
      rw [hcast]; linarith only [hhi, hdivlo]
    have hupperZ : 2 * ⌊x i / (3 : ℝ) ^ k + 1 / 2⌋ < (3 : ℤ) ^ ((m - k).toNat : ℕ) + 1 := by
      exact_mod_cast hupper
    have hlowerZ : -((3 : ℤ) ^ ((m - k).toNat : ℕ) + 1)
        < 2 * ⌊x i / (3 : ℝ) ^ k + 1 / 2⌋ := by
      exact_mod_cast hlower
    obtain ⟨jj, hjj⟩ := three_pow_odd_int (m - k).toNat
    rcases abs_cases (⌊x i / (3 : ℝ) ^ k + 1 / 2⌋) with ⟨he, _⟩ | ⟨he, _⟩ <;>
      rw [he] <;> omega
  · refine mem_cubeSet_originCube_iff.mpr ?_
    intro i
    obtain ⟨hlo, hhi⟩ := hcoord i
    have hval : (x - Support.triadicLatticePoint k fun i => ⌊x i / (3 : ℝ) ^ k + 1 / 2⌋) i
        = x i - (3 : ℝ) ^ k * ((⌊x i / (3 : ℝ) ^ k + 1 / 2⌋ : ℤ) : ℝ) := rfl
    rw [hval]
    have hmul1 : (3 : ℝ) ^ k * ((⌊x i / (3 : ℝ) ^ k + 1 / 2⌋ : ℤ) : ℝ)
        ≤ (3 : ℝ) ^ k * (x i / (3 : ℝ) ^ k + 1 / 2) :=
      mul_le_mul_of_nonneg_left hlo hA.le
    have hmul2 : (3 : ℝ) ^ k * (x i / (3 : ℝ) ^ k + 1 / 2)
        < (3 : ℝ) ^ k * (((⌊x i / (3 : ℝ) ^ k + 1 / 2⌋ : ℤ) : ℝ) + 1) :=
      mul_lt_mul_of_pos_left hhi hA
    have hcancel : (3 : ℝ) ^ k * (x i / (3 : ℝ) ^ k + 1 / 2)
        = x i + (3 : ℝ) ^ k * (1 / 2) := by
      field_simp
    rw [hcancel] at hmul1 hmul2
    constructor
    · linarith only [hmul1]
    · linarith only [hmul2]

/-! ## Part B -- the open-cube sup gauges see the half-open closure -/

private theorem mem_closure_openCubeSet_originCube {ell : ℤ} {x : Vec d}
    (hx : x ∈ cubeSet (originCube d ell)) :
    x ∈ closure (openCubeSet (originCube d ell)) := by
  rw [Metric.mem_closure_iff]
  intro eps heps
  have hf : (0 : ℝ) < (3 : ℝ) ^ ell := by positivity
  set del : ℝ := min (1 / 2) (eps / ((3 : ℝ) ^ ell + 1)) with hdel
  have hdel0 : 0 < del := lt_min (by norm_num) (by positivity)
  have hdelhalf : del ≤ 1 / 2 := min_le_left _ _
  have hdelbd : del ≤ eps / ((3 : ℝ) ^ ell + 1) := min_le_right _ _
  refine ⟨(1 - del) • x, ?_, ?_⟩
  · refine mem_openCubeSet_originCube_iff.mpr ?_
    intro i
    have hxi := mem_cubeSet_originCube_iff.mp hx i
    have hval : ((1 - del) • x) i = (1 - del) * x i := rfl
    rw [hval]
    have hpos : (0 : ℝ) < 1 - del := by linarith only [hdelhalf]
    have hprod : 0 < del * ((1 / 2) * (3 : ℝ) ^ ell) := by positivity
    constructor
    · have hstep := mul_le_mul_of_nonneg_left hxi.1 hpos.le
      have hexp : (1 - del) * (-(1 / 2 : ℝ) * (3 : ℝ) ^ ell)
          = -(1 / 2 : ℝ) * (3 : ℝ) ^ ell + del * ((1 / 2) * (3 : ℝ) ^ ell) := by ring
      linarith only [hstep, hprod, hexp]
    · have hstep := mul_lt_mul_of_pos_left hxi.2 hpos
      have hexp : (1 - del) * ((1 / 2 : ℝ) * (3 : ℝ) ^ ell)
          = (1 / 2 : ℝ) * (3 : ℝ) ^ ell - del * ((1 / 2) * (3 : ℝ) ^ ell) := by ring
      linarith only [hstep, hprod, hexp]
  · have hbound : dist x ((1 - del) • x) ≤ del * ((1 / 2) * (3 : ℝ) ^ ell) := by
      refine (dist_pi_le_iff (by positivity)).mpr ?_
      intro i
      have hxi := mem_cubeSet_originCube_iff.mp hx i
      have hval : ((1 - del) • x) i = (1 - del) * x i := rfl
      rw [hval, Real.dist_eq]
      have habs : |x i - (1 - del) * x i| = del * |x i| := by
        rw [show x i - (1 - del) * x i = del * x i from by ring, abs_mul,
          abs_of_pos hdel0]
      rw [habs]
      have hxabs : |x i| ≤ (1 / 2) * (3 : ℝ) ^ ell :=
        abs_le.mpr ⟨by linarith only [hxi.1], by linarith only [hxi.2]⟩
      exact mul_le_mul_of_nonneg_left hxabs hdel0.le
    have hlt : del * ((1 / 2) * (3 : ℝ) ^ ell) < eps := by
      have hstep : del * ((1 / 2) * (3 : ℝ) ^ ell)
          ≤ (eps / ((3 : ℝ) ^ ell + 1)) * ((1 / 2) * (3 : ℝ) ^ ell) :=
        mul_le_mul_of_nonneg_right hdelbd (by positivity)
      have hfrac : (eps / ((3 : ℝ) ^ ell + 1)) * ((1 / 2) * (3 : ℝ) ^ ell)
          < eps := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        have hcmp : (1 / 2 : ℝ) * (3 : ℝ) ^ ell < (3 : ℝ) ^ ell + 1 := by
          linarith only [hf]
        have hstep := mul_lt_mul_of_pos_left hcmp heps
        linarith only [hstep]
      linarith only [hstep, hfrac]
    linarith only [hbound, hlt]

private theorem le_of_mem_cubeSet_of_continuous {ell : ℤ} {F : Vec d → ℝ}
    (hF : Continuous F) {C : ℝ}
    (h : ∀ y ∈ openCubeSet (originCube d ell), F y ≤ C)
    {x : Vec d} (hx : x ∈ cubeSet (originCube d ell)) : F x ≤ C := by
  have hclosed : IsClosed {y : Vec d | F y ≤ C} := isClosed_le hF continuous_const
  have hsub : closure (openCubeSet (originCube d ell)) ⊆ {y : Vec d | F y ≤ C} :=
    hclosed.closure_subset_iff.mpr fun y hy => h y hy
  exact hsub (mem_closure_openCubeSet_originCube hx)

/-- The second-derivative gauge of a shell dominates the exact induced norm at
every point of the **half-open** triadic cube, not only the open one: the
frozen shell carrier stores a continuous second derivative. -/
theorem matrixSecondDerivativeNorm_secondDeriv_le_localCubeSecondDerivNorm_cubeSet
    (ell : ℤ) (j : ShellField d) {x : Vec d} (hx : x ∈ cubeSet (originCube d ell)) :
    ShellField.matrixSecondDerivativeNorm (ShellField.secondDeriv j x) ≤
      Provider.Stream.localCubeSecondDerivNorm ell j :=
  le_of_mem_cubeSet_of_continuous
    (ShellField.matrixSecondDerivativeNorm_continuous.comp
      (ShellField.secondDeriv j).continuous)
    (fun _y hy =>
      Provider.Stream.matrixSecondDerivativeNorm_secondDeriv_le_localCubeSecondDerivNorm
        ell j hy)
    hx

/-- The first-derivative gauge, at every point of the half-open cube. -/
theorem matrixDerivativeNorm_deriv_le_localCubeDerivNorm_cubeSet
    (ell : ℤ) (j : ShellField d) {x : Vec d} (hx : x ∈ cubeSet (originCube d ell)) :
    ShellField.matrixDerivativeNorm (ShellField.deriv j x) ≤
      Provider.Stream.localCubeDerivNorm ell j :=
  le_of_mem_cubeSet_of_continuous
    (ShellField.matrixDerivativeNorm_continuous.comp (ShellField.deriv j).continuous)
    (fun _y hy =>
      Provider.Stream.matrixDerivativeNorm_deriv_le_localCubeDerivNorm ell j hy)
    hx

private theorem matrixOperatorNorm_le_localCubeControl_openCubeSet (ell : ℤ)
    (j : ShellField d) {x : Vec d} (hx : x ∈ openCubeSet (originCube d ell)) :
    Ch02.matrixOperatorNorm (j x) ≤ Cutoff.localCubeControl ell j :=
  Cutoff.matrixOperatorNorm_le_localCubeControl ell j hx

/-- The value gauge, at every point of the half-open cube. -/
theorem matrixOperatorNorm_le_localCubeControl_cubeSet (ell : ℤ) (j : ShellField d)
    {x : Vec d} (hx : x ∈ cubeSet (originCube d ell)) :
    Ch02.matrixOperatorNorm (j x) ≤ Cutoff.localCubeControl ell j :=
  le_of_mem_cubeSet_of_continuous
    (ShellField.continuous_matrixOperatorNorm.comp j.1.1.continuous)
    (fun _y hy => matrixOperatorNorm_le_localCubeControl_openCubeSet ell j hy) hx

/-- A nonnegative pointwise bound controls the value gauge. -/
theorem localCubeControl_le_of_forall (ell : ℤ) (j : ShellField d) {C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ x ∈ openCubeSet (originCube d ell),
      Ch02.matrixOperatorNorm (j x) ≤ C) :
    Cutoff.localCubeControl ell j ≤ C :=
  Cutoff.localCubeControl_le_of_pointwise ell j C h hC

private theorem matrixOperatorNorm_add_le (A B : Mat d) :
    Ch02.matrixOperatorNorm (A + B)
      ≤ Ch02.matrixOperatorNorm A + Ch02.matrixOperatorNorm B := by
  have h := Ch02.matrixOperatorNorm_le_matrixOperatorNorm_add_matrixOperatorNorm_sub
    (A + B) A
  rwa [add_sub_cancel_left] at h

private theorem matrixOperatorNorm_sum_le {iota : Type*} (s : Finset iota)
    (A : iota → Mat d) :
    Ch02.matrixOperatorNorm (∑ i ∈ s, A i)
      ≤ ∑ i ∈ s, Ch02.matrixOperatorNorm (A i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      rw [Finset.sum_cons, Finset.sum_cons]
      exact le_trans (matrixOperatorNorm_add_le _ _)
        (add_le_add le_rfl ih)

/-- **The layer-sum triangle inequality at the value gauge**, the `L^infinity`
analogue of `Support.shellW1InfGradNorm_translate_sum_le`. -/
theorem localCubeControl_sum_le {iota : Type*} (ell : ℤ) (s : Finset iota)
    (f : iota → ShellField d) :
    Cutoff.localCubeControl ell (ShellField.sum s f)
      ≤ ∑ i ∈ s, Cutoff.localCubeControl ell (f i) := by
  refine localCubeControl_le_of_forall ell _
    (Finset.sum_nonneg fun i _ => Cutoff.localCubeControl_nonneg ell (f i)) ?_
  intro x hx
  have hval : (ShellField.sum s f) x = ∑ i ∈ s, (f i) x := rfl
  rw [hval]
  refine le_trans (matrixOperatorNorm_sum_le s fun i => (f i) x) ?_
  exact Finset.sum_le_sum fun i _ =>
    matrixOperatorNorm_le_localCubeControl_openCubeSet ell (f i) hx

/-! ## Part C -- the annulus cube stays inside the observation cube -/

/-- **`z + cu_n` is contained in `cu_m`** for every scale-`n` lattice point `z`
of `cu_m` and every `n <= m`.  The containment is in the *open* cube on both
sides: `z` is a lattice point, so `|z_i| <= (3^m - 3^n)/2` exactly. -/
theorem translate_openCubeSet_originCube_subset {n m : ℤ} (hnm : n ≤ m)
    {v : Fin d → ℤ} (hv : v ∈ Support.latticeCubeSet d n m) {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d n)) :
    x + Support.triadicLatticePoint n v ∈ openCubeSet (originCube d m) := by
  have hA : (0 : ℝ) < (3 : ℝ) ^ n := by positivity
  have hpow := three_zpow_add_toNat hnm
  have hvi := (mem_latticeCubeSet_iff hnm v).mp hv
  obtain ⟨jj, hjj⟩ := three_pow_odd_int (m - n).toNat
  refine mem_openCubeSet_originCube_iff.mpr ?_
  intro i
  have hvZ : 2 * |v i| ≤ (3 : ℤ) ^ ((m - n).toNat : ℕ) - 1 := by
    have := hvi i
    omega
  have hcast : ((2 * |v i| : ℤ) : ℝ) ≤ (((3 : ℤ) ^ ((m - n).toNat : ℕ) - 1 : ℤ) : ℝ) := by
    exact_mod_cast hvZ
  have hcast2 : (2 : ℝ) * |((v i : ℤ) : ℝ)| ≤ (3 : ℝ) ^ ((m - n).toNat : ℕ) - 1 := by
    push_cast at hcast
    exact hcast
  have hzabs : |(3 : ℝ) ^ n * ((v i : ℤ) : ℝ)|
      ≤ (1 / 2) * ((3 : ℝ) ^ n * (3 : ℝ) ^ ((m - n).toNat : ℕ)) - (1 / 2) * (3 : ℝ) ^ n := by
    rw [abs_mul, abs_of_pos hA]
    have hstep := mul_le_mul_of_nonneg_left hcast2
      (by positivity : (0 : ℝ) ≤ (3 : ℝ) ^ n / 2)
    linarith only [hstep]
  have hxi := mem_openCubeSet_originCube_iff.mp hx i
  have hval : (x + Support.triadicLatticePoint n v) i
      = x i + (3 : ℝ) ^ n * ((v i : ℤ) : ℝ) := rfl
  rw [hval, hpow]
  rcases abs_le.mp hzabs with ⟨hz1, hz2⟩
  constructor
  · linarith only [hxi.1, hz1]
  · linarith only [hxi.2, hz2]

/-! ## Part D -- the lattice-max enlargement at the two shell gauges -/

/-- `DisplaySlots.shellW2InfLatticeMax`, read at an abstract shell field: the
maximum of the `W^{2,infinity}` gauge over `3^k Z^d ∩ cu_m`. -/
def shellW2InfLatticeMaxOf (m k : ℤ) (j : ShellField d) : ℝ :=
  Proportion.fmax (latticeCubeFinset d k m)
    fun w => Support.shellW2InfNormAt (Support.triadicLatticePoint k w) k j

theorem shellW2InfLatticeMaxOf_nonneg (m k : ℤ) (j : ShellField d) :
    0 ≤ shellW2InfLatticeMaxOf m k j :=
  Proportion.fmax_nonneg _ _

/-- **The enlargement at the second-derivative leg.** -/
theorem localCubeSecondDerivNorm_translate_le_shellW2InfLatticeMaxOf
    {n k m : ℤ} (hnm : n ≤ m) (hkm : k ≤ m) {v : Fin d → ℤ}
    (hv : v ∈ Support.latticeCubeSet d n m) (j : ShellField d) :
    Provider.Stream.localCubeSecondDerivNorm n
        (ShellField.translate (Support.triadicLatticePoint n v) j)
      ≤ shellW2InfLatticeMaxOf m k j := by
  refine Provider.Stream.localCubeSecondDerivNorm_le_of_forall n _
    (shellW2InfLatticeMaxOf_nonneg m k j) ?_
  intro x hx
  obtain ⟨w, hw, hmem⟩ :=
    exists_mem_latticeCubeSet_sub_mem_cubeSet hkm
      (translate_openCubeSet_originCube_subset hnm hv hx)
  have hshift : ShellField.matrixSecondDerivativeNorm
      (ShellField.secondDeriv
        (ShellField.translate (Support.triadicLatticePoint n v) j) x)
      = ShellField.matrixSecondDerivativeNorm
        (ShellField.secondDeriv
          (ShellField.translate (Support.triadicLatticePoint k w) j)
          (x + Support.triadicLatticePoint n v - Support.triadicLatticePoint k w)) := by
    rw [ShellField.translate_secondDeriv, ShellField.translate_secondDeriv]
    congr 2
    abel
  rw [hshift]
  refine le_trans
    (matrixSecondDerivativeNorm_secondDeriv_le_localCubeSecondDerivNorm_cubeSet k _ hmem)
    ?_
  refine le_trans
    (Support.localCubeSecondDerivNorm_le_shellW1InfGradNorm k _) ?_
  exact le_trans (Support.shellW1InfGradNorm_translate_le_shellW2InfNormAt _ k j)
    (Proportion.le_fmax
      (f := fun w => Support.shellW2InfNormAt (Support.triadicLatticePoint k w) k j)
      ((mem_latticeCubeFinset_iff hkm w).mpr hw))

/-- **The enlargement at the first-derivative leg.** -/
theorem localCubeDerivNorm_translate_le_shellW2InfLatticeMaxOf
    {n k m : ℤ} (hnm : n ≤ m) (hkm : k ≤ m) {v : Fin d → ℤ}
    (hv : v ∈ Support.latticeCubeSet d n m) (j : ShellField d) :
    Provider.Stream.localCubeDerivNorm n
        (ShellField.translate (Support.triadicLatticePoint n v) j)
      ≤ (3 : ℝ) ^ k * shellW2InfLatticeMaxOf m k j := by
  have hpos : (0 : ℝ) < (3 : ℝ) ^ k := by positivity
  refine Provider.Stream.localCubeDerivNorm_le_of_forall n _
    (mul_nonneg hpos.le (shellW2InfLatticeMaxOf_nonneg m k j)) ?_
  intro x hx
  obtain ⟨w, hw, hmem⟩ :=
    exists_mem_latticeCubeSet_sub_mem_cubeSet hkm
      (translate_openCubeSet_originCube_subset hnm hv hx)
  have hshift : ShellField.matrixDerivativeNorm
      (ShellField.deriv
        (ShellField.translate (Support.triadicLatticePoint n v) j) x)
      = ShellField.matrixDerivativeNorm
        (ShellField.deriv
          (ShellField.translate (Support.triadicLatticePoint k w) j)
          (x + Support.triadicLatticePoint n v - Support.triadicLatticePoint k w)) := by
    rw [ShellField.translate_deriv, ShellField.translate_deriv]
    congr 2
    abel
  rw [hshift]
  refine le_trans
    (matrixDerivativeNorm_deriv_le_localCubeDerivNorm_cubeSet k _ hmem) ?_
  have hleg : (3 : ℝ) ^ (-k) *
      Provider.Stream.localCubeDerivNorm k
        (ShellField.translate (Support.triadicLatticePoint k w) j)
      ≤ shellW2InfLatticeMaxOf m k j := by
    refine le_trans
      (Support.three_zpow_mul_localCubeDerivNorm_le_shellW1InfGradNorm k _) ?_
    exact le_trans (Support.shellW1InfGradNorm_translate_le_shellW2InfNormAt _ k j)
      (Proportion.le_fmax
        (f := fun w => Support.shellW2InfNormAt (Support.triadicLatticePoint k w) k j)
        ((mem_latticeCubeFinset_iff hkm w).mpr hw))
  have hmul := mul_le_mul_of_nonneg_left hleg hpos.le
  rw [← mul_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), add_neg_cancel, zpow_zero,
    one_mul] at hmul
  exact hmul

/-- **The enlargement at the value leg.** -/
theorem localCubeControl_translate_le_shellW2InfLatticeMaxOf
    {n k m : ℤ} (hnm : n ≤ m) (hkm : k ≤ m) {v : Fin d → ℤ}
    (hv : v ∈ Support.latticeCubeSet d n m) (j : ShellField d) :
    Cutoff.localCubeControl n
        (ShellField.translate (Support.triadicLatticePoint n v) j)
      ≤ (3 : ℝ) ^ (2 * k) * shellW2InfLatticeMaxOf m k j := by
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (2 * k) := by positivity
  refine localCubeControl_le_of_forall n _
    (mul_nonneg hpos.le (shellW2InfLatticeMaxOf_nonneg m k j)) ?_
  intro x hx
  obtain ⟨w, hw, hmem⟩ :=
    exists_mem_latticeCubeSet_sub_mem_cubeSet hkm
      (translate_openCubeSet_originCube_subset hnm hv hx)
  have hshift : (ShellField.translate (Support.triadicLatticePoint n v) j) x
      = (ShellField.translate (Support.triadicLatticePoint k w) j)
          (x + Support.triadicLatticePoint n v - Support.triadicLatticePoint k w) := by
    rw [ShellField.translate_apply, ShellField.translate_apply]
    congr 1
    abel
  rw [hshift]
  refine le_trans (matrixOperatorNorm_le_localCubeControl_cubeSet k _ hmem) ?_
  have hleg : (3 : ℝ) ^ (-2 * k) *
      Cutoff.localCubeControl k
        (ShellField.translate (Support.triadicLatticePoint k w) j)
      ≤ shellW2InfLatticeMaxOf m k j :=
    le_trans (Support.three_zpow_mul_localCubeControl_le_shellW2InfNormAt _ k j)
      (Proportion.le_fmax
        (f := fun w => Support.shellW2InfNormAt (Support.triadicLatticePoint k w) k j)
        ((mem_latticeCubeFinset_iff hkm w).mpr hw))
  have hmul := mul_le_mul_of_nonneg_left hleg hpos.le
  have hexp : 2 * k + -2 * k = (0 : ℤ) := by ring
  rw [← mul_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), hexp, zpow_zero,
    one_mul] at hmul
  exact hmul

/-- **The lattice-max enlargement of the `W^{1,infinity}` shell gauge**: the gauge
of a shell on the annulus cube `z + cu_n` is at most `max(1, 3^{k-n})` times
the maximum of its `W^{2,infinity}` gauge over the scale-`k` lattice cubes of
`cu_m`, for every `k <= m`. -/
theorem shellW1InfGradNorm_translate_le_shellW2InfLatticeMaxOf
    {n k m : ℤ} (hnm : n ≤ m) (hkm : k ≤ m) {v : Fin d → ℤ}
    (hv : v ∈ Support.latticeCubeSet d n m) (j : ShellField d) :
    Support.shellW1InfGradNorm n
        (ShellField.translate (Support.triadicLatticePoint n v) j)
      ≤ max 1 ((3 : ℝ) ^ (k - n)) * shellW2InfLatticeMaxOf m k j := by
  have hL0 : 0 ≤ shellW2InfLatticeMaxOf m k j := shellW2InfLatticeMaxOf_nonneg m k j
  have hone : (1 : ℝ) ≤ max 1 ((3 : ℝ) ^ (k - n)) := le_max_left _ _
  have htwo : (3 : ℝ) ^ (k - n) ≤ max 1 ((3 : ℝ) ^ (k - n)) := le_max_right _ _
  rw [Support.shellW1InfGradNorm_def]
  refine max_le ?_ ?_
  · refine le_trans
      (localCubeSecondDerivNorm_translate_le_shellW2InfLatticeMaxOf hnm hkm hv j) ?_
    calc shellW2InfLatticeMaxOf m k j = 1 * shellW2InfLatticeMaxOf m k j := (one_mul _).symm
      _ ≤ max 1 ((3 : ℝ) ^ (k - n)) * shellW2InfLatticeMaxOf m k j :=
          mul_le_mul_of_nonneg_right hone hL0
  · have hpos : (0 : ℝ) < (3 : ℝ) ^ (-n) := by positivity
    have hstep := mul_le_mul_of_nonneg_left
      (localCubeDerivNorm_translate_le_shellW2InfLatticeMaxOf hnm hkm hv j) hpos.le
    have hid : (3 : ℝ) ^ (-n) * ((3 : ℝ) ^ k * shellW2InfLatticeMaxOf m k j)
        = (3 : ℝ) ^ (k - n) * shellW2InfLatticeMaxOf m k j := by
      rw [← mul_assoc, ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      congr 2
      ring
    rw [hid] at hstep
    exact hstep.trans (mul_le_mul_of_nonneg_right htwo hL0)

end

end Algsuperdiff.Section4.Provider.Annular
