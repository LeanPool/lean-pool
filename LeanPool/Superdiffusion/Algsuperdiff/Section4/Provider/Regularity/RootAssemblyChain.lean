/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepNineOffGridIndicator
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenEndAssembly

/-!
# RootAssemblyChain

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` root assembly, part two: the carrier bridge and the bracket

## The gap this module closes

The frozen root, by contrast, states `e.energy.density.estimate` in `ℝ≥0∞`:

```text
  ENNReal.ofReal (√ν) * eLpNorm (fun y => √(vecNormSq (u.grad y))) 2
      (normalizedVolumeMeasureOn ((x+□_n) ∩ □_m))
    ≤ ENNReal.ofReal (C·3^{(1-α)(m-n)}) *
        (ENNReal.ofReal (√ν) * eLpNorm … (normalizedVolumeMeasureOn □_m)
          + ENNReal.ofReal (√σ_m⁻¹·3^{m/2}·K_g)
          + ENNReal.ofReal (√σ_m·3^{m/2}·K_h)) .
```

Two things separate the two ends, and N is an estimate:

1. **The carrier.**  `Support.normalizedL2On W f` is the `toReal` of `eLpNorm f
   2 (normalizedVolumeMeasureOn W)` (the proved dictionary
   `Support.normalizedL2On_eq_toReal_eLpNorm_normalizedVolumeMeasureOn`), so a
   real inequality lifts to the `ℝ≥0∞` one exactly when the `eLpNorm` is
   finite.  §1 proves the finiteness from the `H¹` datum the root's own binders
   carry and §2 performs the lift into the root's three-leg and two-leg bracket
   shapes.

2. **The bracket.**  The chain's output carries two powers of three
   (`3^{(1-α)(m-n)}` on the oscillation half and `3^{(3/4)(1-α)(m-n)}` on the
   data half) and its own data scalars `dataG`, `dataM`; the root prints ONE
   power and the two seminorm legs `√σ_m⁻¹·3^{m/2}K_g`, `√σ_m·3^{m/2}K_h`.
   §3 collapses the former into the latter.  The collapse is pure arithmetic:
   `3^{3E/4} ≤ 3^E` at `E ≥ 0` and two DOMINATION hypotheses (`dataG` and
   `dataM` are `K_g`-legs), each of which is a proved conversion, not a new
   estimate.

§4 composes §2 and §3 with `energyDensityEstimate_offGrid_pair` and produces
the frozen root's two-clause conclusion at an arbitrary centre `x ∈ □_m`.

## References

* ABK26, `t.regularity`, (`e.energy.density.estimate`), 12203.
* `Algsuperdiff/Section4/Support/NormalizedL2.lean` (the dictionary).
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Provider.ExcessDecay
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Finiteness of the normalized `L²` norm -/

/-- The normalized-measure `eLpNorm` in terms of the restricted one. -/
theorem eLpNormTwo_normalizedVolumeMeasureOn_eq_smul (W : Set (Vec d)) (f : Vec d → ℝ) :
    eLpNorm f 2 (Support.normalizedVolumeMeasureOn W)
      = (volume W)⁻¹ ^ ((1 : ℝ) / 2) * eLpNorm f 2 (volume.restrict W) := by
  have hhalf : ((1 : ℝ≥0∞) / 2).toReal = 1 / 2 := by
    rw [ENNReal.toReal_div]
    norm_num
  by_cases hWtop : volume W = ⊤
  · simp [Support.normalizedVolumeMeasureOn_def, hWtop]
  rw [Support.normalizedVolumeMeasureOn_def,
    eLpNorm_smul_measure_of_ne_zero (ENNReal.inv_ne_zero.2 hWtop) f 2, smul_eq_mul, hhalf]

/-- **The normalized `L²` norm is finite** on a window of nonzero volume carrying
an `L²` datum. -/
theorem eLpNormTwo_normalizedVolumeMeasureOn_ne_top {W : Set (Vec d)} {f : Vec d → ℝ}
    (hW0 : volume W ≠ 0) (hf : MemLp f 2 (volume.restrict W)) :
    eLpNorm f 2 (Support.normalizedVolumeMeasureOn W) ≠ ⊤ := by
  rw [eLpNormTwo_normalizedVolumeMeasureOn_eq_smul W f]
  refine ENNReal.mul_ne_top ?_ hf.eLpNorm_ne_top
  exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.inv_ne_top.mpr hW0)

/-- **The bridge.**  On a window of nonzero finite volume carrying an `L²` datum,
the frozen root's `ℝ≥0∞` quantity is the `ENNReal.ofReal` of the proved chain's real
quantity. -/
theorem eLpNormTwo_eq_ofReal_normalizedL2On {W : Set (Vec d)} {f : Vec d → ℝ}
    (hW0 : volume W ≠ 0) (hWtop : volume W ≠ ⊤) (hf : MemLp f 2 (volume.restrict W)) :
    eLpNorm f 2 (Support.normalizedVolumeMeasureOn W)
      = ENNReal.ofReal (Support.normalizedL2On W f) := by
  rw [Support.normalizedL2On_eq_toReal_eLpNorm_normalizedVolumeMeasureOn
      (pos_iff_ne_zero.mpr hW0) hWtop hf,
    ENNReal.ofReal_toReal (eLpNormTwo_normalizedVolumeMeasureOn_ne_top hW0 hf)]

/-! ## 2. The lift of a real display into the root's bracket -/

/-- **The three-leg lift.**  A real `e.energy.density.estimate` display becomes the
frozen root's `ℝ≥0∞` display, with the bracket in the root's own shape (the
`√ν`-weighted `□_m` leg plus two `ENNReal.ofReal` data legs). -/
theorem energyDensityDisplay_ofReal_threeLeg {W Wm : Set (Vec d)} {f : Vec d → ℝ}
    {nu Cpre A B : ℝ} (hCpre : 0 ≤ Cpre)
    (hW0 : volume W ≠ 0) (hWtop : volume W ≠ ⊤) (hfW : MemLp f 2 (volume.restrict W))
    (hM0 : volume Wm ≠ 0) (hMtop : volume Wm ≠ ⊤)
    (hfM : MemLp f 2 (volume.restrict Wm))
    (h : Real.sqrt nu * Support.normalizedL2On W f
      ≤ Cpre * (Real.sqrt nu * Support.normalizedL2On Wm f + A + B)) :
    ENNReal.ofReal (Real.sqrt nu) * eLpNorm f 2 (Support.normalizedVolumeMeasureOn W)
      ≤ ENNReal.ofReal Cpre *
        (ENNReal.ofReal (Real.sqrt nu) *
            eLpNorm f 2 (Support.normalizedVolumeMeasureOn Wm)
          + ENNReal.ofReal A + ENNReal.ofReal B) := by
  have hsq : (0 : ℝ) ≤ Real.sqrt nu := Real.sqrt_nonneg nu
  have hstep : ENNReal.ofReal (Real.sqrt nu * Support.normalizedL2On W f)
      ≤ ENNReal.ofReal
        (Cpre * (Real.sqrt nu * Support.normalizedL2On Wm f + A + B)) :=
    ENNReal.ofReal_le_ofReal h
  rw [eLpNormTwo_eq_ofReal_normalizedL2On hW0 hWtop hfW,
    eLpNormTwo_eq_ofReal_normalizedL2On hM0 hMtop hfM,
    ← ENNReal.ofReal_mul hsq, ← ENNReal.ofReal_mul hsq]
  refine le_trans hstep ?_
  rw [ENNReal.ofReal_mul hCpre]
  refine mul_le_mul' (le_refl (ENNReal.ofReal Cpre)) ?_
  calc ENNReal.ofReal (Real.sqrt nu * Support.normalizedL2On Wm f + A + B)
      ≤ ENNReal.ofReal (Real.sqrt nu * Support.normalizedL2On Wm f + A) +
          ENNReal.ofReal B := ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal (Real.sqrt nu * Support.normalizedL2On Wm f) +
          ENNReal.ofReal A + ENNReal.ofReal B :=
        add_le_add ENNReal.ofReal_add_le (le_refl (ENNReal.ofReal B))

/-- **The two-leg lift** — the frozen root's boundary-leg-free clause. -/
theorem energyDensityDisplay_ofReal_twoLeg {W Wm : Set (Vec d)} {f : Vec d → ℝ}
    {nu Cpre A : ℝ} (hCpre : 0 ≤ Cpre)
    (hW0 : volume W ≠ 0) (hWtop : volume W ≠ ⊤) (hfW : MemLp f 2 (volume.restrict W))
    (hM0 : volume Wm ≠ 0) (hMtop : volume Wm ≠ ⊤)
    (hfM : MemLp f 2 (volume.restrict Wm))
    (h : Real.sqrt nu * Support.normalizedL2On W f
      ≤ Cpre * (Real.sqrt nu * Support.normalizedL2On Wm f + A)) :
    ENNReal.ofReal (Real.sqrt nu) * eLpNorm f 2 (Support.normalizedVolumeMeasureOn W)
      ≤ ENNReal.ofReal Cpre *
        (ENNReal.ofReal (Real.sqrt nu) *
            eLpNorm f 2 (Support.normalizedVolumeMeasureOn Wm)
          + ENNReal.ofReal A) := by
  have hsq : (0 : ℝ) ≤ Real.sqrt nu := Real.sqrt_nonneg nu
  have hstep : ENNReal.ofReal (Real.sqrt nu * Support.normalizedL2On W f)
      ≤ ENNReal.ofReal (Cpre * (Real.sqrt nu * Support.normalizedL2On Wm f + A)) :=
    ENNReal.ofReal_le_ofReal h
  rw [eLpNormTwo_eq_ofReal_normalizedL2On hW0 hWtop hfW,
    eLpNormTwo_eq_ofReal_normalizedL2On hM0 hMtop hfM,
    ← ENNReal.ofReal_mul hsq, ← ENNReal.ofReal_mul hsq]
  refine le_trans hstep ?_
  rw [ENNReal.ofReal_mul hCpre]
  exact mul_le_mul' (le_refl (ENNReal.ofReal Cpre)) ENNReal.ofReal_add_le

/-! ## 3. The bracket collapse -/

/-- `3^{(3/4)E} ≤ 3^E` at `E ≥ 0`. -/
theorem rpow_three_threeQuarter_le {E : ℝ} (hE : 0 ≤ E) :
    Real.rpow (3 : ℝ) (3 / 4 * E) ≤ Real.rpow (3 : ℝ) E := by
  refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
  linarith only [hE]

/-! ## 4. Volume data of the two windows -/

/-- The volume of `□_m` is nonzero. -/
theorem volume_openCubeSet_originCube_ne_zero (d : ℕ) (m : ℤ) :
    volume (openCubeSet (originCube d m)) ≠ 0 := by
  rw [volume_openCubeSet_originCube_eq]
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  exact pow_pos (zpow_pos (by norm_num) m) d

/-- The volume of `□_m` is finite. -/
theorem volume_openCubeSet_originCube_ne_top (d : ℕ) (m : ℤ) :
    volume (openCubeSet (originCube d m)) ≠ ⊤ := by
  rw [volume_openCubeSet_originCube_eq]
  exact ENNReal.ofReal_ne_top

/-- The lattice window of the off-grid transfer has nonzero volume. -/
theorem volume_offGridWindow_ne_zero {x : Vec d} {m n : ℤ}
    (hx : x ∈ openCubeSet (originCube d m)) (hnm : n ≤ m) :
    volume (truncatedWindow (offGridCentre n x) m (n + 1)) ≠ 0 := by
  have hlow := volume_truncatedWindow_ge (x := x) (m := m) (k := n) hx hnm
  have hmono : volume (truncatedWindow x m n) ≤
      volume (truncatedWindow (offGridCentre n x) m (n + 1)) :=
    measure_mono (truncatedWindow_subset_offGrid n m x)
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal (((3 : ℝ) ^ (n - 1)) ^ d) := by
    simp only [ENNReal.ofReal_pos]
    exact pow_pos (zpow_pos (by norm_num) (n - 1)) d
  exact ne_of_gt (lt_of_lt_of_le hpos (le_trans hlow hmono))

/-- The lattice window of the off-grid transfer has finite volume. -/
theorem volume_offGridWindow_ne_top (x : Vec d) (m n : ℤ) :
    volume (truncatedWindow (offGridCentre n x) m (n + 1)) ≠ ⊤ :=
  ne_of_lt (lt_of_le_of_lt (volume_truncatedWindow_le (offGridCentre n x) m (n + 1))
    ENNReal.ofReal_lt_top)

/-- The `L²` datum on `□_m` restricts to any truncated window. -/
theorem memLp_truncatedWindow_of_cube {f : Vec d → ℝ} {m : ℤ} (c : Vec d) (k : ℤ)
    (hf : MemLp f 2 (volume.restrict (openCubeSet (originCube d m)))) :
    MemLp f 2 (volume.restrict (truncatedWindow c m k)) :=
  hf.mono_measure (Measure.restrict_mono (Set.inter_subset_right) le_rfl)

/-! ## 4b. The `L²` datum of the displayed function -/

/-- The Euclidean length is a continuous function of the vector.  Re-derived
here: the sibling `sqrt_vecNormSq_le_sqrt_dim_mul_norm` lives inside
`BoundaryGradH`, which this file does not import. -/
private theorem continuous_sqrt_vecNormSq :
    Continuous (fun v : Vec d => Real.sqrt (vecNormSq v)) := by
  have hc : Continuous (fun v : Vec d => vecNormSq v) := by
    unfold vecNormSq vecDot
    fun_prop
  exact Real.continuous_sqrt.comp hc

/-- The Euclidean length is at most `√d` times the ambient (sup) norm.  Re-derived
here (see `continuous_sqrt_vecNormSq`). -/
private theorem sqrt_vecNormSq_le_dim (v : Vec d) :
    Real.sqrt (vecNormSq v) ≤ Real.sqrt (d : ℝ) * ‖v‖ := by
  have hcoord : ∀ i : Fin d, v i * v i ≤ ‖v‖ * ‖v‖ := by
    intro i
    have h1 : |v i| ≤ ‖v‖ := by
      have h := norm_le_pi_norm v i
      rwa [Real.norm_eq_abs] at h
    have h3 : v i * v i = |v i| * |v i| := (abs_mul_abs_self (v i)).symm
    rw [h3]
    exact mul_le_mul h1 h1 (abs_nonneg _) (norm_nonneg v)
  have hsum : vecNormSq v ≤ (d : ℝ) * (‖v‖ * ‖v‖) := by
    rw [vecNormSq, vecDot]
    calc ∑ i : Fin d, v i * v i ≤ ∑ _i : Fin d, ‖v‖ * ‖v‖ :=
          Finset.sum_le_sum fun i _ => hcoord i
      _ = (d : ℝ) * (‖v‖ * ‖v‖) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc Real.sqrt (vecNormSq v) ≤ Real.sqrt ((d : ℝ) * (‖v‖ * ‖v‖)) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt (d : ℝ) * ‖v‖ := by
        rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_mul_self (norm_nonneg v)]

/-- **The displayed function is `L²`.**  The frozen root's left-hand side is the
`L²` norm of `|∇u|`, and its `L²` membership is a of the root's own `u:
H1Function □_m` — not an extra hypothesis. -/
theorem memLp_two_sqrt_vecNormSq_grad {U : Set (Vec d)} (u : H1Function U) :
    MemLp (fun y => Real.sqrt (vecNormSq (u.grad y))) 2 (volume.restrict U) := by
  have hgrad : MemLp u.grad 2 (volume.restrict U) := by
    simpa [MemVectorL2, volumeMeasureOn] using u.grad_memVectorL2
  have hmeas : AEStronglyMeasurable (fun y => Real.sqrt (vecNormSq (u.grad y)))
      (volume.restrict U) :=
    continuous_sqrt_vecNormSq.comp_aestronglyMeasurable hgrad.aestronglyMeasurable
  have hdom : MemLp (fun y => Real.sqrt (d : ℝ) * ‖u.grad y‖) 2 (volume.restrict U) :=
    hgrad.norm.const_mul _
  refine MemLp.of_le hdom hmeas (Filter.Eventually.of_forall (fun y => ?_))
  have h1 : ‖Real.sqrt (vecNormSq (u.grad y))‖ = Real.sqrt (vecNormSq (u.grad y)) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have h2 : ‖Real.sqrt (d : ℝ) * ‖u.grad y‖‖ = Real.sqrt (d : ℝ) * ‖u.grad y‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))]
  rw [h1, h2]
  exact sqrt_vecNormSq_le_dim (u.grad y)

/-! ## 5. The frozen root's two-clause conclusion at an arbitrary centre -/

/-- **The root assembly's `ℝ`-to-root step.**

From the §4.4 chain's real display at the lattice centre `z = offGridCentre n x`
and scale `n+1` — in both the general and the boundary-leg-free form — this
produces the frozen root's two-clause conclusion at an arbitrary centre
`x ∈ □_m` and scale `n`, at the constant `3^d·C` (the off-grid transfer factor
and nothing else).

The only data beyond the root's own binders is `hfM`, the `L²` membership of
the displayed function on `□_m` — a field of the root's `u : H1Function □_m`,
not a new hypothesis. -/
theorem rootEnergyDensityPair_of_realDisplays (nu : ℝ) (f : Vec d → ℝ)
    {x : Vec d} {m n : ℤ} {C alpha A B : ℝ}
    (hx : x ∈ openCubeSet (originCube d m)) (hnm : n ≤ m) (hC : 0 ≤ C)
    (hfM : MemLp f 2 (volume.restrict (openCubeSet (originCube d m))))
    (hzfull : Real.sqrt nu *
        Support.normalizedL2On (truncatedWindow (offGridCentre n x) m (n + 1)) f
      ≤ C * Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
        (Real.sqrt nu *
          Support.normalizedL2On (openCubeSet (originCube d m)) f + A + B))
    (hzinner : offGridCentre n x ∈ openCubeSet (originCube d (m - 1)) →
      Real.sqrt nu *
          Support.normalizedL2On (truncatedWindow (offGridCentre n x) m (n + 1)) f
        ≤ C * Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) *
          (Real.sqrt nu *
            Support.normalizedL2On (openCubeSet (originCube d m)) f + A)) :
    (ENNReal.ofReal (Real.sqrt nu) *
        eLpNorm f 2 (Support.normalizedVolumeMeasureOn (truncatedWindow x m n))
      ≤ ENNReal.ofReal (((3 : ℝ) ^ d * C) *
          Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) *
        (ENNReal.ofReal (Real.sqrt nu) *
            eLpNorm f 2 (Support.normalizedVolumeMeasureOn
              (openCubeSet (originCube d m)))
          + ENNReal.ofReal A + ENNReal.ofReal B)) ∧
      (x ∈ openCubeSet (originCube d (m - 1)) →
        ENNReal.ofReal (Real.sqrt nu) *
            eLpNorm f 2 (Support.normalizedVolumeMeasureOn (truncatedWindow x m n))
          ≤ ENNReal.ofReal (((3 : ℝ) ^ d * C) *
              Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ)))) *
            (ENNReal.ofReal (Real.sqrt nu) *
                eLpNorm f 2 (Support.normalizedVolumeMeasureOn
                  (openCubeSet (originCube d m)))
              + ENNReal.ofReal A)) := by
  have hW0 := volume_offGridWindow_ne_zero hx hnm
  have hWtop := volume_offGridWindow_ne_top x m n
  have hfW := memLp_truncatedWindow_of_cube (offGridCentre n x) (n + 1) hfM
  have hM0 := volume_openCubeSet_originCube_ne_zero d m
  have hMtop := volume_openCubeSet_originCube_ne_top d m
  have hCpre : (0 : ℝ) ≤ C * Real.rpow (3 : ℝ) ((1 - alpha) * ((m : ℝ) - (n : ℝ))) :=
    mul_nonneg hC (Real.rpow_pos_of_pos (by norm_num) _).le
  refine energyDensityEstimate_offGrid_pair nu f hx hnm
    (energyDensityDisplay_ofReal_threeLeg hCpre hW0 hWtop hfW hM0 hMtop hfM
      hzfull) ?_
  intro hzin
  exact energyDensityDisplay_ofReal_twoLeg hCpre hW0 hWtop hfW hM0 hMtop hfM
    (hzinner hzin)

end

end Algsuperdiff.Section4.Provider.Regularity
