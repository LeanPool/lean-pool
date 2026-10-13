/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderResidue

/-!
# CubeSchauderCampanato

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Cube Schauder: the Campanato bound of the zero-datum solution

## The rate resolution, made explicit

Per triadic step of size `k` the two rates are

```text
  theta_k = lipschitzContractionConst d · 3^{-k}      (the contraction)
  rho_k   = √(3^{-k})                                  (the freezing gain)
```

`theta_k / rho_k = lipschitzContractionConst d · √(3^{-k}) → 0`, so the gap is
uniform as soon as `k` is large; `schauderStepSize d` is such a `k` (and `≥ 3`,
the one-step machinery's own requirement).  With the `C^{0,1/2}` interior atom
one would instead get `theta_k = C(d)·√(3^{-k}) = C(d)·rho_k` — no gap at any
`k`, the Campanato exponent strictly below `1/2` and the frozen external's
inclusive endpoint `s ≤ 1/2` unreachable.  That is why the composition is routed
through the Lipschitz atom.

At the sharp gap the Campanato bound reads, on the window family
`W_j = (x + □_j) ∩ □_m` of a point `x` of the interior half-cube `□_{m-1}`,

```text
  E(w, W_j) ≤ schauderCampanatoConst d · KG · √(3^j)     for every j ≤ m,
```

`w` the zero-datum `H¹₀(□_m)` solution of `-Δw = ∇·G` and `KG` the `C^{0,1/2}`
seminorm of `G` — the Campanato characterization of `∇w ∈ C^{0,1/2}`, with
exponent **exactly** `1/2`.

## Main results

* `exists_schauderStepSize` / `schauderStepSize` / `schauderStepSize_gap` — the
  step size and the machine-checked rate gap `theta < rho`.
* `excessDecay_oneStep_forced` — the one step for the forced equation.
* `affineExcess_initial_le` — the excess at the top scale.
* `affineExcess_le_campanato_sublattice` — the iterated bound at the scales
  `m - i·k₀`.
* `affineExcess_le_campanato` — the same at **every** scale `j ≤ m`.

## What this module does *not* do

It is the **interior** regime: the base point `x` is restricted to the interior
half-cube `□_{m-1}`, which is what makes the geometry slot `x + □_{j-2} ⊆ □_m`
of the one-step producer available at every scale.

## References

* Armstrong--Kuusi, *Elliptic Regularity* (`ellipticregularity.tex`),
  Proposition `p.Schauder.C1alpha`, displays `e.Sch1a.1`--`e.Sch1a.2`.
* ABK26; `Algsuperdiff/Frozen/External/CubeSchauder.lean`.
-/

namespace Algsuperdiff.Section4.Provider.Schauder

open MeasureTheory InnerProductSpace
open HCPolySupport
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

/-! ## 1. Two arithmetic helpers -/

/-- `√(t^i) = (√t)^i`. -/
theorem sqrt_pow_nat {t : ℝ} (ht : 0 ≤ t) (i : ℕ) :
    Real.sqrt (t ^ i) = Real.sqrt t ^ i := by
  induction i with
  | zero => simp
  | succ n ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg ht n), ih, pow_succ]

/-- The triadic scale at step `i` of the iteration factorizes. -/
theorem zpow_sub_mul_step (m : ℤ) (k i : ℕ) :
    (3 : ℝ) ^ (m - (i : ℤ) * (k : ℤ)) = (3 : ℝ) ^ m * ((3 : ℝ) ^ (-(k : ℤ))) ^ i := by
  have hne : (3 : ℝ) ≠ 0 := by norm_num
  rw [show m - (i : ℤ) * (k : ℤ) = m + (-(k : ℤ)) * (i : ℤ) by ring, zpow_add₀ hne,
    zpow_mul, zpow_natCast]

/-! ## 4. The excess at the top scale -/

/-- The constant of the top-scale excess: `9 · √((3²)^d) · C_Poincaré(d) · d`. -/
def schauderInitialConst (d : ℕ) : ℝ :=
  9 * Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) * (schauderDirichletPoincareConst d * (d : ℝ))

theorem schauderInitialConst_nonneg (d : ℕ) : 0 ≤ schauderInitialConst d :=
  mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
    (mul_nonneg (schauderDirichletPoincareConst_nonneg d) (Nat.cast_nonneg d))

/-- **The excess of the zero-datum solution at the top scale.**

`E(w, (x+□_m) ∩ □_m) ≤ schauderInitialConst d · KG · √(3^m)`.  The proof is the
freezing identity at the constant `G(0)` (a zero-trace test function does not see
a constant forcing), the sharp energy bound, the coordinate dictionary and the
Dirichlet Poincaré inequality — the same four steps as the one-step residue, run
once at the top scale. -/
theorem affineExcess_initial_le [NeZero d] (hd : d ≠ 0) {m : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m))
    (u : H10Function (openCubeSet (originCube d m)))
    {G : Vec d → Vec d} {KG : ℝ} (hKG : 0 ≤ KG)
    (hGL2 : MemVectorL2 (openCubeSet (originCube d m)) G)
    (hG : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) KG G)
    (hu : IsDivFormWeakSolutionOn (fun _ => (1 : Mat d))
      (openCubeSet (originCube d m)) u.toH1Function G) :
    affineExcess (truncatedWindow x m m) u.toFun
      ≤ schauderInitialConst d * KG * Real.sqrt ((3 : ℝ) ^ m) := by
  have hQdom : IsOpenBoundedConvexDomain (openCubeSet (originCube d m)) :=
    isOpenBoundedConvexDomain_openCubeSet _
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube d m))) :=
    hQdom.isFiniteMeasure_restrict_volume
  have hvolQ : (volume (openCubeSet (originCube d m))).toReal = ((3 : ℝ) ^ m) ^ d := by
    rw [volume_openCubeSet_toReal, cubeVolume_eq_pow_scale]
    rfl
  have hvolQpos : (0 : ℝ) < (volume (openCubeSet (originCube d m))).toReal := by
    rw [hvolQ]
    positivity
  -- the frozen equation and the sharp energy bound
  have hGc : MemVectorL2 (openCubeSet (originCube d m)) (fun y => G y - G 0) :=
    hGL2.sub (memLp_const (G 0))
  have hufroz : IsDivFormWeakSolutionOn (fun _ => (1 : Mat d))
      (openCubeSet (originCube d m)) u.toH1Function (fun y => G y - G 0) :=
    isDivFormWeakSolutionOn_sub_const hGL2 (G 0) hu
  have henergy := dirichletEnergy_le_of_isDivFormWeakSolutionOn_one hGc u hufroz
  -- the oscillation bound at the base point `0`
  have h0 : (0 : Vec d) ∈ openCubeSet (originCube d m) :=
    zero_mem_openCubeSet_originCube m
  have hint : IntegrableOn (fun y => vecNormSq (G y - G 0))
      (openCubeSet (originCube d m)) volume :=
    integrableOn_vecNormSq_of_memVectorL2 hGc
  have hbd : ∀ y ∈ openCubeSet (originCube d m),
      vecNormSq (G y - G 0) ≤ (d : ℝ) * (KG ^ 2 * (3 : ℝ) ^ m) := by
    intro y hy
    have h := vecNormSq_sub_le_of_holderSeminormBoundOn_openCubeSet
      (Q := originCube d m) hKG hG h0 hy
    have hscale : cubeScaleFactor (originCube d m) = (3 : ℝ) ^ m := rfl
    rwa [hscale] at h
  have hconst : IntegrableOn (fun _ : Vec d => (d : ℝ) * (KG ^ 2 * (3 : ℝ) ^ m))
      (openCubeSet (originCube d m)) volume := integrable_const _
  have hmono := setIntegral_mono_on hint hconst (measurableSet_openCubeSet _) hbd
  rw [setIntegral_const, smul_eq_mul, mul_comm] at hmono
  have hE := henergy.trans hmono
  have hsum := sum_toReal_eLpNorm_grad_le_of_dirichletEnergy_le u.toH1Function hE
  have hsum' : ∑ i : Fin d,
      (eLpNorm (fun y => u.toH1Function.grad y i) 2
        (volume.restrict (openCubeSet (originCube d m)))).toReal
      ≤ (d : ℝ) * KG *
        Real.sqrt ((3 : ℝ) ^ m * (volume (openCubeSet (originCube d m))).toReal) := by
    refine hsum.trans (le_of_eq ?_)
    exact sqrt_freezing_budget (d : ℝ) KG ((3 : ℝ) ^ m)
      ((volume (openCubeSet (originCube d m))).toReal) (Nat.cast_nonneg d) hKG
  -- the Dirichlet Poincaré at the inscribing cube `0 + □_m`
  have hinscribe : ∀ y ∈ openCubeSet (originCube d m), ∀ j : Fin d,
      (0 : Vec d) j - (1 / 2 : ℝ) * (3 : ℝ) ^ m < y j ∧
        y j < (0 : Vec d) j + (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
    intro y hy j
    have h := mem_openCubeSet_originCube_iff.1 hy j
    exact ⟨by simpa using by linarith only [h.1], by simpa using by linarith only [h.2]⟩
  have hpoin := eLpNorm_le_schauderDirichletPoincare (measurableSet_openCubeSet _) 0 m
    hinscribe u
  have hpoin' : (eLpNorm u.toFun 2 (volume.restrict (openCubeSet (originCube d m)))).toReal
      ≤ schauderDirichletPoincareConst d * (3 : ℝ) ^ m *
        ((d : ℝ) * KG *
          Real.sqrt ((3 : ℝ) ^ m * (volume (openCubeSet (originCube d m))).toReal)) := by
    refine hpoin.trans (mul_le_mul_of_nonneg_left hsum' ?_)
    exact mul_nonneg (schauderDirichletPoincareConst_nonneg d) (zpow_pos (by norm_num) m).le
  have huQ : MemLp u.toFun 2 (volume.restrict (openCubeSet (originCube d m))) := by
    simpa only [volumeMeasureOn] using u.toH1Function.memL2
  have hsqrtV : Real.sqrt ((3 : ℝ) ^ m * (volume (openCubeSet (originCube d m))).toReal)
      = Real.sqrt ((3 : ℝ) ^ m) *
        Real.sqrt ((volume (openCubeSet (originCube d m))).toReal) :=
    Real.sqrt_mul (zpow_pos (by norm_num) m).le _
  have hnormQ : normalizedL2On (openCubeSet (originCube d m)) u.toFun
      ≤ schauderDirichletPoincareConst d * (d : ℝ) * KG *
        ((3 : ℝ) ^ m * Real.sqrt ((3 : ℝ) ^ m)) := by
    rw [normalizedL2On_eq_toReal_eLpNorm_div huQ, div_le_iff₀ (Real.sqrt_pos.2 hvolQpos)]
    refine hpoin'.trans (le_of_eq ?_)
    rw [hsqrtV]
    ring
  -- transfer to the truncated window at the top scale
  have hWQ : truncatedWindow x m m ⊆ openCubeSet (originCube d m) :=
    truncatedWindow_subset_domain x m m
  have hWpos : (0 : ℝ) < (volume (truncatedWindow x m m)).toReal :=
    volume_toReal_truncatedWindow_pos x hx (by omega)
  have hratio : (volume (openCubeSet (originCube d m))).toReal /
      (volume (truncatedWindow x m m)).toReal ≤ ((3 : ℝ) ^ (2 : ℤ)) ^ d := by
    have hlo : ((3 : ℝ) ^ (m - 2)) ^ d ≤ (volume (truncatedWindow x m m)).toReal :=
      (volume_toReal_truncatedWindow_bounds x hx (by omega)).1
    rw [div_le_iff₀ hWpos, hvolQ]
    refine le_trans (le_of_eq ?_) (mul_le_mul_of_nonneg_left hlo (by positivity))
    rw [← mul_pow]
    congr 1
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    ring
  have hintQ : IntegrableOn (fun y => u.toFun y ^ 2) (openCubeSet (originCube d m)) :=
    (memLp_two_iff_integrable_sq huQ.aestronglyMeasurable).1 huQ
  have htrans : normalizedL2On (truncatedWindow x m m) u.toFun
      ≤ Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
        normalizedL2On (openCubeSet (originCube d m)) u.toFun := by
    refine (normalizedL2On_le_of_subset hWQ hvolQpos hWpos hintQ).trans ?_
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hratio) (normalizedL2On_nonneg _ _)
  -- the excess against the zero competitor
  have hzero : affineExcessRaw (truncatedWindow x m m) u.toFun
      ≤ normalizedL2On (truncatedWindow x m m) u.toFun := by
    have h := affineExcessRaw_le_normalizedL2On_sub_const (truncatedWindow x m m) u.toFun 0
    have hfun : (fun y => u.toFun y - 0) = u.toFun := by funext y; ring
    rwa [hfun] at h
  obtain ⟨_, hnorm⟩ := rpow_volume_truncatedWindow_bounds hd x hx (by omega : m - 1 ≤ m)
  have hchain : affineExcess (truncatedWindow x m m) u.toFun
      ≤ 9 * (3 : ℝ) ^ (-m) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
        (schauderDirichletPoincareConst d * (d : ℝ) * KG *
          ((3 : ℝ) ^ m * Real.sqrt ((3 : ℝ) ^ m)))) := by
    have hup : normalizedL2On (truncatedWindow x m m) u.toFun
        ≤ Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
          (schauderDirichletPoincareConst d * (d : ℝ) * KG *
            ((3 : ℝ) ^ m * Real.sqrt ((3 : ℝ) ^ m))) :=
      htrans.trans (mul_le_mul_of_nonneg_left hnormQ (Real.sqrt_nonneg _))
    have hraw : affineExcessRaw (truncatedWindow x m m) u.toFun
        ≤ Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
          (schauderDirichletPoincareConst d * (d : ℝ) * KG *
            ((3 : ℝ) ^ m * Real.sqrt ((3 : ℝ) ^ m))) := hzero.trans hup
    have hnn : (0 : ℝ) ≤ Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
        (schauderDirichletPoincareConst d * (d : ℝ) * KG *
          ((3 : ℝ) ^ m * Real.sqrt ((3 : ℝ) ^ m))) := by
      have h1 : (0 : ℝ) ≤ schauderDirichletPoincareConst d :=
        schauderDirichletPoincareConst_nonneg d
      have h2 : (0 : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ m) := Real.sqrt_nonneg _
      have h3 : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
      have h4 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      exact mul_nonneg (Real.sqrt_nonneg _)
        (mul_nonneg (mul_nonneg (mul_nonneg h1 h4) hKG) (mul_nonneg h3.le h2))
    change ((volume (truncatedWindow x m m)).toReal) ^ (-(d : ℝ)⁻¹) *
      affineExcessRaw (truncatedWindow x m m) u.toFun ≤ _
    exact mul_le_mul hnorm hraw (affineExcessRaw_nonneg _ _) (by positivity)
  refine hchain.trans (le_of_eq ?_)
  have hcancel : (3 : ℝ) ^ (-m) * (3 : ℝ) ^ m = 1 := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), neg_add_cancel, zpow_zero]
  rw [schauderInitialConst]
  calc 9 * (3 : ℝ) ^ (-m) * (Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
        (schauderDirichletPoincareConst d * (d : ℝ) * KG *
          ((3 : ℝ) ^ m * Real.sqrt ((3 : ℝ) ^ m))))
      = 9 * Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
          (schauderDirichletPoincareConst d * (d : ℝ)) * KG *
          Real.sqrt ((3 : ℝ) ^ m) * ((3 : ℝ) ^ (-m) * (3 : ℝ) ^ m) := by ring
    _ = 9 * Real.sqrt (((3 : ℝ) ^ (2 : ℤ)) ^ d) *
          (schauderDirichletPoincareConst d * (d : ℝ)) * KG *
          Real.sqrt ((3 : ℝ) ^ m) := by rw [hcancel, mul_one]

end

end Algsuperdiff.Section4.Provider.Schauder
