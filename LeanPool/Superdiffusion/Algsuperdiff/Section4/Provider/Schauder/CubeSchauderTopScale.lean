/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderPointwise

/-!
# CubeSchauderTopScale

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Cube Schauder: the excess of the zero-datum solution at the top scale

`CubeSchauderCampanato.affineExcess_le_campanato` delivers the Campanato datum
for every scale `j ≤ m`.  The full-cube consumer
(`CubeSchauderAssembly.exists_zeroDatumWitness_of_campanato`) runs the slope
telescope at top index `T = m+1`, so it needs one further scale: the excess of
the solution over the window at scale `m+1`, which by
`CubeSchauderPointwise.truncatedWindow_top_eq` **is** `□_m` itself, independently
of the base point.

This module supplies exactly that one estimate:

```text
  E(w, □_m) ≤ C_Poincaré(d)·d · KG · √(3^m) ≤ C_Poincaré(d)·d · KG · √(3^{m+1}) .
```

The proof is `CubeSchauderCampanato.affineExcess_initial_le` run **without** the
window transfer: freeze the forcing at `G(0)` (a zero-trace test function does
not see a constant forcing), apply the sharp energy bound
`dirichletEnergy_le_of_isDivFormWeakSolutionOn_one`, convert the coordinate sum
by `sqrt_freezing_budget`, apply the Dirichlet Poincaré inequality
`eLpNorm_le_schauderDirichletPoincare` at the inscribing cube `0 + □_m`, and
compare the excess against the constant competitor `c = 0`.  Because the window
is the cube itself, `Support.AffineExcess.affineExcess_openCubeSet` identifies
the general normalizer `|W|^{-1/d}` with the cube normalizer `3^{-m}` — no
volume sandwich and no aspect-ratio loss appear, so the constant is strictly
smaller than the truncated-window constant `schauderInitialConst d`.

## References

* ABK26; Armstrong--Kuusi, *Elliptic Regularity*, Proposition `p.Schauder.C1alpha`.
-/

namespace Algsuperdiff.Section4.Provider.Schauder

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The constant -/

/-- The top-scale constant `C_Poincaré(d)·d`. -/
def schauderTopScaleConst (d : ℕ) : ℝ :=
  schauderDirichletPoincareConst d * (d : ℝ)

theorem schauderTopScaleConst_nonneg (d : ℕ) : 0 ≤ schauderTopScaleConst d :=
  mul_nonneg (schauderDirichletPoincareConst_nonneg d) (Nat.cast_nonneg d)

/-! ## 2. The normalized `L²` bound on the whole cube -/

/-- **The zero-datum solution is small in `L²(□_m)`.**

Freezing the forcing at `G(0)`, the sharp energy bound and the Dirichlet
Poincaré inequality give

```text
  ‖w‖_{L²(□_m)} ≤ C_Poincaré(d)·d·KG·3^m·√(3^m) .
```
-/
theorem normalizedL2On_le_of_isDivFormWeakSolutionOn_one [NeZero d] {m : ℤ}
    (u : H10Function (openCubeSet (originCube d m)))
    {G : Vec d → Vec d} {KG : ℝ} (hKG : 0 ≤ KG)
    (hGL2 : MemVectorL2 (openCubeSet (originCube d m)) G)
    (hG : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) KG G)
    (hu : IsDivFormWeakSolutionOn (fun _ => (1 : Mat d))
      (openCubeSet (originCube d m)) u.toH1Function G) :
    normalizedL2On (openCubeSet (originCube d m)) u.toFun
      ≤ schauderTopScaleConst d * KG * ((3 : ℝ) ^ m * Real.sqrt ((3 : ℝ) ^ m)) := by
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
  rw [normalizedL2On_eq_toReal_eLpNorm_div huQ, div_le_iff₀ (Real.sqrt_pos.2 hvolQpos)]
  refine hpoin'.trans (le_of_eq ?_)
  rw [hsqrtV, schauderTopScaleConst]
  ring

/-! ## 3. The excess on the whole cube -/

/-- **The excess of the zero-datum solution over `□_m` itself.**

`E(w, □_m) ≤ C_Poincaré(d)·d·KG·√(3^m)`.  On the cube the general normalizer
`|W|^{-1/d}` *is* `3^{-m}` (`affineExcess_openCubeSet`), so the `3^m` of the
Poincaré inequality cancels exactly and no aspect-ratio constant appears. -/
theorem affineExcess_openCubeSet_le [NeZero d] (hd : d ≠ 0) {m : ℤ}
    (u : H10Function (openCubeSet (originCube d m)))
    {G : Vec d → Vec d} {KG : ℝ} (hKG : 0 ≤ KG)
    (hGL2 : MemVectorL2 (openCubeSet (originCube d m)) G)
    (hG : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) KG G)
    (hu : IsDivFormWeakSolutionOn (fun _ => (1 : Mat d))
      (openCubeSet (originCube d m)) u.toH1Function G) :
    affineExcess (openCubeSet (originCube d m)) u.toFun
      ≤ schauderTopScaleConst d * KG * Real.sqrt ((3 : ℝ) ^ m) := by
  have hnormQ := normalizedL2On_le_of_isDivFormWeakSolutionOn_one u hKG hGL2 hG hu
  have hzero : affineExcessRaw (openCubeSet (originCube d m)) u.toFun
      ≤ normalizedL2On (openCubeSet (originCube d m)) u.toFun := by
    have h := affineExcessRaw_le_normalizedL2On_sub_const
      (openCubeSet (originCube d m)) u.toFun 0
    have hfun : (fun y => u.toFun y - 0) = u.toFun := by funext y; ring
    rwa [hfun] at h
  have hraw : affineExcessRaw (openCubeSet (originCube d m)) u.toFun
      ≤ schauderTopScaleConst d * KG * ((3 : ℝ) ^ m * Real.sqrt ((3 : ℝ) ^ m)) :=
    hzero.trans hnormQ
  have hscale : (originCube d m).scale = m := rfl
  rw [affineExcess_openCubeSet hd (originCube d m) u.toFun, affineExcessScaled, hscale]
  have hstep := mul_le_mul_of_nonneg_left hraw
    (le_of_lt (zpow_pos (by norm_num : (0 : ℝ) < 3) (-m)))
  refine hstep.trans (le_of_eq ?_)
  have hcancel : (3 : ℝ) ^ (-m) * (3 : ℝ) ^ m = 1 := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), neg_add_cancel, zpow_zero]
  calc (3 : ℝ) ^ (-m) *
        (schauderTopScaleConst d * KG * ((3 : ℝ) ^ m * Real.sqrt ((3 : ℝ) ^ m)))
      = schauderTopScaleConst d * KG * Real.sqrt ((3 : ℝ) ^ m) *
          ((3 : ℝ) ^ (-m) * (3 : ℝ) ^ m) := by ring
    _ = schauderTopScaleConst d * KG * Real.sqrt ((3 : ℝ) ^ m) := by
        rw [hcancel, mul_one]

/-! ## 4. The Campanato datum at the top scale, at every base point -/

/-- **The top-scale Campanato datum, uniform in the base point.**

At scale `m+1` every truncated window centred in `□_m` is `□_m` itself, so the
single cube estimate of `affineExcess_openCubeSet_le` supplies the datum at
`j = m+1` for *every* `z ∈ □_m` — interior and boundary base points alike.  The
scale is relaxed from `√(3^m)` to `√(3^{m+1})` to meet the consumer's display. -/
theorem affineExcess_truncatedWindow_top_le [NeZero d] (hd : d ≠ 0) {m : ℤ}
    {z : Vec d} (hz : z ∈ openCubeSet (originCube d m))
    (u : H10Function (openCubeSet (originCube d m)))
    {G : Vec d → Vec d} {KG : ℝ} (hKG : 0 ≤ KG)
    (hGL2 : MemVectorL2 (openCubeSet (originCube d m)) G)
    (hG : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) KG G)
    (hu : IsDivFormWeakSolutionOn (fun _ => (1 : Mat d))
      (openCubeSet (originCube d m)) u.toH1Function G) :
    affineExcess (truncatedWindow z m (m + 1)) u.toFun
      ≤ schauderTopScaleConst d * KG * Real.sqrt ((3 : ℝ) ^ (m + 1)) := by
  rw [truncatedWindow_top_eq hz]
  refine (affineExcess_openCubeSet_le hd u hKG hGL2 hG hu).trans ?_
  have hmono : Real.sqrt ((3 : ℝ) ^ m) ≤ Real.sqrt ((3 : ℝ) ^ (m + 1)) :=
    Real.sqrt_le_sqrt (zpow_le_zpow_right₀ (by norm_num) (by omega))
  exact mul_le_mul_of_nonneg_left hmono
    (mul_nonneg (schauderTopScaleConst_nonneg d) hKG)

end

end Algsuperdiff.Section4.Provider.Schauder
