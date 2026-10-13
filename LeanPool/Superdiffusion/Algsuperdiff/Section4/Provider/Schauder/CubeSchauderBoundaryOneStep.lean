/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderFold
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderBoundaryTwin
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderBoundaryResidue

/-!
# CubeSchauderBoundaryOneStep

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Cube Schauder: the boundary one-step contraction at the Lipschitz rate

The boundary twin of `CubeSchauderOneStep.excessDecay_oneStep_lipschitz`.
Three proved ingredients meet here:

1. the **competitor** — `exists_harmonicCompetitor_reflected_odd`, the chain of
   `CubeSchauderBoundaryResidue` re-run with the odd-reflection producer's
   met-face oddness *kept* (`ExcessDecay.faceOdd_eqOn_reflectedWindow_of_ae`'s
   seam, run off `continuousOn_of_harmonicOnNhd`), so the fold can consume it;
2. the **atom** — `CubeSchauderBoundaryTwin.exists_gradientLipschitz_boundary`,
   the harmonic gradient-Lipschitz bound on the reflected window family;
3. the **fold** — `CubeSchauderFold.exists_affineExcess_reflectedWindow_le`,
   which converts the doubled-window excess of the atom's conclusion into the
   truncated-window excess the recursion iterates.

The result carries **no interior geometry slot**: it holds at every base point
of `□_m` and every scale with `n - 2 < m`, so a single branch supplies the
Campanato datum everywhere.

```text
  E(u,U_k) ≤ C_contr(d) · 3^{-k} · E(u,U_0)
              + C_rem(d,k) · 3^{-n} · ‖u - V‖_{L²(U_2)} ,
```

`U_j = (x + □_{n-j}) ∩ □_m`, with the contraction at a **full** power of the
step, exactly as in the interior branch — the reflected geometry costs only
constants.

## References

* Armstrong--Kuusi, *Elliptic Regularity* (`ellipticregularity.tex`),
  Proposition `p.Schauder.C1alpha`, display `e.Sch1a.1`.
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

/-! ## 1. The competitor, with its met-face oddness kept -/

/-- **The harmonic competitor on the doubled window, odd about every met face.**

`CubeSchauderBoundaryResidue.exists_harmonicCompetitor_residue_reflected` with the
odd-reflection producer's oddness clause retained and transported to the Weyl
representative: the representative is continuous on the doubled window
(`continuousOn_of_harmonicOnNhd`) and almost everywhere equal there to the
globally odd `H¹` datum, so it is *pointwise* odd about every met face at every
point of the doubled window — exactly the binder shape the fold consumes. -/
theorem exists_harmonicCompetitor_reflected_odd [NeZero d] {m n : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hnm : n - 2 < m)
    (u : H10Function (openCubeSet (originCube d m)))
    {G : Vec d → Vec d} {KG : ℝ} (hKG : 0 ≤ KG)
    (hGL2 : MemVectorL2 (openCubeSet (originCube d m)) G)
    (hG : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) KG G)
    (hu : IsDivFormWeakSolutionOn (fun _ => (1 : Mat d))
      (openCubeSet (originCube d m)) u.toH1Function G) :
    ∃ V : Vec d → ℝ,
      HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
          ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)) ∧
        MemLp V 2 (volume : Measure (Vec d)) ∧
        (∀ l : Fin d, MeetsUpperFace x m (n - 2) l →
          ∀ y ∈ reflectedWindow x m (n - 2),
            V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -V y) ∧
        (∀ l : Fin d, MeetsLowerFace x m (n - 2) l →
          ∀ y ∈ reflectedWindow x m (n - 2),
            V (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -V y) ∧
        (3 : ℝ) ^ (-n) *
            normalizedL2On (truncatedWindow x m (n - 2)) (fun y => u.toFun y - V y)
          ≤ boundaryResidueConst d * KG * Real.sqrt ((3 : ℝ) ^ n) := by
  have hWopen : IsOpen (truncatedWindow x m (n - 2)) := isOpen_truncatedWindow x m (n - 2)
  have hWsub : truncatedWindow x m (n - 2) ⊆ openCubeSet (originCube d m) :=
    truncatedWindow_subset_domain x m (n - 2)
  have hWmeas : MeasurableSet (truncatedWindow x m (n - 2)) :=
    measurableSet_truncatedWindow x m (n - 2)
  have hWpos : 0 < (volume (truncatedWindow x m (n - 2))).toReal :=
    volume_toReal_truncatedWindow_pos x hx (by omega)
  -- (1) the freezing step at the replacement scale
  obtain ⟨w, hharm, hgrad⟩ :=
    exists_frozenHarmonicReplacement_truncatedWindow (n := n - 2) hx u.toH1Function hKG
      hGL2 hG hu
  -- (2) the zero-trace slot
  have hzt : LocalizedZeroTraceFunctionOn (truncatedWindow x m (n - 2))
      (reflectedWindow x m (n - 2))
      (u.toH1Function.restrict hWopen hWsub - w.toH1Function).toFun :=
    localizedZeroTraceFunctionOn_h1Function_sub x ⟨u, rfl⟩ w (fun _ => rfl)
  -- (3) the odd reflection, oddness kept, and (4) Weyl on the doubled window
  obtain ⟨W₁, hW₁harm, hW₁pin, hW₁odd⟩ :=
    exists_h1_oddReflection_reflectedWindow (by omega : n - 2 < m) _ hharm hzt
  obtain ⟨V, hVharm, hVmem, hVae⟩ :=
    exists_classicalCompetitor_reflectedWindow x m (n - 2) hW₁harm
  have hVcont : ContinuousOn V (reflectedWindow x m (n - 2)) :=
    continuousOn_of_harmonicOnNhd hVharm
  refine ⟨V, hVharm, hVmem,
    fun l hl => eqOn_faceOdd_upper_of_ae_eq hnm hl hVcont hVae ((hW₁odd l).1 hl),
    fun l hl => eqOn_faceOdd_lower_of_ae_eq hnm hl hVcont hVae ((hW₁odd l).2 hl), ?_⟩
  -- `u - V = w` almost everywhere on the window
  have hVaeW : V =ᵐ[volume.restrict (truncatedWindow x m (n - 2))] W₁.toFun :=
    ae_restrict_of_ae_restrict_of_subset
      (truncatedWindow_subset_reflectedWindow x m (n - 2)) hVae
  have hae : ∀ᵐ y ∂(volume.restrict (truncatedWindow x m (n - 2))),
      u.toFun y - V y = w.toH1Function.toFun y := by
    filter_upwards [hVaeW, MeasureTheory.self_mem_ae_restrict hWmeas] with y hy hyW
    have hsub : (u.toH1Function.restrict hWopen hWsub - w.toH1Function).toFun y
        = u.toFun y - w.toH1Function.toFun y := by
      simp only [H1Function.sub_toFun]
      rfl
    rw [hy, hW₁pin y hyW, hsub]
    ring
  have hcongr : normalizedL2On (truncatedWindow x m (n - 2)) (fun y => u.toFun y - V y)
      = normalizedL2On (truncatedWindow x m (n - 2)) w.toH1Function.toFun :=
    normalizedL2On_congr_ae hae
  -- (5) the Dirichlet Poincaré at the inscribing cube
  have hwW : MemLp w.toH1Function.toFun 2
      (volume.restrict (truncatedWindow x m (n - 2))) := by
    have h := w.toH1Function.memL2
    simpa only [volumeMeasureOn] using h
  have hinscribe : ∀ y ∈ truncatedWindow x m (n - 2), ∀ j : Fin d,
      x j - (1 / 2 : ℝ) * (3 : ℝ) ^ (n - 2) < y j ∧
        y j < x j + (1 / 2 : ℝ) * (3 : ℝ) ^ (n - 2) := by
    intro y hy j
    have h := mem_image_add_openCubeSet_iff.1
      (truncatedWindow_subset_translate x m (n - 2) hy) j
    exact ⟨by linarith only [h.1], by linarith only [h.2]⟩
  have hpoin := eLpNorm_le_schauderDirichletPoincare hWmeas x (n - 2) hinscribe w
  have hpoin' : (eLpNorm w.toH1Function.toFun 2
        (volume.restrict (truncatedWindow x m (n - 2)))).toReal
      ≤ schauderDirichletPoincareConst d * (3 : ℝ) ^ (n - 2) *
        ((d : ℝ) * KG *
          Real.sqrt ((3 : ℝ) ^ (n - 2) *
            (volume (truncatedWindow x m (n - 2))).toReal)) := by
    refine hpoin.trans (mul_le_mul_of_nonneg_left hgrad ?_)
    exact mul_nonneg (schauderDirichletPoincareConst_nonneg d)
      (zpow_pos (by norm_num) (n - 2)).le
  have hsqrtV : Real.sqrt ((3 : ℝ) ^ (n - 2)
        * (volume (truncatedWindow x m (n - 2))).toReal)
      = Real.sqrt ((3 : ℝ) ^ (n - 2))
        * Real.sqrt ((volume (truncatedWindow x m (n - 2))).toReal) :=
    Real.sqrt_mul (zpow_pos (by norm_num) (n - 2)).le _
  have hnormW : normalizedL2On (truncatedWindow x m (n - 2)) w.toH1Function.toFun
      ≤ schauderDirichletPoincareConst d * (d : ℝ) * KG *
        ((3 : ℝ) ^ (n - 2) * Real.sqrt ((3 : ℝ) ^ (n - 2))) := by
    rw [normalizedL2On_eq_toReal_eLpNorm_div hwW, div_le_iff₀ (Real.sqrt_pos.2 hWpos)]
    refine hpoin'.trans (le_of_eq ?_)
    rw [hsqrtV]
    ring
  -- the scale bookkeeping
  rw [hcongr]
  have h3n : (0 : ℝ) < (3 : ℝ) ^ (-n) := zpow_pos (by norm_num) _
  have hmul := mul_le_mul_of_nonneg_left hnormW h3n.le
  refine hmul.trans ?_
  have hc : (3 : ℝ) ^ (-n) * (3 : ℝ) ^ (n - 2) = 1 / 9 := by
    rw [← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), show -n + (n - 2) = (-2 : ℤ) by ring]
    norm_num
  have hAnn : (0 : ℝ) ≤ schauderDirichletPoincareConst d * (d : ℝ) * KG :=
    mul_nonneg (mul_nonneg (schauderDirichletPoincareConst_nonneg d) (Nat.cast_nonneg d)) hKG
  have hsq : Real.sqrt ((3 : ℝ) ^ (n - 2)) ≤ Real.sqrt ((3 : ℝ) ^ n) :=
    Real.sqrt_le_sqrt (zpow_le_zpow_right₀ (by norm_num) (by omega))
  have hstep : schauderDirichletPoincareConst d * (d : ℝ) * KG
        * Real.sqrt ((3 : ℝ) ^ (n - 2)) * (1 / 9)
      ≤ boundaryResidueConst d * KG * Real.sqrt ((3 : ℝ) ^ n) := by
    have h1 : schauderDirichletPoincareConst d * (d : ℝ) * KG
          * Real.sqrt ((3 : ℝ) ^ (n - 2))
        ≤ schauderDirichletPoincareConst d * (d : ℝ) * KG * Real.sqrt ((3 : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_left hsq hAnn
    have h2 : (0 : ℝ) ≤ schauderDirichletPoincareConst d * (d : ℝ) * KG
        * Real.sqrt ((3 : ℝ) ^ (n - 2)) := mul_nonneg hAnn (Real.sqrt_nonneg _)
    have hid : boundaryResidueConst d * KG * Real.sqrt ((3 : ℝ) ^ n)
        = schauderDirichletPoincareConst d * (d : ℝ) * KG * Real.sqrt ((3 : ℝ) ^ n) := by
      rw [boundaryResidueConst]
    rw [hid]
    linarith only [h1, h2]
  refine le_trans (le_of_eq ?_) hstep
  calc (3 : ℝ) ^ (-n) * (schauderDirichletPoincareConst d * (d : ℝ) * KG
        * ((3 : ℝ) ^ (n - 2) * Real.sqrt ((3 : ℝ) ^ (n - 2))))
      = (schauderDirichletPoincareConst d * (d : ℝ) * KG
          * Real.sqrt ((3 : ℝ) ^ (n - 2)))
        * ((3 : ℝ) ^ (-n) * (3 : ℝ) ^ (n - 2)) := by ring
    _ = schauderDirichletPoincareConst d * (d : ℝ) * KG
          * Real.sqrt ((3 : ℝ) ^ (n - 2)) * (1 / 9) := by rw [hc]

/-! ## 2. The fold constant -/

/-- **The fold constant** `C_fold(d)` of `CubeSchauderFold`, named by choice. -/
def boundaryFoldConst (d : ℕ) [NeZero d] : ℝ :=
  (exists_affineExcess_reflectedWindow_le d).choose

theorem boundaryFoldConst_nonneg (d : ℕ) [NeZero d] : 0 ≤ boundaryFoldConst d :=
  (exists_affineExcess_reflectedWindow_le d).choose_spec.1

/-- **The fold, at the named constant.** -/
theorem affineExcess_reflectedWindow_le [NeZero d] {m n : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hmn : n - 2 < m) {V : Vec d → ℝ}
    (hupV : ∀ l : Fin d, MeetsUpperFace x m (n - 2) l →
      ∀ y ∈ reflectedWindow x m (n - 2),
        V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -V y)
    (hlowV : ∀ l : Fin d, MeetsLowerFace x m (n - 2) l →
      ∀ y ∈ reflectedWindow x m (n - 2),
        V (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -V y)
    (hharm : HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2)))
    (hVR : MemLp V 2 (volume.restrict (reflectedWindow x m (n - 2)))) :
    affineExcess (reflectedWindow x m (n - 2)) V
      ≤ boundaryFoldConst d * affineExcess (truncatedWindow x m (n - 2)) V :=
  (exists_affineExcess_reflectedWindow_le d).choose_spec.2 m n x V hx hmn hupV hlowV
    hharm hVR

/-! ## 3. The one-step contraction -/

/-- The contraction constant of the boundary Lipschitz one step. -/
def boundaryContractionConst (d : ℕ) [NeZero d] : ℝ :=
  taylorLipschitzConst d * (boundaryLipschitzWindowConst d * boundaryFoldConst d)
    * windowRatioConst d 2

theorem boundaryContractionConst_nonneg (d : ℕ) [NeZero d] :
    0 ≤ boundaryContractionConst d :=
  mul_nonneg (mul_nonneg (taylorLipschitzConst_nonneg d)
    (mul_nonneg (boundaryLipschitzWindowConst_nonneg d) (boundaryFoldConst_nonneg d)))
    (windowRatioConst_nonneg d 2)

/-- The remainder constant of the boundary Lipschitz one step. -/
def boundaryRemainderConst (d : ℕ) [NeZero d] (k : ℕ) : ℝ :=
  81 * taylorLipschitzConst d * (boundaryLipschitzWindowConst d * boundaryFoldConst d)
    + 9 * (3 : ℝ) ^ (k : ℤ) * Real.sqrt (((3 : ℝ) ^ (k : ℤ)) ^ d)

theorem boundaryRemainderConst_nonneg (d : ℕ) [NeZero d] (k : ℕ) :
    0 ≤ boundaryRemainderConst d k := by
  have h1 : 0 ≤ 81 * taylorLipschitzConst d
      * (boundaryLipschitzWindowConst d * boundaryFoldConst d) :=
    mul_nonneg (mul_nonneg (by norm_num) (taylorLipschitzConst_nonneg d))
      (mul_nonneg (boundaryLipschitzWindowConst_nonneg d) (boundaryFoldConst_nonneg d))
  have h2 : 0 ≤ 9 * (3 : ℝ) ^ (k : ℤ) * Real.sqrt (((3 : ℝ) ^ (k : ℤ)) ^ d) := by positivity
  rw [boundaryRemainderConst]
  linarith only [h1, h2]

private theorem three_zpow_neg_nat_le_one_bdry {k : ℕ} : (3 : ℝ) ^ (-(k : ℤ)) ≤ 1 := by
  calc (3 : ℝ) ^ (-(k : ℤ)) ≤ (3 : ℝ) ^ (0 : ℤ) :=
        zpow_le_zpow_right₀ (by norm_num) (by omega)
    _ = 1 := zpow_zero 3

/-- **The boundary one-step contraction at the Lipschitz rate.**

For `u` on the window family `U_j = (x + □_{n-j}) ∩ □_m` at *any* base point of
`□_m`, and `V` classically harmonic and met-face odd on the doubled window
`reflectedWindow x m (n-2)`,

```text
  E(u,U_k) ≤ C_contr(d) · 3^{-k} · E(u,U_0)
              + C_rem(d,k) · 3^{-n} · ‖u - V‖_{L²(U_2)} .
```

The interior display, at the boundary, with **no** interior geometry slot: the
reflected window replaces `x + □_{n-2} ⊆ □_m`. -/
theorem excessDecay_oneStep_boundary_lipschitz [NeZero d] (hd : d ≠ 0) {m n : ℤ} {k : ℕ}
    (hk : 3 ≤ k) {x : Vec d} (hx : x ∈ openCubeSet (originCube d m)) (hnm : n - 1 ≤ m)
    (hmn : n - 2 < m) {u V : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (truncatedWindow x m n)))
    (hVR : MemLp V 2 (volume.restrict (reflectedWindow x m (n - 2))))
    (hupV : ∀ l : Fin d, MeetsUpperFace x m (n - 2) l →
      ∀ y ∈ reflectedWindow x m (n - 2),
        V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -V y)
    (hlowV : ∀ l : Fin d, MeetsLowerFace x m (n - 2) l →
      ∀ y ∈ reflectedWindow x m (n - 2),
        V (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) l y) = -V y)
    (hharm : HarmonicOnNhd (V ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) '' reflectedWindow x m (n - 2))) :
    affineExcess (truncatedWindow x m (n - (k : ℤ))) u
      ≤ boundaryContractionConst d * (3 : ℝ) ^ (-(k : ℤ))
            * affineExcess (truncatedWindow x m n) u
        + boundaryRemainderConst d k
            * ((3 : ℝ) ^ (-n)
              * normalizedL2On (truncatedWindow x m (n - 2)) (fun y => u y - V y)) := by
  have hne : (3 : ℝ) ≠ 0 := by norm_num
  have hCT : 0 ≤ taylorLipschitzConst d := taylorLipschitzConst_nonneg d
  have hCL : 0 ≤ boundaryLipschitzWindowConst d * boundaryFoldConst d :=
    mul_nonneg (boundaryLipschitzWindowConst_nonneg d) (boundaryFoldConst_nonneg d)
  have hmk : n - (k : ℤ) - 1 ≤ m := by omega
  have hm2 : n - 2 - 1 ≤ m := by omega
  have hsub_k2 : truncatedWindow x m (n - (k : ℤ)) ⊆ truncatedWindow x m (n - 2) :=
    truncatedWindow_mono x m (by omega)
  have hsub_k3 : truncatedWindow x m (n - (k : ℤ)) ⊆ truncatedWindow x m (n - 3) :=
    truncatedWindow_mono x m (by omega)
  have hsub_20 : truncatedWindow x m (n - 2) ⊆ truncatedWindow x m n :=
    truncatedWindow_mono x m (by omega)
  have hV2 : MemLp V 2 (volume.restrict (truncatedWindow x m (n - 2))) :=
    memLp_restrict_of_subset (truncatedWindow_subset_reflectedWindow x m (n - 2)) hVR
  have huk : MemLp u 2 (volume.restrict (truncatedWindow x m (n - (k : ℤ)))) :=
    memLp_restrict_of_subset (hsub_k2.trans hsub_20) hu
  have hVk : MemLp V 2 (volume.restrict (truncatedWindow x m (n - (k : ℤ)))) :=
    memLp_restrict_of_subset hsub_k2 hV2
  have hu2 : MemLp u 2 (volume.restrict (truncatedWindow x m (n - 2))) :=
    memLp_restrict_of_subset hsub_20 hu
  have hintsq : ∀ (c : ℝ) (g : Vec d),
      IntegrableOn (fun y => (V y - affineEval c g y) ^ 2)
        (reflectedWindow x m (n - 2)) volume :=
    fun c g => integrableOn_sub_affineEval_sq_reflectedWindow x hVR c g
  -- the producer slots and the Lipschitz atom
  obtain ⟨_, _, hint, hgrad, _, _⟩ := exists_gradientHolder_boundary_raw hx hmn hharm hintsq
  have hlip := exists_gradientLipschitz_boundary hd hx hmn hharm hintsq
  -- the fold
  have hfoldle := affineExcess_reflectedWindow_le hx hmn hupV hlowV hharm hVR
  set Ev2 : ℝ := affineExcess (truncatedWindow x m (n - 2)) V with hEv2def
  set L : ℝ := boundaryLipschitzWindowConst d * boundaryFoldConst d * (3 : ℝ) ^ (-n) * Ev2
    with hLdef
  have hEv2nn : 0 ≤ Ev2 := affineExcess_nonneg _ _
  have hLnn : 0 ≤ L := by
    rw [hLdef]
    exact mul_nonneg (mul_nonneg hCL (zpow_pos (by norm_num) _).le) hEv2nn
  have hlip' : ∀ p ∈ truncatedWindow x m (n - 3), ∀ q ∈ truncatedWindow x m (n - 3),
      ‖gradField V p - gradField V q‖ ≤ L * ‖p - q‖ := by
    intro p hp q hq
    refine (hlip p hp q hq).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    have hcoef : (0 : ℝ) ≤ boundaryLipschitzWindowConst d * (3 : ℝ) ^ (-n) :=
      mul_nonneg (boundaryLipschitzWindowConst_nonneg d) (zpow_pos (by norm_num) _).le
    have h := mul_le_mul_of_nonneg_left hfoldle hcoef
    rw [hLdef]
    linarith only [h]
  -- (1) the triangle step on `U_k`
  have h1 := affineExcess_sub_le_truncatedWindow hd hx hmk huk hVk
  -- (2) the Lipschitz affine competitor on `U_k`
  have h2 := affineExcess_le_taylorLipschitz hd hx hmk hLnn hVk
    (fun i => (hint i).mono_set hsub_k3) (hgrad.mono_set hsub_k3)
    (fun p hp q hq => hlip' p (hsub_k3 hp) q (hsub_k3 hq))
  -- (4) the triangle step on `U_2`, with `u` and `V` interchanged
  have h4 := affineExcess_sub_le_truncatedWindow hd hx hm2 hV2 hu2
  rw [normalizedL2On_sub_comm] at h4
  -- (5) quasi-monotonicity `E(u,U_2) ≤ κ E(u,U_0)`
  have h5 : affineExcess (truncatedWindow x m (n - 2)) u
      ≤ windowRatioConst d 2 * affineExcess (truncatedWindow x m n) u := by
    have h := affineExcess_truncatedWindow_le (l := n) x hx hm2 hnm (by omega) hu
    rwa [show n - (n - 2) = (2 : ℤ) by ring] at h
  -- (6) the `L²` window transfer
  have h6 : normalizedL2On (truncatedWindow x m (n - (k : ℤ))) (fun y => u y - V y)
      ≤ Real.sqrt (((3 : ℝ) ^ (k : ℤ)) ^ d)
        * normalizedL2On (truncatedWindow x m (n - 2)) (fun y => u y - V y) := by
    have h := normalizedL2On_truncatedWindow_le (l := n - 2) (k := n - (k : ℤ)) hx hmk hm2
      (by omega) (f := fun y => u y - V y) (hu2.sub hV2)
    rwa [show n - 2 - (n - (k : ℤ)) + 2 = (k : ℤ) by ring] at h
  -- the two `3`-power rewrites
  have hpow_k : (3 : ℝ) ^ (-(n - (k : ℤ))) = (3 : ℝ) ^ (k : ℤ) * (3 : ℝ) ^ (-n) := by
    rw [show -(n - (k : ℤ)) = (k : ℤ) + -n by ring, zpow_add₀ hne]
  have hpow_2 : (3 : ℝ) ^ (-(n - 2)) = 9 * (3 : ℝ) ^ (-n) := by
    rw [show -(n - 2) = (2 : ℤ) + -n by ring, zpow_add₀ hne]
    norm_num
  rw [hpow_k] at h1
  rw [hpow_2] at h4
  -- assemble
  set S2 := normalizedL2On (truncatedWindow x m (n - 2)) (fun y => u y - V y) with hS2
  set E0 := affineExcess (truncatedWindow x m n) u with hE0
  set R := Real.sqrt (((3 : ℝ) ^ (k : ℤ)) ^ d) with hR
  have hS2nn : 0 ≤ S2 := normalizedL2On_nonneg _ _
  have h3npos : (0 : ℝ) < (3 : ℝ) ^ (-n) := zpow_pos (by norm_num) _
  have hL3 : taylorLipschitzConst d * L * (3 : ℝ) ^ (n - (k : ℤ))
      = taylorLipschitzConst d * (boundaryLipschitzWindowConst d * boundaryFoldConst d)
        * (3 : ℝ) ^ (-(k : ℤ)) * Ev2 := by
    rw [hLdef]
    have hmul : (3 : ℝ) ^ (-n) * (3 : ℝ) ^ (n - (k : ℤ)) = (3 : ℝ) ^ (-(k : ℤ)) := by
      rw [← zpow_add₀ hne]
      congr 1
      ring
    calc taylorLipschitzConst d
          * (boundaryLipschitzWindowConst d * boundaryFoldConst d * (3 : ℝ) ^ (-n) * Ev2)
          * (3 : ℝ) ^ (n - (k : ℤ))
        = taylorLipschitzConst d * (boundaryLipschitzWindowConst d * boundaryFoldConst d)
            * ((3 : ℝ) ^ (-n) * (3 : ℝ) ^ (n - (k : ℤ))) * Ev2 := by ring
      _ = taylorLipschitzConst d * (boundaryLipschitzWindowConst d * boundaryFoldConst d)
            * (3 : ℝ) ^ (-(k : ℤ)) * Ev2 := by rw [hmul]
  rw [hL3] at h2
  have hEv2 : Ev2 ≤ windowRatioConst d 2 * E0 + 81 * ((3 : ℝ) ^ (-n) * S2) := by
    linarith only [h4, h5]
  have hcoef : (0 : ℝ) ≤ taylorLipschitzConst d
      * (boundaryLipschitzWindowConst d * boundaryFoldConst d) * (3 : ℝ) ^ (-(k : ℤ)) :=
    mul_nonneg (mul_nonneg hCT hCL) (zpow_pos (by norm_num) _).le
  have hfold : taylorLipschitzConst d
        * (boundaryLipschitzWindowConst d * boundaryFoldConst d)
        * (3 : ℝ) ^ (-(k : ℤ)) * Ev2
      ≤ boundaryContractionConst d * (3 : ℝ) ^ (-(k : ℤ)) * E0
        + 81 * taylorLipschitzConst d
            * (boundaryLipschitzWindowConst d * boundaryFoldConst d)
            * (3 : ℝ) ^ (-(k : ℤ)) * ((3 : ℝ) ^ (-n) * S2) := by
    have h := mul_le_mul_of_nonneg_left hEv2 hcoef
    rw [boundaryContractionConst]
    linarith only [h]
  have hQnn : (0 : ℝ) ≤ 81 * taylorLipschitzConst d
      * (boundaryLipschitzWindowConst d * boundaryFoldConst d) * ((3 : ℝ) ^ (-n) * S2) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCT) hCL)
      (mul_nonneg h3npos.le hS2nn)
  have hdrop : 81 * taylorLipschitzConst d
        * (boundaryLipschitzWindowConst d * boundaryFoldConst d)
        * (3 : ℝ) ^ (-(k : ℤ)) * ((3 : ℝ) ^ (-n) * S2)
      ≤ 81 * taylorLipschitzConst d
          * (boundaryLipschitzWindowConst d * boundaryFoldConst d)
          * ((3 : ℝ) ^ (-n) * S2) := by
    calc 81 * taylorLipschitzConst d
          * (boundaryLipschitzWindowConst d * boundaryFoldConst d)
          * (3 : ℝ) ^ (-(k : ℤ)) * ((3 : ℝ) ^ (-n) * S2)
        = (81 * taylorLipschitzConst d
            * (boundaryLipschitzWindowConst d * boundaryFoldConst d)
            * ((3 : ℝ) ^ (-n) * S2)) * (3 : ℝ) ^ (-(k : ℤ)) := by ring
      _ ≤ (81 * taylorLipschitzConst d
            * (boundaryLipschitzWindowConst d * boundaryFoldConst d)
            * ((3 : ℝ) ^ (-n) * S2)) * 1 :=
          mul_le_mul_of_nonneg_left three_zpow_neg_nat_le_one_bdry hQnn
      _ = 81 * taylorLipschitzConst d
            * (boundaryLipschitzWindowConst d * boundaryFoldConst d)
            * ((3 : ℝ) ^ (-n) * S2) := by ring
  have hraw : 9 * ((3 : ℝ) ^ (k : ℤ) * (3 : ℝ) ^ (-n))
        * normalizedL2On (truncatedWindow x m (n - (k : ℤ))) (fun y => u y - V y)
      ≤ 9 * (3 : ℝ) ^ (k : ℤ) * R * ((3 : ℝ) ^ (-n) * S2) := by
    have hc : (0 : ℝ) ≤ 9 * ((3 : ℝ) ^ (k : ℤ) * (3 : ℝ) ^ (-n)) := by positivity
    have h := mul_le_mul_of_nonneg_left h6 hc
    linarith only [h]
  rw [boundaryRemainderConst]
  linarith only [h1, h2, hfold, hdrop, hraw]

end

end Algsuperdiff.Section4.Provider.Schauder
