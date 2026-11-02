/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomSpineCloseClause
public import LeanPool.HighContrastHomogenization.Support.Sobolev.W1p.ZeroExtensionGraph

/-!
# HomSpineFrameData

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5: the per-datum frame from the root's own binders

## What this module is

`HomSpineCloseClause`'s clause body carries eight frame
binders for the Step-3c leg,

```text
  hw, hwI, hwc, hGI, hGzero, hgc, hgw, hzero
```

exactly as the `L^∞` conversion carries them.  This module produces
the first FIVE of them from the root's own data binders `hsol` and `hcomp`, and
DERIVES the eighth (`hzero`) from the other two.  What is left is stated as one
named predicate, `HasContinuousRepresentative`, and is this file's reported
residue (see the module docstring's last section).

### The construction, and why it is the zero extension and not `u - v`

The frame items are global statements on `Vec d` (`HasWeakGradientOn Set.univ`,
`Integrable … volume`, `HasCompactSupport`).  The literal difference
`u.toFun - v.toFun` does NOT satisfy them: an `H1Function (openCubeSet Q)`
constrains its representative only on `Q`, so `u.toFun - v.toFun` is arbitrary
off the cube and is in particular not compactly supported.

The object that does satisfy them is the `H¹₀` ZERO EXTENSION — which is
exactly the object the manuscript names ("`u - v ∈ H¹₀(□_m)`").  `hsol` and
`hcomp` carry the SAME boundary datum `h`, so the
`HomSpineCloseUnique.exists_h10Function_sub_of_hasZeroTrace` produces `w:
H10Function (openCubeSet Q)` with

```text
  ∀ x, w x = u.toFun x - v.toFun x       and      ∀ x, ∇w x = ∇u x - ∇v x,
```

and `CoarseGraining`'s `H10Function.hasWeakGradientOn_univ_zeroExtension` turns
the pair `(w.zeroExtension, w.zeroExtensionGrad)` into a GLOBAL weak-gradient
graph. The two extensions agree with `u - v` and `∇u - ∇v` on the open cube and
vanish off it — which is simultaneously the `hGzero` binder ("the gradient
vanishes off `□_m`") and the reason the a.e.-on-`□_m` conclusion is unchanged.

### `hzero` is DERIVED, not assumed

`faceZero_of_continuousRepresentative`: if `W` vanishes off the open cube and
`g` is a continuous representative of `W`, then `g` vanishes on
`cubeFaceSet Q`.  The complement of the CLOSED cube is open and `W` vanishes on
it pointwise, so `g` vanishes there a.e., hence — being continuous, and Lebesgue
measure being open-positive — everywhere on it; `g⁻¹{0}` is closed and contains
that complement, so it contains its closure, which contains every face point
(`cubeFaceSet_subset_closure_compl`).

### THE RESIDUE (reported, not closed)

`HasContinuousRepresentative W` — the existence of a continuous `g` with `W
=ᵐ[volume] g`.  It is NOT derivable from `w ∈ H¹₀(□_m)` alone (for `d ≥ 2` an
`H¹₀` function need not have a continuous representative), and it is not
derivable from the root's data binders.  Mathematically it comes from the SAME
"fractional Sobolev–Poincaré" step the print invokes in the paper: the negative
gauge on `∇w` makes every mollification `w ⋆ ψ` Hölder-`(1-s)` at one constant
(the `holderSeminormBoundOn_convolution_of_uniformBoxGauge`), and a uniformly
Hölder family with `L¹` convergence is uniformly Cauchy.  That compactness step
is not formalized in this tree.
-/

open MeasureTheory HCPolySupport

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The cube's measure-theoretic frame -/

/-- A triadic cube has finite Lebesgue measure: it is bounded and `Vec d` is a
proper space carrying a measure finite on compacts. -/
theorem volume_openCubeSet_ne_top (Q : TriadicCube d) :
    volume (openCubeSet Q) ≠ ⊤ :=
  ((isBounded_openCubeSet Q).measure_lt_top).ne

/-- The open realization sits inside the half-open one. -/
theorem openCubeSet_subset_cubeSet (Q : TriadicCube d) :
    openCubeSet Q ⊆ cubeSet Q :=
  fun _ hx i => ⟨(hx i).1.le, (hx i).2⟩

/-- Anything supported in a triadic cube has compact support: the closure of a
bounded set in `Vec d` is compact. -/
theorem hasCompactSupport_indicator_openCubeSet (Q : TriadicCube d) (f : Vec d → ℝ) :
    HasCompactSupport (Set.indicator (openCubeSet Q) f) := by
  refine HasCompactSupport.intro (isBounded_openCubeSet Q).isCompact_closure ?_
  intro x hx
  exact Set.indicator_of_notMem (fun hmem => hx (subset_closure hmem)) f

/-- On a cube, `L²` control gives `L¹` control of the zero extension. -/
theorem integrable_indicator_openCubeSet_of_memL2 (Q : TriadicCube d) {f : Vec d → ℝ}
    (hf : MemLp f 2 (volume.restrict (openCubeSet Q))) :
    Integrable (Set.indicator (openCubeSet Q) f) volume := by
  have hfin : IsFiniteMeasure (volume.restrict (openCubeSet Q)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.mpr (volume_openCubeSet_ne_top Q)
  have h1 : MemLp f 1 (volume.restrict (openCubeSet Q)) := hf.mono_exponent (by norm_num)
  have h2 : MemLp (Set.indicator (openCubeSet Q) f) 1 volume :=
    (memLp_indicator_iff_restrict (measurableSet_openCubeSet Q)).2 h1
  exact memLp_one_iff_integrable.mp h2

/-! ## 2. The frame of an `H¹₀` function -/

/-- The value zero extension is integrable. -/
theorem integrable_zeroExtension {Q : TriadicCube d} (w : H10Function (openCubeSet Q)) :
    Integrable w.zeroExtension volume :=
  integrable_indicator_openCubeSet_of_memL2 Q w.toH1Function.memL2

/-- The value zero extension has compact support. -/
theorem hasCompactSupport_zeroExtension {Q : TriadicCube d}
    (w : H10Function (openCubeSet Q)) : HasCompactSupport w.zeroExtension :=
  hasCompactSupport_indicator_openCubeSet Q _

/-- Every coordinate of the gradient zero extension is integrable. -/
theorem integrable_zeroExtensionGrad_coord {Q : TriadicCube d}
    (w : H10Function (openCubeSet Q)) (i : Fin d) :
    Integrable (fun y => w.zeroExtensionGrad y i) volume := by
  have hcoord : (fun y => w.zeroExtensionGrad y i) =
      Set.indicator (openCubeSet Q) (fun y => w.toH1Function.grad y i) := by
    funext y
    by_cases hy : y ∈ openCubeSet Q
    · simp only [H10Function.zeroExtensionGrad, Set.indicator_of_mem hy]
    · simp only [H10Function.zeroExtensionGrad, Set.indicator_of_notMem hy, Pi.zero_apply]
  rw [hcoord]
  exact integrable_indicator_openCubeSet_of_memL2 Q (w.toH1Function.gradMemL2 i)

/-- The gradient zero extension vanishes off the (half-open) cube — the
`hGzero` binder of the `L^∞` conversion. -/
theorem zeroExtensionGrad_eq_zero_of_not_mem_cubeSet {Q : TriadicCube d}
    (w : H10Function (openCubeSet Q)) {y : Vec d} (hy : y ∉ cubeSet Q) :
    w.zeroExtensionGrad y = 0 :=
  w.zeroExtensionGrad_apply_of_not_mem (fun hmem => hy (openCubeSet_subset_cubeSet Q hmem))

/-! ## 3. The face geometry, and `hzero` -/

/-- The closed realization of a triadic cube is closed. -/
theorem isClosed_closedCubeSet (Q : TriadicCube d) : IsClosed (closedCubeSet Q) := by
  have h : closedCubeSet Q =
      ⋂ i : Fin d, (fun x : Vec d => x i) ⁻¹'
        (Set.Icc (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q)
          (((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q)) := by
    ext x
    simp only [closedCubeSet, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_Icc]
  rw [h]
  exact isClosed_iInter fun i => isClosed_Icc.preimage (continuous_apply i)

/-- **Every face point is a limit of exterior points.**  A point of
`cubeFaceSet Q` has, in some coordinate, the exact value of a face, so pushing
that one coordinate outwards leaves the closed cube at arbitrarily small
sup-distance. -/
theorem cubeFaceSet_subset_closure_compl (Q : TriadicCube d) :
    cubeFaceSet Q ⊆ closure ((closedCubeSet Q)ᶜ) := by
  intro y hy
  obtain ⟨hyc, hyo⟩ := hy
  have hex : ∃ i : Fin d,
      ¬ (((Q.index i : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q < y i ∧
        y i < ((Q.index i : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q) := by
    by_contra hcon
    push Not at hcon
    exact hyo fun i => hcon i
  obtain ⟨i0, hi0⟩ := hex
  rw [Metric.mem_closure_iff]
  intro eps heps
  /- the coordinate `i0` sits exactly on one of the two fac -/
  have hlo : ((Q.index i0 : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q ≤ y i0 := (hyc i0).1
  have hhi : y i0 ≤ ((Q.index i0 : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q := (hyc i0).2
  have hface : y i0 = ((Q.index i0 : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q ∨
      y i0 = ((Q.index i0 : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q := by
    by_contra hcon
    push Not at hcon
    exact hi0 ⟨lt_of_le_of_ne hlo (Ne.symm hcon.1), lt_of_le_of_ne hhi hcon.2⟩
  /- the shift, outwards, by `eps/2` -/
  set delta : ℝ := if y i0 = ((Q.index i0 : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q
    then -(eps / 2) else eps / 2 with hdelta
  refine ⟨Function.update y i0 (y i0 + delta), ?_, ?_⟩
  · intro hmem
    have hval : (Function.update y i0 (y i0 + delta)) i0 = y i0 + delta :=
      Function.update_self i0 _ y
    rcases hface with hL | hR
    · have hd : delta = -(eps / 2) := by rw [hdelta, ite_eq_left hL]
      have hbd := (hmem i0).1
      rw [hval, hd, hL] at hbd
      linarith only [hbd, heps]
    · have hne : y i0 ≠ ((Q.index i0 : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q := by
        rw [hR]
        intro hcon
        have hgap : ((Q.index i0 : ℝ) + (1 / 2 : ℝ)) * cubeScaleFactor Q -
            ((Q.index i0 : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q = cubeScaleFactor Q := by
          ring
        have hpos : (0 : ℝ) < cubeScaleFactor Q := cubeScaleFactor_pos Q
        linarith only [hcon, hgap, hpos]
      have hd : delta = eps / 2 := by rw [hdelta, ite_eq_right hne]
      have hbd := (hmem i0).2
      rw [hval, hd, hR] at hbd
      linarith only [hbd, heps]
  · refine (dist_pi_lt_iff heps).mpr ?_
    intro j
    by_cases hj : j = i0
    · subst hj
      have hval : (Function.update y j (y j + delta)) j = y j + delta :=
        Function.update_self j _ y
      rw [hval, Real.dist_eq]
      have habs : |y j - (y j + delta)| = |delta| := by
        rw [show y j - (y j + delta) = -delta by ring, abs_neg]
      have hd2 : |delta| = eps / 2 := by
        by_cases hL : y j = ((Q.index j : ℝ) - (1 / 2 : ℝ)) * cubeScaleFactor Q
        · rw [hdelta, ite_eq_left hL, abs_neg, abs_of_pos (by linarith only [heps])]
        · rw [hdelta, ite_eq_right hL, abs_of_pos (by linarith only [heps])]
      rw [habs, hd2]
      linarith only [heps]
    · have hval : (Function.update y i0 (y i0 + delta)) j = y j := Function.update_of_ne hj _ y
      rw [hval, dist_self]
      exact heps

/-- **`hzero` is DERIVED.**

If `W` vanishes off the open cube and `g` is a continuous representative of
`W`, then `g` vanishes on the faces of the cube.  This is the eighth frame
binder of the `L^∞` conversion, obtained from the other two
representative binders and the zero extension itself; nothing about the
Dirichlet problem is used. -/
theorem faceZero_of_continuousRepresentative {Q : TriadicCube d} {W : Vec d → ℝ}
    (hWzero : ∀ x, x ∉ openCubeSet Q → W x = 0) {g : Vec d → ℝ}
    (hgc : Continuous g) (hgw : W =ᵐ[volume] g) :
    ∀ y ∈ cubeFaceSet Q, g y = 0 := by
  /- off the closed cube, `g` agrees a.e. with the vanishing `W` -/
  have hnull : volume {x | x ∈ (closedCubeSet Q)ᶜ ∧ g x ≠ 0} = 0 := by
    refine measure_mono_null (fun x hx => ?_) hgw
    have hout : x ∉ openCubeSet Q := fun hmem =>
      hx.1 (openCubeSet_subset_closedCubeSet Q hmem)
    have hW : W x = 0 := hWzero x hout
    have hne : ¬ (W x = g x) := by
      rw [hW]
      exact fun hcon => hx.2 hcon.symm
    exact hne
  /- an open set on which a continuous function is a.e. zero is a set where it is ze -/
  have hzeroOut : ∀ x ∈ (closedCubeSet Q)ᶜ, g x = 0 := by
    intro x hx
    by_contra hne
    have hopen : IsOpen {z | z ∈ (closedCubeSet Q)ᶜ ∧ g z ≠ 0} := by
      have h1 : IsOpen ((closedCubeSet Q)ᶜ) := (isClosed_closedCubeSet Q).isOpen_compl
      have h2 : IsOpen (g ⁻¹' {(0 : ℝ)}ᶜ) := (isOpen_compl_singleton).preimage hgc
      exact h1.inter h2
    have hne' : {z | z ∈ (closedCubeSet Q)ᶜ ∧ g z ≠ 0}.Nonempty := ⟨x, hx, hne⟩
    have hpos : 0 < volume {z | z ∈ (closedCubeSet Q)ᶜ ∧ g z ≠ 0} := hopen.measure_pos _ hne'
    rw [hnull] at hpos
    exact lt_irrefl _ hpos
  /- the zero set is closed, hence contains the closure of the exteri -/
  have hclosed : IsClosed (g ⁻¹' {(0 : ℝ)}) := isClosed_singleton.preimage hgc
  have hsub : closure ((closedCubeSet Q)ᶜ) ⊆ g ⁻¹' {(0 : ℝ)} :=
    hclosed.closure_subset_iff.mpr fun x hx => hzeroOut x hx
  intro y hy
  exact hsub (cubeFaceSet_subset_closure_compl Q hy)

/-! ## 4. The frame, from the root's own data binders -/

/-- **The residue.**  A scalar has a continuous representative if some
continuous function agrees with it a.e.  For `W = u - v` on `□_m` this is NOT
implied by `u - v ∈ H¹₀(□_m)`; see the module docstring. -/
def HasContinuousRepresentative (W : Vec d → ℝ) : Prop :=
  ∃ g : Vec d → ℝ, Continuous g ∧ W =ᵐ[volume] g

/-- **THE PER-DATUM FRAME.**

From the root's own two data binders `hsol` and `hcomp` — solutions of the two
Dirichlet problems at the SAME boundary datum `h` and the SAME forcing `g` —
the `H¹₀` zero extension of `u - v` and its gradient carry every frame item of
the `L^∞` conversion except the continuous representative:

* the two agree with `u - v` and `∇u - ∇v` on the open cube;
* the value extension vanishes off the open cube;
* the pair is a GLOBAL weak-gradient graph, the value is integrable and
  compactly supported, each gradient coordinate is integrable;
* the gradient vanishes off the cube (`hGzero`).

Nothing beyond `hsol.1`/`hcomp.1` (the zero-trace conjuncts) is consumed. -/
theorem spineFrame_of_dirichletPair {Q : TriadicCube d} {a : CoeffField d} {sigmaBarM : ℝ}
    {u v h : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hsol : IsDirichletSolutionOn a Q u h g)
    (hcomp : IsDirichletSolutionOn (fun _ => sigmaBarM • (1 : Mat d)) Q v h g) :
    ∃ (W : Vec d → ℝ) (G : Vec d → Vec d),
      (∀ x ∈ openCubeSet Q, W x = u.toFun x - v.toFun x) ∧
        (∀ x ∈ openCubeSet Q, G x = u.grad x - v.grad x) ∧
        (∀ x, x ∉ openCubeSet Q → W x = 0) ∧
        HasWeakGradientOn Set.univ W G ∧
        Integrable W volume ∧
        HasCompactSupport W ∧
        (∀ i : Fin d, Integrable (fun y => G y i) volume) ∧
        (∀ y, y ∉ cubeSet Q → G y = 0) := by
  obtain ⟨w, hwF, hwG⟩ := exists_h10Function_sub_of_hasZeroTrace hsol.1 hcomp.1
  refine ⟨w.zeroExtension, w.zeroExtensionGrad, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [w.zeroExtension_apply_of_mem hx, hwF x]
  · intro x hx
    rw [w.zeroExtensionGrad_apply_of_mem hx, hwG x]
  · intro x hx
    exact w.zeroExtension_apply_of_not_mem hx
  · exact w.hasWeakGradientOn_univ_zeroExtension (measurableSet_openCubeSet Q)
  · exact integrable_zeroExtension w
  · exact hasCompactSupport_zeroExtension w
  · exact fun i => integrable_zeroExtensionGrad_coord w i
  · exact fun y hy => zeroExtensionGrad_eq_zero_of_not_mem_cubeSet w hy

end

end Algsuperdiff.Section4.Provider.Homogenization
