/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderExistence
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.AffineSplitHarmonic
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.EquationRestriction

/-!
# CubeSchauderFreezing

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Cube Schauder: the freezing step (harmonic approximation with divergence forcing)

If `u` solves `-Δ u = ∇·G` on a window `U` and `V ⊆ U` is an interior sub-domain,
then for **any** constant vector `c` the same `u` solves `-Δ u = ∇·(G - c)` on
`V`, because a constant field is weakly divergence free.  Solving the zero-trace
problem `-Δ w = ∇·(G - c)` on `V` and setting `h := u - w` produces a *weakly
harmonic* comparison function on `V` together with the sharp energy bound

```text
  ∫_V |∇w|² ≤ ∫_V |G - c|² .
```

Taking `c = G(x₀)` for a point `x₀` of the sub-cube and using the `C^{0,1/2}`
bound on `G` gives the **freezing gain**: the harmonic approximation error is
controlled by the *oscillation* of the forcing over the sub-cube, hence by
`(side)^{1/2} · [G]_{C^{0,1/2}}` rather than by `‖G‖`.

This is Armstrong--Kuusi `ellipticregularity.tex`, the display
`e.harmapprox.Schauder` (~2660) specialized to `a = I_d` (where the `‖a -
I_d‖_{L^∞}` leg vanishes identically), in the development's own carriers.

## Main results

* `integral_vecDot_const_h10_eq_zero` — a constant field pairs to zero against
  the gradient of a zero-trace test function.
* `isDivFormWeakSolutionOn_sub_const` — the equation is invariant under
  subtracting a constant from the forcing.
* `exists_h10_isDivFormWeakSolutionOn_one` — the zero-trace solution of
  `-Δ w = ∇·F` on an arbitrary open bounded convex domain.
* `dirichletEnergy_le_of_isDivFormWeakSolutionOn_one` — the sharp energy bound
  `∫|∇w|² ≤ ∫|F|²` for the zero-trace solution.
* `exists_frozenHarmonicReplacement` — the freezing step on an arbitrary open
  bounded convex domain.
* `exists_frozenHarmonicReplacement_openCubeSet` — the freezing step at a
  triadic sub-cube of a window, with the oscillation bound made explicit:
  `∫_{□} |∇w|² ≤ d · KG² · 3^{Q.scale} · |□|`.

## References

* ABK26; `Algsuperdiff/Frozen/External/CubeSchauder.lean`.
* Armstrong--Kuusi, *Elliptic Regularity* (`ellipticregularity.tex`),
  Propositions `p.Schauder.Calpha` and `p.Schauder.C1alpha`.
-/

namespace Algsuperdiff.Section4.Provider.Schauder

open MeasureTheory
open HCPolySupport
open Algsuperdiff.Section4.Support

variable {d : ℕ}

/-! ## 1. The identity background -/

/-- The identity coefficient field drops out of the flux pairing. -/
theorem integral_vecDot_matVecMul_one {U : Set (Vec d)} (F p : Vec d → Vec d) :
    ∫ x in U, vecDot (matVecMul ((fun _ => (1 : Mat d)) x) (F x)) (p x) ∂volume =
      ∫ x in U, vecDot (F x) (p x) ∂volume :=
  integral_congr_ae (Filter.Eventually.of_forall fun x => by
    change vecDot (matVecMul (1 : Mat d) (F x)) (p x) = vecDot (F x) (p x)
    rw [matVecMul_one])

/-- `-Δ u = ∇·g` in the development's carrier, unfolded at the identity background. -/
theorem isDivFormWeakSolutionOn_one_iff {U : Set (Vec d)} {u : H1Function U}
    {g : Vec d → Vec d} :
    IsDivFormWeakSolutionOn (fun _ => (1 : Mat d)) U u g ↔
      ∀ φ : H10Function U,
        ∫ x in U, vecDot (u.grad x) (φ.toH1Function.grad x) ∂volume =
          -∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂volume := by
  unfold IsDivFormWeakSolutionOn
  simp only [integral_vecDot_matVecMul_one]

/-- The identity is the unit diffusivity. -/
theorem isEllipticFieldOn_one {U : Set (Vec d)} (hU : MeasurableSet U) :
    IsEllipticFieldOn 1 1 U (fun _ => (1 : Mat d)) := by
  have h := isEllipticFieldOn_smul_one (d := d) (sigma := 1) (by norm_num) hU
  simpa only [one_smul] using h

/-! ## 2. A constant field is weakly divergence free -/

/-- **A constant field pairs to zero against zero-trace gradients.**  This is the
weak statement `∇ · c = 0` for a constant vector `c`, and it is the algebraic
heart of the freezing step. -/
theorem integral_vecDot_const_h10_eq_zero {U : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)] (c : Vec d) (φ : H10Function U) :
    ∫ x in U, vecDot c (φ.toH1Function.grad x) ∂volume = 0 := by
  have hint : ∀ i : Fin d,
      Integrable (fun y => c i * φ.toH1Function.grad y i) (volume.restrict U) := by
    intro i
    have h : Integrable (fun y => φ.toH1Function.grad y i) (volume.restrict U) := by
      have h2 := φ.toH1Function.gradMemL2 i
      simpa only [volumeMeasureOn] using
        h2.integrable (μ := volume.restrict U) (by norm_num)
    exact h.const_mul (c i)
  have hrw : ∀ y, vecDot c (φ.toH1Function.grad y) =
      ∑ i : Fin d, c i * φ.toH1Function.grad y i := fun y => by rw [vecDot]
  calc ∫ y in U, vecDot c (φ.toH1Function.grad y) ∂volume
      = ∫ y in U, ∑ i : Fin d, c i * φ.toH1Function.grad y i ∂volume :=
        integral_congr_ae (Filter.Eventually.of_forall hrw)
    _ = ∑ i : Fin d, ∫ y in U, c i * φ.toH1Function.grad y i ∂volume :=
        integral_finsetSum _ fun i _ => hint i
    _ = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [integral_const_mul,
          Algsuperdiff.Section4.Provider.ExcessDecay.integral_grad_coord_h10_eq_zero φ i,
          mul_zero]

/-- **Freezing invariance of the equation.**  Subtracting a constant from the
forcing does not change the divergence-form weak equation. -/
theorem isDivFormWeakSolutionOn_sub_const {U : Set (Vec d)}
    [IsFiniteMeasure (volumeMeasureOn U)] {a : CoeffField d} {u : H1Function U}
    {g : Vec d → Vec d} (hg : MemVectorL2 U g) (c : Vec d)
    (hu : IsDivFormWeakSolutionOn a U u g) :
    IsDivFormWeakSolutionOn a U u (fun x => g x - c) := by
  have hc : MemVectorL2 U (fun _ : Vec d => c) := memLp_const c
  intro φ
  rw [integral_vecDot_sub_split (F := g) (G := fun _ => c) hg hc (fun _ => rfl) φ,
    integral_vecDot_const_h10_eq_zero c φ, sub_zero]
  exact hu φ

/-! ## 3. Zero-trace solvability and the sharp energy bound -/

/-- **The zero-datum comparator exists on any open bounded convex domain.**  For
`F ∈ L²(U)` there is `w ∈ H¹₀(U)` with `-Δ w = ∇·F` weakly. -/
theorem exists_h10_isDivFormWeakSolutionOn_one [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hUne : U.Nonempty)
    {F : Vec d → Vec d} (hF : MemVectorL2 U F) :
    ∃ w : H10Function U,
      IsDivFormWeakSolutionOn (fun _ => (1 : Mat d)) U w.toH1Function F := by
  have : IsFiniteMeasure (volumeMeasureOn U) := hU.isFiniteMeasure_restrict_volume
  have hreal :=
    PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_convexDomain
      hU
  obtain ⟨w, hw⟩ :=
    exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
      (a := fun _ => (1 : Mat d)) (U := U) (g := fun x => -F x) (lam := 1) (Lam := 1)
      hF.neg hreal hUne (isEllipticFieldOn_one hU.isOpen.measurableSet)
  exact ⟨w,
    (isZeroTraceDirichletRhsWeakSolution_iff_isDivFormWeakSolutionOn
      (u := w.toH1Function) (w := w) (g := F) fun _ => rfl).1 hw⟩

/-- The Dirichlet energy of an `H¹` function is integrable on its domain. -/
theorem integrableOn_vecNormSq_grad {U : Set (Vec d)} (u : H1Function U) :
    IntegrableOn (fun x => vecNormSq (u.grad x)) U volume :=
  Algsuperdiff.Section4.Provider.ExcessDecay.integrableOn_vecDot_grad u u

/-- The squared Euclidean length of an `L²` field is integrable. -/
theorem integrableOn_vecNormSq_of_memVectorL2 {U : Set (Vec d)} {F : Vec d → Vec d}
    (hF : MemVectorL2 U F) : IntegrableOn (fun x => vecNormSq (F x)) U volume :=
  integrableOn_vecDot_of_memVectorL2 hF hF

/-- **The sharp zero-trace energy bound.**  A zero-trace weak solution of
`-Δ w = ∇·F` has Dirichlet energy at most the `L²` energy of the forcing.

The proof tests the equation with `w` itself and applies Young's inequality
`|ξ·η| ≤ |ξ|²/2 + |η|²/2` pointwise; the balanced split reproduces the sharp
constant `1`. -/
theorem dirichletEnergy_le_of_isDivFormWeakSolutionOn_one {U : Set (Vec d)}
    {F : Vec d → Vec d} (hF : MemVectorL2 U F) (w : H10Function U)
    (hw : IsDivFormWeakSolutionOn (fun _ => (1 : Mat d)) U w.toH1Function F) :
    ∫ x in U, vecNormSq (w.toH1Function.grad x) ∂volume ≤
      ∫ x in U, vecNormSq (F x) ∂volume := by
  set E : ℝ := ∫ x in U, vecNormSq (w.toH1Function.grad x) ∂volume with hEdef
  set N : ℝ := ∫ x in U, vecNormSq (F x) ∂volume with hNdef
  have heq : E = -∫ x in U, vecDot (F x) (w.toH1Function.grad x) ∂volume := by
    rw [hEdef]
    exact isDivFormWeakSolutionOn_one_iff.1 hw w
  have hint1 : IntegrableOn (fun x => vecDot (F x) (w.toH1Function.grad x)) U volume :=
    integrableOn_vecDot_of_memVectorL2 hF w.toH1Function.grad_memVectorL2
  have hint2 : IntegrableOn (fun x => vecNormSq (F x) / 2 +
      vecNormSq (w.toH1Function.grad x) / 2) U volume :=
    ((integrableOn_vecNormSq_of_memVectorL2 hF).div_const 2).add
      ((integrableOn_vecNormSq_grad w.toH1Function).div_const 2)
  have hpt : ∀ x, -vecDot (F x) (w.toH1Function.grad x) ≤
      vecNormSq (F x) / 2 + vecNormSq (w.toH1Function.grad x) / 2 := by
    intro x
    have h := abs_vecDot_le_add_halves_vecNormSq (F x) (w.toH1Function.grad x)
    have h2 : -vecDot (F x) (w.toH1Function.grad x) ≤
        |vecDot (F x) (w.toH1Function.grad x)| := neg_le_abs _
    linarith only [h, h2]
  have hmono : (∫ x in U, -vecDot (F x) (w.toH1Function.grad x) ∂volume) ≤
      ∫ x in U, (vecNormSq (F x) / 2 + vecNormSq (w.toH1Function.grad x) / 2) ∂volume :=
    integral_mono hint1.neg hint2 hpt
  have hsplit : (∫ x in U, (vecNormSq (F x) / 2 +
      vecNormSq (w.toH1Function.grad x) / 2) ∂volume) = N / 2 + E / 2 := by
    rw [integral_add ((integrableOn_vecNormSq_of_memVectorL2 hF).div_const 2)
      ((integrableOn_vecNormSq_grad w.toH1Function).div_const 2),
      integral_div, integral_div, hEdef, hNdef]
  rw [integral_neg, ← heq, hsplit] at hmono
  linarith only [hmono]

/-! ## 4. The freezing step -/

/-- **The freezing step (harmonic approximation with divergence forcing).**

Let `u` solve `-Δ u = ∇·G` weakly on an open bounded convex domain `U` and let
`c` be an arbitrary constant vector.  Then there is `w ∈ H¹₀(U)` with

* `-Δ w = ∇·(G - c)` weakly on `U`,
* `u - w` **weakly harmonic** on `U`, and
* `∫_U |∇w|² ≤ ∫_U |G - c|²`.

With `c := G(x₀)` the right side is the squared `L²` oscillation of the forcing,
which is the freezing gain of the Schauder argument. -/
theorem exists_frozenHarmonicReplacement [NeZero d] {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) (hUne : U.Nonempty) (u : H1Function U)
    {G : Vec d → Vec d} (hG : MemVectorL2 U G)
    (hu : IsDivFormWeakSolutionOn (fun _ => (1 : Mat d)) U u G) (c : Vec d) :
    ∃ w : H10Function U,
      IsDivFormWeakSolutionOn (fun _ => (1 : Mat d)) U w.toH1Function
          (fun x => G x - c) ∧
        IsWeaklyHarmonicOn U (u - w.toH1Function) ∧
          ∫ x in U, vecNormSq (w.toH1Function.grad x) ∂volume ≤
            ∫ x in U, vecNormSq (G x - c) ∂volume := by
  have : IsFiniteMeasure (volumeMeasureOn U) := hU.isFiniteMeasure_restrict_volume
  have hc : MemVectorL2 U (fun _ : Vec d => c) := memLp_const c
  have hGc : MemVectorL2 U (fun x => G x - c) := hG.sub hc
  obtain ⟨w, hw⟩ := exists_h10_isDivFormWeakSolutionOn_one hU hUne hGc
  refine ⟨w, hw, ?_, dirichletEnergy_le_of_isDivFormWeakSolutionOn_one hGc w hw⟩
  have hufroze : IsDivFormWeakSolutionOn (fun _ => (1 : Mat d)) U u (fun x => G x - c) :=
    isDivFormWeakSolutionOn_sub_const hG c hu
  intro φ
  have h1 := isDivFormWeakSolutionOn_one_iff.1 hufroze φ
  have h2 := isDivFormWeakSolutionOn_one_iff.1 hw φ
  have hrw : ∀ y, vecDot ((u - w.toH1Function).grad y) (φ.toH1Function.grad y) =
      vecDot (u.grad y) (φ.toH1Function.grad y) -
        vecDot (w.toH1Function.grad y) (φ.toH1Function.grad y) := by
    intro y
    rw [H1Function.sub_grad, vecDot, vecDot, vecDot, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [Pi.sub_apply]
      ring
  calc ∫ y in U, vecDot ((u - w.toH1Function).grad y) (φ.toH1Function.grad y) ∂volume
      = ∫ y in U, (vecDot (u.grad y) (φ.toH1Function.grad y) -
          vecDot (w.toH1Function.grad y) (φ.toH1Function.grad y)) ∂volume :=
        integral_congr_ae (Filter.Eventually.of_forall hrw)
    _ = (∫ y in U, vecDot (u.grad y) (φ.toH1Function.grad y) ∂volume) -
          ∫ y in U, vecDot (w.toH1Function.grad y) (φ.toH1Function.grad y) ∂volume :=
        integral_sub
          (Algsuperdiff.Section4.Provider.ExcessDecay.integrableOn_vecDot_grad u
            φ.toH1Function)
          (Algsuperdiff.Section4.Provider.ExcessDecay.integrableOn_vecDot_grad
            w.toH1Function φ.toH1Function)
    _ = 0 := by rw [h1, h2, sub_self]

/-! ## 5. The freezing gain on a triadic sub-cube -/

/-- **The sup-norm diameter of a triadic cube is its side length.** -/
theorem norm_sub_le_of_mem_openCubeSet {Q : TriadicCube d} {x y : Vec d}
    (hx : x ∈ openCubeSet Q) (hy : y ∈ openCubeSet Q) :
    ‖x - y‖ ≤ cubeScaleFactor Q := by
  have hs : (0 : ℝ) < cubeScaleFactor Q := by
    rw [cubeScaleFactor]
    exact zpow_pos (by norm_num) _
  refine (pi_norm_le_iff_of_nonneg hs.le).2 fun i => ?_
  have hxi := hx i
  have hyi := hy i
  simp only [Pi.sub_apply, Real.norm_eq_abs, abs_le]
  exact ⟨by linarith only [hxi.1, hyi.2], by linarith only [hxi.2, hyi.1]⟩

/-- The Euclidean square length is at most `d` times the squared sup norm. -/
theorem vecNormSq_le_dim_mul_sq_norm (v : Vec d) : vecNormSq v ≤ (d : ℝ) * ‖v‖ ^ 2 := by
  have hstep : ∀ i : Fin d, v i * v i ≤ ‖v‖ ^ 2 := by
    intro i
    have h := norm_le_pi_norm v i
    rw [Real.norm_eq_abs] at h
    have habs : |v i| * |v i| ≤ ‖v‖ * ‖v‖ :=
      mul_le_mul h h (abs_nonneg _) (norm_nonneg _)
    rw [abs_mul_abs_self] at habs
    rw [pow_two]
    exact habs
  have hsum : vecNormSq v = ∑ _i : Fin d, v _i * v _i := by rw [vecNormSq, vecDot]
  rw [hsum]
  calc ∑ _i : Fin d, v _i * v _i ≤ ∑ _i : Fin d, ‖v‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => hstep i
    _ = (d : ℝ) * ‖v‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The pointwise oscillation bound produced by a `C^{0,1/2}` forcing on a cube. -/
theorem vecNormSq_sub_le_of_holderSeminormBoundOn_openCubeSet {Q : TriadicCube d}
    {G : Vec d → Vec d} {KG : ℝ} (hKG : 0 ≤ KG)
    (hG : HolderSeminormBoundOn (openCubeSet Q) (1 / 2) KG G)
    {x0 : Vec d} (hx0 : x0 ∈ openCubeSet Q) {x : Vec d} (hx : x ∈ openCubeSet Q) :
    vecNormSq (G x - G x0) ≤ (d : ℝ) * (KG ^ 2 * cubeScaleFactor Q) := by
  have hs : (0 : ℝ) < cubeScaleFactor Q := by
    rw [cubeScaleFactor]
    exact zpow_pos (by norm_num) _
  have hdiam : ‖x - x0‖ ≤ cubeScaleFactor Q := norm_sub_le_of_mem_openCubeSet hx hx0
  have hmono : ‖x - x0‖ ^ (1 / 2 : ℝ) ≤ (cubeScaleFactor Q) ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow (norm_nonneg _) hdiam (by norm_num)
  have hbd : ‖G x - G x0‖ ≤ KG * (cubeScaleFactor Q) ^ (1 / 2 : ℝ) :=
    (hG x hx x0 hx0).trans (mul_le_mul_of_nonneg_left hmono hKG)
  have hsq : ‖G x - G x0‖ ^ 2 ≤ (KG * (cubeScaleFactor Q) ^ (1 / 2 : ℝ)) ^ 2 := by
    refine pow_le_pow_left₀ (norm_nonneg _) hbd 2
  have hexp : (KG * (cubeScaleFactor Q) ^ (1 / 2 : ℝ)) ^ 2 = KG ^ 2 * cubeScaleFactor Q := by
    rw [mul_pow, ← Real.rpow_natCast ((cubeScaleFactor Q) ^ (1 / 2 : ℝ)) 2,
      ← Real.rpow_mul hs.le]
    norm_num
  have hdim := vecNormSq_le_dim_mul_sq_norm (G x - G x0)
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hchain : (d : ℝ) * ‖G x - G x0‖ ^ 2 ≤ (d : ℝ) * (KG ^ 2 * cubeScaleFactor Q) := by
    rw [← hexp]
    exact mul_le_mul_of_nonneg_left hsq hdnn
  linarith only [hdim, hchain]

end Algsuperdiff.Section4.Provider.Schauder
