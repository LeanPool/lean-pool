/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderPointwise
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderCore

/-!
# CubeSchauderAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Cube Schauder: the representative rebuild and the zero-datum assembly

`ZeroDatumCubeSchauder d C0` bounds the **`H¹` witness's own `grad` field**
pointwise, and an `H¹` gradient is only defined almost everywhere.  The
existential in the statement is therefore load-bearing: one must *rebuild* the
witness so that its `grad` field is the continuous representative produced by
`CubeSchauderPointwise.campanatoSlopeLimit`.

This module does exactly that, and then assembles the two displays:

* `exists_h10Function_grad_eq` — the rebuild.  An `H¹₀` witness may have its
  `grad` field replaced by any almost-everywhere equal field: `L²` membership,
  the weak-gradient identity and the smooth-approximation package are all
  invariant under modification on a null set.
* `exists_mem_norm_le_of_energy` — the sharp energy bound gives a point of the
  cube where the representative is small.
* `exists_zeroDatumWitness_of_campanato` — the two displays of the zero-datum
  core, from the Campanato datum on **all** of `□_m` plus the a.e.
  identification of the limit field with the witness's gradient.

## The two residues, named

`exists_zeroDatumWitness_of_campanato` carries exactly two mathematical
hypotheses, both displayed in its own statement:

* `hE` — the Campanato bound at **every** base point of `□_m` (not only the
  interior half-cube `□_{m-1}` that `CubeSchauderCampanato.affineExcess_le_campanato`
  reaches).  The boundary regime is what supplies it.
* `hae` — the almost-everywhere identification `Ψ = ∇w`.

Neither is proved here.  This module is a **conditional A**: it proves that the
two residues *suffice* for `ZeroDatumCubeSchauder`, and nothing else.

## The sup bound without Poincaré

The `L^∞` leg is obtained from the `C^{0,1/2}` bound plus one point of the cube
where the field is small, and that point comes from the sharp Dirichlet energy
estimate `dirichletEnergy_le_of_isDivFormWeakSolutionOn_one` alone: a continuous
field that exceeds `A` everywhere would force the energy above `A²|□_m|`.  No
Poincaré inequality and no bound on the top-scale minimizer slope are needed.

## References

* ABK26; `Algsuperdiff/Frozen/External/CubeSchauder.lean`.
-/

namespace Algsuperdiff.Section4.Provider.Schauder

open MeasureTheory Filter Topology
open HCPolySupport
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay
open Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

noncomputable section

variable {d : ℕ}

/-! ## 1. The representative rebuild -/

/-- **The `H¹₀` witness may be rebuilt on an almost-everywhere equal gradient
field.**

Every field of `H10Function` is invariant under modification of `grad` on a null
set: `gradMemL2` by `MemLp.ae_eq`, `hasWeakGradient` because its right-hand side
is an integral, and `tendsto_approx_grad` because `eLpNorm` is an
almost-everywhere invariant.  The function itself is untouched. -/
theorem exists_h10Function_grad_eq {U : Set (Vec d)} (w : H10Function U)
    {Psi : Vec d → Vec d}
    (hae : ∀ᵐ y ∂(volume.restrict U), Psi y = w.toH1Function.grad y) :
    ∃ w' : H10Function U,
      w'.toH1Function.toFun = w.toH1Function.toFun ∧ w'.toH1Function.grad = Psi := by
  have hcoord : ∀ i : Fin d,
      (fun y => w.toH1Function.grad y i) =ᵐ[volume.restrict U] fun y => Psi y i := by
    intro i
    filter_upwards [hae] with y hy
    rw [hy]
  have hgradL2 : GradMemL2On U Psi := fun i =>
    MemLp.ae_eq (hcoord i) (w.toH1Function.gradMemL2 i)
  have hweak : HasWeakGradientOn U w.toH1Function.toFun Psi := by
    intro i φ hφ hφc hφs
    have h := w.toH1Function.hasWeakGradient i φ hφ hφc hφs
    rw [h]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hcoord i] with y hy
    rw [hy]
  have hgradtend : ∀ i : Fin d,
      Tendsto (fun n : ℕ => eLpNorm
        (fun x => (fderiv ℝ (w.approx n) x) (basisVec i) - Psi x i) 2
        (volume.restrict U)) atTop (𝓝 0) := by
    intro i
    refine (w.tendsto_approx_grad i).congr fun n => ?_
    refine eLpNorm_congr_ae ?_
    filter_upwards [hcoord i] with y hy
    rw [hy]
  exact ⟨⟨⟨w.toH1Function.toFun, Psi, w.toH1Function.memL2, hgradL2, hweak⟩,
    w.approx, w.approx_smooth, w.approx_hasCompactSupport, w.approx_support_subset,
    w.tendsto_approx, hgradtend⟩, rfl, rfl⟩

/-! ## 2. A small value of the representative from the energy -/

/-- The coordinate norm dominates the ambient sup norm squared. -/
theorem sq_norm_le_vecNormSq (v : Vec d) : ‖v‖ ^ 2 ≤ vecNormSq v := by
  have h1 : ‖v‖ ≤ Real.sqrt (vecNormSq v) := norm_le_slopeMagnitude v
  have h2 : (0 : ℝ) ≤ vecNormSq v := vecNormSq_nonneg v
  have h3 : Real.sqrt (vecNormSq v) ^ 2 = vecNormSq v := Real.sq_sqrt h2
  have h4 : ‖v‖ ^ 2 ≤ Real.sqrt (vecNormSq v) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  linarith only [h3, h4]

/-- **A point where the representative is small.**

If the Dirichlet energy of `F` on `U` is at most `A²|U|` and `Psi = F` almost
everywhere on `U`, then `Psi` comes within `δ` of `A` somewhere on `U`, for
every `δ > 0`. -/
theorem exists_mem_norm_le_of_energy {U : Set (Vec d)} (hUmeas : MeasurableSet U)
    (hUpos : 0 < (volume U).toReal)
    (hUtop : volume U ≠ ⊤) {F Psi : Vec d → Vec d}
    (hint : IntegrableOn (fun y => vecNormSq (F y)) U volume)
    (hae : ∀ᵐ y ∂(volume.restrict U), Psi y = F y)
    {A : ℝ} (hA : 0 ≤ A)
    (hM : ∫ y in U, vecNormSq (F y) ∂volume ≤ A ^ 2 * (volume U).toReal)
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ y ∈ U, ‖Psi y‖ ≤ A + delta := by
  by_contra hcon
  push Not at hcon
  have hlow : (fun _ : Vec d => (A + delta) ^ 2) ≤ᵐ[volume.restrict U]
      fun y => vecNormSq (F y) := by
    filter_upwards [hae, self_mem_ae_restrict hUmeas] with y hy hyU
    · have h1 : A + delta ≤ ‖Psi y‖ := (hcon y hyU).le
      have h2 : ‖Psi y‖ ^ 2 ≤ vecNormSq (Psi y) := sq_norm_le_vecNormSq _
      have h3 : (A + delta) ^ 2 ≤ ‖Psi y‖ ^ 2 :=
        pow_le_pow_left₀ (by linarith only [hA, hdelta]) h1 2
      rw [← hy]
      linarith only [h2, h3]
  have hconst : Integrable (fun _ : Vec d => (A + delta) ^ 2) (volume.restrict U) := by
    have : IsFiniteMeasure (volume.restrict U) := by
      refine ⟨?_⟩
      rw [Measure.restrict_apply_univ]
      exact lt_top_iff_ne_top.2 hUtop
    exact integrable_const _
  have hmono := integral_mono_ae hconst hint hlow
  rw [setIntegral_const, measureReal_def, smul_eq_mul] at hmono
  have hgap : A ^ 2 * (volume U).toReal < (A + delta) ^ 2 * (volume U).toReal := by
    have hsq : A ^ 2 < (A + delta) ^ 2 := by
      have hexp : (A + delta) ^ 2 - A ^ 2 = 2 * A * delta + delta ^ 2 := by ring
      have h1 : (0 : ℝ) ≤ 2 * A * delta :=
        mul_nonneg (mul_nonneg (by norm_num) hA) hdelta.le
      have h2 : (0 : ℝ) < delta ^ 2 := pow_pos hdelta 2
      linarith only [hexp, h1, h2]
    exact mul_lt_mul_of_pos_right hsq hUpos
  linarith only [hmono, hM, hgap]

/-! ## 3. The scale dictionary -/

/-- `√(3^m) = 3^{m/2}` in the frozen statement's `rpow` shape. -/
theorem sqrt_zpow_eq_rpow_half (m : ℤ) :
    Real.sqrt ((3 : ℝ) ^ m) = Real.rpow 3 ((m : ℝ) / 2) := by
  have hgoal : Real.rpow 3 ((m : ℝ) / 2) = (3 : ℝ) ^ ((m : ℝ) / 2) := rfl
  rw [hgoal, Real.sqrt_eq_rpow, ← Real.rpow_intCast 3 m,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

/-! ## 4. The zero-datum witness -/

/-- **The two displays of the zero-datum core, off the two named residues.**

From the Campanato datum `hE` at *every* base point of `□_m` and the
almost-everywhere identification `hae`, the solution `w` may be rebuilt so that
its own gradient field is `C^{0,1/2}` with constant `campanatoHolderConst d · K`
and bounded by `(√(3d) · KG + √3 · campanatoHolderConst d · K) · 3^{m/2}`.

Both hypotheses are displayed; nothing about them is claimed here. -/
theorem exists_zeroDatumWitness_of_campanato [NeZero d] (hd : 0 < d) {m : ℤ}
    {G : Vec d → Vec d} {KG : ℝ} (hKG : 0 ≤ KG)
    (hG : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) KG G)
    (w : H10Function (openCubeSet (originCube d m)))
    (hw : IsDivFormWeakSolutionOn (fun _ => (1 : Mat d))
      (openCubeSet (originCube d m)) w.toH1Function G)
    {K : ℝ} (hK : 0 ≤ K)
    (hE : ∀ z ∈ openCubeSet (originCube d m), ∀ j : ℤ, j ≤ m + 1 →
      affineExcess (truncatedWindow z m j) w.toH1Function.toFun
        ≤ K * Real.sqrt ((3 : ℝ) ^ j))
    (hae : ∀ᵐ y ∂(volume.restrict (openCubeSet (originCube d m))),
      campanatoSlopeLimit m (m + 1) w.toH1Function.toFun y = w.toH1Function.grad y) :
    ∃ w' : H10Function (openCubeSet (originCube d m)),
      IsDivFormWeakSolutionOn (fun _ => (1 : Mat d)) (openCubeSet (originCube d m))
          w'.toH1Function G ∧
        (∀ x ∈ openCubeSet (originCube d m),
            ‖w'.toH1Function.grad x‖
              ≤ (Real.sqrt (3 * (d : ℝ)) * KG + Real.sqrt 3 * (campanatoHolderConst d * K))
                * Real.rpow 3 ((m : ℝ) / 2)) ∧
        HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2)
          (campanatoHolderConst d * K) w'.toH1Function.grad := by
  obtain ⟨w', hfun, hgrad⟩ := exists_h10Function_grad_eq w hae
  have hUdom : IsOpenBoundedConvexDomain (openCubeSet (originCube d m)) :=
    isOpenBoundedConvexDomain_openCubeSet (originCube d m)
  have hUmeas : MeasurableSet (openCubeSet (originCube d m)) :=
    hUdom.isOpen.measurableSet
  have hUtop : volume (openCubeSet (originCube d m)) ≠ ⊤ := hUdom.volume_lt_top.ne
  have hUpos : 0 < (volume (openCubeSet (originCube d m))).toReal := by
    have hvol : (volume (openCubeSet (originCube d m))).toReal = ((3 : ℝ) ^ m) ^ d := by
      rw [HCPolySupport.volume_openCubeSet_toReal, HCPolySupport.cubeVolume_eq_pow_scale]
      norm_num [HCPolySupport.originCube]
    rw [hvol]
    positivity
  -- the equation transports
  have hw' : IsDivFormWeakSolutionOn (fun _ => (1 : Mat d))
      (openCubeSet (originCube d m)) w'.toH1Function G := by
    intro φ
    have h := hw φ
    have hcongr : (∫ x in openCubeSet (originCube d m),
          vecDot (matVecMul ((fun _ => (1 : Mat d)) x)
          (w'.toH1Function.grad x)) (φ.toH1Function.grad x) ∂volume)
        = ∫ x in openCubeSet (originCube d m),
          vecDot (matVecMul ((fun _ => (1 : Mat d)) x)
          (w.toH1Function.grad x)) (φ.toH1Function.grad x) ∂volume := by
      refine integral_congr_ae ?_
      filter_upwards [hae] with y hy
      rw [hgrad, hy]
    rw [hcongr]
    exact h
  -- the Hölder leg
  have hu2 : MemLp w.toH1Function.toFun 2
      (volume.restrict (openCubeSet (originCube d m))) := by
    simpa only [volumeMeasureOn] using w.toH1Function.memL2
  have hholPsi : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2 : ℝ)
      (campanatoHolderConst d * K) (campanatoSlopeLimit m (m + 1) w.toH1Function.toFun) :=
    holderSeminormBoundOn_campanatoSlopeLimit hd
      (Set.Subset.refl (openCubeSet (originCube d m))) (le_refl (m + 1)) hu2 hK
      (fun p hp q hq => by
        have h := norm_sub_lt_of_mem_openCubeSet hp hq
        rwa [show m + 1 - 1 = m by ring]) hE
  have hhol : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2 : ℝ)
      (campanatoHolderConst d * K) w'.toH1Function.grad := by
    rw [hgrad]
    exact hholPsi
  refine ⟨w', hw', ?_, hhol⟩
  -- the sup leg
  intro x hx
  -- the energy bound at the frozen forcing
  have : IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube d m))) :=
    hUdom.isFiniteMeasure_restrict_volume
  have hGL2 : MemVectorL2 (openCubeSet (originCube d m)) G :=
    memVectorL2_of_holderSeminormBoundOn hKG (by norm_num) hG
  have hGc : MemVectorL2 (openCubeSet (originCube d m)) (fun y => G y - G x) :=
    hGL2.sub (memLp_const (G x))
  have hwc : IsDivFormWeakSolutionOn (fun _ => (1 : Mat d))
      (openCubeSet (originCube d m)) w.toH1Function
      (fun y => G y - G x) := isDivFormWeakSolutionOn_sub_const hGL2 (G x) hw
  have henergy := dirichletEnergy_le_of_isDivFormWeakSolutionOn_one hGc w hwc
  have hintG : IntegrableOn (fun y => vecNormSq (G y - G x))
      (openCubeSet (originCube d m)) volume :=
    integrableOn_vecNormSq_of_memVectorL2 hGc
  have hosc : ∀ y ∈ openCubeSet (originCube d m), vecNormSq (G y - G x)
      ≤ (d : ℝ) * (KG ^ 2 * (3 : ℝ) ^ (m + 1)) := by
    intro y hy
    have htop : truncatedWindow x m (m + 1) = openCubeSet (originCube d m) :=
      truncatedWindow_top_eq hx
    have hGw : HolderSeminormBoundOn (truncatedWindow x m (m + 1)) (1 / 2) KG G := by
      rw [htop]; exact hG
    exact vecNormSq_sub_le_of_holderSeminormBoundOn_truncatedWindow hKG hGw
      (by rw [htop]; exact hy) (by rw [htop]; exact hx)
  have hbudget : ∫ y in openCubeSet (originCube d m), vecNormSq (G y - G x) ∂volume
      ≤ ((d : ℝ) * (KG ^ 2 * (3 : ℝ) ^ (m + 1)))
        * (volume (openCubeSet (originCube d m))).toReal := by
    have hmono := setIntegral_mono_on hintG (integrableOn_const hUtop) hUmeas hosc
    rwa [setIntegral_const, measureReal_def, smul_eq_mul, mul_comm] at hmono
  -- the small-value point
  set A : ℝ := Real.sqrt ((d : ℝ) * (KG ^ 2 * (3 : ℝ) ^ (m + 1))) with hAdef
  have hAnn : 0 ≤ A := Real.sqrt_nonneg _
  have hAsq : A ^ 2 = (d : ℝ) * (KG ^ 2 * (3 : ℝ) ^ (m + 1)) := by
    rw [hAdef, Real.sq_sqrt (by positivity)]
  have hgradint : IntegrableOn (fun y => vecNormSq (w.toH1Function.grad y))
      (openCubeSet (originCube d m)) volume :=
    integrableOn_vecNormSq_grad w.toH1Function
  have hpoint : ∀ delta : ℝ, 0 < delta → ∃ y ∈ openCubeSet (originCube d m),
      ‖campanatoSlopeLimit m (m + 1) w.toH1Function.toFun y‖ ≤ A + delta := by
    intro delta hdelta
    refine exists_mem_norm_le_of_energy hUmeas hUpos hUtop hgradint hae hAnn ?_ hdelta
    rw [hAsq]
    linarith only [henergy, hbudget]
  -- propagate by the Hölder bound
  have hdiam : ∀ y ∈ openCubeSet (originCube d m),
      ‖campanatoSlopeLimit m (m + 1) w.toH1Function.toFun x
        - campanatoSlopeLimit m (m + 1) w.toH1Function.toFun y‖
      ≤ campanatoHolderConst d * K * Real.sqrt ((3 : ℝ) ^ (m + 1)) := by
    intro y hy
    have hxy : ‖x - y‖ ≤ (3 : ℝ) ^ (m + 1) := by
      have htop : truncatedWindow x m (m + 1) = openCubeSet (originCube d m) :=
        truncatedWindow_top_eq hx
      refine norm_sub_le_of_mem_truncatedWindow_pair (m := m) (k := m + 1) (x := x) ?_ ?_
      · rw [htop]; exact hx
      · rw [htop]; exact hy
    refine (hholPsi x hx y hy).trans ?_
    have hmono : ‖x - y‖ ^ (1 / 2 : ℝ) ≤ ((3 : ℝ) ^ (m + 1)) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (norm_nonneg _) hxy (by norm_num)
    have hcnn : (0 : ℝ) ≤ campanatoHolderConst d * K :=
      mul_nonneg (campanatoHolderConst_nonneg d) hK
    refine (mul_le_mul_of_nonneg_left hmono hcnn).trans (le_of_eq ?_)
    rw [Real.sqrt_eq_rpow]
  have hbound : ‖campanatoSlopeLimit m (m + 1) w.toH1Function.toFun x‖
      ≤ A + campanatoHolderConst d * K * Real.sqrt ((3 : ℝ) ^ (m + 1)) := by
    refine le_of_forall_pos_le_add fun delta hdelta => ?_
    obtain ⟨y, hyU, hy⟩ := hpoint delta hdelta
    have htri : ‖campanatoSlopeLimit m (m + 1) w.toH1Function.toFun x‖
        ≤ ‖campanatoSlopeLimit m (m + 1) w.toH1Function.toFun x
            - campanatoSlopeLimit m (m + 1) w.toH1Function.toFun y‖
          + ‖campanatoSlopeLimit m (m + 1) w.toH1Function.toFun y‖ := by
      have h := norm_add_le (campanatoSlopeLimit m (m + 1) w.toH1Function.toFun x
        - campanatoSlopeLimit m (m + 1) w.toH1Function.toFun y)
        (campanatoSlopeLimit m (m + 1) w.toH1Function.toFun y)
      have hid : campanatoSlopeLimit m (m + 1) w.toH1Function.toFun x
          - campanatoSlopeLimit m (m + 1) w.toH1Function.toFun y
          + campanatoSlopeLimit m (m + 1) w.toH1Function.toFun y
          = campanatoSlopeLimit m (m + 1) w.toH1Function.toFun x := by abel
      rwa [hid] at h
    have h2 := hdiam y hyU
    linarith only [htri, h2, hy]
  -- the final shape
  rw [hgrad]
  refine hbound.trans (le_of_eq ?_)
  have hsplit : Real.sqrt ((3 : ℝ) ^ (m + 1)) = Real.sqrt 3 * Real.sqrt ((3 : ℝ) ^ m) := by
    rw [show ((3 : ℝ) ^ (m + 1)) = 3 * (3 : ℝ) ^ m by
      rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]; ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have hAval : A = Real.sqrt (3 * (d : ℝ)) * KG * Real.sqrt ((3 : ℝ) ^ m) := by
    rw [hAdef, show (d : ℝ) * (KG ^ 2 * (3 : ℝ) ^ (m + 1))
        = (3 * (d : ℝ)) * (KG ^ 2 * (3 : ℝ) ^ m) by
      rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]; ring,
      Real.sqrt_mul (by positivity), Real.sqrt_mul (sq_nonneg KG), Real.sqrt_sq hKG,
      ← mul_assoc]
  rw [hAval, hsplit, ← sqrt_zpow_eq_rpow_half m]
  ring

/-! ## 5. The zero-datum core off the two residues -/

/-- The constant delivered by the route: `√(3d) + (√3 + 1)·campanatoHolderConst d·C`. -/
def zeroDatumRouteConst (d : ℕ) (C : ℝ) : ℝ :=
  Real.sqrt (3 * (d : ℝ)) + Real.sqrt 3 * (campanatoHolderConst d * C)
    + campanatoHolderConst d * C

theorem zeroDatumRouteConst_nonneg (d : ℕ) {C : ℝ} (hC : 0 ≤ C) :
    0 ≤ zeroDatumRouteConst d C := by
  have h1 : (0 : ℝ) ≤ Real.sqrt (3 * (d : ℝ)) := Real.sqrt_nonneg _
  have h2 : (0 : ℝ) ≤ campanatoHolderConst d * C :=
    mul_nonneg (campanatoHolderConst_nonneg d) hC
  have h3 : (0 : ℝ) ≤ Real.sqrt 3 * (campanatoHolderConst d * C) :=
    mul_nonneg (Real.sqrt_nonneg 3) h2
  rw [zeroDatumRouteConst]
  linarith only [h1, h2, h3]

/-- **`ZeroDatumCubeSchauder` off the two named residues.**

If, at every scale and every `C^{0,1/2}` forcing, the zero-datum solution can be
produced together with (i) the Campanato bound at **every** base point of `□_m`
and (ii) the almost-everywhere identification of its gradient with the limit
field, then the zero-datum cube Schauder core holds at the explicit constant
`zeroDatumRouteConst d C`.

Both residues are hypotheses of this statement; nothing about them is claimed
here.  This is the exact reduction the route delivers. -/
theorem zeroDatumCubeSchauder_of_residues (hd : 0 < d) {C : ℝ} (hC : 0 ≤ C)
    (hres : ∀ (m : ℤ) (G : Vec d → Vec d) (KG : ℝ), 0 ≤ KG →
      HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) KG G →
      ∃ w : H10Function (openCubeSet (originCube d m)),
        IsDivFormWeakSolutionOn (fun _ => (1 : Mat d)) (openCubeSet (originCube d m))
            w.toH1Function G ∧
          (∀ z ∈ openCubeSet (originCube d m), ∀ j : ℤ, j ≤ m + 1 →
            affineExcess (truncatedWindow z m j) w.toH1Function.toFun
              ≤ C * KG * Real.sqrt ((3 : ℝ) ^ j)) ∧
          (∀ᵐ y ∂(volume.restrict (openCubeSet (originCube d m))),
            campanatoSlopeLimit m (m + 1) w.toH1Function.toFun y = w.toH1Function.grad y)) :
    ZeroDatumCubeSchauder d (zeroDatumRouteConst d C) := by
  have : NeZero d := ⟨by omega⟩
  intro m G KG hG
  have hKG : 0 ≤ KG := holderSeminormBoundOn_nonneg_openCubeSet hd hG
  obtain ⟨w, hw, hE, hae⟩ := hres m G KG hKG hG
  have hKnn : 0 ≤ C * KG := mul_nonneg hC hKG
  obtain ⟨w', hw', hsup, hhol⟩ :=
    exists_zeroDatumWitness_of_campanato hd hKG hG w hw hKnn hE hae
  refine ⟨w', hw', ?_, ?_⟩
  · intro x hx
    refine (hsup x hx).trans ?_
    rw [zeroDatumRouteConst]
    have hid : (Real.sqrt (3 * (d : ℝ)) + Real.sqrt 3 * (campanatoHolderConst d * C)
          + campanatoHolderConst d * C) * Real.rpow 3 ((m : ℝ) / 2) * KG
        - (Real.sqrt (3 * (d : ℝ)) * KG
            + Real.sqrt 3 * (campanatoHolderConst d * (C * KG)))
          * Real.rpow 3 ((m : ℝ) / 2)
        = campanatoHolderConst d * C * KG * Real.rpow 3 ((m : ℝ) / 2) := by ring
    have hnn : (0 : ℝ) ≤ campanatoHolderConst d * C * KG * Real.rpow 3 ((m : ℝ) / 2) :=
      mul_nonneg (mul_nonneg (mul_nonneg (campanatoHolderConst_nonneg d) hC) hKG)
        (rpow_three_pos _).le
    linarith only [hid, hnn]
  · refine hhol.mono_const ?_
    have h1 : (0 : ℝ) ≤ Real.sqrt (3 * (d : ℝ)) * KG :=
      mul_nonneg (Real.sqrt_nonneg _) hKG
    have h2 : (0 : ℝ) ≤ Real.sqrt 3 * (campanatoHolderConst d * C) * KG := by
      have h := mul_nonneg (Real.sqrt_nonneg 3)
        (mul_nonneg (campanatoHolderConst_nonneg d) hC)
      exact mul_nonneg h hKG
    have hid : zeroDatumRouteConst d C * KG
        = Real.sqrt (3 * (d : ℝ)) * KG + Real.sqrt 3 * (campanatoHolderConst d * C) * KG
          + campanatoHolderConst d * (C * KG) := by
      rw [zeroDatumRouteConst]
      ring
    rw [hid]
    linarith only [h1, h2]

end

end Algsuperdiff.Section4.Provider.Schauder
