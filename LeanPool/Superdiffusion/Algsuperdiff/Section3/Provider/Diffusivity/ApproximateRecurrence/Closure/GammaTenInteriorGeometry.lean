/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure.GammaTenInteriorFamily
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationGammaFold
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationOscillationBridge
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.OscillationCubeFamily
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.OscillationDecayAverage

/-!
# GammaTenInteriorGeometry

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The interior mesh refines into the interior mesh, at cost `2`

ABK26, `e.nablaw.oscillations`, `e.lower.bound.oscillations`,
`e.recurrence.params`.

## What this module supplies

`Closure.GammaTenInteriorFamily.exists_besovEnvelope_of_family_depth_oscillation`
runs the Besov envelope device on an arbitrary sub-mesh `I`, and asks for the
per-depth input in the form

```
  avsum_{R in I} avsum_{R' in desc(R,i)} E[ osc_{n-i}(u)(R')^4 ]  <=  D i .
```

The depth-indexed endpoints of `Closure.GammaTenDepthOscillation` deliver instead
the **interior grid** average at scale `n - i`,

```
  avsum_{R' in interiorMesoCubeGrid d K (n-i) (m-h-1)} E[ osc_{n-i}(u)(R')^4 ] .
```

Two facts connect them, and both are proved here.

* **Refinement stays interior**
  (`mem_interiorMesoCubeGrid_of_mem_descendantsAtDepth`).  If the cell `R` of
  scale `n` has its *enlarged* window `z_R + cu_{outer+1}` inside `cu_K`, then
  every depth-`i` descendant `R'` has `z_{R'} + cu_{outer}` inside `cu_K`,
  because the site `z_{R'}` is a point of `R` and therefore within `3^n/2` of
  `z_R`, and `3^n/2 + 3^{outer}/2 <= 3^{outer+1}/2` as soon as `n <= outer`.
  So the source mesh is read at the window scale one **larger** than the
  target: `interiorMesoCubeGrid d K n (m-h)` refines into `interiorMesoCubeGrid
  d K (n-i) (m-h-1)`, the exact carrier.

* **The interior mesh is at least half the full mesh**
  (`card_mesoCubeGrid_le_two_mul_card_interiorMesoCubeGrid`).  This is the
  boundary count of `LocalizationFluctuationMeshTransfer.one_sub_interior_card_ratio_le`
  read once, under the recurrence's own large-cube gate; the resulting
  cardinality ratio `|T| / (|I| 3^{d i})` is then below `2` at **every** depth,
  since numerator and denominator both gain the factor `3^{d i}`.

The composite `cubeFamilyAverage_descendantsAverage_interiorMesoCubeGrid_le`
is the per-depth input of the family device, at the cost `2` and no other.

## Binders

Cube-index arithmetic and finite combinatorics, plus the two scale gates `n <=
K`, `n <= outer` and the numerical boundary gate `d 3^{g-p} <= 1/2`, which
`Closure.GammaTenInteriorGeometry.mesh_boundary_half_of_gamma_threshold`
produces from
`LocalizationFluctuationGammaFold.exists_gamma_threshold_mesh_boundary` and the
large-cube gate.  No smallness gate is assumed, nothing about the corrector,
the coefficient field or the sample space occurs.

## Scope

Internal Provider infrastructure for the Step-2 fluctuation estimate.  There is
no `sorry`, no `admit`, no custom axiom and no `set_option maxHeartbeats`.

## References

* ABK26, `e.nablaw.oscillations`, `e.lower.bound.oscillations`,
  `e.recurrence.params`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book.Ch03 MeasureTheory
open Algsuperdiff.Section3.Provider.Diffusivity.Corrector

noncomputable section

variable {d : ℕ}

/-! ## The site of a descendant is a point of the parent -/

/-- **The site of a descendant is inside the parent cube.**  Unconditional. -/
theorem abs_triadicCubeShift_sub_lt_of_mem_descendantsAtDepth {R R' : TriadicCube d}
    {i : ℕ} (hR' : R' ∈ descendantsAtDepth R i) (k : Fin d) :
    |triadicCubeShift R' k - triadicCubeShift R k| < (3 : ℝ) ^ R.scale / 2 := by
  have hself : triadicCubeShift R' ∈ openCubeAtScale (triadicCubeShift R') R'.scale :=
    mem_openCubeAtScale_self _ _
  rw [openCubeAtScale_triadicCubeShift_eq_openCubeSet] at hself
  have hsub : openCubeSet R' ⊆ openCubeSet R :=
    openCubeSet_subset_of_mem_descendantsAtDepth hR'
  have hmem : triadicCubeShift R' ∈
      openCubeAtScale (triadicCubeShift R) R.scale := by
    rw [openCubeAtScale_triadicCubeShift_eq_openCubeSet]
    exact hsub hself
  exact (mem_openCubeAtScale_iff _ _ _).mp hmem k

/-! ## Refinement of the interior mesh -/

/-- **The descendants of an interior cell are interior at the finer scale.**

If `R` is a cell of the interior mesh at scale `n` and window scale `outer + 1`,
then every depth-`i` descendant of `R` is a cell of the interior mesh at scale
`n - i` and window scale `outer`.  The window scale drops by one and nothing
else moves.

only on the two scale gates `n <= K` and `n <= outer`. -/
theorem mem_interiorMesoCubeGrid_of_mem_descendantsAtDepth {K n outer : ℤ}
    {R R' : TriadicCube d} {i : ℕ} (hnK : n ≤ K) (hno : n ≤ outer)
    (hR : R ∈ interiorMesoCubeGrid d K n outer)
    (hR' : R' ∈ descendantsAtDepth R i) :
    R' ∈ interiorMesoCubeGrid d K (n - (i : ℤ)) (outer - 1) := by
  classical
  have hRmesh : R ∈ mesoCubeGrid d K n := interiorMesoCubeGrid_subset hR
  have hscale : R.scale = n := scale_eq_of_mem_mesoCubeGrid hRmesh
  have hniK : n - (i : ℤ) ≤ K := by omega
  -- the coarse membership
  have hmesh : R' ∈ mesoCubeGrid d K (n - (i : ℤ)) := by
    rw [mesoCubeGrid_eq_descendantsAtDepth hnK] at hRmesh
    have hstep : R' ∈ descendantsAtDepth (originCube d K) ((K - n).toNat + i) :=
      mem_descendantsAtDepth_add hRmesh hR'
    have hcast : (K - n).toNat + i = (K - (n - (i : ℤ))).toNat := by omega
    rw [hcast] at hstep
    rw [mesoCubeGrid_eq_descendantsAtDepth hniK]
    exact hstep
  refine mem_interiorMesoCubeGrid_iff.mpr ⟨hmesh, ?_⟩
  -- the window containment
  have hwin : openCubeAtScale (triadicCubeShift R) (outer + 1) ⊆
      openCubeSet (originCube d K) := by
    have h := window_subset_of_mem_interiorMesoCubeGrid hR
    rwa [openCubeAtScale_eq_translateSet, openCubeAtScale_zero_eq_openCubeSet_originCube]
  have hstep : openCubeAtScale (triadicCubeShift R') (outer - 1 + 1) ⊆
      openCubeAtScale (triadicCubeShift R) (outer + 1) := by
    refine openCubeAtScale_subset_of_forall_abs_add_le fun k => ?_
    have hdist := abs_triadicCubeShift_sub_lt_of_mem_descendantsAtDepth hR' k
    rw [hscale] at hdist
    have hpow : (3 : ℝ) ^ n ≤ (3 : ℝ) ^ outer :=
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 3) hno
    have hout : (0 : ℝ) < (3 : ℝ) ^ outer := zpow_three_pos outer
    have hsucc : (3 : ℝ) ^ (outer + 1) = 3 * (3 : ℝ) ^ outer := by
      rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0), zpow_one]; ring
    rw [show outer - 1 + 1 = outer by ring, hsucc]
    linarith
  have hfinal : openCubeAtScale (triadicCubeShift R') (outer - 1 + 1) ⊆
      openCubeSet (originCube d K) := fun x hx => hwin (hstep hx)
  rwa [openCubeAtScale_eq_translateSet, openCubeAtScale_zero_eq_openCubeSet_originCube]
    at hfinal

/-! ## The interior mesh is at least half the full mesh -/

/-- **The interior mesh carries at least half the cells**, once the boundary
fraction is below `1/2`.

only on the scale bookkeeping and on the numerical gate `hsmall`. -/
theorem card_mesoCubeGrid_le_two_mul_card_interiorMesoCubeGrid (d : ℕ) {K n outer : ℤ}
    {p g : ℕ} (hK : K = n + (p : ℤ)) (houter : outer + 1 = n + (g : ℤ)) (hgp : g ≤ p)
    (hsmall : (d : ℝ) * ((3 : ℝ) ^ g / (3 : ℝ) ^ p) ≤ 1 / 2) :
    ((mesoCubeGrid d K n).card : ℝ) ≤
      2 * ((interiorMesoCubeGrid d K n outer).card : ℝ) := by
  have hnK : n ≤ K := by omega
  have hpn : (K - n).toNat = p := by omega
  have hCM : ((mesoCubeGrid d K n).card : ℝ) = ((3 : ℝ) ^ p) ^ d := by
    rw [card_mesoCubeGrid hnK, hpn]
    push_cast
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hCMpos : (0 : ℝ) < ((mesoCubeGrid d K n).card : ℝ) := by
    rw [hCM]; positivity
  have hratio := one_sub_interior_card_ratio_le d hK houter hgp
  have hhalf : (1 : ℝ) / 2 ≤ ((interiorMesoCubeGrid d K n outer).card : ℝ) /
      ((mesoCubeGrid d K n).card : ℝ) := by linarith
  rw [le_div_iff₀ hCMpos] at hhalf
  linarith

/-- **The refined interior mesh is small compared with the source mesh.**  The
cardinality ratio the family device pays is below `2` at every depth.

on the scale bookkeeping and the boundary gate. -/
theorem card_interiorMesoCubeGrid_refined_le (d : ℕ) {K n outer : ℤ} {p g : ℕ} (i : ℕ)
    (hK : K = n + (p : ℤ)) (houter : outer + 1 = n + (g : ℤ)) (hgp : g ≤ p)
    (hsmall : (d : ℝ) * ((3 : ℝ) ^ g / (3 : ℝ) ^ p) ≤ 1 / 2) :
    ((interiorMesoCubeGrid d K (n - (i : ℤ)) (outer - 1)).card : ℝ) ≤
      2 * (((interiorMesoCubeGrid d K n outer).card : ℝ) * ((3 : ℝ) ^ d) ^ i) := by
  have hnK : n ≤ K := by omega
  have hniK : n - (i : ℤ) ≤ K := by omega
  have hpn : (K - n).toNat = p := by omega
  have hpni : (K - (n - (i : ℤ))).toNat = p + i := by omega
  have hsub : ((interiorMesoCubeGrid d K (n - (i : ℤ)) (outer - 1)).card : ℝ) ≤
      ((mesoCubeGrid d K (n - (i : ℤ))).card : ℝ) := by
    have := Finset.card_le_card
      (interiorMesoCubeGrid_subset (d := d) (K := K) (n := n - (i : ℤ)) (outer := outer - 1))
    exact_mod_cast this
  have hCMi : ((mesoCubeGrid d K (n - (i : ℤ))).card : ℝ) =
      ((3 : ℝ) ^ p) ^ d * ((3 : ℝ) ^ d) ^ i := by
    rw [card_mesoCubeGrid hniK, hpni]
    push_cast
    rw [pow_add, ← pow_mul, ← pow_mul, Nat.mul_comm]
    ring
  have hCM : ((mesoCubeGrid d K n).card : ℝ) = ((3 : ℝ) ^ p) ^ d := by
    rw [card_mesoCubeGrid hnK, hpn]
    push_cast
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  have hhalf := card_mesoCubeGrid_le_two_mul_card_interiorMesoCubeGrid d hK houter hgp hsmall
  rw [hCM] at hhalf
  have hpowpos : (0 : ℝ) < ((3 : ℝ) ^ d) ^ i := by positivity
  calc ((interiorMesoCubeGrid d K (n - (i : ℤ)) (outer - 1)).card : ℝ)
      ≤ ((3 : ℝ) ^ p) ^ d * ((3 : ℝ) ^ d) ^ i := by rw [← hCMi]; exact hsub
    _ ≤ (2 * ((interiorMesoCubeGrid d K n outer).card : ℝ)) * ((3 : ℝ) ^ d) ^ i :=
        mul_le_mul_of_nonneg_right hhalf hpowpos.le
    _ = 2 * (((interiorMesoCubeGrid d K n outer).card : ℝ) * ((3 : ℝ) ^ d) ^ i) := by ring

/-! ## The per-depth input of the family device, on the interior mesh -/

/-- **The per-depth input of the interior-mesh Besov device.**

The depth-`i` descendant average over the interior mesh at scale `n` is below
twice the interior-grid average at scale `n - i`, which is the carrier of the
depth-indexed endpoints of `Closure.GammaTenDepthOscillation`.

on the scale bookkeeping, on the boundary gate, and on the nonnegativity of the
cell functional. -/
theorem cubeFamilyAverage_descendantsAverage_interiorMesoCubeGrid_le (d : ℕ)
    {K n outer : ℤ} {p g : ℕ} (i : ℕ)
    (hK : K = n + (p : ℤ)) (houter : outer + 1 = n + (g : ℤ)) (hgp : g ≤ p)
    (hno : n ≤ outer)
    (hsmall : (d : ℝ) * ((3 : ℝ) ^ g / (3 : ℝ) ^ p) ≤ 1 / 2)
    (f : TriadicCube d → ℝ)
    (hf : ∀ R' ∈ interiorMesoCubeGrid d K (n - (i : ℤ)) (outer - 1), 0 ≤ f R') :
    cubeFamilyAverage (interiorMesoCubeGrid d K n outer)
        (fun R => descendantsAverage R i f) ≤
      2 * cubeFamilyAverage (interiorMesoCubeGrid d K (n - (i : ℤ)) (outer - 1)) f := by
  have hnK : n ≤ K := by omega
  have hIsub : interiorMesoCubeGrid d K n outer ⊆
      descendantsAtDepth (originCube d K) (K - n).toNat := by
    rw [← mesoCubeGrid_eq_descendantsAtDepth hnK]
    exact interiorMesoCubeGrid_subset
  refine cubeFamilyAverage_descendantsAverage_le hIsub
    (fun R hR => fun R' hR' =>
      mem_interiorMesoCubeGrid_of_mem_descendantsAtDepth hnK hno hR hR')
    f hf (by norm_num)
    (card_interiorMesoCubeGrid_refined_le d i hK houter hgp hsmall)

/-! ## The boundary gate, produced -/

/-- **The boundary fraction is below `1/2` once `cgamma` is small.**  The threshold
is *produced* by
`LocalizationFluctuationGammaFold.exists_gamma_threshold_mesh_boundary` at the
absolute constant `1`, and the gate consumed is the recurrence's own large-cube
gate read on the mesh. -/
theorem exists_gamma_threshold_mesh_boundary_half (d : ℕ) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧ gamma0 ≤ 1 / 4 ∧
      ∀ gamma : ℝ, 0 < gamma → gamma ≤ gamma0 →
        ∀ p g : ℕ, (10 : ℝ) ^ (10 : ℕ) * gamma⁻¹ ≤ (p : ℝ) - (g : ℝ) →
          (d : ℝ) * ((3 : ℝ) ^ g / (3 : ℝ) ^ p) ≤ 1 / 2 := by
  obtain ⟨gamma0, hpos, hquarter, hthr⟩ :=
    exists_gamma_threshold_mesh_boundary d 1 zero_le_one
  refine ⟨gamma0, hpos, hquarter, ?_⟩
  intro gamma hgamma hle p g hgap
  have hb := hthr gamma hgamma hle p g hgap
  rw [one_mul] at hb
  have hq : gamma ≤ 1 / 4 := hle.trans hquarter
  have hbase0 : (0 : ℝ) ≤ (d : ℝ) * ((3 : ℝ) ^ g / (3 : ℝ) ^ p) := by positivity
  have hpow : gamma ^ (100 : ℕ) ≤ (1 / 4 : ℝ) ^ (100 : ℕ) :=
    pow_le_pow_left₀ hgamma.le hq 100
  have hsmallpow : ((1 : ℝ) / 4) ^ (100 : ℕ) ≤ 1 / 2 := by
    have h1 : ((1 : ℝ) / 4) ^ (100 : ℕ) ≤ ((1 : ℝ) / 4) ^ (1 : ℕ) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by norm_num)
    rw [pow_one] at h1
    linarith
  have hsq := Real.sq_sqrt hbase0
  nlinarith [Real.sqrt_nonneg ((d : ℝ) * ((3 : ℝ) ^ g / (3 : ℝ) ^ p)), hb, hpow,
    hsmallpow, hsq]

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
