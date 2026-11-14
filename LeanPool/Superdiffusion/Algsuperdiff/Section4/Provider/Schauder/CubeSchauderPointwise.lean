/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderSlope
public import Mathlib.Data.Int.Log

/-!
# CubeSchauderPointwise

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Cube Schauder: from the Campanato bound to a pointwise `C^{0,1/2}` slope field

```text
  E(u, (z+□_j) ∩ □_m) ≤ K · √(3^j)      for every z ∈ S and every j ≤ m+1 .
```

From it we build the continuous slope field

```text
  Ψ(z) := lim_{j → -∞} ∇ℓ(u, (z+□_j) ∩ □_m)
```

and prove the two displays the cube Schauder core needs about it: a `C^{0,1/2}`
seminorm bound with a `d`-constant times `K`, and a sup bound at the top scale.

## Why the family is Cauchy, and why no chaining lemma is needed

`CubeSchauderSlope.slopeMagnitude_windowSlope_sub_le` bounds the slope
increment by the two excesses, so consecutive slopes differ by at most
`2·C_stab·K·√(3^j)` — a geometric sequence of ratio `√(1/3)`, whence mathlib's
`cauchySeq_of_le_geometric` and `dist_le_of_le_geometric_of_tendsto` give the
limit and its tail estimate in two lines each.

For the two-point estimate the usual Campanato argument runs a *local* Hölder
bound (valid only for nearby points) and then chains it along segments of a
convex set.  That chaining step is **not needed here**: at the top scale
`j = m+1` every window `(z+□_{m+1}) ∩ □_m` is the *same set* `□_m`, so all the
slopes coincide there and the far-apart case is closed by two tail estimates
alone.  This is what makes the module short.

## Main results

* `campanatoSlopeLimit` — the field `Ψ`, defined by `limUnder` (junk value off
  the Cauchy locus, no subtype, no bundled choice).
* `campanatoSlopeLimit_tail` — `|∇ℓ_j − Ψ| ≤ C(d)·K·√(3^j)` at every `j ≤ m+1`.
* `holderSeminormBoundOn_campanatoSlopeLimit` — the `C^{0,1/2}` bound.
* `norm_campanatoSlopeLimit_le` — the sup bound off the top-scale slope.

## References

* ABK26; Armstrong--Kuusi, *Elliptic Regularity*, Proposition `p.Schauder.C1alpha`.
-/

namespace Algsuperdiff.Section4.Provider.Schauder

open MeasureTheory Filter Topology
open HCPolySupport
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. Two window identities -/

/-- At scale `m+1` every truncated window centred in `□_m` *is* `□_m`. -/
theorem truncatedWindow_top_eq {m : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) :
    truncatedWindow x m (m + 1) = openCubeSet (originCube d m) := by
  refine Set.Subset.antisymm (truncatedWindow_subset_domain x m (m + 1)) ?_
  intro y hy
  refine ⟨⟨y - x, ?_, by ring⟩, hy⟩
  rw [mem_openCubeSet_originCube_iff] at hx hy ⊢
  intro i
  have h1 := hx i
  have h2 := hy i
  have h3 : (3 : ℝ) ^ (m + 1) = 3 * (3 : ℝ) ^ m := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  have hpos : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) _
  refine ⟨?_, ?_⟩ <;> simp only [Pi.sub_apply] <;>
    rw [h3] <;> linarith only [h1.1, h1.2, h2.1, h2.2, hpos]

/-- A window at a nearby centre and one scale down sits inside the window at
`x`: if `‖x − y‖ < 3^k` then `(y+□_k) ∩ □_m ⊆ (x+□_{k+1}) ∩ □_m`. -/
theorem truncatedWindow_subset_of_norm_lt {m k : ℤ} {x y : Vec d}
    (hxy : ‖x - y‖ < (3 : ℝ) ^ k) :
    truncatedWindow y m k ⊆ truncatedWindow x m (k + 1) := by
  rintro p ⟨⟨w, hw, rfl⟩, hp⟩
  refine ⟨⟨y + w - x, ?_, by ring⟩, hp⟩
  rw [mem_openCubeSet_originCube_iff] at hw ⊢
  intro i
  have hcoord : |x i - y i| ≤ ‖x - y‖ := by
    have h := norm_le_pi_norm (x - y) i
    rwa [Pi.sub_apply, Real.norm_eq_abs] at h
  have habs := abs_le.1 hcoord
  have hwi := hw i
  have h3 : (3 : ℝ) ^ (k + 1) = 3 * (3 : ℝ) ^ k := by
    rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    ring
  refine ⟨?_, ?_⟩ <;> simp only [Pi.sub_apply, Pi.add_apply] <;>
    rw [h3] <;> linarith only [habs.1, habs.2, hwi.1, hwi.2, hxy]

/-- Two points of `□_m` are less than `3^m` apart in the ambient sup norm. -/
theorem norm_sub_lt_of_mem_openCubeSet {m : ℤ} {x y : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hy : y ∈ openCubeSet (originCube d m)) :
    ‖x - y‖ < (3 : ℝ) ^ m := by
  rw [mem_openCubeSet_originCube_iff] at hx hy
  refine pi_norm_lt_iff (zpow_pos (by norm_num) m) |>.2 fun i => ?_
  have h1 := hx i
  have h2 := hy i
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_lt]
  constructor <;> linarith only [h1.1, h1.2, h2.1, h2.2]

/-! ## 2. The Campanato constants -/

/-- The geometric ratio of the slope telescope: `√(1/3)`. -/
def campanatoRatio : ℝ := Real.sqrt ((3 : ℝ) ^ (-1 : ℤ))

theorem campanatoRatio_lt_one : campanatoRatio < 1 := by
  rw [campanatoRatio, show ((3 : ℝ) ^ (-1 : ℤ)) = 1 / 3 by norm_num]
  have h : Real.sqrt (1 / 3 : ℝ) < Real.sqrt 1 := by
    refine Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [Real.sqrt_one] at h

/-- The slope-stability constant of the truncated window family. -/
def campanatoStabConst (d : ℕ) : ℝ :=
  slopeStabilityConst d (1 / 9 : ℝ) (volumeRatioConstTriadic d)

theorem campanatoStabConst_nonneg (d : ℕ) : 0 ≤ campanatoStabConst d :=
  slopeStabilityConst_nonneg (by norm_num)
    (le_trans zero_le_one (one_le_volumeRatioConstTriadic d))

/-- The tail constant of the slope telescope: `2·C_stab/(1 − √(1/3))`. -/
def campanatoTailConst (d : ℕ) : ℝ :=
  2 * campanatoStabConst d / (1 - campanatoRatio)

theorem campanatoTailConst_nonneg (d : ℕ) : 0 ≤ campanatoTailConst d := by
  have h := campanatoRatio_lt_one
  exact div_nonneg (by linarith only [campanatoStabConst_nonneg d]) (by linarith only [h])

/-! ## 3. The one-step slope increment -/

/-- The scale factorization used by the geometric telescope. -/
theorem sqrt_zpow_sub_natCast (m : ℤ) (n : ℕ) :
    Real.sqrt ((3 : ℝ) ^ (m - (n : ℤ)))
      = Real.sqrt ((3 : ℝ) ^ m) * campanatoRatio ^ n := by
  have hsplit : (3 : ℝ) ^ (m - (n : ℤ)) = (3 : ℝ) ^ m * ((3 : ℝ) ^ (-1 : ℤ)) ^ n := by
    rw [← zpow_natCast ((3 : ℝ) ^ (-1 : ℤ)) n, ← zpow_mul,
      ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
    congr 1
    ring
  rw [hsplit, Real.sqrt_mul (by positivity), campanatoRatio, sqrt_pow_nat (by positivity) n]

/-- **The slope increment at one triadic step.**

Under the Campanato datum the slopes on consecutive windows about the same
centre differ by at most `2·C_stab(d)·K·√(3^j)`. -/
theorem slopeMagnitude_windowSlope_step_le (hd : 0 < d) {m T j : ℤ} {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d m)) (hTm : T ≤ m + 1) (hjT : j ≤ T)
    {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (openCubeSet (originCube d m)))) {K : ℝ}
    (hK : 0 ≤ K)
    (hE : ∀ i : ℤ, i ≤ T →
      affineExcess (truncatedWindow z m i) u ≤ K * Real.sqrt ((3 : ℝ) ^ i)) :
    slopeMagnitude (windowSlope m u z j - windowSlope m u z (j - 1))
      ≤ 2 * campanatoStabConst d * K * Real.sqrt ((3 : ℝ) ^ j) := by
  have huj : MemLp u 2 (volume.restrict (truncatedWindow z m j)) :=
    hu.mono_measure (Measure.restrict_mono (truncatedWindow_subset_domain z m j) le_rfl)
  have hmain := slopeMagnitude_windowSlope_sub_le (u := u) hd hz hz
    (by omega : j - 1 - 1 ≤ m) (by omega : j - 1 ≤ m) (by omega : j ≤ j - 1 + 1)
    (truncatedWindow_mono z m (by omega : j - 1 ≤ j)) huj
  refine hmain.trans ?_
  have h1 := hE (j - 1) (by omega)
  have h2 := hE j (by omega)
  have hmono : Real.sqrt ((3 : ℝ) ^ (j - 1)) ≤ Real.sqrt ((3 : ℝ) ^ j) :=
    Real.sqrt_le_sqrt (zpow_le_zpow_right₀ (by norm_num) (by omega))
  have hKmono : K * Real.sqrt ((3 : ℝ) ^ (j - 1)) ≤ K * Real.sqrt ((3 : ℝ) ^ j) :=
    mul_le_mul_of_nonneg_left hmono hK
  have hsum : affineExcess (truncatedWindow z m (j - 1)) u
      + affineExcess (truncatedWindow z m j) u
      ≤ 2 * (K * Real.sqrt ((3 : ℝ) ^ j)) := by linarith only [h1, h2, hKmono]
  have hstep := mul_le_mul_of_nonneg_left hsum (campanatoStabConst_nonneg d)
  calc campanatoStabConst d * (affineExcess (truncatedWindow z m (j - 1)) u
        + affineExcess (truncatedWindow z m j) u)
      ≤ campanatoStabConst d * (2 * (K * Real.sqrt ((3 : ℝ) ^ j))) := hstep
    _ = 2 * campanatoStabConst d * K * Real.sqrt ((3 : ℝ) ^ j) := by ring

/-! ## 4. The limit field -/

/-- **The Campanato slope field.**  `Ψ(z)` is the limit of the affine-minimizer
slopes of `u` on the windows `(z+□_{T-n}) ∩ □_m` as `n → ∞`.  The top index `T`
is a parameter: the interior regime runs it at `T = m` (the range of
`CubeSchauderCampanato.affineExcess_le_campanato`), the full-cube regime at
`T = m+1`, where every window degenerates to `□_m`. -/
def campanatoSlopeLimit (m T : ℤ) (u : Vec d → ℝ) (z : Vec d) : Vec d :=
  limUnder atTop fun n : ℕ => windowSlope m u z (T - (n : ℤ))

/-- The geometric step bound of the reindexed slope sequence. -/
theorem dist_windowSlope_succ_le (hd : 0 < d) {m T : ℤ} {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d m)) (hTm : T ≤ m + 1) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (openCubeSet (originCube d m)))) {K : ℝ}
    (hK : 0 ≤ K)
    (hE : ∀ i : ℤ, i ≤ T →
      affineExcess (truncatedWindow z m i) u ≤ K * Real.sqrt ((3 : ℝ) ^ i))
    (n : ℕ) :
    dist (windowSlope m u z (T - (n : ℤ))) (windowSlope m u z (T - ((n : ℤ) + 1)))
      ≤ (2 * campanatoStabConst d * K * Real.sqrt ((3 : ℝ) ^ T)) * campanatoRatio ^ n := by
  have hidx : T - ((n : ℤ) + 1) = (T - (n : ℤ)) - 1 := by ring
  have hstep := slopeMagnitude_windowSlope_step_le (u := u) hd hz hTm
    (by omega : T - (n : ℤ) ≤ T) hu hK hE
  rw [dist_eq_norm, hidx]
  refine le_trans (norm_le_slopeMagnitude _) (hstep.trans (le_of_eq ?_))
  rw [sqrt_zpow_sub_natCast T n]
  ring

/-- The reindexed slope sequence is Cauchy. -/
theorem cauchySeq_windowSlope (hd : 0 < d) {m T : ℤ} {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d m)) (hTm : T ≤ m + 1) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (openCubeSet (originCube d m)))) {K : ℝ}
    (hK : 0 ≤ K)
    (hE : ∀ i : ℤ, i ≤ T →
      affineExcess (truncatedWindow z m i) u ≤ K * Real.sqrt ((3 : ℝ) ^ i)) :
    CauchySeq fun n : ℕ => windowSlope m u z (T - (n : ℤ)) := by
  refine cauchySeq_of_le_geometric campanatoRatio
    (2 * campanatoStabConst d * K * Real.sqrt ((3 : ℝ) ^ T))
    campanatoRatio_lt_one fun n => ?_
  have h := dist_windowSlope_succ_le hd hz hTm hu hK hE n
  have hcast : ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) := by push_cast; ring
  rwa [hcast] at h

theorem tendsto_windowSlope (hd : 0 < d) {m T : ℤ} {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d m)) (hTm : T ≤ m + 1) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (openCubeSet (originCube d m)))) {K : ℝ}
    (hK : 0 ≤ K)
    (hE : ∀ i : ℤ, i ≤ T →
      affineExcess (truncatedWindow z m i) u ≤ K * Real.sqrt ((3 : ℝ) ^ i)) :
    Tendsto (fun n : ℕ => windowSlope m u z (T - (n : ℤ))) atTop
      (𝓝 (campanatoSlopeLimit m T u z)) :=
  (cauchySeq_windowSlope hd hz hTm hu hK hE).tendsto_limUnder

/-- **The tail estimate.**  At every scale `j ≤ T` the slope of the window at
scale `j` is within `C_tail(d)·K·√(3^j)` of the limit. -/
theorem campanatoSlopeLimit_tail (hd : 0 < d) {m T j : ℤ} {z : Vec d}
    (hz : z ∈ openCubeSet (originCube d m)) (hTm : T ≤ m + 1) (hjT : j ≤ T)
    {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (openCubeSet (originCube d m)))) {K : ℝ}
    (hK : 0 ≤ K)
    (hE : ∀ i : ℤ, i ≤ T →
      affineExcess (truncatedWindow z m i) u ≤ K * Real.sqrt ((3 : ℝ) ^ i)) :
    ‖windowSlope m u z j - campanatoSlopeLimit m T u z‖
      ≤ campanatoTailConst d * K * Real.sqrt ((3 : ℝ) ^ j) := by
  set n : ℕ := (T - j).toNat with hndef
  have hn : ((n : ℤ)) = T - j := Int.toNat_of_nonneg (by omega)
  have hjn : T - (n : ℤ) = j := by omega
  have hgeo := dist_le_of_le_geometric_of_tendsto campanatoRatio
    (2 * campanatoStabConst d * K * Real.sqrt ((3 : ℝ) ^ T))
    campanatoRatio_lt_one
    (fun i => by
      have h := dist_windowSlope_succ_le hd hz hTm hu hK hE i
      have hcast : ((i : ℤ) + 1) = ((i + 1 : ℕ) : ℤ) := by push_cast; ring
      rwa [hcast] at h)
    (tendsto_windowSlope hd hz hTm hu hK hE) n
  rw [hjn, dist_eq_norm] at hgeo
  refine hgeo.trans (le_of_eq ?_)
  have hsq : Real.sqrt ((3 : ℝ) ^ T) * campanatoRatio ^ n = Real.sqrt ((3 : ℝ) ^ j) := by
    rw [← sqrt_zpow_sub_natCast T n, hjn]
  have hne : (1 : ℝ) - campanatoRatio ≠ 0 := by
    have h := campanatoRatio_lt_one
    linarith only [h]
  rw [campanatoTailConst, ← hsq]
  field_simp

/-! ## 5. The top scale -/

/-! ## 6. The two-point estimate -/

/-- The Hölder constant of the slope field: `√3·(2·C_tail + 2·C_stab·(1 + √3))`. -/
def campanatoHolderConst (d : ℕ) : ℝ :=
  Real.sqrt 3 * (2 * campanatoTailConst d + 2 * campanatoStabConst d
    + 2 * campanatoStabConst d * Real.sqrt 3)

theorem campanatoHolderConst_nonneg (d : ℕ) : 0 ≤ campanatoHolderConst d := by
  have h1 := campanatoTailConst_nonneg d
  have h2 := campanatoStabConst_nonneg d
  have h3 : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  have h4 : (0 : ℝ) ≤ 2 * campanatoStabConst d * Real.sqrt 3 :=
    mul_nonneg (by linarith only [h2]) h3
  exact mul_nonneg h3 (by linarith only [h1, h2, h4])

/-- The scale selected by the two-point estimate: the least triadic scale
strictly above the separation. -/
private theorem exists_triadic_bracket {rho : ℝ} (hrho : 0 < rho) :
    ∃ j : ℤ, rho < (3 : ℝ) ^ j ∧ (3 : ℝ) ^ j ≤ 3 * rho := by
  refine ⟨Int.log 3 rho + 1, ?_, ?_⟩
  · have h := Int.lt_zpow_succ_log_self (b := 3) (by norm_num) rho
    norm_num at h
    exact h
  · have h := Int.zpow_log_le_self (b := 3) (by norm_num) hrho
    norm_num at h
    have hz : (3 : ℝ) ^ (Int.log 3 rho + 1) = 3 * (3 : ℝ) ^ (Int.log 3 rho) := by
      rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
      ring
    rw [hz]
    linarith only [h]

/-- **The `C^{0,1/2}` bound of the slope field.**

If the Campanato datum holds at every point of `S ⊆ □_m` up to the top scale `T`
with constant `K`, and `S` has diameter below `3^{T-1}`, then

```text
  ‖Ψ(x) − Ψ(y)‖ ≤ campanatoHolderConst d · K · ‖x − y‖^{1/2}
```

for all `x, y ∈ S`.  No convexity of `S` and no chaining are needed: for far
apart points the two windows at scale `T-1` sit inside the *common* window
`(x+□_T) ∩ □_m`, which closes the case with two tails and two slope
comparisons. -/
theorem holderSeminormBoundOn_campanatoSlopeLimit (hd : 0 < d) {m T : ℤ} {S : Set (Vec d)}
    (hS : S ⊆ openCubeSet (originCube d m)) (hTm : T ≤ m + 1) {u : Vec d → ℝ}
    (hu : MemLp u 2 (volume.restrict (openCubeSet (originCube d m)))) {K : ℝ}
    (hK : 0 ≤ K)
    (hdiamS : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ < (3 : ℝ) ^ (T - 1))
    (hE : ∀ z ∈ S, ∀ i : ℤ, i ≤ T →
      affineExcess (truncatedWindow z m i) u ≤ K * Real.sqrt ((3 : ℝ) ^ i)) :
    HolderSeminormBoundOn S (1 / 2 : ℝ) (campanatoHolderConst d * K)
      (campanatoSlopeLimit m T u) := by
  intro x hx y hy
  have hxm : x ∈ openCubeSet (originCube d m) := hS hx
  have hym : y ∈ openCubeSet (originCube d m) := hS hy
  have hEx := hE x hx
  have hEy := hE y hy
  have hstab := campanatoStabConst_nonneg d
  have htailc := campanatoTailConst_nonneg d
  have hs3nn : (0 : ℝ) ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  rcases eq_or_lt_of_le (norm_nonneg (x - y)) with hzero | hpos
  · have hxy : x = y := by
      have h : x - y = 0 := by
        rw [← norm_eq_zero]
        exact hzero.symm
      exact sub_eq_zero.mp h
    subst hxy
    rw [sub_self, norm_zero, sub_self, norm_zero,
      Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0), mul_zero]
  · set rho : ℝ := ‖x - y‖ with hrhodef
    obtain ⟨j, hjlt, hjle⟩ := exists_triadic_bracket hpos
    have hrpow : rho ^ (1 / 2 : ℝ) = Real.sqrt rho := (Real.sqrt_eq_rpow rho).symm
    have hsqrt_rho : Real.sqrt ((3 : ℝ) ^ j) ≤ Real.sqrt 3 * Real.sqrt rho := by
      have h := Real.sqrt_le_sqrt hjle
      rwa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)] at h
    have hsucc : ∀ i : ℤ,
        Real.sqrt ((3 : ℝ) ^ (i + 1)) = Real.sqrt 3 * Real.sqrt ((3 : ℝ) ^ i) := by
      intro i
      rw [show ((3 : ℝ) ^ (i + 1)) = 3 * (3 : ℝ) ^ i by
        rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]; ring,
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    by_cases hjm : j ≤ T - 1
    · -- the near case: the window at `y`, scale `j`, sits in the window at `x`, scale `j+1`
      have hsubxy : truncatedWindow y m j ⊆ truncatedWindow x m (j + 1) :=
        truncatedWindow_subset_of_norm_lt hjlt
      have hux : MemLp u 2 (volume.restrict (truncatedWindow x m (j + 1))) :=
        hu.mono_measure (Measure.restrict_mono
          (truncatedWindow_subset_domain x m (j + 1)) le_rfl)
      have hA := slopeMagnitude_windowSlope_sub_le (u := u) hd hxm hym
        (by omega : j - 1 ≤ m) (by omega : j + 1 - 1 ≤ m) (by omega : j + 1 ≤ j + 1)
        hsubxy hux
      have hB := slopeMagnitude_windowSlope_sub_le (u := u) hd hxm hxm
        (by omega : j - 1 ≤ m) (by omega : j + 1 - 1 ≤ m) (by omega : j + 1 ≤ j + 1)
        (truncatedWindow_mono x m (by omega : j ≤ j + 1)) hux
      have htx := campanatoSlopeLimit_tail (u := u) hd hxm hTm (by omega : j ≤ T) hu hK hEx
      have hty := campanatoSlopeLimit_tail (u := u) hd hym hTm (by omega : j ≤ T) hu hK hEy
      have hEx1 := hEx (j + 1) (by omega)
      have hExj := hEx j (by omega)
      have hEyj := hEy j (by omega)
      have htri : ‖campanatoSlopeLimit m T u x - campanatoSlopeLimit m T u y‖
          ≤ ‖windowSlope m u x j - campanatoSlopeLimit m T u x‖
            + ‖windowSlope m u x j - windowSlope m u x (j + 1)‖
            + ‖windowSlope m u x (j + 1) - windowSlope m u y j‖
            + ‖windowSlope m u y j - campanatoSlopeLimit m T u y‖ := by
        have hsplit : campanatoSlopeLimit m T u x - campanatoSlopeLimit m T u y
            = -(windowSlope m u x j - campanatoSlopeLimit m T u x)
              + ((windowSlope m u x j - windowSlope m u x (j + 1))
                + ((windowSlope m u x (j + 1) - windowSlope m u y j)
                  + (windowSlope m u y j - campanatoSlopeLimit m T u y))) := by abel
        rw [hsplit]
        have h1 := norm_add_le (-(windowSlope m u x j - campanatoSlopeLimit m T u x))
          ((windowSlope m u x j - windowSlope m u x (j + 1))
            + ((windowSlope m u x (j + 1) - windowSlope m u y j)
              + (windowSlope m u y j - campanatoSlopeLimit m T u y)))
        have h2 := norm_add_le (windowSlope m u x j - windowSlope m u x (j + 1))
          ((windowSlope m u x (j + 1) - windowSlope m u y j)
            + (windowSlope m u y j - campanatoSlopeLimit m T u y))
        have h3 := norm_add_le (windowSlope m u x (j + 1) - windowSlope m u y j)
          (windowSlope m u y j - campanatoSlopeLimit m T u y)
        have h4 : ‖-(windowSlope m u x j - campanatoSlopeLimit m T u x)‖
            = ‖windowSlope m u x j - campanatoSlopeLimit m T u x‖ := norm_neg _
        linarith only [h1, h2, h3, h4]
      have hab : ‖windowSlope m u x j - windowSlope m u x (j + 1)‖
          ≤ campanatoStabConst d * (K * Real.sqrt ((3 : ℝ) ^ j)
            + K * Real.sqrt ((3 : ℝ) ^ (j + 1))) := by
        rw [norm_sub_rev]
        refine (norm_le_slopeMagnitude _).trans (hB.trans ?_)
        exact mul_le_mul_of_nonneg_left (by linarith only [hExj, hEx1]) hstab
      have hbc : ‖windowSlope m u x (j + 1) - windowSlope m u y j‖
          ≤ campanatoStabConst d * (K * Real.sqrt ((3 : ℝ) ^ j)
            + K * Real.sqrt ((3 : ℝ) ^ (j + 1))) := by
        refine (norm_le_slopeMagnitude _).trans (hA.trans ?_)
        exact mul_le_mul_of_nonneg_left (by linarith only [hEyj, hEx1]) hstab
      have hcollect : ‖campanatoSlopeLimit m T u x - campanatoSlopeLimit m T u y‖
          ≤ (2 * campanatoTailConst d + 2 * campanatoStabConst d
              + 2 * campanatoStabConst d * Real.sqrt 3) * (K * Real.sqrt ((3 : ℝ) ^ j)) := by
        rw [hsucc j] at hab hbc
        linarith only [htri, hab, hbc, htx, hty]
      refine hcollect.trans ?_
      have hcoef : (0 : ℝ) ≤ 2 * campanatoTailConst d + 2 * campanatoStabConst d
          + 2 * campanatoStabConst d * Real.sqrt 3 := by
        have h4 : (0 : ℝ) ≤ 2 * campanatoStabConst d * Real.sqrt 3 :=
          mul_nonneg (by linarith only [hstab]) hs3nn
        linarith only [htailc, hstab, h4]
      have hstepp := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsqrt_rho hK) hcoef
      refine hstepp.trans (le_of_eq ?_)
      rw [hrpow, campanatoHolderConst]
      ring
    · -- the far case: both windows at scale `T-1` sit in the common window at `x`
      have hjT : T ≤ j := by omega
      have hrho_lo : (3 : ℝ) ^ (T - 1) ≤ rho := by
        have hstep : (3 : ℝ) ^ (T - 1) ≤ (3 : ℝ) ^ (j - 1) :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
        have hid : (3 : ℝ) ^ j = 3 * (3 : ℝ) ^ (j - 1) := by
          rw [show (3 : ℝ) * (3 : ℝ) ^ (j - 1)
              = (3 : ℝ) ^ (1 : ℤ) * (3 : ℝ) ^ (j - 1) by norm_num,
            ← zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0)]
          congr 1
          ring
        have h3 : (0 : ℝ) < (3 : ℝ) ^ (j - 1) := zpow_pos (by norm_num) _
        rw [hid] at hjle
        linarith only [hjle, hstep, h3]
      have hdxy := hdiamS x hx y hy
      have hsubxy : truncatedWindow y m (T - 1) ⊆ truncatedWindow x m T := by
        have h := truncatedWindow_subset_of_norm_lt (m := m) (k := T - 1) (x := x) (y := y)
          (by rw [← hrhodef]; exact hdxy)
        rwa [show T - 1 + 1 = T by ring] at h
      have hux : MemLp u 2 (volume.restrict (truncatedWindow x m T)) :=
        hu.mono_measure (Measure.restrict_mono (truncatedWindow_subset_domain x m T) le_rfl)
      have hA := slopeMagnitude_windowSlope_sub_le (u := u) hd hxm hym
        (by omega : T - 1 - 1 ≤ m) (by omega : T - 1 ≤ m) (by omega : T ≤ T - 1 + 1)
        hsubxy hux
      have hB := slopeMagnitude_windowSlope_sub_le (u := u) hd hxm hxm
        (by omega : T - 1 - 1 ≤ m) (by omega : T - 1 ≤ m) (by omega : T ≤ T - 1 + 1)
        (truncatedWindow_mono x m (by omega : T - 1 ≤ T)) hux
      have htx := campanatoSlopeLimit_tail (u := u) hd hxm hTm (by omega : T - 1 ≤ T)
        hu hK hEx
      have hty := campanatoSlopeLimit_tail (u := u) hd hym hTm (by omega : T - 1 ≤ T)
        hu hK hEy
      have hExT := hEx T (by omega)
      have hExj := hEx (T - 1) (by omega)
      have hEyj := hEy (T - 1) (by omega)
      have htri : ‖campanatoSlopeLimit m T u x - campanatoSlopeLimit m T u y‖
          ≤ ‖windowSlope m u x (T - 1) - campanatoSlopeLimit m T u x‖
            + ‖windowSlope m u x (T - 1) - windowSlope m u x T‖
            + ‖windowSlope m u x T - windowSlope m u y (T - 1)‖
            + ‖windowSlope m u y (T - 1) - campanatoSlopeLimit m T u y‖ := by
        have hsplit : campanatoSlopeLimit m T u x - campanatoSlopeLimit m T u y
            = -(windowSlope m u x (T - 1) - campanatoSlopeLimit m T u x)
              + ((windowSlope m u x (T - 1) - windowSlope m u x T)
                + ((windowSlope m u x T - windowSlope m u y (T - 1))
                  + (windowSlope m u y (T - 1) - campanatoSlopeLimit m T u y))) := by abel
        rw [hsplit]
        have h1 := norm_add_le (-(windowSlope m u x (T - 1) - campanatoSlopeLimit m T u x))
          ((windowSlope m u x (T - 1) - windowSlope m u x T)
            + ((windowSlope m u x T - windowSlope m u y (T - 1))
              + (windowSlope m u y (T - 1) - campanatoSlopeLimit m T u y)))
        have h2 := norm_add_le (windowSlope m u x (T - 1) - windowSlope m u x T)
          ((windowSlope m u x T - windowSlope m u y (T - 1))
            + (windowSlope m u y (T - 1) - campanatoSlopeLimit m T u y))
        have h3 := norm_add_le (windowSlope m u x T - windowSlope m u y (T - 1))
          (windowSlope m u y (T - 1) - campanatoSlopeLimit m T u y)
        have h4 : ‖-(windowSlope m u x (T - 1) - campanatoSlopeLimit m T u x)‖
            = ‖windowSlope m u x (T - 1) - campanatoSlopeLimit m T u x‖ := norm_neg _
        linarith only [h1, h2, h3, h4]
      have hab : ‖windowSlope m u x (T - 1) - windowSlope m u x T‖
          ≤ campanatoStabConst d * (K * Real.sqrt ((3 : ℝ) ^ (T - 1))
            + K * Real.sqrt ((3 : ℝ) ^ T)) := by
        rw [norm_sub_rev]
        refine (norm_le_slopeMagnitude _).trans (hB.trans ?_)
        exact mul_le_mul_of_nonneg_left (by linarith only [hExj, hExT]) hstab
      have hbc : ‖windowSlope m u x T - windowSlope m u y (T - 1)‖
          ≤ campanatoStabConst d * (K * Real.sqrt ((3 : ℝ) ^ (T - 1))
            + K * Real.sqrt ((3 : ℝ) ^ T)) := by
        refine (norm_le_slopeMagnitude _).trans (hA.trans ?_)
        exact mul_le_mul_of_nonneg_left (by linarith only [hEyj, hExT]) hstab
      have hTsucc : Real.sqrt ((3 : ℝ) ^ T)
          = Real.sqrt 3 * Real.sqrt ((3 : ℝ) ^ (T - 1)) := by
        have h := hsucc (T - 1)
        rwa [show T - 1 + 1 = T by ring] at h
      have hcollect : ‖campanatoSlopeLimit m T u x - campanatoSlopeLimit m T u y‖
          ≤ (2 * campanatoTailConst d + 2 * campanatoStabConst d
              + 2 * campanatoStabConst d * Real.sqrt 3)
            * (K * Real.sqrt ((3 : ℝ) ^ (T - 1))) := by
        rw [hTsucc] at hab hbc
        linarith only [htri, hab, hbc, htx, hty]
      refine hcollect.trans ?_
      have hsqrtT : Real.sqrt ((3 : ℝ) ^ (T - 1)) ≤ Real.sqrt 3 * Real.sqrt rho := by
        have h : Real.sqrt ((3 : ℝ) ^ (T - 1)) ≤ Real.sqrt rho := Real.sqrt_le_sqrt hrho_lo
        have h1 : (1 : ℝ) ≤ Real.sqrt 3 := by
          have := Real.sqrt_le_sqrt (by norm_num : (1 : ℝ) ≤ 3)
          rwa [Real.sqrt_one] at this
        have h2 : Real.sqrt rho ≤ Real.sqrt 3 * Real.sqrt rho := by
          have := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg rho)
          linarith only [this]
        linarith only [h, h2]
      have hcoef : (0 : ℝ) ≤ 2 * campanatoTailConst d + 2 * campanatoStabConst d
          + 2 * campanatoStabConst d * Real.sqrt 3 := by
        have h4 : (0 : ℝ) ≤ 2 * campanatoStabConst d * Real.sqrt 3 :=
          mul_nonneg (by linarith only [hstab]) hs3nn
        linarith only [htailc, hstab, h4]
      have hstepp := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hsqrtT hK) hcoef
      refine hstepp.trans (le_of_eq ?_)
      rw [hrpow, campanatoHolderConst]
      ring

end

end Algsuperdiff.Section4.Provider.Schauder
