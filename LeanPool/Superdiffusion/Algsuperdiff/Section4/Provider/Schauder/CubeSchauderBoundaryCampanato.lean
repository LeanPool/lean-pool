/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderBoundaryOneStep
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Schauder.CubeSchauderCampanato

/-!
# CubeSchauderBoundaryCampanato

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Cube Schauder: the Campanato bound at **every** base point of `□_m`

The boundary mirror of `CubeSchauderCampanato`.  The interior module's chain is
reproduced verbatim with one substitution: the interior one step
(`excessDecay_oneStep_lipschitz`, which needs the geometry slot
`x + □_{n-2} ⊆ □_m` and therefore the interior half-cube) is replaced by the
boundary one step (`excessDecay_oneStep_boundary_lipschitz`, which needs only
`x ∈ □_m` and `n - 2 < m`).  Everything else — the rate gap, the geometric
recursion `CubeSchauderIteration.excess_le_geometric`, the top-scale estimate
`CubeSchauderCampanato.affineExcess_initial_le` (already stated at *every* base
point of `□_m`), and the sub-lattice-to-every-scale interpolation — is reused
unchanged.

This is the structural point: the boundary route carries no
interior slot, so **one** branch supplies the Campanato datum at every base
point, and the interior restriction `x ∈ □_{m-1}` disappears from the endpoint.

```text
  E(w, (x + □_j) ∩ □_m) ≤ boundaryCampanatoFullConst d · KG · √(3^j)
      for every x ∈ □_m and every j ≤ m.
```

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

/-! ## 1. The step size and the rate gap -/

/-- **The boundary rate gap exists.**  There is a step size `k ≥ 3` at which the
boundary contraction rate `C_contr(d)·3^{-k}` is strictly below the freezing rate
`√(3^{-k})`.  The proof is the interior argument at the boundary constant. -/
theorem exists_boundaryStepSize (d : ℕ) [NeZero d] :
    ∃ k : ℕ, 3 ≤ k ∧
      boundaryContractionConst d * (3 : ℝ) ^ (-(k : ℤ))
        < Real.sqrt ((3 : ℝ) ^ (-(k : ℤ))) := by
  have hC0 : 0 ≤ boundaryContractionConst d := boundaryContractionConst_nonneg d
  set C : ℝ := boundaryContractionConst d with hCdef
  have hden : (0 : ℝ) < C + 1 := by linarith only [hC0]
  have heps : (0 : ℝ) < (1 / (C + 1)) ^ 2 := by positivity
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one heps (by norm_num : (1 / 3 : ℝ) < 1)
  refine ⟨max n 3, le_max_right n 3, ?_⟩
  set k : ℕ := max n 3 with hkdef
  have hpow : (3 : ℝ) ^ (-(k : ℤ)) = (1 / 3 : ℝ) ^ k := by
    rw [zpow_neg, zpow_natCast, one_div, inv_pow]
  have hmono : (1 / 3 : ℝ) ^ k ≤ (1 / 3 : ℝ) ^ n :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_max_left n 3)
  have hlt : (3 : ℝ) ^ (-(k : ℤ)) < (1 / (C + 1)) ^ 2 := by
    rw [hpow]
    linarith only [hmono, hn]
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (-(k : ℤ)) := zpow_pos (by norm_num) _
  have hrho : Real.sqrt ((3 : ℝ) ^ (-(k : ℤ))) < 1 / (C + 1) := by
    have h := Real.sqrt_lt_sqrt hpos.le hlt
    rwa [Real.sqrt_sq (by positivity)] at h
  have hrhopos : (0 : ℝ) < Real.sqrt ((3 : ℝ) ^ (-(k : ℤ))) := Real.sqrt_pos.2 hpos
  have hsq : Real.sqrt ((3 : ℝ) ^ (-(k : ℤ))) * Real.sqrt ((3 : ℝ) ^ (-(k : ℤ)))
      = (3 : ℝ) ^ (-(k : ℤ)) := Real.mul_self_sqrt hpos.le
  have hCr : C * Real.sqrt ((3 : ℝ) ^ (-(k : ℤ))) < 1 := by
    have h1 : C * Real.sqrt ((3 : ℝ) ^ (-(k : ℤ))) ≤ C * (1 / (C + 1)) :=
      mul_le_mul_of_nonneg_left hrho.le hC0
    have h2 : C * (1 / (C + 1)) < 1 := by
      rw [mul_one_div, div_lt_one hden]
      linarith only []
    linarith only [h1, h2]
  calc C * (3 : ℝ) ^ (-(k : ℤ))
      = (C * Real.sqrt ((3 : ℝ) ^ (-(k : ℤ)))) * Real.sqrt ((3 : ℝ) ^ (-(k : ℤ))) := by
        rw [mul_assoc, hsq]
    _ < 1 * Real.sqrt ((3 : ℝ) ^ (-(k : ℤ))) := mul_lt_mul_of_pos_right hCr hrhopos
    _ = Real.sqrt ((3 : ℝ) ^ (-(k : ℤ))) := one_mul _

/-- **The step size of the boundary Campanato iteration**, `k₀^∂(d)`. -/
def boundaryStepSize (d : ℕ) [NeZero d] : ℕ := (exists_boundaryStepSize d).choose

theorem boundaryStepSize_ge_three (d : ℕ) [NeZero d] : 3 ≤ boundaryStepSize d :=
  (exists_boundaryStepSize d).choose_spec.1

/-- **The boundary rate gap, machine-checked.** -/
theorem boundaryStepSize_gap (d : ℕ) [NeZero d] :
    boundaryContractionConst d * (3 : ℝ) ^ (-(boundaryStepSize d : ℤ))
      < Real.sqrt ((3 : ℝ) ^ (-(boundaryStepSize d : ℤ))) :=
  (exists_boundaryStepSize d).choose_spec.2

/-! ## 2. The one step for the forced equation, at any base point -/

/-- **The boundary one step, forced.**

For the zero-datum solution `u` of `-Δu = ∇·G` on `□_m` with
`[G]_{C^{0,1/2}} ≤ KG`, at **any** base point `x ∈ □_m` and any scale `n` with
`n - 1 ≤ m`:

```text
  E(u, W_{n-k}) ≤ C_contr(d)·3^{-k}·E(u, W_n) + C_rem(d,k)·C_res(d)·KG·√(3ⁿ) .
```
-/
theorem excessDecay_oneStep_boundary_forced [NeZero d] (hd : d ≠ 0) {m n : ℤ} {k : ℕ}
    (hk : 3 ≤ k) {x : Vec d} (hx : x ∈ openCubeSet (originCube d m)) (hnm : n - 1 ≤ m)
    (u : H10Function (openCubeSet (originCube d m)))
    {G : Vec d → Vec d} {KG : ℝ} (hKG : 0 ≤ KG)
    (hGL2 : MemVectorL2 (openCubeSet (originCube d m)) G)
    (hG : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) KG G)
    (hu : IsDivFormWeakSolutionOn (fun _ => (1 : Mat d))
      (openCubeSet (originCube d m)) u.toH1Function G) :
    affineExcess (truncatedWindow x m (n - (k : ℤ))) u.toFun
      ≤ boundaryContractionConst d * (3 : ℝ) ^ (-(k : ℤ))
            * affineExcess (truncatedWindow x m n) u.toFun
        + boundaryRemainderConst d k *
            (boundaryResidueConst d * KG * Real.sqrt ((3 : ℝ) ^ n)) := by
  have hmn : n - 2 < m := by omega
  obtain ⟨V, hVharm, hVmem, hupV, hlowV, hres⟩ :=
    exists_harmonicCompetitor_reflected_odd (n := n) hx hmn u hKG hGL2 hG hu
  have hWsub : truncatedWindow x m n ⊆ openCubeSet (originCube d m) :=
    truncatedWindow_subset_domain x m n
  have huW : MemLp u.toFun 2 (volume.restrict (truncatedWindow x m n)) := by
    have h : MemLp u.toFun 2 (volume.restrict (openCubeSet (originCube d m))) := by
      simpa only [volumeMeasureOn] using u.toH1Function.memL2
    exact memLp_restrict_of_subset hWsub h
  have hVR : MemLp V 2 (volume.restrict (reflectedWindow x m (n - 2))) := hVmem.restrict _
  have hstep := excessDecay_oneStep_boundary_lipschitz hd hk hx hnm hmn huW hVR hupV
    hlowV hVharm
  have hfinal := mul_le_mul_of_nonneg_left hres (boundaryRemainderConst_nonneg d k)
  linarith only [hstep, hfinal]

/-! ## 3. The Campanato bound -/

/-- **The boundary Campanato constant.** -/
def boundaryCampanatoConst (d : ℕ) [NeZero d] : ℝ :=
  schauderInitialConst d
    + boundaryRemainderConst d (boundaryStepSize d) * boundaryResidueConst d /
        (Real.sqrt ((3 : ℝ) ^ (-(boundaryStepSize d : ℤ)))
          - boundaryContractionConst d * (3 : ℝ) ^ (-(boundaryStepSize d : ℤ)))

theorem boundaryCampanatoConst_nonneg (d : ℕ) [NeZero d] :
    0 ≤ boundaryCampanatoConst d := by
  have h1 : (0 : ℝ) ≤ schauderInitialConst d := schauderInitialConst_nonneg d
  have hgap := boundaryStepSize_gap d
  have hgap0 : (0 : ℝ) < Real.sqrt ((3 : ℝ) ^ (-(boundaryStepSize d : ℤ)))
      - boundaryContractionConst d * (3 : ℝ) ^ (-(boundaryStepSize d : ℤ)) := by
    linarith only [hgap]
  have h2 : (0 : ℝ) ≤ boundaryRemainderConst d (boundaryStepSize d)
      * boundaryResidueConst d /
      (Real.sqrt ((3 : ℝ) ^ (-(boundaryStepSize d : ℤ)))
        - boundaryContractionConst d * (3 : ℝ) ^ (-(boundaryStepSize d : ℤ))) :=
    div_nonneg (mul_nonneg (boundaryRemainderConst_nonneg d (boundaryStepSize d))
      (boundaryResidueConst_nonneg d)) hgap0.le
  rw [boundaryCampanatoConst]
  linarith only [h1, h2]

/-- **The boundary Campanato bound on the triadic sub-lattice**, at every base
point of `□_m`. -/
theorem affineExcess_le_boundaryCampanato_sublattice [NeZero d] (hd : d ≠ 0) {m : ℤ}
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d m))
    (u : H10Function (openCubeSet (originCube d m)))
    {G : Vec d → Vec d} {KG : ℝ} (hKG : 0 ≤ KG)
    (hGL2 : MemVectorL2 (openCubeSet (originCube d m)) G)
    (hG : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) KG G)
    (hu : IsDivFormWeakSolutionOn (fun _ => (1 : Mat d))
      (openCubeSet (originCube d m)) u.toH1Function G) (i : ℕ) :
    affineExcess (truncatedWindow x m (m - (i : ℤ) * (boundaryStepSize d : ℤ))) u.toFun
      ≤ boundaryCampanatoConst d * KG *
          Real.sqrt ((3 : ℝ) ^ (m - (i : ℤ) * (boundaryStepSize d : ℤ))) := by
  have hgap := boundaryStepSize_gap d
  have hk3 : 3 ≤ boundaryStepSize d := boundaryStepSize_ge_three d
  set k : ℕ := boundaryStepSize d with hkdef
  have h3m : (0 : ℝ) < (3 : ℝ) ^ m := zpow_pos (by norm_num) m
  have h3k : (0 : ℝ) < (3 : ℝ) ^ (-(k : ℤ)) := zpow_pos (by norm_num) _
  have hrhonn : (0 : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ (-(k : ℤ))) := Real.sqrt_nonneg _
  have hthetann : (0 : ℝ) ≤ boundaryContractionConst d * (3 : ℝ) ^ (-(k : ℤ)) :=
    mul_nonneg (boundaryContractionConst_nonneg d) h3k.le
  have hFnn : (0 : ℝ) ≤ boundaryRemainderConst d k *
      (boundaryResidueConst d * KG * Real.sqrt ((3 : ℝ) ^ m)) :=
    mul_nonneg (boundaryRemainderConst_nonneg d k)
      (mul_nonneg (mul_nonneg (boundaryResidueConst_nonneg d) hKG) (Real.sqrt_nonneg _))
  have hscale : ∀ j : ℕ, Real.sqrt ((3 : ℝ) ^ (m - (j : ℤ) * (k : ℤ)))
      = Real.sqrt ((3 : ℝ) ^ m) * Real.sqrt ((3 : ℝ) ^ (-(k : ℤ))) ^ j := by
    intro j
    rw [zpow_sub_mul_step, Real.sqrt_mul h3m.le, sqrt_pow_nat h3k.le]
  have hstep : ∀ j : ℕ,
      affineExcess (truncatedWindow x m (m - ((j + 1 : ℕ) : ℤ) * (k : ℤ))) u.toFun
        ≤ boundaryContractionConst d * (3 : ℝ) ^ (-(k : ℤ)) *
            affineExcess (truncatedWindow x m (m - (j : ℤ) * (k : ℤ))) u.toFun
          + boundaryRemainderConst d k *
              (boundaryResidueConst d * KG * Real.sqrt ((3 : ℝ) ^ m)) *
              Real.sqrt ((3 : ℝ) ^ (-(k : ℤ))) ^ j := by
    intro j
    have hjk : (0 : ℤ) ≤ (j : ℤ) * (k : ℤ) := by positivity
    have hnm : m - (j : ℤ) * (k : ℤ) - 1 ≤ m := by linarith only [hjk]
    have hone := excessDecay_oneStep_boundary_forced hd hk3 hx hnm u hKG hGL2 hG hu
    have hidx : m - ((j + 1 : ℕ) : ℤ) * (k : ℤ) = m - (j : ℤ) * (k : ℤ) - (k : ℤ) := by
      push_cast
      ring
    rw [hidx]
    refine hone.trans (le_of_eq ?_)
    rw [hscale j]
    ring
  have hE0nn : (0 : ℝ) ≤
      affineExcess (truncatedWindow x m (m - ((0 : ℕ) : ℤ) * (k : ℤ))) u.toFun :=
    affineExcess_nonneg _ _
  have hmain := excess_le_geometric
    (E := fun j : ℕ => affineExcess (truncatedWindow x m (m - (j : ℤ) * (k : ℤ))) u.toFun)
    (theta := boundaryContractionConst d * (3 : ℝ) ^ (-(k : ℤ)))
    (rho := Real.sqrt ((3 : ℝ) ^ (-(k : ℤ))))
    (F := boundaryRemainderConst d k *
      (boundaryResidueConst d * KG * Real.sqrt ((3 : ℝ) ^ m)))
    hthetann hgap hFnn hE0nn hstep i
  have hinit : affineExcess (truncatedWindow x m (m - ((0 : ℕ) : ℤ) * (k : ℤ))) u.toFun
      ≤ schauderInitialConst d * KG * Real.sqrt ((3 : ℝ) ^ m) := by
    have hz : m - ((0 : ℕ) : ℤ) * (k : ℤ) = m := by push_cast; ring
    rw [hz]
    exact affineExcess_initial_le hd hx u hKG hGL2 hG hu
  have hgap0 : (0 : ℝ) < Real.sqrt ((3 : ℝ) ^ (-(k : ℤ)))
      - boundaryContractionConst d * (3 : ℝ) ^ (-(k : ℤ)) := by
    linarith only [hgap]
  have hamp : affineExcess (truncatedWindow x m (m - ((0 : ℕ) : ℤ) * (k : ℤ))) u.toFun
      + boundaryRemainderConst d k *
          (boundaryResidueConst d * KG * Real.sqrt ((3 : ℝ) ^ m)) /
        (Real.sqrt ((3 : ℝ) ^ (-(k : ℤ)))
          - boundaryContractionConst d * (3 : ℝ) ^ (-(k : ℤ)))
      ≤ boundaryCampanatoConst d * KG * Real.sqrt ((3 : ℝ) ^ m) := by
    have hid : boundaryRemainderConst d k *
        (boundaryResidueConst d * KG * Real.sqrt ((3 : ℝ) ^ m)) /
          (Real.sqrt ((3 : ℝ) ^ (-(k : ℤ)))
            - boundaryContractionConst d * (3 : ℝ) ^ (-(k : ℤ)))
        = boundaryRemainderConst d k * boundaryResidueConst d /
            (Real.sqrt ((3 : ℝ) ^ (-(k : ℤ)))
              - boundaryContractionConst d * (3 : ℝ) ^ (-(k : ℤ)))
          * KG * Real.sqrt ((3 : ℝ) ^ m) := by ring
    rw [hid, boundaryCampanatoConst, ← hkdef]
    have hexp : (schauderInitialConst d +
        boundaryRemainderConst d k * boundaryResidueConst d /
          (Real.sqrt ((3 : ℝ) ^ (-(k : ℤ)))
            - boundaryContractionConst d * (3 : ℝ) ^ (-(k : ℤ)))) * KG *
          Real.sqrt ((3 : ℝ) ^ m)
        = schauderInitialConst d * KG * Real.sqrt ((3 : ℝ) ^ m) +
          boundaryRemainderConst d k * boundaryResidueConst d /
            (Real.sqrt ((3 : ℝ) ^ (-(k : ℤ)))
              - boundaryContractionConst d * (3 : ℝ) ^ (-(k : ℤ)))
            * KG * Real.sqrt ((3 : ℝ) ^ m) := by ring
    rw [hexp]
    have hadd : ∀ a b c : ℝ, a ≤ b → a + c ≤ b + c := fun a b c h => by linarith only [h]
    exact hadd _ _ _ hinit
  have hpow : (0 : ℝ) ≤ Real.sqrt ((3 : ℝ) ^ (-(k : ℤ))) ^ i := pow_nonneg hrhonn i
  have hfin := mul_le_mul_of_nonneg_right hamp hpow
  rw [hscale i]
  refine hmain.trans (hfin.trans (le_of_eq ?_))
  ring

/-! ## 4. Every scale, every base point -/

/-- The full-range boundary Campanato constant. -/
def boundaryCampanatoFullConst (d : ℕ) [NeZero d] : ℝ :=
  windowRatioConst d (boundaryStepSize d : ℤ) *
    Real.sqrt ((3 : ℝ) ^ (boundaryStepSize d : ℤ)) * boundaryCampanatoConst d

theorem boundaryCampanatoFullConst_nonneg (d : ℕ) [NeZero d] :
    0 ≤ boundaryCampanatoFullConst d :=
  mul_nonneg (mul_nonneg (windowRatioConst_nonneg d _) (Real.sqrt_nonneg _))
    (boundaryCampanatoConst_nonneg d)

/-- **The Campanato bound at every scale and every base point of `□_m`.**

For the zero-datum solution `w` of `-Δw = ∇·G` on `□_m` with
`[G]_{C^{0,1/2}(□_m)} ≤ KG`, at **every** `x ∈ □_m` and every `j ≤ m`,

```text
  E(w, (x + □_j) ∩ □_m) ≤ boundaryCampanatoFullConst d · KG · √(3^j) .
```

The interior restriction of `CubeSchauderCampanato.affineExcess_le_campanato` is
gone: the reflected competitor needs no room inside the cube. -/
theorem affineExcess_le_boundaryCampanato [NeZero d] (hd : d ≠ 0) {m j : ℤ} (hjm : j ≤ m)
    {x : Vec d} (hx : x ∈ openCubeSet (originCube d m))
    (u : H10Function (openCubeSet (originCube d m)))
    {G : Vec d → Vec d} {KG : ℝ} (hKG : 0 ≤ KG)
    (hGL2 : MemVectorL2 (openCubeSet (originCube d m)) G)
    (hG : HolderSeminormBoundOn (openCubeSet (originCube d m)) (1 / 2) KG G)
    (hu : IsDivFormWeakSolutionOn (fun _ => (1 : Mat d))
      (openCubeSet (originCube d m)) u.toH1Function G) :
    affineExcess (truncatedWindow x m j) u.toFun
      ≤ boundaryCampanatoFullConst d * KG * Real.sqrt ((3 : ℝ) ^ j) := by
  have hk3 : 3 ≤ boundaryStepSize d := boundaryStepSize_ge_three d
  set k : ℕ := boundaryStepSize d with hkdef
  have hkpos : 0 < k := by omega
  set N : ℕ := (m - j).toNat with hNdef
  have hNcast : ((N : ℤ)) = m - j := Int.toNat_of_nonneg (by omega)
  set i : ℕ := N / k with hidef
  have hdiv : k * (N / k) + N % k = N := Nat.div_add_mod N k
  have hmod : N % k < k := Nat.mod_lt N hkpos
  have hle : (i : ℤ) * (k : ℤ) ≤ (N : ℤ) := by
    have h : k * (N / k) ≤ N := Nat.le.intro hdiv
    have h' : ((k * (N / k) : ℕ) : ℤ) ≤ ((N : ℕ) : ℤ) := Int.ofNat_le.2 h
    push_cast at h' ⊢
    rw [hidef]
    push_cast
    linarith only [h']
  have hlt : (N : ℤ) < (i : ℤ) * (k : ℤ) + (k : ℤ) := by
    have h : N < k * (N / k) + k := by omega
    have h' : ((N : ℕ) : ℤ) < ((k * (N / k) + k : ℕ) : ℤ) := Int.ofNat_lt.2 h
    push_cast at h' ⊢
    rw [hidef]
    push_cast
    linarith only [h']
  set n : ℤ := m - (i : ℤ) * (k : ℤ) with hndef
  have hjn : j ≤ n := by
    rw [hndef]
    linarith only [hle, hNcast]
  have hnj : n - j ≤ (k : ℤ) := by
    rw [hndef]
    linarith only [hlt, hNcast]
  have hnm : n ≤ m := by
    have hjk : (0 : ℤ) ≤ (i : ℤ) * (k : ℤ) := by positivity
    rw [hndef]
    linarith only [hjk]
  have hsub := affineExcess_le_boundaryCampanato_sublattice hd hx u hKG hGL2 hG hu i
  rw [← hkdef, ← hndef] at hsub
  have hun : MemLp u.toFun 2 (volume.restrict (truncatedWindow x m n)) := by
    have h : MemLp u.toFun 2 (volume.restrict (openCubeSet (originCube d m))) := by
      simpa only [volumeMeasureOn] using u.toH1Function.memL2
    exact memLp_restrict_of_subset (truncatedWindow_subset_domain x m n) h
  have hmono := affineExcess_truncatedWindow_le (l := n) (k := j) x hx
    (by omega : j - 1 ≤ m) (by omega : n - 1 ≤ m) hjn hun
  have hratio : windowRatioConst d (n - j) ≤ windowRatioConst d (k : ℤ) := by
    have hbase : ((3 : ℝ) ^ (n - j + 2)) ^ d ≤ ((3 : ℝ) ^ ((k : ℤ) + 2)) ^ d :=
      pow_le_pow_left₀ (by positivity)
        (zpow_le_zpow_right₀ (by norm_num) (by linarith only [hnj])) d
    exact Real.rpow_le_rpow (by positivity) hbase (by positivity)
  have hsqrt : Real.sqrt ((3 : ℝ) ^ n)
      ≤ Real.sqrt ((3 : ℝ) ^ (k : ℤ)) * Real.sqrt ((3 : ℝ) ^ j) := by
    have hstep : (3 : ℝ) ^ n ≤ (3 : ℝ) ^ ((k : ℤ) + j) :=
      zpow_le_zpow_right₀ (by norm_num) (by linarith only [hnj])
    calc Real.sqrt ((3 : ℝ) ^ n) ≤ Real.sqrt ((3 : ℝ) ^ ((k : ℤ) + j)) :=
          Real.sqrt_le_sqrt hstep
      _ = Real.sqrt ((3 : ℝ) ^ (k : ℤ)) * Real.sqrt ((3 : ℝ) ^ j) := by
          rw [zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0),
            Real.sqrt_mul (zpow_pos (by norm_num) _).le]
  have hCnn : (0 : ℝ) ≤ boundaryCampanatoConst d * KG :=
    mul_nonneg (boundaryCampanatoConst_nonneg d) hKG
  have hstep1 : affineExcess (truncatedWindow x m j) u.toFun
      ≤ windowRatioConst d (k : ℤ) *
        (boundaryCampanatoConst d * KG * Real.sqrt ((3 : ℝ) ^ n)) := by
    refine hmono.trans ?_
    have hrhs : (0 : ℝ) ≤ affineExcess (truncatedWindow x m n) u.toFun :=
      affineExcess_nonneg _ _
    have h1 : windowRatioConst d (n - j) * affineExcess (truncatedWindow x m n) u.toFun
        ≤ windowRatioConst d (k : ℤ) * affineExcess (truncatedWindow x m n) u.toFun :=
      mul_le_mul_of_nonneg_right hratio hrhs
    have h2 : windowRatioConst d (k : ℤ) * affineExcess (truncatedWindow x m n) u.toFun
        ≤ windowRatioConst d (k : ℤ) *
          (boundaryCampanatoConst d * KG * Real.sqrt ((3 : ℝ) ^ n)) :=
      mul_le_mul_of_nonneg_left hsub (windowRatioConst_nonneg d (k : ℤ))
    linarith only [h1, h2]
  refine hstep1.trans ?_
  have h3 : boundaryCampanatoConst d * KG * Real.sqrt ((3 : ℝ) ^ n)
      ≤ boundaryCampanatoConst d * KG *
        (Real.sqrt ((3 : ℝ) ^ (k : ℤ)) * Real.sqrt ((3 : ℝ) ^ j)) :=
    mul_le_mul_of_nonneg_left hsqrt hCnn
  have h4 := mul_le_mul_of_nonneg_left h3 (windowRatioConst_nonneg d (k : ℤ))
  refine h4.trans (le_of_eq ?_)
  rw [boundaryCampanatoFullConst, ← hkdef]
  ring

end

end Algsuperdiff.Section4.Provider.Schauder
