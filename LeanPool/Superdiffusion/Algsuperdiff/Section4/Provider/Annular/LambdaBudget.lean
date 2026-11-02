/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.LambdaMatrixRoute
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.SigmaBarBudget
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Localize.GaugeAntitone
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Localize.Nonlocal
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Localize.SensitivitySwitch

/-!
# LambdaBudget

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `hlam` budget, discharged from `𝒢₀`

ABK26, Section 4.1, `p.mathcalE.annular.decomp` Step 2.  The ugly chain's
`λ`-budget is

```
σ_{n−2} · λ_{s,2}^{-1}(z+□_n; a_{n−2}) ≤ C_l 3^{γ(m−n)} ,
    z = 3^n v ,  s = 2γ  (the gapped gauge).
```

`𝒢₀(m)` controls `λ_{γ,2}^{-1}` only at **domain scale = cutoff scale = n−2**
and only at the **annulus** lattice positions `3^{n−2}ℤ^d ∩ (□_m ∖ □_n)`.  Three
steps close the gap, and a fourth is a genuine obstruction:

1. **The gauge.** `Localize.inv_lambdaSq_two_antitone_gauge` transports the
   event's `γ`-gauge control to the gapped gauge `2γ` at constant `1`.  This is
   the only available direction.
2. **The domain.** `lambdaSq_finite_two_inv_le_nine_pow_mul_max_descendants_sub_two`
   raises the domain from `n−2` to `n` at the same exponent, at the constant
   `1 + 9^d·3^{−4γ} ≤ 1 + 9^d`.
3. **The coverage** (`index_mem_latticeAnnulusSet_of_mem_descendantsAtScale`).
   Every scale-`(n−2)` descendant of `z+□_n` has its base point in
   `□_m ∖ □_n` — hence at an index `𝒢₀` actually controls — **provided
   `v ≠ 0`**.  The containment in `□_m` is the tiling of `□_m` by the scale-`n`
   lattice cubes; the exclusion from `□_n` is the disjointness of distinct
   scale-`n` cubes.
4. **The `σ` index.** `𝒢₀`'s bracket carries `σ_{n−3}` while the budget needs
   `σ_{n−2}`; the induction state gives `σ_{n−2} ≤ 8 σ_{n−3}`
   (`sigmaBar_sub_two_le_eight_mul_sigmaBar_sub_three`).

## The uncovered class

At `v = 0` the cube is the centred cube `□_n`, and **every** one of its `9^d`
scale-`(n−2)` descendants has its base point inside `□_n` (those base points are
`3^{n−2} w` with `|w_i| ≤ 4 < 9/2`).  `𝒢₀` therefore says nothing at all about
`λ^{-1}(□_n; a_{n−2})`, at any `k`: its own supremum only ever reaches the
annulus `□_m ∖ □_k`, and only `k = n` produces the field index `n−2`.

This is not a gap in the ugly chain: the consumer never needs `v = 0`.  The
chain applies the budget only at annulus indices `v ∈ 3^nℤ^d ∩ (□_j ∖ □_{j−1})`
with `n ≤ j−1`, and `□_n ⊆ □_{j−1}` forces `3^n v ∉ □_n`, i.e. `v ≠ 0`.  The
`hlam` binder of the chain is therefore stated at `Support.latticeAnnulusSet d
n m n` — the manuscript's own annulus indexing — which is a strictly weaker
hypothesis than `Support.latticeCubeSet d n m` and is exactly what
the consumer supplies.

## References

* ABK26, `p.mathcalE.annular.decomp` Step 2.
* `d.good.event.for.lambda`, (`𝒢₀`).
-/

namespace Algsuperdiff.Section4.Provider.Annular

open HCPolySupport HCPolySupport.Book
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.BadEvents
open Algsuperdiff.Frozen.Section24

noncomputable section

variable {d : ℕ}

/-! ## Part A -- the coverage geometry -/

private theorem two_abs_lt_iff' {y K : ℤ} : 2 * |y| < K ↔ (-K < 2 * y ∧ 2 * y < K) := by
  rcases abs_cases y with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> omega

private theorem three_pow_odd' (t : ℕ) : ∃ j : ℤ, (3 : ℤ) ^ t = 2 * j + 1 := by
  induction t with
  | zero => exact ⟨0, by norm_num⟩
  | succ p ih =>
      obtain ⟨j, hj⟩ := ih
      exact ⟨3 * j + 1, by rw [pow_succ, hj]; ring⟩

/-- The scale and index box of a scale-`(n−2)` descendant of the scale-`n`
lattice cube: the index sits within `4` of `9 v`. -/
theorem descendantsAtScale_latticeCube_sub_two_data {n : ℤ} {v : Fin d → ℤ}
    {R : TriadicCube d} (hR : R ∈ descendantsAtScale (latticeCube n v) (n - 2)) :
    R.scale = n - 2 ∧ ∀ i, 2 * |R.index i - 9 * v i| < 9 := by
  have hk : n - 2 ≤ (latticeCube n v).scale := by rw [latticeCube_scale]; omega
  rw [descendantsAtScale_eq_descendantsAtDepth _ hk] at hR
  have htn : ((latticeCube n v).scale - (n - 2)).toNat = 2 := by
    rw [latticeCube_scale]; omega
  rw [htn, mem_descendantsAtDepth_iff] at hR
  obtain ⟨hs, hi⟩ := hR
  rw [latticeCube_scale] at hs
  refine ⟨by omega, fun i => ?_⟩
  have hbox := hi i
  rw [latticeCube_index] at hbox
  norm_num at hbox
  exact hbox

/-- The scale-`(n−2)` descendants of a scale-`n` cube are never empty: the
central one, at index `9 v`, is always there. -/
theorem descendantsAtScale_latticeCube_sub_two_nonempty (n : ℤ) (v : Fin d → ℤ) :
    (descendantsAtScale (latticeCube n v) (n - 2)).Nonempty := by
  refine ⟨latticeCube (n - 2) (fun i => 9 * v i), ?_⟩
  have hk : n - 2 ≤ (latticeCube n v).scale := by rw [latticeCube_scale]; omega
  rw [descendantsAtScale_eq_descendantsAtDepth _ hk]
  have htn : ((latticeCube n v).scale - (n - 2)).toNat = 2 := by
    rw [latticeCube_scale]; omega
  rw [htn, mem_descendantsAtDepth_iff]
  refine ⟨by rw [latticeCube_scale, latticeCube_scale]; omega, fun i => ?_⟩
  rw [latticeCube_index, latticeCube_index]
  norm_num

/-- **The coverage step.**  For a scale-`n` lattice cube of `□_m` that is *not* the centred
one, every scale-`(n−2)` descendant sits at a lattice index of the annulus `□_m
∖ □_n` — precisely the index family `𝒢₀(m)` controls at `k = n`.

`v ≠ 0` is necessary and not merely convenient: at `v = 0` all `9^d`
descendants have `|index| ≤ 4`, hence base point inside `□_n`, and `𝒢₀` reaches
none of them (module docstring). -/
theorem index_mem_latticeAnnulusSet_of_mem_descendantsAtScale {n m : ℤ}
    (hnm : n ≤ m) {v : Fin d → ℤ} (hv : v ∈ Support.latticeCubeSet d n m)
    (hv0 : v ≠ 0) {R : TriadicCube d}
    (hR : R ∈ descendantsAtScale (latticeCube n v) (n - 2)) :
    R.index ∈ Support.latticeAnnulusSet d (n - 2) m n := by
  obtain ⟨-, hbox⟩ := descendantsAtScale_latticeCube_sub_two_data hR
  have hvbox := (mem_latticeCubeSet_iff hnm v).mp hv
  refine ⟨?_, ?_⟩
  · refine (mem_latticeCubeSet_iff (by omega : n - 2 ≤ m) R.index).mpr fun i => ?_
    obtain ⟨j, hj⟩ := three_pow_odd' (m - n).toNat
    have hpow : ((3 : ℤ) ^ (m - (n - 2)).toNat) = 9 * (3 : ℤ) ^ (m - n).toNat := by
      have h2 : (m - (n - 2)).toNat = (m - n).toNat + 2 := by omega
      rw [h2, pow_add]; ring
    rw [hpow, two_abs_lt_iff']
    have h1 := two_abs_lt_iff'.mp (hvbox i)
    have h2 := two_abs_lt_iff'.mp (hbox i)
    omega
  · intro hmem
    have hin : R.index ∈ Support.latticeCubeSet d (n - 2) n := hmem
    have hbox2 := (mem_latticeCubeSet_iff (by omega : n - 2 ≤ n) R.index).mp hin
    have hpow : ((3 : ℤ) ^ (n - (n - 2)).toNat) = 9 := by
      have h2 : (n - (n - 2)).toNat = 2 := by omega
      rw [h2]; norm_num
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hv0 (funext hcon)
    have h1 := two_abs_lt_iff'.mp (hbox2 i)
    rw [hpow] at h1
    have h2 := two_abs_lt_iff'.mp (hbox i)
    omega

/-- The centred cube is the only scale-`n` lattice cube whose base point lies in
`□_n`; hence an annulus index is nonzero. -/
theorem ne_zero_of_mem_latticeAnnulusSet {n m : ℤ} {v : Fin d → ℤ}
    (hv : v ∈ Support.latticeAnnulusSet d n m n) : v ≠ 0 := by
  intro hv0
  refine hv.2 ?_
  have hmem : v ∈ Support.latticeCubeSet d n n := by
    refine (mem_latticeCubeSet_iff (le_refl n) v).mpr fun i => ?_
    have h0 : ((n - n).toNat) = 0 := by omega
    rw [hv0, h0]
    simp only [Pi.zero_apply, abs_zero, mul_zero, pow_zero]
    norm_num
  exact hmem

/-! ## Part B -- the descendant atom, read off `𝒢₀` -/

private theorem latticeCube_eq_localize (j : ℤ) (v : Fin d → ℤ) :
    latticeCube j v = Localize.latticeCube j v := rfl

private theorem coarseTwo_val :
    Support.coarseEllipticityExponentTwo.1 = (Ch02.MultiscaleExponent.finite 2) := rfl

/-- **The `𝒢₀` reading at one annulus descendant.**  For an annulus lattice
index `w` of `□_m ∖ □_n`, the `λ_{γ,2}^{-1}` of the scale-`(n−2)` cube at `w`,
read at the cutoff field `a_{n−2}`, is at most
`σ_{n−3}^{-1}(C_cg + 3^{γ(m−n)/4})`.  This is `𝒢₀`'s own inequality at the
single index `k = n`, rearranged. -/
theorem inv_lambdaSq_latticeCube_le_of_mem_eventG0 (M : ABKModel d) (Ccg : ℝ)
    {m n : ℤ} (hn : n ≤ m - 1) {omega : Cutoff.CutoffSample d}
    (homega : omega ∈ Support.eventG0 M Ccg m)
    {w : Fin d → ℤ} (hw : w ∈ Support.latticeAnnulusSet d (n - 2) m n) :
    (Ch02.lambdaSq (latticeCube (n - 2) w) M.gamma (.finite 2)
        (Cutoff.coefficientCutoffTriadicCoeffFamily M (n - 2) omega))⁻¹ ≤
      ((Annealed.sigmaBar M (n - 3) : ℝ))⁻¹ *
        (Ccg + (3 : ℝ) ^ ((1 / 4 : ℝ) * M.gamma * ((m - n : ℤ) : ℝ))) := by
  have hs3 : (0 : ℝ) < (Annealed.sigmaBar M (n - 3) : ℝ) :=
    (Annealed.sigmaBar M (n - 3)).2
  have hatom := Localize.cgExcess_le_of_mem_eventG0 M Ccg hn homega ⟨w, hw⟩
  rw [Localize.cgExcess_sub_two] at hatom
  have hle : (Annealed.sigmaBar M (n - 3) : ℝ) *
      Support.lambdaAnnulusAtom M n (Support.triadicLatticePoint (n - 2) w) omega
        - Ccg ≤ (3 : ℝ) ^ ((1 / 4 : ℝ) * M.gamma * ((m - n : ℤ) : ℝ)) :=
    le_trans (le_max_left _ _) hatom
  rw [Localize.lambdaAnnulusAtom_eq_inv_lambdaSq, coarseTwo_val,
    ← latticeCube_eq_localize] at hle
  have hmul := mul_le_mul_of_nonneg_left
    (show (Annealed.sigmaBar M (n - 3) : ℝ) *
        (Ch02.lambdaSq (latticeCube (n - 2) w) M.gamma (.finite 2)
          (Cutoff.coefficientCutoffTriadicCoeffFamily M (n - 2) omega))⁻¹ ≤
      Ccg + (3 : ℝ) ^ ((1 / 4 : ℝ) * M.gamma * ((m - n : ℤ) : ℝ)) from by
      linarith only [hle]) (inv_pos.2 hs3).le
  rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hs3), one_mul] at hmul

/-! ## Part C -- the one-step `σ` ratio -/

private theorem three_rpow_mono₄ {x y : ℝ} (h : x ≤ y) : (3 : ℝ) ^ x ≤ (3 : ℝ) ^ y :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) h

private theorem three_rpow_half_le_two₄ : (3 : ℝ) ^ ((1 : ℝ) / 2) ≤ 2 := by
  refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by norm_num) ?_
  have hsq : ((3 : ℝ) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = 3 := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ ((1 : ℝ) / 2)) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  rw [hsq]
  norm_num

/-- **The one-step running-diffusivity ratio.**  Both branches of
`e.shom.h.bounds` at the two consecutive indices, with the shift `3^{2γ} ≤ 2`
supplied by the standing `γ ≤ 1/4`.  This converts `𝒢₀`'s `σ_{n−3}` bracket
into the budget's `σ_{n−2}` at the absolute numeral `8`. -/
theorem sigmaBar_sub_two_le_eight_mul_sigmaBar_sub_three (M : ABKModel d) {m0 : ℤ}
    {E : {E : ℝ // 1 ≤ E}} (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E)
    {n : ℤ} (hn : n - 2 ≤ m0) :
    (Annealed.sigmaBar M (n - 2) : ℝ) ≤ 8 * (Annealed.sigmaBar M (n - 3) : ℝ) := by
  have hg0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hg14 : M.gamma ≤ 1 / 4 := M.shellPrefix.gamma_le_quarter
  have hs3 : (0 : ℝ) < (Annealed.sigmaBar M (n - 3) : ℝ) :=
    (Annealed.sigmaBar M (n - 3)).2
  have hup := (hS.1 (n - 2) hn).2
  have hlow := (hS.1 (n - 3) (by omega)).1
  have hA3 : (0 : ℝ) ≤ Disorder.cstar M * M.gamma⁻¹ *
      (3 : ℝ) ^ (2 * M.gamma * (((n - 3 : ℤ)) : ℝ)) := by
    have hcs : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
    positivity
  have hsplit : (3 : ℝ) ^ (2 * M.gamma * (((n - 2 : ℤ)) : ℝ))
      = (3 : ℝ) ^ (2 * M.gamma) * (3 : ℝ) ^ (2 * M.gamma * (((n - 3 : ℤ)) : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  have h2g : (3 : ℝ) ^ (2 * M.gamma) ≤ 2 :=
    le_trans (three_rpow_mono₄ (by linarith only [hg14])) three_rpow_half_le_two₄
  have hmaxlow : (0 : ℝ) ≤ max (Disorder.cstar M * M.gamma⁻¹ *
      (3 : ℝ) ^ (2 * M.gamma * (((n - 3 : ℤ)) : ℝ))) (M.nu ^ 2) :=
    le_trans hA3 (le_max_left _ _)
  have hmax : max (Disorder.cstar M * M.gamma⁻¹ *
        (3 : ℝ) ^ (2 * M.gamma * (((n - 2 : ℤ)) : ℝ))) (M.nu ^ 2)
      ≤ 2 * max (Disorder.cstar M * M.gamma⁻¹ *
          (3 : ℝ) ^ (2 * M.gamma * (((n - 3 : ℤ)) : ℝ))) (M.nu ^ 2) := by
    refine max_le ?_ ?_
    · rw [hsplit]
      have hstep : Disorder.cstar M * M.gamma⁻¹ *
          ((3 : ℝ) ^ (2 * M.gamma) *
            (3 : ℝ) ^ (2 * M.gamma * (((n - 3 : ℤ)) : ℝ)))
          ≤ 2 * (Disorder.cstar M * M.gamma⁻¹ *
            (3 : ℝ) ^ (2 * M.gamma * (((n - 3 : ℤ)) : ℝ))) := by
        have := mul_le_mul_of_nonneg_left h2g hA3
        linarith only [this]
      have hmono := le_max_left (Disorder.cstar M * M.gamma⁻¹ *
        (3 : ℝ) ^ (2 * M.gamma * (((n - 3 : ℤ)) : ℝ))) (M.nu ^ 2)
      linarith only [hstep, hmono]
    · have hmono := le_max_right (Disorder.cstar M * M.gamma⁻¹ *
        (3 : ℝ) ^ (2 * M.gamma * (((n - 3 : ℤ)) : ℝ))) (M.nu ^ 2)
      linarith only [hmono, hmaxlow]
  have hsq : (Annealed.sigmaBar M (n - 2) : ℝ) ^ 2
      ≤ (8 * (Annealed.sigmaBar M (n - 3) : ℝ)) ^ 2 := by
    have hexpand : (8 * (Annealed.sigmaBar M (n - 3) : ℝ)) ^ 2
        = 64 * (Annealed.sigmaBar M (n - 3) : ℝ) ^ 2 := by ring
    rw [hexpand]
    have hsq3 : (0 : ℝ) ≤ (Annealed.sigmaBar M (n - 3) : ℝ) ^ 2 := sq_nonneg _
    linarith only [hup, hlow, hmax, hsq3]
  exact le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by linarith only [hs3]) hsq

/-! ## Part D -- the `hlam` display -/

/-- The `hlam` constant: `8 (1 + 9^d)(1 + C_cg)`.  The `8` is the one-step `σ`
ratio, the `1 + 9^d` is the cube-raising at separation `2` (its sharp value `1
+ 9^d 3^{−4γ}` is only relaxed here), and the `1 + C_cg` is the `𝒢₀` bracket.
Dimension and `C_cg` only: no `s`, no `γ`, no `c⋆`. -/
def annularLambdaConstant (d : ℕ) (Ccg : ℝ) : ℝ := 8 * (1 + 9 ^ d) * (1 + Ccg)

theorem annularLambdaConstant_nonneg (d : ℕ) {Ccg : ℝ} (hCcg : 0 ≤ Ccg) :
    0 ≤ annularLambdaConstant d Ccg := by
  unfold annularLambdaConstant
  have h9 : (0 : ℝ) ≤ (9 : ℝ) ^ d := by positivity
  positivity

/-- **The `hlam` budget, discharged** at the gapped gauge `s = 2γ`, on `𝒢₀(m)` and
at every annulus lattice cube of `□_m ∖ □_n`.

The four steps are the gauge antitonicity, the cube-raising bound of
`LambdaMatrixRoute`, the coverage step proved above, and the one-step `σ` ratio; the constant is
`annularLambdaConstant d C_cg = 8(1+9^d)(1+C_cg)`, and the printed weight
`3^{γ(m−n)}` is unchanged (the event supplies only `3^{γ(m−n)/4}`, so three
quarters of the printed discount is left on the table).

`v ≠ 0` — carried here as `v ∈ latticeAnnulusSet d n m n` — is essential: see
the module docstring for the exact uncovered class. -/
theorem sigmaBar_mul_inv_unitCubeLambda_two_gamma_le_of_mem_eventG0 [NeZero d]
    (M : ABKModel d) {Ccg : ℝ} (hCcg : 0 ≤ Ccg) {m0 : ℤ} {E : {E : ℝ // 1 ≤ E}}
    (hS : Algsuperdiff.Frozen.Section3.inductionState M m0 E) {m n : ℤ}
    (hn : n ≤ m - 1) (hn2 : n - 2 ≤ m0) {omega : Cutoff.CutoffSample d}
    (homega : omega ∈ Support.eventG0 M Ccg m) {v : Fin d → ℤ}
    (hv : v ∈ Support.latticeAnnulusSet d n m n) :
    (Annealed.sigmaBar M (n - 2) : ℝ) *
        (unitCubeLambda (2 * M.gamma) (.finite 2)
          (unitRescaledCutoffCoeff M (⟨n, v⟩ : TriadicCube d) (n - 2) omega))⁻¹ ≤
      annularLambdaConstant d Ccg * (3 : ℝ) ^ (M.gamma * ((m : ℝ) - (n : ℝ))) := by
  classical
  have hg0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hs2 : (0 : ℝ) < (Annealed.sigmaBar M (n - 2) : ℝ) :=
    (Annealed.sigmaBar M (n - 2)).2
  have hs3 : (0 : ℝ) < (Annealed.sigmaBar M (n - 3) : ℝ) :=
    (Annealed.sigmaBar M (n - 3)).2
  set a := Cutoff.coefficientCutoffTriadicCoeffFamily M (n - 2) omega with ha
  -- the carrier identification
  rw [unitCubeLambda_unitRescaledCutoffCoeff M (⟨n, v⟩ : TriadicCube d) (n - 2)
    (2 * M.gamma) (.finite 2) omega, ← ha]
  -- step 1: the gauge antitonicity
  have hgauge : (Ch02.lambdaSq (⟨n, v⟩ : TriadicCube d) (2 * M.gamma) (.finite 2) a)⁻¹
      ≤ (Ch02.lambdaSq (⟨n, v⟩ : TriadicCube d) M.gamma (.finite 2) a)⁻¹ :=
    Localize.inv_lambdaSq_two_antitone_gauge _ a hg0 (by linarith only [hg0])
  -- step 2: the cube-raising at separation two
  have hraise : (Ch02.lambdaSq (⟨n, v⟩ : TriadicCube d) M.gamma (.finite 2) a)⁻¹ ≤
      (1 + ((9 : ℝ) ^ d) * (3 : ℝ) ^ (-(4 * M.gamma))) *
        Ch02.finsetSupReal (descendantsAtScale (latticeCube n v) (n - 2)) fun R =>
          (Ch02.lambdaSq R M.gamma (.finite 2) a)⁻¹ := by
    have h := lambdaSq_finite_two_inv_le_nine_pow_mul_max_descendants_sub_two
      (⟨n, v⟩ : TriadicCube d) a hg0
    exact h
  -- step 3: the coverage, and the event bound at every descendant
  set B : ℝ := ((Annealed.sigmaBar M (n - 3) : ℝ))⁻¹ *
    (Ccg + (3 : ℝ) ^ ((1 / 4 : ℝ) * M.gamma * ((m - n : ℤ) : ℝ))) with hB
  have hsup : Ch02.finsetSupReal (descendantsAtScale (latticeCube n v) (n - 2))
      (fun R => (Ch02.lambdaSq R M.gamma (.finite 2) a)⁻¹) ≤ B := by
    refine Ch02.finsetSupReal_le _
      (descendantsAtScale_latticeCube_sub_two_nonempty n v) fun R hR => ?_
    obtain ⟨hscale, -⟩ := descendantsAtScale_latticeCube_sub_two_data hR
    have hidx := index_mem_latticeAnnulusSet_of_mem_descendantsAtScale
      (by omega : n ≤ m) hv.1 (ne_zero_of_mem_latticeAnnulusSet hv) hR
    have hRe : R = latticeCube (n - 2) R.index := by
      rw [← hscale]
      exact (latticeCube_index_self R).symm
    rw [hRe]
    exact inv_lambdaSq_latticeCube_le_of_mem_eventG0 M Ccg hn homega hidx
  -- the constants
  have hcard : (0 : ℝ) ≤ (9 : ℝ) ^ d := by positivity
  have hdisc : (3 : ℝ) ^ (-(4 * M.gamma)) ≤ 1 := by
    have hmono := three_rpow_mono₄ (show -(4 * M.gamma) ≤ (0 : ℝ) by linarith only [hg0])
    rwa [Real.rpow_zero] at hmono
  have hCd0 : (0 : ℝ) ≤ 1 + ((9 : ℝ) ^ d) * (3 : ℝ) ^ (-(4 * M.gamma)) := by positivity
  have hCd : 1 + ((9 : ℝ) ^ d) * (3 : ℝ) ^ (-(4 * M.gamma)) ≤ 1 + (9 : ℝ) ^ d := by
    have := mul_le_mul_of_nonneg_left hdisc hcard
    linarith only [this]
  have hB0 : (0 : ℝ) ≤ B := by
    rw [hB]
    have h1 : (0 : ℝ) ≤ (Annealed.sigmaBar M (n - 3) : ℝ)⁻¹ := (inv_pos.2 hs3).le
    have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 / 4 : ℝ) * M.gamma * ((m - n : ℤ) : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    have h3 : (0 : ℝ) ≤ Ccg + (3 : ℝ) ^ ((1 / 4 : ℝ) * M.gamma * ((m - n : ℤ) : ℝ)) := by
      linarith only [hCcg, h2]
    exact mul_nonneg h1 h3
  -- step 4: the `σ` ratio
  have hratio : (Annealed.sigmaBar M (n - 2) : ℝ) *
      ((Annealed.sigmaBar M (n - 3) : ℝ))⁻¹ ≤ 8 := by
    have hle := sigmaBar_sub_two_le_eight_mul_sigmaBar_sub_three M hS hn2
    have hstep := mul_le_mul_of_nonneg_right hle (inv_pos.2 hs3).le
    rwa [mul_assoc, mul_inv_cancel₀ (ne_of_gt hs3), mul_one] at hstep
  -- the weights
  have hq0 : (0 : ℝ) ≤ ((m - n : ℤ) : ℝ) := by
    have : (0 : ℤ) ≤ m - n := by omega
    exact_mod_cast this
  have hX1 : (1 : ℝ) ≤ (3 : ℝ) ^ ((1 / 4 : ℝ) * M.gamma * ((m - n : ℤ) : ℝ)) := by
    have hmono := three_rpow_mono₄
      (show (0 : ℝ) ≤ (1 / 4 : ℝ) * M.gamma * ((m - n : ℤ) : ℝ) by positivity)
    rwa [Real.rpow_zero] at hmono
  have hXW : (3 : ℝ) ^ ((1 / 4 : ℝ) * M.gamma * ((m - n : ℤ) : ℝ)) ≤
      (3 : ℝ) ^ (M.gamma * ((m : ℝ) - (n : ℝ))) := by
    refine three_rpow_mono₄ ?_
    have hcast : ((m - n : ℤ) : ℝ) = (m : ℝ) - (n : ℝ) := by push_cast; ring
    rw [hcast]
    have hq0' : (0 : ℝ) ≤ (m : ℝ) - (n : ℝ) := by rw [← hcast]; exact hq0
    have := mul_le_mul_of_nonneg_right
      (show (1 / 4 : ℝ) * M.gamma ≤ M.gamma by linarith only [hg0]) hq0'
    linarith only [this]
  -- the assembly
  calc (Annealed.sigmaBar M (n - 2) : ℝ) *
        (Ch02.lambdaSq (⟨n, v⟩ : TriadicCube d) (2 * M.gamma) (.finite 2) a)⁻¹
      ≤ (Annealed.sigmaBar M (n - 2) : ℝ) *
          ((1 + ((9 : ℝ) ^ d) * (3 : ℝ) ^ (-(4 * M.gamma))) * B) :=
        mul_le_mul_of_nonneg_left
          (le_trans hgauge (le_trans hraise
            (mul_le_mul_of_nonneg_left hsup hCd0))) hs2.le
    _ = ((1 + ((9 : ℝ) ^ d) * (3 : ℝ) ^ (-(4 * M.gamma))) *
          ((Annealed.sigmaBar M (n - 2) : ℝ) *
            ((Annealed.sigmaBar M (n - 3) : ℝ))⁻¹)) *
          (Ccg + (3 : ℝ) ^ ((1 / 4 : ℝ) * M.gamma * ((m - n : ℤ) : ℝ))) := by
        rw [hB]; ring
    _ ≤ ((1 + (9 : ℝ) ^ d) * 8) *
          ((1 + Ccg) * (3 : ℝ) ^ ((1 / 4 : ℝ) * M.gamma * ((m - n : ℤ) : ℝ))) := by
        refine mul_le_mul ?_ ?_ ?_ ?_
        · exact mul_le_mul hCd hratio
            (mul_nonneg hs2.le (inv_pos.2 hs3).le) (by positivity)
        · have hstep : Ccg * 1 ≤
              Ccg * (3 : ℝ) ^ ((1 / 4 : ℝ) * M.gamma * ((m - n : ℤ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hX1 hCcg
          linarith only [hstep]
        · have h2 : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 / 4 : ℝ) * M.gamma * ((m - n : ℤ) : ℝ)) :=
            Real.rpow_nonneg (by norm_num) _
          linarith only [hCcg, h2]
        · have := hcard
          positivity
    _ ≤ annularLambdaConstant d Ccg * (3 : ℝ) ^ (M.gamma * ((m : ℝ) - (n : ℝ))) := by
        unfold annularLambdaConstant
        have hcoef : (0 : ℝ) ≤ 8 * (1 + (9 : ℝ) ^ d) * (1 + Ccg) := by
          have := hcard; positivity
        have hstep := mul_le_mul_of_nonneg_left hXW hcoef
        calc ((1 + (9 : ℝ) ^ d) * 8) *
              ((1 + Ccg) * (3 : ℝ) ^ ((1 / 4 : ℝ) * M.gamma * ((m - n : ℤ) : ℝ)))
            = 8 * (1 + (9 : ℝ) ^ d) * (1 + Ccg) *
                (3 : ℝ) ^ ((1 / 4 : ℝ) * M.gamma * ((m - n : ℤ) : ℝ)) := by ring
          _ ≤ 8 * (1 + (9 : ℝ) ^ d) * (1 + Ccg) *
                (3 : ℝ) ^ (M.gamma * ((m : ℝ) - (n : ℝ))) := hstep

end

end Algsuperdiff.Section4.Provider.Annular
