/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.LatticeCover
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.Step1

/-!
# EventBudgets

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The two on-event budget slots of the clause-(i) assembly

ABK26, Section 4.1, Step 2 of `p.mathcalE.annular.decomp` and Step 3's
gradient resummation.

`ClauseOne.clauseOne_bound` carries the *gradient* comparison as the named slot

```
hcsGn : forall j n, j <= m -> n <= j - 1 ->
          gradNf j n <= Kgn * ((m - n) + 2)
                        * sum_{v < (m-n)+2} A (m - v) ^ 2 ,
```

where `A` is the shell block family `A(k) = 3^{(2-gamma)k} max_{z in 3^k Z^d
∩ cu_m} ||j_k||_{W^{2,infinity}(z+cu_k)}` -- pinned by the A5b interface to
`DisplaySlots.shellBlockLatticeReal`, which is literally the bracket of the
frozen clause-(i) fourth term and of `Support.eventG1`'s second condition.

This module discharges that slot at the **honest** fourth-term content

```
gradNf j n = ( 3^{(2-gamma)n}
                 max_{z in 3^n Z^d ∩ (cu_j \ cu_{j-1})}
                   ||grad (k_m - k_{n-2})||_{W^{1,infinity}(z+cu_n)} )^2 ,
```

i.e. `annularGradBlock` below, at the explicit constant `Kgn = 81`.

Part E does the same for the companion `hcsL2` slot -- the `L^2` term of
`e.mathcalE.annular.decomp.pre.zero` -- at the family

```
L2f j n = ( 3^{-gamma n}
              max_{z in 3^n Z^d ∩ (cu_j \ cu_{j-1})}
                ||k_m - k_{n-2}||_{L^infinity(z+cu_n)} )^2 ,
```

i.e. `annularL2Block`, at the constant `Kl2 = 1`.  The printed content is the
volume-normalized `L^2` norm on the same cube; the `L^infinity` norm dominates
it there, so the family below is the conservative reading (a producer of the
per-cube ugly estimate at the honest `L^2` norm feeds it unchanged).

## The three moves

1. **The layer sum**.  `k_m - k_{n-2} = sum_{l in (n-2, m]} j_l`, and
   `Support.shellW1InfGradNorm_translate_shellIncrement_le` is the triangle
   inequality at the translated Section 4 gauge.
2. **The lattice-max enlargement**.  Each shell term is dominated by `9 A(l)`
   -- `LatticeCover`'s tiling result, together with the weight arithmetic
   `3^{(2-gamma)n} max(1, 3^{l-n}) <= 9 * 3^{(2-gamma)l}` valid for every `l >=
   n - 1` (the honest range: the layer sum starts at `l = n - 1`, one scale
   *below* the cube, which is exactly where the factor `9 = 3^2 >= 3^{2-gamma}`
   is spent).
3. **Cauchy--Schwarz with the annulus count**.  The layer range `(n-2, m]` has
   exactly `(m-n)+2` members, and reindexing it by `l = m - v` turns `(sum_l
   A(l))^2 <= ((m-n)+2) sum_l A(l)^2` into the printed shape.

Both slots are pointwise in the sample: no event membership and nothing
probabilistic enters.  The good event `Support.eventG1` is what later bounds
the *sums* of `A(k)^2` these two displays produce; that is Step 3's business,
not this module's.

## References

* ABK26, `p.mathcalE.annular.decomp` Step 2.
* ABK26, `p.mathcalE.annular.decomp` Step 3.
* (the `(1-gamma)` shell rate of the volume-normalized cube comparison),
  consistent with the weight arithmetic of move 2.
-/

namespace Algsuperdiff.Section4.Provider.Annular

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Section3
open Algsuperdiff.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-! ## Part A -- the weight arithmetic, over abstract reals -/

private theorem three_rpow_mono {x y : ℝ} (h : x ≤ y) : (3 : ℝ) ^ x ≤ (3 : ℝ) ^ y :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) h

/-- **The Step-2 weight arithmetic.**  For a shell index `ll` at or above
`nn - 1` -- the honest range of the layer sum `(n-2, m]` -- the cube-comparison
factor `max(1, 3^{ll-nn})` is paid for by the constant `9`:

```
3^{(2-gam) nn} max(1, 3^{ll-nn}) <= 9 * 3^{(2-gam) ll} .
```

Both branches are tight at `ll = nn - 1`, where the factor is `3^{2-gam}`. -/
theorem three_rpow_gauge_weight_le {gam nn ll : ℝ} (hg0 : 0 ≤ gam) (hg1 : gam ≤ 1)
    (hl : nn - 1 ≤ ll) :
    (3 : ℝ) ^ ((2 - gam) * nn) * max 1 ((3 : ℝ) ^ (ll - nn))
      ≤ 9 * (3 : ℝ) ^ ((2 - gam) * ll) := by
  have h9 : (9 : ℝ) = (3 : ℝ) ^ (2 : ℝ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    norm_num
  have hbranch1 : (3 : ℝ) ^ ((2 - gam) * nn) * 1 ≤ 9 * (3 : ℝ) ^ ((2 - gam) * ll) := by
    rw [mul_one, h9, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    refine three_rpow_mono ?_
    have hstep : (2 - gam) * (nn - ll) ≤ 2 := by
      rcases le_or_gt nn ll with h | h
      · have h1 : (2 - gam) * (nn - ll) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by linarith only [hg1]) (by linarith only [h])
        linarith only [h1]
      · have hpos : (0 : ℝ) ≤ nn - ll := by linarith only [h]
        have hle : nn - ll ≤ 1 := by linarith only [hl]
        have h1 : (2 - gam) * (nn - ll) ≤ 2 * 1 := by
          have hstep1 : (2 - gam) * (nn - ll) ≤ 2 * (nn - ll) :=
            mul_le_mul_of_nonneg_right (by linarith only [hg0]) hpos
          have hstep2 : 2 * (nn - ll) ≤ 2 * 1 :=
            mul_le_mul_of_nonneg_left hle (by norm_num)
          linarith only [hstep1, hstep2]
        linarith only [h1]
    linarith only [hstep]
  have hbranch2 : (3 : ℝ) ^ ((2 - gam) * nn) * (3 : ℝ) ^ (ll - nn)
      ≤ 9 * (3 : ℝ) ^ ((2 - gam) * ll) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3), h9,
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    refine three_rpow_mono ?_
    have hstep : (1 - gam) * (nn - ll) ≤ 2 := by
      rcases le_or_gt nn ll with h | h
      · have h1 : (1 - gam) * (nn - ll) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by linarith only [hg1]) (by linarith only [h])
        linarith only [h1]
      · have hpos : (0 : ℝ) ≤ nn - ll := by linarith only [h]
        have hle : nn - ll ≤ 1 := by linarith only [hl]
        have hstep1 : (1 - gam) * (nn - ll) ≤ 1 * (nn - ll) :=
          mul_le_mul_of_nonneg_right (by linarith only [hg0]) hpos
        have hstep2 : (1 : ℝ) * (nn - ll) ≤ 1 * 1 :=
          mul_le_mul_of_nonneg_left hle (by norm_num)
        linarith only [hstep1, hstep2]
    linarith only [hstep]
  rcases max_cases (1 : ℝ) ((3 : ℝ) ^ (ll - nn)) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he]
  · exact hbranch1
  · exact hbranch2

/-! ## Part B -- the per-shell atom bound at the pinned lattice family -/

/-- **The per-shell atom bound**.  On the annulus cube `z + cu_n` with `z` a
scale-`n` lattice point of `cu_j`, the weighted `W^{1,infinity}` gauge of the
shell `j_l` is at most `9 A(l)`, with `A = shellBlockLatticeReal` the pinned
lattice family of the frozen fourth term, for every layer index `l` with `n - 1
<= l <= m`. -/
theorem three_rpow_mul_shellW1InfGradNorm_translate_le_shellBlockLatticeReal
    (M : ABKModel d) {m j n l : ℤ} (hjm : j ≤ m) (hnj : n ≤ j - 1)
    (hln : n - 1 ≤ l) (hlm : l ≤ m) (omega : Cutoff.CutoffSample d)
    {v : Fin d → ℤ} (hv : v ∈ Support.latticeAnnulusSet d n j (j - 1)) :
    (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
        Support.shellW1InfGradNorm n
          (ShellField.translate (Support.triadicLatticePoint n v) (omega.1 l))
      ≤ 9 * shellBlockLatticeReal M m omega l := by
  have hg0 : (0 : ℝ) ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hg1 : M.gamma ≤ 1 := by
    have := M.shellPrefix.gamma_le_quarter
    linarith only [this]
  have hnm : n ≤ m := by omega
  have hvm : v ∈ Support.latticeCubeSet d n m :=
    openCubeSet_originCube_subset hjm hv.1
  have hL0 : 0 ≤ shellW2InfLatticeMaxOf m l (omega.1 l) :=
    shellW2InfLatticeMaxOf_nonneg m l (omega.1 l)
  have hgauge :=
    shellW1InfGradNorm_translate_le_shellW2InfLatticeMaxOf hnm hlm hvm (omega.1 l)
  have hpos : (0 : ℝ) < (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) := by positivity
  have hstep := mul_le_mul_of_nonneg_left hgauge hpos.le
  have hzpow : ((3 : ℝ) ^ (l - n) : ℝ) = (3 : ℝ) ^ (((l : ℝ)) - (n : ℝ)) := by
    rw [show ((l : ℝ)) - (n : ℝ) = (((l - n : ℤ) : ℝ)) from by push_cast; ring,
      Real.rpow_intCast]
  have hweight := three_rpow_gauge_weight_le (gam := M.gamma) (nn := (n : ℝ))
    (ll := (l : ℝ)) hg0 hg1 (by
      have hz : ((n - 1 : ℤ) : ℝ) ≤ ((l : ℤ) : ℝ) := by exact_mod_cast hln
      push_cast at hz
      linarith only [hz])
  rw [hzpow] at hstep
  have hfinal : (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
      (max 1 ((3 : ℝ) ^ ((l : ℝ) - (n : ℝ))) * shellW2InfLatticeMaxOf m l (omega.1 l))
      ≤ (9 * (3 : ℝ) ^ ((2 - M.gamma) * (l : ℝ)))
        * shellW2InfLatticeMaxOf m l (omega.1 l) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hweight hL0
  have hdef : shellBlockLatticeReal M m omega l
      = (3 : ℝ) ^ ((2 - M.gamma) * (l : ℝ)) * shellW2InfLatticeMaxOf m l (omega.1 l) :=
    rfl
  refine le_trans hstep (le_trans hfinal (le_of_eq ?_))
  rw [hdef]
  ring

/-! ## Part C -- the layer sum and the reindexing -/

private theorem sum_Ioc_eq_sum_range {n m : ℤ} (hnm : n ≤ m) (f : ℤ → ℝ) :
    ∑ l ∈ Finset.Ioc (n - 2) m, f l
      = ∑ u ∈ Finset.range ((m - n).toNat + 2), f (m - (u : ℤ)) := by
  classical
  have himg : Finset.Ioc (n - 2) m
      = (Finset.range ((m - n).toNat + 2)).image fun u : ℕ => m - (u : ℤ) := by
    ext l
    simp only [Finset.mem_Ioc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(m - l).toNat, by omega, by omega⟩
    · rintro ⟨u, hu, rfl⟩
      omega
  have hinj : Set.InjOn (fun u : ℕ => m - (u : ℤ))
      (↑(Finset.range ((m - n).toNat + 2)) : Set ℕ) := by
    intro x _hx y _hy hxy
    have hxy' : m - (x : ℤ) = m - (y : ℤ) := hxy
    omega
  rw [himg, Finset.sum_image hinj]

/-! ## Part D -- the honest fourth-term content, and the `hcsGn` slot -/

/-- **The head-block gradient content of the clause-(i) fourth term.**

The fourth term of `e.mathcalE.annular.decomp.pre.zero` after the `m`-vs-`L`
tail routing of `ClauseOne.isUglyJEstimate_routeTail`: the annulus maximum of
the volume-normalized `W^{1,infinity}` gauge of `grad (k_m - k_{n-2})`,
weighted by `3^{(2-gamma)n}` and squared.  This is the `gradNf` family
`clauseOne_bound` consumes. -/
def annularGradBlock (M : ABKModel d) (m : ℤ) (omega : Cutoff.CutoffSample d)
    (j n : ℤ) : ℝ :=
  ((3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
    Proportion.fmax (Proportion.latticeAnnulusFinset d n j (j - 1))
      fun v => Support.shellW1InfGradNorm n
        (ShellField.translate (Support.triadicLatticePoint n v)
          (Provider.Stream.shellIncrement omega.1 (n - 2) m))) ^ 2

theorem annularGradBlock_nonneg (M : ABKModel d) (m : ℤ)
    (omega : Cutoff.CutoffSample d) (j n : ℤ) :
    0 ≤ annularGradBlock M m omega j n :=
  sq_nonneg _

/-- **The layer bound.**  The weighted annulus maximum of the increment gauge is
at most `9` times the layer sum of the pinned lattice family. -/
theorem three_rpow_mul_fmax_le_sum (M : ABKModel d) {m j n : ℤ} (hjm : j ≤ m)
    (hnj : n ≤ j - 1) (omega : Cutoff.CutoffSample d) :
    (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
        Proportion.fmax (Proportion.latticeAnnulusFinset d n j (j - 1))
          (fun v => Support.shellW1InfGradNorm n
            (ShellField.translate (Support.triadicLatticePoint n v)
              (Provider.Stream.shellIncrement omega.1 (n - 2) m)))
      ≤ 9 * ∑ l ∈ Finset.Ioc (n - 2) m, shellBlockLatticeReal M m omega l := by
  have hpos : (0 : ℝ) < (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) := by positivity
  have hsum0 : 0 ≤ ∑ l ∈ Finset.Ioc (n - 2) m, shellBlockLatticeReal M m omega l :=
    Finset.sum_nonneg fun l _ => shellBlockLatticeReal_nonneg M m omega l
  have hbdd : Proportion.fmax (Proportion.latticeAnnulusFinset d n j (j - 1))
      (fun v => Support.shellW1InfGradNorm n
        (ShellField.translate (Support.triadicLatticePoint n v)
          (Provider.Stream.shellIncrement omega.1 (n - 2) m)))
      ≤ ((3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)))⁻¹ *
        (9 * ∑ l ∈ Finset.Ioc (n - 2) m, shellBlockLatticeReal M m omega l) := by
    refine Proportion.fmax_le (by positivity) ?_
    intro v hv
    have hvset : v ∈ Support.latticeAnnulusSet d n j (j - 1) :=
      (Proportion.mem_latticeAnnulusFinset_iff (by omega)).mp hv
    have htri := Support.shellW1InfGradNorm_translate_shellIncrement_le n v omega.1
      (n - 2) m
    have hterm : ∀ l ∈ Finset.Ioc (n - 2) m,
        (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
            Support.shellW1InfGradNorm n
              (ShellField.translate (Support.triadicLatticePoint n v) (omega.1 l))
          ≤ 9 * shellBlockLatticeReal M m omega l := by
      intro l hl
      rw [Finset.mem_Ioc] at hl
      exact three_rpow_mul_shellW1InfGradNorm_translate_le_shellBlockLatticeReal M
        hjm hnj (by omega) hl.2 omega hvset
    have hsum : (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
        ∑ l ∈ Finset.Ioc (n - 2) m,
          Support.shellW1InfGradNorm n
            (ShellField.translate (Support.triadicLatticePoint n v) (omega.1 l))
        ≤ 9 * ∑ l ∈ Finset.Ioc (n - 2) m, shellBlockLatticeReal M m omega l := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_le_sum hterm
    have hleft := mul_le_mul_of_nonneg_left htri hpos.le
    rw [le_inv_mul_iff₀ hpos]
    exact le_trans hleft hsum
  have hmul := mul_le_mul_of_nonneg_left hbdd hpos.le
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), one_mul] at hmul
  exact hmul

/-- **The `hcsGn` slot of `ClauseOne.clauseOne_bound`, at `Kgn = 81`.**

The gradient comparison of Step 3, discharged at the honest fourth-term content
`annularGradBlock` and at the A5b-pinned shell family `shellBlockLatticeReal`.
Every hypothesis is the enclosing display's own scale ordering; nothing
probabilistic and no event membership enters -- the estimate is pointwise in
the sample. -/
theorem annularGradBlock_le (M : ABKModel d) (m : ℤ)
    (omega : Cutoff.CutoffSample d) (j n : ℤ) (hjm : j ≤ m) (hnj : n ≤ j - 1) :
    annularGradBlock M m omega j n
      ≤ 81 * (((m - n : ℤ) : ℝ) + 2)
        * ∑ v ∈ Finset.range ((m - n).toNat + 2),
            shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2 := by
  have hnm : n ≤ m := by omega
  have hbase := three_rpow_mul_fmax_le_sum M hjm hnj omega
  have hfm0 : 0 ≤ (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
      Proportion.fmax (Proportion.latticeAnnulusFinset d n j (j - 1))
        (fun v => Support.shellW1InfGradNorm n
          (ShellField.translate (Support.triadicLatticePoint n v)
            (Provider.Stream.shellIncrement omega.1 (n - 2) m))) := by
    have h1 : (0 : ℝ) ≤ (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    exact mul_nonneg h1 (Proportion.fmax_nonneg _ _)
  have hsq : annularGradBlock M m omega j n
      ≤ (9 * ∑ l ∈ Finset.Ioc (n - 2) m, shellBlockLatticeReal M m omega l) ^ 2 := by
    rw [annularGradBlock]
    exact pow_le_pow_left₀ hfm0 hbase 2
  rw [sum_Ioc_eq_sum_range hnm] at hsq
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := Finset.range ((m - n).toNat + 2))
    (f := fun u : ℕ => shellBlockLatticeReal M m omega (m - (u : ℤ)))
  have hr : (((m - n).toNat : ℕ) : ℝ) = (m : ℝ) - (n : ℝ) := by
    have hz : ((m - n).toNat : ℤ) = m - n := Int.toNat_of_nonneg (by omega)
    have hcast := congrArg (fun z : ℤ => (z : ℝ)) hz
    push_cast at hcast
    exact hcast
  have hcard : ((Finset.range ((m - n).toNat + 2)).card : ℝ) = ((m - n : ℤ) : ℝ) + 2 := by
    rw [Finset.card_range]
    push_cast [hr]
    ring
  rw [hcard] at hcs
  have hexpand : (9 * ∑ u ∈ Finset.range ((m - n).toNat + 2),
        shellBlockLatticeReal M m omega (m - (u : ℤ))) ^ 2
      = 81 * (∑ u ∈ Finset.range ((m - n).toNat + 2),
        shellBlockLatticeReal M m omega (m - (u : ℤ))) ^ 2 := by ring
  rw [hexpand] at hsq
  have hmul := mul_le_mul_of_nonneg_left hcs (by norm_num : (0 : ℝ) ≤ 81)
  have hassoc : (81 : ℝ) * ((((m - n : ℤ) : ℝ) + 2) *
      ∑ u ∈ Finset.range ((m - n).toNat + 2),
        shellBlockLatticeReal M m omega (m - (u : ℤ)) ^ 2)
      = 81 * (((m - n : ℤ) : ℝ) + 2)
        * ∑ v ∈ Finset.range ((m - n).toNat + 2),
            shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2 := by ring
  rw [hassoc] at hmul
  exact le_trans hsq hmul

/-! ## Part E -- the `L^infinity` value leg and the `hcsL2` slot -/

/-- **The Step-2 weight arithmetic at the value leg.**  For a shell index `ll`
at most `mm`, the value gauge's own factor `3^{2 ll}` is converted into the
shell block weight at the cost of the single factor `3^{gam (mm - nn)}`. -/
theorem three_rpow_value_weight_le {gam nn ll mm : ℝ} (hg0 : 0 ≤ gam)
    (hlm : ll ≤ mm) :
    (3 : ℝ) ^ (-(gam * nn)) * (3 : ℝ) ^ (2 * ll)
      ≤ (3 : ℝ) ^ (gam * (mm - nn)) * (3 : ℝ) ^ ((2 - gam) * ll) := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  refine three_rpow_mono ?_
  have hstep : 0 ≤ gam * (mm - ll) :=
    mul_nonneg hg0 (by linarith only [hlm])
  linarith only [hstep]

/-- **The per-shell atom bound at the value leg.**  On the annulus cube
`z + cu_n`, the weighted `L^infinity` norm of the shell `j_l` is at most
`3^{gamma(m-n)} A(l)`, with `A = shellBlockLatticeReal`. -/
theorem three_rpow_mul_localCubeControl_translate_le_shellBlockLatticeReal
    (M : ABKModel d) {m j n l : ℤ} (hjm : j ≤ m) (hnj : n ≤ j - 1)
    (hlm : l ≤ m) (omega : Cutoff.CutoffSample d)
    {v : Fin d → ℤ} (hv : v ∈ Support.latticeAnnulusSet d n j (j - 1)) :
    (3 : ℝ) ^ (-(M.gamma * (n : ℝ))) *
        Cutoff.localCubeControl n
          (ShellField.translate (Support.triadicLatticePoint n v) (omega.1 l))
      ≤ (3 : ℝ) ^ (M.gamma * ((m - n : ℤ) : ℝ)) * shellBlockLatticeReal M m omega l := by
  have hg0 : (0 : ℝ) ≤ M.gamma := M.shellPrefix.gamma_pos.le
  have hnm : n ≤ m := by omega
  have hvm : v ∈ Support.latticeCubeSet d n m :=
    openCubeSet_originCube_subset hjm hv.1
  have hL0 : 0 ≤ shellW2InfLatticeMaxOf m l (omega.1 l) :=
    shellW2InfLatticeMaxOf_nonneg m l (omega.1 l)
  have hgauge :=
    localCubeControl_translate_le_shellW2InfLatticeMaxOf hnm hlm hvm (omega.1 l)
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (-(M.gamma * (n : ℝ))) := by positivity
  have hstep := mul_le_mul_of_nonneg_left hgauge hpos.le
  have hzpow : ((3 : ℝ) ^ (2 * l) : ℝ) = (3 : ℝ) ^ (2 * (l : ℝ)) := by
    rw [show 2 * ((l : ℤ) : ℝ) = (((2 * l : ℤ)) : ℝ) from by push_cast; ring,
      Real.rpow_intCast]
  have hweight := three_rpow_value_weight_le (gam := M.gamma) (nn := (n : ℝ))
    (ll := (l : ℝ)) (mm := (m : ℝ)) hg0 (by exact_mod_cast hlm)
  have hcast : (M.gamma * ((m : ℝ) - (n : ℝ))) = M.gamma * ((m - n : ℤ) : ℝ) := by
    push_cast
    ring
  rw [hcast] at hweight
  rw [hzpow] at hstep
  have hfinal : (3 : ℝ) ^ (-(M.gamma * (n : ℝ))) *
      ((3 : ℝ) ^ (2 * (l : ℝ)) * shellW2InfLatticeMaxOf m l (omega.1 l))
      ≤ ((3 : ℝ) ^ (M.gamma * ((m - n : ℤ) : ℝ)) *
          (3 : ℝ) ^ ((2 - M.gamma) * (l : ℝ)))
        * shellW2InfLatticeMaxOf m l (omega.1 l) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hweight hL0
  have hdef : shellBlockLatticeReal M m omega l
      = (3 : ℝ) ^ ((2 - M.gamma) * (l : ℝ)) * shellW2InfLatticeMaxOf m l (omega.1 l) :=
    rfl
  refine le_trans hstep (le_trans hfinal (le_of_eq ?_))
  rw [hdef]
  ring

/-- **The `L^2` content of the clause-(i) third term**, in the conservative
`L^infinity` reading.

`e.mathcalE.annular.decomp.pre.zero`'s third term carries the
*volume-normalized* `L^2` norm of `k_m - k_{n-2}` on `z + cu_n`; the family
below uses the `L^infinity` norm of the same increment on the same cube, which
dominates it on a normalized cube.  The reading is therefore conservative: any
producer of the per-cube ugly estimate at the honest `L^2` norm feeds this
family unchanged.  It is the `L2f` family `clauseOne_bound` consumes. -/
def annularL2Block (M : ABKModel d) (m : ℤ) (omega : Cutoff.CutoffSample d)
    (j n : ℤ) : ℝ :=
  ((3 : ℝ) ^ (-(M.gamma * (n : ℝ))) *
    Proportion.fmax (Proportion.latticeAnnulusFinset d n j (j - 1))
      fun v => Cutoff.localCubeControl n
        (ShellField.translate (Support.triadicLatticePoint n v)
          (Provider.Stream.shellIncrement omega.1 (n - 2) m))) ^ 2

theorem annularL2Block_nonneg (M : ABKModel d) (m : ℤ)
    (omega : Cutoff.CutoffSample d) (j n : ℤ) :
    0 ≤ annularL2Block M m omega j n :=
  sq_nonneg _

/-- The value-leg analogue of `three_rpow_mul_fmax_le_sum`. -/
theorem three_rpow_mul_fmax_le_sum_value (M : ABKModel d) {m j n : ℤ} (hjm : j ≤ m)
    (hnj : n ≤ j - 1) (omega : Cutoff.CutoffSample d) :
    (3 : ℝ) ^ (-(M.gamma * (n : ℝ))) *
        Proportion.fmax (Proportion.latticeAnnulusFinset d n j (j - 1))
          (fun v => Cutoff.localCubeControl n
            (ShellField.translate (Support.triadicLatticePoint n v)
              (Provider.Stream.shellIncrement omega.1 (n - 2) m)))
      ≤ (3 : ℝ) ^ (M.gamma * ((m - n : ℤ) : ℝ))
        * ∑ l ∈ Finset.Ioc (n - 2) m, shellBlockLatticeReal M m omega l := by
  have hpos : (0 : ℝ) < (3 : ℝ) ^ (-(M.gamma * (n : ℝ))) := by positivity
  have hbdd : Proportion.fmax (Proportion.latticeAnnulusFinset d n j (j - 1))
      (fun v => Cutoff.localCubeControl n
        (ShellField.translate (Support.triadicLatticePoint n v)
          (Provider.Stream.shellIncrement omega.1 (n - 2) m)))
      ≤ ((3 : ℝ) ^ (-(M.gamma * (n : ℝ))))⁻¹ *
        ((3 : ℝ) ^ (M.gamma * ((m - n : ℤ) : ℝ))
          * ∑ l ∈ Finset.Ioc (n - 2) m, shellBlockLatticeReal M m omega l) := by
    refine Proportion.fmax_le (mul_nonneg (inv_nonneg.2 hpos.le)
      (mul_nonneg (Real.rpow_nonneg (by norm_num) _)
        (Finset.sum_nonneg fun l _ => shellBlockLatticeReal_nonneg M m omega l))) ?_
    intro v hv
    have hvset : v ∈ Support.latticeAnnulusSet d n j (j - 1) :=
      (Proportion.mem_latticeAnnulusFinset_iff (by omega)).mp hv
    have htrans : ShellField.translate (Support.triadicLatticePoint n v)
        (Provider.Stream.shellIncrement omega.1 (n - 2) m)
        = ShellField.sum (Finset.Ioc (n - 2) m)
          fun l => ShellField.translate (Support.triadicLatticePoint n v) (omega.1 l) :=
      ShellField.translate_sum _ _ _
    have htri : Cutoff.localCubeControl n
        (ShellField.translate (Support.triadicLatticePoint n v)
          (Provider.Stream.shellIncrement omega.1 (n - 2) m))
        ≤ ∑ l ∈ Finset.Ioc (n - 2) m,
            Cutoff.localCubeControl n
              (ShellField.translate (Support.triadicLatticePoint n v) (omega.1 l)) := by
      rw [htrans]
      exact localCubeControl_sum_le n (Finset.Ioc (n - 2) m) _
    have hterm : ∀ l ∈ Finset.Ioc (n - 2) m,
        (3 : ℝ) ^ (-(M.gamma * (n : ℝ))) *
            Cutoff.localCubeControl n
              (ShellField.translate (Support.triadicLatticePoint n v) (omega.1 l))
          ≤ (3 : ℝ) ^ (M.gamma * ((m - n : ℤ) : ℝ))
            * shellBlockLatticeReal M m omega l := by
      intro l hl
      rw [Finset.mem_Ioc] at hl
      exact three_rpow_mul_localCubeControl_translate_le_shellBlockLatticeReal M
        hjm hnj hl.2 omega hvset
    have hsum : (3 : ℝ) ^ (-(M.gamma * (n : ℝ))) *
        ∑ l ∈ Finset.Ioc (n - 2) m,
          Cutoff.localCubeControl n
            (ShellField.translate (Support.triadicLatticePoint n v) (omega.1 l))
        ≤ (3 : ℝ) ^ (M.gamma * ((m - n : ℤ) : ℝ))
          * ∑ l ∈ Finset.Ioc (n - 2) m, shellBlockLatticeReal M m omega l := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_le_sum hterm
    have hleft := mul_le_mul_of_nonneg_left htri hpos.le
    rw [le_inv_mul_iff₀ hpos]
    exact le_trans hleft hsum
  have hmul := mul_le_mul_of_nonneg_left hbdd hpos.le
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hpos), one_mul] at hmul
  exact hmul

/-- **The `hcsL2` slot of `ClauseOne.clauseOne_bound`, at `Kl2 = 1`.**

The `L^2` comparison of Step 3, discharged at the conservative `L^infinity`
content `annularL2Block` and at the A5b-pinned shell family
`shellBlockLatticeReal`.  No constant is lost: the `3^{2 gamma (m-n)}` factor
of the printed shape is exactly the square of the per-shell weight `3^{gamma
(m-n)}`, and the annulus count `(m-n)+2` is exactly the length of the layer
range `(n-2, m]`. -/
theorem annularL2Block_le (M : ABKModel d) (m : ℤ)
    (omega : Cutoff.CutoffSample d) (j n : ℤ) (hjm : j ≤ m) (hnj : n ≤ j - 1) :
    annularL2Block M m omega j n
      ≤ 1 * (((m - n : ℤ) : ℝ) + 2)
        * (3 : ℝ) ^ (2 * M.gamma * ((m - n : ℤ) : ℝ))
        * ∑ v ∈ Finset.range ((m - n).toNat + 2),
            shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2 := by
  have hnm : n ≤ m := by omega
  have hbase := three_rpow_mul_fmax_le_sum_value M hjm hnj omega
  have hfm0 : 0 ≤ (3 : ℝ) ^ (-(M.gamma * (n : ℝ))) *
      Proportion.fmax (Proportion.latticeAnnulusFinset d n j (j - 1))
        (fun v => Cutoff.localCubeControl n
          (ShellField.translate (Support.triadicLatticePoint n v)
            (Provider.Stream.shellIncrement omega.1 (n - 2) m))) := by
    have h1 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(M.gamma * (n : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    exact mul_nonneg h1 (Proportion.fmax_nonneg _ _)
  have hsq : annularL2Block M m omega j n
      ≤ ((3 : ℝ) ^ (M.gamma * ((m - n : ℤ) : ℝ))
          * ∑ l ∈ Finset.Ioc (n - 2) m, shellBlockLatticeReal M m omega l) ^ 2 := by
    rw [annularL2Block]
    exact pow_le_pow_left₀ hfm0 hbase 2
  rw [sum_Ioc_eq_sum_range hnm] at hsq
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := Finset.range ((m - n).toNat + 2))
    (f := fun u : ℕ => shellBlockLatticeReal M m omega (m - (u : ℤ)))
  have hr : (((m - n).toNat : ℕ) : ℝ) = (m : ℝ) - (n : ℝ) := by
    have hz : ((m - n).toNat : ℤ) = m - n := Int.toNat_of_nonneg (by omega)
    have hcast := congrArg (fun z : ℤ => (z : ℝ)) hz
    push_cast at hcast
    exact hcast
  have hcard : ((Finset.range ((m - n).toNat + 2)).card : ℝ) = ((m - n : ℤ) : ℝ) + 2 := by
    rw [Finset.card_range]
    push_cast [hr]
    ring
  rw [hcard] at hcs
  have hwsq : ((3 : ℝ) ^ (M.gamma * ((m - n : ℤ) : ℝ))) ^ 2
      = (3 : ℝ) ^ (2 * M.gamma * ((m - n : ℤ) : ℝ)) := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ (M.gamma * ((m - n : ℤ) : ℝ))) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    push_cast
    ring
  have hexpand : ((3 : ℝ) ^ (M.gamma * ((m - n : ℤ) : ℝ))
        * ∑ u ∈ Finset.range ((m - n).toNat + 2),
            shellBlockLatticeReal M m omega (m - (u : ℤ))) ^ 2
      = (3 : ℝ) ^ (2 * M.gamma * ((m - n : ℤ) : ℝ))
        * (∑ u ∈ Finset.range ((m - n).toNat + 2),
            shellBlockLatticeReal M m omega (m - (u : ℤ))) ^ 2 := by
    rw [mul_pow, hwsq]
  rw [hexpand] at hsq
  have hwpos : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * M.gamma * ((m - n : ℤ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hmul := mul_le_mul_of_nonneg_left hcs hwpos
  have hassoc : (3 : ℝ) ^ (2 * M.gamma * ((m - n : ℤ) : ℝ)) *
      ((((m - n : ℤ) : ℝ) + 2) *
        ∑ u ∈ Finset.range ((m - n).toNat + 2),
          shellBlockLatticeReal M m omega (m - (u : ℤ)) ^ 2)
      = 1 * (((m - n : ℤ) : ℝ) + 2)
        * (3 : ℝ) ^ (2 * M.gamma * ((m - n : ℤ) : ℝ))
        * ∑ v ∈ Finset.range ((m - n).toNat + 2),
            shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2 := by ring
  rw [hassoc] at hmul
  exact le_trans hsq hmul

end

end Algsuperdiff.Section4.Provider.Annular
