/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationOscillationEndpointSixteen

/-!
# GammaTenDepthOscillation

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `e.lower.bound.oscillations` at every depth below the recurrence mesh

ABK26, `e.lower.bound.oscillations`, `e.nablaw.oscillations`,
`e.recurrence.params`.

## What this module adds

`LocalizationOscillationEndpointSixteen` reads the interior-mesh endpoint of
`e.lower.bound.oscillations` at the **one** mesh scale
`nmesh = recurrenceMesoScale a cgamma m h` of `e.recurrence.params`.  The Besov
tower of Step 2 needs it at **every** scale `nmesh - i`, `i : ℕ`, with a
geometric gain in `i`; that is what
`Closure.GammaTenEnvelopeInputGrid.exists_besovEnvelope_of_grid_depth_oscillation`
consumes as its per-depth input `D i`.

The route is a re-instantiation, at no new analytic cost: the free-buffer
display
`LocalizationOscillationDisplay.exists_freshShell*_gradient_oscillation_lower_bound_display`
is run at inner scale `nmesh - i` and buffer `N_i = Ngap + i`, so that the outer
scale `n + N = m - h` --- the corrector's own fresh-shell scale --- does not
move.  Consequently

* the coarse-energy envelope
  `LocalizationEnvelopeWire.exists_freshShell_gridFourthMoment_mesoWindowEnergy_le_wired`
  applies at `(n, N) = (nmesh - i, Ngap + i)` with its **buffer-independent**
  right-hand side `3^d freshShellFourthEnergyConst Chead (cgamma^{100})`, so the
  amplitude `W` is one constant for all depths;
* the cell integrability
`exists_gamma0_integrable_freshShell*_meshEnergyCell_rpow_four`
  applies verbatim, its containment hypothesis being supplied on the finer grid
  by `openCubeAtScale_subset_openCubeSet_of_mem_interiorMesoCubeGrid`;
* the two `cgamma`-facing gauges `S * P <= shellNormalizationConst` and
  `Ctot cgamma^{15} <= 1` are untouched, since `n + N` is unchanged.

## The one new piece of arithmetic, and the polynomial factor it leaves

Only the display's first factor moves with the depth: `3^{-N}` becomes
`3^{-(Ngap + i)} = 3^{-Ngap} 3^{-i}`, and the middle term's linear factor `N`
becomes `Ngap + i`.  The proved collapse
`LocalizationOscillationEndpointSixteen.three_term_budget_le_sixteen` absorbs
the linear factor through `Ngap cgamma <= 96`; at depth `i` the same step needs
`(Ngap + i) 3^{-(Ngap+i)}`, and the sharp elementary bound is `Ngap + i <= Ngap
(1 + i)`, i.e.

```
  (Ngap + i) 3^{-(Ngap+i)}  <=  96 cgamma^{31} * ((1 + i) 3^{-i}) .
```

The conclusion therefore carries the decay factor `(1 + i) 3^{-i}`, **not** the
bare `3^{-i}`: the linear factor is genuinely there and is not silently dropped.
It is harmless downstream --- at the fourth power the depth input is
`cgamma^{64} (1+i)^4 3^{-4i} <= 25 cgamma^{64} 36^{-i}`, and `36^{-1}` is the
exact ratio gate of
`Closure.GammaTenEnvelopeInputGrid.sum_two_pow_mul_rpow_pow_four_geometric_le`
at the closure's exponent `gammaTenBesovExponent = 1/2` --- but it is recorded
in the statement.

## What is proved

* `three_term_budget_le_sixteen_decay` --- the three-term collapse of
  `LocalizationOscillationEndpointSixteen.three_term_budget_le_sixteen`
  carrying an arbitrary nonnegative decay factor `delta` through both the first
  factor `G` and the product `Nr * G`.
* `rpow_three_neg_add_split`, `depth_natCast_add_le`, `depth_geometric_le`,
  `depth_linear_geometric_le` --- the depth arithmetic, isolated so that the two
  endpoints below stay inside the default heartbeat budget.
* `exists_gamma0_freshShellDirichlet_meshOscillationDepth_le_gamma_pow_sixteen`
  and its Neumann mirror --- **the depth-indexed interior endpoints**:
  statement, binders and threshold are those of the proved
  `..._meshOscillation_le_gamma_pow_sixteen` pair, with the mesh scale relaxed
  to `nmesh - i` and the conclusion multiplied by `(1 + i) 3^{-i}`.  At `i = 0`
  they are the proved statements.

## Binders

Verbatim those of `LocalizationOscillationEndpointSixteen`: `hd`, the model gate
`M.gamma <= gamma0`, the induction state, the four source gates `0 < h`,
`m - h <= m0`, `h <= 6 cstar gamma^{-1}`, `10^10 gamma^{-1} <= K - m`, the two
direction bounds, the base point `z0`, and the corrector family with the weak
formulation of `e.def.w`.  The depth `i : ℕ` is universally quantified after the
corrector, so **one** threshold serves every depth.  No sample-space binder and
no smallness gate beyond the produced threshold occurs.

## Declared divergence: the carrier is the interior mesh

The statements are on `interiorMesoCubeGrid d K (nmesh - i) (m - h - 1)`, the
carrier.  The transfer to the **full** mesh performed by
`LocalizationOscillationFullMesh` for the single scale `nmesh` does **not**
survive the depth index: the remainder of
`LocalizationFluctuationGammaFold.gridFourthMoment_mesoCubeGrid_le_interior_add_of_eighthMoment`
is `sqrt (d 3^g / 3^p) sqrt E` with `K = n + p` and `outer + 1 = n + g`, i.e.
`3^{g-p} = 3^{(outer+1) - K} = 3^{(m-h) - K}`, which does not move with the
mesh scale `n`.  The boundary strip is the same fixed fraction at every depth,
so no `3^{-i}` is available for it.  This is recorded, not closed, here.

## Scope

There is no `sorry`, no `admit`, no custom axiom and no `set_option
maxHeartbeats`.

## References

* ABK26, `e.lower.bound.oscillations`, `e.nablaw.oscillations`,
  `e.recurrence.params`, `e.def.w`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport HCPolySupport.Book.Ch02 MeasureTheory
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The three-term collapse, with a depth decay factor -/

theorem three_term_budget_le_sixteen_decay
    {C W Csig sqd Nr G P S Eb gamma Ctot Kn delta : ℝ}
    (hC : 0 ≤ C) (hW : 0 ≤ W) (hCsig : 0 ≤ Csig) (hsqd : 0 ≤ sqd)
    (hNr0 : 0 ≤ Nr) (hG0 : 0 ≤ G) (hEb0 : 0 ≤ Eb)
    (hdelta0 : 0 ≤ delta) (hgamma0 : 0 < gamma)
    (hGle : G ≤ gamma ^ (31 : ℕ) * delta)
    (hNrG : Nr * G ≤ Kn * (gamma ^ (31 : ℕ) * delta))
    (hSP : S * P ≤ Csig) (hEb : Eb ≤ 1)
    (hCtot : C * W + Kn * (C * sqd * Csig) + C * Csig ≤ Ctot)
    (hfinal : Ctot * gamma ^ (15 : ℕ) ≤ 1) :
    C * (G * W) + C * (Nr * (S * sqd * Eb)) * (G * P) + C * S * (G * P) ≤
      gamma ^ (16 : ℕ) * delta := by
  have hX0 : (0 : ℝ) ≤ gamma ^ (31 : ℕ) * delta :=
    mul_nonneg (pow_nonneg hgamma0.le _) hdelta0
  have h1 : C * (G * W) ≤ C * W * (gamma ^ (31 : ℕ) * delta) := by
    calc C * (G * W) = C * W * G := by ring
      _ ≤ C * W * (gamma ^ (31 : ℕ) * delta) :=
          mul_le_mul_of_nonneg_left hGle (mul_nonneg hC hW)
  have h3 : C * S * (G * P) ≤ C * Csig * (gamma ^ (31 : ℕ) * delta) := by
    calc C * S * (G * P) = C * G * (S * P) := by ring
      _ ≤ C * G * Csig := mul_le_mul_of_nonneg_left hSP (mul_nonneg hC hG0)
      _ ≤ C * (gamma ^ (31 : ℕ) * delta) * Csig :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hGle hC) hCsig
      _ = C * Csig * (gamma ^ (31 : ℕ) * delta) := by ring
  have h2 : C * (Nr * (S * sqd * Eb)) * (G * P) ≤
      Kn * (C * sqd * Csig) * (gamma ^ (31 : ℕ) * delta) := by
    have hNrG0 : (0 : ℝ) ≤ Nr * G := mul_nonneg hNr0 hG0
    have hA0 : (0 : ℝ) ≤ C * sqd * Eb := mul_nonneg (mul_nonneg hC hsqd) hEb0
    have hstep2 : C * sqd * Eb ≤ C * sqd := by
      have hCs : (0 : ℝ) ≤ C * sqd := mul_nonneg hC hsqd
      exact mul_le_of_le_one_right hCs hEb
    calc C * (Nr * (S * sqd * Eb)) * (G * P)
        = (C * sqd * Eb) * (Nr * G) * (S * P) := by ring
      _ ≤ (C * sqd * Eb) * (Nr * G) * Csig :=
          mul_le_mul_of_nonneg_left hSP (mul_nonneg hA0 hNrG0)
      _ ≤ (C * sqd) * (Nr * G) * Csig :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hstep2 hNrG0) hCsig
      _ ≤ (C * sqd) * (Kn * (gamma ^ (31 : ℕ) * delta)) * Csig :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hNrG (mul_nonneg hC hsqd)) hCsig
      _ = Kn * (C * sqd * Csig) * (gamma ^ (31 : ℕ) * delta) := by ring
  have hsum : C * (G * W) + C * (Nr * (S * sqd * Eb)) * (G * P) + C * S * (G * P) ≤
      (C * W + Kn * (C * sqd * Csig) + C * Csig) * (gamma ^ (31 : ℕ) * delta) := by
    have hadd := add_le_add (add_le_add h1 h2) h3
    calc C * (G * W) + C * (Nr * (S * sqd * Eb)) * (G * P) + C * S * (G * P)
        ≤ C * W * (gamma ^ (31 : ℕ) * delta) +
            Kn * (C * sqd * Csig) * (gamma ^ (31 : ℕ) * delta) +
            C * Csig * (gamma ^ (31 : ℕ) * delta) := hadd
      _ = (C * W + Kn * (C * sqd * Csig) + C * Csig) *
            (gamma ^ (31 : ℕ) * delta) := by ring
  have hmid : (C * W + Kn * (C * sqd * Csig) + C * Csig) * (gamma ^ (31 : ℕ) * delta) ≤
      Ctot * (gamma ^ (31 : ℕ) * delta) := mul_le_mul_of_nonneg_right hCtot hX0
  have hlast : Ctot * (gamma ^ (31 : ℕ) * delta) ≤ gamma ^ (16 : ℕ) * delta := by
    have hg16 : (0 : ℝ) ≤ gamma ^ (16 : ℕ) * delta :=
      mul_nonneg (pow_nonneg hgamma0.le _) hdelta0
    calc Ctot * (gamma ^ (31 : ℕ) * delta)
        = (Ctot * gamma ^ (15 : ℕ)) * (gamma ^ (16 : ℕ) * delta) := by ring
      _ ≤ 1 * (gamma ^ (16 : ℕ) * delta) := mul_le_mul_of_nonneg_right hfinal hg16
      _ = gamma ^ (16 : ℕ) * delta := one_mul _
  linarith

/-! ## The two depth arithmetic facts -/

theorem rpow_three_neg_add_split (Ngap i : ℕ) :
    (3 : ℝ) ^ (-(((Ngap + i : ℕ) : ℝ))) =
      (3 : ℝ) ^ (-((Ngap : ℕ) : ℝ)) * (3 : ℝ) ^ (-(i : ℝ)) := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  push_cast
  ring

theorem depth_natCast_add_le (Ngap i : ℕ) (hN : 1 ≤ Ngap) :
    ((Ngap + i : ℕ) : ℝ) ≤ ((Ngap : ℕ) : ℝ) * (1 + (i : ℝ)) := by
  have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  have hN1 : (1 : ℝ) ≤ ((Ngap : ℕ) : ℝ) := by exact_mod_cast hN
  have hmul : (i : ℝ) ≤ ((Ngap : ℕ) : ℝ) * (i : ℝ) := le_mul_of_one_le_left hi0 hN1
  have hexp : ((Ngap : ℕ) : ℝ) * (1 + (i : ℝ)) =
      ((Ngap : ℕ) : ℝ) + ((Ngap : ℕ) : ℝ) * (i : ℝ) := by ring
  rw [hexp]
  push_cast
  linarith only [hmul]

theorem depth_geometric_le {gamma : ℝ} (hgamma0 : 0 < gamma) (hgamma1 : gamma ≤ 1)
    (Ngap i : ℕ) (hGle : (3 : ℝ) ^ (-((Ngap : ℕ) : ℝ)) ≤ gamma ^ (32 : ℕ)) :
    (3 : ℝ) ^ (-(((Ngap + i : ℕ) : ℝ))) ≤
      gamma ^ (31 : ℕ) * ((1 + (i : ℝ)) * (3 : ℝ) ^ (-(i : ℝ))) := by
  have hthree0 : (0 : ℝ) < (3 : ℝ) ^ (-(i : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  have hg3231 : gamma ^ (32 : ℕ) ≤ gamma ^ (31 : ℕ) :=
    pow_le_pow_of_le_one hgamma0.le hgamma1 (by norm_num)
  have hone : (1 : ℝ) ≤ 1 + (i : ℝ) := by linarith only [hi0]
  have hg31 : (0 : ℝ) ≤ gamma ^ (31 : ℕ) := pow_nonneg hgamma0.le _
  rw [rpow_three_neg_add_split]
  calc (3 : ℝ) ^ (-((Ngap : ℕ) : ℝ)) * (3 : ℝ) ^ (-(i : ℝ))
      ≤ gamma ^ (31 : ℕ) * (3 : ℝ) ^ (-(i : ℝ)) :=
        mul_le_mul_of_nonneg_right (le_trans hGle hg3231) hthree0.le
    _ = gamma ^ (31 : ℕ) * (3 : ℝ) ^ (-(i : ℝ)) * 1 := by ring
    _ ≤ gamma ^ (31 : ℕ) * (3 : ℝ) ^ (-(i : ℝ)) * (1 + (i : ℝ)) :=
        mul_le_mul_of_nonneg_left hone (mul_nonneg hg31 hthree0.le)
    _ = gamma ^ (31 : ℕ) * ((1 + (i : ℝ)) * (3 : ℝ) ^ (-(i : ℝ))) := by ring

theorem depth_linear_geometric_le {gamma : ℝ} (hgamma0 : 0 < gamma) (Ngap i : ℕ)
    (hN : 1 ≤ Ngap) (hGle : (3 : ℝ) ^ (-((Ngap : ℕ) : ℝ)) ≤ gamma ^ (32 : ℕ))
    (hNrle : ((Ngap : ℕ) : ℝ) * gamma ≤ 96) :
    ((Ngap + i : ℕ) : ℝ) * (3 : ℝ) ^ (-(((Ngap + i : ℕ) : ℝ))) ≤
      96 * (gamma ^ (31 : ℕ) * ((1 + (i : ℝ)) * (3 : ℝ) ^ (-(i : ℝ)))) := by
  have hthree0 : (0 : ℝ) < (3 : ℝ) ^ (-(i : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hthreeN : (0 : ℝ) < (3 : ℝ) ^ (-((Ngap : ℕ) : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hi0 : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg i
  have hone : (0 : ℝ) ≤ 1 + (i : ℝ) := by linarith only [hi0]
  have hNn : (0 : ℝ) ≤ ((Ngap : ℕ) : ℝ) := Nat.cast_nonneg Ngap
  have hg31 : (0 : ℝ) ≤ gamma ^ (31 : ℕ) := pow_nonneg hgamma0.le _
  rw [rpow_three_neg_add_split]
  calc ((Ngap + i : ℕ) : ℝ) *
        ((3 : ℝ) ^ (-((Ngap : ℕ) : ℝ)) * (3 : ℝ) ^ (-(i : ℝ)))
      ≤ (((Ngap : ℕ) : ℝ) * (1 + (i : ℝ))) *
          ((3 : ℝ) ^ (-((Ngap : ℕ) : ℝ)) * (3 : ℝ) ^ (-(i : ℝ))) :=
        mul_le_mul_of_nonneg_right (depth_natCast_add_le Ngap i hN)
          (mul_nonneg hthreeN.le hthree0.le)
    _ ≤ (((Ngap : ℕ) : ℝ) * (1 + (i : ℝ))) *
          (gamma ^ (32 : ℕ) * (3 : ℝ) ^ (-(i : ℝ))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hGle hthree0.le) (mul_nonneg hNn hone)
    _ = (((Ngap : ℕ) : ℝ) * gamma) *
          (gamma ^ (31 : ℕ) * ((1 + (i : ℝ)) * (3 : ℝ) ^ (-(i : ℝ)))) := by ring
    _ ≤ 96 * (gamma ^ (31 : ℕ) * ((1 + (i : ℝ)) * (3 : ℝ) ^ (-(i : ℝ)))) :=
        mul_le_mul_of_nonneg_right hNrle
          (mul_nonneg hg31 (mul_nonneg hone hthree0.le))

private theorem gammaTenDepthOscillation_comparisonBounds1 :
    ∀ (d : ℕ) (Ctot : ℝ) (_ : (0 : ℝ) ≤ Ctot) (M : ABKModel d) (m0 : ℤ) (Eind : { E : ℝ // (1 : ℝ)
      ≤ E })
      (_ : Frozen.Section3.inductionState M m0 Eind) (m K : ℤ) (h : ℕ) (_ : (0 : ℕ) < h) (_ : m -
        (↑h : ℤ) ≤ m0)
      (_ : (↑h : ℝ) ≤ (6 : ℝ) * Disorder.cstar M * M.gamma⁻¹)
      (_ : (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (↑K : ℝ) - (↑m : ℝ)) (_ : M.gamma ≤ (1 / 4 : ℝ))
      (_ : M.gamma ≤ (3 : ℝ) ^ (-((↑d : ℝ) + (3 : ℝ)))) (_ : M.gamma ≤ (1 : ℝ) / ((1 : ℝ) + Ctot))
      (_ : (0 : ℝ) < M.gamma) (_ : M.gamma ≤ (1 : ℝ)) (nbuf : ℤ)
      (_ : nbuf = recurrenceMesoScale recurrenceGapMultiplier M.gamma m (↑h : ℤ)) (Ngap : ℕ)
      (_ : Ngap = recurrenceGap recurrenceGapMultiplier M.gamma) (_ : nbuf + (↑Ngap : ℤ) = m - (↑h
        : ℤ))
      (_ : (↑nbuf : ℝ) + (↑Ngap : ℝ) = (↑(m - (↑h : ℤ)) : ℝ)),
      (1 : ℝ) ≤ (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ∧
        d + (3 : ℕ) ≤ Ngap ∧
          (3 : ℝ) ^ (-(↑Ngap : ℝ)) ≤ M.gamma ^ (32 : ℕ) ∧
            (↑Ngap : ℝ) * M.gamma ≤ (96 : ℝ) ∧
              (0 : ℝ) ≤ (↑(Annealed.sigmaBar M (m - (↑h : ℤ))) : ℝ)⁻¹ ∧
                (↑(Annealed.sigmaBar M (m - (↑h : ℤ))) : ℝ)⁻¹ * (3 : ℝ) ^ (M.gamma * ((↑nbuf : ℝ)
                  + (↑Ngap : ℝ))) ≤
                    shellNormalizationConst ∧
                  Ctot * M.gamma ^ (15 : ℕ) ≤ (1 : ℝ) := by
  intro d Ctot hCtot0 M _ _ hstate m K h hhpos hm0 hcstar _ _ hdimgate hCgate hgamma0 hgamma1 nbuf
    _ Ngap hNgap _ hsumR
  have hKone : (1 : ℝ) ≤ (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ := by
    have hinv : (1 : ℝ) ≤ M.gamma⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hgamma0]
      linarith
    have h10 : (1 : ℝ) ≤ (10 : ℝ) ^ (10 : ℕ) := by norm_num
    exact one_le_mul_of_one_le_of_one_le h10 hinv
  have hmK1 : m ≤ K - 1 := by
    have hle : (m : ℝ) + 1 ≤ (K : ℝ) := by linarith
    have : m + 1 ≤ K := by exact_mod_cast hle
    omega
  have hnNle : nbuf + (Ngap : ℤ) ≤ K - 1 := by omega
  have hdimN : d + 3 ≤ Ngap := by
    rw [hNgap]
    refine dim_add_three_le_recurrenceGap (a := recurrenceGapMultiplier) d hgamma0
      (by norm_num [recurrenceGapMultiplier]) ?_
    have hpow : (0 : ℝ) < (3 : ℝ) ^ ((d : ℝ) + 3) := Real.rpow_pos_of_pos (by norm_num) _
    have h2 : M.gamma ≤ ((3 : ℝ) ^ ((d : ℝ) + 3))⁻¹ := by
      rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
      exact hdimgate
    exact (le_inv_comm₀ hpow hgamma0).mpr h2
  have hGle : (3 : ℝ) ^ (-((Ngap : ℕ) : ℝ)) ≤ M.gamma ^ (32 : ℕ) := by
    have hbase := rpow_three_neg_recurrenceGap_le_gamma_pow recurrenceGapMultiplier
      (gamma := M.gamma) hgamma0 hgamma1
    rw [hNgap]
    simpa [recurrenceGapMultiplier] using hbase
  have hNrle : ((Ngap : ℕ) : ℝ) * M.gamma ≤ 96 := by
    have hbase := recurrenceGap_mul_gamma_le recurrenceGapMultiplier
      (gamma := M.gamma) hgamma0 hgamma1
    rw [hNgap]
    calc ((recurrenceGap recurrenceGapMultiplier M.gamma : ℕ) : ℝ) * M.gamma
        ≤ 3 * ((recurrenceGapMultiplier : ℕ) : ℝ) := hbase
      _ = 96 := by norm_num [recurrenceGapMultiplier]
  have hsigma0 : (0 : ℝ) ≤ ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ :=
    (inv_pos.2 (Annealed.sigmaBar_characterization M (m - (h : ℤ))).1).le
  have hSPle : ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ *
      (3 : ℝ) ^ (M.gamma * (((nbuf : ℤ) : ℝ) + ((Ngap : ℕ) : ℝ))) ≤
        shellNormalizationConst := by
    rw [hsumR]
    exact sigmaBarInv_mul_rpow_gamma_shell_le M hstate hhpos hm0 hcstar
  have hfinal : Ctot * M.gamma ^ (15 : ℕ) ≤ 1 := by
    have h15 : M.gamma ^ (15 : ℕ) ≤ M.gamma := by
      calc M.gamma ^ (15 : ℕ) ≤ M.gamma ^ (1 : ℕ) :=
            pow_le_pow_of_le_one hgamma0.le hgamma1 (by norm_num)
        _ = M.gamma := pow_one _
    have hCg : Ctot * M.gamma ^ (15 : ℕ) ≤ Ctot * M.gamma :=
      mul_le_mul_of_nonneg_left h15 hCtot0
    have hCg2 : Ctot * M.gamma ≤ Ctot * (1 / (1 + Ctot)) :=
      mul_le_mul_of_nonneg_left hCgate hCtot0
    have hden : (0 : ℝ) < 1 + Ctot := by linarith
    have hlast : Ctot * (1 / (1 + Ctot)) ≤ 1 := by
      rw [mul_one_div, div_le_one hden]
      linarith
    linarith
  exact ⟨hKone, hdimN, hGle, hNrle, hsigma0, hSPle, hfinal⟩

theorem exists_gamma0_freshShellDirichlet_meshOscillationDepth_le_gamma_pow_sixteen
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧ gamma0 ≤ 1 / 4 ∧
      ∀ (M : ABKModel d), M.gamma ≤ gamma0 →
        ∀ (m0 : ℤ) (Eind : {E : ℝ // 1 ≤ E}),
          Algsuperdiff.Frozen.Section3.inductionState M m0 Eind →
          ∀ (m K : ℤ) (h : ℕ), 0 < h → m - (h : ℤ) ≤ m0 →
            (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
            (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (K : ℝ) - (m : ℝ) →
            ∀ e e' : Vec d, Book.Ch02.vecNorm e ≤ 1 →
              Book.Ch02.vecNorm e' ≤ 1 →
              ∀ z₀ : Vec d,
                ∀ wD : Cutoff.ShellSeq d → H10Function (openCubeSet (originCube d K)),
                  (∀ omega, IsZeroTraceDirichletRhsWeakSolution
                      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                      (openCubeSet (originCube d K)) (wD omega)
                      (fun x => -Corrector.streamForcing
                        ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ omega
                        (m - (h : ℤ)) m e x)) →
                  ∀ i : ℕ,
                    gridFourthMomentRoot M.P.toMeasure
                        (interiorMesoCubeGrid d K
                          (recurrenceMesoScale recurrenceGapMultiplier M.gamma m (h : ℤ) -
                            (i : ℤ))
                          (m - (h : ℤ) - 1))
                        (fun R omega => meshOscillationCell
                          (recurrenceMesoScale recurrenceGapMultiplier M.gamma m (h : ℤ) -
                            (i : ℤ))
                          (wD omega).toH1Function.grad R) +
                        ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ *
                          ((3 : ℝ) ^ ((recurrenceMesoScale recurrenceGapMultiplier M.gamma
                              m (h : ℤ) - (i : ℤ) : ℤ) : ℝ) *
                            (∫ omega : Cutoff.ShellSeq d,
                              shellDerivNormSum (m - (h : ℤ)) m z₀ omega ^ (4 : ℝ)
                                ∂M.P.toMeasure) ^ ((4 : ℝ)⁻¹)) ≤
                      M.gamma ^ (16 : ℕ) * ((1 + (i : ℝ)) * (3 : ℝ) ^ (-(i : ℝ))) := by
  classical
  obtain ⟨Cdisp, hCdisp0, hdisp⟩ :=
    exists_freshShellDirichlet_gradient_oscillation_lower_bound_display
      (d := d) (lt_of_lt_of_le (by norm_num) hd)
  obtain ⟨Chead, -, genv, hgenv0, -, henv⟩ :=
    exists_freshShell_gridFourthMoment_mesoWindowEnergy_le_wired d hd
  obtain ⟨gcell, hgcell0, -, hcell⟩ :=
    exists_gamma0_integrable_freshShellDirichlet_meshEnergyCell_rpow_four d hd
  obtain ⟨W0, hW0⟩ : ∃ W0 : ℝ,
      W0 = ((3 : ℝ) ^ d * freshShellFourthEnergyConst Chead 1) ^ ((4 : ℝ)⁻¹) := ⟨_, rfl⟩
  have hbase0 : (0 : ℝ) ≤ (3 : ℝ) ^ d * freshShellFourthEnergyConst Chead 1 :=
    mul_nonneg (by positivity) (freshShellFourthEnergyConst_nonneg _ _)
  have hW00 : 0 ≤ W0 := by rw [hW0]; exact Real.rpow_nonneg hbase0 _
  obtain ⟨Ctot, hCtot⟩ : ∃ Ctot : ℝ,
      Ctot = Cdisp * W0 + 96 * (Cdisp * Real.sqrt (d : ℝ) * shellNormalizationConst)
        + Cdisp * shellNormalizationConst := ⟨_, rfl⟩
  have hCtot0 : 0 ≤ Ctot := by
    have hsq : (0 : ℝ) ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
    have hsn : (0 : ℝ) ≤ shellNormalizationConst := shellNormalizationConst_nonneg
    have hb1 : (0 : ℝ) ≤ Cdisp * W0 := mul_nonneg hCdisp0 hW00
    have hb2 : (0 : ℝ) ≤ 96 * (Cdisp * Real.sqrt (d : ℝ) * shellNormalizationConst) :=
      mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hCdisp0 hsq) hsn)
    have hb3 : (0 : ℝ) ≤ Cdisp * shellNormalizationConst := mul_nonneg hCdisp0 hsn
    rw [hCtot]
    linarith
  refine ⟨min gcell
      (min (1 / 4) (min genv (min ((3 : ℝ) ^ (-((d : ℝ) + 3))) (1 / (1 + Ctot))))),
    ?_, le_trans (min_le_right _ _) (min_le_left _ _), ?_⟩
  · refine lt_min hgcell0 (lt_min (by norm_num) (lt_min hgenv0 (lt_min ?_ ?_)))
    · exact Real.rpow_pos_of_pos (by norm_num) _
    · exact div_pos one_pos (by linarith)
  intro M hMgamma m0 Eind hstate m K h hhpos hm0 hcstar hK e e' he he' z₀ wD hsol
  have hgcellle : M.gamma ≤ gcell := le_trans hMgamma (min_le_left _ _)
  have hq : M.gamma ≤ 1 / 4 :=
    le_trans hMgamma (le_trans (min_le_right _ _) (min_le_left _ _))
  have hgenvle : M.gamma ≤ genv :=
    le_trans hMgamma
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hdimgate : M.gamma ≤ (3 : ℝ) ^ (-((d : ℝ) + 3)) :=
    le_trans hMgamma (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hCgate : M.gamma ≤ 1 / (1 + Ctot) :=
    le_trans hMgamma (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
  clear hMgamma
  have hgrad : ∀ omega : Cutoff.ShellSeq d,
      MemLp (wD omega).toH1Function.grad (8 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d K)) := fun omega =>
    memLp_eight_grad_freshShellDirichlet hd (originCube d K)
      ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ omega (m - (h : ℤ)) m e
      (wD omega) (hsol omega)
  have hmem : ∀ omega : Cutoff.ShellSeq d,
      MemLp (fun x => Book.Ch02.vecNorm ((wD omega).toH1Function.grad x)) 8
        (normalizedCubeMeasure (originCube d K)) := fun omega =>
    memLp_vecNorm_eight_of_memLp_eight _ (hgrad omega)
  have hcoord : ∀ (omega : Cutoff.ShellSeq d) (k : Fin d),
      IntegrableOn (fun x => ((wD omega).toH1Function.grad x k) ^ 2)
        (openCubeSet (originCube d K)) volume := fun omega k =>
    integrableOn_openCubeSet_coord_sq_of_memLp_eight _ (hgrad omega) k
  have hsq : ∀ omega : Cutoff.ShellSeq d,
      IntegrableOn (fun x => vecNormSq ((wD omega).toH1Function.grad x))
        (openCubeSet (originCube d K)) volume := fun omega =>
    integrableOn_openCubeSet_vecNormSq_of_memLp_eight _ (hgrad omega)
  have hfour : ∀ omega : Cutoff.ShellSeq d,
      IntegrableOn (fun x => vecNormSq ((wD omega).toH1Function.grad x) ^ 2)
        (openCubeSet (originCube d K)) volume := fun omega =>
    integrableOn_openCubeSet_vecNormSq_sq_of_memLp_eight _ (hgrad omega)
  clear hgrad
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hgamma1 : M.gamma ≤ 1 := le_trans hq (by norm_num)
  obtain ⟨nbuf, hnbuf⟩ : ∃ n : ℤ,
      n = recurrenceMesoScale recurrenceGapMultiplier M.gamma m (h : ℤ) := ⟨_, rfl⟩
  obtain ⟨Ngap, hNgap⟩ : ∃ N : ℕ,
      N = recurrenceGap recurrenceGapMultiplier M.gamma := ⟨_, rfl⟩
  have hsum : nbuf + (Ngap : ℤ) = m - (h : ℤ) := by
    rw [hnbuf, hNgap]
    exact recurrenceMesoScale_add_recurrenceGap _ _ _ _
  have hsumR : ((nbuf : ℤ) : ℝ) + ((Ngap : ℕ) : ℝ) = (((m - (h : ℤ) : ℤ)) : ℝ) := by
    rw [hnbuf, hNgap]
    exact recurrenceMesoScale_add_recurrenceGap_real _ _ _ _
  have hmK : m ≤ K := by
    have hpos : (0 : ℝ) < (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ := by positivity
    have hle : (m : ℝ) ≤ (K : ℝ) := by linarith
    exact_mod_cast hle
  obtain ⟨hKone, hdimN, hGle, hNrle, hsigma0, hSPle, hfinal⟩ :=
    (show ((1 : ℝ) ≤ (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹) ∧ (d + 3 ≤ Ngap) ∧ ((3 : ℝ) ^ (-((Ngap : ℕ)
      : ℝ)) ≤ M.gamma ^ (32 : ℕ)) ∧ (((Ngap : ℕ) : ℝ) * M.gamma ≤ 96) ∧ ((0 : ℝ) ≤
        ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹) ∧ (((Annealed.sigmaBar M (m - (h : ℤ)) :
          ℝ))⁻¹ *
      (3 : ℝ) ^ (M.gamma * (((nbuf : ℤ) : ℝ) + ((Ngap : ℕ) : ℝ))) ≤
        shellNormalizationConst) ∧ (Ctot * M.gamma ^ (15 : ℕ) ≤ 1) from
      @gammaTenDepthOscillation_comparisonBounds1 (d) (Ctot) (hCtot0) (M) (m0) (Eind) (hstate) (m)
        (K) (h) (hhpos) (hm0) (hcstar) (hK) (hq) (hdimgate) (hCgate) (hgamma0) (hgamma1) (nbuf)
          (hnbuf) (Ngap) (hNgap) (hsum) (hsumR))
  obtain ⟨Aenv, hAenv⟩ : ∃ A : ℝ,
      A = (3 : ℝ) ^ d * freshShellFourthEnergyConst Chead (M.gamma ^ (100 : ℕ)) := ⟨_, rfl⟩
  have hAenv0 : 0 ≤ Aenv := by
    rw [hAenv]
    exact mul_nonneg (by positivity) (freshShellFourthEnergyConst_nonneg _ _)
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = Aenv ^ ((4 : ℝ)⁻¹) := ⟨_, rfl⟩
  have hW0nn : 0 ≤ W := by rw [hW]; exact Real.rpow_nonneg hAenv0 _
  have hWpow : W ^ (4 : ℕ) = Aenv := by
    rw [hW, ← Real.rpow_natCast (Aenv ^ ((4 : ℝ)⁻¹)) 4, ← Real.rpow_mul hAenv0,
      show ((4 : ℝ)⁻¹ * ((4 : ℕ) : ℝ)) = 1 by norm_num]
    exact Real.rpow_one Aenv
  have hWle : W ≤ W0 := by
    rw [hW, hW0]
    refine Real.rpow_le_rpow hAenv0 ?_ (by norm_num)
    rw [hAenv]
    have hmono : freshShellFourthEnergyConst Chead (M.gamma ^ (100 : ℕ)) ≤
        freshShellFourthEnergyConst Chead 1 := by
      simp only [freshShellFourthEnergyConst]
      have h1 : M.gamma ^ (100 : ℕ) ≤ 1 := pow_le_one₀ hgamma0.le hgamma1
      have h0 : (0 : ℝ) ≤ M.gamma ^ (100 : ℕ) := by positivity
      have hsq2 : (M.gamma ^ (100 : ℕ)) ^ (2 : ℕ) ≤ (1 : ℝ) ^ (2 : ℕ) :=
        pow_le_pow_left₀ h0 h1 2
      have hcoef : (0 : ℝ) ≤ 32 * Real.exp 1 ^ (2 : ℕ) := by positivity
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hsq2 hcoef)
    have h3d : (0 : ℝ) ≤ (3 : ℝ) ^ d := by positivity
    exact mul_le_mul_of_nonneg_left hmono h3d
  have hCtotle : Cdisp * W + 96 * (Cdisp * Real.sqrt (d : ℝ) * shellNormalizationConst)
      + Cdisp * shellNormalizationConst ≤ Ctot := by
    have hstep : Cdisp * W ≤ Cdisp * W0 := mul_le_mul_of_nonneg_left hWle hCdisp0
    rw [hCtot]
    linarith only [hstep]
  obtain ⟨-, -, -, hDleg, -⟩ :=
    henv M hgenvle m0 Eind hstate m K h hhpos hm0 hcstar hK e e' he he'
  clear henv hCgate hdimgate hgenvle hq hKone hW0 hCtot hWle hW hW00 hbase0 hAenv0
  -- the depth index
  intro i
  rw [← hnbuf]
  have hsumi : (nbuf - (i : ℤ)) + ((Ngap + i : ℕ) : ℤ) = m - (h : ℤ) := by
    push_cast
    omega
  have hdimNi : d + 3 ≤ Ngap + i := le_trans hdimN (Nat.le_add_right _ _)
  have hlti : (nbuf - (i : ℤ)) + ((Ngap + i : ℕ) : ℤ) < m := by
    rw [hsumi]
    have h1 : (1 : ℤ) ≤ (h : ℤ) := by exact_mod_cast hhpos
    omega
  have hnlei : nbuf - (i : ℤ) ≤ K - 1 := by
    have h0 : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg i
    have hNg : (0 : ℤ) ≤ (Ngap : ℤ) := Int.natCast_nonneg Ngap
    omega
  have hnNlei : (nbuf - (i : ℤ)) + ((Ngap + i : ℕ) : ℤ) ≤ K - 1 := by
    rw [hsumi]; omega
  have hcellInt : ∀ R ∈ interiorMesoCubeGrid d K (nbuf - (i : ℤ))
      ((nbuf - (i : ℤ)) + ((Ngap + i : ℕ) : ℤ) - 1),
      Integrable (fun omega : Cutoff.ShellSeq d =>
        meshEnergyCell ((nbuf - (i : ℤ)) + ((Ngap + i : ℕ) : ℤ))
          (wD omega).toH1Function.grad R ^ (4 : ℝ)) M.P.toMeasure := by
    intro R hR
    exact hcell M hgcellle m0 Eind hstate m K h hhpos hm0 hcstar hK e e' he he' wD hsol
      hmem hcoord hsq hfour ((nbuf - (i : ℤ)) + ((Ngap + i : ℕ) : ℤ)) R
      (openCubeAtScale_subset_openCubeSet_of_mem_interiorMesoCubeGrid hR)
  have henvD := hDleg (nbuf - (i : ℤ)) (Ngap + i) hnlei hnNlei wD hsol hmem hcoord hsq
    hfour
  rw [← hAenv] at henvD
  have hcoarse : gridFourthMoment M.P.toMeasure
      (interiorMesoCubeGrid d K (nbuf - (i : ℤ))
        ((nbuf - (i : ℤ)) + ((Ngap + i : ℕ) : ℤ) - 1))
      (fun R omega => meshEnergyCell ((nbuf - (i : ℤ)) + ((Ngap + i : ℕ) : ℤ))
        (wD omega).toH1Function.grad R) ≤ W ^ (4 : ℕ) := by
    rw [hWpow]
    exact henvD
  have hmain := hdisp M K (nbuf - (i : ℤ)) (Ngap + i) hdimNi m hlti
    ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ hsigma0 e z₀ wD
    (by rw [hsumi]; exact hsol) W hW0nn hcoarse hcellInt
  clear hcoarse hcellInt henvD hDleg hcell hdisp hmem hcoord hsq hfour hsol
  -- the decay factor
  have hthree0 : (0 : ℝ) < (3 : ℝ) ^ (-(i : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hdelta0 : (0 : ℝ) ≤ (1 + (i : ℝ)) * (3 : ℝ) ^ (-(i : ℝ)) := by positivity
  have hG0i : (0 : ℝ) ≤ (3 : ℝ) ^ (-(((Ngap + i : ℕ) : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
  have hNgap1 : 1 ≤ Ngap := by omega
  have hGdec := depth_geometric_le hgamma0 hgamma1 Ngap i hGle
  have hNrGdec := depth_linear_geometric_le hgamma0 Ngap i hNgap1 hGle hNrle
  have hPeq : (((nbuf - (i : ℤ) : ℤ)) : ℝ) + (((Ngap + i : ℕ)) : ℝ) =
      ((nbuf : ℤ) : ℝ) + ((Ngap : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hPeq] at hmain
  have hbudget : Cdisp * ((3 : ℝ) ^ (-(((Ngap + i : ℕ) : ℝ))) * W) +
        Cdisp * (((Ngap + i : ℕ) : ℝ) *
            (((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ * Real.sqrt (d : ℝ) *
              Book.Ch02.vecNorm e)) *
          ((3 : ℝ) ^ (-(((Ngap + i : ℕ) : ℝ))) *
            (3 : ℝ) ^ (M.gamma * (((nbuf : ℤ) : ℝ) + ((Ngap : ℕ) : ℝ)))) +
        Cdisp * ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ *
          ((3 : ℝ) ^ (-(((Ngap + i : ℕ) : ℝ))) *
            (3 : ℝ) ^ (M.gamma * (((nbuf : ℤ) : ℝ) + ((Ngap : ℕ) : ℝ)))) ≤
      M.gamma ^ (16 : ℕ) * ((1 + (i : ℝ)) * (3 : ℝ) ^ (-(i : ℝ))) :=
    three_term_budget_le_sixteen_decay hCdisp0 hW0nn shellNormalizationConst_nonneg
      (Real.sqrt_nonneg _) (Nat.cast_nonneg _) hG0i (Book.Ch02.vecNorm_nonneg e)
      hdelta0 hgamma0 hGdec hNrGdec hSPle he hCtotle hfinal
  have hgoal := le_trans hmain hbudget
  rw [hsumi] at hgoal
  exact hgoal

private theorem gammaTenDepthOscillation_comparisonBounds2 :
    ∀ (d : ℕ) (Ctot : ℝ) (_ : (0 : ℝ) ≤ Ctot) (M : ABKModel d) (m0 : ℤ) (Eind : { E : ℝ // (1 : ℝ)
      ≤ E })
      (_ : Frozen.Section3.inductionState M m0 Eind) (m K : ℤ) (h : ℕ) (_ : (0 : ℕ) < h) (_ : m -
        (↑h : ℤ) ≤ m0)
      (_ : (↑h : ℝ) ≤ (6 : ℝ) * Disorder.cstar M * M.gamma⁻¹)
      (_ : (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (↑K : ℝ) - (↑m : ℝ)) (_ : M.gamma ≤ (1 / 4 : ℝ))
      (_ : M.gamma ≤ (3 : ℝ) ^ (-((↑d : ℝ) + (3 : ℝ)))) (_ : M.gamma ≤ (1 : ℝ) / ((1 : ℝ) + Ctot))
      (_ : (0 : ℝ) < M.gamma) (_ : M.gamma ≤ (1 : ℝ)) (nbuf : ℤ)
      (_ : nbuf = recurrenceMesoScale recurrenceGapMultiplier M.gamma m (↑h : ℤ)) (Ngap : ℕ)
      (_ : Ngap = recurrenceGap recurrenceGapMultiplier M.gamma) (_ : nbuf + (↑Ngap : ℤ) = m - (↑h
        : ℤ))
      (_ : (↑nbuf : ℝ) + (↑Ngap : ℝ) = (↑(m - (↑h : ℤ)) : ℝ)),
      (1 : ℝ) ≤ (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ∧
        d + (3 : ℕ) ≤ Ngap ∧
          (3 : ℝ) ^ (-(↑Ngap : ℝ)) ≤ M.gamma ^ (32 : ℕ) ∧
            (↑Ngap : ℝ) * M.gamma ≤ (96 : ℝ) ∧
              (0 : ℝ) ≤ (↑(Annealed.sigmaBar M (m - (↑h : ℤ))) : ℝ)⁻¹ ∧
                (↑(Annealed.sigmaBar M (m - (↑h : ℤ))) : ℝ)⁻¹ * (3 : ℝ) ^ (M.gamma * ((↑nbuf : ℝ)
                  + (↑Ngap : ℝ))) ≤
                    shellNormalizationConst ∧
                  Ctot * M.gamma ^ (15 : ℕ) ≤ (1 : ℝ) := by
  intro d Ctot hCtot0 M _ _ hstate m K h hhpos hm0 hcstar _ _ hdimgate hCgate hgamma0 hgamma1 nbuf
    _ Ngap hNgap _ hsumR
  have hKone : (1 : ℝ) ≤ (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ := by
    have hinv : (1 : ℝ) ≤ M.gamma⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) hgamma0]
      linarith
    have h10 : (1 : ℝ) ≤ (10 : ℝ) ^ (10 : ℕ) := by norm_num
    exact one_le_mul_of_one_le_of_one_le h10 hinv
  have hmK1 : m ≤ K - 1 := by
    have hle : (m : ℝ) + 1 ≤ (K : ℝ) := by linarith
    have : m + 1 ≤ K := by exact_mod_cast hle
    omega
  have hnNle : nbuf + (Ngap : ℤ) ≤ K - 1 := by omega
  have hdimN : d + 3 ≤ Ngap := by
    rw [hNgap]
    refine dim_add_three_le_recurrenceGap (a := recurrenceGapMultiplier) d hgamma0
      (by norm_num [recurrenceGapMultiplier]) ?_
    have hpow : (0 : ℝ) < (3 : ℝ) ^ ((d : ℝ) + 3) := Real.rpow_pos_of_pos (by norm_num) _
    have h2 : M.gamma ≤ ((3 : ℝ) ^ ((d : ℝ) + 3))⁻¹ := by
      rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
      exact hdimgate
    exact (le_inv_comm₀ hpow hgamma0).mpr h2
  have hGle : (3 : ℝ) ^ (-((Ngap : ℕ) : ℝ)) ≤ M.gamma ^ (32 : ℕ) := by
    have hbase := rpow_three_neg_recurrenceGap_le_gamma_pow recurrenceGapMultiplier
      (gamma := M.gamma) hgamma0 hgamma1
    rw [hNgap]
    simpa [recurrenceGapMultiplier] using hbase
  have hNrle : ((Ngap : ℕ) : ℝ) * M.gamma ≤ 96 := by
    have hbase := recurrenceGap_mul_gamma_le recurrenceGapMultiplier
      (gamma := M.gamma) hgamma0 hgamma1
    rw [hNgap]
    calc ((recurrenceGap recurrenceGapMultiplier M.gamma : ℕ) : ℝ) * M.gamma
        ≤ 3 * ((recurrenceGapMultiplier : ℕ) : ℝ) := hbase
      _ = 96 := by norm_num [recurrenceGapMultiplier]
  have hsigma0 : (0 : ℝ) ≤ ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ :=
    (inv_pos.2 (Annealed.sigmaBar_characterization M (m - (h : ℤ))).1).le
  have hSPle : ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ *
      (3 : ℝ) ^ (M.gamma * (((nbuf : ℤ) : ℝ) + ((Ngap : ℕ) : ℝ))) ≤
        shellNormalizationConst := by
    rw [hsumR]
    exact sigmaBarInv_mul_rpow_gamma_shell_le M hstate hhpos hm0 hcstar
  have hfinal : Ctot * M.gamma ^ (15 : ℕ) ≤ 1 := by
    have h15 : M.gamma ^ (15 : ℕ) ≤ M.gamma := by
      calc M.gamma ^ (15 : ℕ) ≤ M.gamma ^ (1 : ℕ) :=
            pow_le_pow_of_le_one hgamma0.le hgamma1 (by norm_num)
        _ = M.gamma := pow_one _
    have hCg : Ctot * M.gamma ^ (15 : ℕ) ≤ Ctot * M.gamma :=
      mul_le_mul_of_nonneg_left h15 hCtot0
    have hCg2 : Ctot * M.gamma ≤ Ctot * (1 / (1 + Ctot)) :=
      mul_le_mul_of_nonneg_left hCgate hCtot0
    have hden : (0 : ℝ) < 1 + Ctot := by linarith
    have hlast : Ctot * (1 / (1 + Ctot)) ≤ 1 := by
      rw [mul_one_div, div_le_one hden]
      linarith
    linarith
  exact ⟨hKone, hdimN, hGle, hNrle, hsigma0, hSPle, hfinal⟩

theorem exists_gamma0_freshShellNeumann_meshOscillationDepth_le_gamma_pow_sixteen
    (d : ℕ) (hd : 2 ≤ d) :
    ∃ gamma0 : ℝ, 0 < gamma0 ∧ gamma0 ≤ 1 / 4 ∧
      ∀ (M : ABKModel d), M.gamma ≤ gamma0 →
        ∀ (m0 : ℤ) (Eind : {E : ℝ // 1 ≤ E}),
          Algsuperdiff.Frozen.Section3.inductionState M m0 Eind →
          ∀ (m K : ℤ) (h : ℕ), 0 < h → m - (h : ℤ) ≤ m0 →
            (h : ℝ) ≤ 6 * Disorder.cstar M * M.gamma⁻¹ →
            (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ ≤ (K : ℝ) - (m : ℝ) →
            ∀ e e' : Vec d, Book.Ch02.vecNorm e ≤ 1 →
              Book.Ch02.vecNorm e' ≤ 1 →
              ∀ z₀ : Vec d,
                ∀ wN : Cutoff.ShellSeq d → H1MeanZeroFunction (openCubeSet (originCube d K)),
                  (∀ omega, IsMeanZeroNeumannRhsWeakSolution
                      (fun _ : Vec d => (1 : Matrix (Fin d) (Fin d) ℝ))
                      (openCubeSet (originCube d K)) (wN omega)
                      (fun x => -Corrector.streamForcing
                        ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ omega
                        (m - (h : ℤ)) m e' x)) →
                  ∀ i : ℕ,
                    gridFourthMomentRoot M.P.toMeasure
                        (interiorMesoCubeGrid d K
                          (recurrenceMesoScale recurrenceGapMultiplier M.gamma m (h : ℤ) -
                            (i : ℤ))
                          (m - (h : ℤ) - 1))
                        (fun R omega => meshOscillationCell
                          (recurrenceMesoScale recurrenceGapMultiplier M.gamma m (h : ℤ) -
                            (i : ℤ))
                          (wN omega).toH1Function.grad R) +
                        ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ *
                          ((3 : ℝ) ^ ((recurrenceMesoScale recurrenceGapMultiplier M.gamma
                              m (h : ℤ) - (i : ℤ) : ℤ) : ℝ) *
                            (∫ omega : Cutoff.ShellSeq d,
                              shellDerivNormSum (m - (h : ℤ)) m z₀ omega ^ (4 : ℝ)
                                ∂M.P.toMeasure) ^ ((4 : ℝ)⁻¹)) ≤
                      M.gamma ^ (16 : ℕ) * ((1 + (i : ℝ)) * (3 : ℝ) ^ (-(i : ℝ))) := by
  classical
  obtain ⟨Cdisp, hCdisp0, hdisp⟩ :=
    exists_freshShellNeumann_gradient_oscillation_lower_bound_display
      (d := d) (lt_of_lt_of_le (by norm_num) hd)
  obtain ⟨Chead, -, genv, hgenv0, -, henv⟩ :=
    exists_freshShell_gridFourthMoment_mesoWindowEnergy_le_wired d hd
  obtain ⟨gcell, hgcell0, -, hcell⟩ :=
    exists_gamma0_integrable_freshShellNeumann_meshEnergyCell_rpow_four d hd
  obtain ⟨W0, hW0⟩ : ∃ W0 : ℝ,
      W0 = ((3 : ℝ) ^ d * freshShellFourthEnergyConst Chead 1) ^ ((4 : ℝ)⁻¹) := ⟨_, rfl⟩
  have hbase0 : (0 : ℝ) ≤ (3 : ℝ) ^ d * freshShellFourthEnergyConst Chead 1 :=
    mul_nonneg (by positivity) (freshShellFourthEnergyConst_nonneg _ _)
  have hW00 : 0 ≤ W0 := by rw [hW0]; exact Real.rpow_nonneg hbase0 _
  obtain ⟨Ctot, hCtot⟩ : ∃ Ctot : ℝ,
      Ctot = Cdisp * W0 + 96 * (Cdisp * Real.sqrt (d : ℝ) * shellNormalizationConst)
        + Cdisp * shellNormalizationConst := ⟨_, rfl⟩
  have hCtot0 : 0 ≤ Ctot := by
    have hsq : (0 : ℝ) ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
    have hsn : (0 : ℝ) ≤ shellNormalizationConst := shellNormalizationConst_nonneg
    have hb1 : (0 : ℝ) ≤ Cdisp * W0 := mul_nonneg hCdisp0 hW00
    have hb2 : (0 : ℝ) ≤ 96 * (Cdisp * Real.sqrt (d : ℝ) * shellNormalizationConst) :=
      mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hCdisp0 hsq) hsn)
    have hb3 : (0 : ℝ) ≤ Cdisp * shellNormalizationConst := mul_nonneg hCdisp0 hsn
    rw [hCtot]
    linarith
  refine ⟨min gcell
      (min (1 / 4) (min genv (min ((3 : ℝ) ^ (-((d : ℝ) + 3))) (1 / (1 + Ctot))))),
    ?_, le_trans (min_le_right _ _) (min_le_left _ _), ?_⟩
  · refine lt_min hgcell0 (lt_min (by norm_num) (lt_min hgenv0 (lt_min ?_ ?_)))
    · exact Real.rpow_pos_of_pos (by norm_num) _
    · exact div_pos one_pos (by linarith)
  intro M hMgamma m0 Eind hstate m K h hhpos hm0 hcstar hK e e' he he' z₀ wN hsol
  have hgcellle : M.gamma ≤ gcell := le_trans hMgamma (min_le_left _ _)
  have hq : M.gamma ≤ 1 / 4 :=
    le_trans hMgamma (le_trans (min_le_right _ _) (min_le_left _ _))
  have hgenvle : M.gamma ≤ genv :=
    le_trans hMgamma
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hdimgate : M.gamma ≤ (3 : ℝ) ^ (-((d : ℝ) + 3)) :=
    le_trans hMgamma (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hCgate : M.gamma ≤ 1 / (1 + Ctot) :=
    le_trans hMgamma (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))))
  clear hMgamma
  have hgrad : ∀ omega : Cutoff.ShellSeq d,
      MemLp (wN omega).toH1Function.grad (8 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d K)) := fun omega =>
    memLp_eight_grad_freshShellNeumann hd (originCube d K)
      ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ omega (m - (h : ℤ)) m e'
      (wN omega) (hsol omega)
  have hmem : ∀ omega : Cutoff.ShellSeq d,
      MemLp (fun x => Book.Ch02.vecNorm ((wN omega).toH1Function.grad x)) 8
        (normalizedCubeMeasure (originCube d K)) := fun omega =>
    memLp_vecNorm_eight_of_memLp_eight _ (hgrad omega)
  have hcoord : ∀ (omega : Cutoff.ShellSeq d) (k : Fin d),
      IntegrableOn (fun x => ((wN omega).toH1Function.grad x k) ^ 2)
        (openCubeSet (originCube d K)) volume := fun omega k =>
    integrableOn_openCubeSet_coord_sq_of_memLp_eight _ (hgrad omega) k
  have hsq : ∀ omega : Cutoff.ShellSeq d,
      IntegrableOn (fun x => vecNormSq ((wN omega).toH1Function.grad x))
        (openCubeSet (originCube d K)) volume := fun omega =>
    integrableOn_openCubeSet_vecNormSq_of_memLp_eight _ (hgrad omega)
  have hfour : ∀ omega : Cutoff.ShellSeq d,
      IntegrableOn (fun x => vecNormSq ((wN omega).toH1Function.grad x) ^ 2)
        (openCubeSet (originCube d K)) volume := fun omega =>
    integrableOn_openCubeSet_vecNormSq_sq_of_memLp_eight _ (hgrad omega)
  clear hgrad
  have hgamma0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  have hgamma1 : M.gamma ≤ 1 := le_trans hq (by norm_num)
  obtain ⟨nbuf, hnbuf⟩ : ∃ n : ℤ,
      n = recurrenceMesoScale recurrenceGapMultiplier M.gamma m (h : ℤ) := ⟨_, rfl⟩
  obtain ⟨Ngap, hNgap⟩ : ∃ N : ℕ,
      N = recurrenceGap recurrenceGapMultiplier M.gamma := ⟨_, rfl⟩
  have hsum : nbuf + (Ngap : ℤ) = m - (h : ℤ) := by
    rw [hnbuf, hNgap]
    exact recurrenceMesoScale_add_recurrenceGap _ _ _ _
  have hsumR : ((nbuf : ℤ) : ℝ) + ((Ngap : ℕ) : ℝ) = (((m - (h : ℤ) : ℤ)) : ℝ) := by
    rw [hnbuf, hNgap]
    exact recurrenceMesoScale_add_recurrenceGap_real _ _ _ _
  have hmK : m ≤ K := by
    have hpos : (0 : ℝ) < (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹ := by positivity
    have hle : (m : ℝ) ≤ (K : ℝ) := by linarith
    exact_mod_cast hle
  obtain ⟨hKone, hdimN, hGle, hNrle, hsigma0, hSPle, hfinal⟩ :=
    (show ((1 : ℝ) ≤ (10 : ℝ) ^ (10 : ℕ) * M.gamma⁻¹) ∧ (d + 3 ≤ Ngap) ∧ ((3 : ℝ) ^ (-((Ngap : ℕ)
      : ℝ)) ≤ M.gamma ^ (32 : ℕ)) ∧ (((Ngap : ℕ) : ℝ) * M.gamma ≤ 96) ∧ ((0 : ℝ) ≤
        ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹) ∧ (((Annealed.sigmaBar M (m - (h : ℤ)) :
          ℝ))⁻¹ *
      (3 : ℝ) ^ (M.gamma * (((nbuf : ℤ) : ℝ) + ((Ngap : ℕ) : ℝ))) ≤
        shellNormalizationConst) ∧ (Ctot * M.gamma ^ (15 : ℕ) ≤ 1) from
      @gammaTenDepthOscillation_comparisonBounds2 (d) (Ctot) (hCtot0) (M) (m0) (Eind) (hstate) (m)
        (K) (h) (hhpos) (hm0) (hcstar) (hK) (hq) (hdimgate) (hCgate) (hgamma0) (hgamma1) (nbuf)
          (hnbuf) (Ngap) (hNgap) (hsum) (hsumR))
  obtain ⟨Aenv, hAenv⟩ : ∃ A : ℝ,
      A = (3 : ℝ) ^ d * freshShellFourthEnergyConst Chead (M.gamma ^ (100 : ℕ)) := ⟨_, rfl⟩
  have hAenv0 : 0 ≤ Aenv := by
    rw [hAenv]
    exact mul_nonneg (by positivity) (freshShellFourthEnergyConst_nonneg _ _)
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = Aenv ^ ((4 : ℝ)⁻¹) := ⟨_, rfl⟩
  have hW0nn : 0 ≤ W := by rw [hW]; exact Real.rpow_nonneg hAenv0 _
  have hWpow : W ^ (4 : ℕ) = Aenv := by
    rw [hW, ← Real.rpow_natCast (Aenv ^ ((4 : ℝ)⁻¹)) 4, ← Real.rpow_mul hAenv0,
      show ((4 : ℝ)⁻¹ * ((4 : ℕ) : ℝ)) = 1 by norm_num]
    exact Real.rpow_one Aenv
  have hWle : W ≤ W0 := by
    rw [hW, hW0]
    refine Real.rpow_le_rpow hAenv0 ?_ (by norm_num)
    rw [hAenv]
    have hmono : freshShellFourthEnergyConst Chead (M.gamma ^ (100 : ℕ)) ≤
        freshShellFourthEnergyConst Chead 1 := by
      simp only [freshShellFourthEnergyConst]
      have h1 : M.gamma ^ (100 : ℕ) ≤ 1 := pow_le_one₀ hgamma0.le hgamma1
      have h0 : (0 : ℝ) ≤ M.gamma ^ (100 : ℕ) := by positivity
      have hsq2 : (M.gamma ^ (100 : ℕ)) ^ (2 : ℕ) ≤ (1 : ℝ) ^ (2 : ℕ) :=
        pow_le_pow_left₀ h0 h1 2
      have hcoef : (0 : ℝ) ≤ 32 * Real.exp 1 ^ (2 : ℕ) := by positivity
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hsq2 hcoef)
    have h3d : (0 : ℝ) ≤ (3 : ℝ) ^ d := by positivity
    exact mul_le_mul_of_nonneg_left hmono h3d
  have hCtotle : Cdisp * W + 96 * (Cdisp * Real.sqrt (d : ℝ) * shellNormalizationConst)
      + Cdisp * shellNormalizationConst ≤ Ctot := by
    have hstep : Cdisp * W ≤ Cdisp * W0 := mul_le_mul_of_nonneg_left hWle hCdisp0
    rw [hCtot]
    linarith only [hstep]
  obtain ⟨-, -, -, -, hDleg⟩ :=
    henv M hgenvle m0 Eind hstate m K h hhpos hm0 hcstar hK e e' he he'
  clear henv hCgate hdimgate hgenvle hq hKone hW0 hCtot hWle hW hW00 hbase0 hAenv0
  -- the depth index
  intro i
  rw [← hnbuf]
  have hsumi : (nbuf - (i : ℤ)) + ((Ngap + i : ℕ) : ℤ) = m - (h : ℤ) := by
    push_cast
    omega
  have hdimNi : d + 3 ≤ Ngap + i := le_trans hdimN (Nat.le_add_right _ _)
  have hlti : (nbuf - (i : ℤ)) + ((Ngap + i : ℕ) : ℤ) < m := by
    rw [hsumi]
    have h1 : (1 : ℤ) ≤ (h : ℤ) := by exact_mod_cast hhpos
    omega
  have hnlei : nbuf - (i : ℤ) ≤ K - 1 := by
    have h0 : (0 : ℤ) ≤ (i : ℤ) := Int.natCast_nonneg i
    have hNg : (0 : ℤ) ≤ (Ngap : ℤ) := Int.natCast_nonneg Ngap
    omega
  have hnNlei : (nbuf - (i : ℤ)) + ((Ngap + i : ℕ) : ℤ) ≤ K - 1 := by
    rw [hsumi]; omega
  have hcellInt : ∀ R ∈ interiorMesoCubeGrid d K (nbuf - (i : ℤ))
      ((nbuf - (i : ℤ)) + ((Ngap + i : ℕ) : ℤ) - 1),
      Integrable (fun omega : Cutoff.ShellSeq d =>
        meshEnergyCell ((nbuf - (i : ℤ)) + ((Ngap + i : ℕ) : ℤ))
          (wN omega).toH1Function.grad R ^ (4 : ℝ)) M.P.toMeasure := by
    intro R hR
    exact hcell M hgcellle m0 Eind hstate m K h hhpos hm0 hcstar hK e e' he he' wN hsol
      hmem hcoord hsq hfour ((nbuf - (i : ℤ)) + ((Ngap + i : ℕ) : ℤ)) R
      (openCubeAtScale_subset_openCubeSet_of_mem_interiorMesoCubeGrid hR)
  have henvD := hDleg (nbuf - (i : ℤ)) (Ngap + i) hnlei hnNlei wN hsol hmem hcoord hsq
    hfour
  rw [← hAenv] at henvD
  have hcoarse : gridFourthMoment M.P.toMeasure
      (interiorMesoCubeGrid d K (nbuf - (i : ℤ))
        ((nbuf - (i : ℤ)) + ((Ngap + i : ℕ) : ℤ) - 1))
      (fun R omega => meshEnergyCell ((nbuf - (i : ℤ)) + ((Ngap + i : ℕ) : ℤ))
        (wN omega).toH1Function.grad R) ≤ W ^ (4 : ℕ) := by
    rw [hWpow]
    exact henvD
  have hmain := hdisp M K (nbuf - (i : ℤ)) (Ngap + i) hdimNi m hlti
    ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ hsigma0 e' z₀ wN
    (by rw [hsumi]; exact hsol) W hW0nn hcoarse hcellInt
  clear hcoarse hcellInt henvD hDleg hcell hdisp hmem hcoord hsq hfour hsol
  -- the decay factor
  have hthree0 : (0 : ℝ) < (3 : ℝ) ^ (-(i : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
  have hdelta0 : (0 : ℝ) ≤ (1 + (i : ℝ)) * (3 : ℝ) ^ (-(i : ℝ)) := by positivity
  have hG0i : (0 : ℝ) ≤ (3 : ℝ) ^ (-(((Ngap + i : ℕ) : ℝ))) :=
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 3) _).le
  have hNgap1 : 1 ≤ Ngap := by omega
  have hGdec := depth_geometric_le hgamma0 hgamma1 Ngap i hGle
  have hNrGdec := depth_linear_geometric_le hgamma0 Ngap i hNgap1 hGle hNrle
  have hPeq : (((nbuf - (i : ℤ) : ℤ)) : ℝ) + (((Ngap + i : ℕ)) : ℝ) =
      ((nbuf : ℤ) : ℝ) + ((Ngap : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hPeq] at hmain
  have hbudget : Cdisp * ((3 : ℝ) ^ (-(((Ngap + i : ℕ) : ℝ))) * W) +
        Cdisp * (((Ngap + i : ℕ) : ℝ) *
            (((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ * Real.sqrt (d : ℝ) *
              Book.Ch02.vecNorm e')) *
          ((3 : ℝ) ^ (-(((Ngap + i : ℕ) : ℝ))) *
            (3 : ℝ) ^ (M.gamma * (((nbuf : ℤ) : ℝ) + ((Ngap : ℕ) : ℝ)))) +
        Cdisp * ((Annealed.sigmaBar M (m - (h : ℤ)) : ℝ))⁻¹ *
          ((3 : ℝ) ^ (-(((Ngap + i : ℕ) : ℝ))) *
            (3 : ℝ) ^ (M.gamma * (((nbuf : ℤ) : ℝ) + ((Ngap : ℕ) : ℝ)))) ≤
      M.gamma ^ (16 : ℕ) * ((1 + (i : ℝ)) * (3 : ℝ) ^ (-(i : ℝ))) :=
    three_term_budget_le_sixteen_decay hCdisp0 hW0nn shellNormalizationConst_nonneg
      (Real.sqrt_nonneg _) (Nat.cast_nonneg _) hG0i (Book.Ch02.vecNorm_nonneg e')
      hdelta0 hgamma0 hGdec hNrGdec hSPle he' hCtotle hfinal
  have hgoal := le_trans hmain hbudget
  rw [hsumi] at hgoal
  exact hgoal


end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
