/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.RecurrenceIntegration
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.SmallScaleBound
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Disorder.CstarUpperBound
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Scales.Landmarks

/-!
# SubLandmarkDisplays

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
Binder descriptions below are an informal inventory only, NOT a source
certification; certification vocabulary is reserved for frozen source-facing
declarations.

# The recurrence binders below the base landmark, from the base-case plateau

## The seam

`l.approximate.recurrence.formula` (ABK26) supplies its two displays
`e.what.do.we.have` only on the range `m** <= n <= m_0 - h`, whereas its
consumer `l.integrate.approx.recurrence` assumes
`e.assump.upper`/`e.assump.lower.modified` at every pair `n <= m <= m_0` with
`m <= n + c_star gamma^{-1}`. bridges the two by bare citation.

This file pays that debt.  It proves that on the uncovered range the two
binders are consequences of the base-case plateau alone, and then re-derives
the full conclusion of `integrate_approx_recurrence_cstarPlus` from an
`m**`-floored recurrence family.  No second integration engine is introduced:
the headline theorem's proof is a call to the proved
`integrate_approx_recurrence_cstarPlus`.

## Why the uncovered range is small

The consumer's own admissible-scale restriction is `(m: real) <= (n: real) +
c_star gamma^{-1}`.  Hence for an uncovered pair (`n < m**`) one has `m < m** +
c_star gamma^{-1}`, so *both* endpoints lie within `c_star gamma^{-1}` scales
of `m**`.  The landmark `m**` is defined by the `gamma^{-3}` threshold `nu^2 >=
2 (log 3) c+ gamma^{-3} 3^{2 gamma m}`, three powers of `gamma` below the `m*`
threshold, and `gamma (m - n) <= c_star <= 3/2` on the admissible range costs
only the absolute factor `3^{2 c_star} <= 81`.  The plateau envelope
`e.small.scale.bound`/`e.plateau.region.bound` therefore still pins the
sequence at `nu` to relative accuracy `O(gamma^2)` at *both* endpoints, while
the recurrence increment `A_{n,m}` is itself `O(nu^2 gamma^2)`.  Every term
that the two displays are meant to track is thus dominated by the single slack
term `E gamma` of the binders, and both binders hold with room to spare.

This is exactly the "vacuously-easily on the base-case plateau" reading
suggested but never carried out.  Note that it is the consumer's *narrow* shell
budget `c_star gamma^{-1}` that makes it work; the argument below does **not**
cover the source lemma's wider `h <= 6 c_star gamma^{-1}`, which is not needed
here.

## Main results

* `recurrence_binders_of_below_landmark`: at a single pair `(n, m)` whose lower
  endpoint meets the `m**` threshold, the plateau envelope alone gives both
  `e.assump.upper` and `e.assump.lower.modified`.
* `integrate_approx_recurrence_of_landmark_floored`: the conclusion
  `e.concl.root.gamma.inv` of `l.integrate.approx.recurrence`, from a
  recurrence family that is supplied only for `mss <= n`.
* `sigmaBar_integrate_approx_recurrence_of_mStarStar_floored`: the same, at the
  genuine running diffusivity `Annealed.sigmaBar`, the genuine constants
  `Disorder.cstar`/`Disorder.cstarPlus`, and the genuine landmark
  `Section3.mStarStar`.

## What is NOT claimed

`l.approximate.recurrence.formula` is not proved here and nothing in this file
asserts it; the `hupper`/`hlower` families of the headline theorems remain
disclosed hypotheses.  What is proved is that those families no longer need to
be assumed below `m**`.  No node is claimed closed.

## References

* ABK26, `e.mstarstar` and `e.mstar`.
* ABK26, `p.base.case`; `e.plateau.region.bound`.
* ABK26, `l.approximate.recurrence.formula`.
* ABK26, `l.integrate.approx.recurrence`; the citation.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

open Algsuperdiff.Section3
open Algsuperdiff.Section3.Provider.Diffusivity.RecurrenceIntegration

noncomputable section

private lemma gamma_sq_le_one_twenty_eighth {gamma : ℝ}
    (hgamma : 0 < gamma) (hgamma128 : gamma ≤ 1 / 128) :
    gamma ^ 2 ≤ gamma / 128 := by
  calc
    gamma ^ 2 = gamma * gamma := by rw [pow_two]
    _ ≤ gamma * (1 / 128) := mul_le_mul_of_nonneg_left hgamma128 hgamma.le
    _ = gamma / 128 := by ring

private lemma plateau_final_chunk {c cp X : ℝ} (hcp : 0 < cp)
    (hkey : 81 * c ^ 2 ≤ 243 / 2 * cp) (hX : 0 ≤ X) :
    81 * c ^ 2 * X / (2 * cp) ≤ 243 / 4 * X := by
  rw [div_le_iff₀ (mul_pos (by norm_num) hcp)]
  nlinarith only [hkey, hX]

/-! ## Scalar algebra

The three lemmas of this section are pure real algebra: no `rpow`, `exp` or
`log` occurs in their statements, so the nonlinear arithmetic used to prove
them never meets a transcendental atom. -/

/-- The three plateau estimates on an admissible pair whose lower endpoint
meets the `m**` threshold, in abstract form.

`gn`, `gm` stand for `3 ^ (2 gamma n)`, `3 ^ (2 gamma m)`, `L` for `log 3`,
`d0` for `m - n`, and `hfl` is the `m**` threshold at `n`.  Only the upper
bound on `d0` is used. -/
private lemma plateau_pair_bounds
    {nu cstar cstarPlus gamma L gn gm d0 : ℝ}
    (hnu : 0 < nu) (hcstar : 0 < cstar) (hcstar32 : cstar ≤ 3 / 2)
    (hcc : cstar ≤ cstarPlus) (hgamma : 0 < gamma) (hL : 1 ≤ L)
    (hgn : 0 < gn) (hgm : 0 < gm) (hgmn : gm ≤ 81 * gn)
    (hd0' : d0 ≤ cstar * gamma⁻¹)
    (hfl : 2 * L * cstarPlus * gn ≤ nu ^ 2 * gamma ^ 3) :
    (nu ^ 2)⁻¹ * cstarPlus * gamma⁻¹ * gn ≤ gamma ^ 2 / 2 ∧
      (nu ^ 2)⁻¹ * cstarPlus * gamma⁻¹ * gm ≤ 81 * gamma ^ 2 / 2 ∧
        cstar * L * d0 * gm ≤ 243 / 4 * nu ^ 2 * gamma ^ 2 := by
  have hcp : 0 < cstarPlus := lt_of_lt_of_le hcstar hcc
  have hnu2 : (0 : ℝ) < nu ^ 2 := pow_pos hnu 2
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL
  have hginv : (0 : ℝ) < gamma⁻¹ := inv_pos.mpr hgamma
  -- `c+ (L gn) ≤ nu² gamma³ / 2`, a pure restatement of the threshold.
  have hLgn : cstarPlus * (L * gn) ≤ nu ^ 2 * gamma ^ 3 / 2 := by linarith
  -- dropping the factor `L ≥ 1` gives `c+ gn ≤ nu² gamma³ / 2`.
  have haux : 0 ≤ (L - 1) * (cstarPlus * gn) :=
    mul_nonneg (by linarith) (mul_pos hcp hgn).le
  have hgnb : cstarPlus * gn ≤ nu ^ 2 * gamma ^ 3 / 2 := by
    calc
      cstarPlus * gn ≤ (cstarPlus * gn) * L :=
        le_mul_of_one_le_right (mul_pos hcp hgn).le hL
      _ = cstarPlus * (L * gn) := by ring
      _ ≤ nu ^ 2 * gamma ^ 3 / 2 := hLgn
  have hgmb : cstarPlus * gm ≤ 81 * (nu ^ 2 * gamma ^ 3 / 2) := by
    have h1 : cstarPlus * gm ≤ cstarPlus * (81 * gn) :=
      mul_le_mul_of_nonneg_left hgmn hcp.le
    calc
      cstarPlus * gm ≤ cstarPlus * (81 * gn) := h1
      _ = 81 * (cstarPlus * gn) := by ring
      _ ≤ 81 * (nu ^ 2 * gamma ^ 3 / 2) :=
        mul_le_mul_of_nonneg_left hgnb (by norm_num)
  have hcoef : (0 : ℝ) ≤ (nu ^ 2)⁻¹ * gamma⁻¹ :=
    mul_nonneg (inv_nonneg.mpr hnu2.le) hginv.le
  refine ⟨?_, ?_, ?_⟩
  · calc (nu ^ 2)⁻¹ * cstarPlus * gamma⁻¹ * gn
        = (nu ^ 2)⁻¹ * gamma⁻¹ * (cstarPlus * gn) := by ring
      _ ≤ (nu ^ 2)⁻¹ * gamma⁻¹ * (nu ^ 2 * gamma ^ 3 / 2) :=
          mul_le_mul_of_nonneg_left hgnb hcoef
      _ = gamma ^ 2 / 2 := by field_simp
  · calc (nu ^ 2)⁻¹ * cstarPlus * gamma⁻¹ * gm
        = (nu ^ 2)⁻¹ * gamma⁻¹ * (cstarPlus * gm) := by ring
      _ ≤ (nu ^ 2)⁻¹ * gamma⁻¹ * (81 * (nu ^ 2 * gamma ^ 3 / 2)) :=
          mul_le_mul_of_nonneg_left hgmb hcoef
      _ = 81 * gamma ^ 2 / 2 := by field_simp
  · have hLgn2 : L * gn ≤ nu ^ 2 * gamma ^ 3 / (2 * cstarPlus) := by
      rw [le_div_iff₀ (by positivity)]
      linarith [hLgn]
    have hkey : 81 * cstar ^ 2 ≤ 243 / 2 * cstarPlus := by
      have hmul := mul_le_mul hcstar32 hcc hcstar.le (by norm_num : (0 : ℝ) ≤ 3 / 2)
      calc
        81 * cstar ^ 2 = 81 * (cstar * cstar) := by rw [pow_two]
        _ ≤ 81 * ((3 / 2) * cstarPlus) :=
          mul_le_mul_of_nonneg_left hmul (by norm_num)
        _ = 243 / 2 * cstarPlus := by ring
    calc cstar * L * d0 * gm
        ≤ cstar * L * (cstar * gamma⁻¹) * gm :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hd0'
              (mul_nonneg hcstar.le hLpos.le)) hgm.le
      _ ≤ cstar * L * (cstar * gamma⁻¹) * (81 * gn) :=
          mul_le_mul_of_nonneg_left hgmn
            (mul_nonneg (mul_nonneg hcstar.le hLpos.le)
              (mul_nonneg hcstar.le hginv.le))
      _ = 81 * cstar ^ 2 * gamma⁻¹ * (L * gn) := by ring
      _ ≤ 81 * cstar ^ 2 * gamma⁻¹ * (nu ^ 2 * gamma ^ 3 / (2 * cstarPlus)) :=
          mul_le_mul_of_nonneg_left hLgn2
            (mul_nonneg (by positivity) hginv.le)
      _ = 81 * cstar ^ 2 * nu ^ 2 * gamma ^ 2 / (2 * cstarPlus) := by
          field_simp
      _ ≤ 243 / 4 * nu ^ 2 * gamma ^ 2 := by
          simpa only [mul_assoc] using plateau_final_chunk hcp hkey
            (mul_nonneg (sq_nonneg nu) (sq_nonneg gamma))

/-- `e.assump.upper` on the plateau: the whole increment term is spare. -/
private lemma upper_binder_of_plateau
    {nu gamma E x y t : ℝ}
    (hnu : 0 < nu) (hgamma : 0 < gamma) (hgamma128 : gamma ≤ 1 / 128) (hE : 1 ≤ E)
    (hx : x ≤ (1 + 81 * gamma ^ 2 / 2) * nu) (hy : nu ≤ y) (ht : 0 ≤ t) :
    x ≤ (1 + E * gamma) * y + t := by
  have hsq : gamma ^ 2 ≤ gamma / 128 :=
    gamma_sq_le_one_twenty_eighth hgamma hgamma128
  have hEg : gamma ≤ E * gamma := le_mul_of_one_le_left hgamma.le hE
  have h1 : 81 * gamma ^ 2 / 2 ≤ E * gamma := by linarith
  have h2 : (1 + 81 * gamma ^ 2 / 2) * nu ≤ (1 + E * gamma) * nu :=
    mul_le_mul_of_nonneg_right (by linarith) hnu.le
  have h3 : (1 + E * gamma) * nu ≤ (1 + E * gamma) * y :=
    mul_le_mul_of_nonneg_left hy (add_nonneg zero_le_one (mul_nonneg (by linarith) hgamma.le))
  linarith

/-- `e.assump.lower.modified` on the plateau: the subtracted `F`-term is not
even needed, and the increment term is absorbed by the `E gamma` slack. -/
private lemma lower_binder_of_plateau
    {nu gamma E x y a t : ℝ}
    (hnu : 0 < nu) (hgamma : 0 < gamma) (hgamma128 : gamma ≤ 1 / 128) (hE : 1 ≤ E)
    (hx : nu ≤ x) (hy : y ≤ (1 + gamma ^ 2 / 2) * nu) (hynu : nu ≤ y)
    (ha' : a ≤ 243 / 4 * gamma ^ 2) (ht : 0 ≤ t) :
    (1 - E * gamma) * y + a * x - t ≤ x := by
  have hxpos : 0 < x := lt_of_lt_of_le hnu hx
  have hEg0 : 0 ≤ E * gamma := mul_nonneg (by linarith) hgamma.le
  have hsq : gamma ^ 2 ≤ gamma / 128 :=
    gamma_sq_le_one_twenty_eighth hgamma hgamma128
  have hEg : gamma ≤ E * gamma := le_mul_of_one_le_left hgamma.le hE
  have h1 : a * x ≤ 243 / 4 * gamma ^ 2 * x :=
    mul_le_mul_of_nonneg_right ha' hxpos.le
  have h2 : E * gamma * nu ≤ E * gamma * y := mul_le_mul_of_nonneg_left hynu hEg0
  have h3 : (1 - E * gamma) * y ≤ (1 + gamma ^ 2 / 2) * nu - E * gamma * nu := by
    linarith only [hy, h2]
  have h5 : 245 / 4 * gamma ^ 2 ≤ E * gamma := by linarith
  have h6 : (0 : ℝ) ≤ 1 - 243 / 4 * gamma ^ 2 := by
    linarith only [hsq, hgamma128]
  have h7 : nu * (1 - 243 / 4 * gamma ^ 2) ≤ x * (1 - 243 / 4 * gamma ^ 2) :=
    mul_le_mul_of_nonneg_right hx h6
  have h8 : 0 ≤ nu * (E * gamma - 245 / 4 * gamma ^ 2) :=
    mul_nonneg hnu.le (by linarith)
  nlinarith only [h1, h3, h7, h8, ht]

/-! ## The two binders below the landmark -/

/-- **The uncovered range of the recurrence, discharged from the base-case
plateau.**

Let `s` satisfy the all-scale envelope `e.small.scale.bound`, which
`p.base.case` supplies unconditionally for the genuine diffusivity
(`e.plateau.region.bound`).  Let `(n, m)` be admissible for
`l.integrate.approx.recurrence`, i.e. `n ≤ m` and `(m: ℝ) ≤ (n: ℝ) + c_star
gamma⁻¹`, and suppose the *lower* endpoint `n` meets the defining threshold of
`m**` (`e.mstarstar`): `3 ^ (2 gamma n) ≤ nu ^ 2 gamma ^ 3 / (2 (log 3) c+)`.

Then both binders of `l.integrate.approx.recurrence` hold at `(n, m)`, for any
`E ≥ 1` and any `F ≥ 0`.  The approximate recurrence formula is not used.

The proof is quantitative: on this range `s_n ≤ (1 + gamma²/2) nu`,
`s_m ≤ (1 + 81 gamma²/2) nu` and `A_{n,m} ≤ (243/4) nu² gamma²`, all three
`O(gamma^2)`, while the binders' slack is `E gamma ≥ gamma`. -/
theorem recurrence_binders_of_below_landmark
    {nu cstar cstarPlus gamma E F : ℝ} {s : ℤ → ℝ} {n m : ℤ}
    (hnu : 0 < nu) (hcstar : 0 < cstar) (hcstar32 : cstar ≤ 3 / 2)
    (hcc : cstar ≤ cstarPlus) (hgamma : 0 < gamma) (hgamma128 : gamma ≤ 1 / 128)
    (hE : 1 ≤ E) (hF : 0 ≤ F)
    (hsmall : ∀ k : ℤ, nu ≤ s k ∧
      s k ≤ (1 + (nu ^ 2)⁻¹ * cstarPlus * gamma⁻¹ *
        (3 : ℝ) ^ (2 * gamma * (k : ℝ))) * nu)
    (hfloor : (3 : ℝ) ^ (2 * gamma * (n : ℝ)) ≤
      nu ^ 2 * gamma ^ 3 / (2 * Real.log 3 * cstarPlus))
    (hnm : n ≤ m) (hrange : (m : ℝ) ≤ (n : ℝ) + cstar * gamma⁻¹) :
    (s m ≤ (1 + E * gamma) * s n + recurrenceIncrement cstar gamma n m * (s n)⁻¹) ∧
      ((1 - E * gamma) * s n +
            recurrenceIncrement cstar gamma n m * ((s n)⁻¹) ^ 2 * s m -
          F * ((m : ℝ) - (n : ℝ)) ^ 2 * ((s n)⁻¹) ^ 4 * s m *
            (3 : ℝ) ^ (4 * gamma * (m : ℝ))
        ≤ s m) := by
  have hcp : 0 < cstarPlus := lt_of_lt_of_le hcstar hcc
  have hginv : (0 : ℝ) < gamma⁻¹ := inv_pos.mpr hgamma
  have hL : (1 : ℝ) ≤ Real.log 3 := by
    have hexp : Real.exp 1 ≤ 3 :=
      le_of_lt (lt_of_lt_of_le Real.exp_one_lt_d9 (by norm_num))
    exact (Real.le_log_iff_exp_le (by norm_num)).mpr hexp
  have hgnpos : (0 : ℝ) < (3 : ℝ) ^ (2 * gamma * (n : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hgmpos : (0 : ℝ) < (3 : ℝ) ^ (2 * gamma * (m : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hd0' : (m : ℝ) - (n : ℝ) ≤ cstar * gamma⁻¹ := by linarith
  -- the exponent gap costs at most `3 ^ 4 = 81`
  have hexpgap : 2 * gamma * ((m : ℝ) - (n : ℝ)) ≤ 4 := by
    have h1 : gamma * ((m : ℝ) - (n : ℝ)) ≤ gamma * (cstar * gamma⁻¹) :=
      mul_le_mul_of_nonneg_left hd0' hgamma.le
    have h2 : gamma * (cstar * gamma⁻¹) = cstar := by field_simp
    rw [h2] at h1
    linarith
  have hgmn : (3 : ℝ) ^ (2 * gamma * (m : ℝ)) ≤ 81 * (3 : ℝ) ^ (2 * gamma * (n : ℝ)) := by
    have hsplit : (3 : ℝ) ^ (2 * gamma * (m : ℝ))
        = (3 : ℝ) ^ (2 * gamma * (n : ℝ)) *
            (3 : ℝ) ^ (2 * gamma * ((m : ℝ) - (n : ℝ))) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    have h81 : (3 : ℝ) ^ (4 : ℝ) = 81 := by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      norm_num
    have hpow : (3 : ℝ) ^ (2 * gamma * ((m : ℝ) - (n : ℝ))) ≤ 81 := by
      have hmono :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hexpgap
      rw [h81] at hmono
      exact hmono
    calc (3 : ℝ) ^ (2 * gamma * (m : ℝ))
        = (3 : ℝ) ^ (2 * gamma * (n : ℝ)) *
            (3 : ℝ) ^ (2 * gamma * ((m : ℝ) - (n : ℝ))) := hsplit
      _ ≤ (3 : ℝ) ^ (2 * gamma * (n : ℝ)) * 81 :=
          mul_le_mul_of_nonneg_left hpow hgnpos.le
      _ = 81 * (3 : ℝ) ^ (2 * gamma * (n : ℝ)) := by ring
  -- the `m**` threshold, cleared of its denominator
  have hfl : 2 * Real.log 3 * cstarPlus * (3 : ℝ) ^ (2 * gamma * (n : ℝ))
      ≤ nu ^ 2 * gamma ^ 3 := by
    rw [le_div_iff₀ (by positivity)] at hfloor
    linarith
  obtain ⟨hPn, hPm, hA⟩ :=
    plateau_pair_bounds hnu hcstar hcstar32 hcc hgamma hL hgnpos hgmpos hgmn hd0' hfl
  obtain ⟨hn1, hn2⟩ := hsmall n
  obtain ⟨hm1, hm2⟩ := hsmall m
  have hsnpos : 0 < s n := lt_of_lt_of_le hnu hn1
  have hsmpos : 0 < s m := lt_of_lt_of_le hnu hm1
  have hsnup : s n ≤ (1 + gamma ^ 2 / 2) * nu :=
    hn2.trans (mul_le_mul_of_nonneg_right (by linarith) hnu.le)
  have hsmup : s m ≤ (1 + 81 * gamma ^ 2 / 2) * nu :=
    hm2.trans (mul_le_mul_of_nonneg_right (by linarith) hnu.le)
  -- the increment, and the increment divided by `s_n ^ 2`
  have hAnn : 0 ≤ recurrenceIncrement cstar gamma n m :=
    Internal.recurrenceIncrement_nonneg hcstar.le n m
  have hAle : recurrenceIncrement cstar gamma n m ≤ 243 / 4 * nu ^ 2 * gamma ^ 2 := by
    refine le_trans (Internal.recurrenceIncrement_le_count hgamma hcstar.le hnm) ?_
    simpa only [geometricTerm] using hA
  have hinvle : (s n)⁻¹ ≤ nu⁻¹ := inv_anti₀ hnu hn1
  have hinvpos : (0 : ℝ) < (s n)⁻¹ := inv_pos.mpr hsnpos
  have hinvsq : ((s n)⁻¹) ^ 2 ≤ (nu ^ 2)⁻¹ := by
    calc ((s n)⁻¹) ^ 2 ≤ (nu⁻¹) ^ 2 := by
          exact pow_le_pow_left₀ hinvpos.le hinvle 2
      _ = (nu ^ 2)⁻¹ := by rw [inv_pow]
  have hAsq : recurrenceIncrement cstar gamma n m * ((s n)⁻¹) ^ 2
      ≤ 243 / 4 * gamma ^ 2 := by
    have hstep : recurrenceIncrement cstar gamma n m * ((s n)⁻¹) ^ 2
        ≤ (243 / 4 * nu ^ 2 * gamma ^ 2) * (nu ^ 2)⁻¹ := by
      refine mul_le_mul hAle hinvsq (by positivity) (by positivity)
    have hval : (243 / 4 * nu ^ 2 * gamma ^ 2) * (nu ^ 2)⁻¹ = 243 / 4 * gamma ^ 2 := by
      field_simp
    linarith [hstep, hval.le, hval.ge]
  constructor
  · exact upper_binder_of_plateau hnu hgamma hgamma128 hE hsmup hn1
      (mul_nonneg hAnn hinvpos.le)
  · refine lower_binder_of_plateau hnu hgamma hgamma128 hE hm1 hsnup hn1 hAsq ?_
    have h4 : (0 : ℝ) < (3 : ℝ) ^ (4 * gamma * (m : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have := mul_nonneg
      (mul_nonneg
        (mul_nonneg (mul_nonneg hF (sq_nonneg ((m : ℝ) - (n : ℝ))))
          (pow_nonneg hinvpos.le 4)) hsmpos.le) h4.le
    exact this

/-! ## The integration lemma from a floored recurrence family -/

/-- **`l.integrate.approx.recurrence` from an `m**`-floored recurrence.**

Same conclusion as
`Provider.Diffusivity.RecurrenceIntegration.integrate_approx_recurrence_cstarPlus`,
but the two recurrence families are only required at pairs whose lower endpoint
lies at or above a scale `mss` meeting the `m**` threshold `hmss` -- which is
precisely the range that `l.approximate.recurrence.formula` delivers.  Below
`mss` the binders are supplied by `recurrence_binders_of_below_landmark` from
the plateau envelope `hsmall` alone.

The `gamma ≤ 1/128` smallness needed there is *derived* from the
`gamma`-threshold that `integrate_approx_recurrence_cstarPlus` already imposes;
it is not an extra hypothesis.

There is no second integration engine: the final step is a call to the proved
`integrate_approx_recurrence_cstarPlus`. -/
theorem integrate_approx_recurrence_of_landmark_floored
    {nu cstar cstarPlus gamma E F : ℝ} {m0 mss : ℤ} {s : ℤ → ℝ}
    (hnu : 0 < nu) (hcstar : 0 < cstar) (hcstar32 : cstar ≤ 3 / 2)
    (hcc : cstar ≤ cstarPlus) (hgamma : 0 < gamma) (hE : 1 ≤ E) (hF : 1 ≤ F)
    (hsmall : ∀ k : ℤ, nu ≤ s k ∧
      s k ≤ (1 + (nu ^ 2)⁻¹ * cstarPlus * gamma⁻¹ *
        (3 : ℝ) ^ (2 * gamma * (k : ℝ))) * nu)
    (hmss : (3 : ℝ) ^ (2 * gamma * (mss : ℝ)) ≤
      nu ^ 2 * gamma ^ 3 / (2 * Real.log 3 * cstarPlus))
    (hupper : ∀ n m : ℤ, mss ≤ n → m ≤ m0 → n ≤ m →
      (m : ℝ) ≤ (n : ℝ) + cstar * gamma⁻¹ →
      s m ≤ (1 + E * gamma) * s n + recurrenceIncrement cstar gamma n m * (s n)⁻¹)
    (hlower : ∀ n m : ℤ, mss ≤ n → m ≤ m0 → n ≤ m →
      (m : ℝ) ≤ (n : ℝ) + cstar * gamma⁻¹ →
      (1 - E * gamma) * s n +
            recurrenceIncrement cstar gamma n m * ((s n)⁻¹) ^ 2 * s m -
          F * ((m : ℝ) - (n : ℝ)) ^ 2 * ((s n)⁻¹) ^ 4 * s m *
            (3 : ℝ) ^ (4 * gamma * (m : ℝ))
        ≤ s m) :
    gamma ≤ (recurrenceIntegrationConstant
      * (E * (1 + (cstar ^ 2)⁻¹ * F + (cstar ^ 2)⁻¹ * cstarPlus)))⁻¹ →
      ∀ m : ℤ, m ≤ m0 →
        |s m - Real.sqrt
            (nu ^ 2 + cstar * gamma⁻¹ * (3 : ℝ) ^ (2 * gamma * (m : ℝ)))|
          ≤ recurrenceIntegrationConstant
              * Real.sqrt
                  (E * (1 + (cstar ^ 2)⁻¹ * F + (cstar ^ 2)⁻¹ * cstarPlus) * gamma) *
                s m := by
  intro hthr
  have hcp : 0 < cstarPlus := lt_of_lt_of_le hcstar hcc
  have hF0 : (0 : ℝ) ≤ F := by linarith
  -- the composite constant is at least one, hence `gamma ≤ 1/128`
  have hbracket : (1 : ℝ) ≤ 1 + (cstar ^ 2)⁻¹ * F + (cstar ^ 2)⁻¹ * cstarPlus := by
    have h1 : (0 : ℝ) ≤ (cstar ^ 2)⁻¹ * F := by positivity
    have h2 : (0 : ℝ) ≤ (cstar ^ 2)⁻¹ * cstarPlus :=
      mul_nonneg (inv_nonneg.mpr (sq_nonneg cstar)) hcp.le
    linarith
  have hTheta : (1 : ℝ) ≤ E * (1 + (cstar ^ 2)⁻¹ * F + (cstar ^ 2)⁻¹ * cstarPlus) := by
    exact one_le_mul_of_one_le_of_one_le hE hbracket
  have hprod : (128 : ℝ) ≤ recurrenceIntegrationConstant
      * (E * (1 + (cstar ^ 2)⁻¹ * F + (cstar ^ 2)⁻¹ * cstarPlus)) := by
    have hC : recurrenceIntegrationConstant = 320000000008 :=
      recurrenceIntegrationConstant_eq
    calc
      (128 : ℝ) ≤ recurrenceIntegrationConstant := by rw [hC]; norm_num
      _ ≤ recurrenceIntegrationConstant *
          (E * (1 + (cstar ^ 2)⁻¹ * F + (cstar ^ 2)⁻¹ * cstarPlus)) :=
        le_mul_of_one_le_right (by rw [hC]; norm_num) hTheta
  have hgamma128 : gamma ≤ 1 / 128 := by
    refine hthr.trans ?_
    have := inv_anti₀ (by norm_num : (0 : ℝ) < 128) hprod
    simpa only [one_div] using this
  -- fill both families: above `mss` by hypothesis, below `mss` from the plateau
  have hfloor_of_le : ∀ n : ℤ, n ≤ mss →
      (3 : ℝ) ^ (2 * gamma * (n : ℝ)) ≤
        nu ^ 2 * gamma ^ 3 / (2 * Real.log 3 * cstarPlus) := by
    intro n hn
    refine le_trans ?_ hmss
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) ?_
    have hnR : (n : ℝ) ≤ (mss : ℝ) := by exact_mod_cast hn
    exact mul_le_mul_of_nonneg_left hnR (mul_nonneg (by norm_num) hgamma.le)
  have hupper' : ∀ n m : ℤ, m ≤ m0 → n ≤ m →
      (m : ℝ) ≤ (n : ℝ) + cstar * gamma⁻¹ →
      s m ≤ (1 + E * gamma) * s n +
        recurrenceIncrement cstar gamma n m * (s n)⁻¹ := by
    intro n m hm hnm hr
    rcases le_or_gt mss n with hn | hn
    · exact hupper n m hn hm hnm hr
    · exact (recurrence_binders_of_below_landmark hnu hcstar hcstar32 hcc hgamma
        hgamma128 hE hF0 hsmall (hfloor_of_le n (le_of_lt hn))
        hnm hr).1
  have hlower' : ∀ n m : ℤ, m ≤ m0 → n ≤ m →
      (m : ℝ) ≤ (n : ℝ) + cstar * gamma⁻¹ →
      (1 - E * gamma) * s n +
            recurrenceIncrement cstar gamma n m * ((s n)⁻¹) ^ 2 * s m -
          F * ((m : ℝ) - (n : ℝ)) ^ 2 * ((s n)⁻¹) ^ 4 * s m *
            (3 : ℝ) ^ (4 * gamma * (m : ℝ))
        ≤ s m := by
    intro n m hm hnm hr
    rcases le_or_gt mss n with hn | hn
    · exact hlower n m hn hm hnm hr
    · exact (recurrence_binders_of_below_landmark hnu hcstar hcstar32 hcc hgamma
        hgamma128 hE hF0 hsmall (hfloor_of_le n (le_of_lt hn))
        hnm hr).2
  exact integrate_approx_recurrence_cstarPlus hnu hcstar hcstar32 hcc hgamma hE hF hsmall
    hupper' hlower' hthr

/-! ## At the genuine diffusivity and the genuine landmark -/

variable {d : ℕ}

/-- `c_star ≤ c+` for the genuine constants: `J4`'s directional constant never
exceeds the normalized Frobenius origin mass, because the dimension is at
least two. -/
theorem cstar_le_cstarPlus (M : ABKModel d) :
    Disorder.cstar M ≤ Disorder.cstarPlus M := by
  have hd : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast M.shellPrefix.dimension
  have hpos : 0 < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hdim := Disorder.dim_mul_cstar_le_cstarPlus M
  calc
    Disorder.cstar M ≤ 2 * Disorder.cstar M :=
      le_mul_of_one_le_left hpos.le (by norm_num)
    _ ≤ (d : ℝ) * Disorder.cstar M :=
      mul_le_mul_of_nonneg_right hd hpos.le
    _ ≤ Disorder.cstarPlus M := hdim

/-- **The seam, at the genuine carriers.**

`l.integrate.approx.recurrence` for the running diffusivity `sigmaBar`, from a
recurrence family supplied only on `mStarStar M ≤ n` -- exactly the range that
`l.approximate.recurrence.formula` delivers.

The envelope is the proved `annealedPlateau_smallScaleBound`
(`e.plateau.region.bound`), the landmark threshold is the proved
`Provider.Scales.rpow_mStarStar_le` (`e.mstarstar`), and `c_star ≤ 3/2` is the
proved `Provider.Disorder.cstar_le_three_halves`; none of them is assumed.

**This theorem is conditional on `hupper`/`hlower` and claims no node status.**
Those two families are the conclusion of `l.approximate.recurrence.formula`,
which this repository does not prove. -/
theorem sigmaBar_integrate_approx_recurrence_of_mStarStar_floored
    (M : ABKModel d) {m0 : ℤ} {E F : ℝ} (hE : 1 ≤ E) (hF : 1 ≤ F)
    (hupper : ∀ n m : ℤ, mStarStar M ≤ n → m ≤ m0 → n ≤ m →
      (m : ℝ) ≤ (n : ℝ) + Disorder.cstar M * M.gamma⁻¹ →
      (Annealed.sigmaBar M m : ℝ) ≤
        (1 + E * M.gamma) * (Annealed.sigmaBar M n : ℝ) +
          recurrenceIncrement (Disorder.cstar M) M.gamma n m *
            ((Annealed.sigmaBar M n : ℝ))⁻¹)
    (hlower : ∀ n m : ℤ, mStarStar M ≤ n → m ≤ m0 → n ≤ m →
      (m : ℝ) ≤ (n : ℝ) + Disorder.cstar M * M.gamma⁻¹ →
      (1 - E * M.gamma) * (Annealed.sigmaBar M n : ℝ) +
            recurrenceIncrement (Disorder.cstar M) M.gamma n m *
              (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 2 * (Annealed.sigmaBar M m : ℝ) -
          F * ((m : ℝ) - (n : ℝ)) ^ 2 * (((Annealed.sigmaBar M n : ℝ))⁻¹) ^ 4 *
            (Annealed.sigmaBar M m : ℝ) * (3 : ℝ) ^ (4 * M.gamma * (m : ℝ))
        ≤ (Annealed.sigmaBar M m : ℝ)) :
    M.gamma ≤ (recurrenceIntegrationConstant
      * (E * (1 + (Disorder.cstar M ^ 2)⁻¹ * F +
          (Disorder.cstar M ^ 2)⁻¹ * Disorder.cstarPlus M)))⁻¹ →
      ∀ m : ℤ, m ≤ m0 →
        |(Annealed.sigmaBar M m : ℝ) - Real.sqrt
            (M.nu ^ 2 + Disorder.cstar M * M.gamma⁻¹ *
              (3 : ℝ) ^ (2 * M.gamma * (m : ℝ)))|
          ≤ recurrenceIntegrationConstant
              * Real.sqrt
                  (E * (1 + (Disorder.cstar M ^ 2)⁻¹ * F +
                    (Disorder.cstar M ^ 2)⁻¹ * Disorder.cstarPlus M) * M.gamma) *
                (Annealed.sigmaBar M m : ℝ) :=
  integrate_approx_recurrence_of_landmark_floored M.nu_pos
    (Disorder.cstar_characterization M).1
    (Provider.Disorder.cstar_le_three_halves M) (cstar_le_cstarPlus M)
    M.shellPrefix.gamma_pos hE hF
    (annealedPlateau_smallScaleBound M)
    (Provider.Scales.rpow_mStarStar_le M) hupper hlower

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence
