/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.DescendantLattice
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.EightEss
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.Step1
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.Step3Producers
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.UglyChain

/-!
# ClauseOne

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The clause-(i) assembly of the annular decomposition

ABK26, Section 4.1, the proof of `p.mathcalE.annular.decomp`, assembled end to
end at the **literal flux-corrected carrier** `Support.fluxCorrectedError`.

The chain composed here is the manuscript's own:

```
  the (infinity,2) opening  e.mathcal.E.eight.ess.bound      (EightEss)
   -> the two J-sums (field leg + transposed leg)   (BlockResponse/DescendantLattice)
   -> the annular cover                             (Step1, IsAnnularDecompPre)
   -> the per-cube ugly estimate                    (UglyChain, IsUglyJEstimate)
   -> e.mathcalE.annular.decomp.pre.zero            (Resum.preZero_of_pre_and_ugly)
   -> the three Step-3 resummations                 (Step3Producers)
   -> e.mathcalE.annular.decomp                     (Step3.annularDecomp_of_preZero)
```

## The two structural moves made explicit here

* **The transposed leg.**  The manuscript discharges the second `J`-sum by
  asserting that "the right side of `e.mathcalE.annular.decomp.pre.zero` does
  not change if we replace the field with its transpose".  Here the two legs
  are run through the *same* composite with the *same* five right-hand
  families, `sig`, `L2f`, `gradNf`, `gradTailSq`; each of the five terms is
  therefore literally the same expression for the two legs, and the assertion
  is reduced to its one genuine content, the transposed leg's per-cube ugly
  estimate.
* `pre.zero`'s fourth term carries `grad(k_L - k_{n-2})` while the Step-3
  resummation display carries `grad(k_m - k_{n-2})`; the manuscript substitutes
  silently.
-/

namespace Algsuperdiff.Section4.Provider.Annular

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable

noncomputable section

variable {d : ℕ}

/-! ## Part A -- the two arithmetic bridges of the opening -/

/-- **The `c_{2s}` discount is linear in `s`.**  `1 - 3^(-2s) <= 4 s` for
`s >= 0`, from `1 + y <= exp y` and `log 3 <= 2`.  This is what converts the
normalizing factor `c_{2s}` of the `(infinity,2)` opening into the prefactor
`C s` of the first conclusion term. -/
theorem one_sub_three_rpow_neg_two_le {s : ℝ} (hs0 : 0 ≤ s) :
    1 - (3 : ℝ) ^ (-(2 * s)) ≤ 4 * s := by
  have hlog : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    linarith only [h]
  have hE : (3 : ℝ) ^ (-(2 * s)) = Real.exp (-(2 * s * Real.log 3)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hexp : 1 - 2 * s * Real.log 3 ≤ Real.exp (-(2 * s * Real.log 3)) := by
    linarith only [Real.add_one_le_exp (-(2 * s * Real.log 3))]
  have hbound : 2 * s * Real.log 3 ≤ 4 * s := by
    have h := mul_le_mul_of_nonneg_left hlog (by linarith only [hs0] : (0 : ℝ) ≤ 2 * s)
    linarith only [h]
  rw [hE]
  linarith only [hexp, hbound]

/-- **The scale-index bridge.**  The `(infinity,2)` opening sums over the depth
`l` in `N`; every downstream module sums over the scale `n <= m`.  Under
`n = m - l` the two weighted sums agree. -/
theorem tsum_guard_eq_tsum_shell (m : ℤ) (s : ℝ) (J : ℤ → ℝ) :
    ∑' n : ℤ, (if n ≤ m then (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ))) * J n else 0)
      = ∑' l : ℕ, (3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * J (m - (l : ℤ)) := by
  rw [tsum_int_guard_le]
  refine tsum_congr fun i => ?_
  have hcast : ((m - (m - (i : ℤ)) : ℤ) : ℝ) = (i : ℝ) := by push_cast; ring
  rw [hcast, show -(2 * s * (i : ℝ)) = -(2 * s) * (i : ℝ) from by ring]

/-! ## Part B -- the `m`-vs-`L` tail routing -/

/-- `e.mathcalE.annular.decomp.pre.zero`'s fourth term carries the gradient of `k_L
- k_{n-2}` while the Step-3 resummation display carries the gradient of `k_m -
k_{n-2}`; the manuscript substitutes one for the other without comment.
Honestly `k_L - k_{n-2} = (k_m - k_{n-2}) + (k_L - k_m)`, and the triangle
inequality leaves a `k > m` tail.

This lemma states the routing: if the per-cube estimate holds with the tail
*included* in the fourth slot, at a tail budget `Ktail * gradM` proportional to
the fifth term's own content, then it holds in the clean five-term shape at the
constant `(1 + Ktail) C`.  The move is available because on the annular region
`n <= j - 1 <= m - 1` the fifth term's weight `w_gamma = 3^((s+gamma)(m-n))`
dominates the fourth's `w = 3^(s(m-n))`, so the tail is absorbed by the term
whose content is exactly the `k >= m` object. -/
theorem isUglyJEstimate_routeTail
    {Jval E2 sigDiff L2 gradN gradM cstar gam w wgam C Ktail : ℝ}
    (hC0 : 0 ≤ C) (hcstar0 : 0 ≤ cstar⁻¹) (hgam0 : 0 ≤ gam)
    (hE20 : 0 ≤ E2) (hsig0 : 0 ≤ sigDiff) (hL20 : 0 ≤ L2) (hgradN0 : 0 ≤ gradN)
    (hgradM0 : 0 ≤ gradM) (hKtail0 : 0 ≤ Ktail) (hw0 : 0 ≤ w) (hw : w ≤ wgam)
    (h : IsUglyJEstimate Jval E2 sigDiff L2 (gradN + Ktail * gradM) gradM cstar gam
      w wgam C) :
    IsUglyJEstimate Jval E2 sigDiff L2 gradN gradM cstar gam w wgam
      ((1 + Ktail) * C) := by
  unfold IsUglyJEstimate at h ⊢
  have hCle : C ≤ (1 + Ktail) * C := by
    have hKC : (0 : ℝ) ≤ Ktail * C := mul_nonneg hKtail0 hC0
    linarith only [hKC]
  have hbase : (0 : ℝ) ≤ C * cstar⁻¹ * gam :=
    mul_nonneg (mul_nonneg hC0 hcstar0) hgam0
  -- the tail moves from the fourth weight to the fifth
  have hmove : C * cstar⁻¹ * gam * w * (Ktail * gradM)
      ≤ C * cstar⁻¹ * gam * wgam * (Ktail * gradM) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw hbase)
      (mul_nonneg hKtail0 hgradM0)
  -- the first four terms only grow when `C` becomes `(1 + Ktail) C`
  have hT1 : C * w * E2 ≤ (1 + Ktail) * C * w * E2 := by
    calc C * w * E2 = C * (w * E2) := by ring
      _ ≤ (1 + Ktail) * C * (w * E2) :=
          mul_le_mul_of_nonneg_right hCle (mul_nonneg hw0 hE20)
      _ = (1 + Ktail) * C * w * E2 := by ring
  have hT2 : C * w * sigDiff ≤ (1 + Ktail) * C * w * sigDiff := by
    calc C * w * sigDiff = C * (w * sigDiff) := by ring
      _ ≤ (1 + Ktail) * C * (w * sigDiff) :=
          mul_le_mul_of_nonneg_right hCle (mul_nonneg hw0 hsig0)
      _ = (1 + Ktail) * C * w * sigDiff := by ring
  have hT3 : C * cstar⁻¹ * gam * w * L2
      ≤ (1 + Ktail) * C * cstar⁻¹ * gam * w * L2 := by
    calc C * cstar⁻¹ * gam * w * L2 = C * (cstar⁻¹ * gam * w * L2) := by ring
      _ ≤ (1 + Ktail) * C * (cstar⁻¹ * gam * w * L2) :=
          mul_le_mul_of_nonneg_right hCle
            (mul_nonneg (mul_nonneg (mul_nonneg hcstar0 hgam0) hw0) hL20)
      _ = (1 + Ktail) * C * cstar⁻¹ * gam * w * L2 := by ring
  have hT4 : C * cstar⁻¹ * gam * w * gradN
      ≤ (1 + Ktail) * C * cstar⁻¹ * gam * w * gradN := by
    calc C * cstar⁻¹ * gam * w * gradN = C * (cstar⁻¹ * gam * w * gradN) := by ring
      _ ≤ (1 + Ktail) * C * (cstar⁻¹ * gam * w * gradN) :=
          mul_le_mul_of_nonneg_right hCle
            (mul_nonneg (mul_nonneg (mul_nonneg hcstar0 hgam0) hw0) hgradN0)
      _ = (1 + Ktail) * C * cstar⁻¹ * gam * w * gradN := by ring
  have hT5 : C * cstar⁻¹ * gam * wgam * gradM
        + C * cstar⁻¹ * gam * wgam * (Ktail * gradM)
      = (1 + Ktail) * C * cstar⁻¹ * gam * wgam * gradM := by ring
  have hexpand : C * cstar⁻¹ * gam * w * (gradN + Ktail * gradM)
      = C * cstar⁻¹ * gam * w * gradN
        + C * cstar⁻¹ * gam * w * (Ktail * gradM) := by ring
  rw [hexpand] at h
  linarith only [h, hmove, hT1, hT2, hT3, hT4, hT5]

/-! ## Part C -- one leg of the opening, taken to the `pre.zero` shape -/

/-- **One leg of the opening, taken to the `pre.zero` shape.**

Given

* `hess` -- the leg's contribution to the `(infinity,2)` opening, in the shape
  `eightEss_of_blockResponse_le` produces it;
* `hpreA` -- the Step-1 annular cover at the leg's grid family;
* `hugly` -- the per-cube ugly estimate at the manuscript's weights;
* the four summability facts of `preZero_of_pre_and_ugly`,

the leg satisfies the five-term `e.mathcalE.annular.decomp.pre.zero` shape.  The
work done here beyond `preZero_of_pre_and_ugly` is the conversion of the
`c_{2s}` prefactor into `4 Cbf s` and the scale-index bridge. -/
theorem preZero_leg {s gamma cstar Cbf C₁ C₂ C gradM Ecal2 : ℝ} {m : ℤ}
    {Jleg : ℤ → ℝ} {Jann E2 L2f gradNf : ℤ → ℤ → ℝ} {sig : ℤ → ℝ}
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hgamma0 : 0 ≤ gamma) (hsg : 8 * gamma ≤ s)
    (hcstar : 0 < cstar) (hCbf : 0 ≤ Cbf) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hgradM : 0 ≤ gradM)
    (hJleg0 : ∀ n, 0 ≤ Jleg n)
    (hJann0 : ∀ j n, 0 ≤ Jann j n)
    (hE0 : ∀ j n, 0 ≤ E2 j n) (hsig0 : ∀ n, 0 ≤ sig n)
    (hL20 : ∀ j n, 0 ≤ L2f j n) (hgrad0 : ∀ j n, 0 ≤ gradNf j n)
    (hess : Ecal2 ≤ Cbf * (1 - (3 : ℝ) ^ (-(2 * s)))
      * ∑' l : ℕ, (3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * Jleg (m - (l : ℤ)))
    (hpreA : IsAnnularDecompPre s m Jleg Jann C₁)
    (hugly : ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
      IsUglyJEstimate (Jann j n) (E2 j n) (sig n) (L2f j n) (gradNf j n) gradM
        cstar gamma ((3 : ℝ) ^ (s * ((m - n : ℤ) : ℝ)))
        ((3 : ℝ) ^ ((s + gamma) * ((m - n : ℤ) : ℝ))) C₂)
    (hsumE :
      Summable (annFam m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * E2 j n)))
    (hsumS :
      Summable (annFam m (fun _ n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * sig n)))
    (hsumL :
      Summable (annFam m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * L2f j n)))
    (hsumG :
      Summable (annFam m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * gradNf j n)))
    (hCge : 24 * Cbf * C₁ * C₂ ≤ C) :
    Ecal2
      ≤ C * s * annDouble m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * E2 j n)
        + C * s * annDouble m (fun _ n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * sig n)
        + C * cstar⁻¹ * gamma * s
            * annDouble m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * L2f j n)
        + C * cstar⁻¹ * gamma * s
            * annDouble m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * gradNf j n)
        + C * cstar⁻¹ * (s ^ 2)⁻¹ * gamma * gradM := by
  have hS0 : (0 : ℝ) ≤ ∑' l : ℕ, (3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * Jleg (m - (l : ℤ)) :=
    tsum_nonneg fun l => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hJleg0 _)
  have hcoef : Cbf * (1 - (3 : ℝ) ^ (-(2 * s))) ≤ 4 * Cbf * s := by
    have h := mul_le_mul_of_nonneg_left (one_sub_three_rpow_neg_two_le hs0.le) hCbf
    linarith only [h]
  have hess' : Ecal2 ≤ 4 * Cbf * s
      * ∑' n : ℤ, (if n ≤ m then
          (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ))) * Jleg n else 0) := by
    rw [tsum_guard_eq_tsum_shell]
    have h := mul_le_mul_of_nonneg_right hcoef hS0
    linarith only [hess, h]
  have hCge' : 6 * (4 * Cbf) * C₁ * C₂ ≤ C := by
    have hid : 6 * (4 * Cbf) * C₁ * C₂ = 24 * Cbf * C₁ * C₂ := by ring
    linarith only [hCge, hid]
  exact preZero_of_pre_and_ugly (Cess := 4 * Cbf) hs0 hs1 hgamma0 hsg hcstar
    (by linarith only [hCbf]) hC₁ hC₂ hgradM hJann0 hE0 hsig0 hL20 hgrad0 hess'
    hpreA (fun j n hj hn => hugly j n hj hn) hsumE hsumS hsumL hsumG hCge'

/-! ## Part D -- the four-term shape with separated constants

The Step-3 four-term shape carries ONE constant across all four right-hand
terms. -/

/-- ```
Ecal2 <= C s G2 + C s^(-3) cstar^(-4) Rem
         + C s^(-2) cstar^(-1) gamma G1a + C s^(-2) cstar^(-1) gamma G1b .
```

A naming convenience inside this provider module; it is not a source-facing
declaration and closes no node. -/
def IsClauseOneBound (Ecal2 G2 Rem G1a G1b s cstar gamma C : ℝ) : Prop :=
  Ecal2 ≤ C * s * G2
    + C * (s⁻¹ ^ (3 : ℕ)) * (cstar⁻¹ ^ (4 : ℕ)) * Rem
    + C * (s⁻¹ ^ (2 : ℕ)) * cstar⁻¹ * gamma * G1a
    + C * (s⁻¹ ^ (2 : ℕ)) * cstar⁻¹ * gamma * G1b

/-- **The Step-3 regrouping at separated constants.**  The regrouping in which
the `sigma-bar` slot's extra `s^(-1)` is carried by the *second term's exponent*
rather than by the shared constant, so the output constant is `s`-free. -/
theorem clauseOneBound_of_preZero
    {Ecal2 G2raw SigSum GradSum L2Sum Gm Rem G1a G1b s cstar gamma D Csig Cgrad
      CL2 C : ℝ}
    (hs0 : 0 < s) (hcstar : 0 < cstar) (hgamma : 0 ≤ gamma) (hD : 0 ≤ D)
    (hG2raw : 0 ≤ G2raw) (hRem : 0 ≤ Rem) (hG1a0 : 0 ≤ G1a) (hG1b0 : 0 ≤ G1b)
    (hpre : Ecal2 ≤ D * s * G2raw + D * s * SigSum
      + D * cstar⁻¹ * gamma * s * GradSum + D * cstar⁻¹ * gamma * s * L2Sum
      + D * cstar⁻¹ * (s ^ 2)⁻¹ * gamma * Gm)
    (hsig : SigSum ≤ Csig * s⁻¹ * (s ^ 3)⁻¹ * (cstar ^ 4)⁻¹ * Rem)
    (hgrad : GradSum ≤ Cgrad * (s ^ 3)⁻¹ * G1b)
    (hL2 : L2Sum ≤ CL2 * (s ^ 3)⁻¹ * G1b)
    (hGm : Gm ≤ G1a)
    (hC1 : D ≤ C) (hC2 : D * Csig ≤ C) (hC3 : D * (Cgrad + CL2) ≤ C) :
    IsClauseOneBound Ecal2 G2raw Rem G1a G1b s cstar gamma C := by
  unfold IsClauseOneBound
  have hs' : s ≠ 0 := ne_of_gt hs0
  have hc' : cstar ≠ 0 := ne_of_gt hcstar
  have hcsinv : (0 : ℝ) ≤ cstar⁻¹ := inv_nonneg.2 hcstar.le
  have hpref : (0 : ℝ) ≤ D * cstar⁻¹ * gamma * s :=
    mul_nonneg (mul_nonneg (mul_nonneg hD hcsinv) hgamma) hs0.le
  have hnnRem : (0 : ℝ) ≤ (s ^ 3)⁻¹ * (cstar ^ 4)⁻¹ * Rem :=
    mul_nonneg (by positivity) hRem
  have hnnG1a : (0 : ℝ) ≤ (s ^ 2)⁻¹ * cstar⁻¹ * gamma * G1a :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hcsinv) hgamma) hG1a0
  have hnnG1b : (0 : ℝ) ≤ (s ^ 2)⁻¹ * cstar⁻¹ * gamma * G1b :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hcsinv) hgamma) hG1b0
  have hT1 : D * s * G2raw ≤ C * s * G2raw := by
    calc D * s * G2raw = D * (s * G2raw) := by ring
      _ ≤ C * (s * G2raw) :=
          mul_le_mul_of_nonneg_right hC1 (mul_nonneg hs0.le hG2raw)
      _ = C * s * G2raw := by ring
  have hT2 : D * s * SigSum
      ≤ C * (s⁻¹ ^ (3 : ℕ)) * (cstar⁻¹ ^ (4 : ℕ)) * Rem := by
    calc D * s * SigSum
        ≤ D * s * (Csig * s⁻¹ * (s ^ 3)⁻¹ * (cstar ^ 4)⁻¹ * Rem) :=
          mul_le_mul_of_nonneg_left hsig (mul_nonneg hD hs0.le)
      _ = (D * Csig) * ((s ^ 3)⁻¹ * (cstar ^ 4)⁻¹ * Rem) := by field_simp
      _ ≤ C * ((s ^ 3)⁻¹ * (cstar ^ 4)⁻¹ * Rem) :=
          mul_le_mul_of_nonneg_right hC2 hnnRem
      _ = C * (s⁻¹ ^ (3 : ℕ)) * (cstar⁻¹ ^ (4 : ℕ)) * Rem := by
          rw [inv_pow, inv_pow]; ring
  have hT34 : D * cstar⁻¹ * gamma * s * GradSum + D * cstar⁻¹ * gamma * s * L2Sum
      ≤ C * (s⁻¹ ^ (2 : ℕ)) * cstar⁻¹ * gamma * G1b := by
    calc D * cstar⁻¹ * gamma * s * GradSum + D * cstar⁻¹ * gamma * s * L2Sum
        ≤ D * cstar⁻¹ * gamma * s * (Cgrad * (s ^ 3)⁻¹ * G1b)
            + D * cstar⁻¹ * gamma * s * (CL2 * (s ^ 3)⁻¹ * G1b) :=
          add_le_add (mul_le_mul_of_nonneg_left hgrad hpref)
            (mul_le_mul_of_nonneg_left hL2 hpref)
      _ = (D * (Cgrad + CL2)) * ((s ^ 2)⁻¹ * cstar⁻¹ * gamma * G1b) := by field_simp
      _ ≤ C * ((s ^ 2)⁻¹ * cstar⁻¹ * gamma * G1b) :=
          mul_le_mul_of_nonneg_right hC3 hnnG1b
      _ = C * (s⁻¹ ^ (2 : ℕ)) * cstar⁻¹ * gamma * G1b := by rw [inv_pow]; ring
  have hT5 : D * cstar⁻¹ * (s ^ 2)⁻¹ * gamma * Gm
      ≤ C * (s⁻¹ ^ (2 : ℕ)) * cstar⁻¹ * gamma * G1a := by
    calc D * cstar⁻¹ * (s ^ 2)⁻¹ * gamma * Gm
        ≤ D * cstar⁻¹ * (s ^ 2)⁻¹ * gamma * G1a :=
          mul_le_mul_of_nonneg_left hGm
            (mul_nonneg (mul_nonneg (mul_nonneg hD hcsinv) (by positivity)) hgamma)
      _ = D * ((s ^ 2)⁻¹ * cstar⁻¹ * gamma * G1a) := by ring
      _ ≤ C * ((s ^ 2)⁻¹ * cstar⁻¹ * gamma * G1a) :=
          mul_le_mul_of_nonneg_right hC1 hnnG1a
      _ = C * (s⁻¹ ^ (2 : ℕ)) * cstar⁻¹ * gamma * G1a := by rw [inv_pow]; ring
  linarith only [hpre, hT1, hT2, hT34, hT5]

/-! ## Part D' -- the two legs and the Step-3 regrouping -/

/-- **The two-leg Step-3 regrouping.**

The field leg and the transposed leg are both taken to the five-term `pre.zero`
shape *at the same five right-hand families*; adding them doubles the constant
and nothing else.  This is the machine-visible content of the manuscript's
transpose remark: each of the five right-hand terms is literally the same
expression for the two legs, so "the right side does not change" is not a claim
about the terms at all -- its whole content is that the transposed leg admits
the same per-cube ugly estimate, which is the caller's `hlegt`.

The three Step-3 resummations are then discharged from their comparison inputs
(`hshom`, `hcsL2`, `hcsGn`) and the regrouping is `clauseOneBound_of_preZero`. -/
theorem clauseOneBound_of_legs
    {s gamma cstar C Cshom Kl2 Kgn Cout gradM Ecal2 Ecal2f Ecal2t : ℝ} {m : ℤ}
    {E2 L2f gradNf : ℤ → ℤ → ℝ} {sig : ℤ → ℝ} {A : ℤ → ℝ}
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hgamma0 : 0 ≤ gamma) (hsg : 8 * gamma ≤ s)
    (hcstar0 : 0 < cstar) (hcstar4 : cstar ^ 4 ≤ 6) (hlog : 1 ≤ |Real.log gamma|)
    (hC0 : 0 ≤ C) (hKl2 : 0 ≤ Kl2) (hKgn : 0 ≤ Kgn) (hgradM : 0 ≤ gradM)
    (hE0 : ∀ j n, 0 ≤ E2 j n) (hsig0 : ∀ n, 0 ≤ sig n)
    (hL20 : ∀ j n, 0 ≤ L2f j n) (hgrad0 : ∀ j n, 0 ≤ gradNf j n)
    (hsplit : Ecal2 ≤ Ecal2f + Ecal2t)
    (hlegf : Ecal2f
      ≤ C * s * annDouble m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * E2 j n)
        + C * s * annDouble m (fun _ n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * sig n)
        + C * cstar⁻¹ * gamma * s
            * annDouble m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * L2f j n)
        + C * cstar⁻¹ * gamma * s
            * annDouble m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * gradNf j n)
        + C * cstar⁻¹ * (s ^ 2)⁻¹ * gamma * gradM)
    (hlegt : Ecal2t
      ≤ C * s * annDouble m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * E2 j n)
        + C * s * annDouble m (fun _ n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * sig n)
        + C * cstar⁻¹ * gamma * s
            * annDouble m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * L2f j n)
        + C * cstar⁻¹ * gamma * s
            * annDouble m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * gradNf j n)
        + C * cstar⁻¹ * (s ^ 2)⁻¹ * gamma * gradM)
    (hshom : ∀ n : ℤ, n ≤ m - 1 →
      sig n ≤ (Cshom * gamma * ((m - n : ℤ) : ℝ)
          + Cshom * (2 * gamma
            + (cstar ^ 2)⁻¹ * (gamma * |Real.log gamma| ^ 2))) ^ 2
        * (3 : ℝ) ^ (2 * gamma * ((m - n : ℤ) : ℝ)))
    (hAsum : Summable (fun v : ℕ => (3 : ℝ) ^ (-(s / 2) * (v : ℝ)) * A (m - (v : ℤ)) ^ 2))
    (hcsL2 : ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
      L2f j n ≤ Kl2 * (((m - n : ℤ) : ℝ) + 2)
        * (3 : ℝ) ^ (2 * gamma * ((m - n : ℤ) : ℝ))
        * ∑ v ∈ Finset.range ((m - n).toNat + 2), A (m - (v : ℤ)) ^ 2)
    (hcsGn : ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
      gradNf j n ≤ Kgn * (((m - n : ℤ) : ℝ) + 2)
        * ∑ v ∈ Finset.range ((m - n).toNat + 2), A (m - (v : ℤ)) ^ 2)
    (hCout1 : 2 * C ≤ Cout)
    (hCout2 : 2 * C * (7000 * Cshom ^ 2) ≤ Cout)
    (hCout3 : 2 * C * (4608 * Kl2 + 576 * Kgn) ≤ Cout) :
    IsClauseOneBound Ecal2
      (annDouble m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * E2 j n))
      (gamma ^ 2 * |Real.log gamma| ^ 4) gradM
      (∑' v : ℕ, (3 : ℝ) ^ (-(s / 2) * (v : ℝ)) * A (m - (v : ℤ)) ^ 2)
      s cstar gamma Cout := by
  have hG2raw0 :
      0 ≤ annDouble m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * E2 j n) :=
    annDouble_nonneg fun j n => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hE0 j n)
  have hRem0 : (0 : ℝ) ≤ gamma ^ 2 * |Real.log gamma| ^ 4 := by positivity
  have hG1b0 : (0 : ℝ)
      ≤ ∑' v : ℕ, (3 : ℝ) ^ (-(s / 2) * (v : ℝ)) * A (m - (v : ℤ)) ^ 2 :=
    tsum_nonneg fun v => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (sq_nonneg _)
  have hpre : Ecal2
      ≤ 2 * C * s
          * annDouble m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * E2 j n)
        + 2 * C * s
          * annDouble m (fun _ n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * sig n)
        + 2 * C * cstar⁻¹ * gamma * s
          * annDouble m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * L2f j n)
        + 2 * C * cstar⁻¹ * gamma * s
          * annDouble m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * gradNf j n)
        + 2 * C * cstar⁻¹ * (s ^ 2)⁻¹ * gamma * gradM := by
    linarith only [hsplit, hlegf, hlegt]
  have hsig := step3_sigma_ratio_slot (m := m) (s := s) (gamma := gamma)
    (cstar := cstar) (Cshom := Cshom) (sig := sig) hs0 hs1 hgamma0 hsg hcstar0
    hcstar4 hlog hsig0 hshom
  have hgrad := step3_kL2_resummation (m := m) (s := s) (gamma := gamma)
    (Kcs := Kl2) (A := A) (T := L2f) hs0 hs1 hgamma0 hsg hKl2 hL20 hAsum hcsL2
  have hL2 := step3_grad_resummation (m := m) (s := s) (Kcs := Kgn) (A := A)
    (T := gradNf) hs0 hs1 hKgn hgrad0 hAsum hcsGn
  exact clauseOneBound_of_preZero (D := 2 * C) hs0 hcstar0 hgamma0
    (by linarith only [hC0]) hG2raw0 hRem0 hgradM hG1b0 hpre hsig hgrad hL2 le_rfl
    hCout1 hCout2 hCout3

/-! ## Part E -- the composite at the flux-corrected carrier -/

/-- ```
gradTailSq M m omega = ( sum_{k >= m} 3^((2-gamma) m) ‖grad j_k‖_{W^{1,infinity}(Box_m)} )^2 .
```

The square is outside the sum; the printed display puts it inside, and the
inside-square variant cannot dominate the fifth `pre.zero` term. -/
def gradTailSq (M : ABKModel d) (m : ℤ) (omega : Cutoff.CutoffSample d) : ℝ :=
  (∑' k : {k : ℤ // m ≤ k},
    (3 : ℝ) ^ ((2 - M.gamma) * (m : ℝ))
      * Support.shellW1InfGradNorm m (omega.1 k.1)) ^ 2

theorem gradTailSq_nonneg (M : ABKModel d) (m : ℤ) (omega : Cutoff.CutoffSample d) :
    0 ≤ gradTailSq M m omega :=
  sq_nonneg _

/-- **The clause-(i) composite at the literal flux-corrected carrier.**

* `hbfJ` -- the `e.bfJ.general` conversion of the depth-`l` descendant maximum
  of the normalized block response into the two lattice `J`-maxima (A4a proves
  it at the constant `1`; the manuscript's `C >= 1` is carried here);
* `hpref` / `hpret` -- the Step-1 annular cover at the two legs;
* `huglyf` / `huglyt` -- the per-cube ugly estimate at the lattice cube
  `z + Box_n`, **with the `k > m` tail included in the fourth slot** (the honest
  `m`-vs-`L` reading; `isUglyJEstimate_routeTail` moves it to the fifth term);
* `hshom` -- `e.shom.m.vs.shom.n` in the manuscript's own shape;
* `hcsL2` / `hcsGn` -- the two Step-3 cube comparisons;
* the summability facts, and the constant inequalities.

The conclusion is the four-term shape at the concrete left-hand carrier, the
concrete `G_1^a` content `gradTailSq`, and the concrete remainder
`gamma^2 |log gamma|^4`. -/
theorem clauseOne_bound (M : ABKModel d) (L m : ℤ)
    {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (hsg : 8 * M.gamma ≤ s)
    (omega : Cutoff.CutoffSample d)
    {Jlegf Jlegt : ℤ → ℝ} {Jannf Jannt E2 L2f gradNf : ℤ → ℤ → ℝ}
    {sig : ℤ → ℝ} {A : ℤ → ℝ}
    {Cbf C₁ C₂ Cleg Cshom Kl2 Kgn Ktail Cout : ℝ}
    (hCbf : 0 ≤ Cbf) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hKl2 : 0 ≤ Kl2)
    (hKgn : 0 ≤ Kgn) (hKtail : 0 ≤ Ktail)
    (hJf0 : ∀ n, 0 ≤ Jlegf n) (hJt0 : ∀ n, 0 ≤ Jlegt n)
    (hJannf0 : ∀ j n, 0 ≤ Jannf j n) (hJannt0 : ∀ j n, 0 ≤ Jannt j n)
    (hE0 : ∀ j n, 0 ≤ E2 j n) (hsig0 : ∀ n, 0 ≤ sig n)
    (hL20 : ∀ j n, 0 ≤ L2f j n) (hgrad0 : ∀ j n, 0 ≤ gradNf j n)
    (hbfJ : ∀ l : ℕ,
      maxDescendantNormalizedBlockResponseAtScale (originCube d m) (m - (l : ℤ))
          (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
          (isotropicComparatorMatrix (Annealed.sigmaBar M m))
        ≤ Cbf * (Jlegf (m - (l : ℤ)) + Jlegt (m - (l : ℤ))))
    (hsumFl : Summable
      (fun l : ℕ => (3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * Jlegf (m - (l : ℤ))))
    (hsumTl : Summable
      (fun l : ℕ => (3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * Jlegt (m - (l : ℤ))))
    (hpref : IsAnnularDecompPre s m Jlegf Jannf C₁)
    (hpret : IsAnnularDecompPre s m Jlegt Jannt C₁)
    (huglyf : ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
      IsUglyJEstimate (Jannf j n) (E2 j n) (sig n) (L2f j n)
        (gradNf j n + Ktail * gradTailSq M m omega) (gradTailSq M m omega)
        (Disorder.cstar M) M.gamma ((3 : ℝ) ^ (s * ((m - n : ℤ) : ℝ)))
        ((3 : ℝ) ^ ((s + M.gamma) * ((m - n : ℤ) : ℝ))) C₂)
    (huglyt : ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
      IsUglyJEstimate (Jannt j n) (E2 j n) (sig n) (L2f j n)
        (gradNf j n + Ktail * gradTailSq M m omega) (gradTailSq M m omega)
        (Disorder.cstar M) M.gamma ((3 : ℝ) ^ (s * ((m - n : ℤ) : ℝ)))
        ((3 : ℝ) ^ ((s + M.gamma) * ((m - n : ℤ) : ℝ))) C₂)
    (hsumE : Summable
      (annFam m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * E2 j n)))
    (hsumS : Summable
      (annFam m (fun _ n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * sig n)))
    (hsumL : Summable
      (annFam m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * L2f j n)))
    (hsumG : Summable
      (annFam m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * gradNf j n)))
    (hcstar4 : Disorder.cstar M ^ 4 ≤ 6) (hlog : 1 ≤ |Real.log M.gamma|)
    (hshom : ∀ n : ℤ, n ≤ m - 1 →
      sig n ≤ (Cshom * M.gamma * ((m - n : ℤ) : ℝ)
          + Cshom * (2 * M.gamma
            + (Disorder.cstar M ^ 2)⁻¹
              * (M.gamma * |Real.log M.gamma| ^ 2))) ^ 2
        * (3 : ℝ) ^ (2 * M.gamma * ((m - n : ℤ) : ℝ)))
    (hAsum : Summable (fun v : ℕ => (3 : ℝ) ^ (-(s / 2) * (v : ℝ)) * A (m - (v : ℤ)) ^ 2))
    (hcsL2 : ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
      L2f j n ≤ Kl2 * (((m - n : ℤ) : ℝ) + 2)
        * (3 : ℝ) ^ (2 * M.gamma * ((m - n : ℤ) : ℝ))
        * ∑ v ∈ Finset.range ((m - n).toNat + 2), A (m - (v : ℤ)) ^ 2)
    (hcsGn : ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
      gradNf j n ≤ Kgn * (((m - n : ℤ) : ℝ) + 2)
        * ∑ v ∈ Finset.range ((m - n).toNat + 2), A (m - (v : ℤ)) ^ 2)
    (hCleg : 24 * Cbf * C₁ * ((1 + Ktail) * C₂) ≤ Cleg)
    (hCout1 : 2 * Cleg ≤ Cout)
    (hCout2 : 2 * Cleg * (7000 * Cshom ^ 2) ≤ Cout)
    (hCout3 : 2 * Cleg * (4608 * Kl2 + 576 * Kgn) ≤ Cout) :
    IsClauseOneBound (Support.fluxCorrectedError M L m s omega ^ 2)
      (annDouble m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * E2 j n))
      (M.gamma ^ 2 * |Real.log M.gamma| ^ 4) (gradTailSq M m omega)
      (∑' v : ℕ, (3 : ℝ) ^ (-(s / 2) * (v : ℝ)) * A (m - (v : ℤ)) ^ 2)
      s (Disorder.cstar M) M.gamma Cout := by
  have hgam0 : 0 < M.gamma := M.shellPrefix.gamma_pos
  have hcs0 : 0 < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hcsinv : (0 : ℝ) ≤ (Disorder.cstar M)⁻¹ := inv_nonneg.2 hcs0.le
  have hgradM0 : (0 : ℝ) ≤ gradTailSq M m omega := gradTailSq_nonneg M m omega
  have hCleg0 : (0 : ℝ) ≤ Cleg := by
    have hnn : (0 : ℝ) ≤ 24 * Cbf * C₁ * ((1 + Ktail) * C₂) := by positivity
    linarith only [hCleg, hnn]
  -- the weight comparison on the annular region: `3^(s q) <= 3^((s+gamma) q)`
  have hweight : ∀ n : ℤ, n ≤ m - 1 →
      (3 : ℝ) ^ (s * ((m - n : ℤ) : ℝ))
        ≤ (3 : ℝ) ^ ((s + M.gamma) * ((m - n : ℤ) : ℝ)) := by
    intro n hn
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hq : (0 : ℝ) ≤ ((m - n : ℤ) : ℝ) := by
      have : (0 : ℤ) ≤ m - n := by omega
      exact_mod_cast this
    have hprod : 0 ≤ M.gamma * ((m - n : ℤ) : ℝ) := mul_nonneg hgam0.le hq
    linarith only [hprod]
  -- the two per-cube estimates after the `m`-vs-`L` tail routing
  have hrouted : ∀ (Jann : ℤ → ℤ → ℝ),
      (∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
        IsUglyJEstimate (Jann j n) (E2 j n) (sig n) (L2f j n)
          (gradNf j n + Ktail * gradTailSq M m omega) (gradTailSq M m omega)
          (Disorder.cstar M) M.gamma ((3 : ℝ) ^ (s * ((m - n : ℤ) : ℝ)))
          ((3 : ℝ) ^ ((s + M.gamma) * ((m - n : ℤ) : ℝ))) C₂) →
      ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
        IsUglyJEstimate (Jann j n) (E2 j n) (sig n) (L2f j n) (gradNf j n)
          (gradTailSq M m omega) (Disorder.cstar M) M.gamma
          ((3 : ℝ) ^ (s * ((m - n : ℤ) : ℝ)))
          ((3 : ℝ) ^ ((s + M.gamma) * ((m - n : ℤ) : ℝ))) ((1 + Ktail) * C₂) := by
    intro Jann hJ j n hj hn
    exact isUglyJEstimate_routeTail hC₂ hcsinv hgam0.le (hE0 j n) (hsig0 n)
      (hL20 j n) (hgrad0 j n) hgradM0 hKtail
      (Real.rpow_nonneg (by norm_num) _) (hweight n (by omega)) (hJ j n hj hn)
  -- the `(infinity,2)` opening
  have hopen := eightEss_of_blockResponse_le M L m hs0 omega
    (Jfld := fun l : ℕ => Jlegf (m - (l : ℤ)))
    (Jtrn := fun l : ℕ => Jlegt (m - (l : ℤ))) hbfJ hsumFl hsumTl
  have hC₂' : (0 : ℝ) ≤ (1 + Ktail) * C₂ := by positivity
  have hlegf := preZero_leg (Cbf := Cbf) (C₁ := C₁) (C₂ := (1 + Ktail) * C₂)
    (C := Cleg) (Jleg := Jlegf) (Jann := Jannf) hs0 hs1 hgam0.le hsg hcs0 hCbf hC₁
    hC₂' hgradM0 hJf0 hJannf0 hE0 hsig0 hL20 hgrad0 le_rfl hpref
    (hrouted Jannf huglyf) hsumE hsumS hsumL hsumG hCleg
  have hlegt := preZero_leg (Cbf := Cbf) (C₁ := C₁) (C₂ := (1 + Ktail) * C₂)
    (C := Cleg) (Jleg := Jlegt) (Jann := Jannt) hs0 hs1 hgam0.le hsg hcs0 hCbf hC₁
    hC₂' hgradM0 hJt0 hJannt0 hE0 hsig0 hL20 hgrad0 le_rfl hpret
    (hrouted Jannt huglyt) hsumE hsumS hsumL hsumG hCleg
  exact clauseOneBound_of_legs (C := Cleg) (Cshom := Cshom) hs0 hs1 hgam0.le hsg
    hcs0 hcstar4 hlog hCleg0 hKl2 hKgn hgradM0 hE0 hsig0 hL20 hgrad0 hopen hlegf
    hlegt hshom hAsum hcsL2 hcsGn hCout1 hCout2 hCout3

/-- The `e.bfJ.general` slot at the manuscript's constant `C >= 1`, from A4a's
`C = 1` producer: a bound on the two lattice `J`-maxima, for the field and for
its transpose, at every depth. -/
theorem hbfJ_of_lattice_bounds [NeZero d] (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) {Jlegf Jlegt : ℤ → ℝ} {Cbf : ℝ}
    (hCbf : 1 ≤ Cbf) (hJf0 : ∀ n, 0 ≤ Jlegf n) (hJt0 : ∀ n, 0 ≤ Jlegt n)
    (hfld : ∀ l : ℕ, ∀ v ∈ Support.latticeCubeSet d (m - (l : ℤ)) m, ∀ e : Vec d,
      vecNorm e = 1 →
      responseJ (cubeDomain (latticeCube (m - (l : ℤ)) v))
          ((Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega).coeffOn
            (latticeCube (m - (l : ℤ)) v))
        (Observable.inverseSqrtLoad (Annealed.sigmaBar M m) e)
        (Observable.sqrtLoad (Annealed.sigmaBar M m) e) ≤ Jlegf (m - (l : ℤ)))
    (htrn : ∀ l : ℕ, ∀ v ∈ Support.latticeCubeSet d (m - (l : ℤ)) m, ∀ e : Vec d,
      vecNorm e = 1 →
      responseJ (cubeDomain (latticeCube (m - (l : ℤ)) v))
          ((Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega).coeffOn
            (latticeCube (m - (l : ℤ)) v)).transpose
        (Observable.inverseSqrtLoad (Annealed.sigmaBar M m) e)
        (Observable.sqrtLoad (Annealed.sigmaBar M m) e) ≤ Jlegt (m - (l : ℤ))) :
    ∀ l : ℕ,
      maxDescendantNormalizedBlockResponseAtScale (originCube d m) (m - (l : ℤ))
          (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
          (isotropicComparatorMatrix (Annealed.sigmaBar M m))
        ≤ Cbf * (Jlegf (m - (l : ℤ)) + Jlegt (m - (l : ℤ))) := by
  intro l
  have hone := eightEss_blockResponse_le_of_lattice_bounds
    (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega) m
    (Annealed.sigmaBar M m)
    (Jfld := fun l : ℕ => Jlegf (m - (l : ℤ)))
    (Jtrn := fun l : ℕ => Jlegt (m - (l : ℤ))) hfld htrn l
  rw [one_mul] at hone
  refine hone.trans ?_
  have hnn : (0 : ℝ) ≤ Jlegf (m - (l : ℤ)) + Jlegt (m - (l : ℤ)) := by
    have h1 := hJf0 (m - (l : ℤ))
    have h2 := hJt0 (m - (l : ℤ))
    linarith only [h1, h2]
  calc Jlegf (m - (l : ℤ)) + Jlegt (m - (l : ℤ))
      = 1 * (Jlegf (m - (l : ℤ)) + Jlegt (m - (l : ℤ))) := by ring
    _ ≤ Cbf * (Jlegf (m - (l : ℤ)) + Jlegt (m - (l : ℤ))) :=
        mul_le_mul_of_nonneg_right hCbf hnn

end

end Algsuperdiff.Section4.Provider.Annular
