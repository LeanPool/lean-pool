/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.MinimalScale.StepOneWindow
public import LeanPool.Superdiffusion.Algsuperdiff.Probability.CesaroAlgebra
public import LeanPool.Superdiffusion.Algsuperdiff.Probability.ColoredCesaro
public import LeanPool.Superdiffusion.Algsuperdiff.Probability.TruncatedScaleTriangle
public import LeanPool.Superdiffusion.Algsuperdiff.Probability.WindowRearrange

/-!
# StepOneAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `D₁` half of `e.kick.Dees.Dees`

ABK26, §4.2, the end of Step 1 of `l.minimal.scale.sep`.  Summing the Step-1
pointwise estimate over the window and rearranging (`e.D1k.Larry`) gives

```
avsum_{k=n}^m D₁(k)
  ≤ C s^{1/2} · [ 𝔠 · avsum_{j=n}^m X_j  +  (min{N, 𝔠}/N) · ∑_{p ≥ 0} 3^{−¼sp} X_{n−1−p} ]
```

with `N = m − n + 1` and `𝔠 = (1 − 3^{−¼s})^{−1} ≤ 8/s`.  The window average is closed
by the `r`-dependent Cesàro engine (`p.concentration`) and the head by the countable
`Γ₂` triangle inequality; adding the two gives the `D₁` half of `e.kick.Dees.Dees`:

```
avsum_{k=n}^m D₁(k) ≤ C c⋆^{−1}s^{−7/2}√γ + 𝒪_{Γ₂}(C c⋆^{−1}s^{−7/2}√γ N^{−1/2}) .
```

## Where the printed `s^{−7/2}` comes from

The two legs land at different `s`-powers:

* the window leg gives `s^{1/2}·𝔠·A₁ ≍ s^{1/2}·s^{−1}·s^{−5/2} = s^{−3}`;
* the head leg gives `s^{1/2}·√𝔠·(𝔠 A₁) ≍ s^{1/2}·s^{−1/2}·s^{−1}·s^{−5/2} = s^{−7/2}`.

So the printed `s^{−7/2}` of `e.kick.Dees.Dees` is attained **only at the
head**, and only if the head's window coefficient is read at the sharp
`min{N,𝔠}/N ≤ √𝔠·N^{−1/2}` (`Probability.min_div_le_sqrt_mul_rpow`).

The one-shot engine `Probability.cesaroAvg_isBigO_of_rDependent_with_tail`
**cannot** deliver this: it absorbs the boundary term through `1/N ≤ N^{−1/2}`,
which loses exactly the `√N` that the sharp `min`-coefficient provides, and the
head then costs `s^{−4}` (with the `N^{−1/2}` decay) or `s^{−7/2}` (without
it).  The assembly below therefore uses the plain engine
`cesaroAvg_isBigO_of_rDependent` for the window leg and applies the sharp
`min`-coefficient to the head leg by hand before adding the two `Γ₂` bounds —
which is exactly what the manuscript does ("adding the previous two displays").

## The `r`-dependence is read at `r = d + 2`

This module instantiates `r = d + 2`, which clears the count for every `d`
(`three_pow_dim_clears`) and keeps the output constant a function of `d` alone.
It is not the minimal admissible `r` (the minimal one is logarithmic in `d`);
the cost of the non-minimal choice is the factor `√(r+1)` inside
`rDepEngineConst`, i.e. a `d`-only constant.

## Main results

* `three_pow_dim_clears` — the separation count at `r = d + 2`.
* `exists_stepOne_d1_bound` — **the `D₁` half of `e.kick.Dees.Dees`**.

## References

* ABK26, `l.minimal.scale.sep`, Step 1; `e.D1k.Larry`; `p.concentration`.
-/

namespace Algsuperdiff.Section4.Provider.MinimalScale

open Algsuperdiff.Section3
open HCPolySupport HCPolySupport.IndependentSums MeasureTheory
open Algsuperdiff.Section4.Support
open Algsuperdiff.Probability
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The separation count at `r = d + 2` -/

/-- **The `r`-dependence count is cleared at `r = d + 2`, for every `d`.**  The
proved bridge asks for `3 + 2·3^{1−2}·√d ≤ 3^r`; at `r = d+2` this follows from
`√d ≤ 1 + d` and `1 + 2d ≤ 3^d`.  No dimension restriction is introduced. -/
theorem three_pow_dim_clears (d : ℕ) :
    3 + 2 * (3 : ℝ) ^ (1 - (2 : ℤ)) * Real.sqrt (d : ℝ) ≤ (3 : ℝ) ^ (d + 2 : ℕ) := by
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hsqrt : Real.sqrt (d : ℝ) ≤ 1 + (d : ℝ) := sqrt_le_one_add hd0
  have hpow : (1 : ℝ) + 2 * (d : ℝ) ≤ (3 : ℝ) ^ (d : ℕ) := by
    have h := one_add_mul_le_pow (a := (2 : ℝ)) (by norm_num) d
    calc (1 : ℝ) + 2 * (d : ℝ) = 1 + (d : ℝ) * 2 := by ring
      _ ≤ (1 + 2 : ℝ) ^ (d : ℕ) := h
      _ = (3 : ℝ) ^ (d : ℕ) := by norm_num
  have hval : (3 : ℝ) ^ (1 - (2 : ℤ)) = 1 / 3 := by norm_num
  have hsplit : (3 : ℝ) ^ (d + 2 : ℕ) = 9 * (3 : ℝ) ^ (d : ℕ) := by
    rw [pow_add]
    ring
  rw [hval, hsplit]
  have hstep : 2 * (1 / 3 : ℝ) * Real.sqrt (d : ℝ) ≤ 2 * (1 / 3 : ℝ) * (1 + (d : ℝ)) :=
    mul_le_mul_of_nonneg_left hsqrt (by norm_num)
  linarith only [hstep, hpow, hd0]

/-! ## 2. The endpoint -/

private theorem stepOneAssembly_comparisonBounds1 :
    ∀ (d : ℕ) (CK : ℝ) (M : ABKModel d) (s : { s : ℝ // (0 : ℝ) < s }) (Ccg : ℝ) (n m : ℤ) (_ : n
      ≤ m),
      let rho : ℝ := √√(max (216 : ℝ) CK / CK);
      ∀ (_ : (0 : ℝ) ≤ rho)  (_ : (0 : ℝ) < (↑s : ℝ))
        (_ : (↑s : ℝ) ≤ (1 : ℝ)) (lam : ℝ) (_ : (0 : ℝ) ≤ lam),
        let K0 : ℝ := CK * (√(↑s : ℝ) ^ (9 : ℕ))⁻¹;
        let K1c : ℝ := max (216 : ℝ) CK * (√(↑s : ℝ) ^ (9 : ℕ))⁻¹;
        ∀ (_ : (0 : ℝ) < K0) (_ : K0 ≤ K1c) (_ : (216 : ℝ) * (√(↑s : ℝ) ^ (9 : ℕ))⁻¹ ≤ K1c)
          (_ : K1c / K0 = max (216 : ℝ) CK / CK)
          (_ : ∀ (j : ℤ) (omega : Cutoff.CutoffSample d), (0 : ℝ) ≤ kickCollapsed M s lam K0 j
            omega),
          let G : ℝ := geomTailConst ((↑s : ℝ) / (4 : ℝ));
          ∀ (_ : (0 : ℝ) < G),
            let N : ℝ := (↑(m - n + (1 : ℤ)) : ℝ);
            ∀ (_ : (0 : ℝ) < N),
              let aw : ℝ := √(↑s : ℝ) * rho * G;
                let ah : ℝ := √(↑s : ℝ) * rho * ((1 : ℝ) / N * min N G);
                  (0 : ℝ) ≤ aw ∧
                    (0 : ℝ) ≤ ah ∧
                      ∀ (omega : Cutoff.CutoffSample d),
                        cesaroAvg (fun (k : ℤ) => (dOne M Ccg s k omega).toReal) n m ≤
                          aw * cesaroAvg (fun (j : ℤ) => kickCollapsed M s lam K0 j omega) n m +
                            ah *
                              ∑' (p : ℕ),
                                (3 : ℝ) ^ (-((↑s : ℝ) / (4 : ℝ) * (↑p : ℝ))) *
                                  kickCollapsed M s lam K0 (n - (1 : ℤ) - (↑p : ℤ)) omega := by
  intro d calculationCK M s Ccg n m hnm rho hrho0 hs0 hs1 lam hlam0 K0 _ hK00 hK0K1 hK1ge
    hratioeq hX0 G hG0 N hN0 aw ah
  have hrhodef : rho = √√(max (216 : ℝ) calculationCK / calculationCK) := rfl
  have hawdef : aw = √(↑s : ℝ) * rho * G := rfl
  have hahdef : ah = √(↑s : ℝ) * rho * ((1 : ℝ) / N * min N G) := rfl
  have haw0 : (0 : ℝ) ≤ aw :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hrho0) hG0.le
  have hah0 : (0 : ℝ) ≤ ah := by
    refine mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hrho0) ?_
    exact mul_nonneg (by positivity) (le_min hN0.le hG0.le)
  -- the rearranged display (e.D1k.Larry)
  have hdom : ∀ omega : Cutoff.CutoffSample d,
      cesaroAvg (fun k => (dOne M Ccg s k omega).toReal) n m
        ≤ aw * cesaroAvg (fun j => kickCollapsed M s lam K0 j omega) n m +
          ah * ∑' p : ℕ, (3 : ℝ) ^ (-(((s : ℝ) / 4) * (p : ℝ))) *
            kickCollapsed M s lam K0 (n - 1 - (p : ℤ)) omega := by
    intro omega
    have hpt : ∀ k ∈ Finset.Icc n m, (dOne M Ccg s k omega).toReal
        ≤ Real.sqrt (s : ℝ) * rho * windowKickSum M s lam K0 k omega := by
      intro k _
      have h := dOne_toReal_le_scaled M s Ccg hlam0 hs1 hK00 hK0K1 hK1ge (k := k) omega
      rw [hratioeq, ← hrhodef] at h
      calc (dOne M Ccg s k omega).toReal
          ≤ Real.sqrt (s : ℝ) * (rho * windowKickSum M s lam K0 k omega) := h
        _ = Real.sqrt (s : ℝ) * rho * windowKickSum M s lam K0 k omega := by ring
    have h1 : cesaroAvg (fun k => (dOne M Ccg s k omega).toReal) n m
        ≤ cesaroAvg (fun k => Real.sqrt (s : ℝ) * rho *
            windowKickSum M s lam K0 k omega) n m := cesaroAvg_mono hnm hpt
    rw [cesaroAvg_const_mul] at h1
    -- the rearrangement of the window sums
    have h2 : ∑ k ∈ Finset.Icc n m, windowKickSum M s lam K0 k omega
        ≤ G * (∑ l ∈ Finset.Icc n m, kickCollapsed M s lam K0 l omega) +
          min N G * ∑' p : ℕ, (3 : ℝ) ^ (-(((s : ℝ) / 4) * (p : ℝ))) *
            kickCollapsed M s lam K0 (n - 1 - (p : ℤ)) omega :=
      window_geom_head_rearrange (α := (s : ℝ) / 4) (by linarith only [hs0])
        (X := fun l => kickCollapsed M s lam K0 l omega) (fun l => hX0 l omega) hnm
    have h3 : cesaroAvg (fun k => windowKickSum M s lam K0 k omega) n m
        ≤ G * cesaroAvg (fun j => kickCollapsed M s lam K0 j omega) n m +
          ((1 / N) * min N G) * ∑' p : ℕ, (3 : ℝ) ^ (-(((s : ℝ) / 4) * (p : ℝ))) *
            kickCollapsed M s lam K0 (n - 1 - (p : ℤ)) omega := by
      have hstep := mul_le_mul_of_nonneg_left h2
        (by positivity : (0 : ℝ) ≤ 1 / N)
      rw [cesaroAvg]
      calc (1 / N) * ∑ k ∈ Finset.Icc n m, windowKickSum M s lam K0 k omega
          ≤ (1 / N) * (G * (∑ l ∈ Finset.Icc n m, kickCollapsed M s lam K0 l omega) +
              min N G * ∑' p : ℕ, (3 : ℝ) ^ (-(((s : ℝ) / 4) * (p : ℝ))) *
                kickCollapsed M s lam K0 (n - 1 - (p : ℤ)) omega) := by
            exact hstep
        _ = G * ((1 / N) * ∑ l ∈ Finset.Icc n m, kickCollapsed M s lam K0 l omega) +
              ((1 / N) * min N G) * ∑' p : ℕ, (3 : ℝ) ^ (-(((s : ℝ) / 4) * (p : ℝ))) *
                kickCollapsed M s lam K0 (n - 1 - (p : ℤ)) omega := by ring
        _ = G * cesaroAvg (fun j => kickCollapsed M s lam K0 j omega) n m +
              ((1 / N) * min N G) * ∑' p : ℕ, (3 : ℝ) ^ (-(((s : ℝ) / 4) * (p : ℝ))) *
                kickCollapsed M s lam K0 (n - 1 - (p : ℤ)) omega := by
            rw [cesaroAvg]
    have hmul := mul_le_mul_of_nonneg_left h3
      (mul_nonneg (Real.sqrt_nonneg (s : ℝ)) hrho0)
    refine h1.trans (hmul.trans (le_of_eq ?_))
    rw [hawdef, hahdef]
    ring
  exact ⟨haw0, hah0, hdom⟩

private theorem stepOneAssembly_momentBounds1 :
    ∀ (d : ℕ) (CK : ℝ) (_ : (0 : ℝ) < CK)
      (_ :
        ∀ (M : ABKModel d),
          M.gamma ≤ CK⁻¹ ^ (10 : ℕ) * Disorder.cstar M ^ (10 : ℕ) →
            ∀ (s : { s : ℝ // (0 : ℝ) < s }),
              (8 : ℝ) * M.gamma ≤ (↑s : ℝ) →
                (↑s : ℝ) ≤ (1 / 2 : ℝ) →
                  ∃ (lam : ℝ),
                    (0 : ℝ) ≤ lam ∧
                      (∀ (j : ℤ) (omega : Cutoff.CutoffSample d),
                          kickLegLow M s lam j omega + kickLegHigh M s lam j omega = annularKick M
                            s j omega) ∧
                        (∀ (j : ℤ),
                            IsBigOWith (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample
                              d)) (gammaSigma (2 : ℝ))
                              (kickCollapsed M s lam (CK * (√(↑s : ℝ) ^ (9 : ℕ))⁻¹) j)
                              (CK * (Disorder.cstar M)⁻¹ * (√(↑s : ℝ) ^ (5 : ℕ))⁻¹ * √M.gamma)) ∧
                          ∀ (j : ℤ),
                            ∫ (omega : Cutoff.CutoffSample d),
                                kickCollapsed M s lam (CK * (√(↑s : ℝ) ^ (9 : ℕ))⁻¹) j
                                  omega ∂(↑(Cutoff.cutoffSampleLaw M) : Measure
                                    (Cutoff.CutoffSample d)) ≤
                              CK * (Disorder.cstar M)⁻¹ * (√(↑s : ℝ) ^ (5 : ℕ))⁻¹ * √M.gamma)
      (M : ABKModel d) (s : { s : ℝ // (0 : ℝ) < s }) (_ : (8 : ℝ) * M.gamma ≤ (↑s : ℝ)) (_ : (↑s
        : ℝ) ≤ (1 / 4 : ℝ))
      (n m : ℤ) (_ : n ≤ m),
      let rho : ℝ := √√(max (216 : ℝ) CK / CK);
      ∀ (_ : (0 : ℝ) ≤ rho),
        let Ce : ℝ := rDepEngineConst (d + (2 : ℕ));
        ∀ (_ : (0 : ℝ) < Ce),
          let Ct : ℝ := gammaTriangleConst (2 : ℝ);
          ∀ (_ : (0 : ℝ) < Ct) ,
            let Cout : ℝ := CK + (8 : ℝ) * rho * CK + (2 : ℝ) * ((8 : ℝ) * rho * CK * Ce + (24 :
              ℝ) * rho * Ct * CK);
            ∀ (_ : M.gamma ≤ Cout⁻¹ ^ (10 : ℕ) * Disorder.cstar M ^ (10 : ℕ))
              (_ : (0 : ℝ) < M.gamma),
              ∃ (_ : (0 : ℝ) < (↑s : ℝ)) (_ : (↑s : ℝ) ≤ (1 : ℝ)) (_ : (0 : ℝ) < √(↑s : ℝ)) (_ :
                √(↑s : ℝ) ≤ (1 : ℝ)) (lam :
                ℝ) (_ : (0 : ℝ) ≤ lam) (_ : (0 : ℝ) < (Disorder.cstar M)⁻¹ * (√(↑s : ℝ) ^ (7 :
                  ℕ))⁻¹ * √M.gamma) (_ :
                (0 : ℝ) < CK * (√(↑s : ℝ) ^ (9 : ℕ))⁻¹) (_ :
                CK * (√(↑s : ℝ) ^ (9 : ℕ))⁻¹ ≤ max (216 : ℝ) CK * (√(↑s : ℝ) ^ (9 : ℕ))⁻¹) (_ :
                (216 : ℝ) * (√(↑s : ℝ) ^ (9 : ℕ))⁻¹ ≤ max (216 : ℝ) CK * (√(↑s : ℝ) ^ (9 : ℕ))⁻¹)
                  (_ :
                max (216 : ℝ) CK * (√(↑s : ℝ) ^ (9 : ℕ))⁻¹ / (CK * (√(↑s : ℝ) ^ (9 : ℕ))⁻¹) = max
                  (216 : ℝ) CK / CK) (_ :
                (0 : ℝ) < CK * (Disorder.cstar M)⁻¹ * (√(↑s : ℝ) ^ (5 : ℕ))⁻¹ * √M.gamma) (_ :
                ∀ (j : ℤ) (omega : Cutoff.CutoffSample d),
                  (0 : ℝ) ≤ kickCollapsed M s lam (CK * (√(↑s : ℝ) ^ (9 : ℕ))⁻¹) j omega)
                (_ : (0 : ℝ) < geomTailConst ((↑s : ℝ) / (4 : ℝ))) (_ :
                geomTailConst ((↑s : ℝ) / (4 : ℝ)) ≤ (8 : ℝ) * (↑s : ℝ)⁻¹) (_ :
                geomTailConst ((↑s : ℝ) / (4 : ℝ)) * (CK * (Disorder.cstar M)⁻¹ * (√(↑s : ℝ) ^ (5
                  : ℕ))⁻¹ * √M.gamma) ≤
                  (8 : ℝ) * CK * ((Disorder.cstar M)⁻¹ * (√(↑s : ℝ) ^ (7 : ℕ))⁻¹ * √M.gamma))
                (Xf : Cutoff.CutoffSample d → ℝ) (_ :
                ∀ (ω : Cutoff.CutoffSample d),
                  cesaroAvg (fun (j : ℤ) => kickCollapsed M s lam (CK * (√(↑s : ℝ) ^ (9 : ℕ))⁻¹) j
                    ω) n m ≤
                    CK * (Disorder.cstar M)⁻¹ * (√(↑s : ℝ) ^ (5 : ℕ))⁻¹ * √M.gamma + Xf ω)
                (_ :
                IsBigO (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d)) (gammaSigma
                  (2 : ℝ)) Xf
                  (rDepEngineConst (d + (2 : ℕ)) * (CK * (Disorder.cstar M)⁻¹ * (√(↑s : ℝ) ^ (5 :
                    ℕ))⁻¹ * √M.gamma) *
                    (↑(m - n + (1 : ℤ)) : ℝ) ^ (-1 / 2 : ℝ))),
                IsBigO (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d)) (gammaSigma
                  (2 : ℝ))
                  (fun (omega : Cutoff.CutoffSample d) =>
                    ∑' (p : ℕ),
                      (3 : ℝ) ^ (-((↑s : ℝ) / (4 : ℝ) * (↑p : ℝ))) *
                        kickCollapsed M s lam (CK * (√(↑s : ℝ) ^ (9 : ℕ))⁻¹) (n - (1 : ℤ) - (↑p :
                          ℤ)) omega)
                  (Ct *
                    (geomTailConst ((↑s : ℝ) / (4 : ℝ)) *
                      (CK * (Disorder.cstar M)⁻¹ * (√(↑s : ℝ) ^ (5 : ℕ))⁻¹ * √M.gamma))) := by
  classical
  intro d CK hCK hcol M s hs8 hs4 n m hnm rho hrho0 Ce hCe0 Ct hCt0 Cout hreg hgam
  have hCtdef : Ct = gammaTriangleConst (2 : ℝ) := rfl
  have hCoutdef : Cout = CK + (8 : ℝ) * rho * CK + (2 : ℝ) * ((8 : ℝ) * rho * CK * Ce + (24 : ℝ)
                * rho * Ct * CK) := rfl
  have hcs : (0 : ℝ) < Disorder.cstar M := (Disorder.cstar_characterization M).1
  have hs0 : (0 : ℝ) < (s : ℝ) := s.2
  have hs1 : (s : ℝ) ≤ 1 := by linarith only [hs4]
  have hs2 : (s : ℝ) ≤ 1 / 2 := by linarith only [hs4]
  have hsq0 : (0 : ℝ) < Real.sqrt (s : ℝ) := Real.sqrt_pos.2 hs0
  have hsq1 : Real.sqrt (s : ℝ) ≤ 1 := by
    have h := Real.sqrt_le_sqrt hs1
    rwa [Real.sqrt_one] at h
  have hgsq : (0 : ℝ) < Real.sqrt M.gamma := Real.sqrt_pos.2 hgam
  -- the regime at the kick family's constant
  have hCKCout : CK ≤ Cout := by
    have h1 : (0 : ℝ) ≤ 8 * rho * CK := mul_nonneg (mul_nonneg (by norm_num) hrho0) hCK.le
    have h2 : (0 : ℝ) ≤ 8 * rho * CK * Ce := mul_nonneg h1 hCe0.le
    have h3 : (0 : ℝ) ≤ 24 * rho * Ct * CK :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hrho0) hCt0.le) hCK.le
    rw [hCoutdef]
    linarith only [h1, h2, h3]
  have hregK : M.gamma ≤ CK⁻¹ ^ 10 * Disorder.cstar M ^ 10 := by
    refine hreg.trans (mul_le_mul_of_nonneg_right ?_ (pow_nonneg hcs.le 10))
    exact pow_le_pow_left₀ (inv_nonneg.2 (lt_of_lt_of_le hCK hCKCout).le)
      (inv_anti₀ hCK hCKCout) 10
  obtain ⟨lam, hlam0, -, htail, hmean⟩ := hcol M hregK s hs8 hs2
  -- the two collapse coefficients and the envelope
  set K0 : ℝ := CK * ((Real.sqrt (s : ℝ)) ^ 9)⁻¹ with hK0def
  set K1c : ℝ := max 216 CK * ((Real.sqrt (s : ℝ)) ^ 9)⁻¹ with hK1def
  set E : ℝ := (Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ 7)⁻¹ * Real.sqrt M.gamma
    with hEdef
  have hE0 : (0 : ℝ) < E := by
    rw [hEdef]
    exact mul_pos (mul_pos (inv_pos.2 hcs) (inv_pos.2 (pow_pos hsq0 7))) hgsq
  have hinv9 : (0 : ℝ) < ((Real.sqrt (s : ℝ)) ^ 9)⁻¹ := inv_pos.2 (pow_pos hsq0 9)
  have hK00 : (0 : ℝ) < K0 := by rw [hK0def]; exact mul_pos hCK hinv9
  have hK0K1 : K0 ≤ K1c := by
    rw [hK0def, hK1def]
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) hinv9.le
  have hK1ge : 216 * ((Real.sqrt (s : ℝ)) ^ 9)⁻¹ ≤ K1c := by
    rw [hK1def]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hinv9.le
  have hratioeq : K1c / K0 = max 216 CK / CK := by
    rw [hK0def, hK1def]
    field_simp
  -- the family and its amplitude
  set A1 : ℝ := CK * (Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ 5)⁻¹ *
    Real.sqrt M.gamma with hA1def
  have hA10 : (0 : ℝ) < A1 := by
    rw [hA1def]
    exact mul_pos (mul_pos (mul_pos hCK (inv_pos.2 hcs)) (inv_pos.2 (pow_pos hsq0 5))) hgsq
  have hA1E : A1 = CK * (s : ℝ) * E := by
    have hsq : Real.sqrt (s : ℝ) ^ 2 = (s : ℝ) := Real.sq_sqrt hs0.le
    have hne5 : (Real.sqrt (s : ℝ)) ^ 5 ≠ 0 := ne_of_gt (pow_pos hsq0 5)
    have hnes : (s : ℝ) ≠ 0 := ne_of_gt hs0
    have h7 : (Real.sqrt (s : ℝ)) ^ 7 = (Real.sqrt (s : ℝ)) ^ 5 * (s : ℝ) := by
      calc (Real.sqrt (s : ℝ)) ^ 7
          = (Real.sqrt (s : ℝ)) ^ 5 * (Real.sqrt (s : ℝ)) ^ 2 := by ring
        _ = (Real.sqrt (s : ℝ)) ^ 5 * (s : ℝ) := by rw [hsq]
    have hpow : ((Real.sqrt (s : ℝ)) ^ 5)⁻¹
        = (s : ℝ) * ((Real.sqrt (s : ℝ)) ^ 7)⁻¹ := by
      rw [h7, mul_inv]
      field_simp
    rw [hA1def, hEdef, hpow]
    ring
  have hXmeas : ∀ j : ℤ, Measurable (kickCollapsed M s lam K0 j) := fun j =>
    measurable_kickCollapsed M s lam K0 j
  have hX0 : ∀ (j : ℤ) (omega : Cutoff.CutoffSample d),
      0 ≤ kickCollapsed M s lam K0 j omega := fun j omega =>
    kickCollapsed_nonneg M s hlam0 K0 j omega
  have hXtailW : ∀ j : ℤ, IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (kickCollapsed M s lam K0 j) A1 := htail
  have hXtail : ∀ j : ℤ, IsBigO (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (kickCollapsed M s lam K0 j) A1 := fun j =>
    isBigO_of_isBigOWith_of_nonneg (fun omega => hX0 j omega) (hXtailW j)
  have hXmean : ∀ j : ℤ, ∫ omega, kickCollapsed M s lam K0 j omega
      ∂(Cutoff.cutoffSampleLaw M).toMeasure ≤ A1 := hmean
  have hdep : RDependent (Cutoff.cutoffSampleLaw M).toMeasure
      (fun j => kickCollapsed M s lam K0 j) (d + 2) :=
    rDependent_kickCollapsed M s lam K0
      (rDependent_annularKick M s (by omega) (three_pow_dim_clears d))
  -- the geometric closure constant of the window rearrangement
  set G : ℝ := geomTailConst ((s : ℝ) / 4) with hGdef
  have hG0 : (0 : ℝ) < G := geomTailConst_pos (by linarith only [hs0])
  have hGle : G ≤ 8 * ((s : ℝ))⁻¹ := by
    have h : G ≤ 2 / ((s : ℝ) / 4) :=
      geomTailConst_le (alpha := (s : ℝ) / 4) (by linarith only [hs0])
        (by linarith only [hs4])
    refine h.trans (le_of_eq ?_)
    have h4 : ((s : ℝ) / 4)⁻¹ = 4 * ((s : ℝ))⁻¹ := by
      rw [div_eq_mul_inv, mul_inv, inv_inv]
      ring
    rw [div_eq_mul_inv, h4]
    ring
  have hGA1 : G * A1 ≤ 8 * CK * E := by
    have hinv : ((s : ℝ))⁻¹ * (s : ℝ) = 1 := inv_mul_cancel₀ (ne_of_gt hs0)
    calc G * A1 ≤ 8 * ((s : ℝ))⁻¹ * A1 := mul_le_mul_of_nonneg_right hGle hA10.le
      _ = 8 * CK * E * (((s : ℝ))⁻¹ * (s : ℝ)) := by rw [hA1E]; ring
      _ = 8 * CK * E := by rw [hinv, mul_one]
  -- the window average, by the plain `r`-dependent engine
  obtain ⟨Xf, hXfpt, hXfbig⟩ := cesaroAvg_isBigO_of_rDependent
    (P := (Cutoff.cutoffSampleLaw M).toMeasure) (fun j => kickCollapsed M s lam K0 j)
    hA10 hdep hXmeas hXtail hXmean n m hnm
  -- the head, by the countable geometric `Γ₂` closure
  have hHeadW : IsBigOWith (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (fun omega => ∑' p : ℕ, (3 : ℝ) ^ (-(((s : ℝ) / 4) * (p : ℝ))) *
        kickCollapsed M s lam K0 (n - 1 - (p : ℤ)) omega) (Ct * (G * A1)) := by
    rw [hCtdef, hGdef]
    exact weightedTsum_isBigOWith (by norm_num) (by linarith only [hs0]) hA10
      (fun p omega => hX0 _ omega) (fun p => hXmeas _) (fun p => hXtailW _)
  have hHead0 : ∀ omega : Cutoff.CutoffSample d,
      0 ≤ ∑' p : ℕ, (3 : ℝ) ^ (-(((s : ℝ) / 4) * (p : ℝ))) *
        kickCollapsed M s lam K0 (n - 1 - (p : ℤ)) omega := by
    intro omega
    exact tsum_nonneg fun p =>
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hX0 _ omega)
  have hHead : IsBigO (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (fun omega => ∑' p : ℕ, (3 : ℝ) ^ (-(((s : ℝ) / 4) * (p : ℝ))) *
        kickCollapsed M s lam K0 (n - 1 - (p : ℤ)) omega) (Ct * (G * A1)) :=
    isBigO_of_isBigOWith_of_nonneg hHead0 hHeadW
  exact ⟨hs0, hs1, hsq0, hsq1, lam, hlam0, hE0, hK00, hK0K1, hK1ge, hratioeq, hA10, hX0, hG0,
    hGle, hGA1, Xf, hXfpt, hXfbig, hHead⟩

/-- **The `D₁` half of `e.kick.Dees.Dees`.**

There is a dimensional constant `C` such that, in the printed regime
`γ ≤ C^{−10}c⋆^{10}` and on the window `s ∈ [8γ, 1/4]`, for every window
`[n, m]` the Cesàro average of `D₁` splits as a deterministic mean below the printed
envelope plus a `Γ₂` fluctuation of the printed size:

```
avsum_{k=n}^m D₁(k) ≤ Xdet + Xfluc ,
Xdet ≤ C c⋆^{−1}s^{−7/2}√γ ,
Xfluc ≤ 𝒪_{Γ₂}( C c⋆^{−1}s^{−7/2}√γ · (m−n+1)^{−1/2} ) .
```

`s^{−7/2} = ((√s)⁷)⁻¹`, so no `rpow` appears in the envelope.  The additive
`𝒪_{Γ₂}` of the manuscript is unfolded into the explicit `∃ Xdet Xfluc` split,
which is the standard reading (and the one the proved proposition-side
apparatus consumes).

**Hypotheses.**  Exactly the premises of `l.minimal.scale.sep`, with the
window `s ≤ 1/4` of the annular anchor in place of the printed `1/2`
(see `DDecomposition.lean`); `n ≤ m` is the printed `n < m` weakened, and `Ccg`
is free because `D₁`'s good-event gate only ever consumes `𝒢₂`. -/
private theorem stepOneAssembly_estimate1 :
    ∀ (d : ℕ) (CK : ℝ) (M : ABKModel d) (s : { s : ℝ // (0 : ℝ) < s }) (n m : ℤ),
      let rho : ℝ := √√(max (216 : ℝ) CK / CK);
      ∀ (_ : (0 : ℝ) ≤ rho),
        let Ct : ℝ := gammaTriangleConst (2 : ℝ);
        ∀ (_ : (0 : ℝ) < Ct) (_ : (0 : ℝ) < √(↑s : ℝ)) (lam : ℝ),
          let K0 : ℝ := CK * (√(↑s : ℝ) ^ (9 : ℕ))⁻¹;
          let E : ℝ := (Disorder.cstar M)⁻¹ * (√(↑s : ℝ) ^ (7 : ℕ))⁻¹ * √M.gamma;
          let A1 : ℝ := CK * (Disorder.cstar M)⁻¹ * (√(↑s : ℝ) ^ (5 : ℕ))⁻¹ * √M.gamma;
          ∀ (_ : (0 : ℝ) < A1),
            let G : ℝ := geomTailConst ((↑s : ℝ) / (4 : ℝ));
            ∀ (_ : (0 : ℝ) < G) (_ : G ≤ (8 : ℝ) * (↑s : ℝ)⁻¹)
              (_ :
                IsBigO (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d)) (gammaSigma
                  (2 : ℝ))
                  (fun (omega : Cutoff.CutoffSample d) =>
                    ∑' (p : ℕ),
                      (3 : ℝ) ^ (-((↑s : ℝ) / (4 : ℝ) * (↑p : ℝ))) *
                        kickCollapsed M s lam K0 (n - (1 : ℤ) - (↑p : ℤ)) omega)
                  (gammaTriangleConst (2 : ℝ) * (G * A1)))
              (_ : G * A1 ≤ (8 : ℝ) * CK * E),
              let N : ℝ := (↑(m - n + (1 : ℤ)) : ℝ);
              ∀ (_ : (0 : ℝ) < N),
                let ah : ℝ := √(↑s : ℝ) * rho * ((1 : ℝ) / N * min N G);
                ∀  (_ : (0 : ℝ) ≤ ah),
                  IsBigO (↑(Cutoff.cutoffSampleLaw M) : Measure (Cutoff.CutoffSample d))
                    (gammaSigma (2 : ℝ))
                    (fun (omega : Cutoff.CutoffSample d) =>
                      ah *
                        ∑' (p : ℕ),
                          (3 : ℝ) ^ (-((↑s : ℝ) / (4 : ℝ) * (↑p : ℝ))) *
                            kickCollapsed M s lam K0 (n - (1 : ℤ) - (↑p : ℤ)) omega)
                    ((24 : ℝ) * rho * Ct * CK * E * N ^ (-1 / 2 : ℝ)) := by
  intro _ CK M s n _ rho hrho0 Ct hCt0 hsq0 lam K0 E A1 hA10 G hG0 hGle hHead hGA1 N hN0 ah hah0
  have hahdef : ah = √(↑s : ℝ) * rho * ((1 : ℝ) / N * min N G) := rfl
  have hbig0 : IsBigO (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
      (fun omega => ah * ∑' p : ℕ, (3 : ℝ) ^ (-(((s : ℝ) / 4) * (p : ℝ))) *
        kickCollapsed M s lam K0 (n - 1 - (p : ℤ)) omega) (ah * (Ct * (G * A1))) :=
    IsBigO.const_mul hah0 hHead
  refine hbig0.mono_scale ?_
  -- the sharp `min`-coefficient
  have hmin := min_div_le_sqrt_mul_rpow hN0 hG0
  have hsqG : Real.sqrt G ≤ 3 * (Real.sqrt (s : ℝ))⁻¹ := by
    have h1 : Real.sqrt G ≤ Real.sqrt (8 * ((s : ℝ))⁻¹) := Real.sqrt_le_sqrt hGle
    have h2 : Real.sqrt (8 * ((s : ℝ))⁻¹) = Real.sqrt 8 * (Real.sqrt (s : ℝ))⁻¹ := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_inv]
    have h3 : Real.sqrt 8 ≤ 3 := by
      have h := Real.sqrt_le_sqrt (show (8 : ℝ) ≤ 3 ^ 2 by norm_num)
      rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)] at h
    have h4 : Real.sqrt 8 * (Real.sqrt (s : ℝ))⁻¹ ≤ 3 * (Real.sqrt (s : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_right h3 (inv_pos.2 hsq0).le
    rw [h2] at h1
    exact h1.trans h4
  have hcoef : ah ≤ 3 * rho * N ^ (-(1 : ℝ) / 2) := by
    have hstep : (1 / N) * min N G ≤ Real.sqrt G * N ^ (-(1 : ℝ) / 2) := hmin
    have hpow0 : (0 : ℝ) ≤ N ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hN0.le _
    have hsq : Real.sqrt (s : ℝ) * rho * ((1 / N) * min N G)
        ≤ Real.sqrt (s : ℝ) * rho * (Real.sqrt G * N ^ (-(1 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left hstep
        (mul_nonneg (Real.sqrt_nonneg _) hrho0)
    have hsq2 : Real.sqrt (s : ℝ) * rho * (Real.sqrt G * N ^ (-(1 : ℝ) / 2))
        ≤ Real.sqrt (s : ℝ) * rho * (3 * (Real.sqrt (s : ℝ))⁻¹ *
          N ^ (-(1 : ℝ) / 2)) := by
      refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (Real.sqrt_nonneg _) hrho0)
      exact mul_le_mul_of_nonneg_right hsqG hpow0
    have hsqinv : Real.sqrt (s : ℝ) * (Real.sqrt (s : ℝ))⁻¹ = 1 :=
      mul_inv_cancel₀ (ne_of_gt hsq0)
    have hval : Real.sqrt (s : ℝ) * rho * (3 * (Real.sqrt (s : ℝ))⁻¹ *
        N ^ (-(1 : ℝ) / 2)) = 3 * rho * N ^ (-(1 : ℝ) / 2) := by
      calc Real.sqrt (s : ℝ) * rho * (3 * (Real.sqrt (s : ℝ))⁻¹ * N ^ (-(1 : ℝ) / 2))
          = 3 * rho * N ^ (-(1 : ℝ) / 2) *
              (Real.sqrt (s : ℝ) * (Real.sqrt (s : ℝ))⁻¹) := by ring
        _ = 3 * rho * N ^ (-(1 : ℝ) / 2) := by rw [hsqinv, mul_one]
    rw [hahdef, ← hval]
    exact hsq.trans hsq2
  have hHle : Ct * (G * A1) ≤ 8 * Ct * CK * E := by
    calc Ct * (G * A1) ≤ Ct * (8 * CK * E) :=
          mul_le_mul_of_nonneg_left hGA1 hCt0.le
      _ = 8 * Ct * CK * E := by ring
  have hprod : ah * (Ct * (G * A1))
      ≤ (3 * rho * N ^ (-(1 : ℝ) / 2)) * (8 * Ct * CK * E) := by
    refine mul_le_mul hcoef hHle (mul_nonneg hCt0.le (mul_nonneg hG0.le hA10.le)) ?_
    exact mul_nonneg (mul_nonneg (by norm_num) hrho0) (Real.rpow_nonneg hN0.le _)
  refine hprod.trans (le_of_eq ?_)
  ring

theorem exists_stepOne_d1_bound (d : ℕ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ M : ABKModel d, M.gamma ≤ C⁻¹ ^ 10 * Disorder.cstar M ^ 10 →
        ∀ s : {s : ℝ // 0 < s}, 8 * M.gamma ≤ (s : ℝ) → (s : ℝ) ≤ 1 / 4 →
          ∀ (Ccg : ℝ) (n m : ℤ), n ≤ m →
            ∃ Xdet Xfluc : Cutoff.CutoffSample d → ℝ,
              (∀ omega, cesaroAvg (fun k => (dOne M Ccg s k omega).toReal) n m
                  ≤ Xdet omega + Xfluc omega) ∧
              (∀ omega, Xdet omega
                ≤ C * ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ 7)⁻¹ *
                    Real.sqrt M.gamma)) ∧
              IsBigO (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2) Xfluc
                (C * ((Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ 7)⁻¹ *
                    Real.sqrt M.gamma) *
                  ((m - n + 1 : ℤ) : ℝ) ^ (-(1 : ℝ) / 2)) := by
  obtain ⟨CK, hCK, hcol⟩ := exists_kickCollapse d
  have hCe0 : (0 : ℝ) < rDepEngineConst (d + 2) := rDepEngineConst_pos (d + 2)
  have hCt0 : (0 : ℝ) < gammaTriangleConst 2 := gammaTriangleConst_pos
  have hratio1 : (1 : ℝ) ≤ max 216 CK / CK := (one_le_div hCK).2 (le_max_right _ _)
  have hrho1 : (1 : ℝ) ≤ Real.sqrt (Real.sqrt (max 216 CK / CK)) :=
    one_le_sqrt_of_one_le (one_le_sqrt_of_one_le hratio1)
  have hrho0 : (0 : ℝ) ≤ Real.sqrt (Real.sqrt (max 216 CK / CK)) := by
    linarith only [hrho1]
  -- the output constant
  refine ⟨CK + 8 * Real.sqrt (Real.sqrt (max 216 CK / CK)) * CK +
      2 * (8 * Real.sqrt (Real.sqrt (max 216 CK / CK)) * CK * rDepEngineConst (d + 2) +
        24 * Real.sqrt (Real.sqrt (max 216 CK / CK)) * gammaTriangleConst 2 * CK), ?_, ?_⟩
  · have h1 : (0 : ℝ) ≤ 8 * Real.sqrt (Real.sqrt (max 216 CK / CK)) * CK :=
      mul_nonneg (mul_nonneg (by norm_num) hrho0) hCK.le
    have h2 : (0 : ℝ) ≤ 8 * Real.sqrt (Real.sqrt (max 216 CK / CK)) * CK *
        rDepEngineConst (d + 2) := mul_nonneg h1 hCe0.le
    have h3 : (0 : ℝ) ≤ 24 * Real.sqrt (Real.sqrt (max 216 CK / CK)) *
        gammaTriangleConst 2 * CK :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hrho0) hCt0.le) hCK.le
    linarith only [hCK, h1, h2, h3]
  intro M hreg s hs8 hs4 Ccg n m hnm
  set rho : ℝ := Real.sqrt (Real.sqrt (max 216 CK / CK)) with hrhodef
  set Ce : ℝ := rDepEngineConst (d + 2) with hCedef
  set Ct : ℝ := gammaTriangleConst 2 with hCtdef
  set Cout : ℝ := CK + 8 * rho * CK + 2 * (8 * rho * CK * Ce + 24 * rho * Ct * CK)
    with hCoutdef
  -- standing quantities
  have hgam : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  obtain ⟨hs0, hs1, hsq0, hsq1, lam, hlam0, hE0, hK00, hK0K1, hK1ge, hratioeq, hA10, hX0, hG0,
    hGle, hGA1, Xf, hXfpt, hXfbig, hHead⟩ :=
    @stepOneAssembly_momentBounds1 (d) (CK) (hCK) (hcol) (M) (s) (hs8) (hs4) (n) (m) (hnm) (hrho0)
      (hCe0) (hCt0)  (hreg)  (hgam)
  set K0 : ℝ := CK * ((Real.sqrt (s : ℝ)) ^ 9)⁻¹ with hK0def
  set K1c : ℝ := max 216 CK * ((Real.sqrt (s : ℝ)) ^ 9)⁻¹ with hK1def
  set E : ℝ := (Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ 7)⁻¹ * Real.sqrt M.gamma
    with hEdef
  set A1 : ℝ := CK * (Disorder.cstar M)⁻¹ * ((Real.sqrt (s : ℝ)) ^ 5)⁻¹ *
    Real.sqrt M.gamma with hA1def
  set G : ℝ := geomTailConst ((s : ℝ) / 4) with hGdef
  -- the window normaliser
  set N : ℝ := ((m - n + 1 : ℤ) : ℝ) with hNdef
  have hN1 : (1 : ℝ) ≤ N := one_le_window hnm
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN1
  -- the two coefficients of the rearranged display
  set aw : ℝ := Real.sqrt (s : ℝ) * rho * G with hawdef
  set ah : ℝ := Real.sqrt (s : ℝ) * rho * ((1 / N) * min N G) with hahdef
  obtain ⟨haw0, hah0, hdom⟩ :=
    (show ((0 : ℝ) ≤ aw) ∧ ((0 : ℝ) ≤ ah) ∧ (∀ omega : Cutoff.CutoffSample d,
      cesaroAvg (fun k => (dOne M Ccg s k omega).toReal) n m
        ≤ aw * cesaroAvg (fun j => kickCollapsed M s lam K0 j omega) n m +
          ah * ∑' p : ℕ, (3 : ℝ) ^ (-(((s : ℝ) / 4) * (p : ℝ))) *
            kickCollapsed M s lam K0 (n - 1 - (p : ℤ)) omega) from
      @stepOneAssembly_comparisonBounds1 (d) (CK) (M) (s) (Ccg) (n) (m) (hnm) (hrho0)
        (hs0) (hs1) (lam) (hlam0) (hK00) (hK0K1) (hK1ge) (hratioeq) (hX0) (hG0) (hN0)
          )
  -- assemble
  refine ⟨fun _ => aw * A1, fun omega => aw * Xf omega +
    ah * ∑' p : ℕ, (3 : ℝ) ^ (-(((s : ℝ) / 4) * (p : ℝ))) *
      kickCollapsed M s lam K0 (n - 1 - (p : ℤ)) omega, ?_, ?_, ?_⟩
  · intro omega
    have hstep : aw * cesaroAvg (fun j => kickCollapsed M s lam K0 j omega) n m
        ≤ aw * (A1 + Xf omega) := mul_le_mul_of_nonneg_left (hXfpt omega) haw0
    have hexp : aw * (A1 + Xf omega) = aw * A1 + aw * Xf omega := by ring
    linarith only [hdom omega, hstep, hexp.le, hexp.ge]
  · -- the deterministic mean
    intro _
    have hstep : aw * A1 ≤ 8 * rho * CK * E := by
      have hsq : Real.sqrt (s : ℝ) * rho * (G * A1)
          ≤ Real.sqrt (s : ℝ) * rho * (8 * CK * E) :=
        mul_le_mul_of_nonneg_left hGA1 (mul_nonneg (Real.sqrt_nonneg _) hrho0)
      have hfin : Real.sqrt (s : ℝ) * rho * (8 * CK * E) ≤ 8 * rho * CK * E := by
        have hbase : (0 : ℝ) ≤ rho * (8 * CK * E) :=
          mul_nonneg hrho0 (mul_nonneg (mul_nonneg (by norm_num) hCK.le) hE0.le)
        have h := mul_le_mul_of_nonneg_right hsq1 hbase
        rw [one_mul] at h
        calc Real.sqrt (s : ℝ) * rho * (8 * CK * E)
            = Real.sqrt (s : ℝ) * (rho * (8 * CK * E)) := by ring
          _ ≤ rho * (8 * CK * E) := h
          _ = 8 * rho * CK * E := by ring
      calc aw * A1 = Real.sqrt (s : ℝ) * rho * (G * A1) := by rw [hawdef]; ring
        _ ≤ Real.sqrt (s : ℝ) * rho * (8 * CK * E) := hsq
        _ ≤ 8 * rho * CK * E := hfin
    have hCle : 8 * rho * CK * E ≤ Cout * E := by
      refine mul_le_mul_of_nonneg_right ?_ hE0.le
      have h2 : (0 : ℝ) ≤ 8 * rho * CK * Ce :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hrho0) hCK.le) hCe0.le
      have h3 : (0 : ℝ) ≤ 24 * rho * Ct * CK :=
        mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hrho0) hCt0.le) hCK.le
      rw [hCoutdef]
      linarith only [hCK, h2, h3]
    exact hstep.trans hCle
  · -- the fluctuation
    have hwin : IsBigO (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
        (fun omega => aw * Xf omega)
        (8 * rho * CK * Ce * E * N ^ (-(1 : ℝ) / 2)) := by
      have hbig0 : IsBigO (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
          (fun omega => aw * Xf omega) (aw * (Ce * A1 * N ^ (-(1 : ℝ) / 2))) :=
        IsBigO.const_mul haw0 hXfbig
      refine hbig0.mono_scale ?_
      have hpow0 : (0 : ℝ) ≤ N ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hN0.le _
      have hbase : aw * (Ce * A1) ≤ 8 * rho * CK * Ce * E := by
        have hstep : Real.sqrt (s : ℝ) * rho * Ce * (G * A1)
            ≤ Real.sqrt (s : ℝ) * rho * Ce * (8 * CK * E) := by
          refine mul_le_mul_of_nonneg_left hGA1 ?_
          exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hrho0) hCe0.le
        have hbnd : (0 : ℝ) ≤ rho * Ce * (8 * CK * E) :=
          mul_nonneg (mul_nonneg hrho0 hCe0.le)
            (mul_nonneg (mul_nonneg (by norm_num) hCK.le) hE0.le)
        have hlast := mul_le_mul_of_nonneg_right hsq1 hbnd
        rw [one_mul] at hlast
        calc aw * (Ce * A1) = Real.sqrt (s : ℝ) * rho * Ce * (G * A1) := by
              rw [hawdef]; ring
          _ ≤ Real.sqrt (s : ℝ) * rho * Ce * (8 * CK * E) := hstep
          _ = Real.sqrt (s : ℝ) * (rho * Ce * (8 * CK * E)) := by ring
          _ ≤ rho * Ce * (8 * CK * E) := hlast
          _ = 8 * rho * CK * Ce * E := by ring
      calc aw * (Ce * A1 * N ^ (-(1 : ℝ) / 2))
          = (aw * (Ce * A1)) * N ^ (-(1 : ℝ) / 2) := by ring
        _ ≤ (8 * rho * CK * Ce * E) * N ^ (-(1 : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right hbase hpow0
        _ = 8 * rho * CK * Ce * E * N ^ (-(1 : ℝ) / 2) := by ring
    have hhead : IsBigO (Cutoff.cutoffSampleLaw M).toMeasure (gammaSigma 2)
        (fun omega => ah * ∑' p : ℕ, (3 : ℝ) ^ (-(((s : ℝ) / 4) * (p : ℝ))) *
          kickCollapsed M s lam K0 (n - 1 - (p : ℤ)) omega)
        (24 * rho * Ct * CK * E * N ^ (-(1 : ℝ) / 2))  := @stepOneAssembly_estimate1 (d) (CK) (M)
          (s) (n) (m) (hrho0) (hCt0) (hsq0) (lam) (hA10) (hG0) (hGle) (hHead) (hGA1) (hN0)
             (hah0)
    have hA1nn : (0 : ℝ) ≤ 8 * rho * CK * Ce * E * N ^ (-(1 : ℝ) / 2) := by
      refine mul_nonneg (mul_nonneg ?_ hE0.le) (Real.rpow_nonneg hN0.le _)
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hrho0) hCK.le) hCe0.le
    have hA2nn : (0 : ℝ) ≤ 24 * rho * Ct * CK * E * N ^ (-(1 : ℝ) / 2) := by
      refine mul_nonneg (mul_nonneg ?_ hE0.le) (Real.rpow_nonneg hN0.le _)
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hrho0) hCt0.le) hCK.le
    have hsum := isBigO_gammaSigma_add2'
      (μ := (Cutoff.cutoffSampleLaw M).toMeasure) (by norm_num : (0 : ℝ) < 2)
      hA1nn hA2nn hwin hhead
    refine hsum.mono_scale ?_
    have hL2 : (1 + Real.log 2) ^ ((2 : ℝ))⁻¹ ≤ 2 := triangleConstTwo_le
    have hpow0 : (0 : ℝ) ≤ N ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hN0.le _
    have hbig : (0 : ℝ) ≤ 8 * rho * CK * Ce * E * N ^ (-(1 : ℝ) / 2) +
        24 * rho * Ct * CK * E * N ^ (-(1 : ℝ) / 2) := add_nonneg hA1nn hA2nn
    have hstep1 : (1 + Real.log 2) ^ ((2 : ℝ))⁻¹ *
        (8 * rho * CK * Ce * E * N ^ (-(1 : ℝ) / 2) +
          24 * rho * Ct * CK * E * N ^ (-(1 : ℝ) / 2))
        ≤ 2 * (8 * rho * CK * Ce * E * N ^ (-(1 : ℝ) / 2) +
          24 * rho * Ct * CK * E * N ^ (-(1 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_right hL2 hbig
    have hstep2 : 2 * (8 * rho * CK * Ce * E * N ^ (-(1 : ℝ) / 2) +
        24 * rho * Ct * CK * E * N ^ (-(1 : ℝ) / 2))
        ≤ Cout * E * N ^ (-(1 : ℝ) / 2) := by
      have hfac : 2 * (8 * rho * CK * Ce * E * N ^ (-(1 : ℝ) / 2) +
          24 * rho * Ct * CK * E * N ^ (-(1 : ℝ) / 2))
          = (2 * (8 * rho * CK * Ce + 24 * rho * Ct * CK)) * E *
            N ^ (-(1 : ℝ) / 2) := by ring
      rw [hfac]
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hE0.le) hpow0
      have h1 : (0 : ℝ) ≤ 8 * rho * CK := mul_nonneg (mul_nonneg (by norm_num) hrho0) hCK.le
      rw [hCoutdef]
      linarith only [hCK, h1]
    exact hstep1.trans hstep2

end

end Algsuperdiff.Section4.Provider.MinimalScale
