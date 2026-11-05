/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenCaccGradient

/-!
# StepSevenEndPoincare

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 7d, part one: `e.cg.Poincare.with.rhs.grad.applied`

## The target

```text
  3^{-m'}‖∇u‖_{B^{-1}_{2,2}(z'+□_{m'-1})} 1_{𝒢(m',z;·,·)}
    ≤ C σ_{m'}^{-1/2} ν^{1/2}‖∇u‖_{L²(z'+□_{m'-1})}
        + C σ_{m'}^{-1} 3^{sm'}[𝐠]_{H^s(z'+□_{m'-1})}
    ≤ C 3^{(1/2)(d+γ)(m-m')} ( σ_m^{-1/2} ν^{1/2}‖∇u‖_{L²(□_m)}
        + σ_m^{-1} 3^{sm}[𝐠]_{H^s(□_m)} ) .
```

Two independent inequalities, proved here as two independent theorems on the S
the display names (/ discipline), plus the `C₁`-largeness accounting that
absorbs the transport exponent.

## The scalar carriers

* `besov` — `3^{-m'}‖∇u‖_{B^{-1}_{2,2}(z'+□_{m'-1})}·1_{𝒢}`, the left-hand
  side.
* `lamInv` — `λ_{1/4,2}^{-1}(z+□_{m'};𝐚_{L,m'})·1_{𝒢}`, the coarse-graining
  lemma's ellipticity weight at the lattice centre.
* `shomMpInv` / `shomMinv` — `σ_{m'}^{-1}` and `σ_m^{-1}`.
* `gradLoc` / `gradM` — `ν^{1/2}‖∇u‖_{L²}` on `z'+□_{m'-1}` and on `□_m`: for
  `𝐚_L = ν I + 𝐤` with `𝐤` antisymmetric this is the symmetric coefficient
  energy.
* `dataLoc` / `dataM` — `3^{sm'}[𝐠]_{H^s(z'+□_{m'-1})}` and
  `3^{sm}[𝐠]_{H^s(□_m)}`.
* `Kg`, `Kd`, `Ks` — the three transport factors of the second inequality: the
  `L²` volume ratio, the `H^s` window restriction, and the `σ` comparison.

## The conditional inputs, and nothing else

* **`hcg`** — `l.coarse.graining.RHS` applied on `z'+□_{m'-1}` at the good scale
  `m'`, in the ellipticity-weighted form the display quotes:
  `besov ≤ C(√lamInv·gradLoc) + C(lamInv·dataLoc)`.
* **`hlambda`** — `e.lambda.stability.applied`, the lower leg at `k' = m'`:
  `λ_{1/4,2}^{-1}(z+□_{m'};𝐚_{L,m'})1_{𝒢} ≤ C σ_{m'}^{-1}`.  This is the first
  conjunct of the printed display, in exactly the rendering discipline the
  Step-7c `hlambda` uses for the second conjunct (lattice centre, indicator absorbed,
  one scalar inequality `weight ≤ C · σ-power`), so that a single future
  Step-7b theorem discharges both.

The three transport ingredients `hgrad`, `hdata`, `hshom` are *not* conditional
inputs of this module: they are the caller's own geometry/`σ` facts, and each
is supplied unconditionally elsewhere in the development
(`normalizedL2On_le_of_subset` for `Kg`, the window restriction for `Kd`, and
`sigmaBar_le_rpow_mul_sigmaBar_of_inductionState` for `Ks`).

## The `C₁`-largeness accounting (the transport exponent)

The transport exponent `(1/2)(d+γ)(m-m')` is absorbed into
`3^{(1/4)(1-α)(m-n)}` by the third and fourth `C₁`-largeness conditions.  The
`C₁` floor already carries the exact clause: `stepOneC1`'s second maximand is
`2d+2`, which reads as `2(d+γ) ≤ C₁` for `γ ≤ 1` — the pin whose docstring
names *this* transport.  So

```text
  (1/2)(d+γ)(m-m') ≤ (1/2)(d+γ)·3 + 1/4 + (1/4)(1-α)(m-n)
```

with NO new largeness demand: the quarter-bound on `(d+γ)/(2C₁)` needs
exactly `2d+2 ≤ C₁` and `γ ≤ 1`.  Nothing was enlarged.

## References

* ABK26, `e.cg.Poincare.with.rhs.grad.applied`.
* ABK26, graining.; `e.lambda.stability.applied`.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

noncomputable section

/-! ## 2. The first inequality: the coarse-graining Poincaré after `hlambda` -/

/-- **`e.cg.Poincare.with.rhs.grad.applied`, first inequality**, on abstract reals.

`l.coarse.graining.RHS` produces the Besov left-hand side against the weight
`λ^{-1}` (square root on the gradient leg, full power on the data leg);
`e.lambda.stability.applied` replaces `λ^{-1}` by `C σ_{m'}^{-1}`.  The two
legs are then carried by the single constant `Ccg(√Clam + Clam)`. -/
theorem cgPoincareShom_compose {Ccg Clam lamInv shomInv besov gradLoc dataLoc : ℝ}
    (hCcg : 0 ≤ Ccg) (hClam : 0 ≤ Clam) (hshomInv : 0 ≤ shomInv)
    (hgradLoc : 0 ≤ gradLoc) (hdataLoc : 0 ≤ dataLoc)
    (hcg : besov ≤ Ccg * (Real.sqrt lamInv * gradLoc) + Ccg * (lamInv * dataLoc))
    (hlambda : lamInv ≤ Clam * shomInv) :
    besov ≤ (Ccg * (Real.sqrt Clam + Clam)) * (Real.sqrt shomInv * gradLoc) +
      (Ccg * (Real.sqrt Clam + Clam)) * (shomInv * dataLoc) := by
  have hL : (0 : ℝ) ≤ Real.sqrt Clam := Real.sqrt_nonneg _
  have hS : (0 : ℝ) ≤ Real.sqrt shomInv := Real.sqrt_nonneg _
  have hsqrt : Real.sqrt lamInv ≤ Real.sqrt Clam * Real.sqrt shomInv := by
    calc Real.sqrt lamInv ≤ Real.sqrt (Clam * shomInv) := Real.sqrt_le_sqrt hlambda
      _ = Real.sqrt Clam * Real.sqrt shomInv := Real.sqrt_mul hClam shomInv
  have h1 : Ccg * (Real.sqrt lamInv * gradLoc) ≤
      Ccg * (Real.sqrt Clam * (Real.sqrt shomInv * gradLoc)) := by
    have hstep : Real.sqrt lamInv * gradLoc ≤
        Real.sqrt Clam * (Real.sqrt shomInv * gradLoc) := by
      have h := mul_le_mul_of_nonneg_right hsqrt hgradLoc
      calc Real.sqrt lamInv * gradLoc
          ≤ Real.sqrt Clam * Real.sqrt shomInv * gradLoc := h
        _ = Real.sqrt Clam * (Real.sqrt shomInv * gradLoc) := by ring
    exact mul_le_mul_of_nonneg_left hstep hCcg
  have h2 : Ccg * (lamInv * dataLoc) ≤ Ccg * (Clam * (shomInv * dataLoc)) := by
    have hstep : lamInv * dataLoc ≤ Clam * (shomInv * dataLoc) := by
      have h := mul_le_mul_of_nonneg_right hlambda hdataLoc
      calc lamInv * dataLoc ≤ Clam * shomInv * dataLoc := h
        _ = Clam * (shomInv * dataLoc) := by ring
    exact mul_le_mul_of_nonneg_left hstep hCcg
  have p1 : 0 ≤ Ccg * Clam * (Real.sqrt shomInv * gradLoc) :=
    mul_nonneg (mul_nonneg hCcg hClam) (mul_nonneg hS hgradLoc)
  have p2 : 0 ≤ Ccg * Real.sqrt Clam * (shomInv * dataLoc) :=
    mul_nonneg (mul_nonneg hCcg hL) (mul_nonneg hshomInv hdataLoc)
  have hkey : Ccg * (Real.sqrt Clam * (Real.sqrt shomInv * gradLoc)) +
      Ccg * (Clam * (shomInv * dataLoc)) +
      (Ccg * Clam * (Real.sqrt shomInv * gradLoc) +
        Ccg * Real.sqrt Clam * (shomInv * dataLoc)) =
      (Ccg * (Real.sqrt Clam + Clam)) * (Real.sqrt shomInv * gradLoc) +
        (Ccg * (Real.sqrt Clam + Clam)) * (shomInv * dataLoc) := by
    ring
  linarith only [hcg, h1, h2, p1, p2, hkey.ge, hkey.le]

/-! ## 3. The second inequality: the transport to `□_m` -/

/-- **`e.cg.Poincare.with.rhs.grad.applied`, second inequality**, on abstract
reals: the three transports

```text
  gradLoc ≤ Kg · gradM ,   dataLoc ≤ Kd · dataM ,   σ_{m'}^{-1} ≤ Ks · σ_m^{-1}
```

(the `L²` volume ratio, the `H^s` window restriction, and the `σ`
comparison) carry the weighted bracket from `z'+□_{m'-1}` to `□_m` at the two
factors `√Ks·Kg` and `Ks·Kd`. -/
theorem cgPoincareTransport_compose {Kg Kd Ks gradLoc dataLoc gradM dataM
    shomMpInv shomMinv : ℝ}
    (hKs : 0 ≤ Ks) (hshomMinv : 0 ≤ shomMinv)
    (hgradLoc : 0 ≤ gradLoc) (hdataLoc : 0 ≤ dataLoc)
    (hgrad : gradLoc ≤ Kg * gradM) (hdata : dataLoc ≤ Kd * dataM)
    (hshom : shomMpInv ≤ Ks * shomMinv) :
    Real.sqrt shomMpInv * gradLoc + shomMpInv * dataLoc ≤
      (Real.sqrt Ks * Kg) * (Real.sqrt shomMinv * gradM) +
        (Ks * Kd) * (shomMinv * dataM) := by
  have hKsS : (0 : ℝ) ≤ Real.sqrt Ks := Real.sqrt_nonneg _
  have hSm : (0 : ℝ) ≤ Real.sqrt shomMinv := Real.sqrt_nonneg _
  have hsqrt : Real.sqrt shomMpInv ≤ Real.sqrt Ks * Real.sqrt shomMinv := by
    calc Real.sqrt shomMpInv ≤ Real.sqrt (Ks * shomMinv) := Real.sqrt_le_sqrt hshom
      _ = Real.sqrt Ks * Real.sqrt shomMinv := Real.sqrt_mul hKs shomMinv
  have h1 : Real.sqrt shomMpInv * gradLoc ≤
      (Real.sqrt Ks * Real.sqrt shomMinv) * (Kg * gradM) :=
    mul_le_mul hsqrt hgrad hgradLoc (mul_nonneg hKsS hSm)
  have h2 : shomMpInv * dataLoc ≤ (Ks * shomMinv) * (Kd * dataM) :=
    mul_le_mul hshom hdata hdataLoc (mul_nonneg hKs hshomMinv)
  have hkey1 : (Real.sqrt Ks * Real.sqrt shomMinv) * (Kg * gradM) =
      (Real.sqrt Ks * Kg) * (Real.sqrt shomMinv * gradM) := by ring
  have hkey2 : (Ks * shomMinv) * (Kd * dataM) = (Ks * Kd) * (shomMinv * dataM) := by
    ring
  linarith only [h1, h2, hkey1.ge, hkey1.le, hkey2.ge, hkey2.le]

/-! ## 4. The display -/

/-- **`e.cg.Poincare.with.rhs.grad.applied`, as printed.**

The two inequalities composed, at a single transport factor `Ktr` dominating
both legs' factors:

```text
  besov ≤ Ccg(√Clam + Clam) · Ktr · ( √σ_m^{-1}·gradM + σ_m^{-1}·dataM ) .
```

`hcg` and `hlambda` are the only conditional
inputs; `hgrad`, `hdata`, `hshom`, `hKgb`, `hKdb` are the caller's own
transport data. -/
theorem stepSevenCgPoincareApplied {Ccg Clam Kg Kd Ks Ktr lamInv shomMpInv shomMinv
    besov gradLoc dataLoc gradM dataM : ℝ}
    (hCcg : 0 ≤ Ccg) (hClam : 0 ≤ Clam) (hKs : 0 ≤ Ks)
    (hshomMpInv : 0 ≤ shomMpInv) (hshomMinv : 0 ≤ shomMinv)
    (hgradLoc : 0 ≤ gradLoc) (hdataLoc : 0 ≤ dataLoc)
    (hgradM : 0 ≤ gradM) (hdataM : 0 ≤ dataM)
    (hcg : besov ≤ Ccg * (Real.sqrt lamInv * gradLoc) + Ccg * (lamInv * dataLoc))
    (hlambda : lamInv ≤ Clam * shomMpInv)
    (hgrad : gradLoc ≤ Kg * gradM) (hdata : dataLoc ≤ Kd * dataM)
    (hshom : shomMpInv ≤ Ks * shomMinv)
    (hKgb : Real.sqrt Ks * Kg ≤ Ktr) (hKdb : Ks * Kd ≤ Ktr) :
    besov ≤ (Ccg * (Real.sqrt Clam + Clam)) * Ktr *
      (Real.sqrt shomMinv * gradM + shomMinv * dataM) := by
  have hCout : (0 : ℝ) ≤ Ccg * (Real.sqrt Clam + Clam) :=
    mul_nonneg hCcg (add_nonneg (Real.sqrt_nonneg _) hClam)
  have hA := cgPoincareShom_compose hCcg hClam hshomMpInv hgradLoc hdataLoc hcg hlambda
  have hB := cgPoincareTransport_compose hKs hshomMinv hgradLoc hdataLoc hgrad hdata hshom
  -- the bracket at `m'` is dominated by `Ktr` times the bracket at `m`
  have hg : (0 : ℝ) ≤ Real.sqrt shomMinv * gradM :=
    mul_nonneg (Real.sqrt_nonneg _) hgradM
  have hdd : (0 : ℝ) ≤ shomMinv * dataM := mul_nonneg hshomMinv hdataM
  have hC1 : (Real.sqrt Ks * Kg) * (Real.sqrt shomMinv * gradM) ≤
      Ktr * (Real.sqrt shomMinv * gradM) := mul_le_mul_of_nonneg_right hKgb hg
  have hC2 : (Ks * Kd) * (shomMinv * dataM) ≤ Ktr * (shomMinv * dataM) :=
    mul_le_mul_of_nonneg_right hKdb hdd
  have hbr : Real.sqrt shomMpInv * gradLoc + shomMpInv * dataLoc ≤
      Ktr * (Real.sqrt shomMinv * gradM + shomMinv * dataM) := by
    have hexp : Ktr * (Real.sqrt shomMinv * gradM) + Ktr * (shomMinv * dataM) =
        Ktr * (Real.sqrt shomMinv * gradM + shomMinv * dataM) := by ring
    linarith only [hB, hC1, hC2, hexp.ge, hexp.le]
  have hfin : (Ccg * (Real.sqrt Clam + Clam)) *
      (Real.sqrt shomMpInv * gradLoc + shomMpInv * dataLoc) ≤
      (Ccg * (Real.sqrt Clam + Clam)) *
        (Ktr * (Real.sqrt shomMinv * gradM + shomMinv * dataM)) :=
    mul_le_mul_of_nonneg_left hbr hCout
  have hexp2 : (Ccg * (Real.sqrt Clam + Clam)) *
      (Real.sqrt shomMpInv * gradLoc + shomMpInv * dataLoc) =
      (Ccg * (Real.sqrt Clam + Clam)) * (Real.sqrt shomMpInv * gradLoc) +
        (Ccg * (Real.sqrt Clam + Clam)) * (shomMpInv * dataLoc) := by ring
  have hexp3 : (Ccg * (Real.sqrt Clam + Clam)) *
      (Ktr * (Real.sqrt shomMinv * gradM + shomMinv * dataM)) =
      (Ccg * (Real.sqrt Clam + Clam)) * Ktr *
        (Real.sqrt shomMinv * gradM + shomMinv * dataM) := by ring
  linarith only [hA, hfin, hexp2.ge, hexp2.le, hexp3.ge, hexp3.le]

end

end Algsuperdiff.Section4.Provider.Regularity
