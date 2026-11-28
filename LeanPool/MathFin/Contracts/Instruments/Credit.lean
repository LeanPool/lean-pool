/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Contracts.Instruments.FixedIncome

/-!
# A credit default swap, as a contract

The credit event is observed through the default indicator process `N u = 1{τ ≤ u}`, the single
underlying `()` of the scenario (`Models/Credit/DefaultTime.lean` supplies it from a default
time `τ`). `N` enters `[1, ∞)` exactly at `τ`, and `Contract.payAtHit` pays at the first time an
observed underlying enters a set, so a payment at the default time is a contract:

* the **protection leg paid at the default time** pays the loss `1 − R` at `τ` if `τ ≤ T`
  (`cdsProtectionAtDefault`), the contract whose value under the Cox default time, at a flat
  rate, is `Cox.protectionLeg`.

The tower otherwise pays at fixed dates, so the CDS is also written on a payment grid
`t 0 ≤ t 1 ≤ … ≤ t n`:

* the **premium leg** pays the spread `s` on each accrual period `[tᵢ, tᵢ₊₁]` if the name has
  survived to the payment date, `s · (tᵢ₊₁ − tᵢ) · (1 − N tᵢ₊₁)` at `tᵢ₊₁` (`cdsPremiumLeg`);
  no premium accrued between the last payment and a default is paid;
* the **protection leg** pays the loss `1 − R` at the end of the period in which default
  happens, `(1 − R) · (N tᵢ₊₁ − N tᵢ)` at `tᵢ₊₁` (`cdsProtectionLeg`);
* the **protection buyer** receives the protection leg and pays the premium leg (`cdsBuyer`).

The grid legs are `payFlows`, so their path value is a finite sum (`pathPV_cdsPremiumLeg`,
`pathPV_cdsProtectionLeg`). Default is paid at the end of its period, not at `τ`: the grid
protection leg is the discretisation of `cdsProtectionAtDefault`
(`Models/Credit/DefaultTimeMesh.lean` proves the limit). There is no continuous premium
stream in the tower, so the premium leg exists only on the grid.

## Main definitions

* `cdsProtectionAtDefault`, `cdsPremiumLeg`, `cdsProtectionLeg`, `cdsBuyer`.

## Main results

* `pathPV_cdsPremiumLeg`, `pathPV_cdsProtectionLeg`.

## Tags

credit default swap, CDS premium leg, protection leg, default indicator, accrual grid, MSC 91G40,
JEL G12, JEL G33
-/

@[expose] public section

open scoped NNReal

namespace MathFin.Contracts

/-- The **protection leg paid at the default time**: `(1 − R)·N_T` is paid at the first time the
default indicator `N` reaches `1`, that is at `τ`, and nothing if the name never defaults.
`N_T = 1{τ ≤ T}`, so the loss `1 − R` is paid at `τ` exactly when default happens by `T`. -/
noncomputable def cdsProtectionAtDefault (T : ℝ≥0) (R : ℝ) : Contract Unit :=
  .payAtHit () (Set.Ici 1) (.mul (.const (1 - R)) (.obs () T))

/-- The **premium leg** of a CDS at spread `s` on the grid `t`: at `t (i + 1)`, for `i < n`, pay
`s · (t (i + 1) − t i)` if no default has happened by then, i.e. times `1 − N (t (i + 1))`
for the default indicator `N`. -/
noncomputable def cdsPremiumLeg (t : ℕ → ℝ≥0) (s : ℝ) (n : ℕ) : Contract Unit :=
  payFlows (fun i ↦ t (i + 1))
    (fun i ↦ .mul (.const (s * ((t (i + 1) : ℝ) - t i))) (.sub (.const 1) (.obs () (t (i + 1))))) n

/-- The **protection leg** of a CDS with recovery `R` on the grid `t`: at `t (i + 1)`, for
`i < n`, pay `(1 − R) · (N (t (i + 1)) − N (t i))`, the loss given default if default happened
during `(t i, t (i + 1)]`. -/
noncomputable def cdsProtectionLeg (t : ℕ → ℝ≥0) (R : ℝ) (n : ℕ) : Contract Unit :=
  payFlows (fun i ↦ t (i + 1))
    (fun i ↦ .mul (.const (1 - R)) (.sub (.obs () (t (i + 1))) (.obs () (t i)))) n

/-- The **protection buyer's** CDS: receive the protection leg, pay the premium leg. -/
noncomputable def cdsBuyer (t : ℕ → ℝ≥0) (s R : ℝ) (n : ℕ) : Contract Unit :=
  .both (cdsProtectionLeg t R n) (.scale (-1) (cdsPremiumLeg t s n))

/-- Along a scenario `σ` whose observation at `u` is the default indicator `σ () u`, the premium
leg is worth `∑ D(tᵢ₊₁) · s (tᵢ₊₁ − tᵢ) (1 − σ () tᵢ₊₁)`. -/
theorem pathPV_cdsPremiumLeg (D : ℝ≥0 → ℝ) (σ : Scenario Unit) (t : ℕ → ℝ≥0) (s : ℝ) (n : ℕ) :
    (cdsPremiumLeg t s n).pathPV D σ
      = ∑ i ∈ Finset.range n, D (t (i + 1)) *
          (s * ((t (i + 1) : ℝ) - t i) * (1 - σ () (t (i + 1)))) := by
  simp [cdsPremiumLeg, pathPV_payFlows, Payoff.eval]

/-- Along a scenario `σ` whose observation at `u` is the default indicator `σ () u`, the
protection leg is worth `∑ D(tᵢ₊₁) · (1 − R) (σ () tᵢ₊₁ − σ () tᵢ)`. -/
theorem pathPV_cdsProtectionLeg (D : ℝ≥0 → ℝ) (σ : Scenario Unit) (t : ℕ → ℝ≥0) (R : ℝ)
    (n : ℕ) :
    (cdsProtectionLeg t R n).pathPV D σ
      = ∑ i ∈ Finset.range n, D (t (i + 1)) * ((1 - R) * (σ () (t (i + 1)) - σ () (t i))) := by
  simp [cdsProtectionLeg, pathPV_payFlows, Payoff.eval]

end MathFin.Contracts
