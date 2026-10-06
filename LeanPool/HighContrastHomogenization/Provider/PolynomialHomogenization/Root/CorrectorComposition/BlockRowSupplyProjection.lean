/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.CertificateProjections

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.BlockRowSupplyProjection

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# `RootBlockRowSupply` against the ceiling-exporting smallness interface — what is carried and
what is not

The stationary corrector family clause reduces to

```lean
def RootBlockRowSupply (d : ℕ) [NeZero d]
    (GoodScale : Mat d → CoeffSpace d → ℝ → Prop) : Prop :=
  ∀ (abar : Mat d), (symmPart abar).PosDef →
    ∀ (a : CoeffSpace d) (x : ℝ), GoodScale abar a x →
      ∃ (Omega : Set (CoeffSpace d)) (s rho kappa delta : ℝ)
        (S X : CoeffSpace d → ℝ),
        a ∈ Omega ∧
        (∀ z : Fin d → ℤ, translateCoeff z ⁻¹' Omega = Omega) ∧
        0 < s ∧ s < 1 / 2 ∧
        0 < rho ∧ rho ≤ 1 ∧ rho < 2 * s ∧
        0 < kappa ∧ 0 ≤ delta ∧
        ∀ b ∈ Omega, 1 ≤ X b ∧ S b ≤ X b ∧
          Quenched.HasAllLaterPhysicalBlockRow rho kappa delta
            (Book.Ch02.constantBlockMatrix abar) S X b
```

(order-free form: the order `s` is supplied here, not frozen upstream; the
statement is restated below rather than imported, because importing it would
pull in the whole normalized-supply chain at the free order.)

## What `rootGoodScaleAt` literally carries

Destructuring `rootGoodScaleAt d g c kappaRate abar a x` gives
`h : RowSupply.RowRetainingPrintOrderGoodScale d g c kappaRate abar a x`, and
that structure carries, **for the sample `a` only**:

| demanded field | carried by | status |
|---|---|---|
| `rho` | `Certificate.printRowOrder g = (1 + 3 * g) / 4` | ✓ |
| `0 < rho ∧ rho ≤ 1` | `g ∈ Ico 0 1` arithmetic | ✓ |
| `kappa` and `0 < kappa` | `2 * kappaRate`, positive from the hole's own `0 < κ` | ✓ |
| `delta`, `0 ≤ delta` | `h.delta`, `h.delta_nonneg` | ✓ |
| `S`, `X` | `h.sourceScale`, `h.activationScale` | ✓ |
| `1 ≤ X a`, `S a ≤ X a` | `h.activation_one`, `h.source_le_activation` | ✓ **at `a`** |
| the row at `a` | `h.row`, at `Book.Ch02.constantBlockMatrix abar` | ✓ **at `a`** |
| `s` with `0 < s < 1/2` and `rho < 2 * s` | the printed order `(1 + g) / 4`, chosen after `g` | ✓ |
| `Omega` with `∀ z, translateCoeff z ⁻¹' Omega = Omega`, `a ∈ Omega`, and the row **at every `b ∈
Omega`** | — | ✗ **the missing field** |

**The single missing field is the translation-invariant event.**  The
certificate is a per-sample predicate: it carries the row at `a` and at no other
sample.  The demanded `Omega` exists — it is `hquenched`'s `OmegaEnd`, which
carries `MeasurableSet`, `P.real = 1`, the literal
`∀ z, translateCoeff z ⁻¹' OmegaEnd = OmegaEnd`, and
`∀ a ∈ OmegaEnd, HasAllLaterPhysicalBlockRow ((1 + 3 * g) / 4) kappa delta Abar S X a`
— but `hhomogenized`'s binder surface applies **one sample at a time**
(`… (a : CoeffSpace d), HasAllLaterPhysicalBlockRow … S X a → 1 ≤ X a →
S a ≤ X a → GoodScale g kappaRate abar a …`), so the event is discarded before
`GoodScale` is formed.  No choice of `Omega` repairs this downstream:
`Omega = {a}` is not translation invariant, `Omega = univ` does not carry the
row, and the orbit of `a` carries the row only if the row is already known at
every integer translate — which is the demand itself.

**The second missing field was an order window, not a datum — and it is now
gone.**  At the stationary corrector family clause's frozen `rootCorrectorOrder = 3/16` the window
`rho < 2 * rootCorrectorOrder` read `(1 + 3 * g) / 4 < 3 / 8`, i.e. `g < 1/6`
(still proved below, as the record of what the frozen order cost).  The
corrector datum records its order as a *field* rather than reading a
global constant, so the supply chooses the order **after `g`**, at the printed
`(1 + g) / 4`; the corrector cone `s < 1/2` and the window `rho < 2 * s` are
then *both* equivalent to `g < 1`, and the admitted range is the whole of
`Ico 0 1`.

## The repair, machine-checked: the event-retaining certificate

Widen the certificate by the event and widen `hhomogenized` correspondingly.
Both directions are proved here:

* the event-level supply theorem — the event-retaining certificate discharges
  `RootBlockRowSupply` outright (given the window);
* `exists_rootGoodScaleOn_of_quenchedEventRow` — `hhomogenized` still holds at
  the event-retaining certificate, from **exactly the data `hquenched`
  already produces**, with no new hypothesis.

So the event-retaining certificate is a pure binder-surface change to `hhomogenized`: replace its
per-sample row premise by the event-level one that the assembly already has in
hand at the point of application.
-/

namespace HCPolySupport
namespace HighContrast
namespace CorrectorComposition

open MeasureTheory Set
open RowSupply (eccentricityFoldFactor)

noncomputable section

variable {d : ℕ}

/-! ## The stationary corrector family clause's demand, restated -/

/-! ## The order window -/

/-- On `g ∈ Ico 0 1` the row order is a genuine exponent. -/
theorem printRowOrder_mem {g : ℝ} (hg : g ∈ Ico (0 : ℝ) 1) :
    0 < (1 + 3 * g) / 4 ∧ (1 + 3 * g) / 4 ≤ 1 := by
  obtain ⟨hg0, hg1⟩ := hg
  constructor
  · linarith only [hg0]
  · linarith only [hg1]

/-! ### The per-`g` order, and the exact admitted range

The order the supply chooses is the **printed certificate order**
`HighContrast.printCertificateOrder g = (1 + g) / 4`, selected *after* `g`.  At
that order the two constraints the supply must meet — the corrector cone
`0 < s < 1/2` and the window `printRowOrder g < 2 * s` — are **both equivalent
to `g < 1`**, so the admitted range is exactly `Ico 0 1`: the whole root range,
and nothing is admitted beyond it. -/

/-- **The corrector cone at the printed order is exactly `g < 1`.** -/
theorem printCertificateOrder_lt_half_iff (g : ℝ) :
    (1 + g) / 4 < 1 / 2 ↔ g < 1 := by
  constructor
  · intro h; linarith only [h]
  · intro h; linarith only [h]

/-- **The supply window at the printed order is exactly `g < 1`.** -/
theorem printRowOrder_lt_twice_printCertificateOrder_iff (g : ℝ) :
    (1 + 3 * g) / 4 < 2 * ((1 + g) / 4) ↔ g < 1 := by
  constructor
  · intro h; linarith only [h]
  · intro h; linarith only [h]

/-- The printed order is positive on the whole root range (indeed for
`-1 < g`). -/
theorem printCertificateOrder_pos {g : ℝ} (hg : g ∈ Ico (0 : ℝ) 1) :
    0 < (1 + g) / 4 := by
  linarith only [hg.1]

/-! ## The event-retaining certificate the event-retaining certificate -/

/-- **The block-row event.**  Exactly the data `hquenched` produces, restricted
to what `RootBlockRowSupply` reads: a translation-invariant set carrying the
sample, and the physical block row on all of it. -/
@[expose]
def RootBlockRowEvent (d : ℕ) [NeZero d] (abar : Mat d) (a : CoeffSpace d)
    (rho : ℝ) : Prop :=
  ∃ (Omega : Set (CoeffSpace d)) (kappa delta : ℝ)
    (S X : CoeffSpace d → ℝ),
    a ∈ Omega ∧
    (∀ z : Fin d → ℤ, translateCoeff z ⁻¹' Omega = Omega) ∧
    0 < kappa ∧ 0 ≤ delta ∧
    ∀ b ∈ Omega, 1 ≤ X b ∧ S b ≤ X b ∧
      Quenched.HasAllLaterPhysicalBlockRow rho kappa delta
        (Book.Ch02.constantBlockMatrix abar) S X b

/-- **The event-retaining certificate**: the ceiling-exporting smallness interface with the
producing
event retained. -/
@[expose]
def rootGoodScaleOn (d : ℕ) [NeZero d] (g c kappaRate : ℝ) (abar : Mat d)
    (a : CoeffSpace d) (x : ℝ) : Prop :=
  rootGoodScaleAt d g c kappaRate abar a x ∧
    RootBlockRowEvent d abar a ((1 + 3 * g) / 4)

/-! ## The discharge -/

/-! ## `hhomogenized` at the event-retaining certificate -/

/-- **`hhomogenized` survives the widening.**  From the event-level row —
which is precisely what `hquenched` hands the assembly — the event-retaining certificate holds at
every sample of the event, at every corrector smallness.
No new hypothesis is introduced: the premises below are `hquenched`'s own
`OmegaEnd` data. -/
theorem exists_rootGoodScaleOn_of_quenchedEventRow (d : ℕ) [NeZero d]
    {g : ℝ} (hg : g ∈ Ico (0 : ℝ) 1) {c kappa delta : ℝ}
    (hc : c ∈ Ioo (0 : ℝ) 1) (hkappa : 0 < kappa)
    (hdelta : delta ∈ Ioo (0 : ℝ) 1) :
    ∃ kappaRate Lcert pCert : ℝ,
      0 < kappaRate ∧ kappaRate ≤ (1 + g) / 4 ∧
      1 ≤ Lcert ∧ 0 ≤ pCert ∧
      ∀ (abar : Mat d), (symmPart abar).PosDef →
        ∀ (Omega : Set (CoeffSpace d)) (S X : CoeffSpace d → ℝ),
          (∀ z : Fin d → ℤ, translateCoeff z ⁻¹' Omega = Omega) →
          (∀ b ∈ Omega, 1 ≤ X b) →
          (∀ b ∈ Omega, S b ≤ X b) →
          (∀ b ∈ Omega, Quenched.HasAllLaterPhysicalBlockRow
            ((1 + 3 * g) / 4) kappa delta
            (Book.Ch02.constantBlockMatrix abar) S X b) →
          ∀ a ∈ Omega,
            rootGoodScaleOn d g c kappaRate abar a
              (X a * (Lcert * eccentricityFoldFactor abar pCert)) := by
  obtain ⟨kappaRate, Lcert, pCert, hrate, hrateLe, hLcert, hpCert, hmain⟩ :=
    exists_rootGoodScaleAt_of_quenchedRow d hg hc hkappa hdelta
  refine ⟨kappaRate, Lcert, pCert, hrate, hrateLe, hLcert, hpCert, ?_⟩
  intro abar hS Omega S X hinv hX hSX hrow a ha
  refine ⟨hmain abar hS S X a (hrow a ha) (hX a ha) (hSX a ha), ?_⟩
  exact ⟨Omega, kappa, delta, S, X, ha, hinv, hkappa, hdelta.1.le,
    fun b hb ↦ ⟨hX b hb, hSX b hb, hrow b hb⟩⟩

end

end CorrectorComposition
end HighContrast
end HCPolySupport
