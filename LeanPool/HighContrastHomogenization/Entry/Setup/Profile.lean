/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Setup.AdaptedGridCells
public import LeanPool.HighContrastHomogenization.Entry.Setup.NormalizedFluctuation
public import LeanPool.HighContrastHomogenization.Entry.Setup.ProjectiveDistance
public import LeanPool.HighContrastHomogenization.Entry.Setup.SchattenNorm
public import LeanPool.HighContrastHomogenization.Setup.CoefficientSpace
public import LeanPool.HighContrastHomogenization.Setup.Moments

/-!
# High-contrast homogenization: Entry.Setup.Profile

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Profile

The fluctuation history, the mean history and the history along a scale, the mean penalty
`Ψ_Q` read off the relative means, and the determinant drift and complete profile `𝒫_q`
that the printed statements are stated with.  The complete profile is the object of
`e.scale.selection.complete.profile`; its drift term is the one of
`e.scale.selection.determinant.drift`, and the moment and scale parameters are those fixed
by `e.scale.selection.Q.choice`.
-/

section
/-!
## The mean penalty `Ψ_Q(P)`

Near `e.scale.selection.fluctuation.history`:

> For `P ≥ I_{2d}`, set `Ψ_Q(P) := (1 + tr(P - I_{2d}))^Q - 1`.

Matches the printed display symbol for symbol, with `I_{2d}` CoarseGraining's
`Book.Ch02.blockIdentity d` and `tr`
the trace of the `2d`-by-`2d` matrix.  `Q` is the fixed even moment of
`e.scale.selection.Q.choice`; it is a parameter here rather than `bigQ d γ`, because the
display fixes `Q` once and for all and every consumer passes the same value.

The printed hypothesis `P ≥ I_{2d}` is not part of the definition: the formula is a total
function of `P`, and on blocks that are not above the identity it takes the value the
formula gives (which may be negative).  The hypothesis stays with the consumer.  Under the
real-valued reading of the histories and the profile such a value is carried
through unchanged: `HCPoly/Entry/Setup/Profile.lean` sums `Ψ_Q` in `ℝ`, so nothing is truncated,
and the sign of `Ψ_Q` is the consumer's business rather than a junk branch of an insertion
into `ℝ≥0∞`.

The print subtracts the matrix inside the trace, and the moment is the natural number `Q`.
-/

open HCPolySupport.HighContrast (blockSub blockTrace)
namespace HCPolySupport.HighContrast

noncomputable section

variable {d : ℕ}

/-- The mean penalty `Ψ_Q(P) = (1 + tr(P - I_{2d}))^Q - 1` near
`e.scale.selection.fluctuation.history`. -/
@[expose]
def meanPenalty (Q : ℕ) (P : BlockMat d) : ℝ :=
  (1 + blockTrace (blockSub P (Book.Ch02.blockIdentity d))) ^ Q - 1

end

end HCPolySupport.HighContrast
end

section
/-!
## The fluctuation history, the mean history and the history

Near `e.scale.selection.mean.history`
(`e.scale.selection.fluctuation.history`, `e.scale.selection.mean.history`):

> For `m ≥ j_*`, define the fluctuation history by
> `ℋ^fluc_q(m) := E[ sup_{j_* ≤ j ≤ m} 3^{−Qρ_max(m−j)} max_{z ∈ 3^j q ℤ^d ∩ ⋄_m^q}
> |V^q_{j,m}(z)|^Q ]`.
> For `j_* ≤ n ≤ m`, define the mean history by
> `ℋ^mean_q(m;n) := ∑_{j=n}^{m−1} 3^{−¼(1−γ)(m−1−j)} Ψ_Q(P^q_{j,m})`.
> Set `ℋ^mean_q(m) := ℋ^mean_q(m;j_*)` and `ℋ_q(m) := ℋ^fluc_q(m) + ℋ^mean_q(m)`.

`Q` and `ρ_max` are the fixed values of `e.scale.selection.Q.choice`, so `bigQ d γ` and
`rhoMax d γ`; `|·|` is the operator norm `blockOpNorm`; `3^j q ℤ^d` is `adaptedLatticeAtScale q j`
and `⋄_m^q` is `adaptedCell q m`.  The print's `ℋ^mean_q(m)` is the two-argument
`meanHistory P γ q jStar m` and gets no separate name here.

**The three quantities are real-valued**: the expectation is the Bochner
integral, the printed `sup` and `max` are `⨆` in `ℝ`, and `Ψ_Q` is summed as it stands.
What that costs, recorded rather than left to be discovered:

* These are total real formulas. Before using a history or profile as the printed expectation,
  prove the integrability of every needed random integrand and of the entries defining the
  annealed blocks. For the real suprema, also prove the relevant finite/nonempty index-set and
  boundedness facts. `SchattenMemLp P N H` supplies the moment condition only for its specified
  `H`. Where the paper states membership it may be carried as that printed premise; elsewhere
  these properties must be derived from the standing source hypotheses. An estimate of the
  totalized real value does not itself establish integrability. No unprinted premise is added
  to a theorem.
* Nothing is truncated: `Ψ_Q(P^q_{j,m})` enters with whatever sign the formula gives
  (`HCPoly/Entry/Setup/Profile.lean`), and the printed sums `𝒫 + D` of
  `HCPoly/Entry/Setup/Profile.lean`
  are a sum of two reals, written literally as the print writes them.

`j_*` is a natural number (near `e.rounded.grid.bounds`), coerced to `ℤ` where it is
compared with the generations `j`, `m`, which range over `ℤ`; the declaration
`explicitRoundedGrid (jStar : ℕ)` stands.  The second argument `n` of `ℋ^mean_q(m;n)` stays an
integer: the print instantiates it both at `j_*` and at a general generation `n ≥ j_*`.

The mean history is summed over the `Finset.Ico n m` range, and the supremum and the
maximum are `⨆`.  The expectation takes real values as the Bochner integral, rather than
values in `ℝ≥0∞` with `∫⁻`.  The three exponents `Q`, `ρ_max` and `a` are not free real
parameters: `Q` and `ρ_max` are fixed by `e.scale.selection.Q.choice` and `¼(1−γ)` is
written out.  The operator norm is `blockOpNorm` itself, not a Loewner encoding, and `|·|`
means that operator norm.  The inner maximum is indexed by the printed index set
`3^j q ℤ^d ∩ ⋄_m^q`.
-/

open HCPolySupport.HighContrast (CoeffSpace)
namespace HCPolySupport.HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The fluctuation history
`ℋ^fluc_q(m) = E[sup_{j_* ≤ j ≤ m} 3^{−Qρ_max(m−j)} max_{z ∈ 3^j q ℤ^d ∩ ⋄_m^q}
|V^q_{j,m}(z)|^Q]` (`e.scale.selection.fluctuation.history`). -/
@[expose]
def fluctuationHistory (P : Measure (CoeffSpace d)) (γ : ℝ) (q : Mat d) (jStar : ℕ)
    (m : ℤ) : ℝ :=
  ∫ a, ⨆ j ∈ Set.Icc (jStar : ℤ) m,
    (3 : ℝ) ^ (-(bigQ d γ : ℝ) * rhoMax d γ * ((m : ℝ) - (j : ℝ))) *
      ⨆ z ∈ adaptedLatticeAtScale q j ∩ HighContrast.adaptedCell q m,
        blockOpNorm (normalizedFluctuation P q j m z a) ^ bigQ d γ ∂P

/-- The mean history `ℋ^mean_q(m;n) = ∑_{j=n}^{m−1} 3^{−¼(1−γ)(m−1−j)} Ψ_Q(P^q_{j,m})`
(`e.scale.selection.mean.history`).  The print's one-argument `ℋ^mean_q(m)` is this at
`n = j_*`. -/
@[expose]
def meanHistory (P : Measure (CoeffSpace d)) (γ : ℝ) (q : Mat d) (n m : ℤ) : ℝ :=
  ∑ j ∈ Finset.Ico n m,
    (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - 1 - (j : ℝ))) *
      meanPenalty (bigQ d γ) (relMean P q j m)

/-- The history `ℋ_q(m) = ℋ^fluc_q(m) + ℋ^mean_q(m;j_*)` (near `e.scale.selection.mean.history`). -/
@[expose]
def history (P : Measure (CoeffSpace d)) (γ : ℝ) (q : Mat d) (jStar : ℕ) (m : ℤ) : ℝ :=
  fluctuationHistory P γ q jStar m + meanHistory P γ q (jStar : ℤ) m

end

end HCPolySupport.HighContrast
end

section
/-!
## The determinant drift `D_{q,j_*}(m)` and the complete profile `𝒫_q(m;n)`

Near `e.scale.selection.determinant.drift`
(`e.scale.selection.determinant.drift`, `e.scale.selection.complete.profile`):

> Set `D_{q,j_*}(m) := ∑_{j=j_*+1}^{m} 3^{−⅛(1−γ)(m−j)} tr(P^q_{j−1,m} − P^q_{j,m})`.
> For `j_* ≤ n ≤ m`, set
> `𝒫_q(m;n) := 3^{−¼(1−γ)(m−n)}(1 + Ψ_Q(P^q_{n,m})) ℋ_q(n) + ℋ^mean_q(m;n)
> + ∑_{j=n+1}^{m} 3^{−¼(1−γ)(m−j)} e^{QΔ^q_{j,m}} E[|V^q_j|_{S_Q}^Q]`.
> In particular, `𝒫_q(n;n) = ℋ_q(n)`.

Both match the printed display symbol for symbol.  The identity `𝒫_q(n;n) = ℋ_q(n)` is a statement
about the
values, not part of the definition, and is not asserted here.

**Both are real-valued**.  The drift always was: its summand is a trace of a
difference of two normalized means, which the manuscript does not assert to be nonnegative
where it defines the drift.  The profile is real, so the printed sums
`𝒫_q(m;n) + D_{q,j_*}(m)` — which occur in many of the printed statements — are a sum
of two reals and stay literal: no `ENNReal.ofReal` around `D`, and no truncation of a
negative `Ψ_Q` or a negative drift.  What the real reading costs is recorded in
`HCPoly/Entry/Setup/Profile.lean`: these are total real formulas. Before using a history or profile
as the printed expectation, prove the integrability of every needed random integrand and of
the entries defining the annealed blocks. For the real suprema, also prove the relevant
finite/nonempty index-set and boundedness facts. `SchattenMemLp P N H` supplies the moment
condition only for its specified `H`. Where the paper states membership it may be carried as
that printed premise; elsewhere these properties must be derived from the standing source
hypotheses. An estimate of the totalized real value does not itself establish integrability.
No unprinted premise is added to a theorem.

`E[|V^q_j|_{S_Q}^Q]` is the **Bochner** integral of the real function
`a ↦ |V^q_j(a)|_{S_Q}^Q`, not the lower integral of its `ENNReal.ofReal`.  Two reasons:
the value is real, and `lqSchattenNorm` of `HCPoly/Entry/Setup/SchattenNorm.lean` is the same
expectation under its own `1/Q`-th power, so writing this one differently would make
`E[|V^q_j|_{S_Q}^Q]` and `‖V^q_j‖_{L^Q(S_Q)}^Q` two different numbers on a non-integrable
moment.  The integrability premise is `SchattenMemLp P (Q : ℝ) (V^q_j)`, which is the
printed "in `L^Q(S_Q)`" and belongs to the statements, not here.  The Schatten index is the
real `Q` that `absSchattenNorm` takes and the outer power is the natural number `Q`, exactly as
printed.

`j_*` is a natural number, coerced to `ℤ` in the drift's summation range,
where it is compared with the generations; `n` and `m` are integers.

This definition takes the real value of the drift and the `Finset.Icc` ranges.  An
`ℝ≥0∞`-valued formulation of the profile would instead use free exponents (`a`, `ρ_dr`) in
place of the printed `¼(1−γ)` and `⅛(1−γ)`, expand the profile's second term into the mean
history's defining sum, where the print writes `ℋ^mean_q(m;n)`, and use, for its third term,
the mixed norm raised to the power `Q` rather than the printed moment `E[|V^q_j|_{S_Q}^Q]`.
Its drift summand `tr((𝐀hom_{T,q})^{-1}(𝐀hom_{r−1,q} − 𝐀hom_{r,q}))` is the printed
`tr(P^q_{j−1,m} − P^q_{j,m})` only after a cyclicity argument.
-/

open HCPolySupport.HighContrast (CoeffSpace blockSub blockTrace)
namespace HCPolySupport.HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The determinant drift
`D_{q,j_*}(m) = ∑_{j=j_*+1}^{m} 3^{−⅛(1−γ)(m−j)} tr(P^q_{j−1,m} − P^q_{j,m})`
(`e.scale.selection.determinant.drift`). -/
@[expose]
def determinantDrift (P : Measure (CoeffSpace d)) (γ : ℝ) (q : Mat d) (jStar : ℕ) (m : ℤ) :
    ℝ :=
  ∑ j ∈ Finset.Icc ((jStar : ℤ) + 1) m,
    (3 : ℝ) ^ (-((1 - γ) / 8) * ((m : ℝ) - (j : ℝ))) *
      blockTrace (blockSub (relMean P q (j - 1) m) (relMean P q j m))

/-- The complete profile `𝒫_q(m;n)` of `e.scale.selection.complete.profile`. -/
@[expose]
def profile (P : Measure (CoeffSpace d)) (γ : ℝ) (q : Mat d) (jStar : ℕ) (n m : ℤ) : ℝ :=
  (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (n : ℝ))) *
        (1 + meanPenalty (bigQ d γ) (relMean P q n m)) *
      history P γ q jStar n +
    meanHistory P γ q n m +
    ∑ j ∈ Finset.Icc (n + 1) m,
      (3 : ℝ) ^ (-((1 - γ) / 4) * ((m : ℝ) - (j : ℝ))) *
          Real.exp ((bigQ d γ : ℝ) * detIncrement P q j m) *
        ∫ a, absSchattenNorm (bigQ d γ : ℝ) (normalizedFluctuationSelf P q j a) ^ bigQ d γ ∂P

end

end HCPolySupport.HighContrast
end
