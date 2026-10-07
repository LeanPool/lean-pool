/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Comparison.ELpNormBridge
public import LeanPool.CIVAxisymmetric.Comparison.AncientVanishing
public import LeanPool.CIVAxisymmetric.Statements.IsAdmissibleDrift
public import LeanPool.CIVAxisymmetric.Statements.IsDistributionalDriftDiffusion
public import Mathlib.Order.Interval.Set.OrdConnected

/-!
# The comparison assertions from the transfer of essential bounds

This file reduces both assertions of `lem:aniso:comparison`, the statements `CIV.comparison` and
`CIV.comparisonAncient`, to one transfer property of essential bounds forward in time: for a.e.
reference time `τ₀` and a.e. later time `τ`, every essential bound `M` of `q (·, τ₀)` is an
essential bound of `q (·, τ)`. This is the hypothesis `hstep`, in the binder shape of
`comparison_eLpNorm_top_of_ae_dominance`, which converts it into the `eLpNorm ⊤` conclusion. Both
theorems below take every hypothesis of the corresponding statement, plus `hstep`, and have
exactly its conclusion.

The transfer property itself is proved from the hypotheses of the comparison lemma by
`CIV.ae_ae_abs_le_of_isDistributionalDriftDiffusion`; `CIV.Main.comparisonAncient` combines it
with `comparisonAncient_of_eLpNorm_transfer`. Every function constant in time satisfies `hstep`
(`hstep_of_forall_eq_of_time_indep`).

The hypotheses `hd`, `hI`, `hB` and `heq` of `comparison_of_eLpNorm_transfer` are not used by its
proof, which goes through `hq` and `hstep` alone; they are kept, under their ordinary names, so
that its hypotheses are those of the statement.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN


noncomputable section

namespace CIV

/-- **`hstep` is satisfiable.** Any function constant in the time variable satisfies the
transfer hypothesis `hstep` of `comparison_of_eLpNorm_transfer`: the bounding condition at a
reference time `τ₀` and at a later time `τ` are then literally the same statement, since
`q (·, τ)` and `q (·, τ₀)` agree pointwise for every `x`. In particular every steady state
satisfies `hstep`. -/
theorem hstep_of_forall_eq_of_time_indep {m : ℕ} {I : Set ℝ} {q : Vec m × ℝ → ℝ}
    (hconst : ∀ x : Vec m, ∀ τ τ' : ℝ, q (x, τ) = q (x, τ')) :
    ∀ᵐ τ₀ ∂(volume.restrict I), ∀ᵐ τ ∂(volume.restrict I), τ₀ < τ →
      ∀ M : ℝ, (∀ᵐ x : Vec m, |q (x, τ₀)| ≤ M) → ∀ᵐ x : Vec m, |q (x, τ)| ≤ M := by
  refine Filter.Eventually.of_forall fun τ₀ => Filter.Eventually.of_forall
    fun τ _hlt M hM => ?_
  filter_upwards [hM] with x hx
  rwa [hconst x τ τ₀]

/-- **`comparison`, from the transfer of essential bounds.** Every hypothesis of the statement
`CIV.comparison` is carried unchanged; the one addition is `hstep`, the transfer hypothesis of
`comparison_eLpNorm_top_of_ae_dominance`, in that lemma's binder shape. The conclusion is that of
`CIV.comparison`.

`hd`, `hI`, `hB` and `heq` are not used by this derivation, which goes through `hq` and `hstep`
alone: given `hstep`, `comparison_eLpNorm_top_of_ae_dominance` supplies the `eLpNorm ⊤`
reformulation, and nothing further is needed from the drift or distributional hypotheses. The
transfer property `hstep` follows from `hI`, `hB`, `hq` and `heq` by
`CIV.ae_ae_abs_le_of_isDistributionalDriftDiffusion`. -/
theorem comparison_of_eLpNorm_transfer (m d : ℕ) (hd : 1 ≤ d ∧ d ≤ m) (I : Set ℝ)
    (hI : IsOpen I ∧ I.OrdConnected)
    (B : Vec m × ℝ → Vec m) (divB : Vec m × ℝ → ℝ) (hB : IsAdmissibleDrift m I B divB)
    (q : Vec m × ℝ → ℝ) (hq : IsLocallyBoundedOn m I q)
    (heq : IsDistributionalDriftDiffusion m d I B divB q)
    (hstep : ∀ᵐ τ₀ ∂(volume.restrict I), ∀ᵐ τ ∂(volume.restrict I), τ₀ < τ →
      ∀ M : ℝ, (∀ᵐ x : Vec m, |q (x, τ₀)| ≤ M) → ∀ᵐ x : Vec m, |q (x, τ)| ≤ M) :
    ∀ᵐ τ₀ ∂(volume.restrict I), ∀ᵐ τ ∂(volume.restrict I), τ₀ < τ →
      eLpNorm (fun x => q (x, τ)) ⊤ volume ≤ eLpNorm (fun x => q (x, τ₀)) ⊤ volume := by
  -- `hd`, `hI`, `hB`, `heq` are not used by this proof (see the docstring); each is referenced
  -- once rather than given a leading-underscore binder name.
  have _hdUnused := hd
  have _hIUnused := hI
  have _hBUnused := hB
  have _heqUnused := heq
  exact comparison_eLpNorm_top_of_ae_dominance hq hstep

/-- **`comparisonAncient`, from the transfer of essential bounds.** Every hypothesis of the
statement `CIV.comparisonAncient` is carried unchanged; the one addition is `hstep`, in the same
shape as `comparison_of_eLpNorm_transfer` above, instantiated at `I := Iio T`. The conclusion is
that of `CIV.comparisonAncient`.

The proof composes three lemmas. `comparison_of_eLpNorm_transfer` supplies, from `hstep`, exactly
the comparison-monotonicity hypothesis `ancientVanishing_ae_eq_zero` needs.
`ancientVanishing_ae_eq_zero` then proves the first conjunct from that and the decay hypothesis
`hdecay`. `ancientVanishing_continuousOn_eq_zero` proves the second conjunct from the first; it is
stated over `V`, `q'`, openness, continuity and the a.e. agreement in the shape of the
statement. -/
theorem comparisonAncient_of_eLpNorm_transfer (m d : ℕ) (hd : 1 ≤ d ∧ d ≤ m) (T : ℝ)
    (B : Vec m × ℝ → Vec m) (divB : Vec m × ℝ → ℝ) (hB : IsAdmissibleDrift m (Iio T) B divB)
    (q : Vec m × ℝ → ℝ) (hq : IsLocallyBoundedOn m (Iio T) q)
    (heq : IsDistributionalDriftDiffusion m d (Iio T) B divB q)
    (C κ : ℝ) (hκ : 0 < κ)
    (hdecay : ∀ᵐ τ ∂(volume.restrict (Iio (min (-1) T))),
      eLpNorm (fun x => q (x, τ)) ⊤ volume ≤ ENNReal.ofReal (C * |τ| ^ (-κ)))
    (hstep : ∀ᵐ τ₀ ∂(volume.restrict (Iio T)), ∀ᵐ τ ∂(volume.restrict (Iio T)), τ₀ < τ →
      ∀ M : ℝ, (∀ᵐ x : Vec m, |q (x, τ₀)| ≤ M) → ∀ᵐ x : Vec m, |q (x, τ)| ≤ M) :
    (∀ᵐ z ∂(volume.restrict (univ ×ˢ Iio T)), q z = 0) ∧
      ∀ (V : Set (Vec m × ℝ)) (q' : Vec m × ℝ → ℝ), IsOpen V →
        ContinuousOn q' (V ∩ univ ×ˢ Iic T) →
        (∀ᵐ z ∂(volume.restrict (V ∩ univ ×ˢ Iio T)), q' z = q z) →
        ∀ z ∈ V ∩ univ ×ˢ Iic T, q' z = 0 := by
  have hcomp := comparison_of_eLpNorm_transfer m d hd (Iio T) ⟨isOpen_Iio, ordConnected_Iio⟩
    B divB hB q hq heq hstep
  have hzero := ancientVanishing_ae_eq_zero (m := m) (T := T) (q := q) hq C κ hκ hdecay hcomp
  exact ⟨hzero, fun V q' hV hcont heqOn =>
    ancientVanishing_continuousOn_eq_zero hzero hV hcont heqOn⟩

end CIV
