/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.BTTruncations
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MongeAmpere
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorMaxLocality

/-!
# Canonical bounded Bedford–Taylor measures and truncation steps

The measure is chosen from the proved existence theorem, not supplied as an
input. Strict max-constant locality for locally bounded BT measures is proved
in Pending.BedfordTaylorMaxLocality; the finite-level consistency statements use it.

Sources: BEGZ §1.2, `equ:nonpp`, `equ:welldef`; revised `sec:npp`.
BEGZ invokes the bounded BT foundation and does not fix our numerical ddC
normalization. We retain the density convention `ddC = i ∂∂bar / (2π)` of
`FirstPass.MongeAmpere`. No ambient Radon assumption, uniform compact mass
bound, non-pluripolar limit, or general mixed product is asserted here.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace

namespace SGPT.Foundations.Analysis.Pending.MongeAmpere

open FirstPass FirstPass.MongeAmpere

variable {n : ℕ}

/-- Select an actual measure from the explicit bounded BT existence theorem. -/
def canonicalBedfordTaylorMeasure (Ω : Opens (ComplexModel n))
    (v : ComplexModel n → ℝ) (hv : IsLocallyBoundedPshOn Ω v) : Measure (ComplexModel n) :=
  Classical.choose (exists_localBedfordTaylorMeasure hv)

theorem canonicalBedfordTaylorMeasure_spec (Ω : Opens (ComplexModel n))
    (v : ComplexModel n → ℝ) (hv : IsLocallyBoundedPshOn Ω v) :
    IsLocalBedfordTaylorMeasure Ω v (canonicalBedfordTaylorMeasure Ω v hv) :=
  Classical.choose_spec (exists_localBedfordTaylorMeasure hv)

theorem canonicalBedfordTaylorMeasure_eq {Ω : Opens (ComplexModel n)}
    {v : ComplexModel n → ℝ} (hv : IsLocallyBoundedPshOn Ω v)
    {μ : Measure (ComplexModel n)} (hμ : IsLocalBedfordTaylorMeasure Ω v μ) :
    canonicalBedfordTaylorMeasure Ω v hv = μ :=
  localBedfordTaylorMeasure_unique (canonicalBedfordTaylorMeasure_spec Ω v hv) hμ

theorem canonicalBedfordTaylorMeasure_proof_independent {Ω : Opens (ComplexModel n)}
    {v : ComplexModel n → ℝ} (hv hw : IsLocallyBoundedPshOn Ω v) :
    canonicalBedfordTaylorMeasure Ω v hv = canonicalBedfordTaylorMeasure Ω v hw := rfl

theorem canonicalBedfordTaylorMeasure_compl (Ω : Opens (ComplexModel n))
    (v : ComplexModel n → ℝ) (hv : IsLocallyBoundedPshOn Ω v) :
    canonicalBedfordTaylorMeasure Ω v hv (Ω : Set (ComplexModel n))ᶜ = 0 :=
  (canonicalBedfordTaylorMeasure_spec Ω v hv).2.1

/-- Finiteness is only for compact sets contained in the open domain. -/
theorem canonicalBedfordTaylorMeasure_finiteOnCompacts {Ω : Opens (ComplexModel n)}
    {v : ComplexModel n → ℝ} (hv : IsLocallyBoundedPshOn Ω v)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    canonicalBedfordTaylorMeasure Ω v hv K < ⊤ :=
  (canonicalBedfordTaylorMeasure_spec Ω v hv).2.2.1 K hK hKΩ

theorem canonicalBedfordTaylorMeasure_restrict {Ω U : Opens (ComplexModel n)}
    (hU : U ≤ Ω) {v : ComplexModel n → ℝ}
    (hv : IsLocallyBoundedPshOn Ω v) (hvU : IsLocallyBoundedPshOn U v) :
    (canonicalBedfordTaylorMeasure Ω v hv).restrict (U : Set (ComplexModel n)) =
      canonicalBedfordTaylorMeasure U v hvU :=
  localBedfordTaylorMeasure_unique
    (localBedfordTaylorMeasure_restrict (canonicalBedfordTaylorMeasure_spec Ω v hv) hU)
    (canonicalBedfordTaylorMeasure_spec U v hvU)

/-- Bounded BT plurifine locality for a maximum with a constant. Both measures
satisfy the full BT relation (including local boundedness and PSH). The maximum
identity is needed only on Ω, so arbitrary representatives outside Ω are allowed.
The restriction set is a strict superlevel, not an arbitrary equality set and
not necessarily an ordinary open set. Source: BEGZ §1.2, invoking bounded BT. -/
theorem localBedfordTaylorMeasure_max_const_locality
    {Ω : Opens (ComplexModel n)} {v w : ComplexModel n → ℝ}
    {μ ν : Measure (ComplexModel n)}
    (hμ : IsLocalBedfordTaylorMeasure Ω v μ)
    (hν : IsLocalBedfordTaylorMeasure Ω w ν) (c : ℝ)
    (hmax : EqOn w (fun z => max (v z) c) Ω) :
    ν.restrict {z | z ∈ Ω ∧ c < v z} = μ.restrict {z | z ∈ Ω ∧ c < v z} :=
  BedfordTaylor.IsLocalBedfordTaylorMeasure.restrict_max_const hμ hν c hmax

/-- The genuine finite-level measure: bounded BT of the actual truncation,
restricted to its strict locus. -/
def truncationMeasure (Ω : Opens (ComplexModel n)) (u : ComplexModel n → EReal)
    (hu : PlurisubharmonicOn u Ω) (k : ℕ) : Measure (ComplexModel n) :=
  (canonicalBedfordTaylorMeasure Ω (truncationReal u k)
    (truncationReal_isLocallyBoundedPshOn hu k)).restrict (strictTruncationLocus Ω u k)

theorem truncationMeasure_proof_independent {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → EReal} (hu hv : PlurisubharmonicOn u Ω) (k : ℕ) :
    truncationMeasure Ω u hu k = truncationMeasure Ω u hv k := rfl

/-- Equality of bounded BT measures after restriction to the lower strict locus. -/
theorem bedfordTaylor_truncation_restrict {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → EReal} (hu : PlurisubharmonicOn u Ω) {k l : ℕ} (hkl : k ≤ l) :
    (canonicalBedfordTaylorMeasure Ω (truncationReal u l)
      (truncationReal_isLocallyBoundedPshOn hu l)).restrict (strictTruncationLocus Ω u k) =
    (canonicalBedfordTaylorMeasure Ω (truncationReal u k)
      (truncationReal_isLocallyBoundedPshOn hu k)).restrict (strictTruncationLocus Ω u k) := by
  have h := localBedfordTaylorMeasure_max_const_locality
    (canonicalBedfordTaylorMeasure_spec Ω (truncationReal u l)
      (truncationReal_isLocallyBoundedPshOn hu l))
    (canonicalBedfordTaylorMeasure_spec Ω (truncationReal u k)
      (truncationReal_isLocallyBoundedPshOn hu k)) (-(k : ℝ))
    (fun z hz => (truncationReal_nested hu hkl hz).symm)
  rw [← strictLocus_eq_truncationReal_superlevel hu hkl] at h
  exact h.symm

theorem truncationMeasure_restrict {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → EReal} (hu : PlurisubharmonicOn u Ω) {k l : ℕ} (hkl : k ≤ l) :
    (truncationMeasure Ω u hu l).restrict (strictTruncationLocus Ω u k) =
      truncationMeasure Ω u hu k := by
  unfold truncationMeasure
  rw [Measure.restrict_restrict_of_subset (strictTruncationLocus_mono Ω u hkl)]
  exact bedfordTaylor_truncation_restrict hu hkl

/-- Finite-level monotonicity from Pending max-locality; no limit is defined. -/
theorem truncationMeasure_mono {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → EReal} (hu : PlurisubharmonicOn u Ω) :
    Monotone (truncationMeasure Ω u hu) := by
  intro k l hkl
  rw [← truncationMeasure_restrict hu hkl]
  exact Measure.restrict_le_self

theorem truncationMeasure_finiteOnCompacts {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → EReal} (hu : PlurisubharmonicOn u Ω) (k : ℕ)
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKΩ : K ⊆ Ω) :
    truncationMeasure Ω u hu k K < ⊤ := by
  unfold truncationMeasure
  rw [Measure.restrict_apply hK.measurableSet]
  exact (measure_mono inter_subset_left).trans_lt
    (canonicalBedfordTaylorMeasure_finiteOnCompacts
      (truncationReal_isLocallyBoundedPshOn hu k) hK hKΩ)

/-- This vanishing uses exclusion from the restriction set, not the deep
theorem that bounded BT measures do not charge arbitrary pluripolar sets. -/
theorem truncationMeasure_poleSet {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → EReal} (hu : PlurisubharmonicOn u Ω) (k : ℕ) :
    truncationMeasure Ω u hu k {z | u z = ⊥} = 0 := by
  unfold truncationMeasure
  rw [Measure.restrict_apply' (measurableSet_strictTruncationLocus hu k)]
  have hempty : {z | u z = ⊥} ∩ strictTruncationLocus Ω u k = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact pole_not_mem_strictLocus k hz.1 hz.2
  rw [hempty, measure_empty]

end SGPT.Foundations.Analysis.Pending.MongeAmpere
