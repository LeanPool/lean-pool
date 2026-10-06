/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Comparison.ComparisonLimits
public import LeanPool.CIVAxisymmetric.Comparison.Representative

/-!
# The `x`-uniformity crossing: joint measurability of the comparison identity

`Representative.mollifySlice_ae_ae_sub_eq_intervalIntegral` proves, **for each fixed spatial
point `x`**, that the mollified slice's change between two times `τ₁, τ₂` equals the interval
integral of the right side of `eq:aniso:comparison:mollified`, for a.e. `τ₁, τ₂ ∈ I`. The
exceptional null set of bad `(τ₁, τ₂)` pairs may depend on `x`. The next stage of the comparison
argument (spatial integration of this identity) instead needs the identity to hold, for one fixed
pair `(τ₁, τ₂)` (or a.e. one), for a.e. `x` **simultaneously** — a statement about the *product*
measure on `Vec m × I × I`, strictly stronger than "for every `x`, the `x`-slice is null".

This file closes that crossing. The route: restate the bad set purely in terms of the two honest,
everywhere-defined functions `mollifySlice` and the right side of the mollified equation; show
both are jointly `AEStronglyMeasurable` in `(x, τ)`; apply the abstract crossing lemma
`ae_prod_prod_eq_of_forall_ae_ae` (a two-layer Fubini/Tonelli argument through the measurable
representatives of each side) to upgrade "for every `x`, a.e. `(τ₁, τ₂)`" to "jointly a.e.
`(x, τ₁, τ₂)`"; then swap the product order (as in `SliceBounds.IsLocallyBoundedOn.ae_slice_bound`)
to read it off as "a.e. `(τ₁, τ₂)`, a.e. `x`", the shape the spatial integration needs.

## Contents

* A countable compact exhaustion of an open subset of `ℝ` (`exists_compact_exhaustion_of_isOpen`),
  built from `compactCovering` of the open set as a topological subspace.
* A single `x`-independent "good time set" `G ⊆ I` of full measure, assembled from the exhaustion,
  on which the per-`τ` hypotheses `IsLocallyBoundedOn` only supplies for a.e. `τ` on each compact
  hold for *every* `τ ∈ G` (`exists_good_time_set`).
* Joint measurability, in `(x, τ)`, of `mollifySlice`, of `partialLaplacian`/`gradPair` applied to
  `mollifySlice`, and hence of the whole right side of `eq:aniso:comparison:mollified`
  (`aestronglyMeasurable_comparisonRHS`) — the joint measurability of the DiPerna–Lions commutator
  term is `ComparisonLimits.aestronglyMeasurable_diPernaLionsCommutator_prod`.
* Joint measurability of the parametrized interval integral `(x, τ₁, τ₂) ↦ ∫ s in τ₁..τ₂, f x s`.
* The abstract two-layer crossing lemma `ae_prod_prod_eq_of_forall_ae_ae`, and its application to
  close the crossing (`mollifySlice_ae_prod_sub_eq_intervalIntegral`).
-/

public section

open MeasureTheory Set Filter Topology
open CKN

noncomputable section
namespace CIV

variable {m : ℕ}

/-! ## Part 0: a countable compact exhaustion of an open subset of `ℝ` -/

/-- Every open subset of `ℝ` is the increasing union of a countable family of compact subsets.
Built from the canonical compact exhaustion (`compactCovering`) of the open set regarded as a
topological subspace: an open subset of a locally compact, second-countable space is itself
locally compact and (hence) `σ`-compact. -/
theorem exists_compact_exhaustion_of_isOpen {I : Set ℝ} (hI : IsOpen I) :
    ∃ J : ℕ → Set ℝ, (∀ n, IsCompact (J n)) ∧ Monotone J ∧ (∀ n, J n ⊆ I) ∧ (⋃ n, J n) = I := by
  have hLC : LocallyCompactSpace I := hI.locallyCompactSpace
  have hSC : SigmaCompactSpace I := inferInstance
  refine ⟨fun n => (Subtype.val : I → ℝ) '' compactCovering I n, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (isCompact_compactCovering I n).image continuous_subtype_val
  · intro p q hpq
    exact image_mono (compactCovering_subset I hpq)
  · intro n
    rintro x ⟨a, -, rfl⟩
    exact a.2
  · rw [← Set.image_iUnion, iUnion_compactCovering, Set.image_univ, Subtype.range_val]

/-! ## Part 1: the `x`-independent good time set -/

/-- A single time set `G ⊆ I`, of full measure in `I` and independent of any spatial point, on
which the per-`τ` hypotheses `IsLocallyBoundedOn` supplies only for a.e. `τ` on each compact
`J ⊆ I` hold for *every* `τ ∈ G`: `q(·, τ)` is `AEStronglyMeasurable` and bounded a.e. Assembled
from a compact exhaustion `J n ↗ I` (`exists_compact_exhaustion_of_isOpen`) plus the countable
union of the per-`J n` exceptional null sets. -/
theorem exists_good_time_set {I : Set ℝ} (hI : IsOpen I) {q : Vec m × ℝ → ℝ}
    (hq : IsLocallyBoundedOn m I q) :
    ∃ G : Set ℝ, G ⊆ I ∧ volume (I \ G) = 0 ∧
      ∀ τ ∈ G, AEStronglyMeasurable (fun x => q (x, τ)) volume ∧
        ∃ M : ℝ, ∀ᵐ x : Vec m, |q (x, τ)| ≤ M := by
  obtain ⟨J, hJcpt, -, hJsub, hJUnion⟩ := exists_compact_exhaustion_of_isOpen hI
  have hbdd : ∀ n : ℕ, ∃ M : ℝ, ∀ᵐ τ ∂ volume, τ ∈ J n → ∀ᵐ x : Vec m, |q (x, τ)| ≤ M := by
    intro n
    obtain ⟨M, -, hM⟩ := hq.ae_slice_bound (hJcpt n) (hJsub n)
    exact ⟨M, (ae_restrict_iff' (hJcpt n).measurableSet).mp hM⟩
  choose Mn hMn using hbdd
  have hboundedAll : ∀ᵐ τ ∂ volume, ∀ n, τ ∈ J n → ∀ᵐ x : Vec m, |q (x, τ)| ≤ Mn n :=
    ae_all_iff.mpr hMn
  have hmeasAll : ∀ᵐ τ ∂ (volume.restrict I), AEStronglyMeasurable (fun x => q (x, τ)) volume :=
    hq.ae_slice_measurable
  have hboundedI : ∀ᵐ τ ∂ (volume.restrict I), ∃ M : ℝ, ∀ᵐ x : Vec m, |q (x, τ)| ≤ M := by
    rw [ae_restrict_iff' hI.measurableSet]
    filter_upwards [hboundedAll] with τ hτ hτI
    have hex : ∃ n, τ ∈ J n := by rw [← hJUnion] at hτI; exact Set.mem_iUnion.mp hτI
    obtain ⟨n, hn⟩ := hex
    exact ⟨Mn n, hτ n hn⟩
  have hgood : ∀ᵐ τ ∂ (volume.restrict I),
      AEStronglyMeasurable (fun x => q (x, τ)) volume ∧ ∃ M : ℝ, ∀ᵐ x : Vec m, |q (x, τ)| ≤ M :=
    hmeasAll.and hboundedI
  set G : Set ℝ := I ∩ {τ | AEStronglyMeasurable (fun x => q (x, τ)) volume ∧
      ∃ M : ℝ, ∀ᵐ x : Vec m, |q (x, τ)| ≤ M} with hGdef
  refine ⟨G, Set.inter_subset_left, ?_, ?_⟩
  · have hnull : volume.restrict I {τ | ¬ (AEStronglyMeasurable (fun x => q (x, τ)) volume ∧
        ∃ M : ℝ, ∀ᵐ x : Vec m, |q (x, τ)| ≤ M)} = 0 := ae_iff.mp hgood
    rw [Measure.restrict_apply' hI.measurableSet] at hnull
    have heq : {τ | ¬ (AEStronglyMeasurable (fun x => q (x, τ)) volume ∧
        ∃ M : ℝ, ∀ᵐ x : Vec m, |q (x, τ)| ≤ M)} ∩ I = I \ G := by
      rw [hGdef]
      ext τ
      simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_ofPred_eq]
      tauto
    rwa [heq] at hnull
  · intro τ hτ
    exact hτ.2

/-! ## Part 2: joint measurability of the individual right-side terms -/

/-- `q` composed with the coordinate map that drops the extra `Vec m` factor and swaps `(y, τ)`
to match `q`'s own argument order, jointly measurable on a triple product. The shared internal
step behind every kernel-integral joint-measurability argument below. -/
private theorem aestronglyMeasurable_comp_swap {q : Vec m × ℝ → ℝ} {μs : Measure ℝ} [SFinite μs]
    (hqmeas : AEStronglyMeasurable q ((volume : Measure (Vec m)).prod μs)) :
    AEStronglyMeasurable (fun t : (Vec m × ℝ) × Vec m => q (t.2, t.1.2))
      (((volume : Measure (Vec m)).prod μs).prod (volume : Measure (Vec m))) := by
  set μx : Measure (Vec m) := (volume : Measure (Vec m)) with hμx_def
  have hg : AEStronglyMeasurable (fun z : ℝ × Vec m => q z.swap) (μs.prod μx) := hqmeas.prod_swap
  have hf : Measure.QuasiMeasurePreserving
      (Prod.map (Prod.snd : Vec m × ℝ → ℝ) (id : Vec m → Vec m))
      ((μx.prod μs).prod μx) (μs.prod μx) :=
    QuasiMeasurePreserving.prodMap Measure.quasiMeasurePreserving_snd
      (Measure.QuasiMeasurePreserving.id μx)
  exact hg.comp_quasiMeasurePreserving hf

/-- Joint measurability, in `(x, τ)`, of a spatial convolution `(x, τ) ↦ ∫ y, k (x - y) * q (y, τ)`
against a fixed continuous kernel `k`, from joint measurability of `q` alone. Both `mollifySlice`
and the kernel formula for `partialLaplacian (mollifySlice ...)` are instances of this shape. -/
private theorem aestronglyMeasurable_kernelIntegral {k : Vec m → ℝ} (hk : Continuous k)
    {q : Vec m × ℝ → ℝ} {μs : Measure ℝ} [SFinite μs]
    (hqmeas : AEStronglyMeasurable q ((volume : Measure (Vec m)).prod μs)) :
    AEStronglyMeasurable (fun p : Vec m × ℝ => ∫ y, k (p.1 - y) * q (y, p.2))
      ((volume : Measure (Vec m)).prod μs) := by
  set μx : Measure (Vec m) := (volume : Measure (Vec m)) with hμx_def
  have hqjoint := aestronglyMeasurable_comp_swap hqmeas
  have hxminusy : Continuous (fun t : (Vec m × ℝ) × Vec m => t.1.1 - t.2) :=
    (continuous_fst.comp continuous_fst).sub continuous_snd
  have hk' : Continuous (fun t : (Vec m × ℝ) × Vec m => k (t.1.1 - t.2)) := hk.comp hxminusy
  have hΦ : AEStronglyMeasurable (fun t : (Vec m × ℝ) × Vec m => k (t.1.1 - t.2) * q (t.2, t.1.2))
      ((μx.prod μs).prod μx) := hk'.aestronglyMeasurable.mul hqjoint
  exact hΦ.integral_prod_right'

/-- **Piece 1.** Joint `AEStronglyMeasurable`ness, in `(x, τ)`, of the spatial mollification
`mollifySlice`. Since `mollifySlice_apply` is the unconditional closed formula
`mollifySlice m ε q (x, τ) = ∫ y, mollifierKernel m ε (x - y) * q (y, τ)`, this follows directly
from `aestronglyMeasurable_kernelIntegral`; no side hypothesis on `q` beyond joint measurability
is needed. -/
theorem aestronglyMeasurable_mollifySlice {ε : ℝ} {q : Vec m × ℝ → ℝ} {μs : Measure ℝ}
    [SFinite μs] (hqmeas : AEStronglyMeasurable q ((volume : Measure (Vec m)).prod μs)) :
    AEStronglyMeasurable (fun p : Vec m × ℝ => mollifySlice m ε q p)
      ((volume : Measure (Vec m)).prod μs) :=
  aestronglyMeasurable_kernelIntegral (contDiff_mollifierKernel (m := m) ε).continuous hqmeas

/-- Joint measurability of the kernel formula for `partialLaplacian (mollifySlice ...)`, again a
direct instance of `aestronglyMeasurable_kernelIntegral`. -/
theorem aestronglyMeasurable_partialLaplacianKernelIntegral {ε : ℝ} (d : ℕ) {q : Vec m × ℝ → ℝ}
    {μs : Measure ℝ} [SFinite μs]
    (hqmeas : AEStronglyMeasurable q ((volume : Measure (Vec m)).prod μs)) :
    AEStronglyMeasurable
      (fun p : Vec m × ℝ => ∫ y, partialLaplacianKernel m d ε (p.1 - y) * q (y, p.2))
      ((volume : Measure (Vec m)).prod μs) :=
  aestronglyMeasurable_kernelIntegral (continuous_partialLaplacianKernel m d ε) hqmeas

/-- Joint measurability of the kernel formula for `gradPair (mollifySlice ...) B`: unlike the
plain kernel integral, the direction `B p` fed to `fderiv` also varies jointly with `(x, τ)`, so
the argument first expands the directional derivative in the coordinate basis
(`sum_smul_basisVec`) to isolate `B`'s dependence from the kernel's. -/
theorem aestronglyMeasurable_gradPairKernelIntegral {ε : ℝ} {B : Vec m × ℝ → Vec m}
    {q : Vec m × ℝ → ℝ} {μs : Measure ℝ} [SFinite μs] (hBmeas : Measurable B)
    (hqmeas : AEStronglyMeasurable q ((volume : Measure (Vec m)).prod μs)) :
    AEStronglyMeasurable (fun p : Vec m × ℝ =>
        ∫ y, fderiv ℝ (mollifierKernel m ε) (p.1 - y) (B p) * q (y, p.2))
      ((volume : Measure (Vec m)).prod μs) := by
  set μx : Measure (Vec m) := (volume : Measure (Vec m)) with hμx_def
  have hqjoint := aestronglyMeasurable_comp_swap hqmeas
  have hBcomp : Measurable (fun t : (Vec m × ℝ) × Vec m => B t.1) := hBmeas.comp measurable_fst
  have hBi : ∀ i : Fin m, Measurable (fun t : (Vec m × ℝ) × Vec m => B t.1 i) :=
    fun i => (measurable_pi_apply i).comp hBcomp
  have hxminusy : Continuous (fun t : (Vec m × ℝ) × Vec m => t.1.1 - t.2) :=
    (continuous_fst.comp continuous_fst).sub continuous_snd
  have hfderiv : ∀ i : Fin m, Continuous (fun t : (Vec m × ℝ) × Vec m =>
      fderiv ℝ (mollifierKernel m ε) (t.1.1 - t.2) (basisVec i)) :=
    fun i => (continuous_fderiv_mollifierKernel ε (basisVec i)).comp hxminusy
  have hsum : Measurable (fun t : (Vec m × ℝ) × Vec m =>
      ∑ i, B t.1 i * fderiv ℝ (mollifierKernel m ε) (t.1.1 - t.2) (basisVec i)) :=
    Finset.measurable_sum Finset.univ (fun i _ => (hBi i).mul (hfderiv i).measurable)
  have hexpand : ∀ t : (Vec m × ℝ) × Vec m,
      fderiv ℝ (mollifierKernel m ε) (t.1.1 - t.2) (B t.1)
        = ∑ i, B t.1 i * fderiv ℝ (mollifierKernel m ε) (t.1.1 - t.2) (basisVec i) := by
    intro t
    conv_lhs => rw [← sum_smul_basisVec (B t.1)]
    rw [map_sum]
    simp [smul_eq_mul]
  have hΦ : AEStronglyMeasurable (fun t : (Vec m × ℝ) × Vec m =>
      fderiv ℝ (mollifierKernel m ε) (t.1.1 - t.2) (B t.1) * q (t.2, t.1.2))
      ((μx.prod μs).prod μx) := by
    have heqfun : (fun t : (Vec m × ℝ) × Vec m =>
        fderiv ℝ (mollifierKernel m ε) (t.1.1 - t.2) (B t.1) * q (t.2, t.1.2))
        = fun t => (∑ i, B t.1 i * fderiv ℝ (mollifierKernel m ε) (t.1.1 - t.2) (basisVec i))
            * q (t.2, t.1.2) := by
      funext t; rw [hexpand t]
    rw [heqfun]
    exact hsum.aestronglyMeasurable.mul hqjoint
  exact hΦ.integral_prod_right'

/-- **Piece 3, part a.** `partialLaplacian m d (mollifySlice m ε q)` is jointly
`AEStronglyMeasurable` in `(x, τ) ∈ Vec m × I`. The kernel formula `partialLaplacian_mollifySlice`
holds pointwise on `Vec m × G` (the good time set of `exists_good_time_set`), where it agrees with
the everywhere jointly measurable `aestronglyMeasurable_partialLaplacianKernelIntegral`; the
complement `Vec m × (I \ G)` is null in the product measure since `volume (I \ G) = 0`. -/
theorem aestronglyMeasurable_partialLaplacian_mollifySlice {ε : ℝ} (hε : 0 < ε) (d : ℕ)
    {I : Set ℝ} (hI : IsOpen I) {q : Vec m × ℝ → ℝ} (hq : IsLocallyBoundedOn m I q) :
    AEStronglyMeasurable (fun p : Vec m × ℝ => partialLaplacian m d (mollifySlice m ε q) p)
      ((volume : Measure (Vec m)).prod (volume.restrict I)) := by
  obtain ⟨G, -, hGnull, hGgood⟩ := exists_good_time_set hI hq
  have hqmeas : AEStronglyMeasurable q ((volume : Measure (Vec m)).prod (volume.restrict I)) := by
    have heq : (volume : Measure (Vec m)).prod (volume.restrict I)
        = volume.restrict (univ ×ˢ I) := by
      rw [← Measure.restrict_univ (μ := (volume : Measure (Vec m))), Measure.prod_restrict,
        ← Measure.volume_eq_prod]
    rw [heq]; exact hq.1
  have hkernel := aestronglyMeasurable_partialLaplacianKernelIntegral (ε := ε) d hqmeas
  have hsubset : {p : Vec m × ℝ | (∫ y, partialLaplacianKernel m d ε (p.1 - y) * q (y, p.2))
      ≠ partialLaplacian m d (mollifySlice m ε q) p} ⊆ Set.univ ×ˢ Gᶜ := by
    rintro ⟨x, τ⟩ hp
    simp only [Set.mem_ofPred_eq] at hp
    refine ⟨Set.mem_univ _, ?_⟩
    intro hτG
    apply hp
    obtain ⟨hmeas, M, hbdd⟩ := hGgood τ hτG
    exact (partialLaplacian_mollifySlice d hε q τ M hmeas hbdd x).symm
  have hnullbad : (volume : Measure (Vec m)).prod (volume.restrict I) (Set.univ ×ˢ Gᶜ) = 0 := by
    rw [Measure.prod_prod]
    have hGcI : Gᶜ ∩ I = I \ G := by
      ext τ; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]; tauto
    have hzero : (volume.restrict I) Gᶜ = 0 := by
      rw [Measure.restrict_apply' hI.measurableSet, hGcI, hGnull]
    rw [hzero, mul_zero]
  have heqfun : (fun p : Vec m × ℝ => ∫ y, partialLaplacianKernel m d ε (p.1 - y) * q (y, p.2))
      =ᵐ[(volume : Measure (Vec m)).prod (volume.restrict I)]
      (fun p : Vec m × ℝ => partialLaplacian m d (mollifySlice m ε q) p) := by
    rw [Filter.EventuallyEq, ae_iff]
    exact measure_mono_null hsubset hnullbad
  exact hkernel.congr heqfun

/-- **Piece 3, part b.** `fun p => gradPair m (mollifySlice m ε q) p (B p)` is jointly
`AEStronglyMeasurable` in `(x, τ) ∈ Vec m × I`, by the same good-time-set congruence argument as
`aestronglyMeasurable_partialLaplacian_mollifySlice`, using `gradPair_mollifySlice`'s kernel
formula in place of `partialLaplacian_mollifySlice`'s. -/
theorem aestronglyMeasurable_gradPair_mollifySlice {ε : ℝ} (hε : 0 < ε)
    {I : Set ℝ} (hI : IsOpen I) {B : Vec m × ℝ → Vec m} {divB q : Vec m × ℝ → ℝ}
    (hB : IsAdmissibleDrift m I B divB) (hq : IsLocallyBoundedOn m I q) :
    AEStronglyMeasurable (fun p : Vec m × ℝ => gradPair m (mollifySlice m ε q) p (B p))
      ((volume : Measure (Vec m)).prod (volume.restrict I)) := by
  obtain ⟨G, -, hGnull, hGgood⟩ := exists_good_time_set hI hq
  have hqmeas : AEStronglyMeasurable q ((volume : Measure (Vec m)).prod (volume.restrict I)) := by
    have heq : (volume : Measure (Vec m)).prod (volume.restrict I)
        = volume.restrict (univ ×ˢ I) := by
      rw [← Measure.restrict_univ (μ := (volume : Measure (Vec m))), Measure.prod_restrict,
        ← Measure.volume_eq_prod]
    rw [heq]; exact hq.1
  have hkernel := aestronglyMeasurable_gradPairKernelIntegral (ε := ε) hB.1 hqmeas
  have hsubset : {p : Vec m × ℝ |
      (∫ y, fderiv ℝ (mollifierKernel m ε) (p.1 - y) (B p) * q (y, p.2))
      ≠ gradPair m (mollifySlice m ε q) p (B p)} ⊆ Set.univ ×ˢ Gᶜ := by
    rintro ⟨x, τ⟩ hp
    simp only [Set.mem_ofPred_eq] at hp
    refine ⟨Set.mem_univ _, ?_⟩
    intro hτG
    apply hp
    obtain ⟨hmeas, M, hbdd⟩ := hGgood τ hτG
    exact (gradPair_mollifySlice hε q τ M hmeas hbdd x (B (x, τ))).symm
  have hnullbad : (volume : Measure (Vec m)).prod (volume.restrict I) (Set.univ ×ˢ Gᶜ) = 0 := by
    rw [Measure.prod_prod]
    have hGcI : Gᶜ ∩ I = I \ G := by
      ext τ; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_sdiff]; tauto
    have hzero : (volume.restrict I) Gᶜ = 0 := by
      rw [Measure.restrict_apply' hI.measurableSet, hGcI, hGnull]
    rw [hzero, mul_zero]
  have heqfun : (fun p : Vec m × ℝ =>
      ∫ y, fderiv ℝ (mollifierKernel m ε) (p.1 - y) (B p) * q (y, p.2))
      =ᵐ[(volume : Measure (Vec m)).prod (volume.restrict I)]
      (fun p : Vec m × ℝ => gradPair m (mollifySlice m ε q) p (B p)) := by
    rw [Filter.EventuallyEq, ae_iff]
    exact measure_mono_null hsubset hnullbad
  exact hkernel.congr heqfun

/-- **Piece 3, assembled.** The whole right side of `eq:aniso:comparison:mollified` is jointly
`AEStronglyMeasurable` in `(x, τ) ∈ Vec m × I`: the sum of the three terms just shown measurable
(`aestronglyMeasurable_partialLaplacian_mollifySlice`, `aestronglyMeasurable_gradPair_mollifySlice`)
plus the DiPerna–Lions commutator term, whose joint measurability is
`ComparisonLimits.aestronglyMeasurable_diPernaLionsCommutator_prod`. -/
theorem aestronglyMeasurable_comparisonRHS {d : ℕ} {ε : ℝ} (hε : 0 < ε) {I : Set ℝ}
    (hI : IsOpen I) {B : Vec m × ℝ → Vec m} {divB q : Vec m × ℝ → ℝ}
    (hB : IsAdmissibleDrift m I B divB) (hq : IsLocallyBoundedOn m I q) :
    AEStronglyMeasurable (fun p : Vec m × ℝ =>
        partialLaplacian m d (mollifySlice m ε q) p - gradPair m (mollifySlice m ε q) p (B p)
          + diPernaLionsCommutator m ε (fun y => B (y, p.2)) (fun y => divB (y, p.2))
              (fun y => q (y, p.2)) p.1)
      ((volume : Measure (Vec m)).prod (volume.restrict I)) := by
  have h1 := aestronglyMeasurable_partialLaplacian_mollifySlice hε d hI hq
  have h2 := aestronglyMeasurable_gradPair_mollifySlice hε hI hB hq
  have hqmeas : AEStronglyMeasurable q ((volume : Measure (Vec m)).prod (volume.restrict I)) := by
    have heq : (volume : Measure (Vec m)).prod (volume.restrict I)
        = volume.restrict (univ ×ˢ I) := by
      rw [← Measure.restrict_univ (μ := (volume : Measure (Vec m))), Measure.prod_restrict,
        ← Measure.volume_eq_prod]
    rw [heq]; exact hq.1
  have h3 := aestronglyMeasurable_diPernaLionsCommutator_prod (ε := ε) hB.1 hB.2.1 hqmeas
  exact (h1.sub h2).add h3

/-! ## Part 3: joint measurability of the parametrized interval integral -/

/-- Joint measurability of the one-sided set integral `∫ s in Ioc (a p) (b p), f p.1 s ∂μI`, in
`p`, from joint measurability of `f` in `(x, s)` and measurability of the two endpoint functions
`a, b`. The shared step behind the parametrized interval integral, applied once with
`a, b := (·.2.1), (·.2.2)` and once with the roles reversed. -/
private theorem aestronglyMeasurable_setIntegral_Ioc {f : Vec m → ℝ → ℝ} {μx : Measure (Vec m)}
    {μτ : Measure (ℝ × ℝ)} {μI : Measure ℝ} [SFinite μx] [SFinite μτ] [SFinite μI]
    {a b : Vec m × ℝ × ℝ → ℝ} (ha : Measurable a) (hb : Measurable b)
    (hf : AEStronglyMeasurable (fun z : Vec m × ℝ => f z.1 z.2) (μx.prod μI)) :
    AEStronglyMeasurable (fun p : Vec m × ℝ × ℝ => ∫ s in Set.Ioc (a p) (b p), f p.1 s ∂μI)
      (μx.prod μτ) := by
  set proj : (Vec m × ℝ × ℝ) × ℝ → Vec m × ℝ := fun w => (w.1.1, w.2) with hprojdef
  have hprojQMP : Measure.QuasiMeasurePreserving proj ((μx.prod μτ).prod μI) (μx.prod μI) :=
    QuasiMeasurePreserving.prodMap Measure.quasiMeasurePreserving_fst
      (Measure.QuasiMeasurePreserving.id μI)
  have hflift : AEStronglyMeasurable (fun w : (Vec m × ℝ × ℝ) × ℝ => f w.1.1 w.2)
      ((μx.prod μτ).prod μI) := hf.comp_quasiMeasurePreserving hprojQMP
  have hSmeas : MeasurableSet {w : (Vec m × ℝ × ℝ) × ℝ | w.2 ∈ Set.Ioc (a w.1) (b w.1)} := by
    have heq : {w : (Vec m × ℝ × ℝ) × ℝ | w.2 ∈ Set.Ioc (a w.1) (b w.1)}
        = {w : (Vec m × ℝ × ℝ) × ℝ | a w.1 < w.2} ∩ {w : (Vec m × ℝ × ℝ) × ℝ | w.2 ≤ b w.1} := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Ioc]
    rw [heq]
    refine MeasurableSet.inter ?_ ?_
    · exact measurableSet_lt (ha.comp measurable_fst) measurable_snd
    · exact measurableSet_le measurable_snd (hb.comp measurable_fst)
  have hGind : AEStronglyMeasurable
      ({w : (Vec m × ℝ × ℝ) × ℝ | w.2 ∈ Set.Ioc (a w.1) (b w.1)}.indicator
        (fun w : (Vec m × ℝ × ℝ) × ℝ => f w.1.1 w.2)) ((μx.prod μτ).prod μI) :=
    hflift.indicator hSmeas
  have hres := hGind.integral_prod_right'
  refine hres.congr (Filter.Eventually.of_forall fun p => ?_)
  have hpt : ∀ y : ℝ, ({w : (Vec m × ℝ × ℝ) × ℝ | w.2 ∈ Set.Ioc (a w.1) (b w.1)}.indicator
      (fun w : (Vec m × ℝ × ℝ) × ℝ => f w.1.1 w.2)) (p, y)
      = (Set.Ioc (a p) (b p)).indicator (fun s => f p.1 s) y := by
    intro y
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Ioc]
  simp only [hpt]
  exact integral_indicator (measurableSet_Ioc (a := a p) (b := b p))

/-- **Piece 4.** Joint measurability of the parametrized interval integral
`(x, τ₁, τ₂) ↦ ∫ s in τ₁..τ₂, f x s ∂μI`, from joint measurability of `f` in `(x, s)` alone.
Unfolds the interval integral as the difference of two one-sided set integrals
(`aestronglyMeasurable_setIntegral_Ioc`, applied with the two endpoint roles swapped) and uses
that `intervalIntegral` is definitionally exactly that difference. -/
theorem aestronglyMeasurable_intervalIntegral {f : Vec m → ℝ → ℝ} {μx : Measure (Vec m)}
    {μτ : Measure (ℝ × ℝ)} {μI : Measure ℝ} [SFinite μx] [SFinite μτ] [SFinite μI]
    (hf : AEStronglyMeasurable (fun z : Vec m × ℝ => f z.1 z.2) (μx.prod μI)) :
    AEStronglyMeasurable (fun p : Vec m × ℝ × ℝ => ∫ s in p.2.1..p.2.2, f p.1 s ∂μI)
      (μx.prod μτ) := by
  have h1 := aestronglyMeasurable_setIntegral_Ioc (μτ := μτ)
    (a := fun p : Vec m × ℝ × ℝ => p.2.1) (b := fun p : Vec m × ℝ × ℝ => p.2.2)
    (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd) hf
  have h2 := aestronglyMeasurable_setIntegral_Ioc (μτ := μτ)
    (a := fun p : Vec m × ℝ × ℝ => p.2.2) (b := fun p : Vec m × ℝ × ℝ => p.2.1)
    (measurable_snd.comp measurable_snd) (measurable_fst.comp measurable_snd) hf
  have hdiff := h1.sub h2
  refine hdiff.congr (Filter.Eventually.of_forall fun p => ?_)
  rfl

/-- A set integral over `I`-restricted volume equals the plain set integral, on any subset of `I`.
Since `∫ s in S, g s ∂(volume.restrict I) = ∫ s, g s ∂((volume.restrict I).restrict S)`, and
restricting twice with `S ⊆ I` collapses to a single restriction to `S`. -/
private theorem setIntegral_restrict_eq {g : ℝ → ℝ} {S I : Set ℝ} (hI : MeasurableSet I)
    (hSI : S ⊆ I) : ∫ s in S, g s ∂(volume.restrict I) = ∫ s in S, g s := by
  show ∫ s, g s ∂((volume.restrict I).restrict S) = ∫ s, g s ∂(volume.restrict S)
  rw [Measure.restrict_restrict' hI, Set.inter_eq_left.mpr hSI]

/-- The `I`-restricted and plain interval integrals of `g` agree whenever both endpoints lie in
the order-connected open set `I`: both one-sided pieces `Ioc τ₁ τ₂`, `Ioc τ₂ τ₁` lie inside `I`
(via `uIoc ⊆ uIcc ⊆ I`), so `setIntegral_restrict_eq` applies to each. -/
private theorem intervalIntegral_restrict_eq {g : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    (hIoc : I.OrdConnected) {τ1 τ2 : ℝ} (hτ1 : τ1 ∈ I) (hτ2 : τ2 ∈ I) :
    (∫ s in τ1..τ2, g s ∂(volume.restrict I)) = ∫ s in τ1..τ2, g s := by
  have hUIcc : Set.uIcc τ1 τ2 ⊆ I := hIoc.uIcc_subset hτ1 hτ2
  have hsub1 : Set.Ioc τ1 τ2 ⊆ I := (Ioc_subset_uIoc.trans uIoc_subset_uIcc).trans hUIcc
  have hsub2 : Set.Ioc τ2 τ1 ⊆ I := (Ioc_subset_uIoc'.trans uIoc_subset_uIcc).trans hUIcc
  have h1 := setIntegral_restrict_eq (g := g) hI.measurableSet hsub1
  have h2 := setIntegral_restrict_eq (g := g) hI.measurableSet hsub2
  show (∫ s in Set.Ioc τ1 τ2, g s ∂(volume.restrict I))
      - ∫ s in Set.Ioc τ2 τ1, g s ∂(volume.restrict I)
      = (∫ s in Set.Ioc τ1 τ2, g s) - ∫ s in Set.Ioc τ2 τ1, g s
  rw [h1, h2]

/-! ## Part 4: the abstract crossing -/

/-- **The abstract crossing at the heart of the comparison chain's structural blocker.** Given two
functions on a triple product, jointly `AEStronglyMeasurable`, that agree for *every* point `a` of
the first factor at a.e. point `(b₁, b₂)` of the other two, they agree at a.e. point of the *whole*
product jointly. The exceptional a.e. set in the hypothesis may depend on `a`; the conclusion's
does not privilege any factor.

The proof passes to the measurable representatives `F', G'` of `f, g` (`AEStronglyMeasurable.mk`).
Since `F', G'` are measurable *everywhere* (not just a.e.), every one of their `a`-slices is
genuinely measurable with no exceptional set, so the hypothesis's nested a.e. statement (available
for a.e. `a`, where `f, g` agree with `F', G'` slice-wise) upgrades to a product statement on that
slice via `Measure.ae_prod_iff_ae_ae` — the two-variable Fubini/Tonelli fact that does need
measurability. Chaining `f =ᵐ F'`, `F' =ᵐ G'`, `G' =ᵐ g` slice-wise gives `f =ᵐ g` for a.e. `a`,
and one more application of the same Fubini/Tonelli fact (now on the full product) closes it. -/
theorem ae_prod_prod_eq_of_forall_ae_ae {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {ν1 ν2 : Measure ℝ} [SFinite ν1] [SFinite ν2] {f g : α × ℝ × ℝ → ℝ}
    (hf : AEStronglyMeasurable f (μ.prod (ν1.prod ν2)))
    (hg : AEStronglyMeasurable g (μ.prod (ν1.prod ν2)))
    (h : ∀ a : α, ∀ᵐ b1 ∂ν1, ∀ᵐ b2 ∂ν2, f (a, b1, b2) = g (a, b1, b2)) :
    f =ᵐ[μ.prod (ν1.prod ν2)] g := by
  set F' := hf.mk f with hF'def
  set G' := hg.mk g with hG'def
  have hFeq : f =ᵐ[μ.prod (ν1.prod ν2)] F' := hf.ae_eq_mk
  have hGeq : g =ᵐ[μ.prod (ν1.prod ν2)] G' := hg.ae_eq_mk
  have hF'meas : Measurable F' := hf.stronglyMeasurable_mk.measurable
  have hG'meas : Measurable G' := hg.stronglyMeasurable_mk.measurable
  have hFslice : ∀ᵐ a ∂μ, (fun b : ℝ × ℝ => f (a, b)) =ᵐ[ν1.prod ν2] (fun b => F' (a, b)) :=
    Measure.ae_ae_eq_curry_of_prod hFeq
  have hGslice : ∀ᵐ a ∂μ, (fun b : ℝ × ℝ => g (a, b)) =ᵐ[ν1.prod ν2] (fun b => G' (a, b)) :=
    Measure.ae_ae_eq_curry_of_prod hGeq
  have key : ∀ᵐ a ∂μ, (fun b : ℝ × ℝ => f (a, b)) =ᵐ[ν1.prod ν2] (fun b => g (a, b)) := by
    filter_upwards [hFslice, hGslice] with a haF haG
    have hFnest : ∀ᵐ b1 ∂ν1, ∀ᵐ b2 ∂ν2, f (a, b1, b2) = F' (a, b1, b2) :=
      Measure.ae_ae_of_ae_prod haF
    have hGnest : ∀ᵐ b1 ∂ν1, ∀ᵐ b2 ∂ν2, g (a, b1, b2) = G' (a, b1, b2) :=
      Measure.ae_ae_of_ae_prod haG
    have hNest : ∀ᵐ b1 ∂ν1, ∀ᵐ b2 ∂ν2, F' (a, b1, b2) = G' (a, b1, b2) := by
      filter_upwards [hFnest, hGnest, h a] with b1 hb1F hb1G hb1h
      filter_upwards [hb1F, hb1G, hb1h] with b2 hb2F hb2G hb2h
      rw [← hb2F, ← hb2G]; exact hb2h
    have hFa'M : Measurable (fun b : ℝ × ℝ => F' (a, b)) := hF'meas.comp measurable_prodMk_left
    have hGa'M : Measurable (fun b : ℝ × ℝ => G' (a, b)) := hG'meas.comp measurable_prodMk_left
    have hSetMeas : MeasurableSet {b : ℝ × ℝ | F' (a, b) = G' (a, b)} :=
      measurableSet_eq_fun hFa'M hGa'M
    have hProd : ∀ᵐ b ∂(ν1.prod ν2), F' (a, b) = G' (a, b) :=
      (Measure.ae_prod_iff_ae_ae hSetMeas).mpr hNest
    filter_upwards [haF, haG, hProd] with b hbF hbG hbFG
    rw [hbF, hbG, hbFG]
  have hFGmeas : MeasurableSet {w : α × ℝ × ℝ | F' w = G' w} := measurableSet_eq_fun hF'meas hG'meas
  have hkeyF' : ∀ᵐ a ∂μ, (fun b : ℝ × ℝ => F' (a, b)) =ᵐ[ν1.prod ν2] (fun b => G' (a, b)) := by
    filter_upwards [hFslice, hGslice, key] with a haF haG hakey
    calc (fun b : ℝ × ℝ => F' (a, b)) =ᵐ[ν1.prod ν2] (fun b => f (a, b)) := haF.symm
      _ =ᵐ[ν1.prod ν2] (fun b => g (a, b)) := hakey
      _ =ᵐ[ν1.prod ν2] (fun b => G' (a, b)) := haG
  have hFG' : ∀ᵐ w ∂μ.prod (ν1.prod ν2), F' w = G' w :=
    (Measure.ae_prod_iff_ae_ae hFGmeas).mpr hkeyF'
  filter_upwards [hFeq, hGeq, hFG'] with w hw1 hw2 hw3
  rw [hw1, hw2, hw3]

/-! ## Part 5: the crossing, applied -/

/-- **The structural blocker, fully closed.** For a.e. `(τ₁, τ₂) ∈ I × I` and a.e. `x`, the
mollified slice's change between `τ₁` and `τ₂` equals the interval integral of the right side of
`eq:aniso:comparison:mollified` — upgrading
`Representative.mollifySlice_ae_ae_sub_eq_intervalIntegral`
(true for every `x`, a.e. `τ₁, τ₂`, with the exceptional set possibly depending on `x`) to hold
jointly a.e., the form spatial integration of the identity needs.

The proof restates the bad set purely from the two honest, everywhere-defined sides of the
identity, shows both jointly `AEStronglyMeasurable` in `(x, τ₁, τ₂)`
(`aestronglyMeasurable_mollifySlice`, `aestronglyMeasurable_comparisonRHS` composed with
`aestronglyMeasurable_intervalIntegral`), and applies the abstract crossing
`ae_prod_prod_eq_of_forall_ae_ae` followed by a `Prod.swap` pushforward (as in
`SliceBounds.IsLocallyBoundedOn.ae_slice_bound`) to read the conclusion in the `(τ₁, τ₂)`-first
order. -/
theorem mollifySlice_ae_prod_sub_eq_intervalIntegral {d : ℕ} {I : Set ℝ} (hI : IsOpen I)
    (hIoc : I.OrdConnected) {B : Vec m × ℝ → Vec m} {divB q : Vec m × ℝ → ℝ}
    (hB : IsAdmissibleDrift m I B divB) (hq : IsLocallyBoundedOn m I q)
    (heq : IsDistributionalDriftDiffusion m d I B divB q) {ε : ℝ} (hε : 0 < ε)
    {τ₀ : ℝ} (hτ₀ : τ₀ ∈ I) :
    ∀ᵐ τ1 ∂(volume.restrict I), ∀ᵐ τ2 ∂(volume.restrict I), ∀ᵐ x : Vec m,
      mollifySlice m ε q (x, τ2) - mollifySlice m ε q (x, τ1)
        = ∫ s in τ1..τ2, (partialLaplacian m d (mollifySlice m ε q) (x, s)
            - gradPair m (mollifySlice m ε q) (x, s) (B (x, s))
            + diPernaLionsCommutator m ε (fun y => B (y, s)) (fun y => divB (y, s))
                (fun y => q (y, s)) x) := by
  set μx : Measure (Vec m) := (volume : Measure (Vec m)) with hμx_def
  set μI : Measure ℝ := volume.restrict I with hμI_def
  set f : Vec m × ℝ × ℝ → ℝ :=
    fun p => mollifySlice m ε q (p.1, p.2.2) - mollifySlice m ε q (p.1, p.2.1) with hfdef
  set RHSfun : Vec m → ℝ → ℝ := fun x s => partialLaplacian m d (mollifySlice m ε q) (x, s)
      - gradPair m (mollifySlice m ε q) (x, s) (B (x, s))
      + diPernaLionsCommutator m ε (fun y => B (y, s)) (fun y => divB (y, s))
          (fun y => q (y, s)) x with hRHSdef
  set g : Vec m × ℝ × ℝ → ℝ := fun p => ∫ s in p.2.1..p.2.2, RHSfun p.1 s with hgdef
  -- joint measurability of `f`
  have hqmeas : AEStronglyMeasurable q (μx.prod μI) := by
    have heq2 : μx.prod μI = volume.restrict (univ ×ˢ I) := by
      rw [hμx_def, hμI_def, ← Measure.restrict_univ (μ := (volume : Measure (Vec m))),
        Measure.prod_restrict, ← Measure.volume_eq_prod]
    rw [heq2]; exact hq.1
  have hmoll : AEStronglyMeasurable (fun z : Vec m × ℝ => mollifySlice m ε q z) (μx.prod μI) :=
    aestronglyMeasurable_mollifySlice hqmeas
  have hproj2 : Measure.QuasiMeasurePreserving (fun p : Vec m × ℝ × ℝ => (p.1, p.2.2))
      (μx.prod (μI.prod μI)) (μx.prod μI) :=
    QuasiMeasurePreserving.prodMap (Measure.QuasiMeasurePreserving.id μx)
      Measure.quasiMeasurePreserving_snd
  have hproj1 : Measure.QuasiMeasurePreserving (fun p : Vec m × ℝ × ℝ => (p.1, p.2.1))
      (μx.prod (μI.prod μI)) (μx.prod μI) :=
    QuasiMeasurePreserving.prodMap (Measure.QuasiMeasurePreserving.id μx)
      Measure.quasiMeasurePreserving_fst
  have hf2 : AEStronglyMeasurable (fun p : Vec m × ℝ × ℝ => mollifySlice m ε q (p.1, p.2.2))
      (μx.prod (μI.prod μI)) := hmoll.comp_quasiMeasurePreserving hproj2
  have hf1 : AEStronglyMeasurable (fun p : Vec m × ℝ × ℝ => mollifySlice m ε q (p.1, p.2.1))
      (μx.prod (μI.prod μI)) := hmoll.comp_quasiMeasurePreserving hproj1
  have hf : AEStronglyMeasurable f (μx.prod (μI.prod μI)) := by
    rw [hfdef]; exact hf2.sub hf1
  -- joint measurability of `g`
  have hRHSmeas : AEStronglyMeasurable (fun z : Vec m × ℝ => RHSfun z.1 z.2) (μx.prod μI) := by
    rw [hRHSdef]; exact aestronglyMeasurable_comparisonRHS hε hI hB hq
  have hg0 : AEStronglyMeasurable
      (fun p : Vec m × ℝ × ℝ => ∫ s in p.2.1..p.2.2, RHSfun p.1 s ∂μI)
      (μx.prod (μI.prod μI)) := aestronglyMeasurable_intervalIntegral hRHSmeas
  have hsubsetRestrict : {p : Vec m × ℝ × ℝ | (∫ s in p.2.1..p.2.2, RHSfun p.1 s ∂μI)
      ≠ ∫ s in p.2.1..p.2.2, RHSfun p.1 s} ⊆ Set.univ ×ˢ (Iᶜ ×ˢ (univ : Set ℝ) ∪ univ ×ˢ Iᶜ) := by
    rintro ⟨x, τ1, τ2⟩ hp
    simp only [Set.mem_ofPred_eq] at hp
    refine ⟨Set.mem_univ _, ?_⟩
    by_contra hcon
    simp only [Set.mem_union, Set.mem_prod, Set.mem_compl_iff, Set.mem_univ, and_true,
      true_and, not_or] at hcon
    exact hp (intervalIntegral_restrict_eq (g := RHSfun x) hI hIoc
      (not_not.mp hcon.1) (not_not.mp hcon.2))
  have hnullRestrict : μx.prod (μI.prod μI)
      (Set.univ ×ˢ (Iᶜ ×ˢ (univ : Set ℝ) ∪ univ ×ˢ Iᶜ)) = 0 := by
    rw [Measure.prod_prod]
    have hIcI : Iᶜ ∩ I = (∅ : Set ℝ) := by
      ext τ; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false]
      tauto
    have hz1 : (μI.prod μI) (Iᶜ ×ˢ (univ : Set ℝ)) = 0 := by
      rw [Measure.prod_prod, hμI_def]
      simp only [Measure.restrict_apply' hI.measurableSet, hIcI, measure_empty, zero_mul]
    have hz2 : (μI.prod μI) ((univ : Set ℝ) ×ˢ Iᶜ) = 0 := by
      rw [Measure.prod_prod, hμI_def]
      simp only [Measure.restrict_apply' hI.measurableSet, hIcI, measure_empty, mul_zero]
    rw [measure_union_null hz1 hz2, mul_zero]
  have hg0eq : (fun p : Vec m × ℝ × ℝ => ∫ s in p.2.1..p.2.2, RHSfun p.1 s ∂μI)
      =ᵐ[μx.prod (μI.prod μI)] g := by
    rw [Filter.EventuallyEq, ae_iff]
    refine measure_mono_null ?_ hnullRestrict
    rw [hgdef]; exact hsubsetRestrict
  have hg : AEStronglyMeasurable g (μx.prod (μI.prod μI)) := hg0.congr hg0eq
  -- the per-`x` hypothesis, exactly `Representative.mollifySlice_ae_ae_sub_eq_intervalIntegral`
  have hforall : ∀ x : Vec m, ∀ᵐ τ1 ∂μI, ∀ᵐ τ2 ∂μI, f (x, τ1, τ2) = g (x, τ1, τ2) := by
    intro x
    have hx := mollifySlice_ae_ae_sub_eq_intervalIntegral hI hIoc hB hq heq hε x hτ₀
    filter_upwards [hx] with τ1 hτ1
    filter_upwards [hτ1] with τ2 hτ2
    rw [hfdef, hgdef]
    exact hτ2
  -- the crossing
  have hcross : f =ᵐ[μx.prod (μI.prod μI)] g :=
    ae_prod_prod_eq_of_forall_ae_ae hf hg hforall
  -- swap to read off "a.e. (τ1, τ2), a.e. x"
  have hswap : ∀ᵐ w ∂ (μI.prod μI).prod μx, f w.swap = g w.swap := by
    refine ae_of_ae_map (f := (Prod.swap : (ℝ × ℝ) × Vec m → Vec m × ℝ × ℝ))
      (p := fun z : Vec m × ℝ × ℝ => f z = g z)
      (measurable_swap.aemeasurable (μ := (μI.prod μI).prod μx)) ?_
    rw [Measure.prod_swap]
    exact hcross
  have htarget := Measure.ae_ae_of_ae_prod hswap
  have htarget2 := Measure.ae_ae_of_ae_prod htarget
  filter_upwards [htarget2] with τ1 hτ1
  filter_upwards [hτ1] with τ2 hτ2
  filter_upwards [hτ2] with x hx
  rw [hfdef, hgdef] at hx
  simpa using hx

end CIV
