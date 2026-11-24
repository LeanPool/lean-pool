/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.NPP.NonPluripolarCurrentLocal
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorCalculus

/-!
# Locality of the non-pluripolar product of arbitrary degree

Source: `chapter_npp.tex`, `prop:npp1` (1)–(3), (5); Xia, *Foundations of pluripotential
theory*, `lem:nonpluripolar-truncation-limit` (the converse direction),
`prop:nonpluripolar-local-calculus` (symmetry, compatibility with restriction).

For the local non-pluripolar product `NonPluripolarCurrent.nonPluripolarProduct` of
`SGPT.NPP.NonPluripolarCurrentLocal`:

* `hasLocallyFiniteMass_of_weakTendsto` — if the truncated products converge weakly to a positive
  current, the mass condition holds (FPT `lem:nonpluripolar-truncation-limit`, converse);
* `nonPluripolarProduct_congr` — the product (and its well-definedness) only depends on the
  values of the potentials on `U`;
* `isWellDefinedOn_restrict`, `restrict_nonPluripolarProduct` — on an open `V ⊆ U` the product
  is well defined and is the restriction of the product on `U` (`prop:npp1` (1), `eq:ppp2`);
* `isWellDefinedOn_of_cover` — well-definedness is local: it holds on `U` as soon as it holds on
  the members of an open cover of `U` (`prop:npp1` (1), last sentence);
* `nonPluripolarProduct_comp_perm` — symmetry in the factors (`prop:npp1` (2), the ordering);
* `isWellDefinedOn_of_isLocallyBoundedPshOn`, `nonPluripolarProduct_of_isLocallyBoundedPshOn` —
  for locally bounded potentials the product is well defined and equals the Bedford–Taylor
  product (`prop:npp1` (3), first sentence).
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal

namespace SGPT.NPP.NonPluripolarCurrent

open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
open SGPT.Foundations.Analysis.Pending.LocalCurrentLebesgue
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorForms
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorLocality

attribute [local instance] addCommGroupFormSpan

variable {n : ℕ}

/-! ### Generalities on positive currents -/

section General

variable {U : Opens (ComplexModel n)} {q : ℕ}

theorem traceMeasure_congr {T T' : LocalProductCurrent n U q} (hT : IsPositive T)
    (hT' : IsPositive T') (h : T = T') : hT.traceMeasure = hT'.traceMeasure := by
  subst h
  rfl

/-- If `1_A T = 1_A T'` for a Borel set `A`, then `σ_T(K ∩ A) = σ_{T'}(K ∩ A)` for the compact
subsets `K` of `U`. -/
theorem traceMeasure_inter_eq_of_mulBorel_eq {T T' : LocalProductCurrent n U q}
    (hT : IsPositive T) (hT' : IsPositive T') {A : Set (ComplexModel n)} (hA : MeasurableSet A)
    (h : mulBorel T (A.indicator fun _ => (1 : ℝ)) = mulBorel T' (A.indicator fun _ => (1 : ℝ)))
    {K : Set (ComplexModel n)} (hK : IsCompact K) (hKU : K ⊆ U) :
    hT.traceMeasure (K ∩ A) = hT'.traceMeasure (K ∩ A) := by
  have hloc : ∀ {S : LocalProductCurrent n U q} (hS : IsPositive S),
      IsLocalDensity (U := U) hS.traceMeasure
        (fun x => A.indicator (fun _ => (1 : ℝ)) x * hS.density (kahlerPower n q) x) :=
    fun {S} hS => by
      obtain ⟨C, -, hC⟩ := hS.exists_abs_density_le (kahlerPower n q)
      refine ⟨hS.traceMeasure_compl, fun K hK hKU => hS.traceMeasure_lt_top hK hKU,
        (measurable_const.indicator hA).mul (hS.measurable_density _), fun K _ _ =>
          ⟨C, fun x _ => ?_⟩⟩
      rw [abs_mul]
      by_cases hx : x ∈ A
      · simpa [hx] using hC x
      · simp [hx, (abs_nonneg _).trans (hC x)]
  have hw : IsTestWeight (U := U) (K.indicator fun _ => (1 : ℝ)) :=
    ⟨measurable_const.indicator hK.measurableSet, ⟨1, fun x => by
      by_cases hx : x ∈ K <;> simp [hx]⟩, K, hK, hKU, fun x hx => Set.indicator_of_notMem hx _⟩
  have key := integral_eq_of_forall_testFunction (hloc hT) (hloc hT') (fun ψ => by
    have e := congrArg (fun S : LocalProductCurrent n U q => S (kahlerPower n q) ψ) h
    simp only at e
    rw [mulBorel_apply hT (measurable_const.indicator hA) (isLocallyBoundedOn_indicator_one _),
      mulBorel_apply hT' (measurable_const.indicator hA)
        (isLocallyBoundedOn_indicator_one _)] at e
    calc ∫ x, A.indicator (fun _ => (1 : ℝ)) x * hT.density (kahlerPower n q) x * ψ x
            ∂hT.traceMeasure =
          ∫ x, ψ x * (A.indicator (fun _ => (1 : ℝ)) x * hT.density (kahlerPower n q) x)
            ∂hT.traceMeasure := integral_congr_ae (ae_of_all _ fun x => by ring)
      _ = _ := e
      _ = _ := integral_congr_ae (ae_of_all _ fun x => by ring)) hw
  have hval : ∀ {S : LocalProductCurrent n U q} (hS : IsPositive S),
      ∫ x, A.indicator (fun _ => (1 : ℝ)) x * hS.density (kahlerPower n q) x *
        K.indicator (fun _ => (1 : ℝ)) x ∂hS.traceMeasure = (hS.traceMeasure (K ∩ A)).toReal :=
    fun {S} hS => by
      rw [← measureReal_def, ← integral_indicator_one (hK.measurableSet.inter hA)]
      refine integral_congr_ae ?_
      filter_upwards [density_kahlerPower_ae hS] with x hx
      rw [hx]
      by_cases hxK : x ∈ K <;> by_cases hxA : x ∈ A <;> simp [hxK, hxA]
  rw [hval hT, hval hT'] at key
  have hlt : ∀ {S : LocalProductCurrent n U q} (hS : IsPositive S),
      hS.traceMeasure (K ∩ A) ≠ ⊤ := fun {S} hS =>
    ((measure_mono inter_subset_left).trans_lt (hS.traceMeasure_lt_top hK hKU)).ne
  exact (ENNReal.toReal_eq_toReal_iff' (hlt hT) (hlt hT')).mp key

/-- `v (u T) = (u v) T` for a nonnegative `u`. -/
theorem mulBorel_mulBorel {T : LocalProductCurrent n U q} (hT : IsPositive T) {u v : (ComplexModel
    n) → ℝ}
    (hu : Measurable u) (hub : IsLocallyBoundedOn u U) (hu0 : ∀ x, 0 ≤ u x)
    (hv : Measurable v) (hvb : IsLocallyBoundedOn v U) :
    mulBorel (mulBorel T u) v = mulBorel T (fun x => u x * v x) := by
  have hT' := BedfordTaylorTopDegree.isPositive_mulBorel_of_nonneg hT hu hub hu0
  have huv : IsLocallyBoundedOn (fun x => u x * v x) U := fun K hK hKU => by
    obtain ⟨M, hM⟩ := hub K hK hKU
    obtain ⟨N, hN⟩ := hvb K hK hKU
    exact ⟨M * N, fun x hx => by
      rw [abs_mul]
      exact mul_le_mul (hM x hx) (hN x hx) (abs_nonneg _) ((abs_nonneg _).trans (hM x hx))⟩
  ext γ φ
  have hd : IsLocalDensity (U := U) hT.traceMeasure (fun x => u x * hT.density γ x) := by
    obtain ⟨C, -, hC⟩ := hT.exists_abs_density_le γ
    refine ⟨hT.traceMeasure_compl, fun K hK hKU => hT.traceMeasure_lt_top hK hKU,
      hu.mul (hT.measurable_density γ), fun K hK hKU => ?_⟩
    obtain ⟨M, hM⟩ := hub K hK hKU
    exact ⟨M * C, fun x hx => by
      rw [abs_mul]
      exact mul_le_mul (hM x hx) (hC x) (abs_nonneg _) ((abs_nonneg _).trans (hM x hx))⟩
  rw [mulBorel_apply_of_integral_eq hT' γ hd (fun ψ => mulBorel_apply hT hu hub γ ψ) hv hvb φ,
    mulBorel_apply hT (u := fun x => u x * v x) (hu.mul hv) huv]
  exact integral_congr_ae (ae_of_all _ fun x => by ring)

end General

/-! ### The converse of the truncation limit lemma -/

section Converse

variable {U : Opens (ComplexModel n)} {q : ℕ} {B : ℕ → LocalProductCurrent n U q} {O : ℕ → Set
    (ComplexModel n)}

/-- **Weak convergence of the truncated products forces the mass condition** (FPT
`lem:nonpluripolar-truncation-limit`, converse direction). -/
theorem IsTruncationFamily.hasLocallyFiniteMass_of_weakTendsto (hF : IsTruncationFamily B O)
    {S : LocalProductCurrent n U q}
    (h : LocalBedfordTaylorContinuity.WeakTendsto (truncAt B O) S) :
    hF.HasLocallyFiniteMass := by
  rw [hF.hasLocallyFiniteMass_iff]
  intro K hK hKU
  obtain ⟨χ, hχs, hχ1, hχU, hχ01⟩ := LocalBedfordTaylorMass.exists_cutoff_unit hK U.isOpen hKU
  obtain ⟨W, hWo, hKW, hWcl, hWc⟩ := exists_open_between_and_isCompact_closure hK U.isOpen hKU
  obtain ⟨χ', hχ's, hχ'1, hχ'W, hχ'01⟩ := LocalBedfordTaylorMass.exists_cutoff_unit hK hWo hKW
  have hχ'c : HasCompactSupport χ' :=
    hWc.of_isClosed_subset (isClosed_tsupport χ') (hχ'W.trans subset_closure)
  let ψ : 𝓓(U, ℝ) := ⟨χ', hχ's, hχ'c, hχ'W.trans (subset_closure.trans hWcl)⟩
  obtain ⟨M, hM⟩ := (h (kahlerPower n q) ψ).bddAbove_range
  refine lt_of_le_of_lt (iSup_le fun k => ?_) (ENNReal.ofReal_lt_top (r := M))
  have hval : truncAt B O k (kahlerPower n q) ψ =
      ∫ x, ψ x * (O k).indicator (fun _ => (1 : ℝ)) x ∂(hF.isPositive k).traceMeasure := by
    rw [truncAt, mulBorel_apply (hF.isPositive k) (measurable_const.indicator (hF.measurableSet k))
      (isLocallyBoundedOn_indicator_one _)]
    refine integral_congr_ae ?_
    filter_upwards [density_kahlerPower_ae (hF.isPositive k)] with x hx
    rw [hx, mul_one]
  have hle : ((hF.isPositive k).traceMeasure (K ∩ O k)).toReal ≤
      truncAt B O k (kahlerPower n q) ψ := by
    rw [hval, ← measureReal_def, ← integral_indicator_one (hK.measurableSet.inter
      (hF.measurableSet k))]
    have hi : Integrable (fun x => ψ x * (O k).indicator (fun _ => (1 : ℝ)) x)
        (hF.isPositive k).traceMeasure := by
      refine (hF.isPositive k).integrable_mul_of_bounded ψ.continuous ψ.hasCompactSupport
        ψ.tsupport_subset (measurable_const.indicator (hF.measurableSet k)).aestronglyMeasurable
        ⟨1, fun x _ => by by_cases hx : x ∈ O k <;> simp [hx]⟩
    refine integral_mono_of_nonneg (ae_of_all _ fun x => ?_) hi (ae_of_all _ fun x => ?_)
    · by_cases hx : x ∈ K ∩ O k <;> simp [hx]
    · change (K ∩ O k).indicator 1 x ≤ ψ x * (O k).indicator (fun _ => (1 : ℝ)) x
      by_cases hx : x ∈ K ∩ O k
      · rw [Set.indicator_of_mem hx, Pi.one_apply, Set.indicator_of_mem hx.2, mul_one]
        exact le_of_eq (hχ'1 x hx.1).symm
      · rw [Set.indicator_of_notMem hx]
        exact mul_nonneg (hχ'01 x).1 (by by_cases h : x ∈ O k <;> simp [h])
  have hfin : (hF.isPositive k).traceMeasure (K ∩ O k) ≠ ⊤ :=
    ((measure_mono inter_subset_left).trans_lt ((hF.isPositive k).traceMeasure_lt_top hK hKU)).ne
  rw [← ENNReal.ofReal_toReal hfin]
  exact ENNReal.ofReal_le_ofReal (hle.trans (hM ⟨k, rfl⟩))

theorem IsTruncationFamily.glue_congr {B' : ℕ → LocalProductCurrent n U q} {O' : ℕ → Set
    (ComplexModel n)}
    (hF : IsTruncationFamily B O) (hF' : IsTruncationFamily B' O') (hB : B = B') (hO : O = O') :
    hF.glue = hF'.glue := by
  subst hB
  subst hO
  rfl

end Converse

/-! ### Locality of the non-pluripolar product -/

section Product

variable {p q : ℕ} (hqp : q + p = n)

variable {U : Opens (ComplexModel n)} {φ : Fin p → (ComplexModel n) → EReal}

/-- The `k`-th truncated product only depends on the values of the potentials on `U`. -/
theorem truncatedBT_congr {φ' : Fin p → (ComplexModel n) → EReal} (h : ∀ i, ∀ x ∈ U,
    φ i x = φ' i x) :
    truncatedBT hqp U φ = truncatedBT hqp U φ' := by
  funext k
  refine LocalBedfordTaylorDecreasing.btProduct_congr p q _ _ _ fun i x hx => ?_
  simp only [truncationReal, truncation, h i x hx]

theorem strictLocus_congr {φ' : Fin p → (ComplexModel n) → EReal} (h : ∀ i, ∀ x ∈ U,
    φ i x = φ' i x) :
    BedfordTaylorTopDegree.strictLocus U φ = BedfordTaylorTopDegree.strictLocus U φ' := by
  funext k
  ext x
  simp only [BedfordTaylorTopDegree.strictLocus, mem_ofPred_eq]
  exact ⟨fun ⟨hx, h'⟩ => ⟨hx, fun i => h i x hx ▸ h' i⟩,
    fun ⟨hx, h'⟩ => ⟨hx, fun i => (h i x hx).symm ▸ h' i⟩⟩

/-- **The product only depends on the potentials on `U`.** -/
theorem nonPluripolarProduct_congr {φ' : Fin p → (ComplexModel n) → EReal}
    (h : ∀ i, ∀ x ∈ U, φ i x = φ' i x) :
    (IsWellDefinedOn hqp U φ ↔ IsWellDefinedOn hqp U φ') ∧
      nonPluripolarProduct hqp U φ = nonPluripolarProduct hqp U φ' := by
  have hB := truncatedBT_congr hqp h
  have hO := strictLocus_congr h
  refine ⟨by unfold IsWellDefinedOn; rw [hB, hO], ?_⟩
  by_cases hφ : ∀ i, PlurisubharmonicOn (φ i) U
  · have hφ' : ∀ i, PlurisubharmonicOn (φ' i) U := fun i x hx =>
      (hφ i x hx).congr (Filter.eventually_of_mem (U.isOpen.mem_nhds hx) fun y hy => h i y hy)
    rw [nonPluripolarProduct_eq hqp hφ, nonPluripolarProduct_eq hqp hφ']
    exact IsTruncationFamily.glue_congr _ _ hB hO
  · have hφ' : ¬ ∀ i, PlurisubharmonicOn (φ' i) U := fun hφ' => hφ fun i x hx =>
      (hφ' i x hx).congr (Filter.eventually_of_mem (U.isOpen.mem_nhds hx) fun y hy =>
        (h i y hy).symm)
    rw [nonPluripolarProduct, dite_eq_right hφ, nonPluripolarProduct, dite_eq_right hφ']

/-- **Symmetry**: the product does not depend on the ordering of the factors (`prop:npp1` (2)). -/
theorem nonPluripolarProduct_comp_perm (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (σ : Equiv.Perm (Fin p)) :
    (IsWellDefinedOn hqp U (φ ∘ σ) ↔ IsWellDefinedOn hqp U φ) ∧
      nonPluripolarProduct hqp U (φ ∘ σ) = nonPluripolarProduct hqp U φ := by
  have hB : truncatedBT hqp U (φ ∘ σ) = truncatedBT hqp U φ := by
    funext k
    exact LocalBedfordTaylorCalculus.btProduct_comp_perm p q _ (isPositive_oneCurrentOf hqp)
      (isClosedAny_oneCurrentOf hqp) (fun i => truncationReal (φ i) k)
      (fun i => truncationReal_isLocallyBoundedPshOn (hφ i) k) σ
  have hO : BedfordTaylorTopDegree.strictLocus U (φ ∘ σ) =
      BedfordTaylorTopDegree.strictLocus U φ := by
    funext k
    ext x
    simp only [BedfordTaylorTopDegree.strictLocus, mem_ofPred_eq, Function.comp_apply]
    exact ⟨fun ⟨hx, h⟩ => ⟨hx, fun i => by simpa using h (σ.symm i)⟩,
      fun ⟨hx, h⟩ => ⟨hx, fun i => h (σ i)⟩⟩
  refine ⟨by unfold IsWellDefinedOn; rw [hB, hO], ?_⟩
  rw [nonPluripolarProduct_eq hqp (φ := φ ∘ σ) (fun i => hφ (σ i)), nonPluripolarProduct_eq hqp hφ]
  exact IsTruncationFamily.glue_congr _ _ hB hO

/-! #### Restriction to open subsets -/

theorem restrict_oneCurrentOf' {V : Opens (ComplexModel n)} (hVU : V ≤ U) :
    restrict hVU (oneCurrentOf (U := U) hqp) = oneCurrentOf (U := V) hqp := by
  subst hqp
  exact LocalCurrentPullbackDdc.restrict_oneCurrent hVU

theorem restrict_restrict {V W : Opens (ComplexModel n)} (hWV : W ≤ V) (hVU : V ≤ U)
    (T : LocalProductCurrent n U q) :
    restrict hWV (restrict hVU T) = restrict (hWV.trans hVU) T := by
  ext γ ψ
  simp only [LocalBedfordTaylorLocality.restrict_apply]
  congr 1
  ext x
  simp

theorem truncatedBT_restrict (hφ : ∀ i, PlurisubharmonicOn (φ i) U) {V : Opens (ComplexModel n)}
    (hVU : V ≤ U)
    (k : ℕ) : truncatedBT hqp V φ k = restrict hVU (truncatedBT hqp U φ k) := by
  rw [truncatedBT, truncatedBT, ← btProduct_restrict hVU p q _ _ (isPositive_oneCurrentOf hqp)
    (isClosedAny_oneCurrentOf hqp) (fun i => truncationReal_isLocallyBoundedPshOn (hφ i) k),
    restrict_oneCurrentOf' hqp hVU]

theorem strictLocus_restrict {V : Opens (ComplexModel n)} (hVU : V ≤ U) (k : ℕ) :
    BedfordTaylorTopDegree.strictLocus V φ k =
      BedfordTaylorTopDegree.strictLocus U φ k ∩ V := by
  ext x
  simp only [BedfordTaylorTopDegree.strictLocus, mem_inter_iff, mem_ofPred_eq, SetLike.mem_coe]
  exact ⟨fun ⟨hx, h⟩ => ⟨⟨hVU hx, h⟩, hx⟩, fun ⟨⟨_, h⟩, hx⟩ => ⟨hx, h⟩⟩

/-- **Well-definedness passes to open subsets.** -/
theorem isWellDefinedOn_restrict (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hW : IsWellDefinedOn hqp U φ) {V : Opens (ComplexModel n)} (hVU : V ≤ U) : IsWellDefinedOn
      hqp V φ := by
  intro V' hV'V hconn α hαs hαp K hK hKV'
  have h := hW V' (hV'V.trans hVU) hconn α hαs hαp K hK hKV'
  have e : ∀ k, K ∩ BedfordTaylorTopDegree.strictLocus V φ k =
      K ∩ BedfordTaylorTopDegree.strictLocus U φ k := fun k => by
    rw [strictLocus_restrict hVU k]
    ext x
    constructor
    · rintro ⟨hxK, hxO, -⟩
      exact ⟨hxK, hxO⟩
    · rintro ⟨hxK, hxO⟩
      exact ⟨hxK, hxO, hV'V (hKV' hxK)⟩
  simp_rw [e, truncatedBT_restrict hqp hφ hVU, restrict_restrict]
  exact h

theorem indicator_strictLocus_restrict {V : Opens (ComplexModel n)} (hVU : V ≤ U)
    {x : (ComplexModel n)} (hx : x ∈ V)
    (k : ℕ) :
    (BedfordTaylorTopDegree.strictLocus V φ k).indicator (fun _ => (1 : ℝ)) x =
      (BedfordTaylorTopDegree.strictLocus U φ k).indicator (fun _ => (1 : ℝ)) x := by
  have : x ∈ BedfordTaylorTopDegree.strictLocus V φ k ↔
      x ∈ BedfordTaylorTopDegree.strictLocus U φ k := by
    rw [strictLocus_restrict hVU k]
    exact ⟨fun h => h.1, fun h => ⟨h, hx⟩⟩
  by_cases h : x ∈ BedfordTaylorTopDegree.strictLocus V φ k
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (this.mp h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (this.mpr h'))]

theorem indicator_compl_strictLocus_restrict {V : Opens (ComplexModel n)} (hVU : V ≤ U)
    {x : (ComplexModel n)} (hx : x ∈ V) :
    (⋃ k, BedfordTaylorTopDegree.strictLocus V φ k)ᶜ.indicator (fun _ => (1 : ℝ)) x =
      (⋃ k, BedfordTaylorTopDegree.strictLocus U φ k)ᶜ.indicator (fun _ => (1 : ℝ)) x := by
  have : x ∈ (⋃ k, BedfordTaylorTopDegree.strictLocus V φ k)ᶜ ↔
      x ∈ (⋃ k, BedfordTaylorTopDegree.strictLocus U φ k)ᶜ := by
    simp only [mem_compl_iff, mem_iUnion]
    refine not_congr ⟨fun ⟨k, h⟩ => ⟨k, ?_⟩, fun ⟨k, h⟩ => ⟨k, ?_⟩⟩
    · rw [strictLocus_restrict hVU k] at h
      exact h.1
    · rw [strictLocus_restrict hVU k]
      exact ⟨h, hx⟩
  by_cases h : x ∈ (⋃ k, BedfordTaylorTopDegree.strictLocus V φ k)ᶜ
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (this.mp h)]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (this.mpr h'))]

/-- **The product commutes with restriction to open subsets** (`prop:npp1` (1), `eq:ppp2`). -/
theorem restrict_nonPluripolarProduct (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hW : IsWellDefinedOn hqp U φ) {V : Opens (ComplexModel n)} (hVU : V ≤ U) :
    restrict hVU (nonPluripolarProduct hqp U φ) = nonPluripolarProduct hqp V φ := by
  have hφV : ∀ i, PlurisubharmonicOn (φ i) V := fun i => (hφ i).mono hVU
  have hWV := isWellDefinedOn_restrict hqp hφ hW hVU
  have hS := isPositive_nonPluripolarProduct hqp hφ hW
  have hSV := isPositive_restrict hS hVU
  have hOm := BedfordTaylorTopDegree.measurableSet_strictLocus hφ
  have hOVm := BedfordTaylorTopDegree.measurableSet_strictLocus hφV
  have hb : ∀ A : Set (ComplexModel n), IsLocallyBoundedOn (A.indicator fun _ => (1 : ℝ)) U :=
    fun A => isLocallyBoundedOn_indicator_one A
  have hbV : ∀ A : Set (ComplexModel n), IsLocallyBoundedOn (A.indicator fun _ => (1 : ℝ)) V :=
    fun A => isLocallyBoundedOn_indicator_one A
  refine eq_nonPluripolarProduct_of_mulBorel hqp hφV hWV hSV (fun k => ?_) ?_
  · calc mulBorel (restrict hVU (nonPluripolarProduct hqp U φ))
          ((BedfordTaylorTopDegree.strictLocus V φ k).indicator fun _ => (1 : ℝ)) =
        mulBorel (restrict hVU (nonPluripolarProduct hqp U φ))
          ((BedfordTaylorTopDegree.strictLocus U φ k).indicator fun _ => (1 : ℝ)) :=
          mulBorel_congr hSV (measurable_const.indicator (hOVm k)) (hbV _)
            (measurable_const.indicator (hOm k)) (hbV _)
            fun x hx => indicator_strictLocus_restrict hVU hx k
      _ = restrict hVU (mulBorel (nonPluripolarProduct hqp U φ)
          ((BedfordTaylorTopDegree.strictLocus U φ k).indicator fun _ => (1 : ℝ))) :=
          mulBorel_restrict hS hVU (measurable_const.indicator (hOm k)) (hb _)
      _ = restrict hVU (mulBorel (truncatedBT hqp U φ k)
          ((BedfordTaylorTopDegree.strictLocus U φ k).indicator fun _ => (1 : ℝ))) := by
          rw [mulBorel_nonPluripolarProduct_strictLocus hqp hφ hW k]
          rfl
      _ = mulBorel (truncatedBT hqp V φ k)
          ((BedfordTaylorTopDegree.strictLocus U φ k).indicator fun _ => (1 : ℝ)) := by
          rw [truncatedBT_restrict hqp hφ hVU k, mulBorel_restrict
            (isPositive_truncatedBT hqp hφ k).1 hVU (measurable_const.indicator (hOm k)) (hb _)]
      _ = mulBorel (truncatedBT hqp V φ k)
          ((BedfordTaylorTopDegree.strictLocus V φ k).indicator fun _ => (1 : ℝ)) :=
          mulBorel_congr (isPositive_truncatedBT hqp hφV k).1
            (measurable_const.indicator (hOm k)) (hbV _) (measurable_const.indicator (hOVm k))
            (hbV _) fun x hx => (indicator_strictLocus_restrict hVU hx k).symm
      _ = BedfordTaylorTopDegree.truncatedProduct hqp V φ k := rfl
  · have hA : MeasurableSet (⋃ k, BedfordTaylorTopDegree.strictLocus U φ k)ᶜ :=
      (MeasurableSet.iUnion hOm).compl
    have hAV : MeasurableSet (⋃ k, BedfordTaylorTopDegree.strictLocus V φ k)ᶜ :=
      (MeasurableSet.iUnion hOVm).compl
    rw [mulBorel_congr hSV (measurable_const.indicator hAV) (hbV _)
      (measurable_const.indicator hA) (hbV _)
      (fun x hx => indicator_compl_strictLocus_restrict hVU hx),
      mulBorel_restrict hS hVU (measurable_const.indicator hA) (hb _),
      mulBorel_nonPluripolarProduct_compl hqp hφ hW]
    ext γ ψ
    simp [LocalBedfordTaylorLocality.restrict_apply]

/-- **Well-definedness is a local property** (`prop:npp1` (1), last sentence): it holds on `U`
when it holds on every member of an open cover of `U`. -/
theorem isWellDefinedOn_of_cover (hφ : ∀ i, PlurisubharmonicOn (φ i) U) {ι : Type*}
    (V : ι → Opens (ComplexModel n)) (hVU : ∀ i, V i ≤ U) (hcov : (U : Set (ComplexModel n))
      ⊆ ⋃ i, (V i : Set (ComplexModel n)))
    (hW : ∀ i, IsWellDefinedOn hqp (V i) φ) : IsWellDefinedOn hqp U φ := by
  have hφV : ∀ i j, PlurisubharmonicOn (φ j) (V i) := fun i j => (hφ j).mono (hVU i)
  set hF := isTruncationFamily hqp hφ
  rw [isWellDefinedOn_iff hqp hφ, hF.hasLocallyFiniteMass_iff]
  intro K hK hKU
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun i => (V i : Set (ComplexModel n)))
    (fun i => (V i).isOpen)
    (hKU.trans hcov)
  obtain ⟨L, hLc, hLV, hKL⟩ := hK.finite_compact_cover t (fun i => (V i : Set (ComplexModel n)))
    (fun i _ => (V i).isOpen) ht
  have hb : ∀ i, ⨆ k, ((isTruncationFamily hqp (hφV i)).isPositive k).traceMeasure
      (L i ∩ BedfordTaylorTopDegree.strictLocus (V i) φ k) < ⊤ := fun i =>
    ((isTruncationFamily hqp (hφV i)).hasLocallyFiniteMass_iff.mp
      ((isWellDefinedOn_iff hqp (hφV i)).mp (hW i))) (L i) (hLc i) (hLV i)
  have heq : ∀ i k, (hF.isPositive k).traceMeasure (L i ∩ BedfordTaylorTopDegree.strictLocus U φ
    k) =
      ((isTruncationFamily hqp (hφV i)).isPositive k).traceMeasure
        (L i ∩ BedfordTaylorTopDegree.strictLocus (V i) φ k) := fun i k => by
    rw [traceMeasure_congr ((isTruncationFamily hqp (hφV i)).isPositive k)
      (isPositive_restrict (hF.isPositive k) (hVU i))
      (truncatedBT_restrict hqp hφ (hVU i) k), traceMeasure_restrict (hF.isPositive k) (hVU i),
      strictLocus_restrict (hVU i), Measure.restrict_apply
        ((hLc i).measurableSet.inter ((hF.measurableSet k).inter (V i).isOpen.measurableSet))]
    congr 1
    ext x
    simp only [mem_inter_iff]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, h2, hLV i h1⟩, hLV i h1⟩
    · rintro ⟨⟨h1, h2, -⟩, -⟩
      exact ⟨h1, h2⟩
  refine lt_of_le_of_lt (b := ∑ i ∈ t, ⨆ k, ((isTruncationFamily hqp (hφV i)).isPositive
    k).traceMeasure
      (L i ∩ BedfordTaylorTopDegree.strictLocus (V i) φ k)) (iSup_le fun k => ?_)
    (ENNReal.sum_lt_top.mpr fun i _ => hb i)
  calc (hF.isPositive k).traceMeasure (K ∩ BedfordTaylorTopDegree.strictLocus U φ k) ≤
        ∑ i ∈ t, (hF.isPositive k).traceMeasure
          (L i ∩ BedfordTaylorTopDegree.strictLocus U φ k) := by
        refine (measure_mono ?_).trans (measure_biUnion_finset_le _ _)
        rintro x ⟨hxK, hxO⟩
        rw [hKL] at hxK
        obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hxK
        exact mem_iUnion₂.mpr ⟨i, hi, hxi, hxO⟩
    _ ≤ ∑ i ∈ t, ⨆ k, ((isTruncationFamily hqp (hφV i)).isPositive k).traceMeasure
          (L i ∩ BedfordTaylorTopDegree.strictLocus (V i) φ k) :=
        Finset.sum_le_sum fun i _ => (heq i k).le.trans (le_iSup (fun k =>
          ((isTruncationFamily hqp (hφV i)).isPositive k).traceMeasure
            (L i ∩ BedfordTaylorTopDegree.strictLocus (V i) φ k)) k)

/-! #### Locally bounded potentials -/

/-- On the strict locus, the truncated products of locally bounded potentials are the restrictions
of their Bedford–Taylor product. -/
theorem truncatedProduct_of_isLocallyBoundedPshOn {u : Fin p → (ComplexModel n) → ℝ}
    (hu : ∀ i, IsLocallyBoundedPshOn U (u i)) (k : ℕ) :
    BedfordTaylorTopDegree.truncatedProduct hqp U (fun i z => (u i z : EReal)) k =
      mulBorel (btProduct p q u (oneCurrentOf (U := U) hqp))
        ((BedfordTaylorTopDegree.strictLocus U (fun i z => (u i z : EReal)) k).indicator
          fun _ => (1 : ℝ)) := by
  have hL : BedfordTaylorTopDegree.strictLocus U (fun i z => (u i z : EReal)) k =
      {z | z ∈ U ∧ ∀ i, -(k : ℝ) < u i z} := by
    ext z
    simp only [BedfordTaylorTopDegree.strictLocus, mem_ofPred_eq, EReal.coe_lt_coe_iff]
  rw [hL, BedfordTaylorTopDegree.truncatedProduct, hL]
  refine BedfordTaylorTopDegree.mulBorel_btProduct_max_const hqp hu
    (fun i => truncationReal_isLocallyBoundedPshOn (hu i).1 k) (-(k : ℝ)) fun i z _ => ?_
  simp only [truncationReal, truncation]
  rcases le_total (u i z) (-(k : ℝ)) with h | h
  · rw [max_eq_right (EReal.coe_le_coe_iff.mpr h), max_eq_right h, EReal.toReal_coe]
  · rw [max_eq_left (EReal.coe_le_coe_iff.mpr h), max_eq_left h, EReal.toReal_coe]

/-- **Locally bounded potentials** (`prop:npp1` (3), first sentence): the non-pluripolar product
of locally bounded psh functions is well defined. -/
theorem isWellDefinedOn_of_isLocallyBoundedPshOn {u : Fin p → (ComplexModel n) → ℝ}
    (hu : ∀ i, IsLocallyBoundedPshOn U (u i)) :
    IsWellDefinedOn hqp U (fun i z => (u i z : EReal)) := by
  have hφ : ∀ i, PlurisubharmonicOn (fun z => (u i z : EReal)) U := fun i => (hu i).1
  set hF := isTruncationFamily hqp hφ
  have hS := (isPositive_btProduct p q u _ (isPositive_oneCurrentOf hqp)
    (isClosedAny_oneCurrentOf hqp) hu).1
  rw [isWellDefinedOn_iff hqp hφ, hF.hasLocallyFiniteMass_iff]
  intro K hK hKU
  refine lt_of_le_of_lt (iSup_le fun k => ?_) (hS.traceMeasure_lt_top hK hKU)
  rw [traceMeasure_inter_eq_of_mulBorel_eq (hF.isPositive k) hS (hF.measurableSet k)
    (truncatedProduct_of_isLocallyBoundedPshOn hqp hu k) hK hKU]
  exact measure_mono inter_subset_left

/-- **The non-pluripolar product of locally bounded potentials is their Bedford–Taylor product**
(`prop:npp1` (3), first sentence). -/
theorem nonPluripolarProduct_of_isLocallyBoundedPshOn {u : Fin p → (ComplexModel n) → ℝ}
    (hu : ∀ i, IsLocallyBoundedPshOn U (u i)) :
    nonPluripolarProduct hqp U (fun i z => (u i z : EReal)) =
      btProduct p q u (oneCurrentOf (U := U) hqp) := by
  have hφ : ∀ i, PlurisubharmonicOn (fun z => (u i z : EReal)) U := fun i => (hu i).1
  have hS := (isPositive_btProduct p q u _ (isPositive_oneCurrentOf hqp)
    (isClosedAny_oneCurrentOf hqp) hu).1
  have hOm := BedfordTaylorTopDegree.measurableSet_strictLocus hφ
  refine (eq_nonPluripolarProduct_of_mulBorel hqp hφ
    (isWellDefinedOn_of_isLocallyBoundedPshOn hqp hu) hS
    (fun k => (truncatedProduct_of_isLocallyBoundedPshOn hqp hu k).symm) ?_).symm
  have hA : MeasurableSet (⋃ k, BedfordTaylorTopDegree.strictLocus U
      (fun i z => (u i z : EReal)) k)ᶜ := (MeasurableSet.iUnion hOm).compl
  rw [mulBorel_congr hS (measurable_const.indicator hA) (isLocallyBoundedOn_indicator_one _)
    measurable_const (fun _ _ _ => ⟨0, fun _ _ => by simp⟩) (w := fun _ => 0) (fun x hx => ?_),
    mulBorel_const hS, zero_smul]
  obtain ⟨k, hk⟩ := exists_nat_gt (∑ i, |u i x|)
  have hmem : x ∈ ⋃ k, BedfordTaylorTopDegree.strictLocus U (fun i z => (u i z : EReal)) k := by
    refine mem_iUnion.mpr ⟨k, hx, fun i => ?_⟩
    rw [EReal.coe_lt_coe_iff]
    have h1 : |u i x| ≤ ∑ j, |u j x| :=
      Finset.single_le_sum (f := fun j => |u j x|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    have h2 := neg_abs_le (u i x)
    linarith
  rw [Set.indicator_of_notMem (Set.notMem_compl_iff.mpr hmem)]

end Product

end SGPT.NPP.NonPluripolarCurrent
