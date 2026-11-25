/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.NPP.NonPluripolarCurrentPlurifine
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.SourceBedfordTaylorCurrentNormalization
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.SourceBedfordTaylorTraceNormalization
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.ActualPositiveCurrentLebesgueUniqueness
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PositiveCurrentBorelAddition

/-!
# Multilinearity of the non-pluripolar product of arbitrary degree

Source: `chapter_npp.tex`, `prop:npp1` (6) (`eq:ppp6`); Xia, *Foundations of pluripotential
theory*, `prop:nonpluripolar-local-calculus` ("Additivity", and the homogeneity paragraph).

Let `U ⊆ ℂⁿ` be open, `q + p = n`, `φ₁, …, φ_p, ψ` psh on `U`, `j` a slot and `a, b > 0`.  Write
`φ^{ab}` for the tuple with `a φ_j + b ψ` in the slot `j` and `φ^ψ` for the tuple with `ψ` in the
slot `j`.  With `E_k = O_k(φ) ∩ O_k(φ^ψ)` (all of `φ₁, …, φ_p, ψ` are `> -k`), a Borel plurifine
open set, and `N ≥ a + b` an integer, the truncations satisfy on `E_k`:
`(a φ_j + b ψ) ∨ (-Nk) = a (φ_j ∨ (-k)) + b (ψ ∨ (-k))` and `φ_i ∨ (-Nk) = φ_i ∨ (-k)`.  Plurifine
locality and the multilinearity of bounded Bedford–Taylor products give
`1_{E_k} B_{Nk}(φ^{ab}) = a 1_{E_k} B_k(φ) + b 1_{E_k} B_k(φ^ψ)` (`mulBorel_truncatedBT_combo`).

* `glueMeasure_combo` — the limit measures (the glued trace measures of the truncations,
  possibly infinite on compact sets) satisfy `μ(φ^{ab}) = a μ(φ) + b μ(φ^ψ)`, provided `φ_j` and
  `ψ` are nondegenerate (`≢ -∞` near every point), so that their pole sets are locally pluripolar
  and are not charged by the truncated products;
* `isWellDefinedOn_combo_iff` — **`prop:npp1` (6), well-definedness**: the left-hand side of
  `eq:ppp6` is well defined iff both terms on the right-hand side are;
* `nonPluripolarProduct_combo` — **`eq:ppp6`**:
  `⟨dd^c(a φ_j + b ψ) ∧ ⋀_{i ≠ j} dd^c φ_i⟩ = a ⟨⋀ dd^c φ_i⟩ + b ⟨dd^c ψ ∧ ⋀_{i≠j} dd^c φ_i⟩`;
* `isNonPluripolarWellDefined_combo_iff`, `nonPluripolarProduct_combo_inChart` — the same on a
  complex manifold, for psh functions in the sense of `def:pshmfd`.

General tools: `traceMeasure_mulBorel_indicator` (`σ_{1_A T} = σ_T|_A`) and
`eq_of_mulBorel_indicator_eq` (two positive currents carried by `⋃ₖ E_k` that agree on every
`E_k` are equal).
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal Manifold

namespace SGPT.NPP.NonPluripolarCurrent

open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
open SGPT.Foundations.Analysis.Pending.LocalCurrentLebesgue

attribute [local instance] addCommGroupFormSpan

variable {n : ℕ}

/-! ### Generalities on positive currents -/

section General

variable {U : Opens (ComplexModel n)} {q : ℕ}

theorem indicator_one_nonneg (A : Set (ComplexModel n)) (x : (ComplexModel n)) : 0 ≤ A.indicator
    (fun _ => (1 : ℝ)) x := by
  by_cases hx : x ∈ A <;> simp [hx]

theorem isPositive_mulBorel_indicator {T : LocalProductCurrent n U q} (hT : IsPositive T)
    {A : Set (ComplexModel n)} (hA : MeasurableSet A) :
    IsPositive (mulBorel T (A.indicator fun _ => (1 : ℝ))) :=
  BedfordTaylorTopDegree.isPositive_mulBorel_of_nonneg hT (measurable_const.indicator hA)
    (isLocallyBoundedOn_indicator_one A) (indicator_one_nonneg A)

/-- **The trace measure of `1_A T` is `σ_T|_A`.** -/
theorem traceMeasure_mulBorel_indicator {T : LocalProductCurrent n U q} (hT : IsPositive T)
    {A : Set (ComplexModel n)} (hA : MeasurableSet A) :
    (isPositive_mulBorel_indicator hT hA).traceMeasure = hT.traceMeasure.restrict A := by
  have hS := isPositive_mulBorel_indicator hT hA
  refine LocalBedfordTaylorLocality.eq_of_forall_testFunction_integral_eq (U := U)
    hS.traceMeasure_compl
    (le_antisymm ((Measure.le_iff'.mp Measure.restrict_le_self _).trans
      hT.traceMeasure_compl.le) zero_le)
    (fun K hK hKU => hS.traceMeasure_lt_top hK hKU)
    (fun K hK hKU => ((Measure.le_iff'.mp Measure.restrict_le_self _).trans_lt
      (hT.traceMeasure_lt_top hK hKU))) fun φ => ?_
  rw [hS.integral_traceMeasure, mulBorel_apply hT (measurable_const.indicator hA)
    (isLocallyBoundedOn_indicator_one A), ← integral_indicator hA]
  refine integral_congr_ae ?_
  filter_upwards [density_kahlerPower_ae hT] with x hx
  rw [hx]
  by_cases hxA : x ∈ A <;> simp [hxA]

/-- `σ_{1_A T}(s) = σ_T(s ∩ A)`. -/
theorem traceMeasure_mulBorel_indicator_apply {T : LocalProductCurrent n U q}
    (hT : IsPositive T) {A : Set (ComplexModel n)} (hA : MeasurableSet A) (hS : IsPositive
      (mulBorel T (A.indicator fun _ => (1 : ℝ)))) {s : Set (ComplexModel n)} (hs : MeasurableSet
        s) :
    hS.traceMeasure s = hT.traceMeasure (s ∩ A) := by
  rw [show hS.traceMeasure = (isPositive_mulBorel_indicator hT hA).traceMeasure from rfl,
    traceMeasure_mulBorel_indicator hT hA, Measure.restrict_apply hs]

/-- **Positive currents carried by `⋃ₖ E_k` and agreeing on every `E_k` are equal**: if
`1_{E_k} S = 1_{E_k} S'` for an increasing sequence of Borel sets and the trace measures of `S`
and `S'` are carried by `⋃ₖ E_k`, then `S = S'`. -/
theorem eq_of_mulBorel_indicator_eq {S S' : LocalProductCurrent n U q} (hS : IsPositive S)
    (hS' : IsPositive S') {A : ℕ → Set (ComplexModel n)} (hAm : ∀ k, MeasurableSet (A k))
      (hA : Monotone A)
    (h : ∀ k, mulBorel S ((A k).indicator fun _ => (1 : ℝ)) =
      mulBorel S' ((A k).indicator fun _ => (1 : ℝ)))
    (hSA : ∀ᵐ x ∂hS.traceMeasure, ∃ k, x ∈ A k)
    (hS'A : ∀ᵐ x ∂hS'.traceMeasure, ∃ k, x ∈ A k) : S = S' := by
  have key : ∀ {T : LocalProductCurrent n U q} (hT : IsPositive T),
      (∀ᵐ x ∂hT.traceMeasure, ∃ k, x ∈ A k) → ∀ (γ : formSpan n q) (χ : 𝓓(U, ℝ)),
      Tendsto (fun k => mulBorel T ((A k).indicator fun _ => (1 : ℝ)) γ χ) atTop
        (𝓝 (T γ χ)) := by
    intro T hT hTA γ χ
    have hlim : ∀ᵐ x ∂hT.traceMeasure,
        Tendsto (fun k => (A k).indicator (fun _ => (1 : ℝ)) x) atTop (𝓝 1) := by
      filter_upwards [hTA] with x hx
      obtain ⟨k₀, hk₀⟩ := hx
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop k₀] with k hk
      rw [Set.indicator_of_mem (hA hk hk₀)]
    simpa only [mulBorel_const hT, one_smul] using
      tendsto_mulBorel_apply_of_ae_tendsto hT
        (fun k => measurable_const.indicator (hAm k)) measurable_const
        (fun k x => by by_cases hx : x ∈ A k <;> simp [hx]) (fun _ => by simp)
        hlim γ χ
  ext γ χ
  have h1 := key hS hSA γ χ
  have h2 := key hS' hS'A γ χ
  simp_rw [h] at h1
  exact tendsto_nhds_unique h1 h2

/-- `1_A (a S + b T) = a 1_A S + b 1_A T` for positive currents and `a, b ≥ 0`. -/
theorem mulBorel_smul_add_smul {S T : LocalProductCurrent n U q} (hS : IsPositive S)
    (hT : IsPositive T) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {f : (ComplexModel n)
      → ℝ} (hf : Measurable f)
    (hfb : IsLocallyBoundedOn f U) :
    mulBorel (a • S + b • T) f = a • mulBorel S f + b • mulBorel T f := by
  rw [PositiveCurrentBorelAddition.mulBorel_add_currents (hS.smul ha) (hT.smul hb) hf hfb,
    SourceBedfordTaylorCurrentNormalization.mulBorel_smul_current hS ha hf hfb,
    SourceBedfordTaylorCurrentNormalization.mulBorel_smul_current hT hb hf hfb]

/-- `σ_{a S + b T} = a σ_S + b σ_T` for `a, b ≥ 0`. -/
theorem traceMeasure_smul_add_smul {S T : LocalProductCurrent n U q} (hS : IsPositive S)
    (hT : IsPositive T) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hST : IsPositive (a • S + b • T)) :
    hST.traceMeasure = ENNReal.ofReal a • hS.traceMeasure + ENNReal.ofReal b • hT.traceMeasure :=
      by
  rw [show hST.traceMeasure = ((hS.smul ha).add (hT.smul hb)).traceMeasure from rfl,
    ActualPositiveCurrentLebesgueUniqueness.traceMeasure_add (hS.smul ha) (hT.smul hb),
    SourceBedfordTaylorTraceNormalization.traceMeasure_smul hS ha,
    SourceBedfordTaylorTraceNormalization.traceMeasure_smul hT hb]
  rfl

end General

/-! ### Multilinearity of bounded Bedford–Taylor products -/

section Bounded

variable {U : Opens (ComplexModel n)}

theorem isLocallyBoundedPshOn_const_mul {v : (ComplexModel n) → ℝ} (hv : IsLocallyBoundedPshOn U
    v) {a : ℝ}
    (ha : 0 < a) : IsLocallyBoundedPshOn U fun z => a * v z := by
  refine ⟨?_, fun z hz => ?_⟩
  · simpa only [EReal.coe_mul] using hv.1.const_mul ha
  · obtain ⟨V, hzV, hVU, C, hC⟩ := hv.2 z hz
    exact ⟨V, hzV, hVU, a * C, fun y hy => by
      rw [abs_mul, abs_of_pos ha]
      exact mul_le_mul_of_nonneg_left (hC y hy) ha.le⟩

theorem mulBorel_const_mul_fun {m : ℕ} {S : LocalProductCurrent n U m} (hS : IsPositive S)
    {v : (ComplexModel n) → ℝ} (hv : Measurable v) (hvb : IsLocallyBoundedOn v U) (a : ℝ) :
    mulBorel S (fun z => a * v z) = a • mulBorel S v := by
  have hab : IsLocallyBoundedOn (fun z => a * v z) U := fun K hK hKU => by
    obtain ⟨C, hC⟩ := hvb K hK hKU
    refine ⟨|a| * C, fun x hx => ?_⟩
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hC x hx) (abs_nonneg a)
  ext γ φ
  rw [mulBorel_apply hS (hv.const_mul a) hab, LinearMap.smul_apply, _root_.smul_apply,
    mulBorel_apply hS hv hvb, smul_eq_mul, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  ring

/-- `dd^c((a v) S) = a dd^c(v S)`. -/
theorem ddcMul_const_mul {m : ℕ} {S : LocalProductCurrent n U (m + 1)} (hS : IsPositive S)
    {v : (ComplexModel n) → ℝ} (hv : IsLocallyBoundedPshOn U v) (a : ℝ) :
    ddcMul S (fun z => a * v z) = a • ddcMul S v := by
  have e : (U : Set (ComplexModel n)).indicator (fun z => a * v z) =
      fun z => a * (U : Set (ComplexModel n)).indicator v z := by
    funext z
    by_cases hz : z ∈ (U : Set (ComplexModel n)) <;> simp [hz]
  rw [ddcMul, ddcMul, e, mulBorel_const_mul_fun hS
    (measurable_indicator_of_isLocallyBoundedPshOn hv) (isLocallyBoundedOn_indicator hv),
    ddc_smul]

/-- **Homogeneity of the Bedford–Taylor product in each potential**. -/
theorem btProduct_update_const_mul (q r : ℕ) (T : LocalProductCurrent n U (r + q))
    (hT : IsPositive T) (hTc : IsClosedAny (r + q) T) (u : Fin q → (ComplexModel n) → ℝ)
    (hu : ∀ i, IsLocallyBoundedPshOn U (u i)) (j : Fin q) {v : (ComplexModel n) → ℝ}
    (hv : IsLocallyBoundedPshOn U v) {a : ℝ} (ha : 0 < a) :
    btProduct q r (Function.update u j fun z => a * v z) T =
      a • btProduct q r (Function.update u j v) T := by
  cases q with
  | zero => exact j.elim0
  | succ q =>
    open LocalBedfordTaylorCalculus LocalBedfordTaylorCollar in
    rw [btProduct_update_eq q r T hT hTc u hu j (isLocallyBoundedPshOn_const_mul hv ha),
      btProduct_update_eq q r T hT hTc u hu j hv]
    have h1 : r + (q + 1) = r + 1 + q := by omega
    have hX := isPositive_btProduct q (r + 1) (Fin.tail (u ∘ Equiv.swap 0 j)) (castLPC h1 T)
      (isPositive_castLPC h1 hT) (isClosedAny_castLPC h1 hTc) fun i => hu _
    simp only [btProduct_succ_eq_ddcMul q r _ T (castLPC h1 T) (heq_castLPC h1 T),
      Fin.tail_update_zero, Function.update_self]
    exact ddcMul_const_mul hX.1 hv a

/-- **Multilinearity of the Bedford–Taylor product in each potential**, with nonnegative
coefficients: `B(…, a v + b w, …) = a B(…, v, …) + b B(…, w, …)`. -/
theorem btProduct_update_combo (q r : ℕ) (T : LocalProductCurrent n U (r + q))
    (hT : IsPositive T) (hTc : IsClosedAny (r + q) T) (u : Fin q → (ComplexModel n) → ℝ)
    (hu : ∀ i, IsLocallyBoundedPshOn U (u i)) (j : Fin q) {v w : (ComplexModel n) → ℝ}
    (hv : IsLocallyBoundedPshOn U v) (hw : IsLocallyBoundedPshOn U w) {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) :
    btProduct q r (Function.update u j fun z => a * v z + b * w z) T =
      a • btProduct q r (Function.update u j v) T + b • btProduct q r (Function.update u j w)
        T := by
  rw [LocalBedfordTaylorCalculus.btProduct_update_add q r T hT hTc u hu j
      (isLocallyBoundedPshOn_const_mul hv ha) (isLocallyBoundedPshOn_const_mul hw hb),
    btProduct_update_const_mul q r T hT hTc u hu j hv ha,
    btProduct_update_const_mul q r T hT hTc u hu j hw hb]

end Bounded

/-! ### Truncation levels -/

section Levels

theorem ne_top_of_plurisubharmonicOn {u : (ComplexModel n) → EReal} {U : Set (ComplexModel n)} (hu
    : PlurisubharmonicOn u U)
    {x : (ComplexModel n)} (hx : x ∈ U) : u x ≠ ⊤ := by
  obtain ⟨V, -, hxV, hd⟩ := hu x hx
  exact hd.ne_top x hxV

theorem truncationReal_of_lt {u : (ComplexModel n) → EReal} {k : ℕ} {x : (ComplexModel n)}
    (h : ((-(k : ℝ) : ℝ) : EReal) < u x) : truncationReal u k x = (u x).toReal := by
  rw [truncationReal, truncation, max_eq_left h.le]

theorem neg_lt_of_le {v : EReal} {k m : ℕ} (hkm : k ≤ m)
    (h : ((-(k : ℝ) : ℝ) : EReal) < v) : ((-(m : ℝ) : ℝ) : EReal) < v :=
  lt_of_le_of_lt (EReal.coe_le_coe_iff.mpr (neg_le_neg (Nat.cast_le.mpr hkm))) h

theorem exists_nat_neg_lt {v : EReal} (hv : v ≠ ⊥) : ∃ k : ℕ, ((-(k : ℝ) : ℝ) : EReal) < v := by
  induction v using EReal.rec with
  | bot => exact absurd rfl hv
  | coe r =>
    obtain ⟨k, hk⟩ := exists_nat_gt (-r)
    exact ⟨k, EReal.coe_lt_coe_iff.mpr (by linarith)⟩
  | top => exact ⟨0, EReal.coe_lt_top _⟩

theorem truncationReal_mono_level {u : (ComplexModel n) → EReal} {k m : ℕ} (hkm : k ≤ m)
    {x : (ComplexModel n)}
    (hu : ((-(k : ℝ) : ℝ) : EReal) < u x) : truncationReal u m x = truncationReal u k x := by
  rw [truncationReal_of_lt (neg_lt_of_le hkm hu), truncationReal_of_lt hu]

/-- The integer level `N = ⌈a + b⌉₊ + 1` (so `N ≥ a + b` and `N ≥ 1`). -/
def comboLevel (a b : ℝ) : ℕ := ⌈a + b⌉₊ + 1

theorem le_comboLevel (a b : ℝ) : a + b ≤ comboLevel a b := by
  unfold comboLevel
  push_cast
  linarith [Nat.le_ceil (a + b)]

theorem one_le_comboLevel (a b : ℝ) : 1 ≤ comboLevel a b := by
  unfold comboLevel
  omega

theorem le_comboLevel_mul (a b : ℝ) (k : ℕ) : k ≤ comboLevel a b * k :=
  Nat.le_mul_of_pos_left k (one_le_comboLevel a b)

private theorem neg_comboLevel_lt_combo {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {u w : EReal} {k : ℕ} (hu : ((-(k : ℝ) : ℝ) : EReal) < u) (hut : u ≠ ⊤)
    (hw : ((-(k : ℝ) : ℝ) : EReal) < w) (hwt : w ≠ ⊤) :
    ((-((comboLevel a b * k : ℕ) : ℝ) : ℝ) : EReal) < (a : EReal) * u + (b : EReal) * w := by
  lift u to ℝ using ⟨hut, ne_bot_of_gt hu⟩
  lift w to ℝ using ⟨hwt, ne_bot_of_gt hw⟩
  rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_lt_coe_iff]
  have hu' := EReal.coe_lt_coe_iff.mp hu
  have hw' := EReal.coe_lt_coe_iff.mp hw
  have h1 := mul_lt_mul_of_pos_left hu' ha
  have h2 := mul_lt_mul_of_pos_left hw' hb
  have h3 : (a + b) * k ≤ (comboLevel a b : ℝ) * k :=
    mul_le_mul_of_nonneg_right (le_comboLevel a b) (Nat.cast_nonneg k)
  push_cast
  nlinarith only [h1, h2, h3]

/-- On `{u > -k} ∩ {w > -k}`: `(a u + b w) ∨ (-Nk) = a (u ∨ (-k)) + b (w ∨ (-k))`. -/
theorem truncationReal_combo {u w : (ComplexModel n) → EReal} {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    {k : ℕ}
    {x : (ComplexModel n)} (hu : ((-(k : ℝ) : ℝ) : EReal) < u x) (hut : u x ≠ ⊤)
    (hw : ((-(k : ℝ) : ℝ) : EReal) < w x) (hwt : w x ≠ ⊤) :
    truncationReal (fun z => (a : EReal) * u z + (b : EReal) * w z) (comboLevel a b * k) x =
      a * truncationReal u k x + b * truncationReal w k x := by
  have eu : u x = ((u x).toReal : EReal) := (EReal.coe_toReal hut (ne_bot_of_gt hu)).symm
  have ew : w x = ((w x).toReal : EReal) := (EReal.coe_toReal hwt (ne_bot_of_gt hw)).symm
  have hsum : (a : EReal) * u x + (b : EReal) * w x =
      ((a * (u x).toReal + b * (w x).toReal : ℝ) : EReal) := by
    rw [eu, ew]
    simp only [EReal.toReal_coe]
    norm_cast
  rw [truncationReal_of_lt (neg_comboLevel_lt_combo ha hb hu hut hw hwt),
    truncationReal_of_lt hu, truncationReal_of_lt hw]
  change ((a : EReal) * u x + (b : EReal) * w x).toReal = _
  rw [hsum, EReal.toReal_coe]

end Levels

/-! ### The common locus `E_k` -/

section Common

variable {p : ℕ} {U : Opens (ComplexModel n)}

/-- The tuple with `a φ_j + b ψ` in the slot `j` (the left-hand side of `eq:ppp6`). -/
def comboTuple (φ : Fin p → (ComplexModel n) → EReal) (j : Fin p) (a b : ℝ) (ψ : (ComplexModel n)
    → EReal) :
    Fin p → (ComplexModel n) → EReal :=
  Function.update φ j fun x => (a : EReal) * φ j x + (b : EReal) * ψ x

/-- `E_k = O_k(φ) ∩ O_k(φ^ψ)`: the points of `U` where all of `φ₁, …, φ_p, ψ` are `> -k`. -/
def commonLocus (U : Opens (ComplexModel n)) (φ : Fin p → (ComplexModel n) → EReal) (j : Fin p)
    (ψ : (ComplexModel n) → EReal) (k : ℕ) :
    Set (ComplexModel n) :=
  BedfordTaylorTopDegree.strictLocus U φ k ∩
    BedfordTaylorTopDegree.strictLocus U (Function.update φ j ψ) k

variable {φ : Fin p → (ComplexModel n) → EReal} {j : Fin p} {ψ : (ComplexModel n) → EReal}

theorem commonLocus_subset_left (k : ℕ) :
    commonLocus U φ j ψ k ⊆ BedfordTaylorTopDegree.strictLocus U φ k := inter_subset_left

theorem commonLocus_subset_right (k : ℕ) :
    commonLocus U φ j ψ k ⊆ BedfordTaylorTopDegree.strictLocus U (Function.update φ j ψ) k :=
  inter_subset_right

theorem commonLocus_subset (k : ℕ) : commonLocus U φ j ψ k ⊆ U := fun _ hx => hx.1.1

theorem lt_of_mem_commonLocus {k : ℕ} {x : (ComplexModel n)} (hx : x ∈ commonLocus U φ j ψ k) :
    ((-(k : ℝ) : ℝ) : EReal) < ψ x := by
  simpa using hx.2.2 j

theorem commonLocus_mono : Monotone (commonLocus U φ j ψ) := fun _ _ hkl =>
  inter_subset_inter (BedfordTaylorTopDegree.strictLocus_mono U φ hkl)
    (BedfordTaylorTopDegree.strictLocus_mono U _ hkl)

theorem plurisubharmonicOn_update (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    {f : (ComplexModel n) → EReal} (hf : PlurisubharmonicOn f U) (i : Fin p) :
    PlurisubharmonicOn (Function.update φ j f i) U := by
  by_cases hij : i = j
  · subst hij
    simpa using hf
  · simpa [Function.update_of_ne hij] using hφ i

theorem plurisubharmonicOn_comboTuple (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hψ : PlurisubharmonicOn ψ U) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (i : Fin p) :
    PlurisubharmonicOn (comboTuple φ j a b ψ i) U :=
  plurisubharmonicOn_update hφ (((hφ j).const_mul ha).add (hψ.const_mul hb)) i

theorem measurableSet_commonLocus (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hψ : PlurisubharmonicOn ψ U) (k : ℕ) : MeasurableSet (commonLocus U φ j ψ k) :=
  (BedfordTaylorTopDegree.measurableSet_strictLocus hφ k).inter
    (BedfordTaylorTopDegree.measurableSet_strictLocus (plurisubharmonicOn_update hφ hψ) k)

/-- The strict loci `O_k` are plurifine open (`def:pftopologydomain`). -/
theorem isOpen_plurifine_strictLocus {φ : Fin p → (ComplexModel n) → EReal}
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U) (k : ℕ) :
    IsOpen[SGPT.PSH.domainPlurifineTopology U]
      (Subtype.val ⁻¹' BedfordTaylorTopDegree.strictLocus U φ k) := by
  have e : (Subtype.val ⁻¹' BedfordTaylorTopDegree.strictLocus U φ k : Set U) =
      ⋂ i, {z : U | (((-(k : ℝ)) : ℝ) : EReal) < φ i z.val} := by
    ext z
    simp [BedfordTaylorTopDegree.strictLocus]
  rw [e]
  exact @isOpen_iInter_of_finite _ _ (SGPT.PSH.domainPlurifineTopology U) _ _
    fun i => PlurifinePshTopology.isOpen_psh_superlevel (hφ i) _

theorem isOpen_plurifine_commonLocus (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hψ : PlurisubharmonicOn ψ U) (k : ℕ) :
    IsOpen[SGPT.PSH.domainPlurifineTopology U] (Subtype.val ⁻¹' commonLocus U φ j ψ k) := by
  rw [commonLocus, preimage_inter]
  exact @IsOpen.inter _ (SGPT.PSH.domainPlurifineTopology U) _ _
    (isOpen_plurifine_strictLocus hφ k)
    (isOpen_plurifine_strictLocus (plurisubharmonicOn_update hφ hψ) k)

theorem commonLocus_subset_combo (hφ : ∀ i, PlurisubharmonicOn (φ i) U) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hψ : PlurisubharmonicOn ψ U) (k : ℕ) :
    commonLocus U φ j ψ k ⊆
      BedfordTaylorTopDegree.strictLocus U (comboTuple φ j a b ψ) (comboLevel a b * k) := by
  intro x hx
  refine ⟨hx.1.1, fun i => ?_⟩
  by_cases hij : i = j
  · subst hij
    simp only [comboTuple, Function.update_self]
    exact neg_comboLevel_lt_combo ha hb (hx.1.2 i)
      (ne_top_of_plurisubharmonicOn (hφ i) hx.1.1) (lt_of_mem_commonLocus hx)
      (ne_top_of_plurisubharmonicOn hψ hx.1.1)
  · simp only [comboTuple, Function.update_of_ne hij]
    exact neg_lt_of_le (le_comboLevel_mul a b k) (hx.1.2 i)

/-- On `E_k` the truncated potentials of the combination are the combination of the
truncations. -/
theorem truncationReal_comboTuple_eqOn (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hψ : PlurisubharmonicOn ψ U) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (k : ℕ) (i : Fin p) :
    EqOn (truncationReal (comboTuple φ j a b ψ i) (comboLevel a b * k))
      (Function.update (fun i => truncationReal (φ i) k) j
        (fun z => a * truncationReal (φ j) k z + b * truncationReal ψ k z) i)
      (commonLocus U φ j ψ k) := by
  intro x hx
  by_cases hij : i = j
  · subst hij
    simp only [comboTuple, Function.update_self]
    exact truncationReal_combo ha hb (hx.1.2 i) (ne_top_of_plurisubharmonicOn (hφ i) hx.1.1)
      (lt_of_mem_commonLocus hx) (ne_top_of_plurisubharmonicOn hψ hx.1.1)
  · simp only [comboTuple, Function.update_of_ne hij]
    exact truncationReal_mono_level (le_comboLevel_mul a b k) (hx.1.2 i)

theorem update_truncationReal (φ : Fin p → (ComplexModel n) → EReal) (j : Fin p)
    (ψ : (ComplexModel n) → EReal) (k : ℕ) :
    Function.update (fun i => truncationReal (φ i) k) j (truncationReal ψ k) =
      fun i => truncationReal (Function.update φ j ψ i) k := by
  funext i
  by_cases hij : i = j
  · subst hij
    simp
  · simp [Function.update_of_ne hij]

theorem exists_mem_commonLocus {x : (ComplexModel n)} (hxU : x ∈ U) (hfin : ∀ i, φ i x ≠ ⊥)
    (hψx : ψ x ≠ ⊥) : ∃ k, x ∈ commonLocus U φ j ψ k := by
  choose k hk using fun i => exists_nat_neg_lt (hfin i)
  obtain ⟨l, hl⟩ := exists_nat_neg_lt hψx
  have hle : ∀ i, k i ≤ ∑ i, k i + l := fun i =>
    le_add_right (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  refine ⟨∑ i, k i + l, ⟨hxU, fun i => neg_lt_of_le (hle i) (hk i)⟩, hxU, fun i => ?_⟩
  by_cases hij : i = j
  · subst hij
    simp only [Function.update_self]
    exact neg_lt_of_le (le_add_left le_rfl) hl
  · simp only [Function.update_of_ne hij]
    exact neg_lt_of_le (hle i) (hk i)

theorem locallyPluripolarOn_poles {u : (ComplexModel n) → EReal} (hu : PlurisubharmonicOn u U)
    (hnd : LocallyNondegenerate fun x : U => u x) : LocallyPluripolarOn {x | u x = ⊥} U := by
  intro x hx
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp U.isOpen x hx
  have hW : IsOpen (Subtype.val ⁻¹' Metric.ball x r : Set U) :=
    Metric.isOpen_ball.preimage continuous_subtype_val
  have hxW : (⟨x, hx⟩ : U) ∈ (Subtype.val ⁻¹' Metric.ball x r : Set U) :=
    Set.mem_preimage.mpr (Metric.mem_ball_self hr)
  obtain ⟨y, hy, hne⟩ := hnd ⟨x, hx⟩ _ hW hxW
  refine ⟨Metric.ball x r, u, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball x r).isPreconnected, ?_, ⟨y.1, hy, hne⟩, fun _ _ hz => hz⟩
  exact fun z hz => hu z (hball hz)

end Common

/-! ### The local multilinearity -/

section Product

variable {p q : ℕ} (hqp : q + p = n) {U : Opens (ComplexModel n)} {φ : Fin p → (ComplexModel n)
    → EReal} {j : Fin p}
  {ψ : (ComplexModel n) → EReal} {a b : ℝ}

/-- **The key identity on `E_k`**:
`1_{E_k} B_{Nk}(φ^{ab}) = a 1_{E_k} B_k(φ) + b 1_{E_k} B_k(φ^ψ)`. -/
theorem mulBorel_truncatedBT_combo (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hψ : PlurisubharmonicOn ψ U) (ha : 0 < a) (hb : 0 < b) (k : ℕ) :
    mulBorel (truncatedBT hqp U (comboTuple φ j a b ψ) (comboLevel a b * k))
        ((commonLocus U φ j ψ k).indicator fun _ => (1 : ℝ)) =
      a • mulBorel (truncatedBT hqp U φ k) ((commonLocus U φ j ψ k).indicator fun _ => (1 : ℝ)) +
        b • mulBorel (truncatedBT hqp U (Function.update φ j ψ) k)
          ((commonLocus U φ j ψ k).indicator fun _ => (1 : ℝ)) := by
  have hcm := measurableSet_commonLocus hφ hψ (j := j) k
  have htr := fun i => truncationReal_isLocallyBoundedPshOn (hφ i) k
  have hψtr := truncationReal_isLocallyBoundedPshOn hψ k
  have hc := plurisubharmonicOn_comboTuple hφ hψ (j := j) ha hb
  have hw : ∀ i, IsLocallyBoundedPshOn U (Function.update (fun i => truncationReal (φ i) k) j
      (fun z => a * truncationReal (φ j) k z + b * truncationReal ψ k z) i) := by
    intro i
    by_cases hij : i = j
    · subst hij
      simp only [Function.update_self]
      exact LocalBedfordTaylorCalculus.isLocallyBoundedPshOn_add
        (isLocallyBoundedPshOn_const_mul (htr i) ha) (isLocallyBoundedPshOn_const_mul hψtr hb)
    · simpa [Function.update_of_ne hij] using htr i
  unfold truncatedBT
  rw [mulBorel_btProduct_eq_of_eqOn_plurifineOpen hqp
      (fun i => truncationReal_isLocallyBoundedPshOn (hc i) _) hw (commonLocus_subset k) hcm
      (isOpen_plurifine_commonLocus hφ hψ k)
      (fun i => truncationReal_comboTuple_eqOn hφ hψ ha hb k i),
    btProduct_update_combo p q (oneCurrentOf (U := U) hqp) (isPositive_oneCurrentOf hqp)
      (isClosedAny_oneCurrentOf hqp) _ htr j (htr j) hψtr ha hb,
    Function.update_eq_self, update_truncationReal]
  exact mulBorel_smul_add_smul (isPositive_truncatedBT hqp hφ k).1
    (isPositive_truncatedBT hqp (plurisubharmonicOn_update hφ hψ) k).1 ha.le hb.le
    (measurable_const.indicator hcm) (isLocallyBoundedOn_indicator_one _)

end Product

/-! ### Glued measures of truncation families -/

section GlueMeasure

variable {U : Opens (ComplexModel n)} {q : ℕ} {B : ℕ → LocalProductCurrent n U q} {O : ℕ → Set
    (ComplexModel n)}

/-- Consistency of a truncation family on the level of trace measures:
`σ_{B_m}|_{O_j} = σ_{B_j}|_{O_j}` for `j ≤ m`. -/
theorem IsTruncationFamily.traceMeasure_restrict_consistent (hF : IsTruncationFamily B O)
    {j m : ℕ} (hjm : j ≤ m) :
    (hF.isPositive m).traceMeasure.restrict (O j) =
      (hF.isPositive j).traceMeasure.restrict (O j) := by
  rw [← traceMeasure_mulBorel_indicator (hF.isPositive m) (hF.measurableSet j),
    ← traceMeasure_mulBorel_indicator (hF.isPositive j) (hF.measurableSet j)]
  exact IsPositive.traceMeasure_congr _ _ (hF.consistent hjm)

/-- **On `O_m` the glued measure is the trace measure of `B_m`.** -/
theorem IsTruncationFamily.glueMeasure_eq_traceMeasure (hF : IsTruncationFamily B O) {m : ℕ}
    {s : Set (ComplexModel n)} (hs : MeasurableSet s) (hsO : s ⊆ O m) :
    hF.glueMeasure s = (hF.isPositive m).traceMeasure s := by
  have hlay := measurableSet_layer hF.measurableSet
  have hterm : ∀ j, (hF.isPositive j).traceMeasure (s ∩ layer O j) =
      (hF.isPositive m).traceMeasure (s ∩ layer O j) := by
    intro j
    by_cases hj : j ≤ m
    · have hsub : s ∩ layer O j ⊆ O j := inter_subset_right.trans (layer_subset j)
      rw [← Measure.restrict_eq_self (μ := (hF.isPositive j).traceMeasure) hsub,
        ← Measure.restrict_eq_self (μ := (hF.isPositive m).traceMeasure) hsub,
        hF.traceMeasure_restrict_consistent hj]
    · have he : s ∩ layer O j = ∅ := by
        ext x
        simp only [mem_inter_iff, mem_empty_iff_false, iff_false, not_and]
        exact fun hx hxl => hxl.2 m (lt_of_not_ge hj) (hsO hx)
      rw [he, measure_empty, measure_empty]
  rw [hF.glueMeasure_apply hs]
  simp_rw [hterm]
  rw [← measure_iUnion (fun i k hik => (disjoint_layer hik).mono inter_subset_right
      inter_subset_right) fun j => hs.inter (hlay j)]
  congr 1
  ext x
  simp only [mem_iUnion, mem_inter_iff]
  constructor
  · rintro ⟨_, hx, _⟩
    exact hx
  · intro hx
    obtain ⟨j, -, hj⟩ := exists_mem_layer (hsO hx)
    exact ⟨j, hx, hj⟩

/-- The glued measure does not charge the locally pluripolar subsets that none of the `B_k`
charges. -/
theorem IsTruncationFamily.glueMeasure_inter_eq_zero (hF : IsTruncationFamily B O)
    {s : Set (ComplexModel n)}
    (hs : ∀ k, DoesNotChargePluripolarOn (hF.isPositive k).traceMeasure (U : Set (ComplexModel n)))
    (hsp : LocallyPluripolarOn s U) : hF.glueMeasure (s ∩ U) = 0 :=
  hF.glueMeasure_eq_zero fun k => hs k s hsp

end GlueMeasure

/-! ### Additivity of the limit measures and of the products -/

section Additivity

variable {p q : ℕ} (hqp : q + p = n) {U : Opens (ComplexModel n)} {φ : Fin p → (ComplexModel n)
    → EReal} {j : Fin p}
  {ψ : (ComplexModel n) → EReal} {a b : ℝ}

theorem doesNotChargePluripolarOn_truncatedBT {φ : Fin p → (ComplexModel n) → EReal}
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U) (k : ℕ) :
    DoesNotChargePluripolarOn ((isTruncationFamily hqp hφ).isPositive k).traceMeasure
      (U : Set (ComplexModel n)) :=
  doesNotChargePluripolarOn_btProduct hqp fun i => truncationReal_isLocallyBoundedPshOn (hφ i) k

/-- The trace measures of the three truncations on `E_k`. -/
theorem traceMeasure_truncatedBT_combo_inter (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hψ : PlurisubharmonicOn ψ U) (ha : 0 < a) (hb : 0 < b) (k : ℕ) {s : Set (ComplexModel n)}
    (hs : MeasurableSet s) :
    ((isTruncationFamily hqp (plurisubharmonicOn_comboTuple hφ hψ (j := j) ha hb)).isPositive
        (comboLevel a b * k)).traceMeasure (s ∩ commonLocus U φ j ψ k) =
      ENNReal.ofReal a * ((isTruncationFamily hqp hφ).isPositive k).traceMeasure
          (s ∩ commonLocus U φ j ψ k) +
        ENNReal.ofReal b * ((isTruncationFamily hqp
          (plurisubharmonicOn_update hφ hψ (j := j))).isPositive k).traceMeasure
            (s ∩ commonLocus U φ j ψ k) := by
  have hcm := measurableSet_commonLocus hφ hψ (j := j) k
  have hC := (isTruncationFamily hqp (plurisubharmonicOn_comboTuple hφ hψ (j := j)
    ha hb)).isPositive
    (comboLevel a b * k)
  have hX := (isTruncationFamily hqp hφ).isPositive k
  have hY := (isTruncationFamily hqp (plurisubharmonicOn_update hφ hψ (j := j))).isPositive k
  have hCA := isPositive_mulBorel_indicator hC hcm
  have hXA := isPositive_mulBorel_indicator hX hcm
  have hYA := isPositive_mulBorel_indicator hY hcm
  have hsum := (hXA.smul ha.le).add (hYA.smul hb.le)
  rw [← traceMeasure_mulBorel_indicator_apply hC hcm hCA hs,
    IsPositive.traceMeasure_congr hCA hsum (mulBorel_truncatedBT_combo hqp hφ hψ ha hb k),
    traceMeasure_smul_add_smul hXA hYA ha.le hb.le hsum, add_apply, smul_apply,
    smul_apply, smul_eq_mul, smul_eq_mul,
    traceMeasure_mulBorel_indicator_apply hX hcm hXA hs,
    traceMeasure_mulBorel_indicator_apply hY hcm hYA hs]

theorem ne_bot_left_of_combo {u w : EReal} (ha : 0 < a) {c : EReal}
    (h : c < (a : EReal) * u + (b : EReal) * w) : u ≠ ⊥ := by
  rintro rfl
  rw [EReal.coe_mul_bot_of_pos ha, EReal.bot_add] at h
  exact not_lt_bot h

theorem ne_bot_right_of_combo {u w : EReal} (hb : 0 < b) {c : EReal}
    (h : c < (a : EReal) * u + (b : EReal) * w) : w ≠ ⊥ := by
  rintro rfl
  rw [EReal.coe_mul_bot_of_pos hb, EReal.add_bot] at h
  exact not_lt_bot h

/-- The limit measure of `φ^{ab}` is carried by `⋃ₖ E_k`. -/
theorem ae_glueMeasure_comboTuple (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hψ : PlurisubharmonicOn ψ U) (ha : 0 < a) (hb : 0 < b) :
    ∀ᵐ x ∂(isTruncationFamily hqp (plurisubharmonicOn_comboTuple hφ hψ (j := j)
      ha hb)).glueMeasure,
      x ∈ ⋃ k, commonLocus U φ j ψ k := by
  filter_upwards [(isTruncationFamily hqp
    (plurisubharmonicOn_comboTuple hφ hψ (j := j) ha hb)).ae_glueMeasure_mem] with x hx
  obtain ⟨m, hxU, hm⟩ := hx
  have hj := hm j
  simp only [comboTuple, Function.update_self] at hj
  refine mem_iUnion.mpr (exists_mem_commonLocus hxU (fun i => ?_) (ne_bot_right_of_combo hb hj))
  by_cases hij : i = j
  · subst hij
    exact ne_bot_left_of_combo ha hj
  · have hi := hm i
    simp only [comboTuple, Function.update_of_ne hij] at hi
    exact ne_bot_of_gt hi

/-- The limit measure of `φ` is carried by `⋃ₖ E_k` when `ψ` is nondegenerate. -/
theorem ae_glueMeasure_left (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hψ : PlurisubharmonicOn ψ U) (hψnd : LocallyNondegenerate fun x : U => ψ x) :
    ∀ᵐ x ∂(isTruncationFamily hqp hφ).glueMeasure, x ∈ ⋃ k, commonLocus U φ j ψ k := by
  have h0 := (isTruncationFamily hqp hφ).glueMeasure_inter_eq_zero
    (doesNotChargePluripolarOn_truncatedBT hqp hφ) (locallyPluripolarOn_poles hψ hψnd)
  filter_upwards [(isTruncationFamily hqp hφ).ae_glueMeasure_mem,
    measure_eq_zero_iff_ae_notMem.mp h0] with x hx hx0
  obtain ⟨m, hxU, hm⟩ := hx
  exact mem_iUnion.mpr (exists_mem_commonLocus hxU (fun i => ne_bot_of_gt (hm i))
    fun h => hx0 ⟨h, hxU⟩)

/-- The limit measure of `φ^ψ` is carried by `⋃ₖ E_k` when `φ_j` is nondegenerate. -/
theorem ae_glueMeasure_right (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hψ : PlurisubharmonicOn ψ U) (hφnd : LocallyNondegenerate fun x : U => φ j x) :
    ∀ᵐ x ∂(isTruncationFamily hqp (plurisubharmonicOn_update hφ hψ (j := j))).glueMeasure,
      x ∈ ⋃ k, commonLocus U φ j ψ k := by
  have hF := isTruncationFamily hqp (plurisubharmonicOn_update hφ hψ (j := j))
  have h0 := hF.glueMeasure_inter_eq_zero
    (doesNotChargePluripolarOn_truncatedBT hqp (plurisubharmonicOn_update hφ hψ))
    (locallyPluripolarOn_poles (hφ j) hφnd)
  filter_upwards [hF.ae_glueMeasure_mem, measure_eq_zero_iff_ae_notMem.mp h0] with x hx hx0
  obtain ⟨m, hxU, hm⟩ := hx
  have hψx : ψ x ≠ ⊥ := by
    have := hm j
    simp only [Function.update_self] at this
    exact ne_bot_of_gt this
  refine mem_iUnion.mpr (exists_mem_commonLocus hxU (fun i => ?_) hψx)
  by_cases hij : i = j
  · subst hij
    exact fun h => hx0 ⟨h, hxU⟩
  · have hi := hm i
    simp only [Function.update_of_ne hij] at hi
    exact ne_bot_of_gt hi

/-- **The limit measures are additive** (FPT `prop:nonpluripolar-local-calculus`, "Before local
finiteness is known we argue with trace measures"): `μ(φ^{ab}) = a μ(φ) + b μ(φ^ψ)`, where
`μ(·)` is the increasing limit of the trace measures of the truncated products (possibly infinite
on compact sets). -/
theorem glueMeasure_combo (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hψ : PlurisubharmonicOn ψ U) (hφnd : LocallyNondegenerate fun x : U => φ j x)
    (hψnd : LocallyNondegenerate fun x : U => ψ x) (ha : 0 < a) (hb : 0 < b) :
    (isTruncationFamily hqp (plurisubharmonicOn_comboTuple hφ hψ (j := j) ha hb)).glueMeasure =
      ENNReal.ofReal a • (isTruncationFamily hqp hφ).glueMeasure +
        ENNReal.ofReal b • (isTruncationFamily hqp (plurisubharmonicOn_update hφ hψ (j :=
          j))).glueMeasure := by
  set hFc := isTruncationFamily hqp (plurisubharmonicOn_comboTuple hφ hψ (j := j) ha hb)
  set hFφ := isTruncationFamily hqp hφ
  set hFψ := isTruncationFamily hqp (plurisubharmonicOn_update hφ hψ (j := j))
  have hcm := measurableSet_commonLocus hφ hψ (j := j)
  have hrestr : ∀ k, hFc.glueMeasure.restrict (commonLocus U φ j ψ k) =
      (ENNReal.ofReal a • hFφ.glueMeasure + ENNReal.ofReal b • hFψ.glueMeasure).restrict
        (commonLocus U φ j ψ k) := by
    intro k
    ext s hs
    rw [Measure.restrict_apply hs, Measure.restrict_apply hs, add_apply,
      smul_apply, smul_apply, smul_eq_mul, smul_eq_mul,
      hFc.glueMeasure_eq_traceMeasure (m := comboLevel a b * k) (hs.inter (hcm k))
        (inter_subset_right.trans (commonLocus_subset_combo hφ ha hb hψ k)),
      hFφ.glueMeasure_eq_traceMeasure (m := k) (hs.inter (hcm k))
        (inter_subset_right.trans (commonLocus_subset_left k)),
      hFψ.glueMeasure_eq_traceMeasure (m := k) (hs.inter (hcm k))
        (inter_subset_right.trans (commonLocus_subset_right k))]
    exact traceMeasure_truncatedBT_combo_inter hqp hφ hψ ha hb k hs
  have hsum : ∀ᵐ x ∂(ENNReal.ofReal a • hFφ.glueMeasure + ENNReal.ofReal b • hFψ.glueMeasure),
      x ∈ ⋃ k, commonLocus U φ j ψ k :=
    ae_add_measure_iff.mpr ⟨Measure.ae_smul_measure (ae_glueMeasure_left hqp hφ hψ hψnd) _,
      Measure.ae_smul_measure (ae_glueMeasure_right hqp hφ hψ hφnd) _⟩
  rw [← Measure.restrict_eq_self_of_ae_mem (ae_glueMeasure_comboTuple hqp hφ hψ ha hb),
    ← Measure.restrict_eq_self_of_ae_mem hsum]
  exact Measure.restrict_iUnion_congr.mpr hrestr

/-- **`prop:npp1` (6), well-definedness** (local form): for psh `φ₁, …, φ_p, ψ` on `U` with `φ_j`
and `ψ` nondegenerate and `a, b > 0`, `dd^c(a φ_j + b ψ) ∧ ⋀_{i ≠ j} dd^c φ_i` is well defined iff
both `⋀ dd^c φ_i` and `dd^c ψ ∧ ⋀_{i ≠ j} dd^c φ_i` are. -/
theorem isWellDefinedOn_combo_iff (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hψ : PlurisubharmonicOn ψ U) (hφnd : LocallyNondegenerate fun x : U => φ j x)
    (hψnd : LocallyNondegenerate fun x : U => ψ x) (ha : 0 < a) (hb : 0 < b) :
    IsWellDefinedOn hqp U (comboTuple φ j a b ψ) ↔
      IsWellDefinedOn hqp U φ ∧ IsWellDefinedOn hqp U (Function.update φ j ψ) := by
  rw [isWellDefinedOn_iff hqp (plurisubharmonicOn_comboTuple hφ hψ ha hb),
    isWellDefinedOn_iff hqp hφ, isWellDefinedOn_iff hqp (plurisubharmonicOn_update hφ hψ)]
  simp only [IsTruncationFamily.HasLocallyFiniteMass]
  rw [glueMeasure_combo hqp hφ hψ hφnd hψnd ha hb]
  have ha0 : ENNReal.ofReal a ≠ 0 := ENNReal.ofReal_pos.mpr ha |>.ne'
  have hb0 : ENNReal.ofReal b ≠ 0 := ENNReal.ofReal_pos.mpr hb |>.ne'
  constructor
  · intro h
    refine ⟨fun K hK hKU => ?_, fun K hK hKU => ?_⟩
    · have h1 := h K hK hKU
      rw [add_apply, smul_apply, smul_apply, smul_eq_mul,
        smul_eq_mul] at h1
      exact ENNReal.lt_top_of_mul_ne_top_right (ENNReal.add_lt_top.mp h1).1.ne ha0
    · have h1 := h K hK hKU
      rw [add_apply, smul_apply, smul_apply, smul_eq_mul,
        smul_eq_mul] at h1
      exact ENNReal.lt_top_of_mul_ne_top_right (ENNReal.add_lt_top.mp h1).2.ne hb0
  · rintro ⟨h1, h2⟩ K hK hKU
    rw [add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul]
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top (h1 K hK hKU),
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top (h2 K hK hKU)⟩

/-- On a Borel subset `A` of `O_m`, the product agrees with the level-`m` truncation:
`1_A ⟨⋯⟩ = 1_A ⋀ⱼ dd^c (φⱼ ∨ (-m))`. -/
theorem mulBorel_nonPluripolarProduct_of_subset {φ : Fin p → (ComplexModel n) → EReal}
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U) (hW : IsWellDefinedOn hqp U φ) {m : ℕ} {A : Set
      (ComplexModel n)}
    (hAm : MeasurableSet A) (hAO : A ⊆ BedfordTaylorTopDegree.strictLocus U φ m) :
    mulBorel (nonPluripolarProduct hqp U φ) (A.indicator fun _ => (1 : ℝ)) =
      mulBorel (truncatedBT hqp U φ m) (A.indicator fun _ => (1 : ℝ)) := by
  have hOm := BedfordTaylorTopDegree.measurableSet_strictLocus hφ m
  have e : BedfordTaylorTopDegree.strictLocus U φ m ∩ A = A := inter_eq_right.mpr hAO
  calc mulBorel (nonPluripolarProduct hqp U φ) (A.indicator fun _ => (1 : ℝ)) =
        mulBorel (mulBorel (nonPluripolarProduct hqp U φ)
          ((BedfordTaylorTopDegree.strictLocus U φ m).indicator fun _ => (1 : ℝ)))
          (A.indicator fun _ => (1 : ℝ)) := by
        rw [mulBorel_indicator_indicator (isPositive_nonPluripolarProduct hqp hφ hW) hOm hAm, e]
    _ = mulBorel (mulBorel (truncatedBT hqp U φ m)
          ((BedfordTaylorTopDegree.strictLocus U φ m).indicator fun _ => (1 : ℝ)))
          (A.indicator fun _ => (1 : ℝ)) := by
        rw [mulBorel_nonPluripolarProduct_strictLocus hqp hφ hW m]
        rfl
    _ = mulBorel (truncatedBT hqp U φ m) (A.indicator fun _ => (1 : ℝ)) := by
        rw [mulBorel_indicator_indicator (isPositive_truncatedBT hqp hφ m).1 hOm hAm, e]

/-- The trace measure of the non-pluripolar product is the glued measure. -/
theorem traceMeasure_nonPluripolarProduct {φ : Fin p → (ComplexModel n) → EReal}
    (hφ : ∀ i, PlurisubharmonicOn (φ i) U) (hW : IsWellDefinedOn hqp U φ) :
    (isPositive_nonPluripolarProduct hqp hφ hW).traceMeasure =
      (isTruncationFamily hqp hφ).glueMeasure := by
  have hm := (isWellDefinedOn_iff hqp hφ).mp hW
  rw [IsPositive.traceMeasure_congr _ ((isTruncationFamily hqp hφ).isPositive_glue hm)
    (nonPluripolarProduct_eq hqp hφ), (isTruncationFamily hqp hφ).traceMeasure_glue hm]

/-- **`prop:npp1` (6), `eq:ppp6`** (local form): when the products are well defined,
`⟨dd^c(a φ_j + b ψ) ∧ ⋀_{i ≠ j} dd^c φ_i⟩ = a ⟨⋀ dd^c φ_i⟩ + b ⟨dd^c ψ ∧ ⋀_{i ≠ j} dd^c φ_i⟩`. -/
theorem nonPluripolarProduct_combo (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hψ : PlurisubharmonicOn ψ U) (hφnd : LocallyNondegenerate fun x : U => φ j x)
    (hψnd : LocallyNondegenerate fun x : U => ψ x) (ha : 0 < a) (hb : 0 < b)
    (hW : IsWellDefinedOn hqp U φ) (hWψ : IsWellDefinedOn hqp U (Function.update φ j ψ)) :
    nonPluripolarProduct hqp U (comboTuple φ j a b ψ) =
      a • nonPluripolarProduct hqp U φ + b • nonPluripolarProduct hqp U (Function.update φ j ψ)
        := by
  have hc := plurisubharmonicOn_comboTuple hφ hψ (j := j) ha hb
  have hφψ := plurisubharmonicOn_update hφ hψ (j := j)
  have hWc := (isWellDefinedOn_combo_iff hqp hφ hψ hφnd hψnd ha hb).mpr ⟨hW, hWψ⟩
  have hcm := measurableSet_commonLocus hφ hψ (j := j)
  have hS := isPositive_nonPluripolarProduct hqp hc hWc
  have hX := isPositive_nonPluripolarProduct hqp hφ hW
  have hY := isPositive_nonPluripolarProduct hqp hφψ hWψ
  have hS' := (hX.smul ha.le).add (hY.smul hb.le)
  refine eq_of_mulBorel_indicator_eq hS hS' hcm commonLocus_mono (fun k => ?_) ?_ ?_
  · rw [mulBorel_nonPluripolarProduct_of_subset hqp hc hWc (hcm k)
        (commonLocus_subset_combo hφ ha hb hψ k),
      mulBorel_truncatedBT_combo hqp hφ hψ ha hb k,
      mulBorel_smul_add_smul hX hY ha.le hb.le (measurable_const.indicator (hcm k))
        (isLocallyBoundedOn_indicator_one _),
      mulBorel_nonPluripolarProduct_of_subset hqp hφ hW (hcm k) (commonLocus_subset_left k),
      mulBorel_nonPluripolarProduct_of_subset hqp hφψ hWψ (hcm k) (commonLocus_subset_right k)]
  · rw [traceMeasure_nonPluripolarProduct hqp hc hWc]
    filter_upwards [ae_glueMeasure_comboTuple hqp hφ hψ (j := j) ha hb] with x hx
    exact mem_iUnion.mp hx
  · rw [traceMeasure_smul_add_smul hX hY ha.le hb.le hS', traceMeasure_nonPluripolarProduct hqp hφ
    hW,
      traceMeasure_nonPluripolarProduct hqp hφψ hWψ]
    filter_upwards [ae_add_measure_iff.mpr ⟨Measure.ae_smul_measure (ae_glueMeasure_left hqp hφ hψ
      hψnd) _,
      Measure.ae_smul_measure (ae_glueMeasure_right hqp hφ hψ hφnd) _⟩] with x hx
    exact mem_iUnion.mp hx

end Additivity

end SGPT.NPP.NonPluripolarCurrent

/-! ### Multilinearity on a complex manifold -/

namespace SGPT.NPP

open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.NPP.NonPluripolarCurrent

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel n) M]
  [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M]

theorem ereal_combo_ne_bot {u w : EReal} (hu : u ≠ ⊤ ∧ u ≠ ⊥) (hw : w ≠ ⊤ ∧ w ≠ ⊥) (a b : ℝ) :
    (a : EReal) * u + (b : EReal) * w ≠ ⊥ := by
  rw [← EReal.coe_toReal hu.1 hu.2, ← EReal.coe_toReal hw.1 hw.2]
  exact_mod_cast EReal.coe_ne_bot _

/-- **Positive combinations of psh functions on a manifold are psh** (`def:pshmfd`). -/
theorem manifoldPSH_combo {u w : M → EReal} (hu : SGPT.PSH.ManifoldPSH (n := n) u)
    (hw : SGPT.PSH.ManifoldPSH (n := n) w) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    SGPT.PSH.ManifoldPSH (n := n) fun x => (a : EReal) * u x + (b : EReal) * w x := by
  intro x
  obtain ⟨e, hxe, V, hV, hVc, hVe, hxV, hpu⟩ := hu x
  have hwV : PlurisubharmonicOn (chartFunction w e) V := fun z hz =>
    hw.chartPlurisubharmonic e z (hVe hz)
  have hopen : IsOpen (e.val.source ∩ e.val ⁻¹' V) :=
    e.val.continuousOn.isOpen_inter_preimage e.val.open_source hV
  obtain ⟨y, ⟨hye, hyV⟩, hwy⟩ := hw.locallyNondegenerate x _ hopen ⟨hxe, hxV⟩
  have hwne : ∃ z ∈ V, chartFunction w e z ≠ ⊥ :=
    ⟨e.val y, hyV, by simpa [chartFunction, e.val.left_inv hye] using hwy⟩
  have huae := (hpu.disc.plurisubharmonicOn hV).ae_finite MeasureTheory.volume
    hVc.isPreconnected hpu.nontrivial
  have hwae := hwV.ae_finite MeasureTheory.volume hVc.isPreconnected hwne
  obtain ⟨z, hz, huz, hwz⟩ := MeasureTheory.Measure.exists_mem_of_measure_ne_zero_of_ae
    (hV.measure_pos MeasureTheory.volume ⟨_, hxV⟩).ne' (huae.and hwae)
  exact ⟨e, hxe, V, hV, hVc, hVe, hxV,
    ⟨(hpu.disc.const_mul ha).add (hwV.discPshOn.const_mul hb), z, hz,
      ereal_combo_ne_bot huz hwz a b⟩⟩

omit [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M] in
theorem manifoldPSH_update {p : ℕ} {φ : Fin p → M → EReal}
    (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i)) (j : Fin p) {f : M → EReal}
    (hf : SGPT.PSH.ManifoldPSH (n := n) f) (i : Fin p) :
    SGPT.PSH.ManifoldPSH (n := n) (Function.update φ j f i) := by
  by_cases hij : i = j
  · subst hij
    simpa using hf
  · simpa [Function.update_of_ne hij] using hφ i

omit [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M] in
/-- The coordinate expression of a tuple with a replaced slot. -/
theorem chart_update {p : ℕ} (φ : Fin p → M → EReal) (j : Fin p) (f : M → EReal)
    (e : ComplexChart n M) :
    (fun i z => Function.update φ j f i (e.val.symm z)) =
      Function.update (fun i z => φ i (e.val.symm z)) j (fun z => f (e.val.symm z)) := by
  funext i z
  by_cases hij : i = j
  · subst hij
    simp
  · simp [Function.update_of_ne hij]

omit [IsManifold (𝓘(ℂ, ComplexModel n)) ∞ M] in
/-- The coordinate expressions of a nondegenerate function are nondegenerate. -/
theorem locallyNondegenerate_chart {u : M → EReal} (hu : LocallyNondegenerate u)
    (e : ComplexChart n M) :
    LocallyNondegenerate fun z : chartTarget e => u (e.val.symm z) := by
  intro z W hW hzW
  obtain ⟨W', hW', rfl⟩ := isOpen_induced_iff.mp hW
  have hopen : IsOpen (e.val.source ∩ e.val ⁻¹' W') :=
    e.val.continuousOn.isOpen_inter_preimage e.val.open_source hW'
  have hz : (z : ComplexModel n) ∈ e.val.target := z.2
  obtain ⟨y, ⟨hye, hyW⟩, hy⟩ := hu (e.val.symm z) _ hopen
    ⟨e.val.map_target hz, by simpa [e.val.right_inv hz] using hzW⟩
  exact ⟨⟨e.val y, e.val.map_source hye⟩, hyW, by simpa [e.val.left_inv hye] using hy⟩

variable {p q : ℕ} (hqp : q + p = n)

/-- **`prop:npp1` (6) on a complex manifold, well-definedness**: for psh `φ₁, …, φ_p, ψ` on `M`
(`def:pshmfd`) and `a, b > 0`, `dd^c(a φ_j + b ψ) ∧ ⋀_{i ≠ j} dd^c φ_i` is well defined iff
`⋀ dd^c φ_i` and `dd^c ψ ∧ ⋀_{i ≠ j} dd^c φ_i` are. -/
theorem isNonPluripolarWellDefined_combo_iff {φ : Fin p → M → EReal} {ψ : M → EReal}
    (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i)) (hψ : SGPT.PSH.ManifoldPSH (n := n) ψ)
    (j : Fin p) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    IsNonPluripolarWellDefined hqp
        (Function.update φ j fun x => (a : EReal) * φ j x + (b : EReal) * ψ x) ↔
      IsNonPluripolarWellDefined hqp φ ∧
        IsNonPluripolarWellDefined hqp (Function.update φ j ψ) := by
  unfold IsNonPluripolarWellDefined
  rw [← forall_and]
  refine forall_congr' fun e => ?_
  rw [chart_update, chart_update]
  exact isWellDefinedOn_combo_iff hqp (chartPlurisubharmonicOn hφ e)
    ((hψ.chartPlurisubharmonic e)) (locallyNondegenerate_chart (hφ j).locallyNondegenerate e)
    (locallyNondegenerate_chart hψ.locallyNondegenerate e) ha hb

/-- **`prop:npp1` (6) on a complex manifold, `eq:ppp6`**: in every chart,
`⟨dd^c(a φ_j + b ψ) ∧ ⋀_{i ≠ j} dd^c φ_i⟩ = a ⟨⋀ dd^c φ_i⟩ + b ⟨dd^c ψ ∧ ⋀_{i ≠ j} dd^c φ_i⟩`
(currents on `M` are determined by their chart expressions). -/
theorem nonPluripolarProduct_combo_inChart {φ : Fin p → M → EReal} {ψ : M → EReal}
    (hφ : ∀ i, SGPT.PSH.ManifoldPSH (n := n) (φ i)) (hψ : SGPT.PSH.ManifoldPSH (n := n) ψ)
    (j : Fin p) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hW : IsNonPluripolarWellDefined hqp φ)
    (hWψ : IsNonPluripolarWellDefined hqp (Function.update φ j ψ))
    (hWc : IsNonPluripolarWellDefined hqp
      (Function.update φ j fun x => (a : EReal) * φ j x + (b : EReal) * ψ x))
    (e : ComplexChart n M) :
    (nonPluripolarProduct hqp _ (manifoldPSH_update hφ j (manifoldPSH_combo (hφ j) hψ ha hb))
        hWc).inChart e =
      a • (nonPluripolarProduct hqp φ hφ hW).inChart e +
        b • (nonPluripolarProduct hqp _ (manifoldPSH_update hφ j hψ) hWψ).inChart e := by
  simp only [nonPluripolarProduct_inChart]
  rw [chart_update, chart_update]
  have hWe := hW e
  have hWψe := hWψ e
  rw [chart_update] at hWψe
  exact NonPluripolarCurrent.nonPluripolarProduct_combo hqp (chartPlurisubharmonicOn hφ e)
    (hψ.chartPlurisubharmonic e) (locallyNondegenerate_chart (hφ j).locallyNondegenerate e)
    (locallyNondegenerate_chart hψ.locallyNondegenerate e) ha hb hWe hWψe

end SGPT.NPP
