/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.NPP.NonPluripolarClosedGlue
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorCalculus
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PshConvexCone

/-!
# Closedness of non-pluripolar products in every degree: the local theorem

Source: `chapter_npp.tex`, `prop:npp1` (5) ("`⟨dd^c φ₁ ∧ ⋯ ∧ dd^c φ_p⟩` is a closed positive
current"); Xia, *Foundations of pluripotential theory*, `thm:nonpluripolar-product-closed`
("Every locally finite non-pluripolar product is closed").

Let `U ⊆ ℂⁿ` be open, `q + p = n` and `φ₁, …, φ_p` psh on `U` with
`⟨dd^c φ₁ ∧ ⋯ ∧ dd^c φ_p⟩` well defined (`IsWellDefinedOn`, the source condition
`eq:welldefinepluri`).  Then the non-pluripolar product is closed in TN's sense
(`IsClosedAny q`, i.e. `IsClosedCurrent` for `q ≥ 1`; for `q = 0` there is nothing to prove):
`isClosedAny_nonPluripolarProduct`.

The proof is FPT's: the truncated products `B_k = ⋀ⱼ dd^c (φⱼ ∨ (-k))` are closed
(`isPositive_truncatedBT`), and the cutoffs (`hasPshCutoffs_strictLocus`)
`w_k = (1/k) max(k + ∑ⱼ (φⱼ ∨ (-k) - cⱼ), 0) = max(1 + ∑ⱼ(φⱼ ∨ (-k) - cⱼ)/k, 0)` near a compact
set `K`, with constants `cⱼ ≥ 0` bounding `φⱼ` above on a neighbourhood `V` of `K` (this replaces
FPT's normalization `uⱼ ≤ 0` after shrinking `U`), are locally bounded psh on `V`, take values
in `[0, 1]`, vanish off `O_k = {φ₁ > -k, …, φ_p > -k}` and tend to `1` on `⋃ O_k`; the abstract
theorem `IsTruncationFamily.isClosedCurrent_glue` applies.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.NPP.NonPluripolarCurrent

open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts

variable {n : ℕ}

/-! ### Closure properties of locally bounded psh functions -/

section Psh

variable {V : Opens (ComplexModel n)}

theorem isLocallyBoundedPshOn_const (V : Opens (ComplexModel n)) (c : ℝ) :
    IsLocallyBoundedPshOn V (fun _ => c) :=
  ⟨fun x _ => plurisubharmonicAt_const _ (EReal.coe_ne_top _) x,
    fun _ hz => ⟨V, hz, le_rfl, |c|, fun _ _ => le_rfl⟩⟩

theorem isLocallyBoundedPshOn_max' {f g : (ComplexModel n) → ℝ} (hf : IsLocallyBoundedPshOn V f)
    (hg : IsLocallyBoundedPshOn V g) : IsLocallyBoundedPshOn V fun z => max (f z) (g z) := by
  refine ⟨by simpa only [EReal.coe_strictMono.monotone.map_max] using hf.1.max hg.1,
    fun z hz => ?_⟩
  obtain ⟨W, hzW, hWV, C, hC⟩ := hf.2 z hz
  obtain ⟨W', hzW', hW'V, C', hC'⟩ := hg.2 z hz
  exact ⟨W ⊓ W', ⟨hzW, hzW'⟩, inf_le_left.trans hWV, max C C', fun w hw =>
    (abs_max_le_max_abs_abs).trans (max_le_max (hC w hw.1) (hC' w hw.2))⟩

theorem isLocallyBoundedPshOn_const_mul' {u : (ComplexModel n) → ℝ} (hu : IsLocallyBoundedPshOn V
    u) {c : ℝ}
    (hc : 0 < c) : IsLocallyBoundedPshOn V fun z => c * u z := by
  refine ⟨by simpa only [EReal.coe_mul] using hu.1.const_mul hc, fun z hz => ?_⟩
  obtain ⟨W, hzW, hWV, C, hC⟩ := hu.2 z hz
  exact ⟨W, hzW, hWV, c * C, fun w hw => by
    rw [abs_mul, abs_of_pos hc]
    exact mul_le_mul_of_nonneg_left (hC w hw) hc.le⟩

theorem isLocallyBoundedPshOn_finsetSum {ι : Type*} (s : Finset ι) {f : ι → (ComplexModel n) → ℝ}
    (hf : ∀ i ∈ s, IsLocallyBoundedPshOn V (f i)) :
    IsLocallyBoundedPshOn V fun z => ∑ i ∈ s, f i z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact isLocallyBoundedPshOn_const V 0
  | insert a s has ih =>
    simp only [Finset.sum_insert has]
    exact LocalBedfordTaylorCalculus.isLocallyBoundedPshOn_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem isLocallyBoundedPshOn_congr' {u u' : (ComplexModel n) → ℝ} (hu : IsLocallyBoundedPshOn V u)
    (h : EqOn u u' V) : IsLocallyBoundedPshOn V u' := by
  refine ⟨fun x hx => (hu.1 x hx).congr ?_, fun z hz => ?_⟩
  · filter_upwards [V.isOpen.mem_nhds hx] with y hy
    rw [h hy]
  · obtain ⟨W, hzW, hWV, C, hC⟩ := hu.2 z hz
    exact ⟨W, hzW, hWV, C, fun y hy => h (hWV hy) ▸ hC y hy⟩

end Psh

/-! ### The cutoffs of the truncations -/

section Cutoffs

variable {p : ℕ}

/-- The cutoff `w_k = (1/k) max(k + ∑ⱼ (φⱼ ∨ (-k) - cⱼ), 0)` (and `0` for `k = 0`). -/
def nppCutoff (φ : Fin p → (ComplexModel n) → EReal) (c : Fin p → ℝ) (k : ℕ) (x : (ComplexModel
    n)) : ℝ :=
  (k : ℝ)⁻¹ * max ((k : ℝ) + ∑ i, (truncationReal (φ i) k x - c i)) 0

variable {U : Opens (ComplexModel n)} {φ : Fin p → (ComplexModel n) → EReal}

theorem isLocallyBoundedPshOn_nppCutoff (hφ : ∀ i, PlurisubharmonicOn (φ i) U) (c : Fin p → ℝ)
    (k : ℕ) : IsLocallyBoundedPshOn U (nppCutoff φ c k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have e : nppCutoff φ c 0 = fun _ => 0 := by
      funext x
      simp [nppCutoff]
    rw [e]
    exact isLocallyBoundedPshOn_const U 0
  · have hs : IsLocallyBoundedPshOn U fun x => (k : ℝ) + ∑ i, (truncationReal (φ i) k x - c i) :=
      LocalBedfordTaylorCalculus.isLocallyBoundedPshOn_add (isLocallyBoundedPshOn_const U _)
        (isLocallyBoundedPshOn_finsetSum Finset.univ fun i _ =>
          isLocallyBoundedPshOn_congr' (LocalBedfordTaylorCalculus.isLocallyBoundedPshOn_add
            (truncationReal_isLocallyBoundedPshOn (hφ i) k) (isLocallyBoundedPshOn_const U (-c i)))
            fun x _ => by simp only [sub_eq_add_neg])
    exact isLocallyBoundedPshOn_const_mul' (isLocallyBoundedPshOn_max' hs
      (isLocallyBoundedPshOn_const U 0)) (inv_pos.mpr (Nat.cast_pos.mpr hk))

theorem truncationReal_le {u : (ComplexModel n) → EReal} (hu : PlurisubharmonicOn u U) (k : ℕ)
    {c : ℝ}
    (hc0 : 0 ≤ c) {x : (ComplexModel n)} (hxU : x ∈ U) (hx : u x ≤ (c : EReal))
      : truncationReal u k x ≤ c := by
  rw [← EReal.coe_le_coe_iff, coe_truncationReal hu k hxU]
  refine max_le hx (EReal.coe_le_coe_iff.mpr ?_)
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

theorem truncationReal_of_le {u : (ComplexModel n) → EReal} (k : ℕ) {x : (ComplexModel n)} (hx : u
    x ≤ ((-(k : ℝ) : ℝ) : EReal)) :
    truncationReal u k x = -(k : ℝ) := by
  unfold truncationReal truncation
  rw [max_eq_right hx]
  exact EReal.toReal_coe _

/-- **Psh cutoffs for the truncations of psh functions** (FPT, proof of
`thm:nonpluripolar-product-closed`, "Cutoff functions"). -/
theorem hasPshCutoffs_strictLocus (hφ : ∀ i, PlurisubharmonicOn (φ i) U) :
    HasPshCutoffs U (BedfordTaylorTopDegree.strictLocus U φ) := by
  intro K hK hKU
  obtain ⟨W, hWo, hKW, hWU, hWc⟩ := exists_open_between_and_isCompact_closure hK U.isOpen hKU
  set V : Opens (ComplexModel n) := ⟨W, hWo⟩ with hVdef
  have hVU : V ≤ U := subset_closure.trans hWU
  choose c hc0 hc using fun i => (hφ i).exists_nonnegative_compact_upper_bound hWc hWU
  have hcV : ∀ i, ∀ x ∈ V, φ i x ≤ (c i : EReal) := fun i x hx => hc i x (subset_closure hx)
  have hraw : ∀ k, IsLocallyBoundedPshOn V (nppCutoff φ c k) := fun k =>
    LocalBedfordTaylorLocality.isLocallyBoundedPshOn_mono (isLocallyBoundedPshOn_nppCutoff hφ c k)
      hVU
  have heq : ∀ k, EqOn (nppCutoff φ c k) ((V : Set (ComplexModel n)).indicator (nppCutoff φ c k))
    V :=
    fun k x hx => (Set.indicator_of_mem hx _).symm
  have hsum_le : ∀ k, ∀ x ∈ V, ∑ i, (truncationReal (φ i) k x - c i) ≤ 0 := fun k x hx =>
    Finset.sum_nonpos fun i _ => sub_nonpos.mpr
      (truncationReal_le (hφ i) k (hc0 i) (hVU hx) (hcV i x hx))
  refine ⟨V, hVU, hKW, fun k => (V : Set (ComplexModel n)).indicator (nppCutoff φ c k), fun k =>
    measurable_indicator_of_isLocallyBoundedPshOn (hraw k),
    fun k => isLocallyBoundedPshOn_congr' (hraw k) (heq k),
    fun k x hx => ?_, fun k x hx hxO => ?_, fun x hx hxO => ?_⟩
  · -- `0 ≤ w_k ≤ 1` on `V`
    dsimp only
    rw [Set.indicator_of_mem hx]
    refine ⟨mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg k)) (le_max_right _ _), ?_⟩
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [nppCutoff]
    · have hkpos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
      unfold nppCutoff
      rw [inv_mul_le_iff₀ hkpos, mul_one]
      exact max_le (by linarith [hsum_le k x hx]) hkpos.le
  · -- `w_k = 0` on `V \ O_k`
    dsimp only
    rw [Set.indicator_of_mem hx]
    have hxU : x ∈ U := hVU hx
    have : ∃ i, φ i x ≤ ((-(k : ℝ) : ℝ) : EReal) := by
      by_contra h
      push Not at h
      exact hxO ⟨hxU, h⟩
    obtain ⟨i, hi⟩ := this
    have hti := truncationReal_of_le k hi
    have hle : ∑ j, (truncationReal (φ j) k x - c j) ≤ truncationReal (φ i) k x - c i := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      have : ∑ j ∈ Finset.univ.erase i, (truncationReal (φ j) k x - c j) ≤ 0 :=
        Finset.sum_nonpos fun j _ => sub_nonpos.mpr
          (truncationReal_le (hφ j) k (hc0 j) hxU (hcV j x hx))
      linarith
    unfold nppCutoff
    rw [max_eq_right (by linarith [hc0 i]), mul_zero]
  · -- `w_k → 1` on `V ∩ ⋃ O_k`
    obtain ⟨m, hm⟩ := hxO
    have hxU : x ∈ U := hVU hx
    have hfin : ∀ i, φ i x ≠ ⊤ := fun i => (hφ i x hxU).ne_top
    set S : ℝ := ∑ i, ((φ i x).toReal - c i) with hSdef
    have htr : ∀ k, m ≤ k → ∀ i, truncationReal (φ i) k x = (φ i x).toReal := fun k hk i =>
      truncationReal_eq_on_strictLocus (Ω := U) k
        (strictTruncationLocus_mono U (φ i) hk ⟨hxU, hm.2 i⟩)
    have hev : ∀ᶠ k : ℕ in atTop, (V : Set (ComplexModel n)).indicator (nppCutoff φ c k) x =
        1 + S * (k : ℝ)⁻¹ := by
      filter_upwards [eventually_ge_atTop (m + ⌈|S|⌉₊ + 1)] with k hk
      rw [Set.indicator_of_mem hx]
      have hkm : m ≤ k := by omega
      have hkS : |S| < (k : ℝ) := by
        have h1 : |S| ≤ (⌈|S|⌉₊ : ℝ) := Nat.le_ceil _
        have h2 : ((m + ⌈|S|⌉₊ + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hk
        push_cast at h2
        have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
        linarith
      have hkpos : (0 : ℝ) < k := (abs_nonneg S).trans_lt hkS
      have hsum : ∑ i, (truncationReal (φ i) k x - c i) = S := by
        rw [hSdef]
        exact Finset.sum_congr rfl fun i _ => by rw [htr k hkm i]
      unfold nppCutoff
      rw [hsum, max_eq_left (by linarith [neg_abs_le S])]
      field_simp
    have hlim : Tendsto (fun k : ℕ => 1 + S * (k : ℝ)⁻¹) atTop (𝓝 1) := by
      have h := ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul S).const_add 1
      simpa only [mul_zero, add_zero, Function.comp_def] using h
    exact hlim.congr' (hev.mono fun k hk => hk.symm)

end Cutoffs

/-! ### The theorem -/

section Product

variable {p q : ℕ}

/-- **Closedness of the non-pluripolar product in every degree** (source `prop:npp1` (5);
FPT `thm:nonpluripolar-product-closed`): for psh `φ₁, …, φ_p` on an open `U ⊆ ℂⁿ` with
`⟨dd^c φ₁ ∧ ⋯ ∧ dd^c φ_p⟩` well defined (`eq:welldefinepluri`), the product is closed
(`IsClosedAny q`: `⟨S, d(ψ ℓ ∧ γ)⟩ = 0` for all test functions `ψ`, real linear forms `ℓ` and
constant `(q-1,q-1)`-forms `γ`). -/
theorem isClosedAny_nonPluripolarProduct (hqp : q + p = n) {U : Opens (ComplexModel n)}
    {φ : Fin p → (ComplexModel n) → EReal} (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (hW : IsWellDefinedOn hqp U φ) : IsClosedAny q (nonPluripolarProduct hqp U φ) := by
  match q, hqp, hW with
  | 0, _, _ => trivial
  | q' + 1, hqp, hW =>
    rw [nonPluripolarProduct_eq hqp hφ]
    exact (isTruncationFamily hqp hφ).isClosedCurrent_glue ((isWellDefinedOn_iff hqp hφ).mp hW)
      (fun k => (isPositive_truncatedBT hqp hφ k).2) (hasPshCutoffs_strictLocus hφ)

end Product

end SGPT.NPP.NonPluripolarCurrent
