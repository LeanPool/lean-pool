/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.NPP.NonPluripolarCurrent2Multilinear
public import LeanPool.NonpluripolarProducts.Currents.PluriharmonicPotential
public import LeanPool.NonpluripolarProducts.Currents.LocalCurrentGluing

/-!
# The non-pluripolar product depends only on the currents `dd^c φ_j` (local theory)

Source: `chapter_npp.tex`, `prop:npp1` (2): "The current `dd^c φ₁ ∧ ⋯ ∧ dd^c φ_p` and the fact
that it is well-defined depend only on the currents `dd^c φ_j`"; Xia, *Foundations of
pluripotential theory*, `prop:nonpluripolar-local-calculus` ("Dependence on the currents
`dd^c u_j`").

Let `U ⊆ ℂⁿ` be open, `q + p = n`.

* `btProduct_update_eq_zero_of_pluriharmonic` — a Bedford–Taylor product with a smooth
  pluriharmonic factor (`dd^c h = 0`) vanishes (`dd^c(h S) = dd^c h ∧ S = 0` for closed `S`).
* `truncatedProduct_update_pluriharmonic` — hence every truncated product
  `1_{O_k} ⋀ dd^c(ψᵢ ∨ (-k))` of a tuple `ψ` with a smooth pluriharmonic entry vanishes (plurifine
  locality on the Borel plurifine open set `O_k`, where `max(h, -k) = h`), and
  `isWellDefinedOn_update_pluriharmonic`, `nonPluripolarProduct_update_pluriharmonic`: such a
  product is well defined and zero.
* `isWellDefinedOn_add_pluriharmonic_iff`, `nonPluripolarProduct_add_pluriharmonic` — **gauge
  invariance**: adding smooth pluriharmonic functions `hᵢ` to the potentials changes neither the
  well-definedness nor the product (multilinearity `eq:ppp6`, S24's
  `NonPluripolarCurrent.nonPluripolarProduct_combo`, slot by slot).
* `isWellDefinedOn_iff_of_ddcL1_eq`, `nonPluripolarProduct_eq_of_ddcL1_eq` — **`prop:npp1` (2),
  local form**: if `dd^c φᵢ = dd^c ψᵢ` as currents (`ddcL1`) for psh, locally integrable
  `φᵢ, ψᵢ`, then `⋀ dd^c φᵢ` is well defined iff `⋀ dd^c ψᵢ` is, and the two products agree
  (Weyl's lemma `SGPT.Currents.exists_pluriharmonic_of_ddcL1_eq` and gauge invariance).
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
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCollar
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCalculus
open SGPT.Foundations.Analysis.Pending.LocalCurrentL1Ddc

variable {n : ℕ}

/-! ### Bounded products with a pluriharmonic factor -/

section Bounded

variable {U : Opens (ComplexModel n)}

/-- **A Bedford–Taylor product with a smooth pluriharmonic factor vanishes**:
`B(u₁, …, h, …, u_p; T) = 0` when `h` is smooth on `U` with `dd^c h = 0` and `T` is closed
    positive.
-/
theorem btProduct_update_eq_zero_of_pluriharmonic (p q : ℕ) (T : LocalProductCurrent n U (q + p))
    (hT : IsPositive T) (hTc : IsClosedAny (q + p) T) (u : Fin p → (ComplexModel n) → ℝ)
    (hu : ∀ i, IsLocallyBoundedPshOn U (u i)) (j : Fin p) {h : (ComplexModel n) → ℝ}
    (hh : ContDiffOn ℝ ∞ h U) (h0 : ∀ z ∈ (U : Set (ComplexModel n)), smoothDDC h z = 0) :
    btProduct p q (Function.update u j h) T = 0 := by
  have hhp : IsLocallyBoundedPshOn U h := isLocallyBoundedPshOn_of_continuousOn
    (plurisubharmonicOn_coe_of_smoothDDC_eq_zero U.isOpen hh h0) hh.continuousOn
  cases p with
  | zero => exact j.elim0
  | succ p =>
    have h1 : q + (p + 1) = q + 1 + p := by omega
    have hX := isPositive_btProduct p (q + 1) (Fin.tail (u ∘ Equiv.swap 0 j)) (castLPC h1 T)
      (isPositive_castLPC h1 hT) (isClosedAny_castLPC h1 hTc) fun i => hu _
    rw [btProduct_update_eq p q T hT hTc u hu j hhp,
      btProduct_succ_eq_ddcMul p q (Function.update (u ∘ Equiv.swap 0 j) 0 h) T (castLPC h1 T)
        (heq_castLPC h1 T), Fin.tail_update_zero, Function.update_self,
      ddcMul_eq_zero_of_smoothDDC_eq_zero hX.1 hX.2 hh h0]

variable {q : ℕ}

/-- The trace measure of the zero current is zero. -/
theorem traceMeasure_zero :
    (isPositive_zero : IsPositive (0 : LocalProductCurrent n U q)).traceMeasure = 0 := by
  have hS : IsPositive (0 : LocalProductCurrent n U q) := isPositive_zero
  refine LocalBedfordTaylorLocality.eq_of_forall_testFunction_integral_eq (U := U)
    hS.traceMeasure_compl (by simp) (fun K hK hKU => hS.traceMeasure_lt_top hK hKU)
    (fun K _ _ => by simp) fun φ => ?_
  rw [hS.integral_traceMeasure]
  simp

/-- Multiplying the zero current by a function gives zero. -/
theorem mulBorel_zero_current (c : (ComplexModel n) → ℝ) : mulBorel (0 : LocalProductCurrent n U
    q) c = 0 := by
  by_cases h : Measurable c ∧ IsLocallyBoundedOn c U
  · ext γ φ
    rw [mulBorel_apply isPositive_zero h.1 h.2, traceMeasure_zero]
    simp
  · rw [mulBorel, dite_eq_right (fun h' => h ⟨h'.2.1, h'.2.2⟩)]

end Bounded

/-! ### Truncated products with a pluriharmonic entry -/

section Truncated

variable {p q : ℕ} (hqp : q + p = n) {U : Opens (ComplexModel n)} {φ : Fin p → (ComplexModel n)
    → EReal}

/-- A smooth function with `dd^c h = 0` on `U` is psh on `U`. -/
theorem plurisubharmonicOn_coe_of_pluriharmonic {h : (ComplexModel n) → ℝ} (hh : ContDiffOn ℝ ∞ h
    U)
    (h0 : ∀ z ∈ (U : Set (ComplexModel n)), smoothDDC h z = 0) :
    PlurisubharmonicOn (fun z => (h z : EReal)) U :=
  plurisubharmonicOn_coe_of_smoothDDC_eq_zero U.isOpen hh h0

/-- **Every truncated product of a tuple with a smooth pluriharmonic entry vanishes**:
`1_{O_k} ⋀ᵢ dd^c(ψᵢ ∨ (-k)) = 0` for `ψ = φ` with `h` in the slot `j`. -/
theorem truncatedProduct_update_pluriharmonic (hφ : ∀ i, PlurisubharmonicOn (φ i) U) (j : Fin p)
    {h : (ComplexModel n) → ℝ} (hh : ContDiffOn ℝ ∞ h U) (h0 : ∀ z ∈ (U : Set (ComplexModel n)),
      smoothDDC h z = 0) (k : ℕ) :
    BedfordTaylorTopDegree.truncatedProduct hqp U (Function.update φ j fun z => (h z : EReal)) k =
      0 := by
  set ψ := Function.update φ j fun z => (h z : EReal)
  have hψ : ∀ i, PlurisubharmonicOn (ψ i) U :=
    plurisubharmonicOn_update hφ (plurisubharmonicOn_coe_of_pluriharmonic hh h0)
  have hhb : IsLocallyBoundedPshOn U h := isLocallyBoundedPshOn_of_continuousOn
    (plurisubharmonicOn_coe_of_pluriharmonic hh h0) hh.continuousOn
  have hv : ∀ i, IsLocallyBoundedPshOn U (truncationReal (ψ i) k) := fun i =>
    truncationReal_isLocallyBoundedPshOn (hψ i) k
  have hw : ∀ i, IsLocallyBoundedPshOn U
      (Function.update (fun i => truncationReal (ψ i) k) j h i) := by
    intro i
    by_cases hij : i = j
    · subst hij
      simpa using hhb
    · simpa [Function.update_of_ne hij] using hv i
  rw [← truncAt_eq_truncatedProduct, truncAt]
  change mulBorel (btProduct p q (fun i => truncationReal (ψ i) k) (oneCurrentOf (U := U) hqp))
    ((BedfordTaylorTopDegree.strictLocus U ψ k).indicator fun _ => (1 : ℝ)) = 0
  have hsub : BedfordTaylorTopDegree.strictLocus U ψ k ⊆ (U : Set (ComplexModel n)) :=
    fun _ hz => hz.1
  rw [mulBorel_btProduct_eq_of_eqOn_plurifineOpen hqp hv hw hsub
    (BedfordTaylorTopDegree.measurableSet_strictLocus hψ k)
    (isOpen_plurifine_strictLocus hψ k) (fun i z hz => ?_)]
  · rw [btProduct_update_eq_zero_of_pluriharmonic p q _ (isPositive_oneCurrentOf hqp)
      (isClosedAny_oneCurrentOf hqp) _ hv j hh h0, mulBorel_zero_current]
  · by_cases hij : i = j
    · subst hij
      rw [Function.update_self]
      have hlt := hz.2 i
      simp only [ψ, Function.update_self] at hlt ⊢
      rw [truncationReal_of_lt hlt, EReal.toReal_coe]
    · rw [Function.update_of_ne hij]

/-- The glued measure of a tuple with a smooth pluriharmonic entry is zero. -/
theorem glueMeasure_update_pluriharmonic (hφ : ∀ i, PlurisubharmonicOn (φ i) U) (j : Fin p)
    {h : (ComplexModel n) → ℝ} (hh : ContDiffOn ℝ ∞ h U) (h0 : ∀ z ∈ (U : Set (ComplexModel n)),
      smoothDDC h z = 0)
    (hψ : ∀ i, PlurisubharmonicOn ((Function.update φ j fun z => (h z : EReal)) i) U) :
    (isTruncationFamily hqp hψ).glueMeasure = 0 := by
  set ψ := Function.update φ j fun z => (h z : EReal)
  set hF := isTruncationFamily hqp hψ
  ext s hs
  rw [hF.glueMeasure_apply hs, FunLike.coe_zero, Pi.zero_apply, tsum_eq_zero_iff]
  intro k
  have hO := BedfordTaylorTopDegree.measurableSet_strictLocus hψ k
  have hS := isPositive_mulBorel_indicator (hF.isPositive k) hO
  have e1 := traceMeasure_mulBorel_indicator_apply (hF.isPositive k) hO hS hs
  have e2 : hS.traceMeasure = 0 := by
    have h' : mulBorel (truncatedBT hqp U ψ k)
        ((BedfordTaylorTopDegree.strictLocus U ψ k).indicator fun _ => (1 : ℝ)) = 0 :=
      truncatedProduct_update_pluriharmonic hqp hφ j hh h0 k
    rw [SGPT.Currents.traceMeasure_congr h' hS isPositive_zero, traceMeasure_zero]
  rw [e2, FunLike.coe_zero, Pi.zero_apply] at e1
  exact measure_mono_null (inter_subset_inter_right _ (layer_subset k)) e1.symm

/-- **A product with a smooth pluriharmonic entry is well defined.** -/
theorem isWellDefinedOn_update_pluriharmonic (hφ : ∀ i, PlurisubharmonicOn (φ i) U) (j : Fin p)
    {h : (ComplexModel n) → ℝ} (hh : ContDiffOn ℝ ∞ h U) (h0 : ∀ z ∈ (U : Set (ComplexModel n)),
      smoothDDC h z = 0) :
    IsWellDefinedOn hqp U (Function.update φ j fun z => (h z : EReal)) := by
  have hψ := plurisubharmonicOn_update hφ (plurisubharmonicOn_coe_of_pluriharmonic hh h0)
    (j := j)
  rw [isWellDefinedOn_iff hqp hψ]
  intro K _ _
  rw [glueMeasure_update_pluriharmonic hqp hφ j hh h0 hψ]
  simp

/-- **A product with a smooth pluriharmonic entry is zero.** -/
theorem nonPluripolarProduct_update_pluriharmonic (hφ : ∀ i, PlurisubharmonicOn (φ i) U)
    (j : Fin p) {h : (ComplexModel n) → ℝ} (hh : ContDiffOn ℝ ∞ h U)
    (h0 : ∀ z ∈ (U : Set (ComplexModel n)), smoothDDC h z = 0) :
    nonPluripolarProduct hqp U (Function.update φ j fun z => (h z : EReal)) = 0 := by
  have hψ := plurisubharmonicOn_update hφ (plurisubharmonicOn_coe_of_pluriharmonic hh h0)
    (j := j)
  have hm := (isWellDefinedOn_iff hqp hψ).mp (isWellDefinedOn_update_pluriharmonic hqp hφ j hh h0)
  ext γ χ
  rw [nonPluripolarProduct_eq hqp hψ, IsTruncationFamily.glue_apply _ hm,
    glueMeasure_update_pluriharmonic hqp hφ j hh h0 hψ]
  simp

end Truncated

/-! ### Gauge invariance -/

section Gauge

variable {p q : ℕ} (hqp : q + p = n) {U : Opens (ComplexModel n)}

/-- A real-valued function is nondegenerate. -/
theorem locallyNondegenerate_coe (h : (ComplexModel n) → ℝ) :
    LocallyNondegenerate fun x : U => (h x : EReal) :=
  fun x _ _ hx => ⟨x, hx, EReal.coe_ne_bot _⟩

/-- **Gauge invariance in one slot**: adding a smooth pluriharmonic `h` to `φ_j` (with `φ_j`
nondegenerate) changes neither well-definedness nor the product. -/
theorem add_pluriharmonic_slot {φ : Fin p → (ComplexModel n) → EReal} (hφ : ∀ i,
    PlurisubharmonicOn (φ i) U)
    (j : Fin p) (hnd : LocallyNondegenerate fun x : U => φ j x) {h : (ComplexModel n) → ℝ}
    (hh : ContDiffOn ℝ ∞ h U) (h0 : ∀ z ∈ (U : Set (ComplexModel n)), smoothDDC h z = 0) :
    (IsWellDefinedOn hqp U (Function.update φ j fun z => φ j z + h z) ↔
        IsWellDefinedOn hqp U φ) ∧
      (IsWellDefinedOn hqp U φ →
        nonPluripolarProduct hqp U (Function.update φ j fun z => φ j z + h z) =
          nonPluripolarProduct hqp U φ) := by
  have hc : Function.update φ j (fun z => φ j z + h z) =
      comboTuple φ j 1 1 fun z => (h z : EReal) := by
    rw [comboTuple]
    congr 1
    funext z
    simp
  have hψ := plurisubharmonicOn_coe_of_pluriharmonic hh h0
  have hcombo := isWellDefinedOn_combo_iff hqp hφ hψ hnd (locallyNondegenerate_coe h)
    one_pos one_pos (j := j)
  have hW2 := isWellDefinedOn_update_pluriharmonic hqp hφ j hh h0
  rw [hc]
  refine ⟨hcombo.trans ⟨fun h' => h'.1, fun h' => ⟨h', hW2⟩⟩, fun hW => ?_⟩
  rw [nonPluripolarProduct_combo hqp hφ hψ hnd (locallyNondegenerate_coe h) one_pos one_pos hW
    hW2, nonPluripolarProduct_update_pluriharmonic hqp hφ j hh h0, one_smul, one_smul, add_zero]

/-- The tuple with `hᵢ` added in the slots of `s`. -/
def addOn (φ : Fin p → (ComplexModel n) → EReal) (h : Fin p → (ComplexModel n) → ℝ)
    (s : Finset (Fin p)) : Fin p → (ComplexModel n) → EReal :=
  fun i z => if i ∈ s then φ i z + h i z else φ i z

theorem addOn_insert (φ : Fin p → (ComplexModel n) → EReal) (h : Fin p → (ComplexModel n) → ℝ)
    {s : Finset (Fin p)}
    {j : Fin p} (hj : j ∉ s) :
    addOn φ h (insert j s) = Function.update (addOn φ h s) j fun z => addOn φ h s j z + h j z := by
  classical
  funext i z
  by_cases hij : i = j
  · subst hij
    simp [addOn, hj]
  · rw [Function.update_of_ne hij]
    simp [addOn, Finset.mem_insert, hij]

/-- **Gauge invariance**: adding smooth pluriharmonic functions `hᵢ` to nondegenerate psh
potentials `φᵢ` changes neither the well-definedness nor the non-pluripolar product. -/
theorem add_pluriharmonic {φ : Fin p → (ComplexModel n) → EReal} (hφ : ∀ i, PlurisubharmonicOn (φ
    i) U)
    (hnd : ∀ i, LocallyNondegenerate fun x : U => φ i x) {h : Fin p → (ComplexModel n) → ℝ}
    (hh : ∀ i, ContDiffOn ℝ ∞ (h i) U) (h0 : ∀ i, ∀ z ∈ (U : Set (ComplexModel n)),
      smoothDDC (h i) z = 0) :
    (IsWellDefinedOn hqp U (fun i z => φ i z + h i z) ↔ IsWellDefinedOn hqp U φ) ∧
      (IsWellDefinedOn hqp U φ →
        nonPluripolarProduct hqp U (fun i z => φ i z + h i z) = nonPluripolarProduct hqp U φ) := by
  classical
  have key : ∀ s : Finset (Fin p),
      (∀ i, PlurisubharmonicOn (addOn φ h s i) U) ∧
      (IsWellDefinedOn hqp U (addOn φ h s) ↔ IsWellDefinedOn hqp U φ) ∧
      (IsWellDefinedOn hqp U φ →
        nonPluripolarProduct hqp U (addOn φ h s) = nonPluripolarProduct hqp U φ) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have e : addOn φ h ∅ = φ := by funext i z; simp [addOn]
      rw [e]
      exact ⟨hφ, Iff.rfl, fun _ => rfl⟩
    | @insert j s hj ih =>
      obtain ⟨hpsh, hiff, heq⟩ := ih
      have hndj : LocallyNondegenerate fun x : U => addOn φ h s j x := by
        have e : (fun x : U => addOn φ h s j x) = fun x : U => φ j x := by
          funext x; simp [addOn, hj]
        rw [e]
        exact hnd j
      have hstep := add_pluriharmonic_slot hqp hpsh j hndj (hh j) (h0 j)
      rw [addOn_insert φ h hj]
      refine ⟨plurisubharmonicOn_update hpsh ((hpsh j).add
          (plurisubharmonicOn_coe_of_pluriharmonic (hh j) (h0 j))), hstep.1.trans hiff,
        fun hW => ?_⟩
      rw [hstep.2 (hiff.mpr hW), heq hW]
  have e : (fun i z => φ i z + h i z) = addOn φ h Finset.univ := by
    funext i z; simp [addOn]
  rw [e]
  exact (key Finset.univ).2

end Gauge

/-! ### `prop:npp1` (2): dependence only on the currents `dd^c φᵢ` -/

section DdcCurrents

variable {m p q : ℕ} (hqp : q + p = m + 1) {U : Opens (ComplexModel (m + 1))}

/-- A psh function in `L¹_loc` is nondegenerate on `U`. -/
theorem locallyNondegenerate_of_isL1PshOn {u : ComplexModel (m + 1) → EReal} (hu : IsL1PshOn U u) :
    LocallyNondegenerate fun x : U => u x := by
  intro x V hV hxV
  obtain ⟨V', hV', rfl⟩ := isOpen_induced_iff.mp hV
  have hmem : V' ∩ U ∈ 𝓝 (x : ComplexModel (m + 1)) :=
    inter_mem (hV'.mem_nhds hxV) (U.isOpen.mem_nhds x.2)
  obtain ⟨y, hy, hyV, hyU⟩ := ((hu.frequently_ne_bot x x.2).and_eventually hmem).exists
  exact ⟨⟨y, hyU⟩, hyV, hy⟩

/-- **`prop:npp1` (2), local form.**  If `φᵢ, ψᵢ` are psh and locally integrable on `U ⊆ ℂ^{m+1}`
and `dd^c φᵢ = dd^c ψᵢ` as currents for every `i`, then `⋀ dd^c φᵢ` is well defined iff
`⋀ dd^c ψᵢ` is, and in that case the non-pluripolar products coincide. -/
theorem nonPluripolarProduct_eq_of_ddcL1_eq {φ ψ : Fin p → ComplexModel (m + 1) → EReal}
    (hφ : ∀ i, IsL1PshOn U (φ i)) (hψ : ∀ i, IsL1PshOn U (ψ i))
    (h : ∀ i, ddcL1 U (φ i) = ddcL1 U (ψ i)) :
    (IsWellDefinedOn hqp U φ ↔ IsWellDefinedOn hqp U ψ) ∧
      (IsWellDefinedOn hqp U φ → nonPluripolarProduct hqp U φ = nonPluripolarProduct hqp U ψ) := by
  choose g hg hg0 hgeq using fun i => SGPT.Currents.exists_pluriharmonic_of_ddcL1_eq (hφ i) (hψ i)
    (h i)
  have hgauge := add_pluriharmonic hqp (fun i => (hφ i).psh)
    (fun i => locallyNondegenerate_of_isL1PshOn (hφ i)) hg hg0
  have hc := nonPluripolarProduct_congr hqp (U := U) (φ := fun i z => φ i z + g i z) (φ' := ψ)
    fun i x hx => (hgeq i x hx).symm
  refine ⟨hgauge.1.symm.trans hc.1, fun hW => ?_⟩
  rw [← hgauge.2 hW, hc.2]

end DdcCurrents

end SGPT.NPP.NonPluripolarCurrent
