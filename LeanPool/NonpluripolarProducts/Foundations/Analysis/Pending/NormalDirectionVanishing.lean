/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.CarriedCurrentTests
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.SkodaElMirEstimate
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.CoordinateWedgeFamilyPairing

/-!
# Closed positive currents carried by a set do not see normal directions

Let `T` be a closed positive current of bidimension `(k+1, k+1)` on a compact Kähler manifold,
carried by a measurable set `E` (`σ_T(M \ E) = 0`), and let `g, F` be chart-smooth functions
with `g = 0` on `E` which form a *holomorphic pair* where a cut-off `ρ` is nonzero:
`dF(iv) = dg(v)` in every chart (i.e. `g + iF` is holomorphic there; in the application
`g + iF` is a coordinate of `X × X` normal to the diagonal).  Then

`T (H · R ∧ Π₁₁ (dg ∧ dG)) = 0`

for EVERY test form `R` of bidimension `(k, k)`, every chart-smooth `G` and every chart-smooth `H`
with `ρ = 1` where `H ≠ 0` (`apply_wedge_normalPair_eq_zero`).  This extends the second step of
the support theorem (`CarriedCurrentTests.apply_slotForm_smulFun_exactPair_eq_zero`, where the
other slots are closed forms) to arbitrary test forms, which is what the tangential reduction
of `bou:diagonal-support` (TN.4 step B4.4, S3) needs.

*Proof.*  (1) For `R = ωᵏ` this is the closed-slot statement (the slots commute,
`wedgeProd_comp_perm`).  (2) For a positive `R` and `P ≥ 0`, the form
`N = Π₁₁ (dg ∧ dF) = dg² + dF²` (on complex lines) is semipositive where `P ≠ 0`, so
`0 ≤ T(P R ∧ N) ≤ c T(P ωᵏ ∧ N) = 0` (`ωᵏ` is an order unit).  (3) Cauchy--Schwarz:
`N + t Π₁₁(dg ∧ dG) + t² Π₁₁ s(G) ≥ 0` on complex lines for every real `t`, so the linear term
vanishes.  (4) Linearity in `R` and `H`.
-/

@[expose] public section

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff

namespace SGPT.Foundations.Analysis.Pending.NormalDirectionVanishing

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
  ProductTestForms PositiveProductCurrents ClosedProductCurrents CurrentTraceMeasure
  CurrentRestriction SlotTestForms CarriedCurrentTests SkodaElMirEstimate TopDegreeDensity
  ClosedCurrentLocalTests

/-! ### Two-forms commute -/

section Perm

variable {n : ℕ}

/-- **The product of two-forms is symmetric in its factors.** -/
theorem wedgeProd_comp_perm (q : ℕ) (β : Fin q → RealForm n 2) (σ : Equiv.Perm (Fin q)) :
    wedgeProd q (fun i => β (σ i)) = wedgeProd q β := by
  ext v
  rw [wedgeProd_apply, wedgeProd_apply, coordinateWedgeFamily_apply_eq_pairingSum,
    coordinateWedgeFamily_apply_eq_pairingSum, coordinatePairingSumFamily_comp_perm]

theorem wedgeProd_snoc_eq_cons (q : ℕ) (β : Fin q → RealForm n 2) (B : RealForm n 2) :
    wedgeProd (q + 1) (Fin.snoc β B) = wedgeProd (q + 1) (Fin.cons B β) := by
  rw [Fin.snoc_eq_cons_rotate]
  exact wedgeProd_comp_perm (q + 1) (Fin.cons B β) (finRotate (q + 1))

end Perm

/-! ### Holomorphic pairs -/

section Pair

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M]

/-- `g + iF` is holomorphic, read in every chart, at the points where `ρ ≠ 0`:
`dF(iv) = dg(v)`. -/
def IsHoloPairOn (g F ρ : M → ℝ) : Prop :=
  ∀ (e : ComplexChart N M) z, z ∈ e.val.target → ρ (e.val.symm z) ≠ 0 → ∀ v : ComplexModel N,
    fderiv ℝ (fun y => F (e.val.symm y)) z (Complex.I • v) =
      fderiv ℝ (fun y => g (e.val.symm y)) z v

/-- On a complex line, `d(g dF)(v, iv) = dg(v)² + dF(v)²` for a holomorphic pair. -/
theorem exactPair_coeff_line_holo {g F ρ : M → ℝ} (hg : ChartSmooth (n := N) g)
    (hF : ChartSmooth (n := N) F) (hpair : IsHoloPairOn (N := N) g F ρ) (e : ComplexChart N M)
    {z : ComplexModel N} (hz : z ∈ e.val.target) (hρ : ρ (e.val.symm z) ≠ 0)
    (v : ComplexModel N) :
    (exactPair g F hg hF).coeff e z ![v, Complex.I • v] =
      fderiv ℝ (fun y => g (e.val.symm y)) z v ^ 2 +
        fderiv ℝ (fun y => F (e.val.symm y)) z v ^ 2 := by
  have h1 := hpair e z hz hρ v
  have h2 := hpair e z hz hρ (Complex.I • v)
  rw [I_smul_I_smul, map_neg] at h2
  rw [exactPair_coeff_line hg hF e hz, h1, ← h2]
  ring

end Pair

/-! ### The vanishing -/

section Vanishing

variable {N : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (ComplexModel N) M]
  [IsComplexManifold N M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  (w : KahlerBackground N M) {k : ℕ} {T : ProductCurrent N M (k + 1)} (hT : IsPositive T)

/-- The Kähler order unit `ωᵏ` as a test form. -/
def kahlerUnit (k : ℕ) : testSpace N M k :=
  ⟨formPow w.form.val k, formPow_mem_testSpace (fun e z hz => (w.isKahler.1 e z hz).1) k⟩

omit [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
theorem smulTest_sub_right {q : ℕ} {h : M → ℝ} (hh : ChartSmooth (n := N) h)
    (φ ψ : testSpace N M q) : smulTest h hh (φ - ψ) = smulTest h hh φ - smulTest h hh ψ :=
  Subtype.ext (smoothRealForm_ext fun _ _ => smul_sub _ _ _)

omit [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
theorem smulTest_smul_right {q : ℕ} {h : M → ℝ} (hh : ChartSmooth (n := N) h) (c : ℝ)
    (φ : testSpace N M q) : smulTest h hh (c • φ) = c • smulTest h hh φ :=
  Subtype.ext (smoothRealForm_ext fun _ _ => smul_comm _ _ _)

omit [CompactSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- A function multiple of `R ∧ β` is positive if `R` is, the function is nonnegative and `β` is
semipositive where the function does not vanish. -/
theorem smulTest_wedge_mem_positiveCone {β : SmoothRealForm N M 2} (hβ : β.IsTypeOneOne)
    {P : M → ℝ} (hP : ChartSmooth (n := N) P) (hP0 : ∀ x, 0 ≤ P x)
    (hβP : ∀ (e : ComplexChart N M) z, z ∈ e.val.target → P (e.val.symm z) ≠ 0 →
      CoefficientSemipositive (β.coeff e z))
    {R : testSpace N M k} (hR : R ∈ positiveCone N M k) :
    smulTest P hP (wedgeTestLM hβ k R) ∈ positiveCone N M (k + 1) := by
  intro e z hz
  change P (e.val.symm z) • coordinateWedge ((R : SmoothRealForm N M (2 * k)).coeff e z)
    (β.coeff e z) ∈ spCone (k + 1)
  by_cases hPz : P (e.val.symm z) = 0
  · rw [hPz, zero_smul]
    exact (spCone (k + 1)).zero_mem
  · exact smul_mem_spCone (wedge_mem_spCone (hR e z hz) ⟨hβ e z hz, hβP e z hz hPz⟩) (hP0 _)

variable {E : Set M} {g F ρ : M → ℝ} (hg : ChartSmooth (n := N) g) (hF : ChartSmooth (n := N) F)

include hT in
/-- **Step 1**: `T(P ωᵏ ∧ Π₁₁ d(g dF)) = 0` (the closed-slot statement, slots commuted). -/
theorem apply_kahlerUnit_eq_zero (hTc : IsClosedCurrent T) (hE : MeasurableSet E)
    (hcar : traceMeasure w T hT Eᶜ = 0) (hg0 : ∀ x ∈ E, g x = 0) {P : M → ℝ}
    (hP : ChartSmooth (n := N) P) :
    T (smulTest P hP (wedgeTestLM (isTypeOneOne_pi11Form (exactPair g F hg hF)) k
      (kahlerUnit w k))) = 0 := by
  rw [← apply_slotForm_smulFun_exactPair_eq_zero w hT hTc hE hcar hg hP hF hg0
    (fun _ : Fin k => w.form)]
  refine hT.apply_eq_of_coeff_eqOn fun e z _ => ?_
  change P (e.val.symm z) • coordinateWedge ((formPow w.form.val k).coeff e z)
      (pi11 ((exactPair g F hg hF).coeff e z)) = _
  rw [slotForm_coeff, formPow_coeff, formPower_eq_wedgeProd, ← wedgeProd_snoc,
    wedgeProd_snoc_eq_cons, smulFun_coeff, pi11_smul]
  have h := wedgeProd_update_smul (k + 1) (Fin.cons (pi11 ((exactPair g F hg hF).coeff e z))
    fun _ : Fin k => w.form.val.coeff e z) 0 (P (e.val.symm z))
    (pi11 ((exactPair g F hg hF).coeff e z))
  rw [Fin.update_cons_zero, Fin.update_cons_zero] at h
  exact h.symm

include hT in
/-- **Step 2**: `T(P R ∧ Π₁₁ d(g dF)) = 0` for positive `R` and `P ≥ 0` vanishing off `{ρ ≠ 0}`. -/
theorem apply_wedge_holoPair_eq_zero (hTc : IsClosedCurrent T) (hE : MeasurableSet E)
    (hcar : traceMeasure w T hT Eᶜ = 0) (hg0 : ∀ x ∈ E, g x = 0)
    (hpair : IsHoloPairOn (N := N) g F ρ) {P : M → ℝ} (hP : ChartSmooth (n := N) P)
    (hP0 : ∀ x, 0 ≤ P x) (hPρ : ∀ x, P x ≠ 0 → ρ x ≠ 0) {R : testSpace N M k}
    (hR : R ∈ positiveCone N M k) :
    T (smulTest P hP (wedgeTestLM (isTypeOneOne_pi11Form (exactPair g F hg hF)) k R)) = 0 := by
  set hN := isTypeOneOne_pi11Form (exactPair g F hg hF)
  have hsemi : ∀ (e : ComplexChart N M) z, z ∈ e.val.target → P (e.val.symm z) ≠ 0 →
      CoefficientSemipositive ((pi11Form (exactPair g F hg hF)).coeff e z) := by
    intro e z hz hPz v
    rw [pi11Form_coeff, pi11_apply_line, exactPair_coeff_line_holo hg hF hpair e hz (hPρ _ hPz)]
    positivity
  have hpos : ∀ R' ∈ positiveCone N M k, 0 ≤ T (smulTest P hP (wedgeTestLM hN k R')) :=
    fun R' hR' => hT _ (smulTest_wedge_mem_positiveCone hN hP hP0 hsemi hR')
  obtain ⟨c, hc0, hc1, -⟩ := exists_orderUnit_bound w.isKahler.1 k R
  have h1 := hpos _ hc1
  have h2 := hpos R hR
  have h3 := apply_kahlerUnit_eq_zero w hT hg hF hTc hE hcar hg0 hP
  change 0 ≤ T (smulTest P hP (wedgeTestLM hN k (c • kahlerUnit w k - R))) at h1
  rw [map_sub, map_smul, smulTest_sub_right, smulTest_smul_right, map_sub, map_smul, h3,
    smul_zero, zero_sub] at h1
  linarith

variable {G : M → ℝ} (hG : ChartSmooth (n := N) G)

include hT hF in
/-- **Step 3 (Cauchy--Schwarz)**: `T(P R ∧ Π₁₁ d(g dG)) = 0` for positive `R` and `P ≥ 0`
vanishing off `{ρ ≠ 0}`. -/
theorem apply_wedge_normalPair_eq_zero_of_pos (hTc : IsClosedCurrent T) (hE : MeasurableSet E)
    (hcar : traceMeasure w T hT Eᶜ = 0) (hg0 : ∀ x ∈ E, g x = 0)
    (hpair : IsHoloPairOn (N := N) g F ρ) {P : M → ℝ} (hP : ChartSmooth (n := N) P)
    (hP0 : ∀ x, 0 ≤ P x) (hPρ : ∀ x, P x ≠ 0 → ρ x ≠ 0) {R : testSpace N M k}
    (hR : R ∈ positiveCone N M k) :
    T (smulTest P hP (wedgeTestLM (isTypeOneOne_pi11Form (exactPair g G hg hG)) k R)) = 0 := by
  set A := exactPair g F hg hF
  set B := exactPair g G hg hG
  set C := gradForm G hG
  have hQ : ∀ t : ℝ, 0 ≤ T (smulTest P hP (wedgeTestLM
      (isTypeOneOne_pi11Form (A + t • B + (t * t) • C)) k R)) := by
    intro t
    refine hT _ (smulTest_wedge_mem_positiveCone _ hP hP0 (fun e z hz hPz v => ?_) hR)
    rw [pi11Form_coeff, pi11_apply_line]
    simp only [coeff_add, coeff_smul, ContinuousAlternatingMap.add_apply,
      ContinuousAlternatingMap.smul_apply, smul_eq_mul, A, B, C]
    rw [exactPair_coeff_line_holo hg hF hpair e hz (hPρ _ hPz), exactPair_coeff_line hg hG e hz,
      gradForm_coeff_line hG e hz]
    have hc := hpair e z hz (hPρ _ hPz) (Complex.I • v)
    rw [I_smul_I_smul, map_neg] at hc
    rw [← hc]
    set a := fderiv ℝ (fun y => g (e.val.symm y)) z v
    set b := fderiv ℝ (fun y => F (e.val.symm y)) z v
    set p := fderiv ℝ (fun y => G (e.val.symm y)) z v
    set q := fderiv ℝ (fun y => G (e.val.symm y)) z (Complex.I • v)
    nlinarith [sq_nonneg (a + t * q / 2), sq_nonneg (b + t * p / 2), sq_nonneg (t * p),
      sq_nonneg (t * q)]
  have hsplit : ∀ t : ℝ, T (smulTest P hP (wedgeTestLM
      (isTypeOneOne_pi11Form (A + t • B + (t * t) • C)) k R)) =
      T (smulTest P hP (wedgeTestLM (isTypeOneOne_pi11Form A) k R)) +
        t * T (smulTest P hP (wedgeTestLM (isTypeOneOne_pi11Form B) k R)) +
        (t * t) * T (smulTest P hP (wedgeTestLM (isTypeOneOne_pi11Form C) k R)) := by
    intro t
    have hform : smulTest P hP (wedgeTestLM (isTypeOneOne_pi11Form (A + t • B + (t * t) • C)) k R)
      =
        smulTest P hP (wedgeTestLM (isTypeOneOne_pi11Form A) k R) +
          t • smulTest P hP (wedgeTestLM (isTypeOneOne_pi11Form B) k R) +
          (t * t) • smulTest P hP (wedgeTestLM (isTypeOneOne_pi11Form C) k R) :=
      Subtype.ext (smoothRealForm_ext fun e z => by
        simp only [smulTest, wedgeTestLM, LinearMap.coe_mk, AddHom.coe_mk, Submodule.coe_add,
          Submodule.coe_smul, smulFun_coeff, wedgeTwo_coeff, coeff_add, coeff_smul,
          pi11Form_coeff, pi11_add, pi11_smul, coordinateWedge_add_right,
          coordinateWedge_smul_right, smul_add, smul_comm (P (e.val.symm z)) t,
          smul_comm (P (e.val.symm z)) (t * t)])
    rw [hform, map_add, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have h0 := apply_wedge_holoPair_eq_zero w hT hg hF hTc hE hcar hg0 hpair hP hP0 hPρ hR
  have hquad : ∀ t : ℝ, 0 ≤ T (smulTest P hP (wedgeTestLM (isTypeOneOne_pi11Form C) k R)) *
      (t * t) + T (smulTest P hP (wedgeTestLM (isTypeOneOne_pi11Form B) k R)) * t + 0 := by
    intro t
    have := hQ t
    rw [hsplit t, h0] at this
    linarith
  have hd := discrim_le_zero hquad
  rw [discrim] at hd
  nlinarith [sq_nonneg (T (smulTest P hP (wedgeTestLM (isTypeOneOne_pi11Form B) k R)))]

include hT hF in
/-- **Closed positive currents carried by `E` do not see normal directions**:
`T (H · R ∧ Π₁₁ (dg ∧ dG)) = 0` for every test form `R`, every chart-smooth `G`, and every
chart-smooth `H` with `ρ = 1` where `H ≠ 0`, if `g = 0` on `E` and `(g, F)` is a holomorphic pair
where `ρ ≠ 0`. -/
theorem apply_wedge_normalPair_eq_zero (hTc : IsClosedCurrent T) (hE : MeasurableSet E)
    (hcar : traceMeasure w T hT Eᶜ = 0) (hg0 : ∀ x ∈ E, g x = 0)
    (hpair : IsHoloPairOn (N := N) g F ρ) (hρ : ChartSmooth (n := N) ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    {H : M → ℝ} (hH : ChartSmooth (n := N) H) (hHρ : ∀ x, H x ≠ 0 → ρ x = 1)
    (R : testSpace N M k) :
    T (smulTest H hH (wedgeTestLM (isTypeOneOne_pi11Form (exactPair g G hg hG)) k R)) = 0 := by
  set hB := isTypeOneOne_pi11Form (exactPair g G hg hG)
  -- positive `R`
  have hposR : ∀ {P : M → ℝ} (hP : ChartSmooth (n := N) P), (∀ x, 0 ≤ P x) →
      (∀ x, P x ≠ 0 → ρ x ≠ 0) → ∀ R : testSpace N M k,
        T (smulTest P hP (wedgeTestLM hB k R)) = 0 := by
    intro P hP hP0 hPρ R
    obtain ⟨c, hc0, -, hc2⟩ := exists_orderUnit_bound w.isKahler.1 k R
    have hW : kahlerUnit w k ∈ positiveCone N M k := formPow_mem_positiveCone w.isKahler.1 k
    have h1 := apply_wedge_normalPair_eq_zero_of_pos w hT hg hF hG hTc hE hcar hg0 hpair hP hP0
      hPρ hc2
    have h2 := apply_wedge_normalPair_eq_zero_of_pos w hT hg hF hG hTc hE hcar hg0 hpair hP hP0
      hPρ hW
    change T (smulTest P hP (wedgeTestLM hB k (c • kahlerUnit w k + R))) = 0 at h1
    rw [map_add, map_smul, smulTest_add_right, smulTest_smul_right, map_add, map_smul, h2,
      smul_zero, zero_add] at h1
    exact h1
  -- split `H` into nonnegative parts
  obtain ⟨K, hK⟩ := isCompact_univ.exists_bound_of_continuousOn
    (ChartSmooth.continuous hH).continuousOn
  set K' := max K 0
  have hHK : ∀ x, |H x| ≤ K' := fun x => (hK x (mem_univ x)).trans (le_max_left _ _)
  have hK'0 : 0 ≤ K' := le_max_right _ _
  have hP₂ : ChartSmooth (n := N) (fun x => K' * ρ x) := chartSmooth_mul (chartSmooth_const K') hρ
  have hP₁ : ChartSmooth (n := N) (fun x => H x + K' * ρ x) :=
    fun e => (hH e).add (hP₂ e)
  have hsplitH : smulTest H hH (wedgeTestLM hB k R) =
      smulTest (fun x => H x + K' * ρ x) hP₁ (wedgeTestLM hB k R) -
        smulTest (fun x => K' * ρ x) hP₂ (wedgeTestLM hB k R) :=
    Subtype.ext (smoothRealForm_ext fun e z => by
      simp only [smulTest, Submodule.coe_sub, smulFun_coeff, coeff_sub]
      ext v
      simp only [ContinuousAlternatingMap.sub_apply, ContinuousAlternatingMap.smul_apply,
        smul_eq_mul]
      ring)
  have h₁0 : ∀ x, 0 ≤ H x + K' * ρ x := by
    intro x
    by_cases hx : H x = 0
    · rw [hx, zero_add]
      exact mul_nonneg hK'0 (hρ0 x)
    · rw [hHρ x hx, mul_one]
      have := hHK x
      rw [abs_le] at this
      linarith
  have h₁ρ : ∀ x, H x + K' * ρ x ≠ 0 → ρ x ≠ 0 := by
    intro x hx h0
    have hH0 : H x = 0 := by
      by_contra hH0
      rw [hHρ x hH0] at h0
      exact one_ne_zero h0
    rw [hH0, h0, mul_zero, add_zero] at hx
    exact hx rfl
  have h₂0 : ∀ x, 0 ≤ K' * ρ x := fun x => mul_nonneg hK'0 (hρ0 x)
  have h₂ρ : ∀ x, K' * ρ x ≠ 0 → ρ x ≠ 0 := by
    intro x hx h0
    rw [h0, mul_zero] at hx
    exact hx rfl
  rw [hsplitH, map_sub, hposR hP₁ h₁0 h₁ρ R, hposR hP₂ h₂0 h₂ρ R, sub_zero]

end Vanishing

end SGPT.Foundations.Analysis.Pending.NormalDirectionVanishing
