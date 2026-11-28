/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Pricing.EquivMartingaleMeasure
public import LeanPool.MathFin.Pricing.FTAP.FTAP

/-!
# Pasting one-period densities into an equivalent martingale measure

The pasting step of the Dalang–Morton–Willinger theorem. Let `S` be an adapted, integrable
`F`-valued discounted price on a filtered probability space `(Ω, 𝓕, P)` with finite horizon `T`,
and suppose each period `t < T` carries a *one-period density* `Z t`: an `𝓕 (t+1)`-measurable,
strictly positive, bounded weight with `P[Z t | 𝓕 t] = 1` that makes `S` a conditional martingale
over that period, `P[Z t • S (t+1) | 𝓕 t] = S t` (`IsOnePeriodDensity`, bundled over the periods
as `LocalEMMDensities`). Then the measure
`Q = P.withDensity (∏_{t<T} Z t)` (`pastedMeasure`) is an equivalent martingale measure
(`isEMM_pastedMeasure`).

The proof is the tower property for the product density `D n = ∏_{s<n} Z s`:
`∫ D m • Y = ∫ D n • Y` for `n ≤ m ≤ T` and `Y` an `𝓕 n`-measurable integrable function
(`integral_pasted_eq`), because `E[Z m | 𝓕 m] = 1` lets each factor be peeled off from the
outside (`integral_smul_cond`). Hence `D T` integrates to `1`, and for `A ∈ 𝓕 t` the `Q`-integrals
of `S (t+1)` and `S t` over `A` agree (`setIntegral_pasted_step`); the conditional-expectation
characterisation `ae_eq_condExp_of_forall_setIntegral_eq` turns this into
`S t = E_Q[S (t+1) | 𝓕 t]` and `IsEMM.of_condExp_succ` packages it.

This pastes given one-period densities. That conditional one-period no-arbitrage *produces* such
densities (a measurable selection of the one-period equivalent martingale measure over `𝓕 t`) is
the remaining step of the Dalang–Morton–Willinger theorem, see `DalangMortonWillinger.lean`.

## Main definitions

* `IsOnePeriodDensity`: a bounded, positive, `𝓕 (t+1)`-measurable weight of conditional mean one
  that makes `S` a conditional martingale over the period `(t, t+1]`.
* `LocalEMMDensities`: the data of one-period densities `Z t`, `t < T`, for an adapted
  integrable price.
* `pastedDensity`: the product density `D n = ∏_{s<n} Z s`.
* `pastedMeasure`: `P.withDensity (ofReal (D T))`.

## Main results

* `LocalEMMDensities.integral_pasted_eq`: the tower property of the product density.
* `LocalEMMDensities.isEMM_pastedMeasure`: the pasted measure is an equivalent martingale measure
  for `S` up to the horizon `T`.

## References

* [H. Föllmer and A. Schied, *Stochastic Finance: An Introduction in Discrete Time*][FollmerSchied],
  §5.2

## Tags

equivalent martingale measure, change of measure, density process, pasting of one-period
measures, tower property, Dalang–Morton–Willinger, JEL G13, MSC 91G20, MSC 60G42, MSC 60G44
-/

@[expose] public section

namespace MathFin

open MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω}
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {𝓕 : Filtration ℕ m0} {P : Measure Ω} {S : ℕ → Ω → F} {T : ℕ} {Z : ℕ → Ω → ℝ}

/-- **A one-period density for period `t`**: a bounded, strictly positive, `𝓕 (t+1)`-measurable
weight `Z` with conditional mean one, `P[Z | 𝓕 t] = 1`, under which `S` is a conditional
martingale over `(t, t+1]`, `P[Z • S (t+1) | 𝓕 t] = S t` (equivalently
`E[Z (S (t+1) − S t) | 𝓕 t] = 0`). This is a one-period equivalent martingale measure conditional
on `𝓕 t`. -/
structure IsOnePeriodDensity (𝓕 : Filtration ℕ m0) (P : Measure Ω) (S : ℕ → Ω → F) (t : ℕ)
    (Z : Ω → ℝ) : Prop where
  meas : StronglyMeasurable[𝓕 (t + 1)] Z
  pos : ∀ ω, 0 < Z ω
  bdd : ∃ C : ℝ, ∀ ω, Z ω ≤ C
  cond_one : P[Z | 𝓕 t] =ᵐ[P] fun _ ↦ (1 : ℝ)
  cond_price : P[Z • S (t + 1) | 𝓕 t] =ᵐ[P] S t

/-- **One-period densities** `Z t`, `t < T`, for an adapted integrable price `S`: each `Z t` is a
one-period density for period `t` (`IsOnePeriodDensity`). These are the conditional one-period
equivalent martingale measures that are pasted into a multi-period one. -/
structure LocalEMMDensities (𝓕 : Filtration ℕ m0) (P : Measure Ω) (S : ℕ → Ω → F) (T : ℕ)
    (Z : ℕ → Ω → ℝ) : Prop where
  adapted : ∀ t ≤ T, StronglyMeasurable[𝓕 t] (S t)
  integrable : ∀ t ≤ T, Integrable (S t) P
  density : ∀ t < T, IsOnePeriodDensity 𝓕 P S t (Z t)

/-- The **product density** `D n ω = ∏_{s<n} Z s ω` of the first `n` one-period densities. -/
noncomputable def pastedDensity (Z : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∏ s ∈ Finset.range n, Z s ω

/-- The **pasted measure**: `P` with density the product `D T` of the one-period densities. -/
noncomputable def pastedMeasure (P : Measure Ω) (Z : ℕ → Ω → ℝ) (T : ℕ) : Measure Ω :=
  P.withDensity fun ω ↦ ENNReal.ofReal (pastedDensity Z T ω)

lemma pastedDensity_zero (ω : Ω) : pastedDensity Z 0 ω = 1 := Finset.prod_range_zero _

lemma pastedDensity_succ (n : ℕ) (ω : Ω) :
    pastedDensity Z (n + 1) ω = pastedDensity Z n ω * Z n ω := Finset.prod_range_succ _ _

omit [CompleteSpace E] in
/-- A bounded nonnegative a.e.-strongly measurable weight against an integrable function is
integrable. -/
lemma integrable_smul_of_bdd {φ : Ω → ℝ} {Y : Ω → E} (hφm : AEStronglyMeasurable φ P)
    (hφ0 : ∀ ω, 0 ≤ φ ω) (C : ℝ) (hC : ∀ ω, φ ω ≤ C) (hY : Integrable Y P) :
    Integrable (fun ω ↦ φ ω • Y ω) P :=
  hY.bdd_smul C hφm (ae_of_all _ fun ω ↦ (Real.norm_of_nonneg (hφ0 ω)).le.trans (hC ω))

omit [CompleteSpace E] in
/-- `∫_A φ • X = ∫ φ • 1_A X`. -/
lemma setIntegral_smul_eq_integral_indicator {A : Set Ω} (hA : MeasurableSet A) (φ : Ω → ℝ)
    (X : Ω → E) :
    ∫ ω in A, φ ω • X ω ∂P = ∫ ω, φ ω • A.indicator X ω ∂P := by
  rw [← integral_indicator hA]
  refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
  by_cases hω : ω ∈ A <;> simp [hω]

namespace LocalEMMDensities

variable (h : LocalEMMDensities 𝓕 P S T Z)

omit [CompleteSpace F] in
include h in
lemma stronglyMeasurable_pasted (n : ℕ) (hn : n ≤ T) :
    StronglyMeasurable[𝓕 n] (pastedDensity Z n) := by
  induction n with
  | zero =>
    have e : pastedDensity Z 0 = fun _ ↦ (1 : ℝ) := funext pastedDensity_zero
    rw [e]
    exact stronglyMeasurable_const
  | succ n ih =>
    have hnT : n < T := Nat.lt_of_succ_le hn
    have e : pastedDensity Z (n + 1) = pastedDensity Z n * Z n := funext (pastedDensity_succ n)
    rw [e]
    exact ((ih hnT.le).mono (𝓕.mono n.le_succ)).mul (h.density n hnT).meas

omit [CompleteSpace F] in
include h in
lemma pastedDensity_pos {n : ℕ} (hn : n ≤ T) (ω : Ω) : 0 < pastedDensity Z n ω :=
  Finset.prod_pos fun s hs ↦ (h.density s (lt_of_lt_of_le (Finset.mem_range.1 hs) hn)).pos ω

omit [CompleteSpace F] in
include h in
lemma exists_bound_pasted (n : ℕ) (hn : n ≤ T) : ∃ C : ℝ, ∀ ω, pastedDensity Z n ω ≤ C := by
  induction n with
  | zero =>
    exact ⟨1, fun ω ↦ (pastedDensity_zero ω).le⟩
  | succ n ih =>
    have hnT : n < T := Nat.lt_of_succ_le hn
    obtain ⟨C, hC⟩ := ih hnT.le
    obtain ⟨B, hB⟩ := (h.density n hnT).bdd
    refine ⟨C * B, fun ω ↦ ?_⟩
    rw [pastedDensity_succ]
    exact mul_le_mul (hC ω) (hB ω) ((h.density n hnT).pos ω).le
      ((h.pastedDensity_pos hnT.le ω).le.trans (hC ω))

omit [CompleteSpace F] in
include h in
lemma measurable_pasted {n : ℕ} (hn : n ≤ T) : Measurable (pastedDensity Z n) :=
  ((h.stronglyMeasurable_pasted n hn).mono (𝓕.le n)).measurable

omit [CompleteSpace F] in
include h in
lemma measurable_Z {t : ℕ} (ht : t < T) : Measurable (Z t) :=
  ((h.density t ht).meas.mono (𝓕.le (t + 1))).measurable

omit [CompleteSpace F] [CompleteSpace E] in
include h in
lemma integrable_smul_pasted {n : ℕ} (hn : n ≤ T) {Y : Ω → E} (hY : Integrable Y P) :
    Integrable (fun ω ↦ pastedDensity Z n ω • Y ω) P := by
  obtain ⟨C, hC⟩ := h.exists_bound_pasted n hn
  exact integrable_smul_of_bdd (h.measurable_pasted hn).aestronglyMeasurable
    (fun ω ↦ (h.pastedDensity_pos hn ω).le) C hC hY

omit [CompleteSpace F] [CompleteSpace E] in
include h in
lemma integrable_smul_Z {t : ℕ} (ht : t < T) {Y : Ω → E} (hY : Integrable Y P) :
    Integrable (fun ω ↦ Z t ω • Y ω) P := by
  obtain ⟨C, hC⟩ := (h.density t ht).bdd
  exact integrable_smul_of_bdd (h.measurable_Z ht).aestronglyMeasurable
    (fun ω ↦ ((h.density t ht).pos ω).le) C hC hY

section Probability

variable [IsProbabilityMeasure P]

omit [CompleteSpace F] in
include h in
lemma integrable_Z {t : ℕ} (ht : t < T) : Integrable (Z t) P := by
  obtain ⟨C, hC⟩ := (h.density t ht).bdd
  exact Integrable.of_bound (h.measurable_Z ht).aestronglyMeasurable C
    (ae_of_all _ fun ω ↦ (Real.norm_of_nonneg ((h.density t ht).pos ω).le).le.trans (hC ω))

omit [CompleteSpace F] in
include h in
/-- **Peeling one density factor**: against an `𝓕 t`-measurable integrable `g`, the period-`t`
density integrates as if it were `1`, since `P[Z t | 𝓕 t] = 1`. -/
lemma integral_smul_cond {t : ℕ} (ht : t < T) {g : Ω → E} (hg : StronglyMeasurable[𝓕 t] g)
    (hgi : Integrable g P) : ∫ ω, Z t ω • g ω ∂P = ∫ ω, g ω ∂P := by
  have hZg : Integrable (Z t • g) P := h.integrable_smul_Z ht hgi
  have e : P[Z t • g | 𝓕 t] =ᵐ[P] P[Z t | 𝓕 t] • g :=
    condExp_smul_of_aestronglyMeasurable_right (h.integrable_Z ht) hZg hg.aestronglyMeasurable
  calc ∫ ω, Z t ω • g ω ∂P = ∫ ω, (P[Z t • g | 𝓕 t]) ω ∂P := (integral_condExp (𝓕.le t)).symm
    _ = ∫ ω, (P[Z t | 𝓕 t] • g) ω ∂P := integral_congr_ae e
    _ = ∫ ω, g ω ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [(h.density t ht).cond_one] with ω hω
      simp [hω]

omit [CompleteSpace F] in
include h in
/-- **Tower property of the product density**: for `n ≤ m ≤ T` and an `𝓕 n`-measurable
integrable `Y`, `∫ D m • Y = ∫ D n • Y`. -/
lemma integral_pasted_eq {n m : ℕ} (hnm : n ≤ m) (hmT : m ≤ T) {Y : Ω → E}
    (hY : StronglyMeasurable[𝓕 n] Y) (hYi : Integrable Y P) :
    ∫ ω, pastedDensity Z m ω • Y ω ∂P = ∫ ω, pastedDensity Z n ω • Y ω ∂P := by
  induction m, hnm using Nat.le_induction with
  | base => rfl
  | succ m hnm ih =>
    have hmlt : m < T := Nat.lt_of_succ_le hmT
    have hg : StronglyMeasurable[𝓕 m] (fun ω ↦ pastedDensity Z m ω • Y ω) :=
      (h.stronglyMeasurable_pasted m hmlt.le).smul (hY.mono (𝓕.mono hnm))
    have hgi : Integrable (fun ω ↦ pastedDensity Z m ω • Y ω) P :=
      h.integrable_smul_pasted hmlt.le hYi
    have e (ω : Ω) : pastedDensity Z (m + 1) ω • Y ω =
        Z m ω • (pastedDensity Z m ω • Y ω) := by
      rw [pastedDensity_succ, mul_comm, mul_smul]
    simp_rw [e]
    exact (h.integral_smul_cond hmlt hg hgi).trans (ih hmlt.le)

omit [CompleteSpace F] in
include h in
/-- The **total mass** of the product density is `1`. -/
lemma integral_pasted_eq_one : ∫ ω, pastedDensity Z T ω ∂P = 1 := by
  have := h.integral_pasted_eq (E := ℝ) (Nat.zero_le T) le_rfl (Y := fun _ ↦ (1 : ℝ))
    stronglyMeasurable_const (integrable_const 1)
  simpa [pastedDensity_zero] using this

omit [CompleteSpace F] [CompleteSpace E] [IsProbabilityMeasure P] in
include h in
/-- **Change of measure to the pasted measure**: over a measurable set the `pastedMeasure`
integral of `g` is the `P`-integral of `D T • g`. -/
lemma setIntegral_pastedMeasure {A : Set Ω} (hA : MeasurableSet A) (g : Ω → E) :
    ∫ ω in A, g ω ∂(pastedMeasure P Z T) = ∫ ω in A, pastedDensity Z T ω • g ω ∂P := by
  unfold pastedMeasure
  rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
    (h.measurable_pasted le_rfl).ennreal_ofReal
    (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top) g hA]
  refine setIntegral_congr_ae hA (ae_of_all _ fun ω _ ↦ ?_)
  simp only [ENNReal.toReal_ofReal (h.pastedDensity_pos le_rfl ω).le]

include h in
/-- **The one-period step of the martingale property**: for `A ∈ 𝓕 t`, `t < T`, the
`D T`-weighted integrals of `S (t+1)` and `S t` over `A` agree. The weight is peeled down to
`D (t+1)` on `S (t+1)` and to `D t` on `S t`; between them lies the one-period identity
`P[Z t • S (t+1) | 𝓕 t] = S t`. -/
lemma setIntegral_pasted_step {t : ℕ} (ht : t < T) {A : Set Ω} (hA : MeasurableSet[𝓕 t] A) :
    ∫ ω in A, pastedDensity Z T ω • S (t + 1) ω ∂P = ∫ ω in A, pastedDensity Z T ω • S t ω ∂P := by
  have hAm : MeasurableSet A := 𝓕.le t A hA
  have hA1 : MeasurableSet[𝓕 (t + 1)] A := 𝓕.mono t.le_succ A hA
  have hS1 : StronglyMeasurable[𝓕 (t + 1)] (A.indicator (S (t + 1))) :=
    (h.adapted (t + 1) (Nat.succ_le_of_lt ht)).indicator hA1
  have hS1i : Integrable (A.indicator (S (t + 1))) P :=
    (h.integrable (t + 1) (Nat.succ_le_of_lt ht)).indicator hAm
  have hS0 : StronglyMeasurable[𝓕 t] (A.indicator (S t)) :=
    (h.adapted t ht.le).indicator hA
  have hS0i : Integrable (A.indicator (S t)) P := (h.integrable t ht.le).indicator hAm
  -- the weight `D T` on `S (t+1)` is peeled down to `D (t+1)`
  have hL : ∫ ω in A, pastedDensity Z T ω • S (t + 1) ω ∂P =
      ∫ ω in A, pastedDensity Z (t + 1) ω • S (t + 1) ω ∂P := by
    rw [setIntegral_smul_eq_integral_indicator hAm (pastedDensity Z T) (S (t + 1)),
      setIntegral_smul_eq_integral_indicator hAm (pastedDensity Z (t + 1)) (S (t + 1))]
    exact h.integral_pasted_eq (Nat.succ_le_of_lt ht) le_rfl hS1 hS1i
  -- the weight `D T` on `S t` is peeled down to `D t`
  have hR : ∫ ω in A, pastedDensity Z T ω • S t ω ∂P =
      ∫ ω in A, pastedDensity Z t ω • S t ω ∂P := by
    rw [setIntegral_smul_eq_integral_indicator hAm (pastedDensity Z T) (S t),
      setIntegral_smul_eq_integral_indicator hAm (pastedDensity Z t) (S t)]
    exact h.integral_pasted_eq ht.le le_rfl hS0 hS0i
  -- the one-period identity
  have hint : Integrable (pastedDensity Z t • (Z t • S (t + 1))) P :=
    h.integrable_smul_pasted ht.le (h.integrable_smul_Z ht (h.integrable (t + 1)
      (Nat.succ_le_of_lt ht)))
  have e1 : P[pastedDensity Z t • (Z t • S (t + 1)) | 𝓕 t] =ᵐ[P]
      pastedDensity Z t • P[Z t • S (t + 1) | 𝓕 t] :=
    condExp_smul_of_aestronglyMeasurable_left
      (h.stronglyMeasurable_pasted t ht.le).aestronglyMeasurable hint
      (h.integrable_smul_Z ht (h.integrable (t + 1) (Nat.succ_le_of_lt ht)))
  have e2 : pastedDensity Z t • P[Z t • S (t + 1) | 𝓕 t] =ᵐ[P] pastedDensity Z t • S t := by
    filter_upwards [(h.density t ht).cond_price] with ω hω
    exact congrArg (fun x ↦ pastedDensity Z t ω • x) hω
  have hM : ∫ ω in A, pastedDensity Z (t + 1) ω • S (t + 1) ω ∂P =
      ∫ ω in A, pastedDensity Z t ω • S t ω ∂P := by
    calc ∫ ω in A, pastedDensity Z (t + 1) ω • S (t + 1) ω ∂P
        = ∫ ω in A, (pastedDensity Z t • (Z t • S (t + 1))) ω ∂P := by
          refine setIntegral_congr_ae hAm (ae_of_all _ fun ω _ ↦ ?_)
          change pastedDensity Z (t + 1) ω • S (t + 1) ω =
            pastedDensity Z t ω • (Z t ω • S (t + 1) ω)
          rw [pastedDensity_succ, mul_smul]
      _ = ∫ ω in A, (P[pastedDensity Z t • (Z t • S (t + 1)) | 𝓕 t]) ω ∂P :=
          (setIntegral_condExp (𝓕.le t) hint hA).symm
      _ = ∫ ω in A, pastedDensity Z t ω • S t ω ∂P :=
          setIntegral_congr_ae hAm ((e1.trans e2).mono fun ω hω _ ↦ hω)
  rw [hL, hM, hR]

include h in
/-- **The pasted measure is an equivalent martingale measure.** Given one-period densities
`Z t`, `t < T`, for an adapted integrable price `S` (`LocalEMMDensities`), the measure
`P.withDensity (∏_{t<T} Z t)` is an equivalent probability measure of `P` under which `S`,
frozen at the horizon `T`, is a martingale. -/
theorem isEMM_pastedMeasure : IsEMM 𝓕 P S T (pastedMeasure P Z T) := by
  have hDm := h.measurable_pasted (le_refl T)
  have hDpos := h.pastedDensity_pos (le_refl T)
  have hDint : Integrable (pastedDensity Z T) P := by
    obtain ⟨C, hC⟩ := h.exists_bound_pasted T le_rfl
    exact Integrable.of_bound hDm.aestronglyMeasurable C
      (ae_of_all _ fun ω ↦ (Real.norm_of_nonneg (hDpos ω).le).le.trans (hC ω))
  have hQ : IsEquivProbMeasure P (pastedMeasure P Z T) :=
    isEquivProbMeasure_withDensity P hDpos hDint h.integral_pasted_eq_one
  have := hQ.isProb
  have hint : ∀ t ≤ T, Integrable (S t) (pastedMeasure P Z T) := by
    intro t ht
    change Integrable (S t) (P.withDensity fun ω ↦ ENNReal.ofReal (pastedDensity Z T ω))
    refine (integrable_withDensity_iff_integrable_smul' hDm.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).2 ?_
    refine (h.integrable_smul_pasted le_rfl (h.integrable t ht)).congr
      (ae_of_all _ fun ω ↦ ?_)
    simp only [ENNReal.toReal_ofReal (hDpos ω).le]
  refine IsEMM.of_condExp_succ hQ h.adapted hint fun t ht ↦ ?_
  refine ae_eq_condExp_of_forall_setIntegral_eq (𝓕.le t) (hint (t + 1) (Nat.succ_le_of_lt ht))
    (fun s _ _ ↦ (hint t ht.le).integrableOn) (fun s hs _ ↦ ?_)
    (h.adapted t ht.le).aestronglyMeasurable
  have hsm : MeasurableSet s := 𝓕.le t s hs
  rw [h.setIntegral_pastedMeasure hsm (S t), h.setIntegral_pastedMeasure hsm (S (t + 1))]
  exact (h.setIntegral_pasted_step ht hs).symm

end Probability

end LocalEMMDensities

end MathFin
