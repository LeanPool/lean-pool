/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BTTruncations
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorSlotStokes
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorSlotSmul
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.PshConvexCone

/-!
# The relative Monge–Ampère capacity

For an open set `Ω ⊆ ℂⁿ` and `E ⊆ ℂⁿ` the *relative Monge–Ampère capacity* is
`c(E, Ω) = sup { (ddᶜu)ⁿ(E) : u psh on Ω, -1 ≤ u ≤ 0 }`, the supremum of the
bounded Bedford–Taylor measures of `E` (Bedford–Taylor; Błocki, *The complex
Monge–Ampère operator in pluripotential theory*, lecture notes, §2.2).

We prove monotonicity and countable subadditivity (Błocki, Prop. 2.2.1 ii, iii)
and the **domination of mixed measures by the capacity**: if `-M ≤ vᵢ ≤ 0` are
locally bounded plurisubharmonic on `Ω`, then

  `ddᶜv₁ ∧ ⋯ ∧ ddᶜvₙ (E) ≤ (nM)ⁿ · c(E, Ω)`.

Proof: `w = (nM)⁻¹ ∑ᵢ vᵢ` is a competitor, and expanding `(ddᶜw)ⁿ` slot by slot
(slot additivity and homogeneity of Bedford–Taylor limits) exhibits
`(nM)⁻ⁿ ddᶜv₁ ∧ ⋯ ∧ ddᶜvₙ` as one of its nonnegative summands. A diagonal form
for `a ≤ u ≤ b` follows by the gauge invariance under constants.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff ENNReal

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

variable {n : ℕ}

/-- The **relative Monge–Ampère capacity** `c(E, Ω)`. -/
def relCapacity (Ω : Opens (ComplexModel n)) (E : Set (ComplexModel n)) : ℝ≥0∞ :=
  ⨆ (u : ComplexModel n → ℝ) (hu : IsLocallyBoundedPshOn Ω u)
    (_ : ∀ z ∈ Ω, -1 ≤ u z ∧ u z ≤ 0),
      Pending.MongeAmpere.canonicalBedfordTaylorMeasure Ω u hu E

theorem canonicalBedfordTaylorMeasure_le_relCapacity {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u)
    (hb : ∀ z ∈ Ω, -1 ≤ u z ∧ u z ≤ 0) (E : Set (ComplexModel n)) :
    Pending.MongeAmpere.canonicalBedfordTaylorMeasure Ω u hu E ≤ relCapacity Ω E :=
  le_iSup₂_of_le (f := fun u hu ↦ ⨆ (_ : ∀ z ∈ Ω, -1 ≤ u z ∧ u z ≤ 0),
    Pending.MongeAmpere.canonicalBedfordTaylorMeasure Ω u hu E) u hu (le_iSup_of_le hb le_rfl)

theorem relCapacity_le_of_forall {Ω : Opens (ComplexModel n)} {E : Set (ComplexModel n)}
    {c : ℝ≥0∞} (h : ∀ (u : ComplexModel n → ℝ) (hu : IsLocallyBoundedPshOn Ω u),
      (∀ z ∈ Ω, -1 ≤ u z ∧ u z ≤ 0) →
        Pending.MongeAmpere.canonicalBedfordTaylorMeasure Ω u hu E ≤ c) :
    relCapacity Ω E ≤ c :=
  iSup₂_le fun u hu ↦ iSup_le fun hb ↦ h u hu hb

/-- Monotonicity in the set (Błocki, Prop. 2.2.1 ii). -/
theorem relCapacity_mono {Ω : Opens (ComplexModel n)} {E F : Set (ComplexModel n)}
    (h : E ⊆ F) : relCapacity Ω E ≤ relCapacity Ω F :=
  relCapacity_le_of_forall fun _ hu hb ↦
    (measure_mono h).trans (canonicalBedfordTaylorMeasure_le_relCapacity hu hb F)

@[simp] theorem relCapacity_empty (Ω : Opens (ComplexModel n)) : relCapacity Ω ∅ = 0 :=
  le_antisymm (relCapacity_le_of_forall fun _ _ _ ↦ by simp) bot_le

/-- Countable subadditivity (Błocki, Prop. 2.2.1 iii). -/
theorem relCapacity_iUnion_le {ι : Type*} [Countable ι] (Ω : Opens (ComplexModel n))
    (E : ι → Set (ComplexModel n)) :
    relCapacity Ω (⋃ i, E i) ≤ ∑' i, relCapacity Ω (E i) :=
  relCapacity_le_of_forall fun _ hu hb ↦ (measure_iUnion_le _).trans
    (tsum_le_tsum fun i ↦ canonicalBedfordTaylorMeasure_le_relCapacity hu hb (E i))

theorem relCapacity_union_le (Ω : Opens (ComplexModel n)) (E F : Set (ComplexModel n)) :
    relCapacity Ω (E ∪ F) ≤ relCapacity Ω E + relCapacity Ω F :=
  relCapacity_le_of_forall fun _ hu hb ↦ (measure_union_le _ _).trans
    (add_le_add (canonicalBedfordTaylorMeasure_le_relCapacity hu hb E)
      (canonicalBedfordTaylorMeasure_le_relCapacity hu hb F))

/-! ## Bedford–Taylor limits of bounded tuples -/

theorem isLocallyBoundedPshOn_of_abs_le {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : PlurisubharmonicOn (fun z ↦ (u z : EReal)) Ω) {C : ℝ} (hC : ∀ z ∈ Ω, |u z| ≤ C) :
    IsLocallyBoundedPshOn Ω u :=
  ⟨hu, fun _ hz ↦ ⟨Ω, hz, le_rfl, C, hC⟩⟩

theorem isBTLimit_canonicalBedfordTaylorMeasure {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u) :
    IsBTLimit Ω (fun _ ↦ u) (Pending.MongeAmpere.canonicalBedfordTaylorMeasure Ω u hu) :=
  IsLocalBedfordTaylorMeasure.isBTLimit
    (Pending.MongeAmpere.canonicalBedfordTaylorMeasure_spec Ω u hu)

/-- Tuples of locally bounded plurisubharmonic functions have Bedford–Taylor limits. -/
theorem exists_isBTLimit_of_isLocallyBoundedPshOn {Ω : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} (hu : ∀ i, IsLocallyBoundedPshOn Ω (u i)) :
    ∃ μ, IsBTLimit Ω u μ := by
  refine exists_isBTLimit fun V hV ↦ ?_
  choose f hf using fun i ↦ HolomorphicPullback.exists_decreasingMollifierApproximation (hu i) hV
  exact ⟨f, fun i ↦ isDecApprox_of_isDecreasingApproximation (hu i) (subset_closure.trans hV.2)
    (hf i), fun i hi ↦ absurd i.isLt (not_lt.mpr hi)⟩

/-- Restriction of a Bedford–Taylor limit to an open subset. -/
theorem IsBTLimit.restrict_opens {Ω V : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → ℝ}
    {μ : Measure (ComplexModel n)} (hμ : IsBTLimit Ω u μ) (hVΩ : V ≤ Ω) :
    IsBTLimit V u (μ.restrict V) := by
  refine ⟨by rw [Measure.restrict_apply' V.isOpen.measurableSet]; simp,
    fun K hK hKV ↦ (Measure.restrict_apply_le _ _).trans_lt (hμ.2.1 K hK (hKV.trans hVΩ)),
    fun U hU ↦ ?_⟩
  have hUΩ : RelativelyCompactIn U Ω := ⟨hU.1, hU.2.trans hVΩ⟩
  obtain ⟨F, hF, hFT⟩ := hμ.2.2 U hUΩ
  refine ⟨F, hF, fun φ hφ hφc hφU ↦ ?_⟩
  have hUV : (U : Set (ComplexModel n)) ⊆ V := subset_closure.trans hU.2
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦
    image_eq_zero_of_notMem_tsupport fun h ↦ hz (hUV (hφU h))]
  exact hFT φ hφ hφc hφU

/-- Scaling every slot by `c ≥ 0` scales the limit by `cⁿ`. -/
theorem IsBTLimit.const_mul_all {Ω : Opens (ComplexModel n)} {v : Fin n → ComplexModel n → ℝ}
    {μ : Measure (ComplexModel n)} (hμ : IsBTLimit Ω v μ) {c : ℝ} (hc : 0 ≤ c) :
    IsBTLimit Ω (fun i z ↦ c * v i z) (ENNReal.ofReal c ^ n • μ) := by
  classical
  have key : ∀ k, k ≤ n → IsBTLimit Ω (fun i z ↦ if i.val < k then c * v i z else v i z)
      (ENNReal.ofReal c ^ k • μ) := by
    intro k
    induction k with
    | zero => intro _; simpa using hμ
    | succ k ih =>
      intro hk
      set i₀ : Fin n := ⟨k, hk⟩
      have e1 : Function.update (fun i z ↦ if i.val < k then c * v i z else v i z) i₀ (v i₀) =
          fun i z ↦ if i.val < k then c * v i z else v i z := by
        funext i z
        by_cases hi : i = i₀
        · subst hi; simp [i₀]
        · simp [Function.update_of_ne hi]
      have e2 : Function.update (fun i z ↦ if i.val < k then c * v i z else v i z) i₀
          (fun z ↦ c * v i₀ z) = fun i z ↦ if i.val < k + 1 then c * v i z else v i z := by
        funext i z
        by_cases hi : i = i₀
        · subst hi; simp [i₀]
        · have hne : i.val ≠ k := fun h ↦ hi (Fin.ext h)
          simp only [Function.update_of_ne hi]
          by_cases hlt : i.val < k
          · simp [hlt, show i.val < k + 1 by omega]
          · simp [hlt, show ¬ i.val < k + 1 by omega]
      have hk' := ih (by omega)
      rw [← e1] at hk'
      have h := IsBTLimit.const_mul_slot i₀ hc hk'
      rw [e2, ← mul_smul, ← pow_succ'] at h
      exact h
  simpa using key n le_rfl

/-- **Expansion lower bound.** If every slot of the constant tuple `w` is the sum
`∑ᵢ sᵢ` of locally bounded plurisubharmonic functions, then the Bedford–Taylor
limit of `(s₀, …, s_{n-1})` is at most that of `(w, …, w)`. -/
theorem IsBTLimit.le_of_sum_diagonal {N : ℕ} {Ω : Opens (ComplexModel (N + 1))}
    {s : Fin (N + 1) → ComplexModel (N + 1) → ℝ} (hs : ∀ i, IsLocallyBoundedPshOn Ω (s i))
    {w : ComplexModel (N + 1) → ℝ} (hw : IsLocallyBoundedPshOn Ω w)
    (hsw : ∀ z, w z = ∑ i, s i z)
    {μ ν : Measure (ComplexModel (N + 1))} (hμ : IsBTLimit Ω s μ)
    (hν : IsBTLimit Ω (fun _ ↦ w) ν) : μ ≤ ν := by
  classical
  set P : ℕ → Fin (N + 1) → ComplexModel (N + 1) → ℝ := fun k i ↦
    if i.val < k then s i else w with hP
  have hPb (k : ℕ) (i : Fin (N + 1)) : IsLocallyBoundedPshOn Ω (P k i) := by
    by_cases h : i.val < k <;> simp [hP, h, hs i, hw]
  have key : ∀ k, k ≤ N + 1 → ∃ ρ, IsBTLimit Ω (P k) ρ ∧ ρ ≤ ν := by
    intro k
    induction k with
    | zero => exact fun _ ↦ ⟨ν, by simpa [hP] using hν, le_rfl⟩
    | succ k ih =>
      intro hk
      obtain ⟨ρ, hρ, hρν⟩ := ih (by omega)
      set i₀ : Fin (N + 1) := ⟨k, hk⟩
      have hupd (a : ComplexModel (N + 1) → ℝ) (ha : IsLocallyBoundedPshOn Ω a) (i : Fin (N + 1)) :
          IsLocallyBoundedPshOn Ω (Function.update (P k) i₀ a i) := by
        by_cases h : i = i₀
        · subst h; simpa using ha
        · simpa [Function.update_of_ne h] using hPb k i
      choose ν' hν' using fun b ↦ exists_isBTLimit_of_isLocallyBoundedPshOn (hupd (s b) (hs b))
      have hsum := IsBTLimit.sum_slot i₀ (s := s) (ν := ν') hν'
      have hwfun : (fun z ↦ ∑ b, s b z) = w := funext fun z ↦ (hsw z).symm
      have hPk : Function.update (P k) i₀ w = P k := by
        funext i
        by_cases h : i = i₀
        · subst h; simp [hP, i₀]
        · simp [Function.update_of_ne h]
      rw [hwfun, hPk] at hsum
      have heq := hsum.unique hρ
      have hPk1 : Function.update (P k) i₀ (s i₀) = P (k + 1) := by
        funext i
        by_cases h : i = i₀
        · subst h; simp [hP, i₀]
        · have hne : i.val ≠ k := fun h' ↦ h (Fin.ext h')
          simp only [Function.update_of_ne h, hP]
          by_cases hlt : i.val < k
          · simp [hlt, show i.val < k + 1 by omega]
          · simp [hlt, show ¬ i.val < k + 1 by omega]
      refine ⟨ν' i₀, hPk1 ▸ hν' i₀, le_trans ?_ hρν⟩
      rw [← heq]
      refine Measure.le_iff'.2 fun t ↦ ?_
      rw [FunLike.coe_sum, Finset.sum_apply]
      exact Finset.single_le_sum (f := fun b ↦ ν' b t) (fun _ _ ↦ bot_le) (Finset.mem_univ i₀)
  obtain ⟨ρ, hρ, hρν⟩ := key (N + 1) le_rfl
  have hPn : P (N + 1) = s := by funext i; simp [hP, i.isLt]
  rw [hPn] at hρ
  rw [hμ.unique hρ]
  exact hρν

/-! ## Domination by the capacity -/

theorem plurisubharmonicOn_coe_sum {Ω : Opens (ComplexModel n)} {ι : Type*} (t : Finset ι)
    {s : ι → ComplexModel n → ℝ} (hs : ∀ i ∈ t, PlurisubharmonicOn (fun z ↦ (s i z : EReal)) Ω) :
    PlurisubharmonicOn (fun z ↦ ((∑ i ∈ t, s i z : ℝ) : EReal)) Ω := by
  classical
  induction t using Finset.induction_on with
  | empty => intro x _; simpa using plurisubharmonicAt_const (0 : EReal) (by simp) x
  | insert a t hat ih =>
    simp only [Finset.sum_insert hat, EReal.coe_add]
    exact (hs a (Finset.mem_insert_self a t)).add (ih fun i hi ↦ hs i (Finset.mem_insert_of_mem
      hi))

theorem plurisubharmonicOn_coe_const_mul {Ω : Opens (ComplexModel n)} {u : ComplexModel n → ℝ}
    (hu : PlurisubharmonicOn (fun z ↦ (u z : EReal)) Ω) {c : ℝ} (hc : 0 < c) :
    PlurisubharmonicOn (fun z ↦ ((c * u z : ℝ) : EReal)) Ω := by
  simpa only [EReal.coe_mul] using hu.const_mul hc

/-- **Domination of mixed Bedford–Taylor measures by the capacity.** -/
theorem IsBTLimit.le_relCapacity {Ω : Opens (ComplexModel n)} {v : Fin n → ComplexModel n → ℝ}
    {μ : Measure (ComplexModel n)} (hμ : IsBTLimit Ω v μ)
    (hv : ∀ i, IsLocallyBoundedPshOn Ω (v i)) {M : ℝ} (hM : 0 < M)
    (hvM : ∀ i, ∀ z ∈ Ω, -M ≤ v i z ∧ v i z ≤ 0) (E : Set (ComplexModel n)) :
    μ E ≤ ENNReal.ofReal ((n * M) ^ n) * relCapacity Ω E := by
  classical
  cases n with
  | zero =>
    have hw : IsLocallyBoundedPshOn Ω (fun _ : ComplexModel 0 ↦ (0 : ℝ)) :=
      isLocallyBoundedPshOn_of_abs_le (C := 0)
        (fun x _ ↦ by simpa using plurisubharmonicAt_const (0 : EReal) (by simp) x)
        fun _ _ ↦ by simp
    have h := isBTLimit_canonicalBedfordTaylorMeasure hw
    have hvw : v = fun _ ↦ fun _ ↦ (0 : ℝ) := funext fun i ↦ i.elim0
    rw [hvw] at hμ
    rw [hμ.unique h]
    simpa using canonicalBedfordTaylorMeasure_le_relCapacity hw (by simp) E
  | succ N =>
    set c : ℝ := ((N + 1 : ℕ) * M)⁻¹ with hc_def
    have hc : 0 < c := by positivity
    have hcM : ((N + 1 : ℕ) : ℝ) * M * c = 1 := by rw [hc_def]; field_simp
    set s : Fin (N + 1) → ComplexModel (N + 1) → ℝ := fun i z ↦ c * v i z with hs_def
    set w : ComplexModel (N + 1) → ℝ := fun z ↦ ∑ i, s i z with hw_def
    have hsb (i : Fin (N + 1)) : IsLocallyBoundedPshOn Ω (s i) :=
      isLocallyBoundedPshOn_of_abs_le (C := c * M) (plurisubharmonicOn_coe_const_mul (hv i).1 hc)
        fun z hz ↦ by
          have := hvM i z hz
          rw [abs_le]; constructor <;> simp only [hs_def] <;> nlinarith
    have hwb : ∀ z ∈ Ω, -1 ≤ w z ∧ w z ≤ 0 := by
      intro z hz
      constructor
      · have h1 : ∑ _i : Fin (N + 1), -(c * M) ≤ w z :=
          Finset.sum_le_sum fun i _ ↦ by have := hvM i z hz; simp only [hs_def]; nlinarith
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
        linarith
      · exact Finset.sum_nonpos fun i _ ↦ by
          have := hvM i z hz; simp only [hs_def]; nlinarith
    have hw : IsLocallyBoundedPshOn Ω w :=
      isLocallyBoundedPshOn_of_abs_le (C := 1)
        (plurisubharmonicOn_coe_sum Finset.univ fun i _ ↦ (hsb i).1)
        fun z hz ↦ abs_le.2 ⟨(hwb z hz).1, (hwb z hz).2.trans zero_le_one⟩
    have hν := isBTLimit_canonicalBedfordTaylorMeasure hw
    have hscaled := hμ.const_mul_all hc.le
    have hle := IsBTLimit.le_of_sum_diagonal hsb hw (fun z ↦ rfl) hscaled hν
    have h1 : ENNReal.ofReal ((((N + 1 : ℕ) : ℝ) * M) ^ (N + 1)) * ENNReal.ofReal c ^ (N + 1)
      = 1 := by
      rw [← ENNReal.ofReal_pow hc.le, ← ENNReal.ofReal_mul (by positivity), ← mul_pow, hcM]
      simp
    calc μ E = ENNReal.ofReal ((((N + 1 : ℕ) : ℝ) * M) ^ (N + 1)) *
          (ENNReal.ofReal c ^ (N + 1) • μ) E := by
          rw [smul_apply, smul_eq_mul, ← mul_assoc, h1, one_mul]
      _ ≤ ENNReal.ofReal ((((N + 1 : ℕ) : ℝ) * M) ^ (N + 1)) *
          Pending.MongeAmpere.canonicalBedfordTaylorMeasure Ω w hw E := by
          gcongr
      _ ≤ _ := by
          gcongr
          exact canonicalBedfordTaylorMeasure_le_relCapacity hw hwb E

/-- **Diagonal domination.** For a locally bounded plurisubharmonic `u` with
`a ≤ u ≤ b` on `Ω`, `(ddᶜu)ⁿ(E) ≤ (b - a)ⁿ · c(E, Ω)`. -/
theorem canonicalBedfordTaylorMeasure_le_relCapacity_of_bounds {Ω : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} (hu : IsLocallyBoundedPshOn Ω u) {a b : ℝ} (hab : a < b)
    (hbd : ∀ z ∈ Ω, a ≤ u z ∧ u z ≤ b) (E : Set (ComplexModel n)) :
    Pending.MongeAmpere.canonicalBedfordTaylorMeasure Ω u hu E ≤
      ENNReal.ofReal ((b - a) ^ n) * relCapacity Ω E := by
  set d : ℝ := b - a with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  set w : ComplexModel n → ℝ := fun z ↦ d⁻¹ * (u z + -b) with hw_def
  have hwb : ∀ z ∈ Ω, -1 ≤ w z ∧ w z ≤ 0 := by
    intro z hz
    obtain ⟨h1, h2⟩ := hbd z hz
    refine ⟨?_, mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 hd0.le) (by linarith)⟩
    change -1 ≤ d⁻¹ * (u z + -b)
    rw [show u z + -b = -(b - u z) by ring, mul_neg, neg_le_neg_iff, inv_mul_le_iff₀ hd0]
    linarith
  have hpsh : PlurisubharmonicOn (fun z ↦ (w z : EReal)) Ω := by
    have hc : PlurisubharmonicOn (fun z ↦ ((∑ i ∈ ({0, 1} : Finset (Fin 2)),
        (![u, fun _ ↦ -b] i) z : ℝ) : EReal)) Ω := by
      refine plurisubharmonicOn_coe_sum _ fun i _ ↦ ?_
      fin_cases i
      · simpa using hu.1
      · intro x _; simpa using plurisubharmonicAt_const ((-b : ℝ) : EReal) (by simp) x
    have := plurisubharmonicOn_coe_const_mul hc (inv_pos.2 hd0)
    simpa [hw_def] using this
  have hw : IsLocallyBoundedPshOn Ω w :=
    isLocallyBoundedPshOn_of_abs_le hpsh (C := 1) fun z hz ↦
      abs_le.2 ⟨(hwb z hz).1, (hwb z hz).2.trans zero_le_one⟩
  have hconst : IsSmoothPluriharmonicOn Ω (fun _ ↦ -b) :=
    ⟨contDiffOn_const, fun z _ ↦ by ext j k; simp [complexHessian]⟩
  have h1 := (isBTLimit_canonicalBedfordTaylorMeasure hu).add_pluriharmonic
    (h := fun _ _ ↦ -b) fun _ ↦ hconst
  have h2 := (isBTLimit_canonicalBedfordTaylorMeasure hw).const_mul_all hd0.le
  have hfun : (fun (_ : Fin n) (z : ComplexModel n) ↦ d * w z) =
      fun (_ : Fin n) (z : ComplexModel n) ↦ u z + -b := by
    funext _ z; simp only [hw_def]; field_simp
  rw [hfun] at h2
  rw [h1.unique h2, smul_apply, smul_eq_mul, ENNReal.ofReal_pow hd0.le]
  gcongr
  exact canonicalBedfordTaylorMeasure_le_relCapacity hw hwb E

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
