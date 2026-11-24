/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorSlotIBP
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorSlotDefect

/-!
# Integration by parts against a regularized slot defect

`exists_integral_sub_eq_ibp_slot` compares two tuples differing in one slot
through measures carrying `φ + C‖z‖²` and `‖z‖²` in that slot, on a relatively
compact subdomain. For a global argument the regularizer must be allowed to be
an arbitrary smooth plurisubharmonic function `p` — on a manifold, the local
potential of a Kähler form — and the comparison measures must be the
Bedford–Taylor limits on the whole domain. This module provides that form:

  `∫ φ dμ_a - ∫ φ dμ_b = ∫ χ (a - b) dμ(φ + p) - ∫ χ (a - b) dμ(p)`,

for a cutoff `χ` equal to one near the support of `φ`. The passage from `C‖z‖²`
to `p` is `IsBTLimit.slotDefect_regularizer_congr`, after scaling one slot by a
natural number with `IsBTLimit.sum_slot`.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

variable {n : ℕ}

/-- Bedford–Taylor limits are symmetric functions of the tuple. -/
theorem IsBTLimit.comp_perm {Ω : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → ℝ}
    {μ : Measure (ComplexModel n)} (hμ : IsBTLimit Ω u μ) (τ : Equiv.Perm (Fin n)) :
    IsBTLimit Ω (fun i => u (τ i)) μ :=
  ⟨hμ.1, hμ.2.1, fun U hU => by
    obtain ⟨F, hF, hT⟩ := hμ.2.2 U hU
    exact ⟨fun i => F (τ i), hF.comp_perm τ, hT.comp_perm τ⟩⟩

/-- A Bedford–Taylor limit, restricted to a relatively compact subdomain, is the
limit of every admissible family at any level. -/
theorem IsBTLimit.tendstoMixed_restrict {Ω U : Opens (ComplexModel n)}
    {u : Fin n → ComplexModel n → ℝ} {μ : Measure (ComplexModel n)} (hμ : IsBTLimit Ω u μ)
    (hU : RelativelyCompactIn U Ω) {q : ℕ} {F : Fin n → ℕ → ComplexModel n → ℝ}
    (hF : IsAdmissible q U u F) :
    TendstoMixed U F (μ.restrict (U : Set (ComplexModel n))) := by
  have hF' : IsAdmissible n U u F := ⟨hF.1, fun i hi => absurd i.isLt (not_lt.mpr hi)⟩
  intro φ hφ hφc hφU
  have hint : (∫ z, φ z ∂(μ.restrict (U : Set (ComplexModel n)))) = ∫ z, φ z ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz =>
      image_eq_zero_of_notMem_tsupport fun h => hz (hφU h)
  rw [hint]
  exact hμ.tendstoMixed hU hF' φ hφ hφc hφU

/-- **Finite slot additivity.** The limit for a finite sum of slot functions is
the sum of the limits. -/
theorem IsBTLimit.sum_slot {Ω : Opens (ComplexModel n)} {v : Fin n → ComplexModel n → ℝ}
    (i₀ : Fin n) {N : ℕ} {s : Fin (N + 1) → ComplexModel n → ℝ}
    {ν : Fin (N + 1) → Measure (ComplexModel n)}
    (hν : ∀ b, IsBTLimit Ω (Function.update v i₀ (s b)) (ν b)) :
    IsBTLimit Ω (Function.update v i₀ fun z => ∑ b, s b z) (∑ b, ν b) := by
  induction N with
  | zero =>
    have hfun : (fun z => ∑ b : Fin 1, s b z) = s 0 := by
      funext z; exact Fin.sum_univ_one _
    rw [hfun, Fin.sum_univ_one]
    exact hν 0
  | succ N ih =>
    have hpart := ih (s := fun b => s (Fin.castSucc b)) (ν := fun b => ν (Fin.castSucc b))
      fun b => hν _
    obtain ⟨ρ, hρ⟩ := exists_isBTLimit_update_add i₀ hpart (hν (Fin.last _))
    have hρeq := IsBTLimit.add_slot i₀ hρ hpart (hν (Fin.last _))
    have hfun : (fun z => ∑ b, s b z) =
        fun z => (∑ b : Fin (N + 1), s (Fin.castSucc b) z) + s (Fin.last _) z := by
      funext z
      exact Fin.sum_univ_castSucc _
    rw [hfun, Fin.sum_univ_castSucc, ← hρeq]
    exact hρ

/-- Existence of the Bedford–Taylor limit after putting a smooth PSD function in
one slot of a tuple that already has a limit. -/
theorem IsBTLimit.exists_update_smoothPsd {Ω : Opens (ComplexModel n)}
    {v : Fin n → ComplexModel n → ℝ} (i₀ : Fin n) {a s : ComplexModel n → ℝ}
    {μ : Measure (ComplexModel n)} (hμ : IsBTLimit Ω (Function.update v i₀ a) μ)
    (hs : IsSmoothPsdOn Ω s) : ∃ ν, IsBTLimit Ω (Function.update v i₀ s) ν := by
  classical
  refine exists_isBTLimit fun U hU => ?_
  obtain ⟨F, hF, -⟩ := hμ.2.2 U hU
  have hUΩ : U ≤ Ω := subset_closure.trans hU.2
  have h := hF.update_smoothPsd i₀ ⟨hs.1.mono hUΩ, fun z hz => hs.2 z (hUΩ hz)⟩
  rw [Function.update_idem] at h
  exact ⟨_, h⟩

/-- A smooth PSD function plus a nonnegative multiple of `‖z‖²` is smooth PSD. -/
theorem IsSmoothPsdOn.add_smul_norm_sq {U : Opens (ComplexModel n)} {f : ComplexModel n → ℝ}
    (hf : IsSmoothPsdOn U f) {c : ℝ} (hc : 0 ≤ c) :
    IsSmoothPsdOn U fun z => f z + c * ‖z‖ ^ 2 := by
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top
  have hψ : ContDiff ℝ ∞ (fun z : ComplexModel n => c * ‖z‖ ^ 2) :=
    contDiff_const.mul (contDiff_norm_sq ℝ)
  refine ⟨hf.1.add hψ.contDiffOn, fun z hz => ?_⟩
  have hfz : ContDiffAt ℝ 2 f z := ((hf.1.contDiffAt (U.isOpen.mem_nhds hz))).of_le h2
  have hsplit : (fun z => f z + c * ‖z‖ ^ 2) =
      f + c • fun z : ComplexModel n => ‖z‖ ^ 2 := by
    funext y; simp
  have hcz : ContDiffAt ℝ 2 (c • fun z : ComplexModel n => ‖z‖ ^ 2) z :=
    ((contDiff_norm_sq ℝ).const_smul c).contDiffAt.of_le h2
  rw [hsplit, complexHessian_add hfz hcz,
    complexHessian_smul ((contDiff_norm_sq ℝ).contDiffAt.of_le h2), complexHessian_norm_sq]
  exact (hf.2 z hz).add (Matrix.PosSemidef.one.smul (by exact_mod_cast hc))

open scoped Distributions in
/-- **Integration by parts in the last slot against a regularized defect.** Two
tuples with Bedford–Taylor limits that differ only in the last slot have test
integrals differing by the pairing of `χ (a - b)` against the defect
`μ(φ + p) - μ(p)`, for an arbitrary regularizer `p` for which both limits exist
on the whole domain. -/
theorem exists_integral_sub_eq_slotDefect_last {Ω : Opens (ComplexModel n)}
    {v : Fin n → ComplexModel n → ℝ} {j : Fin n} (hlast : (j : ℕ) + 1 = n)
    {a b φ p : ComplexModel n → ℝ} {μa μb ν₁ ν₂ : Measure (ComplexModel n)}
    (hμa : IsBTLimit Ω (Function.update v j a) μa)
    (hμb : IsBTLimit Ω (Function.update v j b) μb)
    (hν₁ : IsBTLimit Ω (Function.update v j fun z => φ z + p z) ν₁)
    (hν₂ : IsBTLimit Ω (Function.update v j p) ν₂)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφΩ : tsupport φ ⊆ (Ω : Set (ComplexModel n))) :
    ∃ χ : ComplexModel n → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ (Ω : Set (ComplexModel n)) ∧ (∀ᶠ x in 𝓝ˢ (tsupport φ), χ x = 1) ∧
      (∫ z, φ z ∂μa) - ∫ z, φ z ∂μb =
        (∫ z, χ z * (a z - b z) ∂ν₁) - ∫ z, χ z * (a z - b z) ∂ν₂ := by
  classical
  obtain ⟨V, hVo, hKV, hVΩ, hVc⟩ :=
    exists_open_between_and_isCompact_closure hφc Ω.isOpen hφΩ
  set U : Opens (ComplexModel n) := ⟨V, hVo⟩ with hU_def
  have hU : RelativelyCompactIn U Ω := ⟨hVc, hVΩ⟩
  have hUΩ : (U : Set (ComplexModel n)) ⊆ Ω := subset_closure.trans hVΩ
  have hφU : tsupport φ ⊆ (U : Set (ComplexModel n)) := hKV
  -- a natural-number regularizing constant
  obtain ⟨C, hC0, hCpsd⟩ := exists_isSmoothPsdOn_add_norm_sq hφ hφc
  set N : ℕ := ⌈C⌉₊ with hN_def
  set Cn : ℝ := ((N + 1 : ℕ) : ℝ) with hCn_def
  have hCCn : C ≤ Cn := by
    rw [hCn_def]; push_cast; linarith [Nat.le_ceil C]
  have hNpsd : IsSmoothPsdOn ⊤ fun z => φ z + Cn * ‖z‖ ^ 2 := by
    have h := hCpsd.add_smul_norm_sq (sub_nonneg.mpr hCCn)
    have hfun : (fun z => (φ z + C * ‖z‖ ^ 2) + (Cn - C) * ‖z‖ ^ 2) =
        fun z => φ z + Cn * ‖z‖ ^ 2 := by funext z; ring
    rwa [hfun] at h
  have hsq : IsSmoothPsdOn Ω fun z : ComplexModel n => ‖z‖ ^ 2 := isSmoothPsdOn_norm_sq Ω
  have hNpsdΩ : IsSmoothPsdOn Ω fun z => φ z + Cn * ‖z‖ ^ 2 :=
    ⟨hNpsd.1.mono (subset_univ _), fun z _ => hNpsd.2 z trivial⟩
  obtain ⟨σ₁, hσ₁⟩ := hμa.exists_update_smoothPsd j hNpsdΩ
  obtain ⟨σ₂, hσ₂⟩ := hμa.exists_update_smoothPsd j hsq
  have hσ₃ : IsBTLimit Ω (Function.update v j fun z => Cn * ‖z‖ ^ 2)
      (∑ _b : Fin (N + 1), σ₂) := by
    have h := IsBTLimit.sum_slot j (s := fun _ : Fin (N + 1) => fun z : ComplexModel n => ‖z‖ ^ 2)
      (ν := fun _ => σ₂) fun _ => hσ₂
    have hfun : (fun z : ComplexModel n => ∑ _b : Fin (N + 1), ‖z‖ ^ 2) =
        fun z => Cn * ‖z‖ ^ 2 := by
      funext z; simp [hCn_def, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rwa [hfun] at h
  -- the cutoff
  obtain ⟨χ, hχ1, -⟩ := exists_testFunction_eq_one_nhds_compact hφc hφU
  have hχΩ : tsupport (χ : ComplexModel n → ℝ) ⊆ (Ω : Set (ComplexModel n)) :=
    χ.tsupport_subset.trans hUΩ
  -- the integration by parts identity on `U`
  have hibp := integral_sub_eq_ibp (U := U) (v := v) (i₀ := j) hlast
    (fun F hF => hμa.tendstoMixed hU hF) (fun F hF => hμb.tendstoMixed hU hF)
    ((hμa.2.2 U hU).imp fun _ h => h.1) ((hμb.2.2 U hU).imp fun _ h => h.1)
    hφ hφc hφU hNpsd χ hχ1
    (μ₁ := σ₁.restrict (U : Set (ComplexModel n)))
    (by rw [Measure.restrict_apply' U.isOpen.measurableSet]; simp)
    (fun K hK hKU => lt_of_le_of_lt (Measure.restrict_le_self K) (hσ₁.2.1 K hK (hKU.trans hUΩ)))
    (fun F hF => hσ₁.tendstoMixed_restrict hU hF)
    (μ₂ := σ₂.restrict (U : Set (ComplexModel n)))
    (by rw [Measure.restrict_apply' U.isOpen.measurableSet]; simp)
    (fun K hK hKU => lt_of_le_of_lt (Measure.restrict_le_self K) (hσ₂.2.1 K hK (hKU.trans hUΩ)))
    (fun F hF => hσ₂.tendstoMixed_restrict hU hF)
  refine ⟨χ, χ.contDiff, χ.hasCompactSupport, hχΩ, hχ1, ?_⟩
  -- the restrictions to `U` are invisible to integrands supported in `U`
  have hres : ∀ (w : ComplexModel n → ℝ) (ρ : Measure (ComplexModel n)),
      (∫ z in (U : Set (ComplexModel n)), χ z * w z ∂ρ) = ∫ z, χ z * w z ∂ρ := fun w ρ =>
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport fun h => hz (χ.tsupport_subset h), zero_mul]
  simp only [hres] at hibp
  -- integrability of the pairings
  have hdec : ∀ {c : ComplexModel n → ℝ} {μ : Measure (ComplexModel n)},
      IsBTLimit Ω (Function.update v j c) μ →
        ∀ ρ : Measure (ComplexModel n), (∀ K, IsCompact K → K ⊆ Ω → ρ K < ⊤) →
          Integrable (fun z => χ z * c z) ρ := by
    intro c μ hμ ρ hρ
    obtain ⟨F, hF, -⟩ := hμ.2.2 U hU
    have hG : IsDecApprox U c (F j) := by simpa using hF.1 j
    exact hG.integrable_mul (fun K hK hKU => hρ K hK (hKU.trans hUΩ)) χ.continuous
      χ.hasCompactSupport χ.tsupport_subset
  have hIa : ∀ ρ : Measure (ComplexModel n), (∀ K, IsCompact K → K ⊆ Ω → ρ K < ⊤) →
      Integrable (fun z => χ z * a z) ρ := hdec hμa
  have hIb : ∀ ρ : Measure (ComplexModel n), (∀ K, IsCompact K → K ⊆ Ω → ρ K < ⊤) →
      Integrable (fun z => χ z * b z) ρ := hdec hμb
  -- scaling the regularizer
  have hscale : ∀ w : ComplexModel n → ℝ, Integrable (fun z => χ z * w z) σ₂ →
      Cn * ∫ z, χ z * w z ∂σ₂ = ∫ z, χ z * w z ∂(∑ _b : Fin (N + 1), σ₂) := by
    intro w hw
    rw [integral_finsetSum_measure fun _ _ => hw]
    simp [hCn_def, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_sub, hscale a (hIa σ₂ hσ₂.2.1), hscale b (hIb σ₂ hσ₂.2.1)] at hibp
  -- changing the regularizer
  have hcongr := IsBTLimit.slotDefect_regularizer_congr j (φ := φ)
    (p := fun z => Cn * ‖z‖ ^ 2) (q := p) hσ₁ hσ₃ hν₁ hν₂
  have hsum : ∀ w : ComplexModel n → ℝ,
      (∀ ρ : Measure (ComplexModel n), (∀ K, IsCompact K → K ⊆ Ω → ρ K < ⊤) →
        Integrable (fun z => χ z * w z) ρ) →
      (∫ z, χ z * w z ∂σ₁) - ∫ z, χ z * w z ∂(∑ _b : Fin (N + 1), σ₂) =
        (∫ z, χ z * w z ∂ν₁) - ∫ z, χ z * w z ∂ν₂ := by
    intro w hw
    have hfin3 : ∀ K, IsCompact K → K ⊆ Ω → (∑ _b : Fin (N + 1), σ₂) K < ⊤ := hσ₃.2.1
    have e := congrArg (fun ρ : Measure (ComplexModel n) => ∫ z, χ z * w z ∂ρ) hcongr
    rw [integral_add_measure (hw _ hσ₁.2.1) (hw _ hν₂.2.1),
      integral_add_measure (hw _ hν₁.2.1) (hw _ hfin3)] at e
    linarith
  have hsplit : ∀ ρ : Measure (ComplexModel n), (∀ K, IsCompact K → K ⊆ Ω → ρ K < ⊤) →
      (∫ z, χ z * (a z - b z) ∂ρ) = (∫ z, χ z * a z ∂ρ) - ∫ z, χ z * b z ∂ρ := by
    intro ρ hρ
    rw [← integral_sub (hIa ρ hρ) (hIb ρ hρ)]
    congr 1; funext z; ring
  rw [hsplit ν₁ hν₁.2.1, hsplit ν₂ hν₂.2.1, hibp]
  linarith [hsum a hIa, hsum b hIb]

/-- **Integration by parts in an arbitrary slot against a regularized defect.**
The slot is moved to the last position first; Bedford–Taylor limits are
symmetric in the tuple. -/
theorem exists_integral_sub_eq_slotDefect {Ω : Opens (ComplexModel n)}
    {v : Fin n → ComplexModel n → ℝ} (i₀ : Fin n)
    {a b φ p : ComplexModel n → ℝ} {μa μb ν₁ ν₂ : Measure (ComplexModel n)}
    (hμa : IsBTLimit Ω (Function.update v i₀ a) μa)
    (hμb : IsBTLimit Ω (Function.update v i₀ b) μb)
    (hν₁ : IsBTLimit Ω (Function.update v i₀ fun z => φ z + p z) ν₁)
    (hν₂ : IsBTLimit Ω (Function.update v i₀ p) ν₂)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφΩ : tsupport φ ⊆ (Ω : Set (ComplexModel n))) :
    ∃ χ : ComplexModel n → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ (Ω : Set (ComplexModel n)) ∧ (∀ᶠ x in 𝓝ˢ (tsupport φ), χ x = 1) ∧
      (∫ z, φ z ∂μa) - ∫ z, φ z ∂μb =
        (∫ z, χ z * (a z - b z) ∂ν₁) - ∫ z, χ z * (a z - b z) ∂ν₂ := by
  classical
  set j : Fin n := lastSlot i₀ with hj
  set τ : Equiv.Perm (Fin n) := Equiv.swap i₀ j with hτ
  have hsymm : τ.symm i₀ = j := by simp [hτ]
  have hupd : ∀ c : ComplexModel n → ℝ,
      (fun i => Function.update v i₀ c (τ i)) = Function.update (fun i => v (τ i)) j c := by
    intro c; rw [← hsymm]; exact update_comp_perm i₀ c τ
  have hperm : ∀ {c : ComplexModel n → ℝ} {μ : Measure (ComplexModel n)},
      IsBTLimit Ω (Function.update v i₀ c) μ →
        IsBTLimit Ω (Function.update (fun i => v (τ i)) j c) μ := by
    intro c μ hμ
    rw [← hupd c]
    exact hμ.comp_perm τ
  exact exists_integral_sub_eq_slotDefect_last (lastSlot_val_succ i₀) (hperm hμa) (hperm hμb)
    (hperm hν₁) (hperm hν₂) hφ hφc hφΩ

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
