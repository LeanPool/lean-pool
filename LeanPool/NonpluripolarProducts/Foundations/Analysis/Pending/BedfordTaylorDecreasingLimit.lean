/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorCapacity
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorCollarSymmetry
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorBlockiInequality
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.MongeAmpere

/-!
# The Bedford–Taylor measure along a decreasing sequence

Let `w 0 ≥ w 1 ≥ ...` be locally bounded plurisubharmonic functions on an open
`Ω ⊆ ℂⁿ` decreasing pointwise to a locally bounded plurisubharmonic `v`.  This
module proves that the Bedford–Taylor measures converge:

  `∫ φ d(ddᶜ w i)ⁿ → ∫ φ d(ddᶜ v)ⁿ` for every compactly supported continuous
  test function `φ` with `tsupport φ ⊆ Ω`.

This is the diagonal top-degree case of [Błocki, Theorem 2.1.5](https://gamma.im.uj.edu.pl/~blocki/publ/ln/wykl.pdf#page=36)
and Demailly, CADG III.3.7. It supplies the local convergence needed to pass
from decreasing smooth approximations of boundary data to upper semicontinuous
data in the Bedford–Taylor balayage used in [Xia's balayage lemma](https://github.com/MingchenXia/SGPT/blob/4390e77497d699ac3a4f878b97c34fc867513add/author/chapter_npp.tex#L662-L688).

## The proof

`HolomorphicPullback.exists_decreasingMollifierApproximation` gives, on a
relatively compact `A`, a decreasing smooth `G i : ℕ → _` with `G i k ↓ₖ w i`.
Everything rests on selecting one index `k i` per stage so that the **diagonal**
`G i (k i)` is again decreasing in `i`, up to a summable constant — and a
constant does not change a complex Hessian, so the correction is free.

Selecting it is a Dini argument **with slack**: on a compact `K`,

  `G (i+1) k z < G i (k i) z + 4⁻ⁱ` for all large `k` and all `z ∈ K`.

Without the slack this is false in general, because the pointwise limit
`w (i+1)` is merely upper semicontinuous and may meet `G i (k i)`; with it, the
limit inequality `w (i+1) ≤ w i ≤ G i (k i)` is *strict* against the shifted
target, and the existing Dini theorem
`Pending.BedfordTaylor.eventually_forall_lt_of_antitone` applies to the
differences `G (i+1) k − G i (k i)`.

The index is taken large enough for two further tolerances, both of which are
also satisfied by all large indices: `∫_B (G i k - w i) < 4⁻ⁱ`, which forces the
diagonal to converge to `v` in `L¹` and hence almost everywhere, and a tolerance
on the test integral, which transports the limit measure back to `μ i`.  Almost
everywhere convergence is upgraded to everywhere convergence by
`FirstPass.MongeAmpere.tendsto_everywhere_of_ae_of_antitone_psh`, so the
diagonal is a genuine `IsDecApprox` of `v` and `IsBTLimit.tendstoMixed` applies
to it on both sides.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace Metric
open scoped Topology ContDiff ENNReal Distributions

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

variable {n : ℕ}

/-! ### Dini's theorem with slack -/

/-- **Dini with slack.**  A sequence decreasing pointwise to `p` on a compact
set eventually lies below `q + c` uniformly there, as soon as `p ≤ q` on that
set and `c > 0`.  Neither `p` nor `q` is assumed to be the continuous limit of
anything: the slack `c` is what replaces continuity of the limit in Dini's
theorem.

This is `Pending.BedfordTaylor.eventually_forall_lt_of_antitone` applied to the
differences `g k − q`, restated in the `∃ N, ∀ k ≥ N` form the diagonal
construction below consumes. -/
theorem exists_forall_lt_add_of_antitone {X : Type*} [TopologicalSpace X]
    [T2Space X] {K : Set X} (hK : IsCompact K)
    {g : ℕ → X → ℝ} {p q : X → ℝ}
    (hg : ∀ k, ContinuousOn (g k) K) (hq : ContinuousOn q K)
    (hanti : ∀ z ∈ K, Antitone fun k ↦ g k z)
    (hlim : ∀ z ∈ K, Tendsto (fun k ↦ g k z) atTop (𝓝 (p z)))
    (hpq : ∀ z ∈ K, p z ≤ q z) {c : ℝ} (hc : 0 < c) :
    ∃ N, ∀ k, N ≤ k → ∀ z ∈ K, g k z < q z + c := by
  have hdini := eventually_forall_lt_of_antitone (ε := c) hK
    (g := fun k z ↦ g k z - q z) (fun k ↦ (hg k).sub hq)
    (fun z hz k l hkl ↦ sub_le_sub_right (hanti z hz hkl) _)
    (fun z hz ↦ by
      have h1 : Tendsto (fun k ↦ g k z - q z) atTop (𝓝 (p z - q z)) :=
        (hlim z hz).sub_const _
      have h2 : p z - q z < c := by
        have := hpq z hz
        linarith
      exact h1.eventually_lt_const h2)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hdini
  exact ⟨N, fun k hk z hz ↦ by have := hN k hk z hz; linarith⟩

/-! ### Elementary facts about the approximations -/

/-- A decreasing approximation dominates its limit. -/
theorem IsDecreasingApproximation.le_apply {A : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} {f : ℕ → ComplexModel n → ℝ}
    (hf : IsDecreasingApproximation A u f) {z : ComplexModel n} (hz : z ∈ A)
    (k : ℕ) : u z ≤ f k z :=
  (hf.2.1 z hz).le_of_tendsto (hf.2.2 z hz) k

/-- Restriction of a decreasing approximation to a smaller open set. -/
theorem IsDecreasingApproximation.mono {A B : Opens (ComplexModel n)}
    {u : ComplexModel n → ℝ} {f : ℕ → ComplexModel n → ℝ}
    (hf : IsDecreasingApproximation A u f) (hBA : B ≤ A) :
    IsDecreasingApproximation B u f :=
  ⟨fun j ↦ ⟨(hf.1 j).1.mono hBA, (hf.1 j).2.1.mono hBA, fun z hz ↦ (hf.1 j).2.2 z (hBA hz)⟩,
    fun z hz ↦ hf.2.1 z (hBA hz), fun z hz ↦ hf.2.2 z (hBA hz)⟩

/-- A constant is smooth and pluriharmonic. -/
theorem isSmoothPluriharmonicOn_const (A : Opens (ComplexModel n)) (c : ℝ) :
    IsSmoothPluriharmonicOn A (fun _ ↦ c) :=
  ⟨contDiff_const.contDiffOn, fun z _ ↦ complexHessian_const c z⟩

/-! ### The diagonal approximation -/

private theorem ae_tendsto_of_integral_sub_tendsto_zero
    {B : Opens (ComplexModel n)} {F : ℕ → ComplexModel n → ℝ} {v : ComplexModel n → ℝ}
    (hFanti : ∀ z ∈ B, Antitone fun i ↦ F i z) (hvF : ∀ z ∈ B, ∀ i, v z ≤ F i z)
    (hdLI : ∀ i, IntegrableOn (fun z ↦ F i z - v z) B volume)
    (hlimit : Tendsto (fun i ↦ ∫ z in (B : Set (ComplexModel n)), (F i z - v z)) atTop (𝓝 0)) :
    ∀ᵐ z ∂(volume.restrict (B : Set (ComplexModel n))),
      Tendsto (fun i ↦ F i z) atTop (𝓝 (v z)) := by
  have hBmeas := B.isOpen.measurableSet
  set D : ComplexModel n → ℝ := fun z ↦ ⨅ i, (F i z - v z) with hD_def
  have hdanti : ∀ z ∈ (B : Set (ComplexModel n)), Antitone fun i ↦ F i z - v z :=
    fun z hz _ _ hij ↦ sub_le_sub_right (hFanti z hz hij) _
  have hdnonneg : ∀ z ∈ (B : Set (ComplexModel n)), ∀ i, 0 ≤ F i z - v z :=
    fun z hz i ↦ sub_nonneg.2 (hvF z hz i)
  have hdtend : ∀ z ∈ (B : Set (ComplexModel n)),
      Tendsto (fun i ↦ F i z - v z) atTop (𝓝 (D z)) := fun z hz ↦
    tendsto_atTop_ciInf (hdanti z hz) ⟨0, by rintro _ ⟨i, rfl⟩; exact hdnonneg z hz i⟩
  have hDmeas : AEStronglyMeasurable D (volume.restrict (B : Set (ComplexModel n))) :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun i ↦ (hdLI i).aestronglyMeasurable)
      ((ae_restrict_iff' hBmeas).2 (Eventually.of_forall fun z hz ↦ hdtend z hz))
  have hDnonneg : ∀ᵐ z ∂(volume.restrict (B : Set (ComplexModel n))), 0 ≤ D z :=
    (ae_restrict_iff' hBmeas).2 (Eventually.of_forall fun z hz ↦
      le_ciInf fun i ↦ hdnonneg z hz i)
  have hDle : ∀ᵐ z ∂(volume.restrict (B : Set (ComplexModel n))),
      ‖D z‖ ≤ F 0 z - v z := by
    filter_upwards [hDnonneg, (ae_restrict_iff' hBmeas).2
      (Eventually.of_forall fun z (hz : z ∈ (B : Set (ComplexModel n))) ↦ hz)] with z h0 hzB
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    exact ciInf_le ⟨0, by rintro _ ⟨i, rfl⟩; exact hdnonneg z hzB i⟩ 0
  have hDLI : IntegrableOn D (B : Set (ComplexModel n)) volume :=
    Integrable.mono' (hdLI 0) hDmeas hDle
  have hDint : Tendsto (fun i ↦ ∫ z in (B : Set (ComplexModel n)), (F i z - v z)) atTop
      (𝓝 (∫ z in (B : Set (ComplexModel n)), D z)) := by
    refine tendsto_integral_of_dominated_convergence (fun z ↦ F 0 z - v z)
      (fun i ↦ (hdLI i).aestronglyMeasurable) (hdLI 0) (fun i ↦ ?_)
      ((ae_restrict_iff' hBmeas).2 (Eventually.of_forall fun z hz ↦ hdtend z hz))
    refine (ae_restrict_iff' hBmeas).2 (Eventually.of_forall fun z hz ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hdnonneg z hz i)]
    exact sub_le_sub_right (hFanti z hz (Nat.zero_le i)) _
  have hDzero : ∫ z in (B : Set (ComplexModel n)), D z = 0 :=
    tendsto_nhds_unique hDint hlimit
  have hDae : D =ᵐ[volume.restrict (B : Set (ComplexModel n))] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hDnonneg hDLI).mp hDzero
  filter_upwards [hDae, (ae_restrict_iff' hBmeas).2
    (Eventually.of_forall fun z (hz : z ∈ (B : Set (ComplexModel n))) ↦ hz)] with z h0 hzB
  have h1 := hdtend z hzB
  rw [show D z = 0 from h0] at h1
  simpa using h1.add_const (v z)

/-- **The diagonal of a decreasing family of decreasing approximations.**
Let `w i ↓ v` be locally bounded plurisubharmonic on `Ω`, and let `G i` be a
decreasing smooth approximation of `w i` on a relatively compact `A`.  Then one
index `k i` per stage can be chosen, as large as any prescribed `N i`, so that

  `F i := G i (k i) + 2·4⁻ⁱ`

is a decreasing smooth approximation of `v` on a relatively compact `B ⋐ A`.

The constant `2·4⁻ⁱ` is invisible to every Monge--Ampère statement, a complex
Hessian being unchanged by adding a constant; it is what buys the strictness
that a plain Dini argument does not have, the limits `w i` being merely upper
semicontinuous.  The freedom to take `k i` beyond a prescribed `N i` is what
lets a caller also demand that the diagonal carry the mass of `w i`. -/
theorem exists_isDecApprox_diagonal
    {Ω A B : Opens (ComplexModel n)} (hAΩ : RelativelyCompactIn A Ω)
    (hBA : RelativelyCompactIn B A)
    {w : ℕ → ComplexModel n → ℝ} {v : ComplexModel n → ℝ}
    (hw : ∀ i, IsLocallyBoundedPshOn Ω (w i)) (hv : IsLocallyBoundedPshOn Ω v)
    (hanti : ∀ z ∈ Ω, Antitone fun i ↦ w i z)
    (hlim : ∀ z ∈ Ω, Tendsto (fun i ↦ w i z) atTop (𝓝 (v z)))
    {G : ℕ → ℕ → ComplexModel n → ℝ}
    (hG : ∀ i, IsDecreasingApproximation A (w i) (G i))
    (N : ℕ → ℕ) :
    ∃ k : ℕ → ℕ, (∀ i, N i ≤ k i) ∧
      IsDecApprox B v (fun i z ↦ G i (k i) z + 2 * ((4 : ℝ)⁻¹ ^ i)) := by
  classical
  have hAΩ' : A ≤ Ω := subset_closure.trans hAΩ.2
  have hBA' : B ≤ A := subset_closure.trans hBA.2
  have hBΩ' : B ≤ Ω := hBA'.trans hAΩ'
  set K : Set (ComplexModel n) := closure (B : Set (ComplexModel n)) with hK_def
  have hK : IsCompact K := hBA.1
  have hKA : K ⊆ A := hBA.2
  have hBK : (B : Set (ComplexModel n)) ⊆ K := subset_closure
  set c : ℕ → ℝ := fun i ↦ (4 : ℝ)⁻¹ ^ i with hc_def
  have hc : ∀ i, 0 < c i := fun i ↦ by positivity
  have hcsucc : ∀ i, c (i + 1) = c i / 4 := by
    intro i
    simp only [hc_def, pow_succ]
    ring
  have hvw : ∀ z ∈ (Ω : Set (ComplexModel n)), ∀ i, v z ≤ w i z :=
    fun z hz i ↦ (hanti z hz).le_of_tendsto (hlim z hz) i
  have hwG : ∀ i, ∀ z ∈ (A : Set (ComplexModel n)), ∀ m, w i z ≤ G i m z :=
    fun i z hz m ↦ IsDecreasingApproximation.le_apply (hG i) hz m
  -- measure-theoretic preliminaries on `B`
  have hBmeas : MeasurableSet (B : Set (ComplexModel n)) := B.isOpen.measurableSet
  have hBvol : volume (B : Set (ComplexModel n)) < ⊤ :=
    lt_of_le_of_lt (measure_mono hBK) hK.measure_lt_top
  have hwLI : ∀ i, IntegrableOn (w i) (B : Set (ComplexModel n)) volume := fun i ↦
    ((locallyIntegrableOn_of_plurisubharmonicOn_real (hw i).1).integrableOn_compact_subset
      (hKA.trans hAΩ') hK).mono_set hBK
  have hvLI : IntegrableOn v (B : Set (ComplexModel n)) volume :=
    ((locallyIntegrableOn_of_plurisubharmonicOn_real hv.1).integrableOn_compact_subset
      (hKA.trans hAΩ') hK).mono_set hBK
  have hGcont : ∀ i m, ContinuousOn (G i m) (A : Set (ComplexModel n)) := fun i m ↦
    ((hG i).1 m).1.continuousOn
  have hGLI : ∀ i m, IntegrableOn (G i m) (B : Set (ComplexModel n)) volume := fun i m ↦
    (((hGcont i m).mono hKA).integrableOn_compact hK).mono_set hBK
  have hconstLI : ∀ r : ℝ, IntegrableOn (fun _ : ComplexModel n ↦ r)
      (B : Set (ComplexModel n)) volume := fun r ↦
    ((continuousOn_const (c := r)).integrableOn_compact hK).mono_set hBK
  -- STEP 1: the Dini threshold with slack
  have hT1 : ∀ i p : ℕ, ∃ M, ∀ m, M ≤ m → ∀ z ∈ K, G (i + 1) m z < G i p z + c i := by
    intro i p
    refine exists_forall_lt_add_of_antitone hK
      (fun m ↦ (hGcont (i + 1) m).mono hKA) ((hGcont i p).mono hKA)
      (fun z hz ↦ (hG (i + 1)).2.1 z (hKA hz)) (fun z hz ↦ (hG (i + 1)).2.2 z (hKA hz))
      (fun z hz ↦ ?_) (hc i)
    exact le_trans (hanti z (hAΩ' (hKA hz)) (Nat.le_succ i)) (hwG i z (hKA hz) p)
  choose T1 hT1 using hT1
  -- STEP 2: the `L¹` threshold
  have hT2 : ∀ i : ℕ, ∃ M, ∀ m, M ≤ m →
      ∫ z in (B : Set (ComplexModel n)), (G i m z - w i z) < c i := by
    intro i
    have hbound : ∀ m, ∀ᵐ z ∂(volume.restrict (B : Set (ComplexModel n))),
        ‖G i m z - w i z‖ ≤ G i 0 z - w i z := by
      intro m
      refine (ae_restrict_iff' hBmeas).2 (Eventually.of_forall fun z hz ↦ ?_)
      have hzA : z ∈ (A : Set (ComplexModel n)) := hBA' hz
      have h1 : w i z ≤ G i m z := hwG i z hzA m
      have h2 : G i m z ≤ G i 0 z := (hG i).2.1 z hzA (Nat.zero_le m)
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    have hptw : ∀ᵐ z ∂(volume.restrict (B : Set (ComplexModel n))),
        Tendsto (fun m ↦ G i m z - w i z) atTop (𝓝 0) := by
      refine (ae_restrict_iff' hBmeas).2 (Eventually.of_forall fun z hz ↦ ?_)
      simpa using ((hG i).2.2 z (hBA' hz)).sub_const (w i z)
    have hlimint : Tendsto
        (fun m ↦ ∫ z in (B : Set (ComplexModel n)), (G i m z - w i z)) atTop (𝓝 0) := by
      have h := tendsto_integral_of_dominated_convergence
        (μ := volume.restrict (B : Set (ComplexModel n)))
        (F := fun m z ↦ G i m z - w i z) (f := fun _ ↦ (0 : ℝ))
        (bound := fun z ↦ G i 0 z - w i z)
        (fun m ↦ ((hGLI i m).sub (hwLI i)).aestronglyMeasurable)
        ((hGLI i 0).sub (hwLI i)) hbound hptw
      simpa using h
    exact eventually_atTop.mp (hlimint.eventually_lt_const (hc i))
  choose T2 hT2 using hT2
  -- STEP 3: the diagonal index
  set kk : ℕ → ℕ := fun i ↦ Nat.rec (max (N 0) (T2 0))
    (fun i prev ↦ max (max (N (i + 1)) (T2 (i + 1))) (T1 i prev)) i with hkk_def
  have hkks : ∀ i, kk (i + 1) = max (max (N (i + 1)) (T2 (i + 1))) (T1 i (kk i)) :=
    fun i ↦ rfl
  have hkN : ∀ i, N i ≤ kk i := by
    intro i
    cases i with
    | zero => exact le_max_left _ _
    | succ i => rw [hkks i]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hkT2 : ∀ i, T2 i ≤ kk i := by
    intro i
    cases i with
    | zero => exact le_max_right _ _
    | succ i => rw [hkks i]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hkT1 : ∀ i, T1 i (kk i) ≤ kk (i + 1) := by
    intro i; rw [hkks i]; exact le_max_right _ _
  set F : ℕ → ComplexModel n → ℝ := fun i z ↦ G i (kk i) z + 2 * c i with hF_def
  -- STEP 4: the diagonal is a decreasing smooth approximation of `v`
  have hFsmooth : ∀ i, IsSmoothPsdOn B (F i) := by
    intro i
    have hcd : ContDiffOn ℝ ∞ (G i (kk i)) (B : Set (ComplexModel n)) :=
      ((hG i).1 (kk i)).1.mono hBA'
    refine ⟨hcd.add contDiffOn_const, fun z hz ↦ ?_⟩
    have hph : IsSmoothPluriharmonicOn B (fun _ : ComplexModel n ↦ 2 * c i) :=
      isSmoothPluriharmonicOn_const B (2 * c i)
    have hhess : complexHessian (F i) z = complexHessian (G i (kk i)) z :=
      complexHessian_add_of_isSmoothPluriharmonicOn hcd hph hz
    rw [hhess]
    exact ((hG i).1 (kk i)).2.2 z (hBA' hz)
  have hFanti : ∀ z ∈ (B : Set (ComplexModel n)), Antitone fun i ↦ F i z := by
    intro z hz
    refine antitone_nat_of_succ_le fun i ↦ ?_
    have h1 : G (i + 1) (kk (i + 1)) z < G i (kk i) z + c i :=
      hT1 i (kk i) (kk (i + 1)) (hkT1 i) z (hBK hz)
    have h2 : c (i + 1) = c i / 4 := hcsucc i
    have h3 := hc i
    simp only [hF_def]
    rw [h2]
    linarith
  have hvF : ∀ z ∈ (B : Set (ComplexModel n)), ∀ i, v z ≤ F i z := by
    intro z hz i
    have h1 : v z ≤ w i z := hvw z (hBΩ' hz) i
    have h2 : w i z ≤ G i (kk i) z := hwG i z (hBA' hz) (kk i)
    have h3 := (hc i).le
    simp only [hF_def]
    linarith
  have hFLI : ∀ i, IntegrableOn (F i) (B : Set (ComplexModel n)) volume := fun i ↦
    (hGLI i (kk i)).add (hconstLI (2 * c i))
  have hdLI : ∀ i, IntegrableOn (fun z ↦ F i z - v z) (B : Set (ComplexModel n)) volume :=
    fun i ↦ (hFLI i).sub hvLI
  -- the diagonal converges to `v` in `L¹`
  have hwvint : Tendsto (fun i ↦ ∫ z in (B : Set (ComplexModel n)), (w i z - v z)) atTop
      (𝓝 0) := by
    have hbound : ∀ i, ∀ᵐ z ∂(volume.restrict (B : Set (ComplexModel n))),
        ‖w i z - v z‖ ≤ w 0 z - v z := by
      intro i
      refine (ae_restrict_iff' hBmeas).2 (Eventually.of_forall fun z hz ↦ ?_)
      have hzΩ : z ∈ (Ω : Set (ComplexModel n)) := hBΩ' hz
      have h1 : v z ≤ w i z := hvw z hzΩ i
      have h2 : w i z ≤ w 0 z := hanti z hzΩ (Nat.zero_le i)
      rw [Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    have hptw : ∀ᵐ z ∂(volume.restrict (B : Set (ComplexModel n))),
        Tendsto (fun i ↦ w i z - v z) atTop (𝓝 0) := by
      refine (ae_restrict_iff' hBmeas).2 (Eventually.of_forall fun z hz ↦ ?_)
      simpa using (hlim z (hBΩ' hz)).sub_const (v z)
    have h := tendsto_integral_of_dominated_convergence
      (μ := volume.restrict (B : Set (ComplexModel n)))
      (F := fun i z ↦ w i z - v z) (f := fun _ ↦ (0 : ℝ))
      (bound := fun z ↦ w 0 z - v z)
      (fun i ↦ ((hwLI i).sub hvLI).aestronglyMeasurable)
      ((hwLI 0).sub hvLI) hbound hptw
    simpa using h
  have hsplit : ∀ i, ∫ z in (B : Set (ComplexModel n)), (F i z - v z) =
      (∫ z in (B : Set (ComplexModel n)), (G i (kk i) z - w i z)) +
        (∫ z in (B : Set (ComplexModel n)), (w i z - v z)) +
        volume.real (B : Set (ComplexModel n)) * (2 * c i) := by
    intro i
    have step1 : ∫ z in (B : Set (ComplexModel n)), (F i z - v z) =
        ∫ z in (B : Set (ComplexModel n)),
          ((G i (kk i) z - w i z) + ((w i z - v z) + 2 * c i)) := by
      congr 1
      funext z
      simp only [hF_def]
      ring
    have step2 : ∫ z in (B : Set (ComplexModel n)),
          ((G i (kk i) z - w i z) + ((w i z - v z) + 2 * c i)) =
        (∫ z in (B : Set (ComplexModel n)), (G i (kk i) z - w i z)) +
          ∫ z in (B : Set (ComplexModel n)), ((w i z - v z) + 2 * c i) :=
      integral_add ((hGLI i (kk i)).sub (hwLI i))
        (((hwLI i).sub hvLI).add (hconstLI (2 * c i)))
    have step3 : ∫ z in (B : Set (ComplexModel n)), ((w i z - v z) + 2 * c i) =
        (∫ z in (B : Set (ComplexModel n)), (w i z - v z)) +
          ∫ _z in (B : Set (ComplexModel n)), (2 * c i) :=
      integral_add ((hwLI i).sub hvLI) (hconstLI (2 * c i))
    have step4 : ∫ _z in (B : Set (ComplexModel n)), (2 * c i) =
        volume.real (B : Set (ComplexModel n)) * (2 * c i) := by
      rw [setIntegral_const, smul_eq_mul]
    rw [step1, step2, step3, step4]
    ring
  have hFv0 : Tendsto (fun i ↦ ∫ z in (B : Set (ComplexModel n)), (F i z - v z)) atTop
      (𝓝 0) := by
    have hle : ∀ i, ∫ z in (B : Set (ComplexModel n)), (F i z - v z) ≤
        c i + (∫ z in (B : Set (ComplexModel n)), (w i z - v z)) +
          volume.real (B : Set (ComplexModel n)) * (2 * c i) := by
      intro i
      rw [hsplit i]
      have := hT2 i (kk i) (hkT2 i)
      linarith
    have hge : ∀ i, 0 ≤ ∫ z in (B : Set (ComplexModel n)), (F i z - v z) := by
      intro i
      refine setIntegral_nonneg hBmeas fun z hz ↦ sub_nonneg.mpr (hvF z hz i)
    have hcz : Tendsto c atTop (𝓝 0) := by
      simpa [hc_def] using tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0:ℝ) ≤ (4:ℝ)⁻¹) (by norm_num : (4:ℝ)⁻¹ < 1)
    have hupper : Tendsto (fun i ↦ c i +
        (∫ z in (B : Set (ComplexModel n)), (w i z - v z)) +
          (volume (B : Set (ComplexModel n))).toReal * (2 * c i)) atTop (𝓝 0) := by
      have := (hcz.add hwvint).add
        ((hcz.const_mul (2 : ℝ)).const_mul
          ((volume (B : Set (ComplexModel n))).toReal))
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper hge hle
  have hae := ae_tendsto_of_integral_sub_tendsto_zero hFanti hvF hdLI hFv0
  have hFpsh : ∀ i, PlurisubharmonicOn (fun z ↦ ((F i z : ℝ) : EReal)) B :=
    fun i ↦ (hFsmooth i).plurisubharmonicOn
  have hFtend : ∀ z ∈ (B : Set (ComplexModel n)),
      Tendsto (fun i ↦ F i z) atTop (𝓝 (v z)) :=
    tendsto_everywhere_of_ae_of_antitone_psh (hv.1.mono hBΩ') hFpsh hFanti hae
  refine ⟨kk, hkN, hFsmooth, hFanti, hFtend, fun K' hK' hK'B ↦ ?_⟩
  obtain ⟨C, hC⟩ := IsLocallyBoundedPshOn.exists_abs_le hv hK' (hK'B.trans hBΩ')
  exact ⟨-C, by rintro _ ⟨z, hz, rfl⟩; exact neg_le_of_abs_le (hC z hz)⟩

/-! ### The convergence theorem -/

/-- **Bedford--Taylor convergence along a decreasing sequence.**  If locally
bounded plurisubharmonic functions `w i` decrease pointwise to a locally bounded
plurisubharmonic `v` on `Ω`, then their Bedford--Taylor measures converge weakly
against every compactly supported continuous test function on `Ω`.

This is the diagonal top-degree measure consequence of [Błocki, Theorem 2.1.5](https://gamma.im.uj.edu.pl/~blocki/publ/ln/wykl.pdf#page=36).
The proof extends smooth test convergence to continuous tests using locally uniform mass bounds.

The whole proof is the diagonal of `exists_isDecApprox_diagonal`: it is
simultaneously a decreasing approximation of `v`, so the *right*-hand side is
its limit, and a member of the approximating sequence of each `w i`, so the
*left*-hand side is within `4⁻ⁱ` of it. -/
theorem tendsto_integral_of_antitone_isBTLimit
    {Ω : Opens (ComplexModel n)}
    {w : ℕ → ComplexModel n → ℝ} {v : ComplexModel n → ℝ}
    (hw : ∀ i, IsLocallyBoundedPshOn Ω (w i)) (hv : IsLocallyBoundedPshOn Ω v)
    (hanti : ∀ z ∈ Ω, Antitone fun i ↦ w i z)
    (hlim : ∀ z ∈ Ω, Tendsto (fun i ↦ w i z) atTop (𝓝 (v z)))
    {mu : ℕ → Measure (ComplexModel n)} {nu : Measure (ComplexModel n)}
    (hmu : ∀ i, IsBTLimit Ω (fun _ ↦ w i) (mu i)) (hnu : IsBTLimit Ω (fun _ ↦ v) nu)
    {φ : ComplexModel n → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφΩ : tsupport φ ⊆ Ω) :
    Tendsto (fun i ↦ ∫ z, φ z ∂(mu i)) atTop (𝓝 (∫ z, φ z ∂nu)) := by
  classical
  obtain ⟨δ, hδ, hδΩ⟩ := hφc.exists_cthickening_subset_open Ω.isOpen hφΩ
  set A : Opens (ComplexModel n) := ⟨thickening δ (tsupport φ), isOpen_thickening⟩ with hA_def
  set B : Opens (ComplexModel n) :=
    ⟨thickening (δ / 2) (tsupport φ), isOpen_thickening⟩ with hB_def
  have hclA : closure (A : Set (ComplexModel n)) ⊆ cthickening δ (tsupport φ) :=
    closure_thickening_subset_cthickening δ (tsupport φ)
  have hcompA : IsCompact (closure (A : Set (ComplexModel n))) := by
    refine IsCompact.of_isClosed_subset ?_ isClosed_closure hclA
    exact hφc.cthickening
  have hAΩ : RelativelyCompactIn A Ω := ⟨hcompA, hclA.trans hδΩ⟩
  have hclB : closure (B : Set (ComplexModel n)) ⊆ cthickening (δ / 2) (tsupport φ) :=
    closure_thickening_subset_cthickening (δ / 2) (tsupport φ)
  have hcompB : IsCompact (closure (B : Set (ComplexModel n))) := by
    refine IsCompact.of_isClosed_subset ?_ isClosed_closure hclB
    exact hφc.cthickening
  have hBA : RelativelyCompactIn B A :=
    ⟨hcompB, hclB.trans (cthickening_subset_thickening' hδ (by linarith) (tsupport φ))⟩
  have hBA' : B ≤ A := subset_closure.trans hBA.2
  have hφB : tsupport φ ⊆ (B : Set (ComplexModel n)) :=
    self_subset_thickening (by linarith) (tsupport φ)
  have hBΩ : RelativelyCompactIn B Ω :=
    ⟨hcompB, hBA.2.trans (subset_closure.trans hAΩ.2)⟩
  have hBΩ' : B ≤ Ω := subset_closure.trans hBΩ.2
  choose G hG using fun i ↦
    HolomorphicPullback.exists_decreasingMollifierApproximation (hw i) hAΩ
  -- the tolerance on the test integral against the measure of the `i`-th member
  have hNex : ∀ i : ℕ, ∃ M, ∀ m, M ≤ m →
      |(∫ z, φ z * smoothDensity (G i m) z) - ∫ z, φ z ∂(mu i)| < (4 : ℝ)⁻¹ ^ i := by
    intro i
    have hadm : IsAdmissible n B (fun _ ↦ w i) (fun _ ↦ G i) :=
      isAdmissible_diagonal (hw i) hBΩ' (IsDecreasingApproximation.mono (hG i) hBA')
    have h := (hmu i).tendstoMixed hBΩ hadm φ hφ hφc hφB
    simp only [mixedDensity_diagonal] at h
    have h2 : Tendsto (fun m ↦ |(∫ z, φ z * smoothDensity (G i m) z) - ∫ z, φ z ∂(mu i)|)
        atTop (𝓝 0) := by
      simpa using (h.sub_const (∫ z, φ z ∂(mu i))).abs
    exact eventually_atTop.mp (h2.eventually_lt_const (by positivity))
  choose N hN using hNex
  obtain ⟨k, hkN, hdec⟩ := exists_isDecApprox_diagonal hAΩ hBA hw hv hanti hlim hG N
  -- the diagonal computes the limit measure
  have hadm : IsAdmissible n B (fun _ ↦ v)
      (fun _ i z ↦ G i (k i) z + 2 * ((4 : ℝ)⁻¹ ^ i)) :=
    ⟨fun _ ↦ hdec, fun i hi ↦ absurd i.isLt (not_lt.mpr hi)⟩
  have hmix := hnu.tendstoMixed hBΩ hadm φ hφ hφc hφB
  have hdens : ∀ i, (∫ z, φ z *
      mixedDensity (fun _ : Fin n ↦ fun y ↦ G i (k i) y + 2 * ((4 : ℝ)⁻¹ ^ i)) z) =
      ∫ z, φ z * smoothDensity (G i (k i)) z := by
    intro i
    congr 1
    funext z
    by_cases hz : z ∈ (B : Set (ComplexModel n))
    · have hcd : ContDiffOn ℝ ∞ (G i (k i)) (B : Set (ComplexModel n)) :=
        ((hG i).1 (k i)).1.mono hBA'
      have hhess : ∀ _j : Fin n,
          complexHessian (fun y ↦ G i (k i) y + 2 * ((4 : ℝ)⁻¹ ^ i)) z =
            complexHessian (G i (k i)) z := fun _ ↦
        complexHessian_add_of_isSmoothPluriharmonicOn hcd
          (isSmoothPluriharmonicOn_const B (2 * ((4 : ℝ)⁻¹ ^ i))) hz
      rw [mixedDensity_congr_hessian (g := fun _ : Fin n ↦ G i (k i)) hhess,
        mixedDensity_diagonal]
    · simp [image_eq_zero_of_notMem_tsupport fun h' ↦ hz (hφB h')]
  have h1 : Tendsto (fun i ↦ ∫ z, φ z * smoothDensity (G i (k i)) z) atTop
      (𝓝 (∫ z, φ z ∂nu)) := hmix.congr fun i ↦ hdens i
  have h2 : Tendsto (fun i ↦ (∫ z, φ z ∂(mu i)) -
      ∫ z, φ z * smoothDensity (G i (k i)) z) atTop (𝓝 0) := by
    have hb : Tendsto (fun i : ℕ ↦ (4 : ℝ)⁻¹ ^ i) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ (4 : ℝ)⁻¹) (by norm_num : (4 : ℝ)⁻¹ < 1)
    refine squeeze_zero_norm ?_ hb
    intro i
    have hi := hN i (k i) (hkN i)
    rw [Real.norm_eq_abs, abs_sub_comm]
    exact hi.le
  have h3 := h2.add h1
  simpa using h3

/-- **Balayage passes to decreasing limits.**  If the Bedford--Taylor measure of
every member of a decreasing sequence of locally bounded plurisubharmonic
functions vanishes, so does that of the limit.

This is the form in which the theorem is consumed: Błocki solves the homogeneous
Monge--Ampère equation for smooth boundary data (here
`Pending.BedfordTaylor.IsPerronData.eq_zero_of_isBTLimit_perronEnvelope_of_contDiff`)
and reaches bounded upper semicontinuous data by decreasing regularization of the
data, which decreases the envelopes. -/
theorem eq_zero_of_antitone_of_isBTLimit
    {Ω : Opens (ComplexModel n)}
    {w : ℕ → ComplexModel n → ℝ} {v : ComplexModel n → ℝ}
    (hw : ∀ i, IsLocallyBoundedPshOn Ω (w i)) (hv : IsLocallyBoundedPshOn Ω v)
    (hanti : ∀ z ∈ Ω, Antitone fun i ↦ w i z)
    (hlim : ∀ z ∈ Ω, Tendsto (fun i ↦ w i z) atTop (𝓝 (v z)))
    {mu : ℕ → Measure (ComplexModel n)} {nu : Measure (ComplexModel n)}
    (hmu : ∀ i, IsBTLimit Ω (fun _ ↦ w i) (mu i)) (hnu : IsBTLimit Ω (fun _ ↦ v) nu)
    (hzero : ∀ i, mu i = 0) : nu = 0 := by
  have hrestrict : nu.restrict (Ω : Set (ComplexModel n)) =
      (0 : Measure (ComplexModel n)).restrict (Ω : Set (ComplexModel n)) := by
    refine restrict_eq_of_testFunction_integral_eq hnu.2.1 (by simp) fun φ ↦ ?_
    have h := tendsto_integral_of_antitone_isBTLimit hw hv hanti hlim hmu hnu
      φ.continuous φ.hasCompactSupport φ.tsupport_subset
    have h0 : (fun i ↦ ∫ z, φ z ∂(mu i)) = fun _ ↦ (0 : ℝ) := by
      funext i; rw [hzero i]; simp
    rw [h0] at h
    have := tendsto_nhds_unique tendsto_const_nhds h
    simp [← this]
  have hself : nu.restrict (Ω : Set (ComplexModel n)) = nu :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hnu.1)
  rw [← hself, hrestrict]
  simp

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
