/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.FirstPass.PshSupremumRegularization
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.IncreasingPshBallSubmean
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.IncreasingPshGapCapacityZero
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.MeasureLocality

/-!
# The capacity-zero regularization gap of a normalized increasing PSH sequence

The actual regularized supremum, finite realification and increasing
approximation are constructed from the original sequence. The final gap
has zero literal relative capacity on every ordinary smaller domain.
-/

@[expose] public section

noncomputable section

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped Topology ENNReal

namespace SGPT.Foundations.Analysis.Pending.RegularizedIncreasingPshGapCapacityZero

open FirstPass FirstPass.MongeAmpere SGPT.Foundations.Analysis.MeasureLocality
open SGPT.Foundations.Analysis.Pending.BedfordTaylor

variable {n : ℕ}

/-- The genuine increasing approximation and all-subdomain capacity-zero gap
are produced from the original PSH sequence and its normalized local bounds. -/
theorem regularized_isIncApprox_and_relCapacity_gap_eq_zero
    {Ω B : Opens (ComplexModel n)} (hBΩ : B ≤ Ω)
    (g : ℕ → ComplexModel n → ℝ)
    (hg : ∀ k, PlurisubharmonicOn (fun x ↦ (g k x : EReal)) Ω)
    (hmono : ∀ x ∈ Ω, Monotone (fun k ↦ g k x))
    (hb : ∀ k x, x ∈ B → -1 ≤ g k x ∧ g k x ≤ 1) :
    let p : ComplexModel n → EReal := fun x ↦ ⨆ k, (g k x : EReal)
    let P : ComplexModel n → EReal := uscRegularization p
    let V : ComplexModel n → ℝ := fun x ↦ (P x).toReal
    IsLocallyBoundedPshOn B V ∧
      (∀ x ∈ B, -1 ≤ V x ∧ V x ≤ 1) ∧
      IsIncApprox B V g ∧
      ∀ (D : Opens (ComplexModel n)), D ≤ B →
        relCapacity D {x | x ∈ D ∧ p x < P x} = 0 := by
  classical
  dsimp only
  let e : ℕ → ComplexModel n → EReal := fun k x ↦ (g k x : EReal)
  let F : Set (ComplexModel n → EReal) := range e
  let p : ComplexModel n → EReal := fun x ↦ ⨆ k, e k x
  let P : ComplexModel n → EReal := uscRegularization p
  let V : ComplexModel n → ℝ := fun x ↦ (P x).toReal
  have hs : sSup F = p := by
    ext x
    simp only [F, sSup_range, iSup_apply, p]
  have hF : LocallyUniformlyBoundedAbove F B := by
    intro x _hx
    refine ⟨univ, univ_mem, 1, ?_⟩
    rintro f ⟨k, rfl⟩ y hy
    exact EReal.coe_le_coe_iff.mpr (hb k y hy.2).2
  have hPpsh : PlurisubharmonicOn P B := by
    have h := plurisubharmonicOn_uscRegularization_sSup B.isOpen
      (fun _ hf ↦ by obtain ⟨k, rfl⟩ := hf; exact (hg k).mono hBΩ) hF
    simpa only [hs] using h
  have hpb : ∀ x ∈ B, ((-1 : ℝ) : EReal) ≤ p x ∧ p x ≤ (1 : EReal) := by
    intro x hx
    exact ⟨(EReal.coe_le_coe_iff.mpr (hb 0 x hx).1).trans
      (le_iSup (fun k ↦ e k x) 0),
      iSup_le fun k ↦ EReal.coe_le_coe_iff.mpr (hb k x hx).2⟩
  have hPb : ∀ x ∈ B, ((-1 : ℝ) : EReal) ≤ P x ∧ P x ≤ (1 : EReal) := by
    intro x hx
    refine ⟨(hpb x hx).1.trans (le_uscRegularization p x), ?_⟩
    exact (uscRegularization_le_localSup p (B.isOpen.mem_nhds hx)).trans
      (iSup_le fun y ↦ iSup_le fun hy ↦ (hpb y hy).2)
  have hPtop : ∀ x ∈ B, P x ≠ ⊤ := fun x hx ↦
    ne_of_lt ((hPb x hx).2.trans_lt (EReal.coe_lt_top 1))
  have hPbot : ∀ x ∈ B, P x ≠ ⊥ := fun x hx ↦
    ne_of_gt ((EReal.bot_lt_coe (-1)).trans_le (hPb x hx).1)
  have hVeq : EqOn (fun x ↦ (V x : EReal)) P B :=
    fun x hx ↦ EReal.coe_toReal (hPtop x hx) (hPbot x hx)
  have hVval (x : ComplexModel n) (hx : x ∈ B) : (V x : EReal) = P x := hVeq hx
  have hVb : ∀ x ∈ B, -1 ≤ V x ∧ V x ≤ 1 := by
    intro x hx
    constructor
    · apply EReal.coe_le_coe_iff.mp
      rw [hVval x hx]
      exact (hPb x hx).1
    · apply EReal.coe_le_coe_iff.mp
      rw [hVval x hx]
      exact (hPb x hx).2
  have hV : IsLocallyBoundedPshOn B V :=
    isLocallyBoundedPshOn_of_abs_le
      ((hPpsh.discPshOn.congr hVeq.symm).plurisubharmonicOn B.isOpen)
      (fun x hx ↦ abs_le.mpr (hVb x hx))
  have hgB : ∀ k, IsLocallyBoundedPshOn B (g k) := fun k ↦
    isLocallyBoundedPshOn_of_abs_le ((hg k).mono hBΩ)
      (fun x hx ↦ abs_le.mpr (hb k x hx))
  have hPeq : ∀ᵐ x ∂volume, x ∈ B → P x = p x := by
    apply ae_of_forall_ball
    intro a ha
    obtain ⟨S, hS, hSB⟩ := Metric.isOpen_iff.mp B.isOpen a ha
    refine ⟨S / 2, by positivity, ?_⟩
    exact ae_uscRegularization_iSup_eq_on_ball
      (fun k ↦ (hg k).discPshOn)
      (fun x hx ↦ EReal.coe_strictMono.monotone.comp (hmono x hx))
      volume a hS (hSB.trans hBΩ)
      (fun k x hx ↦ EReal.coe_le_coe_iff.mpr (hb k x (hSB hx)).2)
  have hInc : IsIncApprox B V g := by
    refine ⟨hgB, fun x hx ↦ hmono x (hBΩ hx), ?_, ?_⟩
    · intro k x hx
      apply EReal.coe_le_coe_iff.mp
      rw [hVval x hx]
      exact (le_iSup (fun j ↦ e j x) k).trans (le_uscRegularization p x)
    · filter_upwards [hPeq] with x hx hxB
      have ht : Tendsto (fun k ↦ e k x) atTop (𝓝 (P x)) := by
        rw [hx hxB]
        exact tendsto_atTop_iSup
          (EReal.coe_strictMono.monotone.comp (hmono x (hBΩ hxB)))
      have htR : Tendsto (fun k ↦ (e k x).toReal) atTop (𝓝 (P x).toReal) :=
        (EReal.tendsto_toReal (hPtop x hxB) (hPbot x hxB)).comp ht
      simpa only [e, EReal.toReal_coe, V] using htR
  refine ⟨hV, hVb, hInc, ?_⟩
  intro D hDB
  have hz := IncreasingPshGapCapacityZero.relCapacity_gap_eq_zero_of_le hDB hV hInc
  refine le_antisymm ((relCapacity_mono ?_).trans hz.le) bot_le
  rintro x ⟨hxD, hgap⟩
  have hxB := hDB hxD
  have hptop : p x ≠ ⊤ := ne_of_lt ((hpb x hxB).2.trans_lt (EReal.coe_lt_top 1))
  have hpbot : p x ≠ ⊥ := ne_of_gt ((EReal.bot_lt_coe (-1)).trans_le (hpb x hxB).1)
  have hpeq : ((p x).toReal : EReal) = p x := EReal.coe_toReal hptop hpbot
  have hlt : (p x).toReal < V x := by
    apply EReal.coe_lt_coe_iff.mp
    rw [hpeq, hVval x hxB]
    exact hgap
  refine ⟨hxD, (V x - (p x).toReal) / 2, by linarith, ?_⟩
  intro k
  have hgk : g k x ≤ (p x).toReal := by
    apply EReal.coe_le_coe_iff.mp
    rw [hpeq]
    exact le_iSup (fun j ↦ e j x) k
  linarith

end SGPT.Foundations.Analysis.Pending.RegularizedIncreasingPshGapCapacityZero
