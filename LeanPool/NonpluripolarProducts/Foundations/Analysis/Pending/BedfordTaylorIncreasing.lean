/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorIncreasingStepP
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorIncreasingStepW
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorIncreasingCollar

/-!
# Bedford–Taylor convergence along increasing sequences

Let `u₁ʲ, …, uₙʲ` be sequences of locally bounded plurisubharmonic functions on an open
set `Ω ⊆ ℂⁿ`, each increasing and converging Lebesgue-almost everywhere to a locally
bounded plurisubharmonic `uᵢ`. Then the mixed Monge–Ampère measures
`ddᶜu₁ʲ ∧ ⋯ ∧ ddᶜuₙʲ` converge vaguely to `ddᶜu₁ ∧ ⋯ ∧ ddᶜuₙ`, and the same holds
after multiplying by an increasing sequence of weights (Bedford–Taylor; Błocki,
*The complex Monge–Ampère operator in pluripotential theory*, lecture notes, Thm 2.2.5).

The proof is Cegrell's, which avoids the Dirichlet problem: an induction on the number of
varying slots, whose steps are `incPClaim_succ` (integration by parts against smooth
tests), `incWClaim_of_collar` (localization to collared data on balls) and
`incWCollarClaim_succ` (quasi-continuity and the symmetric integration by parts).
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere

variable {n : ℕ}

/-- Both convergence claims hold at every level `q ≤ n`. -/
theorem incClaims_of_le : ∀ q : ℕ, q ≤ n → IncPClaim n q ∧ IncWClaim n q
  | 0, _ => ⟨incPClaim_zero, incWClaim_zero⟩
  | q + 1, h => by
    obtain ⟨hP, hW⟩ := incClaims_of_le q (Nat.le_of_succ_le h)
    have hq : q < n := h
    have hP' := incPClaim_succ hq hP hW
    exact ⟨hP', incWClaim_of_collar hP' (incWCollarClaim_succ hq hP' hW)⟩

/-- **Bedford–Taylor convergence along increasing sequences**, unweighted. -/
theorem incPClaim_all : IncPClaim n n := (incClaims_of_le n le_rfl).1

/-- **Bedford–Taylor convergence along increasing sequences**, with increasing weights. -/
theorem incWClaim_all : IncWClaim n n := (incClaims_of_le n le_rfl).2

/-- **Local form.** If `vTilde_k` increasingly approximates the locally bounded psh `VTilde` on `D`
and `μ` is the Bedford--Taylor measure of a locally bounded psh `wTilde` on `D`, then for every
compact `K ⊆ D` and `δ > 0`, `μ (K ∩ {z | ∀ k, vTilde_k z + δ ≤ VTilde z}) = 0`. -/
theorem measure_inter_gap_eq_zero {D : TopologicalSpace.Opens (ComplexModel n)}
    {w : ComplexModel n → ℝ} (hw : IsLocallyBoundedPshOn D w) {μ : Measure (ComplexModel n)}
    (hμ : IsBTLimit D (fun _ => w) μ) {V : ComplexModel n → ℝ} (hV : IsLocallyBoundedPshOn D V)
    {v : ℕ → ComplexModel n → ℝ} (hv : IsIncApprox D V v) {K : Set (ComplexModel n)}
    (hK : IsCompact K) (hKD : K ⊆ D) {δ : ℝ} (hδ : 0 < δ) :
    μ (K ∩ {z | ∀ k, v k z + δ ≤ V z}) = 0 := by
  classical
  obtain ⟨χ, hχK, hχc, hχD, hχ01⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hK D.isOpen hKD
  have hχcs : HasCompactSupport χ := hχc
  have hμf : ∀ K', IsCompact K' → K' ⊆ D → μ K' < ⊤ := fun K' hK' hK'D => hμ.2.1 K' hK' hK'D
  have hadm : IsIncAdmissible n D (fun _ => w) (fun _ _ => w) :=
    ⟨fun _ => hw, fun _ => isIncApprox_const hw, fun i hi => absurd i.isLt (not_lt.mpr hi)⟩
  have hconv := incWClaim_all D (fun _ => w) (fun _ _ => w) (fun _ => μ) μ hadm (fun _ => hμ) hμ
    V v hV hv χ χ.continuous hχcs hχD
  -- the gap integrals tend to `0`
  have hint : ∀ f : ComplexModel n → ℝ, IsLocallyBoundedPshOn D f →
      Integrable (fun z => χ z * f z) μ := fun f hf =>
    integrable_test_mul_of_isLocallyBoundedPshOn hf hμf χ.continuous hχcs hχD
  have hgap : Tendsto (fun k => ∫ z, χ z * (V z - v k z) ∂μ) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := ∫ z, χ z * V z ∂μ)).sub hconv
    rw [sub_self] at h
    refine h.congr fun k => ?_
    rw [← integral_sub (hint V hV) (hint (v k) (hv.1 k))]
    congr 1
    funext z
    ring
  -- Markov's inequality, uniformly in `k`
  have hnonneg : ∀ k z, 0 ≤ χ z * (V z - v k z) := by
    intro k z
    by_cases hz : z ∈ (D : Set (ComplexModel n))
    · exact mul_nonneg (hχ01 z).1 (sub_nonneg.mpr (hv.2.2.1 k z hz))
    · have : χ z = 0 := image_eq_zero_of_notMem_tsupport fun h => hz (hχD h)
      rw [this, zero_mul]
  have hsub : ∀ k, K ∩ {z | ∀ k, v k z + δ ≤ V z} ⊆ {z | δ ≤ χ z * (V z - v k z)} := by
    intro k z hz
    have h1 : χ z = 1 := hχK hz.1
    change δ ≤ χ z * (V z - v k z)
    rw [h1, one_mul]
    linarith [hz.2 k]
  have hbound : ∀ k, δ * (μ (K ∩ {z | ∀ k, v k z + δ ≤ V z})).toReal ≤
      ∫ z, χ z * (V z - v k z) ∂μ := by
    intro k
    have hI : Integrable (fun z => χ z * (V z - v k z)) μ := by
      have := (hint V hV).sub (hint (v k) (hv.1 k))
      refine this.congr (Eventually.of_forall fun z => ?_)
      simp only [Pi.sub_apply]
      ring
    have hfinK : μ {z | δ ≤ χ z * (V z - v k z)} ≠ ⊤ := by
      refine ne_top_of_le_ne_top (hμf _ hχc hχD).ne (measure_mono fun z hz => ?_)
      by_contra hzt
      have : χ z = 0 := image_eq_zero_of_notMem_tsupport hzt
      have hz' : δ ≤ χ z * (V z - v k z) := hz
      rw [this, zero_mul] at hz'
      linarith
    calc δ * (μ (K ∩ {z | ∀ k, v k z + δ ≤ V z})).toReal
        ≤ δ * (μ {z | δ ≤ χ z * (V z - v k z)}).toReal := by
          gcongr
          exact hsub k
      _ ≤ ∫ z, χ z * (V z - v k z) ∂μ :=
          mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall (hnonneg k)) hI δ
  have hle0 : δ * (μ (K ∩ {z | ∀ k, v k z + δ ≤ V z})).toReal ≤ 0 :=
    ge_of_tendsto hgap (Eventually.of_forall hbound)
  have htoReal : (μ (K ∩ {z | ∀ k, v k z + δ ≤ V z})).toReal = 0 := by
    refine le_antisymm ?_ ENNReal.toReal_nonneg
    by_contra h
    push Not at h
    have := mul_pos hδ h
    linarith
  have hfin : μ (K ∩ {z | ∀ k, v k z + δ ≤ V z}) ≠ ⊤ :=
    ne_top_of_le_ne_top (hμf K hK hKD).ne (measure_mono inter_subset_left)
  exact (ENNReal.toReal_eq_zero_iff _).mp htoReal |>.resolve_right hfin

end SGPT.Foundations.Analysis.Pending.BedfordTaylor

end
