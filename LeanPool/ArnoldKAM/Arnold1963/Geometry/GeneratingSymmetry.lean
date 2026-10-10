/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Geometry.GeneratingGlobal
public import Mathlib.Analysis.Calculus.FDeriv.Star

/-!
Conjugation and physical angle translation laws for the same selected inverse. No periodicity
or real compatibility is required of arbitrary extensions outside the original domain.
-/

@[expose] public section
noncomputable section
open Set Metric Filter
open scoped NNReal Topology
namespace KamProject.Arnold1963


/-- Translation of phase space by an integer angle-period shift. -/
def phaseShift {n : ℕ} (k : FourierIndex n) (x : ComplexPhaseSpace n) :=
  (x.1, x.2 + angleShift k)

theorem phaseShift_eq_add {n : ℕ} (k : FourierIndex n) (x : ComplexPhaseSpace n) :
    phaseShift k x = x + (0, angleShift k) := by simp [phaseShift, Prod.add_def]

theorem phaseShift_mem_phaseDomain {n : ℕ} {G : Set (ComplexSpace n)} {ρ : ℝ≥0}
    (k : FourierIndex n) (x : ComplexPhaseSpace n) :
    phaseShift k x ∈ phaseDomain G ρ ↔ x ∈ phaseDomain G ρ := by
  simp [phaseShift, phaseDomain, add_angleShift_mem_iff]

theorem star_mem_erosion {E : Type*} [NormedAddCommGroup E] [StarAddMonoid E]
    [NormedStarGroup E] {V : Set E} (hc : ∀ x ∈ V, star x ∈ V)
    {r : ℝ≥0} {x : E} (hx : x ∈ erosion V r) : star x ∈ erosion V r := by
  intro z hz
  have hd : dist (star z) x = dist z (star x) := by
    rw [← dist_star_star z (star x), star_star]
  have hh := hc (star z) (hx (by simpa only [Metric.mem_closedBall, hd] using hz))
  simpa only [star_star] using hh

theorem add_mem_erosion {E : Type*} [NormedAddCommGroup E] {V : Set E} {c : E}
    (hc : ∀ z, z + c ∈ V ↔ z ∈ V) {r : ℝ≥0} {x : E}
    (hx : x ∈ erosion V r) : x + c ∈ erosion V r := by
  intro z hz
  have hd : dist (z - c) x = dist z (x + c) := by
    simp only [dist_eq_norm]; congr 1; abel
  have hh := (hc (z - c)).mpr (hx (by simpa only [Metric.mem_closedBall, hd] using hz))
  simpa using hh

theorem conj_mem_phaseDomain {n : ℕ} {G : Set (ComplexSpace n)} {ρ : ℝ≥0}
    (hG : ConjInvariant G) {x : ComplexPhaseSpace n} (hx : x ∈ phaseDomain G ρ) :
    conjPhase x ∈ phaseDomain G ρ := by
  refine ⟨hG _ hx.1, ?_⟩
  apply (mem_angleStrip_iff _ _).2
  intro j
  simpa [conjPhase, conjVec] using (mem_angleStrip_iff _ _).1 hx.2 j

theorem fderiv_conjPhase {n : ℕ} {S : ComplexPhaseSpace n → ℂ}
    {V : Set (ComplexPhaseSpace n)} {x : ComplexPhaseSpace n}
    (ha : AnalyticAt ℂ S x) (hc : ConjCompatibleOn S V) (hx : V ∈ 𝓝 (conjPhase x))
    (v : ComplexPhaseSpace n) :
    fderiv ℂ S (conjPhase x) (conjPhase v) = star (fderiv ℂ S x v) := by
  have he : S =ᶠ[𝓝 (star x)] (star ∘ S ∘ star) := by
    filter_upwards [hx] with z hz
    simpa [Function.comp_def, ← hc z hz] using (star_star (S z)).symm
  have hd := ha.differentiableAt.hasFDerivAt.star_star
  rw [conjPhase_eq_star, he.fderiv_eq, hd.fderiv]
  simp [conjPhase_eq_star]

theorem gradients_conj {n : ℕ} {S : ComplexPhaseSpace n → ℂ}
    {V : Set (ComplexPhaseSpace n)} {x : ComplexPhaseSpace n}
    (ha : AnalyticAt ℂ S x) (hc : ConjCompatibleOn S V) (hx : V ∈ 𝓝 (conjPhase x)) :
    pGradient S (conjPhase x) = conjVec (pGradient S x) ∧
      qGradient S (conjPhase x) = conjVec (qGradient S x) := by
  constructor <;> ext j
  · simpa [pGradient, pDirection, conjPhase, conjVec] using fderiv_conjPhase ha hc hx (pDirection j)
  · simpa [qGradient, qDirection, conjPhase, conjVec] using fderiv_conjPhase ha hc hx (qDirection j)

theorem gradients_periodic {n : ℕ} {G : Set (ComplexSpace n)} {ρ r : ℝ≥0}
    (S : AnalyticPhaseFunction n G ρ) (hr : 0 < r) {x : ComplexPhaseSpace n}
    (hx : x ∈ erosion (phaseDomain G ρ) r) (k : FourierIndex n) :
    pGradient S.toFun (phaseShift k x) = pGradient S.toFun x ∧
      qGradient S.toFun (phaseShift k x) = qGradient S.toFun x := by
  have hn : phaseDomain G ρ ∈ 𝓝 x :=
    mem_of_superset (closedBall_mem_nhds x (show (0 : ℝ) < r from hr)) hx
  have he : (S.toFun ∘ phaseShift k) =ᶠ[𝓝 x] S.toFun := by
    filter_upwards [hn] with z hz
    exact S.periodic z.1 hz.1 z.2 hz.2 k
  have hshift : HasFDerivAt (phaseShift k) (ContinuousLinearMap.id ℂ _) x := by
    convert (hasFDerivAt_id (𝕜 := ℂ) x).add_const (0, angleShift k) using 1
    funext z
    exact phaseShift_eq_add k z
  have ha := S.analytic _ ((phaseShift_mem_phaseDomain k x).2 (erosion_subset _ _ hx))
  have hd := ha.differentiableAt.hasFDerivAt.comp x hshift
  have heq : fderiv ℂ S.toFun (phaseShift k x) = fderiv ℂ S.toFun x := by
    simpa using hd.fderiv.symm.trans he.fderiv_eq
  constructor <;> ext j
  · exact congrArg (fun L : ComplexPhaseSpace n →L[ℂ] ℂ => L (pDirection j)) heq
  · exact congrArg (fun L : ComplexPhaseSpace n →L[ℂ] ℂ => L (qDirection j)) heq

end KamProject.Arnold1963
