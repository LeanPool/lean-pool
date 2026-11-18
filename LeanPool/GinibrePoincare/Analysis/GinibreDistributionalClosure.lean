/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreDistributionalClosure.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GinibreDistributionalGradient

/-! # Closedness of the ordinary distributional gradient graph

Interior compact tests define continuous pairings on actual Ginibre L².
Consequently the independently defined local distributional gradient graph
is closed. This does not assert smooth radial core density in that graph.
-/


@[expose] public section


open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section


/-- An interior test divided by the density is continuous and compactly supported. -/
theorem collisionFree_test_div_density (n : ℕ) (hn : 0 < n)
    (θ : Configuration n → ℝ) (hθ : Continuous θ) (hc : HasCompactSupport θ)
    (hs : tsupport θ ⊆ {z | CollisionFree z}) :
    Continuous (fun z => θ z / ginibreLebesgueDensityReal n z) ∧
      HasCompactSupport (fun z => θ z / ginibreLebesgueDensityReal n z) := by
  refine ⟨continuous_iff_continuousAt.mpr (fun z => ?_), hc.mono ?_⟩
  · by_cases hz : ginibreLebesgueDensityReal n z = 0
    · have ht : z ∉ tsupport θ := fun ht =>
        ginibreLebesgueDensityReal_ne_zero_of_collisionFree hn (hs ht) hz
      apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
      filter_upwards [notMem_tsupport_iff_eventuallyEq.mp ht] with y hy
      simp [hy]
    · exact hθ.continuousAt.div (contDiff_ginibreLebesgueDensityReal n).continuous.continuousAt hz
  · intro z hz hzero
    apply hz
    simp [hzero]

/-- Lebesgue test pairing expressed as a bounded Ginibre L² pairing. -/
theorem integral_collisionFree_test_eq_ginibre (n : ℕ) (hn : 0 < n)
    (f θ : Configuration n → ℝ) (hs : tsupport θ ⊆ {z | CollisionFree z}) :
    (∫ z, f z * θ z) = (ginibreNormalizingMass n).toReal *
      ∫ z, f z * (θ z / ginibreLebesgueDensityReal n z) ∂ginibreMeasure n := by
  rw [integral_ginibreMeasure_eq_density_volume hn]
  have he : (fun z => ginibreLebesgueDensityReal n z *
      (f z * (θ z / ginibreLebesgueDensityReal n z))) = (fun z => f z * θ z) := by
    funext z
    by_cases hz : ginibreLebesgueDensityReal n z = 0
    · have ht : z ∉ tsupport θ := fun ht =>
        ginibreLebesgueDensityReal_ne_zero_of_collisionFree hn (hs ht) hz
      simp [hz, image_eq_zero_of_notMem_tsupport ht]
    · field_simp
  rw [he]
  have hm : (ginibreNormalizingMass n).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr
    ⟨(ginibreMassEvaluation n hn).1.ne', (ginibreMassEvaluation n hn).2.ne⟩
  simp [hm]

theorem continuous_ginibre_distributional_pairing (n : ℕ) (hn : 0 < n)
    (θ : Configuration n → ℝ) (hθ : Continuous θ) (hc : HasCompactSupport θ)
    (hs : tsupport θ ⊆ {z | CollisionFree z}) :
    Continuous (fun u : Lp ℝ 2 (ginibreMeasure n) => ∫ z, u z * θ z) := by
  let := ginibreMeasure_isProbabilityMeasure hn
  simp_rw [integral_collisionFree_test_eq_ginibre n hn _ θ hs]
  have ht := collisionFree_test_div_density n hn θ hθ hc hs
  exact continuous_const.mul (continuous_L2_integral_mul _ _
    (ht.1.memLp_of_hasCompactSupport ht.2))

theorem continuous_ginibre_distributional_gradient_pairing (n : ℕ) (hn : 0 < n)
    (k : Fin n × Fin 2) (θ : Configuration n → ℝ) (hθ : Continuous θ)
    (hc : HasCompactSupport θ) (hs : tsupport θ ⊆ {z | CollisionFree z}) :
    Continuous (fun g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n) =>
      ∫ z, g z k * θ z) := by
  let := ginibreMeasure_isProbabilityMeasure hn
  simp_rw [integral_collisionFree_test_eq_ginibre n hn _ θ hs]
  have ht := collisionFree_test_div_density n hn θ hθ hc hs
  exact continuous_const.mul (continuous_ginibre_gradient_pairing n k _
    (ht.1.memLp_of_hasCompactSupport ht.2))

/-- The ordinary weak-gradient relation is closed in the weighted L² product topology. -/
theorem isClosed_ginibre_distributional_gradient_pairs (n : ℕ) (hn : 0 < n) :
    IsClosed {p : Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n) |
      IsGinibreDistributionalGradient n p.1 p.2} := by
  have he : {p : Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n) |
      IsGinibreDistributionalGradient n p.1 p.2} =
      {p | ∀ (k : Fin n × Fin 2) (θ : Configuration n → ℝ),
        ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ {z | CollisionFree z} →
          (∫ z, p.2 z k * θ z) =
            -(∫ z, p.1 z * fderiv ℝ θ z (ginibreCoordinateDirection k))} := by
    ext p
    constructor
    · exact fun hp => hp.2.2
    · intro hp
      refine ⟨ginibre_memLp_locallyIntegrable_collisionFree hn _ (Lp.memLp p.1), ?_, hp⟩
      intro k
      let P : EuclideanSpace ℝ (Fin n × Fin 2) →L[ℝ] ℝ :=
        PiLp.proj 2 (fun _ : Fin n × Fin 2 => ℝ) k
      have hm : MemLp (fun z => p.2 z k) 2 (ginibreMeasure n) := P.comp_memLp p.2
      exact ginibre_memLp_locallyIntegrable_collisionFree hn (fun z => p.2 z k) hm
  rw [he]
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro k
  apply isClosed_iInter
  intro θ
  apply isClosed_iInter
  intro hθ
  apply isClosed_iInter
  intro hc
  apply isClosed_iInter
  intro hs
  exact isClosed_eq
    ((continuous_ginibre_distributional_gradient_pairing n hn k θ hθ.continuous hc hs).comp
      continuous_snd)
    (((continuous_ginibre_distributional_pairing n hn _
      ((hθ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hc.fderiv_apply ℝ _) ((tsupport_fderiv_apply_subset ℝ _).trans hs)).comp
      continuous_fst).neg)

/-- Ordinary weak derivatives persist under strong weighted value-gradient convergence. -/
theorem ginibre_distributional_gradient_tendsto (n : ℕ) (hn : 0 < n)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (p : ι → Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hp : ∀ᶠ i in l, IsGinibreDistributionalGradient n (p i).1 (p i).2)
    (hu : Tendsto (fun i => (p i).1) l (𝓝 u))
    (hg : Tendsto (fun i => (p i).2) l (𝓝 g)) :
    IsGinibreDistributionalGradient n u g :=
  (isClosed_ginibre_distributional_gradient_pairs n hn).mem_of_tendsto
    (hu.prodMk_nhds hg) hp

/-- The independently defined weak-H¹ value domain on the collision-free set. -/
def ginibreDistributionalSobolevDomain (n : ℕ) : Set (Lp ℝ 2 (ginibreMeasure n)) :=
  {u | ∃ g, IsGinibreDistributionalGradient n u g}

/-- The unique ordinary distributional gradient, extended by zero off its domain. -/
def ginibreDistributionalSobolevGradient (n : ℕ) (u : Lp ℝ 2 (ginibreMeasure n)) :
    Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n) := by
  classical
  exact if hu : u ∈ ginibreDistributionalSobolevDomain n then hu.choose else 0

theorem ginibreDistributionalSobolevGradient_spec (n : ℕ)
    (u : Lp ℝ 2 (ginibreMeasure n)) (hu : u ∈ ginibreDistributionalSobolevDomain n) :
    IsGinibreDistributionalGradient n u (ginibreDistributionalSobolevGradient n u) := by
  simpa only [ginibreDistributionalSobolevGradient, dite_eq_left hu] using hu.choose_spec

theorem ginibreDistributionalSobolevGradient_eq (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g) :
    ginibreDistributionalSobolevGradient n u = g :=
  ginibre_distributional_gradient_unique n hn u _ g
    (ginibreDistributionalSobolevGradient_spec n u ⟨g, hg⟩) hg

theorem ginibreDistributionalSobolevGradient_graph (n : ℕ) (hn : 0 < n) :
    {p : Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n) |
      p.1 ∈ ginibreDistributionalSobolevDomain n ∧
        ginibreDistributionalSobolevGradient n p.1 = p.2} =
    {p | IsGinibreDistributionalGradient n p.1 p.2} := by
  ext p
  constructor
  · rintro ⟨hu, hg⟩
    change IsGinibreDistributionalGradient n p.1 p.2
    simpa only [hg] using ginibreDistributionalSobolevGradient_spec n p.1 hu
  · intro hp
    exact ⟨⟨p.2, hp⟩, ginibreDistributionalSobolevGradient_eq n hn p.1 p.2 hp⟩

/-- This maximal local weak gradient is a closed operator on actual Ginibre L². -/
theorem ginibreDistributionalSobolevGradient_closed (n : ℕ) (hn : 0 < n) :
    IsClosed {p : Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n) |
      p.1 ∈ ginibreDistributionalSobolevDomain n ∧
        ginibreDistributionalSobolevGradient n p.1 = p.2} := by
  rw [ginibreDistributionalSobolevGradient_graph n hn]
  exact isClosed_ginibre_distributional_gradient_pairs n hn

end
end GinibrePoincare
