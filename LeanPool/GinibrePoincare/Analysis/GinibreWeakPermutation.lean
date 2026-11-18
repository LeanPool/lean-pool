/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreWeakPermutation.lean.
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
public import LeanPool.GinibrePoincare.Analysis.GinibreWeakSobolevMultipliers
public import LeanPool.GinibrePoincare.Analysis.GinibrePermutationAverage
public import LeanPool.GinibrePoincare.Analysis.GinibreL2Norm

/-! # Particle permutations on actual Ginibre weak-pair spaces -/


@[expose] public section


open MeasureTheory
open Filter
open scoped ENNReal ContDiff BigOperators Topology
namespace GinibrePoincare
noncomputable section

/-- Pullback by a particle relabelling on real Ginibre `L²`. -/
def ginibreRealPermutationL2 {n : ℕ} (σ : ParticlePermutation n) :
    Lp ℝ 2 (ginibreMeasure n) →ₗᵢ[ℝ] Lp ℝ 2 (ginibreMeasure n) :=
  Lp.compMeasurePreservingₗᵢ ℝ (permute σ) (ginibre_measurePreserving_permute σ)

/-- Coordinate reindexing on the real Euclidean gradient values. -/
def ginibreGradientCoordinateEquiv {n : ℕ} (σ : ParticlePermutation n) :
    EuclideanSpace ℝ (Fin n × Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n × Fin 2) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (Equiv.prodCongr σ (Equiv.refl (Fin 2)))

/-- The gradient representation combines spatial pullback with the matching
coordinate reindexing. -/
def ginibreGradientPermutationL2 {n : ℕ} (σ : ParticlePermutation n) :
    Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n) →L[ℝ]
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n) := by
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let Q := (ginibreGradientCoordinateEquiv σ).toContinuousLinearMap
  let S : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n) →ₗᵢ[ℝ]
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n) :=
    Lp.compMeasurePreservingₗᵢ ℝ (permute σ) (ginibre_measurePreserving_permute σ)
  exact Q.compLpL 2 (ginibreMeasure n) ∘L
    S.toContinuousLinearMap

/-- The gradient pullback representation preserves the actual Ginibre L² norm. -/
theorem ginibreGradientPermutationL2_norm {n : ℕ} (σ : ParticlePermutation n)
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n)) :
    ‖ginibreGradientPermutationL2 σ g‖ = ‖g‖ := by
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let Q := (ginibreGradientCoordinateEquiv σ).toContinuousLinearMap
  let S : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n) →ₗᵢ[ℝ]
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n) :=
    Lp.compMeasurePreservingₗᵢ ℝ (permute σ) (ginibre_measurePreserving_permute σ)
  change ‖Q.compLpL 2 (ginibreMeasure n) (S g)‖ = ‖g‖
  have hsq : ‖Q.compLpL 2 (ginibreMeasure n) (S g)‖ ^ 2 = ‖S g‖ ^ 2 := by
    rw [← integral_norm_sq_eq_L2_norm_sq, ← integral_norm_sq_eq_L2_norm_sq]
    apply integral_congr_ae
    filter_upwards [Q.coeFn_compLpL (S g)] with z hz
    rw [hz]
    exact congrArg (fun r : ℝ => r ^ 2)
      ((ginibreGradientCoordinateEquiv σ).norm_map ((S g) z))
  have hnQ : ‖Q.compLpL 2 (ginibreMeasure n) (S g)‖ = ‖S g‖ := by
    nlinarith [norm_nonneg (Q.compLpL 2 (ginibreMeasure n) (S g)), norm_nonneg (S g)]
  change ‖Q.compLpL 2 (ginibreMeasure n) (S g)‖ = ‖g‖
  rw [hnQ]
  exact S.norm_map g

theorem ginibreRealPermutationL2_ae {n : ℕ} (σ : ParticlePermutation n)
    (u : Lp ℝ 2 (ginibreMeasure n)) :
    (ginibreRealPermutationL2 σ u : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
      fun z => u (permute σ z) := by
  change Lp.compMeasurePreserving (permute σ)
    (ginibre_measurePreserving_permute σ) u =ᵐ[ginibreMeasure n] _
  exact Lp.coeFn_compMeasurePreserving u (ginibre_measurePreserving_permute σ)

theorem ginibreGradientPermutationL2_ae {n : ℕ} (σ : ParticlePermutation n)
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n)) :
    (ginibreGradientPermutationL2 σ g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[
      ginibreMeasure n] fun z => WithLp.toLp 2 (fun k : Fin n × Fin 2 =>
        g (permute σ z) (σ.symm k.1, k.2)) := by
  let Q := (ginibreGradientCoordinateEquiv σ).toContinuousLinearMap
  let S : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n) →ₗᵢ[ℝ]
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n) :=
    Lp.compMeasurePreservingₗᵢ ℝ (permute σ) (ginibre_measurePreserving_permute σ)
  filter_upwards [Q.coeFn_compLpL (S g), Lp.coeFn_compMeasurePreserving g
    (ginibre_measurePreserving_permute σ)] with z hQ hS
  have hSz : S g z = g (permute σ z) := by
    change (Lp.compMeasurePreserving (permute σ)
      (ginibre_measurePreserving_permute σ) g) z = _
    exact hS
  change (Q.compLpL 2 (ginibreMeasure n) (S g)) z = _
  rw [hQ, hSz]
  apply PiLp.ext
  intro k
  change g (permute σ z)
      ((Equiv.prodCongr σ (Equiv.refl (Fin 2))).symm k) =
    g (permute σ z) (σ.symm k.1, k.2)
  have hidx : (Equiv.prodCongr σ (Equiv.refl (Fin 2))).symm k =
      (σ.symm k.1, k.2) := by
    cases k
    simp [Equiv.prodCongr_symm, Equiv.prodCongr_apply]
  exact congrArg (g (permute σ z)) hidx

/-- A weak pair is permutation invariant when both components are fixed by
their natural pullback representations. -/
def IsGinibreSymmetricWeakPair {n : ℕ}
    (p : Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n)) : Prop :=
  ∀ σ : ParticlePermutation n,
    ginibreRealPermutationL2 σ p.1 = p.1 ∧
      ginibreGradientPermutationL2 σ p.2 = p.2

/-- Particle relabelling carries the ordinary collision-free weak-gradient
relation to itself, with the matching coordinate permutation on gradients. -/
theorem ginibreDistributionalGradient_permute {n : ℕ} (hn : 0 < n)
    (σ : ParticlePermutation n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g) :
    IsGinibreDistributionalGradient n
      (ginibreRealPermutationL2 σ u) (ginibreGradientPermutationL2 σ g) := by
  refine ⟨ginibre_memLp_locallyIntegrable_collisionFree hn _ (Lp.memLp _), ?_, ?_⟩
  · intro k
    let P : EuclideanSpace ℝ (Fin n × Fin 2) →L[ℝ] ℝ := PiLp.proj 2 _ k
    exact ginibre_memLp_locallyIntegrable_collisionFree hn _ (P.comp_memLp _)
  · intro k θ hθ hc hs
    let e : Configuration n ≃L[ℝ] Configuration n :=
      ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin n => ℂ) σ.symm
    let ψ : Configuration n → ℝ := θ ∘ e.symm
    have hψ : ContDiff ℝ ∞ ψ := hθ.comp e.symm.contDiff
    have hcψ : HasCompactSupport ψ := hc.comp_homeomorph e.symm.toHomeomorph
    have hsψ : tsupport ψ ⊆ {z | CollisionFree z} := by
      intro z hz
      have ht := hs (tsupport_comp_subset_preimage θ e.symm.continuous hz)
      intro i j hij
      apply σ.injective
      have hcoords : e.symm z (σ i) = e.symm z (σ j) := by
        change z (σ.symm (σ i)) = z (σ.symm (σ j))
        simpa using hij
      exact ht hcoords
    let k' : Fin n × Fin 2 := (σ.symm k.1, k.2)
    have hder (y : Configuration n) :
        fderiv ℝ ψ y (ginibreCoordinateDirection k') =
          fderiv ℝ θ (e.symm y) (ginibreCoordinateDirection k) := by
      have hc := ginibreEuclideanGradient_comp_permute σ.symm θ hθ y
      have hk := congrArg (fun v : EuclideanSpace ℝ (Fin n × Fin 2) => v k') hc
      have heval (x : Configuration n) : e.symm x = permute σ.symm x := by
        funext i
        change x (σ.symm i) = x (σ.symm i)
        rfl
      have hpsi : ψ = fun x => θ (permute σ.symm x) := by
        funext x
        exact congrArg θ (heval x)
      rw [hpsi]
      have heval' : e.symm y = permute σ.symm y := heval y
      simpa [k', ginibreCoordinateDirection, ginibreEuclideanGradient_coordinate,
        heval'] using hk
    have hleft : (∫ z, (ginibreGradientPermutationL2 σ g) z k * θ z) =
        ∫ z, g (permute σ z) k' * θ z := by
      apply integral_congr_ae
      filter_upwards [(ginibre_ae_eq_iff_volume n hn _ _).mp
        (ginibreGradientPermutationL2_ae σ g)] with z hz
      rw [hz]
    have hright : (∫ z, (ginibreRealPermutationL2 σ u) z *
        fderiv ℝ θ z (ginibreCoordinateDirection k)) =
        ∫ z, u (permute σ z) * fderiv ℝ θ z (ginibreCoordinateDirection k) := by
      apply integral_congr_ae
      filter_upwards [(ginibre_ae_eq_iff_volume n hn _ _).mp
        (ginibreRealPermutationL2_ae σ u)] with z hz
      rw [hz]
    let me := permutationMeasurableEquiv σ
    have hmp : MeasurePreserving me (volume : Measure (Configuration n)) volume := by
      have h := volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℂ) σ.symm
      change MeasurePreserving (permutationMeasurableEquiv σ) volume volume at h
      exact h
    have hmp₁ := hmp.integral_comp'
      (fun y => g y k' * ψ y)
    have hmp₂ := hmp.integral_comp'
      (fun y => u y * fderiv ℝ ψ y (ginibreCoordinateDirection k'))
    have hψcomp (z : Configuration n) : ψ (permute σ z) = θ z := by
      have he : e.symm (permute σ z) = z := by
        funext i
        change (permute σ.symm (permute σ z)) i = z i
        simp [permute]
      simp [ψ, he]
    have hsub₁ : (∫ z, g (permute σ z) k' * θ z) = ∫ y, g y k' * ψ y := by
      calc
        _ = ∫ z, g (permute σ z) k' * ψ (permute σ z) := by
          apply integral_congr_ae
          exact ae_of_all _ (fun z => by
            change g (permute σ z) k' * θ z = _
            rw [← hψcomp z])
        _ = _ := by
          calc
            _ = ∫ z, g (permutationMeasurableEquiv σ z) k' *
                ψ (permutationMeasurableEquiv σ z) := by
              apply integral_congr_ae
              exact ae_of_all _ (fun z => by simp [permutationMeasurableEquiv_apply])
            _ = _ := hmp₁
    have hsub₂ : (∫ z, u (permute σ z) *
        fderiv ℝ θ z (ginibreCoordinateDirection k)) =
        ∫ y, u y * fderiv ℝ ψ y (ginibreCoordinateDirection k') := by
      have hchange (z : Configuration n) :
          fderiv ℝ ψ (permute σ z) (ginibreCoordinateDirection k') =
            fderiv ℝ θ z (ginibreCoordinateDirection k) := by
        rw [hder]
        congr 1
        have he : e.symm (permute σ z) = z := by
          funext i
          change (permute σ z) (σ.symm i) = z i
          simp [permute]
        exact congrArg (fun x => fderiv ℝ θ x) he
      calc
        _ = ∫ z, u (permute σ z) *
            fderiv ℝ ψ (permute σ z) (ginibreCoordinateDirection k') := by
          apply integral_congr_ae
          exact ae_of_all _ (fun z => by
            change u (permute σ z) *
              fderiv ℝ θ z (ginibreCoordinateDirection k) =
              u (permute σ z) *
                fderiv ℝ ψ (permute σ z) (ginibreCoordinateDirection k')
            rw [hchange z])
        _ = _ := by
          calc
            _ = ∫ z, u (permutationMeasurableEquiv σ z) *
                fderiv ℝ ψ (permutationMeasurableEquiv σ z)
                  (ginibreCoordinateDirection k') := by
              apply integral_congr_ae
              exact ae_of_all _ (fun z => by simp [permutationMeasurableEquiv_apply])
            _ = _ := hmp₂
    rw [hleft, hright, hsub₁, hsub₂]
    exact hg.2.2 k' ψ hψ hcψ hsψ

/-- The Reynolds average on scalar Ginibre L². -/
def ginibreRealPermutationAverageL2 {n : ℕ} :
    Lp ℝ 2 (ginibreMeasure n) →L[ℝ] Lp ℝ 2 (ginibreMeasure n) := by
  classical
  let N : ℝ := (Fintype.card (ParticlePermutation n) : ℝ)⁻¹
  exact N • ∑ σ : ParticlePermutation n,
    (ginibreRealPermutationL2 σ).toContinuousLinearMap

/-- The scalar L² Reynolds operator has its literal finite-average representative. -/
theorem ginibreRealPermutationAverageL2_ae {n : ℕ}
    (u : Lp ℝ 2 (ginibreMeasure n)) (f : Configuration n → ℝ)
    (hu : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f) :
    (ginibreRealPermutationAverageL2 u : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
      ginibrePermutationAverage f := by
  classical
  have hterm (σ : ParticlePermutation n) :
      (ginibreRealPermutationL2 σ u : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
        fun z => f (permute σ z) := by
    have hcomp := (ginibre_measurePreserving_permute σ).quasiMeasurePreserving.ae_eq_comp hu
    filter_upwards [ginibreRealPermutationL2_ae σ u, hcomp] with z hp hc
    simp only [Function.comp_apply] at hc
    rw [hp, hc]
  unfold ginibreRealPermutationAverageL2
  simp only [smul_apply, sum_apply]
  filter_upwards [Lp.coeFn_smul ((Fintype.card (ParticlePermutation n) : ℝ)⁻¹)
      (∑ σ : ParticlePermutation n, ginibreRealPermutationL2 σ u),
    Lp.coeFn_fun_finsetSum Finset.univ (fun σ => ginibreRealPermutationL2 σ u),
    ae_all_iff.mpr hterm] with z hscale hsum hall
  change (↑((Fintype.card (ParticlePermutation n) : ℝ)⁻¹ •
    ∑ σ : ParticlePermutation n, ginibreRealPermutationL2 σ u) : Configuration n → ℝ) z = _
  rw [hscale]
  change (Fintype.card (ParticlePermutation n) : ℝ)⁻¹ *
    (∑ σ : ParticlePermutation n, ginibreRealPermutationL2 σ u : Lp ℝ 2 (ginibreMeasure n)) z = _
  rw [hsum]
  simp only [ginibrePermutationAverage]
  congr 1
  exact Finset.sum_congr rfl (fun σ _ => hall σ)

/-- The compatible Reynolds average on vector Ginibre L² gradients. -/
def ginibreGradientPermutationAverageL2 {n : ℕ} :
    Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n) →L[ℝ]
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n) := by
  classical
  let N : ℝ := (Fintype.card (ParticlePermutation n) : ℝ)⁻¹
  exact N • ∑ σ : ParticlePermutation n, ginibreGradientPermutationL2 σ

theorem ginibreRealPermutationAverageL2_fixed {n : ℕ}
    (u : Lp ℝ 2 (ginibreMeasure n))
    (hu : ∀ σ, ginibreRealPermutationL2 σ u = u) :
    ginibreRealPermutationAverageL2 u = u := by
  classical
  unfold ginibreRealPermutationAverageL2
  simp only [smul_apply, sum_apply]
  change (Fintype.card (ParticlePermutation n) : ℝ)⁻¹ •
    ∑ σ : ParticlePermutation n, ginibreRealPermutationL2 σ u = u
  simp_rw [hu]
  have hc : (Fintype.card (ParticlePermutation n) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hc]

theorem ginibreGradientPermutationAverageL2_fixed {n : ℕ}
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : ∀ σ, ginibreGradientPermutationL2 σ g = g) :
    ginibreGradientPermutationAverageL2 g = g := by
  classical
  unfold ginibreGradientPermutationAverageL2
  simp only [smul_apply, sum_apply]
  change (Fintype.card (ParticlePermutation n) : ℝ)⁻¹ •
    ∑ σ : ParticlePermutation n, ginibreGradientPermutationL2 σ g = g
  simp_rw [hg]
  have hc : (Fintype.card (ParticlePermutation n) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hc]

theorem ginibreWeakPair_average_tendsto_of_tendsto {n : ℕ}
    (p : ℕ → Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (ht : Tendsto p atTop (𝓝 (u, g)))
    (hs : IsGinibreSymmetricWeakPair (u, g)) :
    Tendsto (fun m => (ginibreRealPermutationAverageL2 (p m).1,
      ginibreGradientPermutationAverageL2 (p m).2)) atTop (𝓝 (u, g)) := by
  have hv := ((ginibreRealPermutationAverageL2).continuous.continuousAt.tendsto.comp
    (continuous_fst.tendsto _ |>.comp ht))
  have hg := ((ginibreGradientPermutationAverageL2).continuous.continuousAt.tendsto.comp
    (continuous_snd.tendsto _ |>.comp ht))
  rw [ginibreRealPermutationAverageL2_fixed u (fun σ => (hs σ).1)] at hv
  rw [ginibreGradientPermutationAverageL2_fixed g (fun σ => (hs σ).2)] at hg
  exact hv.prodMk_nhds hg


end
end GinibrePoincare
