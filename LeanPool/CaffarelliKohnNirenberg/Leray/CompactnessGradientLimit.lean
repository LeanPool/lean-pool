/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessGradientRepresentative
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessGradientGlobal
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessGradientTimeGlue

/-!
# Compactness Gradient Limit

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set Topology
open CKN CKN.Foundation.Parabolic
open scoped ENNReal

namespace CKN.Leray

/-- Strong local velocity convergence and weak local matrix convergence
select a measurable limit gradient with the almost-every-time weak
spatial-gradient identity on the full open domain. -/
theorem compactness_gradient_limit_of_joint_limits
    {U : Set Vec3} {I : Set ℝ} (hU : IsOpen U)
    (u : ℕ → Vec3 × ℝ → Vec3)
    (Du : ℕ → Vec3 × ℝ → Fin 3 → Vec3)
    (v : Vec3 × ℝ → Vec3)
    (σ : ℕ → ℕ)
    (K : ℕ → Set Vec3) (J : ℕ → Set ℝ)
    (hK : ∀ j, IsCompact (K j) ∧ K j ⊆ U ∧
      K j ⊆ K (j + 1) ∧ K j ⊆ interior (K (j + 1)))
    (hKcover : ⋃ j, K j = U)
    (hJ : ∀ j, IsCompact (J j) ∧ J j ⊆ I ∧
      J j ⊆ J (j + 1) ∧ J j ⊆ interior (J (j + 1)))
    (hJcover : ⋃ j, J j = I)
    (hweakGrad : ∀ n, ∀ᵐ t ∂(volume.restrict I), ∀ i : Fin 3,
      CKN.HasWeakGradientOn U (fun x => u n (x,t) i)
        (fun x => Du n (x,t) i))
    (D : ∀ j, Lp CompactnessGradientFiber 2
      ((volume.restrict (K j)).prod (volume.restrict (J j))))
    (hDweak : ∀ j,
      ∃ hgrad : ∀ k, MemLp
        (fun z : Vec3 × ℝ => toCompactnessGradientFiber (Du (σ k) z)) 2
        ((volume.restrict (K j)).prod (volume.restrict (J j))),
        ∀ w, Tendsto
          (fun k => inner ℝ ((hgrad k).toLp
            (fun z => toCompactnessGradientFiber (Du (σ k) z))) w) atTop
          (nhds (inner ℝ (D j) w)))
    (hstrong : ∀ j, ∃ _hf : ∀ k, MemLp
      (fun z : Vec3 × ℝ => (WithLp.toLp 2 (u (σ k) z) : L2Vec3)) 2
      ((volume.restrict (K j)).prod (volume.restrict (J j))),
      Tendsto (fun k => eLpNorm
        ((fun z : Vec3 × ℝ => (WithLp.toLp 2 (u (σ k) z) : L2Vec3)) -
          (fun z : Vec3 × ℝ => (WithLp.toLp 2 (v z) : L2Vec3))) 2
        ((volume.restrict (K j)).prod (volume.restrict (J j))))
        atTop (nhds 0)) :
    ∃ g : Vec3 × ℝ → CompactnessGradientFiber,
      Measurable g ∧
      (∀ j, g =ᵐ[
        (volume.restrict (interior (K j))).prod (volume.restrict (J j))]
        compactnessGradientLocalRepresentative K J D j) ∧
      (∀ᵐ t ∂(volume.restrict I), ∀ i : Fin 3,
        HasWeakGradientOn U (fun x => v (x,t) i)
          (fun x m => g (x,t) i m)) := by
  let gLocal : ℕ → Vec3 × ℝ → CompactnessGradientFiber :=
    compactnessGradientLocalRepresentative K J D
  have hgLocalMeas (j : ℕ) : Measurable (gLocal j) :=
    measurable_compactnessGradientLocalRepresentative K J D j
  have hlocal (j : ℕ) (i m : Fin 3) :
      ∀ᵐ t ∂(volume.restrict (J j)),
        LocallyIntegrableOn
          (fun x => gLocal j (x,t) i m) (interior (K j)) volume ∧
        HasWeakPartialDerivOn (interior (K j)) m
          (fun x => v (x,t) i) (fun x => gLocal j (x,t) i m) :=
    compactnessGradientLocalRepresentative_weak_partial
      u Du v σ K J
      (fun a => ⟨(hK a).1, (hK a).2.1⟩)
      (fun a => ⟨(hJ a).1, (hJ a).2.1⟩)
      hweakGrad D hDweak hstrong j i m
  obtain ⟨g, hg, hEq⟩ :=
    exists_measurable_gradient_of_local_weak_partials
      K J (fun a => (hK a).2.2.1) (fun a => (hJ a).2.2.1)
      (fun a => (hJ a).1) v gLocal hgLocalMeas hlocal
  refine ⟨g, hg, hEq, ?_⟩
  change ∀ᵐ t ∂(volume.restrict I), ∀ i m : Fin 3,
    HasWeakPartialDerivOn U m (fun x => v (x,t) i)
      (fun x => g (x,t) i m)
  apply (ae_all_iff).mpr
  intro i
  apply (ae_all_iff).mpr
  intro m
  have hlocalG (j : ℕ) : ∀ᵐ t ∂(volume.restrict (J j)),
      HasWeakPartialDerivOn (interior (K j)) m
        (fun x => v (x,t) i) (fun x => g (x,t) i m) := by
    have heqTime := ae_ae_of_ae_prod_snd (hEq j)
    filter_upwards [hlocal j i m, heqTime] with t ht heq
    have heqCoord :
        (fun x => gLocal j (x,t) i m) =ᵐ[
          volume.restrict (interior (K j))]
        (fun x => g (x,t) i m) := by
      filter_upwards [heq] with x hx
      rw [hx]
    exact ht.2.congr_deriv_ae heqCoord
  exact ae_weak_partial_on_union_of_exhaustions hU K J
    (fun a => (hK a).2.2.1) (fun a => (hK a).2.2.2)
    hKcover (fun a => (hJ a).2.2.1) hJcover
    (fun z => v z i) (fun z => g z i m) m hlocalG

end CKN.Leray
