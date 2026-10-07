/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessGradientLimit
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessGradientRestriction
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessStrongLocal

/-!
# Compactness Gradient Weak Local

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set Topology
open CKN.Foundation.Parabolic
open scoped ENNReal

namespace CKN.Leray

/-- The jointly measurable gradient limit is the weak local L² limit of
the selected matrix gradients on every compact space-time set. -/
theorem weak_gradient_to_measurable_limit_on_compact
    {U : Set Vec3} {I : Set ℝ}
    (Du : ℕ → Vec3 × ℝ → Fin 3 → Vec3)
    (σ : ℕ → ℕ)
    (K : ℕ → Set Vec3) (J : ℕ → Set ℝ)
    (hK : ∀ j, IsCompact (K j) ∧ K j ⊆ U ∧
      K j ⊆ K (j + 1) ∧ K j ⊆ interior (K (j + 1)))
    (hKcover : ⋃ j, K j = U)
    (hJ : ∀ j, IsCompact (J j) ∧ J j ⊆ I ∧
      J j ⊆ J (j + 1) ∧ J j ⊆ interior (J (j + 1)))
    (hJcover : ⋃ j, J j = I)
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
    (g : Vec3 × ℝ → CompactnessGradientFiber)
    (hgEq : ∀ j, g =ᵐ[
      (volume.restrict (interior (K j))).prod (volume.restrict (J j))]
      compactnessGradientLocalRepresentative K J D j)
    (Q : Set (Vec3 × ℝ)) (hQ : IsCompact Q)
    (hQI : Q ⊆ U ×ˢ I) :
    ∃ hs : ∀ k, MemLp
      (fun z => toCompactnessGradientFiber (Du (σ k) z)) 2
        (volume.restrict Q),
    ∃ hl : MemLp g 2 (volume.restrict Q),
      ∀ w : Lp CompactnessGradientFiber 2 (volume.restrict Q),
        Tendsto (fun k => inner ℝ ((hs k).toLp
          (fun z => toCompactnessGradientFiber (Du (σ k) z))) w) atTop
          (nhds (inner ℝ (hl.toLp g) w)) := by
  obtain ⟨j, hQinner⟩ := compact_subset_inner_rectangle_exhaustion
    K J (fun a => (hK a).2.2.1) (fun a => (hK a).2.2.2)
    hKcover (fun a => (hJ a).2.2.1)
    (fun a => (hJ a).2.2.2) hJcover Q hQ hQI
  let R : Set (Vec3 × ℝ) := K j ×ˢ J j
  let S : Set (Vec3 × ℝ) := interior (K j) ×ˢ J j
  let ρ : Measure (Vec3 × ℝ) :=
    (volume.restrict (K j)).prod (volume.restrict (J j))
  let ρS : Measure (Vec3 × ℝ) :=
    (volume.restrict (interior (K j))).prod
      (volume.restrict (J j))
  have hQR : Q ⊆ R := by
    intro z hz
    exact ⟨interior_subset (hQinner hz).1, (hQinner hz).2⟩
  have hρ : ρ = (volume : Measure (Vec3 × ℝ)).restrict R := by
    change (volume.restrict (K j)).prod (volume.restrict (J j)) =
      ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        (K j ×ˢ J j)
    rw [Measure.prod_restrict]
  have hρS : ρS = (volume : Measure (Vec3 × ℝ)).restrict S := by
    change (volume.restrict (interior (K j))).prod
      (volume.restrict (J j)) =
      ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        (interior (K j) ×ˢ J j)
    rw [Measure.prod_restrict]
  have hρQ : ρ.restrict Q = (volume : Measure (Vec3 × ℝ)).restrict Q := by
    rw [hρ, Measure.restrict_restrict_of_subset hQR]
  have hDlocal : (fun z => D j z) =ᵐ[
      (volume : Measure (Vec3 × ℝ)).restrict Q]
      compactnessGradientLocalRepresentative K J D j := by
    have h := compactnessGradientLocalRepresentative_ae_eq K J D j
    change (fun z => D j z) =ᵐ[ρ]
      compactnessGradientLocalRepresentative K J D j at h
    rw [hρ] at h
    exact ae_restrict_of_ae_restrict_of_subset hQR h
  have hglocal : g =ᵐ[(volume : Measure (Vec3 × ℝ)).restrict Q]
      compactnessGradientLocalRepresentative K J D j := by
    have h := hgEq j
    change g =ᵐ[ρS]
      compactnessGradientLocalRepresentative K J D j at h
    rw [hρS] at h
    exact ae_restrict_of_ae_restrict_of_subset hQinner h
  have hDg : (fun z => D j z) =ᵐ[
      (volume : Measure (Vec3 × ℝ)).restrict Q] g :=
    hDlocal.trans hglocal.symm
  obtain ⟨hgrad, hweak⟩ := hDweak j
  let hs : ∀ k, MemLp
      (fun z => toCompactnessGradientFiber (Du (σ k) z)) 2
        (volume.restrict Q) := by
    intro k
    have hk := (hgrad k).restrict Q
    rwa [hρQ] at hk
  have hDmem : MemLp (fun z => D j z) 2 (volume.restrict Q) := by
    have hd := (Lp.memLp (D j)).restrict Q
    rwa [hρQ] at hd
  let hl : MemLp g 2 (volume.restrict Q) :=
    (memLp_congr_ae hDg).1 hDmem
  have hEqLp : hDmem.toLp (fun z => D j z) = hl.toLp g :=
    MemLp.toLp_congr hDmem hl hDg
  refine ⟨hs, hl, ?_⟩
  intro w
  have h := weak_l2_restrict_of_weak_l2 Q hQ.measurableSet
    (fun k z => toCompactnessGradientFiber (Du (σ k) z))
    (D j) hgrad hweak
  have h' : ∀ w : Lp CompactnessGradientFiber 2 (volume.restrict Q),
      Tendsto (fun k => inner ℝ ((hs k).toLp
        (fun z => toCompactnessGradientFiber (Du (σ k) z))) w) atTop
        (nhds (inner ℝ (hDmem.toLp (fun z => D j z)) w)) := by
    exact weak_l2_of_measure_eq hρQ
      (fun k z => toCompactnessGradientFiber (Du (σ k) z))
      (fun z => D j z)
      (fun k => (hgrad k).restrict Q)
      ((Lp.memLp (D j)).restrict Q) hs hDmem h
  simpa only [hEqLp] using h' w

end CKN.Leray
