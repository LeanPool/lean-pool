/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessStrongRepresentative
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessTimeExhaustion

/-!
# Compactness Strong Local

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set Topology
open CKN.Foundation.Parabolic
open scoped ENNReal

namespace CKN.Leray

/-- Strong convergence on a nested rectangle exhaustion gives strong
convergence on every compact subset of the open product domain. -/
theorem strong_l2_on_compacts_of_exhaustion
    {U : Set Vec3} {I : Set ℝ}
    (K : ℕ → Set Vec3) (J : ℕ → Set ℝ)
    (hKmono : ∀ j, K j ⊆ K (j + 1))
    (hKinner : ∀ j, K j ⊆ interior (K (j + 1)))
    (hKcover : ⋃ j, K j = U)
    (hJmono : ∀ j, J j ⊆ J (j + 1))
    (hJinner : ∀ j, J j ⊆ interior (J (j + 1)))
    (hJcover : ⋃ j, J j = I)
    (f : ℕ → Vec3 × ℝ → L2Vec3) (g : Vec3 × ℝ → L2Vec3)
    (hstrong : ∀ j, Tendsto (fun k => eLpNorm (f k - g) 2
      ((volume.restrict (K j)).prod (volume.restrict (J j))))
      atTop (nhds 0)) :
    ∀ Q : Set (Vec3 × ℝ), IsCompact Q → Q ⊆ U ×ˢ I →
      Tendsto (fun k => eLpNorm (f k - g) 2
        (volume.restrict Q)) atTop (nhds 0) := by
  intro Q hQ hQI
  let C : Set Vec3 := Prod.fst '' Q
  let T : Set ℝ := Prod.snd '' Q
  have hC : IsCompact C := hQ.image continuous_fst
  have hT : IsCompact T := hQ.image continuous_snd
  have hCU : C ⊆ U := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact (hQI hz).1
  have hTI : T ⊆ I := by
    intro t ht
    obtain ⟨z, hz, rfl⟩ := ht
    exact (hQI hz).2
  obtain ⟨a, ha⟩ := compact_subset_eventually_in_exhaustion
    hC hCU K hKmono hKinner hKcover
  obtain ⟨b, hb⟩ := compact_time_subset_eventually_in_exhaustion
    hT hTI J hJmono hJinner hJcover
  let j := max a b
  have hKmonotone : Monotone K := monotone_nat_of_le_succ hKmono
  have hJmonotone : Monotone J := monotone_nat_of_le_succ hJmono
  have hQj : Q ⊆ K j ×ˢ J j := by
    intro z hz
    exact ⟨hKmonotone (le_max_left a b) (ha ⟨z, hz, rfl⟩),
      hJmonotone (le_max_right a b) (hb ⟨z, hz, rfl⟩)⟩
  have hmeasure : (volume : Measure (Vec3 × ℝ)).restrict Q ≤
      (volume.restrict (K j)).prod (volume.restrict (J j)) := by
    have hprod : (volume.restrict (K j)).prod (volume.restrict (J j)) =
        (volume : Measure (Vec3 × ℝ)).restrict (K j ×ˢ J j) := by
      change (volume.restrict (K j)).prod (volume.restrict (J j)) =
        ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
          (K j ×ˢ J j)
      rw [Measure.prod_restrict]
    rw [hprod]
    exact Measure.restrict_mono_set _ hQj
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  filter_upwards [(ENNReal.tendsto_nhds_zero.mp (hstrong j)) ε hε]
    with k hk
  exact (eLpNorm_mono_measure (f k - g) hmeasure).trans hk

/-- Every compact subset of an open product domain lies in an open inner
spatial member times a compact temporal member of nested exhaustions. -/
theorem compact_subset_inner_rectangle_exhaustion
    {U : Set Vec3} {I : Set ℝ}
    (K : ℕ → Set Vec3) (J : ℕ → Set ℝ)
    (hKmono : ∀ j, K j ⊆ K (j + 1))
    (hKinner : ∀ j, K j ⊆ interior (K (j + 1)))
    (hKcover : ⋃ j, K j = U)
    (hJmono : ∀ j, J j ⊆ J (j + 1))
    (hJinner : ∀ j, J j ⊆ interior (J (j + 1)))
    (hJcover : ⋃ j, J j = I)
    (Q : Set (Vec3 × ℝ)) (hQ : IsCompact Q)
    (hQI : Q ⊆ U ×ˢ I) :
    ∃ j, Q ⊆ interior (K j) ×ˢ J j := by
  let C : Set Vec3 := Prod.fst '' Q
  let T : Set ℝ := Prod.snd '' Q
  have hC : IsCompact C := hQ.image continuous_fst
  have hT : IsCompact T := hQ.image continuous_snd
  have hCU : C ⊆ U := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hx
    exact (hQI hz).1
  have hTI : T ⊆ I := by
    intro t ht
    obtain ⟨z, hz, rfl⟩ := ht
    exact (hQI hz).2
  obtain ⟨a, ha⟩ := compact_subset_eventually_in_exhaustion
    hC hCU K hKmono hKinner hKcover
  obtain ⟨b, hb⟩ := compact_time_subset_eventually_in_exhaustion
    hT hTI J hJmono hJinner hJcover
  let j := max (a + 1) b
  have hKmonotone : Monotone K := monotone_nat_of_le_succ hKmono
  have hJmonotone : Monotone J := monotone_nat_of_le_succ hJmono
  refine ⟨j, ?_⟩
  intro z hz
  exact ⟨interior_mono (hKmonotone (le_max_left (a + 1) b))
      (hKinner a (ha ⟨z, hz, rfl⟩)),
    hJmonotone (le_max_right (a + 1) b)
      (hb ⟨z, hz, rfl⟩)⟩

end CKN.Leray
