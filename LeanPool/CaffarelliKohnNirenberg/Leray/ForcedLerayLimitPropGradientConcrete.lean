/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedLerayLimitPropGradient
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedLerayLimitCompactnessInputs
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedHopfEnergy
public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegularisedDissipation

/-!
# The gradient clauses of `prop:forced-limit`

For the forced regularized gradients along the subsequence of
the forced local compactness theorem (forcedLerayLimit_local_compactness), and every finite slab
`ℝ³ × (0,T)`: the weak limit `Du`, read off from the compactness gradient
limit, is square integrable on the slab and every coordinate of the gradients
converges to it weakly against every square-integrable test on the slab. The
local weak limits come from the compactness step on an exhaustion of the slab
by compact cylinders, and the uniform bound on the slab is the dissipation
bound of `lem:forced-energy-bounds`.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The compact cylinders exhausting the slab `ℝ³ × (0,T)`. -/
@[expose]
def forcedLerayLimitGradientCylinder (T : ℝ) (m : ℕ) : Set (Vec3 × ℝ) :=
  Metric.closedBall (0 : Vec3) (m : ℝ) ×ˢ Icc (T / ((m : ℝ) + 2)) (T - T / ((m : ℝ) + 2))

private theorem forcedLerayLimitGradientCylinder_subset {T : ℝ} (hT : 0 < T) (m : ℕ) :
    forcedLerayLimitGradientCylinder T m ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := by
  intro z hz
  have hpos : 0 < T / ((m : ℝ) + 2) := by positivity
  refine ⟨Set.mem_univ _, ?_, ?_⟩
  · exact lt_of_lt_of_le hpos hz.2.1
  · exact lt_of_le_of_lt hz.2.2 (by linarith only [hpos])

private theorem forcedLerayLimitGradientCylinder_subset_pos {T : ℝ} (hT : 0 < T) (m : ℕ) :
    forcedLerayLimitGradientCylinder T m ⊆ (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ) := by
  intro z hz
  exact ⟨Set.mem_univ _, ((forcedLerayLimitGradientCylinder_subset hT m) hz).2.1⟩

private theorem forcedLerayLimitGradientCylinder_isCompact (T : ℝ) (m : ℕ) :
    IsCompact (forcedLerayLimitGradientCylinder T m) :=
  (isCompact_closedBall _ _).prod isCompact_Icc

private theorem forcedLerayLimitGradientCylinder_aecover (T : ℝ) :
    AECover ((volume : Measure (Vec3 × ℝ)).restrict
      (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) atTop
      (forcedLerayLimitGradientCylinder T) := by
  have hSmeas : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) :
      Set (Vec3 × ℝ)) := MeasurableSet.univ.prod measurableSet_Ioo
  refine ⟨?_, fun m => (forcedLerayLimitGradientCylinder_isCompact T m).isClosed.measurableSet⟩
  refine (ae_restrict_iff' hSmeas).2 (Eventually.of_forall fun z hz => ?_)
  obtain ⟨-, ht0, htT⟩ := hz
  have hsmall : Tendsto (fun m : ℕ => T / ((m : ℝ) + 2)) atTop (𝓝 0) := by
    have h := tendsto_const_div_atTop_nhds_zero_nat T
    have hshift : Tendsto (fun m : ℕ => T / (((m + 2 : ℕ) : ℝ))) atTop (𝓝 0) :=
      h.comp (tendsto_add_atTop_nat 2)
    refine hshift.congr fun m => ?_
    push_cast
    ring
  have hδ : 0 < min z.2 (T - z.2) := lt_min ht0 (by linarith only [htT])
  have hev1 : ∀ᶠ m : ℕ in atTop, T / ((m : ℝ) + 2) < min z.2 (T - z.2) :=
    hsmall.eventually (gt_mem_nhds hδ)
  have hev2 : ∀ᶠ m : ℕ in atTop, ‖z.1‖ ≤ (m : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  filter_upwards [hev1, hev2] with m hm1 hm2
  have hm1a : T / ((m : ℝ) + 2) < z.2 := lt_of_lt_of_le hm1 (min_le_left _ _)
  have hm1b : T / ((m : ℝ) + 2) < T - z.2 := lt_of_lt_of_le hm1 (min_le_right _ _)
  refine ⟨?_, hm1a.le, by linarith only [hm1b]⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact hm2

/-- The uniform dissipation bound of `lem:forced-energy-bounds` for the forced
regularized gradients on a finite slab, in the norm of the gradient carrier. -/
private theorem forcedLerayLimitGradient_dissipation_bound
    (ρ : RegMollifierProfile) (a : Vec3 → Vec3) (ha : IsInJ a)
    (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
    (T : ℝ) (hT : 0 < T) :
    ∃ B : ℝ≥0∞, B < ⊤ ∧ ∀ (ε : ℝ), 0 < ε →
      (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
        ‖toCompactnessGradientFiber (forcedRegGradient ρ a ha f hf ε z)‖ₑ ^ (2 : ℝ)) ≤ B := by
  let A : ℝ := ∑ i : Fin 3, ∫ x : Vec3, a x i ^ 2
  let F : ℝ := ∑ i : Fin 3, ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), f z i ^ 2
  refine ⟨ENNReal.ofReal ((A + F + T * (Real.exp T * (A + F))) / 2),
    ENNReal.ofReal_lt_top, fun ε hε => ?_⟩
  obtain ⟨⟨hSlice, hcont, -, -⟩, -, hR2, -, hE⟩ := forcedRegularised ρ a ha f hf ε hε
  obtain ⟨-, hgrad⟩ := forcedLerayLimit_energy_bounds ρ ε hε a ha.1 f hf
    (forcedRegVelocity ρ a ha f hf ε) (forcedRegGradient ρ a ha f hf ε)
    hSlice hcont (fun S hS => (forcedRegVelocity_memLp_slab ρ a ha f hf ε hε S hS).1)
    (fun S hS => (hR2 S hS).1) (fun t ht => (hE t ht).2) T hT
  let u := forcedRegVelocity ρ a ha f hf ε
  let D := forcedRegGradient ρ a ha f hf ε
  have hpt : ∀ z : ParabolicPoint,
      ‖toCompactnessGradientFiber (D z)‖ₑ ^ (2 : ℝ) =
        ENNReal.ofReal (CKN.spatialGradientSq u D z) := by
    intro z
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num),
      ← norm_toCompactnessGradientFiber_sq u D z]
    congr 1
    exact Real.rpow_two _
  calc (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
        ‖toCompactnessGradientFiber (D z)‖ₑ ^ (2 : ℝ))
      = ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
          ENNReal.ofReal (CKN.spatialGradientSq u D z) := by
        simp only [hpt]
    _ = ENNReal.ofReal (∑ i : Fin 3, ∑ j : Fin 3,
          ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T), D z i j ^ 2) := by
        rw [← regUniformDissipation_eq_slab, forcedHopf_dissipation_eq_ofReal u D T
          (hR2 T hT).1]
    _ ≤ ENNReal.ofReal ((A + F + T * (Real.exp T * (A + F))) / 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        linarith only [hgrad]

/-- The gradient clauses of `prop:forced-limit` on every finite slab: for the
subsequence `σ` and the gradient limit `g` of
the forced local compactness theorem (forcedLerayLimit_local_compactness) (its third output is the
hypothesis `hgrad`), the field `Du z i j = g z i j` is strongly measurable and
square integrable on `ℝ³ × (0,T)`, and each coordinate of the forced
regularized gradients converges to it weakly against every square-integrable
test on the slab. -/
theorem forcedLerayLimit_gradient_clauses
    (ρ : RegMollifierProfile) (a : Vec3 → Vec3) (ha : IsInJ a)
    (f : ParabolicPoint → Vec3) (hf : IsLocallySquareIntegrableForce f)
    (εseq : ℕ → ℝ) (hseq : ∀ n, 0 < εseq n ∧ εseq n ≤ 1)
    (σ : ℕ → ℕ) (g : Vec3 × ℝ → CompactnessGradientFiber)
    (hgrad : ∀ Q : Set (Vec3 × ℝ), IsCompact Q → Q ⊆
        (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ) →
        ∃ hs : ∀ k, MemLp
          (fun z => toCompactnessGradientFiber
            (forcedRegGradient ρ a ha f hf (εseq (σ k)) z)) 2
          (volume.restrict Q),
        ∃ hg : MemLp g 2 (volume.restrict Q),
        ∀ w : Lp CompactnessGradientFiber 2 (volume.restrict Q),
          Tendsto (fun k => inner ℝ ((hs k).toLp
            (fun z => toCompactnessGradientFiber
              (forcedRegGradient ρ a ha f hf (εseq (σ k)) z))) w)
            atTop (nhds (inner ℝ (hg.toLp g) w)))
    (T : ℝ) (hT : 0 < T) :
    let μ : Measure ParabolicPoint :=
      volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))
    let Dseq : ℕ → ParabolicPoint → Fin 3 → Vec3 := fun n =>
      forcedRegGradient ρ a ha f hf (εseq (σ n))
    let Du : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
      WithLp.ofLp (g (parabolicHomeomorph z) i) j
    AEStronglyMeasurable Du μ ∧ MemLp Du 2 μ ∧
      (∀ i j, ∀ w : ParabolicPoint → ℝ, MemLp w 2 μ →
        Tendsto (fun n => ∫ z in spaceTimeSet
            (Set.univ : Set Vec3) (Ioo 0 T), Dseq n z i j * w z)
          atTop (nhds (∫ z in spaceTimeSet
            (Set.univ : Set Vec3) (Ioo 0 T), Du z i j * w z))) := by
  intro μ Dseq Du
  obtain ⟨B, hB, hbound⟩ := forcedLerayLimitGradient_dissipation_bound ρ a ha f hf T hT
  have hmain := forcedLerayLimit_globalGradient_outputs T
    (fun n z => forcedRegGradient ρ a ha f hf (εseq (σ n)) z) g
    (forcedLerayLimitGradientCylinder T)
    (forcedLerayLimitGradientCylinder_subset hT)
    (forcedLerayLimitGradientCylinder_aecover T) B hB
    (fun n => hbound (εseq (σ n)) (hseq (σ n)).1)
    (fun m => hgrad _ (forcedLerayLimitGradientCylinder_isCompact T m)
      (forcedLerayLimitGradientCylinder_subset_pos hT m))
  exact hmain

end CKN.Leray

end
