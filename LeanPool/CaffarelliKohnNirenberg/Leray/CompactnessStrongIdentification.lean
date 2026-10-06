/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessLimitSlices

/-!
# Compactness Strong Identification

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set
open CKN.Foundation.Parabolic
open scoped ENNReal

namespace CKN.Leray

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- A local strong space-time limit is the jointly measurable representative
of the all-time weak slice limit. -/
theorem strong_product_limit_ae_eq_of_weak_slices
    {K : Set Vec3} {J : Set ℝ}
    [IsFiniteMeasure (volume.restrict K)]
    [IsFiniteMeasure (volume.restrict J)]
    (hJ : MeasurableSet J)
    (f : ℕ → Vec3 × ℝ → L2Vec3)
    (u : Vec3 × ℝ → L2Vec3) (hu : Measurable u)
    (hf : ∀ n, MemLp (f n) 2
      ((volume.restrict K).prod (volume.restrict J)))
    (G : Lp L2Vec3 2 ((volume.restrict K).prod (volume.restrict J)))
    (hstrong : Tendsto (fun n => (hf n).toLp (f n)) atTop (nhds G))
    (hfslice : ∀ n t, t ∈ J →
      MemLp (fun x : Vec3 => f n (x,t)) 2 (volume.restrict K))
    (huslice : ∀ t, t ∈ J →
      MemLp (fun x : Vec3 => u (x,t)) 2 (volume.restrict K))
    (hweak : ∀ t, (ht : t ∈ J) → ∀ w : Lp L2Vec3 2
        (volume.restrict K), Tendsto
      (fun n => inner ℝ ((hfslice n t ht).toLp
        (fun x => f n (x,t))) w) atTop
      (nhds (inner ℝ ((huslice t ht).toLp
        (fun x => u (x,t))) w)))
    (hbound : ∃ B : ℝ≥0∞, B < ⊤ ∧
      ∀ n t, t ∈ J → eLpNorm (fun x : Vec3 => f n (x,t)) 2
        (volume.restrict K) ≤ B) :
    (fun z => G z) =ᵐ[
      (volume.restrict K).prod (volume.restrict J)] u := by
  let μ : Measure Vec3 := volume.restrict K
  let ν : Measure ℝ := volume.restrict J
  let ρ : Measure (Vec3 × ℝ) := μ.prod ν
  let g : Vec3 × ℝ → L2Vec3 :=
    (Lp.memLp G).aestronglyMeasurable.mk (fun z => G z)
  have hgMeas : Measurable g :=
    (Lp.memLp G).aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hGg : (fun z => G z) =ᵐ[ρ] g :=
    (Lp.memLp G).aestronglyMeasurable.ae_eq_mk
  have hg : MemLp g 2 ρ := (memLp_congr_ae hGg).1 (Lp.memLp G)
  have hstrong0 : Tendsto (fun n => eLpNorm (f n - g) 2 ρ)
      atTop (nhds 0) := by
    have htoLp : (hg.toLp g) = G :=
      (MemLp.toLp_congr (Lp.memLp G) hg hGg).symm.trans
        (Lp.toLp_coeFn G (Lp.memLp G))
    have hstrong' : Tendsto (fun n => (hf n).toLp (f n))
        atTop (nhds (hg.toLp g)) := by simpa only [htoLp] using hstrong
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf g hg).mp hstrong'
  obtain ⟨τ, hτ, hae⟩ :=
    exists_subsequence_ae_slices_of_strong_product_l2
      f g hf hg hstrong0
  have hgSlice := ae_memLp_slice_of_memLp_product_vec3 g hg
  have hEqSections : ∀ᵐ t ∂ν, ∀ᵐ x ∂μ, g (x,t) = u (x,t) := by
    filter_upwards [hae, hgSlice, ae_restrict_mem hJ]
      with t htAE htG htJ
    have hft (k : ℕ) : MemLp (fun x : Vec3 => f (τ k) (x,t)) 2 μ :=
      hfslice (τ k) t htJ
    have hut : MemLp (fun x : Vec3 => u (x,t)) 2 μ := huslice t htJ
    let v : Lp L2Vec3 2 μ := hut.toLp (fun x => u (x,t))
    have hweakτ (w : Lp L2Vec3 2 μ) : Tendsto
        (fun k => inner ℝ ((hft k).toLp
          (fun x => f (τ k) (x,t))) w) atTop
        (nhds (inner ℝ v w)) :=
      (hweak t htJ w).comp hτ.tendsto_atTop
    obtain ⟨B, hB, hBb⟩ := hbound
    have hboundτ : ∃ B : ℝ≥0∞, B < ⊤ ∧
        ∀ k, eLpNorm (fun x : Vec3 => f (τ k) (x,t)) 2 μ ≤ B :=
      ⟨B, hB, fun k => hBb (τ k) t htJ⟩
    have hEq := ae_eq_of_weak_l2_and_ae_tendsto μ
      (fun k x => f (τ k) (x,t)) (fun x => g (x,t)) v
      hft htG hboundτ htAE hweakτ
    have hvEq : (fun x : Vec3 => v x) =ᵐ[μ]
        (fun x => u (x,t)) := hut.coeFn_toLp
    exact hEq.trans hvEq
  have hMeasEq : MeasurableSet {z : Vec3 × ℝ | g z = u z} :=
    measurableSet_eq_fun hgMeas hu
  have hEqProd : g =ᵐ[ρ] u := by
    apply (Measure.ae_prod_iff_ae_ae hMeasEq).2
    exact (Measure.ae_ae_comm hMeasEq).2 hEqSections
  exact hGg.trans hEqProd

end CKN.Leray
