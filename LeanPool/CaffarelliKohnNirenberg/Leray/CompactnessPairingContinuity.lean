/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessSliceRepresentative
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessGradientRestriction

/-!
# Compactness Pairing Continuity

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set Topology
open CKN.Foundation.Parabolic
open scoped ENNReal

namespace CKN.Leray

/-- Pairing the selected representative against a fixed local L² test is
continuous in time. -/
theorem continuous_compactnessMollifiedLimit_local_pairing
    {U : Set Vec3} {I : Set ℝ}
    (u : ℕ → Vec3 × ℝ → Vec3) (σ : ℕ → ℕ)
    (K : ℕ → Set Vec3) (χ : ℕ → Vec3 → ℝ)
    (hK : ∀ j, IsCompact (K j) ∧ K j ⊆ U ∧
      K j ⊆ K (j + 1) ∧ K j ⊆ interior (K (j + 1)))
    (hKcover : ⋃ j, K j = U)
    (hχ : ∀ j x, x ∈ K j → χ j x = 1)
    (hmem : ∀ n j (t : I), MemLp
      (fun x => χ j x • WithLp.toLp 2 (u n (x, t.1)))
      2 (volume : Measure Vec3))
    (V : ℕ → I → Lp L2Vec3 2 (volume : Measure Vec3))
    (hweak : ∀ j t x, Tendsto
      (fun k => inner ℝ ((hmem (σ k) j t).toLp
        (fun y => χ j y • WithLp.toLp 2 (u (σ k) (y, t.1)))) x) atTop
      (nhds (inner ℝ (V j t) x)))
    (hVcont : ∀ j x, Continuous (fun t => inner ℝ (V j t) x))
    (C : Set Vec3) (hC : IsCompact C) (hCU : C ⊆ U)
    (w : Lp L2Vec3 2 (volume.restrict C)) :
    Continuous (fun t : I =>
      ∫ x in C, ∑ i : Fin 3,
        compactnessMollifiedLimit u σ (x, t.1) i * w x i) := by
  classical
  obtain ⟨j, hCj⟩ := compact_subset_eventually_in_exhaustion
    hC hCU K (fun a => (hK a).2.2.1)
    (fun a => (hK a).2.2.2) hKcover
  let ψ : Vec3 → L2Vec3 := C.indicator (fun x => w x)
  let hψ : MemLp ψ 2 (volume : Measure Vec3) :=
    (memLp_indicator_iff_restrict hC.measurableSet).mpr (Lp.memLp w)
  let ψLp : Lp L2Vec3 2 (volume : Measure Vec3) := hψ.toLp ψ
  have hEq (t : I) :
      (∫ x in C, ∑ i : Fin 3,
        compactnessMollifiedLimit u σ (x, t.1) i * w x i) =
        inner ℝ (V (j + 1) t) ψLp := by
    let f : Vec3 → L2Vec3 := fun x =>
      WithLp.toLp 2 (compactnessMollifiedLimit u σ (x, t.1))
    have hfK := compactnessMollifiedLimit_memLp_on_exhaustion
      u σ K χ
      (fun a => ⟨(hK a).1, (hK a).2.2.1, (hK a).2.2.2⟩)
      hχ hmem V hweak j t
    have hf : MemLp f 2 (volume.restrict C) :=
      hfK.mono_measure (Measure.restrict_mono_set volume hCj)
    have hV : MemLp (fun x => V (j + 1) t x) 2
        (volume.restrict C) :=
      (Lp.memLp (V (j + 1) t)).restrict C
    have hrep := compactnessMollifiedLimit_ae_eq_on_exhaustion
      u σ K χ
      (fun a => ⟨(hK a).1, (hK a).2.2.1, (hK a).2.2.2⟩)
      hχ hmem V hweak j t
    have hrepC : f =ᵐ[volume.restrict C]
        (fun x => V (j + 1) t x) := by
      have h' := ae_restrict_of_ae_restrict_of_subset hCj hrep
      filter_upwards [h'] with x hx
      change (WithLp.toLp 2
        (compactnessMollifiedLimit u σ (x, t.1)) : L2Vec3) = _
      rw [hx]
    have hLpEq : hf.toLp f = hV.toLp (fun x => V (j + 1) t x) :=
      MemLp.toLp_congr hf hV hrepC
    have hpair := inner_indicator_eq_restricted_inner
      C hC.measurableSet (fun x => V (j + 1) t x)
      (Lp.memLp (V (j + 1) t)) w
    calc
      (∫ x in C, ∑ i : Fin 3,
        compactnessMollifiedLimit u σ (x, t.1) i * w x i) =
          inner ℝ (hf.toLp f) w := by
            simpa only [f, Lp.toLp_coeFn w (Lp.memLp w)] using
              (inner_toLp_vec3_eq_integral_dot_measure
                (volume.restrict C) f (fun x => w x) hf (Lp.memLp w)).symm
      _ = inner ℝ (hV.toLp (fun x => V (j + 1) t x)) w := by rw [hLpEq]
      _ = inner ℝ (V (j + 1) t) ψLp := by
        simpa only [ψ, hψ, ψLp, Lp.toLp_coeFn
          (V (j + 1) t) (Lp.memLp (V (j + 1) t))] using hpair.symm
  simpa only [hEq] using hVcont (j + 1) ψLp

end CKN.Leray
