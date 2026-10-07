/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessSliceRepresentative

/-!
# Compactness Weak Local

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set Topology
open CKN.Foundation.Parabolic
open scoped ENNReal

namespace CKN.Leray

/-- Every time slice of the selected subsequence converges weakly on every
compact spatial subset to the jointly measurable representative. -/
theorem weak_slices_to_compactnessMollifiedLimit_on_compact
    {U : Set Vec3} {I : Set ℝ} (hI : IsOpen I)
    (u : ℕ → Vec3 × ℝ → Vec3) (σ : ℕ → ℕ)
    (huMeas : ∀ n, Measurable (u n))
    (K : ℕ → Set Vec3) (χ : ℕ → Vec3 → ℝ)
    (hK : ∀ j, IsCompact (K j) ∧ K j ⊆ U ∧
      K j ⊆ K (j + 1) ∧ K j ⊆ interior (K (j + 1)))
    (hKcover : ⋃ j, K j = U)
    (hχ : ∀ j x, x ∈ K j → χ j x = 1)
    (hbound : ∀ C : Set Vec3, IsCompact C → C ⊆ U →
      ∀ J : Set ℝ, IsCompact J → J ⊆ I →
      ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ n t,
        t ∈ J →
          (∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm (u n (x,t))) ^
            (2 : ℝ) ∂volume) ≤ M)
    (hmem : ∀ n j (t : I), MemLp
      (fun x => χ j x • WithLp.toLp 2 (u n (x,t.1)))
      2 (volume : Measure Vec3))
    (V : ℕ → I → Lp L2Vec3 2 (volume : Measure Vec3))
    (hweak : ∀ j t x, Tendsto
      (fun k => inner ℝ ((hmem (σ k) j t).toLp
        (fun y => χ j y • WithLp.toLp 2 (u (σ k) (y,t.1)))) x) atTop
      (nhds (inner ℝ (V j t) x)))
    (C : Set Vec3) (hC : IsCompact C) (hCU : C ⊆ U) (t : I) :
    ∃ hs : ∀ k, MemLp
      (fun x : Vec3 => (WithLp.toLp 2 (u (σ k) (x,t.1)) : L2Vec3))
      2 (volume.restrict C),
    ∃ hl : MemLp
      (fun x : Vec3 => (WithLp.toLp 2
        (compactnessMollifiedLimit u σ (x,t.1)) : L2Vec3))
      2 (volume.restrict C),
      ∀ w : Lp L2Vec3 2 (volume.restrict C),
        Tendsto (fun k => inner ℝ ((hs k).toLp
          (fun x => (WithLp.toLp 2 (u (σ k) (x,t.1)) : L2Vec3))) w)
          atTop (nhds (inner ℝ (hl.toLp
            (fun x => (WithLp.toLp 2
              (compactnessMollifiedLimit u σ (x,t.1)) : L2Vec3))) w)) := by
  classical
  obtain ⟨j, hCj⟩ := compact_subset_eventually_in_exhaustion
    hC hCU K (fun a => (hK a).2.2.1) (fun a => (hK a).2.2.2) hKcover
  let f (k : ℕ) (x : Vec3) := u (σ k) (x,t.1)
  let v (x : Vec3) := compactnessMollifiedLimit u σ (x,t.1)
  let hs : ∀ k, MemLp
      (fun x : Vec3 => (WithLp.toLp 2 (f k x) : L2Vec3))
      2 (volume.restrict C) := by
    intro k
    have hk := memLp_original_slice_on_exhaustion hI u huMeas K
      (fun a => ⟨(hK a).1, (hK a).2.1⟩) hbound (σ k) j t
    exact hk.mono_measure (Measure.restrict_mono_set volume hCj)
  have hvEq : (fun x : Vec3 => (WithLp.toLp 2 (v x) : L2Vec3)) =ᵐ[
      volume.restrict C] (fun x => V (j + 1) t x) := by
    have h := compactnessMollifiedLimit_ae_eq_on_exhaustion
      u σ K χ
      (fun a => ⟨(hK a).1, (hK a).2.2.1, (hK a).2.2.2⟩)
      hχ hmem V hweak j t
    have h' := ae_restrict_of_ae_restrict_of_subset hCj h
    filter_upwards [h'] with x hx
    change (WithLp.toLp 2
      (compactnessMollifiedLimit u σ (x,t.1)) : L2Vec3) = _
    rw [hx]
  let hl : MemLp (fun x : Vec3 => (WithLp.toLp 2 (v x) : L2Vec3))
      2 (volume.restrict C) :=
    (memLp_congr_ae hvEq).2 ((Lp.memLp (V (j + 1) t)).restrict C)
  have hχone : ∀ x ∈ C, χ (j + 1) x = 1 := by
    intro x hx
    exact hχ (j + 1) x ((hK j).2.2.1 (hCj hx))
  have hw := weak_local_slices_of_weak_cutoff hC.measurableSet
    f (χ (j + 1)) hχone
    (fun k => hmem (σ k) (j + 1) t) hs (V (j + 1) t)
    (hweak (j + 1) t)
  have heqLp : hl.toLp (fun x => (WithLp.toLp 2 (v x) : L2Vec3)) =
      ((Lp.memLp (V (j + 1) t)).restrict C).toLp
        (fun x => V (j + 1) t x) :=
    MemLp.toLp_congr hl ((Lp.memLp (V (j + 1) t)).restrict C) hvEq
  refine ⟨hs, hl, ?_⟩
  intro w
  simpa only [f, v, heqLp] using hw w

end CKN.Leray
