/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitSlices
public import LeanPool.CaffarelliKohnNirenberg.Leray.LerayLimitSlices2

/-!
# Leray Limit Slice Bridge

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- Local every-time weak limits and uniform energy bounds give global
L² slices and global weak convergence on every positive-time slice. -/
theorem lerayLimit_globalSlices_of_localWeak
    (F : ℕ → ℝ → Vec3 → Vec3) (u : ℝ → Vec3 → Vec3)
    (K : ℕ → Set Vec3)
    (hK : AECover (volume : Measure Vec3) atTop K)
    (C : ℝ) (hC : 0 ≤ C)
    (hFmeas : ∀ n t, Measurable (fun x : Vec3 => F n t x))
    (humeas : ∀ t, Measurable (fun x : Vec3 => u t x))
    (hFbound : ∀ t n k,
      (∫⁻ x in K k,
        ENNReal.ofReal (vec3EuclideanNorm (F n t x)) ^ (2 : ℝ)
        ∂volume) ≤ ENNReal.ofReal C ^ (2 : ℕ))
    (hubound : ∀ t, 0 < t → ∀ k,
      (∫⁻ x in K k,
        ENNReal.ofReal (vec3EuclideanNorm (u t x)) ^ (2 : ℝ)
        ∂volume) ≤ ENNReal.ofReal C ^ (2 : ℕ))
    (hlocal : ∀ t, 0 < t → ∀ (v : Vec3 → L2Vec3),
      HasCompactSupport v → Continuous v → (hv : MemLp v 2 volume) →
      ∀ (hF : ∀ n, MemLp
          (fun x : Vec3 => (WithLp.toLp 2 (F n t x) : L2Vec3)) 2 volume)
        (hu : MemLp
          (fun x : Vec3 => (WithLp.toLp 2 (u t x) : L2Vec3)) 2 volume),
      Tendsto
        (fun n => inner ℝ
          ((hF n).toLp (fun x => WithLp.toLp 2 (F n t x)))
          (hv.toLp v)) atTop
        (𝓝 (inner ℝ
          (hu.toLp (fun x => WithLp.toLp 2 (u t x)))
          (hv.toLp v)))) :
    ∀ t, (ht : 0 < t) →
      ∃ hF : ∀ n, MemLp
        (fun x : Vec3 => (WithLp.toLp 2 (F n t x) : L2Vec3)) 2 volume,
      ∃ hu : MemLp
        (fun x : Vec3 => (WithLp.toLp 2 (u t x) : L2Vec3)) 2 volume,
      (∀ n, ‖(hF n).toLp (fun x => WithLp.toLp 2 (F n t x))‖ ≤ C) ∧
      ‖hu.toLp (fun x => WithLp.toLp 2 (u t x))‖ ≤ C ∧
      ∀ (w : Vec3 → L2Vec3), (hw : MemLp w 2 volume) →
        Tendsto
          (fun n => inner ℝ
            ((hF n).toLp (fun x => WithLp.toLp 2 (F n t x)))
            (hw.toLp w)) atTop
          (𝓝 (inner ℝ
            (hu.toLp (fun x => WithLp.toLp 2 (u t x)))
            (hw.toLp w))) := by
  intro t ht
  have hFslice (n : ℕ) : MemLp
      (fun x : Vec3 => (WithLp.toLp 2 (F n t x) : L2Vec3)) 2 volume :=
    (lerayLimit_slice_memLp_of_compactIntegralBounds
      (fun s x => F n s x) K hK C hC (hFmeas n)
      (fun s _ k => hFbound s n k) t ht).choose
  have huslice : MemLp
      (fun x : Vec3 => (WithLp.toLp 2 (u t x) : L2Vec3)) 2 volume :=
    (lerayLimit_slice_memLp_of_compactIntegralBounds
      u K hK C hC humeas hubound t ht).choose
  have hFnorm (n : ℕ) : ‖(hFslice n).toLp
      (fun x => WithLp.toLp 2 (F n t x))‖ ≤ C :=
    (lerayLimit_slice_memLp_of_compactIntegralBounds
      (fun s x => F n s x) K hK C hC (hFmeas n)
      (fun s _ k => hFbound s n k) t ht).choose_spec
  have hunorm : ‖huslice.toLp
      (fun x => WithLp.toLp 2 (u t x))‖ ≤ C :=
    (lerayLimit_slice_memLp_of_compactIntegralBounds
      u K hK C hC humeas hubound t ht).choose_spec
  refine ⟨hFslice, huslice, ?_, hunorm, ?_⟩
  · exact hFnorm
  · intro w hw
    exact lerayLimit_globalWeakLp_of_compactSupport
      (fun n x => (WithLp.toLp 2 (F n t x) : L2Vec3))
      (fun x => (WithLp.toLp 2 (u t x) : L2Vec3))
      hFslice huslice C hC hFnorm hunorm
      (fun v hvSupport hvContinuous hv =>
        hlocal t ht v hvSupport hvContinuous hv hFslice huslice)
      w hw

end CKN.Leray

end
