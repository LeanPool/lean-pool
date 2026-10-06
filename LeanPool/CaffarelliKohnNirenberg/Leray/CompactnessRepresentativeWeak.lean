/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessMollifierTest
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessRepresentative
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessMollifierSupport
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessMollifierLp
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessRepresentativeAE

/-!
# Compactness Representative Weak

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set
open CKN.Foundation.Parabolic

namespace CKN.Leray

/-- At a fixed spatial scale, weak convergence of cutoff slices identifies
the pointwise limit of their mollifications at every time. -/
theorem tendsto_mollified_component_of_weak_cutoff
    {I : Set ℝ}
    (u : ℕ → (Vec3 × ℝ) → Vec3) (σ : ℕ → ℕ)
    (χ : Vec3 → ℝ)
    (hmem : ∀ n (t : I), MemLp
       (fun y => χ y • WithLp.toLp 2 (u n (y, t.1)))
      2 (volume : Measure Vec3))
    (V : I → Lp L2Vec3 2 (volume : Measure Vec3))
    (hweak : ∀ t x, Tendsto
      (fun k => inner ℝ ((hmem (σ k) t).toLp
         (fun y => χ y • WithLp.toLp 2 (u (σ k) (y, t.1)))) x) atTop
      (nhds (inner ℝ (V t) x)))
    (m : ℕ) (x : Vec3) (i : Fin 3) (t : I)
    (hχ : ∀ y, CKN.mollifier (d := 3) (CKN.sliceRadius m)
      (CKN.sliceRadius_pos m) (x - y) ≠ 0 → χ y = 1) :
    Tendsto (fun k =>
      CKN.mollify (fun y => u (σ k) (y,t.1) i)
        (CKN.sliceRadius m) (CKN.sliceRadius_pos m) x) atTop
      (nhds (inner ℝ (V t)
        ((memLp_reflected_mollifier_coordinate m x i).toLp
          (fun y : Vec3 =>
            (WithLp.toLp 2 (Pi.single i
              (CKN.mollifier (d := 3) (CKN.sliceRadius m)
                (CKN.sliceRadius_pos m) (x - y))) : L2Vec3))))) := by
  let ψ : Lp L2Vec3 2 (volume : Measure Vec3) :=
    (memLp_reflected_mollifier_coordinate m x i).toLp
      (fun y : Vec3 =>
        (WithLp.toLp 2 (Pi.single i
          (CKN.mollifier (d := 3) (CKN.sliceRadius m)
            (CKN.sliceRadius_pos m) (x - y))) : L2Vec3))
  have hEq (k : ℕ) :
      CKN.mollify (fun y => u (σ k) (y,t.1) i)
        (CKN.sliceRadius m) (CKN.sliceRadius_pos m) x =
        inner ℝ ((hmem (σ k) t).toLp
          (fun y => χ y • WithLp.toLp 2 (u (σ k) (y,t.1)))) ψ :=
    mollify_component_eq_cutoff_inner
      (fun y => u (σ k) (y,t.1)) χ (hmem (σ k) t) m x i hχ
  simpa only [ψ, hEq] using hweak t ψ

/-- On a compact region where a cutoff is one, all sufficiently small
mollifications converge to those of the weak slice limit. -/
theorem eventually_mollified_component_eq_weak_slice
    {I : Set ℝ} {K W : Set Vec3}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (u : ℕ → (Vec3 × ℝ) → Vec3) (σ : ℕ → ℕ)
    (χ : Vec3 → ℝ) (hχone : ∀ x ∈ W, χ x = 1)
    (hmem : ∀ n (t : I), MemLp
       (fun y => χ y • WithLp.toLp 2 (u n (y, t.1)))
      2 (volume : Measure Vec3))
    (V : I → Lp L2Vec3 2 (volume : Measure Vec3))
    (hweak : ∀ t x, Tendsto
      (fun k => inner ℝ ((hmem (σ k) t).toLp
         (fun y => χ y • WithLp.toLp 2 (u (σ k) (y, t.1)))) x) atTop
      (nhds (inner ℝ (V t) x))) :
    ∀ (t : I) x, x ∈ K → ∀ i : Fin 3,
      ∀ᶠ m : ℕ in atTop,
        limUnder atTop (fun k : ℕ =>
          CKN.mollify (fun y : Vec3 => u (σ k) (y,t.1) i)
            (CKN.sliceRadius m) (CKN.sliceRadius_pos m) x) =
          CKN.mollify (fun y : Vec3 => V t y i)
            (CKN.sliceRadius m) (CKN.sliceRadius_pos m) x := by
  obtain ⟨m₀, hsupp⟩ :=
    eventually_reflected_mollifier_supported_in_open hK hW hKW
  intro t x hx i
  apply Filter.eventually_atTop.mpr
  refine ⟨m₀, fun m hm => ?_⟩
  have hχ (y : Vec3) (hy : CKN.mollifier (d := 3)
      (CKN.sliceRadius m) (CKN.sliceRadius_pos m) (x - y) ≠ 0) :
      χ y = 1 := hχone y (hsupp m hm x hx y hy)
  have hlim := tendsto_mollified_component_of_weak_cutoff
    u σ χ hmem V hweak m x i t hχ
  calc
    limUnder atTop (fun k : ℕ =>
        CKN.mollify (fun y : Vec3 => u (σ k) (y,t.1) i)
          (CKN.sliceRadius m) (CKN.sliceRadius_pos m) x) =
      inner ℝ (V t)
        ((memLp_reflected_mollifier_coordinate m x i).toLp
          (fun y : Vec3 =>
            (WithLp.toLp 2 (Pi.single i
              (CKN.mollifier (d := 3) (CKN.sliceRadius m)
                (CKN.sliceRadius_pos m) (x - y))) : L2Vec3))) :=
      hlim.limUnder_eq
    _ = CKN.mollify (fun y : Vec3 => V t y i)
          (CKN.sliceRadius m) (CKN.sliceRadius_pos m) x :=
      (mollify_lp_component_eq_inner (V t) m x i).symm

/-- The jointly measurable mollified limit represents every weak slice on
each compact region where the selected cutoff is one nearby. -/
theorem compactnessMollifiedLimit_ae_eq_weak_slice
    {I : Set ℝ} {K W : Set Vec3}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (u : ℕ → (Vec3 × ℝ) → Vec3) (σ : ℕ → ℕ)
    (χ : Vec3 → ℝ) (hχone : ∀ x ∈ W, χ x = 1)
    (hmem : ∀ n (t : I), MemLp
       (fun y => χ y • WithLp.toLp 2 (u n (y, t.1)))
      2 (volume : Measure Vec3))
    (V : I → Lp L2Vec3 2 (volume : Measure Vec3))
    (hweak : ∀ t x, Tendsto
      (fun k => inner ℝ ((hmem (σ k) t).toLp
         (fun y => χ y • WithLp.toLp 2 (u (σ k) (y, t.1)))) x) atTop
      (nhds (inner ℝ (V t) x))) :
    ∀ t : I, ∀ᵐ x ∂(volume.restrict K),
      compactnessMollifiedLimit u σ (x,t.1) = fun i => V t x i := by
  exact compactnessMollifiedLimit_ae_eq_weak_slice_on hK.measurableSet
    u σ V
    (eventually_mollified_component_eq_weak_slice
      hK hW hKW u σ χ hχone hmem V hweak)

end CKN.Leray
