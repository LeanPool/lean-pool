/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessBallPairing
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Compactness Local Pairing

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open CKN.Foundation.Parabolic

namespace CKN.Leray

/-- The Hilbert pairing in vector-valued `L²` is the coordinatewise spatial
dot-product integral for an arbitrary measure. -/
theorem inner_toLp_vec3_eq_integral_dot_measure
    (μ : Measure Vec3)
    (f g : Vec3 → L2Vec3)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) =
      ∫ x, ∑ i : Fin 3, f x i * g x i ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  rw [hfx, hgx, PiLp.inner_apply]
  congr 1
  funext i
  exact Real.inner_apply _ _

/-- A test extended by zero turns a global cutoff pairing into the local
pairing wherever the cutoff equals one. -/
theorem inner_cutoff_indicator_eq_local_inner
    {C : Set Vec3} (hC : MeasurableSet C)
    (f : Vec3 → Vec3) (χ : Vec3 → ℝ)
    (hχone : ∀ x ∈ C, χ x = 1)
    (hfGlobal : MemLp (fun x => χ x • (WithLp.toLp 2 (f x) : L2Vec3))
      2 (volume : Measure Vec3))
    (hfLocal : MemLp (fun x => (WithLp.toLp 2 (f x) : L2Vec3))
      2 (volume.restrict C))
    (w : Vec3 → L2Vec3) (hwLocal : MemLp w 2 (volume.restrict C)) :
    inner ℝ (hfGlobal.toLp (fun x => χ x •
        (WithLp.toLp 2 (f x) : L2Vec3)))
      (((memLp_indicator_iff_restrict hC).mpr hwLocal).toLp
        (C.indicator w)) =
      inner ℝ (hfLocal.toLp (fun x =>
        (WithLp.toLp 2 (f x) : L2Vec3)))
        (hwLocal.toLp w) := by
  let ψ : Vec3 → L2Vec3 := C.indicator w
  let hψ : MemLp ψ 2 (volume : Measure Vec3) :=
    (memLp_indicator_iff_restrict hC).mpr hwLocal
  rw [inner_toLp_vec3_eq_integral_dot_measure volume _ _ hfGlobal hψ,
    inner_toLp_vec3_eq_integral_dot_measure (volume.restrict C) _ _
      hfLocal hwLocal]
  rw [← integral_indicator hC]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ C
  · simp [ψ, Set.indicator_of_mem hx, hχone x hx]
  · simp [ψ, Set.indicator_of_notMem hx]

/-- Weak convergence of global cutoff slices restricts to weak convergence on
any measurable region where the cutoff is one. -/
theorem weak_local_slices_of_weak_cutoff
    {C : Set Vec3} (hC : MeasurableSet C)
    (u : ℕ → Vec3 → Vec3) (χ : Vec3 → ℝ)
    (hχone : ∀ x ∈ C, χ x = 1)
    (hglobal : ∀ n, MemLp (fun x =>
      χ x • (WithLp.toLp 2 (u n x) : L2Vec3))
      2 (volume : Measure Vec3))
    (hlocal : ∀ n, MemLp (fun x =>
      (WithLp.toLp 2 (u n x) : L2Vec3)) 2 (volume.restrict C))
    (V : Lp L2Vec3 2 (volume : Measure Vec3))
    (hweak : ∀ w, Tendsto (fun n => inner ℝ
      ((hglobal n).toLp (fun x =>
        χ x • (WithLp.toLp 2 (u n x) : L2Vec3))) w) atTop
      (nhds (inner ℝ V w))) :
    ∀ w : Lp L2Vec3 2 (volume.restrict C),
      Tendsto (fun n => inner ℝ
        ((hlocal n).toLp (fun x =>
          (WithLp.toLp 2 (u n x) : L2Vec3))) w) atTop
      (nhds (inner ℝ (((Lp.memLp V).restrict C).toLp
        (fun x => V x)) w)) := by
  intro w
  let ψ : Vec3 → L2Vec3 := C.indicator (fun x => w x)
  let hψ : MemLp ψ 2 (volume : Measure Vec3) :=
    (memLp_indicator_iff_restrict hC).mpr (Lp.memLp w)
  let ψLp : Lp L2Vec3 2 (volume : Measure Vec3) := hψ.toLp ψ
  have hn (n : ℕ) :
      inner ℝ ((hglobal n).toLp (fun x =>
        χ x • (WithLp.toLp 2 (u n x) : L2Vec3))) ψLp =
      inner ℝ ((hlocal n).toLp (fun x =>
        (WithLp.toLp 2 (u n x) : L2Vec3))) w := by
    have h := inner_cutoff_indicator_eq_local_inner hC (u n) χ hχone
      (hglobal n) (hlocal n) (fun x => w x) (Lp.memLp w)
    simpa only [ψ, ψLp, Lp.toLp_coeFn w (Lp.memLp w)] using h
  have hv : inner ℝ V ψLp =
      inner ℝ (((Lp.memLp V).restrict C).toLp (fun x => V x)) w := by
    let f : Vec3 → Vec3 := fun x i => V x i
    have hfGlobal : MemLp (fun x => (1 : ℝ) •
        (WithLp.toLp 2 (f x) : L2Vec3)) 2
        (volume : Measure Vec3) := by
      simpa only [one_smul, f, WithLp.toLp_ofLp] using Lp.memLp V
    have hfLocal : MemLp (fun x =>
        (WithLp.toLp 2 (f x) : L2Vec3)) 2 (volume.restrict C) := by
      simpa only [f, WithLp.toLp_ofLp] using (Lp.memLp V).restrict C
    have h := inner_cutoff_indicator_eq_local_inner hC f (fun _ => 1)
      (fun _ _ => rfl) hfGlobal hfLocal (fun x => w x) (Lp.memLp w)
    simpa only [ψ, ψLp, f, one_smul, WithLp.toLp_ofLp,
      Lp.toLp_coeFn V (Lp.memLp V),
      Lp.toLp_coeFn w (Lp.memLp w)] using h
  simpa only [hn, hv] using hweak ψLp

end CKN.Leray
