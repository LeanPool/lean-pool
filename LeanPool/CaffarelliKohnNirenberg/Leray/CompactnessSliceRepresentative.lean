/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessJointExtract
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessRepresentativeWeak
public import LeanPool.CaffarelliKohnNirenberg.Leray.CompactnessLocalPairing

/-!
# Compactness Slice Representative

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Filter Set Topology
open CKN.Foundation.Parabolic
open scoped ENNReal

namespace CKN.Leray

/-- The measurable mollified representative agrees with every weak slice
limit on the compact exhaustion. -/
theorem compactnessMollifiedLimit_ae_eq_on_exhaustion
    {I : Set ℝ}
    (u : ℕ → Vec3 × ℝ → Vec3) (σ : ℕ → ℕ)
    (K : ℕ → Set Vec3) (χ : ℕ → Vec3 → ℝ)
    (hK : ∀ j, IsCompact (K j) ∧ K j ⊆ K (j + 1) ∧
      K j ⊆ interior (K (j + 1)))
    (hχ : ∀ j x, x ∈ K j → χ j x = 1)
    (hmem : ∀ n j (t : I), MemLp
      (fun x => χ j x • WithLp.toLp 2 (u n (x,t.1)))
      2 (volume : Measure Vec3))
    (V : ℕ → I → Lp L2Vec3 2 (volume : Measure Vec3))
    (hweak : ∀ j t x, Tendsto
      (fun k => inner ℝ ((hmem (σ k) j t).toLp
        (fun y => χ j y • WithLp.toLp 2 (u (σ k) (y,t.1)))) x) atTop
      (nhds (inner ℝ (V j t) x))) :
    ∀ j (t : I), ∀ᵐ x ∂(volume.restrict (K j)),
      compactnessMollifiedLimit u σ (x,t.1) =
        fun i => V (j + 1) t x i := by
  intro j t
  exact compactnessMollifiedLimit_ae_eq_weak_slice
    (hK j).1 isOpen_interior (hK j).2.2
    u σ (χ (j + 1))
    (fun x hx => hχ (j + 1) x (interior_subset hx))
    (fun n t => hmem n (j + 1) t) (V (j + 1))
    (hweak (j + 1)) t

/-- The measurable representative has the same `L²` class as the local weak
limit on every member of the exhaustion. -/
theorem compactnessMollifiedLimit_memLp_on_exhaustion
    {I : Set ℝ} (u : ℕ → Vec3 × ℝ → Vec3) (σ : ℕ → ℕ)
    (K : ℕ → Set Vec3) (χ : ℕ → Vec3 → ℝ)
    (hK : ∀ j, IsCompact (K j) ∧ K j ⊆ K (j + 1) ∧
      K j ⊆ interior (K (j + 1)))
    (hχ : ∀ j x, x ∈ K j → χ j x = 1)
    (hmem : ∀ n j (t : I), MemLp
      (fun x => χ j x • WithLp.toLp 2 (u n (x,t.1)))
      2 (volume : Measure Vec3))
    (V : ℕ → I → Lp L2Vec3 2 (volume : Measure Vec3))
    (hweak : ∀ j t x, Tendsto
      (fun k => inner ℝ ((hmem (σ k) j t).toLp
        (fun y => χ j y • WithLp.toLp 2 (u (σ k) (y,t.1)))) x) atTop
      (nhds (inner ℝ (V j t) x))) :
    ∀ j (t : I), MemLp
      (fun x : Vec3 => (WithLp.toLp 2
        (compactnessMollifiedLimit u σ (x,t.1)) : L2Vec3)) 2
      (volume.restrict (K j)) := by
  intro j t
  have hrep := compactnessMollifiedLimit_ae_eq_on_exhaustion
    u σ K χ hK hχ hmem V hweak j t
  have heq : (fun x : Vec3 => (WithLp.toLp 2
      (compactnessMollifiedLimit u σ (x,t.1)) : L2Vec3)) =ᵐ[
        volume.restrict (K j)] (fun x => V (j + 1) t x) := by
    filter_upwards [hrep] with x hx
    rw [hx]
  exact (memLp_congr_ae heq).2
    ((Lp.memLp (V (j + 1) t)).restrict (K j))

/-- Uniform local slice energy puts each original slice in the `L²` space
of every compact member of the spatial exhaustion. -/
theorem memLp_original_slice_on_exhaustion
    {U : Set Vec3} {I : Set ℝ} (hI : IsOpen I)
    (u : ℕ → Vec3 × ℝ → Vec3)
    (huMeas : ∀ n, Measurable (u n))
    (K : ℕ → Set Vec3)
    (hK : ∀ j, IsCompact (K j) ∧ K j ⊆ U)
    (hbound : ∀ C : Set Vec3, IsCompact C → C ⊆ U →
      ∀ J : Set ℝ, IsCompact J → J ⊆ I →
      ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ n t,
        t ∈ J →
          (∫⁻ x in C, ENNReal.ofReal (vec3EuclideanNorm (u n (x,t))) ^
            (2 : ℝ) ∂volume) ≤ M) :
    ∀ n j (t : I), MemLp
      (fun x : Vec3 => (WithLp.toLp 2 (u n (x,t.1)) : L2Vec3)) 2
      (volume.restrict (K j)) := by
  intro n j t
  obtain ⟨p, htp⟩ := exists_rational_compact_time_window_around
    hI t.property
  obtain ⟨M, hM, hMb⟩ :=
    hbound (K j) (hK j).1 (hK j).2
      (Icc (p.1.1 : ℝ) p.1.2) isCompact_Icc p.property.2
  have henergy : (∫⁻ x in K j,
      ENNReal.ofReal (vec3EuclideanNorm (u n (x,t.1))) ^
        (2 : ℝ) ∂volume) < ⊤ :=
    (hMb n t.1 ⟨htp.1.le, htp.2.le⟩).trans_lt hM
  have hslice : Measurable (fun x : Vec3 => u n (x,t.1)) :=
    (huMeas n).comp (by fun_prop)
  exact CKN.Foundation.memLp_two_vec3_of_lintegral_sq_lt_top
    (volume.restrict (K j)) (fun x => u n (x,t.1)) hslice henergy

/-- At every time, the original slices converge weakly to the jointly
measurable representative on each compact member of the exhaustion. -/
theorem weak_slices_to_compactnessMollifiedLimit_on_exhaustion
    {U : Set Vec3} {I : Set ℝ} (hI : IsOpen I)
    (u : ℕ → Vec3 × ℝ → Vec3) (σ : ℕ → ℕ)
    (huMeas : ∀ n, Measurable (u n))
    (K : ℕ → Set Vec3) (χ : ℕ → Vec3 → ℝ)
    (hK : ∀ j, IsCompact (K j) ∧ K j ⊆ U ∧
      K j ⊆ K (j + 1) ∧ K j ⊆ interior (K (j + 1)))
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
      (nhds (inner ℝ (V j t) x))) :
    ∀ j (t : I),
      ∃ hsource : ∀ k, MemLp
        (fun x : Vec3 => (WithLp.toLp 2 (u (σ k) (x,t.1)) : L2Vec3))
          2 (volume.restrict (K j)),
      ∃ hlimit : MemLp
        (fun x : Vec3 => (WithLp.toLp 2
          (compactnessMollifiedLimit u σ (x,t.1)) : L2Vec3)) 2
        (volume.restrict (K j)),
        ∀ w : Lp L2Vec3 2 (volume.restrict (K j)),
          Tendsto (fun k => inner ℝ ((hsource k).toLp
            (fun x => (WithLp.toLp 2 (u (σ k) (x,t.1)) : L2Vec3))) w)
            atTop (nhds (inner ℝ (hlimit.toLp
              (fun x => (WithLp.toLp 2
                (compactnessMollifiedLimit u σ (x,t.1)) : L2Vec3))) w)) := by
  intro j t
  let hsource : ∀ k, MemLp
      (fun x : Vec3 => (WithLp.toLp 2 (u (σ k) (x,t.1)) : L2Vec3))
        2 (volume.restrict (K j)) :=
    fun k => memLp_original_slice_on_exhaustion hI u huMeas K
      (fun j => ⟨(hK j).1, (hK j).2.1⟩) hbound (σ k) j t
  let hlimit := compactnessMollifiedLimit_memLp_on_exhaustion
    u σ K χ
    (fun j => ⟨(hK j).1, (hK j).2.2.1, (hK j).2.2.2⟩)
    hχ hmem V hweak j t
  have hrep := compactnessMollifiedLimit_ae_eq_on_exhaustion
    u σ K χ
    (fun j => ⟨(hK j).1, (hK j).2.2.1, (hK j).2.2.2⟩)
    hχ hmem V hweak j t
  have heq : (fun x : Vec3 => (WithLp.toLp 2
      (compactnessMollifiedLimit u σ (x,t.1)) : L2Vec3)) =ᵐ[
        volume.restrict (K j)] (fun x => V (j + 1) t x) := by
    filter_upwards [hrep] with x hx
    rw [hx]
  have hlimitEq : hlimit.toLp
      (fun x => (WithLp.toLp 2
        (compactnessMollifiedLimit u σ (x,t.1)) : L2Vec3)) =
      (((Lp.memLp (V (j + 1) t)).restrict (K j)).toLp
        (fun x => V (j + 1) t x)) :=
    MemLp.toLp_congr hlimit _ heq
  have hlocal := weak_local_slices_of_weak_cutoff
    (hK j).1.measurableSet (fun k x => u (σ k) (x,t.1))
    (χ (j + 1))
    (fun x hx => hχ (j + 1) x ((hK j).2.2.1 hx))
    (fun k => hmem (σ k) (j + 1) t) hsource
    (V (j + 1) t) (hweak (j + 1) t)
  refine ⟨hsource, hlimit, fun w => ?_⟩
  rw [hlimitEq]
  exact hlocal w

end CKN.Leray
