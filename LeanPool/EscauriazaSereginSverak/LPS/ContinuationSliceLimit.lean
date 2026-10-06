/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.ContinuationTestField
public import LeanPool.EscauriazaSereginSverak.LPS.StrongSolution

/-!
# Slice limits of strong solutions

Componentwise `L²` continuity and the continuity of the pairing of a strongly
`L²`-continuous velocity with a test field (`lem:lps-continuation`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Componentwise `L²` distance is bounded by the `L²` distance of the vector field. -/
theorem lps_component_l2_tendsto {E : Type} [NormedAddCommGroup E] {l : Filter ℝ}
    {f : ℝ → Vec3 → Fin 3 → E} {f₀ : Vec3 → Fin 3 → E}
    (hm : ∀ᶠ s in l, AEStronglyMeasurable (fun x : Vec3 => f s x - f₀ x) volume)
    (h : Tendsto (fun s : ℝ => eLpNorm (fun x : Vec3 => f s x - f₀ x) 2 volume) l (𝓝 0))
    (i : Fin 3) :
    Tendsto (fun s : ℝ => eLpNorm (fun x : Vec3 => f s x i - f₀ x i) 2 volume) l (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h
    (Eventually.of_forall fun s => zero_le) ?_
  filter_upwards [hm] with s hs
  refine eLpNorm_mono ((continuous_apply i).comp_aestronglyMeasurable hs) fun x => ?_
  exact norm_le_pi_norm (f s x - f₀ x) i

/-- The pairing of a strongly `L²`-continuous field with a test field is continuous. -/
theorem lps_vector_pairing_tendsto {S : Set ℝ} {t₀ : ℝ} {u : ParabolicPoint → Vec3}
    {φ : Vec3 × ℝ → Vec3} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hcont : Tendsto (fun s : ℝ => eLpNorm (fun x : Vec3 => u (x, s) - u (x, t₀)) 2 volume)
      (nhdsWithin t₀ S) (nhds 0))
    (hmem : ∀ s ∈ S, MemLp (fun x : Vec3 => u (x, s)) 2 volume)
    (hmem₀ : MemLp (fun x : Vec3 => u (x, t₀)) 2 volume) :
    Tendsto (fun t : ℝ => ∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * φ (x, t) i)
      (nhdsWithin t₀ S) (nhds (∫ x : Vec3, ∑ i : Fin 3, u (x, t₀) i * φ (x, t₀) i)) := by
  have hφi (i : Fin 3) : Continuous (fun y : Vec3 × ℝ => φ y i) :=
    (contDiff_pi.mp hφ i).continuous
  have hφic (i : Fin 3) : HasCompactSupport (fun y : Vec3 × ℝ => φ y i) :=
    hφc.comp_left (g := fun v : Vec3 => v i) (by simp)
  have hφmemS (i : Fin 3) (s : ℝ) : MemLp (fun x : Vec3 => φ (x, s) i) 2 volume :=
    ((hφi i).comp (continuous_id.prodMk continuous_const)).memLp_of_hasCompactSupport (by
      refine IsCompact.of_isClosed_subset ((hφic i).image continuous_fst) (isClosed_tsupport _) ?_
      refine closure_minimal ?_ ((hφic i).image continuous_fst).isClosed
      intro x hx
      exact ⟨(x, s), subset_tsupport _ hx, rfl⟩)
  have hm : ∀ᶠ s in nhdsWithin t₀ S, AEStronglyMeasurable
      (fun x : Vec3 => u (x, s) - u (x, t₀)) volume := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact ((hmem s hs).sub hmem₀).aestronglyMeasurable
  have hint (i : Fin 3) (s : ℝ) (hs : MemLp (fun x : Vec3 => u (x, s) i) 2 volume) :
      Integrable (fun x : Vec3 => u (x, s) i * φ (x, s) i) volume :=
    hs.integrable_mul (hφmemS i s)
  have hcomp (i : Fin 3) : Tendsto (fun t : ℝ => ∫ x : Vec3, u (x, t) i * φ (x, t) i)
      (nhdsWithin t₀ S) (nhds (∫ x : Vec3, u (x, t₀) i * φ (x, t₀) i)) := by
    refine lps_pairing_tendsto (l := nhdsWithin t₀ S) (f := fun s x => u (x, s) i)
      (g := fun s x => φ (x, s) i) (memLp_pi_iff.1 hmem₀ i) (hφmemS i t₀) ?_
      (Eventually.of_forall (hφmemS i)) (lps_component_l2_tendsto (f := fun s x => u (x, s)) hm hcont i) ?_
    · filter_upwards [self_mem_nhdsWithin] with s hs using memLp_pi_iff.1 (hmem s hs) i
    · exact (lps_test_slice_l2_tendsto (hφi i) (hφic i) t₀).mono_left nhdsWithin_le_nhds
  have hsum : Tendsto (fun t : ℝ => ∑ i : Fin 3, ∫ x : Vec3, u (x, t) i * φ (x, t) i)
      (nhdsWithin t₀ S) (nhds (∑ i : Fin 3, ∫ x : Vec3, u (x, t₀) i * φ (x, t₀) i)) :=
    tendsto_finsetSum _ fun i _ => hcomp i
  have hpt : ∀ s, MemLp (fun x : Vec3 => u (x, s)) 2 volume →
      (∫ x : Vec3, ∑ i : Fin 3, u (x, s) i * φ (x, s) i) =
        ∑ i : Fin 3, ∫ x : Vec3, u (x, s) i * φ (x, s) i := fun s hs =>
    integral_finsetSum _ fun i _ => hint i s (memLp_pi_iff.1 hs i)
  rw [hpt t₀ hmem₀]
  refine hsum.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (hpt s (hmem s hs)).symm

end ESS

end
