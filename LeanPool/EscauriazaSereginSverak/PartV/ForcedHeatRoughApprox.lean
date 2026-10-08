/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatRoughSetup
public import LeanPool.EscauriazaSereginSverak.PartV.ForcedHeatApprox

/-!
# Smooth approximation of a rough forced heat response

A tensor in `L^{5/2} ∩ L²` supported in the slab `Q_τ` is approximated in both
norms by smooth compactly supported tensors supported in positive times, whose
forced heat responses converge almost everywhere on the slab to the forced heat
response of the tensor. This is the approximation step of `lem:pv-stokes`.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Smooth approximation of a rough tensor with almost everywhere convergence of
the forced heat responses on the slab. -/
theorem forcedHeat_rough_approx {τ : ℝ} (hτ : 0 < τ) {G : Fin 3 → Fin 3 → ParabolicPoint → ℝ}
    (hG52 : ∀ i j, MemLp (G i j) (ENNReal.ofReal (5 / 2)) volume)
    (hG2 : ∀ i j, MemLp (G i j) 2 volume)
    (hGsupp : ∀ i j z, z ∉ CKN.spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 τ) → G i j z = 0) :
    ∃ Gn : ℕ → Fin 3 → Fin 3 → ParabolicPoint → ℝ,
      (∀ n i j, ContDiff ℝ (⊤ : ℕ∞) (fun p : Vec3 × ℝ => Gn n i j p)) ∧
      (∀ n i j, HasCompactSupport (fun p : Vec3 × ℝ => Gn n i j p)) ∧
      (∀ n i j, tsupport (fun p : Vec3 × ℝ => Gn n i j p) ⊆ {p | 0 < p.2}) ∧
      (∀ i j, Tendsto (fun n => eLpNorm (fun p : Vec3 × ℝ => Gn n i j p - G i j p)
        (ENNReal.ofReal (5 / 2)) volume) atTop (𝓝 0)) ∧
      (∀ i j, Tendsto (fun n => eLpNorm (fun p : Vec3 × ℝ => Gn n i j p - G i j p) 2 volume)
        atTop (𝓝 0)) ∧
      ∀ᵐ z ∂(volume.restrict ((Set.univ : Set Vec3) ×ˢ Ioo 0 τ)),
        Tendsto (fun n => forcedHeat (Gn n) z) atTop (𝓝 (forcedHeat G z)) := by
  let g : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun i j p => G i j p
  have hg52 (i j : Fin 3) : MemLp (g i j) (ENNReal.ofReal (5 / 2)) volume := hG52 i j
  have hg2 (i j : Fin 3) : MemLp (g i j) 2 volume := hG2 i j
  have hgsupp (i j : Fin 3) (z : Vec3 × ℝ) (hz : g i j z ≠ 0) : 0 < z.2 := by
    by_contra hneg
    apply hz
    apply hGsupp i j z
    intro hmem
    exact hneg hmem.2.1
  choose h hsmooth hcomp hpos h52 h2 using fun (ij : Fin 3 × Fin 3) =>
    exists_smooth_approx_two_norms (hg52 ij.1 ij.2) (hg2 ij.1 ij.2) (hgsupp ij.1 ij.2)
  let gn : ℕ → Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := fun n i j => h (i, j) n
  obtain ⟨ns, hns, hae⟩ := kernelResponse_ae_subseq hτ hg2 hgsupp
    (gn := gn) (fun n i j => hsmooth (i, j) n) (fun n i j => hcomp (i, j) n)
    (fun n i j => hpos (i, j) n) fun i j => h2 (i, j)
  refine ⟨fun n i j z => gn (ns n) i j z, fun n i j => hsmooth (i, j) (ns n),
    fun n i j => hcomp (i, j) (ns n), fun n i j => hpos (i, j) (ns n),
    fun i j => (h52 (i, j)).comp hns.tendsto_atTop, fun i j => (h2 (i, j)).comp hns.tendsto_atTop,
    ?_⟩
  filter_upwards [hae] with z hz
  exact hz

end ESS

end
