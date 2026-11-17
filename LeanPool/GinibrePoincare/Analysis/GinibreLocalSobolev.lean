/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreLocalSobolev.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GinibreWeakSobolevMultipliers

/-! # Unweighted local L² regularity of the independent Ginibre weak graph

Weighted value and gradient L² representatives belong to ordinary Lebesgue L²
on each compact subset of the collision-free open set. These are actual local
Sobolev functions there; no smooth-core membership is needed.
-/


@[expose] public section


open MeasureTheory
open scoped Topology
namespace GinibrePoincare
noncomputable section

/-- Weighted L¹ functions are locally Lebesgue integrable where the density is positive. -/
theorem ginibre_integrable_locallyIntegrable_collisionFree {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : Integrable f (ginibreMeasure n)) :
    LocallyIntegrableOn f {z : Configuration n | CollisionFree z} volume := by
  have hi := (integrable_ginibre_iff_density hn f).mp hf
  have hc : ContinuousOn (fun z => (ginibreLebesgueDensityReal n z)⁻¹)
      {z : Configuration n | CollisionFree z} :=
    (contDiff_ginibreLebesgueDensityReal n).continuous.continuousOn.inv₀
      (fun z hz => ginibreLebesgueDensityReal_ne_zero_of_collisionFree hn hz)
  have hl := (hi.locallyIntegrable.locallyIntegrableOn
    {z : Configuration n | CollisionFree z}).mul_continuousOn hc
      (isOpen_collisionFree n).isLocallyClosed
  apply hl.congr
  apply ae_restrict_of_forall_mem (isOpen_collisionFree n).measurableSet
  intro z hz
  dsimp
  field_simp [ginibreLebesgueDensityReal_ne_zero_of_collisionFree hn hz]

theorem ginibre_memLp_norm_sq_locallyIntegrable_collisionFree {n : ℕ} (hn : 0 < n)
    {V : Type*} [NormedAddCommGroup V] (f : Configuration n → V)
    (hf : MemLp f 2 (ginibreMeasure n)) :
    LocallyIntegrableOn (fun z => ‖f z‖ ^ 2)
      {z : Configuration n | CollisionFree z} volume :=
  ginibre_integrable_locallyIntegrable_collisionFree hn _
    ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf)

/-- Every weighted L² representative belongs to ordinary L² on interior compact sets. -/
theorem ginibre_memLp_restrict_volume_compact_collisionFree {n : ℕ} (hn : 0 < n)
    {V : Type*} [NormedAddCommGroup V] (f : Configuration n → V)
    (hf : MemLp f 2 (ginibreMeasure n)) (K : Set (Configuration n))
    (hK : IsCompact K) (hs : K ⊆ {z | CollisionFree z}) :
    MemLp f 2 (volume.restrict K) := by
  have hm : AEStronglyMeasurable f (volume : Measure (Configuration n)) :=
    AEStronglyMeasurable.mono_ac (volume_absolutelyContinuous_ginibreMeasure n hn)
      hf.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm.restrict).mpr
  exact (ginibre_memLp_norm_sq_locallyIntegrable_collisionFree hn f
    hf).integrableOn_compact_subset hs hK

/-- Interior compactly supported weighted L² representatives are global Lebesgue L². -/
theorem ginibre_memLp_volume_of_interior_compactSupport {n : ℕ} (hn : 0 < n)
    {V : Type*} [NormedAddCommGroup V] (f : Configuration n → V)
    (hf : MemLp f 2 (ginibreMeasure n)) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ {z | CollisionFree z}) : MemLp f 2 volume := by
  have hm : AEStronglyMeasurable f (volume : Measure (Configuration n)) :=
    AEStronglyMeasurable.mono_ac (volume_absolutelyContinuous_ginibreMeasure n hn)
      hf.aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hi : IntegrableOn (fun z => ‖f z‖ ^ 2) (tsupport f) volume :=
    (memLp_two_iff_integrable_sq_norm
    (ginibre_memLp_restrict_volume_compact_collisionFree hn f hf (tsupport f) hc
      hs).aestronglyMeasurable).mp
      (ginibre_memLp_restrict_volume_compact_collisionFree hn f hf (tsupport f) hc hs)
  apply hi.integrable_of_forall_notMem_eq_zero
  intro z hz
  simp [image_eq_zero_of_notMem_tsupport hz]

/-- Both components of every actual weak-gradient pair have ordinary local L² regularity. -/
theorem ginibre_distributional_pair_local_L2 (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (K : Set (Configuration n)) (hK : IsCompact K) (hs : K ⊆ {z | CollisionFree z}) :
    MemLp u 2 (volume.restrict K) ∧ MemLp g 2 (volume.restrict K) :=
  ⟨ginibre_memLp_restrict_volume_compact_collisionFree hn u (Lp.memLp u) K hK hs,
    ginibre_memLp_restrict_volume_compact_collisionFree hn g (Lp.memLp g) K hK hs⟩

end
end GinibrePoincare
