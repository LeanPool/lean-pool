/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2TracePartition
public import LeanPool.GraphMinor.GM12.Section2NormalEntryExistence
import LeanPool.GraphMinor.GM12.Section2RegionIntervals

/-!
# Constructing trace steps from ordered hits

For XII's trace definition on page 243, each consecutive pair of vertex
parameters bounds a curve segment in one region. Choose its radial hub,
then the entering and leaving edges, and concatenate the resulting
two-edge walks. The entry and exit lemmas include leaves, so every
vertex hit is covered.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- Construct the trace walk over an ordered enumeration of vertex hits.
There are two
edges for each interval between successive hits, as required in XII's
trace definition, page 243. -/
theorem exists_traceSteps_of_enumerated_hits {S : Type*} [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] (hS : IsClosedSurface S)
    {Γ K : Drawing S} (hrad : PreRad (.drawing Γ) K)
    (hmax : RadMax (.drawing Γ) K) (hE : Γ.E.Nonempty)
    {f : ℝ → S} (hf : Continuous f) {n : ℕ} (t : Fin (n + 1) → ℝ) (ht : StrictMono t)
    (hΓ : ∀ i, f (t i) ∈ Γ.V)
    (hcover : ∀ s ∈ Icc (t 0) (t (Fin.last n)), f s ∈ Γ.U → s ∈ range t) :
    ∃ W : GraphWalk K.toGraph (f (t 0)) (f (t (Fin.last n))),
      TraceSteps Γ K f (t 0) (t (Fin.last n)) W ∧ W.length = 2 * n := by
  apply exists_traceSteps_of_partition t hΓ (fun i => radial_V hrad (hΓ i))
  intro i
  have hac : t i.castSucc < t i.succ := ht i.castSucc_lt_succ
  have hoff := no_hit_between_consecutive_parameters t ht hcover i
  obtain ⟨r, hr, hfr⟩ := exists_region_of_open_interval hf hac hoff
  obtain ⟨w, ⟨hwr, hwK⟩, _⟩ := hrad.2.2.2.1 r hr
  obtain ⟨e', he', henter⟩ := exists_entersLike hS hrad hmax hE
    (hΓ i.succ) hr hwr hwK hf hac rfl hfr
  obtain ⟨e, he, hleave⟩ := exists_leavesLike hS hrad hmax hE
    (hΓ i.castSucc) hr hwr hwK hf hac rfl hfr
  obtain ⟨W, hW, hlength, _, _⟩ := exists_traceSteps_two_edges hS hrad hac rfl (hΓ i.castSucc)
    rfl (hΓ i.succ) hr hwr hwK hfr he he' hleave henter
  exact ⟨W, hW, hlength⟩

end GraphMinor.GM12
