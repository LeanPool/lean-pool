/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2ConnectedRegionArc
import LeanPool.GraphMinor.GM12.Section2CirclePeriod

/-!
# Distinct vertices and regions in the first trace case

For Case 1 of XII (2.1), page 244, list the vertex parameters in
one closed real period. The original circle is embedded, so all
initial vertex images are distinct. If each region intersection is
preconnected, its whole parameter preimage lies in any one visit
arc. Two intervals assigned to that region would therefore overlap,
contrary to their parameter order. Thus the region labels are also
distinct, as required for the simple trace circle.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

private theorem parameter_in_period {n : ℕ} (t : Fin (n + 1) → ℝ) (ht : StrictMono t)
    (hperiod : t (Fin.last n) = t 0 + 1) (i : Fin n) :
    t i.castSucc ∈ Ico (t 0) (t 0 + 1) := by
  refine ⟨ht.monotone (Fin.zero_le _), ?_⟩
  rw [← hperiod]
  apply ht
  change i.val < n
  exact i.isLt

/-- Initial vertex images of an ordered one-period subdivision of
an embedded circle are distinct. -/
theorem vertex_visits_injective
    {S : Type*} [TopologicalSpace S] {φ : C(Circle, S)} (hφ : Function.Injective φ)
    {n : ℕ} (t : Fin (n + 1) → ℝ) (ht : StrictMono t)
    (hperiod : t (Fin.last n) = t 0 + 1) :
    Function.Injective (fun i : Fin n => periodicCurve φ (t i.castSucc)) := by
  intro i j hij
  have hpar := circle_parameter_injOn (t 0) (parameter_in_period t ht hperiod i)
    (parameter_in_period t ht hperiod j) (hφ hij)
  have hfin := ht.injective hpar
  exact Fin.ext (congrArg (fun k : Fin (n + 1) => k.val) hfin)

/-- If every region intersection with an embedded circle is
preconnected, the regions of its successive normal intervals are
distinct. This supplies the region condition of XII (2.1), Case 1. -/
theorem region_visits_injective
    {S : Type*} [TopologicalSpace S] {Γ : Drawing S}
    {φ : C(Circle, S)} (hφ : IsEmbedding φ)
    (hconn : ∀ r ∈ Γ.R, IsPreconnected (range φ ∩ r))
    {n : ℕ} (t : Fin (n + 1) → ℝ) (ht : StrictMono t)
    (hperiod : t (Fin.last n) = t 0 + 1)
    (hΓ : ∀ i, periodicCurve φ (t i) ∈ Γ.V)
    (r : Fin n → Set S) (hr : ∀ i, r i ∈ Γ.R)
    (hfr : ∀ i s, s ∈ Ioo (t i.castSucc) (t i.succ) → periodicCurve φ s ∈ r i) :
    Function.Injective r := by
  intro i j hij
  let m := (t j.castSucc + t j.succ) / 2
  have hjlt := ht j.castSucc_lt_succ
  have hm : m ∈ Ioo (t j.castSucc) (t j.succ) :=
    ⟨by dsimp [m]; linarith, by dsimp [m]; linarith⟩
  have hmr : periodicCurve φ m ∈ r i := hij.symm ▸ hfr j m hm
  obtain ⟨s, hs, hsm⟩ := preimage_region_subset_parameter_arc hφ (hr i) (hconn _ (hr i))
    (ht i.castSucc_lt_succ) (hΓ _) (hΓ _) (hfr i) hmr
  have in_period : ∀ (k : Fin n) x, x ∈ Ioo (t k.castSucc) (t k.succ) →
      x ∈ Ico (t 0) (t 0 + 1) := by
    intro k x hx
    refine ⟨(ht.monotone (Fin.zero_le _)).trans hx.1.le, ?_⟩
    have hupper := hx.2.trans_le (ht.monotone (Fin.le_last _))
    simpa only [hperiod] using hupper
  have hsm' := circle_parameter_injOn (t 0) (in_period i s hs) (in_period j m hm) hsm
  have hmi : m ∈ Ioo (t i.castSucc) (t i.succ) := hsm' ▸ hs
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle : i.succ ≤ j.castSucc := by change i.val + 1 ≤ j.val; omega
    have := ht.monotone hle
    exact (not_lt_of_ge (this.trans hm.1.le) hmi.2).elim
  · have hle : j.succ ≤ i.castSucc := by change j.val + 1 ≤ i.val; omega
    have := ht.monotone hle
    exact (not_lt_of_ge (this.trans hmi.1.le) hm.2).elim

end GraphMinor.GM12
