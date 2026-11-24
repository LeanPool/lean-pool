/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM07.Section46ProperSubarc
import LeanPool.GraphMinor.GM07.Section46RetainedCircles
import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.Surface.SurfaceGraph
import LeanPool.GraphMinor.GM07.DiscPlace
import LeanPool.GraphMinor.Surface.Cuffs
import LeanPool.GraphMinor.Surface.Classification
import LeanPool.GraphMinor.GM11.RadialBasics
import LeanPool.GraphMinor.GM11.Walks

/-!
# No `I`-arc lies in `U(L)`

VII (4.6), page 226, chooses a proper subarc and applies (i) to put
its ends on one cuff. Join that subarc to one of the two arcs of the
cuff. This is a circle in `U(L) ∪ bd(Σ)`, so the preceding circle claim
makes it a cuff. It contains an interior point of the proper subarc,
which cannot lie in the boundary. This gives the contradiction.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface GraphMinor.GM11

private theorem proper_IArc_not_subset_bd {S : Type*} [TopologicalSpace S]
    {P : Set S} (hP : IsProperIArc P) : ¬P ⊆ bd S := by
  obtain ⟨a, b, _, hends, f, hf0, hf1⟩ := hP
  intro hsub
  let t : unitInterval := ⟨1 / 2, by norm_num, by norm_num⟩
  have hpt : (f t).1 ∈ P ∩ bd S := ⟨(f t).2, hsub (f t).2⟩
  have hpair : (f t).1 ∈ ({a, b} : Set S) := hends ▸ hpt
  rcases hpair with h | h
  · have hft : f t = f 0 := Subtype.ext (h.trans hf0.symm)
    have heq := congrArg Subtype.val (f.injective hft)
    norm_num [t] at heq
  · have hft : f t = f 1 := Subtype.ext (h.trans hf1.symm)
    have heq := congrArg Subtype.val (f.injective hft)
    norm_num [t] at heq

/-- No `I`-arc lies in `U(L)`, in VII (4.6), page 226. -/
theorem not_isIArc_of_subset_retained {S : Type*} [TopologicalSpace S]
    (hS : IsSurface S) (N : Net S) (hcuffs : 2 ≤ (cuffs S).ncard)
    {G J J' L : Drawing S} (hJ : N.IsSeamGraphFor J) (hG : G.IsProper)
    (hnorm : G.IsNormal J.U) (hL : L.IsSubdrawing J') (hU : J'.U = J.U)
    (hLp : L.IsProper) {v : ℕ}
    (hsum : (G.V ∩ L.U).ncard + (G.V ∩ bd S).ncard ≤ v)
    (hi : ∀ B : Set S, G.IsNormal B → IsIArc B → (G.V ∩ B).ncard ≤ v →
      ∃ C ∈ cuffs S, lineEnds B ⊆ C)
    (hii : ∀ B : Set S, G.IsNormal B → IsOArc B → (G.V ∩ B).ncard ≤ v →
      IsNullHomotopicOArc B ∨
        ∃ C ∈ cuffs S, IsNullHomotopicOArcInCappedCuff C B ∧ G.V ∩ C ⊆ B)
    (hiii : ∀ C ∈ cuffs S, 2 ≤ (G.V ∩ C).ncard)
    {F : Set S} (hFL : F ⊆ L.U) : ¬IsIArc F := by
  have : T2Space S := hS.2.1
  intro hF
  obtain ⟨P, hPF, hP⟩ := exists_proper_IArc_subset hLp hF hFL
  have hPL : P ⊆ L.U := hPF.trans hFL
  obtain ⟨a, b, hab, hends, hline⟩ := hP
  have haP : a ∈ P ∩ bd S := hends ▸ mem_insert a {b}
  have hbP : b ∈ P ∩ bd S := hends ▸ mem_insert_of_mem a (mem_singleton b)
  have hPi : IsIArc P := ⟨a, b, haP.2, hbP.2, hline⟩
  have hPN : G.IsNormal P := by
    rintro x ⟨hxP, hxG⟩
    exact hnorm ⟨hU ▸ hL.U_subset (hPL hxP), hxG⟩
  have hsmall : (G.V ∩ P).ncard ≤ v := by
    have hsub : G.V ∩ P ⊆ G.V ∩ L.U := inter_subset_inter_right G.V hPL
    have hcard := ncard_le_ncard hsub (G.finite_V.subset inter_subset_left)
    omega
  obtain ⟨C, hC, hPC⟩ := hi P hPN hPi hsmall
  have haC : a ∈ C := hPC ⟨b, hline⟩
  have hbC : b ∈ C := hPC ⟨a, hline.symm⟩
  have hCO := (cuff_statement S hS).2.2 C hC
  obtain ⟨α, β, htwo, hα0, hα1, hcover⟩ := hCO.exists_arcs haC hbC hab
  have hAline : IsLineWithEnds (range α) a b := by
    simpa only [hα0, hα1] using isLineWithEnds_range_of_arc htwo.arc_left
  have hAC : range α ⊆ C := subset_union_left.trans hcover.subset
  have hCbd : C ⊆ bd S := fun x hx => sUnion_cuffs (S := S) ▸ ⟨C, hC, hx⟩
  have hmeet : P ∩ range α ⊆ {a, b} := fun x hx => hends ▸ ⟨hx.1, hCbd (hAC hx.2)⟩
  have hcircle : IsOArc (P ∪ range α) := isOArc_union hline hAline hmeet
  have hcircleSub : P ∪ range α ⊆ L.U ∪ bd S := union_subset_union hPL (hAC.trans hCbd)
  have hcircleCuff := circles_in_retained_union_are_cuffs hS N hcuffs hJ hG hnorm hL hU
    hsum hii hiii hcircle hcircleSub
  have hPbd : P ⊆ bd S := fun x hx =>
    sUnion_cuffs (S := S) ▸ ⟨P ∪ range α, hcircleCuff, Or.inl hx⟩
  exact proper_IArc_not_subset_bd ⟨a, b, hab, hends, hline⟩ hPbd

end GraphMinor.GM07
