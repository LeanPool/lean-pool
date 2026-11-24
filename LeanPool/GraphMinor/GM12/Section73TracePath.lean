/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73TraceVisitPath
public import LeanPool.GraphMinor.GM12.Section73WalkPaths
import LeanPool.GraphMinor.GM12.Section2TraceParameters

/-!
# A traced curve segment deforms to its walk path

For the representativity step of XII (7.3), page 261, split a trace
at each successive vertex hit. A region interval deforms to its two
prescribed spoke paths. The remaining trace deforms by induction.
The real-interval split and path associativity then give a homotopy
for the whole segment, with its endpoints fixed.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A real curve segment carrying trace steps is homotopic to a
path realizing that trace. This compares the normal curve with the
radial walk in the representativity proof of XII (7.3), page 261. -/
theorem traceSteps_path_homotopic
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {Γ K : Drawing S} (hK : PreRad (PaintingOrDrawing.drawing Γ) K)
    {f : ℝ → S} (hf : Continuous f)
    (q : ∀ e x y, K.toGraph.IsLink e x y → Path x y)
    (hq : ∀ e x y (h : K.toGraph.IsLink e x y), range (q e x y h) ⊆ closure e)
    {a b : ℝ} {u v : S} (W : GraphWalk K.toGraph u v)
    (hW : TraceSteps Γ K f a b W) :
    ∃ (hfa : f a = u) (hfb : f b = v),
      ((realIntervalPath f hf a b).cast hfa.symm hfb.symm).Homotopic (walkPath q W) := by
  cases hWcase : W with
  | nil hv =>
    rw [hWcase] at hW
    obtain ⟨hab, hfa, _⟩ := hW
    subst b
    refine ⟨hfa, hfa, ?_⟩
    rw [realIntervalPath_self]
    have heq : (Path.refl (f a)).cast hfa.symm hfa.symm = Path.refl u := by
      ext t
      exact hfa
    rw [heq]
    exact Path.Homotopic.refl _
  | @cons _ w _ e h₁ rest =>
    rw [hWcase] at hW
    cases hrestcase : rest with
    | nil hv => rw [hrestcase] at hW; exact hW.elim
    | @cons _ x _ e' h₂ tail =>
      rw [hrestcase] at hW
      obtain ⟨c, hac, hfa, hu, hfc, hwK, r, hr, hwr, hfr, hleave, henter, ht⟩ := hW
      have hparams := traceSteps_parameters tail ht
      obtain ⟨hfc', hfb, htail⟩ := traceSteps_path_homotopic hK hf q hq tail ht
      have hab : a < b := hac.trans_le hparams.1
      have hsplit := (realIntervalPath_split f hf hab hac.le hparams.1).symm.pathCast
        hfa.symm hfb.symm
      rw [Path.cast_trans _ _ hfa.symm hfc.symm hfb.symm] at hsplit
      have hvisit := region_visit_homotopic_to_edge_paths hK hf hac hfa hfc hu
        hparams.2.2.1 hr hwr h₁ h₂ hfr hleave henter q hq
      refine ⟨hfa, hfb, ?_⟩
      exact hsplit.trans ((hvisit.hcomp htail).trans
        (Path.Homotopic.trans_assoc (q e u w h₁) (q e' w x h₂) (walkPath q tail)))
termination_by W.length
decreasing_by
  rw [hWcase, hrestcase]
  simp only [GraphWalk.length, GraphWalk.edges, List.length_cons]
  omega

end GraphMinor.GM12
