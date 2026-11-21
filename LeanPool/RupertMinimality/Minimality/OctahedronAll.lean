/-
Copyright (c) 2026 Tom Murphy VII, Jason Reed, David Renshaw. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tom Murphy VII, Jason Reed, David Renshaw
-/

module

public import LeanPool.RupertMinimality.Minimality.Oct9Par

/-! # Octahedron All -/

@[expose] public section

namespace RupertMinimality

/-!
# Theorem 9.9: every convex octahedron is Rupert

Part L9 of the proof (octahedra are the hardest case of step 5 of
`minimality.md`).  For every octahedron the proof finds an edge view with the
antipodal vertex hidden (a *quad edge*) whose tilted silhouette is robustly
unimodal (Lemma 9.3, `Oct9Quad.lean`), or two touching edges seen along an
axis (Lemma 9.4), or a planar equator (both in `Oct9Axis.lean`).  The right
pair of edges is found in the Gale diagram (`Oct9Gale.lean`, §9.5), with the
case of two parallel opposite faces treated separately (`Oct9Par.lean`,
`Oct9Weak.lean`, §9.6).  Everything is reduced to the frame-free Lemma 8.0 /
Corollary 8.0′ of `Tilt.lean`.  The numbered statements are listed in
`README.md`.
-/

namespace Minimality

open scoped RealInnerProductSpace Topology
open Finset Filter

/-- Normalized labels: `κ_W > 0` for the three opposite pairs. -/
theorem isRupert_octahedron_normalized {a a' b b' c c' : ℝ³} (h : IsOctahedron a a' b b' c c')
    (G : GaleData a a' b b' c c') (hκa : 0 < galeD G.l G.m a a')
    (hκb : 0 < galeD G.l G.m b b') (hκc : 0 < galeD G.l G.m c c') :
    IsRupert {a, a', b, b', c, c'} := by
  by_cases hf : G.l a + G.l b + G.l c = 0 ∧ G.m a + G.m b + G.m c = 0
  · exact isRupert_octahedron_parallel h G hκa hκb hκc hf
  · exact isRupert_octahedron_generic h G hκa hκb hκc hf

/-- Nonzero `κ` on all three pairs: relabel within each pair. -/
theorem isRupert_octahedron_nonplanar {a a' b b' c c' : ℝ³} (h : IsOctahedron a a' b b' c c')
    (G : GaleData a a' b b' c c') (hκa : galeD G.l G.m a a' ≠ 0)
    (hκb : galeD G.l G.m b b' ≠ 0) (hκc : galeD G.l G.m c c' ≠ 0) :
    IsRupert {a, a', b, b', c, c'} := by
  have anti := galeD_anti G.l G.m
  have e : ∀ s : Finset ℝ³, s = {a, a', b, b', c, c'} → IsRupert s →
      IsRupert {a, a', b, b', c, c'} := fun s hs hr => hs ▸ hr
  rcases lt_or_gt_of_ne hκa with ha | ha <;> rcases lt_or_gt_of_ne hκb with hb | hb <;>
    rcases lt_or_gt_of_ne hκc with hc | hc
  · exact e _ (by ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
      (isRupert_octahedron_normalized h.swap₁.swap₂.swap₃ G.swap₁.swap₂.swap₃
        (by simp only [GaleData.swap₁, GaleData.swap₂, GaleData.swap₃]; rw [anti]; linarith)
        (by simp only [GaleData.swap₁, GaleData.swap₂, GaleData.swap₃]; rw [anti]; linarith)
        (by simp only [GaleData.swap₁, GaleData.swap₂, GaleData.swap₃]; rw [anti]; linarith))
  · exact e _ (by ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
      (isRupert_octahedron_normalized h.swap₁.swap₂ G.swap₁.swap₂
        (by simp only [GaleData.swap₁, GaleData.swap₂]; rw [anti]; linarith)
        (by simp only [GaleData.swap₁, GaleData.swap₂]; rw [anti]; linarith)
        (by simp only [GaleData.swap₁, GaleData.swap₂]; linarith))
  · exact e _ (by ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
      (isRupert_octahedron_normalized h.swap₁.swap₃ G.swap₁.swap₃
        (by simp only [GaleData.swap₁, GaleData.swap₃]; rw [anti]; linarith)
        (by simp only [GaleData.swap₁, GaleData.swap₃]; linarith)
        (by simp only [GaleData.swap₁, GaleData.swap₃]; rw [anti]; linarith))
  · exact e _ (by ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
      (isRupert_octahedron_normalized h.swap₁ G.swap₁
        (by simp only [GaleData.swap₁]; rw [anti]; linarith)
        (by simp only [GaleData.swap₁]; linarith) (by simp only [GaleData.swap₁]; linarith))
  · exact e _ (by ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
      (isRupert_octahedron_normalized h.swap₂.swap₃ G.swap₂.swap₃
        (by simp only [GaleData.swap₂, GaleData.swap₃]; linarith)
        (by simp only [GaleData.swap₂, GaleData.swap₃]; rw [anti]; linarith)
        (by simp only [GaleData.swap₂, GaleData.swap₃]; rw [anti]; linarith))
  · exact e _ (by ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
      (isRupert_octahedron_normalized h.swap₂ G.swap₂
        (by simp only [GaleData.swap₂]; linarith)
        (by simp only [GaleData.swap₂]; rw [anti]; linarith)
        (by simp only [GaleData.swap₂]; linarith))
  · exact e _ (by ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
      (isRupert_octahedron_normalized h.swap₃ G.swap₃
        (by simp only [GaleData.swap₃]; linarith) (by simp only [GaleData.swap₃]; linarith)
        (by simp only [GaleData.swap₃]; rw [anti]; linarith))
  · exact isRupert_octahedron_normalized h G ha hb hc

/-- **Theorem 9.9.**  Every convex octahedron is Rupert. -/
theorem isRupert_octahedron {a a' b b' c c' : ℝ³} (h : IsOctahedron a a' b b' c c') :
    IsRupert {a, a', b, b', c, c'} := by
  obtain ⟨G⟩ := h.nonempty_galeData
  have e : ∀ s : Finset ℝ³, s = {a, a', b, b', c, c'} → IsRupert s →
      IsRupert {a, a', b, b', c, c'} := fun s hs hr => hs ▸ hr
  by_cases hκa : galeD G.l G.m a a' = 0
  · exact isRupert_of_kappa_zero h G hκa
  by_cases hκb : galeD G.l G.m b b' = 0
  · exact e _ (by ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
      (isRupert_of_kappa_zero h.perm₁₂ G.perm₁₂ hκb)
  by_cases hκc : galeD G.l G.m c c' = 0
  · exact e _ (by ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
      (isRupert_of_kappa_zero h.perm₂₃.perm₁₂ G.perm₂₃.perm₁₂ hκc)
  exact isRupert_octahedron_nonplanar h G hκa hκb hκc

end Minimality

end RupertMinimality
