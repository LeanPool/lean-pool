/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.DiscArcs
import LeanPool.GraphMinor.Surface.DiscGrow
import Mathlib.Topology.TietzeExtension

/-!
# Extending disc coordinates

Extend the two real coordinates of a disc chart separately by Tietze's
theorem. On the disc the resulting map still has the chart inverse.
This provides a continuous map on the whole surface when transporting
the rural neighborhood of XVI (8.1), Claim (11), to the plane.
-/

public section
namespace GraphMinor.GM16
open Set Topology Metric GraphMinor.Surface
universe u
variable {S : Type u} [TopologicalSpace S] [T2Space S] [CompactSpace S]

/-- A continuous complex-valued map on a closed subset extends to the
whole compact Hausdorff space, by extending its real coordinates. -/
theorem exists_complex_extension {D : Set S} (hD : IsClosed D)
    {h : S → ℂ} (hc : ContinuousOn h D) :
    ∃ f : S → ℂ, Continuous f ∧ EqOn f h D := by
  let hr : C(D, ℝ) := ⟨fun x => (h x.val).re,
    Complex.continuous_re.comp (continuousOn_iff_continuous_domRestrict.mp hc)⟩
  let hi : C(D, ℝ) := ⟨fun x => (h x.val).im,
    Complex.continuous_im.comp (continuousOn_iff_continuous_domRestrict.mp hc)⟩
  obtain ⟨fr, hfr⟩ := hr.exists_restrict_eq hD
  obtain ⟨fi, hfi⟩ := hi.exists_restrict_eq hD
  refine ⟨fun x => ⟨fr x, fi x⟩, ?_, ?_⟩
  · have hc := (Complex.continuous_ofReal.comp fr.continuous).add
        ((Complex.continuous_ofReal.comp fi.continuous).mul (continuous_const (y := Complex.I)))
    apply hc.congr
    intro x
    exact (Complex.mk_eq_add_mul_I (fr x) (fi x)).symm
  · intro x hx
    apply Complex.ext
    · exact congrArg (fun q : C(D, ℝ) => q ⟨x, hx⟩) hfr
    · exact congrArg (fun q : C(D, ℝ) => q ⟨x, hx⟩) hfi

/-- A closed disc has coordinates that extend continuously to the
whole surface and remain injective on the disc. -/
theorem exists_extended_disc_chart {D : Set S} (hD : IsClosedDisc D) :
    ∃ f : S → ℂ, ∃ g : ℂ → S,
      Continuous f ∧ IsChart D f g ∧ InjOn f D := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  obtain ⟨f, hf, heq⟩ := exists_complex_extension hD.isClosed c.hc
  have hinv : LeftInvOn g f D := by
    intro x hx
    rw [heq hx]
    exact c.gh hx
  refine ⟨f, g, hf, ⟨hf.continuousOn, c.gc, ?_, c.gm, hinv, ?_, ?_⟩, ?_⟩
  · intro x hx
    rw [heq hx]
    exact c.hm hx
  · intro x hx
    rw [heq (c.gm hx)]
    exact c.hg hx
  · rw [(heq.mono (discBd_subset D)).image_eq, c.bd]
  · intro x hx y hy hxy
    exact (hinv hx).symm.trans ((congrArg g hxy).trans (hinv hy))

end GraphMinor.GM16
