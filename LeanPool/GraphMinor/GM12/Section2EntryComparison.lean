/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
public import Mathlib.Topology.Subpath
import LeanPool.GraphMinor.GM12.Section2EntryNormalization
import LeanPool.GraphMinor.GM12.Section2EntryPaths
import LeanPool.GraphMinor.GM12.Section2PathHomotopy

/-!
# Comparing an entry curve with a common approach

XII, page 243, allows the starting point of an entry curve to vary.
Lift the entry curve and its comparison curve to the region together
with its boundary vertex. Normalize the approach and read off the
terminal spoke. The comparison path stays in the region, which is the
information needed to cancel two approaches starting at different times.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- Normalize one entry-curve witness against a fixed approach path.
Its terminal path is an injective parametrization of the spoke closure.
The normalized entry remains homotopic to a path in the region. -/
theorem compare_entry_to_approach {S : Type*} [TopologicalSpace S] [T2Space S]
    {r e : Set S} {v w : S} (hw : w ∈ r) {a b : (r ∪ {v} : Set S)}
    (F : Path a b) {f : ℝ → S} {h₀ h c : ℝ} {s : unitInterval}
    (hF : ∀ t, (F t).val = f (h₀ + t.val * (c - h₀)))
    (hstart : h = h₀ + s.val * (c - h₀)) (hfc : f c = v)
    (hvE : v ∉ e) (hwE : w ∉ e) (hvw : v ≠ w)
    {ξ ρ : Curve S} (hentry : IsEntryCurve f h c e w ξ)
    (hρ : range ρ ⊆ r) (hh : CurvesHomotopicIn (r ∪ {v}) ξ ρ) :
    ∃ (β : Path (F 1) (⟨w, Or.inl hw⟩ : (r ∪ {v} : Set S)))
      (σ : Path (F s) (⟨w, Or.inl hw⟩ : (r ∪ {v} : Set S))),
      Function.Injective (fun t => (β t).val) ∧
      range (fun t => (β t).val) = closure e ∧
      (fun t => (β t).val) '' Ioo (0 : unitInterval) 1 = e ∧
      (∀ t, (σ t).val ∈ r) ∧ ((F.subpath s 1).trans β).Homotopic σ := by
  obtain ⟨τ, hτ0, hτ1, hfirst, hinj, himage, hξ1⟩ := hentry
  have hξ0 : ξ 0 = f h := by
    simpa only [Icc.coe_zero, zero_div, zero_mul, add_zero] using hfirst 0 (bot_le)
  have hξτ : ξ τ = v := by
    rw [hfirst τ le_rfl, div_self (ne_of_gt hτ0), one_mul]
    convert hfc using 1
    congr 1
    ring
  have hFs : (F s).val = f h := by rw [hF, hstart]
  have hξZ : ∀ t, ξ t ∈ r ∪ {v} := by
    obtain ⟨H, hHZ, hH0, _, _⟩ := hh
    intro t
    exact hH0 t ▸ hHZ (t, 0)
  have heq0 : ξ 0 = ρ 0 := by
    obtain ⟨H, _, _, _, h0, h0', _⟩ := hh
    exact (h0 0).symm.trans (h0' 0)
  have heq1 : ξ 1 = ρ 1 := by
    obtain ⟨H, _, _, _, _, _, h1, h1'⟩ := hh
    exact (h1 0).symm.trans (h1' 0)
  let P : Path (F s) (⟨w, Or.inl hw⟩ : (r ∪ {v} : Set S)) := {
    toFun := fun t => ⟨ξ t, hξZ t⟩
    continuous_toFun := ξ.continuous.subtype_mk _
    source' := Subtype.ext (hξ0.trans hFs.symm)
    target' := Subtype.ext hξ1 }
  let σ : Path (F s) (⟨w, Or.inl hw⟩ : (r ∪ {v} : Set S)) := {
    toFun := fun t => ⟨ρ t, Or.inl (hρ (mem_range_self t))⟩
    continuous_toFun := ρ.continuous.subtype_mk _
    source' := Subtype.ext (heq0.symm.trans (hξ0.trans hFs.symm))
    target' := Subtype.ext (heq1.symm.trans hξ1) }
  have hPval : ∀ t, (P t).val = ξ t := fun _ => rfl
  have hPσ : P.Homotopic σ := paths_homotopic_of_curvesHomotopicIn P σ hh
  obtain ⟨β, hβval, hβhom⟩ := normalize_entry_approach
    (fun x : (r ∪ {v} : Set S) => x.val) Subtype.val_injective F hF hstart
    P ξ hPval hτ0 hfirst
  have hβeq : (fun t => (β t).val) = (fun t => ((P.subpath τ 1) t).val) := by
    funext t
    exact hβval t
  have hβinj : Function.Injective (fun t => (β t).val) := by
    rw [hβeq]
    apply entry_terminal_injective (fun x : (r ∪ {v} : Set S) => x.val) P ξ hPval
      hτ1 himage hinj
    · change ξ τ ∉ e
      rwa [hξτ]
    · change ξ 1 ∉ e
      rwa [hξ1]
    · change ξ τ ≠ ξ 1
      rwa [hξτ, hξ1]
  have hβint : (fun t => (β t).val) '' Ioo (0 : unitInterval) 1 = e := by
    rw [hβeq]
    exact entry_subpath_interior _ P ξ hPval hτ1 himage
  have hβrange : range (fun t => (β t).val) = closure e := by
    have h := path_range_eq_closure_interior (β.map continuous_subtype_val)
    change range (fun t => (β t).val) = closure ((fun t => (β t).val) '' Ioo
      (0 : unitInterval) 1) at h
    rwa [hβint] at h
  exact ⟨β, σ, hβinj, hβrange, hβint, fun t => hρ (mem_range_self t), hβhom.trans hPσ⟩

end GraphMinor.GM12
