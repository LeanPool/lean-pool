/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.Topology.Instances.EReal.Lemmas

/-! # Upper semicontinuous regularization of extended-real functions -/

@[expose] public section

open Set Filter
open scoped Topology

namespace SGPT.Foundations.Analysis.FirstPass

noncomputable section

section Regularization

variable {X : Type*} [TopologicalSpace X]

/-- The upper semicontinuous regularization, as the infimum of the local
suprema over all neighborhoods. Neither infinity is converted to a real. -/
def uscRegularization (f : X → EReal) (x : X) : EReal :=
  ⨅ U ∈ 𝓝 x, ⨆ y ∈ U, f y

theorem le_uscRegularization (f : X → EReal) : f ≤ uscRegularization f := by
  intro x
  apply le_iInf
  intro U
  apply le_iInf
  intro hU
  exact le_iSup_of_le x (le_iSup_of_le (mem_of_mem_nhds hU) le_rfl)

theorem uscRegularization_le_localSup (f : X → EReal) {x : X} {U : Set X}
    (hU : U ∈ 𝓝 x) : uscRegularization f x ≤ ⨆ y ∈ U, f y :=
  iInf_le_of_le U (iInf_le_of_le hU le_rfl)

theorem uscRegularization_mono {f g : X → EReal} (hfg : f ≤ g) :
    uscRegularization f ≤ uscRegularization g := by
  intro x
  exact iInf_mono fun U => iInf_mono fun _ => iSup_mono fun y => iSup_mono fun _ => hfg y

theorem upperSemicontinuous_uscRegularization (f : X → EReal) :
    UpperSemicontinuous (uscRegularization f) := by
  intro x a ha
  obtain ⟨U, hU⟩ := iInf_lt_iff.mp ha
  obtain ⟨hUx, hUa⟩ := iInf_lt_iff.mp hU
  obtain ⟨W, hWU, hW, hxW⟩ := mem_nhds_iff.mp hUx
  filter_upwards [hW.mem_nhds hxW] with y hy
  exact (uscRegularization_le_localSup f
    (mem_of_superset (hW.mem_nhds hy) hWU)).trans_lt hUa

/-- The regularization lies below every upper semicontinuous majorant. -/
theorem uscRegularization_le {f g : X → EReal} (hg : UpperSemicontinuous g)
    (hfg : f ≤ g) : uscRegularization f ≤ g := by
  intro x
  apply le_of_forall_gt
  intro a ha
  obtain ⟨b, hxb, hba⟩ := exists_between ha
  have hU : {y | g y < b} ∈ 𝓝 x := hg x b hxb
  exact ((uscRegularization_le_localSup f hU).trans
    (iSup_le fun y => iSup_le fun hy => (hfg y).trans (le_of_lt hy))).trans_lt hba

theorem uscRegularization_le_iff {f g : X → EReal} (hg : UpperSemicontinuous g) :
    uscRegularization f ≤ g ↔ f ≤ g :=
  ⟨fun h => (le_uscRegularization f).trans h, uscRegularization_le hg⟩

theorem uscRegularization_eq {f : X → EReal} (hf : UpperSemicontinuous f) :
    uscRegularization f = f :=
  le_antisymm (uscRegularization_le hf le_rfl) (le_uscRegularization f)

@[simp] theorem uscRegularization_idem (f : X → EReal) :
    uscRegularization (uscRegularization f) = uscRegularization f :=
  uscRegularization_eq (upperSemicontinuous_uscRegularization f)

/-- This includes both the constant positive- and negative-infinite functions. -/
@[simp] theorem uscRegularization_const (c : EReal) :
    uscRegularization (fun _ : X => c) = fun _ => c :=
  uscRegularization_eq upperSemicontinuous_const

/-- Adding a finite constant preserves upper semicontinuity for
extended-real-valued functions.  Addition on `EReal` is not continuous at
the two indeterminate pairs, but a finite second summand excludes both. -/
theorem upperSemicontinuous_add_coe_const {f : X → EReal}
    (hf : UpperSemicontinuous f) (c : ℝ) :
    UpperSemicontinuous (fun x => f x + (c : EReal)) :=
  hf.add' upperSemicontinuous_const fun _ =>
    EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot c))
      (Or.inr (EReal.coe_ne_top c))

/-- Upper-semicontinuous regularization commutes with translation by a
finite constant. -/
theorem uscRegularization_add_coe_const (f : X → EReal) (c : ℝ) :
    uscRegularization (fun x => f x + (c : EReal)) =
      fun x => uscRegularization f x + (c : EReal) := by
  have hnegpos : (-(c : EReal) + (c : EReal)) = 0 := by
    rw [← EReal.coe_neg, ← EReal.coe_add]
    norm_num
  have hposneg : ((c : EReal) + -(c : EReal)) = 0 := by
    rw [← EReal.coe_neg, ← EReal.coe_add]
    norm_num
  apply le_antisymm
  · exact uscRegularization_le
      (upperSemicontinuous_add_coe_const
        (upperSemicontinuous_uscRegularization f) c)
      (fun x => by gcongr; exact le_uscRegularization f x)
  · have h : uscRegularization f ≤ fun x =>
        uscRegularization (fun y => f y + (c : EReal)) x + ((-c : ℝ) : EReal) := by
      apply uscRegularization_le
        (upperSemicontinuous_add_coe_const
          (upperSemicontinuous_uscRegularization
            (fun y => f y + (c : EReal))) (-c))
      intro x
      rw [← (EReal.addLECancellable_coe c).add_le_add_iff_right]
      simpa [add_assoc, hnegpos] using
        (le_uscRegularization (fun y => f y + (c : EReal)) x)
    intro x
    rw [← (EReal.addLECancellable_coe (-c)).add_le_add_iff_right]
    simpa [add_assoc, hposneg] using h x

/-- Regularizing a pointwise supremum gives the least USC common majorant. -/
theorem uscRegularization_sSup_le_iff {F : Set (X → EReal)} {g : X → EReal}
    (hg : UpperSemicontinuous g) :
    uscRegularization (sSup F) ≤ g ↔ ∀ f ∈ F, f ≤ g := by
  rw [uscRegularization_le_iff hg, sSup_le_iff]

end Regularization

end

end SGPT.Foundations.Analysis.FirstPass
