/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Assembly.Template.Issue
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.BatchDescent.Trail.Compact

/-! # Polynomial bounds for the common template charges -/

@[expose] public section

namespace MatrixMultiplicationAllFields.MatrixExponent.Assembly.Template
open BatchDescent.Phase Packing Coloring

variable {I : Type*} {F : I → Type} {T : (i : I) → Template (F i)}
  {a b delta C : I → ℕ} {large small height hosts : I → ℕ}
  (largeTwo : ∀ i, 2 ≤ large i) (smallTwo : ∀ i, 2 ≤ small i)
  (smallLeLarge : ∀ i, small i ≤ large i)

local notation "Cost" => MixedCost large small height hosts

include largeTwo smallTwo smallLeLarge in
/-- Apply the two fixed rates to the input widths and add the navigation computation. -/
theorem navCost_mixed {degree : I → ℕ}
    (format : Cost (fun i => (T i).format.width))
    (groups : Cost (fun i => ((T i).groupInput (a i)).width))
    (child : Cost (fun i => (Child.Input (T i).scheme.m (T i).scheme.d).width))
    (compute : Cost (fun i => 2 ^ (T i).size (a i) *
      (100 + ((T i).size (a i) + 2 ^ degree i)) ^ 201)) :
    Cost (fun i => (T i).navCost (a i) (degree i)) := by
  have h := format.add (groups.scale 3 smallTwo smallLeLarge) largeTwo smallTwo
  have h := h.add (child.scale 68 smallTwo smallLeLarge) largeTwo smallTwo
  exact h.add compute largeTwo smallTwo

include largeTwo smallTwo smallLeLarge in
/-- Charge the status circuit from the format and status widths. -/
theorem statusCost_mixed (format : Cost (fun i => (T i).format.width))
    (status : Cost (fun i => ((T i).Status (a i)).width)) :
    Cost (fun i => (T i).statusCost (a i)) :=
  format.add (status.scale 34 smallTwo smallLeLarge) largeTwo smallTwo

include largeTwo smallTwo smallLeLarge in
/-- Charge four runs of the child construction at the full template degree. -/
theorem childCost_mixed (format : Cost (fun i => (T i).format.width))
    (status : Cost (fun i => ((T i).Status (a i)).width))
    (navigate : Cost (fun i => (T i).navCost (a i) ((T i).degree (a i) (delta i) (C i)))) :
    Cost (fun i => (T i).childCost (a i) (delta i) (C i)) := by
  have status := statusCost_mixed largeTwo smallTwo smallLeLarge format status
  have h := (format.scale 5 smallTwo smallLeLarge).add status largeTwo smallTwo
  exact (h.add navigate largeTwo smallTwo).scale 4 smallTwo smallLeLarge

include largeTwo smallTwo smallLeLarge in
/-- Combine the full and core navigation, both status records, and the output header. -/
theorem headerCost_mixed (format : Cost (fun i => (T i).format.width))
    (status : Cost (fun i => ((T i).Status (a i)).width))
    (navigate : Cost (fun i => (T i).navCost (a i) ((T i).degree (a i) (delta i) (C i))))
    (navigateCore : Cost (fun i => (T i).navCost (a i)
      (Child.nextWidth ((T i).scheme.h - a i) (delta i) (T i).scheme.d)))
    (compute : Cost (fun i => 2 ^ (T i).size (a i) * (100 + ((T i).size (a i) +
      2 ^ (T i).degree (a i) (delta i) (C i) +
      2 ^ Child.nextWidth ((T i).scheme.h - a i) (delta i) (T i).scheme.d)) ^ 16))
    (flags : Cost (fun i =>
      (Format.vec ((T i).size (a i)) (.vec ((T i).degree (a i) (delta i) (C i)) .bit)).width))
    (header : Cost (fun i => ((T i).ChildHeader (a i) (delta i) (C i)).width)) :
    Cost (fun i => (T i).headerCost (a i) (delta i) (C i)) := by
  have formatFive := format.scale 5 smallTwo smallLeLarge
  have frozen := format.add (status.scale 2 smallTwo smallLeLarge) largeTwo smallTwo
  have statusCharge := statusCost_mixed largeTwo smallTwo smallLeLarge format status
  have preparation := ((formatFive.add statusCharge largeTwo smallTwo).add frozen largeTwo smallTwo)
  have navigation := (formatFive.add navigate largeTwo smallTwo).add navigateCore largeTwo smallTwo
  have navigation := navigation.add compute largeTwo smallTwo
  have lists : Cost (fun i => ((T i).Lists (a i) (delta i) (C i)).width) := by
    refine ((status.add status largeTwo smallTwo).add flags largeTwo smallTwo).mono fun i => ?_
    simp only [Lists, Format.width_pair, le_refl]
  have finish := lists.add (header.scale 34 smallTwo smallLeLarge) largeTwo smallTwo
  exact ((formatFive.add preparation largeTwo smallTwo).add navigation largeTwo smallTwo)
    |>.add finish largeTwo smallTwo

include largeTwo smallTwo smallLeLarge in
/-- Combine the input sampling, group lookups, and projection of the marked entries. -/
theorem markCost_mixed (poll : Cost (fun i => ((T i).Poll (a i) (b i)).width))
    (polls : Cost (fun i => ((T i).Polls (a i) (b i)).width))
    (groups : Cost (fun i => ((T i).Groups (a i) (b i)).width))
    (entries : Cost (fun i => ((T i).Entries (a i) (b i)).width))
    (lookups : Cost (fun i => 2 ^ ((T i).scheme.m + a i) *
      (1 + ((T i).PollRow (a i) (b i)).width +
        (Side.Input ((T i).scheme.h - a i + (T i).scheme.e) (b i)).width))) :
    Cost (fun i => (T i).markCost (a i) (b i)) := by
  have sampling := (poll.add (polls.scale 2 smallTwo smallLeLarge) largeTwo smallTwo)
    |>.scale 4 smallTwo smallLeLarge
  have project := (groups.add (entries.scale 2 smallTwo smallLeLarge) largeTwo smallTwo)
    |>.scale 4 smallTwo smallLeLarge
  exact (sampling.add lookups largeTwo smallTwo).add project largeTwo smallTwo

include largeTwo smallTwo smallLeLarge in
/-- Use the seat count to bound the layout input and the profile computation. -/
theorem layoutCost_mixed {bits profile : ℕ} (mark : Cost (fun i => (T i).markCost (a i) bits))
    (seats : Cost (fun i => Fintype.card ((T i).Slots (a i))))
    (entries : Cost (fun i => ((T i).Entries (a i) bits).width)) :
    Cost (fun i => (T i).layoutCost (a i) bits profile) := by
  let width (i : I) := (T i).scheme.m + a i + ((T i).scheme.h - a i + (T i).scheme.e)
  have slots : Cost (fun i => 2 ^ width i) := by
    refine seats.mono fun i => ?_
    rw [Fintype.card_congr ((T i).seatIndex (a i)).symm, Fintype.card_fin]
  have input : Cost (fun i => (Side.Input (width i) bits).width) :=
    (slots.scale (Side.Entry bits).width smallTwo smallLeLarge).mono fun i => by
      rw [Side.Input, Format.width_vec, mul_comm]
  have mark := mark.add (seats.scale (Branches.charge bits) smallTwo smallLeLarge |>.mono
    (fun i => le_of_eq (mul_comm _ _))) largeTwo smallTwo
  have input := ((entries.add (input.scale 2 smallTwo smallLeLarge) largeTwo smallTwo).scale 4
    smallTwo smallLeLarge)
  have compute := slots.mul (Poly.const smallTwo ((100 + profile) ^ 8)) smallLeLarge
  exact (mark.add input largeTwo smallTwo).add (compute.scale 4 smallTwo smallLeLarge)
    largeTwo smallTwo

include largeTwo smallTwo in
private theorem pair_mixed {A B : I → Format}
    (hA : Cost (fun i => (A i).width)) (hB : Cost (fun i => (B i).width)) :
    Cost (fun i => ((A i).pair (B i)).width) :=
  (hA.add hB largeTwo smallTwo).mono fun _ => (Format.width_pair ..).le

include largeTwo smallTwo smallLeLarge in
/-- Assemble the raw fields and account for the copies, child, layout, and final projection. -/
theorem rawCost_mixed {profile : ℕ} (format : Cost (fun i => (T i).format.width))
    (poll : Cost (fun i => ((T i).Poll (a i) (b i)).width))
    (counted : Cost (fun i => ((T i).Counted (a i) (b i)).width))
    (status : Cost (fun i => ((T i).Status (a i)).width))
    (graph : Cost (fun i => ((T i).Graph (a i) (delta i) (C i)).width))
    (bit : Cost (fun _ => Format.bit.width))
    (child : Cost (fun i => (T i).childCost (a i) (delta i) (C i)))
    (layout : Cost (fun i => (T i).layoutCost (a i) (b i) profile))
    (raw : Cost (fun i => ((T i).Raw (a i) (b i) (delta i) (C i)).width)) :
    Cost (fun i => (T i).rawCost (a i) (b i) (delta i) (C i) profile) := by
  have copies := pair_mixed largeTwo smallTwo format (pair_mixed largeTwo smallTwo poll poll)
  have fields := pair_mixed largeTwo smallTwo (pair_mixed largeTwo smallTwo status graph)
    (pair_mixed largeTwo smallTwo bit counted)
  have x := (poll.add (copies.scale 2 smallTwo smallLeLarge) largeTwo smallTwo)
    |>.scale 4 smallTwo smallLeLarge
  have count := (poll.add (counted.scale 2 smallTwo smallLeLarge) largeTwo smallTwo)
    |>.scale 4 smallTwo smallLeLarge
  have y := child.add (layout.add count largeTwo smallTwo) largeTwo smallTwo
  have z := (fields.add (raw.scale 2 smallTwo smallLeLarge) largeTwo smallTwo)
    |>.scale 4 smallTwo smallLeLarge
  exact (x.add y largeTwo smallTwo).add z largeTwo smallTwo

include largeTwo smallTwo smallLeLarge in
/-- Charge the poll copy and attach the completed header to the raw record. -/
theorem headedCost_mixed {profile : ℕ} (format : Cost (fun i => (T i).format.width))
    (poll : Cost (fun i => ((T i).Poll (a i) (b i)).width))
    (raw : Cost (fun i => (T i).rawCost (a i) (b i) (delta i) (C i) profile))
    (header : Cost (fun i => (T i).headerCost (a i) (delta i) (C i))) :
    Cost (fun i => (T i).headedCost (a i) (b i) (delta i) (C i) profile) := by
  have copies := (pair_mixed largeTwo smallTwo poll format).scale 2 smallTwo smallLeLarge
  have prepare := (poll.add copies largeTwo smallTwo).scale 4 smallTwo smallLeLarge
  exact prepare.add (raw.add (header.scale 4 smallTwo smallLeLarge) largeTwo smallTwo)
    largeTwo smallTwo

end MatrixMultiplicationAllFields.MatrixExponent.Assembly.Template
