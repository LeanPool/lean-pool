/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Word.PeakInitTop
public import LeanPool.OrderMaintenance.Proof.Word.PeakLeaf


/-!
# Theorem W, option (A), stage A2: the peaks of the core procedures, in the form of `wpB_coreCall`

For a core `s` encoded in a machine state (`Enc`), with its stored values below `2^K` (option
(B)'s `WB K s`), its handles below `2^KH`, its parameters with room (`PRoom K s.P`) and its
capacities below `2^K` (`CapsW K κ`), a normal run of each core procedure from its entry state
`setLocs 0 ps vs` (arguments below `2^K`) computes nothing at or above `2^(max (2K+4) KH)`
(`≤ 2^(2K+4) + 2^KH`, `lt_pow_max_add`):

* `order_peak`, `markDead_peak` (any core);
* `prepareStep_peak` (a core being built, `PrepM`);
* `initCore_peak` (the empty core `freshC P` of the construction).

`insertAfter` is `insertAfter_peak` (`PeakIns.lean`), for a core in service.

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Word OrderMaintenance.Proof.Top
open OrderMaintenance.Machine (Reg)

variable {K KH : Nat} {κ : Caps}

/-- The peak width of the core procedures. -/
abbrev wPk (K KH : Nat) : Nat := max (2 * K + 4) KH

theorem wPk_ge (K KH : Nat) : 2 * K + 4 ≤ wPk K KH := le_max_left _ _
theorem wPk_geH (K KH : Nat) : KH ≤ wPk K KH := le_max_right _ _

theorem pk_of_PK {Γ : Reg → Nat} {W : Nat} {c : Stm} {s : Core} {L : Loc} (h : PK K KH κ Γ W c s L)
    {s' : Core} {L' : Loc} {n : Nat} (he : evalF κ c s L = .ok s' L' n) : pkF κ c s L < 2 ^ W :=
  (h (by rw [he]; exact Res.noConfusion)).1

theorem pk_of_PKok {Γ : Reg → Nat} {W : Nat} {c : Stm} {s : Core} {L : Loc} (h : PKok K KH κ Γ W c s L)
    {s' : Core} {L' : Loc} {n : Nat} (he : evalF κ c s L = .ok s' L' n) : pkF κ c s L < 2 ^ W :=
  (h _ _ _ he).1

section top
variable {p : Nat} {m : OrderMaintenance.Machine.State} {s : Core}
variable (hC : CapsW K κ) (hK : 8 ≤ K) (hE : Enc p κ s m) (hWB : WB K s) (hh : ∀ i, (s.E.getX i).h < 2 ^ KH)
  (hR : PRoom K s.P)
include hC hK hE hWB hh hR

theorem gd_entry {ps : List Reg} {vs : List Nat} (hvs : ∀ v ∈ vs, v < 2 ^ K) :
    Gd K KH κ (ΓK K) s (OrderMaintenance.Machine.State.setLocs (fun _ => 0) ps vs) :=
  gd_of_WB hE hWB (by omega) hh hR (setLocs_lt (zero_locs _) (fun _ _ => le_refl K) hvs)

/-- **`order`**. -/
theorem order_peak {vs : List Nat} (hvs : ∀ v ∈ vs, v < 2 ^ K) {s' : Core} {L' : Loc} {n : Nat}
    (he : evalF κ orderP.body s (OrderMaintenance.Machine.State.setLocs (fun _ => 0) orderP.params vs) = .ok s' L' n) :
    pkF κ orderP.body s (OrderMaintenance.Machine.State.setLocs (fun _ => 0) orderP.params vs) < 2 ^ wPk K KH :=
  pk_of_PK (PK.of_safe hC (by omega) (by have := wPk_ge K KH; omega) (order_safe hK (wPk_ge K KH))
    (gd_entry hC hK hE hWB hh hR hvs)) he

/-- **`markDead`**. -/
theorem markDead_peak {vs : List Nat} (hvs : ∀ v ∈ vs, v < 2 ^ K) {s' : Core} {L' : Loc} {n : Nat}
    (he : evalF κ markDeadP.body s (OrderMaintenance.Machine.State.setLocs (fun _ => 0) markDeadP.params vs) = .ok s' L' n) :
    pkF κ markDeadP.body s (OrderMaintenance.Machine.State.setLocs (fun _ => 0) markDeadP.params vs) < 2 ^ wPk K KH :=
  pk_of_PK (PK.of_safe hC (by omega) (by have := wPk_ge K KH; omega) (markDead_safe hK (wPk_ge K KH))
    (gd_entry hC hK hE hWB hh hR hvs)) he

/-- **`prepareStep`**, on a core being built. -/
theorem prepareStep_peak (hM : PrepM s) {vs : List Nat} (hvs : ∀ v ∈ vs, v < 2 ^ K) {s' : Core} {L' : Loc}
    {n : Nat} (he : evalF κ prepP.body s (OrderMaintenance.Machine.State.setLocs (fun _ => 0) prepP.params vs) = .ok s' L' n) :
    pkF κ prepP.body s (OrderMaintenance.Machine.State.setLocs (fun _ => 0) prepP.params vs) < 2 ^ wPk K KH :=
  pk_of_PKok (prepP_pkok hC hK (wPk_ge K KH) hM (gd_entry hC hK hE hWB hh hR hvs)) he

end top

/-- **`initCore`**, from the empty core of the construction. -/
theorem initCore_peak {p : Nat} {m : OrderMaintenance.Machine.State} {P : Params} (hC : CapsW K κ) (hK : 8 ≤ K)
    (hE : Enc p κ (freshC P) m) (hWB : WB K (freshC P)) (hh : ∀ i, ((freshC P).E.getX i).h < 2 ^ KH)
    (hR : PRoom K P) (hH : 1 ≤ P.H) (hK2 : InitCaps κ P) (hE2 : 2 ≤ κ.tbl .E) (hG2 : 2 ≤ κ.tbl .G)
    {vs : List Nat} (hvs : ∀ v ∈ vs, v < 2 ^ K) {s' : Core} {L' : Loc} {n : Nat}
    (he : evalF κ initCoreS (freshC P) (OrderMaintenance.Machine.State.setLocs (fun _ => 0) ["lz"] vs) = .ok s' L' n) :
    pkF κ initCoreS (freshC P) (OrderMaintenance.Machine.State.setLocs (fun _ => 0) ["lz"] vs) < 2 ^ wPk K KH :=
  pk_of_PKok (initCore_pkok hC hK (wPk_ge K KH) hH hK2 hE2 hG2
    (gd_entry (s := freshC P) hC hK hE hWB hh (by simpa [freshC] using hR) hvs)) he

end OrderMaintenance.Impl
