/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Impl.PeakInit
public import LeanPool.OrderMaintenance.Impl.Caps


/-!
# Theorem W, option (A), stage A2: the construction of a core, along its stages

`initStep_pk_stage`: a stage of the chain (`Stage P h`, `Top/PrepStage.lean`) carries the tag
invariant `initStep_pk` needs (`chainTag_lt`). `initCore_pkok`: the eager construction, along the
stages (the context of `initCoreS_eager`), and the lazy one.

Nothing here is used by Theorems A and B.
-/


@[expose] public section

namespace OrderMaintenance.Impl

open OrderMaintenance.Model OrderMaintenance.Proof OrderMaintenance.Proof.Top
open OrderMaintenance.Machine (Reg)

variable {K KH W : Nat} {κ : Caps}

section stage
variable (hC : CapsW K κ) (hK : 8 ≤ K) (hW : 2 * K + 4 ≤ W)
include hC hK hW

theorem initStep_pk_stage {P : Params} {h : Nat} {s : Core} {L : Loc} (S : Stage P h s) (h1 : 1 ≤ h)
    (hG : Gd K KH κ (ΓK K) s L) : PK K KH κ (ΓK K) W initStepP.body s L := by
  have hb := hG.vb.room.beta1
  refine initStep_pk hC hK hW hG (fun pr hp hle => ?_) hb
  obtain ⟨pa, hp', -, -⟩ := S.pr
  rw [hp] at hp'; cases hp'
  have hP := S.P
  refine ⟨?_, h1⟩
  show chainTag P (h - 1) < 2 ^ ((h - 1) * s.P.beta)
  rw [hP] at hb ⊢; exact chainTag_lt hb _

/-- **The eager construction loop**, along the stages (the context of `initCoreS_eager`). -/
theorem initLoop_pkok_stage {P : Params} (hH : 1 ≤ P.H) (hK2 : InitCaps κ P) {L : Loc}
    (hG : Gd K KH κ (ΓK K) (prepStart P true) L) : PKok K KH κ (ΓK K) W initLoopS (prepStart P true) L := by
  have hb := hG.vb.room.beta1
  have hPP : (prepStart P true).P = P := rfl
  rw [hPP] at hb
  have S1 := stage_one (initState P) true
  have hs0 : prepStart P true = { initState (initState P).P with
      prep := some { chunk := 1, below := 1, path := Array.replicate ((initState P).P.H + 1) NIL }, ready := true } :=
    rfl
  refine initLoop_pk hC hK hW (fun j t => Stage P (j + 1) t ∧ (j = 0 → t = prepStart P true))
    ⟨by rw [hs0]; exact S1, fun _ => rfl⟩ (fun j t ⟨St, h0⟩ hj => ?_) hG
  have hjP : j < P.H + 1 := hj
  have hA : ISAgree κ t 400 := isAgree_stage St (by omega) (by omega) hb hH hK2 (fun e => by
    have := h0 (by omega); subst this; exact ⟨rfl, rfl, rfl, rfl⟩)
  by_cases hle : j + 1 ≤ P.H
  · obtain ⟨t', hr, St', -⟩ := stage_next St (by omega) hle hb
    obtain ⟨L', c, ev, hd, -⟩ := hA false t' hr
    exact ⟨false, t', L', c, ev, hd, fun _ => ⟨St', fun e => absurd e (by omega)⟩,
      fun hG0 => PK.ok (initStep_pk_stage hC hK hW St (by omega) hG0)⟩
  · have e : j + 1 = P.H + 1 := by omega
    have St2 := St
    rw [e] at St2
    obtain ⟨t', hr, F, -⟩ := stage_last St2 hH
    obtain ⟨L', c, ev, hd, -⟩ := hA true t' hr
    exact ⟨true, t', L', c, ev, hd, fun h => absurd h (by simp),
      fun hG0 => PK.ok (initStep_pk_stage hC hK hW St (by omega) hG0)⟩

/-- **The construction of a core** (`initCore`, lazy or eager) from the fresh core. -/
theorem initCore_pkok {P : Params} (hH : 1 ≤ P.H) (hK2 : InitCaps κ P) (hE : 2 ≤ κ.tbl .E) (hG2 : 2 ≤ κ.tbl .G)
    {L : Loc} (hG : Gd K KH κ (ΓK K) (freshC P) L) : PKok K KH κ (ΓK K) W initCoreS (freshC P) L := by
  have hR := hG.vb.room
  unfold initCoreS
  refine PKok.seq (PK.ok (initState_pk hC hK hW hG)) (fun s1 L1 n1 h1 hG1 => ?_)
  obtain ⟨L1', c1, e1, -, -⟩ := initStateS_ok (κ := κ) (P := P) (L := L) hR.Be1 hR.Bg1 hE hG2
    (by have := hK2.C; omega) (by have := hK2.N; omega)
  rw [e1] at h1; injection h1 with es eL; subst es eL
  refine PKok.seq (PK.ok (PK.of_safe hC (by omega) (by omega) (by safe_tac) hG1)) (fun s2 L2 n2 h2 hG2' => ?_)
  rw [prepInit_ok hK2] at h2; injection h2 with es eL; subst es eL
  refine PKok.ite_ok hC hK hW hG2' (by safe_tac) (fun _ _ _ => PK.ok (PK.of_safe hC (by omega) (by omega)
    (by safe_tac) hG2')) (fun _ => ?_)
  exact PKok.seq (initLoop_pkok_stage hC hK hW hH hK2 hG2')
    (fun _ _ _ _ hG3 => PK.ok (PK.of_safe hC (by omega) (by omega) (by safe_tac) hG3))

/-- **A preparation step** of a core being built (`PrepM`, the context of `prepAgreeM`). -/
theorem prepP_pkok {s : Core} {L : Loc} (hM : PrepM s) (hG : Gd K KH κ (ΓK K) s L) :
    PKok K KH κ (ΓK K) W prepP.body s L := by
  obtain ⟨⟨-, -, h, h1, -, S⟩, -, -⟩ := hM
  exact prepP_pk hC hK hW hG (fun hG0 => PK.ok (initStep_pk_stage hC hK hW S h1 hG0))

end stage

end OrderMaintenance.Impl
