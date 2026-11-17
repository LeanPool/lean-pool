/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.PrepInv


/-!
# M5: the deferred construction's contract (`PrepContract`)

`initCore` builds the chain at once (eager) or one `prepareStep` at a time (lazy); `topPI`
describes the core while it is being built and `topNu` counts the steps left.
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
/-- What the construction needs of the parameters. -/
def topPP (P : Params) : Prop := TopParams P ∧ 3 ≤ P.H

/-- A core whose chain is being built. -/
def topPI (s : Core) : Prop := topPP s.P ∧ s.ready = false ∧ ∃ h, 1 ≤ h ∧ h ≤ s.P.H + 1 ∧ Stage
  s.P h s

theorem topPP.beta {P : Params} (h : topPP P) : 1 ≤ P.beta := by
  have hr := h.1.room 1 le_rfl
  have h1 : 1 ≤ 2 ^ Dmax P 1 := Nat.one_le_two_pow
  have h2 : 2 ≤ n0max P 1 + 1 := by have := n0max_pos (P := P) 1; omega
  have : 2 ≤ 2 ^ P.beta := le_trans (by nlinarith) hr
  by_contra hb0
  rw [show P.beta = 0 by omega] at this; simp at this

/-- The eager construction's loop. -/
theorem loop_run {P : Params} (hPP : topPP P) : ∀ (l : List Nat) (h : Nat) (s : Core), Stage P h s →
    1 ≤ h → h ≤ P.H + 1 → P.H + 2 - h ≤ l.length →
    ∃ s', (forIn l PUnit.unit fun (_ : Nat) (_ : PUnit) => do
        let b ← initStep
        if b = true then pure (ForInStep.done PUnit.unit) else pure (ForInStep.yield PUnit.unit) :
        CM PUnit).run s = .ok () s' ∧ Final P s'
  | [], h, s, _, _, hH, hl => by simp at hl; omega
  | x :: t, h, s, S, h1, hH, hl => by
    rw [List.forIn_cons]
    by_cases hh : h ≤ P.H
    · obtain ⟨s', hr, S', -⟩ := stage_next S h1 hh hPP.beta
      obtain ⟨s'', hr', F⟩ := loop_run hPP t (h + 1) s' S' (by omega) (by omega) (by
        simp only [List.length_cons] at hl
        omega)
      refine ⟨s'', ?_, F⟩
      rw [run_bind, run_bind, hr]
      simp only [Bool.false_eq_true, ↓reduceIte, EStateM.run_pure]
      exact hr'
    · have e : h = P.H + 1 := by omega
      subst e
      obtain ⟨s', hr, F, -⟩ := stage_last S (by have := hPP.2; omega)
      refine ⟨s', ?_, F⟩
      rw [run_bind, run_bind, hr]
      simp

theorem Final.ready {P : Params} {s : Core} (F : Final P s) (r : Bool) : Final P { s with ready
  := r } :=
  ⟨F.low, F.res, F.prep, F.nsz, F.nodes, F.cin, F.lpar, F.psz, F.path, F.tag⟩

theorem initCore_eager_eq (s : Core) : (initCore false).run s =
    ((forIn (List.range (s.P.H + 1)) PUnit.unit fun (_ : Nat) (_ : PUnit) => do
        let b ← initStep
        if b = true then pure (ForInStep.done PUnit.unit) else pure (ForInStep.yield PUnit.unit) :
        CM PUnit) >>= fun _ => (modify fun t => { t with ready := true } : CM PUnit)).run
      { initState s.P with
        prep := some { chunk := 1, below := 1, path := Array.replicate (s.P.H + 1) NIL }, ready
          := true } :=
  rfl

theorem prep_eager (s s' : Core) (hPP : topPP s.P) (h : (initCore false).run s = .ok () s') :
    TopInv s' ∧ s'.resJob = none := by
  have S := stage_one s true
  obtain ⟨s1, hr, F⟩ := loop_run hPP (List.range (s.P.H + 1)) 1 _ S le_rfl (by omega) (by simp)
  rw [initCore_eager_eq, run_bind, hr] at h
  simp only [run_modify] at h
  cases h
  have F' := F.ready true
  exact ⟨F'.topInv hPP.1 hPP.2, F'.res⟩

theorem prep_lazy (s s' : Core) (hPP : topPP s.P) (h : (initCore true).run s = .ok () s') :
    topPI s' ∧ topNu s' ≤ s.P.H + 1 := by
  rw [initCore_lazy_run] at h; cases h
  have S := stage_one s false
  refine ⟨⟨hPP, rfl, 1, le_rfl, by omega, S⟩, ?_⟩
  rw [S.nu]
  omega

theorem prep_step (s : Core) (hI : topPI s) : ∃ b s', prepareStep.run s = .ok b s' ∧
    (b = true → TopInv s' ∧ s'.resJob = none) ∧ (b = false → topPI s' ∧ topNu s' < topNu s) := by
  obtain ⟨hPP, hrd, h, h1, hH, S⟩ := hI
  have hn := S.nu
  by_cases hh : h ≤ s.P.H
  · obtain ⟨s', hr, S', hrd'⟩ := stage_next S h1 hh hPP.beta
    refine ⟨false, s', ?_, fun e => absurd e (by simp), fun _ => ?_⟩
    · unfold prepareStep
      simp only [hrd, Bool.not_eq_eq_eq_not, Bool.not_true, bind_pure_comp, EStateM.run_bind,
          EStateM.run_get, run_ite, EStateM.run_modify]
      rw [hr]
      change EStateM.Result.ok s'.ready s' = EStateM.Result.ok false s'
      rw [hrd', hrd]
    · have hP' : s'.P = s.P := S'.P.trans S.P.symm
      refine ⟨⟨by rw [hP']; exact hPP, by rw [hrd', hrd], h + 1, by omega, by rw [hP']; omega,
        by rw [hP']; exact S'⟩, ?_⟩
      rw [S'.nu, hn]; omega
  · have e : h = s.P.H + 1 := by omega
    subst e
    obtain ⟨s', hr, F, hrd'⟩ := stage_last S (by have := hPP.2; omega)
    refine ⟨true, { s' with ready := true }, ?_, fun _ => ?_, fun e => absurd e (by simp)⟩
    · unfold prepareStep
      simp only [hrd, Bool.not_eq_eq_eq_not, Bool.not_true, bind_pure_comp, EStateM.run_bind,
          EStateM.run_get, run_ite, EStateM.run_modify]
      rw [hr]
      rfl
    · have F' := F.ready true
      exact ⟨F'.topInv hPP.1 hPP.2, F'.res⟩

/-- **The deferred construction's contract.** -/
theorem prepContract : PrepContract TopInv topPI topNu topPP :=
  ⟨prep_eager, prep_lazy, prep_step⟩

end OrderMaintenance.Proof.Top
