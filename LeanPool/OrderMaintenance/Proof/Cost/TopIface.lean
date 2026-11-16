/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Cost.Sched


/-!
# The top structure, as an interface

M4 uses the top structure through a contract: an invariant `TI` that depends only on the top
structure's fields and the chunk list (`TopSame`), whose insertion job starts when a chunk is
popped, and whose every step succeeds and decreases a measure `μ ≤ J`. M5 proves the contract
(Lemmas T0–T5).
-/


@[expose] public section

namespace OrderMaintenance.Proof

open OrderMaintenance.Model
/-- What the top structure may depend on. -/
structure TopSame (s s' : Core) : Prop where
  top : s'.nodes = s.nodes ∧ s'.path = s.path ∧ s'.cin = s.cin ∧ s'.lpar = s.lpar ∧
    s'.resJob = s.resJob ∧ s'.prep = s.prep ∧ s'.ready = s.ready ∧ s'.firstChunk = s.firstChunk
  Csize : s'.C.size = s.C.size
  links : ∀ c, cN s' c = cN s c ∧ cP s' c = cP s c ∧ cT s' c = cT s c
  P : s'.P = s.P

theorem TopSame.refl (s : Core) : TopSame s s :=
  ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, rfl, fun _ => ⟨rfl, rfl, rfl⟩, rfl⟩

theorem TopSame.trans {a b c : Core} (h1 : TopSame a b) (h2 : TopSame b c) : TopSame a c := by
  obtain ⟨⟨t1, t2, t3, t4, t5, t6, t7, t8⟩, s1, l1, P1⟩ := h1
  obtain ⟨⟨u1, u2, u3, u4, u5, u6, u7, u8⟩, s2, l2, P2⟩ := h2
  exact ⟨⟨u1.trans t1, u2.trans t2, u3.trans t3, u4.trans t4, u5.trans t5, u6.trans t6,
    u7.trans t7, u8.trans t8⟩, s2.trans s1, fun d => ⟨(l2 d).1.trans (l1 d).1,
    (l2 d).2.1.trans (l1 d).2.1, (l2 d).2.2.trans (l1 d).2.2⟩, P2.trans P1⟩

theorem CFrame.topSame {s s' : Core} (h : CFrame s s') : TopSame s s' :=
  ⟨h.top, h.Csize, fun c => ⟨(h.C c).2.2.2.2.2.1, (h.C c).2.2.2.2.2.2.1, (h.C c).2.2.2.2.2.2.2⟩, h.P⟩

theorem DFrame.topSame {s s' : Core} (h : DFrame s s') : TopSame s s' :=
  ⟨h.top, h.Csize, h.links, h.P⟩

/-- The insertion's element link and size update leave the top structure alone. -/
theorem topSame_ins {s s2 : Core} {x lab hh : Nat}
    (hC : s2.C = (sizeState (linkElem s x s.E.size lab hh) (gC s (eG s x))).C)
    (hP : s2.P = s.P)
    (ht : s2.nodes = s.nodes ∧ s2.path = s.path ∧ s2.cin = s.cin ∧ s2.lpar = s.lpar ∧
      s2.resJob = s.resJob ∧ s2.prep = s.prep ∧ s2.ready = s.ready ∧ s2.firstChunk = s.firstChunk) :
    TopSame s s2 := by
  have e : (linkElem s x s.E.size lab hh).C = s.C := rfl
  refine ⟨ht, by rw [hC]; simp [sizeState, e], fun c => ?_, hP⟩
  simp only [cN, cP, cT, hC, sizeState, Array.getX_modify, e]
  split <;> simp

/-- **The top structure's contract.** `TI` is its invariant (it may require INV-S), `μ` measures
the work left in the running job, and the job of a chunk split needs at most `J` steps. Both
depend only on what `TopSame` keeps. The structure has room for chunks below `cap P`. -/
structure TopContract (TI : Core → Prop) (μ : Core → Nat) (J : Nat) (cap : Params → Nat) : Prop where
  frame : ∀ s s', TopSame s s' → TI s → TI s'
  mframe : ∀ s s', TopSame s s' → μ s' = μ s
  start : ∀ s A x, INV s A → TI s → s.resJob = none → LiveC s x → cSt s x = .quiet →
    s.C.size + 2 ≤ cap s.P →
    ∃ job s2, (insertAround x s.C.size (s.C.size + 1)).run
        (linkChunkPair (push2 s) x s.C.size (s.C.size + 1)) = .ok job s2 ∧
      1 ≤ μ (markState s2 x s.C.size (s.C.size + 1) job) ∧
      μ (markState s2 x s.C.size (s.C.size + 1) job) ≤ J ∧
      TI (markState s2 x s.C.size (s.C.size + 1) job)
  step : ∀ s A job, INV s A → TI s → s.resJob = some job →
    ∃ r s', (jobStep job).run s = .ok r s' ∧ TI { s' with resJob := r } ∧
      ∀ j', r = some j' → 1 ≤ μ { s' with resJob := r } ∧ μ { s' with resJob := r } < μ s

/-- **The contract with a parameter-dependent job bound** (what M5 proves): a chunk split's job
needs at most `J P` steps, `P` the core's parameters. -/
structure TopContractP (TI : Core → Prop) (μ : Core → Nat) (J : Params → Nat) (cap : Params → Nat) :
    Prop where
  frame : ∀ s s', TopSame s s' → TI s → TI s'
  mframe : ∀ s s', TopSame s s' → μ s' = μ s
  start : ∀ s A x, INV s A → TI s → s.resJob = none → LiveC s x → cSt s x = .quiet →
    s.C.size + 2 ≤ cap s.P →
    ∃ job s2, (insertAround x s.C.size (s.C.size + 1)).run
        (linkChunkPair (push2 s) x s.C.size (s.C.size + 1)) = .ok job s2 ∧
      1 ≤ μ (markState s2 x s.C.size (s.C.size + 1) job) ∧
      μ (markState s2 x s.C.size (s.C.size + 1) job) ≤ J s.P ∧
      TI (markState s2 x s.C.size (s.C.size + 1) job)
  step : ∀ s A job, INV s A → TI s → s.resJob = some job →
    ∃ r s', (jobStep job).run s = .ok r s' ∧ TI { s' with resJob := r } ∧
      ∀ j', r = some j' → 1 ≤ μ { s' with resJob := r } ∧ μ { s' with resJob := r } < μ s

/-- `TI` at parameters `P`. -/
def TIat (TI : Core → Prop) (P : Params) (s : Core) : Prop := TI s ∧ s.P = P

/-- At fixed parameters, the job bound is a constant. -/
theorem TopContractP.at {TI : Core → Prop} {μ : Core → Nat} {J cap : Params → Nat}
    (h : TopContractP TI μ J cap) (P : Params) : TopContract (TIat TI P) μ (J P) cap := by
  refine ⟨fun s s' hs hT => ⟨h.frame s s' hs hT.1, hs.P.trans hT.2⟩, h.mframe, ?_, ?_⟩
  · intro s A x hI hT hres hx hq hcap
    obtain ⟨job, s2, hrun, h1, h2, h3⟩ := h.start s A x hI hT.1 hres hx hq hcap
    have hR : TopRel (linkChunkPair (push2 s) x s.C.size (s.C.size + 1)) s2 := by
      have := top_insertAround x s.C.size (s.C.size + 1)
        (linkChunkPair (push2 s) x s.C.size (s.C.size + 1))
      rw [hrun] at this; exact this
    refine ⟨job, s2, hrun, h1, by rw [← hT.2]; exact h2, h3, ?_⟩
    show s2.P = P
    rw [hR.rest.1, ← hT.2]; rfl
  · intro s A job hI hT hres
    obtain ⟨r, s', hrun, h1, h2⟩ := h.step s A job hI hT.1 hres
    have hR : TopRel s s' := by have := top_jobStep job s; rw [hrun] at this; exact this
    exact ⟨r, s', hrun, ⟨h1, by show s'.P = P; rw [hR.rest.1, hT.2]⟩, h2⟩

end OrderMaintenance.Proof
