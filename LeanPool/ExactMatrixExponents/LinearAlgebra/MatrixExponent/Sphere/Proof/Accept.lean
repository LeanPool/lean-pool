/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Verifier.Caps
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.General.Weight
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Proof.Initial
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Geometry.Exterior
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Geometry.Origin
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Copy.Overlay
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Sphere.Geometry.Decoding

/-! A certified expansion supplies bounded local credits for every branch. -/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Surface.Local.Scenario
open Coloring Geometry Rounds

variable {F N A : Type} [Field F] [Fintype F] {x y : Wire} {a : Design} [ExpChar F a.p]
  {w : Scenario F N A a x y} {hF : a.M * (2 * a.D + 1) < Fintype.card F}
  {e k g ℓ D : ℕ} {menu : a.Menu F N A e} {start : w.Code 0 menu}
  {c : w.History k a.waves} {q : w.AtCode hF menu k a.waves le_rfl}

open scoped Classical in
theorem Certified.check (hc : w.Certified hF menu k start a.waves c q.frame)
    (written : q.tape = a.path start.tape a.waves (w.tapes c))
    (hu : 0 < a.chart * a.H) {E M : w.V → ℕ}
    (initial : ∀ v, clip a.waves (a.chart * a.H) (start.frame.stage.energyCre a.chart a.H a.g v)
      ≤ E v ∧
      start.frame.stage.timeCre a.chart a.H a.U v ≤ M v)
    (bound : ∀ (i : ℕ) (u : w.At i) (v : w.V),
      clip a.waves (a.chart * a.H) (u.stage.energyCre a.chart a.H a.g v)
        ≤ Input.energyLimit g D a.waves ∧
      u.stage.timeCre a.chart a.H a.U v ≤ Input.timeLimit g ℓ D) :
    let z := fun v : w.V => a.credits hF menu k g ℓ D ((q.tape (w.atlas.coord v).1).2
      (w.atlas.coord v).2)
    Credits.Check w.loc z E M ∧ ∀ v,
      (z v).power (Fin.last a.waves) = clip a.waves (a.chart * a.H) (q.frame.stage.energyCre
        a.chart a.H a.g v) ∧
      (z v).time (Fin.last a.waves) = q.frame.stage.timeCre a.chart a.H a.U v := by
  let row (v : w.V) := a.historyRow hF menu k a.waves le_rfl ((q.tape (w.atlas.coord v).1).2
    (w.atlas.coord v).2)
  let f v i := Metadata.energyCre (row v i) a.chart a.H a.g
  let t v i := Metadata.timeCre (row v i) a.chart a.H a.U
  have read (i : Fin (a.waves + 1)) (u : w.AtCode hF menu k i.val (Nat.le_of_lt_succ i.isLt))
      (ht : u.tape = a.path start.tape i.val (w.tapes (before c (Nat.le_of_lt_succ i.isLt)))) :
      (fun v => f v i) = u.frame.stage.energyCre a.chart a.H a.g ∧
      (fun v => t v i) = u.frame.stage.timeCre a.chart a.H a.U := by
    have eq (v : w.V) : row v i = (w.stored u.frame (w.atlas.coord v)).2 := by
      unfold row
      rw [written, Design.historyRow_path, ← u.read, ht]
      rfl
    exact ⟨funext fun v => by simp only [f, eq, w.stored_energyCre],
      funext fun v => by simp only [t, eq, w.stored_timeCre]⟩
  have first := read 0 start rfl
  have last := read (Fin.last a.waves) q written
  have step (j : Fin a.waves) :
      Geometry.Balanced (w.loc j) 0 (fun v => f v j.castSucc) (fun v => f v j.succ) ∧
      Geometry.Balanced (w.loc j) 0 (fun v => t v j.castSucc) (fun v => t v j.succ) := by
    obtain ⟨u, u', hp, hq, hb⟩ := hc j j.isLt
    obtain ⟨h₁, h₂⟩ := read j.castSucc u hp
    obtain ⟨h₃, h₄⟩ := read j.succ u' hq
    rw [h₁, h₂, h₃, h₄]
    exact ⟨hb.energy, hb.time⟩
  have lim (v : w.V) (i : Fin (a.waves + 1)) :
      clip a.waves (a.chart * a.H) (f v i) ≤ Input.energyLimit g D a.waves ∧ t v i
        ≤ Input.timeLimit g ℓ D := by
    induction i using Fin.lastCases with
    | last =>
      rw [congrFun last.1 v, congrFun last.2 v]
      exact bound _ q.frame v
    | cast j =>
      obtain ⟨u, _, hp, _⟩ := hc j j.isLt
      obtain ⟨h₁, h₂⟩ := read j.castSucc u hp
      rw [congrFun h₁ v, congrFun h₂ v]
      exact bound _ u.frame v
  refine ⟨Credits.check_issue (a := f) (b := t) _ hu ?_ (fun j => (step j).1) (fun j
    => (step j).2) lim, fun v => ?_⟩
  · intro v
    rw [congrFun first.1 v, congrFun first.2 v]
    exact initial v
  · obtain ⟨hl, ht⟩ := lim v (Fin.last a.waves)
    exact ⟨(Credits.issue_power _ _ _ _ hl).trans (congrArg _ (congrFun last.1 v)),
      (Credits.issue_time _ _ _ _ ht).trans (congrFun last.2 v)⟩

end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Surface.Local.Scenario
end

/- The credits and regional checks use one local rule across all initial shapes. -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Surface.Stage
open Finset
variable {F T V E X : Type} {r t : ℕ} [Fintype V] (s : Stage F r t T V E X)

open scoped Classical in
theorem collectors_timeCre (P H U : ℕ) (v : V) :
    U * Fintype.card {i : Fin (s.scene.cell v).stations.length //
      (Sphere.Layout.item s.scene.cell ⟨v, i⟩).label.role = .collector} ≤ s.timeCre P H U v := by
  have eq (r : Role) : (if r = .collector then 1 else 0) = r.collected 1 := by
    cases r <;> simp [Role.collected]
  refine le_trans (Nat.mul_le_mul_left U (le_of_eq ?_))
    ((Nat.le_add_right (U * s.tally P collectorUnit v) _).trans (Nat.le_add_right ..))
  rw [Fintype.card_subtype, card_eq_sum_ones, sum_filter]
  let l := (s.scene.cell v).stations
  let f := fun a : s.St => a.label.role.collected 1
  trans ∑ i : Fin l.length, f (l.get i)
  · exact sum_congr rfl fun i _ => eq _
  rw [← List.sum_ofFn]
  change (List.ofFn (f ∘ l.get)).sum = (l.map f).sum
  rw [← List.map_ofFn, List.ofFn_get]

open scoped Classical in
theorem collected_energyCre (P H g : ℕ) (v : V) :
    s.tally P Role.collected v ≤ s.energyCre P H g v := Nat.le_add_left ..

end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Surface.Stage

namespace MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input
open Assembly Coloring Routing.Private Sphere SphereScale Surface Surface.Local Geometry
variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
  {x y : Wire} {g ℓ D T b d p l : ℕ} [ExpChar F p] {W : ℝ}

section
variable (S : Scheme F)
local notation "Cfg" => design S g ℓ D b d p l

open scoped Classical in
/-- The value specified by `(Cfg).credits hF (localMenu S hK mobility k) k g ℓ D raw`. -/
abbrev credits (hK : Ready K ℓ D g (p ^ l) b d)
    (hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F)
    (mobility : B S.ℓ → B S.k → Bool) (k : ℕ)
    (raw : B ((Cfg).widthAt (panelQuery S g ℓ D b d p l k).width k (Cfg).waves)) :=
  (Cfg).credits hF (localMenu S hK mobility k) k g ℓ D raw
end

variable {S : Scheme F} (P : Input F x y S.h D T (d * b) g W) {z : S.format.obj}
  (A : P.HostChart S z) (sc : Scales g ℓ D T (p ^ l) b d) (hK : Ready K ℓ D g (p ^ l) b d)

local notation "Cfg" => design S g ℓ D b d p l
local notation "H" => SphereScale.energy ℓ D (d * b)

omit [Fintype F] [ExpChar F p] in
open scoped Classical in
theorem loc_eq (s t : P.Occupied → Shape (probes ℓ D) b d) :
    (P.localWorld A sc hK s).loc = (P.localWorld A sc hK t).loc := rfl

variable {hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F}
  {mobility : B S.ℓ → B S.k → Bool} {k : ℕ} {pres : S.Presentation z P.diagram}
  {placed : P.Placed pres A.coord (fun i => (A.tone (2 * D ^ 5 + 2) i).val)
    (fun v => mobility ((z v.1).2 v.2.1) v.2.2)}
  {ranks : P.LocalRanks} {init : initialChoices ℓ D b d ≤ 2 ^ k}

open scoped Classical in
theorem check_motion (s : P.Occupied → Shape (probes ℓ D) b d)
    (motion : (P.localWorld A sc hK s).CompleteRun hF (localMenu S hK mobility k) k
      (P.localCode A sc hK s placed ranks init)) (i : motion.I)
    {E M : P.Occupied → ℕ}
    (initial : ∀ v, clip (Cfg).waves (p ^ l * H) ((P.plant (P.kit sc hK) s).energyCre (p ^ l) H (2
      * g) v) ≤ E v ∧
      (P.plant (P.kit sc hK) s).timeCre (p ^ l) H (D ^ 5) v ≤ M v) :
    let q := motion.code i
    let vtx := fun v => credits S hK hF mobility k ((q.tape (A.coord v).1).2 (A.coord v).2)
    Credits.Check (P.localWorld A sc hK s).loc vtx E M ∧ ∀ v,
      (vtx v).power (Fin.last (Cfg).waves) = clip (Cfg).waves (p ^ l * H) (q.frame.stage.energyCre
        (p ^ l) H (2 * g) v) ∧
      (vtx v).time (Fin.last (Cfg).waves) = q.frame.stage.timeCre (p ^ l) H (D ^ 5) v :=
  Scenario.Certified.check (motion.good i) (motion.written i)
    (Nat.mul_pos sc.pos sc.Hpos) initial fun _ a v =>
      P.credit_limits (P.kit sc hK) s sc a.reach a.valid (Cfg).waves v

end MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input
end

/-
# The labels and the visible checks of the local expansion

The oracle below is used only inside scalar table entries. The
visible checks operate on a proposed blueprint and proposed credits.
-/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input.ReadyPanel
open Assembly Coloring Sphere SphereScale Surface Surface.Local Geometry

variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
    {x y : Wire} {g ℓ D T b d p l k r t n u f : ℕ} [ExpChar F p] {W : ℝ}
    {S : Scheme F} {P : Input F x y S.h D T (d * b) g W} {z : S.format.obj}
    {A : P.HostChart S z} {hK : Ready K ℓ D g (p ^ l) b d}
    {hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F}
    {mobility : B S.ℓ → B S.k → Bool} {U : LocalPrinter S g ℓ D b d p l k r t n u f}
    {status : (Print.Children.Header S.m S.d).obj} {pres : S.Presentation z P.diagram}

local notation "Cfg" => design S g ℓ D b d p l
local notation "PanelOK" => P.ReadyPanel A hK hF mobility k U status pres

open scoped Classical in
/-- Computes the book by the application `Journal P.Occupied k (Cfg).waves U.digits`. -/
abbrev Book (_h : PanelOK) := Journal P.Occupied k (Cfg).waves U.digits
open scoped Classical in
/-- The value specified by `U.Tag S g ℓ (Cfg).waves`. -/
abbrev Guess (_h : PanelOK) := U.Tag S g ℓ (Cfg).waves
open scoped Classical in
/-- Evaluates `(fun _ => 0, fun _ => 0)` at the input `_`. -/
def zeroShape (_h : PanelOK) : P.InitialShapes ℓ := fun _ => (fun _ => 0, fun _ => 0)

variable (h : P.ReadyPanel A hK hF mobility k U status pres) (sc : Scales g ℓ D T (p ^ l) b d)

open scoped Classical in
/-- Computes the printing by the application `U.advance (lastPage S sc z A.coord c) status
(c.close A.coord U.pad)`. -/
abbrev printing (c : h.Book) := U.advance (lastPage S sc z A.coord c) status (c.close A.coord U.pad)

open scoped Classical in
/-- The value specified by `(P.localWorld A sc hK h.zeroShape).loc`. -/
abbrev partition := (P.localWorld A sc hK h.zeroShape).loc

open scoped Classical in
/-- The admissible used in the `ReadyPanel` construction. -/
def admissible (c : h.Book) (a : P.Occupied → h.Guess) :=
  U.passes S A.coord (h.partition sc) (P.initialEnergyTokens ℓ (p ^ l) (Cfg).waves)
    P.initialTimeTokens
    (T / u) z (h.printing sc c) a

open scoped Classical in
/-- Computes the paths by the application `Candidate (h.admissible sc)`. -/
abbrev Paths := Candidate (h.admissible sc)

open scoped Classical in
/-- The actual of type `h.Guess`, constructed using `A.coord v`. -/
def actual (c : h.Book) (v : P.Occupied) : h.Guess :=
  let i := A.coord v
  (U.canonical S z (h.printing sc c) i.1 i.2,
    Input.credits S hK hF mobility k (((lastPage S sc z A.coord c) i.1).2 i.2))

open scoped Classical in
/-- The indexed operation `U.complete S A.coord (fun i => (c.2.val i).1)`. -/
abbrev geometry (c : h.Paths sc) := U.complete S A.coord (fun i => (c.2.val i).1)
open scoped Classical in
/-- Computes the data by the application `U.overlay S z (h.printing sc c.1) (h.geometry sc c)`. -/
abbrev data (c : h.Paths sc) := U.overlay S z (h.printing sc c.1) (h.geometry sc c)

end MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input.ReadyPanel
end

/- # Every true branch has an admissible certificate -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input.ReadyPanel
open Assembly Coloring Sphere SphereScale Surface Surface.Local Geometry

variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
    {x y : Wire} {g ℓ D T b d p l k r t n u f : ℕ} [ExpChar F p] {W : ℝ}
    {S : Scheme F} {P : Input F x y S.h D T (d * b) g W} {z : S.format.obj}
    {A : P.HostChart S z} {hK : Ready K ℓ D g (p ^ l) b d}
    {hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F}
    {mobility : B S.ℓ → B S.k → Bool} {U : LocalPrinter S g ℓ D b d p l k r t n u f}
    {status : (Print.Children.Header S.m S.d).obj} {pres : S.Presentation z P.diagram}

local notation "Cfg" => design S g ℓ D b d p l
variable {h : P.ReadyPanel A hK hF mobility k U status pres} {sc : Scales g ℓ D T (p ^ l) b d}
variable (E : Expansion sc h) (i : E.I)

open scoped Classical in
/-- Computes the credit at by the application `Input.credits S hK hF mobility k (((((E.motion
i.1).code i.2.1).tape (A.coord v).1).2 (A.coord v).2))`. -/
def creditAt (v : P.Occupied) :=
  Input.credits S hK hF mobility k (((((E.motion i.1).code i.2.1).tape (A.coord v).1).2 (A.coord
    v).2))

open scoped Classical in
/-- The value specified by `U.Checked pres ℓ A.coord (creditAt E i) (E.record i) (E.term i)
(E.shows i)`. -/
abbrev CertifiedTerm := U.Checked pres ℓ A.coord (creditAt E i) (E.record i) (E.term i) (E.shows i)

open scoped Classical in
theorem actual_eq : h.actual sc (E.select.write i) = fun v =>
    (U.canonical S z (E.record i) (A.coord v).1 (A.coord v).2, creditAt E i v) := by
  funext v
  unfold actual printing
  rw [←E.record_eq, E.written]
  rfl

open scoped Classical in
theorem accepted (M : CertifiedTerm E i) :
    h.admissible sc (E.select.write i) (h.actual sc (E.select.write i)) := by
  have eq := U.complete_of_vacant S A.coord (U.canonical S z (E.record i)) M.away
  let init := P.initialEnergyTokens ℓ (p ^ l) (Cfg).waves
  have hl := (P.check_motion A sc hK i.1 (E.motion i.1) i.2.1 (E := init) (M := P.initialTimeTokens)
    (fun v => ⟨P.initial_energy_fits (P.kit sc hK) i.1 _ v,
      P.initial_time_fits (P.kit sc hK) i.1 sc v⟩)).1
  rw [P.loc_eq A sc hK i.1 h.zeroShape] at hl
  unfold admissible printing
  rw [← E.record_eq, actual_eq E i]
  refine ⟨?_, hl, M.quota⟩
  change U.Valid S z (E.record i) (U.complete S A.coord (fun v =>
    U.canonical S z (E.record i) (A.coord v).1 (A.coord v).2))
  rw [eq]
  exact M.valid

variable (h sc)

open scoped Classical in
/-- Computes the weight by the application `journalWeight S z sc hK hF mobility U A.coord c
(A.coord v)`. -/
def weight (c : h.Book) (v : P.Occupied) := journalWeight S z sc hK hF mobility U A.coord c
    (A.coord v)

open scoped Classical in
/-- The value specified by `Geometry.factor (h.actual sc) (h.admissible sc) (h.weight sc) c`. -/
def factor (c : h.Paths sc) := Geometry.factor (h.actual sc) (h.admissible sc) (h.weight sc) c

end MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input.ReadyPanel
end

/- # Reading a diagram from the visible choice of geometry -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input.ReadyPanel
open Assembly Coloring Sphere SphereScale Surface Surface.Local Geometry

variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
    {x y : Wire} {g ℓ D T b d p l k r t n u f : ℕ} [ExpChar F p] {W : ℝ}
    {S : Scheme F} {P : Input F x y S.h D T (d * b) g W} {z : S.format.obj}
    {A : P.HostChart S z} {hK : Ready K ℓ D g (p ^ l) b d}
    {hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F}
    {mobility : B S.ℓ → B S.k → Bool} {U : LocalPrinter S g ℓ D b d p l k r t n u f}
    {status : (Print.Children.Header S.m S.d).obj} {pres : S.Presentation z P.diagram}

local notation "Cfg" => design S g ℓ D b d p l
variable {h : P.ReadyPanel A hK hF mobility k U status pres} {sc : Scales g ℓ D T (p ^ l) b d}

variable (h sc)

open scoped Classical in
theorem sameGraph (c : h.Book) (i : B S.m) : (lastPage S sc z A.coord c i).1 = A.graph i :=
  Copy.path_nav (design S g ℓ D b d p l) (panelTape S sc z (c.opening A.coord)) _ _ i

include sc in
open scoped Classical in
theorem ports_fit : g ≤ D ^ Layout.Sharing.allocation g ℓ := by
  have hpos : 0 < Layout.Sharing.allocation g ℓ := by unfold Layout.Sharing.allocation; omega
  exact ((Nat.le_mul_of_pos_left g (by decide)).trans sc.degree).trans (Nat.le_self_pow hpos.ne' _)

open scoped Classical in
/-- Computes the host graph by the application `U.graph h.parents (h.sameGraph sc c) (ports_fit
sc) (c.close A.coord U.pad)`. -/
abbrev hostGraph (c : h.Book) :=
  U.graph h.parents (h.sameGraph sc c) (ports_fit sc) (c.close A.coord U.pad)

open scoped Classical in
/-- Computes the board by the application `U.admitted S z (h.printing sc c.1) (h.geometry sc c)
c.2.property.1 (h.hostGraph sc c.1) pres h.directed`. -/
def board (c : h.Paths sc) : Geometry.Board (U.revised S) (h.data sc c) x y u :=
  U.admitted S z (h.printing sc c.1) (h.geometry sc c) c.2.property.1 (h.hostGraph sc c.1) pres
    h.directed

open scoped Classical in
/-- The value specified by `(h.board sc c).term`. -/
abbrev term (c : h.Paths sc) := (h.board sc c).term
open scoped Classical in
/-- The value specified by `(h.board sc c).shows`. -/
abbrev shows (c : h.Paths sc) := (h.board sc c).shows

open scoped Classical in
theorem retains (c : h.Paths sc) : Payload.Retains pres (h.shows sc c).pres U.split U.outer :=
  U.admitted_retains S z (h.printing sc c.1) (h.geometry sc c) c.2.property.1 (h.hostGraph sc c.1)
    pres h.directed

open scoped Classical in
theorem destination (c : h.Paths sc) (i : slots x ⊕ slots y) :
    ((h.shows sc c).pres.boundary i).val.1.1 =
      U.destination S (h.geometry sc c) (pres.boundary i).val.1.1 :=
  U.admitted_address S z (h.printing sc c.1) (h.geometry sc c) c.2.property.1 (h.hostGraph sc c.1)
    pres h.directed i

end MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input.ReadyPanel
end

/- # Projection of the common child graph to the original host -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Sphere.Print.Printer
open Assembly Coloring Rounds
open MatrixMultiplicationAllFields.MatrixExponent.Sphere.Layout (Alphabet Sharing Trie)
variable {F K : Type} [Field F] [Finite K] {S : Scheme F}
  {d ℓ M r t q D k n u j z T R g : ℕ} {x y : Wire} {W : ℝ} {P : Input F x y S.h D T R g W}
  (U : Printer F K (B S.k) S.m d S.h ℓ M r t q D k n u j z)
  {old : P.V ↪ B S.m} {data : U.rows.obj} {status : (Children.Header S.m d).obj}
  {nav : B S.m → B d → B S.m} (A : Children.Shows P.adj old (nav, status))
  (hdata : ∀ i, (data i).1 = nav i) (hg : g ≤ D ^ k) (c : U.selectors.obj)

open scoped Classical in
theorem graph_neighbors {v w : Host P.V M D k n}
    (hw : w ∈ (U.graph A hdata hg c).adj v) : (root w).1 ∈ insert (root v).1 (P.adj (root v).1) :=
  (Finset.mem_product.mp (Children.adj_near (U.graphTree A hg) (fun _ => Finset.mem_product.mpr
    ⟨Finset.mem_insert_self .., Finset.mem_univ _⟩) hw)).1

open scoped Classical in
private theorem dest_parent (mat : U.Matrix S) (v : S.Vtx) :
    ((U.split (U.destination S mat v).1).1, (U.destination S mat v).2.1) = (v.1, v.2.1) := by
  simp only [destination, centerAt, Equiv.apply_symm_apply]
  rfl

end MatrixMultiplicationAllFields.MatrixExponent.Sphere.Print.Printer
namespace MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input.ReadyPanel
open Assembly Coloring Sphere SphereScale Surface Surface.Local Geometry

variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
    {x y : Wire} {g ℓ D T b d p l k r t n u f : ℕ} [ExpChar F p] {W : ℝ}
    {S : Scheme F} {P : Input F x y S.h D T (d * b) g W} {z : S.format.obj}
    {A : P.HostChart S z} {hK : Ready K ℓ D g (p ^ l) b d}
    {hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F}
    {mobility : B S.ℓ → B S.k → Bool} {U : LocalPrinter S g ℓ D b d p l k r t n u f}
    {status : (Print.Children.Header S.m S.d).obj} {pres : S.Presentation z P.diagram}

local notation "Cfg" => design S g ℓ D b d p l
variable {h : P.ReadyPanel A hK hF mobility k U status pres} {sc : Scales g ℓ D T (p ^ l) b d}

variable (h sc)

local notation "L" => Layout.Sharing.allocation g ℓ
local notation "H" => Print.Host P.V (chunks ℓ D) D L n
local notation "shape" => Print.Children.Part (chunks ℓ D) D L n

open scoped Classical in
/-- The value specified by `(Print.root (show H from v)).1`. -/
def parent (c : h.Paths sc) (v : (h.term sc c).V) : P.V := (Print.root (show H from v)).1

open scoped Classical in
theorem parent_mem (c : h.Paths sc) {v w : (h.term sc c).V} (hw : w ∈ (h.term sc c).frame.N v) :
    h.parent sc c w ∈ insert (h.parent sc c v) (P.adj (h.parent sc c v)) :=
  U.graph_neighbors h.parents (h.sameGraph sc c.1) (ports_fit sc) (c.1.close A.coord U.pad) hw

open scoped Classical in
theorem common (c : h.Paths sc) : (h.term sc c).V = H ∧
    (h.term sc c).frame.N = (U.graphTree h.parents (ports_fit sc)).adj ∧
    (h.term sc c).frame.frozen = (U.graphTree h.parents (ports_fit sc)).fixed :=
  ⟨rfl, rfl, rfl⟩

include h sc in
open scoped Classical in
theorem per_parent : Fintype.card shape ≤ D ^ (terminalExponent g ℓ) := by
  have he := Fintype.card_congr (Print.Children.parts P.V (chunks ℓ D) D L n)
  rw [Fintype.card_prod] at he
  have hk := U.graph_cells h.parents (ports_fit sc) (σ:=ℓ) rfl
  rw [he, mul_comm (Fintype.card P.V)] at hk
  exact Nat.le_of_mul_le_mul_right hk (Fintype.card_pos_iff.mpr h.populated)

open scoped Classical in
private theorem parent_address (c : h.Paths sc) (i : slots x ⊕ slots y) :
    let v := (h.term sc c).frame.place (Packing.portEnd (h.term sc c).diagram i)
    let v₀ := Packing.portEnd P.diagram i
    (A.host (h.parent sc c v.1), cellIndex S.h v.2) =
      ((pres.vertex v₀).1, (pres.vertex v₀).2.1) := by
  intro v v₀
  let shown := h.shows sc c
  let target := Packing.portEnd (h.term sc c).diagram i
  have owner := (Payload.owner shown.pres i).trans (shown.vertex target)
  have placed := h.destination sc c i
  have old_owner := congrArg (U.destination S (h.geometry sc c)) (Payload.owner pres i)
  have routed := owner.symm.trans (placed.trans old_owner)
  have h₁ := (congrArg (fun w : U.Actors S => ((U.split w.1).1, w.2.1)) routed).trans
    (U.dest_parent (h.geometry sc c) (pres.vertex v₀))
  have hs := congrArg Prod.fst (Print.Children.host_split A.host U.slot v.1)
  exact (congrArg (fun i => (i, cellIndex S.h v.2)) hs.symm).trans h₁

open scoped Classical in
theorem parent_ext (c : h.Paths sc) (i : slots x ⊕ slots y) :
    let v := (h.term sc c).frame.place (Packing.portEnd (h.term sc c).diagram i)
    (h.parent sc c v.1, v.2) = P.place (Packing.portEnd P.diagram i) := by
  intro v
  let v₀ := Packing.portEnd P.diagram i
  have address := parent_address h sc c i
  have h₀ := h.placed.location (Packing.portEnd P.diagram i)
  rw [h.location] at h₀
  have eq := address.trans h₀
  have parent_eq : h.parent sc c v.1 = (P.place v₀).1 :=
    A.host.injective (Prod.mk.inj eq).1
  have cell_eq : v.2 = (P.place v₀).2 :=
    (cellIndex S.h).injective (Prod.mk.inj eq).2
  exact @Prod.ext _ _ (h.parent sc c v.1, v.2) (P.place v₀) parent_eq cell_eq

end MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input.ReadyPanel
end

/- # Universal arity bounds for the terms of the checked sum -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input.ReadyPanel
open Assembly Coloring Sphere SphereScale Surface Surface.Local Geometry

variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
    {x y : Wire} {g ℓ D T b d p l k r t n u f : ℕ} [ExpChar F p] {W : ℝ}
    {S : Scheme F} {P : Input F x y S.h D T (d * b) g W} {z : S.format.obj}
    {A : P.HostChart S z} {hK : Ready K ℓ D g (p ^ l) b d}
    {hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F}
    {mobility : B S.ℓ → B S.k → Bool} {U : LocalPrinter S g ℓ D b d p l k r t n u f}
    {status : (Print.Children.Header S.m S.d).obj} {pres : S.Presentation z P.diagram}

local notation "Cfg" => design S g ℓ D b d p l
variable {h : P.ReadyPanel A hK hF mobility k U status pres} {sc : Scales g ℓ D T (p ^ l) b d}
variable (h sc)

-- The proof uses only the widths of the finite codes, so keep their cardinalities opaque.
attribute [local irreducible] Print.indexBits

open scoped Classical in
theorem concentrated (c : h.Paths sc) :
    Concentrated P (h.term sc c) (Geometry.overhead g (terminalExponent g ℓ)) n ℓ := by
  have he := P.initial_energy_total sc (Cfg).waves
  have ht := P.initial_time_total (P.kit sc hK) h.zeroShape sc
  rw [Nat.cast_sum] at he ht
  exact U.approved_term (P := P) h.parents (h.sameGraph sc c.1) (ports_fit sc) (c.1.close A.coord
    U.pad)
    pres h.directed c.2.val c.2.property rfl he ht

open scoped Classical in
theorem trivalent (c : h.Paths sc) (i : (h.term sc c).V) : ((h.term sc c).frame.C i).card ≤ 3 :=
  U.graph_coreDegree h.parents (h.sameGraph sc c.1) (ports_fit sc) (c.1.close A.coord U.pad) i

end MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input.ReadyPanel
end

/- Visible proposal checks are independent of the motion history. -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input.ReadyPanel
open Assembly Coloring Sphere SphereScale Surface Surface.Local Geometry

variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
    {x y : Wire} {g ℓ D T b d p l k r t n u f : ℕ} [ExpChar F p] {W : ℝ}
    {S : Scheme F} {P : Input F x y S.h D T (d * b) g W} {z : S.format.obj}
    {A : P.HostChart S z} {hK : Ready K ℓ D g (p ^ l) b d}
    {hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F}
    {mobility : B S.ℓ → B S.k → Bool} {U : LocalPrinter S g ℓ D b d p l k r t n u f}
    {status : (Print.Children.Header S.m S.d).obj} {pres : S.Presentation z P.diagram}

local notation "Cfg" => design S g ℓ D b d p l
variable (h : P.ReadyPanel A hK hF mobility k U status pres)

open scoped Classical in
theorem admissible_eq (sc : Scales g ℓ D T (p ^ l) b d) (c c' : h.Book)
    (a : P.Occupied → h.Guess) : h.admissible sc c a ↔ h.admissible sc c' a := by
  have nav (t : h.Book) (i : B S.m) : (lastPage S sc z A.coord t i).1 = (z i).1 :=
    Copy.path_nav Cfg ..
  exact U.passes_advance S A.coord _ _ _ _ z a status _ _ (fun i => (nav c i).trans (nav c' i).symm)

include h in
open scoped Classical in
theorem vacantHeld : Print.Printer.vacantHeld S A.coord z := by
  intro i b hb l
  have no := mt (h.placed.live_iff (i, b)).mp hb
  have : IsEmpty ((S.decode ((z i).2 b)).Pin l) := ⟨fun j => no ⟨l, ⟨j⟩⟩⟩
  simp [Print.Printer.held, Scheme.extWidth]

open scoped Classical in
/-- All nonempty queries stay in the block and the prescribed neighborhood. -/
theorem query_near (sc : Scales g ℓ D T (p ^ l) b d) (c : h.Book) (v u' : P.Occupied)
    (i : U.Queries S (P.localWorld A sc hK h.zeroShape) v)
    (hi : U.query S (P.localWorld A sc hK h.zeroShape) A.coord (h.printing sc c) v i = some u') :
    (A.coord v).2 = (A.coord u').2 ∧
      Neighborhood.Reach A.graph ((Cfg).U + 1) (A.coord v).1 (A.coord u').1 := by
  rcases i with _ | i | i
  · have he : v = u' := Option.some.inj hi
    subst u'
    exact ⟨rfl, .refl ..⟩
  · let y := U.targetCell S A.coord (h.printing sc c) v i
    change Function.extend A.coord some (fun _ => none) y = some u' at hi
    have he : A.coord u' = y := by
      by_cases hv : y ∈ Set.range A.coord
      · obtain ⟨j, hj⟩ := hv
        rw [← hj, A.coord.injective.extend_apply] at hi
        exact (Option.some.inj hi) ▸ hj
      · rw [Function.extend_apply' _ _ _ hv] at hi
        cases hi
    rw [he]
    refine ⟨rfl, ?_⟩
    have nav : (fun j => (lastPage S sc z A.coord c j).1) = A.graph :=
      funext fun _ => Copy.path_nav Cfg ..
    have hn := U.nav_reach S (lastPage S sc z A.coord c) status (c.close A.coord U.pad)
      (U.split.symm ((A.coord v).1, i.1)) i.2
    rw [Equiv.apply_symm_apply, nav] at hn
    exact (Neighborhood.Reach.refl A.graph (Cfg).U (A.coord v).1).join hn
  · have he : i.val = u' := Option.some.inj hi
    subst u'
    exact (Finset.mem_filter.mp i.property).2

end MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input.ReadyPanel
end

/- Compile all proposal checks once, independently of the selectors. -/

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input.ReadyPanel
open Assembly Coloring Sphere SphereScale Surface Surface.Local Geometry

variable {F K : Type} [Field F] [Fintype F] [Field K] [Algebra K F]
    {x y : Wire} {g ℓ D T b d p l k r t n u f : ℕ} [ExpChar F p] {W : ℝ}
    {S : Scheme F} {P : Input F x y S.h D T (d * b) g W} {z : S.format.obj}
    {A : P.HostChart S z} {hK : Ready K ℓ D g (p ^ l) b d}
    {hF : room ℓ D g * (2 * depth ℓ D g (p ^ l) (d * b) + 1) < Fintype.card F}
    {mobility : B S.ℓ → B S.k → Bool} {U : LocalPrinter S g ℓ D b d p l k r t n u f}
    {status : (Print.Children.Header S.m S.d).obj} {pres : S.Presentation z P.diagram}

local notation "Cfg" => design S g ℓ D b d p l
variable (h : P.ReadyPanel A hK hF mobility k U status pres)
  (sc : Scales g ℓ D T (p ^ l) b d)

local notation "world" => P.localWorld A sc hK h.zeroShape

open scoped Classical in
/-- Uses `U.checkPins S world g ℓ v` as the representation. -/
abbrev checkPins (v : P.Occupied) := U.checkPins S world g ℓ v

open scoped Classical in
/-- The value specified by `U.checkInputs S world A.coord (h.printing sc c)
(P.initialEnergyTokens ℓ (p ^ l) (Cfg).waves) P.initialTimeTokens z a v`. -/
abbrev checkInputs (c : h.Book) (a : P.Occupied → h.Guess) (v : P.Occupied) :
    h.checkPins sc v → Bool :=
  U.checkInputs S world A.coord (h.printing sc c) (P.initialEnergyTokens ℓ (p ^ l) (Cfg).waves)
    P.initialTimeTokens z a v

open scoped Classical in
/-- Any reference selector word gives the same tests for every proposed history. -/
theorem admissible_binary (c₀ : h.Book) :
    let b' := U.checkWidth S g ℓ Cfg
    ∃ test : ∀ v, BitFormula (h.checkPins sc v),
      (∀ v, (test v).cost ≤ (3 * b' + 2) * 2 ^ b' + 1) ∧
      ∀ (c : h.Book) (a : P.Occupied → h.Guess),
        h.admissible sc c a ↔ ∀ v, (test v).eval (h.checkInputs sc c₀ a v) = true := by
  obtain ⟨test, small, works⟩ :=
    U.passes_binary S world (g := g) (σ := ℓ) A.coord (h.printing sc c₀) (T / u)
  exact ⟨test, small, fun c a => (h.admissible_eq sc c c₀ a).trans (works _ _ _ h.vacantHeld a)⟩

end MatrixMultiplicationAllFields.MatrixExponent.Rounds.Input.ReadyPanel
end
