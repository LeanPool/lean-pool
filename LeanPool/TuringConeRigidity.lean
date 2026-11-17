/-
Copyright (c) 2026 Bjørn Kjos-Hanssen, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen, OpenAI
-/


module

public import LeanPool.TuringConeRigidity.TuringTwoConeMain

/-!
# Pairwise rigidity of principal upper cones of the Turing degrees

Source: url:https://github.com/bjoernkjoshanssen/tt-auto/tree/99621af8867a5d272b16eb1454a15f59fb43e9ea
Authors: Bjørn Kjos-Hanssen, OpenAI
Status: verified
Main declarations: `OAI.TuringRigidity.TwoConeMain.cones_orderIso_iff`,
  `OAI.TuringRigidity.TwoConeMain.cone_iso_apply_val`
Tags: turing-degrees, computability, rigidity, forcing, baire-category
MSC: 03D28, 03B35
-/


/-
Turing cone rigidity and truth-table degree formalization

This repository includes OpenAI's DegreeRigidity development, distributed
under Apache-2.0 at:
https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Computability/DegreeRigidity

Before the Palomar module port, that upstream directory and the inherited
OAI/Computability/DegreeRigidity directory at local commit
b934186a456258a055de59689e75b1d503f3c71f had identical Git tree hash
d979299cdac872372c8c2893b287ebf89fbb9258. Existing attribution is retained.

The cone-specific additions under RequestProject/TuringCone*.lean were produced
with ChatGPT 6 Pro under Bjorn Kjos-Hanssen's mathematical direction. The
original Aristotle (Harmonic) credit for earlier work is retained in README.md.

Palomar compatibility modifications include module headers/public interfaces,
pinned build dependencies, independent statement wrappers, metadata, and
verification tooling. Explicit Encodable instances for OracleCode and
SentenceForm replace deriving-handler references to private helper types.
Effective/EncodableTree.lean adapts Kyle Miller's Apache-2.0 implementation in
Mathlib.Tactic.DeriveEncodable and retains the original copyright and authorship
notice. Decoding round-trip laws are proved in Lean.

Submission tooling follows Palomar's public documentation and template:
https://github.com/PalomarRegistry/PalomarTemplate

Apache-2.0 applies to this repository's code. External mathematical papers and
dependencies retain their own licenses. No endorsement by upstream authors,
OpenAI, Harmonic, Lean, Mathlib, or the Palomar Registry is implied.
-/

/-!
## Mathematical background and attribution

The cone-specific argument is by Bjørn Kjos-Hanssen with ChatGPT 6 Pro. Its
persistence and generic-representation methods build on Theodore A. Slaman and
W. Hugh Woodin, *Definability in Degree Structures* (2005 manuscript),
https://math.berkeley.edu/~slaman/talks/sw.pdf, and OpenAI's DegreeRigidity
formalization. The pairwise cone result is an extension developed in the
upstream repository, rather than a theorem quoted verbatim from that manuscript.
-/
