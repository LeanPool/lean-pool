/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Semantics.Batch001
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC2PhiBelowLeaf30000`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30001`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30002`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30003`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30010`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30011`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30012`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30013`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30020`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30021`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30022`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30023`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30030`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30031`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30032`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30033`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30100`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30101`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30102`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30103`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30110`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30111`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30112`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30113`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30120`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30121`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30122`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30123`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30130`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30131`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30132`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30133`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30200`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30201`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30202`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30203`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30210`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30211`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30212`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30213`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30220`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30221`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30222`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30223`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30230`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30231`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30232`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30233`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30300`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30301`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30302`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30303`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30310`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30311`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30312`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30313`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30320`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30321`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30322`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30323`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30330`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30331`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30332`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf30333`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31000`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31001`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31002`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31003`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31010`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31011`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31012`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31013`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31020`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31021`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31022`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31023`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31030`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31031`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31032`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31033`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf3110`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf3111`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31120`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31121`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31122`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31123`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf3113`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31200`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31201`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31202`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31203`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31210`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31211`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31212`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31213`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31220`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31221`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31222`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31223`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31230`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31231`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31232`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31233`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31300`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31301`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31302`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31303`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31310`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31311`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31312`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31313`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31320`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31321`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31322`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31323`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31330`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31331`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31332`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf31333`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32000`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32001`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32002`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32003`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32010`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32011`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32012`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32013`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32020`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32021`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32022`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32023`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32030`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32031`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32032`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32033`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32100`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32101`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32102`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32103`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32110`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32111`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32112`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32113`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32120`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32121`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32122`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32123`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32130`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32131`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32132`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32133`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32200`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32201`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32202`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32203`.
* `KernelOnly.PartE.E24KC2PhiBelowLeaf32210`.
* `KernelOnly.PartE.E24KC4BatchPhiAboveF9C1LLL0006`.
* `KernelOnly.PartE.E24KC4BatchPhiAboveF9C1LLRLL0009`.
-/

@[expose] public section

noncomputable section

namespace GerverSofa.PartE.CoverCertificate7eaf46f70e

private abbrev cellRoot : AngleCell :=
  (childLL (childLL (childLH (childLL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate7eaf46f70e

namespace GerverSofa.PartE.CoverCertificate3307b34685

private abbrev cellRoot : AngleCell :=
  (childLH (childLL (childLH (childLL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate3307b34685

namespace GerverSofa.PartE.CoverCertificatea0fa380a93

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childLH (childLL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatea0fa380a93

namespace GerverSofa.PartE.CoverCertificate5f1fd442d3

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childLH (childLL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate5f1fd442d3

namespace GerverSofa.PartE.CoverCertificated6f9cbc5d6

private abbrev cellRoot : AngleCell :=
  (childHL (childLH (childLH (childLL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificated6f9cbc5d6

namespace GerverSofa.PartE.CoverCertificatecaa270a0ec

private abbrev cellRoot : AngleCell :=
  (childLL (childHL (childLH (childLL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatecaa270a0ec

namespace GerverSofa.PartE.CoverCertificate0254ae442a

private abbrev cellRoot : AngleCell :=
  (childLH (childHL (childLH (childLL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate0254ae442a

namespace GerverSofa.PartE.CoverCertificate44197a14bc

private abbrev cellRoot : AngleCell :=
  (childHL (childHL (childLH (childLL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate44197a14bc

namespace GerverSofa.PartE.CoverCertificateaa4818b079

private abbrev cellRoot : AngleCell :=
  (childHH (childHL (childLH (childLL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificateaa4818b079

namespace GerverSofa.PartE.CoverCertificateade660b261

private abbrev cellRoot : AngleCell :=
  (childLL (childHH (childLH (childLL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificateade660b261

namespace GerverSofa.PartE.CoverCertificateead4291aaf

private abbrev cellRoot : AngleCell :=
  (childHL (childHH (childLH (childLL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificateead4291aaf

namespace GerverSofa.PartE.CoverCertificate76deff8421

private abbrev cellRoot : AngleCell :=
  (childHH (childHH (childLH (childLL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate76deff8421

namespace GerverSofa.PartE.CoverCertificatef9c3dd592d

private abbrev cellRoot : AngleCell :=
  (childLH (childLH (childHL (childLL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatef9c3dd592d

namespace GerverSofa.PartE.CoverCertificate55e26a37bf

private abbrev cellRoot : AngleCell :=
  (childHH (childLH (childHL (childLL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate55e26a37bf

namespace GerverSofa.PartE.CoverCertificated546542719

private abbrev cellRoot : AngleCell :=
  (childLH (childHH (childHL (childLL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificated546542719

namespace GerverSofa.PartE.CoverCertificate09704881ea

private abbrev cellRoot : AngleCell :=
  (childHH (childHH (childHL (childLL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate09704881ea

namespace GerverSofa.PartE.CoverCertificate89f8bf996f

private abbrev cellRoot : AngleCell :=
  (childLL (childLL (childHH (childLL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate89f8bf996f

namespace GerverSofa.PartE.CoverCertificate072d32638e

private abbrev cellRoot : AngleCell :=
  (childLH (childLL (childHH (childLL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate072d32638e

namespace GerverSofa.PartE.CoverCertificate5c3ff9507c

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childHH (childLL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate5c3ff9507c

namespace GerverSofa.PartE.CoverCertificate0e6fd3d794

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childHH (childLL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate0e6fd3d794

namespace GerverSofa.PartE.CoverCertificate1d8d5ed6e8

private abbrev cellRoot : AngleCell :=
  (childLL (childLH (childHH (childLL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate1d8d5ed6e8

namespace GerverSofa.PartE.CoverCertificatead0c92c0d4

private abbrev cellRoot : AngleCell :=
  (childLH (childLH (childHH (childLL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatead0c92c0d4

namespace GerverSofa.PartE.CoverCertificate4e6964ff18

private abbrev cellRoot : AngleCell :=
  (childHL (childLH (childHH (childLL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate4e6964ff18

namespace GerverSofa.PartE.CoverCertificate14906b8c69

private abbrev cellRoot : AngleCell :=
  (childHH (childLH (childHH (childLL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate14906b8c69

namespace GerverSofa.PartE.CoverCertificate4614f242b3

private abbrev cellRoot : AngleCell :=
  (childLL (childHL (childHH (childLL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate4614f242b3

namespace GerverSofa.PartE.CoverCertificatef3c458cae3

private abbrev cellRoot : AngleCell :=
  (childLH (childHL (childHH (childLL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatef3c458cae3

namespace GerverSofa.PartE.CoverCertificateeb6553a302

private abbrev cellRoot : AngleCell :=
  (childHL (childHL (childHH (childLL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificateeb6553a302

namespace GerverSofa.PartE.CoverCertificatefa7152b230

private abbrev cellRoot : AngleCell :=
  (childHH (childHL (childHH (childLL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatefa7152b230

namespace GerverSofa.PartE.CoverCertificate8afa5ed490

private abbrev cellRoot : AngleCell :=
  (childLL (childHH (childHH (childLL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3

end GerverSofa.PartE.CoverCertificate8afa5ed490

namespace GerverSofa.PartE.CoverCertificated9debec79d

private abbrev cellRoot : AngleCell :=
  (childLH (childHH (childHH (childLL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2

end GerverSofa.PartE.CoverCertificated9debec79d

namespace GerverSofa.PartE.CoverCertificate67d4072331

private abbrev cellRoot : AngleCell :=
  (childHL (childHH (childHH (childLL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3

end GerverSofa.PartE.CoverCertificate67d4072331

namespace GerverSofa.PartE.CoverCertificatebed93df298

private abbrev cellRoot : AngleCell :=
  (childHH (childHH (childHH (childLL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3

end GerverSofa.PartE.CoverCertificatebed93df298

namespace GerverSofa.PartE.CoverCertificatefd2c3f3274

private abbrev cellRoot : AngleCell :=
  (childLL (childLL (childHL (childLH (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatefd2c3f3274

namespace GerverSofa.PartE.CoverCertificate1ffa851843

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childHL (childLH (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate1ffa851843

namespace GerverSofa.PartE.CoverCertificated8ac44ac8f

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childHL (childLH (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificated8ac44ac8f

namespace GerverSofa.PartE.CoverCertificate3caeb3dd1d

private abbrev cellRoot : AngleCell :=
  (childLL (childHL (childHL (childLH (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate3caeb3dd1d

namespace GerverSofa.PartE.CoverCertificate3195681328

private abbrev cellRoot : AngleCell :=
  (childLH (childHL (childHL (childLH (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate3195681328

namespace GerverSofa.PartE.CoverCertificate24d91bb18c

private abbrev cellRoot : AngleCell :=
  (childHL (childHL (childHL (childLH (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate24d91bb18c

namespace GerverSofa.PartE.CoverCertificatea5eff6d169

private abbrev cellRoot : AngleCell :=
  (childHH (childHL (childHL (childLH (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatea5eff6d169

namespace GerverSofa.PartE.CoverCertificateabfc719760

private abbrev cellRoot : AngleCell :=
  (childHL (childHH (childHL (childLH (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificateabfc719760

namespace GerverSofa.PartE.CoverCertificate0a514de912

private abbrev cellRoot : AngleCell :=
  (childLH (childLH (childLL (childHL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate0a514de912

namespace GerverSofa.PartE.CoverCertificate7ed638f543

private abbrev cellRoot : AngleCell :=
  (childHH (childLH (childLL (childHL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate7ed638f543

namespace GerverSofa.PartE.CoverCertificatebdb1950cb6

private abbrev cellRoot : AngleCell :=
  (childLH (childHH (childLL (childHL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatebdb1950cb6

namespace GerverSofa.PartE.CoverCertificate5fb7a54ee1

private abbrev cellRoot : AngleCell :=
  (childHH (childHH (childLL (childHL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate5fb7a54ee1

namespace GerverSofa.PartE.CoverCertificated58a87e9b8

private abbrev cellRoot : AngleCell :=
  (childLL (childLL (childLH (childHL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificated58a87e9b8

namespace GerverSofa.PartE.CoverCertificate3ddf17b582

private abbrev cellRoot : AngleCell :=
  (childLH (childLL (childLH (childHL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate3ddf17b582

namespace GerverSofa.PartE.CoverCertificated26b7e0a55

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childLH (childHL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificated26b7e0a55

namespace GerverSofa.PartE.CoverCertificatea04fbf8169

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childLH (childHL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatea04fbf8169

namespace GerverSofa.PartE.CoverCertificate3ba43c403b

private abbrev cellRoot : AngleCell :=
  (childLL (childLH (childLH (childHL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3

end GerverSofa.PartE.CoverCertificate3ba43c403b

namespace GerverSofa.PartE.CoverCertificate1430173dea

private abbrev cellRoot : AngleCell :=
  (childLH (childLH (childLH (childHL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3

end GerverSofa.PartE.CoverCertificate1430173dea

namespace GerverSofa.PartE.CoverCertificate2756e7c1ab

private abbrev cellRoot : AngleCell :=
  (childHL (childLH (childLH (childHL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3

end GerverSofa.PartE.CoverCertificate2756e7c1ab

namespace GerverSofa.PartE.CoverCertificate8e43edbf8f

private abbrev cellRoot : AngleCell :=
  (childHH (childLH (childLH (childHL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3

end GerverSofa.PartE.CoverCertificate8e43edbf8f

namespace GerverSofa.PartE.CoverCertificated1acdb7cc1

private abbrev cellRoot : AngleCell :=
  (childLL (childHL (childLH (childHL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificated1acdb7cc1

namespace GerverSofa.PartE.CoverCertificated9d4fcb914

private abbrev cellRoot : AngleCell :=
  (childLH (childHL (childLH (childHL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificated9d4fcb914

namespace GerverSofa.PartE.CoverCertificate18d654774a

private abbrev cellRoot : AngleCell :=
  (childHL (childHL (childLH (childHL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate18d654774a

namespace GerverSofa.PartE.CoverCertificate3c1ddcbe4a

private abbrev cellRoot : AngleCell :=
  (childHH (childHL (childLH (childHL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate3c1ddcbe4a

namespace GerverSofa.PartE.CoverCertificatecaa9842c01

private abbrev cellRoot : AngleCell :=
  (childLL (childHH (childLH (childHL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3

end GerverSofa.PartE.CoverCertificatecaa9842c01

namespace GerverSofa.PartE.CoverCertificate8a64f55483

private abbrev cellRoot : AngleCell :=
  (childLH (childHH (childLH (childHL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3

end GerverSofa.PartE.CoverCertificate8a64f55483

namespace GerverSofa.PartE.CoverCertificatea45749320c

private abbrev cellRoot : AngleCell :=
  (childHL (childHH (childLH (childHL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3

end GerverSofa.PartE.CoverCertificatea45749320c

namespace GerverSofa.PartE.CoverCertificate96200cdbc3

private abbrev cellRoot : AngleCell :=
  (childHH (childHH (childLH (childHL (childHH (e24PhiBelowRoot))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell20 : AngleCell :=
  childLL cell2


private abbrev cell21 : AngleCell :=
  childLH cell2


private abbrev cell22 : AngleCell :=
  childHL cell2


private abbrev cell23 : AngleCell :=
  childHH cell2


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3

end GerverSofa.PartE.CoverCertificate96200cdbc3

namespace GerverSofa.PartE.CoverCertificate1e0715601d

private abbrev cellRoot : AngleCell :=
  (childLH (childLH (childLH (childLL (childLL (childLH (childLH (e24PhiAboveRoot))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1

end GerverSofa.PartE.CoverCertificate1e0715601d

namespace GerverSofa.PartE.CoverCertificate645c2a2fa6

private abbrev cellRoot : AngleCell :=
  (childLL (childLL (childLL (childLH (childLL (childLH (childLH (e24PhiAboveRoot))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell010 : AngleCell :=
  childLL cell01


private abbrev cell011 : AngleCell :=
  childLH cell01


private abbrev cell012 : AngleCell :=
  childHL cell01


private abbrev cell013 : AngleCell :=
  childHH cell01


private abbrev cell100 : AngleCell :=
  childLL cell10


private abbrev cell101 : AngleCell :=
  childLH cell10


private abbrev cell102 : AngleCell :=
  childHL cell10


private abbrev cell103 : AngleCell :=
  childHH cell10


private abbrev cell110 : AngleCell :=
  childLL cell11


private abbrev cell111 : AngleCell :=
  childLH cell11


private abbrev cell112 : AngleCell :=
  childHL cell11


private abbrev cell113 : AngleCell :=
  childHH cell11

end GerverSofa.PartE.CoverCertificate645c2a2fa6

namespace GerverSofa.PartE.CoverCertificate22a5b25f41

private abbrev cellRoot : AngleCell :=
  (childLH (childLL (childLL (childLH (childLL (childLH (childLH (e24PhiAboveRoot))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell000 : AngleCell :=
  childLL cell00


private abbrev cell001 : AngleCell :=
  childLH cell00


private abbrev cell002 : AngleCell :=
  childHL cell00


private abbrev cell003 : AngleCell :=
  childHH cell00


private abbrev cell010 : AngleCell :=
  childLL cell01


private abbrev cell011 : AngleCell :=
  childLH cell01


private abbrev cell012 : AngleCell :=
  childHL cell01


private abbrev cell013 : AngleCell :=
  childHH cell01


private abbrev cell100 : AngleCell :=
  childLL cell10


private abbrev cell101 : AngleCell :=
  childLH cell10


private abbrev cell102 : AngleCell :=
  childHL cell10


private abbrev cell103 : AngleCell :=
  childHH cell10


private abbrev cell110 : AngleCell :=
  childLL cell11


private abbrev cell111 : AngleCell :=
  childLH cell11


private abbrev cell112 : AngleCell :=
  childHL cell11


private abbrev cell113 : AngleCell :=
  childHH cell11

end GerverSofa.PartE.CoverCertificate22a5b25f41

namespace GerverSofa.PartE.CoverCertificate052935fbc6

private abbrev cellRoot : AngleCell :=
  (childLL (childLH (childLL (childLH (childLL (childLH (childLH (e24PhiAboveRoot))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell000 : AngleCell :=
  childLL cell00


private abbrev cell001 : AngleCell :=
  childLH cell00


private abbrev cell002 : AngleCell :=
  childHL cell00


private abbrev cell003 : AngleCell :=
  childHH cell00


private abbrev cell010 : AngleCell :=
  childLL cell01


private abbrev cell011 : AngleCell :=
  childLH cell01


private abbrev cell012 : AngleCell :=
  childHL cell01


private abbrev cell013 : AngleCell :=
  childHH cell01


private abbrev cell100 : AngleCell :=
  childLL cell10


private abbrev cell101 : AngleCell :=
  childLH cell10


private abbrev cell102 : AngleCell :=
  childHL cell10


private abbrev cell103 : AngleCell :=
  childHH cell10


private abbrev cell110 : AngleCell :=
  childLL cell11


private abbrev cell111 : AngleCell :=
  childLH cell11


private abbrev cell112 : AngleCell :=
  childHL cell11


private abbrev cell113 : AngleCell :=
  childHH cell11


private abbrev cell1010 : AngleCell :=
  childLL cell101


private abbrev cell1011 : AngleCell :=
  childLH cell101


private abbrev cell1012 : AngleCell :=
  childHL cell101


private abbrev cell1013 : AngleCell :=
  childHH cell101


private abbrev cell1100 : AngleCell :=
  childLL cell110


private abbrev cell1101 : AngleCell :=
  childLH cell110


private abbrev cell1102 : AngleCell :=
  childHL cell110


private abbrev cell1103 : AngleCell :=
  childHH cell110


private abbrev cell1110 : AngleCell :=
  childLL cell111


private abbrev cell1111 : AngleCell :=
  childLH cell111


private abbrev cell1112 : AngleCell :=
  childHL cell111


private abbrev cell1113 : AngleCell :=
  childHH cell111

end GerverSofa.PartE.CoverCertificate052935fbc6

namespace GerverSofa.PartE.CoverCertificateda1b0b5031

private abbrev cellRoot : AngleCell :=
  (childLH (childLH (childLL (childLH (childLL (childLH (childLH (e24PhiAboveRoot))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot


private abbrev cell00 : AngleCell :=
  childLL cell0


private abbrev cell01 : AngleCell :=
  childLH cell0


private abbrev cell02 : AngleCell :=
  childHL cell0


private abbrev cell03 : AngleCell :=
  childHH cell0


private abbrev cell10 : AngleCell :=
  childLL cell1


private abbrev cell11 : AngleCell :=
  childLH cell1


private abbrev cell12 : AngleCell :=
  childHL cell1


private abbrev cell13 : AngleCell :=
  childHH cell1


private abbrev cell30 : AngleCell :=
  childLL cell3


private abbrev cell31 : AngleCell :=
  childLH cell3


private abbrev cell32 : AngleCell :=
  childHL cell3


private abbrev cell33 : AngleCell :=
  childHH cell3


private abbrev cell000 : AngleCell :=
  childLL cell00


private abbrev cell001 : AngleCell :=
  childLH cell00


private abbrev cell002 : AngleCell :=
  childHL cell00


private abbrev cell003 : AngleCell :=
  childHH cell00


private abbrev cell010 : AngleCell :=
  childLL cell01


private abbrev cell011 : AngleCell :=
  childLH cell01


private abbrev cell012 : AngleCell :=
  childHL cell01


private abbrev cell013 : AngleCell :=
  childHH cell01


private abbrev cell100 : AngleCell :=
  childLL cell10


private abbrev cell101 : AngleCell :=
  childLH cell10


private abbrev cell102 : AngleCell :=
  childHL cell10


private abbrev cell103 : AngleCell :=
  childHH cell10


private abbrev cell110 : AngleCell :=
  childLL cell11


private abbrev cell111 : AngleCell :=
  childLH cell11


private abbrev cell112 : AngleCell :=
  childHL cell11


private abbrev cell113 : AngleCell :=
  childHH cell11


private abbrev cell0000 : AngleCell :=
  childLL cell000


private abbrev cell0001 : AngleCell :=
  childLH cell000


private abbrev cell0002 : AngleCell :=
  childHL cell000


private abbrev cell0003 : AngleCell :=
  childHH cell000


private abbrev cell0010 : AngleCell :=
  childLL cell001


private abbrev cell0011 : AngleCell :=
  childLH cell001


private abbrev cell0012 : AngleCell :=
  childHL cell001


private abbrev cell0013 : AngleCell :=
  childHH cell001


private abbrev cell0100 : AngleCell :=
  childLL cell010


private abbrev cell0101 : AngleCell :=
  childLH cell010


private abbrev cell0102 : AngleCell :=
  childHL cell010


private abbrev cell0103 : AngleCell :=
  childHH cell010


private abbrev cell0110 : AngleCell :=
  childLL cell011


private abbrev cell0111 : AngleCell :=
  childLH cell011


private abbrev cell0112 : AngleCell :=
  childHL cell011


private abbrev cell0113 : AngleCell :=
  childHH cell011


private abbrev cell1000 : AngleCell :=
  childLL cell100


private abbrev cell1001 : AngleCell :=
  childLH cell100


private abbrev cell1002 : AngleCell :=
  childHL cell100


private abbrev cell1003 : AngleCell :=
  childHH cell100


private abbrev cell1010 : AngleCell :=
  childLL cell101


private abbrev cell1011 : AngleCell :=
  childLH cell101


private abbrev cell1012 : AngleCell :=
  childHL cell101


private abbrev cell1013 : AngleCell :=
  childHH cell101


private abbrev cell1100 : AngleCell :=
  childLL cell110


private abbrev cell1101 : AngleCell :=
  childLH cell110


private abbrev cell1102 : AngleCell :=
  childHL cell110


private abbrev cell1103 : AngleCell :=
  childHH cell110


private abbrev cell1110 : AngleCell :=
  childLL cell111


private abbrev cell1111 : AngleCell :=
  childLH cell111


private abbrev cell1112 : AngleCell :=
  childHL cell111


private abbrev cell1113 : AngleCell :=
  childHH cell111


private abbrev cell11110 : AngleCell :=
  childLL cell1111


private abbrev cell11111 : AngleCell :=
  childLH cell1111


private abbrev cell11112 : AngleCell :=
  childHL cell1111


private abbrev cell11113 : AngleCell :=
  childHH cell1111

end GerverSofa.PartE.CoverCertificateda1b0b5031

namespace GerverSofa.PartE.CoverCertificate87253a3a53

private abbrev cellRoot : AngleCell :=
  (childHL (childLH (childLL (childLH (childLL (childLH (childLH (e24PhiAboveRoot))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate87253a3a53

namespace GerverSofa.PartE.CoverCertificate3f791a2e61

private abbrev cellRoot : AngleCell :=
  (childHH (childLH (childLL (childLH (childLL (childLH (childLH (e24PhiAboveRoot))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate3f791a2e61

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30000 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells68c1109b36

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3000` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3000 : AngleCell :=
  childLL (childLL (childLL (childHH e24PhiBelowRoot)))

end CertificateCells68c1109b36

open CertificateCells68c1109b36
theorem e24KC2PhiBelowLeaf30000 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3000) = true := by
  have h : ((childLL phiBelowCell3000)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL phiBelowCell3000) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30001 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells3eb225f04c

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3000` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3000 : AngleCell :=
  childLL (childLL (childLL (childHH e24PhiBelowRoot)))

end CertificateCells3eb225f04c

open CertificateCells3eb225f04c
theorem e24KC2PhiBelowLeaf30001 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3000) = true := by
  have h : ((childLH phiBelowCell3000)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH phiBelowCell3000) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30002 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells50ca4e3af4

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3000` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3000 : AngleCell :=
  childLL (childLL (childLL (childHH e24PhiBelowRoot)))

end CertificateCells50ca4e3af4

open CertificateCells50ca4e3af4
theorem e24KC2PhiBelowLeaf30002 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3000) = true := by
  have h : ((childHL phiBelowCell3000)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL phiBelowCell3000) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30003 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsfa60677f23

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3000` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3000 : AngleCell :=
  childLL (childLL (childLL (childHH e24PhiBelowRoot)))

end CertificateCellsfa60677f23

open CertificateCellsfa60677f23
theorem e24KC2PhiBelowLeaf30003 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3000) = true := by
  have h : ((childHH phiBelowCell3000)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH phiBelowCell3000) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30010 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsadacfb8de1

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3001` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3001 : AngleCell :=
  childLH (childLL (childLL (childHH e24PhiBelowRoot)))

end CertificateCellsadacfb8de1

open CertificateCellsadacfb8de1
theorem e24KC2PhiBelowLeaf30010 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3001) = true := by
  have h : ((childLL phiBelowCell3001)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL phiBelowCell3001) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30011 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells2e1d52b748

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3001` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3001 : AngleCell :=
  childLH (childLL (childLL (childHH e24PhiBelowRoot)))

end CertificateCells2e1d52b748

open CertificateCells2e1d52b748
theorem e24KC2PhiBelowLeaf30011 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3001) = true := by
  have h : ((childLH phiBelowCell3001)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH phiBelowCell3001) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30012 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells7e7c37fb1b

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3001` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3001 : AngleCell :=
  childLH (childLL (childLL (childHH e24PhiBelowRoot)))

end CertificateCells7e7c37fb1b

open CertificateCells7e7c37fb1b
theorem e24KC2PhiBelowLeaf30012 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3001) = true := by
  have h : ((childHL phiBelowCell3001)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL phiBelowCell3001) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30013 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa8cebe99f5

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3001` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3001 : AngleCell :=
  childLH (childLL (childLL (childHH e24PhiBelowRoot)))

end CertificateCellsa8cebe99f5

open CertificateCellsa8cebe99f5
theorem e24KC2PhiBelowLeaf30013 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3001) = true := by
  have h : ((childHH phiBelowCell3001)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH phiBelowCell3001) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30020 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells7730b0e091

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3002` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3002 : AngleCell :=
  childHL (childLL (childLL (childHH e24PhiBelowRoot)))

end CertificateCells7730b0e091

open CertificateCells7730b0e091
theorem e24KC2PhiBelowLeaf30020 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3002) = true := by
  have h : ((childLL phiBelowCell3002)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL phiBelowCell3002) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30021 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellse8a24af0c4

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3002` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3002 : AngleCell :=
  childHL (childLL (childLL (childHH e24PhiBelowRoot)))

end CertificateCellse8a24af0c4

open CertificateCellse8a24af0c4
theorem e24KC2PhiBelowLeaf30021 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3002) = true := by
  have h : ((childLH phiBelowCell3002)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH phiBelowCell3002) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30022 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellse2e04a6320

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3002` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3002 : AngleCell :=
  childHL (childLL (childLL (childHH e24PhiBelowRoot)))

end CertificateCellse2e04a6320

open CertificateCellse2e04a6320
theorem e24KC2PhiBelowLeaf30022 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3002) = true := by
  have h : ((childHL phiBelowCell3002)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL phiBelowCell3002) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30023 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells1fb6bd85e4

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3002` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3002 : AngleCell :=
  childHL (childLL (childLL (childHH e24PhiBelowRoot)))

end CertificateCells1fb6bd85e4

open CertificateCells1fb6bd85e4
theorem e24KC2PhiBelowLeaf30023 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3002) = true := by
  have h : ((childHH phiBelowCell3002)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH phiBelowCell3002) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30030 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsf0432d10ef

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3003` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3003 : AngleCell :=
  childHH (childLL (childLL (childHH e24PhiBelowRoot)))

end CertificateCellsf0432d10ef

open CertificateCellsf0432d10ef
theorem e24KC2PhiBelowLeaf30030 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3003) = true := by
  have h : ((childLL phiBelowCell3003)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL phiBelowCell3003) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30031 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells283f971137

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3003` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3003 : AngleCell :=
  childHH (childLL (childLL (childHH e24PhiBelowRoot)))

end CertificateCells283f971137

open CertificateCells283f971137
theorem e24KC2PhiBelowLeaf30031 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3003) = true := by
  have h : ((childLH phiBelowCell3003)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH phiBelowCell3003) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30032 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsad7da039d5

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3003` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3003 : AngleCell :=
  childHH (childLL (childLL (childHH e24PhiBelowRoot)))

end CertificateCellsad7da039d5

open CertificateCellsad7da039d5
theorem e24KC2PhiBelowLeaf30032 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3003) = true := by
  have h : ((childHL phiBelowCell3003)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL phiBelowCell3003) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30033 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells1e800a73bb

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3003` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3003 : AngleCell :=
  childHH (childLL (childLL (childHH e24PhiBelowRoot)))

end CertificateCells1e800a73bb

open CertificateCells1e800a73bb
theorem e24KC2PhiBelowLeaf30033 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3003) = true := by
  have h : ((childHH phiBelowCell3003)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH phiBelowCell3003) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30100 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsb9d63d60b8

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3010` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3010 : AngleCell :=
  childLL (childLH (childLL (childHH e24PhiBelowRoot)))

end CertificateCellsb9d63d60b8

open CertificateCellsb9d63d60b8
namespace CoverCertificate7eaf46f70e






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate7eaf46f70e

theorem e24KC2PhiBelowLeaf30100 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3010) = true := by
  exact CoverCertificate7eaf46f70e.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30101 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells73ece5e183

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3010` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3010 : AngleCell :=
  childLL (childLH (childLL (childHH e24PhiBelowRoot)))

end CertificateCells73ece5e183

open CertificateCells73ece5e183
namespace CoverCertificate3307b34685






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate3307b34685

theorem e24KC2PhiBelowLeaf30101 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3010) = true := by
  exact CoverCertificate3307b34685.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30102 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsb58c03cf78

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3010` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3010 : AngleCell :=
  childLL (childLH (childLL (childHH e24PhiBelowRoot)))

end CertificateCellsb58c03cf78

open CertificateCellsb58c03cf78
namespace CoverCertificatea0fa380a93






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatea0fa380a93

theorem e24KC2PhiBelowLeaf30102 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3010) = true := by
  exact CoverCertificatea0fa380a93.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30103 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells3c73252ed6

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3010` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3010 : AngleCell :=
  childLL (childLH (childLL (childHH e24PhiBelowRoot)))

end CertificateCells3c73252ed6

open CertificateCells3c73252ed6
namespace CoverCertificate5f1fd442d3






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate5f1fd442d3

theorem e24KC2PhiBelowLeaf30103 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3010) = true := by
  exact CoverCertificate5f1fd442d3.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30110 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells75abf59285

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3011` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3011 : AngleCell :=
  childLH (childLH (childLL (childHH e24PhiBelowRoot)))

end CertificateCells75abf59285

open CertificateCells75abf59285
theorem e24KC2PhiBelowLeaf30110 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3011) = true := by
  have h : ((childLL phiBelowCell3011)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL phiBelowCell3011) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30111 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsc77278a9b0

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3011` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3011 : AngleCell :=
  childLH (childLH (childLL (childHH e24PhiBelowRoot)))

end CertificateCellsc77278a9b0

open CertificateCellsc77278a9b0
theorem e24KC2PhiBelowLeaf30111 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3011) = true := by
  have h : ((childLH phiBelowCell3011)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH phiBelowCell3011) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30112 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells80b449154c

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3011` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3011 : AngleCell :=
  childLH (childLH (childLL (childHH e24PhiBelowRoot)))

end CertificateCells80b449154c

open CertificateCells80b449154c
namespace CoverCertificated6f9cbc5d6






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificated6f9cbc5d6

theorem e24KC2PhiBelowLeaf30112 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3011) = true := by
  exact CoverCertificated6f9cbc5d6.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30113 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells19cd4580af

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3011` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3011 : AngleCell :=
  childLH (childLH (childLL (childHH e24PhiBelowRoot)))

end CertificateCells19cd4580af

open CertificateCells19cd4580af
theorem e24KC2PhiBelowLeaf30113 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3011) = true := by
  have h : ((childHH phiBelowCell3011)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH phiBelowCell3011) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30120 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsad60f51a47

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3012` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3012 : AngleCell :=
  childHL (childLH (childLL (childHH e24PhiBelowRoot)))

end CertificateCellsad60f51a47

open CertificateCellsad60f51a47
namespace CoverCertificatecaa270a0ec






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatecaa270a0ec

theorem e24KC2PhiBelowLeaf30120 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3012) = true := by
  exact CoverCertificatecaa270a0ec.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30121 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells59722ddf21

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3012` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3012 : AngleCell :=
  childHL (childLH (childLL (childHH e24PhiBelowRoot)))

end CertificateCells59722ddf21

open CertificateCells59722ddf21
namespace CoverCertificate0254ae442a






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate0254ae442a

theorem e24KC2PhiBelowLeaf30121 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3012) = true := by
  exact CoverCertificate0254ae442a.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30122 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells38add90453

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3012` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3012 : AngleCell :=
  childHL (childLH (childLL (childHH e24PhiBelowRoot)))

end CertificateCells38add90453

open CertificateCells38add90453
namespace CoverCertificate44197a14bc






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate44197a14bc

theorem e24KC2PhiBelowLeaf30122 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3012) = true := by
  exact CoverCertificate44197a14bc.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30123 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa2fd436678

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3012` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3012 : AngleCell :=
  childHL (childLH (childLL (childHH e24PhiBelowRoot)))

end CertificateCellsa2fd436678

open CertificateCellsa2fd436678
namespace CoverCertificateaa4818b079






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificateaa4818b079

theorem e24KC2PhiBelowLeaf30123 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3012) = true := by
  exact CoverCertificateaa4818b079.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30130 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells4036e8788a

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3013` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3013 : AngleCell :=
  childHH (childLH (childLL (childHH e24PhiBelowRoot)))

end CertificateCells4036e8788a

open CertificateCells4036e8788a
namespace CoverCertificateade660b261






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificateade660b261

theorem e24KC2PhiBelowLeaf30130 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3013) = true := by
  exact CoverCertificateade660b261.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30131 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellse8e082f5ed

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3013` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3013 : AngleCell :=
  childHH (childLH (childLL (childHH e24PhiBelowRoot)))

end CertificateCellse8e082f5ed

open CertificateCellse8e082f5ed
theorem e24KC2PhiBelowLeaf30131 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3013) = true := by
  have h : ((childLH phiBelowCell3013)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH phiBelowCell3013) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30132 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells33c2a4ae09

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3013` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3013 : AngleCell :=
  childHH (childLH (childLL (childHH e24PhiBelowRoot)))

end CertificateCells33c2a4ae09

open CertificateCells33c2a4ae09
namespace CoverCertificateead4291aaf






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificateead4291aaf

theorem e24KC2PhiBelowLeaf30132 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3013) = true := by
  exact CoverCertificateead4291aaf.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30133 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells8acf2cf43b

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3013` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3013 : AngleCell :=
  childHH (childLH (childLL (childHH e24PhiBelowRoot)))

end CertificateCells8acf2cf43b

open CertificateCells8acf2cf43b
namespace CoverCertificate76deff8421






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate76deff8421

theorem e24KC2PhiBelowLeaf30133 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3013) = true := by
  exact CoverCertificate76deff8421.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30200 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells4c5b439e46

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3020` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3020 : AngleCell :=
  childLL (childHL (childLL (childHH e24PhiBelowRoot)))

end CertificateCells4c5b439e46

open CertificateCells4c5b439e46
theorem e24KC2PhiBelowLeaf30200 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3020) = true := by
  have h : ((childLL phiBelowCell3020)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL phiBelowCell3020) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30201 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells1d890d537b

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3020` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3020 : AngleCell :=
  childLL (childHL (childLL (childHH e24PhiBelowRoot)))

end CertificateCells1d890d537b

open CertificateCells1d890d537b
theorem e24KC2PhiBelowLeaf30201 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3020) = true := by
  have h : ((childLH phiBelowCell3020)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH phiBelowCell3020) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30202 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells3dfd612f88

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3020` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3020 : AngleCell :=
  childLL (childHL (childLL (childHH e24PhiBelowRoot)))

end CertificateCells3dfd612f88

open CertificateCells3dfd612f88
theorem e24KC2PhiBelowLeaf30202 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3020) = true := by
  have h : ((childHL phiBelowCell3020)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL phiBelowCell3020) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30203 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsb73c54b84b

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3020` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3020 : AngleCell :=
  childLL (childHL (childLL (childHH e24PhiBelowRoot)))

end CertificateCellsb73c54b84b

open CertificateCellsb73c54b84b
theorem e24KC2PhiBelowLeaf30203 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3020) = true := by
  have h : ((childHH phiBelowCell3020)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH phiBelowCell3020) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30210 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa2d944a3cb

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3021` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3021 : AngleCell :=
  childLH (childHL (childLL (childHH e24PhiBelowRoot)))

end CertificateCellsa2d944a3cb

open CertificateCellsa2d944a3cb
theorem e24KC2PhiBelowLeaf30210 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3021) = true := by
  have h : ((childLL phiBelowCell3021)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL phiBelowCell3021) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30211 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa175b3d804

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3021` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3021 : AngleCell :=
  childLH (childHL (childLL (childHH e24PhiBelowRoot)))

end CertificateCellsa175b3d804

open CertificateCellsa175b3d804
namespace CoverCertificatef9c3dd592d






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatef9c3dd592d

theorem e24KC2PhiBelowLeaf30211 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3021) = true := by
  exact CoverCertificatef9c3dd592d.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30212 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells2377a41132

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3021` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3021 : AngleCell :=
  childLH (childHL (childLL (childHH e24PhiBelowRoot)))

end CertificateCells2377a41132

open CertificateCells2377a41132
theorem e24KC2PhiBelowLeaf30212 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3021) = true := by
  have h : ((childHL phiBelowCell3021)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL phiBelowCell3021) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30213 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells141b81b7b9

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3021` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3021 : AngleCell :=
  childLH (childHL (childLL (childHH e24PhiBelowRoot)))

end CertificateCells141b81b7b9

open CertificateCells141b81b7b9
namespace CoverCertificate55e26a37bf






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate55e26a37bf

theorem e24KC2PhiBelowLeaf30213 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3021) = true := by
  exact CoverCertificate55e26a37bf.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30220 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells53ed2717a4

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3022` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3022 : AngleCell :=
  childHL (childHL (childLL (childHH e24PhiBelowRoot)))

end CertificateCells53ed2717a4

open CertificateCells53ed2717a4
theorem e24KC2PhiBelowLeaf30220 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3022) = true := by
  have h : ((childLL phiBelowCell3022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL phiBelowCell3022) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30221 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells6cc17280cd

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3022` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3022 : AngleCell :=
  childHL (childHL (childLL (childHH e24PhiBelowRoot)))

end CertificateCells6cc17280cd

open CertificateCells6cc17280cd
theorem e24KC2PhiBelowLeaf30221 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3022) = true := by
  have h : ((childLH phiBelowCell3022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH phiBelowCell3022) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30222 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellscd48c30df5

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3022` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3022 : AngleCell :=
  childHL (childHL (childLL (childHH e24PhiBelowRoot)))

end CertificateCellscd48c30df5

open CertificateCellscd48c30df5
theorem e24KC2PhiBelowLeaf30222 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3022) = true := by
  have h : ((childHL phiBelowCell3022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL phiBelowCell3022) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30223 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells6a90ac3f5f

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3022` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3022 : AngleCell :=
  childHL (childHL (childLL (childHH e24PhiBelowRoot)))

end CertificateCells6a90ac3f5f

open CertificateCells6a90ac3f5f
theorem e24KC2PhiBelowLeaf30223 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3022) = true := by
  have h : ((childHH phiBelowCell3022)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH phiBelowCell3022) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30230 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellscb8a79a1e7

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3023` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3023 : AngleCell :=
  childHH (childHL (childLL (childHH e24PhiBelowRoot)))

end CertificateCellscb8a79a1e7

open CertificateCellscb8a79a1e7
theorem e24KC2PhiBelowLeaf30230 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3023) = true := by
  have h : ((childLL phiBelowCell3023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL phiBelowCell3023) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30231 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa17655a9cd

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3023` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3023 : AngleCell :=
  childHH (childHL (childLL (childHH e24PhiBelowRoot)))

end CertificateCellsa17655a9cd

open CertificateCellsa17655a9cd
namespace CoverCertificated546542719






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificated546542719

theorem e24KC2PhiBelowLeaf30231 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3023) = true := by
  exact CoverCertificated546542719.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30232 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsea417091fc

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3023` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3023 : AngleCell :=
  childHH (childHL (childLL (childHH e24PhiBelowRoot)))

end CertificateCellsea417091fc

open CertificateCellsea417091fc
theorem e24KC2PhiBelowLeaf30232 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3023) = true := by
  have h : ((childHL phiBelowCell3023)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL phiBelowCell3023) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30233 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells58f12e8647

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3023` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3023 : AngleCell :=
  childHH (childHL (childLL (childHH e24PhiBelowRoot)))

end CertificateCells58f12e8647

open CertificateCells58f12e8647
namespace CoverCertificate09704881ea






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate09704881ea

theorem e24KC2PhiBelowLeaf30233 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3023) = true := by
  exact CoverCertificate09704881ea.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30300 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells5256e12156

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3030` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3030 : AngleCell :=
  childLL (childHH (childLL (childHH e24PhiBelowRoot)))

end CertificateCells5256e12156

open CertificateCells5256e12156
namespace CoverCertificate89f8bf996f






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate89f8bf996f

theorem e24KC2PhiBelowLeaf30300 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3030) = true := by
  exact CoverCertificate89f8bf996f.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30301 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa7b064ca3f

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3030` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3030 : AngleCell :=
  childLL (childHH (childLL (childHH e24PhiBelowRoot)))

end CertificateCellsa7b064ca3f

open CertificateCellsa7b064ca3f
namespace CoverCertificate072d32638e






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate072d32638e

theorem e24KC2PhiBelowLeaf30301 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3030) = true := by
  exact CoverCertificate072d32638e.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30302 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa6d5038417

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3030` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3030 : AngleCell :=
  childLL (childHH (childLL (childHH e24PhiBelowRoot)))

end CertificateCellsa6d5038417

open CertificateCellsa6d5038417
namespace CoverCertificate5c3ff9507c






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate5c3ff9507c

theorem e24KC2PhiBelowLeaf30302 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3030) = true := by
  exact CoverCertificate5c3ff9507c.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30303 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa40437554b

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3030` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3030 : AngleCell :=
  childLL (childHH (childLL (childHH e24PhiBelowRoot)))

end CertificateCellsa40437554b

open CertificateCellsa40437554b
namespace CoverCertificate0e6fd3d794






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate0e6fd3d794

theorem e24KC2PhiBelowLeaf30303 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3030) = true := by
  exact CoverCertificate0e6fd3d794.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30310 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells99d0a4be54

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3031` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3031 : AngleCell :=
  childLH (childHH (childLL (childHH e24PhiBelowRoot)))

end CertificateCells99d0a4be54

open CertificateCells99d0a4be54
namespace CoverCertificate1d8d5ed6e8






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate1d8d5ed6e8

theorem e24KC2PhiBelowLeaf30310 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3031) = true := by
  exact CoverCertificate1d8d5ed6e8.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30311 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells473a273fc9

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3031` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3031 : AngleCell :=
  childLH (childHH (childLL (childHH e24PhiBelowRoot)))

end CertificateCells473a273fc9

open CertificateCells473a273fc9
namespace CoverCertificatead0c92c0d4






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatead0c92c0d4

theorem e24KC2PhiBelowLeaf30311 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3031) = true := by
  exact CoverCertificatead0c92c0d4.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30312 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells3c757ee420

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3031` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3031 : AngleCell :=
  childLH (childHH (childLL (childHH e24PhiBelowRoot)))

end CertificateCells3c757ee420

open CertificateCells3c757ee420
namespace CoverCertificate4e6964ff18






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate4e6964ff18

theorem e24KC2PhiBelowLeaf30312 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3031) = true := by
  exact CoverCertificate4e6964ff18.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30313 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsd8b0ff734e

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3031` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3031 : AngleCell :=
  childLH (childHH (childLL (childHH e24PhiBelowRoot)))

end CertificateCellsd8b0ff734e

open CertificateCellsd8b0ff734e
namespace CoverCertificate14906b8c69






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate14906b8c69

theorem e24KC2PhiBelowLeaf30313 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3031) = true := by
  exact CoverCertificate14906b8c69.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30320 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells03aa6fa886

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3032` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3032 : AngleCell :=
  childHL (childHH (childLL (childHH e24PhiBelowRoot)))

end CertificateCells03aa6fa886

open CertificateCells03aa6fa886
namespace CoverCertificate4614f242b3






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate4614f242b3

theorem e24KC2PhiBelowLeaf30320 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3032) = true := by
  exact CoverCertificate4614f242b3.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30321 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsf82ea84544

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3032` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3032 : AngleCell :=
  childHL (childHH (childLL (childHH e24PhiBelowRoot)))

end CertificateCellsf82ea84544

open CertificateCellsf82ea84544
namespace CoverCertificatef3c458cae3






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatef3c458cae3

theorem e24KC2PhiBelowLeaf30321 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3032) = true := by
  exact CoverCertificatef3c458cae3.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30322 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa1f10633df

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3032` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3032 : AngleCell :=
  childHL (childHH (childLL (childHH e24PhiBelowRoot)))

end CertificateCellsa1f10633df

open CertificateCellsa1f10633df
namespace CoverCertificateeb6553a302






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificateeb6553a302

theorem e24KC2PhiBelowLeaf30322 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3032) = true := by
  exact CoverCertificateeb6553a302.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30323 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells92aeaddf18

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3032` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3032 : AngleCell :=
  childHL (childHH (childLL (childHH e24PhiBelowRoot)))

end CertificateCells92aeaddf18

open CertificateCells92aeaddf18
namespace CoverCertificatefa7152b230






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatefa7152b230

theorem e24KC2PhiBelowLeaf30323 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3032) = true := by
  exact CoverCertificatefa7152b230.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30330 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells4d2736f1ee

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3033` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3033 : AngleCell :=
  childHH (childHH (childLL (childHH e24PhiBelowRoot)))

end CertificateCells4d2736f1ee

open CertificateCells4d2736f1ee
namespace CoverCertificate8afa5ed490














private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 7 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 7 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 7 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 7 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate8afa5ed490

theorem e24KC2PhiBelowLeaf30330 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3033) = true := by
  exact CoverCertificate8afa5ed490.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30331 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsf1c569afeb

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3033` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3033 : AngleCell :=
  childHH (childHH (childLL (childHH e24PhiBelowRoot)))

end CertificateCellsf1c569afeb

open CertificateCellsf1c569afeb
namespace CoverCertificated9debec79d










private theorem checked20 : adaptiveCoverCheck 7 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 7 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 7 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 7 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell23 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificated9debec79d

theorem e24KC2PhiBelowLeaf30331 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3033) = true := by
  exact CoverCertificated9debec79d.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30332 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells899e3e87cc

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3033` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3033 : AngleCell :=
  childHH (childHH (childLL (childHH e24PhiBelowRoot)))

end CertificateCells899e3e87cc

open CertificateCells899e3e87cc
namespace CoverCertificate67d4072331














private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 7 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 7 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 7 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 7 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate67d4072331

theorem e24KC2PhiBelowLeaf30332 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3033) = true := by
  exact CoverCertificate67d4072331.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=30333 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells8cea727797

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3033` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3033 : AngleCell :=
  childHH (childHH (childLL (childHH e24PhiBelowRoot)))

end CertificateCells8cea727797

open CertificateCells8cea727797
namespace CoverCertificatebed93df298


















private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell03 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 7 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 7 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 7 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 7 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 7 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 7 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 7 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 7 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatebed93df298

theorem e24KC2PhiBelowLeaf30333 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3033) = true := by
  exact CoverCertificatebed93df298.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31000 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsdf788d056e

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3100` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3100 : AngleCell :=
  childLL (childLL (childLH (childHH e24PhiBelowRoot)))

end CertificateCellsdf788d056e

open CertificateCellsdf788d056e
theorem e24KC2PhiBelowLeaf31000 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3100) = true := by
  have h : ((childLL phiBelowCell3100)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL phiBelowCell3100) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31001 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells83252066d4

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3100` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3100 : AngleCell :=
  childLL (childLL (childLH (childHH e24PhiBelowRoot)))

end CertificateCells83252066d4

open CertificateCells83252066d4
theorem e24KC2PhiBelowLeaf31001 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3100) = true := by
  have h : ((childLH phiBelowCell3100)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH phiBelowCell3100) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31002 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsd15521ecc4

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3100` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3100 : AngleCell :=
  childLL (childLL (childLH (childHH e24PhiBelowRoot)))

end CertificateCellsd15521ecc4

open CertificateCellsd15521ecc4
theorem e24KC2PhiBelowLeaf31002 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3100) = true := by
  have h : ((childHL phiBelowCell3100)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL phiBelowCell3100) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31003 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells9ebe05244a

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3100` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3100 : AngleCell :=
  childLL (childLL (childLH (childHH e24PhiBelowRoot)))

end CertificateCells9ebe05244a

open CertificateCells9ebe05244a
theorem e24KC2PhiBelowLeaf31003 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3100) = true := by
  have h : ((childHH phiBelowCell3100)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH phiBelowCell3100) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31010 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells21fc209558

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3101` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3101 : AngleCell :=
  childLH (childLL (childLH (childHH e24PhiBelowRoot)))

end CertificateCells21fc209558

open CertificateCells21fc209558
theorem e24KC2PhiBelowLeaf31010 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3101) = true := by
  have h : ((childLL phiBelowCell3101)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL phiBelowCell3101) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31011 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsc545b9b00b

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3101` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3101 : AngleCell :=
  childLH (childLL (childLH (childHH e24PhiBelowRoot)))

end CertificateCellsc545b9b00b

open CertificateCellsc545b9b00b
theorem e24KC2PhiBelowLeaf31011 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3101) = true := by
  have h : ((childLH phiBelowCell3101)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH phiBelowCell3101) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31012 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa64e976caf

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3101` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3101 : AngleCell :=
  childLH (childLL (childLH (childHH e24PhiBelowRoot)))

end CertificateCellsa64e976caf

open CertificateCellsa64e976caf
theorem e24KC2PhiBelowLeaf31012 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3101) = true := by
  have h : ((childHL phiBelowCell3101)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL phiBelowCell3101) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31013 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsf9eb6beb81

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3101` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3101 : AngleCell :=
  childLH (childLL (childLH (childHH e24PhiBelowRoot)))

end CertificateCellsf9eb6beb81

open CertificateCellsf9eb6beb81
theorem e24KC2PhiBelowLeaf31013 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3101) = true := by
  have h : ((childHH phiBelowCell3101)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH phiBelowCell3101) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31020 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells1d67e12ba0

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3102` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3102 : AngleCell :=
  childHL (childLL (childLH (childHH e24PhiBelowRoot)))

end CertificateCells1d67e12ba0

open CertificateCells1d67e12ba0
theorem e24KC2PhiBelowLeaf31020 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3102) = true := by
  have h : ((childLL phiBelowCell3102)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL phiBelowCell3102) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31021 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa2d5114e5e

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3102` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3102 : AngleCell :=
  childHL (childLL (childLH (childHH e24PhiBelowRoot)))

end CertificateCellsa2d5114e5e

open CertificateCellsa2d5114e5e
theorem e24KC2PhiBelowLeaf31021 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3102) = true := by
  have h : ((childLH phiBelowCell3102)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH phiBelowCell3102) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31022 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells414314cff6

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3102` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3102 : AngleCell :=
  childHL (childLL (childLH (childHH e24PhiBelowRoot)))

end CertificateCells414314cff6

open CertificateCells414314cff6
theorem e24KC2PhiBelowLeaf31022 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3102) = true := by
  have h : ((childHL phiBelowCell3102)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL phiBelowCell3102) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31023 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsf9010539ff

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3102` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3102 : AngleCell :=
  childHL (childLL (childLH (childHH e24PhiBelowRoot)))

end CertificateCellsf9010539ff

open CertificateCellsf9010539ff
theorem e24KC2PhiBelowLeaf31023 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3102) = true := by
  have h : ((childHH phiBelowCell3102)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH phiBelowCell3102) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31030 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellse34346aa4a

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3103` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3103 : AngleCell :=
  childHH (childLL (childLH (childHH e24PhiBelowRoot)))

end CertificateCellse34346aa4a

open CertificateCellse34346aa4a
theorem e24KC2PhiBelowLeaf31030 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3103) = true := by
  have h : ((childLL phiBelowCell3103)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL phiBelowCell3103) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31031 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellse191f15fec

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3103` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3103 : AngleCell :=
  childHH (childLL (childLH (childHH e24PhiBelowRoot)))

end CertificateCellse191f15fec

open CertificateCellse191f15fec
theorem e24KC2PhiBelowLeaf31031 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3103) = true := by
  have h : ((childLH phiBelowCell3103)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH phiBelowCell3103) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31032 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsf92808a3cc

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3103` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3103 : AngleCell :=
  childHH (childLL (childLH (childHH e24PhiBelowRoot)))

end CertificateCellsf92808a3cc

open CertificateCellsf92808a3cc
theorem e24KC2PhiBelowLeaf31032 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3103) = true := by
  have h : ((childHL phiBelowCell3103)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL phiBelowCell3103) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31033 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells897e4339a9

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3103` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3103 : AngleCell :=
  childHH (childLL (childLH (childHH e24PhiBelowRoot)))

end CertificateCells897e4339a9

open CertificateCells897e4339a9
theorem e24KC2PhiBelowLeaf31033 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3103) = true := by
  have h : ((childHH phiBelowCell3103)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH phiBelowCell3103) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=3110 remaining=10 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsf4227a46c1

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3110` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3110 : AngleCell :=
  childLL (childLH (childLH (childHH e24PhiBelowRoot)))

end CertificateCellsf4227a46c1

open CertificateCellsf4227a46c1
theorem e24KC2PhiBelowLeaf3110 :
    adaptiveCoverCheck 10 phiBelowCell3110 = true := by
  have h : (phiBelowCell3110).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 phiBelowCell3110 h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=3111 remaining=10 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa2ba14667f

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3111` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3111 : AngleCell :=
  childLH (childLH (childLH (childHH e24PhiBelowRoot)))

end CertificateCellsa2ba14667f

open CertificateCellsa2ba14667f
theorem e24KC2PhiBelowLeaf3111 :
    adaptiveCoverCheck 10 phiBelowCell3111 = true := by
  have h : (phiBelowCell3111).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 phiBelowCell3111 h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31120 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells172a47199c

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3112` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3112 : AngleCell :=
  childHL (childLH (childLH (childHH e24PhiBelowRoot)))

end CertificateCells172a47199c

open CertificateCells172a47199c
theorem e24KC2PhiBelowLeaf31120 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3112) = true := by
  have h : ((childLL phiBelowCell3112)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL phiBelowCell3112) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31121 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells503a496e12

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3112` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3112 : AngleCell :=
  childHL (childLH (childLH (childHH e24PhiBelowRoot)))

end CertificateCells503a496e12

open CertificateCells503a496e12
theorem e24KC2PhiBelowLeaf31121 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3112) = true := by
  have h : ((childLH phiBelowCell3112)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH phiBelowCell3112) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31122 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells4f35c82776

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3112` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3112 : AngleCell :=
  childHL (childLH (childLH (childHH e24PhiBelowRoot)))

end CertificateCells4f35c82776

open CertificateCells4f35c82776
theorem e24KC2PhiBelowLeaf31122 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3112) = true := by
  have h : ((childHL phiBelowCell3112)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL phiBelowCell3112) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31123 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsddf26a1af9

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3112` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3112 : AngleCell :=
  childHL (childLH (childLH (childHH e24PhiBelowRoot)))

end CertificateCellsddf26a1af9

open CertificateCellsddf26a1af9
theorem e24KC2PhiBelowLeaf31123 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3112) = true := by
  have h : ((childHH phiBelowCell3112)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH phiBelowCell3112) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=3113 remaining=10 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells725d74e81a

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3113` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3113 : AngleCell :=
  childHH (childLH (childLH (childHH e24PhiBelowRoot)))

end CertificateCells725d74e81a

open CertificateCells725d74e81a
theorem e24KC2PhiBelowLeaf3113 :
    adaptiveCoverCheck 10 phiBelowCell3113 = true := by
  have h : (phiBelowCell3113).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 10 phiBelowCell3113 h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31200 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells3b33327e8a

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3120` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3120 : AngleCell :=
  childLL (childHL (childLH (childHH e24PhiBelowRoot)))

end CertificateCells3b33327e8a

open CertificateCells3b33327e8a
namespace CoverCertificatefd2c3f3274






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatefd2c3f3274

theorem e24KC2PhiBelowLeaf31200 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3120) = true := by
  exact CoverCertificatefd2c3f3274.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31201 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells7bfd1f464a

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3120` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3120 : AngleCell :=
  childLL (childHL (childLH (childHH e24PhiBelowRoot)))

end CertificateCells7bfd1f464a

open CertificateCells7bfd1f464a
theorem e24KC2PhiBelowLeaf31201 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3120) = true := by
  have h : ((childLH phiBelowCell3120)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH phiBelowCell3120) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31202 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsdd644ededa

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3120` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3120 : AngleCell :=
  childLL (childHL (childLH (childHH e24PhiBelowRoot)))

end CertificateCellsdd644ededa

open CertificateCellsdd644ededa
namespace CoverCertificate1ffa851843






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate1ffa851843

theorem e24KC2PhiBelowLeaf31202 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3120) = true := by
  exact CoverCertificate1ffa851843.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31203 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsdd54c72360

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3120` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3120 : AngleCell :=
  childLL (childHL (childLH (childHH e24PhiBelowRoot)))

end CertificateCellsdd54c72360

open CertificateCellsdd54c72360
namespace CoverCertificated8ac44ac8f






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificated8ac44ac8f

theorem e24KC2PhiBelowLeaf31203 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3120) = true := by
  exact CoverCertificated8ac44ac8f.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31210 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsf0f5b1fc54

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3121` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3121 : AngleCell :=
  childLH (childHL (childLH (childHH e24PhiBelowRoot)))

end CertificateCellsf0f5b1fc54

open CertificateCellsf0f5b1fc54
theorem e24KC2PhiBelowLeaf31210 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3121) = true := by
  have h : ((childLL phiBelowCell3121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL phiBelowCell3121) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31211 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells2b0822f9b0

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3121` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3121 : AngleCell :=
  childLH (childHL (childLH (childHH e24PhiBelowRoot)))

end CertificateCells2b0822f9b0

open CertificateCells2b0822f9b0
theorem e24KC2PhiBelowLeaf31211 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3121) = true := by
  have h : ((childLH phiBelowCell3121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH phiBelowCell3121) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31212 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells05e3ee5af2

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3121` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3121 : AngleCell :=
  childLH (childHL (childLH (childHH e24PhiBelowRoot)))

end CertificateCells05e3ee5af2

open CertificateCells05e3ee5af2
theorem e24KC2PhiBelowLeaf31212 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3121) = true := by
  have h : ((childHL phiBelowCell3121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL phiBelowCell3121) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31213 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells8f81fc559c

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3121` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3121 : AngleCell :=
  childLH (childHL (childLH (childHH e24PhiBelowRoot)))

end CertificateCells8f81fc559c

open CertificateCells8f81fc559c
theorem e24KC2PhiBelowLeaf31213 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3121) = true := by
  have h : ((childHH phiBelowCell3121)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH phiBelowCell3121) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31220 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells509a6074b0

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3122` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3122 : AngleCell :=
  childHL (childHL (childLH (childHH e24PhiBelowRoot)))

end CertificateCells509a6074b0

open CertificateCells509a6074b0
namespace CoverCertificate3caeb3dd1d






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate3caeb3dd1d

theorem e24KC2PhiBelowLeaf31220 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3122) = true := by
  exact CoverCertificate3caeb3dd1d.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31221 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells6ac6e4ee1a

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3122` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3122 : AngleCell :=
  childHL (childHL (childLH (childHH e24PhiBelowRoot)))

end CertificateCells6ac6e4ee1a

open CertificateCells6ac6e4ee1a
namespace CoverCertificate3195681328






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate3195681328

theorem e24KC2PhiBelowLeaf31221 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3122) = true := by
  exact CoverCertificate3195681328.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31222 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells2e92118453

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3122` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3122 : AngleCell :=
  childHL (childHL (childLH (childHH e24PhiBelowRoot)))

end CertificateCells2e92118453

open CertificateCells2e92118453
namespace CoverCertificate24d91bb18c






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate24d91bb18c

theorem e24KC2PhiBelowLeaf31222 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3122) = true := by
  exact CoverCertificate24d91bb18c.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31223 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells5761c4811e

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3122` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3122 : AngleCell :=
  childHL (childHL (childLH (childHH e24PhiBelowRoot)))

end CertificateCells5761c4811e

open CertificateCells5761c4811e
namespace CoverCertificatea5eff6d169






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatea5eff6d169

theorem e24KC2PhiBelowLeaf31223 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3122) = true := by
  exact CoverCertificatea5eff6d169.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31230 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsf228466209

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3123` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3123 : AngleCell :=
  childHH (childHL (childLH (childHH e24PhiBelowRoot)))

end CertificateCellsf228466209

open CertificateCellsf228466209
theorem e24KC2PhiBelowLeaf31230 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3123) = true := by
  have h : ((childLL phiBelowCell3123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL phiBelowCell3123) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31231 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells4924d89385

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3123` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3123 : AngleCell :=
  childHH (childHL (childLH (childHH e24PhiBelowRoot)))

end CertificateCells4924d89385

open CertificateCells4924d89385
theorem e24KC2PhiBelowLeaf31231 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3123) = true := by
  have h : ((childLH phiBelowCell3123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH phiBelowCell3123) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31232 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells75bbd1e667

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3123` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3123 : AngleCell :=
  childHH (childHL (childLH (childHH e24PhiBelowRoot)))

end CertificateCells75bbd1e667

open CertificateCells75bbd1e667
namespace CoverCertificateabfc719760






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificateabfc719760

theorem e24KC2PhiBelowLeaf31232 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3123) = true := by
  exact CoverCertificateabfc719760.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31233 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells131513700f

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3123` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3123 : AngleCell :=
  childHH (childHL (childLH (childHH e24PhiBelowRoot)))

end CertificateCells131513700f

open CertificateCells131513700f
theorem e24KC2PhiBelowLeaf31233 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3123) = true := by
  have h : ((childHH phiBelowCell3123)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH phiBelowCell3123) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31300 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells0436aa31cb

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3130` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3130 : AngleCell :=
  childLL (childHH (childLH (childHH e24PhiBelowRoot)))

end CertificateCells0436aa31cb

open CertificateCells0436aa31cb
theorem e24KC2PhiBelowLeaf31300 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3130) = true := by
  have h : ((childLL phiBelowCell3130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL phiBelowCell3130) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31301 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells4cca5ef5ea

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3130` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3130 : AngleCell :=
  childLL (childHH (childLH (childHH e24PhiBelowRoot)))

end CertificateCells4cca5ef5ea

open CertificateCells4cca5ef5ea
theorem e24KC2PhiBelowLeaf31301 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3130) = true := by
  have h : ((childLH phiBelowCell3130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH phiBelowCell3130) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31302 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells2133748f57

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3130` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3130 : AngleCell :=
  childLL (childHH (childLH (childHH e24PhiBelowRoot)))

end CertificateCells2133748f57

open CertificateCells2133748f57
theorem e24KC2PhiBelowLeaf31302 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3130) = true := by
  have h : ((childHL phiBelowCell3130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL phiBelowCell3130) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31303 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells2d9432dbe0

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3130` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3130 : AngleCell :=
  childLL (childHH (childLH (childHH e24PhiBelowRoot)))

end CertificateCells2d9432dbe0

open CertificateCells2d9432dbe0
theorem e24KC2PhiBelowLeaf31303 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3130) = true := by
  have h : ((childHH phiBelowCell3130)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH phiBelowCell3130) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31310 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells28839ca767

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3131` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3131 : AngleCell :=
  childLH (childHH (childLH (childHH e24PhiBelowRoot)))

end CertificateCells28839ca767

open CertificateCells28839ca767
theorem e24KC2PhiBelowLeaf31310 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3131) = true := by
  have h : ((childLL phiBelowCell3131)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL phiBelowCell3131) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31311 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells1b0bf20c51

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3131` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3131 : AngleCell :=
  childLH (childHH (childLH (childHH e24PhiBelowRoot)))

end CertificateCells1b0bf20c51

open CertificateCells1b0bf20c51
theorem e24KC2PhiBelowLeaf31311 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3131) = true := by
  have h : ((childLH phiBelowCell3131)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH phiBelowCell3131) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31312 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells9fb8ae7256

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3131` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3131 : AngleCell :=
  childLH (childHH (childLH (childHH e24PhiBelowRoot)))

end CertificateCells9fb8ae7256

open CertificateCells9fb8ae7256
theorem e24KC2PhiBelowLeaf31312 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3131) = true := by
  have h : ((childHL phiBelowCell3131)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL phiBelowCell3131) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31313 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells10b8b658d1

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3131` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3131 : AngleCell :=
  childLH (childHH (childLH (childHH e24PhiBelowRoot)))

end CertificateCells10b8b658d1

open CertificateCells10b8b658d1
theorem e24KC2PhiBelowLeaf31313 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3131) = true := by
  have h : ((childHH phiBelowCell3131)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH phiBelowCell3131) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31320 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells372671dc1b

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3132` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3132 : AngleCell :=
  childHL (childHH (childLH (childHH e24PhiBelowRoot)))

end CertificateCells372671dc1b

open CertificateCells372671dc1b
theorem e24KC2PhiBelowLeaf31320 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3132) = true := by
  have h : ((childLL phiBelowCell3132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL phiBelowCell3132) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31321 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells91a123c697

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3132` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3132 : AngleCell :=
  childHL (childHH (childLH (childHH e24PhiBelowRoot)))

end CertificateCells91a123c697

open CertificateCells91a123c697
theorem e24KC2PhiBelowLeaf31321 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3132) = true := by
  have h : ((childLH phiBelowCell3132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH phiBelowCell3132) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31322 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsce14c27bce

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3132` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3132 : AngleCell :=
  childHL (childHH (childLH (childHH e24PhiBelowRoot)))

end CertificateCellsce14c27bce

open CertificateCellsce14c27bce
theorem e24KC2PhiBelowLeaf31322 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3132) = true := by
  have h : ((childHL phiBelowCell3132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL phiBelowCell3132) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31323 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsabc89a203a

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3132` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3132 : AngleCell :=
  childHL (childHH (childLH (childHH e24PhiBelowRoot)))

end CertificateCellsabc89a203a

open CertificateCellsabc89a203a
theorem e24KC2PhiBelowLeaf31323 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3132) = true := by
  have h : ((childHH phiBelowCell3132)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH phiBelowCell3132) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31330 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells6f99a95071

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3133` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3133 : AngleCell :=
  childHH (childHH (childLH (childHH e24PhiBelowRoot)))

end CertificateCells6f99a95071

open CertificateCells6f99a95071
theorem e24KC2PhiBelowLeaf31330 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3133) = true := by
  have h : ((childLL phiBelowCell3133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL phiBelowCell3133) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31331 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells4acdbba755

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3133` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3133 : AngleCell :=
  childHH (childHH (childLH (childHH e24PhiBelowRoot)))

end CertificateCells4acdbba755

open CertificateCells4acdbba755
theorem e24KC2PhiBelowLeaf31331 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3133) = true := by
  have h : ((childLH phiBelowCell3133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH phiBelowCell3133) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31332 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells45607104df

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3133` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3133 : AngleCell :=
  childHH (childHH (childLH (childHH e24PhiBelowRoot)))

end CertificateCells45607104df

open CertificateCells45607104df
theorem e24KC2PhiBelowLeaf31332 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3133) = true := by
  have h : ((childHL phiBelowCell3133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL phiBelowCell3133) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=31333 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsf2e66397f6

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3133` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3133 : AngleCell :=
  childHH (childHH (childLH (childHH e24PhiBelowRoot)))

end CertificateCellsf2e66397f6

open CertificateCellsf2e66397f6
theorem e24KC2PhiBelowLeaf31333 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3133) = true := by
  have h : ((childHH phiBelowCell3133)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH phiBelowCell3133) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32000 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsf60a68912f

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3200` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3200 : AngleCell :=
  childLL (childLL (childHL (childHH e24PhiBelowRoot)))

end CertificateCellsf60a68912f

open CertificateCellsf60a68912f
theorem e24KC2PhiBelowLeaf32000 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3200) = true := by
  have h : ((childLL phiBelowCell3200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL phiBelowCell3200) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32001 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsdb667fab49

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3200` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3200 : AngleCell :=
  childLL (childLL (childHL (childHH e24PhiBelowRoot)))

end CertificateCellsdb667fab49

open CertificateCellsdb667fab49
theorem e24KC2PhiBelowLeaf32001 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3200) = true := by
  have h : ((childLH phiBelowCell3200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH phiBelowCell3200) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32002 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells378433963d

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3200` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3200 : AngleCell :=
  childLL (childLL (childHL (childHH e24PhiBelowRoot)))

end CertificateCells378433963d

open CertificateCells378433963d
theorem e24KC2PhiBelowLeaf32002 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3200) = true := by
  have h : ((childHL phiBelowCell3200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL phiBelowCell3200) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32003 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells3c30c58615

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3200` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3200 : AngleCell :=
  childLL (childLL (childHL (childHH e24PhiBelowRoot)))

end CertificateCells3c30c58615

open CertificateCells3c30c58615
theorem e24KC2PhiBelowLeaf32003 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3200) = true := by
  have h : ((childHH phiBelowCell3200)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH phiBelowCell3200) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32010 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellscbc2cb8c4d

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3201` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3201 : AngleCell :=
  childLH (childLL (childHL (childHH e24PhiBelowRoot)))

end CertificateCellscbc2cb8c4d

open CertificateCellscbc2cb8c4d
theorem e24KC2PhiBelowLeaf32010 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3201) = true := by
  have h : ((childLL phiBelowCell3201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL phiBelowCell3201) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32011 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells0ae5e3afe8

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3201` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3201 : AngleCell :=
  childLH (childLL (childHL (childHH e24PhiBelowRoot)))

end CertificateCells0ae5e3afe8

open CertificateCells0ae5e3afe8
namespace CoverCertificate0a514de912






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate0a514de912

theorem e24KC2PhiBelowLeaf32011 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3201) = true := by
  exact CoverCertificate0a514de912.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32012 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells72905f39fb

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3201` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3201 : AngleCell :=
  childLH (childLL (childHL (childHH e24PhiBelowRoot)))

end CertificateCells72905f39fb

open CertificateCells72905f39fb
theorem e24KC2PhiBelowLeaf32012 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3201) = true := by
  have h : ((childHL phiBelowCell3201)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL phiBelowCell3201) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32013 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells36ded03275

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3201` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3201 : AngleCell :=
  childLH (childLL (childHL (childHH e24PhiBelowRoot)))

end CertificateCells36ded03275

open CertificateCells36ded03275
namespace CoverCertificate7ed638f543






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate7ed638f543

theorem e24KC2PhiBelowLeaf32013 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3201) = true := by
  exact CoverCertificate7ed638f543.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32020 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells055eee17e7

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3202` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3202 : AngleCell :=
  childHL (childLL (childHL (childHH e24PhiBelowRoot)))

end CertificateCells055eee17e7

open CertificateCells055eee17e7
theorem e24KC2PhiBelowLeaf32020 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3202) = true := by
  have h : ((childLL phiBelowCell3202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL phiBelowCell3202) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32021 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells86a7b10d51

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3202` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3202 : AngleCell :=
  childHL (childLL (childHL (childHH e24PhiBelowRoot)))

end CertificateCells86a7b10d51

open CertificateCells86a7b10d51
theorem e24KC2PhiBelowLeaf32021 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3202) = true := by
  have h : ((childLH phiBelowCell3202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH phiBelowCell3202) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32022 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells62973479ba

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3202` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3202 : AngleCell :=
  childHL (childLL (childHL (childHH e24PhiBelowRoot)))

end CertificateCells62973479ba

open CertificateCells62973479ba
theorem e24KC2PhiBelowLeaf32022 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3202) = true := by
  have h : ((childHL phiBelowCell3202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL phiBelowCell3202) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32023 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellse26adcc478

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3202` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3202 : AngleCell :=
  childHL (childLL (childHL (childHH e24PhiBelowRoot)))

end CertificateCellse26adcc478

open CertificateCellse26adcc478
theorem e24KC2PhiBelowLeaf32023 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3202) = true := by
  have h : ((childHH phiBelowCell3202)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH phiBelowCell3202) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32030 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsd471241912

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3203` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3203 : AngleCell :=
  childHH (childLL (childHL (childHH e24PhiBelowRoot)))

end CertificateCellsd471241912

open CertificateCellsd471241912
theorem e24KC2PhiBelowLeaf32030 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3203) = true := by
  have h : ((childLL phiBelowCell3203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL phiBelowCell3203) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32031 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells89c6c55f33

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3203` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3203 : AngleCell :=
  childHH (childLL (childHL (childHH e24PhiBelowRoot)))

end CertificateCells89c6c55f33

open CertificateCells89c6c55f33
namespace CoverCertificatebdb1950cb6






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatebdb1950cb6

theorem e24KC2PhiBelowLeaf32031 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3203) = true := by
  exact CoverCertificatebdb1950cb6.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32032 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells371a4c38c5

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3203` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3203 : AngleCell :=
  childHH (childLL (childHL (childHH e24PhiBelowRoot)))

end CertificateCells371a4c38c5

open CertificateCells371a4c38c5
theorem e24KC2PhiBelowLeaf32032 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3203) = true := by
  have h : ((childHL phiBelowCell3203)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL phiBelowCell3203) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32033 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells96fe0c4e84

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3203` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3203 : AngleCell :=
  childHH (childLL (childHL (childHH e24PhiBelowRoot)))

end CertificateCells96fe0c4e84

open CertificateCells96fe0c4e84
namespace CoverCertificate5fb7a54ee1






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate5fb7a54ee1

theorem e24KC2PhiBelowLeaf32033 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3203) = true := by
  exact CoverCertificate5fb7a54ee1.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32100 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells9ae3b0f784

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3210` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3210 : AngleCell :=
  childLL (childLH (childHL (childHH e24PhiBelowRoot)))

end CertificateCells9ae3b0f784

open CertificateCells9ae3b0f784
namespace CoverCertificated58a87e9b8






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificated58a87e9b8

theorem e24KC2PhiBelowLeaf32100 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3210) = true := by
  exact CoverCertificated58a87e9b8.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32101 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells9614d1d005

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3210` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3210 : AngleCell :=
  childLL (childLH (childHL (childHH e24PhiBelowRoot)))

end CertificateCells9614d1d005

open CertificateCells9614d1d005
namespace CoverCertificate3ddf17b582






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate3ddf17b582

theorem e24KC2PhiBelowLeaf32101 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3210) = true := by
  exact CoverCertificate3ddf17b582.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32102 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells27f26686ef

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3210` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3210 : AngleCell :=
  childLL (childLH (childHL (childHH e24PhiBelowRoot)))

end CertificateCells27f26686ef

open CertificateCells27f26686ef
namespace CoverCertificated26b7e0a55






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificated26b7e0a55

theorem e24KC2PhiBelowLeaf32102 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3210) = true := by
  exact CoverCertificated26b7e0a55.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32103 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells9dc2121909

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3210` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3210 : AngleCell :=
  childLL (childLH (childHL (childHH e24PhiBelowRoot)))

end CertificateCells9dc2121909

open CertificateCells9dc2121909
namespace CoverCertificatea04fbf8169






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatea04fbf8169

theorem e24KC2PhiBelowLeaf32103 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3210) = true := by
  exact CoverCertificatea04fbf8169.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32110 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsc35310d566

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3211` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3211 : AngleCell :=
  childLH (childLH (childHL (childHH e24PhiBelowRoot)))

end CertificateCellsc35310d566

open CertificateCellsc35310d566
namespace CoverCertificate3ba43c403b














private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 7 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 7 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 7 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 7 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate3ba43c403b

theorem e24KC2PhiBelowLeaf32110 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3211) = true := by
  exact CoverCertificate3ba43c403b.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32111 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa20e4da390

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3211` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3211 : AngleCell :=
  childLH (childLH (childHL (childHH e24PhiBelowRoot)))

end CertificateCellsa20e4da390

open CertificateCellsa20e4da390
namespace CoverCertificate1430173dea






















private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 7 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 7 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 7 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 7 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 7 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 7 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 7 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 7 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate1430173dea

theorem e24KC2PhiBelowLeaf32111 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3211) = true := by
  exact CoverCertificate1430173dea.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32112 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells3a90cbf635

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3211` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3211 : AngleCell :=
  childLH (childLH (childHL (childHH e24PhiBelowRoot)))

end CertificateCells3a90cbf635

open CertificateCells3a90cbf635
namespace CoverCertificate2756e7c1ab














private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 7 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 7 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 7 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 7 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate2756e7c1ab

theorem e24KC2PhiBelowLeaf32112 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3211) = true := by
  exact CoverCertificate2756e7c1ab.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32113 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells214a11de68

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3211` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3211 : AngleCell :=
  childLH (childLH (childHL (childHH e24PhiBelowRoot)))

end CertificateCells214a11de68

open CertificateCells214a11de68
namespace CoverCertificate8e43edbf8f






















private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 7 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 7 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 7 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 7 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 7 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 7 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 7 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 7 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate8e43edbf8f

theorem e24KC2PhiBelowLeaf32113 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3211) = true := by
  exact CoverCertificate8e43edbf8f.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32120 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells032b91f5bc

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3212` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3212 : AngleCell :=
  childHL (childLH (childHL (childHH e24PhiBelowRoot)))

end CertificateCells032b91f5bc

open CertificateCells032b91f5bc
namespace CoverCertificated1acdb7cc1






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificated1acdb7cc1

theorem e24KC2PhiBelowLeaf32120 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3212) = true := by
  exact CoverCertificated1acdb7cc1.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32121 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsaa8e493e23

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3212` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3212 : AngleCell :=
  childHL (childLH (childHL (childHH e24PhiBelowRoot)))

end CertificateCellsaa8e493e23

open CertificateCellsaa8e493e23
namespace CoverCertificated9d4fcb914






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificated9d4fcb914

theorem e24KC2PhiBelowLeaf32121 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3212) = true := by
  exact CoverCertificated9d4fcb914.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32122 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells6bd715f340

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3212` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3212 : AngleCell :=
  childHL (childLH (childHL (childHH e24PhiBelowRoot)))

end CertificateCells6bd715f340

open CertificateCells6bd715f340
namespace CoverCertificate18d654774a






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate18d654774a

theorem e24KC2PhiBelowLeaf32122 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3212) = true := by
  exact CoverCertificate18d654774a.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32123 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa228f232aa

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3212` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3212 : AngleCell :=
  childHL (childLH (childHL (childHH e24PhiBelowRoot)))

end CertificateCellsa228f232aa

open CertificateCellsa228f232aa
namespace CoverCertificate3c1ddcbe4a






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate3c1ddcbe4a

theorem e24KC2PhiBelowLeaf32123 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3212) = true := by
  exact CoverCertificate3c1ddcbe4a.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32130 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells4dea68b576

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3213` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3213 : AngleCell :=
  childHH (childLH (childHL (childHH e24PhiBelowRoot)))

end CertificateCells4dea68b576

open CertificateCells4dea68b576
namespace CoverCertificatecaa9842c01














private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 7 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 7 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 7 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 7 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatecaa9842c01

theorem e24KC2PhiBelowLeaf32130 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3213) = true := by
  exact CoverCertificatecaa9842c01.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32131 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells3e707fd6af

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3213` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3213 : AngleCell :=
  childHH (childLH (childHL (childHH e24PhiBelowRoot)))

end CertificateCells3e707fd6af

open CertificateCells3e707fd6af
namespace CoverCertificate8a64f55483






















private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 7 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 7 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 7 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 7 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 7 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 7 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 7 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 7 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate8a64f55483

theorem e24KC2PhiBelowLeaf32131 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3213) = true := by
  exact CoverCertificate8a64f55483.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32132 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells46e40ef0a9

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3213` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3213 : AngleCell :=
  childHH (childLH (childHL (childHH e24PhiBelowRoot)))

end CertificateCells46e40ef0a9

open CertificateCells46e40ef0a9
namespace CoverCertificatea45749320c


















private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 7 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 7 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 7 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 7 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 7 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 7 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 7 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 7 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatea45749320c

theorem e24KC2PhiBelowLeaf32132 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3213) = true := by
  exact CoverCertificatea45749320c.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32133 remaining=9 kind=F reason=ADAPTIVE.
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells9651c4a476

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3213` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3213 : AngleCell :=
  childHH (childLH (childHL (childHH e24PhiBelowRoot)))

end CertificateCells9651c4a476

open CertificateCells9651c4a476
namespace CoverCertificate96200cdbc3






















private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 7 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 7 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 7 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 7 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 7 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 7 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 7 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 7 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate96200cdbc3

theorem e24KC2PhiBelowLeaf32133 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3213) = true := by
  exact CoverCertificate96200cdbc3.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32200 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells2fa7cd8552

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3220` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3220 : AngleCell :=
  childLL (childHL (childHL (childHH e24PhiBelowRoot)))

end CertificateCells2fa7cd8552

open CertificateCells2fa7cd8552
theorem e24KC2PhiBelowLeaf32200 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3220) = true := by
  have h : ((childLL phiBelowCell3220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL phiBelowCell3220) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32201 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsec4b7eff4d

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3220` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3220 : AngleCell :=
  childLL (childHL (childHL (childHH e24PhiBelowRoot)))

end CertificateCellsec4b7eff4d

open CertificateCellsec4b7eff4d
theorem e24KC2PhiBelowLeaf32201 :
    adaptiveCoverCheck 9 (childLH phiBelowCell3220) = true := by
  have h : ((childLH phiBelowCell3220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLH phiBelowCell3220) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32202 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells434ca1e74d

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3220` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3220 : AngleCell :=
  childLL (childHL (childHL (childHH e24PhiBelowRoot)))

end CertificateCells434ca1e74d

open CertificateCells434ca1e74d
theorem e24KC2PhiBelowLeaf32202 :
    adaptiveCoverCheck 9 (childHL phiBelowCell3220) = true := by
  have h : ((childHL phiBelowCell3220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHL phiBelowCell3220) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32203 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells886952c236

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3220` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3220 : AngleCell :=
  childLL (childHL (childHL (childHH e24PhiBelowRoot)))

end CertificateCells886952c236

open CertificateCells886952c236
theorem e24KC2PhiBelowLeaf32203 :
    adaptiveCoverCheck 9 (childHH phiBelowCell3220) = true := by
  have h : ((childHH phiBelowCell3220)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childHH phiBelowCell3220) h

end PartE
end GerverSofa

end

end

end

section

/-! Generated E24KC2 kernel leaf. Discovery claim: PB path=32210 remaining=9 kind=T reason=R. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells969a7c12d6

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `3221` of the phi-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiBelowCell3221 : AngleCell :=
  childLH (childHL (childHL (childHH e24PhiBelowRoot)))

end CertificateCells969a7c12d6

open CertificateCells969a7c12d6
theorem e24KC2PhiBelowLeaf32210 :
    adaptiveCoverCheck 9 (childLL phiBelowCell3221) = true := by
  have h : ((childLL phiBelowCell3221)).rejected = true := by
    decide +kernel
  exact adaptiveCoverCheck_true_of_rejected 9 (childLL phiBelowCell3221) h

end PartE
end GerverSofa

end

end

end

section

/-! E24KC4 auto-tuned batched kernel certificates. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells7aa82bee5f

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1100` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1100 : AngleCell :=
  childLL (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))

end CertificateCells7aa82bee5f

open CertificateCells7aa82bee5f
namespace CoverCertificate1e0715601d














private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell01 (by decide +kernel)

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell10 (by decide +kernel)

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell11 (by decide +kernel)

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate1e0715601d

theorem e24KC2PhiAboveLeaf1100111 :
    adaptiveCoverCheck 9 (childLH (childLH (childLH phiAboveCell1100))) = true := by
  exact CoverCertificate1e0715601d.checkedRoot
namespace CoverCertificate645c2a2fa6


























private theorem checked010 : adaptiveCoverCheck 6 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 6 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 6 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 6 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell013 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 6 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 6 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 6 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 6 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 6 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 6 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 6 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 6 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell113 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell00 (by decide +kernel)

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate645c2a2fa6

theorem e24KC2PhiAboveLeaf1101000 :
    adaptiveCoverCheck 9 (childLL (childLL (childLL phiAboveCell1101))) = true := by
  exact CoverCertificate645c2a2fa6.checkedRoot
namespace CoverCertificate22a5b25f41






























private theorem checked000 : adaptiveCoverCheck 6 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 6 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 6 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 6 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 6 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 6 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 6 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 6 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell013 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 6 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 6 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 6 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 6 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 6 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 6 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 6 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 6 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell113 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate22a5b25f41

theorem e24KC2PhiAboveLeaf1101001 :
    adaptiveCoverCheck 9 (childLH (childLL (childLL phiAboveCell1101))) = true := by
  exact CoverCertificate22a5b25f41.checkedRoot
namespace CoverCertificate052935fbc6










































private theorem checked1010 : adaptiveCoverCheck 5 cell1010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1010 (by decide +kernel)

private theorem checked1011 : adaptiveCoverCheck 5 cell1011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1011 (by decide +kernel)

private theorem checked1012 : adaptiveCoverCheck 5 cell1012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1012 (by decide +kernel)

private theorem checked1013 : adaptiveCoverCheck 5 cell1013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1013 (by decide +kernel)

private theorem checked1100 : adaptiveCoverCheck 5 cell1100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1100 (by decide +kernel)

private theorem checked1101 : adaptiveCoverCheck 5 cell1101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1101 (by decide +kernel)

private theorem checked1102 : adaptiveCoverCheck 5 cell1102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1102 (by decide +kernel)

private theorem checked1103 : adaptiveCoverCheck 5 cell1103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1103 (by decide +kernel)

private theorem checked1110 : adaptiveCoverCheck 5 cell1110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1110 (by decide +kernel)

private theorem checked1111 : adaptiveCoverCheck 5 cell1111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1111 (by decide +kernel)

private theorem checked1112 : adaptiveCoverCheck 5 cell1112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1112 (by decide +kernel)

private theorem checked1113 : adaptiveCoverCheck 5 cell1113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1113 (by decide +kernel)

private theorem checked000 : adaptiveCoverCheck 6 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 6 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 6 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 6 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 6 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 6 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 6 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 6 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell013 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 6 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 6 cell101 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell101
    checked1010 checked1011 checked1012 checked1013

private theorem checked102 : adaptiveCoverCheck 6 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 6 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 6 cell110 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell110
    checked1100 checked1101 checked1102 checked1103

private theorem checked111 : adaptiveCoverCheck 6 cell111 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell111
    checked1110 checked1111 checked1112 checked1113

private theorem checked112 : adaptiveCoverCheck 6 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 6 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell113 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate052935fbc6

theorem e24KC2PhiAboveLeaf1101010 :
    adaptiveCoverCheck 9 (childLL (childLH (childLL phiAboveCell1101))) = true := by
  exact CoverCertificate052935fbc6.checkedRoot
namespace CoverCertificateda1b0b5031






































































private theorem checked11110 : adaptiveCoverCheck 4 cell11110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell11110 (by decide +kernel)

private theorem checked11111 : adaptiveCoverCheck 4 cell11111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell11111 (by decide +kernel)

private theorem checked11112 : adaptiveCoverCheck 4 cell11112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell11112 (by decide +kernel)

private theorem checked11113 : adaptiveCoverCheck 4 cell11113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell11113 (by decide +kernel)

private theorem checked0000 : adaptiveCoverCheck 5 cell0000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell0000 (by decide +kernel)

private theorem checked0001 : adaptiveCoverCheck 5 cell0001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell0001 (by decide +kernel)

private theorem checked0002 : adaptiveCoverCheck 5 cell0002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell0002 (by decide +kernel)

private theorem checked0003 : adaptiveCoverCheck 5 cell0003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell0003 (by decide +kernel)

private theorem checked0010 : adaptiveCoverCheck 5 cell0010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell0010 (by decide +kernel)

private theorem checked0011 : adaptiveCoverCheck 5 cell0011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell0011 (by decide +kernel)

private theorem checked0012 : adaptiveCoverCheck 5 cell0012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell0012 (by decide +kernel)

private theorem checked0013 : adaptiveCoverCheck 5 cell0013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell0013 (by decide +kernel)

private theorem checked0100 : adaptiveCoverCheck 5 cell0100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell0100 (by decide +kernel)

private theorem checked0101 : adaptiveCoverCheck 5 cell0101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell0101 (by decide +kernel)

private theorem checked0102 : adaptiveCoverCheck 5 cell0102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell0102 (by decide +kernel)

private theorem checked0103 : adaptiveCoverCheck 5 cell0103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell0103 (by decide +kernel)

private theorem checked0110 : adaptiveCoverCheck 5 cell0110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell0110 (by decide +kernel)

private theorem checked0111 : adaptiveCoverCheck 5 cell0111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell0111 (by decide +kernel)

private theorem checked0112 : adaptiveCoverCheck 5 cell0112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell0112 (by decide +kernel)

private theorem checked0113 : adaptiveCoverCheck 5 cell0113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell0113 (by decide +kernel)

private theorem checked1000 : adaptiveCoverCheck 5 cell1000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1000 (by decide +kernel)

private theorem checked1001 : adaptiveCoverCheck 5 cell1001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1001 (by decide +kernel)

private theorem checked1002 : adaptiveCoverCheck 5 cell1002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1002 (by decide +kernel)

private theorem checked1003 : adaptiveCoverCheck 5 cell1003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1003 (by decide +kernel)

private theorem checked1010 : adaptiveCoverCheck 5 cell1010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1010 (by decide +kernel)

private theorem checked1011 : adaptiveCoverCheck 5 cell1011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1011 (by decide +kernel)

private theorem checked1012 : adaptiveCoverCheck 5 cell1012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1012 (by decide +kernel)

private theorem checked1013 : adaptiveCoverCheck 5 cell1013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1013 (by decide +kernel)

private theorem checked1100 : adaptiveCoverCheck 5 cell1100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1100 (by decide +kernel)

private theorem checked1101 : adaptiveCoverCheck 5 cell1101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1101 (by decide +kernel)

private theorem checked1102 : adaptiveCoverCheck 5 cell1102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1102 (by decide +kernel)

private theorem checked1103 : adaptiveCoverCheck 5 cell1103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1103 (by decide +kernel)

private theorem checked1110 : adaptiveCoverCheck 5 cell1110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1110 (by decide +kernel)

private theorem checked1111 : adaptiveCoverCheck 5 cell1111 = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cell1111
    checked11110 checked11111 checked11112 checked11113

private theorem checked1112 : adaptiveCoverCheck 5 cell1112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1112 (by decide +kernel)

private theorem checked1113 : adaptiveCoverCheck 5 cell1113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1113 (by decide +kernel)

private theorem checked000 : adaptiveCoverCheck 6 cell000 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell000
    checked0000 checked0001 checked0002 checked0003

private theorem checked001 : adaptiveCoverCheck 6 cell001 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell001
    checked0010 checked0011 checked0012 checked0013

private theorem checked002 : adaptiveCoverCheck 6 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 6 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 6 cell010 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell010
    checked0100 checked0101 checked0102 checked0103

private theorem checked011 : adaptiveCoverCheck 6 cell011 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell011
    checked0110 checked0111 checked0112 checked0113

private theorem checked012 : adaptiveCoverCheck 6 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 6 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell013 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 6 cell100 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell100
    checked1000 checked1001 checked1002 checked1003

private theorem checked101 : adaptiveCoverCheck 6 cell101 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell101
    checked1010 checked1011 checked1012 checked1013

private theorem checked102 : adaptiveCoverCheck 6 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 6 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 6 cell110 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell110
    checked1100 checked1101 checked1102 checked1103

private theorem checked111 : adaptiveCoverCheck 6 cell111 = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cell111
    checked1110 checked1111 checked1112 checked1113

private theorem checked112 : adaptiveCoverCheck 6 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 6 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell113 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 7 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 7 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 7 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 7 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 7 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 7 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 7 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 7 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell13 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 7 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 7 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 7 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 7 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 7 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 7 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificateda1b0b5031

theorem e24KC2PhiAboveLeaf1101011 :
    adaptiveCoverCheck 9 (childLH (childLH (childLL phiAboveCell1101))) = true := by
  exact CoverCertificateda1b0b5031.checkedRoot
namespace CoverCertificate87253a3a53






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate87253a3a53

theorem e24KC2PhiAboveLeaf1101012 :
    adaptiveCoverCheck 9 (childHL (childLH (childLL phiAboveCell1101))) = true := by
  exact CoverCertificate87253a3a53.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-! E24KC4 auto-tuned batched kernel certificates. -/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsf8d478d36a

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))

end CertificateCellsf8d478d36a

open CertificateCellsf8d478d36a
namespace CoverCertificate3f791a2e61






private theorem checked0 : adaptiveCoverCheck 8 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 8 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 8 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 8 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 8 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 9 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 8 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate3f791a2e61

theorem e24KC2PhiAboveLeaf1101013 :
    adaptiveCoverCheck 9 (childHH (childLH (childLL phiAboveCell1101))) = true := by
  exact CoverCertificate3f791a2e61.checkedRoot

end PartE
end GerverSofa

end

end

end
