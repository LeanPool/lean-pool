/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Semantics.Batch001
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Batch015
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Batch016
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Batch017
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Batch024

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Batch026
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Batch028
public import LeanPool.MovingSofa.GerverSofa.KernelOnly.PartE.Certificates.Batch034
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC6ThetaBelowReconstruct`.
* `KernelOnly.PartE.PhiAbove.Leaf00025`.
* `KernelOnly.PartE.PhiAbove.Leaf00026`.
* `KernelOnly.PartE.PhiAbove.Leaf00027`.
* `KernelOnly.PartE.PhiAbove.Leaf00028`.
* `KernelOnly.PartE.PhiAbove.Join00029`.
* `KernelOnly.PartE.PhiAbove.Leaf00032`.
* `KernelOnly.PartE.PhiAbove.Leaf00033`.
* `KernelOnly.PartE.PhiAbove.Leaf00034`.
* `KernelOnly.PartE.PhiAbove.Leaf00035`.
* `KernelOnly.PartE.PhiAbove.Join00036`.
* `KernelOnly.PartE.PhiAbove.Leaf00038`.
* `KernelOnly.PartE.PhiAbove.Leaf00039`.
* `KernelOnly.PartE.PhiAbove.Leaf00040`.
* `KernelOnly.PartE.PhiAbove.Leaf00041`.
* `KernelOnly.PartE.PhiAbove.Join00042`.
* `KernelOnly.PartE.PhiAbove.Leaf00043`.
* `KernelOnly.PartE.PhiAbove.Leaf00044`.
* `KernelOnly.PartE.PhiAbove.Join00045`.
* `KernelOnly.PartE.PhiAbove.Leaf00046`.
* `KernelOnly.PartE.PhiAbove.Leaf00047`.
* `KernelOnly.PartE.PhiAbove.Join00048`.
* `KernelOnly.PartE.PhiAbove.Leaf00052`.
* `KernelOnly.PartE.PhiAbove.Leaf00053`.
* `KernelOnly.PartE.PhiAbove.Leaf00054`.
* `KernelOnly.PartE.PhiAbove.Leaf00055`.
* `KernelOnly.PartE.PhiAbove.Join00056`.
* `KernelOnly.PartE.PhiAbove.Leaf00058`.
* `KernelOnly.PartE.PhiAbove.Leaf00059`.
* `KernelOnly.PartE.PhiAbove.Leaf00060`.
* `KernelOnly.PartE.PhiAbove.Leaf00061`.
* `KernelOnly.PartE.PhiAbove.Join00062`.
* `KernelOnly.PartE.PhiAbove.Leaf00063`.
* `KernelOnly.PartE.PhiAbove.Leaf00064`.
* `KernelOnly.PartE.PhiAbove.Join00065`.
* `KernelOnly.PartE.PhiAbove.Leaf00067`.
* `KernelOnly.PartE.PhiAbove.Leaf00068`.
* `KernelOnly.PartE.PhiAbove.Leaf00069`.
* `KernelOnly.PartE.PhiAbove.Leaf00070`.
* `KernelOnly.PartE.PhiAbove.Join00071`.
* `KernelOnly.PartE.PhiAbove.Leaf00072`.
* `KernelOnly.PartE.PhiAbove.Leaf00073`.
* `KernelOnly.PartE.PhiAbove.Join00074`.
* `KernelOnly.PartE.PhiAbove.Leaf00075`.
* `KernelOnly.PartE.PhiAbove.Leaf00076`.
* `KernelOnly.PartE.PhiAbove.Join00077`.
* `KernelOnly.PartE.PhiAbove.Leaf00081`.
-/

@[expose] public section

noncomputable section

namespace GerverSofa.PartE.CoverCertificatefdb2e5aa72

private abbrev cellRoot : AngleCell :=
  (childLL (childLL (childLL (childLL (childLH (childLL (childLH (childLH (childLL (childLH
    (childLH (e24PhiAboveRoot))))))))))))


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

end GerverSofa.PartE.CoverCertificatefdb2e5aa72

namespace GerverSofa.PartE.CoverCertificatefeab482a88

private abbrev cellRoot : AngleCell :=
  (childLH (childLL (childLL (childLL (childLH (childLL (childLH (childLH (childLL (childLH
    (childLH (e24PhiAboveRoot))))))))))))


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

end GerverSofa.PartE.CoverCertificatefeab482a88

namespace GerverSofa.PartE.CoverCertificatebf967458da

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childLL (childLL (childLH (childLL (childLH (childLH (childLL (childLH
    (childLH (e24PhiAboveRoot))))))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatebf967458da

namespace GerverSofa.PartE.CoverCertificate0ae56857be

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childLL (childLL (childLH (childLL (childLH (childLH (childLL (childLH
    (childLH (e24PhiAboveRoot))))))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate0ae56857be

namespace GerverSofa.PartE.CoverCertificate2ea7c8ddef

private abbrev cellRoot : AngleCell :=
  (childLL (childLL (childLH (childLL (childLL (childLH (childLL (childLH (childLH (childLL
    (childLH (childLH (e24PhiAboveRoot)))))))))))))


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

end GerverSofa.PartE.CoverCertificate2ea7c8ddef

namespace GerverSofa.PartE.CoverCertificate75cf82dc9c

private abbrev cellRoot : AngleCell :=
  (childLH (childLL (childLH (childLL (childLL (childLH (childLL (childLH (childLH (childLL
    (childLH (childLH (e24PhiAboveRoot)))))))))))))


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

end GerverSofa.PartE.CoverCertificate75cf82dc9c

namespace GerverSofa.PartE.CoverCertificate94c7306624

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childLH (childLL (childLL (childLH (childLL (childLH (childLH (childLL
    (childLH (childLH (e24PhiAboveRoot)))))))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate94c7306624

namespace GerverSofa.PartE.CoverCertificatefc8969e3d2

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childLH (childLL (childLL (childLH (childLL (childLH (childLH (childLL
    (childLH (childLH (e24PhiAboveRoot)))))))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatefc8969e3d2

namespace GerverSofa.PartE.CoverCertificate0773e6576d

private abbrev cellRoot : AngleCell :=
  (childLL (childLH (childLH (childLL (childLL (childLH (childLL (childLH (childLH (childLL
    (childLH (childLH (e24PhiAboveRoot)))))))))))))


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


private abbrev cell030 : AngleCell :=
  childLL cell03


private abbrev cell031 : AngleCell :=
  childLH cell03


private abbrev cell032 : AngleCell :=
  childHL cell03


private abbrev cell033 : AngleCell :=
  childHH cell03


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


private abbrev cell120 : AngleCell :=
  childLL cell12


private abbrev cell121 : AngleCell :=
  childLH cell12


private abbrev cell122 : AngleCell :=
  childHL cell12


private abbrev cell123 : AngleCell :=
  childHH cell12


private abbrev cell130 : AngleCell :=
  childLL cell13


private abbrev cell131 : AngleCell :=
  childLH cell13


private abbrev cell132 : AngleCell :=
  childHL cell13


private abbrev cell133 : AngleCell :=
  childHH cell13

end GerverSofa.PartE.CoverCertificate0773e6576d

namespace GerverSofa.PartE.CoverCertificate6cd163be74

private abbrev cellRoot : AngleCell :=
  (childLH (childLH (childLH (childLL (childLL (childLH (childLL (childLH (childLH (childLL
    (childLH (childLH (e24PhiAboveRoot)))))))))))))


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


private abbrev cell020 : AngleCell :=
  childLL cell02


private abbrev cell021 : AngleCell :=
  childLH cell02


private abbrev cell022 : AngleCell :=
  childHL cell02


private abbrev cell023 : AngleCell :=
  childHH cell02


private abbrev cell030 : AngleCell :=
  childLL cell03


private abbrev cell031 : AngleCell :=
  childLH cell03


private abbrev cell032 : AngleCell :=
  childHL cell03


private abbrev cell033 : AngleCell :=
  childHH cell03


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


private abbrev cell120 : AngleCell :=
  childLL cell12


private abbrev cell121 : AngleCell :=
  childLH cell12


private abbrev cell122 : AngleCell :=
  childHL cell12


private abbrev cell123 : AngleCell :=
  childHH cell12


private abbrev cell130 : AngleCell :=
  childLL cell13


private abbrev cell131 : AngleCell :=
  childLH cell13


private abbrev cell132 : AngleCell :=
  childHL cell13


private abbrev cell133 : AngleCell :=
  childHH cell13

end GerverSofa.PartE.CoverCertificate6cd163be74

namespace GerverSofa.PartE.CoverCertificate105a276d33

private abbrev cellRoot : AngleCell :=
  (childHL (childLH (childLH (childLL (childLL (childLH (childLL (childLH (childLH (childLL
    (childLH (childLH (e24PhiAboveRoot)))))))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate105a276d33

namespace GerverSofa.PartE.CoverCertificate7b7ada8a92

private abbrev cellRoot : AngleCell :=
  (childHH (childLH (childLH (childLL (childLL (childLH (childLL (childLH (childLH (childLL
    (childLH (childLH (e24PhiAboveRoot)))))))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate7b7ada8a92

namespace GerverSofa.PartE.CoverCertificate216e1a86b9

private abbrev cellRoot : AngleCell :=
  (childHL (childLH (childLL (childLL (childLH (childLL (childLH (childLH (childLL (childLH
    (childLH (e24PhiAboveRoot))))))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate216e1a86b9

namespace GerverSofa.PartE.CoverCertificatecbce86617c

private abbrev cellRoot : AngleCell :=
  (childHH (childLH (childLL (childLL (childLH (childLL (childLH (childLH (childLL (childLH
    (childLH (e24PhiAboveRoot))))))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatecbce86617c

namespace GerverSofa.PartE.CoverCertificate5b9a8c2094

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childLL (childLH (childLL (childLH (childLH (childLL (childLH (childLH
    (e24PhiAboveRoot)))))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate5b9a8c2094

namespace GerverSofa.PartE.CoverCertificatee500b98dc1

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childLL (childLH (childLL (childLH (childLH (childLL (childLH (childLH
    (e24PhiAboveRoot)))))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatee500b98dc1

namespace GerverSofa.PartE.CoverCertificatec4a9c16244

private abbrev cellRoot : AngleCell :=
  (childLL (childLL (childLL (childLH (childLL (childLH (childLL (childLH (childLH (childLL
    (childLH (childLH (e24PhiAboveRoot)))))))))))))


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


private abbrev cell020 : AngleCell :=
  childLL cell02


private abbrev cell021 : AngleCell :=
  childLH cell02


private abbrev cell022 : AngleCell :=
  childHL cell02


private abbrev cell023 : AngleCell :=
  childHH cell02


private abbrev cell030 : AngleCell :=
  childLL cell03


private abbrev cell031 : AngleCell :=
  childLH cell03


private abbrev cell032 : AngleCell :=
  childHL cell03


private abbrev cell033 : AngleCell :=
  childHH cell03


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


private abbrev cell120 : AngleCell :=
  childLL cell12


private abbrev cell121 : AngleCell :=
  childLH cell12


private abbrev cell122 : AngleCell :=
  childHL cell12


private abbrev cell123 : AngleCell :=
  childHH cell12


private abbrev cell130 : AngleCell :=
  childLL cell13


private abbrev cell131 : AngleCell :=
  childLH cell13


private abbrev cell132 : AngleCell :=
  childHL cell13


private abbrev cell133 : AngleCell :=
  childHH cell13

end GerverSofa.PartE.CoverCertificatec4a9c16244

namespace GerverSofa.PartE.CoverCertificated58785d59b

private abbrev cellRoot : AngleCell :=
  (childLH (childLL (childLL (childLH (childLL (childLH (childLL (childLH (childLH (childLL
    (childLH (childLH (e24PhiAboveRoot)))))))))))))


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


private abbrev cell020 : AngleCell :=
  childLL cell02


private abbrev cell021 : AngleCell :=
  childLH cell02


private abbrev cell022 : AngleCell :=
  childHL cell02


private abbrev cell023 : AngleCell :=
  childHH cell02


private abbrev cell030 : AngleCell :=
  childLL cell03


private abbrev cell031 : AngleCell :=
  childLH cell03


private abbrev cell032 : AngleCell :=
  childHL cell03


private abbrev cell033 : AngleCell :=
  childHH cell03


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


private abbrev cell120 : AngleCell :=
  childLL cell12


private abbrev cell121 : AngleCell :=
  childLH cell12


private abbrev cell122 : AngleCell :=
  childHL cell12


private abbrev cell123 : AngleCell :=
  childHH cell12


private abbrev cell130 : AngleCell :=
  childLL cell13


private abbrev cell131 : AngleCell :=
  childLH cell13


private abbrev cell132 : AngleCell :=
  childHL cell13


private abbrev cell133 : AngleCell :=
  childHH cell13

end GerverSofa.PartE.CoverCertificated58785d59b

namespace GerverSofa.PartE.CoverCertificate770e3357d2

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childLL (childLH (childLL (childLH (childLL (childLH (childLH (childLL
    (childLH (childLH (e24PhiAboveRoot)))))))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate770e3357d2

namespace GerverSofa.PartE.CoverCertificate4042eb5094

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childLL (childLH (childLL (childLH (childLL (childLH (childLH (childLL
    (childLH (childLH (e24PhiAboveRoot)))))))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate4042eb5094

namespace GerverSofa.PartE.CoverCertificate9283dd1f18

private abbrev cellRoot : AngleCell :=
  (childLL (childLH (childLL (childLH (childLL (childLH (childLL (childLH (childLH (childLL
    (childLH (childLH (e24PhiAboveRoot)))))))))))))


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


private abbrev cell020 : AngleCell :=
  childLL cell02


private abbrev cell021 : AngleCell :=
  childLH cell02


private abbrev cell022 : AngleCell :=
  childHL cell02


private abbrev cell023 : AngleCell :=
  childHH cell02


private abbrev cell030 : AngleCell :=
  childLL cell03


private abbrev cell031 : AngleCell :=
  childLH cell03


private abbrev cell032 : AngleCell :=
  childHL cell03


private abbrev cell033 : AngleCell :=
  childHH cell03


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


private abbrev cell120 : AngleCell :=
  childLL cell12


private abbrev cell121 : AngleCell :=
  childLH cell12


private abbrev cell122 : AngleCell :=
  childHL cell12


private abbrev cell123 : AngleCell :=
  childHH cell12


private abbrev cell130 : AngleCell :=
  childLL cell13


private abbrev cell131 : AngleCell :=
  childLH cell13


private abbrev cell132 : AngleCell :=
  childHL cell13


private abbrev cell133 : AngleCell :=
  childHH cell13


private abbrev cell310 : AngleCell :=
  childLL cell31


private abbrev cell311 : AngleCell :=
  childLH cell31


private abbrev cell312 : AngleCell :=
  childHL cell31


private abbrev cell313 : AngleCell :=
  childHH cell31

end GerverSofa.PartE.CoverCertificate9283dd1f18

namespace GerverSofa.PartE.CoverCertificate5607aeacca

private abbrev cellRoot : AngleCell :=
  (childLH (childLH (childLL (childLH (childLL (childLH (childLL (childLH (childLH (childLL
    (childLH (childLH (e24PhiAboveRoot)))))))))))))


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


private abbrev cell020 : AngleCell :=
  childLL cell02


private abbrev cell021 : AngleCell :=
  childLH cell02


private abbrev cell022 : AngleCell :=
  childHL cell02


private abbrev cell023 : AngleCell :=
  childHH cell02


private abbrev cell030 : AngleCell :=
  childLL cell03


private abbrev cell031 : AngleCell :=
  childLH cell03


private abbrev cell032 : AngleCell :=
  childHL cell03


private abbrev cell033 : AngleCell :=
  childHH cell03


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


private abbrev cell120 : AngleCell :=
  childLL cell12


private abbrev cell121 : AngleCell :=
  childLH cell12


private abbrev cell122 : AngleCell :=
  childHL cell12


private abbrev cell123 : AngleCell :=
  childHH cell12


private abbrev cell200 : AngleCell :=
  childLL cell20


private abbrev cell201 : AngleCell :=
  childLH cell20


private abbrev cell202 : AngleCell :=
  childHL cell20


private abbrev cell203 : AngleCell :=
  childHH cell20

end GerverSofa.PartE.CoverCertificate5607aeacca

namespace GerverSofa.PartE.CoverCertificate093986cbf5

private abbrev cellRoot : AngleCell :=
  (childHL (childLH (childLL (childLH (childLL (childLH (childLL (childLH (childLH (childLL
    (childLH (childLH (e24PhiAboveRoot)))))))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate093986cbf5

namespace GerverSofa.PartE.CoverCertificate4478c1ce2d

private abbrev cellRoot : AngleCell :=
  (childHH (childLH (childLL (childLH (childLL (childLH (childLL (childLH (childLH (childLL
    (childLH (childLH (e24PhiAboveRoot)))))))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate4478c1ce2d

namespace GerverSofa.PartE.CoverCertificate52d1f78193

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childLH (childLL (childLH (childLL (childLH (childLH (childLL (childLH
    (childLH (e24PhiAboveRoot))))))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate52d1f78193

namespace GerverSofa.PartE.CoverCertificate263f6f95b0

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childLH (childLL (childLH (childLL (childLH (childLH (childLL (childLH
    (childLH (e24PhiAboveRoot))))))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate263f6f95b0

namespace GerverSofa.PartE.CoverCertificatefad4f5904e

private abbrev cellRoot : AngleCell :=
  (childLL (childLH (childLH (childLL (childLH (childLL (childLH (childLH (childLL (childLH
    (childLH (e24PhiAboveRoot))))))))))))


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


private abbrev cell020 : AngleCell :=
  childLL cell02


private abbrev cell021 : AngleCell :=
  childLH cell02


private abbrev cell022 : AngleCell :=
  childHL cell02


private abbrev cell023 : AngleCell :=
  childHH cell02


private abbrev cell030 : AngleCell :=
  childLL cell03


private abbrev cell031 : AngleCell :=
  childLH cell03


private abbrev cell032 : AngleCell :=
  childHL cell03


private abbrev cell033 : AngleCell :=
  childHH cell03


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


private abbrev cell120 : AngleCell :=
  childLL cell12


private abbrev cell121 : AngleCell :=
  childLH cell12


private abbrev cell122 : AngleCell :=
  childHL cell12


private abbrev cell123 : AngleCell :=
  childHH cell12


private abbrev cell130 : AngleCell :=
  childLL cell13


private abbrev cell131 : AngleCell :=
  childLH cell13


private abbrev cell132 : AngleCell :=
  childHL cell13


private abbrev cell133 : AngleCell :=
  childHH cell13


private abbrev cell0000 : AngleCell :=
  childLL cell000


private abbrev cell0001 : AngleCell :=
  childLH cell000


private abbrev cell0002 : AngleCell :=
  childHL cell000


private abbrev cell0003 : AngleCell :=
  childHH cell000

end GerverSofa.PartE.CoverCertificatefad4f5904e

namespace GerverSofa.PartE.CoverCertificatec88446cc5e

private abbrev cellRoot : AngleCell :=
  (childLH (childLH (childLH (childLL (childLH (childLL (childLH (childLH (childLL (childLH
    (childLH (e24PhiAboveRoot))))))))))))


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


private abbrev cell020 : AngleCell :=
  childLL cell02


private abbrev cell021 : AngleCell :=
  childLH cell02


private abbrev cell022 : AngleCell :=
  childHL cell02


private abbrev cell023 : AngleCell :=
  childHH cell02


private abbrev cell030 : AngleCell :=
  childLL cell03


private abbrev cell031 : AngleCell :=
  childLH cell03


private abbrev cell032 : AngleCell :=
  childHL cell03


private abbrev cell033 : AngleCell :=
  childHH cell03


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


private abbrev cell120 : AngleCell :=
  childLL cell12


private abbrev cell121 : AngleCell :=
  childLH cell12


private abbrev cell122 : AngleCell :=
  childHL cell12


private abbrev cell123 : AngleCell :=
  childHH cell12


private abbrev cell130 : AngleCell :=
  childLL cell13


private abbrev cell131 : AngleCell :=
  childLH cell13


private abbrev cell132 : AngleCell :=
  childHL cell13


private abbrev cell133 : AngleCell :=
  childHH cell13


private abbrev cell200 : AngleCell :=
  childLL cell20


private abbrev cell201 : AngleCell :=
  childLH cell20


private abbrev cell202 : AngleCell :=
  childHL cell20


private abbrev cell203 : AngleCell :=
  childHH cell20


private abbrev cell210 : AngleCell :=
  childLL cell21


private abbrev cell211 : AngleCell :=
  childLH cell21


private abbrev cell212 : AngleCell :=
  childHL cell21


private abbrev cell213 : AngleCell :=
  childHH cell21


private abbrev cell300 : AngleCell :=
  childLL cell30


private abbrev cell301 : AngleCell :=
  childLH cell30


private abbrev cell302 : AngleCell :=
  childHL cell30


private abbrev cell303 : AngleCell :=
  childHH cell30


private abbrev cell310 : AngleCell :=
  childLL cell31


private abbrev cell311 : AngleCell :=
  childLH cell31


private abbrev cell312 : AngleCell :=
  childHL cell31


private abbrev cell313 : AngleCell :=
  childHH cell31

end GerverSofa.PartE.CoverCertificatec88446cc5e

namespace GerverSofa.PartE.CoverCertificate8053b84bb6

private abbrev cellRoot : AngleCell :=
  (childHL (childLH (childLH (childLL (childLH (childLL (childLH (childLH (childLL (childLH
    (childLH (e24PhiAboveRoot))))))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate8053b84bb6

namespace GerverSofa.PartE.CoverCertificatea83bf6868e

private abbrev cellRoot : AngleCell :=
  (childHH (childLH (childLH (childLL (childLH (childLL (childLH (childLH (childLL (childLH
    (childLH (e24PhiAboveRoot))))))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatea83bf6868e

namespace GerverSofa.PartE.CoverCertificatec458632307

private abbrev cellRoot : AngleCell :=
  (childHL (childLH (childLL (childLH (childLL (childLH (childLH (childLL (childLH (childLH
    (e24PhiAboveRoot)))))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatec458632307

namespace GerverSofa.PartE.CoverCertificate5ac90060dc

private abbrev cellRoot : AngleCell :=
  (childHH (childLH (childLL (childLH (childLL (childLH (childLH (childLL (childLH (childLH
    (e24PhiAboveRoot)))))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate5ac90060dc

namespace GerverSofa.PartE.CoverCertificatee2e2523660

private abbrev cellRoot : AngleCell :=
  (childHL (childLL (childLH (childLL (childLH (childLH (childLL (childLH (childLH
    (e24PhiAboveRoot))))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificatee2e2523660

namespace GerverSofa.PartE.CoverCertificate2c610dcf32

private abbrev cellRoot : AngleCell :=
  (childHH (childLL (childLH (childLL (childLH (childLH (childLL (childLH (childLH
    (e24PhiAboveRoot))))))))))


private abbrev cell0 : AngleCell :=
  childLL cellRoot


private abbrev cell1 : AngleCell :=
  childLH cellRoot


private abbrev cell2 : AngleCell :=
  childHL cellRoot


private abbrev cell3 : AngleCell :=
  childHH cellRoot

end GerverSofa.PartE.CoverCertificate2c610dcf32

namespace GerverSofa.PartE.CoverCertificate7a43bce112

private abbrev cellRoot : AngleCell :=
  (childLL (childLL (childLL (childLH (childLH (childLL (childLH (childLH (childLL (childLH
    (childLH (e24PhiAboveRoot))))))))))))


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


private abbrev cell020 : AngleCell :=
  childLL cell02


private abbrev cell021 : AngleCell :=
  childLH cell02


private abbrev cell022 : AngleCell :=
  childHL cell02


private abbrev cell023 : AngleCell :=
  childHH cell02


private abbrev cell030 : AngleCell :=
  childLL cell03


private abbrev cell031 : AngleCell :=
  childLH cell03


private abbrev cell032 : AngleCell :=
  childHL cell03


private abbrev cell033 : AngleCell :=
  childHH cell03


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


private abbrev cell120 : AngleCell :=
  childLL cell12


private abbrev cell121 : AngleCell :=
  childLH cell12


private abbrev cell122 : AngleCell :=
  childHL cell12


private abbrev cell123 : AngleCell :=
  childHH cell12


private abbrev cell130 : AngleCell :=
  childLL cell13


private abbrev cell131 : AngleCell :=
  childLH cell13


private abbrev cell132 : AngleCell :=
  childHL cell13


private abbrev cell133 : AngleCell :=
  childHH cell13


private abbrev cell200 : AngleCell :=
  childLL cell20


private abbrev cell201 : AngleCell :=
  childLH cell20


private abbrev cell202 : AngleCell :=
  childHL cell20


private abbrev cell203 : AngleCell :=
  childHH cell20


private abbrev cell210 : AngleCell :=
  childLL cell21


private abbrev cell211 : AngleCell :=
  childLH cell21


private abbrev cell212 : AngleCell :=
  childHL cell21


private abbrev cell213 : AngleCell :=
  childHH cell21


private abbrev cell300 : AngleCell :=
  childLL cell30


private abbrev cell301 : AngleCell :=
  childLH cell30


private abbrev cell302 : AngleCell :=
  childHL cell30


private abbrev cell303 : AngleCell :=
  childHH cell30


private abbrev cell310 : AngleCell :=
  childLL cell31


private abbrev cell311 : AngleCell :=
  childLH cell31


private abbrev cell312 : AngleCell :=
  childHL cell31


private abbrev cell313 : AngleCell :=
  childHH cell31

end GerverSofa.PartE.CoverCertificate7a43bce112

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC6Theta Below Reconstruct
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells6754c8bb3e

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `1110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1110 : AngleCell :=
  childLL (childLH (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `1111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1111 : AngleCell :=
  childLH (childLH (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `1011` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1011 : AngleCell :=
  childLH (childLH (childLL (childLH e24ThetaBelowRoot)))
/-- Subcell `1100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1100 : AngleCell :=
  childLL (childLL (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `1001` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1001 : AngleCell :=
  childLH (childLL (childLL (childLH e24ThetaBelowRoot)))
/-- Subcell `1010` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1010 : AngleCell :=
  childLL (childLH (childLL (childLH e24ThetaBelowRoot)))
/-- Subcell `1112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1112 : AngleCell :=
  childHL (childLH (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `1113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1113 : AngleCell :=
  childHH (childLH (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `0101` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0101 : AngleCell :=
  childLH (childLL (childLH (childLL e24ThetaBelowRoot)))
/-- Subcell `0110` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0110 : AngleCell :=
  childLL (childLH (childLH (childLL e24ThetaBelowRoot)))
/-- Subcell `0111` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0111 : AngleCell :=
  childLH (childLH (childLH (childLL e24ThetaBelowRoot)))
/-- Subcell `1000` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1000 : AngleCell :=
  childLL (childLL (childLL (childLH e24ThetaBelowRoot)))
/-- Subcell `1003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1003 : AngleCell :=
  childHH (childLL (childLL (childLH e24ThetaBelowRoot)))
/-- Subcell `1012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1012 : AngleCell :=
  childHL (childLH (childLL (childLH e24ThetaBelowRoot)))
/-- Subcell `1013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1013 : AngleCell :=
  childHH (childLH (childLL (childLH e24ThetaBelowRoot)))
/-- Subcell `1102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1102 : AngleCell :=
  childHL (childLL (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `1103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1103 : AngleCell :=
  childHH (childLL (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `0003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0003 : AngleCell :=
  childHH (childLL (childLL (childLL e24ThetaBelowRoot)))
/-- Subcell `0010` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0010 : AngleCell :=
  childLL (childLH (childLL (childLL e24ThetaBelowRoot)))
/-- Subcell `0011` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0011 : AngleCell :=
  childLH (childLH (childLL (childLL e24ThetaBelowRoot)))
/-- Subcell `0012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0012 : AngleCell :=
  childHL (childLH (childLL (childLL e24ThetaBelowRoot)))
/-- Subcell `0013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0013 : AngleCell :=
  childHH (childLH (childLL (childLL e24ThetaBelowRoot)))
/-- Subcell `0100` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0100 : AngleCell :=
  childLL (childLL (childLH (childLL e24ThetaBelowRoot)))
/-- Subcell `0102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0102 : AngleCell :=
  childHL (childLL (childLH (childLL e24ThetaBelowRoot)))
/-- Subcell `0103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0103 : AngleCell :=
  childHH (childLL (childLH (childLL e24ThetaBelowRoot)))
/-- Subcell `0112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0112 : AngleCell :=
  childHL (childLH (childLH (childLL e24ThetaBelowRoot)))
/-- Subcell `0113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell0113 : AngleCell :=
  childHH (childLH (childLH (childLL e24ThetaBelowRoot)))
/-- Subcell `1002` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1002 : AngleCell :=
  childHL (childLL (childLL (childLH e24ThetaBelowRoot)))
/-- Subcell `1121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1121 : AngleCell :=
  childLH (childHL (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `1130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1130 : AngleCell :=
  childLL (childHH (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `1131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell1131 : AngleCell :=
  childLH (childHH (childLH (childLH e24ThetaBelowRoot)))
/-- Subcell `11012132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaBelowCell1101)))
/-- Subcell `11012133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11012133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaBelowCell1101)))
/-- Subcell `11013013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaBelowCell1101)))
/-- Subcell `11013021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaBelowCell1101)))
/-- Subcell `11013022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaBelowCell1101)))
/-- Subcell `11013023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaBelowCell1101)))
/-- Subcell `11013030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaBelowCell1101)))
/-- Subcell `11013031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaBelowCell1101)))
/-- Subcell `11013032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaBelowCell1101)))
/-- Subcell `11013033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaBelowCell1101)))
/-- Subcell `11013102` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaBelowCell1101)))
/-- Subcell `11013103` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaBelowCell1101)))
/-- Subcell `11013112` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaBelowCell1101)))
/-- Subcell `11013113` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaBelowCell1101)))
/-- Subcell `11013120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaBelowCell1101)))
/-- Subcell `11013121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaBelowCell1101)))
/-- Subcell `11013122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaBelowCell1101)))
/-- Subcell `11013123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaBelowCell1101)))
/-- Subcell `11013130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaBelowCell1101)))
/-- Subcell `11013131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaBelowCell1101)))
/-- Subcell `11013132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaBelowCell1101)))
/-- Subcell `11013133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11013133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaBelowCell1101)))
/-- Subcell `11102002` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaBelowCell1110)))
/-- Subcell `11102003` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaBelowCell1110)))
/-- Subcell `11102012` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaBelowCell1110)))
/-- Subcell `11102013` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaBelowCell1110)))
/-- Subcell `11102020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaBelowCell1110)))
/-- Subcell `11102021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaBelowCell1110)))
/-- Subcell `11102022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaBelowCell1110)))
/-- Subcell `11102023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaBelowCell1110)))
/-- Subcell `11102030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaBelowCell1110)))
/-- Subcell `11102031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaBelowCell1110)))
/-- Subcell `11102032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaBelowCell1110)))
/-- Subcell `11102033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaBelowCell1110)))
/-- Subcell `11102120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaBelowCell1110)))
/-- Subcell `11102121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaBelowCell1110)))
/-- Subcell `11102122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaBelowCell1110)))
/-- Subcell `11102123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaBelowCell1110)))
/-- Subcell `11102130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaBelowCell1110)))
/-- Subcell `11102131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaBelowCell1110)))
/-- Subcell `11102132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaBelowCell1110)))
/-- Subcell `11102133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaBelowCell1110)))
/-- Subcell `11102200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaBelowCell1110)))
/-- Subcell `11102201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaBelowCell1110)))
/-- Subcell `11102210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaBelowCell1110)))
/-- Subcell `11102211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaBelowCell1110)))
/-- Subcell `11102300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaBelowCell1110)))
/-- Subcell `11102301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaBelowCell1110)))
/-- Subcell `11102310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaBelowCell1110)))
/-- Subcell `11102311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11102311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaBelowCell1110)))
/-- Subcell `11103020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaBelowCell1110)))
/-- Subcell `11103021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaBelowCell1110)))
/-- Subcell `11103022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaBelowCell1110)))
/-- Subcell `11103023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaBelowCell1110)))
/-- Subcell `11103030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaBelowCell1110)))
/-- Subcell `11103031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaBelowCell1110)))
/-- Subcell `11103032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaBelowCell1110)))
/-- Subcell `11103033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaBelowCell1110)))
/-- Subcell `11103120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaBelowCell1110)))
/-- Subcell `11103121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaBelowCell1110)))
/-- Subcell `11103122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaBelowCell1110)))
/-- Subcell `11103123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaBelowCell1110)))
/-- Subcell `11103130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaBelowCell1110)))
/-- Subcell `11103131` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaBelowCell1110)))
/-- Subcell `11103132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaBelowCell1110)))
/-- Subcell `11103133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaBelowCell1110)))
/-- Subcell `11103200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaBelowCell1110)))
/-- Subcell `11103201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaBelowCell1110)))
/-- Subcell `11103210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaBelowCell1110)))
/-- Subcell `11103211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaBelowCell1110)))
/-- Subcell `11103300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaBelowCell1110)))
/-- Subcell `11103301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaBelowCell1110)))
/-- Subcell `11103310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaBelowCell1110)))
/-- Subcell `11103311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11103311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1110)))
/-- Subcell `11112020` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaBelowCell1111)))
/-- Subcell `11112021` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaBelowCell1111)))
/-- Subcell `11112022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaBelowCell1111)))
/-- Subcell `11112023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaBelowCell1111)))
/-- Subcell `11112030` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaBelowCell1111)))
/-- Subcell `11112031` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaBelowCell1111)))
/-- Subcell `11112032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaBelowCell1111)))
/-- Subcell `11112033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaBelowCell1111)))
/-- Subcell `11112120` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaBelowCell1111)))
/-- Subcell `11112121` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaBelowCell1111)))
/-- Subcell `11112122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaBelowCell1111)))
/-- Subcell `11112123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaBelowCell1111)))
/-- Subcell `11112130` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaBelowCell1111)))
/-- Subcell `11112132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaBelowCell1111)))
/-- Subcell `11112133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaBelowCell1111)))
/-- Subcell `11112200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaBelowCell1111)))
/-- Subcell `11112201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaBelowCell1111)))
/-- Subcell `11112210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaBelowCell1111)))
/-- Subcell `11112211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaBelowCell1111)))
/-- Subcell `11112212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaBelowCell1111)))
/-- Subcell `11112213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaBelowCell1111)))
/-- Subcell `11112300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaBelowCell1111)))
/-- Subcell `11112301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaBelowCell1111)))
/-- Subcell `11112302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaBelowCell1111)))
/-- Subcell `11112303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaBelowCell1111)))
/-- Subcell `11112310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaBelowCell1111)))
/-- Subcell `11112311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaBelowCell1111)))
/-- Subcell `11112312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaBelowCell1111)))
/-- Subcell `11112313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11112313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaBelowCell1111)))
/-- Subcell `11113022` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaBelowCell1111)))
/-- Subcell `11113023` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaBelowCell1111)))
/-- Subcell `11113032` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaBelowCell1111)))
/-- Subcell `11113033` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaBelowCell1111)))
/-- Subcell `11113122` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaBelowCell1111)))
/-- Subcell `11113123` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaBelowCell1111)))
/-- Subcell `11113132` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaBelowCell1111)))
/-- Subcell `11113133` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaBelowCell1111)))
/-- Subcell `11113200` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaBelowCell1111)))
/-- Subcell `11113201` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaBelowCell1111)))
/-- Subcell `11113202` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaBelowCell1111)))
/-- Subcell `11113203` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaBelowCell1111)))
/-- Subcell `11113210` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaBelowCell1111)))
/-- Subcell `11113211` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaBelowCell1111)))
/-- Subcell `11113212` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaBelowCell1111)))
/-- Subcell `11113213` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaBelowCell1111)))
/-- Subcell `11113300` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaBelowCell1111)))
/-- Subcell `11113301` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaBelowCell1111)))
/-- Subcell `11113302` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaBelowCell1111)))
/-- Subcell `11113303` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaBelowCell1111)))
/-- Subcell `11113310` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaBelowCell1111)))
/-- Subcell `11113311` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaBelowCell1111)))
/-- Subcell `11113312` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaBelowCell1111)))
/-- Subcell `11113313` of the theta-below root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaBelowCell11113313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaBelowCell1111)))

end CertificateCells6754c8bb3e

open CertificateCells6754c8bb3e

theorem e24KC2ThetaBelowNode11012132 :
    adaptiveCoverCheck 10 thetaBelowCell11012132 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11012132
    e24KC2ThetaBelowLeaf110121320 e24KC2ThetaBelowLeaf110121321 e24KC2ThetaBelowLeaf110121322
      e24KC2ThetaBelowLeaf110121323

theorem e24KC2ThetaBelowNode11012133 :
    adaptiveCoverCheck 10 thetaBelowCell11012133 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11012133
    e24KC2ThetaBelowLeaf110121330 e24KC2ThetaBelowLeaf110121331 e24KC2ThetaBelowLeaf110121332
      e24KC2ThetaBelowLeaf110121333

theorem e24KC2ThetaBelowNode11013013 :
    adaptiveCoverCheck 10 thetaBelowCell11013013 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013013
    e24KC2ThetaBelowLeaf110130130 e24KC2ThetaBelowLeaf110130131 e24KC2ThetaBelowLeaf110130132
      e24KC2ThetaBelowLeaf110130133

theorem e24KC2ThetaBelowNode11013021 :
    adaptiveCoverCheck 10 thetaBelowCell11013021 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013021
    e24KC2ThetaBelowLeaf110130210 e24KC2ThetaBelowLeaf110130211 e24KC2ThetaBelowLeaf110130212
      e24KC2ThetaBelowLeaf110130213

theorem e24KC2ThetaBelowNode11013022 :
    adaptiveCoverCheck 10 thetaBelowCell11013022 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013022
    e24KC2ThetaBelowLeaf110130220 e24KC2ThetaBelowLeaf110130221 e24KC2ThetaBelowLeaf110130222
      e24KC2ThetaBelowLeaf110130223

theorem e24KC2ThetaBelowNode11013023 :
    adaptiveCoverCheck 10 thetaBelowCell11013023 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013023
    e24KC2ThetaBelowLeaf110130230 e24KC2ThetaBelowLeaf110130231 e24KC2ThetaBelowLeaf110130232
      e24KC2ThetaBelowLeaf110130233

theorem e24KC2ThetaBelowNode11013030 :
    adaptiveCoverCheck 10 thetaBelowCell11013030 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013030
    e24KC2ThetaBelowLeaf110130300 e24KC2ThetaBelowLeaf110130301 e24KC2ThetaBelowLeaf110130302
      e24KC2ThetaBelowLeaf110130303

theorem e24KC2ThetaBelowNode11013031 :
    adaptiveCoverCheck 10 thetaBelowCell11013031 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013031
    e24KC2ThetaBelowLeaf110130310 e24KC2ThetaBelowLeaf110130311 e24KC2ThetaBelowLeaf110130312
      e24KC2ThetaBelowLeaf110130313

theorem e24KC2ThetaBelowNode11013032 :
    adaptiveCoverCheck 10 thetaBelowCell11013032 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013032
    e24KC2ThetaBelowLeaf110130320 e24KC2ThetaBelowLeaf110130321 e24KC2ThetaBelowLeaf110130322
      e24KC2ThetaBelowLeaf110130323

theorem e24KC2ThetaBelowNode11013033 :
    adaptiveCoverCheck 10 thetaBelowCell11013033 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013033
    e24KC2ThetaBelowLeaf110130330 e24KC2ThetaBelowLeaf110130331 e24KC2ThetaBelowLeaf110130332
      e24KC2ThetaBelowLeaf110130333

theorem e24KC2ThetaBelowNode11013102 :
    adaptiveCoverCheck 10 thetaBelowCell11013102 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013102
    e24KC2ThetaBelowLeaf110131020 e24KC2ThetaBelowLeaf110131021 e24KC2ThetaBelowLeaf110131022
      e24KC2ThetaBelowLeaf110131023

theorem e24KC2ThetaBelowNode11013103 :
    adaptiveCoverCheck 10 thetaBelowCell11013103 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013103
    e24KC2ThetaBelowLeaf110131030 e24KC2ThetaBelowLeaf110131031 e24KC2ThetaBelowLeaf110131032
      e24KC2ThetaBelowLeaf110131033

theorem e24KC2ThetaBelowNode11013112 :
    adaptiveCoverCheck 10 thetaBelowCell11013112 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013112
    e24KC2ThetaBelowLeaf110131120 e24KC2ThetaBelowLeaf110131121 e24KC2ThetaBelowLeaf110131122
      e24KC2ThetaBelowLeaf110131123

theorem e24KC2ThetaBelowNode11013113 :
    adaptiveCoverCheck 10 thetaBelowCell11013113 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013113
    e24KC2ThetaBelowLeaf110131130 e24KC2ThetaBelowLeaf110131131 e24KC2ThetaBelowLeaf110131132
      e24KC2ThetaBelowLeaf110131133

theorem e24KC2ThetaBelowNode11013120 :
    adaptiveCoverCheck 10 thetaBelowCell11013120 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013120
    e24KC2ThetaBelowLeaf110131200 e24KC2ThetaBelowLeaf110131201 e24KC2ThetaBelowLeaf110131202
      e24KC2ThetaBelowLeaf110131203

theorem e24KC2ThetaBelowNode11013121 :
    adaptiveCoverCheck 10 thetaBelowCell11013121 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013121
    e24KC2ThetaBelowLeaf110131210 e24KC2ThetaBelowLeaf110131211 e24KC2ThetaBelowLeaf110131212
      e24KC2ThetaBelowLeaf110131213

theorem e24KC2ThetaBelowNode11013122 :
    adaptiveCoverCheck 10 thetaBelowCell11013122 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013122
    e24KC2ThetaBelowLeaf110131220 e24KC2ThetaBelowLeaf110131221 e24KC2ThetaBelowLeaf110131222
      e24KC2ThetaBelowLeaf110131223

theorem e24KC2ThetaBelowNode11013123 :
    adaptiveCoverCheck 10 thetaBelowCell11013123 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013123
    e24KC2ThetaBelowLeaf110131230 e24KC2ThetaBelowLeaf110131231 e24KC2ThetaBelowLeaf110131232
      e24KC2ThetaBelowLeaf110131233

theorem e24KC2ThetaBelowNode11013130 :
    adaptiveCoverCheck 10 thetaBelowCell11013130 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013130
    e24KC2ThetaBelowLeaf110131300 e24KC2ThetaBelowLeaf110131301 e24KC2ThetaBelowLeaf110131302
      e24KC2ThetaBelowLeaf110131303

theorem e24KC2ThetaBelowNode11013131 :
    adaptiveCoverCheck 10 thetaBelowCell11013131 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013131
    e24KC2ThetaBelowLeaf110131310 e24KC2ThetaBelowLeaf110131311 e24KC2ThetaBelowLeaf110131312
      e24KC2ThetaBelowLeaf110131313

theorem e24KC2ThetaBelowNode11013132 :
    adaptiveCoverCheck 10 thetaBelowCell11013132 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013132
    e24KC2ThetaBelowLeaf110131320 e24KC2ThetaBelowLeaf110131321 e24KC2ThetaBelowLeaf110131322
      e24KC2ThetaBelowLeaf110131323

theorem e24KC2ThetaBelowNode11013133 :
    adaptiveCoverCheck 10 thetaBelowCell11013133 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11013133
    e24KC2ThetaBelowLeaf110131330 e24KC2ThetaBelowLeaf110131331 e24KC2ThetaBelowLeaf110131332
      e24KC2ThetaBelowLeaf110131333

theorem e24KC2ThetaBelowNode11102002 :
    adaptiveCoverCheck 10 thetaBelowCell11102002 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102002
    e24KC2ThetaBelowLeaf111020020 e24KC2ThetaBelowLeaf111020021 e24KC2ThetaBelowLeaf111020022
      e24KC2ThetaBelowLeaf111020023

theorem e24KC2ThetaBelowNode11102003 :
    adaptiveCoverCheck 10 thetaBelowCell11102003 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102003
    e24KC2ThetaBelowLeaf111020030 e24KC2ThetaBelowLeaf111020031 e24KC2ThetaBelowLeaf111020032
      e24KC2ThetaBelowLeaf111020033

theorem e24KC2ThetaBelowNode11102012 :
    adaptiveCoverCheck 10 thetaBelowCell11102012 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102012
    e24KC2ThetaBelowLeaf111020120 e24KC2ThetaBelowLeaf111020121 e24KC2ThetaBelowLeaf111020122
      e24KC2ThetaBelowLeaf111020123

theorem e24KC2ThetaBelowNode11102013 :
    adaptiveCoverCheck 10 thetaBelowCell11102013 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102013
    e24KC2ThetaBelowLeaf111020130 e24KC2ThetaBelowLeaf111020131 e24KC2ThetaBelowLeaf111020132
      e24KC2ThetaBelowLeaf111020133

theorem e24KC2ThetaBelowNode11102020 :
    adaptiveCoverCheck 10 thetaBelowCell11102020 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102020
    e24KC2ThetaBelowLeaf111020200 e24KC2ThetaBelowLeaf111020201 e24KC2ThetaBelowLeaf111020202
      e24KC2ThetaBelowLeaf111020203

theorem e24KC2ThetaBelowNode11102021 :
    adaptiveCoverCheck 10 thetaBelowCell11102021 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102021
    e24KC2ThetaBelowLeaf111020210 e24KC2ThetaBelowLeaf111020211 e24KC2ThetaBelowLeaf111020212
      e24KC2ThetaBelowLeaf111020213

theorem e24KC2ThetaBelowNode11102022 :
    adaptiveCoverCheck 10 thetaBelowCell11102022 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102022
    e24KC2ThetaBelowLeaf111020220 e24KC2ThetaBelowLeaf111020221 e24KC2ThetaBelowLeaf111020222
      e24KC2ThetaBelowLeaf111020223

theorem e24KC2ThetaBelowNode11102023 :
    adaptiveCoverCheck 10 thetaBelowCell11102023 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102023
    e24KC2ThetaBelowLeaf111020230 e24KC2ThetaBelowLeaf111020231 e24KC2ThetaBelowLeaf111020232
      e24KC2ThetaBelowLeaf111020233

theorem e24KC2ThetaBelowNode11102030 :
    adaptiveCoverCheck 10 thetaBelowCell11102030 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102030
    e24KC2ThetaBelowLeaf111020300 e24KC2ThetaBelowLeaf111020301 e24KC2ThetaBelowLeaf111020302
      e24KC2ThetaBelowLeaf111020303

theorem e24KC2ThetaBelowNode11102031 :
    adaptiveCoverCheck 10 thetaBelowCell11102031 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102031
    e24KC2ThetaBelowLeaf111020310 e24KC2ThetaBelowLeaf111020311 e24KC2ThetaBelowLeaf111020312
      e24KC2ThetaBelowLeaf111020313

theorem e24KC2ThetaBelowNode11102032 :
    adaptiveCoverCheck 10 thetaBelowCell11102032 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102032
    e24KC2ThetaBelowLeaf111020320 e24KC2ThetaBelowLeaf111020321 e24KC2ThetaBelowLeaf111020322
      e24KC2ThetaBelowLeaf111020323

theorem e24KC2ThetaBelowNode11102033 :
    adaptiveCoverCheck 10 thetaBelowCell11102033 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102033
    e24KC2ThetaBelowLeaf111020330 e24KC2ThetaBelowLeaf111020331 e24KC2ThetaBelowLeaf111020332
      e24KC2ThetaBelowLeaf111020333

theorem e24KC2ThetaBelowNode11102120 :
    adaptiveCoverCheck 10 thetaBelowCell11102120 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102120
    e24KC2ThetaBelowLeaf111021200 e24KC2ThetaBelowLeaf111021201 e24KC2ThetaBelowLeaf111021202
      e24KC2ThetaBelowLeaf111021203

theorem e24KC2ThetaBelowNode11102121 :
    adaptiveCoverCheck 10 thetaBelowCell11102121 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102121
    e24KC2ThetaBelowLeaf111021210 e24KC2ThetaBelowLeaf111021211 e24KC2ThetaBelowLeaf111021212
      e24KC2ThetaBelowLeaf111021213

theorem e24KC2ThetaBelowNode11102122 :
    adaptiveCoverCheck 10 thetaBelowCell11102122 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102122
    e24KC2ThetaBelowLeaf111021220 e24KC2ThetaBelowLeaf111021221 e24KC2ThetaBelowLeaf111021222
      e24KC2ThetaBelowLeaf111021223

theorem e24KC2ThetaBelowNode11102123 :
    adaptiveCoverCheck 10 thetaBelowCell11102123 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102123
    e24KC2ThetaBelowLeaf111021230 e24KC2ThetaBelowLeaf111021231 e24KC2ThetaBelowLeaf111021232
      e24KC2ThetaBelowLeaf111021233

theorem e24KC2ThetaBelowNode11102130 :
    adaptiveCoverCheck 10 thetaBelowCell11102130 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102130
    e24KC2ThetaBelowLeaf111021300 e24KC2ThetaBelowLeaf111021301 e24KC2ThetaBelowLeaf111021302
      e24KC2ThetaBelowLeaf111021303

theorem e24KC2ThetaBelowNode11102131 :
    adaptiveCoverCheck 10 thetaBelowCell11102131 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102131
    e24KC2ThetaBelowLeaf111021310 e24KC2ThetaBelowLeaf111021311 e24KC2ThetaBelowLeaf111021312
      e24KC2ThetaBelowLeaf111021313

theorem e24KC2ThetaBelowNode11102132 :
    adaptiveCoverCheck 10 thetaBelowCell11102132 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102132
    e24KC2ThetaBelowLeaf111021320 e24KC2ThetaBelowLeaf111021321 e24KC2ThetaBelowLeaf111021322
      e24KC2ThetaBelowLeaf111021323

theorem e24KC2ThetaBelowNode11102133 :
    adaptiveCoverCheck 10 thetaBelowCell11102133 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102133
    e24KC2ThetaBelowLeaf111021330 e24KC2ThetaBelowLeaf111021331 e24KC2ThetaBelowLeaf111021332
      e24KC2ThetaBelowLeaf111021333

theorem e24KC2ThetaBelowNode11102200 :
    adaptiveCoverCheck 10 thetaBelowCell11102200 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102200
    e24KC2ThetaBelowLeaf111022000 e24KC2ThetaBelowLeaf111022001 e24KC2ThetaBelowLeaf111022002
      e24KC2ThetaBelowLeaf111022003

theorem e24KC2ThetaBelowNode11102201 :
    adaptiveCoverCheck 10 thetaBelowCell11102201 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102201
    e24KC2ThetaBelowLeaf111022010 e24KC2ThetaBelowLeaf111022011 e24KC2ThetaBelowLeaf111022012
      e24KC2ThetaBelowLeaf111022013

theorem e24KC2ThetaBelowNode11102210 :
    adaptiveCoverCheck 10 thetaBelowCell11102210 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102210
    e24KC2ThetaBelowLeaf111022100 e24KC2ThetaBelowLeaf111022101 e24KC2ThetaBelowLeaf111022102
      e24KC2ThetaBelowLeaf111022103

theorem e24KC2ThetaBelowNode11102211 :
    adaptiveCoverCheck 10 thetaBelowCell11102211 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102211
    e24KC2ThetaBelowLeaf111022110 e24KC2ThetaBelowLeaf111022111 e24KC2ThetaBelowLeaf111022112
      e24KC2ThetaBelowLeaf111022113

theorem e24KC2ThetaBelowNode11102300 :
    adaptiveCoverCheck 10 thetaBelowCell11102300 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102300
    e24KC2ThetaBelowLeaf111023000 e24KC2ThetaBelowLeaf111023001 e24KC2ThetaBelowLeaf111023002
      e24KC2ThetaBelowLeaf111023003

theorem e24KC2ThetaBelowNode11102301 :
    adaptiveCoverCheck 10 thetaBelowCell11102301 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102301
    e24KC2ThetaBelowLeaf111023010 e24KC2ThetaBelowLeaf111023011 e24KC2ThetaBelowLeaf111023012
      e24KC2ThetaBelowLeaf111023013

theorem e24KC2ThetaBelowNode11102310 :
    adaptiveCoverCheck 10 thetaBelowCell11102310 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102310
    e24KC2ThetaBelowLeaf111023100 e24KC2ThetaBelowLeaf111023101 e24KC2ThetaBelowLeaf111023102
      e24KC2ThetaBelowLeaf111023103

theorem e24KC2ThetaBelowNode11102311 :
    adaptiveCoverCheck 10 thetaBelowCell11102311 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11102311
    e24KC2ThetaBelowLeaf111023110 e24KC2ThetaBelowLeaf111023111 e24KC2ThetaBelowLeaf111023112
      e24KC2ThetaBelowLeaf111023113

theorem e24KC2ThetaBelowNode11103020 :
    adaptiveCoverCheck 10 thetaBelowCell11103020 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103020
    e24KC2ThetaBelowLeaf111030200 e24KC2ThetaBelowLeaf111030201 e24KC2ThetaBelowLeaf111030202
      e24KC2ThetaBelowLeaf111030203

theorem e24KC2ThetaBelowNode11103021 :
    adaptiveCoverCheck 10 thetaBelowCell11103021 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103021
    e24KC2ThetaBelowLeaf111030210 e24KC2ThetaBelowLeaf111030211 e24KC2ThetaBelowLeaf111030212
      e24KC2ThetaBelowLeaf111030213

theorem e24KC2ThetaBelowNode11103022 :
    adaptiveCoverCheck 10 thetaBelowCell11103022 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103022
    e24KC2ThetaBelowLeaf111030220 e24KC2ThetaBelowLeaf111030221 e24KC2ThetaBelowLeaf111030222
      e24KC2ThetaBelowLeaf111030223

theorem e24KC2ThetaBelowNode11103023 :
    adaptiveCoverCheck 10 thetaBelowCell11103023 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103023
    e24KC2ThetaBelowLeaf111030230 e24KC2ThetaBelowLeaf111030231 e24KC2ThetaBelowLeaf111030232
      e24KC2ThetaBelowLeaf111030233

theorem e24KC2ThetaBelowNode11103030 :
    adaptiveCoverCheck 10 thetaBelowCell11103030 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103030
    e24KC2ThetaBelowLeaf111030300 e24KC2ThetaBelowLeaf111030301 e24KC2ThetaBelowLeaf111030302
      e24KC2ThetaBelowLeaf111030303

theorem e24KC2ThetaBelowNode11103031 :
    adaptiveCoverCheck 10 thetaBelowCell11103031 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103031
    e24KC2ThetaBelowLeaf111030310 e24KC2ThetaBelowLeaf111030311 e24KC2ThetaBelowLeaf111030312
      e24KC2ThetaBelowLeaf111030313

theorem e24KC2ThetaBelowNode11103032 :
    adaptiveCoverCheck 10 thetaBelowCell11103032 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103032
    e24KC2ThetaBelowLeaf111030320 e24KC2ThetaBelowLeaf111030321 e24KC2ThetaBelowLeaf111030322
      e24KC2ThetaBelowLeaf111030323

theorem e24KC2ThetaBelowNode11103033 :
    adaptiveCoverCheck 10 thetaBelowCell11103033 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103033
    e24KC2ThetaBelowLeaf111030330 e24KC2ThetaBelowLeaf111030331 e24KC2ThetaBelowLeaf111030332
      e24KC2ThetaBelowLeaf111030333

theorem e24KC2ThetaBelowNode11103120 :
    adaptiveCoverCheck 10 thetaBelowCell11103120 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103120
    e24KC2ThetaBelowLeaf111031200 e24KC2ThetaBelowLeaf111031201 e24KC2ThetaBelowLeaf111031202
      e24KC2ThetaBelowLeaf111031203

theorem e24KC2ThetaBelowNode11103121 :
    adaptiveCoverCheck 10 thetaBelowCell11103121 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103121
    e24KC2ThetaBelowLeaf111031210 e24KC2ThetaBelowLeaf111031211 e24KC2ThetaBelowLeaf111031212
      e24KC2ThetaBelowLeaf111031213

theorem e24KC2ThetaBelowNode11103122 :
    adaptiveCoverCheck 10 thetaBelowCell11103122 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103122
    e24KC2ThetaBelowLeaf111031220 e24KC2ThetaBelowLeaf111031221 e24KC2ThetaBelowLeaf111031222
      e24KC2ThetaBelowLeaf111031223

theorem e24KC2ThetaBelowNode11103123 :
    adaptiveCoverCheck 10 thetaBelowCell11103123 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103123
    e24KC2ThetaBelowLeaf111031230 e24KC2ThetaBelowLeaf111031231 e24KC2ThetaBelowLeaf111031232
      e24KC2ThetaBelowLeaf111031233

theorem e24KC2ThetaBelowNode11103130 :
    adaptiveCoverCheck 10 thetaBelowCell11103130 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103130
    e24KC2ThetaBelowLeaf111031300 e24KC2ThetaBelowLeaf111031301 e24KC2ThetaBelowLeaf111031302
      e24KC2ThetaBelowLeaf111031303

theorem e24KC2ThetaBelowNode11103131 :
    adaptiveCoverCheck 10 thetaBelowCell11103131 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103131
    e24KC2ThetaBelowLeaf111031310 e24KC2ThetaBelowLeaf111031311 e24KC2ThetaBelowLeaf111031312
      e24KC2ThetaBelowLeaf111031313

theorem e24KC2ThetaBelowNode11103132 :
    adaptiveCoverCheck 10 thetaBelowCell11103132 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103132
    e24KC2ThetaBelowLeaf111031320 e24KC2ThetaBelowLeaf111031321 e24KC2ThetaBelowLeaf111031322
      e24KC2ThetaBelowLeaf111031323

theorem e24KC2ThetaBelowNode11103133 :
    adaptiveCoverCheck 10 thetaBelowCell11103133 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103133
    e24KC2ThetaBelowLeaf111031330 e24KC2ThetaBelowLeaf111031331 e24KC2ThetaBelowLeaf111031332
      e24KC2ThetaBelowLeaf111031333

theorem e24KC2ThetaBelowNode11103200 :
    adaptiveCoverCheck 10 thetaBelowCell11103200 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103200
    e24KC2ThetaBelowLeaf111032000 e24KC2ThetaBelowLeaf111032001 e24KC2ThetaBelowLeaf111032002
      e24KC2ThetaBelowLeaf111032003

theorem e24KC2ThetaBelowNode11103201 :
    adaptiveCoverCheck 10 thetaBelowCell11103201 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103201
    e24KC2ThetaBelowLeaf111032010 e24KC2ThetaBelowLeaf111032011 e24KC2ThetaBelowLeaf111032012
      e24KC2ThetaBelowLeaf111032013

theorem e24KC2ThetaBelowNode11103210 :
    adaptiveCoverCheck 10 thetaBelowCell11103210 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103210
    e24KC2ThetaBelowLeaf111032100 e24KC2ThetaBelowLeaf111032101 e24KC2ThetaBelowLeaf111032102
      e24KC2ThetaBelowLeaf111032103

theorem e24KC2ThetaBelowNode11103211 :
    adaptiveCoverCheck 10 thetaBelowCell11103211 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103211
    e24KC2ThetaBelowLeaf111032110 e24KC2ThetaBelowLeaf111032111 e24KC2ThetaBelowLeaf111032112
      e24KC2ThetaBelowLeaf111032113

theorem e24KC2ThetaBelowNode11103300 :
    adaptiveCoverCheck 10 thetaBelowCell11103300 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103300
    e24KC2ThetaBelowLeaf111033000 e24KC2ThetaBelowLeaf111033001 e24KC2ThetaBelowLeaf111033002
      e24KC2ThetaBelowLeaf111033003

theorem e24KC2ThetaBelowNode11103301 :
    adaptiveCoverCheck 10 thetaBelowCell11103301 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103301
    e24KC2ThetaBelowLeaf111033010 e24KC2ThetaBelowLeaf111033011 e24KC2ThetaBelowLeaf111033012
      e24KC2ThetaBelowLeaf111033013

theorem e24KC2ThetaBelowNode11103310 :
    adaptiveCoverCheck 10 thetaBelowCell11103310 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103310
    e24KC2ThetaBelowLeaf111033100 e24KC2ThetaBelowLeaf111033101 e24KC2ThetaBelowLeaf111033102
      e24KC2ThetaBelowLeaf111033103

theorem e24KC2ThetaBelowNode11103311 :
    adaptiveCoverCheck 10 thetaBelowCell11103311 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11103311
    e24KC2ThetaBelowLeaf111033110 e24KC2ThetaBelowLeaf111033111 e24KC2ThetaBelowLeaf111033112
      e24KC2ThetaBelowLeaf111033113

theorem e24KC2ThetaBelowNode11112020 :
    adaptiveCoverCheck 10 thetaBelowCell11112020 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112020
    e24KC2ThetaBelowLeaf111120200 e24KC2ThetaBelowLeaf111120201 e24KC2ThetaBelowLeaf111120202
      e24KC2ThetaBelowLeaf111120203

theorem e24KC2ThetaBelowNode11112021 :
    adaptiveCoverCheck 10 thetaBelowCell11112021 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112021
    e24KC2ThetaBelowLeaf111120210 e24KC2ThetaBelowLeaf111120211 e24KC2ThetaBelowLeaf111120212
      e24KC2ThetaBelowLeaf111120213

theorem e24KC2ThetaBelowNode11112022 :
    adaptiveCoverCheck 10 thetaBelowCell11112022 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112022
    e24KC2ThetaBelowLeaf111120220 e24KC2ThetaBelowLeaf111120221 e24KC2ThetaBelowLeaf111120222
      e24KC2ThetaBelowLeaf111120223

theorem e24KC2ThetaBelowNode11112023 :
    adaptiveCoverCheck 10 thetaBelowCell11112023 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112023
    e24KC2ThetaBelowLeaf111120230 e24KC2ThetaBelowLeaf111120231 e24KC2ThetaBelowLeaf111120232
      e24KC2ThetaBelowLeaf111120233

theorem e24KC2ThetaBelowNode11112030 :
    adaptiveCoverCheck 10 thetaBelowCell11112030 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112030
    e24KC2ThetaBelowLeaf111120300 e24KC2ThetaBelowLeaf111120301 e24KC2ThetaBelowLeaf111120302
      e24KC2ThetaBelowLeaf111120303

theorem e24KC2ThetaBelowNode11112031 :
    adaptiveCoverCheck 10 thetaBelowCell11112031 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112031
    e24KC2ThetaBelowLeaf111120310 e24KC2ThetaBelowLeaf111120311 e24KC2ThetaBelowLeaf111120312
      e24KC2ThetaBelowLeaf111120313

theorem e24KC2ThetaBelowNode11112032 :
    adaptiveCoverCheck 10 thetaBelowCell11112032 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112032
    e24KC2ThetaBelowLeaf111120320 e24KC2ThetaBelowLeaf111120321 e24KC2ThetaBelowLeaf111120322
      e24KC2ThetaBelowLeaf111120323

theorem e24KC2ThetaBelowNode11112033 :
    adaptiveCoverCheck 10 thetaBelowCell11112033 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112033
    e24KC2ThetaBelowLeaf111120330 e24KC2ThetaBelowLeaf111120331 e24KC2ThetaBelowLeaf111120332
      e24KC2ThetaBelowLeaf111120333

theorem e24KC2ThetaBelowNode11112120 :
    adaptiveCoverCheck 10 thetaBelowCell11112120 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112120
    e24KC2ThetaBelowLeaf111121200 e24KC2ThetaBelowLeaf111121201 e24KC2ThetaBelowLeaf111121202
      e24KC2ThetaBelowLeaf111121203

theorem e24KC2ThetaBelowNode11112121 :
    adaptiveCoverCheck 10 thetaBelowCell11112121 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112121
    e24KC2ThetaBelowLeaf111121210 e24KC2ThetaBelowLeaf111121211 e24KC2ThetaBelowLeaf111121212
      e24KC2ThetaBelowLeaf111121213

theorem e24KC2ThetaBelowNode11112122 :
    adaptiveCoverCheck 10 thetaBelowCell11112122 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112122
    e24KC2ThetaBelowLeaf111121220 e24KC2ThetaBelowLeaf111121221 e24KC2ThetaBelowLeaf111121222
      e24KC2ThetaBelowLeaf111121223

theorem e24KC2ThetaBelowNode11112123 :
    adaptiveCoverCheck 10 thetaBelowCell11112123 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112123
    e24KC2ThetaBelowLeaf111121230 e24KC2ThetaBelowLeaf111121231 e24KC2ThetaBelowLeaf111121232
      e24KC2ThetaBelowLeaf111121233

theorem e24KC2ThetaBelowNode11112130 :
    adaptiveCoverCheck 10 thetaBelowCell11112130 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112130
    e24KC2ThetaBelowLeaf111121300 e24KC2ThetaBelowLeaf111121301 e24KC2ThetaBelowLeaf111121302
      e24KC2ThetaBelowLeaf111121303

theorem e24KC2ThetaBelowNode11112132 :
    adaptiveCoverCheck 10 thetaBelowCell11112132 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112132
    e24KC2ThetaBelowLeaf111121320 e24KC2ThetaBelowLeaf111121321 e24KC2ThetaBelowLeaf111121322
      e24KC2ThetaBelowLeaf111121323

theorem e24KC2ThetaBelowNode11112133 :
    adaptiveCoverCheck 10 thetaBelowCell11112133 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112133
    e24KC2ThetaBelowLeaf111121330 e24KC2ThetaBelowLeaf111121331 e24KC2ThetaBelowLeaf111121332
      e24KC2ThetaBelowLeaf111121333

theorem e24KC2ThetaBelowNode11112200 :
    adaptiveCoverCheck 10 thetaBelowCell11112200 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112200
    e24KC2ThetaBelowLeaf111122000 e24KC2ThetaBelowLeaf111122001 e24KC2ThetaBelowLeaf111122002
      e24KC2ThetaBelowLeaf111122003

theorem e24KC2ThetaBelowNode11112201 :
    adaptiveCoverCheck 10 thetaBelowCell11112201 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112201
    e24KC2ThetaBelowLeaf111122010 e24KC2ThetaBelowLeaf111122011 e24KC2ThetaBelowLeaf111122012
      e24KC2ThetaBelowLeaf111122013

theorem e24KC2ThetaBelowNode11112210 :
    adaptiveCoverCheck 10 thetaBelowCell11112210 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112210
    e24KC2ThetaBelowLeaf111122100 e24KC2ThetaBelowLeaf111122101 e24KC2ThetaBelowLeaf111122102
      e24KC2ThetaBelowLeaf111122103

theorem e24KC2ThetaBelowNode11112211 :
    adaptiveCoverCheck 10 thetaBelowCell11112211 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112211
    e24KC2ThetaBelowLeaf111122110 e24KC2ThetaBelowLeaf111122111 e24KC2ThetaBelowLeaf111122112
      e24KC2ThetaBelowLeaf111122113

theorem e24KC2ThetaBelowNode11112212 :
    adaptiveCoverCheck 10 thetaBelowCell11112212 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112212
    e24KC2ThetaBelowLeaf111122120 e24KC2ThetaBelowLeaf111122121 e24KC2ThetaBelowLeaf111122122
      e24KC2ThetaBelowLeaf111122123

theorem e24KC2ThetaBelowNode11112213 :
    adaptiveCoverCheck 10 thetaBelowCell11112213 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112213
    e24KC2ThetaBelowLeaf111122130 e24KC2ThetaBelowLeaf111122131 e24KC2ThetaBelowLeaf111122132
      e24KC2ThetaBelowLeaf111122133

theorem e24KC2ThetaBelowNode11112300 :
    adaptiveCoverCheck 10 thetaBelowCell11112300 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112300
    e24KC2ThetaBelowLeaf111123000 e24KC2ThetaBelowLeaf111123001 e24KC2ThetaBelowLeaf111123002
      e24KC2ThetaBelowLeaf111123003

theorem e24KC2ThetaBelowNode11112301 :
    adaptiveCoverCheck 10 thetaBelowCell11112301 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112301
    e24KC2ThetaBelowLeaf111123010 e24KC2ThetaBelowLeaf111123011 e24KC2ThetaBelowLeaf111123012
      e24KC2ThetaBelowLeaf111123013

theorem e24KC2ThetaBelowNode11112302 :
    adaptiveCoverCheck 10 thetaBelowCell11112302 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112302
    e24KC2ThetaBelowLeaf111123020 e24KC2ThetaBelowLeaf111123021 e24KC2ThetaBelowLeaf111123022
      e24KC2ThetaBelowLeaf111123023

theorem e24KC2ThetaBelowNode11112303 :
    adaptiveCoverCheck 10 thetaBelowCell11112303 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112303
    e24KC2ThetaBelowLeaf111123030 e24KC2ThetaBelowLeaf111123031 e24KC2ThetaBelowLeaf111123032
      e24KC2ThetaBelowLeaf111123033

theorem e24KC2ThetaBelowNode11112310 :
    adaptiveCoverCheck 10 thetaBelowCell11112310 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112310
    e24KC2ThetaBelowLeaf111123100 e24KC2ThetaBelowLeaf111123101 e24KC2ThetaBelowLeaf111123102
      e24KC2ThetaBelowLeaf111123103

theorem e24KC2ThetaBelowNode11112311 :
    adaptiveCoverCheck 10 thetaBelowCell11112311 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112311
    e24KC2ThetaBelowLeaf111123110 e24KC2ThetaBelowLeaf111123111 e24KC2ThetaBelowLeaf111123112
      e24KC2ThetaBelowLeaf111123113

theorem e24KC2ThetaBelowNode11112312 :
    adaptiveCoverCheck 10 thetaBelowCell11112312 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112312
    e24KC2ThetaBelowLeaf111123120 e24KC2ThetaBelowLeaf111123121 e24KC2ThetaBelowLeaf111123122
      e24KC2ThetaBelowLeaf111123123

theorem e24KC2ThetaBelowNode11112313 :
    adaptiveCoverCheck 10 thetaBelowCell11112313 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11112313
    e24KC2ThetaBelowLeaf111123130 e24KC2ThetaBelowLeaf111123131 e24KC2ThetaBelowLeaf111123132
      e24KC2ThetaBelowLeaf111123133

theorem e24KC2ThetaBelowNode11113022 :
    adaptiveCoverCheck 10 thetaBelowCell11113022 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113022
    e24KC2ThetaBelowLeaf111130220 e24KC2ThetaBelowLeaf111130221 e24KC2ThetaBelowLeaf111130222
      e24KC2ThetaBelowLeaf111130223

theorem e24KC2ThetaBelowNode11113023 :
    adaptiveCoverCheck 10 thetaBelowCell11113023 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113023
    e24KC2ThetaBelowLeaf111130230 e24KC2ThetaBelowLeaf111130231 e24KC2ThetaBelowLeaf111130232
      e24KC2ThetaBelowLeaf111130233

theorem e24KC2ThetaBelowNode11113032 :
    adaptiveCoverCheck 10 thetaBelowCell11113032 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113032
    e24KC2ThetaBelowLeaf111130320 e24KC2ThetaBelowLeaf111130321 e24KC2ThetaBelowLeaf111130322
      e24KC2ThetaBelowLeaf111130323

theorem e24KC2ThetaBelowNode11113033 :
    adaptiveCoverCheck 10 thetaBelowCell11113033 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113033
    e24KC2ThetaBelowLeaf111130330 e24KC2ThetaBelowLeaf111130331 e24KC2ThetaBelowLeaf111130332
      e24KC2ThetaBelowLeaf111130333

theorem e24KC2ThetaBelowNode11113122 :
    adaptiveCoverCheck 10 thetaBelowCell11113122 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113122
    e24KC2ThetaBelowLeaf111131220 e24KC2ThetaBelowLeaf111131221 e24KC2ThetaBelowLeaf111131222
      e24KC2ThetaBelowLeaf111131223

theorem e24KC2ThetaBelowNode11113123 :
    adaptiveCoverCheck 10 thetaBelowCell11113123 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113123
    e24KC2ThetaBelowLeaf111131230 e24KC2ThetaBelowLeaf111131231 e24KC2ThetaBelowLeaf111131232
      e24KC2ThetaBelowLeaf111131233

theorem e24KC2ThetaBelowNode11113132 :
    adaptiveCoverCheck 10 thetaBelowCell11113132 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113132
    e24KC2ThetaBelowLeaf111131320 e24KC2ThetaBelowLeaf111131321 e24KC2ThetaBelowLeaf111131322
      e24KC2ThetaBelowLeaf111131323

theorem e24KC2ThetaBelowNode11113133 :
    adaptiveCoverCheck 10 thetaBelowCell11113133 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113133
    e24KC2ThetaBelowLeaf111131330 e24KC2ThetaBelowLeaf111131331 e24KC2ThetaBelowLeaf111131332
      e24KC2ThetaBelowLeaf111131333

theorem e24KC2ThetaBelowNode11113200 :
    adaptiveCoverCheck 10 thetaBelowCell11113200 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113200
    e24KC2ThetaBelowLeaf111132000 e24KC2ThetaBelowLeaf111132001 e24KC2ThetaBelowLeaf111132002
      e24KC2ThetaBelowLeaf111132003

theorem e24KC2ThetaBelowNode11113201 :
    adaptiveCoverCheck 10 thetaBelowCell11113201 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113201
    e24KC2ThetaBelowLeaf111132010 e24KC2ThetaBelowLeaf111132011 e24KC2ThetaBelowLeaf111132012
      e24KC2ThetaBelowLeaf111132013

theorem e24KC2ThetaBelowNode11113202 :
    adaptiveCoverCheck 10 thetaBelowCell11113202 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113202
    e24KC2ThetaBelowLeaf111132020 e24KC2ThetaBelowLeaf111132021 e24KC2ThetaBelowLeaf111132022
      e24KC2ThetaBelowLeaf111132023

theorem e24KC2ThetaBelowNode11113203 :
    adaptiveCoverCheck 10 thetaBelowCell11113203 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113203
    e24KC2ThetaBelowLeaf111132030 e24KC2ThetaBelowLeaf111132031 e24KC2ThetaBelowLeaf111132032
      e24KC2ThetaBelowLeaf111132033

theorem e24KC2ThetaBelowNode11113210 :
    adaptiveCoverCheck 10 thetaBelowCell11113210 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113210
    e24KC2ThetaBelowLeaf111132100 e24KC2ThetaBelowLeaf111132101 e24KC2ThetaBelowLeaf111132102
      e24KC2ThetaBelowLeaf111132103

theorem e24KC2ThetaBelowNode11113211 :
    adaptiveCoverCheck 10 thetaBelowCell11113211 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113211
    e24KC2ThetaBelowLeaf111132110 e24KC2ThetaBelowLeaf111132111 e24KC2ThetaBelowLeaf111132112
      e24KC2ThetaBelowLeaf111132113

theorem e24KC2ThetaBelowNode11113212 :
    adaptiveCoverCheck 10 thetaBelowCell11113212 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113212
    e24KC2ThetaBelowLeaf111132120 e24KC2ThetaBelowLeaf111132121 e24KC2ThetaBelowLeaf111132122
      e24KC2ThetaBelowLeaf111132123

theorem e24KC2ThetaBelowNode11113213 :
    adaptiveCoverCheck 10 thetaBelowCell11113213 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113213
    e24KC2ThetaBelowLeaf111132130 e24KC2ThetaBelowLeaf111132131 e24KC2ThetaBelowLeaf111132132
      e24KC2ThetaBelowLeaf111132133

theorem e24KC2ThetaBelowNode11113300 :
    adaptiveCoverCheck 10 thetaBelowCell11113300 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113300
    e24KC2ThetaBelowLeaf111133000 e24KC2ThetaBelowLeaf111133001 e24KC2ThetaBelowLeaf111133002
      e24KC2ThetaBelowLeaf111133003

theorem e24KC2ThetaBelowNode11113301 :
    adaptiveCoverCheck 10 thetaBelowCell11113301 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113301
    e24KC2ThetaBelowLeaf111133010 e24KC2ThetaBelowLeaf111133011 e24KC2ThetaBelowLeaf111133012
      e24KC2ThetaBelowLeaf111133013

theorem e24KC2ThetaBelowNode11113302 :
    adaptiveCoverCheck 10 thetaBelowCell11113302 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113302
    e24KC2ThetaBelowLeaf111133020 e24KC2ThetaBelowLeaf111133021 e24KC2ThetaBelowLeaf111133022
      e24KC2ThetaBelowLeaf111133023

theorem e24KC2ThetaBelowNode11113303 :
    adaptiveCoverCheck 10 thetaBelowCell11113303 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113303
    e24KC2ThetaBelowLeaf111133030 e24KC2ThetaBelowLeaf111133031 e24KC2ThetaBelowLeaf111133032
      e24KC2ThetaBelowLeaf111133033

theorem e24KC2ThetaBelowNode11113310 :
    adaptiveCoverCheck 10 thetaBelowCell11113310 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113310
    e24KC2ThetaBelowLeaf111133100 e24KC2ThetaBelowLeaf111133101 e24KC2ThetaBelowLeaf111133102
      e24KC2ThetaBelowLeaf111133103

theorem e24KC2ThetaBelowNode11113311 :
    adaptiveCoverCheck 10 thetaBelowCell11113311 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113311
    e24KC2ThetaBelowLeaf111133110 e24KC2ThetaBelowLeaf111133111 e24KC2ThetaBelowLeaf111133112
      e24KC2ThetaBelowLeaf111133113

theorem e24KC2ThetaBelowNode11113312 :
    adaptiveCoverCheck 10 thetaBelowCell11113312 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113312
    e24KC2ThetaBelowLeaf111133120 e24KC2ThetaBelowLeaf111133121 e24KC2ThetaBelowLeaf111133122
      e24KC2ThetaBelowLeaf111133123

theorem e24KC2ThetaBelowNode11113313 :
    adaptiveCoverCheck 10 thetaBelowCell11113313 = true :=
  adaptiveCoverCheck_succ_of_children 9 thetaBelowCell11113313
    e24KC2ThetaBelowLeaf111133130 e24KC2ThetaBelowLeaf111133131 e24KC2ThetaBelowLeaf111133132
      e24KC2ThetaBelowLeaf111133133

theorem e24KC2ThetaBelowNode1011303 :
    adaptiveCoverCheck 11 (childHH (childLL (childHH thetaBelowCell1011))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLL (childHH thetaBelowCell1011)))
    e24KC2ThetaBelowLeaf10113030 e24KC2ThetaBelowLeaf10113031 e24KC2ThetaBelowLeaf10113032
      e24KC2ThetaBelowLeaf10113033

theorem e24KC2ThetaBelowNode1011311 :
    adaptiveCoverCheck 11 (childLH (childLH (childHH thetaBelowCell1011))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLH (childHH thetaBelowCell1011)))
    e24KC2ThetaBelowLeaf10113110 e24KC2ThetaBelowLeaf10113111 e24KC2ThetaBelowLeaf10113112
      e24KC2ThetaBelowLeaf10113113

theorem e24KC2ThetaBelowNode1011312 :
    adaptiveCoverCheck 11 (childHL (childLH (childHH thetaBelowCell1011))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLH (childHH thetaBelowCell1011)))
    e24KC2ThetaBelowLeaf10113120 e24KC2ThetaBelowLeaf10113121 e24KC2ThetaBelowLeaf10113122
      e24KC2ThetaBelowLeaf10113123

theorem e24KC2ThetaBelowNode1011313 :
    adaptiveCoverCheck 11 (childHH (childLH (childHH thetaBelowCell1011))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLH (childHH thetaBelowCell1011)))
    e24KC2ThetaBelowLeaf10113130 e24KC2ThetaBelowLeaf10113131 e24KC2ThetaBelowLeaf10113132
      e24KC2ThetaBelowLeaf10113133

theorem e24KC2ThetaBelowNode1100032 :
    adaptiveCoverCheck 11 (childHL (childHH (childLL thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childHH (childLL thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11000320 e24KC2ThetaBelowLeaf11000321 e24KC2ThetaBelowLeaf11000322
      e24KC2ThetaBelowLeaf11000323

theorem e24KC2ThetaBelowNode1100033 :
    adaptiveCoverCheck 11 (childHH (childHH (childLL thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childHH (childLL thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11000330 e24KC2ThetaBelowLeaf11000331 e24KC2ThetaBelowLeaf11000332
      e24KC2ThetaBelowLeaf11000333

theorem e24KC2ThetaBelowNode1100122 :
    adaptiveCoverCheck 11 (childHL (childHL (childLH thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childHL (childLH thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11001220 e24KC2ThetaBelowLeaf11001221 e24KC2ThetaBelowLeaf11001222
      e24KC2ThetaBelowLeaf11001223

theorem e24KC2ThetaBelowNode1100123 :
    adaptiveCoverCheck 11 (childHH (childHL (childLH thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childHL (childLH thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11001230 e24KC2ThetaBelowLeaf11001231 e24KC2ThetaBelowLeaf11001232
      e24KC2ThetaBelowLeaf11001233

theorem e24KC2ThetaBelowNode1100132 :
    adaptiveCoverCheck 11 (childHL (childHH (childLH thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childHH (childLH thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11001320 e24KC2ThetaBelowLeaf11001321 e24KC2ThetaBelowLeaf11001322
      e24KC2ThetaBelowLeaf11001323

theorem e24KC2ThetaBelowNode1100133 :
    adaptiveCoverCheck 11 (childHH (childHH (childLH thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childHH (childLH thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11001330 e24KC2ThetaBelowLeaf11001331 e24KC2ThetaBelowLeaf11001332
      e24KC2ThetaBelowLeaf11001333

theorem e24KC2ThetaBelowNode1100200 :
    adaptiveCoverCheck 11 (childLL (childLL (childHL thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLL (childHL thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11002000 e24KC2ThetaBelowLeaf11002001 e24KC2ThetaBelowLeaf11002002
      e24KC2ThetaBelowLeaf11002003

theorem e24KC2ThetaBelowNode1100201 :
    adaptiveCoverCheck 11 (childLH (childLL (childHL thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLL (childHL thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11002010 e24KC2ThetaBelowLeaf11002011 e24KC2ThetaBelowLeaf11002012
      e24KC2ThetaBelowLeaf11002013

theorem e24KC2ThetaBelowNode1100202 :
    adaptiveCoverCheck 11 (childHL (childLL (childHL thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLL (childHL thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11002020 e24KC2ThetaBelowLeaf11002021 e24KC2ThetaBelowLeaf11002022
      e24KC2ThetaBelowLeaf11002023

theorem e24KC2ThetaBelowNode1100203 :
    adaptiveCoverCheck 11 (childHH (childLL (childHL thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLL (childHL thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11002030 e24KC2ThetaBelowLeaf11002031 e24KC2ThetaBelowLeaf11002032
      e24KC2ThetaBelowLeaf11002033

theorem e24KC2ThetaBelowNode1100210 :
    adaptiveCoverCheck 11 (childLL (childLH (childHL thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLH (childHL thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11002100 e24KC2ThetaBelowLeaf11002101 e24KC2ThetaBelowLeaf11002102
      e24KC2ThetaBelowLeaf11002103

theorem e24KC2ThetaBelowNode1100211 :
    adaptiveCoverCheck 11 (childLH (childLH (childHL thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLH (childHL thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11002110 e24KC2ThetaBelowLeaf11002111 e24KC2ThetaBelowLeaf11002112
      e24KC2ThetaBelowLeaf11002113

theorem e24KC2ThetaBelowNode1100212 :
    adaptiveCoverCheck 11 (childHL (childLH (childHL thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLH (childHL thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11002120 e24KC2ThetaBelowLeaf11002121 e24KC2ThetaBelowLeaf11002122
      e24KC2ThetaBelowLeaf11002123

theorem e24KC2ThetaBelowNode1100213 :
    adaptiveCoverCheck 11 (childHH (childLH (childHL thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLH (childHL thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11002130 e24KC2ThetaBelowLeaf11002131 e24KC2ThetaBelowLeaf11002132
      e24KC2ThetaBelowLeaf11002133

theorem e24KC2ThetaBelowNode1100300 :
    adaptiveCoverCheck 11 (childLL (childLL (childHH thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLL (childHH thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11003000 e24KC2ThetaBelowLeaf11003001 e24KC2ThetaBelowLeaf11003002
      e24KC2ThetaBelowLeaf11003003

theorem e24KC2ThetaBelowNode1100301 :
    adaptiveCoverCheck 11 (childLH (childLL (childHH thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLL (childHH thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11003010 e24KC2ThetaBelowLeaf11003011 e24KC2ThetaBelowLeaf11003012
      e24KC2ThetaBelowLeaf11003013

theorem e24KC2ThetaBelowNode1100302 :
    adaptiveCoverCheck 11 (childHL (childLL (childHH thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLL (childHH thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11003020 e24KC2ThetaBelowLeaf11003021 e24KC2ThetaBelowLeaf11003022
      e24KC2ThetaBelowLeaf11003023

theorem e24KC2ThetaBelowNode1100303 :
    adaptiveCoverCheck 11 (childHH (childLL (childHH thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLL (childHH thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11003030 e24KC2ThetaBelowLeaf11003031 e24KC2ThetaBelowLeaf11003032
      e24KC2ThetaBelowLeaf11003033

theorem e24KC2ThetaBelowNode1100310 :
    adaptiveCoverCheck 11 (childLL (childLH (childHH thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLH (childHH thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11003100 e24KC2ThetaBelowLeaf11003101 e24KC2ThetaBelowLeaf11003102
      e24KC2ThetaBelowLeaf11003103

theorem e24KC2ThetaBelowNode1100311 :
    adaptiveCoverCheck 11 (childLH (childLH (childHH thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLH (childHH thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11003110 e24KC2ThetaBelowLeaf11003111 e24KC2ThetaBelowLeaf11003112
      e24KC2ThetaBelowLeaf11003113

theorem e24KC2ThetaBelowNode1100312 :
    adaptiveCoverCheck 11 (childHL (childLH (childHH thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLH (childHH thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11003120 e24KC2ThetaBelowLeaf11003121 e24KC2ThetaBelowLeaf11003122
      e24KC2ThetaBelowLeaf11003123

theorem e24KC2ThetaBelowNode1100313 :
    adaptiveCoverCheck 11 (childHH (childLH (childHH thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLH (childHH thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11003130 e24KC2ThetaBelowLeaf11003131 e24KC2ThetaBelowLeaf11003132
      e24KC2ThetaBelowLeaf11003133

theorem e24KC2ThetaBelowNode1100330 :
    adaptiveCoverCheck 11 (childLL (childHH (childHH thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childHH (childHH thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11003300 e24KC2ThetaBelowLeaf11003301 e24KC2ThetaBelowLeaf11003302
      e24KC2ThetaBelowLeaf11003303

theorem e24KC2ThetaBelowNode1100331 :
    adaptiveCoverCheck 11 (childLH (childHH (childHH thetaBelowCell1100))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childHH (childHH thetaBelowCell1100)))
    e24KC2ThetaBelowLeaf11003310 e24KC2ThetaBelowLeaf11003311 e24KC2ThetaBelowLeaf11003312
      e24KC2ThetaBelowLeaf11003313

theorem e24KC2ThetaBelowNode1101022 :
    adaptiveCoverCheck 11 (childHL (childHL (childLL thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childHL (childLL thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11010220 e24KC2ThetaBelowLeaf11010221 e24KC2ThetaBelowLeaf11010222
      e24KC2ThetaBelowLeaf11010223

theorem e24KC2ThetaBelowNode1101023 :
    adaptiveCoverCheck 11 (childHH (childHL (childLL thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childHL (childLL thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11010230 e24KC2ThetaBelowLeaf11010231 e24KC2ThetaBelowLeaf11010232
      e24KC2ThetaBelowLeaf11010233

theorem e24KC2ThetaBelowNode1101200 :
    adaptiveCoverCheck 11 (childLL (childLL (childHL thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLL (childHL thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11012000 e24KC2ThetaBelowLeaf11012001 e24KC2ThetaBelowLeaf11012002
      e24KC2ThetaBelowLeaf11012003

theorem e24KC2ThetaBelowNode1101201 :
    adaptiveCoverCheck 11 (childLH (childLL (childHL thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLL (childHL thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11012010 e24KC2ThetaBelowLeaf11012011 e24KC2ThetaBelowLeaf11012012
      e24KC2ThetaBelowLeaf11012013

theorem e24KC2ThetaBelowNode1101202 :
    adaptiveCoverCheck 11 (childHL (childLL (childHL thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLL (childHL thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11012020 e24KC2ThetaBelowLeaf11012021 e24KC2ThetaBelowLeaf11012022
      e24KC2ThetaBelowLeaf11012023

theorem e24KC2ThetaBelowNode1101203 :
    adaptiveCoverCheck 11 (childHH (childLL (childHL thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLL (childHL thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11012030 e24KC2ThetaBelowLeaf11012031 e24KC2ThetaBelowLeaf11012032
      e24KC2ThetaBelowLeaf11012033

theorem e24KC2ThetaBelowNode1101210 :
    adaptiveCoverCheck 11 (childLL (childLH (childHL thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLH (childHL thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11012100 e24KC2ThetaBelowLeaf11012101 e24KC2ThetaBelowLeaf11012102
      e24KC2ThetaBelowLeaf11012103

theorem e24KC2ThetaBelowNode1101211 :
    adaptiveCoverCheck 11 (childLH (childLH (childHL thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLH (childHL thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11012110 e24KC2ThetaBelowLeaf11012111 e24KC2ThetaBelowLeaf11012112
      e24KC2ThetaBelowLeaf11012113

theorem e24KC2ThetaBelowNode1101212 :
    adaptiveCoverCheck 11 (childHL (childLH (childHL thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLH (childHL thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11012120 e24KC2ThetaBelowLeaf11012121 e24KC2ThetaBelowLeaf11012122
      e24KC2ThetaBelowLeaf11012123

theorem e24KC2ThetaBelowNode1101213 :
    adaptiveCoverCheck 11 (childHH (childLH (childHL thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLH (childHL thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11012130 e24KC2ThetaBelowLeaf11012131 e24KC2ThetaBelowNode11012132
      e24KC2ThetaBelowNode11012133

theorem e24KC2ThetaBelowNode1101220 :
    adaptiveCoverCheck 11 (childLL (childHL (childHL thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childHL (childHL thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11012200 e24KC2ThetaBelowLeaf11012201 e24KC2ThetaBelowLeaf11012202
      e24KC2ThetaBelowLeaf11012203

theorem e24KC2ThetaBelowNode1101221 :
    adaptiveCoverCheck 11 (childLH (childHL (childHL thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childHL (childHL thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11012210 e24KC2ThetaBelowLeaf11012211 e24KC2ThetaBelowLeaf11012212
      e24KC2ThetaBelowLeaf11012213

theorem e24KC2ThetaBelowNode1101230 :
    adaptiveCoverCheck 11 (childLL (childHH (childHL thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childHH (childHL thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11012300 e24KC2ThetaBelowLeaf11012301 e24KC2ThetaBelowLeaf11012302
      e24KC2ThetaBelowLeaf11012303

theorem e24KC2ThetaBelowNode1101231 :
    adaptiveCoverCheck 11 (childLH (childHH (childHL thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childHH (childHL thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11012310 e24KC2ThetaBelowLeaf11012311 e24KC2ThetaBelowLeaf11012312
      e24KC2ThetaBelowLeaf11012313

theorem e24KC2ThetaBelowNode1101300 :
    adaptiveCoverCheck 11 (childLL (childLL (childHH thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLL (childHH thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11013000 e24KC2ThetaBelowLeaf11013001 e24KC2ThetaBelowLeaf11013002
      e24KC2ThetaBelowLeaf11013003

theorem e24KC2ThetaBelowNode1101301 :
    adaptiveCoverCheck 11 (childLH (childLL (childHH thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLL (childHH thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11013010 e24KC2ThetaBelowLeaf11013011 e24KC2ThetaBelowLeaf11013012
      e24KC2ThetaBelowNode11013013

theorem e24KC2ThetaBelowNode1101302 :
    adaptiveCoverCheck 11 (childHL (childLL (childHH thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLL (childHH thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11013020 e24KC2ThetaBelowNode11013021 e24KC2ThetaBelowNode11013022
      e24KC2ThetaBelowNode11013023

theorem e24KC2ThetaBelowNode1101303 :
    adaptiveCoverCheck 11 (childHH (childLL (childHH thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLL (childHH thetaBelowCell1101)))
    e24KC2ThetaBelowNode11013030 e24KC2ThetaBelowNode11013031 e24KC2ThetaBelowNode11013032
      e24KC2ThetaBelowNode11013033

theorem e24KC2ThetaBelowNode1101310 :
    adaptiveCoverCheck 11 (childLL (childLH (childHH thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLH (childHH thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11013100 e24KC2ThetaBelowLeaf11013101 e24KC2ThetaBelowNode11013102
      e24KC2ThetaBelowNode11013103

theorem e24KC2ThetaBelowNode1101311 :
    adaptiveCoverCheck 11 (childLH (childLH (childHH thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLH (childHH thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11013110 e24KC2ThetaBelowLeaf11013111 e24KC2ThetaBelowNode11013112
      e24KC2ThetaBelowNode11013113

theorem e24KC2ThetaBelowNode1101312 :
    adaptiveCoverCheck 11 (childHL (childLH (childHH thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLH (childHH thetaBelowCell1101)))
    e24KC2ThetaBelowNode11013120 e24KC2ThetaBelowNode11013121 e24KC2ThetaBelowNode11013122
      e24KC2ThetaBelowNode11013123

theorem e24KC2ThetaBelowNode1101313 :
    adaptiveCoverCheck 11 (childHH (childLH (childHH thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLH (childHH thetaBelowCell1101)))
    e24KC2ThetaBelowNode11013130 e24KC2ThetaBelowNode11013131 e24KC2ThetaBelowNode11013132
      e24KC2ThetaBelowNode11013133

theorem e24KC2ThetaBelowNode1101320 :
    adaptiveCoverCheck 11 (childLL (childHL (childHH thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childHL (childHH thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11013200 e24KC2ThetaBelowLeaf11013201 e24KC2ThetaBelowLeaf11013202
      e24KC2ThetaBelowLeaf11013203

theorem e24KC2ThetaBelowNode1101321 :
    adaptiveCoverCheck 11 (childLH (childHL (childHH thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childHL (childHH thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11013210 e24KC2ThetaBelowLeaf11013211 e24KC2ThetaBelowLeaf11013212
      e24KC2ThetaBelowLeaf11013213

theorem e24KC2ThetaBelowNode1101330 :
    adaptiveCoverCheck 11 (childLL (childHH (childHH thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childHH (childHH thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11013300 e24KC2ThetaBelowLeaf11013301 e24KC2ThetaBelowLeaf11013302
      e24KC2ThetaBelowLeaf11013303

theorem e24KC2ThetaBelowNode1101331 :
    adaptiveCoverCheck 11 (childLH (childHH (childHH thetaBelowCell1101))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childHH (childHH thetaBelowCell1101)))
    e24KC2ThetaBelowLeaf11013310 e24KC2ThetaBelowLeaf11013311 e24KC2ThetaBelowLeaf11013312
      e24KC2ThetaBelowLeaf11013313

theorem e24KC2ThetaBelowNode1110200 :
    adaptiveCoverCheck 11 (childLL (childLL (childHL thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLL (childHL thetaBelowCell1110)))
    e24KC2ThetaBelowLeaf11102000 e24KC2ThetaBelowLeaf11102001 e24KC2ThetaBelowNode11102002
      e24KC2ThetaBelowNode11102003

theorem e24KC2ThetaBelowNode1110201 :
    adaptiveCoverCheck 11 (childLH (childLL (childHL thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLL (childHL thetaBelowCell1110)))
    e24KC2ThetaBelowLeaf11102010 e24KC2ThetaBelowLeaf11102011 e24KC2ThetaBelowNode11102012
      e24KC2ThetaBelowNode11102013

theorem e24KC2ThetaBelowNode1110202 :
    adaptiveCoverCheck 11 (childHL (childLL (childHL thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLL (childHL thetaBelowCell1110)))
    e24KC2ThetaBelowNode11102020 e24KC2ThetaBelowNode11102021 e24KC2ThetaBelowNode11102022
      e24KC2ThetaBelowNode11102023

theorem e24KC2ThetaBelowNode1110203 :
    adaptiveCoverCheck 11 (childHH (childLL (childHL thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLL (childHL thetaBelowCell1110)))
    e24KC2ThetaBelowNode11102030 e24KC2ThetaBelowNode11102031 e24KC2ThetaBelowNode11102032
      e24KC2ThetaBelowNode11102033

theorem e24KC2ThetaBelowNode1110210 :
    adaptiveCoverCheck 11 (childLL (childLH (childHL thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLH (childHL thetaBelowCell1110)))
    e24KC2ThetaBelowLeaf11102100 e24KC2ThetaBelowLeaf11102101 e24KC2ThetaBelowLeaf11102102
      e24KC2ThetaBelowLeaf11102103

theorem e24KC2ThetaBelowNode1110211 :
    adaptiveCoverCheck 11 (childLH (childLH (childHL thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLH (childHL thetaBelowCell1110)))
    e24KC2ThetaBelowLeaf11102110 e24KC2ThetaBelowLeaf11102111 e24KC2ThetaBelowLeaf11102112
      e24KC2ThetaBelowLeaf11102113

theorem e24KC2ThetaBelowNode1110212 :
    adaptiveCoverCheck 11 (childHL (childLH (childHL thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLH (childHL thetaBelowCell1110)))
    e24KC2ThetaBelowNode11102120 e24KC2ThetaBelowNode11102121 e24KC2ThetaBelowNode11102122
      e24KC2ThetaBelowNode11102123

theorem e24KC2ThetaBelowNode1110213 :
    adaptiveCoverCheck 11 (childHH (childLH (childHL thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLH (childHL thetaBelowCell1110)))
    e24KC2ThetaBelowNode11102130 e24KC2ThetaBelowNode11102131 e24KC2ThetaBelowNode11102132
      e24KC2ThetaBelowNode11102133

theorem e24KC2ThetaBelowNode1110220 :
    adaptiveCoverCheck 11 (childLL (childHL (childHL thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childHL (childHL thetaBelowCell1110)))
    e24KC2ThetaBelowNode11102200 e24KC2ThetaBelowNode11102201 e24KC2ThetaBelowLeaf11102202
      e24KC2ThetaBelowLeaf11102203

theorem e24KC2ThetaBelowNode1110221 :
    adaptiveCoverCheck 11 (childLH (childHL (childHL thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childHL (childHL thetaBelowCell1110)))
    e24KC2ThetaBelowNode11102210 e24KC2ThetaBelowNode11102211 e24KC2ThetaBelowLeaf11102212
      e24KC2ThetaBelowLeaf11102213

theorem e24KC2ThetaBelowNode1110230 :
    adaptiveCoverCheck 11 (childLL (childHH (childHL thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childHH (childHL thetaBelowCell1110)))
    e24KC2ThetaBelowNode11102300 e24KC2ThetaBelowNode11102301 e24KC2ThetaBelowLeaf11102302
      e24KC2ThetaBelowLeaf11102303

theorem e24KC2ThetaBelowNode1110231 :
    adaptiveCoverCheck 11 (childLH (childHH (childHL thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childHH (childHL thetaBelowCell1110)))
    e24KC2ThetaBelowNode11102310 e24KC2ThetaBelowNode11102311 e24KC2ThetaBelowLeaf11102312
      e24KC2ThetaBelowLeaf11102313

theorem e24KC2ThetaBelowNode1110300 :
    adaptiveCoverCheck 11 (childLL (childLL (childHH thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLL (childHH thetaBelowCell1110)))
    e24KC2ThetaBelowLeaf11103000 e24KC2ThetaBelowLeaf11103001 e24KC2ThetaBelowLeaf11103002
      e24KC2ThetaBelowLeaf11103003

theorem e24KC2ThetaBelowNode1110301 :
    adaptiveCoverCheck 11 (childLH (childLL (childHH thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLL (childHH thetaBelowCell1110)))
    e24KC2ThetaBelowLeaf11103010 e24KC2ThetaBelowLeaf11103011 e24KC2ThetaBelowLeaf11103012
      e24KC2ThetaBelowLeaf11103013

theorem e24KC2ThetaBelowNode1110302 :
    adaptiveCoverCheck 11 (childHL (childLL (childHH thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLL (childHH thetaBelowCell1110)))
    e24KC2ThetaBelowNode11103020 e24KC2ThetaBelowNode11103021 e24KC2ThetaBelowNode11103022
      e24KC2ThetaBelowNode11103023

theorem e24KC2ThetaBelowNode1110303 :
    adaptiveCoverCheck 11 (childHH (childLL (childHH thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLL (childHH thetaBelowCell1110)))
    e24KC2ThetaBelowNode11103030 e24KC2ThetaBelowNode11103031 e24KC2ThetaBelowNode11103032
      e24KC2ThetaBelowNode11103033

theorem e24KC2ThetaBelowNode1110310 :
    adaptiveCoverCheck 11 (childLL (childLH (childHH thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLH (childHH thetaBelowCell1110)))
    e24KC2ThetaBelowLeaf11103100 e24KC2ThetaBelowLeaf11103101 e24KC2ThetaBelowLeaf11103102
      e24KC2ThetaBelowLeaf11103103

theorem e24KC2ThetaBelowNode1110311 :
    adaptiveCoverCheck 11 (childLH (childLH (childHH thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLH (childHH thetaBelowCell1110)))
    e24KC2ThetaBelowLeaf11103110 e24KC2ThetaBelowLeaf11103111 e24KC2ThetaBelowLeaf11103112
      e24KC2ThetaBelowLeaf11103113

theorem e24KC2ThetaBelowNode1110312 :
    adaptiveCoverCheck 11 (childHL (childLH (childHH thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLH (childHH thetaBelowCell1110)))
    e24KC2ThetaBelowNode11103120 e24KC2ThetaBelowNode11103121 e24KC2ThetaBelowNode11103122
      e24KC2ThetaBelowNode11103123

theorem e24KC2ThetaBelowNode1110313 :
    adaptiveCoverCheck 11 (childHH (childLH (childHH thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLH (childHH thetaBelowCell1110)))
    e24KC2ThetaBelowNode11103130 e24KC2ThetaBelowNode11103131 e24KC2ThetaBelowNode11103132
      e24KC2ThetaBelowNode11103133

theorem e24KC2ThetaBelowNode1110320 :
    adaptiveCoverCheck 11 (childLL (childHL (childHH thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childHL (childHH thetaBelowCell1110)))
    e24KC2ThetaBelowNode11103200 e24KC2ThetaBelowNode11103201 e24KC2ThetaBelowLeaf11103202
      e24KC2ThetaBelowLeaf11103203

theorem e24KC2ThetaBelowNode1110321 :
    adaptiveCoverCheck 11 (childLH (childHL (childHH thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childHL (childHH thetaBelowCell1110)))
    e24KC2ThetaBelowNode11103210 e24KC2ThetaBelowNode11103211 e24KC2ThetaBelowLeaf11103212
      e24KC2ThetaBelowLeaf11103213

theorem e24KC2ThetaBelowNode1110330 :
    adaptiveCoverCheck 11 (childLL (childHH (childHH thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childHH (childHH thetaBelowCell1110)))
    e24KC2ThetaBelowNode11103300 e24KC2ThetaBelowNode11103301 e24KC2ThetaBelowLeaf11103302
      e24KC2ThetaBelowLeaf11103303

theorem e24KC2ThetaBelowNode1110331 :
    adaptiveCoverCheck 11 (childLH (childHH (childHH thetaBelowCell1110))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childHH (childHH thetaBelowCell1110)))
    e24KC2ThetaBelowNode11103310 e24KC2ThetaBelowNode11103311 e24KC2ThetaBelowLeaf11103312
      e24KC2ThetaBelowLeaf11103313

theorem e24KC2ThetaBelowNode1111200 :
    adaptiveCoverCheck 11 (childLL (childLL (childHL thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLL (childHL thetaBelowCell1111)))
    e24KC2ThetaBelowLeaf11112000 e24KC2ThetaBelowLeaf11112001 e24KC2ThetaBelowLeaf11112002
      e24KC2ThetaBelowLeaf11112003

theorem e24KC2ThetaBelowNode1111201 :
    adaptiveCoverCheck 11 (childLH (childLL (childHL thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLL (childHL thetaBelowCell1111)))
    e24KC2ThetaBelowLeaf11112010 e24KC2ThetaBelowLeaf11112011 e24KC2ThetaBelowLeaf11112012
      e24KC2ThetaBelowLeaf11112013

theorem e24KC2ThetaBelowNode1111202 :
    adaptiveCoverCheck 11 (childHL (childLL (childHL thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLL (childHL thetaBelowCell1111)))
    e24KC2ThetaBelowNode11112020 e24KC2ThetaBelowNode11112021 e24KC2ThetaBelowNode11112022
      e24KC2ThetaBelowNode11112023

theorem e24KC2ThetaBelowNode1111203 :
    adaptiveCoverCheck 11 (childHH (childLL (childHL thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLL (childHL thetaBelowCell1111)))
    e24KC2ThetaBelowNode11112030 e24KC2ThetaBelowNode11112031 e24KC2ThetaBelowNode11112032
      e24KC2ThetaBelowNode11112033

theorem e24KC2ThetaBelowNode1111210 :
    adaptiveCoverCheck 11 (childLL (childLH (childHL thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childLH (childHL thetaBelowCell1111)))
    e24KC2ThetaBelowLeaf11112100 e24KC2ThetaBelowLeaf11112101 e24KC2ThetaBelowLeaf11112102
      e24KC2ThetaBelowLeaf11112103

theorem e24KC2ThetaBelowNode1111211 :
    adaptiveCoverCheck 11 (childLH (childLH (childHL thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childLH (childHL thetaBelowCell1111)))
    e24KC2ThetaBelowLeaf11112110 e24KC2ThetaBelowLeaf11112111 e24KC2ThetaBelowLeaf11112112
      e24KC2ThetaBelowLeaf11112113

theorem e24KC2ThetaBelowNode1111212 :
    adaptiveCoverCheck 11 (childHL (childLH (childHL thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLH (childHL thetaBelowCell1111)))
    e24KC2ThetaBelowNode11112120 e24KC2ThetaBelowNode11112121 e24KC2ThetaBelowNode11112122
      e24KC2ThetaBelowNode11112123

theorem e24KC2ThetaBelowNode1111213 :
    adaptiveCoverCheck 11 (childHH (childLH (childHL thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLH (childHL thetaBelowCell1111)))
    e24KC2ThetaBelowNode11112130 e24KC2ThetaBelowLeaf11112131 e24KC2ThetaBelowNode11112132
      e24KC2ThetaBelowNode11112133

theorem e24KC2ThetaBelowNode1111220 :
    adaptiveCoverCheck 11 (childLL (childHL (childHL thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childHL (childHL thetaBelowCell1111)))
    e24KC2ThetaBelowNode11112200 e24KC2ThetaBelowNode11112201 e24KC2ThetaBelowLeaf11112202
      e24KC2ThetaBelowLeaf11112203

theorem e24KC2ThetaBelowNode1111221 :
    adaptiveCoverCheck 11 (childLH (childHL (childHL thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childHL (childHL thetaBelowCell1111)))
    e24KC2ThetaBelowNode11112210 e24KC2ThetaBelowNode11112211 e24KC2ThetaBelowNode11112212
      e24KC2ThetaBelowNode11112213

theorem e24KC2ThetaBelowNode1111222 :
    adaptiveCoverCheck 11 (childHL (childHL (childHL thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childHL (childHL thetaBelowCell1111)))
    e24KC2ThetaBelowLeaf11112220 e24KC2ThetaBelowLeaf11112221 e24KC2ThetaBelowLeaf11112222
      e24KC2ThetaBelowLeaf11112223

theorem e24KC2ThetaBelowNode1111223 :
    adaptiveCoverCheck 11 (childHH (childHL (childHL thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childHL (childHL thetaBelowCell1111)))
    e24KC2ThetaBelowLeaf11112230 e24KC2ThetaBelowLeaf11112231 e24KC2ThetaBelowLeaf11112232
      e24KC2ThetaBelowLeaf11112233

theorem e24KC2ThetaBelowNode1111230 :
    adaptiveCoverCheck 11 (childLL (childHH (childHL thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childHH (childHL thetaBelowCell1111)))
    e24KC2ThetaBelowNode11112300 e24KC2ThetaBelowNode11112301 e24KC2ThetaBelowNode11112302
      e24KC2ThetaBelowNode11112303

theorem e24KC2ThetaBelowNode1111231 :
    adaptiveCoverCheck 11 (childLH (childHH (childHL thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childHH (childHL thetaBelowCell1111)))
    e24KC2ThetaBelowNode11112310 e24KC2ThetaBelowNode11112311 e24KC2ThetaBelowNode11112312
      e24KC2ThetaBelowNode11112313

theorem e24KC2ThetaBelowNode1111232 :
    adaptiveCoverCheck 11 (childHL (childHH (childHL thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childHH (childHL thetaBelowCell1111)))
    e24KC2ThetaBelowLeaf11112320 e24KC2ThetaBelowLeaf11112321 e24KC2ThetaBelowLeaf11112322
      e24KC2ThetaBelowLeaf11112323

theorem e24KC2ThetaBelowNode1111233 :
    adaptiveCoverCheck 11 (childHH (childHH (childHL thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childHH (childHL thetaBelowCell1111)))
    e24KC2ThetaBelowLeaf11112330 e24KC2ThetaBelowLeaf11112331 e24KC2ThetaBelowLeaf11112332
      e24KC2ThetaBelowLeaf11112333

theorem e24KC2ThetaBelowNode1111302 :
    adaptiveCoverCheck 11 (childHL (childLL (childHH thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLL (childHH thetaBelowCell1111)))
    e24KC2ThetaBelowLeaf11113020 e24KC2ThetaBelowLeaf11113021 e24KC2ThetaBelowNode11113022
      e24KC2ThetaBelowNode11113023

theorem e24KC2ThetaBelowNode1111303 :
    adaptiveCoverCheck 11 (childHH (childLL (childHH thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLL (childHH thetaBelowCell1111)))
    e24KC2ThetaBelowLeaf11113030 e24KC2ThetaBelowLeaf11113031 e24KC2ThetaBelowNode11113032
      e24KC2ThetaBelowNode11113033

theorem e24KC2ThetaBelowNode1111312 :
    adaptiveCoverCheck 11 (childHL (childLH (childHH thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childLH (childHH thetaBelowCell1111)))
    e24KC2ThetaBelowLeaf11113120 e24KC2ThetaBelowLeaf11113121 e24KC2ThetaBelowNode11113122
      e24KC2ThetaBelowNode11113123

theorem e24KC2ThetaBelowNode1111313 :
    adaptiveCoverCheck 11 (childHH (childLH (childHH thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childLH (childHH thetaBelowCell1111)))
    e24KC2ThetaBelowLeaf11113130 e24KC2ThetaBelowLeaf11113131 e24KC2ThetaBelowNode11113132
      e24KC2ThetaBelowNode11113133

theorem e24KC2ThetaBelowNode1111320 :
    adaptiveCoverCheck 11 (childLL (childHL (childHH thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childHL (childHH thetaBelowCell1111)))
    e24KC2ThetaBelowNode11113200 e24KC2ThetaBelowNode11113201 e24KC2ThetaBelowNode11113202
      e24KC2ThetaBelowNode11113203

theorem e24KC2ThetaBelowNode1111321 :
    adaptiveCoverCheck 11 (childLH (childHL (childHH thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childHL (childHH thetaBelowCell1111)))
    e24KC2ThetaBelowNode11113210 e24KC2ThetaBelowNode11113211 e24KC2ThetaBelowNode11113212
      e24KC2ThetaBelowNode11113213

theorem e24KC2ThetaBelowNode1111322 :
    adaptiveCoverCheck 11 (childHL (childHL (childHH thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childHL (childHH thetaBelowCell1111)))
    e24KC2ThetaBelowLeaf11113220 e24KC2ThetaBelowLeaf11113221 e24KC2ThetaBelowLeaf11113222
      e24KC2ThetaBelowLeaf11113223

theorem e24KC2ThetaBelowNode1111323 :
    adaptiveCoverCheck 11 (childHH (childHL (childHH thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childHL (childHH thetaBelowCell1111)))
    e24KC2ThetaBelowLeaf11113230 e24KC2ThetaBelowLeaf11113231 e24KC2ThetaBelowLeaf11113232
      e24KC2ThetaBelowLeaf11113233

theorem e24KC2ThetaBelowNode1111330 :
    adaptiveCoverCheck 11 (childLL (childHH (childHH thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLL (childHH (childHH thetaBelowCell1111)))
    e24KC2ThetaBelowNode11113300 e24KC2ThetaBelowNode11113301 e24KC2ThetaBelowNode11113302
      e24KC2ThetaBelowNode11113303

theorem e24KC2ThetaBelowNode1111331 :
    adaptiveCoverCheck 11 (childLH (childHH (childHH thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childLH (childHH (childHH thetaBelowCell1111)))
    e24KC2ThetaBelowNode11113310 e24KC2ThetaBelowNode11113311 e24KC2ThetaBelowNode11113312
      e24KC2ThetaBelowNode11113313

theorem e24KC2ThetaBelowNode1111332 :
    adaptiveCoverCheck 11 (childHL (childHH (childHH thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHL (childHH (childHH thetaBelowCell1111)))
    e24KC2ThetaBelowLeaf11113320 e24KC2ThetaBelowLeaf11113321 e24KC2ThetaBelowLeaf11113322
      e24KC2ThetaBelowLeaf11113323

theorem e24KC2ThetaBelowNode1111333 :
    adaptiveCoverCheck 11 (childHH (childHH (childHH thetaBelowCell1111))) = true :=
  adaptiveCoverCheck_succ_of_children 10 (childHH (childHH (childHH thetaBelowCell1111)))
    e24KC2ThetaBelowLeaf11113330 e24KC2ThetaBelowLeaf11113331 e24KC2ThetaBelowLeaf11113332
      e24KC2ThetaBelowLeaf11113333

theorem e24KC2ThetaBelowNode100113 :
    adaptiveCoverCheck 12 (childHH (childLH thetaBelowCell1001)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH thetaBelowCell1001))
    e24KC2ThetaBelowLeaf1001130 e24KC2ThetaBelowLeaf1001131 e24KC2ThetaBelowLeaf1001132
      e24KC2ThetaBelowLeaf1001133

theorem e24KC2ThetaBelowNode100121 :
    adaptiveCoverCheck 12 (childLH (childHL thetaBelowCell1001)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL thetaBelowCell1001))
    e24KC2ThetaBelowLeaf1001210 e24KC2ThetaBelowLeaf1001211 e24KC2ThetaBelowLeaf1001212
      e24KC2ThetaBelowLeaf1001213

theorem e24KC2ThetaBelowNode100130 :
    adaptiveCoverCheck 12 (childLL (childHH thetaBelowCell1001)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH thetaBelowCell1001))
    e24KC2ThetaBelowLeaf1001300 e24KC2ThetaBelowLeaf1001301 e24KC2ThetaBelowLeaf1001302
      e24KC2ThetaBelowLeaf1001303

theorem e24KC2ThetaBelowNode100131 :
    adaptiveCoverCheck 12 (childLH (childHH thetaBelowCell1001)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH thetaBelowCell1001))
    e24KC2ThetaBelowLeaf1001310 e24KC2ThetaBelowLeaf1001311 e24KC2ThetaBelowLeaf1001312
      e24KC2ThetaBelowLeaf1001313

theorem e24KC2ThetaBelowNode101001 :
    adaptiveCoverCheck 12 (childLH (childLL thetaBelowCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childLL thetaBelowCell1010))
    e24KC2ThetaBelowLeaf1010010 e24KC2ThetaBelowLeaf1010011 e24KC2ThetaBelowLeaf1010012
      e24KC2ThetaBelowLeaf1010013

theorem e24KC2ThetaBelowNode101002 :
    adaptiveCoverCheck 12 (childHL (childLL thetaBelowCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL thetaBelowCell1010))
    e24KC2ThetaBelowLeaf1010020 e24KC2ThetaBelowLeaf1010021 e24KC2ThetaBelowLeaf1010022
      e24KC2ThetaBelowLeaf1010023

theorem e24KC2ThetaBelowNode101003 :
    adaptiveCoverCheck 12 (childHH (childLL thetaBelowCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL thetaBelowCell1010))
    e24KC2ThetaBelowLeaf1010030 e24KC2ThetaBelowLeaf1010031 e24KC2ThetaBelowLeaf1010032
      e24KC2ThetaBelowLeaf1010033

theorem e24KC2ThetaBelowNode101010 :
    adaptiveCoverCheck 12 (childLL (childLH thetaBelowCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childLH thetaBelowCell1010))
    e24KC2ThetaBelowLeaf1010100 e24KC2ThetaBelowLeaf1010101 e24KC2ThetaBelowLeaf1010102
      e24KC2ThetaBelowLeaf1010103

theorem e24KC2ThetaBelowNode101011 :
    adaptiveCoverCheck 12 (childLH (childLH thetaBelowCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childLH thetaBelowCell1010))
    e24KC2ThetaBelowLeaf1010110 e24KC2ThetaBelowLeaf1010111 e24KC2ThetaBelowLeaf1010112
      e24KC2ThetaBelowLeaf1010113

theorem e24KC2ThetaBelowNode101012 :
    adaptiveCoverCheck 12 (childHL (childLH thetaBelowCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH thetaBelowCell1010))
    e24KC2ThetaBelowLeaf1010120 e24KC2ThetaBelowLeaf1010121 e24KC2ThetaBelowLeaf1010122
      e24KC2ThetaBelowLeaf1010123

theorem e24KC2ThetaBelowNode101013 :
    adaptiveCoverCheck 12 (childHH (childLH thetaBelowCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH thetaBelowCell1010))
    e24KC2ThetaBelowLeaf1010130 e24KC2ThetaBelowLeaf1010131 e24KC2ThetaBelowLeaf1010132
      e24KC2ThetaBelowLeaf1010133

theorem e24KC2ThetaBelowNode101020 :
    adaptiveCoverCheck 12 (childLL (childHL thetaBelowCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL thetaBelowCell1010))
    e24KC2ThetaBelowLeaf1010200 e24KC2ThetaBelowLeaf1010201 e24KC2ThetaBelowLeaf1010202
      e24KC2ThetaBelowLeaf1010203

theorem e24KC2ThetaBelowNode101021 :
    adaptiveCoverCheck 12 (childLH (childHL thetaBelowCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL thetaBelowCell1010))
    e24KC2ThetaBelowLeaf1010210 e24KC2ThetaBelowLeaf1010211 e24KC2ThetaBelowLeaf1010212
      e24KC2ThetaBelowLeaf1010213

theorem e24KC2ThetaBelowNode101030 :
    adaptiveCoverCheck 12 (childLL (childHH thetaBelowCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH thetaBelowCell1010))
    e24KC2ThetaBelowLeaf1010300 e24KC2ThetaBelowLeaf1010301 e24KC2ThetaBelowLeaf1010302
      e24KC2ThetaBelowLeaf1010303

theorem e24KC2ThetaBelowNode101031 :
    adaptiveCoverCheck 12 (childLH (childHH thetaBelowCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH thetaBelowCell1010))
    e24KC2ThetaBelowLeaf1010310 e24KC2ThetaBelowLeaf1010311 e24KC2ThetaBelowLeaf1010312
      e24KC2ThetaBelowLeaf1010313

theorem e24KC2ThetaBelowNode101032 :
    adaptiveCoverCheck 12 (childHL (childHH thetaBelowCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH thetaBelowCell1010))
    e24KC2ThetaBelowLeaf1010320 e24KC2ThetaBelowLeaf1010321 e24KC2ThetaBelowLeaf1010322
      e24KC2ThetaBelowLeaf1010323

theorem e24KC2ThetaBelowNode101033 :
    adaptiveCoverCheck 12 (childHH (childHH thetaBelowCell1010)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH thetaBelowCell1010))
    e24KC2ThetaBelowLeaf1010330 e24KC2ThetaBelowLeaf1010331 e24KC2ThetaBelowLeaf1010332
      e24KC2ThetaBelowLeaf1010333

theorem e24KC2ThetaBelowNode101100 :
    adaptiveCoverCheck 12 (childLL (childLL thetaBelowCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childLL thetaBelowCell1011))
    e24KC2ThetaBelowLeaf1011000 e24KC2ThetaBelowLeaf1011001 e24KC2ThetaBelowLeaf1011002
      e24KC2ThetaBelowLeaf1011003

theorem e24KC2ThetaBelowNode101102 :
    adaptiveCoverCheck 12 (childHL (childLL thetaBelowCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL thetaBelowCell1011))
    e24KC2ThetaBelowLeaf1011020 e24KC2ThetaBelowLeaf1011021 e24KC2ThetaBelowLeaf1011022
      e24KC2ThetaBelowLeaf1011023

theorem e24KC2ThetaBelowNode101103 :
    adaptiveCoverCheck 12 (childHH (childLL thetaBelowCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL thetaBelowCell1011))
    e24KC2ThetaBelowLeaf1011030 e24KC2ThetaBelowLeaf1011031 e24KC2ThetaBelowLeaf1011032
      e24KC2ThetaBelowLeaf1011033

theorem e24KC2ThetaBelowNode101112 :
    adaptiveCoverCheck 12 (childHL (childLH thetaBelowCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH thetaBelowCell1011))
    e24KC2ThetaBelowLeaf1011120 e24KC2ThetaBelowLeaf1011121 e24KC2ThetaBelowLeaf1011122
      e24KC2ThetaBelowLeaf1011123

theorem e24KC2ThetaBelowNode101113 :
    adaptiveCoverCheck 12 (childHH (childLH thetaBelowCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH thetaBelowCell1011))
    e24KC2ThetaBelowLeaf1011130 e24KC2ThetaBelowLeaf1011131 e24KC2ThetaBelowLeaf1011132
      e24KC2ThetaBelowLeaf1011133

theorem e24KC2ThetaBelowNode101120 :
    adaptiveCoverCheck 12 (childLL (childHL thetaBelowCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL thetaBelowCell1011))
    e24KC2ThetaBelowLeaf1011200 e24KC2ThetaBelowLeaf1011201 e24KC2ThetaBelowLeaf1011202
      e24KC2ThetaBelowLeaf1011203

theorem e24KC2ThetaBelowNode101121 :
    adaptiveCoverCheck 12 (childLH (childHL thetaBelowCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL thetaBelowCell1011))
    e24KC2ThetaBelowLeaf1011210 e24KC2ThetaBelowLeaf1011211 e24KC2ThetaBelowLeaf1011212
      e24KC2ThetaBelowLeaf1011213

theorem e24KC2ThetaBelowNode101122 :
    adaptiveCoverCheck 12 (childHL (childHL thetaBelowCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL thetaBelowCell1011))
    e24KC2ThetaBelowLeaf1011220 e24KC2ThetaBelowLeaf1011221 e24KC2ThetaBelowLeaf1011222
      e24KC2ThetaBelowLeaf1011223

theorem e24KC2ThetaBelowNode101123 :
    adaptiveCoverCheck 12 (childHH (childHL thetaBelowCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL thetaBelowCell1011))
    e24KC2ThetaBelowLeaf1011230 e24KC2ThetaBelowLeaf1011231 e24KC2ThetaBelowLeaf1011232
      e24KC2ThetaBelowLeaf1011233

theorem e24KC2ThetaBelowNode101130 :
    adaptiveCoverCheck 12 (childLL (childHH thetaBelowCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH thetaBelowCell1011))
    e24KC2ThetaBelowLeaf1011300 e24KC2ThetaBelowLeaf1011301 e24KC2ThetaBelowLeaf1011302
      e24KC2ThetaBelowNode1011303

theorem e24KC2ThetaBelowNode101131 :
    adaptiveCoverCheck 12 (childLH (childHH thetaBelowCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH thetaBelowCell1011))
    e24KC2ThetaBelowLeaf1011310 e24KC2ThetaBelowNode1011311 e24KC2ThetaBelowNode1011312
      e24KC2ThetaBelowNode1011313

theorem e24KC2ThetaBelowNode101132 :
    adaptiveCoverCheck 12 (childHL (childHH thetaBelowCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH thetaBelowCell1011))
    e24KC2ThetaBelowLeaf1011320 e24KC2ThetaBelowLeaf1011321 e24KC2ThetaBelowLeaf1011322
      e24KC2ThetaBelowLeaf1011323

theorem e24KC2ThetaBelowNode101133 :
    adaptiveCoverCheck 12 (childHH (childHH thetaBelowCell1011)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH thetaBelowCell1011))
    e24KC2ThetaBelowLeaf1011330 e24KC2ThetaBelowLeaf1011331 e24KC2ThetaBelowLeaf1011332
      e24KC2ThetaBelowLeaf1011333

theorem e24KC2ThetaBelowNode110002 :
    adaptiveCoverCheck 12 (childHL (childLL thetaBelowCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL thetaBelowCell1100))
    e24KC2ThetaBelowLeaf1100020 e24KC2ThetaBelowLeaf1100021 e24KC2ThetaBelowLeaf1100022
      e24KC2ThetaBelowLeaf1100023

theorem e24KC2ThetaBelowNode110003 :
    adaptiveCoverCheck 12 (childHH (childLL thetaBelowCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL thetaBelowCell1100))
    e24KC2ThetaBelowLeaf1100030 e24KC2ThetaBelowLeaf1100031 e24KC2ThetaBelowNode1100032
      e24KC2ThetaBelowNode1100033

theorem e24KC2ThetaBelowNode110012 :
    adaptiveCoverCheck 12 (childHL (childLH thetaBelowCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH thetaBelowCell1100))
    e24KC2ThetaBelowLeaf1100120 e24KC2ThetaBelowLeaf1100121 e24KC2ThetaBelowNode1100122
      e24KC2ThetaBelowNode1100123

theorem e24KC2ThetaBelowNode110013 :
    adaptiveCoverCheck 12 (childHH (childLH thetaBelowCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH thetaBelowCell1100))
    e24KC2ThetaBelowLeaf1100130 e24KC2ThetaBelowLeaf1100131 e24KC2ThetaBelowNode1100132
      e24KC2ThetaBelowNode1100133

theorem e24KC2ThetaBelowNode110020 :
    adaptiveCoverCheck 12 (childLL (childHL thetaBelowCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL thetaBelowCell1100))
    e24KC2ThetaBelowNode1100200 e24KC2ThetaBelowNode1100201 e24KC2ThetaBelowNode1100202
      e24KC2ThetaBelowNode1100203

theorem e24KC2ThetaBelowNode110021 :
    adaptiveCoverCheck 12 (childLH (childHL thetaBelowCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL thetaBelowCell1100))
    e24KC2ThetaBelowNode1100210 e24KC2ThetaBelowNode1100211 e24KC2ThetaBelowNode1100212
      e24KC2ThetaBelowNode1100213

theorem e24KC2ThetaBelowNode110022 :
    adaptiveCoverCheck 12 (childHL (childHL thetaBelowCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL thetaBelowCell1100))
    e24KC2ThetaBelowLeaf1100220 e24KC2ThetaBelowLeaf1100221 e24KC2ThetaBelowLeaf1100222
      e24KC2ThetaBelowLeaf1100223

theorem e24KC2ThetaBelowNode110023 :
    adaptiveCoverCheck 12 (childHH (childHL thetaBelowCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL thetaBelowCell1100))
    e24KC2ThetaBelowLeaf1100230 e24KC2ThetaBelowLeaf1100231 e24KC2ThetaBelowLeaf1100232
      e24KC2ThetaBelowLeaf1100233

theorem e24KC2ThetaBelowNode110030 :
    adaptiveCoverCheck 12 (childLL (childHH thetaBelowCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH thetaBelowCell1100))
    e24KC2ThetaBelowNode1100300 e24KC2ThetaBelowNode1100301 e24KC2ThetaBelowNode1100302
      e24KC2ThetaBelowNode1100303

theorem e24KC2ThetaBelowNode110031 :
    adaptiveCoverCheck 12 (childLH (childHH thetaBelowCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH thetaBelowCell1100))
    e24KC2ThetaBelowNode1100310 e24KC2ThetaBelowNode1100311 e24KC2ThetaBelowNode1100312
      e24KC2ThetaBelowNode1100313

theorem e24KC2ThetaBelowNode110032 :
    adaptiveCoverCheck 12 (childHL (childHH thetaBelowCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH thetaBelowCell1100))
    e24KC2ThetaBelowLeaf1100320 e24KC2ThetaBelowLeaf1100321 e24KC2ThetaBelowLeaf1100322
      e24KC2ThetaBelowLeaf1100323

theorem e24KC2ThetaBelowNode110033 :
    adaptiveCoverCheck 12 (childHH (childHH thetaBelowCell1100)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH thetaBelowCell1100))
    e24KC2ThetaBelowNode1100330 e24KC2ThetaBelowNode1100331 e24KC2ThetaBelowLeaf1100332
      e24KC2ThetaBelowLeaf1100333

theorem e24KC2ThetaBelowNode110102 :
    adaptiveCoverCheck 12 (childHL (childLL thetaBelowCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL thetaBelowCell1101))
    e24KC2ThetaBelowLeaf1101020 e24KC2ThetaBelowLeaf1101021 e24KC2ThetaBelowNode1101022
      e24KC2ThetaBelowNode1101023

theorem e24KC2ThetaBelowNode110103 :
    adaptiveCoverCheck 12 (childHH (childLL thetaBelowCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL thetaBelowCell1101))
    e24KC2ThetaBelowLeaf1101030 e24KC2ThetaBelowLeaf1101031 e24KC2ThetaBelowLeaf1101032
      e24KC2ThetaBelowLeaf1101033

theorem e24KC2ThetaBelowNode110112 :
    adaptiveCoverCheck 12 (childHL (childLH thetaBelowCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH thetaBelowCell1101))
    e24KC2ThetaBelowLeaf1101120 e24KC2ThetaBelowLeaf1101121 e24KC2ThetaBelowLeaf1101122
      e24KC2ThetaBelowLeaf1101123

theorem e24KC2ThetaBelowNode110113 :
    adaptiveCoverCheck 12 (childHH (childLH thetaBelowCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH thetaBelowCell1101))
    e24KC2ThetaBelowLeaf1101130 e24KC2ThetaBelowLeaf1101131 e24KC2ThetaBelowLeaf1101132
      e24KC2ThetaBelowLeaf1101133

theorem e24KC2ThetaBelowNode110120 :
    adaptiveCoverCheck 12 (childLL (childHL thetaBelowCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL thetaBelowCell1101))
    e24KC2ThetaBelowNode1101200 e24KC2ThetaBelowNode1101201 e24KC2ThetaBelowNode1101202
      e24KC2ThetaBelowNode1101203

theorem e24KC2ThetaBelowNode110121 :
    adaptiveCoverCheck 12 (childLH (childHL thetaBelowCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL thetaBelowCell1101))
    e24KC2ThetaBelowNode1101210 e24KC2ThetaBelowNode1101211 e24KC2ThetaBelowNode1101212
      e24KC2ThetaBelowNode1101213

theorem e24KC2ThetaBelowNode110122 :
    adaptiveCoverCheck 12 (childHL (childHL thetaBelowCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL thetaBelowCell1101))
    e24KC2ThetaBelowNode1101220 e24KC2ThetaBelowNode1101221 e24KC2ThetaBelowLeaf1101222
      e24KC2ThetaBelowLeaf1101223

theorem e24KC2ThetaBelowNode110123 :
    adaptiveCoverCheck 12 (childHH (childHL thetaBelowCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL thetaBelowCell1101))
    e24KC2ThetaBelowNode1101230 e24KC2ThetaBelowNode1101231 e24KC2ThetaBelowLeaf1101232
      e24KC2ThetaBelowLeaf1101233

theorem e24KC2ThetaBelowNode110130 :
    adaptiveCoverCheck 12 (childLL (childHH thetaBelowCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH thetaBelowCell1101))
    e24KC2ThetaBelowNode1101300 e24KC2ThetaBelowNode1101301 e24KC2ThetaBelowNode1101302
      e24KC2ThetaBelowNode1101303

theorem e24KC2ThetaBelowNode110131 :
    adaptiveCoverCheck 12 (childLH (childHH thetaBelowCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH thetaBelowCell1101))
    e24KC2ThetaBelowNode1101310 e24KC2ThetaBelowNode1101311 e24KC2ThetaBelowNode1101312
      e24KC2ThetaBelowNode1101313

theorem e24KC2ThetaBelowNode110132 :
    adaptiveCoverCheck 12 (childHL (childHH thetaBelowCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH thetaBelowCell1101))
    e24KC2ThetaBelowNode1101320 e24KC2ThetaBelowNode1101321 e24KC2ThetaBelowLeaf1101322
      e24KC2ThetaBelowLeaf1101323

theorem e24KC2ThetaBelowNode110133 :
    adaptiveCoverCheck 12 (childHH (childHH thetaBelowCell1101)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH thetaBelowCell1101))
    e24KC2ThetaBelowNode1101330 e24KC2ThetaBelowNode1101331 e24KC2ThetaBelowLeaf1101332
      e24KC2ThetaBelowLeaf1101333

theorem e24KC2ThetaBelowNode111002 :
    adaptiveCoverCheck 12 (childHL (childLL thetaBelowCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL thetaBelowCell1110))
    e24KC2ThetaBelowLeaf1110020 e24KC2ThetaBelowLeaf1110021 e24KC2ThetaBelowLeaf1110022
      e24KC2ThetaBelowLeaf1110023

theorem e24KC2ThetaBelowNode111003 :
    adaptiveCoverCheck 12 (childHH (childLL thetaBelowCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL thetaBelowCell1110))
    e24KC2ThetaBelowLeaf1110030 e24KC2ThetaBelowLeaf1110031 e24KC2ThetaBelowLeaf1110032
      e24KC2ThetaBelowLeaf1110033

theorem e24KC2ThetaBelowNode111012 :
    adaptiveCoverCheck 12 (childHL (childLH thetaBelowCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH thetaBelowCell1110))
    e24KC2ThetaBelowLeaf1110120 e24KC2ThetaBelowLeaf1110121 e24KC2ThetaBelowLeaf1110122
      e24KC2ThetaBelowLeaf1110123

theorem e24KC2ThetaBelowNode111013 :
    adaptiveCoverCheck 12 (childHH (childLH thetaBelowCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLH thetaBelowCell1110))
    e24KC2ThetaBelowLeaf1110130 e24KC2ThetaBelowLeaf1110131 e24KC2ThetaBelowLeaf1110132
      e24KC2ThetaBelowLeaf1110133

theorem e24KC2ThetaBelowNode111020 :
    adaptiveCoverCheck 12 (childLL (childHL thetaBelowCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL thetaBelowCell1110))
    e24KC2ThetaBelowNode1110200 e24KC2ThetaBelowNode1110201 e24KC2ThetaBelowNode1110202
      e24KC2ThetaBelowNode1110203

theorem e24KC2ThetaBelowNode111021 :
    adaptiveCoverCheck 12 (childLH (childHL thetaBelowCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL thetaBelowCell1110))
    e24KC2ThetaBelowNode1110210 e24KC2ThetaBelowNode1110211 e24KC2ThetaBelowNode1110212
      e24KC2ThetaBelowNode1110213

theorem e24KC2ThetaBelowNode111022 :
    adaptiveCoverCheck 12 (childHL (childHL thetaBelowCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL thetaBelowCell1110))
    e24KC2ThetaBelowNode1110220 e24KC2ThetaBelowNode1110221 e24KC2ThetaBelowLeaf1110222
      e24KC2ThetaBelowLeaf1110223

theorem e24KC2ThetaBelowNode111023 :
    adaptiveCoverCheck 12 (childHH (childHL thetaBelowCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL thetaBelowCell1110))
    e24KC2ThetaBelowNode1110230 e24KC2ThetaBelowNode1110231 e24KC2ThetaBelowLeaf1110232
      e24KC2ThetaBelowLeaf1110233

theorem e24KC2ThetaBelowNode111030 :
    adaptiveCoverCheck 12 (childLL (childHH thetaBelowCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH thetaBelowCell1110))
    e24KC2ThetaBelowNode1110300 e24KC2ThetaBelowNode1110301 e24KC2ThetaBelowNode1110302
      e24KC2ThetaBelowNode1110303

theorem e24KC2ThetaBelowNode111031 :
    adaptiveCoverCheck 12 (childLH (childHH thetaBelowCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH thetaBelowCell1110))
    e24KC2ThetaBelowNode1110310 e24KC2ThetaBelowNode1110311 e24KC2ThetaBelowNode1110312
      e24KC2ThetaBelowNode1110313

theorem e24KC2ThetaBelowNode111032 :
    adaptiveCoverCheck 12 (childHL (childHH thetaBelowCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH thetaBelowCell1110))
    e24KC2ThetaBelowNode1110320 e24KC2ThetaBelowNode1110321 e24KC2ThetaBelowLeaf1110322
      e24KC2ThetaBelowLeaf1110323

theorem e24KC2ThetaBelowNode111033 :
    adaptiveCoverCheck 12 (childHH (childHH thetaBelowCell1110)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH thetaBelowCell1110))
    e24KC2ThetaBelowNode1110330 e24KC2ThetaBelowNode1110331 e24KC2ThetaBelowLeaf1110332
      e24KC2ThetaBelowLeaf1110333

theorem e24KC2ThetaBelowNode111102 :
    adaptiveCoverCheck 12 (childHL (childLL thetaBelowCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLL thetaBelowCell1111))
    e24KC2ThetaBelowLeaf1111020 e24KC2ThetaBelowLeaf1111021 e24KC2ThetaBelowLeaf1111022
      e24KC2ThetaBelowLeaf1111023

theorem e24KC2ThetaBelowNode111103 :
    adaptiveCoverCheck 12 (childHH (childLL thetaBelowCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childLL thetaBelowCell1111))
    e24KC2ThetaBelowLeaf1111030 e24KC2ThetaBelowLeaf1111031 e24KC2ThetaBelowLeaf1111032
      e24KC2ThetaBelowLeaf1111033

theorem e24KC2ThetaBelowNode111112 :
    adaptiveCoverCheck 12 (childHL (childLH thetaBelowCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childLH thetaBelowCell1111))
    e24KC2ThetaBelowLeaf1111120 e24KC2ThetaBelowLeaf1111121 e24KC2ThetaBelowLeaf1111122
      e24KC2ThetaBelowLeaf1111123

theorem e24KC2ThetaBelowNode111120 :
    adaptiveCoverCheck 12 (childLL (childHL thetaBelowCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHL thetaBelowCell1111))
    e24KC2ThetaBelowNode1111200 e24KC2ThetaBelowNode1111201 e24KC2ThetaBelowNode1111202
      e24KC2ThetaBelowNode1111203

theorem e24KC2ThetaBelowNode111121 :
    adaptiveCoverCheck 12 (childLH (childHL thetaBelowCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHL thetaBelowCell1111))
    e24KC2ThetaBelowNode1111210 e24KC2ThetaBelowNode1111211 e24KC2ThetaBelowNode1111212
      e24KC2ThetaBelowNode1111213

theorem e24KC2ThetaBelowNode111122 :
    adaptiveCoverCheck 12 (childHL (childHL thetaBelowCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHL thetaBelowCell1111))
    e24KC2ThetaBelowNode1111220 e24KC2ThetaBelowNode1111221 e24KC2ThetaBelowNode1111222
      e24KC2ThetaBelowNode1111223

theorem e24KC2ThetaBelowNode111123 :
    adaptiveCoverCheck 12 (childHH (childHL thetaBelowCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHL thetaBelowCell1111))
    e24KC2ThetaBelowNode1111230 e24KC2ThetaBelowNode1111231 e24KC2ThetaBelowNode1111232
      e24KC2ThetaBelowNode1111233

theorem e24KC2ThetaBelowNode111130 :
    adaptiveCoverCheck 12 (childLL (childHH thetaBelowCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childHH thetaBelowCell1111))
    e24KC2ThetaBelowLeaf1111300 e24KC2ThetaBelowLeaf1111301 e24KC2ThetaBelowNode1111302
      e24KC2ThetaBelowNode1111303

theorem e24KC2ThetaBelowNode111131 :
    adaptiveCoverCheck 12 (childLH (childHH thetaBelowCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childHH thetaBelowCell1111))
    e24KC2ThetaBelowLeaf1111310 e24KC2ThetaBelowLeaf1111311 e24KC2ThetaBelowNode1111312
      e24KC2ThetaBelowNode1111313

theorem e24KC2ThetaBelowNode111132 :
    adaptiveCoverCheck 12 (childHL (childHH thetaBelowCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHL (childHH thetaBelowCell1111))
    e24KC2ThetaBelowNode1111320 e24KC2ThetaBelowNode1111321 e24KC2ThetaBelowNode1111322
      e24KC2ThetaBelowNode1111323

theorem e24KC2ThetaBelowNode111133 :
    adaptiveCoverCheck 12 (childHH (childHH thetaBelowCell1111)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childHH (childHH thetaBelowCell1111))
    e24KC2ThetaBelowNode1111330 e24KC2ThetaBelowNode1111331 e24KC2ThetaBelowNode1111332
      e24KC2ThetaBelowNode1111333

theorem e24KC2ThetaBelowNode111210 :
    adaptiveCoverCheck 12 (childLL (childLH thetaBelowCell1112)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childLH thetaBelowCell1112))
    e24KC2ThetaBelowLeaf1112100 e24KC2ThetaBelowLeaf1112101 e24KC2ThetaBelowLeaf1112102
      e24KC2ThetaBelowLeaf1112103

theorem e24KC2ThetaBelowNode111211 :
    adaptiveCoverCheck 12 (childLH (childLH thetaBelowCell1112)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childLH thetaBelowCell1112))
    e24KC2ThetaBelowLeaf1112110 e24KC2ThetaBelowLeaf1112111 e24KC2ThetaBelowLeaf1112112
      e24KC2ThetaBelowLeaf1112113

theorem e24KC2ThetaBelowNode111300 :
    adaptiveCoverCheck 12 (childLL (childLL thetaBelowCell1113)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childLL thetaBelowCell1113))
    e24KC2ThetaBelowLeaf1113000 e24KC2ThetaBelowLeaf1113001 e24KC2ThetaBelowLeaf1113002
      e24KC2ThetaBelowLeaf1113003

theorem e24KC2ThetaBelowNode111301 :
    adaptiveCoverCheck 12 (childLH (childLL thetaBelowCell1113)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childLL thetaBelowCell1113))
    e24KC2ThetaBelowLeaf1113010 e24KC2ThetaBelowLeaf1113011 e24KC2ThetaBelowLeaf1113012
      e24KC2ThetaBelowLeaf1113013

theorem e24KC2ThetaBelowNode111310 :
    adaptiveCoverCheck 12 (childLL (childLH thetaBelowCell1113)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLL (childLH thetaBelowCell1113))
    e24KC2ThetaBelowLeaf1113100 e24KC2ThetaBelowLeaf1113101 e24KC2ThetaBelowLeaf1113102
      e24KC2ThetaBelowLeaf1113103

theorem e24KC2ThetaBelowNode111311 :
    adaptiveCoverCheck 12 (childLH (childLH thetaBelowCell1113)) = true :=
  adaptiveCoverCheck_succ_of_children 11 (childLH (childLH thetaBelowCell1113))
    e24KC2ThetaBelowLeaf1113110 e24KC2ThetaBelowLeaf1113111 e24KC2ThetaBelowLeaf1113112
      e24KC2ThetaBelowLeaf1113113

theorem e24KC2ThetaBelowNode01013 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell0101) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH thetaBelowCell0101)
    e24KC2ThetaBelowLeaf010130 e24KC2ThetaBelowLeaf010131 e24KC2ThetaBelowLeaf010132
      e24KC2ThetaBelowLeaf010133

theorem e24KC2ThetaBelowNode01101 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell0110) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell0110)
    e24KC2ThetaBelowLeaf011010 e24KC2ThetaBelowLeaf011011 e24KC2ThetaBelowLeaf011012
      e24KC2ThetaBelowLeaf011013

theorem e24KC2ThetaBelowNode01102 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell0110) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL thetaBelowCell0110)
    e24KC2ThetaBelowLeaf011020 e24KC2ThetaBelowLeaf011021 e24KC2ThetaBelowLeaf011022
      e24KC2ThetaBelowLeaf011023

theorem e24KC2ThetaBelowNode01103 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell0110) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH thetaBelowCell0110)
    e24KC2ThetaBelowLeaf011030 e24KC2ThetaBelowLeaf011031 e24KC2ThetaBelowLeaf011032
      e24KC2ThetaBelowLeaf011033

theorem e24KC2ThetaBelowNode01110 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell0111) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL thetaBelowCell0111)
    e24KC2ThetaBelowLeaf011100 e24KC2ThetaBelowLeaf011101 e24KC2ThetaBelowLeaf011102
      e24KC2ThetaBelowLeaf011103

theorem e24KC2ThetaBelowNode01111 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell0111) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell0111)
    e24KC2ThetaBelowLeaf011110 e24KC2ThetaBelowLeaf011111 e24KC2ThetaBelowLeaf011112
      e24KC2ThetaBelowLeaf011113

theorem e24KC2ThetaBelowNode01112 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell0111) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL thetaBelowCell0111)
    e24KC2ThetaBelowLeaf011120 e24KC2ThetaBelowLeaf011121 e24KC2ThetaBelowLeaf011122
      e24KC2ThetaBelowLeaf011123

theorem e24KC2ThetaBelowNode01113 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell0111) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH thetaBelowCell0111)
    e24KC2ThetaBelowLeaf011130 e24KC2ThetaBelowLeaf011131 e24KC2ThetaBelowLeaf011132
      e24KC2ThetaBelowLeaf011133

theorem e24KC2ThetaBelowNode10000 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1000) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL thetaBelowCell1000)
    e24KC2ThetaBelowLeaf100000 e24KC2ThetaBelowLeaf100001 e24KC2ThetaBelowLeaf100002
      e24KC2ThetaBelowLeaf100003

theorem e24KC2ThetaBelowNode10001 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1000) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell1000)
    e24KC2ThetaBelowLeaf100010 e24KC2ThetaBelowLeaf100011 e24KC2ThetaBelowLeaf100012
      e24KC2ThetaBelowLeaf100013

theorem e24KC2ThetaBelowNode10002 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1000) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL thetaBelowCell1000)
    e24KC2ThetaBelowLeaf100020 e24KC2ThetaBelowLeaf100021 e24KC2ThetaBelowLeaf100022
      e24KC2ThetaBelowLeaf100023

theorem e24KC2ThetaBelowNode10003 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1000) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH thetaBelowCell1000)
    e24KC2ThetaBelowLeaf100030 e24KC2ThetaBelowLeaf100031 e24KC2ThetaBelowLeaf100032
      e24KC2ThetaBelowLeaf100033

theorem e24KC2ThetaBelowNode10010 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1001) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL thetaBelowCell1001)
    e24KC2ThetaBelowLeaf100100 e24KC2ThetaBelowLeaf100101 e24KC2ThetaBelowLeaf100102
      e24KC2ThetaBelowLeaf100103

theorem e24KC2ThetaBelowNode10011 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1001) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell1001)
    e24KC2ThetaBelowLeaf100110 e24KC2ThetaBelowLeaf100111 e24KC2ThetaBelowLeaf100112
      e24KC2ThetaBelowNode100113

theorem e24KC2ThetaBelowNode10012 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1001) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL thetaBelowCell1001)
    e24KC2ThetaBelowLeaf100120 e24KC2ThetaBelowNode100121 e24KC2ThetaBelowLeaf100122
      e24KC2ThetaBelowLeaf100123

theorem e24KC2ThetaBelowNode10013 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1001) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH thetaBelowCell1001)
    e24KC2ThetaBelowNode100130 e24KC2ThetaBelowNode100131 e24KC2ThetaBelowLeaf100132
      e24KC2ThetaBelowLeaf100133

theorem e24KC2ThetaBelowNode10031 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1003) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell1003)
    e24KC2ThetaBelowLeaf100310 e24KC2ThetaBelowLeaf100311 e24KC2ThetaBelowLeaf100312
      e24KC2ThetaBelowLeaf100313

theorem e24KC2ThetaBelowNode10100 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1010) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL thetaBelowCell1010)
    e24KC2ThetaBelowLeaf101000 e24KC2ThetaBelowNode101001 e24KC2ThetaBelowNode101002
      e24KC2ThetaBelowNode101003

theorem e24KC2ThetaBelowNode10101 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1010) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell1010)
    e24KC2ThetaBelowNode101010 e24KC2ThetaBelowNode101011 e24KC2ThetaBelowNode101012
      e24KC2ThetaBelowNode101013

theorem e24KC2ThetaBelowNode10102 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1010) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL thetaBelowCell1010)
    e24KC2ThetaBelowNode101020 e24KC2ThetaBelowNode101021 e24KC2ThetaBelowLeaf101022
      e24KC2ThetaBelowLeaf101023

theorem e24KC2ThetaBelowNode10103 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1010) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH thetaBelowCell1010)
    e24KC2ThetaBelowNode101030 e24KC2ThetaBelowNode101031 e24KC2ThetaBelowNode101032
      e24KC2ThetaBelowNode101033

theorem e24KC2ThetaBelowNode10110 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1011) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL thetaBelowCell1011)
    e24KC2ThetaBelowNode101100 e24KC2ThetaBelowLeaf101101 e24KC2ThetaBelowNode101102
      e24KC2ThetaBelowNode101103

theorem e24KC2ThetaBelowNode10111 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1011) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell1011)
    e24KC2ThetaBelowLeaf101110 e24KC2ThetaBelowLeaf101111 e24KC2ThetaBelowNode101112
      e24KC2ThetaBelowNode101113

theorem e24KC2ThetaBelowNode10112 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1011) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL thetaBelowCell1011)
    e24KC2ThetaBelowNode101120 e24KC2ThetaBelowNode101121 e24KC2ThetaBelowNode101122
      e24KC2ThetaBelowNode101123

theorem e24KC2ThetaBelowNode10113 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1011) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH thetaBelowCell1011)
    e24KC2ThetaBelowNode101130 e24KC2ThetaBelowNode101131 e24KC2ThetaBelowNode101132
      e24KC2ThetaBelowNode101133

theorem e24KC2ThetaBelowNode10120 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1012) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL thetaBelowCell1012)
    e24KC2ThetaBelowLeaf101200 e24KC2ThetaBelowLeaf101201 e24KC2ThetaBelowLeaf101202
      e24KC2ThetaBelowLeaf101203

theorem e24KC2ThetaBelowNode10121 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1012) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell1012)
    e24KC2ThetaBelowLeaf101210 e24KC2ThetaBelowLeaf101211 e24KC2ThetaBelowLeaf101212
      e24KC2ThetaBelowLeaf101213

theorem e24KC2ThetaBelowNode10130 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1013) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL thetaBelowCell1013)
    e24KC2ThetaBelowLeaf101300 e24KC2ThetaBelowLeaf101301 e24KC2ThetaBelowLeaf101302
      e24KC2ThetaBelowLeaf101303

theorem e24KC2ThetaBelowNode10131 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1013) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell1013)
    e24KC2ThetaBelowLeaf101310 e24KC2ThetaBelowLeaf101311 e24KC2ThetaBelowLeaf101312
      e24KC2ThetaBelowLeaf101313

theorem e24KC2ThetaBelowNode11000 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1100) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL thetaBelowCell1100)
    e24KC2ThetaBelowLeaf110000 e24KC2ThetaBelowLeaf110001 e24KC2ThetaBelowNode110002
      e24KC2ThetaBelowNode110003

theorem e24KC2ThetaBelowNode11001 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1100) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell1100)
    e24KC2ThetaBelowLeaf110010 e24KC2ThetaBelowLeaf110011 e24KC2ThetaBelowNode110012
      e24KC2ThetaBelowNode110013

theorem e24KC2ThetaBelowNode11002 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1100) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL thetaBelowCell1100)
    e24KC2ThetaBelowNode110020 e24KC2ThetaBelowNode110021 e24KC2ThetaBelowNode110022
      e24KC2ThetaBelowNode110023

theorem e24KC2ThetaBelowNode11003 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1100) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH thetaBelowCell1100)
    e24KC2ThetaBelowNode110030 e24KC2ThetaBelowNode110031 e24KC2ThetaBelowNode110032
      e24KC2ThetaBelowNode110033

theorem e24KC2ThetaBelowNode11010 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1101) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL thetaBelowCell1101)
    e24KC2ThetaBelowLeaf110100 e24KC2ThetaBelowLeaf110101 e24KC2ThetaBelowNode110102
      e24KC2ThetaBelowNode110103

theorem e24KC2ThetaBelowNode11011 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1101) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell1101)
    e24KC2ThetaBelowLeaf110110 e24KC2ThetaBelowLeaf110111 e24KC2ThetaBelowNode110112
      e24KC2ThetaBelowNode110113

theorem e24KC2ThetaBelowNode11012 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1101) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL thetaBelowCell1101)
    e24KC2ThetaBelowNode110120 e24KC2ThetaBelowNode110121 e24KC2ThetaBelowNode110122
      e24KC2ThetaBelowNode110123

theorem e24KC2ThetaBelowNode11013 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1101) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH thetaBelowCell1101)
    e24KC2ThetaBelowNode110130 e24KC2ThetaBelowNode110131 e24KC2ThetaBelowNode110132
      e24KC2ThetaBelowNode110133

theorem e24KC2ThetaBelowNode11020 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1102) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL thetaBelowCell1102)
    e24KC2ThetaBelowLeaf110200 e24KC2ThetaBelowLeaf110201 e24KC2ThetaBelowLeaf110202
      e24KC2ThetaBelowLeaf110203

theorem e24KC2ThetaBelowNode11021 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1102) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell1102)
    e24KC2ThetaBelowLeaf110210 e24KC2ThetaBelowLeaf110211 e24KC2ThetaBelowLeaf110212
      e24KC2ThetaBelowLeaf110213

theorem e24KC2ThetaBelowNode11030 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1103) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL thetaBelowCell1103)
    e24KC2ThetaBelowLeaf110300 e24KC2ThetaBelowLeaf110301 e24KC2ThetaBelowLeaf110302
      e24KC2ThetaBelowLeaf110303

theorem e24KC2ThetaBelowNode11031 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1103) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell1103)
    e24KC2ThetaBelowLeaf110310 e24KC2ThetaBelowLeaf110311 e24KC2ThetaBelowLeaf110312
      e24KC2ThetaBelowLeaf110313

theorem e24KC2ThetaBelowNode11100 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1110) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL thetaBelowCell1110)
    e24KC2ThetaBelowLeaf111000 e24KC2ThetaBelowLeaf111001 e24KC2ThetaBelowNode111002
      e24KC2ThetaBelowNode111003

theorem e24KC2ThetaBelowNode11101 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1110) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell1110)
    e24KC2ThetaBelowLeaf111010 e24KC2ThetaBelowLeaf111011 e24KC2ThetaBelowNode111012
      e24KC2ThetaBelowNode111013

theorem e24KC2ThetaBelowNode11102 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1110) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL thetaBelowCell1110)
    e24KC2ThetaBelowNode111020 e24KC2ThetaBelowNode111021 e24KC2ThetaBelowNode111022
      e24KC2ThetaBelowNode111023

theorem e24KC2ThetaBelowNode11103 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1110) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH thetaBelowCell1110)
    e24KC2ThetaBelowNode111030 e24KC2ThetaBelowNode111031 e24KC2ThetaBelowNode111032
      e24KC2ThetaBelowNode111033

theorem e24KC2ThetaBelowNode11110 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1111) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL thetaBelowCell1111)
    e24KC2ThetaBelowLeaf111100 e24KC2ThetaBelowLeaf111101 e24KC2ThetaBelowNode111102
      e24KC2ThetaBelowNode111103

theorem e24KC2ThetaBelowNode11111 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1111) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell1111)
    e24KC2ThetaBelowLeaf111110 e24KC2ThetaBelowLeaf111111 e24KC2ThetaBelowNode111112
      e24KC2ThetaBelowLeaf111113

theorem e24KC2ThetaBelowNode11112 :
    adaptiveCoverCheck 13 (childHL thetaBelowCell1111) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHL thetaBelowCell1111)
    e24KC2ThetaBelowNode111120 e24KC2ThetaBelowNode111121 e24KC2ThetaBelowNode111122
      e24KC2ThetaBelowNode111123

theorem e24KC2ThetaBelowNode11113 :
    adaptiveCoverCheck 13 (childHH thetaBelowCell1111) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childHH thetaBelowCell1111)
    e24KC2ThetaBelowNode111130 e24KC2ThetaBelowNode111131 e24KC2ThetaBelowNode111132
      e24KC2ThetaBelowNode111133

theorem e24KC2ThetaBelowNode11120 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1112) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL thetaBelowCell1112)
    e24KC2ThetaBelowLeaf111200 e24KC2ThetaBelowLeaf111201 e24KC2ThetaBelowLeaf111202
      e24KC2ThetaBelowLeaf111203

theorem e24KC2ThetaBelowNode11121 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1112) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell1112)
    e24KC2ThetaBelowNode111210 e24KC2ThetaBelowNode111211 e24KC2ThetaBelowLeaf111212
      e24KC2ThetaBelowLeaf111213

theorem e24KC2ThetaBelowNode11130 :
    adaptiveCoverCheck 13 (childLL thetaBelowCell1113) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLL thetaBelowCell1113)
    e24KC2ThetaBelowNode111300 e24KC2ThetaBelowNode111301 e24KC2ThetaBelowLeaf111302
      e24KC2ThetaBelowLeaf111303

theorem e24KC2ThetaBelowNode11131 :
    adaptiveCoverCheck 13 (childLH thetaBelowCell1113) = true :=
  adaptiveCoverCheck_succ_of_children 12 (childLH thetaBelowCell1113)
    e24KC2ThetaBelowNode111310 e24KC2ThetaBelowNode111311 e24KC2ThetaBelowLeaf111312
      e24KC2ThetaBelowLeaf111313

theorem e24KC2ThetaBelowNode0003 :
    adaptiveCoverCheck 14 thetaBelowCell0003 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell0003
    e24KC2ThetaBelowLeaf00030 e24KC2ThetaBelowLeaf00031 e24KC2ThetaBelowLeaf00032
      e24KC2ThetaBelowLeaf00033

theorem e24KC2ThetaBelowNode0010 :
    adaptiveCoverCheck 14 thetaBelowCell0010 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell0010
    e24KC2ThetaBelowLeaf00100 e24KC2ThetaBelowLeaf00101 e24KC2ThetaBelowLeaf00102
      e24KC2ThetaBelowLeaf00103

theorem e24KC2ThetaBelowNode0011 :
    adaptiveCoverCheck 14 thetaBelowCell0011 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell0011
    e24KC2ThetaBelowLeaf00110 e24KC2ThetaBelowLeaf00111 e24KC2ThetaBelowLeaf00112
      e24KC2ThetaBelowLeaf00113

theorem e24KC2ThetaBelowNode0012 :
    adaptiveCoverCheck 14 thetaBelowCell0012 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell0012
    e24KC2ThetaBelowLeaf00120 e24KC2ThetaBelowLeaf00121 e24KC2ThetaBelowLeaf00122
      e24KC2ThetaBelowLeaf00123

theorem e24KC2ThetaBelowNode0013 :
    adaptiveCoverCheck 14 thetaBelowCell0013 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell0013
    e24KC2ThetaBelowLeaf00130 e24KC2ThetaBelowLeaf00131 e24KC2ThetaBelowLeaf00132
      e24KC2ThetaBelowLeaf00133

theorem e24KC2ThetaBelowNode0100 :
    adaptiveCoverCheck 14 thetaBelowCell0100 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell0100
    e24KC2ThetaBelowLeaf01000 e24KC2ThetaBelowLeaf01001 e24KC2ThetaBelowLeaf01002
      e24KC2ThetaBelowLeaf01003

theorem e24KC2ThetaBelowNode0101 :
    adaptiveCoverCheck 14 thetaBelowCell0101 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell0101
    e24KC2ThetaBelowLeaf01010 e24KC2ThetaBelowLeaf01011 e24KC2ThetaBelowLeaf01012
      e24KC2ThetaBelowNode01013

theorem e24KC2ThetaBelowNode0102 :
    adaptiveCoverCheck 14 thetaBelowCell0102 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell0102
    e24KC2ThetaBelowLeaf01020 e24KC2ThetaBelowLeaf01021 e24KC2ThetaBelowLeaf01022
      e24KC2ThetaBelowLeaf01023

theorem e24KC2ThetaBelowNode0103 :
    adaptiveCoverCheck 14 thetaBelowCell0103 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell0103
    e24KC2ThetaBelowLeaf01030 e24KC2ThetaBelowLeaf01031 e24KC2ThetaBelowLeaf01032
      e24KC2ThetaBelowLeaf01033

theorem e24KC2ThetaBelowNode0110 :
    adaptiveCoverCheck 14 thetaBelowCell0110 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell0110
    e24KC2ThetaBelowLeaf01100 e24KC2ThetaBelowNode01101 e24KC2ThetaBelowNode01102
      e24KC2ThetaBelowNode01103

theorem e24KC2ThetaBelowNode0111 :
    adaptiveCoverCheck 14 thetaBelowCell0111 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell0111
    e24KC2ThetaBelowNode01110 e24KC2ThetaBelowNode01111 e24KC2ThetaBelowNode01112
      e24KC2ThetaBelowNode01113

theorem e24KC2ThetaBelowNode0112 :
    adaptiveCoverCheck 14 thetaBelowCell0112 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell0112
    e24KC2ThetaBelowLeaf01120 e24KC2ThetaBelowLeaf01121 e24KC2ThetaBelowLeaf01122
      e24KC2ThetaBelowLeaf01123

theorem e24KC2ThetaBelowNode0113 :
    adaptiveCoverCheck 14 thetaBelowCell0113 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell0113
    e24KC2ThetaBelowLeaf01130 e24KC2ThetaBelowLeaf01131 e24KC2ThetaBelowLeaf01132
      e24KC2ThetaBelowLeaf01133

theorem e24KC2ThetaBelowNode1000 :
    adaptiveCoverCheck 14 thetaBelowCell1000 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1000
    e24KC2ThetaBelowNode10000 e24KC2ThetaBelowNode10001 e24KC2ThetaBelowNode10002
      e24KC2ThetaBelowNode10003

theorem e24KC2ThetaBelowNode1001 :
    adaptiveCoverCheck 14 thetaBelowCell1001 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1001
    e24KC2ThetaBelowNode10010 e24KC2ThetaBelowNode10011 e24KC2ThetaBelowNode10012
      e24KC2ThetaBelowNode10013

theorem e24KC2ThetaBelowNode1002 :
    adaptiveCoverCheck 14 thetaBelowCell1002 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1002
    e24KC2ThetaBelowLeaf10020 e24KC2ThetaBelowLeaf10021 e24KC2ThetaBelowLeaf10022
      e24KC2ThetaBelowLeaf10023

theorem e24KC2ThetaBelowNode1003 :
    adaptiveCoverCheck 14 thetaBelowCell1003 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1003
    e24KC2ThetaBelowLeaf10030 e24KC2ThetaBelowNode10031 e24KC2ThetaBelowLeaf10032
      e24KC2ThetaBelowLeaf10033

theorem e24KC2ThetaBelowNode1010 :
    adaptiveCoverCheck 14 thetaBelowCell1010 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1010
    e24KC2ThetaBelowNode10100 e24KC2ThetaBelowNode10101 e24KC2ThetaBelowNode10102
      e24KC2ThetaBelowNode10103

theorem e24KC2ThetaBelowNode1011 :
    adaptiveCoverCheck 14 thetaBelowCell1011 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1011
    e24KC2ThetaBelowNode10110 e24KC2ThetaBelowNode10111 e24KC2ThetaBelowNode10112
      e24KC2ThetaBelowNode10113

theorem e24KC2ThetaBelowNode1012 :
    adaptiveCoverCheck 14 thetaBelowCell1012 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1012
    e24KC2ThetaBelowNode10120 e24KC2ThetaBelowNode10121 e24KC2ThetaBelowLeaf10122
      e24KC2ThetaBelowLeaf10123

theorem e24KC2ThetaBelowNode1013 :
    adaptiveCoverCheck 14 thetaBelowCell1013 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1013
    e24KC2ThetaBelowNode10130 e24KC2ThetaBelowNode10131 e24KC2ThetaBelowLeaf10132
      e24KC2ThetaBelowLeaf10133

theorem e24KC2ThetaBelowNode1100 :
    adaptiveCoverCheck 14 thetaBelowCell1100 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1100
    e24KC2ThetaBelowNode11000 e24KC2ThetaBelowNode11001 e24KC2ThetaBelowNode11002
      e24KC2ThetaBelowNode11003

theorem e24KC2ThetaBelowNode1101 :
    adaptiveCoverCheck 14 thetaBelowCell1101 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1101
    e24KC2ThetaBelowNode11010 e24KC2ThetaBelowNode11011 e24KC2ThetaBelowNode11012
      e24KC2ThetaBelowNode11013

theorem e24KC2ThetaBelowNode1102 :
    adaptiveCoverCheck 14 thetaBelowCell1102 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1102
    e24KC2ThetaBelowNode11020 e24KC2ThetaBelowNode11021 e24KC2ThetaBelowLeaf11022
      e24KC2ThetaBelowLeaf11023

theorem e24KC2ThetaBelowNode1103 :
    adaptiveCoverCheck 14 thetaBelowCell1103 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1103
    e24KC2ThetaBelowNode11030 e24KC2ThetaBelowNode11031 e24KC2ThetaBelowLeaf11032
      e24KC2ThetaBelowLeaf11033

theorem e24KC2ThetaBelowNode1110 :
    adaptiveCoverCheck 14 thetaBelowCell1110 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1110
    e24KC2ThetaBelowNode11100 e24KC2ThetaBelowNode11101 e24KC2ThetaBelowNode11102
      e24KC2ThetaBelowNode11103

theorem e24KC2ThetaBelowNode1111 :
    adaptiveCoverCheck 14 thetaBelowCell1111 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1111
    e24KC2ThetaBelowNode11110 e24KC2ThetaBelowNode11111 e24KC2ThetaBelowNode11112
      e24KC2ThetaBelowNode11113

theorem e24KC2ThetaBelowNode1112 :
    adaptiveCoverCheck 14 thetaBelowCell1112 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1112
    e24KC2ThetaBelowNode11120 e24KC2ThetaBelowNode11121 e24KC2ThetaBelowLeaf11122
      e24KC2ThetaBelowLeaf11123

theorem e24KC2ThetaBelowNode1113 :
    adaptiveCoverCheck 14 thetaBelowCell1113 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1113
    e24KC2ThetaBelowNode11130 e24KC2ThetaBelowNode11131 e24KC2ThetaBelowLeaf11132
      e24KC2ThetaBelowLeaf11133

theorem e24KC2ThetaBelowNode1121 :
    adaptiveCoverCheck 14 thetaBelowCell1121 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1121
    e24KC2ThetaBelowLeaf11210 e24KC2ThetaBelowLeaf11211 e24KC2ThetaBelowLeaf11212
      e24KC2ThetaBelowLeaf11213

theorem e24KC2ThetaBelowNode1130 :
    adaptiveCoverCheck 14 thetaBelowCell1130 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1130
    e24KC2ThetaBelowLeaf11300 e24KC2ThetaBelowLeaf11301 e24KC2ThetaBelowLeaf11302
      e24KC2ThetaBelowLeaf11303

theorem e24KC2ThetaBelowNode1131 :
    adaptiveCoverCheck 14 thetaBelowCell1131 = true :=
  adaptiveCoverCheck_succ_of_children 13 thetaBelowCell1131
    e24KC2ThetaBelowLeaf11310 e24KC2ThetaBelowLeaf11311 e24KC2ThetaBelowLeaf11312
      e24KC2ThetaBelowLeaf11313

theorem e24KC2ThetaBelowNode000 :
    adaptiveCoverCheck 15 (childLL (childLL (childLL e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childLL (childLL (childLL e24ThetaBelowRoot)))
    e24KC2ThetaBelowLeaf0000 e24KC2ThetaBelowLeaf0001 e24KC2ThetaBelowLeaf0002
      e24KC2ThetaBelowNode0003

theorem e24KC2ThetaBelowNode001 :
    adaptiveCoverCheck 15 (childLH (childLL (childLL e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childLH (childLL (childLL e24ThetaBelowRoot)))
    e24KC2ThetaBelowNode0010 e24KC2ThetaBelowNode0011 e24KC2ThetaBelowNode0012
      e24KC2ThetaBelowNode0013

theorem e24KC2ThetaBelowNode003 :
    adaptiveCoverCheck 15 (childHH (childLL (childLL e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childHH (childLL (childLL e24ThetaBelowRoot)))
    e24KC2ThetaBelowLeaf0030 e24KC2ThetaBelowLeaf0031 e24KC2ThetaBelowLeaf0032
      e24KC2ThetaBelowLeaf0033

theorem e24KC2ThetaBelowNode010 :
    adaptiveCoverCheck 15 (childLL (childLH (childLL e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childLL (childLH (childLL e24ThetaBelowRoot)))
    e24KC2ThetaBelowNode0100 e24KC2ThetaBelowNode0101 e24KC2ThetaBelowNode0102
      e24KC2ThetaBelowNode0103

theorem e24KC2ThetaBelowNode011 :
    adaptiveCoverCheck 15 (childLH (childLH (childLL e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childLH (childLH (childLL e24ThetaBelowRoot)))
    e24KC2ThetaBelowNode0110 e24KC2ThetaBelowNode0111 e24KC2ThetaBelowNode0112
      e24KC2ThetaBelowNode0113

theorem e24KC2ThetaBelowNode012 :
    adaptiveCoverCheck 15 (childHL (childLH (childLL e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childHL (childLH (childLL e24ThetaBelowRoot)))
    e24KC2ThetaBelowLeaf0120 e24KC2ThetaBelowLeaf0121 e24KC2ThetaBelowLeaf0122
      e24KC2ThetaBelowLeaf0123

theorem e24KC2ThetaBelowNode013 :
    adaptiveCoverCheck 15 (childHH (childLH (childLL e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childHH (childLH (childLL e24ThetaBelowRoot)))
    e24KC2ThetaBelowLeaf0130 e24KC2ThetaBelowLeaf0131 e24KC2ThetaBelowLeaf0132
      e24KC2ThetaBelowLeaf0133

theorem e24KC2ThetaBelowNode100 :
    adaptiveCoverCheck 15 (childLL (childLL (childLH e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childLL (childLL (childLH e24ThetaBelowRoot)))
    e24KC2ThetaBelowNode1000 e24KC2ThetaBelowNode1001 e24KC2ThetaBelowNode1002
      e24KC2ThetaBelowNode1003

theorem e24KC2ThetaBelowNode101 :
    adaptiveCoverCheck 15 (childLH (childLL (childLH e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childLH (childLL (childLH e24ThetaBelowRoot)))
    e24KC2ThetaBelowNode1010 e24KC2ThetaBelowNode1011 e24KC2ThetaBelowNode1012
      e24KC2ThetaBelowNode1013

theorem e24KC2ThetaBelowNode102 :
    adaptiveCoverCheck 15 (childHL (childLL (childLH e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childHL (childLL (childLH e24ThetaBelowRoot)))
    e24KC2ThetaBelowLeaf1020 e24KC2ThetaBelowLeaf1021 e24KC2ThetaBelowLeaf1022
      e24KC2ThetaBelowLeaf1023

theorem e24KC2ThetaBelowNode103 :
    adaptiveCoverCheck 15 (childHH (childLL (childLH e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childHH (childLL (childLH e24ThetaBelowRoot)))
    e24KC2ThetaBelowLeaf1030 e24KC2ThetaBelowLeaf1031 e24KC2ThetaBelowLeaf1032
      e24KC2ThetaBelowLeaf1033

theorem e24KC2ThetaBelowNode110 :
    adaptiveCoverCheck 15 (childLL (childLH (childLH e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childLL (childLH (childLH e24ThetaBelowRoot)))
    e24KC2ThetaBelowNode1100 e24KC2ThetaBelowNode1101 e24KC2ThetaBelowNode1102
      e24KC2ThetaBelowNode1103

theorem e24KC2ThetaBelowNode111 :
    adaptiveCoverCheck 15 (childLH (childLH (childLH e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childLH (childLH (childLH e24ThetaBelowRoot)))
    e24KC2ThetaBelowNode1110 e24KC2ThetaBelowNode1111 e24KC2ThetaBelowNode1112
      e24KC2ThetaBelowNode1113

theorem e24KC2ThetaBelowNode112 :
    adaptiveCoverCheck 15 (childHL (childLH (childLH e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childHL (childLH (childLH e24ThetaBelowRoot)))
    e24KC2ThetaBelowLeaf1120 e24KC2ThetaBelowNode1121 e24KC2ThetaBelowLeaf1122
      e24KC2ThetaBelowLeaf1123

theorem e24KC2ThetaBelowNode113 :
    adaptiveCoverCheck 15 (childHH (childLH (childLH e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childHH (childLH (childLH e24ThetaBelowRoot)))
    e24KC2ThetaBelowNode1130 e24KC2ThetaBelowNode1131 e24KC2ThetaBelowLeaf1132
      e24KC2ThetaBelowLeaf1133

theorem e24KC2ThetaBelowNode130 :
    adaptiveCoverCheck 15 (childLL (childHH (childLH e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childLL (childHH (childLH e24ThetaBelowRoot)))
    e24KC2ThetaBelowLeaf1300 e24KC2ThetaBelowLeaf1301 e24KC2ThetaBelowLeaf1302
      e24KC2ThetaBelowLeaf1303

theorem e24KC2ThetaBelowNode131 :
    adaptiveCoverCheck 15 (childLH (childHH (childLH e24ThetaBelowRoot))) = true :=
  adaptiveCoverCheck_succ_of_children 14 (childLH (childHH (childLH e24ThetaBelowRoot)))
    e24KC2ThetaBelowLeaf1310 e24KC2ThetaBelowLeaf1311 e24KC2ThetaBelowLeaf1312
      e24KC2ThetaBelowLeaf1313

theorem e24KC2ThetaBelowNode00 :
    adaptiveCoverCheck 16 (childLL (childLL e24ThetaBelowRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childLL (childLL e24ThetaBelowRoot))
    e24KC2ThetaBelowNode000 e24KC2ThetaBelowNode001 e24KC2ThetaBelowLeaf002 e24KC2ThetaBelowNode003

theorem e24KC2ThetaBelowNode01 :
    adaptiveCoverCheck 16 (childLH (childLL e24ThetaBelowRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childLH (childLL e24ThetaBelowRoot))
    e24KC2ThetaBelowNode010 e24KC2ThetaBelowNode011 e24KC2ThetaBelowNode012 e24KC2ThetaBelowNode013

theorem e24KC2ThetaBelowNode03 :
    adaptiveCoverCheck 16 (childHH (childLL e24ThetaBelowRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childHH (childLL e24ThetaBelowRoot))
    e24KC2ThetaBelowLeaf030 e24KC2ThetaBelowLeaf031 e24KC2ThetaBelowLeaf032 e24KC2ThetaBelowLeaf033

theorem e24KC2ThetaBelowNode10 :
    adaptiveCoverCheck 16 (childLL (childLH e24ThetaBelowRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childLL (childLH e24ThetaBelowRoot))
    e24KC2ThetaBelowNode100 e24KC2ThetaBelowNode101 e24KC2ThetaBelowNode102 e24KC2ThetaBelowNode103

theorem e24KC2ThetaBelowNode11 :
    adaptiveCoverCheck 16 (childLH (childLH e24ThetaBelowRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childLH (childLH e24ThetaBelowRoot))
    e24KC2ThetaBelowNode110 e24KC2ThetaBelowNode111 e24KC2ThetaBelowNode112 e24KC2ThetaBelowNode113

theorem e24KC2ThetaBelowNode12 :
    adaptiveCoverCheck 16 (childHL (childLH e24ThetaBelowRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childHL (childLH e24ThetaBelowRoot))
    e24KC2ThetaBelowLeaf120 e24KC2ThetaBelowLeaf121 e24KC2ThetaBelowLeaf122 e24KC2ThetaBelowLeaf123

theorem e24KC2ThetaBelowNode13 :
    adaptiveCoverCheck 16 (childHH (childLH e24ThetaBelowRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childHH (childLH e24ThetaBelowRoot))
    e24KC2ThetaBelowNode130 e24KC2ThetaBelowNode131 e24KC2ThetaBelowLeaf132 e24KC2ThetaBelowLeaf133

theorem e24KC2ThetaBelowNode30 :
    adaptiveCoverCheck 16 (childLL (childHH e24ThetaBelowRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childLL (childHH e24ThetaBelowRoot))
    e24KC2ThetaBelowLeaf300 e24KC2ThetaBelowLeaf301 e24KC2ThetaBelowLeaf302 e24KC2ThetaBelowLeaf303

theorem e24KC2ThetaBelowNode31 :
    adaptiveCoverCheck 16 (childLH (childHH e24ThetaBelowRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childLH (childHH e24ThetaBelowRoot))
    e24KC2ThetaBelowLeaf310 e24KC2ThetaBelowLeaf311 e24KC2ThetaBelowLeaf312 e24KC2ThetaBelowLeaf313

theorem e24KC2ThetaBelowNode33 :
    adaptiveCoverCheck 16 (childHH (childHH e24ThetaBelowRoot)) = true :=
  adaptiveCoverCheck_succ_of_children 15 (childHH (childHH e24ThetaBelowRoot))
    e24KC2ThetaBelowLeaf330 e24KC2ThetaBelowLeaf331 e24KC2ThetaBelowLeaf332 e24KC2ThetaBelowLeaf333

theorem e24KC2ThetaBelowNode0 :
    adaptiveCoverCheck 17 (childLL e24ThetaBelowRoot) = true :=
  adaptiveCoverCheck_succ_of_children 16 (childLL e24ThetaBelowRoot)
    e24KC2ThetaBelowNode00 e24KC2ThetaBelowNode01 e24KC2ThetaBelowLeaf02 e24KC2ThetaBelowNode03

theorem e24KC2ThetaBelowNode1 :
    adaptiveCoverCheck 17 (childLH e24ThetaBelowRoot) = true :=
  adaptiveCoverCheck_succ_of_children 16 (childLH e24ThetaBelowRoot)
    e24KC2ThetaBelowNode10 e24KC2ThetaBelowNode11 e24KC2ThetaBelowNode12 e24KC2ThetaBelowNode13

theorem e24KC2ThetaBelowNode3 :
    adaptiveCoverCheck 17 (childHH e24ThetaBelowRoot) = true :=
  adaptiveCoverCheck_succ_of_children 16 (childHH e24ThetaBelowRoot)
    e24KC2ThetaBelowNode30 e24KC2ThetaBelowNode31 e24KC2ThetaBelowLeaf32 e24KC2ThetaBelowNode33

theorem e24KC2ThetaBelowNodeROOT :
    adaptiveCoverCheck 18 e24ThetaBelowRoot = true :=
  adaptiveCoverCheck_succ_of_children 17 e24ThetaBelowRoot
    e24KC2ThetaBelowNode0 e24KC2ThetaBelowNode1 e24KC2ThetaBelowLeaf2 e24KC2ThetaBelowNode3

theorem e24ThetaBelowKernelCheck :
    adaptiveCoverCheck 18 e24ThetaBelowRoot = true :=
  e24KC2ThetaBelowNodeROOT

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1101101_c0_c0_c0_c0_5_00025
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells9e0a1773d8

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end CertificateCells9e0a1773d8

open CertificateCells9e0a1773d8
namespace CoverCertificatefdb2e5aa72






























private theorem checked000 : adaptiveCoverCheck 2 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 2 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 2 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 2 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 2 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 2 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 2 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 2 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell013 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 2 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 2 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 2 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 2 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 2 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 2 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 2 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 2 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell113 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 3 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 3 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 3 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 3 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 3 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 3 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 3 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 3 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 4 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 4 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 4 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 4 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 5 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatefdb2e5aa72

theorem e24KC2PhiAboveLeaf1101101_c0_c0_c0_c0 :
    adaptiveCoverCheck 5 (childLL (childLL (childLL phiAboveCell11011010))) = true := by
  exact CoverCertificatefdb2e5aa72.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1101101_c0_c0_c0_c1_5_00026
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells5867c25b03

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end CertificateCells5867c25b03

open CertificateCells5867c25b03
namespace CoverCertificatefeab482a88






























































private theorem checked0000 : adaptiveCoverCheck 1 cell0000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell0000 (by decide +kernel)

private theorem checked0001 : adaptiveCoverCheck 1 cell0001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell0001 (by decide +kernel)

private theorem checked0002 : adaptiveCoverCheck 1 cell0002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell0002 (by decide +kernel)

private theorem checked0003 : adaptiveCoverCheck 1 cell0003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell0003 (by decide +kernel)

private theorem checked0010 : adaptiveCoverCheck 1 cell0010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell0010 (by decide +kernel)

private theorem checked0011 : adaptiveCoverCheck 1 cell0011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell0011 (by decide +kernel)

private theorem checked0012 : adaptiveCoverCheck 1 cell0012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell0012 (by decide +kernel)

private theorem checked0013 : adaptiveCoverCheck 1 cell0013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell0013 (by decide +kernel)

private theorem checked0100 : adaptiveCoverCheck 1 cell0100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell0100 (by decide +kernel)

private theorem checked0101 : adaptiveCoverCheck 1 cell0101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell0101 (by decide +kernel)

private theorem checked0102 : adaptiveCoverCheck 1 cell0102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell0102 (by decide +kernel)

private theorem checked0103 : adaptiveCoverCheck 1 cell0103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell0103 (by decide +kernel)

private theorem checked0110 : adaptiveCoverCheck 1 cell0110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell0110 (by decide +kernel)

private theorem checked0111 : adaptiveCoverCheck 1 cell0111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell0111 (by decide +kernel)

private theorem checked0112 : adaptiveCoverCheck 1 cell0112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell0112 (by decide +kernel)

private theorem checked0113 : adaptiveCoverCheck 1 cell0113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell0113 (by decide +kernel)

private theorem checked1000 : adaptiveCoverCheck 1 cell1000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell1000 (by decide +kernel)

private theorem checked1001 : adaptiveCoverCheck 1 cell1001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell1001 (by decide +kernel)

private theorem checked1002 : adaptiveCoverCheck 1 cell1002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell1002 (by decide +kernel)

private theorem checked1003 : adaptiveCoverCheck 1 cell1003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell1003 (by decide +kernel)

private theorem checked1010 : adaptiveCoverCheck 1 cell1010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell1010 (by decide +kernel)

private theorem checked1011 : adaptiveCoverCheck 1 cell1011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell1011 (by decide +kernel)

private theorem checked1012 : adaptiveCoverCheck 1 cell1012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell1012 (by decide +kernel)

private theorem checked1013 : adaptiveCoverCheck 1 cell1013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell1013 (by decide +kernel)

private theorem checked1100 : adaptiveCoverCheck 1 cell1100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell1100 (by decide +kernel)

private theorem checked1101 : adaptiveCoverCheck 1 cell1101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell1101 (by decide +kernel)

private theorem checked1102 : adaptiveCoverCheck 1 cell1102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell1102 (by decide +kernel)

private theorem checked1103 : adaptiveCoverCheck 1 cell1103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell1103 (by decide +kernel)

private theorem checked1110 : adaptiveCoverCheck 1 cell1110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell1110 (by decide +kernel)

private theorem checked1111 : adaptiveCoverCheck 1 cell1111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell1111 (by decide +kernel)

private theorem checked1112 : adaptiveCoverCheck 1 cell1112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell1112 (by decide +kernel)

private theorem checked1113 : adaptiveCoverCheck 1 cell1113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell1113 (by decide +kernel)

private theorem checked000 : adaptiveCoverCheck 2 cell000 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell000
    checked0000 checked0001 checked0002 checked0003

private theorem checked001 : adaptiveCoverCheck 2 cell001 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell001
    checked0010 checked0011 checked0012 checked0013

private theorem checked002 : adaptiveCoverCheck 2 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 2 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 2 cell010 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell010
    checked0100 checked0101 checked0102 checked0103

private theorem checked011 : adaptiveCoverCheck 2 cell011 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell011
    checked0110 checked0111 checked0112 checked0113

private theorem checked012 : adaptiveCoverCheck 2 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 2 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell013 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 2 cell100 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell100
    checked1000 checked1001 checked1002 checked1003

private theorem checked101 : adaptiveCoverCheck 2 cell101 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell101
    checked1010 checked1011 checked1012 checked1013

private theorem checked102 : adaptiveCoverCheck 2 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 2 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 2 cell110 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell110
    checked1100 checked1101 checked1102 checked1103

private theorem checked111 : adaptiveCoverCheck 2 cell111 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell111
    checked1110 checked1111 checked1112 checked1113

private theorem checked112 : adaptiveCoverCheck 2 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 2 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell113 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 3 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 3 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 3 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 3 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 3 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 3 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 3 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 3 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 4 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 4 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 4 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 4 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 5 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatefeab482a88

theorem e24KC2PhiAboveLeaf1101101_c0_c0_c0_c1 :
    adaptiveCoverCheck 5 (childLH (childLL (childLL phiAboveCell11011010))) = true := by
  exact CoverCertificatefeab482a88.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1101101_c0_c0_c0_c2_5_00027
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsca01649193

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end CertificateCellsca01649193

open CertificateCellsca01649193
namespace CoverCertificatebf967458da






private theorem checked0 : adaptiveCoverCheck 4 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 4 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 4 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 4 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 5 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatebf967458da

theorem e24KC2PhiAboveLeaf1101101_c0_c0_c0_c2 :
    adaptiveCoverCheck 5 (childHL (childLL (childLL phiAboveCell11011010))) = true := by
  exact CoverCertificatebf967458da.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1101101_c0_c0_c0_c3_5_00028
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells469c6912b9

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end CertificateCells469c6912b9

open CertificateCells469c6912b9
namespace CoverCertificate0ae56857be






private theorem checked0 : adaptiveCoverCheck 4 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 4 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 4 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 4 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 5 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate0ae56857be

theorem e24KC2PhiAboveLeaf1101101_c0_c0_c0_c3 :
    adaptiveCoverCheck 5 (childHH (childLL (childLL phiAboveCell11011010))) = true := by
  exact CoverCertificate0ae56857be.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101101_c0_c0_c0_6_00029
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellse9ea903ef1

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end CertificateCellse9ea903ef1

open CertificateCellse9ea903ef1

theorem e24KC2PhiAboveLeaf1101101_c0_c0_c0 :
    adaptiveCoverCheck 6 (childLL (childLL phiAboveCell11011010)) = true :=
  adaptiveCoverCheck_succ_of_children 5 (childLL (childLL phiAboveCell11011010))
    e24KC2PhiAboveLeaf1101101_c0_c0_c0_c0 e24KC2PhiAboveLeaf1101101_c0_c0_c0_c1
      e24KC2PhiAboveLeaf1101101_c0_c0_c0_c2 e24KC2PhiAboveLeaf1101101_c0_c0_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above
Leaf1101101_c0_c0_c1_c0_c0_4_00032
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellscf0a854a36

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))
/-- Subcell `110110100100` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell110110100100 : AngleCell :=
  childLL (childLL (childLH (childLL phiAboveCell11011010)))

end CertificateCellscf0a854a36

open CertificateCellscf0a854a36
namespace CoverCertificate2ea7c8ddef














































private theorem checked1000 : adaptiveCoverCheck 0 cell1000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1000 (by decide +kernel)

private theorem checked1001 : adaptiveCoverCheck 0 cell1001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1001 (by decide +kernel)

private theorem checked1002 : adaptiveCoverCheck 0 cell1002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1002 (by decide +kernel)

private theorem checked1003 : adaptiveCoverCheck 0 cell1003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1003 (by decide +kernel)

private theorem checked1010 : adaptiveCoverCheck 0 cell1010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1010 (by decide +kernel)

private theorem checked1011 : adaptiveCoverCheck 0 cell1011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1011 (by decide +kernel)

private theorem checked1012 : adaptiveCoverCheck 0 cell1012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1012 (by decide +kernel)

private theorem checked1013 : adaptiveCoverCheck 0 cell1013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1013 (by decide +kernel)

private theorem checked1100 : adaptiveCoverCheck 0 cell1100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1100 (by decide +kernel)

private theorem checked1101 : adaptiveCoverCheck 0 cell1101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1101 (by decide +kernel)

private theorem checked1102 : adaptiveCoverCheck 0 cell1102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1102 (by decide +kernel)

private theorem checked1103 : adaptiveCoverCheck 0 cell1103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1103 (by decide +kernel)

private theorem checked1110 : adaptiveCoverCheck 0 cell1110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1110 (by decide +kernel)

private theorem checked1111 : adaptiveCoverCheck 0 cell1111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1111 (by decide +kernel)

private theorem checked1112 : adaptiveCoverCheck 0 cell1112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1112 (by decide +kernel)

private theorem checked1113 : adaptiveCoverCheck 0 cell1113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1113 (by decide +kernel)

private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 1 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 1 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell013 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 1 cell100 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell100
    checked1000 checked1001 checked1002 checked1003

private theorem checked101 : adaptiveCoverCheck 1 cell101 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell101
    checked1010 checked1011 checked1012 checked1013

private theorem checked102 : adaptiveCoverCheck 1 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 1 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 1 cell110 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell110
    checked1100 checked1101 checked1102 checked1103

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell111
    checked1110 checked1111 checked1112 checked1113

private theorem checked112 : adaptiveCoverCheck 1 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 1 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell113 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell13 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate2ea7c8ddef

theorem e24KC2PhiAboveLeaf1101101_c0_c0_c1_c0_c0 :
    adaptiveCoverCheck 4 phiAboveCell110110100100 = true := by
  exact CoverCertificate2ea7c8ddef.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above
Leaf1101101_c0_c0_c1_c0_c1_4_00033
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellseb0fd3147a

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))
/-- Subcell `110110100101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell110110100101 : AngleCell :=
  childLH (childLL (childLH (childLL phiAboveCell11011010)))

end CertificateCellseb0fd3147a

open CertificateCellseb0fd3147a
namespace CoverCertificate75cf82dc9c






























































private theorem checked0000 : adaptiveCoverCheck 0 cell0000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0000 (by decide +kernel)

private theorem checked0001 : adaptiveCoverCheck 0 cell0001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0001 (by decide +kernel)

private theorem checked0002 : adaptiveCoverCheck 0 cell0002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0002 (by decide +kernel)

private theorem checked0003 : adaptiveCoverCheck 0 cell0003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0003 (by decide +kernel)

private theorem checked0010 : adaptiveCoverCheck 0 cell0010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0010 (by decide +kernel)

private theorem checked0011 : adaptiveCoverCheck 0 cell0011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0011 (by decide +kernel)

private theorem checked0012 : adaptiveCoverCheck 0 cell0012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0012 (by decide +kernel)

private theorem checked0013 : adaptiveCoverCheck 0 cell0013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0013 (by decide +kernel)

private theorem checked0100 : adaptiveCoverCheck 0 cell0100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0100 (by decide +kernel)

private theorem checked0101 : adaptiveCoverCheck 0 cell0101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0101 (by decide +kernel)

private theorem checked0102 : adaptiveCoverCheck 0 cell0102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0102 (by decide +kernel)

private theorem checked0103 : adaptiveCoverCheck 0 cell0103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0103 (by decide +kernel)

private theorem checked0110 : adaptiveCoverCheck 0 cell0110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0110 (by decide +kernel)

private theorem checked0111 : adaptiveCoverCheck 0 cell0111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0111 (by decide +kernel)

private theorem checked0112 : adaptiveCoverCheck 0 cell0112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0112 (by decide +kernel)

private theorem checked0113 : adaptiveCoverCheck 0 cell0113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell0113 (by decide +kernel)

private theorem checked1000 : adaptiveCoverCheck 0 cell1000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1000 (by decide +kernel)

private theorem checked1001 : adaptiveCoverCheck 0 cell1001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1001 (by decide +kernel)

private theorem checked1002 : adaptiveCoverCheck 0 cell1002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1002 (by decide +kernel)

private theorem checked1003 : adaptiveCoverCheck 0 cell1003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1003 (by decide +kernel)

private theorem checked1010 : adaptiveCoverCheck 0 cell1010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1010 (by decide +kernel)

private theorem checked1011 : adaptiveCoverCheck 0 cell1011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1011 (by decide +kernel)

private theorem checked1012 : adaptiveCoverCheck 0 cell1012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1012 (by decide +kernel)

private theorem checked1013 : adaptiveCoverCheck 0 cell1013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1013 (by decide +kernel)

private theorem checked1100 : adaptiveCoverCheck 0 cell1100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1100 (by decide +kernel)

private theorem checked1101 : adaptiveCoverCheck 0 cell1101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1101 (by decide +kernel)

private theorem checked1102 : adaptiveCoverCheck 0 cell1102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1102 (by decide +kernel)

private theorem checked1103 : adaptiveCoverCheck 0 cell1103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 0 cell1103 (by decide +kernel)

private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell000
    checked0000 checked0001 checked0002 checked0003

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell001
    checked0010 checked0011 checked0012 checked0013

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell010
    checked0100 checked0101 checked0102 checked0103

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell011
    checked0110 checked0111 checked0112 checked0113

private theorem checked012 : adaptiveCoverCheck 1 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 1 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell013 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 1 cell100 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell100
    checked1000 checked1001 checked1002 checked1003

private theorem checked101 : adaptiveCoverCheck 1 cell101 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell101
    checked1010 checked1011 checked1012 checked1013

private theorem checked102 : adaptiveCoverCheck 1 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 1 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 1 cell110 = true := by
  exact adaptiveCoverCheck_succ_of_children 0 cell110
    checked1100 checked1101 checked1102 checked1103

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 1 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 1 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell113 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell03 (by decide +kernel)

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell12 (by decide +kernel)

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell13 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate75cf82dc9c

theorem e24KC2PhiAboveLeaf1101101_c0_c0_c1_c0_c1 :
    adaptiveCoverCheck 4 phiAboveCell110110100101 = true := by
  exact CoverCertificate75cf82dc9c.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above
Leaf1101101_c0_c0_c1_c0_c2_4_00034
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa5ae349f6a

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))
/-- Subcell `110110100102` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell110110100102 : AngleCell :=
  childHL (childLL (childLH (childLL phiAboveCell11011010)))

end CertificateCellsa5ae349f6a

open CertificateCellsa5ae349f6a
namespace CoverCertificate94c7306624






private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate94c7306624

theorem e24KC2PhiAboveLeaf1101101_c0_c0_c1_c0_c2 :
    adaptiveCoverCheck 4 phiAboveCell110110100102 = true := by
  exact CoverCertificate94c7306624.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above
Leaf1101101_c0_c0_c1_c0_c3_4_00035
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsed6c91cc2c

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))
/-- Subcell `110110100103` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell110110100103 : AngleCell :=
  childHH (childLL (childLH (childLL phiAboveCell11011010)))

end CertificateCellsed6c91cc2c

open CertificateCellsed6c91cc2c
namespace CoverCertificatefc8969e3d2






private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatefc8969e3d2

theorem e24KC2PhiAboveLeaf1101101_c0_c0_c1_c0_c3 :
    adaptiveCoverCheck 4 phiAboveCell110110100103 = true := by
  exact CoverCertificatefc8969e3d2.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101101_c0_c0_c1_c0_5_00036
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells89d797401e

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end CertificateCells89d797401e

open CertificateCells89d797401e

theorem e24KC2PhiAboveLeaf1101101_c0_c0_c1_c0 :
    adaptiveCoverCheck 5 (childLL (childLH (childLL phiAboveCell11011010))) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLL (childLH (childLL phiAboveCell11011010)))
    e24KC2PhiAboveLeaf1101101_c0_c0_c1_c0_c0 e24KC2PhiAboveLeaf1101101_c0_c0_c1_c0_c1
      e24KC2PhiAboveLeaf1101101_c0_c0_c1_c0_c2 e24KC2PhiAboveLeaf1101101_c0_c0_c1_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above
Leaf1101101_c0_c0_c1_c1_c0_4_00038
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsd58d6f2902

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))
/-- Subcell `110110100110` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell110110100110 : AngleCell :=
  childLL (childLH (childLH (childLL phiAboveCell11011010)))

end CertificateCellsd58d6f2902

open CertificateCellsd58d6f2902
namespace CoverCertificate0773e6576d


















































private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 1 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 1 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell013 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 1 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 1 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 1 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 1 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell033 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 1 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 1 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 1 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 1 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 1 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 1 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 1 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell113 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 1 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 1 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 1 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 1 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 1 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 1 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 1 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 1 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell133 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell02 (by decide +kernel)

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate0773e6576d

theorem e24KC2PhiAboveLeaf1101101_c0_c0_c1_c1_c0 :
    adaptiveCoverCheck 4 phiAboveCell110110100110 = true := by
  exact CoverCertificate0773e6576d.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above
Leaf1101101_c0_c0_c1_c1_c1_4_00039
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsaa730af275

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))
/-- Subcell `110110100111` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell110110100111 : AngleCell :=
  childLH (childLH (childLH (childLL phiAboveCell11011010)))

end CertificateCellsaa730af275

open CertificateCellsaa730af275
namespace CoverCertificate6cd163be74






















































private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 1 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 1 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell013 (by decide +kernel)

private theorem checked020 : adaptiveCoverCheck 1 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 1 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 1 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 1 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 1 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 1 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 1 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 1 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell033 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 1 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 1 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 1 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 1 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 1 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 1 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 1 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell113 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 1 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 1 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 1 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 1 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 1 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 1 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 1 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 1 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell133 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate6cd163be74

theorem e24KC2PhiAboveLeaf1101101_c0_c0_c1_c1_c1 :
    adaptiveCoverCheck 4 phiAboveCell110110100111 = true := by
  exact CoverCertificate6cd163be74.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above
Leaf1101101_c0_c0_c1_c1_c2_4_00040
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellse47b06e09b

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))
/-- Subcell `110110100112` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell110110100112 : AngleCell :=
  childHL (childLH (childLH (childLL phiAboveCell11011010)))

end CertificateCellse47b06e09b

open CertificateCellse47b06e09b
namespace CoverCertificate105a276d33






private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate105a276d33

theorem e24KC2PhiAboveLeaf1101101_c0_c0_c1_c1_c2 :
    adaptiveCoverCheck 4 phiAboveCell110110100112 = true := by
  exact CoverCertificate105a276d33.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above
Leaf1101101_c0_c0_c1_c1_c3_4_00041
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells6d37377041

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))
/-- Subcell `110110100113` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell110110100113 : AngleCell :=
  childHH (childLH (childLH (childLL phiAboveCell11011010)))

end CertificateCells6d37377041

open CertificateCells6d37377041
namespace CoverCertificate7b7ada8a92






private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate7b7ada8a92

theorem e24KC2PhiAboveLeaf1101101_c0_c0_c1_c1_c3 :
    adaptiveCoverCheck 4 phiAboveCell110110100113 = true := by
  exact CoverCertificate7b7ada8a92.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101101_c0_c0_c1_c1_5_00042
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsafdf6e4305

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end CertificateCellsafdf6e4305

open CertificateCellsafdf6e4305

theorem e24KC2PhiAboveLeaf1101101_c0_c0_c1_c1 :
    adaptiveCoverCheck 5 (childLH (childLH (childLL phiAboveCell11011010))) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLH (childLH (childLL phiAboveCell11011010)))
    e24KC2PhiAboveLeaf1101101_c0_c0_c1_c1_c0 e24KC2PhiAboveLeaf1101101_c0_c0_c1_c1_c1
      e24KC2PhiAboveLeaf1101101_c0_c0_c1_c1_c2 e24KC2PhiAboveLeaf1101101_c0_c0_c1_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1101101_c0_c0_c1_c2_5_00043
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellse508f838c4

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end CertificateCellse508f838c4

open CertificateCellse508f838c4
namespace CoverCertificate216e1a86b9






private theorem checked0 : adaptiveCoverCheck 4 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 4 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 4 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 4 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 5 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate216e1a86b9

theorem e24KC2PhiAboveLeaf1101101_c0_c0_c1_c2 :
    adaptiveCoverCheck 5 (childHL (childLH (childLL phiAboveCell11011010))) = true := by
  exact CoverCertificate216e1a86b9.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1101101_c0_c0_c1_c3_5_00044
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells1cda533a6e

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end CertificateCells1cda533a6e

open CertificateCells1cda533a6e
namespace CoverCertificatecbce86617c






private theorem checked0 : adaptiveCoverCheck 4 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 4 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 4 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 4 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 5 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatecbce86617c

theorem e24KC2PhiAboveLeaf1101101_c0_c0_c1_c3 :
    adaptiveCoverCheck 5 (childHH (childLH (childLL phiAboveCell11011010))) = true := by
  exact CoverCertificatecbce86617c.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101101_c0_c0_c1_6_00045
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells0d2c374949

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end CertificateCells0d2c374949

open CertificateCells0d2c374949

theorem e24KC2PhiAboveLeaf1101101_c0_c0_c1 :
    adaptiveCoverCheck 6 (childLH (childLL phiAboveCell11011010)) = true :=
  adaptiveCoverCheck_succ_of_children 5 (childLH (childLL phiAboveCell11011010))
    e24KC2PhiAboveLeaf1101101_c0_c0_c1_c0 e24KC2PhiAboveLeaf1101101_c0_c0_c1_c1
      e24KC2PhiAboveLeaf1101101_c0_c0_c1_c2 e24KC2PhiAboveLeaf1101101_c0_c0_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1101101_c0_c0_c2_6_00046
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells3babcd7448

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end CertificateCells3babcd7448

open CertificateCells3babcd7448
namespace CoverCertificate5b9a8c2094






private theorem checked0 : adaptiveCoverCheck 5 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 5 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 5 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 5 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 6 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate5b9a8c2094

theorem e24KC2PhiAboveLeaf1101101_c0_c0_c2 :
    adaptiveCoverCheck 6 (childHL (childLL phiAboveCell11011010)) = true := by
  exact CoverCertificate5b9a8c2094.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1101101_c0_c0_c3_6_00047
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsbbdc1f9510

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end CertificateCellsbbdc1f9510

open CertificateCellsbbdc1f9510
namespace CoverCertificatee500b98dc1






private theorem checked0 : adaptiveCoverCheck 5 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 5 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 5 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 5 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 6 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatee500b98dc1

theorem e24KC2PhiAboveLeaf1101101_c0_c0_c3 :
    adaptiveCoverCheck 6 (childHH (childLL phiAboveCell11011010)) = true := by
  exact CoverCertificatee500b98dc1.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101101_c0_c0_7_00048
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells3df86e4955

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end CertificateCells3df86e4955

open CertificateCells3df86e4955

theorem e24KC2PhiAboveLeaf1101101_c0_c0 :
    adaptiveCoverCheck 7 (childLL phiAboveCell11011010) = true :=
  adaptiveCoverCheck_succ_of_children 6 (childLL phiAboveCell11011010)
    e24KC2PhiAboveLeaf1101101_c0_c0_c0 e24KC2PhiAboveLeaf1101101_c0_c0_c1
      e24KC2PhiAboveLeaf1101101_c0_c0_c2 e24KC2PhiAboveLeaf1101101_c0_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above
Leaf1101101_c0_c1_c0_c0_c0_4_00052
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells44a650755e

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))
/-- Subcell `110110101000` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell110110101000 : AngleCell :=
  childLL (childLL (childLL (childLH phiAboveCell11011010)))

end CertificateCells44a650755e

open CertificateCells44a650755e
namespace CoverCertificatec4a9c16244






















































private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 1 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 1 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell013 (by decide +kernel)

private theorem checked020 : adaptiveCoverCheck 1 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 1 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 1 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 1 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 1 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 1 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 1 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 1 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell033 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 1 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 1 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 1 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 1 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 1 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 1 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 1 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell113 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 1 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 1 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 1 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 1 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 1 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 1 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 1 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 1 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell133 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatec4a9c16244

theorem e24KC2PhiAboveLeaf1101101_c0_c1_c0_c0_c0 :
    adaptiveCoverCheck 4 phiAboveCell110110101000 = true := by
  exact CoverCertificatec4a9c16244.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above
Leaf1101101_c0_c1_c0_c0_c1_4_00053
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells9dff8fd68c

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))
/-- Subcell `110110101001` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell110110101001 : AngleCell :=
  childLH (childLL (childLL (childLH phiAboveCell11011010)))

end CertificateCells9dff8fd68c

open CertificateCells9dff8fd68c
namespace CoverCertificated58785d59b






















































private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 1 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 1 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell013 (by decide +kernel)

private theorem checked020 : adaptiveCoverCheck 1 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 1 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 1 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 1 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 1 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 1 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 1 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 1 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell033 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 1 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 1 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 1 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 1 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 1 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 1 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 1 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell113 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 1 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 1 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 1 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 1 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 1 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 1 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 1 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 1 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell133 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificated58785d59b

theorem e24KC2PhiAboveLeaf1101101_c0_c1_c0_c0_c1 :
    adaptiveCoverCheck 4 phiAboveCell110110101001 = true := by
  exact CoverCertificated58785d59b.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above
Leaf1101101_c0_c1_c0_c0_c2_4_00054
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells0eb9c7dd4e

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))
/-- Subcell `110110101002` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell110110101002 : AngleCell :=
  childHL (childLL (childLL (childLH phiAboveCell11011010)))

end CertificateCells0eb9c7dd4e

open CertificateCells0eb9c7dd4e
namespace CoverCertificate770e3357d2






private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate770e3357d2

theorem e24KC2PhiAboveLeaf1101101_c0_c1_c0_c0_c2 :
    adaptiveCoverCheck 4 phiAboveCell110110101002 = true := by
  exact CoverCertificate770e3357d2.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above
Leaf1101101_c0_c1_c0_c0_c3_4_00055
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa1f8281244

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))
/-- Subcell `110110101003` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell110110101003 : AngleCell :=
  childHH (childLL (childLL (childLH phiAboveCell11011010)))

end CertificateCellsa1f8281244

open CertificateCellsa1f8281244
namespace CoverCertificate4042eb5094






private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate4042eb5094

theorem e24KC2PhiAboveLeaf1101101_c0_c1_c0_c0_c3 :
    adaptiveCoverCheck 4 phiAboveCell110110101003 = true := by
  exact CoverCertificate4042eb5094.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101101_c0_c1_c0_c0_5_00056
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells3298a326ef

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end CertificateCells3298a326ef

open CertificateCells3298a326ef

theorem e24KC2PhiAboveLeaf1101101_c0_c1_c0_c0 :
    adaptiveCoverCheck 5 (childLL (childLL (childLH phiAboveCell11011010))) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLL (childLL (childLH phiAboveCell11011010)))
    e24KC2PhiAboveLeaf1101101_c0_c1_c0_c0_c0 e24KC2PhiAboveLeaf1101101_c0_c1_c0_c0_c1
      e24KC2PhiAboveLeaf1101101_c0_c1_c0_c0_c2 e24KC2PhiAboveLeaf1101101_c0_c1_c0_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above
Leaf1101101_c0_c1_c0_c1_c0_4_00058
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsa31bfb0e48

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))
/-- Subcell `110110101010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell110110101010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell11011010)))

end CertificateCellsa31bfb0e48

open CertificateCellsa31bfb0e48
namespace CoverCertificate9283dd1f18


























































private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 1 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 1 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell013 (by decide +kernel)

private theorem checked020 : adaptiveCoverCheck 1 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 1 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 1 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 1 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 1 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 1 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 1 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 1 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell033 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 1 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 1 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 1 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 1 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 1 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 1 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 1 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell113 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 1 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 1 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 1 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 1 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 1 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 1 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 1 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 1 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell133 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 1 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 1 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 1 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 1 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell313 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate9283dd1f18

theorem e24KC2PhiAboveLeaf1101101_c0_c1_c0_c1_c0 :
    adaptiveCoverCheck 4 phiAboveCell110110101010 = true := by
  exact CoverCertificate9283dd1f18.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above
Leaf1101101_c0_c1_c0_c1_c1_4_00059
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsba54477f25

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))
/-- Subcell `110110101011` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell110110101011 : AngleCell :=
  childLH (childLH (childLL (childLH phiAboveCell11011010)))

end CertificateCellsba54477f25

open CertificateCellsba54477f25
namespace CoverCertificate5607aeacca






















































private theorem checked000 : adaptiveCoverCheck 1 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 1 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 1 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 1 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 1 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 1 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 1 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 1 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell013 (by decide +kernel)

private theorem checked020 : adaptiveCoverCheck 1 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 1 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 1 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 1 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 1 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 1 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 1 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 1 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell033 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 1 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 1 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 1 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 1 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 1 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 1 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 1 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 1 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell113 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 1 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 1 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 1 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 1 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell123 (by decide +kernel)

private theorem checked200 : adaptiveCoverCheck 1 cell200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell200 (by decide +kernel)

private theorem checked201 : adaptiveCoverCheck 1 cell201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell201 (by decide +kernel)

private theorem checked202 : adaptiveCoverCheck 1 cell202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell202 (by decide +kernel)

private theorem checked203 : adaptiveCoverCheck 1 cell203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell203 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 2 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 2 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 2 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 2 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 2 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 2 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 2 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 2 cell13 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell13 (by decide +kernel)

private theorem checked20 : adaptiveCoverCheck 2 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 2 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 2 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 2 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 2 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 2 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 2 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 2 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate5607aeacca

theorem e24KC2PhiAboveLeaf1101101_c0_c1_c0_c1_c1 :
    adaptiveCoverCheck 4 phiAboveCell110110101011 = true := by
  exact CoverCertificate5607aeacca.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above
Leaf1101101_c0_c1_c0_c1_c2_4_00060
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells40378f08af

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))
/-- Subcell `110110101012` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell110110101012 : AngleCell :=
  childHL (childLH (childLL (childLH phiAboveCell11011010)))

end CertificateCells40378f08af

open CertificateCells40378f08af
namespace CoverCertificate093986cbf5






private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate093986cbf5

theorem e24KC2PhiAboveLeaf1101101_c0_c1_c0_c1_c2 :
    adaptiveCoverCheck 4 phiAboveCell110110101012 = true := by
  exact CoverCertificate093986cbf5.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above
Leaf1101101_c0_c1_c0_c1_c3_4_00061
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsbef31c9887

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))
/-- Subcell `110110101013` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell110110101013 : AngleCell :=
  childHH (childLH (childLL (childLH phiAboveCell11011010)))

end CertificateCellsbef31c9887

open CertificateCellsbef31c9887
namespace CoverCertificate4478c1ce2d






private theorem checked0 : adaptiveCoverCheck 3 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 3 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 3 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 3 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 4 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate4478c1ce2d

theorem e24KC2PhiAboveLeaf1101101_c0_c1_c0_c1_c3 :
    adaptiveCoverCheck 4 phiAboveCell110110101013 = true := by
  exact CoverCertificate4478c1ce2d.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101101_c0_c1_c0_c1_5_00062
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells47980ca575

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end CertificateCells47980ca575

open CertificateCells47980ca575

theorem e24KC2PhiAboveLeaf1101101_c0_c1_c0_c1 :
    adaptiveCoverCheck 5 (childLH (childLL (childLH phiAboveCell11011010))) = true :=
  adaptiveCoverCheck_succ_of_children 4 (childLH (childLL (childLH phiAboveCell11011010)))
    e24KC2PhiAboveLeaf1101101_c0_c1_c0_c1_c0 e24KC2PhiAboveLeaf1101101_c0_c1_c0_c1_c1
      e24KC2PhiAboveLeaf1101101_c0_c1_c0_c1_c2 e24KC2PhiAboveLeaf1101101_c0_c1_c0_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1101101_c0_c1_c0_c2_5_00063
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells6837eba069

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end CertificateCells6837eba069

open CertificateCells6837eba069
namespace CoverCertificate52d1f78193






private theorem checked0 : adaptiveCoverCheck 4 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 4 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 4 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 4 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 5 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate52d1f78193

theorem e24KC2PhiAboveLeaf1101101_c0_c1_c0_c2 :
    adaptiveCoverCheck 5 (childHL (childLL (childLH phiAboveCell11011010))) = true := by
  exact CoverCertificate52d1f78193.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1101101_c0_c1_c0_c3_5_00064
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells21829695a9

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end CertificateCells21829695a9

open CertificateCells21829695a9
namespace CoverCertificate263f6f95b0






private theorem checked0 : adaptiveCoverCheck 4 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 4 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 4 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 4 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 5 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate263f6f95b0

theorem e24KC2PhiAboveLeaf1101101_c0_c1_c0_c3 :
    adaptiveCoverCheck 5 (childHH (childLL (childLH phiAboveCell11011010))) = true := by
  exact CoverCertificate263f6f95b0.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101101_c0_c1_c0_6_00065
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsfed39385df

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end CertificateCellsfed39385df

open CertificateCellsfed39385df

theorem e24KC2PhiAboveLeaf1101101_c0_c1_c0 :
    adaptiveCoverCheck 6 (childLL (childLH phiAboveCell11011010)) = true :=
  adaptiveCoverCheck_succ_of_children 5 (childLL (childLH phiAboveCell11011010))
    e24KC2PhiAboveLeaf1101101_c0_c1_c0_c0 e24KC2PhiAboveLeaf1101101_c0_c1_c0_c1
      e24KC2PhiAboveLeaf1101101_c0_c1_c0_c2 e24KC2PhiAboveLeaf1101101_c0_c1_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1101101_c0_c1_c1_c0_5_00067
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsd170a2bed6

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end CertificateCellsd170a2bed6

open CertificateCellsd170a2bed6
namespace CoverCertificatefad4f5904e


























































private theorem checked0000 : adaptiveCoverCheck 1 cell0000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell0000 (by decide +kernel)

private theorem checked0001 : adaptiveCoverCheck 1 cell0001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell0001 (by decide +kernel)

private theorem checked0002 : adaptiveCoverCheck 1 cell0002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell0002 (by decide +kernel)

private theorem checked0003 : adaptiveCoverCheck 1 cell0003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 1 cell0003 (by decide +kernel)

private theorem checked000 : adaptiveCoverCheck 2 cell000 = true := by
  exact adaptiveCoverCheck_succ_of_children 1 cell000
    checked0000 checked0001 checked0002 checked0003

private theorem checked001 : adaptiveCoverCheck 2 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 2 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 2 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 2 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 2 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 2 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 2 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell013 (by decide +kernel)

private theorem checked020 : adaptiveCoverCheck 2 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 2 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 2 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 2 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 2 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 2 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 2 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 2 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell033 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 2 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 2 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 2 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 2 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 2 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 2 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 2 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 2 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell113 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 2 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 2 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 2 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 2 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 2 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 2 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 2 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 2 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell133 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 3 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 3 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 3 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 3 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 3 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 3 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 3 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 3 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 3 cell20 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell20 (by decide +kernel)

private theorem checked21 : adaptiveCoverCheck 3 cell21 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell21 (by decide +kernel)

private theorem checked22 : adaptiveCoverCheck 3 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 3 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 3 cell30 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell30 (by decide +kernel)

private theorem checked31 : adaptiveCoverCheck 3 cell31 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell31 (by decide +kernel)

private theorem checked32 : adaptiveCoverCheck 3 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 3 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 4 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 4 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 4 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 4 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 5 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatefad4f5904e

theorem e24KC2PhiAboveLeaf1101101_c0_c1_c1_c0 :
    adaptiveCoverCheck 5 (childLL (childLH (childLH phiAboveCell11011010))) = true := by
  exact CoverCertificatefad4f5904e.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1101101_c0_c1_c1_c1_5_00068
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells3fed941c0c

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end CertificateCells3fed941c0c

open CertificateCells3fed941c0c
namespace CoverCertificatec88446cc5e






































































private theorem checked000 : adaptiveCoverCheck 2 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 2 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 2 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 2 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 2 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 2 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 2 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 2 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell013 (by decide +kernel)

private theorem checked020 : adaptiveCoverCheck 2 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 2 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 2 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 2 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 2 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 2 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 2 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 2 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell033 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 2 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 2 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 2 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 2 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 2 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 2 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 2 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 2 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell113 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 2 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 2 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 2 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 2 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 2 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 2 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 2 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 2 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell133 (by decide +kernel)

private theorem checked200 : adaptiveCoverCheck 2 cell200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell200 (by decide +kernel)

private theorem checked201 : adaptiveCoverCheck 2 cell201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell201 (by decide +kernel)

private theorem checked202 : adaptiveCoverCheck 2 cell202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell202 (by decide +kernel)

private theorem checked203 : adaptiveCoverCheck 2 cell203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell203 (by decide +kernel)

private theorem checked210 : adaptiveCoverCheck 2 cell210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell210 (by decide +kernel)

private theorem checked211 : adaptiveCoverCheck 2 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 2 cell212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell212 (by decide +kernel)

private theorem checked213 : adaptiveCoverCheck 2 cell213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell213 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 2 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 2 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 2 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 2 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 2 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 2 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 2 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 2 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell313 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 3 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 3 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 3 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 3 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 3 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 3 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 3 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 3 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 3 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 3 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 3 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 3 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 3 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 3 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 3 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 3 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 4 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 4 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 4 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 4 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 5 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatec88446cc5e

theorem e24KC2PhiAboveLeaf1101101_c0_c1_c1_c1 :
    adaptiveCoverCheck 5 (childLH (childLH (childLH phiAboveCell11011010))) = true := by
  exact CoverCertificatec88446cc5e.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1101101_c0_c1_c1_c2_5_00069
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsb780467ddc

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end CertificateCellsb780467ddc

open CertificateCellsb780467ddc
namespace CoverCertificate8053b84bb6






private theorem checked0 : adaptiveCoverCheck 4 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 4 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 4 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 4 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 5 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate8053b84bb6

theorem e24KC2PhiAboveLeaf1101101_c0_c1_c1_c2 :
    adaptiveCoverCheck 5 (childHL (childLH (childLH phiAboveCell11011010))) = true := by
  exact CoverCertificate8053b84bb6.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1101101_c0_c1_c1_c3_5_00070
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellse5752d8306

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end CertificateCellse5752d8306

open CertificateCellse5752d8306
namespace CoverCertificatea83bf6868e






private theorem checked0 : adaptiveCoverCheck 4 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 4 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 4 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 4 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 4 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 5 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatea83bf6868e

theorem e24KC2PhiAboveLeaf1101101_c0_c1_c1_c3 :
    adaptiveCoverCheck 5 (childHH (childLH (childLH phiAboveCell11011010))) = true := by
  exact CoverCertificatea83bf6868e.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101101_c0_c1_c1_6_00071
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsb1b33fecca

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end CertificateCellsb1b33fecca

open CertificateCellsb1b33fecca

theorem e24KC2PhiAboveLeaf1101101_c0_c1_c1 :
    adaptiveCoverCheck 6 (childLH (childLH phiAboveCell11011010)) = true :=
  adaptiveCoverCheck_succ_of_children 5 (childLH (childLH phiAboveCell11011010))
    e24KC2PhiAboveLeaf1101101_c0_c1_c1_c0 e24KC2PhiAboveLeaf1101101_c0_c1_c1_c1
      e24KC2PhiAboveLeaf1101101_c0_c1_c1_c2 e24KC2PhiAboveLeaf1101101_c0_c1_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1101101_c0_c1_c2_6_00072
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells18ee7077e5

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end CertificateCells18ee7077e5

open CertificateCells18ee7077e5
namespace CoverCertificatec458632307






private theorem checked0 : adaptiveCoverCheck 5 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 5 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 5 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 5 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 6 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatec458632307

theorem e24KC2PhiAboveLeaf1101101_c0_c1_c2 :
    adaptiveCoverCheck 6 (childHL (childLH phiAboveCell11011010)) = true := by
  exact CoverCertificatec458632307.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1101101_c0_c1_c3_6_00073
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells481c5d2cb5

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end CertificateCells481c5d2cb5

open CertificateCells481c5d2cb5
namespace CoverCertificate5ac90060dc






private theorem checked0 : adaptiveCoverCheck 5 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 5 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 5 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 5 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 5 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 6 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 5 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate5ac90060dc

theorem e24KC2PhiAboveLeaf1101101_c0_c1_c3 :
    adaptiveCoverCheck 6 (childHH (childLH phiAboveCell11011010)) = true := by
  exact CoverCertificate5ac90060dc.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101101_c0_c1_7_00074
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsc427a8578f

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end CertificateCellsc427a8578f

open CertificateCellsc427a8578f

theorem e24KC2PhiAboveLeaf1101101_c0_c1 :
    adaptiveCoverCheck 7 (childLH phiAboveCell11011010) = true :=
  adaptiveCoverCheck_succ_of_children 6 (childLH phiAboveCell11011010)
    e24KC2PhiAboveLeaf1101101_c0_c1_c0 e24KC2PhiAboveLeaf1101101_c0_c1_c1
      e24KC2PhiAboveLeaf1101101_c0_c1_c2 e24KC2PhiAboveLeaf1101101_c0_c1_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1101101_c0_c2_7_00075
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsc1762ca3ac

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end CertificateCellsc1762ca3ac

open CertificateCellsc1762ca3ac
namespace CoverCertificatee2e2523660






private theorem checked0 : adaptiveCoverCheck 6 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 6 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 6 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 6 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 7 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificatee2e2523660

theorem e24KC2PhiAboveLeaf1101101_c0_c2 :
    adaptiveCoverCheck 7 (childHL phiAboveCell11011010) = true := by
  exact CoverCertificatee2e2523660.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1101101_c0_c3_7_00076
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells105558b317

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end CertificateCells105558b317

open CertificateCells105558b317
namespace CoverCertificate2c610dcf32






private theorem checked0 : adaptiveCoverCheck 6 cell0 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell0 (by decide +kernel)

private theorem checked1 : adaptiveCoverCheck 6 cell1 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell1 (by decide +kernel)

private theorem checked2 : adaptiveCoverCheck 6 cell2 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell2 (by decide +kernel)

private theorem checked3 : adaptiveCoverCheck 6 cell3 = true := by
  exact adaptiveCoverCheck_true_of_rejected 6 cell3 (by decide +kernel)

private theorem checkedRoot : adaptiveCoverCheck 7 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 6 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate2c610dcf32

theorem e24KC2PhiAboveLeaf1101101_c0_c3 :
    adaptiveCoverCheck 7 (childHH phiAboveCell11011010) = true := by
  exact CoverCertificate2c610dcf32.checkedRoot

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Join_e24KC2Phi Above Leaf1101101_c0_8_00077
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells25978ec18d

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011010` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011010 : AngleCell :=
  childLL (childLH (childLL (childLH phiAboveCell1101)))

end CertificateCells25978ec18d

open CertificateCells25978ec18d

theorem e24KC2PhiAboveLeaf1101101_c0 :
    adaptiveCoverCheck 8 phiAboveCell11011010 = true :=
  adaptiveCoverCheck_succ_of_children 7 phiAboveCell11011010
    e24KC2PhiAboveLeaf1101101_c0_c0 e24KC2PhiAboveLeaf1101101_c0_c1
      e24KC2PhiAboveLeaf1101101_c0_c2 e24KC2PhiAboveLeaf1101101_c0_c3

end PartE
end GerverSofa

end

end

end

section

/-!
# Gerver Sofa / Kernel Only / Part E / E24KC5Direct_e24KC2Phi Above Leaf1101101_c1_c0_c0_c0_5_00081
-/

@[expose] public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCells411895cea3

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.
/-- Subcell `1101` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell1101 : AngleCell :=
  childLH (childLL (childLH (childLH e24PhiAboveRoot)))
/-- Subcell `11011011` of the phi-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev phiAboveCell11011011 : AngleCell :=
  childLH (childLH (childLL (childLH phiAboveCell1101)))

end CertificateCells411895cea3

open CertificateCells411895cea3
namespace CoverCertificate7a43bce112






































































private theorem checked000 : adaptiveCoverCheck 2 cell000 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell000 (by decide +kernel)

private theorem checked001 : adaptiveCoverCheck 2 cell001 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell001 (by decide +kernel)

private theorem checked002 : adaptiveCoverCheck 2 cell002 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell002 (by decide +kernel)

private theorem checked003 : adaptiveCoverCheck 2 cell003 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell003 (by decide +kernel)

private theorem checked010 : adaptiveCoverCheck 2 cell010 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell010 (by decide +kernel)

private theorem checked011 : adaptiveCoverCheck 2 cell011 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell011 (by decide +kernel)

private theorem checked012 : adaptiveCoverCheck 2 cell012 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell012 (by decide +kernel)

private theorem checked013 : adaptiveCoverCheck 2 cell013 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell013 (by decide +kernel)

private theorem checked020 : adaptiveCoverCheck 2 cell020 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell020 (by decide +kernel)

private theorem checked021 : adaptiveCoverCheck 2 cell021 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell021 (by decide +kernel)

private theorem checked022 : adaptiveCoverCheck 2 cell022 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell022 (by decide +kernel)

private theorem checked023 : adaptiveCoverCheck 2 cell023 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell023 (by decide +kernel)

private theorem checked030 : adaptiveCoverCheck 2 cell030 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell030 (by decide +kernel)

private theorem checked031 : adaptiveCoverCheck 2 cell031 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell031 (by decide +kernel)

private theorem checked032 : adaptiveCoverCheck 2 cell032 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell032 (by decide +kernel)

private theorem checked033 : adaptiveCoverCheck 2 cell033 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell033 (by decide +kernel)

private theorem checked100 : adaptiveCoverCheck 2 cell100 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell100 (by decide +kernel)

private theorem checked101 : adaptiveCoverCheck 2 cell101 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell101 (by decide +kernel)

private theorem checked102 : adaptiveCoverCheck 2 cell102 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell102 (by decide +kernel)

private theorem checked103 : adaptiveCoverCheck 2 cell103 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell103 (by decide +kernel)

private theorem checked110 : adaptiveCoverCheck 2 cell110 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell110 (by decide +kernel)

private theorem checked111 : adaptiveCoverCheck 2 cell111 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell111 (by decide +kernel)

private theorem checked112 : adaptiveCoverCheck 2 cell112 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell112 (by decide +kernel)

private theorem checked113 : adaptiveCoverCheck 2 cell113 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell113 (by decide +kernel)

private theorem checked120 : adaptiveCoverCheck 2 cell120 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell120 (by decide +kernel)

private theorem checked121 : adaptiveCoverCheck 2 cell121 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell121 (by decide +kernel)

private theorem checked122 : adaptiveCoverCheck 2 cell122 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell122 (by decide +kernel)

private theorem checked123 : adaptiveCoverCheck 2 cell123 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell123 (by decide +kernel)

private theorem checked130 : adaptiveCoverCheck 2 cell130 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell130 (by decide +kernel)

private theorem checked131 : adaptiveCoverCheck 2 cell131 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell131 (by decide +kernel)

private theorem checked132 : adaptiveCoverCheck 2 cell132 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell132 (by decide +kernel)

private theorem checked133 : adaptiveCoverCheck 2 cell133 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell133 (by decide +kernel)

private theorem checked200 : adaptiveCoverCheck 2 cell200 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell200 (by decide +kernel)

private theorem checked201 : adaptiveCoverCheck 2 cell201 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell201 (by decide +kernel)

private theorem checked202 : adaptiveCoverCheck 2 cell202 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell202 (by decide +kernel)

private theorem checked203 : adaptiveCoverCheck 2 cell203 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell203 (by decide +kernel)

private theorem checked210 : adaptiveCoverCheck 2 cell210 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell210 (by decide +kernel)

private theorem checked211 : adaptiveCoverCheck 2 cell211 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell211 (by decide +kernel)

private theorem checked212 : adaptiveCoverCheck 2 cell212 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell212 (by decide +kernel)

private theorem checked213 : adaptiveCoverCheck 2 cell213 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell213 (by decide +kernel)

private theorem checked300 : adaptiveCoverCheck 2 cell300 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell300 (by decide +kernel)

private theorem checked301 : adaptiveCoverCheck 2 cell301 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell301 (by decide +kernel)

private theorem checked302 : adaptiveCoverCheck 2 cell302 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell302 (by decide +kernel)

private theorem checked303 : adaptiveCoverCheck 2 cell303 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell303 (by decide +kernel)

private theorem checked310 : adaptiveCoverCheck 2 cell310 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell310 (by decide +kernel)

private theorem checked311 : adaptiveCoverCheck 2 cell311 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell311 (by decide +kernel)

private theorem checked312 : adaptiveCoverCheck 2 cell312 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell312 (by decide +kernel)

private theorem checked313 : adaptiveCoverCheck 2 cell313 = true := by
  exact adaptiveCoverCheck_true_of_rejected 2 cell313 (by decide +kernel)

private theorem checked00 : adaptiveCoverCheck 3 cell00 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell00
    checked000 checked001 checked002 checked003

private theorem checked01 : adaptiveCoverCheck 3 cell01 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell01
    checked010 checked011 checked012 checked013

private theorem checked02 : adaptiveCoverCheck 3 cell02 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell02
    checked020 checked021 checked022 checked023

private theorem checked03 : adaptiveCoverCheck 3 cell03 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell03
    checked030 checked031 checked032 checked033

private theorem checked10 : adaptiveCoverCheck 3 cell10 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell10
    checked100 checked101 checked102 checked103

private theorem checked11 : adaptiveCoverCheck 3 cell11 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell11
    checked110 checked111 checked112 checked113

private theorem checked12 : adaptiveCoverCheck 3 cell12 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell12
    checked120 checked121 checked122 checked123

private theorem checked13 : adaptiveCoverCheck 3 cell13 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell13
    checked130 checked131 checked132 checked133

private theorem checked20 : adaptiveCoverCheck 3 cell20 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell20
    checked200 checked201 checked202 checked203

private theorem checked21 : adaptiveCoverCheck 3 cell21 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell21
    checked210 checked211 checked212 checked213

private theorem checked22 : adaptiveCoverCheck 3 cell22 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell22 (by decide +kernel)

private theorem checked23 : adaptiveCoverCheck 3 cell23 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell23 (by decide +kernel)

private theorem checked30 : adaptiveCoverCheck 3 cell30 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell30
    checked300 checked301 checked302 checked303

private theorem checked31 : adaptiveCoverCheck 3 cell31 = true := by
  exact adaptiveCoverCheck_succ_of_children 2 cell31
    checked310 checked311 checked312 checked313

private theorem checked32 : adaptiveCoverCheck 3 cell32 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell32 (by decide +kernel)

private theorem checked33 : adaptiveCoverCheck 3 cell33 = true := by
  exact adaptiveCoverCheck_true_of_rejected 3 cell33 (by decide +kernel)

private theorem checked0 : adaptiveCoverCheck 4 cell0 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell0
    checked00 checked01 checked02 checked03

private theorem checked1 : adaptiveCoverCheck 4 cell1 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell1
    checked10 checked11 checked12 checked13

private theorem checked2 : adaptiveCoverCheck 4 cell2 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell2
    checked20 checked21 checked22 checked23

private theorem checked3 : adaptiveCoverCheck 4 cell3 = true := by
  exact adaptiveCoverCheck_succ_of_children 3 cell3
    checked30 checked31 checked32 checked33

private theorem checkedRoot : adaptiveCoverCheck 5 cellRoot = true := by
  exact adaptiveCoverCheck_succ_of_children 4 cellRoot
    checked0 checked1 checked2 checked3

end CoverCertificate7a43bce112

theorem e24KC2PhiAboveLeaf1101101_c1_c0_c0_c0 :
    adaptiveCoverCheck 5 (childLL (childLL (childLL phiAboveCell11011011))) = true := by
  exact CoverCertificate7a43bce112.checkedRoot

end PartE
end GerverSofa

end

end

end
