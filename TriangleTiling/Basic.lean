/-
Smoke test for the link to Bonfioli's library.

`Erdos634.Dissection` holds his core geometric definitions
(`Plane`, `Tri`, `Tri.carrier`, `Dissection N`) in namespace `Erdos634.Geometry`.
Whether we reuse these or write our own is still to be decided.
-/
import Erdos634.Dissection

namespace TriangleTiling

open Erdos634.Geometry

#check Plane
#check Tri
#check @Dissection

end TriangleTiling
