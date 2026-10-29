# TriangleTiling3Lean

A Lean 4 formalization of M. Beeson, *Triangle tiling: the case 3α + 2β = π*
(arXiv 1206.2229).

An *N-tiling* of a triangle ABC cuts it into N triangles congruent to one tile (reflections
allowed). The paper studies tilings by a tile with angles (α, β, γ) where 3α + 2β = π: the
possible shapes of ABC, the tiling equations, which N occur, and constructions of tilings.
Every theorem, lemma and corollary of the paper has a Lean counterpart here, named after its
label, whose proof is checked by the Lean kernel using only the standard axioms (`propext`,
`Classical.choice`, `Quot.sound`), with no `sorry` and no `native_decide`. The one exception is
the table of possible tilings for N ≤ 108 (`lemma:july29`), which rests on a computer search.

The docstring of each Lean theorem states the result in words and names the corresponding result
of the paper. In the table, † marks results in the separately built library
`TriangleTilingLaczkovich` (see below). All names are in the namespace `TriangleTiling.ThreeAlpha`.

| Result of the paper (TeX label) | Lean name |
|---|---|
| Lemma `lemma:angles` | `angles` † |
| Lemma `lemma:singamma` | `singamma` |
| Lemma `lemma:anglesOK` | `anglesOK` |
| Lemma `lemma:gsquare` | `gsquare` |
| Lemma `lemma:gammagreaterpiover2` | `gammagreaterpiover2` |
| Lemma `lemma:nogamma` | `nogamma` † |
| Lemma `lemma:pigeonhole` | `pigeonhole` |
| Lemma `lemma:twocs` | `twocs` |
| Lemma `lemma:cminusb` | `cminusb` |
| Lemma `lemma:standardvertices` | `standardvertices` † |
| Lemma `lemma:shapes` | `shapes` † |
| Lemma `lemma:signedtiles` | `signedtiles` † |
| Theorem `theorem:coloring` | `coloring` † |
| Lemma `lemma:Mnotzero` | `Mnotzero` † |
| Lemma `lemma:noboundarylink` | `noboundarylink` |
| Lemma `lemma:apropagation` | `apropagation` † |
| Lemma `lemma:incommensurable` | `incommensurable` † |
| Lemma `lemma:deltacoords` | `deltacoords` |
| Lemma `lemma:deltadirections` | `deltadirections` † |
| Lemma `lemma:Phitile` | `Phitile` † |
| Lemma `lemma:Phiproperties` | `Phiproperties` |
| Lemma `lemma:Phicancellation` | `Phicancellation` |
| Theorem `theorem:Mdef` | `Mdef` † |
| Lemma `lemma:Phisigns` | `Phisigns` † |
| Lemma `lemma:sines` | `sines` |
| Theorem `theorem:M1M2` | `M1M2` † |
| Lemma `lemma:relationlattice` | `relationlattice` |
| Lemma `lemma:shapeareas` | `shapeareas` |
| Lemma `lemma:kappa` | `kappa` † |
| Theorem `theorem:rationaliso` | `rationaliso` † |
| Theorem `theorem:shape45` | `shape45` † |
| Theorem `theorem:arelation` | `arelation` † |
| Theorem `theorem:tqsquare` | `tqsquare` † |
| Theorem `theorem:tqrational` | `tqrational` † |
| Corollary `corollary:tqparameters` | `tqparameters` † |
| Theorem `theorem:rationaltile` | `rationaltile` † |
| Lemma `lemma:connectedcomponents` | `connectedcomponents` |
| Lemma `lemma:Hcomponents` | `Hcomponents` |
| Lemma `lemma:dmatrix` | `dmatrix` † |
| Lemma `lemma:52` | `lemma52` † |
| Theorem `theorem:tilingequation` | `tilingequation` † |
| Lemma `lemma:XYZ` | `XYZ` † |
| Lemma `lemma:n<K` | `nltK` † |
| Lemma `lemma:X=M(b+c)` | `XeqMbc` † |
| Lemma `lemma:jmk` | `jmk` † |
| Lemma `lemma:congruences` | `congruences` † |
| Corollary `corollary:nokt` | `nokt` † |
| Lemma `lemma:twocsapplies` | `twocsapplies` † |
| Lemma `lemma:No14` | `No14` † |
| Lemma `lemma:No17` | `No17` † |
| Lemma `lemma:No7` | `No7` † |
| Lemma `lemma:No23` | `No23` † |
| Lemma `lemma:Nolessthan28` | `Nolessthan28` † |
| Theorem `theorem:triquadraticexistence` | `triquadraticexistence` † |
| Theorem `theorem:jshape` | `jshape` † |
| Lemma `lemma:6902` | `lemma6902` † |
| Lemma `lemma:normtheorem` | `normtheorem` † |
| Lemma `lemma:tqprime` | `tqprime` † |
| Lemma `lemma:primeimpliesjone` | `primeimpliesjone` |
| Lemma `lemma:singamma2` | `singamma2` |
| Theorem `theorem:secondtilingequation` | `secondtilingequation` † |
| Lemma `lemma:Msquared` | `Msquared` † |
| Lemma `lemma:scaling` | `scaling` † |
| Theorem `theorem:existence2` | `existence2` † |
| Theorem `theorem:secondcasesolution` | `secondcasesolution` † |
| Theorem `theorem:notprime2` | `notprime2` † |
| Theorem `theorem:solvingsecond` | `solvingsecond` † |
| Theorem `theorem:tilingequation3` | `tilingequation3` † |
| Theorem `theorem:notprime4` | `notprime4` † |
| Theorem `theorem:isoscelesbetaexistence` | `isoscelesbetaexistence` † |
| Lemma `lemma:XY` | `XY` † |
| Theorem `theorem:isosceles1` | `isosceles1` † |
| Theorem `theorem:notprime3` | `notprime3` † |
| Theorem `theorem:Lconstruction` | `Lconstruction` † |
| Lemma `lemma:complementary` | `complementary` |
| Theorem `theorem:isoscelesconstruction` | `isoscelesconstruction` † |
| Corollary `corollary:isoscelesall` | `isoscelesall` † |
| Corollary `corollary:existence2case2` | `existence2case2` † |
| Corollary `corollary:secondshapeall` | `secondshapeall` † |
| Lemma `lemma:mu` | `mu` † |
| Lemma `lemma:halfintegermu` | `halfintegermu` † |
| Theorem `theorem:N45` | `N45` † |
| Corollary `lemma:july29` | not formalized (computer search) |
| Theorem `theorem:tilingequation4` | `tilingequation4` † |
| Theorem `theorem:notprime5` | `notprime5` † |
| Corollary `corollary:isoscelesalphaall` | `isoscelesalphaall` † |
| Theorem `theorem:notprime` | `notprime` † |

The repository also contains the formalization of M. Beeson, *Tilings of an isosceles triangle*
(namespace `TriangleTiling`), which this one builds on; see
[IsoscelesTilingsLean](https://github.com/mjbeeson/IsoscelesTilingsLean).

## Dependencies

- Lean `v4.30.0` and Mathlib `v4.30.0`.
- V. Bonfioli, *Formalizing triangle tiling in Lean*
  ([ElVec1o/formalizing-triangle-tiling-in-lean](https://github.com/ElVec1o/formalizing-triangle-tiling-in-lean),
  pinned to commit `d728130`). It provides the definition of a congruent dissection, Laczkovich's
  classification for congruent tiles (Laczkovich 1995, Thms 4.1, 5.1, 5.3; 2012, Thm 3.3), the
  tilings used in the constructions (Theorems `triquadraticexistence`, `existence2`,
  `secondcasesolution` (converse), `isoscelesbetaexistence`, `Lconstruction`,
  `isoscelesconstruction`, Corollary `existence2case2`), and tools for gluing tilings. These parts
  are marked unaudited in Bonfioli's library; the files here state the results as printed in the
  paper and derive the angles, side lengths and coloring numbers of the constructed tilings.

## Building

Install [elan](https://github.com/leanprover/elan), then:

```bash
lake exe cache get
lake build
```

This builds the library `TriangleTiling`, which is everything except the results marked †.
Continuous integration builds it on every push.

The results marked † use Laczkovich's classification or Bonfioli's constructions and are in the
separate library `TriangleTilingLaczkovich`. Its dependencies are about a thousand modules of
Bonfioli's library, which take several hours to build and need up to 9 GB of memory per Lean
process. To build it one module at a time on a machine with 16 GB:

```bash
LAKE_RSS_LIMIT_GB=13 python3 scripts/lakeserial.py . build TriangleTilingLaczkovich
```

To check the axioms of a theorem, for example:

```lean
import TriangleTilingLaczkovich
#print axioms TriangleTiling.ThreeAlpha.N45
```

## Authorship and license

The mathematics is M. Beeson's. The Lean code was written with Claude (Anthropic), under
Beeson's direction; its proofs are checked by the Lean kernel.

The Lean code is licensed under the Apache License 2.0 (see `LICENSE`).
`scripts/lakeserial.py` is copied from V. Bonfioli's repository
[erdos634_primes_and_N200](https://github.com/ElVec1o/erdos634_primes_and_N200) under the MIT
license.
