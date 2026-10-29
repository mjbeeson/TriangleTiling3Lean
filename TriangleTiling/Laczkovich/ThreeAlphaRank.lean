/-
`corollary:ranktwo` of M. Beeson, *Triangle tiling: the case 3α + 2β = π*, arXiv 1206.2229v4:
`theorem:rationaltile` with `lemma:relationlattice`.
-/
import TriangleTiling.Laczkovich.ThreeAlphaTriquadratic
import TriangleTiling.ThreeAlpha.RelLattice

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional

variable {N : ℕ} (D : CongruentDissection N)

/-- **Corollary `corollary:ranktwo`.** Under the hypotheses of `theorem:rationaltile`,
`rank L = 2`; that is, `ℤa + ℤb + ℤc` is infinite cyclic. -/
theorem ranktwo {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D) :
    Module.finrank ℤ (relLattice a b c) = 2 := by
  obtain ⟨-, -, -, -, hc, ha, hb, ht0, ht1, -, -⟩ := model_facts D hrel hT
  have ha' : 0 < a := by rw [ha]; positivity
  have hb' : 0 < b := by
    rw [hb]
    have : 0 < 1 - (2 * Real.cos (α + β)) ^ 2 := by nlinarith
    positivity
  exact ((relationlattice ha' hb' hc).2.2.1).mpr (rationaltile D hrel hT hns)

end TriangleTiling.ThreeAlpha
