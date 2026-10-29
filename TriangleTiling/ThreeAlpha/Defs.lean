/-
Vocabulary for M. Beeson, *Triangle tiling: the case 3α + 2β = π* (arXiv 1206.2229v4).

The tiled triangle `ABC` is `D.target`, with `A`, `B`, `C` its vertices `0`, `1`, `2`; so
`X = |BC|`, `Y = |AC|`, `Z = |AB|` are `D.target.oppLen 0`, `1`, `2`. A coloring of the tiles
(`lemma:signedtiles`) is Bonfioli's `ProperColouring`: signs `±1`, opposite on any two tiles
sharing a segment of positive length on their boundaries. Its sum is the paper's `M`, the number
of black tiles minus the number of white tiles.
-/
import Erdos634.Draft.BeesonColoringLemma12

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry

variable {N : ℕ} (D : CongruentDissection N)

/-- The tile has angles `(α, β, γ)` with opposite sides `(a, b, c)`. -/
def TileSides (α β γ a b c : ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin 3),
    D.model.angleAt (σ 0) = α ∧ D.model.angleAt (σ 1) = β ∧ D.model.angleAt (σ 2) = γ ∧
    D.model.oppLen (σ 0) = a ∧ D.model.oppLen (σ 1) = b ∧ D.model.oppLen (σ 2) = c

/-- Tile `i` has a vertex at vertex `k` of `ABC`. -/
def TileAt (k : Fin 3) (i : Fin N) : Prop :=
  ∃ l : Fin 3, (D.tile i).pts l = D.target.pts k

/-- The number of tiles with a vertex at vertex `k` of `ABC`. -/
noncomputable def tilesAt (k : Fin 3) : ℕ :=
  open Classical in ({i | TileAt D k i} : Finset (Fin N)).card

/-- The number of tiles having an angle equal to `x` at vertex `k` of `ABC`. -/
noncomputable def anglesAt (k : Fin 3) (x : ℝ) : ℕ :=
  open Classical in
  ({i | ∃ l, (D.tile i).pts l = D.target.pts k ∧ (D.tile i).angleAt l = x} : Finset (Fin N)).card

/-- Tile `i` is at `B` and has an edge on `AB`. -/
def AtBOnAB (i : Fin N) : Prop :=
  ∃ l l' : Fin 3, l ≠ l' ∧ (D.tile i).pts l = D.target.pts 1 ∧
    (D.tile i).pts l' ∈ segment ℝ (D.target.pts 0) (D.target.pts 1)

/-! ### The functions `Φ₁`, `Φ₂` (`definition:Phi`) -/

/-- The base direction: the direction of `AB`, traversing `∂ABC` counterclockwise. -/
noncomputable def baseDir : Real.Angle := (D.target.leftUnit 0).angle

/-- **Definition `definition:Phi`**, `Φ₁`: for a direction `θ = θ₀ + nδ + επ` (`ε ∈ {0, 1}`),
`Φ₁(θ) = (-1)^ε`. Other directions get `0`. -/
noncomputable def Phi1 (δ : ℝ) (θ₀ θ : Real.Angle) : ℝ :=
  open Classical in
  if ∃ n : ℤ, θ = θ₀ + ((n * δ : ℝ) : Real.Angle) then 1
  else if ∃ n : ℤ, θ = θ₀ + ((n * δ + Real.pi : ℝ) : Real.Angle) then -1
  else 0

/-- **Definition `definition:Phi`**, `Φ₂`: for a direction `θ = θ₀ + nδ + επ` (`ε ∈ {0, 1}`),
`Φ₂(θ) = (-1)^(n+ε)`. Other directions get `0`. -/
noncomputable def Phi2 (δ : ℝ) (θ₀ θ : Real.Angle) : ℝ :=
  open Classical in
  if h : ∃ n : ℤ, θ = θ₀ + ((n * δ : ℝ) : Real.Angle) then (h.choose.negOnePow : ℤ)
  else if h : ∃ n : ℤ, θ = θ₀ + ((n * δ + Real.pi : ℝ) : Real.Angle) then
    -((h.choose.negOnePow : ℤ) : ℝ)
  else 0

/-- **Definition `definition:Phi`**, `Φ(R)`: the sum of `ℓ_j Φ(θ_j)` over the edges of the
triangle `R`, traversed counterclockwise, of lengths `ℓ_j` and directions `θ_j`. -/
noncomputable def PhiR (Φ : Real.Angle → ℝ) (R : Tri) : ℝ := R.flux fun d => Φ d.angle

/-! ### Circumdiameters and rational tiles (Sections 5–6) -/

/-- The circumdiameter of a triangle, `|BC| / sin A` (the same for every vertex, by the law of
sines). -/
noncomputable def circumdiam (T : Tri) : ℝ := T.oppLen 0 / Real.sin (T.angleAt 0)

/-- `Λ`: the ratio of the circumdiameter of `ABC` to that of the tile. -/
noncomputable def Lam : ℝ := circumdiam D.target / circumdiam D.model

/-- The tile `(a, b, c)` is *rational*: `a/c`, `b/c` and `a/b` are all rational. -/
def RationalTile (a b c : ℝ) : Prop :=
  (∃ q : ℚ, a / c = q) ∧ (∃ q : ℚ, b / c = q) ∧ (∃ q : ℚ, a / b = q)

end TriangleTiling.ThreeAlpha
