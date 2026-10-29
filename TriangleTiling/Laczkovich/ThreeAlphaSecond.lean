/-
The shape `(2α, α, 2β)` (Section 9 of M. Beeson, *Triangle tiling: the case 3α + 2β = π*,
arXiv 1206.2229v4): `theorem:secondtilingequation` and `theorem:notprime2`.

Statements not yet checked with Beeson (written 2026-10-24 while he was away).
-/
import TriangleTiling.Laczkovich.ThreeAlphaTilingEq
import TriangleTiling.ThreeAlpha.NotPrimeArith

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles)
open Erdos634.BeesonColoring

variable {N : ℕ} (D : CongruentDissection N)

/-- **Theorem `theorem:secondtilingequation`.** Let `3α + 2β = π`, let `ABC` have angles
`(2α, α, 2β)` (at `A, B, C`), and suppose `ABC` is `N`-tiled by a tile with angles `(α, β, γ)`. Let
the tiles be colored alternately black and white with a black tile at `B`, and let `M` be the
number of black tiles minus the number of white tiles. Let `s = a/c`. Then `s` is rational and
`N / M² = (2 - s²)(3 - s²) / ((1 - s)²(2 + s)²)`.

`ABC` not similar to the tile is a hypothesis (the paper's standing assumption): for `α = π/7` the
angles `(2α, α, 2β)` are those of the tile. -/
theorem secondtilingequation {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D)
    (hshape : D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = 2 * β)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : TileAt D 1 i₀)
    (hb : ε i₀ = 1) :
    let s := a / c
    let M : ℤ := ∑ i, ε i
    (∃ q : ℚ, s = q) ∧
      (N : ℝ) / (M : ℝ) ^ 2 = (2 - s ^ 2) * (3 - s ^ 2) / ((1 - s) ^ 2 * (2 + s) ^ 2) := by
  intro s M
  have hT' : TileAngles D α β γ := by
    obtain ⟨σ, h0, h1, h2, -⟩ := hT
    exact ⟨σ, h0, h1, h2⟩
  have hirr := (angles D hrel hT' hns).1
  have h := threeAlphaData_of_sides D hrel hT
  have hns3 := not_triple3 D hrel hT' hns
  obtain ⟨-, -, t0⟩ := corner_counts D hirr hrel h hns3 0 (p := 2) (q := 0)
    (by rw [hshape.1]; push_cast; ring)
  obtain ⟨-, -, t1⟩ := corner_counts D hirr hrel h hns3 1 (p := 1) (q := 0)
    (by rw [hshape.2.1]; push_cast; ring)
  obtain ⟨-, -, t2⟩ := corner_counts D hirr hrel h hns3 2 (p := 0) (q := 2)
    (by rw [hshape.2.2]; push_cast; ring)
  obtain ⟨hα, hβ, hγ, hS, hc, ha, hb', ht0, ht1, -, -⟩ := model_facts D hrel hT
  have hcol := (coloring D hrel hT hns).2 (by rw [t0, t2]) ε i₀ hε
    (atB_onAB D t1 hi₀) hb
  have hnp : ¬ ((D.target.angleAt 0 = α ∧ D.target.angleAt 2 = α) ∨
      (D.target.angleAt 0 = β ∧ D.target.angleAt 2 = β)) := by
    rw [hshape.1, hshape.2.2]
    rintro (⟨e, -⟩ | ⟨-, e⟩) <;> linarith
  have hM := hcol.2 hnp
  have r := sines hα hβ hrel
  dsimp only at r
  obtain ⟨r1, -, -, -, r5, -, -, r8⟩ := r
  rw [div_eq_iff hS.ne'] at r1 r5 r8
  have s0 := target_side D hrel hT 0
  have s1 := target_side D hrel hT 1
  have s2 := target_side D hrel hT 2
  rw [hshape.1, r5] at s0
  rw [hshape.2.1, r1] at s1
  rw [hshape.2.2, r8] at s2
  set t := 2 * Real.cos (α + β)
  have hst : s = t := by simp only [s]; rw [ha]; field_simp
  have hΛ : 0 < Lam D := div_pos (circumdiam_pos _) (circumdiam_pos _)
  have ar := (shapeareas D hrel hT).2.2.2.2 hshape
  rw [show a / c = t by rw [ha]; field_simp] at ar
  refine ⟨?_, ?_⟩
  · obtain ⟨⟨q, hq⟩, -, -⟩ := rationaltile D hrel hT hns
    exact ⟨q, hq⟩
  have hS' := hS.ne'
  -- `M = Λ t (1 - t)(2 + t)`.
  have hMv : (M : ℝ) = Lam D * t * (1 - t) * (2 + t) := by
    have h2 : (0 : ℝ) < (2 - t) * (1 + t) := by
      have : 0 < 2 - t := by linarith
      positivity
    have s0' : D.target.oppLen 0 = Lam D * c * (t * (2 - t ^ 2)) := by rw [s0]; field_simp
    have s1' : D.target.oppLen 1 = Lam D * c * t := by rw [s1]; field_simp
    have s2' : D.target.oppLen 2 = Lam D * c * (t * (1 - t ^ 2) * (3 - t ^ 2)) := by
      rw [s2]; field_simp
    have key : (M : ℝ) * (c * ((2 - t) * (1 + t))) = Lam D * t * (1 - t) * (2 + t) *
        (c * ((2 - t) * (1 + t))) := by
      have := hM
      rw [s0', s1', s2', ha, hb'] at this
      linear_combination this
    exact mul_right_cancel₀ (by positivity) key
  have eN : (N : ℝ) = Lam D ^ 2 * (t ^ 2 * (2 - t ^ 2) * (3 - t ^ 2)) := by
    rw [← ar]; field_simp
  rw [hst, hMv, eN]
  have h1t : (1 : ℝ) - t ≠ 0 := ne_of_gt (by linarith)
  have h2t : (2 : ℝ) + t ≠ 0 := ne_of_gt (by linarith)
  field_simp

/-- **Theorem `theorem:notprime2`.** Suppose `3α + 2β = π`. Let `ABC` with angles `(2α, α, 2β)` be
`N`-tiled by a tile with angles `(α, β, γ)`, not similar to `ABC`. Then `N` is not prime. -/
theorem notprime2 {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D) (hshape : TgtAngles D (2 * α) α (2 * β)) :
    ¬ N.Prime := by
  intro hN
  obtain ⟨σ, h0, h1, h2⟩ := hshape
  set D₁ := relabelTarget D σ
  have hns₁ : ¬ SimilarTM D₁ := fun h => hns (similar_of_relabel D σ h)
  have hT₁ : TileSides D₁ α β γ a b c := hT
  have e0 : D₁.target.angleAt 0 = 2 * α := by rw [relabel_angleAt]; exact h0
  have e1 : D₁.target.angleAt 1 = α := by rw [relabel_angleAt]; exact h1
  have e2 : D₁.target.angleAt 2 = 2 * β := by rw [relabel_angleAt]; exact h2
  have hT' : TileAngles D₁ α β γ := by
    obtain ⟨τ, g0, g1, g2, -⟩ := hT₁
    exact ⟨τ, g0, g1, g2⟩
  have hirr := (angles D₁ hrel hT' hns₁).1
  have h := threeAlphaData_of_sides D₁ hrel hT₁
  have hns3 := not_triple3 D₁ hrel hT' hns₁
  obtain ⟨-, -, t1⟩ := corner_counts D₁ hirr hrel h hns3 1 (p := 1) (q := 0)
    (by rw [e1]; push_cast; ring)
  -- A tile at `B`, colored black.
  obtain ⟨i₀, hi₀⟩ : ∃ i, TileAt D₁ 1 i := by
    classical
    have : 0 < ({i | TileAt D₁ 1 i} : Finset (Fin N)).card := by
      have : tilesAt D₁ 1 = 1 := t1
      unfold tilesAt at this; omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp this
    exact ⟨i, by simpa using hi⟩
  obtain ⟨ε, hε, hεi⟩ := signedtiles D₁ hrel hT' hns₁ hi₀
  have te := secondtilingequation D₁ hrel hT₁ hns₁ ⟨e0, e1, e2⟩ hε hi₀ hεi
  dsimp only at te
  obtain ⟨⟨q, hq⟩, hNM⟩ := te
  have hM0 := Mnotzero D₁ hrel hT' hns₁ hε
  set M : ℤ := ∑ i, ε i
  -- `s = m/k` in lowest terms, `0 < m < k`.
  obtain ⟨-, -, -, -, hc, ha, -, ht0, ht1, -, -⟩ := model_facts D₁ hrel hT₁
  have hs01 : 0 < (q : ℝ) ∧ (q : ℝ) < 1 := by
    rw [← hq, show a / c = 2 * Real.cos (α + β) by rw [ha]; field_simp]; exact ⟨ht0, ht1⟩
  have hq0 : 0 < q := by exact_mod_cast hs01.1
  have hq1 : q < 1 := by exact_mod_cast hs01.2
  set m : ℤ := q.num
  set k : ℤ := (q.den : ℤ)
  have hm : 0 < m := Rat.num_pos.mpr hq0
  have hk : 0 < k := by simp only [k]; exact_mod_cast q.den_pos
  have hmk : m < k := by
    exact Rat.num_lt_denom_iff.mpr hq1
  have hcop : IsCoprime m k := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact q.reduced
  have hqmk : (q : ℝ) = m / k := by rw [Rat.cast_def]; simp [m, k]
  rw [hq, hqmk] at hNM
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM0
  have hkm : (k : ℝ) - m ≠ 0 := by
    have : (m : ℝ) < k := by exact_mod_cast hmk
    linarith
  have h2km : 2 * (k : ℝ) + m ≠ 0 := by
    have : (0 : ℝ) < m := by exact_mod_cast hm
    have : (0 : ℝ) < k := by exact_mod_cast hk
    linarith
  have hN' : (N : ℝ) = (M : ℝ) ^ 2 * ((2 - ((m : ℝ) / k) ^ 2) * (3 - ((m : ℝ) / k) ^ 2) /
      ((1 - (m : ℝ) / k) ^ 2 * (2 + (m : ℝ) / k) ^ 2)) := by
    rw [← hNM]; field_simp
  have heqR : ((N : ℤ) : ℝ) * (((k - m) * (2 * k + m) : ℤ) : ℝ) ^ 2 =
      ((M ^ 2 * ((2 * k ^ 2 - m ^ 2) * (3 * k ^ 2 - m ^ 2)) : ℤ) : ℝ) := by
    push_cast
    rw [hN']
    field_simp
  have heqZ : (N : ℤ) * ((k - m) * (2 * k + m)) ^ 2 =
      M ^ 2 * ((2 * k ^ 2 - m ^ 2) * (3 * k ^ 2 - m ^ 2)) := by exact_mod_cast heqR
  have h2 := notprime2_arith hN hM0 hm hmk hcop heqZ
  have h3 := three_le_N D₁ hirr hrel h hns3
  omega


/-- The only-if direction of **Theorem `theorem:secondcasesolution`** (the converse is a
construction, not formalized). Let `3α + 2β = π`, and suppose `ABC` with angles `(2α, α, 2β)` is
`N`-tiled by the tile `(α, β, γ)`, not similar to it. Then `s = a/c` is rational. If the tile has
integer sides `(a, b, c)` (`lemma:scaling`; no common divisor is not needed), then `c` divides `a²`
and `N = (b + c)(b + 2c)(M/(b + c - a))²`. -/
theorem secondcasesolution_onlyif {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D)
    (hshape : D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = 2 * β)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : TileAt D 1 i₀)
    (hb : ε i₀ = 1) :
    (∃ q : ℚ, a / c = q) ∧
      ∀ A B C : ℤ, a = A → b = B → c = C →
        C ∣ A ^ 2 ∧ (N : ℝ) = (b + c) * (b + 2 * c) * ((∑ i, ε i : ℤ) / (b + c - a)) ^ 2 := by
  obtain ⟨hq, heq⟩ := secondtilingequation D hrel hT hns hshape hε hi₀ hb
  refine ⟨hq, fun A B C hA hB hC => ?_⟩
  obtain ⟨-, -, -, -, hc, ha, hb', ht0, ht1, -⟩ := model_facts D hrel hT
  have hT' : TileAngles D α β γ := by
    obtain ⟨σ, h0, h1, h2, -⟩ := hT
    exact ⟨σ, h0, h1, h2⟩
  have hM := Mnotzero D hrel hT' hns hε
  set t := 2 * Real.cos (α + β)
  refine ⟨?_, ?_⟩
  · -- `a² = c (c - b)`
    have h : (A : ℝ) ^ 2 = C * (C - B) := by rw [← hA, ← hB, ← hC, ha, hb']; ring
    exact ⟨C - B, by exact_mod_cast h⟩
  · have hs : a / c = t := by rw [ha]; field_simp
    simp only [hs] at heq
    have hMr : ((∑ i, ε i : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hM
    have h1 : (1 - t) ≠ 0 := by linarith
    have h2 : (2 + t) ≠ 0 := by linarith
    have h3 : b + c - a ≠ 0 := by
      rw [ha, hb']
      rw [show (1 - (2 * Real.cos (α + β)) ^ 2) * c + c - 2 * Real.cos (α + β) * c
        = (1 - t) * (2 + t) * c by ring]
      exact mul_ne_zero (mul_ne_zero h1 h2) hc.ne'
    rw [div_eq_iff (pow_ne_zero 2 hMr)] at heq
    rw [heq, ha, hb', show (1 - t ^ 2) * c + c - t * c = (1 - t) * (2 + t) * c by ring]
    have hc0 := hc.ne'
    field_simp
    ring

end TriangleTiling.ThreeAlpha
