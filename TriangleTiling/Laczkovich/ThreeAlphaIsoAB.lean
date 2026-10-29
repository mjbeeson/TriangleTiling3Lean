/-
`ABC` isosceles with base angles `α + β` (Section 11 of M. Beeson, *Triangle tiling: the case
3α + 2β = π*, arXiv 1206.2229v4): `theorem:isosceles1`, the corollary "Shape determines the tile"
(no TeX label; named `shapedeterminestile`), and `theorem:notprime3`.

Statements not yet checked with Beeson (written 2026-10-24 while he was away). `M` is the coloring
number of `theorem:coloring`; the scale factor `μ = λ/κ` of `definition:scaling` is `Λ` (`Lam D`):
`λ = Y/sin α` and `κ = a/sin α` are the circumdiameters of `ABC` and of the tile.
-/
import TriangleTiling.Laczkovich.ThreeAlphaIsoBeta

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles)
open Erdos634.BeesonColoring

variable {N : ℕ} (D : CongruentDissection N)

/-- `M = Λ/(1 + s)` and `N = Λ²/(1 - s²)`, for base angles `α + β`. -/
theorem isoab_core {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c)
    (hshape : D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + β)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : AtBOnAB D i₀)
    (hb : ε i₀ = 1) :
    ((∑ i, ε i : ℤ) : ℝ) = Lam D / (1 + a / c) ∧ (N : ℝ) = Lam D ^ 2 / (1 - (a / c) ^ 2) ∧
      D.target.oppLen 1 = Lam D * c * (a / c) ∧ D.target.oppLen 2 = Lam D * c ∧
      D.target.oppLen 0 = Lam D * c ∧ 0 < a / c ∧ a / c < 1 ∧ 0 < Lam D := by
  have hns := not_similar_of_alpha_beta D hrel hT hshape.1
  have hT' : TileAngles D α β γ := by
    obtain ⟨σ, h0, h1, h2, -⟩ := hT
    exact ⟨σ, h0, h1, h2⟩
  have hirr := (angles D hrel hT' hns).1
  have h := threeAlphaData_of_sides D hrel hT
  have hns3 := not_triple3 D hrel hT' hns
  obtain ⟨-, -, t0⟩ := corner_counts D hirr hrel h hns3 0 (p := 1) (q := 1)
    (by rw [hshape.1]; push_cast; ring)
  obtain ⟨-, -, t2⟩ := corner_counts D hirr hrel h hns3 2 (p := 1) (q := 1)
    (by rw [hshape.2.2]; push_cast; ring)
  obtain ⟨hα, hβ, hγ, hS, hc, ha, hb', ht0, ht1, -, -⟩ := model_facts D hrel hT
  have hcol := (coloring D hrel hT hns).2 (by rw [t0, t2]) ε i₀ hε hi₀ hb
  have hnp : ¬ ((D.target.angleAt 0 = α ∧ D.target.angleAt 2 = α) ∨
      (D.target.angleAt 0 = β ∧ D.target.angleAt 2 = β)) := by
    rw [hshape.1]; rintro (⟨e, -⟩ | ⟨e, -⟩) <;> linarith
  have hM := hcol.2 hnp
  have r := sines hα hβ hrel
  dsimp only at r
  obtain ⟨r1, -, -, -, -, -, -, -⟩ := r
  rw [div_eq_iff hS.ne'] at r1
  have s0 := target_side D hrel hT 0
  have s1 := target_side D hrel hT 1
  have s2 := target_side D hrel hT 2
  rw [hshape.1] at s0
  rw [hshape.2.1, r1] at s1
  rw [hshape.2.2] at s2
  set t := 2 * Real.cos (α + β)
  have hst : a / c = t := by rw [ha]; field_simp
  have hΛ : 0 < Lam D := div_pos (circumdiam_pos _) (circumdiam_pos _)
  have ar := (shapeareas D hrel hT).2.2.1 hshape
  rw [hst] at ar
  rw [hst]
  have hS' := hS.ne'
  have s0' : D.target.oppLen 0 = Lam D * c := by rw [s0]; field_simp
  have s1' : D.target.oppLen 1 = Lam D * c * t := by rw [s1]; field_simp
  have s2' : D.target.oppLen 2 = Lam D * c := by rw [s2]; field_simp
  have h1t : (0 : ℝ) < 1 - t ^ 2 := by nlinarith
  have eN : (N : ℝ) = Lam D ^ 2 / (1 - t ^ 2) := by
    rw [div_eq_iff (by positivity)] at ar
    rw [ar]; field_simp
  refine ⟨?_, eN, s1', s2', s0', ht0, ht1, hΛ⟩
  have key : ((∑ i, ε i : ℤ) : ℝ) * (c * ((2 - t) * (1 + t))) =
      Lam D / (1 + t) * (c * ((2 - t) * (1 + t))) := by
    rw [s0', s1', s2', ha, hb'] at hM
    have h1 : (1 : ℝ) + t ≠ 0 := by positivity
    have : Lam D / (1 + t) * (c * ((2 - t) * (1 + t))) = Lam D * c * (2 - t) := by
      field_simp
    rw [this]
    linear_combination hM
  have h2 : (0 : ℝ) < (2 - t) * (1 + t) := by
    have : 0 < 2 - t := by linarith
    positivity
  exact mul_right_cancel₀ (by positivity) key

/-- **Theorem `theorem:isosceles1`** (necessary condition). Suppose `ABC` is `N`-tiled by the tile
`(a, b, c)` with angles `(α, β, γ)`, `3α + 2β = π`, and `ABC` is isosceles with base angles
`α + β`. Let `s = a/c` and `M` the coloring number. Then `N / M² = (1 + s)/(1 - s)`; equivalently
`s = (N - M²)/(N + M²)`. The scale factor `μ` is `M (1 + s)`. -/
theorem isosceles1 {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c)
    (hshape : D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + β)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : AtBOnAB D i₀)
    (hb : ε i₀ = 1) :
    let s := a / c
    let M : ℤ := ∑ i, ε i
    (N : ℝ) / (M : ℝ) ^ 2 = (1 + s) / (1 - s) ∧ s = (N - (M : ℝ) ^ 2) / (N + (M : ℝ) ^ 2) ∧
      Lam D = M * (1 + s) := by
  intro s M
  obtain ⟨eM, eN, -, -, -, ht0, ht1, hΛ⟩ := isoab_core D hrel hT hshape hε hi₀ hb
  simp only [s]
  set t := a / c
  have h1p : (0 : ℝ) < 1 + t := by positivity
  have h1m : (0 : ℝ) < 1 - t := by linarith
  rw [show (1 : ℝ) - t ^ 2 = (1 - t) * (1 + t) by ring] at eN
  refine ⟨?_, ?_, ?_⟩
  · rw [eN, eM]; field_simp
  · rw [eN, eM, eq_div_iff (by positivity)]; field_simp; ring
  · rw [eM, div_mul_cancel₀ _ h1p.ne']

/-- **Corollary** (shape determines the tile; `M` and `N` determine each other; no TeX label). Let
`ABC` be isosceles with vertex angle `α` at `B` and base angles `α + β`, `N`-tiled by a tile with
angles `(α, β, γ)`. Let `Y` be the length of the base `AC` and `X` the length of the equal sides
`AB` and `BC`. Then `s = a/c = Y/X`, and `M² = N (1 - s)/(1 + s) = N (X - Y)/(X + Y)`. -/
theorem shapedeterminestile {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c)
    (hshape : D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + β)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : AtBOnAB D i₀)
    (hb : ε i₀ = 1) :
    let s := a / c
    let M : ℤ := ∑ i, ε i
    let X := D.target.oppLen 2
    let Y := D.target.oppLen 1
    s = Y / X ∧ (M : ℝ) ^ 2 = N * (1 - s) / (1 + s) ∧ N * (1 - s) / (1 + s) = N * (X - Y) / (X + Y) := by
  intro s M X Y
  obtain ⟨eM, eN, e1, e2, -, ht0, ht1, hΛ⟩ := isoab_core D hrel hT hshape hε hi₀ hb
  obtain ⟨-, -, -, -, hc, -, -, -, -, -, -⟩ := model_facts D hrel hT
  have hX : X = Lam D * c := e2
  have hY : Y = Lam D * c * (a / c) := e1
  simp only [s]
  set t := a / c
  have h1p : (0 : ℝ) < 1 + t := by positivity
  have h1m : (0 : ℝ) < 1 - t := by linarith
  rw [show (1 : ℝ) - t ^ 2 = (1 - t) * (1 + t) by ring] at eN
  refine ⟨?_, ?_, ?_⟩
  · rw [hX, hY]; field_simp
  · rw [eM, eN]; field_simp
  · rw [hX, hY]
    rw [show Lam D * c - Lam D * c * t = Lam D * c * (1 - t) by ring,
      show Lam D * c + Lam D * c * t = Lam D * c * (1 + t) by ring]
    field_simp

/-- **Theorem `theorem:notprime3`.** Suppose `ABC` is isosceles with base angles `α + β` and is
`N`-tiled (by a tile with angles `(α, β, γ)`, `3α + 2β = π`). Then `N` is not prime. -/
theorem notprime3 {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hshape : TgtAngles D (α + β) α (α + β)) : ¬ N.Prime := by
  intro hN
  obtain ⟨σ, h0, h1, h2⟩ := hshape
  set D₁ := relabelTarget D σ
  have hT₁ : TileSides D₁ α β γ a b c := hT
  have e0 : D₁.target.angleAt 0 = α + β := by rw [relabel_angleAt]; exact h0
  have e1 : D₁.target.angleAt 1 = α := by rw [relabel_angleAt]; exact h1
  have e2 : D₁.target.angleAt 2 = α + β := by rw [relabel_angleAt]; exact h2
  have hns₁ := not_similar_of_alpha_beta D₁ hrel hT₁ e0
  have hT' : TileAngles D₁ α β γ := by
    obtain ⟨τ, g0, g1, g2, -⟩ := hT₁
    exact ⟨τ, g0, g1, g2⟩
  have hirr := (angles D₁ hrel hT' hns₁).1
  have h := threeAlphaData_of_sides D₁ hrel hT₁
  have hns3 := not_triple3 D₁ hrel hT' hns₁
  obtain ⟨-, -, t1⟩ := corner_counts D₁ hirr hrel h hns3 1 (p := 1) (q := 0)
    (by rw [e1]; push_cast; ring)
  obtain ⟨i₀, hi₀⟩ : ∃ i, TileAt D₁ 1 i := by
    classical
    have : 0 < ({i | TileAt D₁ 1 i} : Finset (Fin N)).card := by
      have : tilesAt D₁ 1 = 1 := t1
      unfold tilesAt at this; omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp this
    exact ⟨i, by simpa using hi⟩
  obtain ⟨ε, hε, hεi⟩ := signedtiles D₁ hrel hT' hns₁ hi₀
  have hAB := atB_onAB D₁ t1 hi₀
  have te := isosceles1 D₁ hrel hT₁ ⟨e0, e1, e2⟩ hε hAB hεi
  dsimp only at te
  obtain ⟨-, hs, hΛ⟩ := te
  obtain ⟨eM, -, eY, -, -, ht0, ht1, hΛ0⟩ := isoab_core D₁ hrel hT₁ ⟨e0, e1, e2⟩ hε hAB hεi
  set M : ℤ := ∑ i, ε i
  have hMpos : (0 : ℝ) < M := by rw [eM]; positivity
  -- `s = m/k` in lowest terms.
  obtain ⟨⟨q, hq⟩, -, -⟩ := rationaltile D₁ hrel hT₁ hns₁
  have hq0 : 0 < q := by have : (0 : ℝ) < q := by rw [← hq]; exact ht0
                         exact_mod_cast this
  have hq1 : q < 1 := by have : (q : ℝ) < 1 := by rw [← hq]; exact ht1
                         exact_mod_cast this
  set m : ℤ := q.num
  set k : ℤ := (q.den : ℤ)
  have hm : 0 < m := Rat.num_pos.mpr hq0
  have hk : 0 < k := by simp only [k]; exact_mod_cast q.den_pos
  have hmk : m < k := Rat.num_lt_denom_iff.mpr hq1
  have hcop : IsCoprime m k := by rw [Int.isCoprime_iff_gcd_eq_one]; exact q.reduced
  have hqmk : (q : ℝ) = m / k := by rw [Rat.cast_def]; simp [m, k]
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  -- `(N + M²) m = (N - M²) k`.
  have h1 : (((N : ℤ) + M ^ 2) * m : ℤ) = ((N : ℤ) - M ^ 2) * k := by
    have : ((((N : ℤ) + M ^ 2) * m : ℤ) : ℝ) = ((((N : ℤ) - M ^ 2) * k : ℤ) : ℝ) := by
      push_cast
      rw [hq, hqmk] at hs
      have hd : (N : ℝ) + (M : ℝ) ^ 2 ≠ 0 := by positivity
      rw [eq_div_iff hd, div_mul_eq_mul_div, div_eq_iff hkR.ne'] at hs
      linarith
    exact_mod_cast this
  -- The base: `Y = p a + q b + r c`, `r ≥ 1`.
  obtain ⟨p', q', r', hr, hY⟩ := side_decomp D₁ hirr hrel h hns3 2
  have hYo : dist (D₁.target.pts 2) (D₁.target.pts (2 + 1)) = D₁.target.oppLen 1 := rfl
  rw [hYo, eY] at hY
  obtain ⟨-, -, -, -, hc, ha, hb', -, -, -, -⟩ := model_facts D₁ hrel hT₁
  have hst : a / c = 2 * Real.cos (α + β) := by rw [ha]; field_simp
  set t := 2 * Real.cos (α + β)
  have htq : t = m / k := by rw [← hst, hq, hqmk]
  -- In units of `τ = c/k²`: `M (k + m) m = p mk + q (k² - m²) + r k²`.
  have eA : a = (m / k) * c := by rw [ha, htq]
  have eB : b = (1 - (m / k) ^ 2) * c := by rw [hb', htq]
  have eL : Lam D₁ = M * (1 + m / k) := by rw [hΛ, hst, htq]
  rw [eL, hst, htq, eA, eB] at hY
  have h2 : M * (k + m) * m = (p' : ℤ) * (m * k) + q' * (k ^ 2 - m ^ 2) + r' * k ^ 2 := by
    have : ((M * (k + m) * m : ℤ) : ℝ) =
        (((p' : ℤ) * (m * k) + q' * (k ^ 2 - m ^ 2) + r' * k ^ 2 : ℤ) : ℝ) := by
      push_cast
      have hk0 : (k : ℝ) ≠ 0 := hkR.ne'
      field_simp at hY
      linear_combination hY
    exact_mod_cast this
  exact notprime3_arith hN (by exact_mod_cast hMpos) hm hmk hcop (by positivity) (by positivity)
    (by exact_mod_cast hr) h1 h2

end TriangleTiling.ThreeAlpha
