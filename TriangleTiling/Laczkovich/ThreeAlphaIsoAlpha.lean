/-
`ABC` isosceles with base angles `α` (M. Beeson, *Triangle tiling: the case 3α + 2β = π*,
arXiv 1206.2229v4): `theorem:tilingequation4`, `theorem:notprime5`, and the summary theorem of the last section
(`theorem:notprime`).

Statements not yet checked with Beeson (written 2026-10-24 while he was away). `M` is the coloring
number of `theorem:coloring` (a tile at `B` with an edge on `AB` black).
-/
import TriangleTiling.Laczkovich.ThreeAlphaIsoAB

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles)
open Erdos634.BeesonColoring

variable {N : ℕ} (D : CongruentDissection N)

/-- The coloring equation, `N` and the leg `X = BC` in terms of `Λ`, `c` and `t = s`, for base
angles `α`. -/
theorem isoalpha_core {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D)
    (hshape : D.target.angleAt 0 = α ∧ D.target.angleAt 1 = α + 2 * β ∧ D.target.angleAt 2 = α)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : AtBOnAB D i₀)
    (hb : ε i₀ = 1) :
    ((∑ i, ε i : ℤ) : ℝ) * (1 + a / c) = Lam D * (a / c) * (2 + a / c) ∧
      (N : ℝ) * (1 - (a / c) ^ 2) = Lam D ^ 2 * (a / c) ^ 2 * (2 - (a / c) ^ 2) ∧
      D.target.oppLen 0 = Lam D * c * (a / c) ∧ 0 < a / c ∧ a / c < 1 ∧ 0 < Lam D := by
  have hT' : TileAngles D α β γ := by
    obtain ⟨σ, h0, h1, h2, -⟩ := hT
    exact ⟨σ, h0, h1, h2⟩
  have hirr := (angles D hrel hT' hns).1
  have h := threeAlphaData_of_sides D hrel hT
  have hns3 := not_triple3 D hrel hT' hns
  obtain ⟨-, -, t0⟩ := corner_counts D hirr hrel h hns3 0 (p := 1) (q := 0)
    (by rw [hshape.1]; push_cast; ring)
  obtain ⟨-, -, t2⟩ := corner_counts D hirr hrel h hns3 2 (p := 1) (q := 0)
    (by rw [hshape.2.2]; push_cast; ring)
  obtain ⟨hα, hβ, hγ, hS, hc, ha, hb', ht0, ht1, -, -⟩ := model_facts D hrel hT
  have hcol := (coloring D hrel hT hns).2 (by rw [t0, t2]) ε i₀ hε hi₀ hb
  have hM := hcol.1 (Or.inl ⟨hshape.1, hshape.2.2⟩)
  have r := sines hα hβ hrel
  dsimp only at r
  obtain ⟨r1, -, -, -, -, r6, -, -⟩ := r
  rw [div_eq_iff hS.ne'] at r1 r6
  have s0 := target_side D hrel hT 0
  have s1 := target_side D hrel hT 1
  have s2 := target_side D hrel hT 2
  rw [hshape.1, r1] at s0
  rw [hshape.2.1, r6] at s1
  rw [hshape.2.2, r1] at s2
  set t := 2 * Real.cos (α + β)
  have hst : a / c = t := by rw [ha]; field_simp
  have hΛ : 0 < Lam D := div_pos (circumdiam_pos _) (circumdiam_pos _)
  have ar := (shapeareas D hrel hT).2.2.2.1 hshape
  rw [hst] at ar
  rw [hst]
  have hS' := hS.ne'
  have s0' : D.target.oppLen 0 = Lam D * c * t := by rw [s0]; field_simp
  have s1' : D.target.oppLen 1 = Lam D * c * (t * (2 - t ^ 2)) := by rw [s1]; field_simp
  have s2' : D.target.oppLen 2 = Lam D * c * t := by rw [s2]; field_simp
  have h1t : 1 - t ^ 2 ≠ 0 := by nlinarith
  refine ⟨?_, ?_, s0', ht0, ht1, hΛ⟩
  · have key : ((∑ i, ε i : ℤ) : ℝ) * (1 + t) * (c * (2 - t)) =
        Lam D * t * (2 + t) * (c * (2 - t)) := by
      rw [s0', s1', s2', ha, hb'] at hM
      linear_combination hM
    have : (0 : ℝ) < 2 - t := by linarith
    exact mul_right_cancel₀ (by positivity) key
  · rw [div_eq_iff (by positivity)] at ar
    rw [ar]; field_simp

/-- The integer form of the tiling equation for base angles `α`: if `a/c = m/k` in lowest terms,
then `2k + m ∣ M` and `N (k - m)(2k + m)² = M² (m + k)(2k² - m²)`. -/
theorem isoalpha_int {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D)
    (hshape : D.target.angleAt 0 = α ∧ D.target.angleAt 1 = α + 2 * β ∧ D.target.angleAt 2 = α)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : AtBOnAB D i₀)
    (hb : ε i₀ = 1) {m k : ℤ} (hk : 0 < k) (hcop : IsCoprime m k) (hratio : a / c = m / k) :
    0 < m ∧ m < k ∧ (2 * k + m ∣ ∑ i, ε i) ∧
      (N : ℤ) * (k - m) * (2 * k + m) ^ 2 = (∑ i, ε i) ^ 2 * (m + k) * (2 * k ^ 2 - m ^ 2) := by
  obtain ⟨eM, eN, eX, ht0, ht1, hΛ⟩ := isoalpha_core D hrel hT hns hshape hε hi₀ hb
  set M : ℤ := ∑ i, ε i
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hm : 0 < m := by
    have : (0 : ℝ) < m / k := by rw [← hratio]; exact ht0
    exact_mod_cast (div_pos_iff_of_pos_right hkR).mp this
  have hmk : m < k := by
    have : (m : ℝ) / k < 1 := by rw [← hratio]; exact ht1
    rw [div_lt_one hkR] at this
    exact_mod_cast this
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [hratio] at eM eN eX
  -- The leg `X = BC` is a sum of tile edges.
  have hT' : TileAngles D α β γ := by
    obtain ⟨σ, h0, h1, h2, -⟩ := hT
    exact ⟨σ, h0, h1, h2⟩
  have hirr := (angles D hrel hT' hns).1
  have h := threeAlphaData_of_sides D hrel hT
  have hns3 := not_triple3 D hrel hT' hns
  obtain ⟨p', q', r', -, hX⟩ := side_decomp D hirr hrel h hns3 1
  have hXo : dist (D.target.pts 1) (D.target.pts (1 + 1)) = D.target.oppLen 0 := rfl
  rw [hXo, eX] at hX
  obtain ⟨-, -, -, -, hc, ha, hb', -, -, -, -⟩ := model_facts D hrel hT
  have hst : a / c = 2 * Real.cos (α + β) := by rw [ha]; field_simp
  have eA : a = (m / k) * c := by rw [← hratio, div_mul_cancel₀ _ hc.ne']
  have eB : b = (1 - (m / k) ^ 2) * c := by rw [hb', ← hst, hratio]
  rw [eA, eB] at hX
  have hk0 : (k : ℝ) ≠ 0 := hkR.ne'
  -- `M (k + m) k² = (p mk + q (k² - m²) + r k²)(2k + m)`.
  have h2 : M * (k + m) * k ^ 2 =
      ((p' : ℤ) * (m * k) + q' * (k ^ 2 - m ^ 2) + r' * k ^ 2) * (2 * k + m) := by
    have : ((M * (k + m) * k ^ 2 : ℤ) : ℝ) =
        ((((p' : ℤ) * (m * k) + q' * (k ^ 2 - m ^ 2) + r' * k ^ 2) * (2 * k + m) : ℤ) : ℝ) := by
      push_cast
      have hL : Lam D * c * (m / k) = c * (p' * (m / k) + q' * (1 - (m / k) ^ 2) + r') := by
        rw [hX]; ring
      have hL' : Lam D * (m / k) = p' * (m / k) + q' * (1 - (m / k) ^ 2) + r' := by
        have := mul_left_cancel₀ hc.ne' (by linear_combination hL :
          c * (Lam D * (m / k)) = c * (p' * (m / k) + q' * (1 - (m / k) ^ 2) + r'))
        exact this
      have e1 : (M : ℝ) * (k + m) = Lam D * (m / k) * (2 * k + m) := by
        field_simp at eM ⊢; linear_combination eM
      rw [hL'] at e1
      field_simp at e1
      linear_combination e1
    exact_mod_cast this
  have hcA : IsCoprime (2 * k + m) (k + m) := by
    obtain ⟨u, v, huv⟩ := hcop
    exact ⟨v - u, 2 * u - v, by linear_combination huv⟩
  have hcB : IsCoprime (2 * k + m) k := by
    obtain ⟨u, v, huv⟩ := hcop
    exact ⟨u, v - 2 * u, by linear_combination huv⟩
  have hdvd : 2 * k + m ∣ M :=
    (hcA.mul_right (hcB.pow_right (n := 2))).dvd_of_dvd_mul_right
      ⟨(p' : ℤ) * (m * k) + q' * (k ^ 2 - m ^ 2) + r' * k ^ 2, by rw [mul_assoc] at h2; rw [h2]; ring⟩
  refine ⟨hm, hmk, hdvd, ?_⟩
  have : (((N : ℤ) * (k - m) * (2 * k + m) ^ 2 : ℤ) : ℝ) =
      ((M ^ 2 * (m + k) * (2 * k ^ 2 - m ^ 2) : ℤ) : ℝ) := by
    push_cast
    have hmk' : (1 : ℝ) + m / k ≠ 0 := by positivity
    have e3 : (N : ℝ) * (1 - m / k) * (2 + m / k) ^ 2 = (M : ℝ) ^ 2 * (1 + m / k) * (2 - (m / k) ^ 2) := by
      have e4 : (1 + m / k) * ((N : ℝ) * (1 - m / k) * (2 + m / k) ^ 2 -
          (M : ℝ) ^ 2 * (1 + m / k) * (2 - (m / k) ^ 2)) = 0 := by
        linear_combination (2 + m / k) ^ 2 * eN -
          (2 - (m / k) ^ 2) * ((M : ℝ) * (1 + m / k) + Lam D * (m / k) * (2 + m / k)) * eM
      rcases mul_eq_zero.mp e4 with e | e
      · exact absurd e hmk'
      · linarith
    field_simp at e3
    linear_combination e3
  exact_mod_cast this

-- The integrality and primitivity of the sides are part of the printed hypotheses; the equations do
-- not need them.
set_option linter.unusedVariables false in
/-- **Theorem `theorem:tilingequation4`** (tiling equation for base angles `α`). Suppose
`3α + 2β = π`, `ABC` is isosceles with base angles `α`, and `ABC` is `N`-tiled by the tile whose
integer sides `(a, b, c)` have no common factor and whose angles are `(α, β, γ)`. Let `s = a/c` and
let `M` be the coloring number of the tiling.
(i) Then `M² ≤ 2N`, and `N = M² (1 + s)(2 - s²) / ((1 - s)(2 + s)²)`.
(ii) If `(a, b, c) = (mk, k² - m², k²)` with `k` and `m` coprime, then `2k + m ∣ M`, and setting
`j = M/(2k + m)`, `N (k - m) = j² (m + k)(2k² - m²)`.

`ABC` not similar to the tile is a hypothesis (the paper's standing assumption): for `α = β = π/5`
the angles `(α, α + 2β, α)` are those of the tile. -/
theorem tilingequation4 {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D)
    (hshape : D.target.angleAt 0 = α ∧ D.target.angleAt 1 = α + 2 * β ∧ D.target.angleAt 2 = α)
    {a' b' c' : ℕ} (hint : a = a' ∧ b = b' ∧ c = c') (hprim : Nat.gcd (Nat.gcd a' b') c' = 1)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : AtBOnAB D i₀)
    (hb : ε i₀ = 1) :
    let s := a / c
    let M : ℤ := ∑ i, ε i
    ((M : ℝ) ^ 2 ≤ 2 * N ∧ (N : ℝ) = (M : ℝ) ^ 2 * ((1 + s) * (2 - s ^ 2) / ((1 - s) * (2 + s) ^ 2))) ∧
      ∀ m k : ℕ, Nat.Coprime k m → (a = m * k ∧ b = k ^ 2 - m ^ 2 ∧ c = k ^ 2) →
        ((2 * k + m : ℤ) ∣ M) ∧
          let j := M / (2 * k + m)
          (N : ℤ) * (k - m) = j ^ 2 * (m + k) * (2 * k ^ 2 - m ^ 2) := by
  intro s M
  obtain ⟨eM, eN, -, ht0, ht1, hΛ⟩ := isoalpha_core D hrel hT hns hshape hε hi₀ hb
  set t := a / c
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have h1 : (1 : ℝ) + t ≠ 0 := by positivity
  have e3 : (N : ℝ) * (1 - t) * (2 + t) ^ 2 = (M : ℝ) ^ 2 * (1 + t) * (2 - t ^ 2) := by
    have e4 : (1 + t) * ((N : ℝ) * (1 - t) * (2 + t) ^ 2 - (M : ℝ) ^ 2 * (1 + t) * (2 - t ^ 2)) = 0 := by
      linear_combination (2 + t) ^ 2 * eN - (2 - t ^ 2) * ((M : ℝ) * (1 + t) + Lam D * t * (2 + t)) * eM
    rcases mul_eq_zero.mp e4 with e | e
    · exact absurd e h1
    · linarith
  refine ⟨⟨?_, ?_⟩, fun m k hcop hsides => ?_⟩
  · -- `2(1 + s)(2 - s²) - (1 - s)(2 + s)² = s(4 + s - s²) > 0`.
    have hD : (0 : ℝ) < (1 - t) * (2 + t) ^ 2 := by positivity
    have hf : (M : ℝ) ^ 2 * ((1 - t) * (2 + t) ^ 2) ≤ 2 * N * ((1 - t) * (2 + t) ^ 2) := by
      have : 0 ≤ (M : ℝ) ^ 2 * (t * (4 + t - t ^ 2)) := by
        have : 0 < 4 + t - t ^ 2 := by nlinarith
        positivity
      nlinarith
    exact le_of_mul_le_mul_right hf hD
  · rw [← mul_div_assoc, eq_div_iff (by positivity)]
    linear_combination e3
  · obtain ⟨ea, eb, ec⟩ := hsides
    have hk : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · obtain ⟨-, -, -, -, hc, -⟩ := model_facts D hrel hT
        rw [ec, h0] at hc; simp at hc
      · exact h0
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk
    have hratio : a / c = ((m : ℤ) : ℝ) / ((k : ℤ) : ℝ) := by
      rw [ea, ec]; push_cast; field_simp
    have hcop' : IsCoprime (m : ℤ) (k : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
    obtain ⟨-, -, hdvd, heq⟩ := isoalpha_int D hrel hT hns hshape hε hi₀ hb
      (by exact_mod_cast hk) hcop' hratio
    refine ⟨hdvd, ?_⟩
    intro j
    obtain ⟨j', hj'⟩ := hdvd
    have hjj : j = j' := by
      simp only [j, M]; rw [hj', Int.mul_ediv_cancel_left _ (by positivity)]
    rw [hjj]
    have hd : (0 : ℤ) < 2 * k + m := by positivity
    have : (2 * (k : ℤ) + m) ^ 2 * ((N : ℤ) * (k - m)) =
        (2 * (k : ℤ) + m) ^ 2 * (j' ^ 2 * (m + k) * (2 * k ^ 2 - m ^ 2)) := by
      rw [hj'] at heq
      linear_combination heq
    exact mul_left_cancel₀ (pow_ne_zero 2 hd.ne') this

/-- **Theorem `theorem:notprime5`.** Suppose `3α + 2β = π`, `ABC` is isosceles with base angles
`α`, and `ABC` is `N`-tiled by a tile with angles `(α, β, γ)`. Then `N` is not prime.

`ABC` not similar to the tile is a hypothesis, as in `theorem:tilingequation4`. -/
theorem notprime5 {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D)
    (hshape : TgtAngles D α (α + 2 * β) α) : ¬ N.Prime := by
  intro hN
  obtain ⟨σ, h0, h1, h2⟩ := hshape
  set D₁ := relabelTarget D σ
  have hT₁ : TileSides D₁ α β γ a b c := hT
  have e0 : D₁.target.angleAt 0 = α := by rw [relabel_angleAt]; exact h0
  have e1 : D₁.target.angleAt 1 = α + 2 * β := by rw [relabel_angleAt]; exact h1
  have e2 : D₁.target.angleAt 2 = α := by rw [relabel_angleAt]; exact h2
  have hns₁ : ¬ SimilarTM D₁ := fun hs => hns (similar_of_relabel D σ hs)
  have hT' : TileAngles D₁ α β γ := by
    obtain ⟨τ, g0, g1, g2, -⟩ := hT₁
    exact ⟨τ, g0, g1, g2⟩
  obtain ⟨i₀, hAB⟩ := exists_atB_onAB D₁
  have hi₀ : TileAt D₁ 1 i₀ := by
    obtain ⟨l, -, -, hl, -⟩ := hAB
    exact ⟨l, hl⟩
  obtain ⟨ε, hε, hεi⟩ := signedtiles D₁ hrel hT' hns₁ hi₀
  obtain ⟨-, -, -, ht0, ht1, -⟩ := isoalpha_core D₁ hrel hT₁ hns₁ ⟨e0, e1, e2⟩ hε hAB hεi
  obtain ⟨⟨q, hq⟩, -, -⟩ := rationaltile D₁ hrel hT₁ hns₁
  have hq0 : 0 < q := by
    have : (0 : ℝ) < q := by rw [← hq]; exact ht0
    exact_mod_cast this
  set m : ℤ := q.num
  set k : ℤ := (q.den : ℤ)
  have hk : 0 < k := by simp only [k]; exact_mod_cast q.den_pos
  have hcop : IsCoprime m k := by rw [Int.isCoprime_iff_gcd_eq_one]; exact q.reduced
  have hqmk : (q : ℝ) = m / k := by rw [Rat.cast_def]; simp [m, k]
  obtain ⟨hm, hmk, hdvd, heq⟩ :=
    isoalpha_int D₁ hrel hT₁ hns₁ ⟨e0, e1, e2⟩ hε hAB hεi hk hcop (by rw [hq, hqmk])
  set M : ℤ := ∑ i, ε i
  obtain ⟨j, hj⟩ := hdvd
  have hd : (0 : ℤ) < 2 * k + m := by omega
  have hMpos : 0 < M := by
    obtain ⟨eM, -, -, ht0', -, hΛ⟩ := isoalpha_core D₁ hrel hT₁ hns₁ ⟨e0, e1, e2⟩ hε hAB hεi
    have : (0 : ℝ) < M := by
      have h' : (0 : ℝ) < (M : ℝ) * (1 + a / c) := by rw [eM]; positivity
      exact pos_of_mul_pos_left h' (by positivity)
    exact_mod_cast this
  have hj0 : 0 < j := by
    rw [hj] at hMpos
    exact pos_of_mul_pos_right hMpos hd.le
  have hNj : (N : ℤ) * (k - m) = j ^ 2 * (m + k) * (2 * k ^ 2 - m ^ 2) := by
    rw [hj] at heq
    have : (2 * k + m) ^ 2 * ((N : ℤ) * (k - m)) =
        (2 * k + m) ^ 2 * (j ^ 2 * (m + k) * (2 * k ^ 2 - m ^ 2)) := by
      linear_combination heq
    exact mul_left_cancel₀ (pow_ne_zero 2 hd.ne') this
  exact notprime5_arith hN hj0 hm hmk hcop hNj

/-- **Theorem `theorem:notprime`.** Let `ABC` be `N`-tiled by a tile with
angles `(α, β, γ)` such that `3α + 2β = π`, and `ABC` not similar to the tile. Then `N` is not
prime, except possibly for the shapes `(2α, β, α + β)` and `(β, 3α, β)`. -/
theorem notprime {α β γ : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (hT : TileAngles D α β γ)
    (hns : ¬ SimilarTM D) (hN : N.Prime) :
    TgtAngles D (2 * α) β (α + β) ∨ TgtAngles D β (3 * α) β := by
  obtain ⟨σ, h0, h1, h2⟩ := hT
  have hT' : TileSides D α β γ (D.model.oppLen (σ 0)) (D.model.oppLen (σ 1))
      (D.model.oppLen (σ 2)) := ⟨σ, h0, h1, h2, rfl, rfl, rfl⟩
  rcases (shapes D hrel ⟨σ, h0, h1, h2⟩ hns).1 with e | e | e | e | e
  · exact absurd hN (notprime5 D hrel hT' hns e)
  · exact Or.inr e
  · exact absurd hN (notprime3 D hrel hT' e)
  · exact Or.inl e
  · exact absurd hN (notprime2 D hrel hT' hns e)

end TriangleTiling.ThreeAlpha
