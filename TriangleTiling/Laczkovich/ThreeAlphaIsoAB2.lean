/-
The isosceles triangle with base angles `α + β` (M. Beeson, *Triangle tiling: the case
3α + 2β = π*, arXiv 1206.2229v4): `lemma:XY`, `lemma:mu`, `lemma:halfintegermu`.

Statements not yet checked by Beeson. Conventions as in `theorem:isosceles1`: the vertex angle `α`
is at `B = target.pts 1`, the base is `AC`; `X = |AB|`, `Y = |AC|`. The scaling factor `μ` of
`definition:scaling` (`λ/κ`, the ratio of circumdiameters) is `Lam D`.
-/
import TriangleTiling.Laczkovich.ThreeAlphaSection10
import TriangleTiling.Laczkovich.ThreeAlphaIsoAB

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.BeesonColoring Set
open Erdos634.Draft.LaczFormal (TileAngles)

variable {N : ℕ} (D : CongruentDissection N)

/-- The sides of the isosceles triangle with base angles `α + β`, by the scale `Λ`. -/
theorem iso_scale {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c)
    (hshape : D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + β) :
    D.target.oppLen 0 = Lam D * c ∧ D.target.oppLen 1 = Lam D * a ∧
      D.target.oppLen 2 = Lam D * c ∧ 0 < Lam D := by
  obtain ⟨hα, hβ, -, hS, hc, ha, -, -, -, -, -⟩ := model_facts D hrel hT
  have hΛ : 0 < Lam D := div_pos (circumdiam_pos _) (circumdiam_pos _)
  have r := sines hα hβ hrel
  dsimp only at r
  obtain ⟨r1, -, -, r4, -, -, -, -⟩ := r
  rw [div_eq_iff hS.ne'] at r1 r4
  have s0 := target_side D hrel hT 0
  have s1 := target_side D hrel hT 1
  have s2 := target_side D hrel hT 2
  rw [hshape.1, r4] at s0
  rw [hshape.2.1, r1] at s1
  rw [hshape.2.2, r4] at s2
  have hS' := hS.ne'
  refine ⟨?_, ?_, ?_, hΛ⟩
  · rw [s0]; field_simp
  · rw [s1, ha]; field_simp
  · rw [s2]; field_simp

-- The integrality of the sides is part of the printed hypotheses; the lengths do not need it.
set_option linter.unusedVariables false in
/-- **Lemma `lemma:XY`.** Let triangle `ABC` be isosceles with base angles `α + β` and vertex angle
`α` at `B`, and suppose `ABC` is `N`-tiled by the integer-sided tile `(a, b, c)` with angles
`(α, β, γ)` and `gcd(a, b, c) = 1`. Let `X` be the length of `AB` and `Y` the length of `AC`.
Then `X = μc` and `Y = μa`. -/
theorem XY {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c)
    (hshape : D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + β)
    {a' b' c' : ℕ} (hint : a = a' ∧ b = b' ∧ c = c') (hprim : Nat.gcd (Nat.gcd a' b') c' = 1) :
    dist (D.target.pts 0) (D.target.pts 1) = Lam D * c ∧
      dist (D.target.pts 0) (D.target.pts 2) = Lam D * a := by
  obtain ⟨-, hY, hZ, -⟩ := iso_scale D hrel hT hshape
  refine ⟨hZ, ?_⟩
  rw [← hY]; unfold Tri.oppLen; exact dist_comm _ _

set_option linter.unusedVariables false in
/-- **Lemma `lemma:mu`.** Suppose `ABC` is isosceles with vertex angle `α` at `B` and base angles
`α + β`, `N`-tiled by the tile with angles `(α, β, γ)` and integer sides `(a, b, c)` with no
common factor. Let `μ` be as in `definition:scaling`. Then `μ = M(1 + s)` and `μ² = Nb/c`.
(`M` is the coloring number, a tile at `B` with an edge on `AB` black.) -/
theorem mu {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c)
    (hshape : D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + β)
    {a' b' c' : ℕ} (hint : a = a' ∧ b = b' ∧ c = c') (hprim : Nat.gcd (Nat.gcd a' b') c' = 1)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : AtBOnAB D i₀)
    (hb : ε i₀ = 1) :
    let s := a / c
    let M : ℤ := ∑ i, ε i
    Lam D = M * (1 + s) ∧ Lam D ^ 2 = N * b / c := by
  intro s M
  obtain ⟨hM, hN, -, -, -, hs0, hs1, hΛ⟩ := isoab_core D hrel hT hshape hε hi₀ hb
  obtain ⟨-, -, -, -, hc, ha, hb', -, -, -, -⟩ := model_facts D hrel hT
  have hst : a / c = 2 * Real.cos (α + β) := by rw [ha]; field_simp
  have h1 : (1 : ℝ) + s ≠ 0 := by positivity
  have ha0 : 0 < a := by
    have h := mul_pos hs0 hc; rwa [div_mul_cancel₀ _ hc.ne'] at h
  have hac : a < c := by
    have h := mul_lt_mul_of_pos_right hs1 hc; rwa [div_mul_cancel₀ _ hc.ne', one_mul] at h
  have hca : c + a ≠ 0 := by positivity
  have hca2 : c ^ 2 - a ^ 2 ≠ 0 := by nlinarith
  refine ⟨by rw [hM]; simp only [s]; field_simp, ?_⟩
  rw [hN, hb', ← hst]
  have : (1 : ℝ) - s ^ 2 ≠ 0 := by nlinarith
  simp only [s] at this ⊢
  field_simp

/-- **Lemma `lemma:halfintegermu`.** Suppose `ABC` is isosceles with vertex angle `α` at `B` and
base angles `α + β`, with `3α + 2β = π`, `N`-tiled by a tile with angles `(α, β, γ)` and integer
sides `(a, b, c)` with no common factor. Let `k = gcd(a, c)`. Then

(i) the number of `b` edges of tiles on side `AB` is divisible by `k`, and the same for `BC`;

(ii) `μk` is an integer, and `μ` is an integer if and only if `k ∣ M`;

(iii) if `q` is the number of `b` edges on the base `AC` and `M` the coloring number of the
tiling, then `M ≡ -q (mod k)`. -/
theorem halfintegermu {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c)
    (hshape : D.target.angleAt 0 = α + β ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = α + β)
    {a' b' c' : ℕ} (hint : a = a' ∧ b = b' ∧ c = c') (hprim : Nat.gcd (Nat.gcd a' b') c' = 1)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : AtBOnAB D i₀)
    (hb : ε i₀ = 1) :
    let M : ℤ := ∑ i, ε i
    let k := Nat.gcd a' c'
    (k ∣ dEntry D 2 β ∧ k ∣ dEntry D 0 β) ∧
      ((∃ z : ℤ, Lam D * k = z) ∧ ((∃ z : ℤ, Lam D = z) ↔ (k : ℤ) ∣ M)) ∧
      M ≡ -(dEntry D 1 β : ℤ) [ZMOD k] := by
  intro M k
  obtain ⟨hMΛ, -, hY, hZ, hX, hs0, hs1, hΛ⟩ := isoab_core D hrel hT hshape hε hi₀ hb
  obtain ⟨hα, hβ, hγ, -, hc, ha, hb', -, -, -, -⟩ := model_facts D hrel hT
  obtain ⟨ea, eb, ec⟩ := hint
  -- `a/c = m/k` in lowest terms, and `(a, b, c) = (mk, k² - m², k²)`.
  have hc0 : 0 < c' := by have : (0 : ℝ) < c' := ec ▸ hc; exact_mod_cast this
  have hg : 0 < Nat.gcd a' c' := Nat.gcd_pos_of_pos_right _ hc0
  set m := a' / Nat.gcd a' c'
  set k₀ := c' / Nat.gcd a' c'
  have hcop : Nat.Coprime m k₀ := Nat.coprime_div_gcd_div_gcd hg
  have hk₀ : 0 < k₀ := Nat.div_pos (Nat.le_of_dvd hc0 (Nat.gcd_dvd_right a' c')) hg
  have hb0 : 0 < b' := by
    have : (0 : ℝ) < b' := by
      rw [← eb, hb']
      have h1 : 0 < 2 * Real.cos (α + β) := by
        have := hs0; rw [ha] at this; field_simp at this; exact this
      have h2 : 2 * Real.cos (α + β) < 1 := by
        have := hs1; rw [ha] at this; field_simp at this; linarith
      have : 0 < 1 - (2 * Real.cos (α + β)) ^ 2 := by nlinarith
      positivity
    exact_mod_cast this
  have hrel' : a' ^ 2 + b' * c' = c' ^ 2 := by
    have : ((a' ^ 2 + b' * c' : ℕ) : ℝ) = ((c' ^ 2 : ℕ) : ℝ) := by
      push_cast; rw [← ea, ← eb, ← ec, ha, hb']; ring
    exact_mod_cast this
  obtain ⟨u, hu⟩ := Nat.gcd_dvd_left a' c'
  obtain ⟨v, hv⟩ := Nat.gcd_dvd_right a' c'
  have hmu : m = u := Nat.div_eq_of_eq_mul_left hg (hu.trans (mul_comm _ _))
  have hkv : k₀ = v := Nat.div_eq_of_eq_mul_left hg (hv.trans (mul_comm _ _))
  have hratio : a' * k₀ = m * c' := by
    rw [hmu, hkv]
    calc a' * v = Nat.gcd a' c' * u * v := by rw [← hu]
      _ = u * (Nat.gcd a' c' * v) := by ring
      _ = u * c' := by rw [← hv]
  obtain ⟨hae, hbe, hce, hkg, -, hmk⟩ :=
    gsquare_arith a' b' c' m k₀ hb0 hc0 hprim hrel' hcop hk₀ hratio
  have hkk : k₀ = k := hkg
  rw [hkk] at hae hbe hce hcop hk₀
  have hle : m ^ 2 ≤ k ^ 2 := Nat.pow_le_pow_left (hkk ▸ hmk).le 2
  have haR : a = (m : ℝ) * k := by rw [ea, hae]; push_cast; ring
  have hbR : b = (k : ℝ) ^ 2 - m ^ 2 := by rw [eb, hbe]; push_cast [hle]; ring
  have hcR : c = (k : ℝ) ^ 2 := by rw [ec, hce]; push_cast; ring
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk₀
  -- `μ = M(k + m)/k`.
  have hΛ' : Lam D * k = M * (k + m) := by
    have hkm : (k : ℝ) + m ≠ 0 := by positivity
    rw [hMΛ, haR, hcR]
    field_simp
  -- The rows of the `d` matrix, as integer equations.
  have hns := not_similar_of_alpha_beta D hrel hT hshape.1
  have hT' : TileAngles D α β γ := by
    obtain ⟨σ, h0, h1, h2, -⟩ := hT
    exact ⟨σ, h0, h1, h2⟩
  have hirr := (angles D hrel hT' hns).1
  have h := threeAlphaData_of_sides D hrel hT
  have hrow : ∀ j, D.target.oppLen j = dEntry D j α * a + dEntry D j β * b + dEntry D j γ * c :=
    fun j => hγ ▸ dmatrix_row D hirr hrel h j
  have hcopZ : IsCoprime (k : ℤ) ((m : ℤ) ^ 2) :=
    (Nat.isCoprime_iff_coprime.mpr hcop.symm).pow_right
  have hleg : ∀ j, D.target.oppLen j = Lam D * c → (k : ℤ) ∣ dEntry D j β := by
    intro j hj
    have r := hrow j
    rw [hj, haR, hbR, hcR] at r
    have rZ : (M : ℤ) * (k + m) * k = dEntry D j α * (m * k) + dEntry D j β * ((k : ℤ) ^ 2 - m ^ 2)
        + dEntry D j γ * (k : ℤ) ^ 2 := by
      have : ((M * (k + m) * k : ℤ) : ℝ) = ((dEntry D j α * (m * k) + dEntry D j β *
          ((k : ℤ) ^ 2 - m ^ 2) + dEntry D j γ * (k : ℤ) ^ 2 : ℤ) : ℝ) := by
        push_cast
        rw [← hΛ']
        linear_combination r
      exact_mod_cast this
    have : (k : ℤ) ∣ dEntry D j β * (m : ℤ) ^ 2 :=
      ⟨dEntry D j β * k + dEntry D j α * m + dEntry D j γ * k - M * (k + m), by
        linear_combination rZ⟩
    exact hcopZ.dvd_of_dvd_mul_right this
  refine ⟨⟨?_, ?_⟩, ⟨⟨M * (k + m), by rw [hΛ']; push_cast; ring⟩, ?_⟩, ?_⟩
  · exact_mod_cast hleg 2 hZ
  · exact_mod_cast hleg 0 hX
  · constructor
    · rintro ⟨z, hz⟩
      have hzZ : z * k = M * (k + m) := by
        have : ((z * k : ℤ) : ℝ) = ((M * (k + m) : ℤ) : ℝ) := by
          push_cast; rw [← hz]; exact hΛ'
        exact_mod_cast this
      have : (k : ℤ) ∣ M * m := ⟨z - M, by linear_combination -hzZ⟩
      exact ((Nat.isCoprime_iff_coprime.mpr hcop.symm).dvd_of_dvd_mul_right this)
    · rintro ⟨t, ht⟩
      refine ⟨t * (k + m), ?_⟩
      have : Lam D * k = (t * (k + m) : ℤ) * k := by
        rw [hΛ']; push_cast; rw [show ((M : ℤ) : ℝ) = ((k * t : ℤ) : ℝ) by rw [ht]]; push_cast; ring
      exact mul_right_cancel₀ hkR.ne' this
  · -- The base: `M ≡ -q (mod k)`.
    have r := hrow 1
    have hY' : D.target.oppLen 1 = Lam D * a := by rw [hY]; field_simp
    rw [hY', haR, hbR, hcR] at r
    have rZ : (M : ℤ) * (k + m) * m = dEntry D 1 α * (m * k) +
        dEntry D 1 β * ((k : ℤ) ^ 2 - m ^ 2) + dEntry D 1 γ * (k : ℤ) ^ 2 := by
      have : ((M * (k + m) * m : ℤ) : ℝ) = ((dEntry D 1 α * (m * k) + dEntry D 1 β *
          ((k : ℤ) ^ 2 - m ^ 2) + dEntry D 1 γ * (k : ℤ) ^ 2 : ℤ) : ℝ) := by
        push_cast
        rw [← hΛ']
        rw [show Lam D * (m * k) = Lam D * k * m by ring] at r
        linear_combination r
      exact_mod_cast this
    rw [Int.modEq_iff_dvd]
    have : (k : ℤ) ∣ (-(dEntry D 1 β : ℤ) - M) * (m : ℤ) ^ 2 :=
      ⟨M * m - dEntry D 1 α * m - dEntry D 1 β * k - dEntry D 1 γ * k, by
        linear_combination -rZ⟩
    exact hcopZ.dvd_of_dvd_mul_right this

end TriangleTiling.ThreeAlpha
