/-
`ABC` isosceles with base angles `β` (Section 10 of M. Beeson, *Triangle tiling: the case
3α + 2β = π*, arXiv 1206.2229v4): `theorem:tilingequation3` and `theorem:notprime4`.

Statements not yet checked with Beeson (written 2026-10-24 while he was away). `M` is the coloring
number of `theorem:coloring` (a tile at `B` with an edge on `AB` black).
-/
import TriangleTiling.Laczkovich.ThreeAlphaSecond

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles)
open Erdos634.BeesonColoring

variable {N : ℕ} (D : CongruentDissection N)

/-- The coloring equation and `N` in terms of `Λ`, `c` and `t = s`, for base angles `β`. -/
theorem isobeta_core {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D)
    (hshape : D.target.angleAt 0 = β ∧ D.target.angleAt 1 = 3 * α ∧ D.target.angleAt 2 = β)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : AtBOnAB D i₀)
    (hb : ε i₀ = 1) :
    ((∑ i, ε i : ℤ) : ℝ) = Lam D * (1 - a / c) * (1 + a / c) ^ 2 ∧
      (N : ℝ) = Lam D ^ 2 * ((1 - (a / c) ^ 2) ^ 2 * (3 - (a / c) ^ 2)) ∧ 0 < a / c ∧ a / c < 1 ∧
      0 < Lam D := by
  have hT' : TileAngles D α β γ := by
    obtain ⟨σ, h0, h1, h2, -⟩ := hT
    exact ⟨σ, h0, h1, h2⟩
  have hirr := (angles D hrel hT' hns).1
  have h := threeAlphaData_of_sides D hrel hT
  have hns3 := not_triple3 D hrel hT' hns
  obtain ⟨-, -, t0⟩ := corner_counts D hirr hrel h hns3 0 (p := 0) (q := 1)
    (by rw [hshape.1]; push_cast; ring)
  obtain ⟨-, -, t2⟩ := corner_counts D hirr hrel h hns3 2 (p := 0) (q := 1)
    (by rw [hshape.2.2]; push_cast; ring)
  obtain ⟨hα, hβ, hγ, hS, hc, ha, hb', ht0, ht1, -, -⟩ := model_facts D hrel hT
  have hcol := (coloring D hrel hT hns).2 (by rw [t0, t2]) ε i₀ hε hi₀ hb
  have hM := hcol.1 (Or.inr ⟨hshape.1, hshape.2.2⟩)
  have r := sines hα hβ hrel
  dsimp only at r
  obtain ⟨-, r2, -, -, -, -, r7, -⟩ := r
  rw [div_eq_iff hS.ne'] at r2 r7
  have s0 := target_side D hrel hT 0
  have s1 := target_side D hrel hT 1
  have s2 := target_side D hrel hT 2
  rw [hshape.1, r2] at s0
  rw [hshape.2.1, r7] at s1
  rw [hshape.2.2, r2] at s2
  set t := 2 * Real.cos (α + β)
  have hst : a / c = t := by rw [ha]; field_simp
  have hΛ : 0 < Lam D := div_pos (circumdiam_pos _) (circumdiam_pos _)
  have ar := (shapeareas D hrel hT).2.1 hshape
  rw [hst] at ar
  rw [hst]
  have hS' := hS.ne'
  have s0' : D.target.oppLen 0 = Lam D * c * (1 - t ^ 2) := by rw [s0]; field_simp
  have s1' : D.target.oppLen 1 = Lam D * c * (t * (1 - t ^ 2) * (3 - t ^ 2)) := by
    rw [s1]; field_simp
  have s2' : D.target.oppLen 2 = Lam D * c * (1 - t ^ 2) := by rw [s2]; field_simp
  refine ⟨?_, by rw [← ar]; field_simp, ht0, ht1, hΛ⟩
  have key : ((∑ i, ε i : ℤ) : ℝ) * (c * ((2 - t) * (1 + t))) =
      Lam D * (1 - t) * (1 + t) ^ 2 * (c * ((2 - t) * (1 + t))) := by
    rw [s0', s1', s2', ha, hb'] at hM
    linear_combination hM
  have h2 : (0 : ℝ) < (2 - t) * (1 + t) := by
    have : 0 < 2 - t := by linarith
    positivity
  exact mul_right_cancel₀ (by positivity) key

-- The integrality of the sides is part of the printed hypotheses; the equation does not need it.
set_option linter.unusedVariables false in
/-- **Theorem `theorem:tilingequation3`** (tiling equation). Suppose `3α + 2β = π`, `ABC` is
isosceles with base angles `β`, and `ABC` is `N`-tiled by a tile with angles `(α, β, γ)` and sides
`(a, b, c)` of integer lengths with no common factor. Let `M` be the coloring number of the tiling
and `s = a/c`. Then `0 < N/3 < M² < 2N`, and `N / M² = (3 - s²)/(1 + s)²`, and consequently
`s = (√(3M² + 2N) M - N)/(M² + N)`.

`ABC` not similar to the tile is a hypothesis (the paper's standing assumption): for `α = β = π/5`
the angles `(β, 3α, β)` are those of the tile. -/
theorem tilingequation3 {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D)
    (hshape : D.target.angleAt 0 = β ∧ D.target.angleAt 1 = 3 * α ∧ D.target.angleAt 2 = β)
    {a' b' c' : ℕ} (hint : a = a' ∧ b = b' ∧ c = c') (hprim : Nat.gcd (Nat.gcd a' b') c' = 1)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : AtBOnAB D i₀)
    (hb : ε i₀ = 1) :
    let s := a / c
    let M : ℤ := ∑ i, ε i
    0 < (N : ℝ) / 3 ∧ (N : ℝ) / 3 < (M : ℝ) ^ 2 ∧ (M : ℝ) ^ 2 < 2 * N ∧
      (N : ℝ) / (M : ℝ) ^ 2 = (3 - s ^ 2) / (1 + s) ^ 2 ∧
      s = (Real.sqrt (3 * (M : ℝ) ^ 2 + 2 * N) * M - N) / ((M : ℝ) ^ 2 + N) := by
  intro s M
  obtain ⟨eM, eN, ht0, ht1, hΛ⟩ := isobeta_core D hrel hT hns hshape hε hi₀ hb
  set t := a / c
  have hMpos : (0 : ℝ) < M := by
    rw [eM]
    have : 0 < 1 - t := by linarith
    positivity
  have hM0 : (M : ℝ) ≠ 0 := hMpos.ne'
  have hf : (N : ℝ) = (M : ℝ) ^ 2 * ((3 - t ^ 2) / (1 + t) ^ 2) := by
    rw [eN, eM]
    have : (1 : ℝ) + t ≠ 0 := by positivity
    field_simp; ring
  have hNM : (N : ℝ) / (M : ℝ) ^ 2 = (3 - t ^ 2) / (1 + t) ^ 2 := by
    rw [hf]; field_simp
  have hlo : 1 / 2 < (3 - t ^ 2) / (1 + t) ^ 2 := by
    rw [lt_div_iff₀ (by positivity)]; nlinarith
  have hhi : (3 - t ^ 2) / (1 + t) ^ 2 < 3 := by
    rw [div_lt_iff₀ (by positivity)]; nlinarith
  have hM2 : (0 : ℝ) < (M : ℝ) ^ 2 := by positivity
  refine ⟨?_, ?_, ?_, hNM, ?_⟩
  · rw [hf]; have : 0 < (3 - t ^ 2) / (1 + t) ^ 2 := by linarith
    positivity
  · rw [hf]; nlinarith
  · rw [hf]; nlinarith
  · -- Solve the quadratic `(M² + N) t² + 2N t + N - 3M² = 0` for its positive root.
    have hquad : ((M : ℝ) ^ 2 + N) * t ^ 2 + 2 * N * t + N - 3 * (M : ℝ) ^ 2 = 0 := by
      have h1 : (N : ℝ) * (1 + t) ^ 2 = (M : ℝ) ^ 2 * (3 - t ^ 2) := by
        rw [hf]; have : (1 : ℝ) + t ≠ 0 := by positivity
        field_simp
      linear_combination h1
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hR := Real.sq_sqrt (show (0 : ℝ) ≤ 3 * (M : ℝ) ^ 2 + 2 * N by positivity)
    have hRnn := Real.sqrt_nonneg (3 * (M : ℝ) ^ 2 + 2 * N)
    have hsq : (((M : ℝ) ^ 2 + N) * t + N) ^ 2 =
        (Real.sqrt (3 * (M : ℝ) ^ 2 + 2 * N) * M) ^ 2 := by
      rw [mul_pow, hR]
      linear_combination ((M : ℝ) ^ 2 + N) * hquad
    have heq := (sq_eq_sq₀ (by positivity) (by positivity)).mp hsq
    rw [eq_div_iff (by positivity)]
    linarith

/-- **Theorem `theorem:notprime4`** (tiling equation, second form). Suppose `3α + 2β = π`, `ABC` is
isosceles with base angles `β`, and `ABC` is `N`-tiled by a tile with angles `(α, β, γ)`, coloring
number `M`, and sides `(a, b, c)` where `a/c = m/k` in lowest terms. Then `m + k ∣ M`, and for some
integer `j`, `N = j²(3k² - m²) = j²(3c - a²/c)`, and if `N` is squarefree, `j = 1`.

As in `theorem:tilingequation3`, the sides are integers with no common factor (needed for
`3c - a²/c = 3k² - m²`); `j = M/(m + k) > 0`. -/
theorem notprime4 {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D)
    (hshape : D.target.angleAt 0 = β ∧ D.target.angleAt 1 = 3 * α ∧ D.target.angleAt 2 = β)
    {a' b' c' : ℕ} (hint : a = a' ∧ b = b' ∧ c = c') (hprim : Nat.gcd (Nat.gcd a' b') c' = 1)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : AtBOnAB D i₀)
    (hb : ε i₀ = 1) {m k : ℕ} (hmk : Nat.Coprime m k) (hk : 0 < k) (hratio : a / c = m / k) :
    let M : ℤ := ∑ i, ε i
    ((m : ℤ) + k ∣ M) ∧ ∃ j : ℤ, 0 < j ∧ M = j * (m + k) ∧ (N : ℤ) = j ^ 2 * (3 * k ^ 2 - m ^ 2) ∧
      (N : ℤ) = j ^ 2 * (3 * c' - (a' : ℤ) ^ 2 / c') ∧ (Squarefree N → j = 1) := by
  intro M
  obtain ⟨eM, eN, ht0, ht1, hΛ⟩ := isobeta_core D hrel hT hns hshape hε hi₀ hb
  have te := tilingequation3 D hrel hT hns hshape hint hprim hε hi₀ hb
  dsimp only at te
  obtain ⟨-, -, -, hNM, -⟩ := te
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hm0 : (0 : ℝ) < m := by
    have := ht0
    rw [hratio] at this
    exact (div_pos_iff_of_pos_right hkR).mp this
  have hmk' : (m : ℝ) < k := by
    have : (m : ℝ) / k < 1 := by rw [← hratio]; exact ht1
    rwa [div_lt_one hkR] at this
  have hMpos : (0 : ℝ) < M := by
    rw [eM]
    have : 0 < 1 - a / c := by linarith
    positivity
  -- `N (m + k)² = M² (3k² - m²)`.
  have heqR : ((N : ℤ) : ℝ) * (((m : ℤ) + k : ℤ) : ℝ) ^ 2 =
      (((M : ℤ) ^ 2 * (3 * (k : ℤ) ^ 2 - (m : ℤ) ^ 2) : ℤ) : ℝ) := by
    push_cast
    rw [hratio] at hNM
    rw [div_eq_div_iff (by positivity) (by positivity)] at hNM
    field_simp at hNM
    linear_combination hNM
  have heqZ : (N : ℤ) * ((m : ℤ) + k) ^ 2 = M ^ 2 * (3 * (k : ℤ) ^ 2 - (m : ℤ) ^ 2) := by
    exact_mod_cast heqR
  have hcop : IsCoprime (m : ℤ) (k : ℤ) := Nat.isCoprime_iff_coprime.mpr hmk
  have hdvd := notprime4_arith (N := (N : ℤ)) (by exact_mod_cast hm0) (by exact_mod_cast hmk') hcop
    heqZ
  refine ⟨hdvd, ?_⟩
  obtain ⟨j, hj⟩ := hdvd
  have hd0 : (0 : ℤ) < m + k := by
    have : (0 : ℤ) < m := by exact_mod_cast hm0
    omega
  have hj0 : 0 < j := by
    have : (0 : ℤ) < M := by exact_mod_cast hMpos
    rw [hj] at this
    exact pos_of_mul_pos_right this hd0.le
  have hNj : (N : ℤ) = j ^ 2 * (3 * k ^ 2 - m ^ 2) := by
    rw [hj] at heqZ
    have : ((m : ℤ) + k) ^ 2 * N = ((m : ℤ) + k) ^ 2 * (j ^ 2 * (3 * k ^ 2 - m ^ 2)) := by
      linear_combination heqZ
    exact mul_left_cancel₀ (pow_ne_zero 2 hd0.ne') this
  -- The primitive sides are `(mk, k² - m², k²)`.
  obtain ⟨-, -, -, -, hc, ha, hb', -, -, -, -⟩ := model_facts D hrel hT
  obtain ⟨ea, eb, ec⟩ := hint
  have hc0 : 0 < c' := by
    have : (0 : ℝ) < c' := by rw [← ec]; exact hc
    exact_mod_cast this
  have hb0 : 0 < b' := by
    have : (0 : ℝ) < b' := by
      rw [← eb, hb']
      obtain ⟨-, -, -, -, -, -, -, ht0', ht1', -, -⟩ := model_facts D hrel hT
      have : 0 < 1 - (2 * Real.cos (α + β)) ^ 2 := by nlinarith
      positivity
    exact_mod_cast this
  have hrel' : a' ^ 2 + b' * c' = c' ^ 2 := by
    have : ((a' ^ 2 + b' * c' : ℕ) : ℝ) = ((c' ^ 2 : ℕ) : ℝ) := by
      push_cast; rw [← ea, ← eb, ← ec, ha, hb']; ring
    exact_mod_cast this
  have hratio' : a' * k = m * c' := by
    have : ((a' * k : ℕ) : ℝ) = ((m * c' : ℕ) : ℝ) := by
      push_cast; rw [← ea, ← ec]
      rw [div_eq_div_iff hc.ne' hkR.ne'] at hratio; linarith
    exact_mod_cast this
  obtain ⟨hae, -, hce, -, -, -⟩ := gsquare_arith a' b' c' m k hb0 hc0 hprim hrel' hmk hk hratio'
  refine ⟨j, hj0, by rw [hj]; ring, hNj, ?_, fun hsf => ?_⟩
  · rw [hNj, hae, hce]
    push_cast
    have : ((m : ℤ) * k) ^ 2 / (k : ℤ) ^ 2 = (m : ℤ) ^ 2 := by
      rw [mul_pow, Int.mul_ediv_cancel _ (pow_ne_zero 2 (by exact_mod_cast hk.ne'))]
    rw [this]
  · have hjN : j.natAbs * j.natAbs ∣ N := by
      have : (j.natAbs : ℤ) * j.natAbs ∣ (N : ℤ) := by
        rw [hNj]; exact ⟨3 * k ^ 2 - m ^ 2, by rw [← sq, Int.natAbs_sq]⟩
      exact_mod_cast this
    have := hsf _ hjN
    rw [Nat.isUnit_iff] at this
    omega

end TriangleTiling.ThreeAlpha
