/-
The tiling equation for the triquadratic shape `(2α, β, α + β)` (Section 8 of M. Beeson,
*Triangle tiling: the case 3α + 2β = π*, arXiv 1206.2229v4): `theorem:tilingequation` and
`lemma:tqprime`.

Statements not yet checked with Beeson (written 2026-10-24 while he was away); the reading choices
are listed in the PR.
-/
import TriangleTiling.Laczkovich.ThreeAlphaTriquadratic
import Erdos634.Draft.BeesonRowL36
import Erdos634.Draft.BeesonRow2Arith

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles)
open Erdos634.BeesonColoring

variable {N : ℕ} (D : CongruentDissection N)

/-- If `ABC` is similar to the tile, every angle of `ABC` is one of the tile's. -/
theorem angles_of_similar {α β γ a b c : ℝ} (hT : TileSides D α β γ a b c) (hs : SimilarTM D)
    (k : Fin 3) : D.target.angleAt k = α ∨ D.target.angleAt k = β ∨ D.target.angleAt k = γ := by
  obtain ⟨μ, τ, hτ⟩ := hs
  obtain ⟨σ, h0, h1, h2, -⟩ := hT
  rw [(hτ k).1]
  obtain ⟨m, hm⟩ := σ.surjective (τ k)
  rw [← hm]
  fin_cases m
  · exact Or.inl h0
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr h2)

/-- A triangle with an angle `α + β` is not similar to the tile. -/
theorem not_similar_of_alpha_beta {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) {k : Fin 3} (hk : D.target.angleAt k = α + β) :
    ¬ SimilarTM D := by
  intro hs
  obtain ⟨hα, hβ, hγ, -⟩ := model_facts D hrel hT
  rcases angles_of_similar D hT hs k with e | e | e <;> rw [hk] at e <;> linarith

/-- **Theorem `theorem:tilingequation`** (necessary condition for a tiling). Let `3α + 2β = π` and
let `ABC` have angles `(2α, β, α + β)` and be `N`-tiled by a tile with angles `α` and `β`. Then

(i) `M² + N = 2K²` for some positive integers `M` and `K` with `M² < N`, where
`s = 2 sin (α/2) = M/K`; and

(ii) the squarefree part of `N` is a product of distinct primes of the form `8n ± 1`, possibly
times `2`.

(ii) is stated as: `N = r² q` with `q` squarefree and every prime factor of `q` equal to `2` or
`≡ ±1 (mod 8)`. -/
theorem tilingequation {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hshape : TgtAngles D (2 * α) β (α + β)) :
    (∃ M K : ℕ, 0 < M ∧ 0 < K ∧ M ^ 2 + N = 2 * K ^ 2 ∧ M ^ 2 < N ∧
      2 * Real.sin (α / 2) = M / K) ∧
    (∃ r q : ℕ, N = r ^ 2 * q ∧ Squarefree q ∧
      ∀ p : ℕ, p.Prime → p ∣ q → p = 2 ∨ p % 8 = 1 ∨ p % 8 = 7) := by
  have hns : ¬ SimilarTM D := by
    obtain ⟨σ, -, -, h2⟩ := hshape
    exact not_similar_of_alpha_beta D hrel hT h2
  obtain ⟨D', hm, hns', hccw, e0, e1, e2⟩ := normalize D hshape hns
  have hT' := tileSides_of_model D hm hT
  obtain ⟨-, -, -, M₁, M₂, -, -, -, -, -, -, h₁, h₂⟩ := Mdef D' hrel hT' hns'
  obtain ⟨hsq, -, -, -, hlt⟩ := tqsquare D' hrel hT' hns' hccw h₁ h₂ ⟨e0, e1, e2⟩
  obtain ⟨-, k, hk⟩ := tqrational D' hrel hT' hns' hccw h₁ h₂ ⟨e0, e1, e2⟩
  have m1 := (M1M2 D' hrel hT' hns' hccw h₁ h₂).1
  dsimp only at m1
  obtain ⟨eM, -⟩ := m1 ⟨e0, e1, e2⟩
  obtain ⟨-, -, -, -, hc, ha, -, ht0, -, -, -⟩ := model_facts D' hrel hT'
  have hst : a / c = 2 * Real.cos (α + β) := by rw [ha]; field_simp
  have hΛ : 0 < Lam D' := div_pos (circumdiam_pos _) (circumdiam_pos _)
  have hM0 : 0 < M₁ := by
    have : (0 : ℝ) < M₁ := by rw [eM, hst]; positivity
    exact_mod_cast this
  -- `2(N + M²) = k²`, so `k = 2K`.
  set M := M₁.toNat
  have hMM : (M : ℤ) = M₁ := Int.toNat_of_nonneg hM0.le
  set k' := k.natAbs
  have hk' : (k' : ℤ) ^ 2 = 2 * ((N : ℤ) + M₁ ^ 2) := by rw [Int.natAbs_sq]; exact hk.symm
  have hkeven : Even k' := by
    have : Even ((k' : ℤ) ^ 2) := ⟨(N : ℤ) + M₁ ^ 2, by rw [hk']; ring⟩
    have := (Int.even_pow' two_ne_zero).mp this
    exact_mod_cast this
  obtain ⟨K, hK⟩ := hkeven
  have hKeq : M ^ 2 + N = 2 * K ^ 2 := by
    have : ((M ^ 2 + N : ℕ) : ℤ) = ((2 * K ^ 2 : ℕ) : ℤ) := by
      push_cast; rw [hMM]
      have := hk'; rw [show (k' : ℤ) = 2 * K by rw [hK]; push_cast; ring] at this
      linarith
    exact_mod_cast this
  have hMpos : 0 < M := by omega
  have hNlt : M ^ 2 < N := by
    have : ((M ^ 2 : ℕ) : ℤ) < N := by push_cast; rw [hMM]; exact hlt
    exact_mod_cast this
  have hKpos : 0 < K := by
    by_contra h0; push Not at h0; interval_cases K; omega
  refine ⟨⟨M, K, hMpos, hKpos, hKeq, hNlt, ?_⟩,
    Erdos634.BeesonRow.lemma36 N M K (by omega) (by exact_mod_cast (by omega : N + M ^ 2 = 2 * K ^ 2))⟩
  -- `2 sin (α/2) = a/c = M/K`.
  have hsin : 2 * Real.sin (α / 2) = a / c := by
    rw [hst, show α + β = Real.pi / 2 - α / 2 by linarith, Real.cos_pi_div_two_sub]
  rw [hsin]
  have hKR : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hsq' : (a / c) ^ 2 = ((M : ℝ) / K) ^ 2 := by
    rw [hsq, div_pow]
    have : (N : ℝ) + (M₁ : ℝ) ^ 2 = 2 * (K : ℝ) ^ 2 := by
      rw [← hMM]; push_cast
      have := hKeq; exact_mod_cast (by omega : N + M ^ 2 = 2 * K ^ 2)
    rw [this, ← hMM]; push_cast; field_simp
  have hpos1 : 0 < a / c := by rw [hst]; exact ht0
  have hpos2 : (0 : ℝ) ≤ M / K := by positivity
  exact (sq_eq_sq₀ hpos1.le hpos2).mp hsq'

/-- **Lemma `lemma:tqprime`.** If a triquadratic triangle is tiled by `N` copies of `T` and `N` is
prime, then `N ≡ ±1 (mod 8)`. Moreover `m` is odd, and `k` is even or odd according as
`N ≡ -1` or `N ≡ 1 (mod 8)`. Here `(a, b, c) = τ(mk, k² - m², k²)` as in
`corollary:tqparameters`. -/
theorem tqprime {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hshape : TgtAngles D (2 * α) β (α + β))
    {τ : ℝ} {m k : ℕ} (hτ : 0 < τ) (hmk : Nat.Coprime m k) (hlt : m < k)
    (ha : a = τ * (m * k)) (hb : b = τ * (k ^ 2 - m ^ 2)) (hc : c = τ * k ^ 2) (hN : N.Prime) :
    (N % 8 = 1 ∨ N % 8 = 7) ∧ Odd m ∧ (Even k ↔ N % 8 = 7) := by
  have hns : ¬ SimilarTM D := by
    obtain ⟨σ, -, -, h2⟩ := hshape
    exact not_similar_of_alpha_beta D hrel hT h2
  obtain ⟨D', hm, hns', hccw, e0, e1, e2⟩ := normalize D hshape hns
  have hT' := tileSides_of_model D hm hT
  obtain ⟨-, -, -, M₁, M₂, -, -, -, -, -, -, h₁, h₂⟩ := Mdef D' hrel hT' hns'
  obtain ⟨hdvd, hNj, hMj, -, -, -, -⟩ :=
    tqparameters D' hrel hT' hns' hccw h₁ h₂ ⟨e0, e1, e2⟩ hτ hmk hlt ha hb hc
  set j := M₁ / (m : ℤ)
  have hm0 : 0 < m := by
    obtain ⟨-, -, -, -, hc0, ha', -, ht0, -, -, -⟩ := model_facts D' hrel hT'
    by_contra h0; push Not at h0
    have : m = 0 := by omega
    subst this
    have : a = 0 := by rw [ha]; simp
    rw [ha'] at this
    have : 2 * Real.cos (α + β) * c > 0 := by positivity
    linarith
  -- `j = 1`, by `lemma:primeimpliesjone`.
  have hj1 : j.natAbs = 1 := by
    apply primeimpliesjone j.natAbs m k (j.natAbs * m) (j.natAbs * k) N rfl rfl
    · have : 0 < j.natAbs := by
        rcases Int.natAbs_pos.mpr (show j ≠ 0 from fun h0 => by
          rw [h0, zero_pow two_ne_zero, zero_mul] at hNj; exact hN.ne_zero (by exact_mod_cast hNj))
          with h; exact h
      positivity
    · have hk : (k : ℤ) ^ 2 ≥ m ^ 2 := by nlinarith
      have : ((N + (j.natAbs * m) ^ 2 : ℕ) : ℤ) = ((2 * (j.natAbs * k) ^ 2 : ℕ) : ℤ) := by
        push_cast; rw [mul_pow, mul_pow, sq_abs, hNj]; ring
      exact_mod_cast this
    · exact hN
  have hj2 : j ^ 2 = 1 := by rw [← Int.natAbs_sq, hj1]; rfl
  have hNmk : N + m ^ 2 = 2 * k ^ 2 := by
    have : ((N + m ^ 2 : ℕ) : ℤ) = ((2 * k ^ 2 : ℕ) : ℤ) := by push_cast; rw [hNj, hj2]; ring
    exact_mod_cast this
  obtain ⟨hmodd, hcase⟩ := Erdos634.BeesonRow2.lemma46 N m k hN hm0 hlt hNmk
  refine ⟨by omega, Nat.odd_iff.mpr hmodd, ?_⟩
  rw [Nat.even_iff]
  omega

end TriangleTiling.ThreeAlpha
