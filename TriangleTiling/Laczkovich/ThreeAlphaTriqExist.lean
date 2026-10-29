/-
`theorem:triquadraticexistence` (M. Beeson, *Triangle tiling: the case 3α + 2β = π*, arXiv
1206.2229v4), from Bonfioli's construction `Erdos634.BeesonThm11.beeson_thm11` (UNAUDITED).

Statement not yet checked by Beeson. The tiling is Bonfioli's; this file relabels its target as
`A, B, C` (vertices `0, 1, 2`) and derives the angle conclusions from the side lengths.
-/
import TriangleTiling.Laczkovich.ThreeAlphaConstrBase
import Erdos634.Draft.BeesonThm11

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry

/-- **Theorem `theorem:triquadraticexistence`.** Let `N` be given. Suppose `M² + N = 2K²` with
`M² < N` and suppose `K` divides `N`. Let `ABC` be the triangle with sides `BC = MN/K`,
`AC = N - K²`, and `AB = K²`, and let the triangle `T` have sides `a = M`, `b = N/K - K`, and
`c = K`. Then there is an `N`-tiling of triangle `ABC` by tile `T`. This tile satisfies
`3α + 2β = π`, and `ABC` has angles `(2α, β, α + β)`.

`M > 0` is a hypothesis (implicit in the paper: `a = M` is a side). -/
theorem triquadraticexistence (M N K : ℕ) (hM : 0 < M) (h : M ^ 2 + N = 2 * K ^ 2)
    (hlt : M ^ 2 < N) (hdiv : K ∣ N) :
    ∃ D : CongruentDissection N,
      D.target.oppLen 0 = (M : ℝ) * N / K ∧ D.target.oppLen 1 = (N : ℝ) - K ^ 2 ∧
      D.target.oppLen 2 = (K : ℝ) ^ 2 ∧
      ∃ α β γ : ℝ, TileSides D α β γ M ((N : ℝ) / K - K) K ∧ 3 * α + 2 * β = Real.pi ∧
        D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β := by
  obtain ⟨D, ht, hm⟩ := Erdos634.BeesonThm11.beeson_thm11 M N K hM h hlt hdiv
  obtain ⟨τ, t0, t1, t2⟩ := hasSides_relabel ht
  obtain ⟨σ, m0, m1, m2⟩ := hasSides_relabel hm
  rw [oppLen_relabel] at t0 t1 t2 m0 m1 m2
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hh : (M : ℝ) ^ 2 + N = 2 * K ^ 2 := by exact_mod_cast h
  have hl : (M : ℝ) ^ 2 < N := by exact_mod_cast hlt
  have hK : (0 : ℝ) < K := by
    rcases Nat.eq_zero_or_pos K with h0 | h0
    · subst h0; simp at h; omega
    · exact_mod_cast h0
  have hKN : (K : ℝ) ^ 2 < N := by nlinarith
  have hb : (0 : ℝ) < N / K - K := by
    rw [sub_pos, lt_div_iff₀ hK]; nlinarith
  have hrel : (N / K - K : ℝ) = K - (M : ℝ) ^ 2 / K := by
    field_simp; linarith
  obtain ⟨hTS, h32, cα, cβ⟩ := tile_of_sides D σ m0 m1 m2 hrel
  set α := D.model.angleAt (σ 0)
  set β := D.model.angleAt (σ 1)
  have hα := D.model.angleAt_pos' (σ 0)
  have hβ := D.model.angleAt_pos' (σ 1)
  set ρ : Equiv.Perm (Fin 3) := (Equiv.swap 0 1).trans τ
  have o0 : (relabelTarget D ρ).target.oppLen 0 = (M : ℝ) * N / K := by
    rw [relabelTarget_target, oppLen_relabel, show ρ 0 = τ 1 by simp [ρ]]; exact t1
  have o1 : (relabelTarget D ρ).target.oppLen 1 = (N : ℝ) - K ^ 2 := by
    rw [relabelTarget_target, oppLen_relabel, show ρ 1 = τ 0 by simp [ρ]]; exact t0
  have o2 : (relabelTarget D ρ).target.oppLen 2 = (K : ℝ) ^ 2 := by
    rw [relabelTarget_target, oppLen_relabel, show ρ 2 = τ 2 by
      simp only [ρ, Equiv.trans_apply]; rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]]
    exact t2
  set T := (relabelTarget D ρ).target
  -- `cos α` and `cos β` from the sides of the tile.
  have hcα : Real.cos α = (((N : ℝ) / K - K) ^ 2 + K ^ 2 - M ^ 2) / (2 * ((N : ℝ) / K - K) * K) := by
    rw [eq_div_iff (mul_pos (mul_pos two_pos hb) hK).ne']; linear_combination cα
  have hcβ : Real.cos β = ((K : ℝ) ^ 2 + M ^ 2 - ((N : ℝ) / K - K) ^ 2) / (2 * K * M) := by
    rw [eq_div_iff (mul_pos (mul_pos two_pos hK) hMr).ne']; linear_combination cβ
  have hN : (N : ℝ) = 2 * K ^ 2 - M ^ 2 := by linarith
  have hKM : (K : ℝ) ^ 2 - M ^ 2 ≠ 0 := (by nlinarith : (0 : ℝ) < K ^ 2 - M ^ 2).ne'
  have hbK : (N : ℝ) / K - K = (K ^ 2 - M ^ 2) / K := by rw [hN]; field_simp; ring
  have A0 : T.angleAt 0 = 2 * α := by
    refine angleAt_eq_of_cos T 0 (by linarith) (by linarith) ?_
    rw [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, o0, o1, o2,
      Real.cos_two_mul, hcα, hbK, hN]
    field_simp
    ring
  have A1 : T.angleAt 1 = β := by
    refine angleAt_eq_of_cos T 1 hβ.le (by linarith) ?_
    rw [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl, o0, o1, o2, hcβ, hbK, hN]
    field_simp
    ring
  have A2 : T.angleAt 2 = α + β := by
    have := T.angleAt_sum
    rw [A0, A1] at this
    linarith
  exact ⟨relabelTarget D ρ, o0, o1, o2, α, β, _, hTS, h32, A0, A1, A2⟩

/-- **Theorem `theorem:jshape`.** Let triangle `ABC` have the angles `(2α, β, α + β)`, and let
`s = 2 sin(α/2)`. Suppose `M` and `K` are positive integers such that `s = M/K` (not necessarily in
lowest terms). Then there is a tiling of `ABC` using a tile similar to `(α, β, γ)`, and the number
of tiles is a square times `2K² - M²`.

`3α + 2β = π` is the paper's standing assumption; `γ = 2α + β`. -/
theorem jshape {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (T₀ : Erdos634.Geometry.Tri)
    (hA : T₀.angleAt 0 = 2 * α) (hB : T₀.angleAt 1 = β) (hC : T₀.angleAt 2 = α + β)
    (M K : ℕ) (hM : 0 < M) (hK : 0 < K) (hs : 2 * Real.sin (α / 2) = (M : ℝ) / K) :
    ∃ (N : ℕ) (D : CongruentDissection N), D.target = T₀ ∧
      (∃ a b c : ℝ, TileSides D α β (2 * α + β) a b c) ∧ ∃ t : ℕ, N = t ^ 2 * (2 * K ^ 2 - M ^ 2) := by
  have hπ := Real.pi_pos
  have hα : 0 < α := by have := T₀.angleAt_pos' 0; linarith
  have hβ : 0 < β := by have := T₀.angleAt_pos' 1; linarith
  have hα3 : α < Real.pi / 3 := by linarith
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  -- `s < 1`, so `M < K`.
  have hlt : M < K := by
    have h1 : Real.sin (α / 2) < 1 / 2 := by
      rw [← Real.sin_pi_div_six]
      exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
    have : (M : ℝ) / K < 1 := by rw [← hs]; linarith
    rw [div_lt_one hKr] at this
    exact_mod_cast this
  have hMK : M ^ 2 < K ^ 2 := Nat.pow_lt_pow_left hlt two_ne_zero
  have hle : M ^ 2 ≤ 2 * K ^ 2 := by omega
  have h1 : (M * K) ^ 2 + K ^ 2 * (2 * K ^ 2 - M ^ 2) = 2 * (K ^ 2) ^ 2 := by
    zify [hle]; ring
  have h2 : (M * K) ^ 2 < K ^ 2 * (2 * K ^ 2 - M ^ 2) := by
    zify [hle]
    have : (M : ℤ) ^ 2 < K ^ 2 := by exact_mod_cast hMK
    have hK2 : (0 : ℤ) < K ^ 2 := by positivity
    nlinarith
  obtain ⟨D, -, -, -, α', β', γ', hTS, h32, A0, A1, A2⟩ :=
    triquadraticexistence (M * K) (K ^ 2 * (2 * K ^ 2 - M ^ 2)) (K ^ 2) (by positivity) h1 h2
      (dvd_mul_right _ _)
  obtain ⟨hα', hβ', hγ', -⟩ := model_facts D h32 hTS
  have heq : α' = α := by
    have := s_eq h32 hTS
    push_cast at this
    rw [show (M : ℝ) * K / K ^ 2 = M / K by field_simp, ← hs] at this
    exact alpha_eq_of_sin hα' (by linarith) hα hα3 this.symm
  subst heq
  have hβeq : β' = β := by linarith
  subst hβeq
  subst hγ'
  obtain ⟨D', r, -, hD', hT', -⟩ := transport_angles D hTS T₀ (fun k => by
    rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) k with rfl | rfl | rfl
    · rw [A0, hA]
    · rw [A1, hB]
    · rw [A2, hC])
  exact ⟨_, D', hD', ⟨_, _, _, hT'⟩, K, rfl⟩

end TriangleTiling.ThreeAlpha
