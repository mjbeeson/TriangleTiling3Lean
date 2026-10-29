/-
`theorem:isoscelesbetaexistence` (M. Beeson, *Triangle tiling: the case 3α + 2β = π*, arXiv
1206.2229v4), from Bonfioli's construction `Erdos634.BeesonThm20.beeson_thm20` (UNAUDITED).

Statement not yet checked by Beeson. Bonfioli's tiling is moved onto the given triangle `ABC`
(`transport_angles`); the area hypothesis makes the scale factor `1`.
-/
import TriangleTiling.Laczkovich.ThreeAlphaConstrBase
import Erdos634.Draft.BeesonThm20
import Erdos634.CongruentArea

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry MeasureTheory
open scoped Pointwise ENNReal

/-- Scaling by `r > 0` multiplies areas by `r²`. -/
theorem volume_scaleTri (T : Erdos634.Geometry.Tri) {r : ℝ} (hr : 0 < r) :
    volume (scaleTri T r hr.ne').carrier = ENNReal.ofReal (r ^ 2) * volume T.carrier := by
  rw [scale_carrier, Measure.addHaar_smul, finrank_euclideanSpace_fin, abs_of_pos (by positivity)]

/-- SSS, in our labelling. -/
theorem congruent_of_oppLen {T U : Erdos634.Geometry.Tri} (τ : Equiv.Perm (Fin 3)) (h : ∀ k, T.oppLen (τ k) = U.oppLen k) :
    T.Congruent U := by
  refine (Tri.congruent_relabel T τ).trans (Erdos634.SssCongruent.congruent_of_dist_three ?_ ?_ ?_)
  · have := h 2; rw [← oppLen_relabel] at this; exact this
  · have := h 0; rw [← oppLen_relabel] at this; exact this
  · have := h 1; rw [← oppLen_relabel] at this; exact this

/-- **Theorem `theorem:isoscelesbetaexistence`.** Suppose the tiling equation in
`theorem:tilingequation3` is solvable by `(M, s)`, with `0 < s < 1`. Let `(a, b, c)` be integers with
no common factor such that `s = a/c` and `c` divides `a²` (so the angles of `(a, b, c)` satisfy
`3α + 2β = π`), and let `ABC` be an isosceles triangle with base angles `β` and scaled so that its
area is equal to `N` times the area of the tile `(a, b, c)`. Suppose in addition that `a + c`
divides `M`. Then there exists an `N`-tiling of `ABC` by `(a, b, c)`.

The tile is a triangle `t` with sides `(a, b, c)` opposite its vertices `0, 1, 2`, so `β` is its
angle at `1`; `b = c - a²/c`; the base of `ABC` is `AC`. -/
theorem isoscelesbetaexistence (N M a b c : ℕ) (ha : 0 < a) (hac : a < c)
    (hg : Nat.gcd (Nat.gcd a b) c = 1) (hdiv : c ∣ a ^ 2) (hb : b = c - a ^ 2 / c) (hM : 0 < M)
    (heq : (N : ℝ) / (M : ℝ) ^ 2 = (3 - ((a : ℝ) / c) ^ 2) / (1 + (a : ℝ) / c) ^ 2)
    (hdvd : a + c ∣ M) (t : Erdos634.Geometry.Tri) (ht0 : t.oppLen 0 = a) (ht1 : t.oppLen 1 = b) (ht2 : t.oppLen 2 = c)
    (T₀ : Erdos634.Geometry.Tri) (hA : T₀.angleAt 0 = t.angleAt 1) (hC : T₀.angleAt 2 = t.angleAt 1)
    (harea : volume T₀.carrier = (N : ℝ≥0∞) * volume t.carrier) :
    ∃ D : CongruentDissection N, D.target = T₀ ∧ D.model.Congruent t := by
  have hc : 0 < c := by omega
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hcr : (0 : ℝ) < c := by exact_mod_cast hc
  have hq : a ^ 2 / c < c := by
    rw [Nat.div_lt_iff_lt_mul hc, sq]; exact Nat.mul_lt_mul'' hac hac
  have hsq : c * (a ^ 2 / c) = a ^ 2 := Nat.mul_div_cancel' hdiv
  have hb' : b + a ^ 2 / c = c := by omega
  have hb0 : 0 < b := by omega
  have hbr : (b : ℝ) = c - (a : ℝ) ^ 2 / c := by
    have h1 : ((c * (a ^ 2 / c) : ℕ) : ℝ) = (a : ℝ) ^ 2 := by exact_mod_cast hsq
    have h2 : ((b + a ^ 2 / c : ℕ) : ℝ) = c := by exact_mod_cast hb'
    push_cast at h1 h2
    field_simp; nlinarith
  -- `M = j (a + c)` and `N = j²(3c² - a²)`
  obtain ⟨j, rfl⟩ := hdvd
  have hj : 0 < j := Nat.pos_of_ne_zero (by rintro rfl; simp at hM)
  have hle : a ^ 2 ≤ 3 * c ^ 2 := by have := Nat.pow_lt_pow_left hac two_ne_zero; omega
  have hNj : N = j ^ 2 * (3 * c ^ 2 - a ^ 2) := by
    have hMr : ((a + c) * j : ℕ) ≠ (0 : ℝ) := by positivity
    rw [div_eq_iff (pow_ne_zero 2 hMr)] at heq
    have : (N : ℝ) = ((j ^ 2 * (3 * c ^ 2 - a ^ 2) : ℕ) : ℝ) := by
      rw [heq]; push_cast [hle]; field_simp; ring
    exact_mod_cast this
  subst hNj
  have hg' : Nat.gcd a (Nat.gcd b c) = 1 := by rw [← Nat.gcd_assoc]; exact hg
  obtain ⟨D₀, htg, hmd⟩ := Erdos634.BeesonThm20.beeson_thm20 a b c j ha hac hg' hdiv hb' hj
  obtain ⟨σ, m0, m1, m2⟩ := hasSides_relabel hmd
  rw [oppLen_relabel] at m0 m1 m2
  obtain ⟨hTS, h32, -, cβ⟩ := tile_of_sides D₀ σ m0 m1 m2 hbr
  set α := D₀.model.angleAt (σ 0)
  set β := D₀.model.angleAt (σ 1)
  have hα := D₀.model.angleAt_pos' (σ 0)
  have hβ := D₀.model.angleAt_pos' (σ 1)
  have hπ := Real.pi_pos
  -- `t` has angle `β` at `1`
  have htβ : t.angleAt 1 = β := by
    refine angleAt_eq_of_cos t 1 hβ.le (by linarith) ?_
    rw [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl, ht0, ht1, ht2]
    linarith
  have hcβ : Real.cos β = ((a : ℝ) ^ 2 + c ^ 2 - b ^ 2) / (2 * a * c) := by
    rw [eq_div_iff (by positivity)]; linear_combination cβ
  -- the target, relabelled with apex `B`
  obtain ⟨τ, t0, t1, t2⟩ := hasSides_relabel htg
  rw [oppLen_relabel] at t0 t1 t2
  set ρ : Equiv.Perm (Fin 3) := (Equiv.swap 1 2).trans τ
  set D₁ := relabelTarget D₀ ρ
  have hTS₁ : TileSides D₁ α β (D₀.model.angleAt (σ 2)) a b c := hTS
  have o0 : D₁.target.oppLen 0 = j * c ^ 2 := by
    rw [relabelTarget_target, oppLen_relabel, show ρ 0 = τ 0 by
      simp only [ρ, Equiv.trans_apply]; rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]]
    exact t0
  have o1 : D₁.target.oppLen 1 = j * a * (3 * c ^ 2 - a ^ 2) / c := by
    rw [relabelTarget_target, oppLen_relabel, show ρ 1 = τ 2 by simp [ρ]]; exact t2
  have o2 : D₁.target.oppLen 2 = j * c ^ 2 := by
    rw [relabelTarget_target, oppLen_relabel, show ρ 2 = τ 1 by simp [ρ]]; exact t1
  have hjr : (0 : ℝ) < j := by exact_mod_cast hj
  have B0 : D₁.target.angleAt 0 = β := by
    refine angleAt_eq_of_cos _ 0 hβ.le (by linarith) ?_
    rw [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, o0, o1, o2, hcβ, hbr]
    field_simp; ring
  have B2 : D₁.target.angleAt 2 = β := by
    refine angleAt_eq_of_cos _ 2 hβ.le (by linarith) ?_
    rw [show (2 : Fin 3) + 1 = 0 from rfl, show (2 : Fin 3) + 2 = 1 from rfl, o0, o1, o2, hcβ, hbr]
    field_simp; ring
  have hang : ∀ k, D₁.target.angleAt k = T₀.angleAt k := by
    have s1 := D₁.target.angleAt_sum
    have s2 := T₀.angleAt_sum
    intro k
    rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) k with rfl | rfl | rfl
    · rw [B0, hA, htβ]
    · rw [hA, hC, htβ] at s2; rw [B0, B2] at s1; linarith
    · rw [B2, hC, htβ]
  obtain ⟨D, r, hr, hD, hTD, hmodel⟩ := transport_angles D₁ hTS₁ T₀ hang
  -- the area forces `r = 1`
  have hcong₀ : D₀.model.Congruent t := congruent_of_oppLen σ (fun k => by
    rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) k with rfl | rfl | rfl
    · rw [m0, ht0]
    · rw [m1, ht1]
    · rw [m2, ht2])
  have hvol := Erdos634.CongruentArea.congruentDissection_volume_target D
  rw [hD, harea, hmodel, volume_scaleTri _ hr,
    show D₁.model = D₀.model from rfl, Erdos634.CongruentArea.volume_congruent hcong₀] at hvol
  have hN0 : ((j ^ 2 * (3 * c ^ 2 - a ^ 2) : ℕ) : ℝ≥0∞) ≠ 0 := by
    have h2 := Nat.pow_lt_pow_left hac two_ne_zero
    have : 0 < j ^ 2 * (3 * c ^ 2 - a ^ 2) := Nat.mul_pos (by positivity) (by omega)
    exact_mod_cast this.ne'
  rw [ENNReal.mul_right_inj hN0 (ENNReal.natCast_ne_top _)] at hvol
  have hV0 := Erdos634.Geometry.Tri.volume_pos t
  have hr1 : ENNReal.ofReal (r ^ 2) = 1 := by
    have := (ENNReal.mul_left_inj hV0.ne' (Erdos634.Geometry.Tri.volume_ne_top t)).mp
      (hvol.symm.trans (one_mul _).symm)
    exact this
  rw [ENNReal.ofReal_eq_one] at hr1
  have hr1' : r = 1 := (pow_eq_one_iff_of_nonneg hr.le two_ne_zero).mp hr1
  subst hr1'
  refine ⟨D, hD, ?_⟩
  obtain ⟨σ', -, -, -, l0, l1, l2⟩ := hTD
  refine congruent_of_oppLen σ' (fun k => ?_)
  rcases (by decide : ∀ k : Fin 3, k = 0 ∨ k = 1 ∨ k = 2) k with rfl | rfl | rfl
  · rw [l0, ht0, one_mul]
  · rw [l1, ht1, one_mul]
  · rw [l2, ht2, one_mul]

end TriangleTiling.ThreeAlpha
