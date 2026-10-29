/-
`lemma:complementary` (M. Beeson, *Triangle tiling: the case 3α + 2β = π*, arXiv 1206.2229v4):
which of the two isosceles constructions applies to a rational tile.

Statement not yet checked by Beeson. The lemma is algebra in `a, b, c` given `b = c - a²/c` (the
form of `3α + 2β = π`, `lemma:anglesOK`); the Lean statement takes only that relation, with
`b, c > 0`. `x₀` is any real root of `x³ = (1 - x)²` (there is exactly one).
-/
import Mathlib

namespace TriangleTiling.ThreeAlpha

/-- `x³ - x² + 2x - 1` has no rational root. -/
theorem no_rat_root (q : ℚ) : q ^ 3 - q ^ 2 + 2 * q - 1 ≠ 0 := by
  intro h
  have hq := Rat.num_div_den q
  set n := q.num
  set d := q.den
  have hd : (d : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
  have hz : (n : ℚ) ^ 3 = d * (n ^ 2 - 2 * n * d + d ^ 2) := by
    rw [← hq] at h; field_simp at h; linear_combination h
  have hz' : n ^ 3 = (d : ℤ) * (n ^ 2 - 2 * n * d + d ^ 2) := by exact_mod_cast hz
  have hdvd : d ∣ n.natAbs ^ 3 := by
    have : (d : ℤ) ∣ n ^ 3 := ⟨_, hz'⟩
    have := Int.natAbs_dvd_natAbs.mpr this
    simpa [Int.natAbs_pow] using this
  have hd1 : d = 1 := Nat.Coprime.eq_one_of_dvd ((q.reduced.symm).pow_right 3) hdvd
  rw [hd1] at hz'
  have h1 : n * (n ^ 2 - n + 2) = 1 := by linear_combination hz'
  rcases Int.eq_one_or_neg_one_of_mul_eq_one h1 with e | e <;> rw [e] at h1 <;> norm_num at h1

/-- `x³ - x² + 2x - 1` is strictly increasing. -/
theorem f_strictMono : StrictMono fun x : ℝ => x ^ 3 - x ^ 2 + 2 * x - 1 := by
  intro x y hxy
  simp only
  nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x + y - 1), sq_nonneg x, sq_nonneg y,
    mul_pos (sub_pos.mpr hxy) (sub_pos.mpr hxy)]

/-- **Lemma `lemma:complementary`.** Let `(a, b, c)` be a tile with `3α + 2β = π` and
`b = c - a²/c`. Then `b(a² + b²) - a²c = -(c³ - 2bc² + b²c - b³)`, and if `b/c` is rational,
neither side is zero. Hence for every rational tile exactly one of the following holds:
(i) `c + b²/c < a²/b + b`, the condition for Laczkovich's construction (equivalently `b/c < x₀`);
(ii) `a²c < b(a² + b²)` (equivalently `b/c > x₀`), where `x₀ ≈ 0.5698` is the real root of
`x³ = (1 - x)²`. -/
theorem complementary {a b c : ℝ} (hb0 : 0 < b) (hc : 0 < c) (hb : b = c - a ^ 2 / c) :
    b * (a ^ 2 + b ^ 2) - a ^ 2 * c = -(c ^ 3 - 2 * b * c ^ 2 + b ^ 2 * c - b ^ 3) ∧
    ((∃ q : ℚ, b / c = q) → b * (a ^ 2 + b ^ 2) - a ^ 2 * c ≠ 0) ∧
    ((∃ q : ℚ, b / c = q) →
      Xor (c + b ^ 2 / c < a ^ 2 / b + b) (a ^ 2 * c < b * (a ^ 2 + b ^ 2))) ∧
    ∀ x₀ : ℝ, x₀ ^ 3 = (1 - x₀) ^ 2 →
      ((c + b ^ 2 / c < a ^ 2 / b + b ↔ b / c < x₀) ∧
        (a ^ 2 * c < b * (a ^ 2 + b ^ 2) ↔ x₀ < b / c)) := by
  have ha2 : a ^ 2 = c * (c - b) := by rw [hb]; field_simp; ring
  have hid : b * (a ^ 2 + b ^ 2) - a ^ 2 * c = -(c ^ 3 - 2 * b * c ^ 2 + b ^ 2 * c - b ^ 3) := by
    rw [ha2]; ring
  -- With `x = b/c`: `c³ - 2bc² + b²c - b³ = -c³ f(x)`, `f(x) = x³ - x² + 2x - 1`.
  set x := b / c with hx
  have hbx : b = x * c := by rw [hx]; field_simp
  have hE : c ^ 3 - 2 * b * c ^ 2 + b ^ 2 * c - b ^ 3 = -(c ^ 3 * (x ^ 3 - x ^ 2 + 2 * x - 1)) := by
    rw [hbx]; ring
  -- (i) is `0 < c³ - 2bc² + b²c - b³`, (ii) is the reverse.
  have hi : c + b ^ 2 / c < a ^ 2 / b + b ↔ x ^ 3 - x ^ 2 + 2 * x - 1 < 0 := by
    rw [div_add' _ _ _ hb0.ne', add_div' _ _ _ hc.ne', div_lt_div_iff₀ hc hb0, ha2]
    have hc3 : 0 < c ^ 3 := by positivity
    constructor
    · intro h
      have : 0 < c ^ 3 - 2 * b * c ^ 2 + b ^ 2 * c - b ^ 3 := by nlinarith
      rw [hE] at this; nlinarith
    · intro h
      have : 0 < c ^ 3 - 2 * b * c ^ 2 + b ^ 2 * c - b ^ 3 := by rw [hE]; nlinarith
      nlinarith
  have hii : a ^ 2 * c < b * (a ^ 2 + b ^ 2) ↔ 0 < x ^ 3 - x ^ 2 + 2 * x - 1 := by
    have hc3 : 0 < c ^ 3 := by positivity
    rw [← sub_pos, hid, hE, neg_neg]
    exact ⟨fun h => pos_of_mul_pos_right h hc3.le, fun h => mul_pos hc3 h⟩
  have hrat : (∃ q : ℚ, b / c = q) → x ^ 3 - x ^ 2 + 2 * x - 1 ≠ 0 := by
    rintro ⟨q, hq⟩ h
    rw [← hx] at hq; rw [hq] at h
    exact no_rat_root q (by exact_mod_cast h)
  refine ⟨hid, fun h => ?_, fun h => ?_, fun x₀ h0 => ?_⟩
  · rw [hid, hE, neg_neg]
    exact mul_ne_zero (by positivity) (hrat h)
  · rw [hi, hii]
    rcases lt_or_gt_of_ne (hrat h) with h' | h'
    · exact Or.inl ⟨h', not_lt.mpr h'.le⟩
    · exact Or.inr ⟨h', not_lt.mpr h'.le⟩
  · have hf0 : x₀ ^ 3 - x₀ ^ 2 + 2 * x₀ - 1 = 0 := by rw [h0]; ring
    rw [hi, hii]
    constructor
    · rw [← hf0]; exact f_strictMono.lt_iff_lt
    · rw [← hf0]; exact f_strictMono.lt_iff_lt

end TriangleTiling.ThreeAlpha
