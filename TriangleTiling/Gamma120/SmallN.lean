/-
`theorem:smallN120` (Section 11 of M. Beeson, *Tilings of an isosceles triangle*): an `N`-tiling
of an isosceles triangle with base angles `α` (`α ∉ ℚπ`) by `(α, β, 2π/3)` has `N ≥ 33`, and for
`N ≤ 200` the tile `(a, b, c)` and the side and base `(X, Y)` of `ABC` are as in the paper's
Table `isosceles120`.

The paper computes the table by a short search over the conditions of `lemma:2b+adividesN`. Here
the same search is the Boolean function `tableCheck`, evaluated by the kernel (`decide +kernel`,
no `native_decide`): for each `N ≤ 200`, each divisor `d = 2b + a` of `N` and each `b`, it computes
`c = √(a² + b² + ab)` and `m = √(N b / d)` by a verified integer square root (`isqrt`), and checks
that every solution with `gcd(a, b, c) = 1` is in the table.
-/
import TriangleTiling.Gamma120.Possible

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry

/-! ### A verified integer square root -/

/-- Binary search for the integer square root, with fuel. -/
def sqrtAux : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0, _, lo, _ => lo
  | f + 1, n, lo, hi =>
    if hi ≤ lo + 1 then lo else
      if (lo + hi) / 2 * ((lo + hi) / 2) ≤ n then sqrtAux f n ((lo + hi) / 2) hi
      else sqrtAux f n lo ((lo + hi) / 2)

/-- The integer square root (for `n < 2⁶⁴`). -/
def isqrt (n : ℕ) : ℕ := sqrtAux 64 n 0 (n + 1)

theorem sqrtAux_spec : ∀ (f n lo hi : ℕ), lo * lo ≤ n → n < hi * hi → lo < hi →
    hi ≤ lo + 2 ^ f →
    sqrtAux f n lo hi * sqrtAux f n lo hi ≤ n ∧
      n < (sqrtAux f n lo hi + 1) * (sqrtAux f n lo hi + 1)
  | 0, n, lo, hi, h1, h2, h3, h4 => by
    have : hi = lo + 1 := by simp at h4; omega
    subst this
    exact ⟨h1, h2⟩
  | f + 1, n, lo, hi, h1, h2, h3, h4 => by
    rw [pow_succ] at h4
    unfold sqrtAux
    split_ifs with hh hm
    · have : hi = lo + 1 := by omega
      subst this
      exact ⟨h1, h2⟩
    · exact sqrtAux_spec f n _ hi hm h2 (by omega) (by omega)
    · push Not at hm
      exact sqrtAux_spec f n lo _ h1 hm (by omega) (by omega)

/-- `isqrt (c²) = c`. -/
theorem isqrt_eq {c v : ℕ} (hc : c * c = v) (hv : v + 1 ≤ 2 ^ 64) : isqrt v = c := by
  obtain ⟨h1, h2⟩ := sqrtAux_spec 64 v 0 (v + 1) (by simp) (by nlinarith) (by omega) (by omega)
  have hle : isqrt v ≤ c := Nat.mul_self_le_mul_self_iff.mp (hc ▸ h1)
  have hlt : c < isqrt v + 1 := Nat.mul_self_lt_mul_self_iff.mp (hc ▸ h2)
  omega

/-! ### The table -/

/-- Table `isosceles120` of the paper: `(N, a, b, c, X, Y)`. -/
def table120 : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [(33, 5, 3, 7, 21, 33), (37, 5, 16, 19, 76, 148), (46, 7, 8, 13, 52, 92),
   (65, 3, 5, 7, 35, 65), (71, 39, 16, 49, 196, 284), (74, 56, 9, 61, 183, 222),
   (130, 16, 5, 19, 95, 130), (132, 5, 3, 7, 42, 66), (148, 5, 16, 19, 152, 296),
   (154, 8, 7, 13, 91, 154), (184, 7, 8, 13, 104, 184), (193, 143, 25, 157, 785, 965)]

/-- The check for one `N`, one `d = 2b + a` and one `b`. -/
def cellOK (N d b : ℕ) : Bool :=
  !(0 < b && 2 * b < d) ||
    !(isqrt ((d - 2 * b) * (d - 2 * b) + b * b + (d - 2 * b) * b) *
        isqrt ((d - 2 * b) * (d - 2 * b) + b * b + (d - 2 * b) * b) ==
      (d - 2 * b) * (d - 2 * b) + b * b + (d - 2 * b) * b) ||
    !(Nat.gcd (Nat.gcd (d - 2 * b) b)
        (isqrt ((d - 2 * b) * (d - 2 * b) + b * b + (d - 2 * b) * b)) == 1) ||
    !(N * b == d * (isqrt (N / d * b) * isqrt (N / d * b))) ||
    table120.contains (N, d - 2 * b, b,
      isqrt ((d - 2 * b) * (d - 2 * b) + b * b + (d - 2 * b) * b),
      isqrt (N / d * b) * isqrt ((d - 2 * b) * (d - 2 * b) + b * b + (d - 2 * b) * b),
      isqrt (N / d * b) * d)

/-- The search over all `N < K`. -/
def tableCheck (K : ℕ) : Bool :=
  (List.range K).all fun N => (List.range (N + 1)).all fun d =>
    !(N % d == 0) || (List.range d).all fun b => cellOK N d b

theorem tableCheck201 : tableCheck 201 = true := by decide +kernel

/-- **The table is complete**: every solution of the conditions of `lemma:2b+adividesN` with
`N ≤ 200` and `gcd(a, b, c) = 1` is in Table `isosceles120`. -/
theorem table120_complete {N a b c m : ℕ} (hN : N ≤ 200) (ha : 0 < a) (hb : 0 < b) (hm : 0 < m)
    (hcop : Nat.gcd (Nat.gcd a b) c = 1) (hcab : c ^ 2 = a ^ 2 + b ^ 2 + a * b)
    (hdvd : (2 * b + a) ∣ N) (hNb : N * b = (2 * b + a) * m ^ 2) :
    (N, a, b, c, m * c, m * (2 * b + a)) ∈ table120 := by
  set d := 2 * b + a with hd
  have hd0 : 0 < d := by omega
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · rw [h, zero_mul] at hNb
      have : 0 < d * m ^ 2 := by positivity
      omega
    · exact h
  have hdN : d ≤ N := Nat.le_of_dvd hN0 hdvd
  obtain ⟨e, he⟩ := hdvd
  have hda : d - 2 * b = a := by omega
  have hb200 : b ≤ 200 := by omega
  have ha200 : a ≤ 200 := by omega
  have hc : isqrt (a * a + b * b + a * b) = c :=
    isqrt_eq (by rw [← sq, hcab]; ring) (by nlinarith)
  have heb : e * b = m * m := by
    apply Nat.eq_of_mul_eq_mul_left hd0
    rw [← mul_assoc, ← he, hNb]; ring
  have he200 : e ≤ 200 := by
    have : 1 ≤ d := hd0
    nlinarith
  have hNd : N / d * b = m * m := by rw [he, Nat.mul_div_cancel_left _ hd0, heb]
  have hmq : isqrt (N / d * b) = m := isqrt_eq hNd.symm (by rw [hNd, ← heb]; nlinarith)
  have h := tableCheck201
  simp only [tableCheck, List.all_eq_true, List.mem_range] at h
  have h2 := h N (by omega) d (by omega)
  have hmod : N % d = 0 := by rw [he]; simp
  simp only [hmod, beq_self_eq_true, Bool.not_true, Bool.false_or, List.all_eq_true,
    List.mem_range] at h2
  have h3 := h2 b (by omega)
  simp only [cellOK, hda, hc, hmq, hcop] at h3
  have hcc : c * c = a * a + b * b + a * b := by rw [← sq, hcab]; ring
  have hNb' : N * b = d * (m * m) := by rw [hNb]; ring
  simp only [hb, show 2 * b < d by omega, decide_true, Bool.and_self, Bool.not_true, hcc,
    beq_self_eq_true, Bool.false_or, hNb'] at h3
  simpa [List.contains_iff_mem, mul_comm] using h3

variable {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * Real.pi / 3)
  (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
  (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D)
  (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D)
include hγ hirr hA hC

/-- **Theorem `theorem:smallN120`.** `N ≥ 33`; and if `N ≤ 200`, then after scaling the tile is
`(a, b, c)` and `ABC` has side `X` and base `Y` with `(N, a, b, c, X, Y)` in Table
`isosceles120`. -/
theorem smallN120 : 33 ≤ N ∧ (N ≤ 200 → ∃ (κ : ℝ) (hκ : κ ≠ 0) (a b c X Y : ℕ),
    dist ((CongruentDissection.scale D κ hκ).model.pts 1)
      ((CongruentDissection.scale D κ hκ).model.pts 2) = a ∧
    dist ((CongruentDissection.scale D κ hκ).model.pts 2)
      ((CongruentDissection.scale D κ hκ).model.pts 0) = b ∧
    dist ((CongruentDissection.scale D κ hκ).model.pts 0)
      ((CongruentDissection.scale D κ hκ).model.pts 1) = c ∧
    dist ((CongruentDissection.scale D κ hκ).target.pts 0)
      ((CongruentDissection.scale D κ hκ).target.pts 1) = X ∧
    dist ((CongruentDissection.scale D κ hκ).target.pts 0)
      ((CongruentDissection.scale D κ hκ).target.pts 2) = Y ∧
    (N, a, b, c, X, Y) ∈ table120) := by
  obtain ⟨κ, hκ, a, b, c, m, ha, hb, hc, hcop, ha0, hb0, hm0, hcab, hdvd, hNb, hX, hY⟩ :=
    possibletiles120 D hγ hirr hA hC
  have hmem : N ≤ 200 → (N, a, b, c, m * c, m * (2 * b + a)) ∈ table120 := fun h =>
    table120_complete h ha0 hb0 hm0 hcop hcab hdvd hNb
  refine ⟨?_, fun h => ⟨κ, hκ, a, b, c, m * c, m * (2 * b + a), ha, hb, hc,
    by rw [hX]; push_cast; ring, by rw [hY]; push_cast; ring, hmem h⟩⟩
  by_contra hlt
  have := hmem (by omega)
  simp [table120] at this
  omega

end TriangleTiling
