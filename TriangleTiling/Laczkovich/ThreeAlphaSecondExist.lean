/-
Tilings of the triangle with angles `(2α, α, 2β)` (M. Beeson, *Triangle tiling: the case
3α + 2β = π*, arXiv 1206.2229v4): `theorem:existence2`, the converse of
`theorem:secondcasesolution`, `corollary:existence2case2`, `corollary:secondshapeall`.

Statements not yet checked by Beeson. The tilings are Bonfioli's (`Erdos634.BeesonT15Conv`,
`Erdos634.BeesonCor6`, UNAUDITED). This file relabels the target as `A, B, C`, derives the
angles from the side lengths, and computes `M` from `theorem:secondtilingequation` and
`theorem:coloring`: `M` is the sum of any proper colouring with a black tile at `B` (on `AB`).
-/
import TriangleTiling.Laczkovich.ThreeAlphaConstrBase
import TriangleTiling.Laczkovich.ThreeAlphaSecond
import Erdos634.Draft.BeesonT15Conv
import Erdos634.Draft.BeesonCor6
import TriangleTiling.Laczkovich.ThreeAlphaTriquadratic

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional
open Erdos634.Draft.LaczFormal (TileAngles)
open Erdos634.BeesonColoring

variable {N : ℕ}

theorem dist_of_sq {x y : Plane} {r : ℝ} (hr : 0 ≤ r) (h : dist x y ^ 2 = r ^ 2) : dist x y = r :=
  (pow_left_inj₀ dist_nonneg hr two_ne_zero).mp h

/-- The triangle with sides `L c(b + c)`, `L c²`, `L b(b + 2c)` (opposite `A, B, C`) has angles
`(2α, α, 2β)`. -/
theorem second_shape (T : Tri) {α β a b c L : ℝ} (ha : 0 < a) (hc : 0 < c) (hL : 0 < L)
    (hb0 : 0 < b) (hb : b = c - a ^ 2 / c) (hrel : 3 * α + 2 * β = Real.pi) (hα : 0 < α) (hβ : 0 < β)
    (cα : a ^ 2 = b ^ 2 + c ^ 2 - 2 * b * c * Real.cos α)
    (h0 : T.oppLen 0 = L * (c * (b + c))) (h1 : T.oppLen 1 = L * c ^ 2)
    (h2 : T.oppLen 2 = L * (b * (b + 2 * c))) :
    T.angleAt 0 = 2 * α ∧ T.angleAt 1 = α ∧ T.angleAt 2 = 2 * β := by
  have hcα : Real.cos α = (b ^ 2 + c ^ 2 - a ^ 2) / (2 * b * c) := by field_simp; linarith
  have ha2 : a ^ 2 = c * (c - b) := by rw [hb]; field_simp; ring
  have A0 : T.angleAt 0 = 2 * α := by
    refine angleAt_eq_of_cos T 0 (by linarith) (by linarith) ?_
    rw [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, h0, h1, h2,
      Real.cos_two_mul, hcα, ha2]
    field_simp
    ring
  have A1 : T.angleAt 1 = α := by
    refine angleAt_eq_of_cos T 1 hα.le (by linarith) ?_
    rw [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl, h0, h1, h2, hcα, ha2]
    field_simp
    ring
  refine ⟨A0, A1, ?_⟩
  have := T.angleAt_sum
  rw [A0, A1] at this
  linarith

/-- The triangle `(2α, α, 2β)` is not similar to the tile when `α ∉ ℚπ`. -/
theorem not_similar_second (D : CongruentDissection N) {α β γ a b c : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi) (hT : TileSides D α β γ a b c) (hirr : IrrPi α)
    (h0 : D.target.angleAt 0 = 2 * α) : ¬ SimilarTM D := by
  intro hs
  obtain ⟨hα, hβ, hγ, -⟩ := model_facts D hrel hT
  rcases angles_of_similar D hT hs 0 with e | e | e <;> rw [h0] at e
  · linarith
  · exact hirr ⟨1 / 7, by push_cast; linarith⟩
  · linarith

/-- `M` for the triangle `(2α, α, 2β)`: if `N = L²(b + c)(b + 2c)`, then `M = L(b + c - a)`. -/
theorem second_M (D : CongruentDissection N) {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c) (hns : ¬ SimilarTM D)
    (hshape : D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = 2 * β)
    {ε : Fin N → ℤ} (hε : D.toDissection.ProperColouring ε) {i₀ : Fin N} (hi₀ : AtBOnAB D i₀)
    (hb1 : ε i₀ = 1) {L : ℝ} (hL : 0 < L) (hN : (N : ℝ) = L ^ 2 * ((b + c) * (b + 2 * c))) :
    ((∑ i, ε i : ℤ) : ℝ) = L * (b + c - a) := by
  have hat : TileAt D 1 i₀ := by obtain ⟨l, -, -, hl, -⟩ := hi₀; exact ⟨l, hl⟩
  obtain ⟨-, heq⟩ := secondtilingequation D hrel hT hns hshape hε hat hb1
  obtain ⟨hα, hβ, -, -, hc, ha, hb, ht0, ht1, -⟩ := model_facts D hrel hT
  set t := 2 * Real.cos (α + β)
  -- `M > 0`, from `theorem:coloring`.
  have hT' : TileAngles D α β γ := by
    obtain ⟨σ, h0, h1, h2, -⟩ := hT
    exact ⟨σ, h0, h1, h2⟩
  have hirr := (angles D hrel hT' hns).1
  have h := threeAlphaData_of_sides D hrel hT
  have hns3 := not_triple3 D hrel hT' hns
  obtain ⟨-, -, t0⟩ := corner_counts D hirr hrel h hns3 0 (p := 2) (q := 0)
    (by rw [hshape.1]; push_cast; ring)
  obtain ⟨-, -, t2⟩ := corner_counts D hirr hrel h hns3 2 (p := 0) (q := 2)
    (by rw [hshape.2.2]; push_cast; ring)
  have hcol := ((coloring D hrel hT hns).2 (by rw [t0, t2]) ε i₀ hε hi₀ hb1).2 (by
    rintro (⟨e, -⟩ | ⟨-, e⟩)
    · rw [hshape.1] at e; linarith
    · rw [hshape.2.2] at e; linarith)
  have hY : D.target.oppLen 1 < D.target.oppLen 2 + D.target.oppLen 0 := by
    have hl := cos_angleAt D.target 1
    rw [show (1 : Fin 3) + 1 = 2 from rfl, show (1 : Fin 3) + 2 = 0 from rfl, hshape.2.1] at hl
    have hcos : 0 < Real.cos α :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    have p0 := oppLen_pos D.target 0
    have p1 := oppLen_pos D.target 1
    have p2 := oppLen_pos D.target 2
    have hsq : D.target.oppLen 1 ^ 2 < (D.target.oppLen 2 + D.target.oppLen 0) ^ 2 := by
      rw [hl]; nlinarith [mul_pos (mul_pos p2 p0) hcos]
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) hsq
  have hMpos : (0 : ℝ) < ((∑ i, ε i : ℤ) : ℝ) := by
    have habc : 0 < a + b + c := by
      have : 0 < (1 - t ^ 2) * c := mul_pos (by nlinarith) hc
      rw [ha, hb]; nlinarith [mul_pos ht0 hc]
    have : 0 < ((∑ i, ε i : ℤ) : ℝ) * (a + b + c) := by
      simp only at hcol; rw [hcol]; linarith
    exact pos_of_mul_pos_left this habc.le
  -- `M² = L²(b + c - a)²` from the second tiling equation.
  have hs : a / c = t := by rw [ha]; field_simp
  simp only [hs] at heq
  have h23 : (2 - t ^ 2) * (3 - t ^ 2) ≠ 0 := by
    apply mul_ne_zero
    · exact (by nlinarith : (0 : ℝ) < 2 - t ^ 2).ne'
    · exact (by nlinarith : (0 : ℝ) < 3 - t ^ 2).ne'
  rw [div_eq_iff (pow_ne_zero 2 hMpos.ne'), hN, hb] at heq
  have hden : (1 - t) ^ 2 * (2 + t) ^ 2 ≠ 0 := by
    apply mul_ne_zero <;> apply pow_ne_zero
    · exact (by linarith : (0 : ℝ) < 1 - t).ne'
    · exact (by linarith : (0 : ℝ) < 2 + t).ne'
  have e2 : L ^ 2 * (((1 - t ^ 2) * c + c) * ((1 - t ^ 2) * c + 2 * c)) =
      (2 - t ^ 2) * (3 - t ^ 2) * (L * c) ^ 2 := by ring
  have h' : (2 - t ^ 2) * (3 - t ^ 2) * ((∑ i, ε i : ℤ) : ℝ) ^ 2 =
      (2 - t ^ 2) * (3 - t ^ 2) * (L * c) ^ 2 * ((1 - t) ^ 2 * (2 + t) ^ 2) := by
    have h1t : (1 : ℝ) - t ≠ 0 := (by linarith : (0 : ℝ) < 1 - t).ne'
    have h2t : (2 : ℝ) + t ≠ 0 := (by linarith : (0 : ℝ) < 2 + t).ne'
    rw [← e2, heq]; field_simp
  have hsq : ((∑ i, ε i : ℤ) : ℝ) ^ 2 = (L * ((1 - t ^ 2) * c + c - t * c)) ^ 2 := by
    have key : (2 - t ^ 2) * (3 - t ^ 2) * (((∑ i, ε i : ℤ) : ℝ) ^ 2 -
        (L * ((1 - t ^ 2) * c + c - t * c)) ^ 2) = 0 := by linear_combination h'
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h h23
    · linarith
  have hQ : 0 < L * ((1 - t ^ 2) * c + c - t * c) := by
    rw [show (1 - t ^ 2) * c + c - t * c = c * (1 - t) * (2 + t) by ring]
    exact mul_pos hL (mul_pos (mul_pos hc (by linarith)) (by linarith))
  rw [ha, hb]
  exact (pow_left_inj₀ hMpos.le hQ.le two_ne_zero).mp hsq

/-- Bonfioli's tiling of `(2α, α, 2β)`, in our vocabulary: relabelled target, angles, `M`. -/
theorem second_package (E : CongruentDissection N) (a b c : ℕ) (ha : 0 < a) (hb : 0 < b)
    (h : a * a + c * b = c * c) {L : ℝ} (hL : 0 < L)
    (m01 : dist (E.model.pts 0) (E.model.pts 1) ^ 2 = (c : ℝ) ^ 2)
    (m02 : dist (E.model.pts 0) (E.model.pts 2) ^ 2 = (b : ℝ) ^ 2)
    (m12 : dist (E.model.pts 1) (E.model.pts 2) ^ 2 = (a : ℝ) ^ 2)
    (t01 : dist (E.target.pts 0) (E.target.pts 1) ^ 2 = (L * c ^ 2) ^ 2)
    (t02 : dist (E.target.pts 0) (E.target.pts 2) ^ 2 = (L * (b * (b + 2 * c))) ^ 2)
    (t12 : dist (E.target.pts 1) (E.target.pts 2) ^ 2 = (L * (c * (b + c))) ^ 2)
    (hN : (N : ℝ) = L ^ 2 * ((b + c) * (b + 2 * c))) :
    ∃ D : CongruentDissection N, ∃ α β γ : ℝ, TileSides D α β γ a b c ∧ 3 * α + 2 * β = Real.pi ∧
      (D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = 2 * β) ∧
      ¬ SimilarTM D ∧
      ∀ (ε : Fin N → ℤ) (i₀ : Fin N), D.toDissection.ProperColouring ε → AtBOnAB D i₀ →
        ε i₀ = 1 → ((∑ i, ε i : ℤ) : ℝ) = L * (b + c - a) := by
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; simp at h; omega
    · exact h0
  have har : (0 : ℝ) < a := by exact_mod_cast ha
  have hbr : (0 : ℝ) < b := by exact_mod_cast hb
  have hcr : (0 : ℝ) < c := by exact_mod_cast hc
  have hh : (a : ℝ) * a + c * b = c * c := by exact_mod_cast h
  have l0 : E.model.oppLen ((Equiv.refl (Fin 3)) 0) = a := dist_of_sq har.le m12
  have l1 : E.model.oppLen ((Equiv.refl (Fin 3)) 1) = b := by
    show dist _ _ = _; rw [dist_comm]; exact dist_of_sq hbr.le m02
  have l2 : E.model.oppLen ((Equiv.refl (Fin 3)) 2) = c := dist_of_sq hcr.le m01
  have hrelb : (b : ℝ) = c - (a : ℝ) ^ 2 / c := by field_simp; linarith
  obtain ⟨hTS, h32, cα, -⟩ := tile_of_sides E (Equiv.refl _) l0 l1 l2 hrelb
  set α := E.model.angleAt ((Equiv.refl (Fin 3)) 0)
  set β := E.model.angleAt ((Equiv.refl (Fin 3)) 1)
  have hα := E.model.angleAt_pos' ((Equiv.refl (Fin 3)) 0)
  have hβ := E.model.angleAt_pos' ((Equiv.refl (Fin 3)) 1)
  set D := relabelTarget E (Equiv.swap 1 2)
  have hTS' : TileSides D α β (E.model.angleAt ((Equiv.refl (Fin 3)) 2)) a b c := hTS
  have o0 : D.target.oppLen 0 = L * (c * (b + c)) := by
    rw [relabelTarget_target, oppLen_relabel,
      Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
    exact dist_of_sq (by positivity) t12
  have o1 : D.target.oppLen 1 = L * c ^ 2 := by
    rw [relabelTarget_target, oppLen_relabel, Equiv.swap_apply_left]
    exact dist_of_sq (by positivity) t01
  have o2 : D.target.oppLen 2 = L * (b * (b + 2 * c)) := by
    rw [relabelTarget_target, oppLen_relabel, Equiv.swap_apply_right]
    show dist _ _ = _; rw [dist_comm]
    exact dist_of_sq (by positivity) t02
  obtain ⟨A0, A1, A2⟩ := second_shape D.target har hcr hL hbr hrelb h32 hα hβ cα o0 o1 o2
  have hirr : IrrPi α := by
    refine irrPi_of_cos_rat hα (by linarith) ⟨((b : ℚ) ^ 2 + c ^ 2 - a ^ 2) / (2 * b * c), ?_⟩
    push_cast
    rw [eq_div_iff (by positivity)]; linarith
  have hns := not_similar_second D h32 hTS' hirr A0
  exact ⟨D, α, β, _, hTS', h32, ⟨A0, A1, A2⟩, hns,
    fun ε i₀ hε hi₀ hb1 => second_M D h32 hTS' hns ⟨A0, A1, A2⟩ hε hi₀ hb1 hL hN⟩

/-- The converse of `theorem:secondcasesolution`: Bonfioli's `thm15_converse`, with `M`. -/
theorem secondcase_converse (a b c t : ℕ) (ha : 0 < a) (hb : 0 < b) (ht : 0 < t)
    (h : a * a + c * b = c * c) (hcb : c < 2 * b) :
    ∃ (N : ℕ) (D : CongruentDissection N),
      N = t ^ 2 * (Nat.lcm a c / c) ^ 2 * ((b + c) * (b + 2 * c)) ∧
      ∃ α β γ : ℝ, TileSides D α β γ a b c ∧ 3 * α + 2 * β = Real.pi ∧
        (D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = 2 * β) ∧
        ∀ (ε : Fin N → ℤ) (i₀ : Fin N), D.toDissection.ProperColouring ε → AtBOnAB D i₀ →
          ε i₀ = 1 → ((∑ i, ε i : ℤ) : ℝ) = (t * (Nat.lcm a c / c) : ℕ) * ((b : ℝ) + c - a) := by
  obtain ⟨T, E, hE, m01, m02, m12, t01, t02, t12⟩ :=
    Erdos634.BeesonT15Conv.thm15_converse a b c t ha hb ht h hcb
  have hc : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; simp at h; omega
    · exact h0
  have hj : 0 < Nat.lcm a c / c := Nat.div_pos (Nat.le_of_dvd (Nat.lcm_pos ha hc) (Nat.dvd_lcm_right a c)) hc
  have hL : (0 : ℝ) < ((t * (Nat.lcm a c / c) : ℕ) : ℝ) := by exact_mod_cast Nat.mul_pos ht hj
  rw [← hE] at m01 m02 m12
  obtain ⟨D, α, β, γ, hTS, h32, hsh, -, hM⟩ := second_package E a b c ha hb h hL m01 m02 m12
    (by rw [t01]; push_cast; ring) (by rw [t02]; push_cast; ring) (by rw [t12]; push_cast; ring)
    (by push_cast; ring)
  exact ⟨_, D, by ring, α, β, γ, hTS, h32, hsh, hM⟩

/-- **Theorem `theorem:existence2`.** Suppose `c` divides `a²`, where `a` and `c` are integers
with `a < c`, let `b = c - a²/c` (so `3α + 2β = π` and `b` is an integer), and suppose `c < 2b`.
Let `s = a/c`, `ℓ = lcm(a, c)`, and `j = ℓ/c`. Then some triangle `ABC` with angles
`(2α, α, 2β)` can be `N`-tiled by the tile `(a, b, c)`, with
`M = ℓ(2 - s² - s) = j(b + c - a)` and `N = ℓ²(2 - s²)(3 - s²) = j²(b + c)(b + 2c)`.

`a > 0` is a hypothesis. `M` is the sum of any proper colouring with a black tile at `B`. -/
theorem existence2 (a c : ℕ) (ha : 0 < a) (hac : a < c) (hdiv : c ∣ a ^ 2)
    (hcb : c < 2 * (c - a ^ 2 / c)) :
    ∃ (N : ℕ) (D : CongruentDissection N), ∃ α β γ : ℝ,
      TileSides D α β γ a ((c - a ^ 2 / c : ℕ) : ℝ) c ∧ 3 * α + 2 * β = Real.pi ∧
      (D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = 2 * β) ∧
      (∀ (ε : Fin N → ℤ) (i₀ : Fin N), D.toDissection.ProperColouring ε → AtBOnAB D i₀ →
        ε i₀ = 1 → ((∑ i, ε i : ℤ) : ℝ) =
          (Nat.lcm a c : ℝ) * (2 - ((a : ℝ) / c) ^ 2 - (a : ℝ) / c)) ∧
      (Nat.lcm a c : ℝ) * (2 - ((a : ℝ) / c) ^ 2 - (a : ℝ) / c) =
        ((Nat.lcm a c / c : ℕ) : ℝ) * (((c - a ^ 2 / c : ℕ) : ℝ) + c - a) ∧
      (N : ℝ) = (Nat.lcm a c : ℝ) ^ 2 * (2 - ((a : ℝ) / c) ^ 2) * (3 - ((a : ℝ) / c) ^ 2) ∧
      N = (Nat.lcm a c / c) ^ 2 * (((c - a ^ 2 / c) + c) * ((c - a ^ 2 / c) + 2 * c)) := by
  set b := c - a ^ 2 / c with hbdef
  have hc : 0 < c := by omega
  have hq : a ^ 2 / c < c := by
    rw [Nat.div_lt_iff_lt_mul hc]; nlinarith
  have hb : 0 < b := by omega
  have hsq : c * (a ^ 2 / c) = a ^ 2 := Nat.mul_div_cancel' hdiv
  have h : a * a + c * b = c * c := by
    rw [hbdef, Nat.mul_sub, hsq]; have : a ^ 2 ≤ c * c := by nlinarith
    rw [sq] at this ⊢; omega
  obtain ⟨N, D, hN, α, β, γ, hTS, h32, hsh, hM⟩ := secondcase_converse a b c 1 ha hb one_pos h hcb
  -- `ℓ = j c`
  have hl : (Nat.lcm a c : ℝ) = (Nat.lcm a c / c : ℕ) * c := by
    rw [Nat.cast_div (Nat.dvd_lcm_right a c) (by exact_mod_cast hc.ne')]
    field_simp
  have hcr : (0 : ℝ) < c := by exact_mod_cast hc
  have hbr : (b : ℝ) = c - (a : ℝ) ^ 2 / c := by
    have : (c : ℝ) * b = c * c - a * a := by
      have := congrArg (fun n : ℕ => (n : ℝ)) h; push_cast at this; linarith
    field_simp; linarith
  have hMid : (Nat.lcm a c : ℝ) * (2 - ((a : ℝ) / c) ^ 2 - (a : ℝ) / c) =
      ((Nat.lcm a c / c : ℕ) : ℝ) * ((b : ℝ) + c - a) := by
    rw [hl, hbr]; field_simp; ring
  refine ⟨N, D, α, β, γ, hTS, h32, hsh, fun ε i₀ hε hi₀ hb1 => ?_, hMid, ?_, by rw [hN]; ring⟩
  · rw [hM ε i₀ hε hi₀ hb1, hMid]; push_cast; ring
  · rw [hN]; push_cast; rw [hl, hbr]; field_simp; ring

/-- **Theorem `theorem:secondcasesolution`.** Let the tile have angles `(α, β, γ)` with
`3α + 2β = π`, and suppose some triangle with angles `(2α, α, 2β)` is `N`-tiled and not similar to
the tile. Then `s = 2 sin(α/2)` is rational. Scale the tile so that `(a, b, c)` are integers with
no common divisor; then `s = a/c`, `c` divides `a²`, and `N = (b + c)(b + 2c)(M/(b + c - a))²`.
Conversely, if `c < 2b`, then for every positive integer `t` there is a tiling with
`M = tj(b + c - a)` and `N = t²j²(b + c)(b + 2c)`, where `j = lcm(a, c)/c`.

The first part is `secondcasesolution_onlyif` (`s = a/c` is `s_eq`). In the converse the tile is
any positive integer tile with `a² + cb = c²` (no common divisor is not needed), and `M` is the sum
of any proper colouring with a black tile at `B`. -/
theorem secondcasesolution :
    (∀ {N : ℕ} (D : CongruentDissection N) {α β γ a b c : ℝ}, 3 * α + 2 * β = Real.pi →
      TileSides D α β γ a b c → ¬ SimilarTM D →
      (D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = 2 * β) →
      ∀ {ε : Fin N → ℤ}, D.toDissection.ProperColouring ε → ∀ {i₀ : Fin N}, TileAt D 1 i₀ →
        ε i₀ = 1 →
        (∃ q : ℚ, 2 * Real.sin (α / 2) = q) ∧ a / c = 2 * Real.sin (α / 2) ∧
        ∀ A B C : ℤ, a = A → b = B → c = C →
          C ∣ A ^ 2 ∧ (N : ℝ) = (b + c) * (b + 2 * c) * ((∑ i, ε i : ℤ) / (b + c - a)) ^ 2) ∧
    (∀ a b c : ℕ, 0 < a → 0 < b → a * a + c * b = c * c → c < 2 * b → ∀ t : ℕ, 0 < t →
      ∃ (N : ℕ) (D : CongruentDissection N),
        N = t ^ 2 * (Nat.lcm a c / c) ^ 2 * ((b + c) * (b + 2 * c)) ∧
        ∃ α β γ : ℝ, TileSides D α β γ a b c ∧ 3 * α + 2 * β = Real.pi ∧
          (D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = 2 * β) ∧
          ∀ (ε : Fin N → ℤ) (i₀ : Fin N), D.toDissection.ProperColouring ε → AtBOnAB D i₀ →
            ε i₀ = 1 → ((∑ i, ε i : ℤ) : ℝ) = (t * (Nat.lcm a c / c) : ℕ) * ((b : ℝ) + c - a)) := by
  refine ⟨fun D α β γ a b c hrel hT hns hsh ε hε i₀ hi₀ hb1 => ?_,
    fun a b c ha hb h hcb t ht => secondcase_converse a b c t ha hb ht h hcb⟩
  obtain ⟨⟨q, hq⟩, h2⟩ := secondcasesolution_onlyif D hrel hT hns hsh hε hi₀ hb1
  have hs := s_eq hrel hT
  exact ⟨⟨q, hs ▸ hq⟩, hs, h2⟩

/-- An integer tile with `c ∣ a²` is `g (pq, q² - p², q²)` with `p, q` coprime. -/
theorem prim_tile (a c : ℕ) (ha : 0 < a) (hac : a < c) (hdiv : c ∣ a ^ 2) :
    ∃ p q g : ℕ, 0 < p ∧ p < q ∧ Nat.Coprime p q ∧ 0 < g ∧ a = g * (p * q) ∧ c = g * (q * q) := by
  have hc : 0 < c := by omega
  obtain ⟨d, p, q, hd, hpq, rfl, rfl⟩ := Nat.exists_coprime' (Nat.gcd_pos_of_pos_right a hc)
  have hq0 : 0 < q := Nat.pos_of_ne_zero (by rintro rfl; simp at hc)
  have hp0 : 0 < p := Nat.pos_of_ne_zero (by rintro rfl; simp at ha)
  -- `q ∣ d p²`, so `q ∣ d`
  have h1 : q ∣ p ^ 2 * d := by
    have : q * d ∣ (p ^ 2 * d) * d := by
      have := hdiv; rw [show (p * d) ^ 2 = (p ^ 2 * d) * d by ring] at this; exact this
    exact Nat.dvd_of_mul_dvd_mul_right hd this
  obtain ⟨g, rfl⟩ := (Nat.Coprime.pow_left 2 hpq).symm.dvd_of_dvd_mul_left h1
  have hg : 0 < g := Nat.pos_of_ne_zero (by rintro rfl; simp at hc)
  refine ⟨p, q, g, hp0, ?_, hpq, hg, by ring, by ring⟩
  by_contra hle; push_neg at hle
  have : q * (q * g) ≤ p * (q * g) := Nat.mul_le_mul_right _ hle
  omega

theorem oppLen_scaleN (k : ℕ) (hk : 0 < k) (T : Tri) (i : Fin 3) :
    (Erdos634.Realizable.scaleN k hk T).oppLen i = k * T.oppLen i := by
  unfold Tri.oppLen Erdos634.Realizable.scaleN
  simp only [Erdos634.Realizable.scaleTri_pts]
  rw [Erdos634.Realizable.dist_homothety, abs_of_nonneg (Nat.cast_nonneg k)]

/-- **Corollary `corollary:existence2case2`.** Suppose `c` divides `a²`, where `a < c` are integers,
and `b = c - a²/c`. Then some triangle with angles `(2α, α, 2β)` can be `N`-tiled by the tile
`(a, b, c)`, with `N = L²(b + c)(b + 2c)`, `M = L(b + c - a)` for some positive integer `L`.

`a > 0` is a hypothesis. `M` is the sum of any proper colouring with a black tile at `B`. -/
theorem existence2case2 (a c : ℕ) (ha : 0 < a) (hac : a < c) (hdiv : c ∣ a ^ 2) :
    ∃ L : ℕ, 0 < L ∧ ∃ (N : ℕ) (D : CongruentDissection N), ∃ α β γ : ℝ,
      TileSides D α β γ a ((c - a ^ 2 / c : ℕ) : ℝ) c ∧ 3 * α + 2 * β = Real.pi ∧
      (D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = 2 * β) ∧
      N = L ^ 2 * (((c - a ^ 2 / c) + c) * ((c - a ^ 2 / c) + 2 * c)) ∧
      ∀ (ε : Fin N → ℤ) (i₀ : Fin N), D.toDissection.ProperColouring ε → AtBOnAB D i₀ →
        ε i₀ = 1 → ((∑ i, ε i : ℤ) : ℝ) = L * (((c - a ^ 2 / c : ℕ) : ℝ) + c - a) := by
  obtain ⟨p, q, g, hp, hpq, hcop, hg, rfl, rfl⟩ := prim_tile a c ha hac hdiv
  obtain ⟨ha0, hb0, h0, hgcd⟩ := Erdos634.BeesonCor6.coprime_tile p q hp hpq hcop
  obtain ⟨L, hL, T, E, hE, m01, m02, m12, t01, t02, t12⟩ :=
    Erdos634.BeesonCor6.cor6_exists (p * q) (q * q - p * p) (q * q) ha0 hb0 h0 hgcd
  -- quadratic subdivision of scale `g`, then scaling by `g`
  obtain ⟨E₁, hE₁t, hE₁m⟩ := Erdos634.Realizable.cut_scale ⟨E, rfl, hE⟩ g hg
  have hgr : (0 : ℝ) < g := by exact_mod_cast hg
  obtain ⟨E₂, hE₂⟩ : ∃ E₂, E₂ = scaleDissection E₁ hgr := ⟨_, rfl⟩
  have hb : g * (q * q) - (g * (p * q)) ^ 2 / (g * (q * q)) = g * (q * q - p * p) := by
    have hq : 0 < q := by omega
    have hqq : 0 < g * (q * q) := Nat.mul_pos hg (Nat.mul_pos hq hq)
    rw [show (g * (p * q)) ^ 2 = (g * (q * q)) * (g * (p * p)) by ring,
      Nat.mul_div_cancel_left _ hqq, ← Nat.mul_sub]
  rw [hb]
  -- the model and target of `E₂`
  have ho : ∀ i, E₂.model.oppLen i = g * T.oppLen i := by
    intro i; rw [show E₂.model = scaleTri E₁.model g hgr.ne' by rw [hE₂]; rfl, scale_oppLen _ hgr, hE₁m]
  have hto : ∀ i, E₂.target.oppLen i = g * (g * E.target.oppLen i) := by
    intro i
    rw [show E₂.target = scaleTri E₁.target g hgr.ne' by rw [hE₂]; rfl, scale_oppLen _ hgr, hE₁t,
      oppLen_scaleN]
  have md : ∀ (r : ℝ) (U V : Tri), (∀ k, V.oppLen k = r * U.oppLen k) →
      ∀ i j : Fin 3, dist (V.pts i) (V.pts j) = r * dist (U.pts i) (U.pts j) := by
    intro r U V hUV i j
    have hcase : ∀ i j : Fin 3, i = j ∨ ∃ k, (i = k + 1 ∧ j = k + 2) ∨ (i = k + 2 ∧ j = k + 1) := by
      decide
    rcases hcase i j with rfl | ⟨k, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · simp
    · exact hUV k
    · rw [dist_comm, dist_comm (U.pts _)]; exact hUV k
  have mE := md g T E₂.model ho
  have tE := md ((g : ℝ) ^ 2) E.target E₂.target (fun k => by rw [hto]; ring)
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  obtain ⟨D, α, β, γ, hTS, h32, hsh, -, hM⟩ := second_package 
    E₂ (g * (p * q)) (g * (q * q - p * p)) (g * (q * q)) (Nat.mul_pos hg ha0) (Nat.mul_pos hg hb0)
    (by rw [show g * (p * q) * (g * (p * q)) + g * (q * q) * (g * (q * q - p * p)) =
      g * g * (p * q * (p * q) + q * q * (q * q - p * p)) by ring, h0]; ring) hLr
    (by rw [mE, mul_pow, m01]; push_cast; ring) (by rw [mE, mul_pow, m02]; push_cast; ring)
    (by rw [mE, mul_pow, m12]; push_cast; ring)
    (by rw [tE, mul_pow, t01]; push_cast; ring) (by rw [tE, mul_pow, t02]; push_cast; ring)
    (by rw [tE, mul_pow, t12]; push_cast; ring) (by push_cast; ring)
  exact ⟨L, hL, _, D, α, β, γ, hTS, h32, hsh, by ring, fun ε i₀ hε hi₀ hb1 => by
    rw [hM ε i₀ hε hi₀ hb1]⟩

/-- **Corollary `corollary:secondshapeall`.** Let the tile have angles `(α, β, γ)` with
`3α + 2β = π`. Some triangle with angles `(2α, α, 2β)` can be tiled by the tile if and only if
`s = 2 sin(α/2)` is rational.

"Tiled by the tile" is read as tiled by a tile with angles `(α, β, γ)` (any size), the triangle
not similar to the tile (the paper's standing assumption; for `α = π/7` the triangle is the tile). -/
theorem secondshapeall {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (hα : 0 < α) (hβ : 0 < β) :
    (∃ (N : ℕ) (D : CongruentDissection N) (a b c : ℝ), TileSides D α β (2 * α + β) a b c ∧
        ¬ SimilarTM D ∧
        D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = α ∧ D.target.angleAt 2 = 2 * β) ↔
      ∃ q : ℚ, 2 * Real.sin (α / 2) = q := by
  constructor
  · rintro ⟨N, D, a, b, c, hT, hns, -⟩
    obtain ⟨⟨q, hq⟩, -⟩ := rationaltile D hrel hT hns
    exact ⟨q, (s_eq hrel hT).symm.trans hq⟩
  · rintro ⟨q, hq⟩
    have hπ := Real.pi_pos
    have hα3 : α < Real.pi / 3 := by linarith
    have hs0 : 0 < Real.sin (α / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
    have hs1 : Real.sin (α / 2) < 1 / 2 := by
      rw [← Real.sin_pi_div_six]
      exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
    have hq0 : (0 : ℝ) < q := by rw [← hq]; linarith
    have hq1 : (q : ℝ) < 1 := by rw [← hq]; linarith
    set p := q.num.toNat
    set r := q.den
    have hnum : (q.num : ℝ) = p := by
      have : 0 ≤ q.num := Rat.num_nonneg.mpr (by exact_mod_cast hq0.le)
      rw [show ((q.num.toNat : ℕ) : ℝ) = ((q.num.toNat : ℤ) : ℝ) by norm_cast,
        Int.toNat_of_nonneg this]
    have hqpr : (q : ℝ) = p / r := by rw [← hnum]; exact_mod_cast (Rat.num_div_den q).symm
    have hr : (0 : ℝ) < r := by exact_mod_cast q.den_pos
    have hp : 0 < p := by
      have : (0 : ℝ) < p := by rw [hqpr] at hq0; exact (div_pos_iff_of_pos_right hr).mp hq0
      exact_mod_cast this
    have hpr : p < r := by
      have : (p : ℝ) < r := by rw [hqpr, div_lt_one hr] at hq1; exact hq1
      exact_mod_cast this
    obtain ⟨L, -, N, D, α', β', γ', hT, h32, hsh, -, -⟩ :=
      existence2case2 (p * r) (r * r) (Nat.mul_pos hp q.den_pos) (Nat.mul_lt_mul_of_pos_right hpr q.den_pos)
        ⟨p * p, by ring⟩
    obtain ⟨hα', hβ', hγ', -⟩ := model_facts D h32 hT
    have heq : α' = α := by
      have := s_eq h32 hT
      rw [show ((p * r : ℕ) : ℝ) / ((r * r : ℕ) : ℝ) = p / r by push_cast; field_simp, ← hqpr, ← hq] at this
      exact alpha_eq_of_sin hα' (by linarith) hα hα3 this.symm
    subst heq
    have hβeq : β' = β := by linarith
    subst hβeq
    subst hγ'
    have hirr : IrrPi α' := by
      refine irrPi_of_cos_rat hα hα3 ⟨1 - q ^ 2 / 2, ?_⟩
      have : Real.cos α' = 1 - 2 * Real.sin (α' / 2) ^ 2 := by
        have h2 := Real.cos_two_mul (α' / 2)
        rw [show 2 * (α' / 2) = α' by ring] at h2
        rw [h2, Real.cos_sq']; ring
      push_cast; rw [this, ← hq]; ring
    exact ⟨N, D, _, _, _, hT, not_similar_second D h32 hT hirr hsh.1, hsh⟩

end TriangleTiling.ThreeAlpha
