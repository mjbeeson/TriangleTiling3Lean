/-
`lemma:isosceleshelper3` (Section 6 of M. Beeson, *Tilings of an isosceles triangle*).

Let the isosceles triangle `ABC` with base angles `β` (at `A` and `C`) be `N`-tiled by the tile
`(α, β, π/2)` with sides `(a, b, c)`. If `β ∉ {π/6, π/4, π/3}` and `λ = √(N/2)` is irrational,
then `a/c` and `b/c` are rational multiples of `λ`, the base `AC` consists of `c` edges, and the
equal sides carry no `c` edge.
-/
import TriangleTiling.RightTile.Helper2

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry Polynomial

variable {N : ℕ} (D : CongruentDissection N)

/-- `b = c sin β`. -/
theorem right_sin (hright : tileγ D = Real.pi / 2) :
    dist (D.model.pts 2) (D.model.pts 0) =
      Real.sin (tileβ D) * dist (D.model.pts 0) (D.model.pts 1) := by
  rw [(right_trig D hright).2, ← Real.cos_pi_div_two_sub, right_beta D hright]
  ring_nf

/-- **`β` is not a rational multiple of `π`** when `cos β` and `sin β` are in `ℚ(λ)` and `β` is
not `π/6`, `π/4` or `π/3`. -/
theorem beta_irrational_of_quadratic (hright : tileγ D = Real.pi / 2) {l : ℝ} {d : ℚ}
    (hl : l ^ 2 = d) (hcos : InQ l (Real.cos (tileβ D))) (hsin : InQ l (Real.sin (tileβ D)))
    (hβ6 : tileβ D ≠ Real.pi / 6) (hβ4 : tileβ D ≠ Real.pi / 4)
    (hβ3 : tileβ D ≠ Real.pi / 3) : ¬ ∃ r : ℚ, tileβ D = r * Real.pi := by
  rintro ⟨r, hr⟩
  have hβ0 := tileβ_pos D
  have hβ := right_beta D hright
  have hα0 := tileα_pos D
  have hpi := Real.pi_pos
  -- `β = 2π m / n` in lowest terms.
  set t : ℚ := r / 2
  have ht0 : 0 < t := by
    have : (0 : ℝ) < r := by
      by_contra h; push Not at h; nlinarith
    have : (0 : ℚ) < r := by exact_mod_cast this
    simp only [t]; linarith
  have hnum : 0 < t.num := Rat.num_pos.mpr ht0
  set m := t.num.natAbs
  have hm : ((m : ℕ) : ℝ) = (t.num : ℝ) := by
    simp only [m]; rw [Nat.cast_natAbs]; push_cast; rw [abs_of_pos (by exact_mod_cast hnum)]
  have hβmn : tileβ D = 2 * Real.pi * m / t.den := by
    rw [hr, hm]
    have : (r : ℝ) = 2 * ((t.num : ℝ) / t.den) := by
      rw [← Rat.cast_intCast, ← Rat.cast_natCast, ← Rat.cast_div, Rat.num_div_den]
      simp only [t]; push_cast; ring
    rw [this]; ring
  have hcop : m.Coprime t.den := t.reduced
  obtain ⟨P, hP, hPd, hPr⟩ := hcos.quadratic hl
  obtain ⟨R, hR, hRd, hRr⟩ := hsin.quadratic hl
  rw [hβmn] at hPr hRr
  have hn := euler_sin t.den_pos hcop hP hPd hPr hR hRd hRr
  -- `0 < β < π/2` gives `0 < 4m < n`.
  have hm1 : 1 ≤ m := by simp only [m]; omega
  have hlt : 4 * m < t.den := by
    have h1 : tileβ D < Real.pi / 2 := by linarith
    rw [hβmn] at h1
    have hn0 : (0 : ℝ) < t.den := by exact_mod_cast t.den_pos
    have : (4 * m : ℝ) < t.den := by
      rw [div_lt_iff₀ hn0] at h1; nlinarith
    exact_mod_cast this
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with h | h | h | h | h | h | h <;> rw [h] at hlt hβmn hcop
  · omega
  · omega
  · omega
  · omega
  · have hm' : m = 1 := by omega
    rw [hm'] at hβmn
    exact hβ3 (by rw [hβmn]; push_cast; ring)
  · have hm' : m = 1 := by omega
    rw [hm'] at hβmn
    exact hβ4 (by rw [hβmn]; push_cast; ring)
  · have hm' : m = 1 ∨ m = 2 := by omega
    rcases hm' with hm' | hm'
    · rw [hm'] at hβmn; exact hβ6 (by rw [hβmn]; push_cast; ring)
    · rw [hm'] at hcop; exact absurd hcop (by decide)

/-- An edge of a covered side ends at each end of the side. -/
theorem side_edge_at_end {part : Finset (Fin N × Fin 3)} {P Q V : Plane}
    (hcov : (⋃ e ∈ part, (D.tile e.1).edge e.2) = segment ℝ P Q) (hV : V = P ∨ V = Q) :
    ∃ e ∈ part, ((D.tile e.1).pts e.2 = V ∨ (D.tile e.1).pts (e.2 + 1) = V) := by
  have hVs : V ∈ segment ℝ P Q := by
    rcases hV with h | h
    · rw [h]; exact left_mem_segment _ _ _
    · rw [h]; exact right_mem_segment _ _ _
  rw [← hcov] at hVs
  obtain ⟨e, he, hVe⟩ := Set.mem_iUnion₂.mp hVs
  have hsub : (D.tile e.1).edge e.2 ⊆ segment ℝ P Q := by
    rw [← hcov]; intro z hz; exact Set.mem_iUnion₂.mpr ⟨e, he, hz⟩
  have hu := hsub (left_mem_segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
  have hv := hsub (right_mem_segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
  refine ⟨e, he, ?_⟩
  rcases hV with h | h
  · rw [← h] at hu hv
    rcases eq_endpoint_of_mem_segment hu hv hVe with h' | h'
    · exact Or.inl h'.symm
    · exact Or.inr h'.symm
  · rw [segment_symm] at hu hv
    rw [← h] at hu hv
    rcases eq_endpoint_of_mem_segment hu hv hVe with h' | h'
    · exact Or.inl h'.symm
    · exact Or.inr h'.symm

/-- **The type of an edge at a vertex** differs from the tile's angle at that vertex. -/
theorem edge_type_ne (hsep : AnglesSep D) {e : Fin N × Fin 3} {V : Plane}
    (hV : (D.tile e.1).pts e.2 = V ∨ (D.tile e.1).pts (e.2 + 1) = V) {φ : ℝ}
    (hφ : φ = tileα D ∨ φ = tileβ D ∨ φ = tileγ D) (hang : (D.tile e.1).localAngle V = φ) :
    ¬ edgeType D φ e := by
  intro hθ
  have hcnt := tile_angle_count_sep D hsep e.1
  simp only [← Tri.localAngle_vertex] at hcnt
  have h1 : (Finset.univ.filter fun k : Fin 3 =>
      (D.tile e.1).localAngle ((D.tile e.1).pts k) = φ).card = 1 := by
    rcases hφ with rfl | rfl | rfl
    · exact hcnt.1
    · exact hcnt.2.1
    · exact hcnt.2.2
  have n1 : ∀ k : Fin 3, k ≠ k + 2 := by decide
  have n2 : ∀ k : Fin 3, k + 1 ≠ k + 2 := by decide
  rcases hV with h | h
  · exact n1 e.2 (Finset.card_le_one.mp h1.le e.2 (by simp [h, hang]) (e.2 + 2)
      (by simpa [edgeType] using hθ))
  · exact n2 e.2 (Finset.card_le_one.mp h1.le (e.2 + 1) (by simp [h, hang]) (e.2 + 2)
      (by simpa [edgeType] using hθ))

/-- The angle at the apex is `2α`. -/
theorem apex_angle (hright : tileγ D = Real.pi / 2)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileβ D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileβ D) :
    D.target.localAngle (D.target.pts 1) = 2 * tileα D := by
  have hβ := right_beta D hright
  rw [Tri.localAngle_vertex]
  have hsum := cornerAngle_sum D.target
  have e1 : cornerAngle (D.target.pts 0) (D.target.pts 2) (D.target.pts 1) = tileβ D := by
    rw [cornerAngle, angle_comm]; exact hC
  have e0 : cornerAngle (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileβ D := hA
  show cornerAngle (D.target.pts 2) (D.target.pts 1) (D.target.pts 0) = _
  linarith

open Classical in
/-- **A side, by edge types**: side `i` is covered by edges whose lengths add up to
`#α · a + #β · b + #γ · c`, counting the edges by the angle opposite them. -/
theorem typed_side (hsep : AnglesSep D) (i : Fin 3) : ∃ part : Finset (Fin N × Fin 3),
    (⋃ e ∈ part, (D.tile e.1).edge e.2) = segment ℝ (D.target.pts i) (D.target.pts (i + 1)) ∧
    dist (D.target.pts i) (D.target.pts (i + 1)) =
      ((part.filter (edgeType D (tileα D))).card : ℝ) * dist (D.model.pts 1) (D.model.pts 2)
      + ((part.filter (edgeType D (tileβ D))).card : ℝ) * dist (D.model.pts 2) (D.model.pts 0)
      + ((part.filter (edgeType D (tileγ D))).card : ℝ) * dist (D.model.pts 0) (D.model.pts 1) := by
  obtain ⟨part, hcov, -, hsum⟩ := D.toDissection.side_walk i
  exact ⟨part, hcov, side_walk_counts_sep D hsep part _ hsum⟩

/-- The angle of a tile at one of its vertices is `α`, `β` or `γ`. -/
theorem angle_at_end {e : Fin N × Fin 3} {V : Plane}
    (hV : (D.tile e.1).pts e.2 = V ∨ (D.tile e.1).pts (e.2 + 1) = V) :
    (D.tile e.1).localAngle V = tileα D ∨ (D.tile e.1).localAngle V = tileβ D ∨
      (D.tile e.1).localAngle V = tileγ D := by
  rcases hV with h | h
  · rw [← h]; exact localAngle_at_own_vertex_mem' D e.1 e.2
  · rw [← h]; exact localAngle_at_own_vertex_mem' D e.1 (e.2 + 1)

/-- The sign analysis in `helper3_algebra`: if `x l + y > 0`, `z l + w > 0`, `x y + z w = 0`,
`x y ≠ 0` and `p y + q w + r = 0` (with `p, q, r ≥ 0` and `q ≥ 1` or `r ≥ 1`), then `x, z > 0`. -/
theorem helper3_signs {l x y z w p q r : ℝ} (hl0 : 0 < l) (ha : 0 < x * l + y) (hb : 0 < z * l + w)
    (hxyzw : x * y + z * w = 0) (hxy : x * y ≠ 0) (hlin : p * y + q * w + r = 0)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) (hqr : 1 ≤ q ∨ 1 ≤ r) : 0 < x ∧ 0 < z := by
  rcases lt_or_gt_of_ne hxy with hneg | hpos
  · have hzw : 0 < z * w := by linarith
    rcases pos_and_pos_or_neg_and_neg_of_mul_pos hzw with ⟨hz, hw⟩ | ⟨hz, hw⟩
    · have hqw : 0 < q * w + r := by
        rcases hqr with h | h
        · have : 0 < q * w := mul_pos (by linarith) hw
          linarith
        · have : 0 ≤ q * w := mul_nonneg hq hw.le
          linarith
      have hy : y < 0 := by
        by_contra h
        push Not at h
        have : 0 ≤ p * y := mul_nonneg hp h
        linarith
      refine ⟨?_, hz⟩
      by_contra hx
      push Not at hx
      have : 0 ≤ x * y := mul_nonneg_of_nonpos_of_nonpos hx hy.le
      linarith
    · exfalso
      have : z * l < 0 := mul_neg_of_neg_of_pos hz hl0
      linarith
  · rcases pos_and_pos_or_neg_and_neg_of_mul_pos hpos with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · have hw : w < 0 := by
        by_contra h
        push Not at h
        have hpy : 0 ≤ p * y := mul_nonneg hp hy.le
        have hqw : 0 ≤ q * w := mul_nonneg hq h
        have hw0 : w ≠ 0 := by
          rintro rfl
          exact hxy (by linarith)
        have hw' : 0 < w := lt_of_le_of_ne h (Ne.symm hw0)
        rcases hqr with h' | h'
        · have : 0 < q * w := mul_pos (by linarith) hw'
          linarith
        · linarith
      refine ⟨hx, ?_⟩
      by_contra hz
      push Not at hz
      have : 0 ≤ z * w := mul_nonneg_of_nonpos_of_nonpos hz hw.le
      have : 0 < x * y := mul_pos hx hy
      linarith
    · exfalso
      have : x * l < 0 := mul_neg_of_neg_of_pos hx hl0
      linarith

/-- **The algebra of `lemma:isosceleshelper3`** (with `c = 1`). Let `a, b > 0` with `a² + b² = 1`
lie in `ℚ(l)`, with `l = p a + q b + r`, `2 a l = s a + t b + u`, `q + r ≥ 1` and `s + u ≥ 1`;
suppose that without a relation `j = v a + v' b` (`j > 0`) we get `r = s = t = 0`. Then `a` and `b`
are rational multiples of `l`. -/
theorem helper3_algebra {l : ℝ} {d : ℚ} (hl : l ^ 2 = d) (hirr : ¬ ∃ q : ℚ, l = q) (hl0 : 0 < l)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ^ 2 + b ^ 2 = 1)
    (hina : InQ l a) (hinb : InQ l b) {p q r s t u : ℕ}
    (h1 : l = p * a + q * b + r) (h2 : 2 * a * l = s * a + t * b + u)
    (hqr : 1 ≤ q + r) (hsu : 1 ≤ s + u)
    (hallc : (∀ j v v' : ℕ, 0 < j → (j : ℝ) ≠ v * a + v' * b) → r = 0 ∧ s = 0 ∧ t = 0) :
    ∃ x z : ℚ, a = x * l ∧ b = z * l := by
  obtain ⟨x, y, rfl⟩ := hina
  obtain ⟨z, w, rfl⟩ := hinb
  have hd : (0 : ℝ) < d := by rw [← hl]; positivity
  -- `p y + q w + r = 0` and `x y + z w = 0`.
  obtain ⟨-, hlin⟩ := InQ.indep hirr (x := p * x + q * z - 1) (y := p * y + q * w + r)
    (by push_cast; linear_combination -h1)
  obtain ⟨hpyth, -⟩ := InQ.indep hirr (x := 2 * (x * y + z * w))
    (y := (x ^ 2 + z ^ 2) * d + y ^ 2 + w ^ 2 - 1)
    (by push_cast; linear_combination hab - ((x : ℝ) ^ 2 + (z : ℝ) ^ 2) * hl)
  have hxyzw : x * y + z * w = 0 := by linarith
  have hlinR : (p : ℝ) * y + q * w + r = 0 := by exact_mod_cast hlin
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  by_cases hxy : x * y = 0
  · -- `x y = 0`: then `y = w = 0`.
    have hzw : z * w = 0 := by linarith
    rcases mul_eq_zero.mp hxy with hx | hy
    · exfalso
      subst hx
      simp only [Rat.cast_zero, zero_mul, zero_add] at ha h1 h2
      rcases mul_eq_zero.mp hzw with hz | hw
      · subst hz
        simp only [Rat.cast_zero, zero_mul, zero_add] at hb
        have : (q : ℝ) * w = 0 ∧ (r : ℝ) = 0 := by
          constructor <;> nlinarith [mul_nonneg hp0 ha.le, mul_nonneg hq0 hb.le]
        have hq : q = 0 := by
          have := this.1
          rcases mul_eq_zero.mp this with h | h
          · exact_mod_cast h
          · exact absurd h hb.ne'
        have hr : r = 0 := by exact_mod_cast this.2
        omega
      · subst hw
        obtain ⟨-, h3⟩ := InQ.indep hirr (x := 2 * y - t * z) (y := -(s * y + u))
          (by push_cast; linear_combination h2)
        have hs : (s : ℝ) * y + u = 0 := by
          have : (s : ℚ) * y + u = 0 := by linarith
          exact_mod_cast this
        have h4 : (s : ℝ) = 0 ∧ (u : ℝ) = 0 := by
          constructor <;> nlinarith [mul_nonneg (Nat.cast_nonneg s : (0 : ℝ) ≤ s) ha.le,
            (Nat.cast_nonneg u : (0 : ℝ) ≤ u)]
        have hs0 : s = 0 := by exact_mod_cast h4.1
        have hu0 : u = 0 := by exact_mod_cast h4.2
        omega
    · subst hy
      simp only [Rat.cast_zero] at hlinR
      have hw : w = 0 := by
        rcases mul_eq_zero.mp hzw with hz | hw
        · exfalso
          subst hz
          simp only [Rat.cast_zero, zero_mul, zero_add] at hb hlinR
          have : (q : ℝ) * w = 0 ∧ (r : ℝ) = 0 := by
            constructor <;> nlinarith [mul_nonneg hq0 hb.le]
          have hq : q = 0 := by
            rcases mul_eq_zero.mp this.1 with h | h
            · exact_mod_cast h
            · exact absurd h hb.ne'
          have hr : r = 0 := by exact_mod_cast this.2
          omega
        · exact hw
      subst hw
      exact ⟨x, z, by push_cast; ring, by push_cast; ring⟩
  · -- `x y ≠ 0`: then `x, z > 0`, there is no relation, and `r = s = t = 0`.
    have hxz : 0 < x ∧ 0 < z := by
      have hxyR : (x : ℝ) * y ≠ 0 := by exact_mod_cast hxy
      have hxyzwR : (x : ℝ) * y + z * w = 0 := by exact_mod_cast hxyzw
      have hqr' : 1 ≤ (q : ℝ) ∨ 1 ≤ (r : ℝ) := by
        rcases Nat.eq_zero_or_pos q with hq | hq
        · right; exact_mod_cast (show 1 ≤ r by omega)
        · left; exact_mod_cast hq
      have := helper3_signs hl0 ha hb hxyzwR hxyR hlinR hp0 hq0 hr0 hqr'
      exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩
    obtain ⟨hx, hz⟩ := hxz
    have hnorel : ∀ j v v' : ℕ, 0 < j →
        (j : ℝ) ≠ v * ((x : ℝ) * l + y) + v' * ((z : ℝ) * l + w) := by
      intro j v v' hj he
      obtain ⟨h3, h4⟩ := InQ.indep hirr (x := v * x + v' * z) (y := v * y + v' * w - j)
        (by push_cast; linear_combination -he)
      have hv : v = 0 := by
        by_contra hv
        have : (0 : ℚ) < v * x := mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hv) hx
        have : (0 : ℚ) ≤ v' * z := mul_nonneg (Nat.cast_nonneg _) hz.le
        linarith
      have hv' : v' = 0 := by
        by_contra hv'
        have : (0 : ℚ) < v' * z := mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hv') hz
        have : (0 : ℚ) ≤ v * x := mul_nonneg (Nat.cast_nonneg _) hx.le
        linarith
      subst hv hv'
      simp at h4
      omega
    obtain ⟨hr, hs, ht⟩ := hallc hnorel
    subst hr hs ht
    simp only [Nat.cast_zero, zero_mul, zero_add, add_zero] at h1 h2
    have hq1 : 1 ≤ q := by omega
    have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    have hdR : (d : ℝ) ≠ 0 := hd.ne'
    have hl' : l ≠ 0 := hl0.ne'
    -- `a = u / (2 l) = (u / 2d) l`, then `b = (l - p a) / q`.
    have ea : (x : ℝ) * l + y = (u : ℝ) / (2 * d) * l := by
      rw [div_mul_eq_mul_div, eq_div_iff (by positivity)]
      linear_combination (-2 * ((x : ℝ) * l + y)) * hl + l * h2
    have eb : (z : ℝ) * l + w = (1 - p * ((u : ℝ) / (2 * d))) / q * l := by
      rw [div_mul_eq_mul_div, eq_div_iff hqR]
      linear_combination -h1 - (p : ℝ) * ea
    exact ⟨u / (2 * d), (1 - p * (u / (2 * d))) / q, by push_cast; exact ea,
      by push_cast; exact eb⟩

open Classical in
/-- **Lemma `lemma:isosceleshelper3`.** Let the isosceles triangle `ABC` with base angles `β` (at
`A` and `C`) be `N`-tiled by the tile `(α, β, π/2)` with sides `(a, b, c)`. If
`β ∉ {π/6, π/4, π/3}` and `λ = √(N/2)` is irrational, then `a/c` and `b/c` are rational multiples
of `λ`, `AC` consists of `c` edges, and `AB` and `BC` carry no `c` edge. -/
theorem isosceleshelper3 (hright : tileγ D = Real.pi / 2)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileβ D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileβ D)
    (hβ6 : tileβ D ≠ Real.pi / 6) (hβ4 : tileβ D ≠ Real.pi / 4) (hβ3 : tileβ D ≠ Real.pi / 3)
    (hirrl : ¬ ∃ q : ℚ, Real.sqrt ((N : ℝ) / 2) = q) :
    (∃ x z : ℚ,
      dist (D.model.pts 1) (D.model.pts 2) / dist (D.model.pts 0) (D.model.pts 1) =
        x * Real.sqrt ((N : ℝ) / 2) ∧
      dist (D.model.pts 2) (D.model.pts 0) / dist (D.model.pts 0) (D.model.pts 1) =
        z * Real.sqrt ((N : ℝ) / 2)) ∧
    (∀ e : Fin N × Fin 3, (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 2) (D.target.pts 0) →
        edgeType D (tileγ D) e) ∧
      ∀ e : Fin N × Fin 3,
        ((D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 0) (D.target.pts 1) ∨
          (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 1) (D.target.pts 2)) →
        ¬ edgeType D (tileγ D) e := by
  obtain ⟨hina, hinb⟩ := isosceleshelper2 D hright hA hC hβ6 hirrl
  set a := dist (D.model.pts 1) (D.model.pts 2) with hadef
  set b := dist (D.model.pts 2) (D.model.pts 0) with hbdef
  set c := dist (D.model.pts 0) (D.model.pts 1) with hcdef
  set l := Real.sqrt ((N : ℝ) / 2) with hldef
  set T := D.target.pts with hT
  have hl : l ^ 2 = (((N : ℚ) / 2 : ℚ) : ℝ) := by
    rw [hldef, Real.sq_sqrt (by positivity)]; push_cast; ring
  have hc0 : 0 < c := dist_pos.mpr fun e => by
    have := D.model.indep.injective e; exact absurd this (by decide)
  have ha0 : 0 < a := dist_pos.mpr fun e => by
    have := D.model.indep.injective e; exact absurd this (by decide)
  have hb0 : 0 < b := dist_pos.mpr fun e => by
    have := D.model.indep.injective e; exact absurd this (by decide)
  have hl0 : 0 < l := by
    rcases (Real.sqrt_nonneg ((N : ℝ) / 2)).lt_or_eq with h | h
    · exact h
    · exact absurd ⟨0, by rw [hldef, ← h]; simp⟩ hirrl
  -- `α` and `β` are not rational multiples of `π`.
  have hβ := right_beta D hright
  obtain ⟨hab, -⟩ := right_trig D hright
  change a = Real.cos (tileβ D) * c at hab
  have hbs : b = Real.sin (tileβ D) * c := right_sin D hright
  have hcos : Real.cos (tileβ D) = a / c := by rw [hab]; field_simp
  have hsin : Real.sin (tileβ D) = b / c := by rw [hbs]; field_simp
  have hβirr := beta_irrational_of_quadratic D hright hl (hcos ▸ hina) (hsin ▸ hinb) hβ6 hβ4 hβ3
  have hαirr : ¬ ∃ r : ℚ, tileα D = r * Real.pi := by
    rintro ⟨r, hr⟩
    exact hβirr ⟨1 / 2 - r, by rw [hβ, hr]; push_cast; ring⟩
  have hsep := anglesSep_right D hright hαirr
  have hα0 := tileα_pos D
  have hβ0 := tileβ_pos D
  have hαγ : tileα D ≠ tileγ D := by rw [hright]; linarith
  have hβγ : tileβ D ≠ tileγ D := by rw [hright]; linarith
  -- The area equation: `|AB| = λ c` and `|AC| = 2 λ a`.
  obtain ⟨-, hcY, hN⟩ := right_area_core D rfl rfl rfl rfl rfl hright hA hC
  set X := dist (T 0) (T 1)
  set Y := dist (T 2) (T 0)
  have hXl : X = l * c := by
    have h1 : X ^ 2 = (l * c) ^ 2 := by
      rw [mul_pow, hl]; push_cast; linarith
    exact (pow_left_inj₀ dist_nonneg (by positivity) two_ne_zero).mp h1
  have hYl : Y = 2 * a * l := by
    have : c * Y = c * (2 * a * l) := by rw [hcY, hXl]; ring
    exact mul_left_cancel₀ hc0.ne' this
  -- The sides `AB` and `AC` as sums of typed edges.
  obtain ⟨part0, hcov0, hs0⟩ := typed_side D hsep 0
  obtain ⟨part2, hcov2, hs2⟩ := typed_side D hsep 2
  have i01 : (0 : Fin 3) + 1 = 1 := rfl
  have i20 : (2 : Fin 3) + 1 = 0 := rfl
  rw [i01] at hcov0 hs0
  rw [i20] at hcov2 hs2
  have e1 : l = ((part0.filter (edgeType D (tileα D))).card : ℝ) * (a / c)
      + ((part0.filter (edgeType D (tileβ D))).card : ℝ) * (b / c)
      + ((part0.filter (edgeType D (tileγ D))).card : ℝ) := by
    field_simp; rw [← hXl]; linarith
  have e2 : 2 * (a / c) * l = ((part2.filter (edgeType D (tileα D))).card : ℝ) * (a / c)
      + ((part2.filter (edgeType D (tileβ D))).card : ℝ) * (b / c)
      + ((part2.filter (edgeType D (tileγ D))).card : ℝ) := by
    field_simp; rw [← hs2.symm.trans hYl]; ring
  have hsub0 : ∀ e ∈ part0, (D.tile e.1).edge e.2 ⊆ segment ℝ (T 0) (T 1) := by
    intro e he y hy; rw [← hcov0]; exact Set.mem_iUnion₂.mpr ⟨e, he, hy⟩
  have hsub2 : ∀ e ∈ part2, (D.tile e.1).edge e.2 ⊆ segment ℝ (T 2) (T 0) := by
    intro e he y hy; rw [← hcov2]; exact Set.mem_iUnion₂.mpr ⟨e, he, hy⟩
  -- Every edge has a type; an all-`c` side has no edges of the other types.
  have htype : ∀ e : Fin N × Fin 3, edgeType D (tileα D) e ∨ edgeType D (tileβ D) e ∨
      edgeType D (tileγ D) e := fun e => localAngle_at_own_vertex_mem' D e.1 (e.2 + 2)
  have hzero : ∀ (part : Finset (Fin N × Fin 3)) (φ : ℝ), φ ≠ tileγ D →
      (∀ e ∈ part, edgeType D (tileγ D) e) → (part.filter (edgeType D φ)).card = 0 := by
    intro part φ hφ hall
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e he hφe
    exact hφ (hφe.symm.trans (hall e he))
  have hpos : ∀ (part : Finset (Fin N × Fin 3)) (φ : ℝ) (e : Fin N × Fin 3), e ∈ part →
      edgeType D φ e → 1 ≤ (part.filter (edgeType D φ)).card := fun part φ e he h =>
    Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, h⟩⟩
  -- At `B` every tile has its `α` angle, so the edge of `AB` at `B` has type `β` or `γ`.
  have hqr : 1 ≤ (part0.filter (edgeType D (tileβ D))).card +
      (part0.filter (edgeType D (tileγ D))).card := by
    obtain ⟨e, he, hV⟩ := side_edge_at_end D hcov0 (V := T 1) (Or.inr rfl)
    have hB := vertex_relations_right D hright hαirr (T 1) 2 0
      (by rw [apex_angle D hright hA hC]; push_cast; ring)
    have hnβ : angleCount D (T 1) (tileβ D) = 0 := by omega
    have hnγ : angleCount D (T 1) (tileγ D) = 0 := by omega
    have hang : (D.tile e.1).localAngle (T 1) = tileα D := by
      rcases angle_at_end D hV with h | h | h
      · exact h
      · exfalso
        have : 0 < angleCount D (T 1) (tileβ D) :=
          Finset.card_pos.mpr ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
        omega
      · exfalso
        have : 0 < angleCount D (T 1) (tileγ D) :=
          Finset.card_pos.mpr ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
        omega
    have hnot := edge_type_ne D hsep hV (Or.inl rfl) hang
    rcases htype e with h | h | h
    · exact absurd h hnot
    · have := hpos _ _ e he h; omega
    · have := hpos _ _ e he h; omega
  -- At `A` the only tile has its `β` angle, so the edge of `AC` at `A` has type `α` or `γ`.
  have hsu : 1 ≤ (part2.filter (edgeType D (tileα D))).card +
      (part2.filter (edgeType D (tileγ D))).card := by
    obtain ⟨e, he, hV⟩ := side_edge_at_end D hcov2 (V := T 0) (Or.inr rfl)
    have hA' := vertex_relations_right D hright hαirr (T 0) (-1) 1
      (by rw [Tri.localAngle_vertex]; change ∠ (T 1) (T 0) (T 2) = _; rw [hA, hβ]; push_cast; ring)
    have hnα : angleCount D (T 0) (tileα D) = 0 := by omega
    have hnγ : angleCount D (T 0) (tileγ D) = 0 := by omega
    have hang : (D.tile e.1).localAngle (T 0) = tileβ D := by
      rcases angle_at_end D hV with h | h | h
      · exfalso
        have : 0 < angleCount D (T 0) (tileα D) :=
          Finset.card_pos.mpr ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
        omega
      · exact h
      · exfalso
        have : 0 < angleCount D (T 0) (tileγ D) :=
          Finset.card_pos.mpr ⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
        omega
    have hnot := edge_type_ne D hsep hV (Or.inr (Or.inl rfl)) hang
    rcases htype e with h | h | h
    · have := hpos _ _ e he h; omega
    · exact absurd h hnot
    · have := hpos _ _ e he h; omega
  -- Without a relation, `allc` holds in its first form (the second makes `λ` rational).
  have halt1 : (∀ j v v' : ℕ, 0 < j → (j : ℝ) ≠ v * (a / c) + v' * (b / c)) →
      (∀ e : Fin N × Fin 3, (D.tile e.1).edge e.2 ⊆ segment ℝ (T 2) (T 0) →
        edgeType D (tileγ D) e) ∧
      ∀ e : Fin N × Fin 3,
        ((D.tile e.1).edge e.2 ⊆ segment ℝ (T 0) (T 1) ∨
          (D.tile e.1).edge e.2 ⊆ segment ℝ (T 1) (T 2)) →
        ¬ edgeType D (tileγ D) e := by
    intro hno
    have hnorel : ¬ ∃ j u v : ℕ, 0 < j ∧ (j : ℝ) * c = u * a + v * b := by
      rintro ⟨j, u, v, hj, he⟩
      apply hno j u v hj
      rw [mul_div_assoc', mul_div_assoc', ← add_div, eq_div_iff hc0.ne']
      exact he
    rcases allc D hright hαirr hA hC hnorel with h | ⟨h0, -⟩
    · exact h
    · exfalso
      have hall : ∀ e ∈ part0, edgeType D (tileγ D) e := fun e he => h0 e (Or.inl (hsub0 e he))
      rw [hzero part0 _ hαγ hall, hzero part0 _ hβγ hall] at e1
      simp only [Nat.cast_zero, zero_mul, zero_add] at e1
      exact hirrl ⟨_, by rw [e1]; rfl⟩
  -- The algebra.
  obtain ⟨x, z, hx, hz⟩ := helper3_algebra hl hirrl hl0 (div_pos ha0 hc0) (div_pos hb0 hc0)
    (by rw [← hcos, ← hsin]; exact Real.cos_sq_add_sin_sq _) hina hinb e1 e2 hqr hsu
    (fun hno => by
      obtain ⟨h1, h2⟩ := halt1 hno
      have hall2 : ∀ e ∈ part2, edgeType D (tileγ D) e := fun e he => h1 e (hsub2 e he)
      refine ⟨?_, hzero part2 _ hαγ hall2, hzero part2 _ hβγ hall2⟩
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun e he => h2 e (Or.inl (hsub0 e he)))
  refine ⟨⟨x, z, hx, hz⟩, halt1 ?_⟩
  -- No relation: `j = (v x + v' z) λ` would make `λ` rational.
  intro j v v' hj he
  rw [hx, hz] at he
  have hx0 : 0 < x := by
    have : (0 : ℝ) < x * l := hx ▸ div_pos ha0 hc0
    exact_mod_cast pos_of_mul_pos_left this hl0.le
  have hz0 : 0 < z := by
    have : (0 : ℝ) < z * l := hz ▸ div_pos hb0 hc0
    exact_mod_cast pos_of_mul_pos_left this hl0.le
  have hS : (0 : ℚ) ≤ v * x + v' * z := by positivity
  have hS0 : (v * x + v' * z : ℚ) ≠ 0 := by
    intro h0
    have : ((v * x + v' * z : ℚ) : ℝ) = 0 := by exact_mod_cast h0
    have hj' : (j : ℝ) = 0 := by rw [he]; push_cast at this; linear_combination l * this
    exact absurd hj' (by exact_mod_cast hj.ne')
  apply hirrl
  refine ⟨j / (v * x + v' * z), ?_⟩
  have hS0' : ((v * x + v' * z : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hS0
  push_cast at hS0' ⊢
  rw [eq_div_iff hS0']
  linear_combination -he

end TriangleTiling
