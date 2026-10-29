/-
No `N`-tilings of the triquadratic triangle for `N < 28` (M. Beeson, *Triangle tiling: the case
3α + 2β = π*, arXiv 1206.2229v4): `lemma:twocsapplies`, `lemma:No14`, `lemma:No17`, `lemma:No7`,
`lemma:No23`, `lemma:Nolessthan28`.

Statements not yet checked by Beeson. The proofs differ from the paper's: with `M, K` from
`theorem:tilingequation`, the sides of `ABC` are `|BC| = cMN/K²`, `|AC| = c(K² - M²)/K`,
`|AB| = Kc` (`tq_sides`). By `lemma:twocs`, applied to any side, every side not of length `c` has
two `c` edges, so length at least `2c`. For `N = 7, 14, 23` the side `AC`, and for `N = 17` the
side `BC`, is shorter than `2c` (no use of `lemma:congruences` or `corollary:nokt` is needed).
-/
import TriangleTiling.Laczkovich.ThreeAlphaTilingEq
import TriangleTiling.TwoCs.TwoCs

namespace TriangleTiling.ThreeAlpha

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional EuclideanGeometry Set

theorem mem_uIcc_of {x y t : ℝ} (h1 : min x y ≤ t) (h2 : t ≤ max x y) : t ∈ Set.uIcc x y :=
  ⟨h1, h2⟩

/-- Two segments inside `AB`, meeting in at most a point, are together at most as long as `AB`. -/
theorem two_segments_le {A B u₁ v₁ u₂ v₂ : Plane} (hAB : A ≠ B)
    (h₁ : segment ℝ u₁ v₁ ⊆ segment ℝ A B) (h₂ : segment ℝ u₂ v₂ ⊆ segment ℝ A B)
    (h : (segment ℝ u₁ v₁ ∩ segment ℝ u₂ v₂).Subsingleton) :
    dist u₁ v₁ + dist u₂ v₂ ≤ dist A B := by
  have hu1 := h₁ (left_mem_segment _ _ _)
  have hv1 := h₁ (right_mem_segment _ _ _)
  have hu2 := h₂ (left_mem_segment _ _ _)
  have hv2 := h₂ (right_mem_segment _ _ _)
  rw [segment_eq_image_lineMap] at hu1 hv1 hu2 hv2
  obtain ⟨x₁, hx₁, rfl⟩ := hu1
  obtain ⟨y₁, hy₁, rfl⟩ := hv1
  obtain ⟨x₂, hx₂, rfl⟩ := hu2
  obtain ⟨y₂, hy₂, rfl⟩ := hv2
  rw [dist_lineMap_lineMap, dist_lineMap_lineMap, Real.dist_eq, Real.dist_eq,
    ← max_sub_min_eq_abs, ← max_sub_min_eq_abs]
  have hinj := AffineMap.lineMap_injective ℝ hAB
  have hmem : ∀ x y t : ℝ, min x y ≤ t → t ≤ max x y →
      AffineMap.lineMap A B t ∈ segment ℝ (AffineMap.lineMap A B x) (AffineMap.lineMap A B y) := by
    intro x y t h1 h2
    rw [← image_segment, segment_eq_uIcc]; exact ⟨t, mem_uIcc_of h1 h2, rfl⟩
  have hd := dist_nonneg (x := A) (y := B)
  have b1 : 0 ≤ min x₁ y₁ := le_min hx₁.1 hy₁.1
  have b2 : 0 ≤ min x₂ y₂ := le_min hx₂.1 hy₂.1
  have c1 : max x₁ y₁ ≤ 1 := max_le hx₁.2 hy₁.2
  have c2 : max x₂ y₂ ≤ 1 := max_le hx₂.2 hy₂.2
  have m1 := min_le_max (a := x₁) (b := y₁)
  have m2 := min_le_max (a := x₂) (b := y₂)
  have key : max x₁ y₁ - min x₁ y₁ + (max x₂ y₂ - min x₂ y₂) ≤ 1 := by
    by_contra hsum
    push Not at hsum
    set lo := max (min x₁ y₁) (min x₂ y₂)
    set hi := min (max x₁ y₁) (max x₂ y₂)
    have hlh : lo < hi := by
      simp only [lo, hi, max_lt_iff, lt_min_iff]
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
    have hl1 : min x₁ y₁ ≤ lo := le_max_left _ _
    have hl2 : min x₂ y₂ ≤ lo := le_max_right _ _
    have hh1 : hi ≤ max x₁ y₁ := min_le_left _ _
    have hh2 : hi ≤ max x₂ y₂ := min_le_right _ _
    have e := h ⟨hmem x₁ y₁ lo hl1 (by linarith), hmem x₂ y₂ lo hl2 (by linarith)⟩
      ⟨hmem x₁ y₁ hi (by linarith) hh1, hmem x₂ y₂ hi (by linarith) hh2⟩
    have := hinj e
    linarith
  rw [max_comm y₁ x₁, min_comm y₁ x₁, max_comm y₂ x₂, min_comm y₂ x₂]
  nlinarith [mul_le_mul_of_nonneg_left key hd]

variable {N : ℕ} (D : CongruentDissection N)

/-- **Two `c` edges on a side.** Edges of two different tiles inside a side of `ABC` are together at
most as long as the side. -/
theorem two_edges_le {p q : Fin 3} (hpq : p ≠ q) {i j : Fin N} (hij : i ≠ j) {m m' : Fin 3}
    (hi : (D.tile i).edge m ⊆ segment ℝ (D.target.pts p) (D.target.pts q))
    (hj : (D.tile j).edge m' ⊆ segment ℝ (D.target.pts p) (D.target.pts q)) :
    dist ((D.tile i).pts m) ((D.tile i).pts (m + 1)) +
      dist ((D.tile j).pts m') ((D.tile j).pts (m' + 1)) ≤ dist (D.target.pts p) (D.target.pts q) := by
  obtain ⟨r, hrp, hrq⟩ : ∃ r : Fin 3, r ≠ p ∧ r ≠ q :=
    (by decide : ∀ p q : Fin 3, p ≠ q → ∃ r : Fin 3, r ≠ p ∧ r ≠ q) p q hpq
  obtain ⟨g, c, hg, hgp, hgq, hgr⟩ := TwoCs.edge_level D.target hrp hpq.symm hrq
  have hAB : D.target.pts p ≠ D.target.pts q := fun h => hpq (D.target.indep.injective h)
  have hline : ∀ y ∈ segment ℝ (D.target.pts p) (D.target.pts q), (-g) y = -c := by
    intro y hy
    rw [segment_eq_image_lineMap] at hy
    obtain ⟨t, -, rfl⟩ := hy
    simp only [LinearMap.neg_apply, neg_inj]
    exact TriangleTiling.level_lineMap hgp hgq t
  have htgt : ∀ y ∈ D.target.carrier, (-g) y ≤ -c := by
    apply Tri.carrier_subset_halfplane
    intro k
    simp only [LinearMap.neg_apply, neg_le_neg_iff]
    have : k = p ∨ k = q ∨ k = r := by
      revert hrp hrq hpq; fin_cases p <;> fin_cases q <;> fin_cases r <;> fin_cases k <;> simp
    rcases this with rfl | rfl | rfl
    · exact hgp.ge
    · exact hgq.ge
    · exact hgr.le
  have hsub : ∀ k (y : Plane), y ∈ (D.tile k).carrier → y ∈ D.target.carrier := by
    intro k y hy; rw [← D.covers]; exact Set.mem_iUnion.mpr ⟨k, hy⟩
  have hsing := D.toDissection.sameside_edges_subsingleton (-g) (-c) (neg_ne_zero.mpr hg)
    (e₁ := (i, m)) (e₂ := (j, m')) (fun h => hij (congrArg Prod.fst h))
    (fun y hy => htgt y (hsub i y hy)) (fun y hy => htgt y (hsub j y hy))
    (fun y hy => hline y (hi hy)) (fun y hy => hline y (hj hy))
  exact two_segments_le hAB hi hj hsing

/-- **`lemma:twocs` on any side**, with `a, b` not multiples of each other. -/
theorem twocs_side {α β γ a b c : ℝ} (hT : TileSides D α β γ a b c) (hγ : Real.pi / 2 < γ)
    (hirr : ¬ ∃ q : ℚ, α / β = q) (hlt : ∀ k, D.target.angleAt k < γ)
    (hab : (¬ ∃ n : ℕ, a = n * b) ∧ (¬ ∃ n : ℕ, b = n * a)) {p q : Fin 3} (hpq : p ≠ q)
    (hlen : dist (D.target.pts p) (D.target.pts q) ≠ c) :
    2 * c ≤ dist (D.target.pts p) (D.target.pts q) := by
  obtain ⟨σ, hσ0, hσ2⟩ : ∃ σ : Equiv.Perm (Fin 3), σ 0 = p ∧ σ 2 = q :=
    (by decide : ∀ p q : Fin 3, p ≠ q → ∃ σ : Equiv.Perm (Fin 3), σ 0 = p ∧ σ 2 = q) p q hpq
  set D' := relabelTarget D σ
  have e0 : D'.target.pts 0 = D.target.pts p := by
    show D.target.pts (σ 0) = _; rw [hσ0]
  have e2 : D'.target.pts 2 = D.target.pts q := by
    show D.target.pts (σ 2) = _; rw [hσ2]
  obtain ⟨i, j, hij, ⟨m, hm, hlm⟩, ⟨m', hm', hlm'⟩⟩ := twocs D' hT hγ hirr
    (fun k => by rw [relabel_angleAt]; exact hlt (σ k)) (Or.inl hab)
    (by rw [e0, e2]; exact hlen)
  rw [e0, e2] at hm hm'
  have := two_edges_le D hpq hij hm hm'
  have e1 : dist ((D.tile i).pts m) ((D.tile i).pts (m + 1)) = c := hlm
  have e2 : dist ((D.tile j).pts m') ((D.tile j).pts (m' + 1)) = c := hlm'
  linarith

/-- **The sides of the triquadratic triangle.** With `M, K` as in `theorem:tilingequation`,
`a/c = M/K`, and `|BC| = cMN/K²`, `|AC| = c(K² - M²)/K`, `|AB| = Kc`. -/
theorem tq_sides {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hT : TileSides D α β γ a b c)
    (hshape : D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β) :
    ∃ M K : ℕ, 0 < M ∧ M < K ∧ M ^ 2 + N = 2 * K ^ 2 ∧ a / c = M / K ∧
      D.target.oppLen 0 = c * M * N / K ^ 2 ∧ D.target.oppLen 1 = c * (K ^ 2 - M ^ 2) / K ∧
      D.target.oppLen 2 = K * c := by
  obtain ⟨⟨M, K, hM, hK, hMK, -, hs⟩, -⟩ := tilingequation D hrel hT ⟨1, hshape⟩
  obtain ⟨hα, hβ, -, hS, hc, ha, -, ht0, ht1, -, -⟩ := model_facts D hrel hT
  set t := 2 * Real.cos (α + β)
  have hst : a / c = t := by rw [ha]; field_simp
  have htMK : t = M / K := by
    rw [← hs]
    simp only [t]
    rw [show α + β = Real.pi / 2 - α / 2 by linarith, Real.cos_pi_div_two_sub]
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hMKR : (M : ℝ) ^ 2 + N = 2 * K ^ 2 := by exact_mod_cast hMK
  have hMltK : M < K := by
    have : (M : ℝ) / K < 1 := htMK ▸ ht1
    rw [div_lt_one hKR] at this
    exact_mod_cast this
  -- `Λ = K`.
  have ar := (shapeareas D hrel hT).1 hshape
  rw [hst, htMK] at ar
  have hΛ : 0 < Lam D := div_pos (circumdiam_pos _) (circumdiam_pos _)
  have hΛK : Lam D = K := by
    have h2 : (2 : ℝ) - ((M : ℝ) / K) ^ 2 = N / (K : ℝ) ^ 2 := by
      field_simp; linarith
    rw [h2, div_eq_div_iff (by positivity) (by positivity)] at ar
    have hMK' : (M : ℝ) < K := by exact_mod_cast hMltK
    have hN0 : (0 : ℝ) < N := by nlinarith
    have : (Lam D) ^ 2 = (K : ℝ) ^ 2 := by
      have h' : (N : ℝ) * (Lam D ^ 2 - K ^ 2) = 0 := by
        first | linear_combination ar | linear_combination -ar
      rcases mul_eq_zero.mp h' with h | h
      · linarith
      · linarith
    nlinarith [sq_nonneg (Lam D - K), sq_nonneg (Lam D + K)]
  have r := sines hα hβ hrel
  dsimp only at r
  obtain ⟨-, r2, -, r4, r5, -, -, -⟩ := r
  rw [div_eq_iff hS.ne'] at r2 r4 r5
  have s0 := target_side D hrel hT 0
  have s1 := target_side D hrel hT 1
  have s2 := target_side D hrel hT 2
  rw [hshape.1, r5, hΛK] at s0
  rw [hshape.2.1, r2, hΛK] at s1
  rw [hshape.2.2, r4, hΛK] at s2
  simp only [t] at htMK
  rw [htMK] at s0 s1
  have hS' := hS.ne'
  refine ⟨M, K, hM, hMltK, hMK, hst.trans htMK, ?_, ?_, ?_⟩
  · rw [s0]
    have hN : (N : ℝ) = 2 * K ^ 2 - M ^ 2 := by linarith
    rw [hN]; field_simp
  · rw [s1]; field_simp
  · rw [s2]; field_simp

/-- `|AC| ≠ c` for the triquadratic triangle: else `M² = K(K - 1)`, strictly between `(K - 1)²`
and `K²`. -/
theorem sq_ne_mul_pred {M K : ℕ} (hM : 0 < M) (hMK : M < K) : M ^ 2 ≠ K * (K - 1) := by
  intro h
  have h1 : (K - 1) ^ 2 < M ^ 2 := by
    rw [h]
    have : 1 ≤ K := by omega
    obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    have : 1 ≤ k := by omega
    nlinarith
  have h2 : M ^ 2 < K ^ 2 := by
    rw [h]
    obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    nlinarith
  have h3 : K - 1 < M := (Nat.pow_lt_pow_iff_left (by norm_num)).mp h1
  have h4 : M < K := hMK
  omega

/-- `α/β` is irrational when `3α + 2β = π` and `α ∉ ℚπ`. -/
theorem irr_ratio {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (hα : 0 < α) (hβ : 0 < β)
    (hirr : IrrPi α) : ¬ ∃ q : ℚ, α / β = q := by
  rintro ⟨q, hq⟩
  have hq0 : (0 : ℝ) < q := by rw [← hq]; positivity
  apply hirr
  refine ⟨q / (3 * q + 2), ?_⟩
  have hα' : α = q * β := by rw [← hq]; field_simp
  push_cast
  have : β = Real.pi / (3 * q + 2) := by
    rw [eq_div_iff (by positivity)]; rw [hα'] at hrel; linarith
  rw [hα', this]; field_simp

/-- **Lemma `lemma:twocsapplies`.** Assume triangle `ABC` has angles `(2α, β, α + β)` with
`3α + 2β = π`, that `α` is not a rational multiple of `π`, and that there is an `N`-tiling.
Suppose that neither of `a, b` is an integer multiple of the other. Then `f ≥ 2`, where `f` is the
number of `c` edges on the side `AC`. -/
theorem twocsapplies {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (hirr : IrrPi α)
    (hT : TileSides D α β γ a b c)
    (hshape : D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β)
    (hab : (¬ ∃ n : ℕ, a = n * b) ∧ (¬ ∃ n : ℕ, b = n * a)) :
    ∃ i j : Fin N, i ≠ j ∧
      (∃ m : Fin 3, (D.tile i).edge m ⊆ segment ℝ (D.target.pts 0) (D.target.pts 2) ∧
        dist ((D.tile i).pts m) ((D.tile i).pts (m + 1)) = c) ∧
      (∃ m : Fin 3, (D.tile j).edge m ⊆ segment ℝ (D.target.pts 0) (D.target.pts 2) ∧
        dist ((D.tile j).pts m) ((D.tile j).pts (m + 1)) = c) := by
  obtain ⟨hα, hβ, hγ, -, hc, -⟩ := model_facts D hrel hT
  refine twocs D hT (by rw [hγ]; linarith) (irr_ratio hrel hα hβ hirr) (fun k => ?_) (Or.inl hab) ?_
  · fin_cases k
    · show D.target.angleAt 0 < γ; rw [hshape.1, hγ]; linarith
    · show D.target.angleAt 1 < γ; rw [hshape.2.1, hγ]; linarith
    · show D.target.angleAt 2 < γ; rw [hshape.2.2, hγ]; linarith
  · obtain ⟨M, K, hM, hMK, hN, -, -, hY, -⟩ := tq_sides D hrel hT hshape
    intro h
    have hY' : D.target.oppLen 1 = dist (D.target.pts 0) (D.target.pts 2) := by
      unfold Tri.oppLen; exact dist_comm _ _
    rw [hY', h] at hY
    have hKR : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
    have h2 : (M : ℝ) ^ 2 = K * (K - 1) := by
      field_simp at hY
      nlinarith
    apply sq_ne_mul_pred hM hMK
    have : ((M ^ 2 : ℕ) : ℝ) = ((K * (K - 1) : ℕ) : ℝ) := by
      push_cast [show 1 ≤ K by omega]; exact h2
    exact_mod_cast this

/-- **The short-side criterion.** For `M, K` of `theorem:tilingequation`, it cannot be that `a, b`
are not multiples of each other while `|AC|` or `|BC|` is shorter than `2c` (and not `c`). -/
theorem tq_no {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (hirr : IrrPi α)
    (hT : TileSides D α β γ a b c)
    (hshape : D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β) :
    ∃ M K : ℕ, 0 < M ∧ M < K ∧ M * M + N = 2 * (K * K) ∧
      ¬ (((K * K - M * M < 2 * K ∧ K * K - M * M ≠ K) ∨
          (M * N < 2 * (K * K) ∧ M * N ≠ K * K)) ∧
        (∀ n : ℕ, M * K ≠ n * (K * K - M * M)) ∧ (∀ n : ℕ, K * K - M * M ≠ n * (M * K))) := by
  obtain ⟨M, K, hM, hMK, hN, hs, hX, hY, -⟩ := tq_sides D hrel hT hshape
  refine ⟨M, K, hM, hMK, by rw [← sq, ← sq]; exact hN, ?_⟩
  rintro ⟨hshort, hn1, hn2⟩
  obtain ⟨hα, hβ, hγ, -, hc, ha, hb, -, -, -, -⟩ := model_facts D hrel hT
  have hKR : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hle : M * M ≤ K * K := Nat.mul_le_mul hMK.le hMK.le
  have hsub : ((K * K - M * M : ℕ) : ℝ) = (K : ℝ) ^ 2 - (M : ℝ) ^ 2 := by
    push_cast [hle]; ring
  have hst : a / c = 2 * Real.cos (α + β) := by rw [ha]; field_simp
  have ea : a = (M / K) * c := by rw [← hs]; field_simp
  have eb : b = (1 - (M / K) ^ 2) * c := by rw [hb, ← hst, hs]
  have hab : (¬ ∃ n : ℕ, a = n * b) ∧ (¬ ∃ n : ℕ, b = n * a) := by
    constructor
    · rintro ⟨n, hn⟩
      apply hn1 n
      have : ((M * K : ℕ) : ℝ) = ((n * (K * K - M * M) : ℕ) : ℝ) := by
        rw [Nat.cast_mul, Nat.cast_mul n, hsub, ea, eb] at *
        push_cast
        field_simp at hn
        linear_combination hn
      exact_mod_cast this
    · rintro ⟨n, hn⟩
      apply hn2 n
      have : ((K * K - M * M : ℕ) : ℝ) = ((n * (M * K) : ℕ) : ℝ) := by
        rw [hsub]
        rw [ea, eb] at hn
        push_cast
        field_simp at hn
        linear_combination hn
      exact_mod_cast this
  have hlt : ∀ k, D.target.angleAt k < γ := by
    intro k
    fin_cases k
    · show D.target.angleAt 0 < γ; rw [hshape.1, hγ]; linarith
    · show D.target.angleAt 1 < γ; rw [hshape.2.1, hγ]; linarith
    · show D.target.angleAt 2 < γ; rw [hshape.2.2, hγ]; linarith
  have hγ' : Real.pi / 2 < γ := by rw [hγ]; linarith
  have hirr' := irr_ratio hrel hα hβ hirr
  rcases hshort with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- the side `AC`
    have hY' : dist (D.target.pts 0) (D.target.pts 2) = c * ((K : ℝ) ^ 2 - M ^ 2) / K := by
      rw [← hY]; unfold Tri.oppLen; exact dist_comm _ _
    have hne : dist (D.target.pts 0) (D.target.pts 2) ≠ c := by
      rw [hY']
      intro h
      apply h2
      have : ((K * K - M * M : ℕ) : ℝ) = (K : ℝ) := by
        rw [hsub]; field_simp at h; nlinarith
      exact_mod_cast this
    have := twocs_side D hT hγ' hirr' hlt hab (by decide : (0 : Fin 3) ≠ 2) hne
    rw [hY'] at this
    have h3 : ((2 * K : ℕ) : ℝ) ≤ ((K * K - M * M : ℕ) : ℝ) := by
      rw [hsub]; push_cast
      rw [le_div_iff₀ hKR] at this
      nlinarith
    have := (Nat.cast_le (α := ℝ)).mp h3
    omega
  · -- the side `BC`
    have hX' : dist (D.target.pts 1) (D.target.pts 2) = c * M * N / (K : ℝ) ^ 2 := hX
    have hne : dist (D.target.pts 1) (D.target.pts 2) ≠ c := by
      rw [hX']
      intro h
      apply h2
      have : ((M * N : ℕ) : ℝ) = ((K * K : ℕ) : ℝ) := by
        push_cast; field_simp at h; nlinarith
      exact_mod_cast this
    have := twocs_side D hT hγ' hirr' hlt hab (by decide : (1 : Fin 3) ≠ 2) hne
    rw [hX'] at this
    have h3 : ((2 * (K * K) : ℕ) : ℝ) ≤ ((M * N : ℕ) : ℝ) := by
      push_cast
      rw [le_div_iff₀ (by positivity)] at this
      have h4 : c * (2 * ((K : ℝ) * K)) ≤ c * ((M : ℝ) * N) := by linarith [this]
      exact le_of_mul_le_mul_left h4 hc
    have := (Nat.cast_le (α := ℝ)).mp h3
    omega

/-- **Lemma `lemma:Nolessthan28`.** Let `3α + 2β = π` and suppose triangle `ABC` has angles
`(A, B, C) = (2α, β, α + β)`, and `α` is not a rational multiple of `π`. Then there is no `N`-tiling
of `ABC` for `N < 28`. -/
theorem Nolessthan28 {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (hirr : IrrPi α)
    (hT : TileSides D α β γ a b c)
    (hshape : D.target.angleAt 0 = 2 * α ∧ D.target.angleAt 1 = β ∧ D.target.angleAt 2 = α + β)
    (hN : N < 28) : False := by
  obtain ⟨M, K, hM, hMK, hMKN, hno⟩ := tq_no D hrel hirr hT hshape
  have hK : K < 6 := by nlinarith
  interval_cases K <;> interval_cases M <;> first
    | omega
    | exact hno ⟨Or.inl ⟨by omega, by omega⟩, fun n => by omega, fun n => by omega⟩
    | exact hno ⟨Or.inr ⟨by omega, by omega⟩, fun n => by omega, fun n => by omega⟩

/-- An `N`-tiling of a triangle with angles `(2α, β, α + β)` in any order, `N < 28`: none. -/
theorem no_lt28 {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi) (hirr : IrrPi α)
    (hT : TileSides D α β γ a b c) (hshape : TgtAngles D (2 * α) β (α + β)) (hN : N < 28) :
    False := by
  obtain ⟨σ, h0, h1, h2⟩ := hshape
  exact Nolessthan28 (relabelTarget D σ) hrel hirr hT
    ⟨by rw [relabel_angleAt]; exact h0, by rw [relabel_angleAt]; exact h1,
      by rw [relabel_angleAt]; exact h2⟩ hN

/-- **Lemma `lemma:No14`.** There is no `14`-tiling of a triangle with angles `(2α, β, α + β)`, where
`3α + 2β = π` and `α` is not a rational multiple of `π`. -/
theorem No14 (D : CongruentDissection 14) {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : IrrPi α) (hT : TileSides D α β γ a b c) (hshape : TgtAngles D (2 * α) β (α + β)) :
    False := no_lt28 D hrel hirr hT hshape (by norm_num)

/-- **Lemma `lemma:No17`.** There is no `17`-tiling of a triangle with angles `(2α, β, α + β)`, where
`3α + 2β = π` and `α` is not a rational multiple of `π`. -/
theorem No17 (D : CongruentDissection 17) {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : IrrPi α) (hT : TileSides D α β γ a b c) (hshape : TgtAngles D (2 * α) β (α + β)) :
    False := no_lt28 D hrel hirr hT hshape (by norm_num)

/-- **Lemma `lemma:No7`.** There is no `7`-tiling of a triangle with angles `(2α, β, α + β)`, where
`3α + 2β = π` and `α` is not a rational multiple of `π`. -/
theorem No7 (D : CongruentDissection 7) {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : IrrPi α) (hT : TileSides D α β γ a b c) (hshape : TgtAngles D (2 * α) β (α + β)) :
    False := no_lt28 D hrel hirr hT hshape (by norm_num)

/-- **Lemma `lemma:No23`.** There is no `23`-tiling of a triangle with angles `(2α, β, α + β)`, where
`3α + 2β = π` and `α` is not a rational multiple of `π`. -/
theorem No23 (D : CongruentDissection 23) {α β γ a b c : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : IrrPi α) (hT : TileSides D α β γ a b c) (hshape : TgtAngles D (2 * α) β (α + β)) :
    False := no_lt28 D hrel hirr hT hshape (by norm_num)

end TriangleTiling.ThreeAlpha
