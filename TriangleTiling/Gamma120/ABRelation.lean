/-
`lemma:abrelation` (Section 11 of M. Beeson, *Tilings of an isosceles triangle*): if the
isosceles triangle `ABC` with base angles `α` (`α ∉ ℚπ`) is `N`-tiled by `(α, β, 2π/3)`, there
are relations `j a = p b + q c` and `J b = P a + Q c` with `j, J > 0`.

The paper's degree count on `Γ_a` (and `Γ_b`), with its table of vertex types replaced by the
vertex relations `n₀ = n₁`, `n₁ + 2 n₂ + 3 n₃ + 6 n₄ = 3 t` (`counts_noncorner`). At a vertex `v`
other than `A, B, C` put `μ v = n₁ - n₂` (a multiple of `3`). Then

* `∑ μ = -3`: the weight `n₀ + n₁ - 2 n₂` adds up to `N + N - 2N = 0`; it is `2 μ` away from the
  corners and `1, 4, 1` at `A, B, C` (`sum_mu`);
* `3 · in(v) ≤ 3 · out(v) + μ v` at every vertex (`degree_bound`): if `μ < 0` the vertex is a
  center (three `γ` angles), where no link ends and one starts (`out_of_center`); if `μ = 0`
  the marked edges there (`n₁ + n₂ = 2 n₁` of them) are even, so a link ending there is followed
  by another (`out_of_in`); if `μ > 0` then `μ ≥ 3` and there is nothing to show.

Summing, `0 ≤ -3`. The paper's centers are the vertices with `μ = -3`, its stars, anomalies and
double stars those with `μ = 3, 3, 6`.
-/
import TriangleTiling.Gamma120.CRelation
import TriangleTiling.Tiling.Center

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry Set

/-- Each tile has exactly one angle `θ ∈ {α, β, γ}`, so these angles number `N` in all. -/
theorem sum_angleCount_sep [DecidableEq Plane] {N : ℕ} (D : CongruentDissection N)
    (hsep : AnglesSep D) (W : Finset Plane) (hW : ∀ i k, (D.tile i).pts k ∈ W) (θ : ℝ)
    (hθ : θ = tileα D ∨ θ = tileβ D ∨ θ = tileγ D) :
    ∑ v ∈ W, angleCount D v θ = N := by
  obtain ⟨hv0, hinj⟩ := hsep
  have ne : ∀ x y : Fin 5, x ≠ y →
      ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] x ≠
        ![tileα D, tileβ D, tileγ D, Real.pi, 2 * Real.pi] y := fun x y h => hinj.ne h
  have hθ0 : θ ≠ 0 ∧ θ ≠ Real.pi ∧ θ ≠ 2 * Real.pi := by
    rcases hθ with rfl | rfl | rfl
    · exact ⟨hv0 0, ne 0 3 (by decide), ne 0 4 (by decide)⟩
    · exact ⟨hv0 1, ne 1 3 (by decide), ne 1 4 (by decide)⟩
    · exact ⟨hv0 2, ne 2 3 (by decide), ne 2 4 (by decide)⟩
  simp only [angleCount, Finset.card_filter]
  rw [Finset.sum_comm]
  have : ∀ i : Fin N, (∑ v ∈ W, if (D.tile i).localAngle v = θ then 1 else 0) = 1 := by
    intro i
    rw [← Finset.card_filter, filter_localAngle_eq (D.tile i) W (hW i) θ hθ0.1 hθ0.2.1 hθ0.2.2,
      Finset.card_image_of_injective _ (D.tile i).indep.injective]
    rcases hθ with rfl | rfl | rfl
    · exact (tile_angle_count_sep D ⟨hv0, hinj⟩ i).1
    · exact (tile_angle_count_sep D ⟨hv0, hinj⟩ i).2.1
    · exact (tile_angle_count_sep D ⟨hv0, hinj⟩ i).2.2
  rw [Finset.sum_congr rfl fun i _ => this i]
  simp

open Classical in
/-- **A relation for `b` from edges**: `J b = p a + q c` with `J > 0`. -/
theorem b_relation_of_edges {N : ℕ} (D : CongruentDissection N) (hsep : AnglesSep D)
    (h : HasRelation D.toDissection (edgeType D (tileβ D))) :
    ∃ J p q : ℕ, 0 < J ∧
    (J : ℝ) * dist (D.model.pts 2) (D.model.pts 0)
      = p * dist (D.model.pts 1) (D.model.pts 2) + q * dist (D.model.pts 0) (D.model.pts 1) := by
  obtain ⟨hαβ, hαγ, hβγ⟩ := types_ne D hsep
  obtain ⟨ha, hb, hc⟩ := model_sides_pos D
  obtain ⟨s₁, s₂, h1, ⟨e, he, hne⟩, hrel⟩ := relation_counts D hsep h
  have f1 : s₁.filter (edgeType D (tileα D)) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun x hx h' => hαβ (h'.symm.trans (h1 x hx))
  have f2 : s₁.filter (edgeType D (tileβ D)) = s₁ := Finset.filter_true_of_mem h1
  have f3 : s₁.filter (edgeType D (tileγ D)) = ∅ :=
    Finset.filter_eq_empty_iff.mpr fun x hx h' => hβγ ((h1 x hx).symm.trans h')
  rw [f1, f2, f3, Finset.card_empty, Nat.cast_zero, zero_mul, zero_mul, zero_add, add_zero] at hrel
  set pα := (s₂.filter (edgeType D (tileα D))).card
  set pβ := (s₂.filter (edgeType D (tileβ D))).card
  set pγ := (s₂.filter (edgeType D (tileγ D))).card
  have hpos : 1 ≤ pα + pγ := by
    rcases localAngle_at_own_vertex_mem' D e.1 (e.2 + 2) with h | h | h
    · have : 1 ≤ pα := Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, h⟩⟩; omega
    · exact absurd h hne
    · have : 1 ≤ pγ := Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, h⟩⟩; omega
  have hlt : pβ < s₁.card := by
    by_contra hle
    push Not at hle
    have h3 : (s₁.card : ℝ) ≤ pβ := by exact_mod_cast hle
    have h5 : (0 : ℝ) < pα * dist (D.model.pts 1) (D.model.pts 2)
        + pγ * dist (D.model.pts 0) (D.model.pts 1) := by
      rcases Nat.eq_zero_or_pos pα with h0 | h0
      · have : (1 : ℝ) ≤ pγ := by rw [h0] at hpos; exact_mod_cast (by omega : 1 ≤ pγ)
        rw [h0, Nat.cast_zero, zero_mul, zero_add]; nlinarith
      · have : (1 : ℝ) ≤ pα := by exact_mod_cast h0
        have : (0 : ℝ) ≤ pγ := Nat.cast_nonneg _
        nlinarith
    nlinarith
  refine ⟨s₁.card - pβ, pα, pγ, by omega, ?_⟩
  rw [Nat.cast_sub hlt.le]
  linarith

variable {N : ℕ} (D : CongruentDissection N) (hγ : tileγ D = 2 * Real.pi / 3)
  (hirr : ¬ ∃ r : ℚ, tileα D = (r : ℝ) * Real.pi)
include hγ hirr

omit hirr in
/-- **No half at a center**: where only `γ` angles occur, no tiles have angles adding up to `π`. -/
theorem no_half120 {Q : Plane} (h0 : angleCount D Q (tileα D) = 0)
    (h1 : angleCount D Q (tileβ D) = 0) (h3 : angleCount D Q Real.pi = 0)
    (h4 : angleCount D Q (2 * Real.pi) = 0) (S : Finset (Fin N)) :
    ∑ i ∈ S, (D.tile i).localAngle Q ≠ Real.pi := by
  classical
  have hval : ∀ i, (D.tile i).localAngle Q = tileγ D ∨ (D.tile i).localAngle Q = 0 := by
    intro i
    rcases localAngle_mem D Q i with h | h | h | h | h | h
    · exfalso; have := angleCount_pos D (show (D.tile i).localAngle Q = tileα D from h); omega
    · exfalso; have := angleCount_pos D (show (D.tile i).localAngle Q = tileβ D from h); omega
    · exact Or.inl h
    · exfalso; have := angleCount_pos D h; omega
    · exfalso; have := angleCount_pos D h; omega
    · exact Or.inr h
  have hγ0 : tileγ D ≠ 0 := by rw [hγ]; positivity
  have hpt : ∀ i ∈ S, (D.tile i).localAngle Q =
      if (D.tile i).localAngle Q = tileγ D then tileγ D else 0 := by
    intro i _
    rcases hval i with h | h
    · rw [if_pos h, h]
    · rw [if_neg (by rw [h]; exact hγ0.symm), h]
  intro hsum
  rw [Finset.sum_congr rfl hpt, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul] at hsum
  set k := (S.filter fun i => (D.tile i).localAngle Q = tileγ D).card
  rw [hγ] at hsum
  have hpi := Real.pi_pos
  have : ((2 * k : ℕ) : ℝ) = ((3 : ℕ) : ℝ) := by
    push_cast
    have : (k : ℝ) * (2 * Real.pi / 3) * 3 = Real.pi * 3 := by rw [hsum]
    nlinarith
  have := Nat.cast_injective this
  omega

variable (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileα D)
  (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileα D)
include hA hC

open Classical in
/-- **`∑ μ = -3`.** -/
theorem sum_mu (W : Finset Plane) (hW : ∀ i k, (D.tile i).pts k ∈ W)
    (hWc : ∀ m, D.target.pts m ∈ W)
    (hWv : ∀ v ∈ W, v ∉ Set.range D.target.pts → v ∈ D.target.carrier) :
    ∑ v ∈ W, (if v ∈ Set.range D.target.pts then (0 : ℤ)
      else (angleCount D v (tileβ D) : ℤ) - angleCount D v (tileγ D)) = -3 := by
  have hsep := (angle_values120 D hγ hirr).2
  have sα := sum_angleCount_sep D hsep W hW _ (Or.inl rfl)
  have sβ := sum_angleCount_sep D hsep W hW _ (Or.inr (Or.inl rfl))
  have sγ := sum_angleCount_sep D hsep W hW _ (Or.inr (Or.inr rfl))
  have hzero : ∑ v ∈ W, ((angleCount D v (tileα D) : ℤ) + angleCount D v (tileβ D)
      - 2 * angleCount D v (tileγ D)) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    have e1 : ∑ v ∈ W, (angleCount D v (tileα D) : ℤ) = N := by exact_mod_cast sα
    have e2 : ∑ v ∈ W, (angleCount D v (tileβ D) : ℤ) = N := by exact_mod_cast sβ
    have e3 : ∑ v ∈ W, (angleCount D v (tileγ D) : ℤ) = N := by exact_mod_cast sγ
    rw [e1, e2, e3]; ring
  -- Away from the corners the weight is `2 μ`.
  have hpt : ∀ v ∈ W, ((angleCount D v (tileα D) : ℤ) + angleCount D v (tileβ D)
      - 2 * angleCount D v (tileγ D)) =
      (if v ∈ Set.range D.target.pts then ((angleCount D v (tileα D) : ℤ)
        + angleCount D v (tileβ D) - 2 * angleCount D v (tileγ D)) else 0)
      + 2 * (if v ∈ Set.range D.target.pts then (0 : ℤ)
        else (angleCount D v (tileβ D) : ℤ) - angleCount D v (tileγ D)) := by
    intro v hv
    by_cases hvc : v ∈ Set.range D.target.pts
    · simp [hvc]
    · have := (counts_noncorner D hγ hirr (hWv v hv hvc) hvc).1
      simp only [hvc, if_false, zero_add]
      omega
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, ← Finset.mul_sum] at hzero
  -- At the corners the weight is `1, 4, 1`.
  have hcorner : ∑ v ∈ W, (if v ∈ Set.range D.target.pts then ((angleCount D v (tileα D) : ℤ)
      + angleCount D v (tileβ D) - 2 * angleCount D v (tileγ D)) else 0) = 6 := by
    rw [← Finset.sum_filter]
    have hset : W.filter (fun v => v ∈ Set.range D.target.pts) =
        Finset.univ.image D.target.pts := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and, Set.mem_range]
      constructor
      · rintro ⟨-, h⟩; exact h
      · rintro ⟨m, rfl⟩; exact ⟨hWc m, m, rfl⟩
    rw [hset, Finset.sum_image (fun x _ y _ h => D.target.indep.injective h), Fin.sum_univ_three]
    obtain ⟨⟨a0, a1, a2⟩, ⟨c0, c1, c2⟩, ⟨b0, b1, b2⟩⟩ := corner_counts120 D hγ hirr hA hC
    rw [a0, a1, a2, b0, b1, b2, c0, c1, c2]
    norm_num
  rw [hcorner] at hzero
  linarith

open Classical in
/-- **`lemma:abrelation` for the marked type `φ ∈ {α, β}`, as edges.** -/
theorem marked_relation_edges (φ : ℝ) (hφ : φ = tileα D ∨ φ = tileβ D) :
    HasRelation D.toDissection (edgeType D φ) := by
  by_contra hnorel
  have hsep := (angle_values120 D hγ hirr).2
  set θ := edgeType D φ
  set TV := tilingVertices D
  set W := TV ∪ Finset.univ.image D.target.pts with hWdef
  have hW : ∀ i k, (D.tile i).pts k ∈ W := fun i k =>
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(i, k), Finset.mem_univ _, rfl⟩)
  have hWc : ∀ m, D.target.pts m ∈ W := fun m =>
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨m, Finset.mem_univ _, rfl⟩)
  have hWTV : ∀ v ∈ W, v ∉ Set.range D.target.pts → v ∈ TV := by
    intro v hv hvc
    rcases Finset.mem_union.mp hv with h | h
    · exact h
    · exact absurd (by obtain ⟨m, -, rfl⟩ := Finset.mem_image.mp h; exact ⟨m, rfl⟩) hvc
  have hWv : ∀ v ∈ W, v ∉ Set.range D.target.pts → v ∈ D.target.carrier := by
    intro v hv hvc
    obtain ⟨i, k, rfl⟩ := (mem_tilingVertices D).mp (hWTV v hv hvc)
    rw [← D.covers]
    exact Set.mem_iUnion.mpr ⟨i, subset_convexHull ℝ _ ⟨k, rfl⟩⟩
  have hlinkW : ∀ {u w}, IsLink D.toDissection θ u w → u ∈ W ∧ w ∈ W := fun h =>
    ⟨Finset.mem_union_left _ (link_mem_vertices D h).1,
      Finset.mem_union_left _ (link_mem_vertices D h).2⟩
  -- The marked edges at a point.
  have hmarked : ∀ v, ((edgesAt D.toDissection v).filter θ).card + angleCount D v φ =
      angleCount D v (tileα D) + angleCount D v (tileβ D) + angleCount D v (tileγ D) :=
    fun v => card_marked D hsep v (φ := φ) (by rcases hφ with h | h <;> simp [h])
  have hφc : ∀ v, angleCount D v (tileα D) = angleCount D v (tileβ D) →
      angleCount D v φ = angleCount D v (tileβ D) := by
    intro v h; rcases hφ with rfl | rfl
    · exact h
    · rfl
  -- The degree bound.
  have key : ∀ v ∈ W, 3 * ((W.filter fun u => IsLink D.toDissection θ u v).card : ℤ) ≤
      3 * ((W.filter fun w => IsLink D.toDissection θ v w).card : ℤ) +
        (if v ∈ Set.range D.target.pts then (0 : ℤ)
          else (angleCount D v (tileβ D) : ℤ) - angleCount D v (tileγ D)) := by
    intro v hv
    have hin1 := in_le_one D.toDissection θ W v
    by_cases hvc : v ∈ Set.range D.target.pts
    · -- No link ends at a corner.
      have hin0 : (W.filter fun u => IsLink D.toDissection θ u v).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro u - ⟨g, c, hl⟩
        obtain ⟨m, rfl⟩ := hvc
        exact corner_not_interior D m hl.end_interior
      rw [if_pos hvc, hin0]
      positivity
    rw [if_neg hvc]
    obtain ⟨i, k, hik⟩ := (mem_tilingVertices D).mp (hWTV v hv hvc)
    have hpos := vertex_counts_pos D hik
    obtain ⟨heq, hcase⟩ := counts_noncorner D hγ hirr (hWv v hv hvc) hvc
    have hm := hmarked v
    have hφv := hφc v heq
    rcases lt_trichotomy (angleCount D v (tileβ D)) (angleCount D v (tileγ D)) with hlt | heq' | hgt
    · -- A center: three `γ` angles and nothing else.
      have hint : v ∈ interior D.target.carrier := by
        rcases hcase with ⟨h, -⟩ | ⟨-, h⟩
        · exact h
        · exfalso; omega
      have hc : angleCount D v (tileβ D) = 0 ∧ angleCount D v (tileγ D) = 3 ∧
          angleCount D v Real.pi = 0 ∧ angleCount D v (2 * Real.pi) = 0 := by
        rcases hcase with ⟨-, h⟩ | ⟨h', -⟩
        · omega
        · exact absurd hint h'.2
      obtain ⟨c1, c2, c3, c4⟩ := hc
      have hnrel : ∀ j : Fin N, ∀ m : Fin 3,
          v ∉ openSegment ℝ ((D.tile j).pts m) ((D.tile j).pts (m + 1)) := by
        intro j m hv'
        have := angleCount_pos D (Tri.localAngle_openSegment _ m hv')
        omega
      have hin0 : (W.filter fun u => IsLink D.toDissection θ u v).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        rintro u - ⟨g, c, hl⟩
        obtain ⟨ε, -, hRε⟩ := hl.across
        exact hnrel _ _ hRε
      obtain ⟨R, hR⟩ := out_of_center D.toDissection θ hint hnrel ⟨1, by omega⟩
        (no_half120 D hγ (by omega) c1 c3 c4) hnorel
      have : 1 ≤ (W.filter fun w => IsLink D.toDissection θ v w).card :=
        Finset.card_pos.mpr ⟨R, Finset.mem_filter.mpr ⟨(hlinkW hR).2, hR⟩⟩
      rw [hin0]; push_cast; omega
    · -- `μ = 0`: a link ending here is followed by another.
      rcases Nat.eq_zero_or_pos (W.filter fun u => IsLink D.toDissection θ u v).card with h0 | hp
      · rw [h0]; push_cast; omega
      · obtain ⟨u, hu⟩ := Finset.card_pos.mp hp
        obtain ⟨-, g, c, hl⟩ := Finset.mem_filter.mp hu
        obtain ⟨R', hR'⟩ := out_of_in D.toDissection θ hl
          ⟨angleCount D v (tileβ D), by omega⟩ hnorel
        have : 1 ≤ (W.filter fun w => IsLink D.toDissection θ v w).card :=
          Finset.card_pos.mpr ⟨R', Finset.mem_filter.mpr ⟨(hlinkW hR').2, hR'⟩⟩
        omega
    · -- `μ > 0`, so `μ ≥ 3`.
      have : 3 ≤ (angleCount D v (tileβ D) : ℤ) - angleCount D v (tileγ D) := by
        rcases hcase with ⟨-, h⟩ | ⟨-, h⟩ <;> omega
      omega
  have hsum := Finset.sum_le_sum key
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_mu D hγ hirr hA hC W hW hWc hWv] at hsum
  have hio := sum_out_eq_sum_in D.toDissection θ W
  have : (∑ v ∈ W, ((W.filter fun w => IsLink D.toDissection θ v w).card : ℤ)) =
      ∑ v ∈ W, ((W.filter fun u => IsLink D.toDissection θ u v).card : ℤ) := by
    rw [← Nat.cast_sum, ← Nat.cast_sum]; exact_mod_cast hio
  linarith

/-- **Lemma `lemma:abrelation`.** Let the isosceles triangle `ABC` with base angles `α`
(`α ∉ ℚπ`) be `N`-tiled by `(α, β, 2π/3)`. Then `j a = p b + q c` and `J b = P a + Q c` with
`j, J > 0`. -/
theorem abrelation :
    (∃ j p q : ℕ, 0 < j ∧ (j : ℝ) * dist (D.model.pts 1) (D.model.pts 2)
      = p * dist (D.model.pts 2) (D.model.pts 0) + q * dist (D.model.pts 0) (D.model.pts 1)) ∧
    (∃ J P Q : ℕ, 0 < J ∧ (J : ℝ) * dist (D.model.pts 2) (D.model.pts 0)
      = P * dist (D.model.pts 1) (D.model.pts 2) + Q * dist (D.model.pts 0) (D.model.pts 1)) :=
  ⟨a_relation_of_edges D (angle_values120 D hγ hirr).2
      (marked_relation_edges D hγ hirr hA hC _ (Or.inl rfl)),
    b_relation_of_edges D (angle_values120 D hγ hirr).2
      (marked_relation_edges D hγ hirr hA hC _ (Or.inr rfl))⟩

end TriangleTiling
