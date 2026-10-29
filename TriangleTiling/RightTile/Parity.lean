/-
The parity step of `theorem:isosceles2`: `N` is even.

Let the isosceles triangle `ABC` with base angles `β` be `N`-tiled by the tile `(α, β, π/2)`,
`α ∉ ℚπ`, with legs in the ratio `a : b = p : q` (`p, q` odd), `c/a` irrational, and the base `AC`
made of `c` edges. Then `N` is even.

The paper's argument, by direction classes. Here the class of an edge is
`DirClass.Cls (4α) (dirC v)` for the edge's vector `v`:

* the two legs of a tile are perpendicular, so exactly one of them has class `0`; hence the legs
  of class `0` number `N` (`legs_count`);
* weight each leg by `p` (an `a` edge) or `q` (a `b` edge), both odd, and each hypotenuse by `0`;
  the total weight of the legs of class `0` is then `N` modulo `2`;
* on a line through the interior, the two sides carry edges of equal total length
  (`line_balance`), so (as `c/a` is irrational) equal total weight; so the line carries even
  weight (`interior_weight`);
* the sides `AB` and `BC` have the same length, hence the same weight, and the same class (they
  meet at the angle `2α`); `AC` carries no legs (`boundary_weight`).

So `N ≡ 0 (mod 2)`.
-/
import TriangleTiling.RightTile.Lines
import TriangleTiling.RightTile.Helper3

namespace TriangleTiling

open Erdos634.Geometry EuclideanGeometry

/-! ### Arithmetic -/

/-- If `a q = b p` and `c/a` is irrational, a length relation `nₐ a + n_b b + n_c c =
mₐ a + m_b b + m_c c` gives `nₐ p + n_b q = mₐ p + m_b q`. -/
theorem xi_eq {a b c : ℝ} {p q na nb nc ma mb mc : ℕ} (ha : 0 < a) (hp : 0 < p)
    (hab : a * q = b * p) (hc : ¬ ∃ r : ℚ, c = r * a)
    (h : (na : ℝ) * a + nb * b + nc * c = ma * a + mb * b + mc * c) :
    na * p + nb * q = ma * p + mb * q := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have key : a * (((na * p + nb * q : ℕ) : ℝ) - ((ma * p + mb * q : ℕ) : ℝ)) =
      p * (((mc : ℝ) - nc) * c) := by
    push_cast; linear_combination (p : ℝ) * h + ((nb : ℝ) - mb) * hab
  by_cases hm : mc = nc
  · subst hm
    simp only [sub_self, zero_mul, mul_zero] at key
    have := (mul_eq_zero.mp key).resolve_left ha.ne'
    exact_mod_cast sub_eq_zero.mp this
  · exfalso
    apply hc
    have hmR : ((mc : ℝ) - nc) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hm)
    refine ⟨(((na * p + nb * q : ℕ) : ℚ) - ((ma * p + mb * q : ℕ) : ℚ)) / (p * ((mc : ℚ) - nc)), ?_⟩
    push_cast at key ⊢
    field_simp
    linear_combination -key

/-! ### Edges and their weights -/

variable {N : ℕ}

/-- The vector of a tile edge. -/
def edgeVec (D : Dissection N) (e : Fin N × Fin 3) : Plane :=
  (D.tile e.1).pts (e.2 + 1) - (D.tile e.1).pts e.2

theorem edgeVec_ne (D : Dissection N) (e : Fin N × Fin 3) : edgeVec D e ≠ 0 :=
  sub_ne_zero.mpr (tile_pts_ne D e.1 e.2).symm

/-- An edge runs through the interior of the tiled triangle. -/
def Internal (D : Dissection N) (e : Fin N × Fin 3) : Prop :=
  openSegment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) ⊆ interior D.target.carrier

variable (D : CongruentDissection N)

open Classical in
/-- The weight of an edge: `p` for an `a` edge, `q` for a `b` edge, `0` for a `c` edge. -/
noncomputable def legWeight (p q : ℕ) (e : Fin N × Fin 3) : ℕ :=
  if edgeType D (tileα D) e then p else if edgeType D (tileβ D) e then q else 0

theorem edgeType_unique {φ ψ : ℝ} {e : Fin N × Fin 3} (h1 : edgeType D φ e)
    (h2 : edgeType D ψ e) : φ = ψ := h1.symm.trans h2

theorem edgeType_cases (e : Fin N × Fin 3) :
    edgeType D (tileα D) e ∨ edgeType D (tileβ D) e ∨ edgeType D (tileγ D) e :=
  localAngle_at_own_vertex_mem' D e.1 (e.2 + 2)

open Classical in
theorem weight_sum (hαβ : tileα D ≠ tileβ D) (p q : ℕ) (part : Finset (Fin N × Fin 3)) :
    ∑ e ∈ part, legWeight D p q e =
      (part.filter (edgeType D (tileα D))).card * p +
        (part.filter (edgeType D (tileβ D))).card * q := by
  have h : ∀ e, legWeight D p q e = (if edgeType D (tileα D) e then p else 0) +
      (if edgeType D (tileβ D) e then q else 0) := by
    intro e
    unfold legWeight
    by_cases h1 : edgeType D (tileα D) e
    · have h2 : ¬ edgeType D (tileβ D) e := fun h2 => hαβ (edgeType_unique D h1 h2)
      simp [h1, h2]
    · simp [h1]
  rw [Finset.sum_congr rfl fun e _ => h e, Finset.sum_add_distrib, ← Finset.sum_filter,
    ← Finset.sum_filter, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]

theorem weight_gamma {p q : ℕ} (hαγ : tileα D ≠ tileγ D) (hβγ : tileβ D ≠ tileγ D)
    {e : Fin N × Fin 3} (h : edgeType D (tileγ D) e) : legWeight D p q e = 0 := by
  have h1 : ¬ edgeType D (tileα D) e := fun h1 => hαγ (edgeType_unique D h1 h)
  have h2 : ¬ edgeType D (tileβ D) e := fun h2 => hβγ (edgeType_unique D h2 h)
  simp [legWeight, h1, h2]

theorem weight_odd {p q : ℕ} (hp : Odd p) (hq : Odd q) {e : Fin N × Fin 3}
    (h : ¬ edgeType D (tileγ D) e) : ((legWeight D p q e : ℕ) : ZMod 2) = 1 := by
  unfold legWeight
  rcases edgeType_cases D e with h1 | h1 | h1
  · simp [h1, ZMod.natCast_eq_one_iff_odd.mpr hp]
  · by_cases h0 : edgeType D (tileα D) e
    · simp [h0, ZMod.natCast_eq_one_iff_odd.mpr hp]
    · simp [h0, h1, ZMod.natCast_eq_one_iff_odd.mpr hq]
  · exact absurd h1 h

open Classical in
/-- The lengths of a set of edges, by type. -/
theorem typed_lengths (hsep : AnglesSep D) (part : Finset (Fin N × Fin 3)) :
    ∑ e ∈ part, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) =
      ((part.filter (edgeType D (tileα D))).card : ℝ) * dist (D.model.pts 1) (D.model.pts 2)
      + ((part.filter (edgeType D (tileβ D))).card : ℝ) * dist (D.model.pts 2) (D.model.pts 0)
      + ((part.filter (edgeType D (tileγ D))).card : ℝ) * dist (D.model.pts 0) (D.model.pts 1) :=
  side_walk_counts_sep D hsep part _ rfl

/-! ### Legs of class `0` -/

theorem fin3_sum (k : Fin 3) (g : Fin 3 → ZMod 2) : ∑ m, g m = g k + g (k + 1) + g (k + 2) := by
  fin_cases k <;> simp [Fin.sum_univ_three] <;> ring

open Classical in
/-- **Each tile has exactly one leg of class `0`.** -/
theorem legs_one (hright : tileγ D = Real.pi / 2) (hsep : AnglesSep D) (θ : ℝ)
    (hθ : ¬ ∃ r : ℚ, θ = r * Real.pi) (i : Fin N) :
    (∑ m : Fin 3, if ¬ edgeType D (tileγ D) (i, m) ∧
        DirClass.Cls θ (dirC (edgeVec D.toDissection (i, m))) then (1 : ZMod 2) else 0) = 1 := by
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp (tile_angle_count_sep D hsep i).2.2
  have hkk : cornerAngle ((D.tile i).pts (k + 1)) ((D.tile i).pts k) ((D.tile i).pts (k + 2)) =
      tileγ D := by
    have : k ∈ ({k} : Finset (Fin 3)) := Finset.mem_singleton_self k
    rw [← hk] at this; exact (Finset.mem_filter.mp this).2
  have huniq : ∀ m : Fin 3, cornerAngle ((D.tile i).pts (m + 1)) ((D.tile i).pts m)
      ((D.tile i).pts (m + 2)) = tileγ D → m = k := by
    intro m hm
    have : m ∈ Finset.univ.filter fun k : Fin 3 => cornerAngle ((D.tile i).pts (k + 1))
        ((D.tile i).pts k) ((D.tile i).pts (k + 2)) = tileγ D :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hm⟩
    rw [hk] at this; exact Finset.mem_singleton.mp this
  have htype : ∀ m : Fin 3, edgeType D (tileγ D) (i, m) ↔ m + 2 = k := by
    intro m
    unfold edgeType
    rw [Tri.localAngle_vertex]
    constructor
    · exact huniq (m + 2)
    · rintro rfl; exact hkk
  -- The two legs at the right angle are perpendicular.
  have hperp : inner ℝ ((D.tile i).pts (k + 1) - (D.tile i).pts k)
      ((D.tile i).pts (k + 2) - (D.tile i).pts k) = 0 := by
    rw [InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two]
    rw [← hright, ← hkk]; rfl
  have hu : (D.tile i).pts (k + 1) - (D.tile i).pts k ≠ 0 :=
    sub_ne_zero.mpr (tile_pts_ne D.toDissection i k).symm
  have hv : (D.tile i).pts (k + 2) - (D.tile i).pts k ≠ 0 := by
    rw [sub_ne_zero]; intro h
    have := (D.tile i).indep.injective h
    have h2 : ∀ m : Fin 3, m + 2 ≠ m := by decide
    exact h2 k this
  have hd := dirC_of_inner hu hv hperp
  have e1 : edgeVec D.toDissection (i, k + 2) =
      -((D.tile i).pts (k + 2) - (D.tile i).pts k) := by
    unfold edgeVec
    have : k + 2 + 1 = k := by fin_cases k <;> rfl
    simp only [this]; abel
  have hcls : DirClass.Cls θ (dirC (edgeVec D.toDissection (i, k + 2))) ↔
      ¬ DirClass.Cls θ (dirC (edgeVec D.toDissection (i, k))) := by
    rw [e1, dirC_neg, hd]
    exact DirClass.cls_neg θ hθ (dirC_ne hu)
  have t0 : ¬ edgeType D (tileγ D) (i, k) := by
    rw [htype]; fin_cases k <;> decide
  have t1 : edgeType D (tileγ D) (i, k + 1) := by
    rw [htype]; fin_cases k <;> rfl
  have t2 : ¬ edgeType D (tileγ D) (i, k + 2) := by
    rw [htype]; fin_cases k <;> decide
  rw [fin3_sum k]
  simp only [t0, t1, t2, not_true_eq_false, not_false_eq_true, true_and, false_and, if_false,
    add_zero]
  by_cases h : DirClass.Cls θ (dirC (edgeVec D.toDissection (i, k)))
  · simp [h]
    simp [hcls, h]
  · simp [h, hcls.mpr h]

/-! ### Lines through the interior -/

theorem lineChain_pair_iff (Dd : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (e : Fin N × Fin 3) :
    (e ∈ Dd.lineChain f c ∨ e ∈ Dd.lineChain (-f) (-c)) ↔
      f ((Dd.tile e.1).pts e.2) = c ∧ f ((Dd.tile e.1).pts (e.2 + 1)) = c := by
  constructor
  · rintro (h | h)
    · obtain ⟨h1, h2, -⟩ := Dissection.mem_lineChain.mp h; exact ⟨h1, h2⟩
    · obtain ⟨h1, h2, -⟩ := Dissection.mem_lineChain.mp h
      simp only [LinearMap.neg_apply, neg_inj] at h1 h2
      exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    have hall : ∀ i : Fin 3, i = e.2 ∨ i = e.2 + 1 ∨ i = e.2 + 2 := by
      have : ∀ k i : Fin 3, i = k ∨ i = k + 1 ∨ i = k + 2 := by decide
      exact fun i => this e.2 i
    by_cases hR : f ((Dd.tile e.1).pts (e.2 + 2)) ≤ c
    · left
      refine Dissection.mem_lineChain.mpr ⟨h1, h2, fun i => ?_⟩
      rcases hall i with rfl | rfl | rfl
      · exact h1.le
      · exact h2.le
      · exact hR
    · right
      refine Dissection.mem_lineChain.mpr ⟨by simp [h1], by simp [h2], fun i => ?_⟩
      rcases hall i with rfl | rfl | rfl
      · simp [h1]
      · simp [h2]
      · simp only [LinearMap.neg_apply, neg_le_neg_iff]; linarith

theorem chain_disjoint (Dd : Dissection N) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ) (hf : f ≠ 0) :
    Disjoint (Dd.lineChain f c) (Dd.lineChain (-f) (-c)) := by
  rw [Finset.disjoint_left]
  intro e h1 h2
  obtain ⟨-, -, hle⟩ := Dissection.mem_lineChain.mp h1
  obtain ⟨-, -, hge⟩ := Dissection.mem_lineChain.mp h2
  exact two_vertices_on_line (Dd.tile e.1) f c hf fun i =>
    le_antisymm (hle i) (by have := hge i; simp only [LinearMap.neg_apply, neg_le_neg_iff] at this; exact this)

theorem edgeLine_eq_iff (Dd : Dissection N) (e e1 : Fin N × Fin 3) :
    edgeLine Dd e = edgeLine Dd e1 ↔
      ((Dd.tile e.1).pts e.2 ∈ edgeLine Dd e1 ∧ (Dd.tile e.1).pts (e.2 + 1) ∈ edgeLine Dd e1) := by
  constructor
  · intro h
    rw [← h]
    exact ⟨left_mem_lineSet _ _, right_mem_lineSet _ _⟩
  · rintro ⟨h1, h2⟩
    exact lineSet_eq (tile_pts_ne Dd e1.1 e1.2) (tile_pts_ne Dd e.1 e.2) h1 h2

/-- An edge on a side does not run through the interior. -/
theorem not_internal_of_side (Dd : Dissection N) {e : Fin N × Fin 3} {i : Fin 3}
    (h : (Dd.tile e.1).edge e.2 ⊆ segment ℝ (Dd.target.pts i) (Dd.target.pts (i + 1))) :
    ¬ Internal Dd e := by
  intro hI
  have hmid : (1 / 2 : ℝ) • (Dd.tile e.1).pts e.2 + (1 / 2 : ℝ) • (Dd.tile e.1).pts (e.2 + 1) ∈
      openSegment ℝ ((Dd.tile e.1).pts e.2) ((Dd.tile e.1).pts (e.2 + 1)) :=
    ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, rfl⟩
  have hfr := tri_side_subset_frontier Dd.target i (h (openSegment_subset_segment ℝ _ _ hmid))
  exact hfr.2 (hI hmid)

/-- If one edge on a line runs through the interior, so do all edges on it. -/
theorem internal_of_line (Dd : Dissection N) {e e1 : Fin N × Fin 3} (h1 : Internal Dd e1)
    (hl : edgeLine Dd e = edgeLine Dd e1) : Internal Dd e := by
  rcases edge_internal_or_side Dd e with h | ⟨i, hi⟩
  · exact h
  · exfalso
    obtain ⟨f, c, -, hle, hfi, hfi1, hfi2⟩ := exists_supporting Dd.target i
    have hS := target_contact_side Dd.target f c hle hfi hfi1 hfi2
    have hTne : Dd.target.pts i ≠ Dd.target.pts (i + 1) := by
      intro h
      have := Dd.target.indep.injective h
      have h2 : ∀ m : Fin 3, m ≠ m + 1 := by decide
      exact h2 i this
    have hline : edgeLine Dd e = lineSet (Dd.target.pts i) (Dd.target.pts (i + 1)) :=
      lineSet_eq hTne (tile_pts_ne Dd e.1 e.2)
        (segment_subset_lineSet _ _ (hi (left_mem_segment ℝ _ _)))
        (segment_subset_lineSet _ _ (hi (right_mem_segment ℝ _ _)))
    have hfline : ∀ y ∈ lineSet (Dd.target.pts i) (Dd.target.pts (i + 1)), f y = c := by
      intro y hy
      obtain ⟨t, rfl⟩ := eq_lineMap_of_mem_lineSet hTne hy
      simp [map_add, map_smul, map_sub, hfi, hfi1]
    have hon : ∀ y ∈ edgeLine Dd e1, y ∈ Dd.target.carrier →
        y ∈ segment ℝ (Dd.target.pts i) (Dd.target.pts (i + 1)) := by
      intro y hy hyc
      rw [← hS]
      exact ⟨hyc, hfline y (by rw [← hline, hl]; exact hy)⟩
    have hP1 := hon _ (left_mem_lineSet _ _) (edge_subset_target Dd e1 (left_mem_segment ℝ _ _))
    have hQ1 := hon _ (right_mem_lineSet _ _) (edge_subset_target Dd e1 (right_mem_segment ℝ _ _))
    exact not_internal_of_side Dd (e := e1) (i := i)
      ((convex_segment _ _).segment_subset hP1 hQ1) h1

open Classical in
/-- **The interior lines carry even weight.** -/
theorem interior_weight (hsep : AnglesSep D) (hαβ : tileα D ≠ tileβ D)
    (hαγ : tileα D ≠ tileγ D) (hβγ : tileβ D ≠ tileγ D) {p q : ℕ} (hp0 : 0 < p)
    (hratio : dist (D.model.pts 1) (D.model.pts 2) * q = dist (D.model.pts 2) (D.model.pts 0) * p)
    (hcirr : ¬ ∃ r : ℚ, dist (D.model.pts 0) (D.model.pts 1) = r * dist (D.model.pts 1) (D.model.pts 2))
    (θ : ℝ) :
    (∑ e, if Internal D.toDissection e ∧ ¬ edgeType D (tileγ D) e ∧
        DirClass.Cls θ (dirC (edgeVec D.toDissection e))
      then ((legWeight D p q e : ℕ) : ZMod 2) else 0) = 0 := by
  set Dd := D.toDissection
  have ha0 : 0 < dist (D.model.pts 1) (D.model.pts 2) := dist_pos.mpr fun h => by
    have := D.model.indep.injective h; exact absurd this (by decide)
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image (edgeLine Dd))
    (g := edgeLine Dd) (fun e _ => Finset.mem_image_of_mem _ (Finset.mem_univ e))]
  apply Finset.sum_eq_zero
  intro ℓ _
  by_cases hex : ∃ e1, edgeLine Dd e1 = ℓ ∧ Internal Dd e1 ∧
      DirClass.Cls θ (dirC (edgeVec Dd e1))
  swap
  · apply Finset.sum_eq_zero
    intro e he
    rw [if_neg]
    rintro ⟨hI, -, hCe⟩
    exact hex ⟨e, (Finset.mem_filter.mp he).2, hI, hCe⟩
  obtain ⟨e1, rfl, hI1, hC1⟩ := hex
  have hPQ1 := tile_pts_ne Dd e1.1 e1.2
  set P1 := (Dd.tile e1.1).pts e1.2
  set Q1 := (Dd.tile e1.1).pts (e1.2 + 1)
  set f := crossL (Q1 - P1)
  set c0 := cross (Q1 - P1) P1
  have hf : f ≠ 0 := crossL_ne_zero (sub_ne_zero.mpr hPQ1.symm)
  have hmem : ∀ e, edgeLine Dd e = edgeLine Dd e1 ↔
      (e ∈ Dd.lineChain f c0 ∨ e ∈ Dd.lineChain (-f) (-c0)) := by
    intro e
    rw [edgeLine_eq_iff, lineChain_pair_iff Dd f c0]
    rfl
  have hfib : (Finset.univ.filter fun e => edgeLine Dd e = edgeLine Dd e1) =
      Dd.lineChain f c0 ∪ Dd.lineChain (-f) (-c0) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    exact hmem e
  have hterm : ∀ e ∈ (Finset.univ.filter fun e => edgeLine Dd e = edgeLine Dd e1),
      (if Internal Dd e ∧ ¬ edgeType D (tileγ D) e ∧ DirClass.Cls θ (dirC (edgeVec Dd e))
        then ((legWeight D p q e : ℕ) : ZMod 2) else 0) = ((legWeight D p q e : ℕ) : ZMod 2) := by
    intro e he
    have hl := (Finset.mem_filter.mp he).2
    have hI := internal_of_line Dd hI1 hl
    have hon := (edgeLine_eq_iff Dd e e1).mp hl
    have hCe : DirClass.Cls θ (dirC (edgeVec Dd e)) ↔ DirClass.Cls θ (dirC (edgeVec Dd e1)) := by
      unfold edgeVec
      rw [dirC_lineSet hPQ1 (tile_pts_ne Dd e.1 e.2) hon.1 hon.2]
    by_cases hγ : edgeType D (tileγ D) e
    · rw [weight_gamma D hαγ hβγ hγ]; simp
    · rw [if_pos ⟨hI, hγ, hCe.mpr hC1⟩]
  rw [Finset.sum_congr rfl hterm, hfib, Finset.sum_union (chain_disjoint Dd f c0 hf)]
  have hint : ∀ e ∈ Dd.lineChain f c0 ∪ Dd.lineChain (-f) (-c0),
      openSegment ℝ ((Dd.tile e.1).pts e.2) ((Dd.tile e.1).pts (e.2 + 1)) ⊆
        interior Dd.target.carrier :=
    fun e he => internal_of_line Dd hI1 ((hmem e).mpr (Finset.mem_union.mp he))
  have hbal := line_balance Dd f c0 hf hint
  rw [typed_lengths D hsep, typed_lengths D hsep] at hbal
  have hxi := xi_eq ha0 hp0 hratio hcirr hbal
  rw [← Nat.cast_sum, ← Nat.cast_sum, weight_sum D hαβ, weight_sum D hαβ, ← Nat.cast_add, hxi,
    ZMod.natCast_eq_zero_iff_even]
  exact Even.add_self _

/-! ### The sides -/

/-- `AB` and `BC` have the same class: they meet at the angle `2α`. -/
theorem apex_class (hright : tileγ D = Real.pi / 2)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileβ D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileβ D)
    (hθ : ¬ ∃ r : ℚ, 4 * tileα D = r * Real.pi) :
    DirClass.Cls (4 * tileα D) (dirC (D.target.pts 1 - D.target.pts 0)) ↔
      DirClass.Cls (4 * tileα D) (dirC (D.target.pts 2 - D.target.pts 1)) := by
  set T := D.target.pts
  have hne : ∀ i j : Fin 3, i ≠ j → T i - T j ≠ 0 := fun i j hij h =>
    hij (D.target.indep.injective (sub_eq_zero.mp h))
  have hang : InnerProductGeometry.angle (T 2 - T 1) (T 0 - T 1) = 2 * tileα D := by
    have := apex_angle D hright hA hC
    rw [Tri.localAngle_vertex] at this
    exact this
  have e0 : dirC (T 1 - T 0) = dirC (T 0 - T 1) := by rw [← neg_sub, dirC_neg]
  rw [e0]
  rcases dirC_of_angle (hne 2 1 (by decide)) (hne 0 1 (by decide)) with h | h
  · rw [h, hang]
    have : Complex.exp (2 * ((2 * tileα D : ℝ) : ℂ) * Complex.I) = DirClass.ω (4 * tileα D) := by
      unfold DirClass.ω; congr 1; push_cast; ring
    rw [this]
    exact DirClass.cls_mul_ω _ hθ (dirC_ne (hne 2 1 (by decide)))
  · rw [h, hang]
    have : Complex.exp (-(2 * ((2 * tileα D : ℝ) : ℂ)) * Complex.I) =
        (DirClass.ω (4 * tileα D))⁻¹ := by
      unfold DirClass.ω; rw [← Complex.exp_neg]; congr 1; push_cast; ring
    rw [this]
    exact DirClass.cls_mul_ω_inv _ hθ (dirC_ne (hne 2 1 (by decide)))

theorem class_on_side {P Q : Plane} (hPQ : P ≠ Q) (θ : ℝ) {e : Fin N × Fin 3}
    (h : (D.tile e.1).edge e.2 ⊆ segment ℝ P Q) :
    DirClass.Cls θ (dirC (edgeVec D.toDissection e)) ↔ DirClass.Cls θ (dirC (Q - P)) := by
  unfold edgeVec
  rw [dirC_lineSet hPQ (tile_pts_ne D.toDissection e.1 e.2)
    (segment_subset_lineSet _ _ (h (left_mem_segment ℝ _ _)))
    (segment_subset_lineSet _ _ (h (right_mem_segment ℝ _ _)))]

open Classical in
/-- **The sides carry even weight.** -/
theorem boundary_weight (hright : tileγ D = Real.pi / 2)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileβ D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileβ D)
    (hsep : AnglesSep D) (hαβ : tileα D ≠ tileβ D)
    (hαγ : tileα D ≠ tileγ D) (hβγ : tileβ D ≠ tileγ D) {p q : ℕ} (hp0 : 0 < p)
    (hratio : dist (D.model.pts 1) (D.model.pts 2) * q = dist (D.model.pts 2) (D.model.pts 0) * p)
    (hcirr : ¬ ∃ r : ℚ, dist (D.model.pts 0) (D.model.pts 1) = r * dist (D.model.pts 1) (D.model.pts 2))
    (hθ : ¬ ∃ r : ℚ, 4 * tileα D = r * Real.pi)
    (hAC : ∀ e : Fin N × Fin 3, (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 2) (D.target.pts 0) →
      edgeType D (tileγ D) e) :
    (∑ e, if ¬ Internal D.toDissection e ∧ ¬ edgeType D (tileγ D) e ∧
        DirClass.Cls (4 * tileα D) (dirC (edgeVec D.toDissection e))
      then ((legWeight D p q e : ℕ) : ZMod 2) else 0) = 0 := by
  set Dd := D.toDissection
  set T := D.target.pts
  set θ := 4 * tileα D
  set w := fun e => ((legWeight D p q e : ℕ) : ZMod 2)
  have ha0 : 0 < dist (D.model.pts 1) (D.model.pts 2) := dist_pos.mpr fun h => by
    have := D.model.indep.injective h; exact absurd this (by decide)
  have hT : ∀ i j : Fin 3, i ≠ j → T i ≠ T j := fun i j hij h => hij (D.target.indep.injective h)
  set CAB := DirClass.Cls θ (dirC (T 1 - T 0))
  have hCBC : DirClass.Cls θ (dirC (T 2 - T 1)) ↔ CAB := (apex_class D hright hA hC hθ).symm
  set AB := segment ℝ (T 0) (T 1)
  set BC := segment ℝ (T 1) (T 2)
  have hdisj : ∀ e : Fin N × Fin 3, (D.tile e.1).edge e.2 ⊆ AB → ¬ (D.tile e.1).edge e.2 ⊆ BC := by
    intro e h1 h2
    have hm : ∀ x ∈ (D.tile e.1).edge e.2, x = T 1 := fun x hx =>
      sides_meet D.target 1 (h2 hx) (h1 hx)
    exact tile_pts_ne Dd e.1 e.2 ((hm _ (left_mem_segment ℝ _ _)).trans
      (hm _ (right_mem_segment ℝ _ _)).symm)
  -- Pointwise: only the edges on `AB` and `BC` count.
  have hpt : ∀ e : Fin N × Fin 3,
      (if ¬ Internal Dd e ∧ ¬ edgeType D (tileγ D) e ∧ DirClass.Cls θ (dirC (edgeVec Dd e))
        then w e else 0) =
      (if (D.tile e.1).edge e.2 ⊆ AB ∧ CAB then w e else 0) +
        (if (D.tile e.1).edge e.2 ⊆ BC ∧ CAB then w e else 0) := by
    intro e
    by_cases hγ : edgeType D (tileγ D) e
    · have : w e = 0 := by simp only [w]; rw [weight_gamma D hαγ hβγ hγ]; simp
      simp [hγ, this]
    by_cases hab : (D.tile e.1).edge e.2 ⊆ AB
    · have hbc := hdisj e hab
      have hI : ¬ Internal Dd e := not_internal_of_side Dd (i := 0) hab
      have hc := class_on_side D (hT 0 1 (by decide)) θ hab
      simp only [hI, hγ, not_false_eq_true, true_and, hab, hbc, false_and, if_false, add_zero]
      rw [hc]
    by_cases hbc : (D.tile e.1).edge e.2 ⊆ BC
    · have hI : ¬ Internal Dd e := not_internal_of_side Dd (i := 1) hbc
      have hc := (class_on_side D (hT 1 2 (by decide)) θ hbc).trans hCBC
      simp only [hI, hγ, not_false_eq_true, true_and, hab, hbc, false_and, if_false, zero_add]
      rw [hc]
    simp only [hab, hbc, false_and, if_false, add_zero]
    rw [if_neg]
    rintro ⟨hI, -, -⟩
    rcases edge_internal_or_side Dd e with h | ⟨i, hi⟩
    · exact hI h
    · fin_cases i
      · exact hab hi
      · exact hbc hi
      · exact hγ (hAC e hi)
  rw [Finset.sum_congr rfl fun e _ => hpt e, Finset.sum_add_distrib]
  by_cases hc : CAB
  swap
  · simp [hc]
  simp only [hc, and_true]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  -- The two sides have the same length, hence the same weight.
  obtain ⟨hXX, -, -⟩ := right_area_core D rfl rfl rfl rfl rfl hright hA hC
  have s0 := side_sum Dd 0
  have s1 := side_sum Dd 1
  have i01 : (0 : Fin 3) + 1 = 1 := rfl
  have i12 : (1 : Fin 3) + 1 = 2 := rfl
  rw [i01] at s0
  rw [i12] at s1
  rw [typed_lengths D hsep] at s0 s1
  have hlen := s0.trans (hXX.symm.trans s1.symm)
  have hxi := xi_eq ha0 hp0 hratio hcirr hlen
  simp only [w]
  rw [← Nat.cast_sum, ← Nat.cast_sum, weight_sum D hαβ, weight_sum D hαβ, ← Nat.cast_add, hxi,
    ZMod.natCast_eq_zero_iff_even]
  exact Even.add_self _

open Classical in
/-- **The parity step of `theorem:isosceles2`: `N` is even.** Hypotheses: the isosceles triangle
`ABC` with base angles `β` is `N`-tiled by `(α, β, π/2)` with `α ∉ ℚπ`; the legs are in the ratio
`a : b = p : q` with `p, q` odd; `c/a` is irrational; and `AC` consists of `c` edges. -/
theorem parity_even (hright : tileγ D = Real.pi / 2)
    (hA : ∠ (D.target.pts 1) (D.target.pts 0) (D.target.pts 2) = tileβ D)
    (hC : ∠ (D.target.pts 1) (D.target.pts 2) (D.target.pts 0) = tileβ D)
    (hαirr : ¬ ∃ r : ℚ, tileα D = r * Real.pi) {p q : ℕ} (hp : Odd p) (hq : Odd q)
    (hratio : dist (D.model.pts 1) (D.model.pts 2) * q = dist (D.model.pts 2) (D.model.pts 0) * p)
    (hcirr : ¬ ∃ r : ℚ, dist (D.model.pts 0) (D.model.pts 1) = r * dist (D.model.pts 1) (D.model.pts 2))
    (hAC : ∀ e : Fin N × Fin 3, (D.tile e.1).edge e.2 ⊆ segment ℝ (D.target.pts 2) (D.target.pts 0) →
      edgeType D (tileγ D) e) :
    Even N := by
  have hsep := anglesSep_right D hright hαirr
  have hβ := right_beta D hright
  have hα0 := tileα_pos D
  have hβ0 := tileβ_pos D
  have hαβ : tileα D ≠ tileβ D := fun h => hαirr ⟨1 / 4, by push_cast; linarith⟩
  have hαγ : tileα D ≠ tileγ D := by rw [hright]; linarith
  have hβγ : tileβ D ≠ tileγ D := by rw [hright]; linarith
  have hθ : ¬ ∃ r : ℚ, 4 * tileα D = r * Real.pi := fun ⟨r, hr⟩ =>
    hαirr ⟨r / 4, by push_cast; linarith⟩
  have hp0 : 0 < p := hp.pos
  set θ := 4 * tileα D
  -- The weight of the legs of class `0` is `N` modulo `2` ...
  have hN : (∑ e, if ¬ edgeType D (tileγ D) e ∧ DirClass.Cls θ (dirC (edgeVec D.toDissection e))
      then ((legWeight D p q e : ℕ) : ZMod 2) else 0) = N := by
    have h1 : ∀ e : Fin N × Fin 3, (if ¬ edgeType D (tileγ D) e ∧
        DirClass.Cls θ (dirC (edgeVec D.toDissection e)) then ((legWeight D p q e : ℕ) : ZMod 2) else 0) =
        if ¬ edgeType D (tileγ D) e ∧ DirClass.Cls θ (dirC (edgeVec D.toDissection e)) then 1 else 0 := by
      intro e
      by_cases h : ¬ edgeType D (tileγ D) e ∧ DirClass.Cls θ (dirC (edgeVec D.toDissection e))
      · rw [if_pos h, if_pos h, weight_odd D hp hq h.1]
      · rw [if_neg h, if_neg h]
    rw [Finset.sum_congr rfl fun e _ => h1 e, Fintype.sum_prod_type]
    simp only [legs_one D hright hsep θ hθ, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  -- ... and splits into the interior lines and the sides, each of even weight.
  have hsplit : ∀ e : Fin N × Fin 3,
      (if ¬ edgeType D (tileγ D) e ∧ DirClass.Cls θ (dirC (edgeVec D.toDissection e))
        then ((legWeight D p q e : ℕ) : ZMod 2) else 0) =
      (if Internal D.toDissection e ∧ ¬ edgeType D (tileγ D) e ∧ DirClass.Cls θ (dirC (edgeVec D.toDissection e))
        then ((legWeight D p q e : ℕ) : ZMod 2) else 0) +
      (if ¬ Internal D.toDissection e ∧ ¬ edgeType D (tileγ D) e ∧ DirClass.Cls θ (dirC (edgeVec D.toDissection e))
        then ((legWeight D p q e : ℕ) : ZMod 2) else 0) := by
    intro e
    by_cases hI : Internal D.toDissection e <;> simp [hI]
  rw [Finset.sum_congr rfl fun e _ => hsplit e, Finset.sum_add_distrib,
    interior_weight D hsep hαβ hαγ hβγ hp0 hratio hcirr θ,
    boundary_weight D hright hA hC hsep hαβ hαγ hβγ hp0 hratio hcirr hθ hAC, add_zero] at hN
  exact ZMod.natCast_eq_zero_iff_even.mp hN.symm

end TriangleTiling
