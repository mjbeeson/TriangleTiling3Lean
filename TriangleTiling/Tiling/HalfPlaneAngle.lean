/-
Angles on one side of a line through an interior point.

If every tile containing an interior point `Q` of the target lies on one side or the other of a
line through `Q`, then the angles at `Q` of the tiles on one side add up to `π`. Proof by area:
near `Q` those tiles fill a half-disk, of area half the disk (the point reflection through `Q`
exchanges the two halves, and the line has area zero), and a tile meets a small disk about `Q`
in area `(local angle / 2) r²` (Bonfioli's `Tri.volume_inter_ball_localAngle`).
-/
import TriangleTiling.Tiling.AngleFacts
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

namespace TriangleTiling

open Erdos634.Geometry MeasureTheory Set

variable {N : ℕ} (D : Dissection N)

/-- The tiles partition the target, a.e., inside any measurable set. -/
theorem volume_inter_eq_sum {U : Set Plane} (hU : MeasurableSet U) :
    volume (D.target.carrier ∩ U) = ∑ i, volume ((D.tile i).carrier ∩ U) := by
  have h := measure_biUnion_finset₀ (μ := volume)
    (s := (Finset.univ : Finset (Fin N)))
    (f := fun i => (D.tile i).carrier ∩ U)
    (fun i _ j _ hij => measure_mono_null
      (Set.inter_subset_inter Set.inter_subset_left Set.inter_subset_left) (D.aedisjoint hij))
    (fun i _ => ((D.tile i).nullMeasurableSet).inter hU.nullMeasurableSet)
  have hUn : (⋃ i ∈ (Finset.univ : Finset (Fin N)), ((D.tile i).carrier ∩ U))
      = D.target.carrier ∩ U := by
    simp only [Finset.mem_univ, Set.iUnion_true]
    rw [← Set.iUnion_inter, D.covers]
  rw [hUn] at h
  exact h

/-- A line has area zero. -/
theorem volume_level_zero {g : Plane →ₗ[ℝ] ℝ} (hg : g ≠ 0) (c : ℝ) :
    volume {y : Plane | g y = c} = 0 := by
  obtain ⟨Q, hQ⟩ : ∃ Q : Plane, g Q = c := by
    obtain ⟨v, hv⟩ : ∃ v, g v ≠ 0 := by
      by_contra h
      push Not at h
      exact hg (LinearMap.ext h)
    exact ⟨(c / g v) • v, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ c hv]⟩
  let s : AffineSubspace ℝ Plane := AffineSubspace.mk' Q (LinearMap.ker g)
  have hsub : {y : Plane | g y = c} ⊆ s := by
    intro y hy
    show y ∈ AffineSubspace.mk' Q (LinearMap.ker g)
    rw [AffineSubspace.mem_mk', LinearMap.mem_ker, vsub_eq_sub, map_sub, hQ]
    exact sub_eq_zero.mpr hy
  have hs : s ≠ ⊤ := by
    intro htop
    apply hg
    ext v
    have hv : Q + v ∈ s := by rw [htop]; exact AffineSubspace.mem_top ℝ Plane _
    have : Q + v ∈ AffineSubspace.mk' Q (LinearMap.ker g) := hv
    rw [AffineSubspace.mem_mk', LinearMap.mem_ker, vsub_eq_sub, add_sub_cancel_left] at this
    simpa using this
  exact measure_mono_null hsub (Measure.addHaar_affineSubspace volume s hs)

theorem continuous_functional (g : Plane →ₗ[ℝ] ℝ) : Continuous g :=
  LinearMap.continuous_of_finiteDimensional g

/-- **Half a disk.** A line through the center of a disk cuts it into halves of equal area. -/
theorem volume_ball_inter_half {g : Plane →ₗ[ℝ] ℝ} (hg : g ≠ 0) {Q : Plane} {c : ℝ}
    (hQ : g Q = c) (r : ℝ) :
    volume (Metric.ball Q r) = 2 * volume (Metric.ball Q r ∩ {y | g y ≤ c}) := by
  have hcont := continuous_functional g
  have hH : MeasurableSet {y : Plane | g y ≤ c} :=
    (isClosed_le hcont continuous_const).measurableSet
  have hH' : MeasurableSet {y : Plane | c ≤ g y} :=
    (isClosed_le continuous_const hcont).measurableSet
  set A := Metric.ball Q r ∩ {y | g y ≤ c}
  set A' := Metric.ball Q r ∩ {y | c ≤ g y}
  -- The point reflection through `Q` exchanges the halves.
  have hrefl : volume A' = volume A := by
    have hmp := Measure.measurePreserving_sub_left (volume : Measure Plane) (Q + Q)
    have hpre : (fun y => Q + Q - y) ⁻¹' A = A' := by
      ext y
      simp only [A, A', Set.mem_preimage, Set.mem_inter_iff, Metric.mem_ball, Set.mem_setOf_eq,
        map_sub, map_add, hQ]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, by linarith⟩
        rwa [dist_eq_norm, show Q + Q - y - Q = Q - y by abel, ← dist_eq_norm, dist_comm] at h1
      · rintro ⟨h1, h2⟩
        refine ⟨?_, by linarith⟩
        rwa [dist_eq_norm, show Q + Q - y - Q = Q - y by abel, ← dist_eq_norm, dist_comm]
    rw [← hpre]
    exact hmp.measure_preimage (Metric.isOpen_ball.measurableSet.inter hH).nullMeasurableSet
  have hunion : A ∪ A' = Metric.ball Q r := by
    ext y
    simp only [A, A', Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro h
      rcases le_total (g y) c with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr ⟨h, h'⟩
  have hinter : volume (A ∩ A') = 0 := by
    refine measure_mono_null ?_ (volume_level_zero hg c)
    rintro y ⟨⟨-, h1⟩, ⟨-, h2⟩⟩
    exact le_antisymm h1 h2
  have hA'm : NullMeasurableSet A' volume :=
    ((Metric.isOpen_ball (x := Q) (ε := r)).measurableSet.inter hH').nullMeasurableSet
  have := measure_union_add_inter₀ (μ := volume) A hA'm
  rw [hunion, hinter, add_zero, hrefl] at this
  rw [this, two_mul]

open Classical in
/-- **Angles on one side of a line.** Let `Q` be interior to the target, and let each tile
containing `Q` lie on one side of a line through `Q`. Then the local angles at `Q` of the tiles on
one side add up to `π`. -/
theorem half_angle_sum {Q : Plane} (hQ : Q ∈ interior D.target.carrier)
    {g : Plane →ₗ[ℝ] ℝ} {c : ℝ} (hg : g ≠ 0) (hgQ : g Q = c)
    (hside : ∀ i, Q ∈ (D.tile i).carrier → (∀ y ∈ (D.tile i).carrier, g y ≤ c) ∨
      (∀ y ∈ (D.tile i).carrier, c ≤ g y)) :
    ∑ i ∈ Finset.univ.filter (fun i => ∀ y ∈ (D.tile i).carrier, g y ≤ c),
      (D.tile i).localAngle Q = Real.pi := by
  -- A radius below all the local ones.
  obtain ⟨rT, hrT, hT⟩ := D.target.volume_inter_ball_localAngle Q
  choose ri hri hcontrib using fun i => (D.tile i).volume_inter_ball_localAngle Q
  have hfar : ∀ i, ∃ s > (0 : ℝ), Q ∉ (D.tile i).carrier →
      Metric.ball Q s ∩ (D.tile i).carrier = ∅ := by
    intro i
    by_cases hQi : Q ∈ (D.tile i).carrier
    · exact ⟨1, one_pos, fun h => absurd hQi h⟩
    · obtain ⟨s, hs, hsub⟩ :=
        Metric.isOpen_iff.mp (D.tile i).isCompact.isClosed.isOpen_compl Q hQi
      exact ⟨s, hs, fun _ => Set.eq_empty_iff_forall_notMem.mpr fun y hy => hsub hy.1 hy.2⟩
  choose si hsi hsfar using hfar
  obtain ⟨r0, hr0, hr0le⟩ := exists_common_radius D.pos (fun i => min (ri i) (si i))
    (fun i => lt_min (hri i) (hsi i))
  obtain ⟨rI, hrI, hball⟩ := Metric.isOpen_iff.mp isOpen_interior Q hQ
  set r := min r0 (min rT rI)
  have hr : 0 < r := lt_min hr0 (lt_min hrT hrI)
  have hrr0 : r ≤ r0 := min_le_left _ _
  have hrT' : r ≤ rT := (min_le_right _ _).trans (min_le_left _ _)
  have hrI' : r ≤ rI := (min_le_right _ _).trans (min_le_right _ _)
  set B := Metric.ball Q r
  have hBt : B ⊆ D.target.carrier := fun y hy =>
    interior_subset (hball (Metric.ball_subset_ball hrI' hy))
  -- The disk.
  have hB : volume B = ENNReal.ofReal (2 * Real.pi / 2 * r ^ 2) := by
    have := hT r hr hrT'
    rwa [Tri.localAngle_interior _ hQ, Set.inter_eq_right.mpr hBt] at this
  set H := {y : Plane | g y ≤ c}
  have hHm : MeasurableSet H :=
    (isClosed_le (continuous_functional g) continuous_const).measurableSet
  have hhalf := volume_ball_inter_half hg hgQ r
  -- Each tile's share of the half-disk.
  have hper : ∀ i, volume ((D.tile i).carrier ∩ (B ∩ H)) = ENNReal.ofReal
      (if ∀ y ∈ (D.tile i).carrier, g y ≤ c then (D.tile i).localAngle Q / 2 * r ^ 2 else 0) := by
    intro i
    have hri' : r ≤ ri i := hrr0.trans ((hr0le i).trans (min_le_left _ _))
    have hsi' : r ≤ si i := hrr0.trans ((hr0le i).trans (min_le_right _ _))
    split_ifs with hsub
    · have heq : (D.tile i).carrier ∩ (B ∩ H) = (D.tile i).carrier ∩ B := by
        ext y
        simp only [Set.mem_inter_iff]
        exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, hsub y h.1⟩⟩
      rw [heq]
      exact hcontrib i r hr hri'
    · rw [ENNReal.ofReal_zero]
      by_cases hQi : Q ∈ (D.tile i).carrier
      · rcases hside i hQi with h | h
        · exact absurd h hsub
        · refine measure_mono_null ?_ (volume_level_zero hg c)
          rintro y ⟨hy, -, hyH⟩
          exact le_antisymm hyH (h y hy)
      · have hempty := hsfar i hQi
        refine measure_mono_null ?_ measure_empty
        rintro y ⟨hy, hyB, -⟩
        rw [← hempty]
        exact ⟨Metric.ball_subset_ball hsi' hyB, hy⟩
  have hsum := volume_inter_eq_sum D ((Metric.isOpen_ball (x := Q) (ε := r)).measurableSet.inter hHm)
  rw [Set.inter_eq_right.mpr (fun y hy => hBt hy.1), Finset.sum_congr rfl (fun i _ => hper i),
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => by
      split_ifs
      · have := (D.tile i).localAngle_nonneg Q; positivity
      · exact le_rfl)] at hsum
  rw [hsum, hB] at hhalf
  have hnn : 0 ≤ ∑ i, (if ∀ y ∈ (D.tile i).carrier, g y ≤ c then
      (D.tile i).localAngle Q / 2 * r ^ 2 else 0) :=
    Finset.sum_nonneg fun i _ => by
      split_ifs
      · have := (D.tile i).localAngle_nonneg Q; positivity
      · exact le_rfl
  have h2 : ∀ x : ℝ, (2 : ENNReal) * ENNReal.ofReal x = ENNReal.ofReal (2 * x) := by
    intro x; rw [ENNReal.ofReal_mul (by norm_num)]; norm_num
  rw [h2] at hhalf
  have hreal := (ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)).mp hhalf
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, ← Finset.sum_mul, ← Finset.sum_div] at hreal
  have hr2 : 0 < r ^ 2 := by positivity
  have : (∑ i ∈ Finset.univ.filter (fun i => ∀ y ∈ (D.tile i).carrier, g y ≤ c),
      (D.tile i).localAngle Q) * r ^ 2 = Real.pi * r ^ 2 := by linarith
  exact mul_right_cancel₀ hr2.ne' this

end TriangleTiling
