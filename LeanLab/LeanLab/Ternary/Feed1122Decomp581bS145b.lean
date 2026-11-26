/-
Split of ordered_prime_quadrature, MMS arXiv 1610.02017v2 page 11 bottom display
and page 12. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp678a

namespace LeanLab.Ternary.MMS.Task581.Feed1122
open Finset MeasureTheory Filter Topology

/-- Partition nodes of the interval from one tenth to one quarter into N cells. -/
noncomputable def s145q_node (N i : ℕ) : ℝ := 1 / 10 + (i : ℝ) * (3 / 20) / N

/-- Logarithmic prime mass of the i th exponent window. -/
noncomputable def s145q_cellMass (x : ℝ) (N i : ℕ) : ℝ :=
  (∑ p ∈ (Ioc ⌊x ^ s145q_node N i⌋₊ ⌊x ^ s145q_node N (i + 1)⌋₊).filter Nat.Prime,
    Real.log p / p) / Real.log x

/-- Strictly ordered cell index triples. -/
def s145q_orderedCells (N : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((range N) ×ˢ ((range N) ×ˢ (range N))).filter fun q => q.1 < q.2.1 ∧ q.2.1 < q.2.2

/-- The discrete ordered Riemann sum against a cell weight w. -/
noncomputable def s145q_cellSum (K : (ℝ × ℝ) × ℝ → ℝ) (N : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ q ∈ s145q_orderedCells N,
    K ((s145q_node N q.1, s145q_node N q.2.1), s145q_node N q.2.2) * w q.1 * w q.2.1 * w q.2.2

theorem s145q_node_pos (N i : ℕ) : 0 < s145q_node N i := by
  unfold s145q_node; positivity

theorem s145q_node_mono (N i : ℕ) : s145q_node N i ≤ s145q_node N (i + 1) := by
  unfold s145q_node; push_cast
  have : (i : ℝ) * (3 / 20) / N ≤ ((i : ℝ) + 1) * (3 / 20) / N :=
    div_le_div_of_nonneg_right (by nlinarith) (Nat.cast_nonneg N)
  linarith

/-- For fixed N the discrete sum with prime cell masses tends to the discrete sum with
cell lengths. From the proved one dimensional window limit Task678.prime_log_window_tendsto. -/
theorem s145q_cellSum_tendsto (K : (ℝ × ℝ) × ℝ → ℝ) (N : ℕ) :
    Tendsto (fun x => s145q_cellSum K N (s145q_cellMass x N)) atTop
      (𝓝 (s145q_cellSum K N (fun i => s145q_node N (i + 1) - s145q_node N i))) := by
  unfold s145q_cellSum
  apply tendsto_finsetSum
  intro q _
  have hm : ∀ i : ℕ, Tendsto (fun x => s145q_cellMass x N i) atTop
      (𝓝 (s145q_node N (i + 1) - s145q_node N i)) := fun i =>
    Task678.prime_log_window_tendsto _ _ (s145q_node_pos N i) (s145q_node_mono N i)
  exact ((tendsto_const_nhds.mul (hm q.1)).mul (hm q.2.1)).mul (hm q.2.2)

section S145_s145q_prime_side
open Finset MeasureTheory Filter Topology

/-- Membership in a floor window is the real half open condition. -/
theorem s145x_mem_window {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) (n : ℕ) :
    n ∈ Ioc ⌊y⌋₊ ⌊z⌋₊ ↔ y < n ∧ (n : ℝ) ≤ z := by
  rw [mem_Ioc, Nat.floor_lt hy, Nat.le_floor_iff hz]

theorem s145x_node_step (N i : ℕ) :
    s145q_node N (i + 1) - s145q_node N i = (3 / 20) / N := by
  unfold s145q_node; push_cast; ring

/-- For fixed N, eventually every cell mass is at most twice the cell length. -/
theorem s145x_cellMass_eventually_le (N : ℕ) (hN : 0 < N) :
    ∀ᶠ x in atTop, ∀ i ∈ range N, s145q_cellMass x N i ≤ 2 * ((3 / 20) / N) := by
  rw [eventually_all_finset]
  intro i _
  have h := Task678.prime_log_window_tendsto _ _ (s145q_node_pos N i) (s145q_node_mono N i)
  rw [s145x_node_step] at h
  have hpos : (0 : ℝ) < (3 / 20) / N := by positivity
  exact (h.eventually_lt_const (by linarith)).mono fun x hx => hx.le

/-- Cell masses are nonnegative once x exceeds one. -/
theorem s145x_cellMass_nonneg {x : ℝ} (hx : 1 < x) (N i : ℕ) : 0 ≤ s145q_cellMass x N i := by
  unfold s145q_cellMass
  apply div_nonneg _ (Real.log_pos hx).le
  apply sum_nonneg
  intro p _
  exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)

/-- The closed cube carrying all rescaled log coordinates. -/
def s145x_cube : Set ((ℝ × ℝ) × ℝ) := (Set.Icc 0 1 ×ˢ Set.Icc 0 1) ×ˢ Set.Icc 0 1

theorem s145x_cube_compact : IsCompact s145x_cube :=
  (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc

/-- Uniform continuity modulus of the kernel on the cube. -/
theorem s145x_kernel_modulus (K : (ℝ × ℝ) × ℝ → ℝ) (hK : Continuous K) :
    ∀ ε > 0, ∃ η > 0, ∀ a ∈ s145x_cube, ∀ b ∈ s145x_cube, dist a b ≤ η →
      |K a - K b| ≤ ε := by
  intro ε hε
  obtain ⟨η, hη, h⟩ := Metric.uniformContinuousOn_iff_le.mp
    (s145x_cube_compact.uniformContinuousOn_of_continuous hK.continuousOn) ε hε
  exact ⟨η, hη, fun a ha b hb hab => by simpa [Real.dist_eq] using h a ha b hb hab⟩

/-- A uniform bound of the kernel on the cube. -/
theorem s145x_kernel_bound (K : (ℝ × ℝ) × ℝ → ℝ) (hK : Continuous K) :
    ∃ M, ∀ a ∈ s145x_cube, |K a| ≤ M := by
  obtain ⟨M, hM⟩ := s145x_cube_compact.exists_bound_of_continuousOn hK.continuousOn
  exact ⟨M, fun a ha => by simpa [Real.norm_eq_abs] using hM a ha⟩

/-- Regrouping the ordered cell sum as one sum over triples of atoms. -/
theorem s145x_regroup {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℕ) (w : α → ℝ)
    (G : ℕ × ℕ × ℕ → ℝ) (N : ℕ) :
    (∑ q ∈ s145q_orderedCells N, G q * (∑ a ∈ S.filter (fun a => f a = q.1), w a) *
        (∑ a ∈ S.filter (fun a => f a = q.2.1), w a) *
        (∑ a ∈ S.filter (fun a => f a = q.2.2), w a)) =
      ∑ t ∈ (S ×ˢ (S ×ˢ S)).filter
          (fun t => (f t.1, f t.2.1, f t.2.2) ∈ s145q_orderedCells N),
        G (f t.1, f t.2.1, f t.2.2) * w t.1 * w t.2.1 * w t.2.2 := by
  classical
  rw [← sum_fiberwise_of_maps_to (s := (S ×ˢ (S ×ˢ S)).filter
          (fun t => (f t.1, f t.2.1, f t.2.2) ∈ s145q_orderedCells N))
      (t := s145q_orderedCells N) (g := fun t => (f t.1, f t.2.1, f t.2.2))
      (fun t ht => (mem_filter.mp ht).2)]
  apply sum_congr rfl
  intro q hq
  rw [filter_filter]
  have hset : ((S ×ˢ (S ×ˢ S)).filter fun t =>
      (f t.1, f t.2.1, f t.2.2) ∈ s145q_orderedCells N ∧ (f t.1, f t.2.1, f t.2.2) = q) =
      S.filter (fun a => f a = q.1) ×ˢ (S.filter (fun a => f a = q.2.1) ×ˢ
        S.filter (fun a => f a = q.2.2)) := by
    ext ⟨a, b, c⟩
    simp only [mem_filter, mem_product]
    constructor
    · rintro ⟨⟨ha, hb, hc⟩, -, he⟩
      subst he
      exact ⟨⟨ha, rfl⟩, ⟨hb, rfl⟩, ⟨hc, rfl⟩⟩
    · rintro ⟨⟨ha, h1⟩, ⟨hb, h2⟩, ⟨hc, h3⟩⟩
      obtain ⟨q1, q2, q3⟩ := q
      simp only at h1 h2 h3
      subst h1 h2 h3
      exact ⟨⟨ha, hb, hc⟩, hq, rfl⟩
  rw [hset, show ∀ g a b c : ℝ, g * a * b * c = g * (a * (b * c)) from fun _ _ _ _ => by ring,
    sum_mul_sum, sum_mul_sum, mul_sum, sum_product]
  refine sum_congr rfl fun a ha => ?_
  rw [sum_product, mul_sum]
  refine sum_congr rfl fun b hb => ?_
  rw [mul_sum, mul_sum]
  refine sum_congr rfl fun c hc => ?_
  rw [(mem_filter.mp ha).2, (mem_filter.mp hb).2, (mem_filter.mp hc).2]
  ring

theorem s145x_rpow_lt_iff {x : ℝ} (hx : 1 < x) (a : ℝ) {p : ℕ} (hp : 0 < p) :
    x ^ a < p ↔ a < Real.log p / Real.log x := by
  rw [lt_div_iff₀ (Real.log_pos hx), ← Real.log_rpow (by linarith),
    Real.log_lt_log_iff (Real.rpow_pos_of_pos (by linarith) _) (by exact_mod_cast hp)]

theorem s145x_le_rpow_iff {x : ℝ} (hx : 1 < x) (b : ℝ) {p : ℕ} (hp : 0 < p) :
    (p : ℝ) ≤ x ^ b ↔ Real.log p / Real.log x ≤ b := by
  rw [div_le_iff₀ (Real.log_pos hx), ← Real.log_rpow (by linarith),
    Real.log_le_log_iff (by exact_mod_cast hp) (Real.rpow_pos_of_pos (by linarith) _)]

/-- The cell index of a rescaled coordinate. -/
noncomputable def s145x_idx (N : ℕ) (t : ℝ) : ℕ := ⌈(t - 1 / 10) * N / (3 / 20)⌉₊ - 1

theorem s145x_idx_iff {N : ℕ} (hN0 : 0 < N) {t : ℝ} (ht : 1 / 10 < t) (i : ℕ) :
    (s145q_node N i < t ∧ t ≤ s145q_node N (i + 1)) ↔ s145x_idx N t = i := by
  have hN : (0 : ℝ) < N := by exact_mod_cast hN0
  have h1 : s145q_node N i < t ↔ (i : ℝ) < (t - 1 / 10) * N / (3 / 20) := by
    unfold s145q_node
    rw [lt_div_iff₀ (by norm_num : (0 : ℝ) < 3 / 20), ← div_lt_iff₀ hN]
    constructor <;> intro h <;> linarith
  have h2 : t ≤ s145q_node N (i + 1) ↔ (t - 1 / 10) * N / (3 / 20) ≤ ((i + 1 : ℕ) : ℝ) := by
    unfold s145q_node
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3 / 20), ← le_div_iff₀ hN]
    constructor <;> intro h <;> linarith
  have hu : 0 < (t - 1 / 10) * N / (3 / 20) := by
    apply div_pos (mul_pos (by linarith) hN) (by norm_num)
  have hc : 1 ≤ ⌈(t - 1 / 10) * N / (3 / 20)⌉₊ := Nat.one_le_iff_ne_zero.mpr
    (by rw [Ne, Nat.ceil_eq_zero, not_le]; exact hu)
  rw [h1, h2, s145x_idx]
  have : ⌈(t - 1 / 10) * N / (3 / 20)⌉₊ - 1 = i ↔ ⌈(t - 1 / 10) * N / (3 / 20)⌉₊ = i + 1 := by
    omega
  rw [this, Nat.ceil_eq_iff (by omega)]
  simp

noncomputable def s145x_P (x : ℝ) : Finset ℕ :=
  (Ioc ⌊x ^ (1 / 10 : ℝ)⌋₊ ⌊x ^ (1 / 4 : ℝ)⌋₊).filter Nat.Prime

noncomputable def s145x_w (x : ℝ) (p : ℕ) : ℝ := (Real.log p / p) / Real.log x

noncomputable def s145x_t (x : ℝ) (p : ℕ) : ℝ := Real.log p / Real.log x

theorem s145x_node_zero (N : ℕ) : s145q_node N 0 = 1 / 10 := by simp [s145q_node]

theorem s145x_node_top {N : ℕ} (hN : 0 < N) : s145q_node N N = 1 / 4 := by
  unfold s145q_node
  have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp; norm_num

theorem s145x_node_ge (N i : ℕ) : 1 / 10 ≤ s145q_node N i := by
  unfold s145q_node; have : 0 ≤ (i : ℝ) * (3 / 20) / N := by positivity
  linarith

theorem s145x_node_le {N i : ℕ} (hi : i ≤ N) : s145q_node N i ≤ 1 / 4 := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp [s145q_node]; norm_num
  rw [← s145x_node_top h]
  unfold s145q_node
  have hiN : (i : ℝ) ≤ N := by exact_mod_cast hi
  have : (i : ℝ) * (3 / 20) / N ≤ (N : ℝ) * (3 / 20) / N :=
    div_le_div_of_nonneg_right (by nlinarith) (Nat.cast_nonneg N)
  linarith

theorem s145x_mem_P {x : ℝ} (hx : 1 < x) {p : ℕ} :
    p ∈ s145x_P x ↔ p.Prime ∧ 1 / 10 < s145x_t x p ∧ s145x_t x p ≤ 1 / 4 := by
  unfold s145x_P s145x_t
  rw [mem_filter, s145x_mem_window (Real.rpow_nonneg (by linarith) _)
    (Real.rpow_nonneg (by linarith) _)]
  constructor
  · rintro ⟨⟨h1, h2⟩, hp⟩
    exact ⟨hp, (s145x_rpow_lt_iff hx _ hp.pos).mp h1, (s145x_le_rpow_iff hx _ hp.pos).mp h2⟩
  · rintro ⟨hp, h1, h2⟩
    exact ⟨⟨(s145x_rpow_lt_iff hx _ hp.pos).mpr h1, (s145x_le_rpow_iff hx _ hp.pos).mpr h2⟩, hp⟩

theorem s145x_window_eq {x : ℝ} (hx : 1 < x) {N : ℕ} (hN : 0 < N) {i : ℕ} (hi : i < N) :
    (Ioc ⌊x ^ s145q_node N i⌋₊ ⌊x ^ s145q_node N (i + 1)⌋₊).filter Nat.Prime =
      (s145x_P x).filter (fun p => s145x_idx N (s145x_t x p) = i) := by
  ext p
  rw [mem_filter, mem_filter, s145x_mem_P hx, s145x_mem_window (Real.rpow_nonneg (by linarith) _)
    (Real.rpow_nonneg (by linarith) _)]
  have hlo := s145x_node_ge N i
  have hhi := s145x_node_le (N := N) (i := i + 1) hi
  constructor
  · rintro ⟨⟨h1, h2⟩, hp⟩
    have a := (s145x_rpow_lt_iff hx _ hp.pos).mp h1
    have b := (s145x_le_rpow_iff hx _ hp.pos).mp h2
    exact ⟨⟨hp, by unfold s145x_t; linarith, by unfold s145x_t; linarith⟩,
      (s145x_idx_iff hN (by unfold s145x_t; linarith) i).mp ⟨a, b⟩⟩
  · rintro ⟨⟨hp, h1, h2⟩, he⟩
    have := (s145x_idx_iff hN h1 i).mpr he
    exact ⟨⟨(s145x_rpow_lt_iff hx _ hp.pos).mpr this.1,
      (s145x_le_rpow_iff hx _ hp.pos).mpr this.2⟩, hp⟩

theorem s145x_cellMass_eq {x : ℝ} (hx : 1 < x) {N : ℕ} (hN : 0 < N) {i : ℕ} (hi : i < N) :
    s145q_cellMass x N i =
      ∑ p ∈ (s145x_P x).filter (fun p => s145x_idx N (s145x_t x p) = i), s145x_w x p := by
  unfold s145q_cellMass s145x_w
  rw [s145x_window_eq hx hN hi, sum_div]

theorem s145x_cellSum_eq (K : (ℝ × ℝ) × ℝ → ℝ) {x : ℝ} (hx : 1 < x) {N : ℕ} (hN : 0 < N) :
    s145q_cellSum K N (s145q_cellMass x N) =
      ∑ t ∈ (s145x_P x ×ˢ (s145x_P x ×ˢ s145x_P x)).filter
          (fun t => (s145x_idx N (s145x_t x t.1), s145x_idx N (s145x_t x t.2.1),
            s145x_idx N (s145x_t x t.2.2)) ∈ s145q_orderedCells N),
        K ((s145q_node N (s145x_idx N (s145x_t x t.1)),
            s145q_node N (s145x_idx N (s145x_t x t.2.1))),
            s145q_node N (s145x_idx N (s145x_t x t.2.2))) *
          s145x_w x t.1 * s145x_w x t.2.1 * s145x_w x t.2.2 := by
  rw [← s145x_regroup (s145x_P x) (fun p => s145x_idx N (s145x_t x p)) (s145x_w x)
    (fun q => K ((s145q_node N q.1, s145q_node N q.2.1), s145q_node N q.2.2)) N]
  unfold s145q_cellSum
  apply sum_congr rfl
  intro q hq
  have h := (mem_filter.mp hq)
  simp only [mem_product, mem_range] at h
  rw [s145x_cellMass_eq hx hN h.1.1, s145x_cellMass_eq hx hN h.1.2.1,
    s145x_cellMass_eq hx hN h.1.2.2]

theorem s145x_w_nonneg {x : ℝ} (hx : 1 < x) (p : ℕ) : 0 ≤ s145x_w x p := by
  unfold s145x_w
  exact div_nonneg (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
    (Real.log_pos hx).le

theorem s145x_w_le {x : ℝ} (hx : 1 < x) {p : ℕ} (hp : p ∈ s145x_P x) :
    s145x_w x p ≤ 1 / x ^ (1 / 10 : ℝ) := by
  have h := (s145x_mem_P hx).mp hp
  have hlow : x ^ (1 / 10 : ℝ) < p := by
    unfold s145x_P at hp
    rw [mem_filter, s145x_mem_window (Real.rpow_nonneg (by linarith) _)
      (Real.rpow_nonneg (by linarith) _)] at hp
    exact hp.1.1
  have hx0 : 0 < x ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have hp0 : (0 : ℝ) < p := hx0.trans hlow
  have ht0 : 0 ≤ s145x_t x p := by
    unfold s145x_t
    exact div_nonneg (Real.log_natCast_nonneg p) (Real.log_pos hx).le
  have e : s145x_w x p = s145x_t x p / p := by
    unfold s145x_w s145x_t; rw [div_div, div_div, mul_comm]
  rw [e]
  calc s145x_t x p / p ≤ 1 / p := div_le_div_of_nonneg_right (by linarith [h.2.2]) hp0.le
    _ ≤ 1 / x ^ (1 / 10 : ℝ) := one_div_le_one_div_of_le hx0 hlow.le

theorem s145x_node_ge_quarter {N i : ℕ} (hN : 0 < N) (hi : N ≤ i) : 1 / 4 ≤ s145q_node N i := by
  rw [← s145x_node_top hN]
  unfold s145q_node
  have hiN : (N : ℝ) ≤ i := by exact_mod_cast hi
  have : (N : ℝ) * (3 / 20) / N ≤ (i : ℝ) * (3 / 20) / N :=
    div_le_div_of_nonneg_right (by nlinarith) (Nat.cast_nonneg N)
  linarith

theorem s145x_idx_spec {x : ℝ} (hx : 1 < x) {N : ℕ} (hN : 0 < N) {p : ℕ} (hp : p ∈ s145x_P x) :
    s145x_idx N (s145x_t x p) < N ∧
      s145q_node N (s145x_idx N (s145x_t x p)) < s145x_t x p ∧
      s145x_t x p ≤ s145q_node N (s145x_idx N (s145x_t x p) + 1) := by
  have h := (s145x_mem_P hx).mp hp
  have hb := (s145x_idx_iff hN h.2.1 (s145x_idx N (s145x_t x p))).mpr rfl
  refine ⟨?_, hb⟩
  by_contra hc
  have := s145x_node_ge_quarter hN (not_lt.mp hc)
  linarith [h.2.2, hb.1]

theorem s145x_idx_mono {x : ℝ} (hx : 1 < x) (N : ℕ) {p q : ℕ} (hp : 0 < p) (hpq : p ≤ q) :
    s145x_idx N (s145x_t x p) ≤ s145x_idx N (s145x_t x q) := by
  have ht : s145x_t x p ≤ s145x_t x q := by
    unfold s145x_t
    apply div_le_div_of_nonneg_right _ (Real.log_pos hx).le
    exact Real.log_le_log (by exact_mod_cast hp) (by exact_mod_cast hpq)
  unfold s145x_idx
  apply Nat.sub_le_sub_right
  apply Nat.ceil_mono
  have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact mul_le_mul_of_nonneg_right (by linarith) this

theorem s145x_diag12 {α : Type*} (S : Finset α) (f : α → ℕ) (w : α → ℝ)
    (hw : ∀ a ∈ S, 0 ≤ w a) (m : ℝ) (hm : ∀ a ∈ S, ∑ b ∈ S.filter (fun b => f b = f a), w b ≤ m) :
    ∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, (if f a = f b then w a * w b * w c else 0) ≤
      (∑ a ∈ S, w a) * m * (∑ c ∈ S, w c) := by
  classical
  have e : ∀ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, (if f a = f b then w a * w b * w c else 0) =
      w a * (∑ c ∈ S, w c) * ∑ b ∈ S.filter (fun b => f b = f a), w b := by
    intro a _
    rw [sum_filter, mul_sum]
    apply sum_congr rfl
    intro b _
    by_cases h : f a = f b
    · simp only [h, if_true]
      rw [mul_sum, sum_mul]
      apply sum_congr rfl; intro c _; ring
    · simp [h, Ne.symm h]
  rw [sum_congr rfl e, sum_mul, sum_mul]
  apply sum_le_sum
  intro a ha
  have hM : 0 ≤ ∑ c ∈ S, w c := sum_nonneg hw
  have := mul_le_mul_of_nonneg_left (hm a ha) (mul_nonneg (hw a ha) hM)
  linarith [this]

theorem s145x_diag23 {α : Type*} (S : Finset α) (f : α → ℕ) (w : α → ℝ)
    (hw : ∀ a ∈ S, 0 ≤ w a) (m : ℝ) (hm : ∀ a ∈ S, ∑ b ∈ S.filter (fun b => f b = f a), w b ≤ m) :
    ∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, (if f b = f c then w a * w b * w c else 0) ≤
      (∑ a ∈ S, w a) * ((∑ a ∈ S, w a) * m) := by
  classical
  rw [sum_mul]
  apply sum_le_sum
  intro a ha
  have e : ∀ b ∈ S, ∑ c ∈ S, (if f b = f c then w a * w b * w c else 0) =
      w a * w b * ∑ c ∈ S.filter (fun c => f c = f b), w c := by
    intro b _
    rw [sum_filter, mul_sum]
    apply sum_congr rfl
    intro c _
    by_cases h : f b = f c
    · simp [h]
    · simp [h, Ne.symm h]
  rw [sum_congr rfl e, sum_mul, mul_sum]
  apply sum_le_sum
  intro b hb
  have := mul_le_mul_of_nonneg_left (hm b hb) (mul_nonneg (hw a ha) (hw b hb))
  linarith [this]

theorem s145x_top_mass {α : Type*} [DecidableEq α] (S : Finset α) (w : α → ℝ)
    (hw : ∀ a ∈ S, 0 ≤ w a) (n : α) (B : ℝ) (hB : n ∈ S → w n ≤ B) (hB0 : 0 ≤ B) :
    ∑ a ∈ S, ∑ b ∈ S, ∑ c ∈ S, (if c = n then w a * w b * w c else 0) ≤
      (∑ a ∈ S, w a) * (∑ a ∈ S, w a) * B := by
  rw [sum_mul, sum_mul]
  apply sum_le_sum
  intro a ha
  rw [mul_sum, sum_mul]
  apply sum_le_sum
  intro b hb
  rw [sum_ite_eq']
  split_ifs with h
  · exact mul_le_mul_of_nonneg_left (hB h) (mul_nonneg (hw a ha) (hw b hb))
  · exact mul_nonneg (mul_nonneg (hw a ha) (hw b hb)) hB0

theorem s145x_mem_P' {x : ℝ} (hx : 1 < x) {p : ℕ} :
    p ∈ s145x_P x ↔ (x ^ (1 / 10 : ℝ) < p ∧ (p : ℝ) ≤ x ^ (1 / 4 : ℝ)) ∧ p.Prime := by
  unfold s145x_P
  rw [mem_filter, s145x_mem_window (Real.rpow_nonneg (by linarith) _)
    (Real.rpow_nonneg (by linarith) _)]

theorem s145x_cube_sum {α : Type*} (S : Finset α) (w : α → ℝ) :
    ∑ t ∈ S ×ˢ (S ×ˢ S), w t.1 * w t.2.1 * w t.2.2 =
      (∑ a ∈ S, w a) * ((∑ a ∈ S, w a) * (∑ a ∈ S, w a)) := by
  rw [sum_product, sum_mul]; refine sum_congr rfl fun a _ => ?_
  rw [sum_product, sum_mul_sum, mul_sum]; refine sum_congr rfl fun b _ => ?_
  rw [mul_sum]; refine sum_congr rfl fun c _ => ?_; ring

theorem s145x_primeTriples_sub {x : ℝ} (hx : 1 < x) {p : ℕ × ℕ × ℕ} (hp : p ∈ primeTriples x) :
    p ∈ s145x_P x ×ˢ (s145x_P x ×ˢ s145x_P x) ∧ p.1 < p.2.1 ∧ p.2.1 < p.2.2 := by
  unfold primeTriples at hp
  simp only [mem_filter] at hp
  obtain ⟨-, h1, h2, h3, a1, o1, o2, b3⟩ := hp
  have o1' : (p.1 : ℝ) < p.2.1 := by exact_mod_cast o1
  have o2' : (p.2.1 : ℝ) < p.2.2 := by exact_mod_cast o2
  refine ⟨?_, o1, o2⟩
  simp only [mem_product, s145x_mem_P' hx]
  refine ⟨⟨⟨a1, by linarith⟩, h1⟩, ⟨⟨by linarith, by linarith⟩, h2⟩, ⟨⟨by linarith, by linarith⟩, h3⟩⟩

theorem s145x_dist_node {x : ℝ} (hx : 1 < x) {N : ℕ} (hN : 0 < N) {p : ℕ} (hp : p ∈ s145x_P x) :
    dist (s145x_t x p) (s145q_node N (s145x_idx N (s145x_t x p))) ≤ (3 / 20) / N := by
  have h := s145x_idx_spec hx hN hp
  have e := s145x_node_step N (s145x_idx N (s145x_t x p))
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith [h.2.1, h.2.2]

theorem s145x_t_mem {x : ℝ} (hx : 1 < x) {p : ℕ} (hp : p ∈ s145x_P x) :
    s145x_t x p ∈ Set.Icc (0 : ℝ) 1 := by
  have h := (s145x_mem_P hx).mp hp
  constructor <;> linarith [h.2.1, h.2.2]

theorem s145x_node_mem {x : ℝ} (hx : 1 < x) {N : ℕ} (hN : 0 < N) {p : ℕ} (hp : p ∈ s145x_P x) :
    s145q_node N (s145x_idx N (s145x_t x p)) ∈ Set.Icc (0 : ℝ) 1 := by
  have h := s145x_idx_spec hx hN hp
  have a := s145x_node_ge N (s145x_idx N (s145x_t x p))
  have b := s145x_node_le (N := N) h.1.le
  constructor <;> linarith

theorem s145q_prime_side_s145 (K : (ℝ × ℝ) × ℝ → ℝ) (hK : Continuous K) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |(∑ p ∈ primeTriples x,
          K ((Real.log p.1 / Real.log x, Real.log p.2.1 / Real.log x),
            Real.log p.2.2 / Real.log x) *
          ((Real.log p.1 / p.1) / Real.log x) *
          ((Real.log p.2.1 / p.2.1) / Real.log x) *
          ((Real.log p.2.2 / p.2.2) / Real.log x)) -
        s145q_cellSum K N (s145q_cellMass x N)| ≤ ε := by
  classical
  intro ε hε
  obtain ⟨B0, hB0⟩ := s145x_kernel_bound K hK
  set B := max B0 0 with hBdef
  have hB : ∀ a ∈ s145x_cube, |K a| ≤ B := fun a ha => (hB0 a ha).trans (le_max_left _ _)
  have hB0' : 0 ≤ B := le_max_right _ _
  obtain ⟨η, hη, hmod⟩ := s145x_kernel_modulus K hK (ε / 3) (by positivity)
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (1 / η + 2 * B / ε)
  refine ⟨N₀, fun N hN => ?_⟩
  have hNr : 1 / η + 2 * B / ε < N := hN₀.trans_le (by exact_mod_cast hN)
  have h1η : 0 < 1 / η := by positivity
  have h2B : 0 ≤ 2 * B / ε := by positivity
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := by linarith
    exact_mod_cast this
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hstep : (3 / 20) / (N : ℝ) ≤ η := by
    rw [div_le_iff₀ hNR]
    have : 1 < η * N := by
      have := (div_lt_iff₀' hη).mp (show 1 / η < N by linarith)
      linarith
    linarith
  have hBN : B * (2 * (2 * ((3 / 20) / (N : ℝ)))) ≤ ε / 3 := by
    have : B * (3 / 5) / N ≤ ε / 3 := by
      rw [div_le_iff₀ hNR]
      have h := (div_lt_iff₀ hε).mp (show 2 * B / ε < N by linarith)
      nlinarith
    calc B * (2 * (2 * ((3 / 20) / (N : ℝ)))) = B * (3 / 5) / N := by ring
      _ ≤ ε / 3 := this
  -- eventual conditions
  have hMt : Tendsto (fun x : ℝ => ∑ p ∈ s145x_P x, s145x_w x p) atTop (𝓝 (1 / 4 - 1 / 10)) := by
    have h := Task678.prime_log_window_tendsto (1 / 10) (1 / 4) (by norm_num) (by norm_num)
    refine h.congr fun x => ?_
    unfold s145x_P s145x_w
    rw [sum_div]
  have hev : ∀ᶠ x in atTop, 2 ≤ x ∧ (∑ p ∈ s145x_P x, s145x_w x p) ≤ 1 ∧
      (∀ i ∈ range N, s145q_cellMass x N i ≤ 2 * ((3 / 20) / N)) ∧
      3 * B / ε + 1 ≤ x ^ (1 / 10 : ℝ) := by
    filter_upwards [eventually_ge_atTop 2, (hMt.eventually_lt_const (by norm_num :
        (1 / 4 - 1 / 10 : ℝ) < 1)), s145x_cellMass_eventually_le N hNpos,
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).eventually_ge_atTop (3 * B / ε + 1)]
      with x a b c d
    exact ⟨a, b.le, c, d⟩
  obtain ⟨X, hX⟩ := eventually_atTop.mp hev
  refine ⟨X, fun x hx => ?_⟩
  obtain ⟨hx2, hM, hcell, hxb⟩ := hX x hx
  have hx1 : 1 < x := by linarith
  set P := s145x_P x with hP
  set M := ∑ p ∈ P, s145x_w x p with hMdef
  have hw : ∀ p ∈ P, 0 ≤ s145x_w x p := fun p _ => s145x_w_nonneg hx1 p
  have hM0 : 0 ≤ M := sum_nonneg hw
  set f : ℕ → ℕ := fun p => s145x_idx N (s145x_t x p) with hf
  set m : ℝ := 2 * ((3 / 20) / N) with hm
  have hm0 : 0 ≤ m := by positivity
  have hfiber : ∀ a ∈ P, ∑ b ∈ P.filter (fun b => f b = f a), s145x_w x b ≤ m := by
    intro a ha
    have hi := (s145x_idx_spec hx1 hNpos ha).1
    rw [← s145x_cellMass_eq hx1 hNpos hi]
    exact hcell _ (mem_range.mpr hi)
  change |(∑ p ∈ primeTriples x, K ((s145x_t x p.1, s145x_t x p.2.1), s145x_t x p.2.2) *
      s145x_w x p.1 * s145x_w x p.2.1 * s145x_w x p.2.2) - _| ≤ ε
  rw [s145x_cellSum_eq K hx1 hNpos]
  set PT := primeTriples x with hPT
  set T := (P ×ˢ (P ×ˢ P)).filter (fun t => (f t.1, f t.2.1, f t.2.2) ∈ s145q_orderedCells N)
    with hT
  set F : ℕ × ℕ × ℕ → ℝ := fun p => K ((s145x_t x p.1, s145x_t x p.2.1), s145x_t x p.2.2) *
      s145x_w x p.1 * s145x_w x p.2.1 * s145x_w x p.2.2 with hF
  set G : ℕ × ℕ × ℕ → ℝ := fun t => K ((s145q_node N (f t.1), s145q_node N (f t.2.1)),
      s145q_node N (f t.2.2)) * s145x_w x t.1 * s145x_w x t.2.1 * s145x_w x t.2.2 with hG
  set W : ℕ × ℕ × ℕ → ℝ := fun t => s145x_w x t.1 * s145x_w x t.2.1 * s145x_w x t.2.2 with hW
  have hW0 : ∀ t, 0 ≤ W t := fun t => mul_nonneg (mul_nonneg (s145x_w_nonneg hx1 _)
    (s145x_w_nonneg hx1 _)) (s145x_w_nonneg hx1 _)
  have hcube : ∑ t ∈ P ×ˢ (P ×ˢ P), W t = M * (M * M) := s145x_cube_sum P (s145x_w x)
  have hTsub : T ⊆ P ×ˢ (P ×ˢ P) := filter_subset _ _
  have hPTsub : ∀ t ∈ PT, t ∈ P ×ˢ (P ×ˢ P) := fun t ht => (s145x_primeTriples_sub hx1 ht).1
  -- cube memberships
  have htc : ∀ t ∈ P ×ˢ (P ×ˢ P),
      ((s145x_t x t.1, s145x_t x t.2.1), s145x_t x t.2.2) ∈ s145x_cube := by
    intro t ht
    simp only [mem_product] at ht
    exact ⟨⟨s145x_t_mem hx1 ht.1, s145x_t_mem hx1 ht.2.1⟩, s145x_t_mem hx1 ht.2.2⟩
  have hnc : ∀ t ∈ P ×ˢ (P ×ˢ P),
      ((s145q_node N (f t.1), s145q_node N (f t.2.1)), s145q_node N (f t.2.2)) ∈ s145x_cube := by
    intro t ht
    simp only [mem_product] at ht
    exact ⟨⟨s145x_node_mem hx1 hNpos ht.1, s145x_node_mem hx1 hNpos ht.2.1⟩,
      s145x_node_mem hx1 hNpos ht.2.2⟩
  have hFb : ∀ t ∈ P ×ˢ (P ×ˢ P), |F t| ≤ B * W t := by
    intro t ht
    simp only [hF, hW, mul_assoc, abs_mul]
    rw [abs_of_nonneg (s145x_w_nonneg hx1 _), abs_of_nonneg (s145x_w_nonneg hx1 _),
      abs_of_nonneg (s145x_w_nonneg hx1 _)]
    exact mul_le_mul_of_nonneg_right (by simpa [mul_assoc] using hB _ (htc t ht))
      (mul_nonneg (s145x_w_nonneg hx1 _) (mul_nonneg (s145x_w_nonneg hx1 _)
        (s145x_w_nonneg hx1 _)))
  have hGb : ∀ t ∈ P ×ˢ (P ×ˢ P), |G t| ≤ B * W t := by
    intro t ht
    simp only [hG, hW, mul_assoc, abs_mul]
    rw [abs_of_nonneg (s145x_w_nonneg hx1 _), abs_of_nonneg (s145x_w_nonneg hx1 _),
      abs_of_nonneg (s145x_w_nonneg hx1 _)]
    exact mul_le_mul_of_nonneg_right (hB _ (hnc t ht))
      (mul_nonneg (s145x_w_nonneg hx1 _) (mul_nonneg (s145x_w_nonneg hx1 _)
        (s145x_w_nonneg hx1 _)))
  have hFG : ∀ t ∈ P ×ˢ (P ×ˢ P), |F t - G t| ≤ ε / 3 * W t := by
    intro t ht
    have e : F t - G t = (K ((s145x_t x t.1, s145x_t x t.2.1), s145x_t x t.2.2) -
        K ((s145q_node N (f t.1), s145q_node N (f t.2.1)), s145q_node N (f t.2.2))) * W t := by
      simp only [hF, hG, hW]; ring
    rw [e, abs_mul, abs_of_nonneg (hW0 t)]
    apply mul_le_mul_of_nonneg_right _ (hW0 t)
    apply hmod _ (htc t ht) _ (hnc t ht)
    simp only [mem_product] at ht
    simp only [Prod.dist_eq]
    refine max_le (max_le ?_ ?_) ?_
    · exact (s145x_dist_node hx1 hNpos ht.1).trans hstep
    · exact (s145x_dist_node hx1 hNpos ht.2.1).trans hstep
    · exact (s145x_dist_node hx1 hNpos ht.2.2).trans hstep
  have hdec : (∑ t ∈ PT, F t) - (∑ t ∈ T, G t) =
      (∑ t ∈ PT.filter (· ∈ T), (F t - G t)) + (∑ t ∈ PT.filter (· ∉ T), F t) -
        (∑ t ∈ T.filter (· ∉ PT), G t) := by
    have hI : T.filter (· ∈ PT) = PT.filter (· ∈ T) := by
      ext t; simp only [mem_filter]; tauto
    rw [← sum_filter_add_sum_filter_not PT (· ∈ T) F,
      ← sum_filter_add_sum_filter_not T (· ∈ PT) G, hI, sum_sub_distrib]
    ring
  -- bound one
  have hb1 : |∑ t ∈ PT.filter (· ∈ T), (F t - G t)| ≤ ε / 3 := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hsub : PT.filter (· ∈ T) ⊆ P ×ˢ (P ×ˢ P) := fun t ht => hTsub (mem_filter.mp ht).2
    calc ∑ t ∈ PT.filter (· ∈ T), |F t - G t| ≤ ∑ t ∈ PT.filter (· ∈ T), ε / 3 * W t :=
          sum_le_sum fun t ht => hFG t (hsub ht)
      _ ≤ ∑ t ∈ P ×ˢ (P ×ˢ P), ε / 3 * W t :=
          sum_le_sum_of_subset_of_nonneg hsub fun t _ _ => mul_nonneg (by positivity) (hW0 t)
      _ = ε / 3 * (M * (M * M)) := by rw [← mul_sum, hcube]
      _ ≤ ε / 3 * 1 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have : M * M ≤ 1 := by nlinarith
          nlinarith
      _ = ε / 3 := by ring
  -- bound two, collisions
  have hb2 : |∑ t ∈ PT.filter (· ∉ T), F t| ≤ ε / 3 := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hsub : PT.filter (· ∉ T) ⊆ P ×ˢ (P ×ˢ P) := fun t ht => hPTsub t (mem_filter.mp ht).1
    have hpt : ∀ t ∈ PT.filter (· ∉ T), W t ≤
        (if f t.1 = f t.2.1 then W t else 0) + (if f t.2.1 = f t.2.2 then W t else 0) := by
      intro t ht
      obtain ⟨htPT, htT⟩ := mem_filter.mp ht
      obtain ⟨hmem, o1, o2⟩ := s145x_primeTriples_sub hx1 htPT
      have hm' := hmem
      simp only [mem_product] at hm'
      have l1 := s145x_idx_mono hx1 N (Nat.Prime.pos ((s145x_mem_P hx1).mp hm'.1).1) o1.le
      have l2 := s145x_idx_mono hx1 N (Nat.Prime.pos ((s145x_mem_P hx1).mp hm'.2.1).1) o2.le
      have i3 := (s145x_idx_spec hx1 hNpos hm'.2.2).1
      have hor : f t.1 = f t.2.1 ∨ f t.2.1 = f t.2.2 := by
        by_contra hc
        push_neg at hc
        apply htT
        rw [hT, mem_filter]
        refine ⟨hmem, ?_⟩
        unfold s145q_orderedCells
        rw [mem_filter]
        simp only [mem_product, mem_range]
        simp only [hf] at hc ⊢
        refine ⟨⟨by omega, by omega, i3⟩, by omega, by omega⟩
      rcases hor with h | h
      · rw [if_pos h]; split_ifs <;> linarith [hW0 t]
      · rw [if_pos h]; split_ifs <;> linarith [hW0 t]
    have hD : ∑ t ∈ P ×ˢ (P ×ˢ P), ((if f t.1 = f t.2.1 then W t else 0) +
        (if f t.2.1 = f t.2.2 then W t else 0)) ≤ M * m * M + M * (M * m) := by
      rw [sum_add_distrib]
      apply add_le_add
      · have := s145x_diag12 P f (s145x_w x) hw m hfiber
        simp only [sum_product]
        simpa [hW] using this
      · have := s145x_diag23 P f (s145x_w x) hw m hfiber
        simp only [sum_product]
        simpa [hW] using this
    calc ∑ t ∈ PT.filter (· ∉ T), |F t| ≤ ∑ t ∈ PT.filter (· ∉ T), B * W t :=
          sum_le_sum fun t ht => hFb t (hsub ht)
      _ = B * ∑ t ∈ PT.filter (· ∉ T), W t := by rw [mul_sum]
      _ ≤ B * ∑ t ∈ P ×ˢ (P ×ˢ P), ((if f t.1 = f t.2.1 then W t else 0) +
            (if f t.2.1 = f t.2.2 then W t else 0)) := by
          apply mul_le_mul_of_nonneg_left _ hB0'
          refine (sum_le_sum hpt).trans ?_
          apply sum_le_sum_of_subset_of_nonneg hsub
          intro t _ _
          apply add_nonneg <;> split_ifs <;> simp [hW0 t]
      _ ≤ B * (M * m * M + M * (M * m)) := mul_le_mul_of_nonneg_left hD hB0'
      _ ≤ B * (2 * m) := by
          apply mul_le_mul_of_nonneg_left _ hB0'
          have : M * M ≤ 1 := by nlinarith
          nlinarith
      _ ≤ ε / 3 := by simpa [hm] using hBN
  -- bound three, top boundary
  have hb3 : |∑ t ∈ T.filter (· ∉ PT), G t| ≤ ε / 3 := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    have hsub : T.filter (· ∉ PT) ⊆ P ×ˢ (P ×ˢ P) := fun t ht => hTsub (mem_filter.mp ht).1
    set n0 := ⌊x ^ (1 / 4 : ℝ)⌋₊ with hn0
    have hpt : ∀ t ∈ T.filter (· ∉ PT), W t ≤ if t.2.2 = n0 then W t else 0 := by
      intro t ht
      obtain ⟨htT, htPT⟩ := mem_filter.mp ht
      obtain ⟨hmem, hord⟩ := mem_filter.mp htT
      have hm' := hmem
      simp only [mem_product] at hm'
      have q1 := (s145x_mem_P' hx1).mp hm'.1
      have q2 := (s145x_mem_P' hx1).mp hm'.2.1
      have q3 := (s145x_mem_P' hx1).mp hm'.2.2
      unfold s145q_orderedCells at hord
      rw [mem_filter] at hord
      have o1 : t.1 < t.2.1 := by
        by_contra hc
        have := s145x_idx_mono hx1 N q2.2.pos (not_lt.mp hc)
        simp only [hf] at hord
        omega
      have o2 : t.2.1 < t.2.2 := by
        by_contra hc
        have := s145x_idx_mono hx1 N q3.2.pos (not_lt.mp hc)
        simp only [hf] at hord
        omega
      have heq : t.2.2 = n0 := by
        by_contra hne
        apply htPT
        have hlt : (t.2.2 : ℝ) < x ^ (1 / 4 : ℝ) := by
          rcases lt_or_eq_of_le q3.1.2 with h | h
          · exact h
          · exact absurd (by rw [hn0, ← h, Nat.floor_natCast]) hne
        have o1' : (t.1 : ℝ) < t.2.1 := by exact_mod_cast o1
        have o2' : (t.2.1 : ℝ) < t.2.2 := by exact_mod_cast o2
        have r : ∀ k : ℕ, (k : ℝ) ≤ x ^ (1 / 4 : ℝ) → k < n0 + 1 := fun k hk =>
          Nat.lt_succ_of_le (Nat.le_floor hk)
        rw [hPT]
        unfold primeTriples
        refine mem_filter.mpr ⟨?_, q1.2, q2.2, q3.2, q1.1.1, o1, o2, hlt⟩
        exact Finset.mem_product.mpr ⟨mem_range.mpr (r _ q1.1.2),
          Finset.mem_product.mpr ⟨mem_range.mpr (r _ q2.1.2), mem_range.mpr (r _ q3.1.2)⟩⟩
      rw [if_pos heq]
    have hD : ∑ t ∈ P ×ˢ (P ×ˢ P), (if t.2.2 = n0 then W t else 0) ≤
        M * M * (1 / x ^ (1 / 10 : ℝ)) := by
      have := s145x_top_mass P (s145x_w x) hw n0 (1 / x ^ (1 / 10 : ℝ))
        (fun h => s145x_w_le hx1 h) (by positivity)
      simp only [sum_product]
      simpa [hW] using this
    have hxpos : 0 < x ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    calc ∑ t ∈ T.filter (· ∉ PT), |G t| ≤ ∑ t ∈ T.filter (· ∉ PT), B * W t :=
          sum_le_sum fun t ht => hGb t (hsub ht)
      _ = B * ∑ t ∈ T.filter (· ∉ PT), W t := by rw [mul_sum]
      _ ≤ B * ∑ t ∈ P ×ˢ (P ×ˢ P), (if t.2.2 = n0 then W t else 0) := by
          apply mul_le_mul_of_nonneg_left _ hB0'
          refine (sum_le_sum hpt).trans ?_
          apply sum_le_sum_of_subset_of_nonneg hsub
          intro t _ _
          split_ifs <;> simp [hW0 t]
      _ ≤ B * (M * M * (1 / x ^ (1 / 10 : ℝ))) := mul_le_mul_of_nonneg_left hD hB0'
      _ ≤ B * (1 / x ^ (1 / 10 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hB0'
          have : M * M ≤ 1 := by nlinarith
          have h0 : 0 ≤ 1 / x ^ (1 / 10 : ℝ) := by positivity
          nlinarith
      _ ≤ ε / 3 := by
          have key : B ≤ ε / 3 * x ^ (1 / 10 : ℝ) := by
            have h := (div_le_iff₀ hε).mp (show 3 * B / ε ≤ x ^ (1 / 10 : ℝ) - 1 by linarith)
            linarith
          calc B * (1 / x ^ (1 / 10 : ℝ)) = B / x ^ (1 / 10 : ℝ) := by ring
            _ ≤ ε / 3 := (div_le_iff₀ hxpos).mpr key
  rw [hdec]
  rw [abs_le] at hb1 hb2 hb3 ⊢
  constructor <;> linarith [hb1.1, hb1.2, hb2.1, hb2.2, hb3.1, hb3.2]

end S145_s145q_prime_side

/-- Proved by S145, formerly a LEAF: MMS page 11 bottom display and page 12, the prime side of the ordered
Riemann sum. Class MEDIUM. For a continuous kernel the ordered prime triple sum is
within ε of the discrete ordered cell sum with prime cell masses, once N is large
and then x is large. Proof plan: uniform continuity of K on the compact cube for
the cells with three distinct indices; the cells with two equal indices carry
prime mass at most three N times the square of the largest cell mass, which is
small by the window limit Task678.prime_log_window_tendsto; the boundary prime at
x to the one tenth is excluded by strict inequality and the top boundary
p less than x to the one quarter differs from the floor window by at most one prime. -/
theorem s145q_prime_side (K : (ℝ × ℝ) × ℝ → ℝ) (hK : Continuous K) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |(∑ p ∈ primeTriples x,
          K ((Real.log p.1 / Real.log x, Real.log p.2.1 / Real.log x),
            Real.log p.2.2 / Real.log x) *
          ((Real.log p.1 / p.1) / Real.log x) *
          ((Real.log p.2.1 / p.2.1) / Real.log x) *
          ((Real.log p.2.2 / p.2.2) / Real.log x)) -
        s145q_cellSum K N (s145q_cellMass x N)| ≤ ε := by
  exact s145q_prime_side_s145 K hK

section S145_s145q_integral_side
open Finset MeasureTheory Filter Topology

theorem s145y_node_ge (N i : ℕ) : 1 / 10 ≤ s145q_node N i := by
  unfold s145q_node
  have : 0 ≤ (i : ℝ) * (3 / 20) / N := by positivity
  linarith

theorem s145y_node_le (N i : ℕ) (hN : 0 < N) (hi : i ≤ N) : s145q_node N i ≤ 1 / 4 := by
  unfold s145q_node
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hi' : (i : ℝ) ≤ N := by exact_mod_cast hi
  have : (i : ℝ) * (3 / 20) / N ≤ 3 / 20 := by
    rw [div_le_iff₀ hN']; nlinarith
  linarith

theorem s145y_node_succ (N i : ℕ) : s145q_node N (i + 1) - s145q_node N i = (3 / 20 : ℝ) / N := by
  unfold s145q_node; push_cast; ring

theorem s145y_node_top (N : ℕ) (hN : 0 < N) : s145q_node N N = 1 / 4 := by
  unfold s145q_node
  have hN' : (N : ℝ) ≠ 0 := by positivity
  field_simp; ring

theorem s145y_r1 (f : ℝ → ℝ) (hf : Continuous f) (η δ : ℝ) (hη : 0 ≤ η)
    (hδ : ∀ s ∈ Set.Icc (1 / 10 : ℝ) (1 / 4), ∀ t ∈ Set.Icc (1 / 10 : ℝ) (1 / 4),
      |s - t| ≤ δ → |f s - f t| ≤ η)
    (N : ℕ) (hN : 0 < N) (hh : (3 / 20 : ℝ) / N ≤ δ) (m : ℕ) (hm : m ≤ N) :
    |(∫ t in s145q_node N m..(1 / 4 : ℝ), f t) -
      ∑ k ∈ Ico m N, (3 / 20 : ℝ) / N * f (s145q_node N k)| ≤ η * (3 / 20) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← s145y_node_top N hN, ← intervalIntegral.sum_integral_adjacent_intervals_Ico hm
    (fun k _ => hf.intervalIntegrable _ _), ← Finset.sum_sub_distrib]
  calc _ ≤ ∑ k ∈ Ico m N, |(∫ x in s145q_node N k..s145q_node N (k + 1), f x) -
        (3 / 20 : ℝ) / N * f (s145q_node N k)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Ico m N, η * ((3 / 20 : ℝ) / N) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkN : k < N := (Finset.mem_Ico.mp hk).2
        have hs := s145y_node_succ N k
        have hmono := s145q_node_mono N k
        have hlo := s145y_node_ge N k
        have hhi := s145y_node_le N (k + 1) hN hkN
        have heq : (∫ x in s145q_node N k..s145q_node N (k + 1), f x) -
            (3 / 20 : ℝ) / N * f (s145q_node N k) =
            ∫ x in s145q_node N k..s145q_node N (k + 1), (f x - f (s145q_node N k)) := by
          rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) intervalIntegrable_const,
            intervalIntegral.integral_const, smul_eq_mul, hs]
        rw [heq, ← Real.norm_eq_abs]
        have := intervalIntegral.norm_integral_le_of_norm_le_const
          (a := s145q_node N k) (b := s145q_node N (k + 1)) (C := η)
          (f := fun x => f x - f (s145q_node N k)) (by
            intro x hx
            rw [Set.uIoc_of_le hmono] at hx
            rw [Real.norm_eq_abs]
            apply hδ x ⟨by linarith [hx.1], by linarith [hx.2]⟩ _ ⟨hlo, by linarith⟩
            rw [abs_of_nonneg (by linarith [hx.1])]; linarith [hx.2])
        rw [abs_of_nonneg (by linarith), hs] at this
        exact this
    _ = ((N : ℝ) - m) * (η * ((3 / 20 : ℝ) / N)) := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hm]
    _ ≤ η * (3 / 20) := by
        have hm' : (0 : ℝ) ≤ m := by positivity
        have : ((N : ℝ) - m) * ((3 / 20 : ℝ) / N) ≤ 3 / 20 := by
          rw [mul_div_assoc', div_le_iff₀ hN']; nlinarith
        nlinarith

theorem s145y_r1f (f : ℝ → ℝ) (hf : Continuous f) (η δ M : ℝ) (hη : 0 ≤ η)
    (hM : ∀ t ∈ Set.Icc (1 / 10 : ℝ) (1 / 4), |f t| ≤ M)
    (hδ : ∀ s ∈ Set.Icc (1 / 10 : ℝ) (1 / 4), ∀ t ∈ Set.Icc (1 / 10 : ℝ) (1 / 4),
      |s - t| ≤ δ → |f s - f t| ≤ η)
    (N : ℕ) (hN : 0 < N) (hh : (3 / 20 : ℝ) / N ≤ δ) (m : ℕ) (hm : m < N) :
    |(∫ t in s145q_node N m..(1 / 4 : ℝ), f t) -
      ∑ k ∈ range N, (if m < k then (3 / 20 : ℝ) / N * f (s145q_node N k) else 0)|
      ≤ η * (3 / 20) + (3 / 20 : ℝ) / N * M := by
  have h1 := s145y_r1 f hf η δ hη hδ N hN hh m hm.le
  rw [Finset.sum_eq_sum_Ico_succ_bot hm] at h1
  have h2 : ∑ k ∈ range N, (if m < k then (3 / 20 : ℝ) / N * f (s145q_node N k) else 0)
      = ∑ k ∈ Ico (m + 1) N, (3 / 20 : ℝ) / N * f (s145q_node N k) := by
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext k; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]; omega
  have h3 : |(3 / 20 : ℝ) / N * f (s145q_node N m)| ≤ (3 / 20 : ℝ) / N * M := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (hM _ ⟨s145y_node_ge N m, s145y_node_le N m hN hm.le⟩)
      (by positivity)
  rw [h2]
  rcases abs_le.mp h1 with ⟨a1, a2⟩
  rcases abs_le.mp h3 with ⟨b1, b2⟩
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem s145y_sumbound (N : ℕ) (c : ℝ) (g : ℕ → ℝ) (hg : ∀ j < N, |g j| ≤ c) :
    |∑ j ∈ range N, g j| ≤ N * c := by
  calc _ ≤ ∑ j ∈ range N, |g j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range N, c := Finset.sum_le_sum fun j hj => hg j (Finset.mem_range.mp hj)
    _ = N * c := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem s145q_integral_side_s145 (K : (ℝ × ℝ) × ℝ → ℝ) (hK : Continuous K) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |(∫ a in (1 / 10 : ℝ)..(1 / 4 : ℝ),
          ∫ b in a..(1 / 4 : ℝ), ∫ c in b..(1 / 4 : ℝ), K ((a, b), c)) -
        s145q_cellSum K N (fun i => s145q_node N (i + 1) - s145q_node N i)| ≤ ε := by
  intro ε hε
  set C := Set.Icc (1 / 10 : ℝ) (1 / 4) with hCdef
  have hC : IsCompact C := isCompact_Icc
  set G : ℝ × ℝ → ℝ := fun p => ∫ c in p.2..(1 / 4 : ℝ), K ((p.1, p.2), c) with hGdef
  have hG : Continuous G := by
    have h1 : Continuous fun p : ℝ × ℝ => ∫ c in (1 / 4 : ℝ)..p.2, K ((p.1, p.2), c) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (f := fun (p : ℝ × ℝ) c => K ((p.1, p.2), c)) (by fun_prop) continuous_snd
    have : G = fun p => -∫ c in (1 / 4 : ℝ)..p.2, K ((p.1, p.2), c) := by
      funext p; exact intervalIntegral.integral_symm _ _
    rw [this]; exact h1.neg
  set F : ℝ → ℝ := fun a => ∫ b in a..(1 / 4 : ℝ), G (a, b) with hFdef
  have hF : Continuous F := by
    have h1 : Continuous fun a : ℝ => ∫ b in (1 / 4 : ℝ)..a, G (a, b) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        (f := fun (a : ℝ) b => G (a, b)) (by fun_prop) continuous_id
    have : F = fun a => -∫ b in (1 / 4 : ℝ)..a, G (a, b) := by
      funext a; exact intervalIntegral.integral_symm _ _
    rw [this]; exact h1.neg
  have hI : (∫ a in (1 / 10 : ℝ)..(1 / 4 : ℝ),
      ∫ b in a..(1 / 4 : ℝ), ∫ c in b..(1 / 4 : ℝ), K ((a, b), c)) =
      ∫ a in (1 / 10 : ℝ)..(1 / 4 : ℝ), F a := rfl
  rw [hI]
  have hKu : UniformContinuousOn K ((C ×ˢ C) ×ˢ C) :=
    ((hC.prod hC).prod hC).uniformContinuousOn_of_continuous hK.continuousOn
  have hGu : UniformContinuousOn G (C ×ˢ C) :=
    (hC.prod hC).uniformContinuousOn_of_continuous hG.continuousOn
  have hFu : UniformContinuousOn F C := hC.uniformContinuousOn_of_continuous hF.continuousOn
  obtain ⟨MK, hMK⟩ := ((hC.prod hC).prod hC).exists_bound_of_continuousOn hK.continuousOn
  obtain ⟨MG, hMG⟩ := (hC.prod hC).exists_bound_of_continuousOn hG.continuousOn
  obtain ⟨MF, hMF⟩ := hC.exists_bound_of_continuousOn hF.continuousOn
  set e := ε / 2 with he
  have hepos : 0 < e := by positivity
  obtain ⟨δ1, hδ1, h1⟩ := Metric.uniformContinuousOn_iff_le.mp hKu e hepos
  obtain ⟨δ2, hδ2, h2⟩ := Metric.uniformContinuousOn_iff_le.mp hGu e hepos
  obtain ⟨δ3, hδ3, h3⟩ := Metric.uniformContinuousOn_iff_le.mp hFu e hepos
  set Mx := |MK| + |MG| + |MF| + 1 with hMx
  have hMxpos : 0 < Mx := by positivity
  set ρ := min (min δ1 (min δ2 δ3)) (e / (2 * Mx)) with hρ
  have hρpos : 0 < ρ := by positivity
  obtain ⟨N₀, hN₀⟩ := exists_nat_gt (1 / ρ)
  refine ⟨N₀, fun N hN => ?_⟩
  have hNR : (1 / ρ : ℝ) < N := lt_of_lt_of_le hN₀ (by exact_mod_cast hN)
  have hNpos' : (0 : ℝ) < N := lt_trans (by positivity) hNR
  have hNpos : 0 < N := by exact_mod_cast hNpos'
  set h := (3 / 20 : ℝ) / N with hhdef
  have hhpos : 0 < h := by positivity
  have hhρ : h ≤ ρ := by
    have : 1 / (N : ℝ) < ρ := (one_div_lt hNpos' hρpos).mpr hNR
    have : h ≤ 1 / (N : ℝ) := by
      rw [hhdef]; exact div_le_div_of_nonneg_right (by norm_num) hNpos'.le
    linarith
  have hh1 : h ≤ δ1 := hhρ.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hh2 : h ≤ δ2 := hhρ.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hh3 : h ≤ δ3 := hhρ.trans ((min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hhM : h * Mx ≤ e / 2 := by
    have : h ≤ e / (2 * Mx) := hhρ.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this; linarith
  have hNh : (N : ℝ) * h = 3 / 20 := by rw [hhdef]; field_simp
  have hMKx : |MK| ≤ Mx := by have := abs_nonneg MG; have := abs_nonneg MF; linarith
  have hMGx : |MG| ≤ Mx := by have := abs_nonneg MK; have := abs_nonneg MF; linarith
  have hMFx : |MF| ≤ Mx := by have := abs_nonneg MG; have := abs_nonneg MK; linarith
  have hnode : ∀ i < N, s145q_node N i ∈ C := fun i hi =>
    ⟨s145y_node_ge N i, s145y_node_le N i hNpos hi.le⟩
  -- level A
  have hA : ∀ i < N, ∀ j < N, |G (s145q_node N i, s145q_node N j) -
      ∑ k ∈ range N, (if j < k then h * K ((s145q_node N i, s145q_node N j), s145q_node N k)
        else 0)| ≤ e := by
    intro i hi j hj
    have := s145y_r1f (fun c => K ((s145q_node N i, s145q_node N j), c)) (by fun_prop) e δ1 Mx
      hepos.le (fun t ht => (Real.norm_eq_abs _ ▸ hMK _ ⟨⟨hnode i hi, hnode j hj⟩, ht⟩).trans
        ((le_abs_self _).trans hMKx))
      (fun s hs t ht hst => by
        have := h1 ((s145q_node N i, s145q_node N j), s) ⟨⟨hnode i hi, hnode j hj⟩, hs⟩
          ((s145q_node N i, s145q_node N j), t) ⟨⟨hnode i hi, hnode j hj⟩, ht⟩
          (by simp [Prod.dist_eq, Real.dist_eq]; exact hst)
        rwa [Real.dist_eq] at this) N hNpos hh1 j hj
    have hh' : (3 / 20 : ℝ) / N * Mx ≤ e / 2 := hhM
    calc _ ≤ e * (3 / 20) + (3 / 20 : ℝ) / N * Mx := this
      _ ≤ e := by linarith
  -- level B
  have hB : ∀ i < N, |F (s145q_node N i) -
      ∑ j ∈ range N, (if i < j then h * G (s145q_node N i, s145q_node N j) else 0)| ≤ e := by
    intro i hi
    have := s145y_r1f (fun b => G (s145q_node N i, b)) (by fun_prop) e δ2 Mx
      hepos.le (fun t ht => (Real.norm_eq_abs _ ▸ hMG _ ⟨hnode i hi, ht⟩).trans
        ((le_abs_self _).trans hMGx))
      (fun s hs t ht hst => by
        have := h2 (s145q_node N i, s) ⟨hnode i hi, hs⟩ (s145q_node N i, t) ⟨hnode i hi, ht⟩
          (by simp [Prod.dist_eq, Real.dist_eq]; exact hst)
        rwa [Real.dist_eq] at this) N hNpos hh2 i hi
    have hh' : (3 / 20 : ℝ) / N * Mx ≤ e / 2 := hhM
    calc _ ≤ e * (3 / 20) + (3 / 20 : ℝ) / N * Mx := this
      _ ≤ e := by linarith
  -- level C
  have hCl : |(∫ a in (1 / 10 : ℝ)..(1 / 4 : ℝ), F a) -
      ∑ i ∈ range N, h * F (s145q_node N i)| ≤ e := by
    have := s145y_r1 F hF e δ3 hepos.le
      (fun s hs t ht hst => by
        have := h3 _ hs _ ht (by rwa [Real.dist_eq])
        rwa [Real.dist_eq] at this) N hNpos hh3 0 (Nat.zero_le _)
    have h0 : s145q_node N 0 = 1 / 10 := by unfold s145q_node; simp
    rw [h0, ← Finset.range_eq_Ico] at this
    linarith
  -- rewrite the cell sum
  have hS : s145q_cellSum K N (fun i => s145q_node N (i + 1) - s145q_node N i) =
      ∑ i ∈ range N, h * ∑ j ∈ range N, (if i < j then h *
        ∑ k ∈ range N, (if j < k then h * K ((s145q_node N i, s145q_node N j), s145q_node N k)
          else 0) else 0) := by
    unfold s145q_cellSum s145q_orderedCells
    simp only [s145y_node_succ]
    rw [Finset.sum_filter, Finset.sum_product]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hij : i < j
    · simp only [hij, true_and, if_true, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases hjk : j < k
      · simp only [hjk, if_true]; ring
      · simp [hjk]
    · simp [hij]
  rw [hS]
  -- assemble
  have hBi : ∀ i < N, |F (s145q_node N i) - ∑ j ∈ range N, (if i < j then h *
        ∑ k ∈ range N, (if j < k then h * K ((s145q_node N i, s145q_node N j), s145q_node N k)
          else 0) else 0)| ≤ e + (3 / 20) * e := by
    intro i hi
    have hd : |∑ j ∈ range N, ((if i < j then h * G (s145q_node N i, s145q_node N j) else 0) -
        (if i < j then h * ∑ k ∈ range N, (if j < k then h *
          K ((s145q_node N i, s145q_node N j), s145q_node N k) else 0) else 0))| ≤ N * (h * e) := by
      apply s145y_sumbound
      intro j hj
      by_cases hij : i < j
      · simp only [hij, if_true]
        rw [← mul_sub, abs_mul, abs_of_pos hhpos]
        exact mul_le_mul_of_nonneg_left (hA i hi j hj) hhpos.le
      · simp only [hij, if_false, sub_zero, abs_zero]; positivity
    rw [Finset.sum_sub_distrib] at hd
    have hNe : (N : ℝ) * (h * e) = 3 / 20 * e := by rw [← mul_assoc, hNh]
    rw [hNe] at hd
    have := hB i hi
    rcases abs_le.mp hd with ⟨a1, a2⟩
    rcases abs_le.mp this with ⟨b1, b2⟩
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hfin : |∑ i ∈ range N, (h * F (s145q_node N i) - h * ∑ j ∈ range N, (if i < j then h *
        ∑ k ∈ range N, (if j < k then h * K ((s145q_node N i, s145q_node N j), s145q_node N k)
          else 0) else 0))| ≤ N * (h * (e + 3 / 20 * e)) := by
    apply s145y_sumbound
    intro i hi
    rw [← mul_sub, abs_mul, abs_of_pos hhpos]
    exact mul_le_mul_of_nonneg_left (hBi i hi) hhpos.le
  rw [Finset.sum_sub_distrib, ← mul_assoc, hNh] at hfin
  rcases abs_le.mp hfin with ⟨a1, a2⟩
  rcases abs_le.mp hCl with ⟨b1, b2⟩
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end S145_s145q_integral_side

/-- Proved by S145, formerly a LEAF: MMS page 11 bottom display and page 12, the integral side of the ordered
Riemann sum. Class MEDIUM. For a continuous kernel the ordered integral over
one tenth at most a at most b at most c at most one quarter is within ε of the
discrete ordered cell sum with cell lengths, for all large N. Proof plan: uniform
continuity of K on the cube for the strictly ordered cells, and the cells with two
equal indices have total volume at most three N times the cell length cubed. -/
theorem s145q_integral_side (K : (ℝ × ℝ) × ℝ → ℝ) (hK : Continuous K) :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      |(∫ a in (1 / 10 : ℝ)..(1 / 4 : ℝ),
          ∫ b in a..(1 / 4 : ℝ), ∫ c in b..(1 / 4 : ℝ), K ((a, b), c)) -
        s145q_cellSum K N (fun i => s145q_node N (i + 1) - s145q_node N i)| ≤ ε := by
  exact s145q_integral_side_s145 K hK

theorem ordered_prime_quadrature_of_s145_leaves (K : (ℝ × ℝ) × ℝ → ℝ) (hK : Continuous K) :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |(∑ p ∈ primeTriples x,
          K ((Real.log p.1 / Real.log x, Real.log p.2.1 / Real.log x),
            Real.log p.2.2 / Real.log x) *
          ((Real.log p.1 / p.1) / Real.log x) *
          ((Real.log p.2.1 / p.2.1) / Real.log x) *
          ((Real.log p.2.2 / p.2.2) / Real.log x)) -
        ∫ a in (1 / 10 : ℝ)..(1 / 4 : ℝ),
          ∫ b in a..(1 / 4 : ℝ), ∫ c in b..(1 / 4 : ℝ), K ((a, b), c)| ≤ δ := by
  intro δ hδ
  obtain ⟨N₁, h₁⟩ := s145q_prime_side K hK (δ / 3) (by linarith)
  obtain ⟨N₂, h₂⟩ := s145q_integral_side K hK (δ / 3) (by linarith)
  set N := max N₁ N₂
  obtain ⟨X₁, hX₁⟩ := h₁ N (le_max_left _ _)
  have hI := h₂ N (le_max_right _ _)
  have hT := s145q_cellSum_tendsto K N
  obtain ⟨X₂, hX₂⟩ := Metric.tendsto_atTop.mp hT (δ / 3) (by linarith)
  refine ⟨max X₁ X₂, fun x hx => ?_⟩
  have hA := hX₁ x ((le_max_left _ _).trans hx)
  have hB := hX₂ x ((le_max_right _ _).trans hx)
  rw [Real.dist_eq] at hB
  set S := ∑ p ∈ primeTriples x,
          K ((Real.log p.1 / Real.log x, Real.log p.2.1 / Real.log x),
            Real.log p.2.2 / Real.log x) *
          ((Real.log p.1 / p.1) / Real.log x) *
          ((Real.log p.2.1 / p.2.1) / Real.log x) *
          ((Real.log p.2.2 / p.2.2) / Real.log x)
  rcases abs_le.mp hA with ⟨a1, a2⟩
  rcases abs_le.mp hB.le with ⟨b1, b2⟩
  rcases abs_le.mp hI with ⟨c1, c2⟩
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end LeanLab.Ternary.MMS.Task581.Feed1122
