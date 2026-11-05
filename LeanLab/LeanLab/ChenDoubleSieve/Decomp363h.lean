import LeanLab.ChenDoubleSieve.Decomp363g

/-!
The exact real cutoff dimension condition for the prime difference local density.
Natural ceiling predecessors preserve the strict prime cutoff at integral endpoints.
Source: https://arxiv.org/pdf/0705.1652, page 5 equation 2.3 and page 38.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task363

/-- The largest natural endpoint strictly below a positive real cutoff. -/
def strictCutoff (z : ℝ) : ℕ := ⌈z⌉₊ - 1

/-- At a real cutoff at least three, the predecessor of its natural ceiling is at least two and lies strictly below the cutoff. -/
theorem strictCutoff_bounds {z : ℝ} (hz : 3 ≤ z) :
    2 ≤ strictCutoff z ∧ (strictCutoff z : ℝ) < z ∧ z ≤ (strictCutoff z : ℝ) + 1 := by
  have hc : 2 < ⌈z⌉₊ := Nat.lt_ceil.mpr (by norm_num; linarith)
  have hcast : (strictCutoff z : ℝ) = (⌈z⌉₊ : ℝ) - 1 := by
    unfold strictCutoff
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  have hl := Nat.le_ceil z
  have hu := Nat.ceil_lt_add_one (by linarith : 0 ≤ z)
  refine ⟨by dsimp [strictCutoff]; omega, ?_, ?_⟩
  · rw [hcast]; linarith
  · rw [hcast]; linarith

/-- The natural predecessor cutoff is monotone. -/
theorem strictCutoff_mono {x z : ℝ} (hxz : x ≤ z) : strictCutoff x ≤ strictCutoff z :=
  Nat.sub_le_sub_right (Nat.ceil_mono hxz) 1

/-- The strict prime product is unchanged when a real cutoff is replaced by its natural ceiling. -/
theorem localDensity_ceil (N : ℕ) (z : ℝ) :
    localDensity N z = localDensity N (⌈z⌉₊ : ℝ) := by
  unfold localDensity
  congr 1
  ext p
  simp only [Wu41.mem_PS, Nat.cast_lt, Nat.lt_ceil]

/-- Replace a real density cutoff by its exact natural successor endpoint. -/
theorem localDensity_strictCutoff (N : ℕ) {z : ℝ} (hz : 3 ≤ z) :
    localDensity N z = localDensity N ((strictCutoff z : ℝ) + 1) := by
  rw [localDensity_ceil N z]
  congr 1
  have hc := (strictCutoff_bounds hz).1
  unfold strictCutoff at *
  have he : ⌈z⌉₊ = (⌈z⌉₊ - 1) + 1 := by omega
  exact_mod_cast he

/-- A real cutoff within one above a number at least two has the stated elementary logarithmic bounds. -/
theorem cutoff_log_bounds {x m : ℝ} (hm : 2 ≤ m) (hx : m < x) (hxm : x ≤ m + 1) :
    log x ≤ 2 * log m ∧ log x - log m ≤ 1 := by
  have hmpos : 0 < m := by linarith
  have hxpos : 0 < x := by linarith
  constructor
  · calc
      log x ≤ log (m ^ 2) := log_le_log hxpos (by nlinarith)
      _ = _ := log_pow m 2
  · have hratio : x / m ≤ 2 := (div_le_iff₀ hmpos).2 (by linarith)
    have hl := log_le_sub_one_of_pos (div_pos hxpos hmpos)
    rw [log_div hxpos.ne' hmpos.ne'] at hl
    linarith


/-- The predecessor logarithms in the dimension bound can be replaced by the actual real cutoff with an absolute larger constant. -/
theorem dimension_factor_shift {x m K : ℝ} (hm : 2 ≤ m) (hx : m < x)
    (hxm : x ≤ m + 1) (hK : 0 ≤ K) :
    (log x / log m) * (1 + K / log m) ≤
      1 + (2 + 2 * K + 4 * K / log 2) / log x := by
  have hm0 : 0 < log m := log_pos (by linarith)
  have hx0 : 0 < log x := log_pos (by linarith)
  have h2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  obtain ⟨hlog, hdiff⟩ := cutoff_log_bounds hm hx hxm
  have hr : 1 / log m ≤ 2 / log x := by
    rw [div_le_div_iff₀ hm0 hx0]
    linarith
  have hquot : log x / log m ≤ 1 + 2 / log x := by
    calc
      _ = 1 + (log x - log m) / log m := by field_simp; ring
      _ ≤ 1 + 1 / log m := by gcongr
      _ ≤ _ := add_le_add le_rfl hr
  have hlinear : 1 + K / log m ≤ 1 + 2 * K / log x := by
    have hk := mul_le_mul_of_nonneg_left hr hK
    simp only [div_eq_mul_inv] at hk ⊢
    nlinarith only [hk]
  have hprod := mul_le_mul hquot hlinear
    (show 0 ≤ 1 + K / log m by positivity)
    (show 0 ≤ 1 + 2 / log x by positivity)
  have hlog2 : log (2 : ℝ) ≤ log x := log_le_log (by norm_num) (by linarith)
  have hrmax : 1 / log x ≤ 1 / log 2 := one_div_le_one_div_of_le h2 hlog2
  have hsq : (1 / log x) ^ 2 ≤ (1 / log 2) * (1 / log x) := by
    nlinarith [one_div_pos.mpr hx0]
  have hk := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 4 * K by positivity)
  apply hprod.trans
  simp only [div_eq_mul_inv] at hk ⊢
  nlinarith only [hk]

/-- The local density satisfies the unshifted real cutoff dimension bound above three. -/
theorem localDensity_real_dimension_above_three : ∃ K : ℝ, 1 < K ∧ ∀ N : ℕ,
    Even N → ∀ x z : ℝ, 3 ≤ x → x ≤ z →
      localDensity N x / localDensity N z ≤ (log z / log x) * (1 + K / log x) := by
  obtain ⟨K, hK, hbound⟩ := localDensity_nat_dimension
  have hK0 : 0 ≤ K := by linarith
  have h2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hnewK : 1 < 2 + 2 * K + 4 * K / log 2 := by
    have hh : 0 ≤ 4 * K / log 2 := by positivity
    linarith
  refine ⟨2 + 2 * K + 4 * K / log 2, hnewK, ?_⟩
  intro N hEven x z hx hxz
  have hz : 3 ≤ z := hx.trans hxz
  obtain ⟨hm, hmx, hxm⟩ := strictCutoff_bounds hx
  obtain ⟨hn, hnz, hzn⟩ := strictCutoff_bounds hz
  have hmn := strictCutoff_mono hxz
  have hb := hbound N hEven (strictCutoff x) (strictCutoff z) hm hmn
  rw [← localDensity_strictCutoff N hx, ← localDensity_strictCutoff N hz] at hb
  have hmR : (2 : ℝ) ≤ strictCutoff x := by exact_mod_cast hm
  have hmLog : 0 < log (strictCutoff x : ℝ) := log_pos (by linarith)
  have hxLog : 0 < log x := log_pos (by linarith)
  have hzLog : 0 ≤ log z := (log_pos (by linarith)).le
  have hnLog : log (strictCutoff z : ℝ) ≤ log z :=
    log_le_log (by exact_mod_cast (show 0 < strictCutoff z by omega)) hnz.le
  have hfactor := dimension_factor_shift hmR hmx hxm hK0
  calc
    _ ≤ (log (strictCutoff z : ℝ) / log (strictCutoff x : ℝ)) *
        (1 + K / log (strictCutoff x : ℝ)) := hb
    _ ≤ (log z / log (strictCutoff x : ℝ)) * (1 + K / log (strictCutoff x : ℝ)) := by gcongr
    _ = (log z / log x) * ((log x / log (strictCutoff x : ℝ)) *
        (1 + K / log (strictCutoff x : ℝ))) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hfactor (div_nonneg hzLog hxLog.le)


/-- For even N no prime below three contributes to the local density. -/
theorem localDensity_below_three {N : ℕ} (hEven : Even N) {z : ℝ} (hz : z ≤ 3) :
    localDensity N z = 1 := by
  apply Finset.prod_eq_one
  intro p hp
  obtain ⟨hp, _, hpz, hcop⟩ := Wu41.mem_PS.mp hp
  have hp3 : p < 3 := by exact_mod_cast (hpz.trans_le hz)
  have hp2 : p = 2 := by have := hp.two_le; omega
  subst p
  exact False.elim ((Nat.prime_two.coprime_iff_not_dvd.mp hcop) hEven.two_dvd)

/-- The actual local density satisfies Wu equation 2.3 uniformly in even N and all real cutoffs at least two. No linear sieve or distribution estimate is used. -/
theorem localDensity_dimension : ∃ K : ℝ, 1 < K ∧ ∀ N : ℕ,
    Even N → ∀ x z : ℝ, 2 ≤ x → x ≤ z →
      localDensity N x / localDensity N z ≤ (log z / log x) * (1 + K / log x) := by
  obtain ⟨K, hK, hbound⟩ := localDensity_real_dimension_above_three
  have hK0 : 0 ≤ K := by linarith
  refine ⟨K, hK, ?_⟩
  intro N hEven x z hx hxz
  have hxLog : 0 < log x := log_pos (by linarith)
  have hzLog : 0 ≤ log z := (log_pos (by linarith)).le
  by_cases hz3 : z ≤ 3
  · rw [localDensity_below_three hEven (hxz.trans hz3), localDensity_below_three hEven hz3,
      div_self one_ne_zero]
    have hratio : 1 ≤ log z / log x :=
      (one_le_div hxLog).2 (log_le_log (by linarith) hxz)
    have hsecond : 1 ≤ 1 + K / log x := by
      have hh : 0 ≤ K / log x := by positivity
      linarith
    simpa only [one_mul] using mul_le_mul hratio hsecond
      (show 0 ≤ (1 : ℝ) by norm_num) (show 0 ≤ log z / log x by positivity)
  · by_cases hx3 : 3 ≤ x
    · exact hbound N hEven x z hx3 hxz
    · have hx3le : x ≤ 3 := le_of_not_ge hx3
      have hlocal : localDensity N x = localDensity N 3 := by
        rw [localDensity_below_three hEven hx3le, localDensity_below_three hEven le_rfl]
      have hlog3 : 0 < log (3 : ℝ) := log_pos (by norm_num)
      have hxlog3 : log x ≤ log 3 := log_le_log (by linarith) hx3le
      calc
        _ = localDensity N 3 / localDensity N z := by rw [hlocal]
        _ ≤ (log z / log 3) * (1 + K / log 3) := hbound N hEven 3 z le_rfl (by linarith)
        _ ≤ _ := by
          apply mul_le_mul
          · exact div_le_div_of_nonneg_left hzLog hxLog hxlog3
          · exact add_le_add le_rfl (div_le_div_of_nonneg_left hK0 hxLog hxlog3)
          · positivity
          · positivity

end LeanLab.ChenDoubleSieve.Task363
