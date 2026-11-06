import LeanLab.GoldbachAverage.Harmonic402
import LeanLab.GoldbachAverage.LowZeroCount402

/-!
BHMS, arXiv 1704.06103v2 pages 16 to 18, Lemma 6 and the low zero pair count.
Unit height shells combine the shifted harmonic bound with the ported local zero count.
All zero sets below contain genuine nontrivial zeros with their actual multiplicities.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.Kernel402
open Finset
open LeanLab.PNTPort.Selberg LeanLab.PNTPort.ExplicitPsi1

/-- The unit shell comparison in BHMS pages 16 and 17 Lemma 6.
Replacing an ordinate by the ceiling of its absolute value costs at most two. -/
theorem reciprocal_ceil (r y : ℝ) :
    1 / (1 + |r - y|) ≤ 2 / (1 + |(⌈|r|⌉₊ : ℝ) - (|y|)|) := by
  have hlow : |r| ≤ (⌈|r|⌉₊ : ℝ) := Nat.le_ceil _
  have hhigh := Nat.ceil_lt_add_one (abs_nonneg r)
  have hs : |(⌈|r|⌉₊ : ℝ) - (|y|)| ≤ 1 + |r - y| := by
    calc _ ≤ |(⌈|r|⌉₊ : ℝ) - (|r|)| + |(|r|) - (|y|)| := abs_sub_le _ _ _
      _ ≤ 1 + |r - y| := by
        rw [abs_of_nonneg (sub_nonneg.mpr hlow)]
        linarith [abs_abs_sub_abs_le_abs_sub r y]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [abs_nonneg (r - y)]

/-- The reciprocal ordinate separation bound from BHMS Lemma 6 pages 16 and 17.
The constant is uniform in the real center y and in every finite set of genuine zeros. -/
theorem reciprocal_ordinate_sum : ∃ K : ℝ, 0 ≤ K ∧
    ∀ x : ℝ, 2 ≤ x → ∀ y : ℝ, ∀ S : Finset ℂ,
      (∀ ρ ∈ S, NZ ρ ∧ |ρ.im| ≤ x) →
      (∑ ρ ∈ S, mz ρ / (1 + |ρ.im - y|)) ≤ K * Real.log x ^ 2 := by
  classical
  obtain ⟨C, hC, hfib⟩ := fiber_count
  obtain ⟨B, hB, hlow⟩ := sum_mz_low
  refine ⟨120 * B + 128 * C, by positivity, ?_⟩
  intro x hx y S hS
  have hx0 : 0 < x := by linarith
  have hlog : (1 : ℝ) / 2 ≤ Real.log x := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
    linarith
  let L := S.filter (fun ρ => |ρ.im| ≤ 4)
  let H := S.filter (fun ρ => ¬ |ρ.im| ≤ 4)
  let M := ⌈x⌉₊
  have hM : (M : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0.le
  have hMx : (M : ℝ) + 1 ≤ x ^ 2 := by nlinarith
  have hLM : Real.log ((M : ℝ) + 1) ≤ 2 * Real.log x := by
    calc _ ≤ Real.log (x ^ 2) := Real.log_le_log (by positivity) hMx
      _ = _ := by rw [Real.log_pow]; norm_num
  have hl : (∑ ρ ∈ L, mz ρ / (1 + |ρ.im - y|)) ≤ 120 * B * Real.log x ^ 2 := by
    have hm := hlow 4 (by norm_num) L (by
      intro ρ hρ
      exact ⟨(hS ρ (mem_filter.mp hρ).1).1, (mem_filter.mp hρ).2⟩)
    have hs : (∑ ρ ∈ L, mz ρ / (1 + |ρ.im - y|)) ≤ ∑ ρ ∈ L, mz ρ := by
      apply sum_le_sum
      intro ρ _
      exact div_le_self (mz_nonneg _) (by linarith [abs_nonneg (ρ.im - y)])
    have hsquare : (1 : ℝ) / 4 ≤ Real.log x ^ 2 := by nlinarith [sq_nonneg (Real.log x - 1 / 2)]
    nlinarith [mul_le_mul_of_nonneg_left hsquare hB]
  have hmap : ∀ ρ ∈ H, ⌈|ρ.im|⌉₊ ∈ range (M + 1) := by
    intro ρ hρ
    rw [mem_range]
    have := Nat.ceil_mono (hS ρ (mem_filter.mp hρ).1).2
    change ⌈|ρ.im|⌉₊ ≤ M at this
    omega
  have hband (n : ℕ) : (∑ ρ ∈ H.filter (fun ρ => ⌈|ρ.im|⌉₊ = n), mz ρ) ≤
      8 * C * Real.log x := by
    by_cases hn : 5 ≤ n
    · have hb := hfib n hn (H.filter (fun ρ => ⌈|ρ.im|⌉₊ = n)) (by
        intro ρ hρ
        obtain ⟨hh, he⟩ := mem_filter.mp hρ
        have hN := (hS ρ (mem_filter.mp hh).1).1
        have hu : |ρ.im| ≤ (n : ℝ) := by rw [← he]; exact Nat.le_ceil _
        have hlo : (n : ℝ) - 1 < |ρ.im| := by
          have := Nat.ceil_lt_add_one (abs_nonneg ρ.im)
          rw [he] at this
          linarith
        exact ⟨hN.1, hlo, hu⟩)
      by_cases hne : (H.filter (fun ρ => ⌈|ρ.im|⌉₊ = n)).Nonempty
      · obtain ⟨ρ, hρ⟩ := hne
        obtain ⟨hh, he⟩ := mem_filter.mp hρ
        have hnM : n ≤ M := by simpa only [he, mem_range, Nat.lt_succ_iff] using hmap ρ hh
        have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
        have hnlog : Real.log n ≤ 2 * Real.log x := by
          apply le_trans (Real.log_le_log hn0 (show (n : ℝ) ≤ (M : ℝ) + 1 by exact_mod_cast (show n ≤ M + 1 by omega))) hLM
        change (∑ ρ ∈ H.filter (fun ρ => ⌈|ρ.im|⌉₊ = n), (analyticOrderNatAt riemannZeta ρ : ℝ)) ≤ _
        nlinarith [mul_le_mul_of_nonneg_left hnlog hC.le]
      · simp only [not_nonempty_iff_eq_empty.mp hne, sum_empty]
        positivity
    · have he : H.filter (fun ρ => ⌈|ρ.im|⌉₊ = n) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro ρ hρ
        obtain ⟨hh, he⟩ := mem_filter.mp hρ
        have hlo : 4 < |ρ.im| := lt_of_not_ge (mem_filter.mp hh).2
        have hu : |ρ.im| ≤ (n : ℝ) := by rw [← he]; exact Nat.le_ceil _
        have hn4 : (n : ℝ) ≤ 4 := by exact_mod_cast (show n ≤ 4 by omega)
        linarith
      rw [he, sum_empty]
      positivity
  have hh : (∑ ρ ∈ H, mz ρ / (1 + |ρ.im - y|)) ≤ 128 * C * Real.log x ^ 2 := by
    have hf := sum_fiberwise_of_maps_to hmap (fun ρ => mz ρ / (1 + |ρ.im - y|))
    rw [← hf]
    calc
      _ ≤ ∑ n ∈ range (M + 1),
          (2 / (1 + |(n : ℝ) - (|y|)|)) * (∑ ρ ∈ H.filter (fun ρ => ⌈|ρ.im|⌉₊ = n), mz ρ) := by
        apply sum_le_sum
        intro n _
        rw [mul_sum]
        apply sum_le_sum
        intro ρ hρ
        have he := (mem_filter.mp hρ).2
        have hc := mul_le_mul_of_nonneg_left (reciprocal_ceil ρ.im y) (mz_nonneg ρ)
        rw [he] at hc
        simpa only [div_eq_mul_inv, mul_one, one_mul, mul_comm, mul_left_comm, mul_assoc] using hc
      _ ≤ ∑ n ∈ range (M + 1), (2 / (1 + |(n : ℝ) - (|y|)|)) * (8 * C * Real.log x) := by
        apply sum_le_sum
        intro n _
        exact mul_le_mul_of_nonneg_left (hband n) (by positivity)
      _ = (16 * C * Real.log x) * ∑ n ∈ range (M + 1), 1 / (1 + |(n : ℝ) - (|y|)|) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro n _
        ring
      _ ≤ (16 * C * Real.log x) * (2 * (1 + Real.log ((M : ℝ) + 1))) :=
        mul_le_mul_of_nonneg_left (Harmonic402.centered_reciprocal_sum M |y|) (by positivity)
      _ ≤ 128 * C * Real.log x ^ 2 := by
        have hm := mul_le_mul_of_nonneg_left (show 2 * (1 + Real.log ((M : ℝ) + 1)) ≤ 8 * Real.log x by linarith) (show 0 ≤ 16 * C * Real.log x by positivity)
        nlinarith only [hm]
  have hsplit := sum_filter_add_sum_filter_not S (fun ρ => |ρ.im| ≤ 4)
    (f := fun ρ => mz ρ / (1 + |ρ.im - y|))
  change (∑ ρ ∈ L, mz ρ / (1 + |ρ.im - y|)) +
    (∑ ρ ∈ H, mz ρ / (1 + |ρ.im - y|)) = _ at hsplit
  rw [← hsplit]
  nlinarith only [hl, hh]

/-- The finite low zero pair count in BHMS page 18 after Lemma 6.
This retains both ordinate cutoffs and uses the genuine multiplicity count. -/
theorem finite_low_pair_count : ∃ C : ℝ, 0 ≤ C ∧
    ∀ x h : ℝ, 2 ≤ x → 2 ≤ h → h ≤ x → ∀ S : Finset ℂ,
      (∀ ρ ∈ S, NZ ρ ∧ |ρ.im| ≤ x / h) →
      (∑ ρ ∈ S, ∑ σ ∈ S, mz ρ * mz σ / (1 + |ρ.im - σ.im|)) ≤
        C * (x / h) * Real.log x ^ 4 := by
  obtain ⟨K, hK, hk⟩ := reciprocal_ordinate_sum
  obtain ⟨H, hH, hhcount⟩ := LowZeroCount402.low_ordinate_count
  refine ⟨2 * K * H, by positivity, ?_⟩
  intro x h hx hh hhx S hS
  have hx0 : 0 < x := by linarith
  have hcut : x / h ≤ x := div_le_self hx0.le (by linarith)
  have hlog : (1 : ℝ) / 2 ≤ Real.log x := by
    have := Real.log_two_gt_d9
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
    linarith
  have hmass := hhcount x h hx hh hhx S (by
    intro ρ hρ
    exact ⟨(hS ρ hρ).1.1, (hS ρ hρ).1.2.1, (hS ρ hρ).1.2.2, (hS ρ hρ).2⟩)
  have hinner (ρ : ℂ) :
      (∑ σ ∈ S, mz σ / (1 + |ρ.im - σ.im|)) ≤ K * Real.log x ^ 2 := by
    have hb := hk x hx ρ.im S (fun σ hσ => ⟨(hS σ hσ).1, (hS σ hσ).2.trans hcut⟩)
    simpa only [abs_sub_comm] using hb
  calc _ = ∑ ρ ∈ S, mz ρ * (∑ σ ∈ S, mz σ / (1 + |ρ.im - σ.im|)) := by
        apply sum_congr rfl
        intro ρ _
        rw [mul_sum]
        apply sum_congr rfl
        intro σ _
        ring
    _ ≤ ∑ ρ ∈ S, mz ρ * (K * Real.log x ^ 2) :=
      sum_le_sum (fun ρ _ => mul_le_mul_of_nonneg_left (hinner ρ) (mz_nonneg ρ))
    _ = (∑ ρ ∈ S, mz ρ) * (K * Real.log x ^ 2) := by rw [sum_mul]
    _ ≤ (H * (x / h) * Real.log x) * (K * Real.log x ^ 2) :=
      mul_le_mul_of_nonneg_right hmass (by positivity)
    _ ≤ (2 * K * H) * (x / h) * Real.log x ^ 4 := by
      have hp : Real.log x ^ 3 ≤ 2 * Real.log x ^ 4 := by
        have hm := mul_le_mul_of_nonneg_right hlog (show 0 ≤ Real.log x ^ 3 by positivity)
        nlinarith only [hm]
      have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ K * H * (x / h) by positivity)
      nlinarith only [hm]

end LeanLab.GoldbachAverage.Kernel402
