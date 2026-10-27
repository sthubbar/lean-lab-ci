/-
P0087 Akeno 2026 Appendix 5.1 page 36.
Conservative bounds for the remaining Kuhn terms.
These bounds do not certify the printed T7 to T10 intervals.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Akeno2026.SieveCTables160
import LeanLab.Akeno2026.FIntegral
import LeanLab.Akeno2026.RecursionFacts

set_option maxRecDepth 8000
namespace LeanLab.Akeno2026.KuhnTail
open Real Set MeasureTheory intervalIntegral LeanLab.Akeno2026.SieveFns

/-- One recursion step bounded by the endpoint value and the length of the interval. -/
theorem cR_next_upper (r : ℕ) {x C : ℝ}
    (hx : (r : ℝ) + 3 ≤ x) (hC : 0 ≤ C) (hp : cR (r + 2) (x - 1) ≤ C) :
    cR (r + 3) x ≤ C * (x - ((r : ℝ) + 3)) / ((r : ℝ) + 2) := by
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hdel := cR_delay (r + 1) (a := (r : ℝ) + 3) (b := x)
    (by push_cast; linarith) hx
  have hbase : cR (r + 3) ((r : ℝ) + 3) = 0 := by
    have h := cR_base (r + 1)
    have he : ((r + 1 : ℕ) : ℝ) + 2 = (r : ℝ) + 3 := by push_cast; ring
    rw [he] at h
    exact h
  rw [hbase, sub_zero] at hdel
  rw [hdel]
  have hi : IntervalIntegrable (fun u => cR (r + 2) (u - 1) / (u - 1)) volume
      ((r : ℝ) + 3) x := by
    apply IntegrableOn.intervalIntegrable
    rw [uIcc_of_le hx]
    exact integrableOn_shift (cR_mono_nonneg (r + 2)).1 (by linarith)
  have h := integral_mono_on hx hi intervalIntegrable_const (fun u hu => by
    have hf : cR (r + 2) (u - 1) ≤ C :=
      ((cR_mono_nonneg (r + 2)).1 (by linarith [hu.2])).trans hp
    calc
      cR (r + 2) (u - 1) / (u - 1) ≤ C / (u - 1) :=
        div_le_div_of_nonneg_right hf (by linarith [hu.1, hr0])
      _ ≤ C / ((r : ℝ) + 2) := div_le_div_of_nonneg_left hC (by positivity) (by linarith [hu.1]))
  simp only [intervalIntegral.integral_const, smul_eq_mul] at h
  convert h using 1; ring

/-- Read an upper bound from the certified c6 grid. -/
theorem c6_upper_of_entry (k U : ℕ) {x : ℝ} (hk : 960 ≤ k) (hk' : k ≤ 1640)
    (hx : x ≤ (k : ℝ) / 160) (hU : Grid160.cU6 k ≤ U) :
    cR 6 x ≤ (U : ℝ) / 10000000000 := by
  have h := Grid160.TB_c6 k hk hk'
  unfold TB at h
  calc
    cR 6 x ≤ cR 6 ((k : ℝ) / 160) := (cR_mono_nonneg 6).1 hx
    _ ≤ (Grid160.cU6 k : ℝ) / 10000000000 := h.2
    _ ≤ (U : ℝ) / 10000000000 :=
      div_le_div_of_nonneg_right (by exact_mod_cast hU) (by norm_num)

theorem tab_tail_checks :
    Grid160.cU6 1475 ≤ 35600000 ∧ Grid160.cU6 1315 ≤ 8940000 ∧
    Grid160.cU6 1155 ≤ 790000 ∧ Grid160.cU6 995 ≤ 320 ∧
    Grid160.cU6 1360 ≤ 14090000 ∧ Grid160.cU6 1200 ≤ 2000000 ∧
    Grid160.cU6 1040 ≤ 20000 := by decide +kernel

theorem c6_tail_bounds :
    cR 6 (1235 / 134) ≤ 0.00356 ∧ cR 6 (1235 / 134 - 1) ≤ 0.000894 ∧
    cR 6 (1235 / 134 - 2) ≤ 0.000079 ∧ cR 6 (1235 / 134 - 3) ≤ 0.000000032 ∧
    cR 6 (17 / 2) ≤ 0.001409 ∧ cR 6 (15 / 2) ≤ 0.0002 ∧ cR 6 (13 / 2) ≤ 0.000002 := by
  obtain ⟨a, b, c, d, e, f, g⟩ := tab_tail_checks
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert c6_upper_of_entry 1475 35600000 (x := 1235 / 134) (by norm_num) (by norm_num) (by norm_num) a using 1; norm_num
  · convert c6_upper_of_entry 1315 8940000 (x := 1235 / 134 - 1) (by norm_num) (by norm_num) (by norm_num) b using 1; norm_num
  · convert c6_upper_of_entry 1155 790000 (x := 1235 / 134 - 2) (by norm_num) (by norm_num) (by norm_num) c using 1; norm_num
  · convert c6_upper_of_entry 995 320 (x := 1235 / 134 - 3) (by norm_num) (by norm_num) (by norm_num) d using 1; norm_num
  · convert c6_upper_of_entry 1360 14090000 (x := 17 / 2) (by norm_num) (by norm_num) (by norm_num) e using 1; norm_num
  · convert c6_upper_of_entry 1200 2000000 (x := 15 / 2) (by norm_num) (by norm_num) (by norm_num) f using 1; norm_num
  · convert c6_upper_of_entry 1040 20000 (x := 13 / 2) (by norm_num) (by norm_num) (by norm_num) g using 1; norm_num

/-- The page 36 one dimensional Kuhn formula at the Theorem 1.2 parameters. -/
noncomputable def kuhnTr (r : ℕ) : ℝ :=
  cR r (19 / 2) + (19 / 4) *
    ∫ u in (17 / 2 : ℝ)..(1235 / 134 : ℝ), cR (r - 1) u / (u * (19 / 2 - u))

/-- A uniform endpoint bound for the integrand gives a conservative Kuhn term bound. -/
theorem kuhnTr_upper (r : ℕ) {C B : ℝ} (hC : 0 ≤ C)
    (hp : cR r (1235 / 134) ≤ C) (hb : cR (r + 1) (19 / 2) ≤ B) :
    kuhnTr (r + 1) ≤ B + (3 / 4) * C := by
  have hl0 := LeanLab.Akeno2026.FIntegral.log_split_bounds
    (by norm_num : (1 : ℝ) ≤ (1235 / 134) / (17 / 2))
  have hl1 := LeanLab.Akeno2026.FIntegral.log_split_bounds
    (by norm_num : (1 : ℝ) ≤ ((19 / 2) - (17 / 2)) / ((19 / 2) - (1235 / 134)))
  have hu := LeanLab.Akeno2026.FIntegral.both_step
    (f := cR r) (a := 17 / 2) (b := 1235 / 134) (t := 19 / 2)
    (lo := 0) (hi := C) (dl := 0) (du := 0)
    (by norm_num) (by norm_num) (by norm_num)
    ((cR_mono_nonneg r).1.monotoneOn _)
    (fun u _ => by simpa using (cR_mono_nonneg r).2 u)
    (fun u hu => by simpa using ((cR_mono_nonneg r).1 hu.2).trans hp)
    hl0.1 hl0.2 hl1.1 hl1.2 (by norm_num) hC (by norm_num) (by norm_num)
  have hlog : LeanLab.Akeno2026.FIntegral.logU ((1235 / 134) / (17 / 2)) +
      LeanLab.Akeno2026.FIntegral.logU (((19 / 2) - (17 / 2)) / ((19 / 2) - (1235 / 134))) ≤ (3 / 2 : ℝ) := by
    norm_num [LeanLab.Akeno2026.FIntegral.logU]
  have hbound : (∫ u in (17 / 2 : ℝ)..(1235 / 134 : ℝ),
      cR r u * (u⁻¹ + (19 / 2 - u)⁻¹)) ≤ (3 / 2) * C := by
    have h := mul_le_mul_of_nonneg_left hlog hC
    nlinarith [hu.2]
  have heq : (19 / 4 : ℝ) * (∫ u in (17 / 2 : ℝ)..(1235 / 134 : ℝ),
      cR r u / (u * (19 / 2 - u))) =
      (1 / 2 : ℝ) * (∫ u in (17 / 2 : ℝ)..(1235 / 134 : ℝ),
      cR r u * (u⁻¹ + (19 / 2 - u)⁻¹)) := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    apply integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num)] at hu
    have h0 : u ≠ 0 := by linarith [hu.1]
    have h1 : (19 / 2 : ℝ) - u ≠ 0 := by linarith [hu.2]
    have h2 : (19 : ℝ) - u * 2 ≠ 0 := by linarith [hu.2]
    field_simp [h0, h1, h2]
    ring
  unfold kuhnTr
  simp only [Nat.add_sub_cancel]
  rw [heq]
  linarith



theorem kuhnTr_nonneg (r : ℕ) : 0 ≤ kuhnTr r := by
  unfold kuhnTr
  apply add_nonneg ((cR_mono_nonneg r).2 _)
  apply mul_nonneg (by norm_num)
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro u hu
  apply div_nonneg ((cR_mono_nonneg (r - 1)).2 _)
  exact mul_nonneg (by linarith [hu.1]) (by linarith [hu.2])

/-- Endpoint bounds from seven c6 entries and three elementary recursion steps. -/
theorem tail_endpoint_bounds :
    cR 7 (1235 / 134) ≤ 0.000331 ∧ cR 8 (1235 / 134) ≤ 0.0000028 ∧
    cR 9 (1235 / 134) ≤ 0.000000000001 ∧
    cR 7 (19 / 2) ≤ 0.000588 ∧ cR 8 (19 / 2) ≤ 0.000011 ∧
    cR 9 (19 / 2) ≤ 0.00000000075 ∧ cR 10 (19 / 2) = 0 := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6⟩ := c6_tail_bounds
  have h7 : cR 7 (1235 / 134) ≤ 0.000331 := by
    have h := cR_next_upper 4 (x := 1235 / 134) (by norm_num) (by norm_num) b1
    norm_num at h ⊢
    linarith
  have h7m : cR 7 (1235 / 134 - 1) ≤ 0.0000161 := by
    have hp : cR 6 ((1235 / 134 - 1) - 1) ≤ 0.000079 := by convert b2 using 1; norm_num
    have h := cR_next_upper 4 (x := 1235 / 134 - 1) (by norm_num) (by norm_num) hp
    norm_num at h ⊢
    linarith
  have h8 : cR 8 (1235 / 134) ≤ 0.0000028 := by
    have h := cR_next_upper 5 (x := 1235 / 134) (by norm_num) (by norm_num) h7m
    norm_num at h ⊢
    linarith
  have h7mm : cR 7 (1235 / 134 - 2) ≤ 0.000000001155 := by
    have hp : cR 6 ((1235 / 134 - 2) - 1) ≤ 0.000000032 := by convert b3 using 1; norm_num
    have h := cR_next_upper 4 (x := 1235 / 134 - 2) (by norm_num) (by norm_num) hp
    norm_num at h ⊢
    linarith
  have h8m : cR 8 (1235 / 134 - 1) ≤ 0.0000000000358 := by
    have hp : cR 7 ((1235 / 134 - 1) - 1) ≤ 0.000000001155 := by convert h7mm using 1; norm_num
    have h := cR_next_upper 5 (x := 1235 / 134 - 1) (by norm_num) (by norm_num) hp
    norm_num at h ⊢
    linarith
  have h9 : cR 9 (1235 / 134) ≤ 0.000000000001 := by
    have h := cR_next_upper 6 (x := 1235 / 134) (by norm_num) (by norm_num) h8m
    norm_num at h ⊢
    linarith
  have ht7 : cR 7 (19 / 2) ≤ 0.000588 := by
    have hp : cR 6 ((19 / 2) - 1) ≤ 0.001409 := by convert b4 using 1; norm_num
    have h := cR_next_upper 4 (x := 19 / 2) (by norm_num) (by norm_num) hp
    norm_num at h ⊢
    linarith
  have ht7m : cR 7 (17 / 2) ≤ 0.00005 := by
    have hp : cR 6 ((17 / 2) - 1) ≤ 0.0002 := by convert b5 using 1; norm_num
    have h := cR_next_upper 4 (x := 17 / 2) (by norm_num) (by norm_num) hp
    norm_num at h ⊢
    linarith
  have ht8 : cR 8 (19 / 2) ≤ 0.000011 := by
    have hp : cR 7 ((19 / 2) - 1) ≤ 0.00005 := by convert ht7m using 1; norm_num
    have h := cR_next_upper 5 (x := 19 / 2) (by norm_num) (by norm_num) hp
    norm_num at h ⊢
    linarith
  have ht7mm : cR 7 (15 / 2) ≤ 0.000000167 := by
    have hp : cR 6 ((15 / 2) - 1) ≤ 0.000002 := by convert b6 using 1; norm_num
    have h := cR_next_upper 4 (x := 15 / 2) (by norm_num) (by norm_num) hp
    norm_num at h ⊢
    linarith
  have ht8m : cR 8 (17 / 2) ≤ 0.000000012 := by
    have hp : cR 7 ((17 / 2) - 1) ≤ 0.000000167 := by convert ht7mm using 1; norm_num
    have h := cR_next_upper 5 (x := 17 / 2) (by norm_num) (by norm_num) hp
    norm_num at h ⊢
    linarith
  have ht9 : cR 9 (19 / 2) ≤ 0.00000000075 := by
    have hp : cR 8 ((19 / 2) - 1) ≤ 0.000000012 := by convert ht8m using 1; norm_num
    have h := cR_next_upper 6 (x := 19 / 2) (by norm_num) (by norm_num) hp
    norm_num at h ⊢
    linarith
  exact ⟨h7, h8, h9, ht7, ht8, ht9, cR_eq_zero_of_le 8 (by norm_num)⟩

theorem T7_coarse_bounds : (0 : ℝ) ≤ kuhnTr 7 ∧ kuhnTr 7 ≤ 0.003258 := by
  obtain ⟨_, _, _, b7, _⟩ := tail_endpoint_bounds
  have h := kuhnTr_upper 6 (by norm_num) c6_tail_bounds.1 b7
  exact ⟨kuhnTr_nonneg 7, by norm_num at h ⊢; linarith⟩

theorem T8_coarse_bounds : (0 : ℝ) ≤ kuhnTr 8 ∧ kuhnTr 8 ≤ 0.0002593 := by
  obtain ⟨b7, _, _, _, b8, _⟩ := tail_endpoint_bounds
  have h := kuhnTr_upper 7 (by norm_num) b7 b8
  exact ⟨kuhnTr_nonneg 8, by norm_num at h ⊢; linarith⟩

theorem T9_coarse_bounds : (0 : ℝ) ≤ kuhnTr 9 ∧ kuhnTr 9 ≤ 0.000002101 := by
  obtain ⟨_, b8, _, _, _, b9, _⟩ := tail_endpoint_bounds
  have h := kuhnTr_upper 8 (by norm_num) b8 b9
  exact ⟨kuhnTr_nonneg 9, by norm_num at h ⊢; linarith⟩

theorem T10_coarse_bounds : (0 : ℝ) ≤ kuhnTr 10 ∧ kuhnTr 10 ≤ 0.000000000001 := by
  obtain ⟨_, _, b9, _, _, _, b10⟩ := tail_endpoint_bounds
  have h := kuhnTr_upper 9 (by norm_num) b9 (le_of_eq b10)
  exact ⟨kuhnTr_nonneg 10, by norm_num at h ⊢; linarith⟩

/-- A coarse tail enclosure sufficient for positivity of the sieve criterion. -/
theorem kuhnTail_bounds :
    (0 : ℝ) ≤ kuhnTr 7 + kuhnTr 8 + kuhnTr 9 + kuhnTr 10 ∧
    kuhnTr 7 + kuhnTr 8 + kuhnTr 9 + kuhnTr 10 ≤ 0.00352 := by
  obtain ⟨a, b⟩ := T7_coarse_bounds
  obtain ⟨c, d⟩ := T8_coarse_bounds
  obtain ⟨e, f⟩ := T9_coarse_bounds
  obtain ⟨g, h⟩ := T10_coarse_bounds
  constructor <;> linarith

end LeanLab.Akeno2026.KuhnTail
