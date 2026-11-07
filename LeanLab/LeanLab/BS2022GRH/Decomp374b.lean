/- AI wrote this Lean code for CODEX task374. Goldbach is open.
The single endpoint, boundary correction and scalar comparison on journal p. 1224.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.Decomp148a
import LeanLab.BS2022GRH.Prefix374

namespace LeanLab.BS2022GRH.Decomp374b
open Real Finset Classical ChenThresholdGRH Decomp148a
noncomputable section

/-- The character sum over primes up to a real endpoint, journal p. 1224. -/
def primePrefix (x : ℝ) {r : ℕ} (χ : DirichletCharacter ℂ r) : ℂ :=
  ∑ p ∈ (range (⌊x⌋₊ + 1)).filter (fun p => p.Prime), χ p

/-- LEAF. Journal p. 1224, the endpoint application of Lemma 3 before display 13.
Use Ernvall Hytonen and Palojarvi Theorem 1, arXiv 2003.01925 p. 2,
and cancellation of a nonprincipal character over the reduced residues.
This estimates one endpoint, not a prime interval.
CONDITIONAL ON the existing progression_at_endpoint input. The finite residue reduction is proved. -/
theorem prefix_bound (hG : GRH) (x : ℝ) (r : ℕ)
    (hx : 25 ≤ x) (hr : 3 ≤ r) (hrx : (r : ℝ) ≤ √x)
    (χ : DirichletCharacter ℂ r) (hχ : χ ≠ 1) :
    ‖primePrefix x χ‖ ≤ r.totient * (qG x * √x * log x) := by
  apply Prefix374.norm_sum_of_residue_errors _ r (by omega) χ hχ
  intro a ha
  have har : a % r = a := Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp ha).1)
  have hp := DecompC164a.progression_at_endpoint hG r a x hr hrx (mem_filter.mp ha).2
  simpa only [filter_filter, har] using hp

/-- Floor is at most ceiling. -/
private lemma floor_le_ceil' (x : ℝ) : ⌊x⌋₊ ≤ ⌈x⌉₊ := by
  by_cases h : 0 ≤ x
  · exact Nat.cast_le.mp (le_trans (Nat.floor_le h) (Nat.le_ceil x))
  · have h' : x < 0 := not_le.mp h
    rw [Nat.floor_eq_zero.mpr (by linarith : x < 1), Nat.ceil_eq_zero.mpr h'.le]

/-- The endpoint boundary correction is at most two character values.
The two prime sets differ only at the two integer endpoints of the range. -/
private theorem interval_boundary_aux (Y Z : ℝ) (r : ℕ)
    (hZ : 25 ≤ Z) (hZY : Z < Y) (χ : DirichletCharacter ℂ r) :
    ‖(∑ p ∈ pRange Y Z, χ p) - (primePrefix Y χ - primePrefix Z χ)‖ ≤ 2 := by
  classical
  have hZ0 : (0 : ℝ) ≤ Z := by linarith
  have hZYle : Z ≤ Y := hZY.le
  have hfl : ⌊Z⌋₊ ≤ ⌊Y⌋₊ := Nat.floor_mono hZYle
  have hceil : ⌈Y⌉₊ ≤ ⌊Y⌋₊ + 1 := by
    rw [Nat.ceil_le]
    push_cast
    exact (Nat.lt_floor_add_one Y).le
  have hfloorCeil : ⌊Y⌋₊ ≤ ⌈Y⌉₊ := floor_le_ceil' Y
  set S1 : Finset ℕ := (range (⌊Y⌋₊ + 1)).filter (fun p => p.Prime) with hS1
  set S2 : Finset ℕ := (range (⌊Z⌋₊ + 1)).filter (fun p => p.Prime) with hS2
  set S3 : Finset ℕ := pRange Y Z with hS3
  have m1 : ∀ p : ℕ, p ∈ S1 ↔ p.Prime ∧ p ≤ ⌊Y⌋₊ := by
    intro p
    simp only [hS1, mem_filter, mem_range, Nat.lt_succ_iff, and_comm]
  have m2 : ∀ p : ℕ, p ∈ S2 ↔ p.Prime ∧ p ≤ ⌊Z⌋₊ := by
    intro p
    simp only [hS2, mem_filter, mem_range, Nat.lt_succ_iff, and_comm]
  have m3 : ∀ p : ℕ, p ∈ S3 ↔ p.Prime ∧ Z ≤ (p : ℝ) ∧ p < ⌈Y⌉₊ := by
    intro p
    simp only [hS3, pRange, mem_filter, mem_range]
    tauto
  have hS2S1 : S2 ⊆ S1 := by
    intro p hp
    rw [m2] at hp
    exact (m1 p).mpr ⟨hp.1, le_trans hp.2 hfl⟩
  have hS3S1 : S3 ⊆ S1 := by
    intro p hp
    have hp3 := (m3 p).mp hp
    refine (m1 p).mpr ⟨hp3.1, ?_⟩
    omega
  -- elements of S3 that are also in S2 sit at the floor of Z
  have hS3S2 : S3 ∩ S2 ⊆ ({⌊Z⌋₊} : Finset ℕ) := by
    intro p hp
    rw [mem_inter] at hp
    obtain ⟨hp3, hp2⟩ := hp
    have h1 := (m3 p).mp hp3
    have h2 := (m2 p).mp hp2
    simp only [mem_singleton]
    have heq : ((p : ℕ) : ℝ) = ((⌊Z⌋₊ : ℕ) : ℝ) :=
      le_antisymm (by exact_mod_cast h2.2) (le_trans (Nat.floor_le hZ0) h1.2.1)
    exact Nat.cast_injective heq
  have hEsing : S3 \ (S1 \ S2) ⊆ ({⌊Z⌋₊} : Finset ℕ) := by
    intro p hp
    rw [mem_sdiff] at hp
    obtain ⟨hp3, hpd⟩ := hp
    have hp2 : p ∈ S2 := by
      by_contra hcon
      exact hpd (by rw [mem_sdiff]; exact ⟨hS3S1 hp3, hcon⟩)
    exact hS3S2 (by rw [mem_inter]; exact ⟨hp3, hp2⟩)
  have hFsing : (S1 \ S2) \ S3 ⊆ ({⌊Y⌋₊} : Finset ℕ) := by
    intro p hp
    rw [mem_sdiff, mem_sdiff] at hp
    obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hp
    have h1 := (m1 p).mp hp1
    have hpgt : ⌊Z⌋₊ < p := by
      by_contra hle
      exact hp2 ((m2 p).mpr ⟨h1.1, not_lt.mp hle⟩)
    have hpZ : Z ≤ (p : ℝ) := by
      have hcast : (⌊Z⌋₊ : ℝ) + 1 ≤ (p : ℝ) := by
        have h2 : ⌊Z⌋₊ + 1 ≤ p := hpgt
        exact_mod_cast h2
      linarith [Nat.lt_floor_add_one Z]
    have hge : ⌈Y⌉₊ ≤ p := by
      by_contra hlt
      exact hp3 ((m3 p).mpr ⟨h1.1, hpZ, not_le.mp hlt⟩)
    simp only [mem_singleton]
    exact le_antisymm h1.2 (le_trans hfloorCeil hge)
  have hcardE : (S3 \ (S1 \ S2)).card ≤ 1 :=
    Finset.card_le_one.mpr (fun a ha b hb => by
      have ha' : a = ⌊Z⌋₊ := by simpa using hEsing ha
      have hb' : b = ⌊Z⌋₊ := by simpa using hEsing hb
      rw [ha', hb'])
  have hcardF : ((S1 \ S2) \ S3).card ≤ 1 :=
    Finset.card_le_one.mpr (fun a ha b hb => by
      have ha' : a = ⌊Y⌋₊ := by simpa using hFsing ha
      have hb' : b = ⌊Y⌋₊ := by simpa using hFsing hb
      rw [ha', hb'])
  have hnormE : ‖∑ p ∈ S3 \ (S1 \ S2), χ p‖ ≤ 1 := by
    have h1 : ‖∑ p ∈ S3 \ (S1 \ S2), χ p‖ ≤ ((S3 \ (S1 \ S2)).card : ℝ) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ p ∈ S3 \ (S1 \ S2), ‖χ p‖ ≤ ∑ _p ∈ S3 \ (S1 \ S2), (1 : ℝ) :=
            Finset.sum_le_sum (fun p _ => χ.norm_le_one p)
        _ = ((S3 \ (S1 \ S2)).card : ℝ) := by simp
    have h2 : ((S3 \ (S1 \ S2)).card : ℝ) ≤ 1 := by
      have h3 : ((S3 \ (S1 \ S2)).card : ℝ) ≤ ((1 : ℕ) : ℝ) := by exact_mod_cast hcardE
      simpa using h3
    linarith
  have hnormF : ‖∑ p ∈ (S1 \ S2) \ S3, χ p‖ ≤ 1 := by
    have h1 : ‖∑ p ∈ (S1 \ S2) \ S3, χ p‖ ≤ (((S1 \ S2) \ S3).card : ℝ) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ p ∈ (S1 \ S2) \ S3, ‖χ p‖ ≤ ∑ _p ∈ (S1 \ S2) \ S3, (1 : ℝ) :=
            Finset.sum_le_sum (fun p _ => χ.norm_le_one p)
        _ = (((S1 \ S2) \ S3).card : ℝ) := by simp
    have h2 : (((S1 \ S2) \ S3).card : ℝ) ≤ 1 := by
      have h3 : (((S1 \ S2) \ S3).card : ℝ) ≤ ((1 : ℕ) : ℝ) := by exact_mod_cast hcardF
      simpa using h3
    linarith
  have hD : (∑ p ∈ S1, χ p) - (∑ p ∈ S2, χ p) = ∑ p ∈ S1 \ S2, χ p := by
    have h := Finset.sum_sdiff (s₁ := S2) (s₂ := S1) (f := fun p => χ p) hS2S1
    rw [← h]
    ring
  have hsplit3 : (∑ p ∈ S3, χ p) =
      ∑ p ∈ S3 ∩ (S1 \ S2), χ p + ∑ p ∈ S3 \ (S1 \ S2), χ p := by
    have h := Finset.sum_sdiff (s₁ := S3 ∩ (S1 \ S2)) (s₂ := S3)
      (f := fun p => χ p) inter_subset_left
    rw [← h]
    have hEq : S3 \ (S3 ∩ (S1 \ S2)) = S3 \ (S1 \ S2) := by
      ext p
      simp only [mem_sdiff, mem_inter]
      tauto
    rw [hEq]
    ring
  have hsplitD : (∑ p ∈ S1 \ S2, χ p) =
      ∑ p ∈ S3 ∩ (S1 \ S2), χ p + ∑ p ∈ (S1 \ S2) \ S3, χ p := by
    have h := Finset.sum_sdiff (s₁ := S3 ∩ (S1 \ S2)) (s₂ := S1 \ S2)
      (f := fun p => χ p) inter_subset_right
    rw [← h]
    have hEq : (S1 \ S2) \ (S3 ∩ (S1 \ S2)) = (S1 \ S2) \ S3 := by
      ext p
      simp only [mem_sdiff, mem_inter]
      tauto
    rw [hEq]
    ring
  rw [primePrefix, primePrefix, ← hS1, ← hS2, hD, hsplit3, hsplitD]
  have hzero : (∑ p ∈ S3 ∩ (S1 \ S2), χ p + ∑ p ∈ S3 \ (S1 \ S2), χ p) -
      (∑ p ∈ S3 ∩ (S1 \ S2), χ p + ∑ p ∈ (S1 \ S2) \ S3, χ p) =
      ∑ p ∈ S3 \ (S1 \ S2), χ p - ∑ p ∈ (S1 \ S2) \ S3, χ p := by
    ring
  rw [hzero]
  exact (norm_sub_le _ _).trans (by linarith)

/-- LEAF. Journal p. 1224, the endpoint correction E before display 13.
Each of the two possible prime endpoints contributes at most one.
This finite correction has no GRH or progression estimate. -/
theorem interval_boundary (Y Z : ℝ) (r : ℕ)
    (hZ : 25 ≤ Z) (hZY : Z < Y) (χ : DirichletCharacter ℂ r) :
    ‖(∑ p ∈ pRange Y Z, χ p) - (primePrefix Y χ - primePrefix Z χ)‖ ≤ 2 :=
  interval_boundary_aux Y Z r hZ hZY χ

private lemma exp_0218_le : exp 0.218 ≤ 1.2436 := by
  have h := Real.exp_bound' (x := 0.218) (by norm_num) (by norm_num) (n := 8) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

private lemma exp_3_218_le : exp 3.218 ≤ 25 := by
  have h3 : exp 3 = exp 1 * exp 1 * exp 1 := by rw [← exp_add, ← exp_add]; norm_num
  have h1 : exp 1 ≤ 2.7182818286 := le_of_lt Real.exp_one_lt_d9
  have hpos : 0 < exp 1 := exp_pos 1
  have h218 := exp_0218_le
  have hp218 : 0 < exp 0.218 := exp_pos 0.218
  have e1 : exp 1 * exp 1 ≤ 2.7182818286 * 2.7182818286 :=
    mul_le_mul h1 h1 hpos.le (by norm_num)
  have e2 : exp 1 * exp 1 * exp 1 ≤ 2.7182818286 * 2.7182818286 * 2.7182818286 :=
    mul_le_mul e1 h1 (by positivity) (by norm_num)
  have e3 : exp 1 * exp 1 * exp 1 * exp 0.218 ≤
      2.7182818286 * 2.7182818286 * 2.7182818286 * 1.2436 :=
    mul_le_mul e2 h218 hp218.le (by norm_num)
  have hab : exp 3.218 = exp 3 * exp 0.218 := by
    rw [← exp_add]; norm_num
  rw [hab, h3]
  linarith

private lemma log_25_ge : (3.218 : ℝ) ≤ log 25 := by
  rw [le_log_iff_exp_le (by norm_num)]
  exact exp_3_218_le

private lemma exp_08045_le : exp 0.8045 ≤ 2.2371 := by
  have h := Real.exp_bound' (x := 0.8045) (by norm_num) (by norm_num) (n := 12) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

private lemma exp_neg_08045_ge : (0.447 : ℝ) ≤ exp (-0.8045) := by
  rw [Real.exp_neg]
  have hp : 0 < exp 0.8045 := exp_pos _
  have h := inv_anti₀ hp exp_08045_le
  have h2 : (0.447:ℝ) ≤ (2.2371:ℝ)⁻¹ := by norm_num
  linarith

private lemma exp_0825_le : exp 0.825 ≤ 2.283 := by
  have h := Real.exp_bound' (x := 0.825) (by norm_num) (by norm_num) (n := 12) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

private lemma exp_neg_0825_ge : (0.438 : ℝ) ≤ exp (-0.825) := by
  rw [Real.exp_neg]
  have hp : 0 < exp 0.825 := exp_pos _
  have h := inv_anti₀ hp exp_0825_le
  have h2 : (0.438:ℝ) ≤ (2.283:ℝ)⁻¹ := by norm_num
  linarith
private lemma exp_neg_one_ge : (0.36 : ℝ) ≤ exp (-1) := by
  rw [Real.exp_neg]
  have hp : 0 < exp 1 := exp_pos _
  have h := inv_anti₀ hp (le_of_lt Real.exp_one_lt_d9)
  have h2 : (0.36:ℝ) ≤ (2.7182818286:ℝ)⁻¹ := by norm_num
  linarith

/-- Region 1: t in [3.218, 3.3]. -/
private lemma env_r1 (t : ℝ) (h1 : 3.218 ≤ t) (h2 : t ≤ 3.3) :
    1.1 ≤ (0.0825*t + 6.5065 + 127.49/t + 1048.947/t^2 + 586.82/t^3 - 34815.168/t^4)
      + exp (-(t/4)) * (0.3285*t^2 + 0.023*t*log t + 17.84875*t + 2.1545*log t + 295.79 + 8.25/t) := by
  have ht : 0 < t := by linarith
  have hu : 0 ≤ t - 3.218 := by linarith
  have b1 : 127.49/3.218 - (127.49/3.218^2)*(t-3.218) ≤ 127.49/t := by
    have hid : (127.49 : ℝ)/t - (127.49/3.218 - (127.49/3.218^2)*(t-3.218))
        = 127.49*(t-3.218)^2/(t*3.218^2) := by
      field_simp
      ring
    have hpos : (0:ℝ) ≤ 127.49*(t-3.218)^2/(t*3.218^2) := by positivity
    linarith
  have b2 : 1048.947/3.218^2 - (2*1048.947/3.218^3)*(t-3.218) ≤ 1048.947/t^2 := by
    have hid : (1048.947 : ℝ)/t^2 - (1048.947/3.218^2 - (2*1048.947/3.218^3)*(t-3.218))
        = 1048.947*(t-3.218)^2*(2*t+3.218)/(t^2*3.218^3) := by
      field_simp
      ring
    have hpos : (0:ℝ) ≤ 1048.947*(t-3.218)^2*(2*t+3.218)/(t^2*3.218^3) := by positivity
    linarith
  have b3 : 586.82/3.218^3 - (3*586.82/3.218^4)*(t-3.218) ≤ 586.82/t^3 := by
    have hid : (586.82 : ℝ)/t^3 - (586.82/3.218^3 - (3*586.82/3.218^4)*(t-3.218))
        = 586.82*(t-3.218)^2*(3*t^2+2*t*3.218+3.218^2)/(t^3*3.218^4) := by
      field_simp
      ring
    have hpos : (0:ℝ) ≤ 586.82*(t-3.218)^2*(3*t^2+2*t*3.218+3.218^2)/(t^3*3.218^4) := by positivity
    linarith
  have b4 : -34815.168/3.218^4 + (4*34815.168/(3.3^4*3.218))*(t-3.218) ≤ -34815.168/t^4 := by
    have hkey : (1:ℝ)/3.218^4 - 1/t^4 =
        (t-3.218)*(t^3+t^2*3.218+t*3.218^2+3.218^3)/(t^4*3.218^4) := by
      field_simp
      ring
    have hA : 4*3.218^3 ≤ t^3+t^2*3.218+t*3.218^2+3.218^3 := by nlinarith
    have hB : t^4 ≤ 3.3^4 := pow_le_pow_left₀ (le_of_lt ht) h2 4
    have hbr : (0:ℝ) ≤ (t^3+t^2*3.218+t*3.218^2+3.218^3)/(t^4*3.218^4) - 4/(3.3^4*3.218) := by
      have key : (t^3+t^2*3.218+t*3.218^2+3.218^3)/(t^4*3.218^4) - 4/(3.3^4*3.218)
          = ((t^3+t^2*3.218+t*3.218^2+3.218^3)*(3.3^4*3.218) - 4*(t^4*3.218^4))
              /((t^4*3.218^4)*(3.3^4*3.218)) := by
        field_simp
      rw [key]
      apply div_nonneg _ (by positivity)
      nlinarith [hA, hB]
    have hfac : (0:ℝ) ≤ 34815.168*(t-3.218) := by
      have h0 : (0:ℝ) ≤ t - 3.218 := by linarith
      positivity
    have hmain : (0:ℝ) ≤ 34815.168*(t-3.218)*((t^3+t^2*3.218+t*3.218^2+3.218^3)/(t^4*3.218^4)
        - 4/(3.3^4*3.218)) := mul_nonneg hfac hbr
    have hid : -34815.168/t^4 - (-34815.168/3.218^4 + (4*34815.168/(3.3^4*3.218))*(t-3.218))
        = 34815.168*(t-3.218)*((t^3+t^2*3.218+t*3.218^2+3.218^3)/(t^4*3.218^4)
              - 4/(3.3^4*3.218)) := by
      have e1 : (34815.168:ℝ)*(t-3.218)*((t^3+t^2*3.218+t*3.218^2+3.218^3)/(t^4*3.218^4)
              - 4/(3.3^4*3.218))
          = 34815.168*((t-3.218)*(t^3+t^2*3.218+t*3.218^2+3.218^3)/(t^4*3.218^4))
            - 4*34815.168/(3.3^4*3.218)*(t-3.218) := by
        field_simp
      rw [e1, ← hkey]
      ring
    linarith [hid ▸ hmain]
  have hu4 : t - 3.218 ≤ 0.082 := by linarith
  have hexp : exp (-(t/4)) = exp (-0.8045) * exp (-(t-3.218)/4) := by
    rw [← exp_add]
    congr 1
    ring
  have hB : (359.128:ℝ) ≤ 0.3285*t^2 + 0.023*t*log t + 17.84875*t + 2.1545*log t + 295.79 + 8.25/t := by
    have hlog0 : 0 ≤ log t := log_nonneg (by linarith)
    have ht2 : 0.3285*(3.218:ℝ)^2 ≤ 0.3285*t^2 := by
      have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3.218) h1 2
      nlinarith
    have ht1 : 17.84875*(3.218:ℝ) ≤ 17.84875*t := by nlinarith
    have hdiv : 8.25/3.3 ≤ 8.25/t := by
      apply div_le_div_of_nonneg_left (by norm_num) ht h2
    have htlog : 0 ≤ 0.023*t*log t := by positivity
    have hlog2 : 0 ≤ 2.1545*log t := by linarith
    nlinarith
  have hE0 : (0.447:ℝ) ≤ exp (-0.8045) := exp_neg_08045_ge
  have h1mu : (0:ℝ) ≤ 1 - (t-3.218)/4 := by linarith
  have hExpU : 1 - (t-3.218)/4 ≤ exp (-(t-3.218)/4) := by
    have := Real.add_one_le_exp (-(t-3.218)/4)
    linarith
  have hstep1 : 0.447*(1-(t-3.218)/4) ≤ exp (-0.8045) * exp (-(t-3.218)/4) :=
    mul_le_mul hE0 hExpU (by linarith) (by positivity)
  have hstep2 : 0.447*(1-(t-3.218)/4)*359.128 ≤
      exp (-0.8045) * exp (-(t-3.218)/4) * (0.3285*t^2 + 0.023*t*log t + 17.84875*t + 2.1545*log t + 295.79 + 8.25/t) := by
    apply mul_le_mul hstep1 hB (by positivity) (by positivity)
  have hblin : 0.447*(1-(t-3.218)/4)*359.128 = 160.530216 - 40.132554*(t-3.218) := by
    ring
  have b5 : 160.53 - 40.14*(t-3.218) ≤
      exp (-(t/4)) * (0.3285*t^2 + 0.023*t*log t + 17.84875*t + 2.1545*log t + 295.79 + 8.25/t) := by
    have h1 : 0.447*(1-(t-3.218)/4)*359.128 ≤
      exp (-(t/4)) * (0.3285*t^2 + 0.023*t*log t + 17.84875*t + 2.1545*log t + 295.79 + 8.25/t) := by
      rw [hexp]
      exact hstep2
    linarith [h1, hblin, hu]
  have b6 : 0.0825*(3.218:ℝ) + 6.5065 ≤ 0.0825*t + 6.5065 := by nlinarith
  have hmain : (0.0825*(3.218:ℝ) + 6.5065) + (127.49/3.218 - (127.49/3.218^2)*(t-3.218))
      + (1048.947/3.218^2 - (2*1048.947/3.218^3)*(t-3.218))
      + (586.82/3.218^3 - (3*586.82/3.218^4)*(t-3.218))
      + (-34815.168/3.218^4 + (4*34815.168/(3.3^4*3.218))*(t-3.218))
      + (160.53 - 40.14*(t-3.218))
      ≤ (0.0825*t + 6.5065 + 127.49/t + 1048.947/t^2 + 586.82/t^3 - 34815.168/t^4)
      + exp (-(t/4)) * (0.3285*t^2 + 0.023*t*log t + 17.84875*t + 2.1545*log t + 295.79 + 8.25/t) := by
    linear_combination b1 + b2 + b3 + b4 + b5 + b6
  have hval : (1.1:ℝ) ≤ (0.0825*(3.218:ℝ) + 6.5065) + (127.49/3.218 - (127.49/3.218^2)*(t-3.218))
      + (1048.947/3.218^2 - (2*1048.947/3.218^3)*(t-3.218))
      + (586.82/3.218^3 - (3*586.82/3.218^4)*(t-3.218))
      + (-34815.168/3.218^4 + (4*34815.168/(3.3^4*3.218))*(t-3.218))
      + (160.53 - 40.14*(t-3.218)) := by
    nlinarith [hu]
  exact le_trans hval hmain

/-- Region 2: t in [3.3, 4]. -/
private lemma env_r2 (t : ℝ) (h1 : 3.3 ≤ t) (h2 : t ≤ 4) :
    22.0 ≤ (0.0825*t + 6.5065 + 127.49/t + 1048.947/t^2 + 586.82/t^3 - 34815.168/t^4)
      + exp (-(t/4)) * (0.3285*t^2 + 0.023*t*log t + 17.84875*t + 2.1545*log t + 295.79 + 8.25/t) := by
  have ht : 0 < t := by linarith
  have hu : 0 ≤ t - 3.3 := by linarith
  have hu4 : t - 3.3 ≤ 0.7 := by linarith
  have b1 : 127.49/3.3 - (127.49/3.3^2)*(t-3.3) ≤ 127.49/t := by
    have hid : (127.49 : ℝ)/t - (127.49/3.3 - (127.49/3.3^2)*(t-3.3))
        = 127.49*(t-3.3)^2/(t*3.3^2) := by
      field_simp
      ring
    have hpos : (0:ℝ) ≤ 127.49*(t-3.3)^2/(t*3.3^2) := by positivity
    linarith
  have b2 : 1048.947/3.3^2 - (2*1048.947/3.3^3)*(t-3.3) ≤ 1048.947/t^2 := by
    have hid : (1048.947 : ℝ)/t^2 - (1048.947/3.3^2 - (2*1048.947/3.3^3)*(t-3.3))
        = 1048.947*(t-3.3)^2*(2*t+3.3)/(t^2*3.3^3) := by
      field_simp
      ring
    have hpos : (0:ℝ) ≤ 1048.947*(t-3.3)^2*(2*t+3.3)/(t^2*3.3^3) := by positivity
    linarith
  have b3 : 586.82/3.3^3 - (3*586.82/3.3^4)*(t-3.3) ≤ 586.82/t^3 := by
    have hid : (586.82 : ℝ)/t^3 - (586.82/3.3^3 - (3*586.82/3.3^4)*(t-3.3))
        = 586.82*(t-3.3)^2*(3*t^2+2*t*3.3+3.3^2)/(t^3*3.3^4) := by
      field_simp
      ring
    have hpos : (0:ℝ) ≤ 586.82*(t-3.3)^2*(3*t^2+2*t*3.3+3.3^2)/(t^3*3.3^4) := by positivity
    linarith
  have b4 : -34815.168/3.3^4 + (4*34815.168/(4^4*3.3))*(t-3.3) ≤ -34815.168/t^4 := by
    have hkey : (1:ℝ)/3.3^4 - 1/t^4 =
        (t-3.3)*(t^3+t^2*3.3+t*3.3^2+3.3^3)/(t^4*3.3^4) := by
      field_simp
      ring
    have hA : 4*3.3^3 ≤ t^3+t^2*3.3+t*3.3^2+3.3^3 := by nlinarith
    have hB : t^4 ≤ 4^4 := pow_le_pow_left₀ (le_of_lt ht) h2 4
    have hbr : (0:ℝ) ≤ (t^3+t^2*3.3+t*3.3^2+3.3^3)/(t^4*3.3^4) - 4/(4^4*3.3) := by
      have key : (t^3+t^2*3.3+t*3.3^2+3.3^3)/(t^4*3.3^4) - 4/(4^4*3.3)
          = ((t^3+t^2*3.3+t*3.3^2+3.3^3)*(4^4*3.3) - 4*(t^4*3.3^4))
              /((t^4*3.3^4)*(4^4*3.3)) := by
        field_simp
      rw [key]
      apply div_nonneg _ (by positivity)
      nlinarith [hA, hB]
    have hfac : (0:ℝ) ≤ 34815.168*(t-3.3) := by
      have h0 : (0:ℝ) ≤ t - 3.3 := by linarith
      positivity
    have hmain : (0:ℝ) ≤ 34815.168*(t-3.3)*((t^3+t^2*3.3+t*3.3^2+3.3^3)/(t^4*3.3^4)
        - 4/(4^4*3.3)) := mul_nonneg hfac hbr
    have hid : -34815.168/t^4 - (-34815.168/3.3^4 + (4*34815.168/(4^4*3.3))*(t-3.3))
        = 34815.168*(t-3.3)*((t^3+t^2*3.3+t*3.3^2+3.3^3)/(t^4*3.3^4)
              - 4/(4^4*3.3)) := by
      have e1 : (34815.168:ℝ)*(t-3.3)*((t^3+t^2*3.3+t*3.3^2+3.3^3)/(t^4*3.3^4)
              - 4/(4^4*3.3))
          = 34815.168*((t-3.3)*(t^3+t^2*3.3+t*3.3^2+3.3^3)/(t^4*3.3^4))
            - 4*34815.168/(4^4*3.3)*(t-3.3) := by
        field_simp
      rw [e1, ← hkey]
      ring
    linarith [hid ▸ hmain]
  have hexp : exp (-(t/4)) = exp (-0.825) * exp (-(t-3.3)/4) := by
    rw [← exp_add]
    congr 1
    ring
  have hB : (360.33:ℝ) ≤ 0.3285*t^2 + 0.023*t*log t + 17.84875*t + 2.1545*log t + 295.79 + 8.25/t := by
    have hlog0 : 0 ≤ log t := log_nonneg (by linarith)
    have ht2 : 0.3285*(3.3:ℝ)^2 ≤ 0.3285*t^2 := by
      have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 3.3) h1 2
      nlinarith
    have ht1 : 17.84875*(3.3:ℝ) ≤ 17.84875*t := by nlinarith
    have hdiv : 8.25/4 ≤ 8.25/t := by
      apply div_le_div_of_nonneg_left (by norm_num) ht h2
    have htlog : 0 ≤ 0.023*t*log t := by positivity
    have hlog2 : 0 ≤ 2.1545*log t := by linarith
    nlinarith
  have hE0 : (0.438:ℝ) ≤ exp (-0.825) := exp_neg_0825_ge
  have h1mu : (0:ℝ) ≤ 1 - (t-3.3)/4 := by linarith
  have hExpU : 1 - (t-3.3)/4 ≤ exp (-(t-3.3)/4) := by
    have := Real.add_one_le_exp (-(t-3.3)/4)
    linarith
  have hstep1 : 0.438*(1-(t-3.3)/4) ≤ exp (-0.825) * exp (-(t-3.3)/4) :=
    mul_le_mul hE0 hExpU (by linarith) (by positivity)
  have hstep2 : 0.438*(1-(t-3.3)/4)*360.33 ≤
      exp (-0.825) * exp (-(t-3.3)/4) * (0.3285*t^2 + 0.023*t*log t + 17.84875*t + 2.1545*log t + 295.79 + 8.25/t) := by
    apply mul_le_mul hstep1 hB (by positivity) (by positivity)
  have hblin : 0.438*(1-(t-3.3)/4)*360.33 = 157.82454 - 39.456135*(t-3.3) := by
    ring
  have b5 : 157.82 - 39.46*(t-3.3) ≤
      exp (-(t/4)) * (0.3285*t^2 + 0.023*t*log t + 17.84875*t + 2.1545*log t + 295.79 + 8.25/t) := by
    have h1' : 0.438*(1-(t-3.3)/4)*360.33 ≤
      exp (-(t/4)) * (0.3285*t^2 + 0.023*t*log t + 17.84875*t + 2.1545*log t + 295.79 + 8.25/t) := by
      rw [hexp]
      exact hstep2
    linarith [h1', hblin, hu]
  have b6 : 0.0825*(3.3:ℝ) + 6.5065 ≤ 0.0825*t + 6.5065 := by nlinarith
  have hmain : (0.0825*(3.3:ℝ) + 6.5065) + (127.49/3.3 - (127.49/3.3^2)*(t-3.3))
      + (1048.947/3.3^2 - (2*1048.947/3.3^3)*(t-3.3))
      + (586.82/3.3^3 - (3*586.82/3.3^4)*(t-3.3))
      + (-34815.168/3.3^4 + (4*34815.168/(4^4*3.3))*(t-3.3))
      + (157.82 - 39.46*(t-3.3))
      ≤ (0.0825*t + 6.5065 + 127.49/t + 1048.947/t^2 + 586.82/t^3 - 34815.168/t^4)
      + exp (-(t/4)) * (0.3285*t^2 + 0.023*t*log t + 17.84875*t + 2.1545*log t + 295.79 + 8.25/t) := by
    linear_combination b1 + b2 + b3 + b4 + b5 + b6
  have hval : (22.0:ℝ) ≤ (0.0825*(3.3:ℝ) + 6.5065) + (127.49/3.3 - (127.49/3.3^2)*(t-3.3))
      + (1048.947/3.3^2 - (2*1048.947/3.3^3)*(t-3.3))
      + (586.82/3.3^3 - (3*586.82/3.3^4)*(t-3.3))
      + (-34815.168/3.3^4 + (4*34815.168/(4^4*3.3))*(t-3.3))
      + (157.82 - 39.46*(t-3.3)) := by
    nlinarith [hu]
  exact le_trans hval hmain

/-- Region 3: t in [4, 5]. -/
private lemma env_r3 (t : ℝ) (h1 : 4 ≤ t) (h2 : t ≤ 5) :
    86 ≤ (0.0825*t + 6.5065 + 127.49/t + 1048.947/t^2 + 586.82/t^3 - 34815.168/t^4)
      + exp (-(t/4)) * (0.3285*t^2 + 0.023*t*log t + 17.84875*t + 2.1545*log t + 295.79 + 8.25/t) := by
  have ht : 0 < t := by linarith
  have hu : 0 ≤ t - 4 := by linarith
  have hu5 : t - 4 ≤ 1 := by linarith
  have b1 : 127.49/4 - (127.49/4^2)*(t-4) ≤ 127.49/t := by
    have hid : (127.49 : ℝ)/t - (127.49/4 - (127.49/4^2)*(t-4))
        = 127.49*(t-4)^2/(t*4^2) := by
      field_simp
      ring
    have hpos : (0:ℝ) ≤ 127.49*(t-4)^2/(t*4^2) := by positivity
    linarith
  have b2 : 1048.947/4^2 - (2*1048.947/4^3)*(t-4) ≤ 1048.947/t^2 := by
    have hid : (1048.947 : ℝ)/t^2 - (1048.947/4^2 - (2*1048.947/4^3)*(t-4))
        = 1048.947*(t-4)^2*(2*t+4)/(t^2*4^3) := by
      field_simp
      ring
    have hpos : (0:ℝ) ≤ 1048.947*(t-4)^2*(2*t+4)/(t^2*4^3) := by positivity
    linarith
  have b3 : 586.82/4^3 - (3*586.82/4^4)*(t-4) ≤ 586.82/t^3 := by
    have hid : (586.82 : ℝ)/t^3 - (586.82/4^3 - (3*586.82/4^4)*(t-4))
        = 586.82*(t-4)^2*(3*t^2+2*t*4+4^2)/(t^3*4^4) := by
      field_simp
      ring
    have hpos : (0:ℝ) ≤ 586.82*(t-4)^2*(3*t^2+2*t*4+4^2)/(t^3*4^4) := by positivity
    linarith
  have b4 : -34815.168/4^4 + (4*34815.168/(5^4*4))*(t-4) ≤ -34815.168/t^4 := by
    have hkey : (1:ℝ)/4^4 - 1/t^4 =
        (t-4)*(t^3+t^2*4+t*4^2+4^3)/(t^4*4^4) := by
      field_simp
      ring
    have hA : 4*4^3 ≤ t^3+t^2*4+t*4^2+4^3 := by nlinarith
    have hB : t^4 ≤ 5^4 := pow_le_pow_left₀ (le_of_lt ht) h2 4
    have hbr : (0:ℝ) ≤ (t^3+t^2*4+t*4^2+4^3)/(t^4*4^4) - 4/(5^4*4) := by
      have key : (t^3+t^2*4+t*4^2+4^3)/(t^4*4^4) - 4/(5^4*4)
          = ((t^3+t^2*4+t*4^2+4^3)*(5^4*4) - 4*(t^4*4^4))
              /((t^4*4^4)*(5^4*4)) := by
        field_simp
      rw [key]
      apply div_nonneg _ (by positivity)
      nlinarith [hA, hB]
    have hfac : (0:ℝ) ≤ 34815.168*(t-4) := by
      have h0 : (0:ℝ) ≤ t - 4 := by linarith
      positivity
    have hmain : (0:ℝ) ≤ 34815.168*(t-4)*((t^3+t^2*4+t*4^2+4^3)/(t^4*4^4)
        - 4/(5^4*4)) := mul_nonneg hfac hbr
    have hid : -34815.168/t^4 - (-34815.168/4^4 + (4*34815.168/(5^4*4))*(t-4))
        = 34815.168*(t-4)*((t^3+t^2*4+t*4^2+4^3)/(t^4*4^4)
              - 4/(5^4*4)) := by
      have e1 : (34815.168:ℝ)*(t-4)*((t^3+t^2*4+t*4^2+4^3)/(t^4*4^4)
              - 4/(5^4*4))
          = 34815.168*((t-4)*(t^3+t^2*4+t*4^2+4^3)/(t^4*4^4))
            - 4*34815.168/(5^4*4)*(t-4) := by
        field_simp
      rw [e1, ← hkey]
      ring
    linarith [hid ▸ hmain]
  have hexp : exp (-(t/4)) = exp (-1) * exp (-(t-4)/4) := by
    rw [← exp_add]
    congr 1
    ring
  have hB : (374:ℝ) ≤ 0.3285*t^2 + 0.023*t*log t + 17.84875*t + 2.1545*log t + 295.79 + 8.25/t := by
    have hlog0 : 0 ≤ log t := log_nonneg (by linarith)
    have ht2 : 0.3285*(4:ℝ)^2 ≤ 0.3285*t^2 := by
      have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 4) h1 2
      nlinarith
    have ht1 : 17.84875*(4:ℝ) ≤ 17.84875*t := by nlinarith
    have hdiv : 8.25/5 ≤ 8.25/t := by
      apply div_le_div_of_nonneg_left (by norm_num) ht h2
    have htlog : 0 ≤ 0.023*t*log t := by positivity
    have hlog2 : 0 ≤ 2.1545*log t := by linarith
    nlinarith
  have hE0 : (0.36:ℝ) ≤ exp (-1) := exp_neg_one_ge
  have h1mu : (0:ℝ) ≤ 1 - (t-4)/4 := by linarith
  have hExpU : 1 - (t-4)/4 ≤ exp (-(t-4)/4) := by
    have := Real.add_one_le_exp (-(t-4)/4)
    linarith
  have hstep1 : 0.36*(1-(t-4)/4) ≤ exp (-1) * exp (-(t-4)/4) :=
    mul_le_mul hE0 hExpU (by linarith) (by positivity)
  have hstep2 : 0.36*(1-(t-4)/4)*374 ≤
      exp (-1) * exp (-(t-4)/4) * (0.3285*t^2 + 0.023*t*log t + 17.84875*t + 2.1545*log t + 295.79 + 8.25/t) := by
    apply mul_le_mul hstep1 hB (by positivity) (by positivity)
  have hblin : 0.36*(1-(t-4)/4)*374 = 134.64 - 33.66*(t-4) := by
    ring
  have b5 : 134.6 - 33.67*(t-4) ≤
      exp (-(t/4)) * (0.3285*t^2 + 0.023*t*log t + 17.84875*t + 2.1545*log t + 295.79 + 8.25/t) := by
    have h1' : 0.36*(1-(t-4)/4)*374 ≤
      exp (-(t/4)) * (0.3285*t^2 + 0.023*t*log t + 17.84875*t + 2.1545*log t + 295.79 + 8.25/t) := by
      rw [hexp]
      exact hstep2
    linarith [h1', hblin, hu]
  have b6 : 0.0825*(4:ℝ) + 6.5065 ≤ 0.0825*t + 6.5065 := by nlinarith
  have hmain : (0.0825*(4:ℝ) + 6.5065) + (127.49/4 - (127.49/4^2)*(t-4))
      + (1048.947/4^2 - (2*1048.947/4^3)*(t-4))
      + (586.82/4^3 - (3*586.82/4^4)*(t-4))
      + (-34815.168/4^4 + (4*34815.168/(5^4*4))*(t-4))
      + (134.6 - 33.67*(t-4))
      ≤ (0.0825*t + 6.5065 + 127.49/t + 1048.947/t^2 + 586.82/t^3 - 34815.168/t^4)
      + exp (-(t/4)) * (0.3285*t^2 + 0.023*t*log t + 17.84875*t + 2.1545*log t + 295.79 + 8.25/t) := by
    linear_combination b1 + b2 + b3 + b4 + b5 + b6
  have hval : (86:ℝ) ≤ (0.0825*(4:ℝ) + 6.5065) + (127.49/4 - (127.49/4^2)*(t-4))
      + (1048.947/4^2 - (2*1048.947/4^3)*(t-4))
      + (586.82/4^3 - (3*586.82/4^4)*(t-4))
      + (-34815.168/4^4 + (4*34815.168/(5^4*4))*(t-4))
      + (134.6 - 33.67*(t-4)) := by
    nlinarith [hu, hu5]
  exact le_trans hval hmain

/-- Region 4: t at least 5. -/
private lemma env_r4 (t : ℝ) (h1 : 5 ≤ t) :
    6.5 ≤ (0.0825*t + 6.5065 + 127.49/t + 1048.947/t^2 + 586.82/t^3 - 34815.168/t^4)
      + exp (-(t/4)) * (0.3285*t^2 + 0.023*t*log t + 17.84875*t + 2.1545*log t + 295.79 + 8.25/t) := by
  have ht : 0 < t := by linarith
  have hexp : 0 ≤ exp (-(t/4)) * (0.3285*t^2 + 0.023*t*log t + 17.84875*t + 2.1545*log t + 295.79 + 8.25/t) := by
    have h1' : (0:ℝ) ≤ 0.3285*t^2 + 0.023*t*log t + 17.84875*t + 2.1545*log t + 295.79 + 8.25/t := by
      have hlog0 : 0 ≤ log t := log_nonneg (by linarith)
      have : (0:ℝ) ≤ 0.023*t*log t := by positivity
      have : (0:ℝ) ≤ 2.1545*log t := by linarith
      have : (0:ℝ) < 8.25/t := by positivity
      nlinarith
    positivity
  have hkey : (0:ℝ) < t^2 := by positivity
  have h4 : 34815.168/t^4 ≤ 34815.168/(25*t^2) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have h25 : (25:ℝ) ≤ t^2 := by nlinarith
    calc (25:ℝ)*t^2 ≤ t^2*t^2 := mul_le_mul_of_nonneg_right h25 (by positivity)
      _ = t^4 := by ring
  have hlin : 0 ≤ 127.49/t - 343.66/t^2 := by
    have h2 : (343.66:ℝ)/t^2 ≤ 127.49/t := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [h1]
    linarith
  have h25 : (25:ℝ) ≤ t^2 := by nlinarith [h1]
  have p1 : (34815.168:ℝ) ≤ 1392.60672*t^2 := by nlinarith [h25]
  have p2 : (0:ℝ) ≤ 0.0825*t^5 + 1392.607*t^2 + 586.82*t - 34815.168 := by
    have h5 : (0:ℝ) < t^5 := pow_pos ht 5
    have h2 : (0:ℝ) ≤ t^2 := by positivity
    nlinarith [p1, h5, h2, ht]
  have hbig : (0.0825*t + 6.5065 + 127.49/t + 1048.947/t^2 + 586.82/t^3 - 34815.168/t^4)
      ≥ 6.5065 + (127.49/t - 343.66/t^2) := by
    rw [ge_iff_le, ← sub_nonneg]
    have hmul : (0.0825*t^5 + 1392.607*t^2 + 586.82*t - 34815.168) =
        ((0.0825*t + 6.5065 + 127.49/t + 1048.947/t^2 + 586.82/t^3 - 34815.168/t^4)
          - (6.5065 + (127.49/t - 343.66/t^2))) * t^4 := by
      field_simp
      ring
    rw [hmul] at p2
    exact nonneg_of_mul_nonneg_left p2 (by positivity : (0:ℝ) < t^4)
  linarith [hbig, hlin, hexp]

/-- The envelope core is nonnegative on the whole ray. -/
private lemma env_core_nonneg (t : ℝ) (ht : 3.218 ≤ t) :
    0 ≤ (0.0825*t + 6.5065 + 127.49/t + 1048.947/t^2 + 586.82/t^3 - 34815.168/t^4)
      + exp (-(t/4)) * (0.3285*t^2 + 0.023*t*log t + 17.84875*t + 2.1545*log t + 295.79 + 8.25/t) := by
  rcases le_total t 3.3 with h | h
  · exact le_trans (by norm_num) (env_r1 t ht h)
  · rcases le_total t 4 with h2 | h2
    · exact le_trans (by norm_num) (env_r2 t h h2)
    · rcases le_total t 5 with h3 | h3
      · exact le_trans (by norm_num) (env_r3 t h2 h3)
      · exact le_trans (by norm_num) (env_r4 t h3)

/-- The derivative of the envelope is nonnegative on the ray. -/
private lemma env_deriv_nonneg (t : ℝ) (ht : 3.218 ≤ t) :
    0 ≤ exp (t/2) * (0.0825*t + 6.5065 + 127.49/t + 1048.947/t^2 + 586.82/t^3 - 34815.168/t^4)
      + exp (t/4) * (0.3285*t^2 + 0.023*t*log t + 17.84875*t + 2.1545*log t + 295.79 + 8.25/t) := by
  have hcore := env_core_nonneg t ht
  have hpos : 0 < exp (t/2) := exp_pos _
  have hm := mul_nonneg hpos.le hcore
  have he1 : exp (t/2) * exp (-(t/4)) = exp (t/4) := by
    rw [← exp_add]
    congr 1
    ring
  have heq : exp (t/2) * ((0.0825*t + 6.5065 + 127.49/t + 1048.947/t^2 + 586.82/t^3 - 34815.168/t^4)
      + exp (-(t/4)) * (0.3285*t^2 + 0.023*t*log t + 17.84875*t + 2.1545*log t + 295.79 + 8.25/t))
      = exp (t/2) * (0.0825*t + 6.5065 + 127.49/t + 1048.947/t^2 + 586.82/t^3 - 34815.168/t^4)
      + exp (t/4) * (0.3285*t^2 + 0.023*t*log t + 17.84875*t + 2.1545*log t + 295.79 + 8.25/t) := by
    rw [mul_add]
    congr 1
    rw [← mul_assoc, he1]
  rwa [heq] at hm

/-- `qG X * sqrt X * log X` written in terms of `u = log X`. -/
private lemma qG_eq_exp (t : ℝ) (ht : 1 < t) :
    qG t * sqrt t * log t
      = exp (log t / 2) * (0.165 * log t + 12.683 + 254.980 / log t + 2607.854 / log t ^ 2 + 11605.056 / log t ^ 3)
        + exp (log t / 4) * (1.314 * log t ^ 2 + 0.092 * log t * log (log t) + 60.883 * log t + 8.250 * log (log t) + 939.260)
        - 237.934 := by
  have ht0 : 0 < t := by linarith
  have hlpos : 0 < log t := log_pos ht
  have hl : log t ≠ 0 := hlpos.ne'
  have h4 : t ^ ((1:ℝ)/4) = exp (log t / 4) := by
    rw [Real.rpow_def_of_pos ht0]; ring_nf
  have h2 : sqrt t = exp (log t / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht0]
    ring_nf
  have hsq : exp (log t / 2) = exp (log t / 4) * exp (log t / 4) := by
    rw [← exp_add]; ring_nf
  have e1 : exp (log t / 4) ≠ 0 := (exp_pos _).ne'
  unfold qG
  rw [h4, h2, hsq]
  field_simp
  ring_nf

private lemma hasDerivAt_h (u : ℝ) (hu : 0 < u) :
    HasDerivAt (fun u : ℝ => 0.165*u + 12.683 + 254.980/u + 2607.854/u^2 + 11605.056/u^3)
      (0.165 - 254.980/u^2 - 2*2607.854/u^3 - 3*11605.056/u^4) u := by
  have hu' : u ≠ 0 := hu.ne'
  have h0 : HasDerivAt (fun u : ℝ => 0.165*u + 12.683) ((0.165:ℝ) * 1) u :=
    ((hasDerivAt_id u).const_mul (0.165:ℝ)).add_const 12.683
  have h1 : HasDerivAt (fun u : ℝ => 254.980/u) ((0 * id u - (254.980:ℝ) * 1) / id u ^ 2) u :=
    HasDerivAt.div (hasDerivAt_const u (254.980:ℝ)) (hasDerivAt_id u) hu'
  have h2 : HasDerivAt (fun u : ℝ => 2607.854/u^2) ((0 * u^2 - (2607.854:ℝ) * (2*u)) / (u^2)^2) u :=
    HasDerivAt.div (hasDerivAt_const u (2607.854:ℝ)) (by simpa using hasDerivAt_pow 2 u) (by positivity)
  have h3 : HasDerivAt (fun u : ℝ => 11605.056/u^3) ((0 * u^3 - (11605.056:ℝ) * (3*u^2)) / (u^3)^2) u :=
    HasDerivAt.div (hasDerivAt_const u (11605.056:ℝ)) (by simpa using hasDerivAt_pow 3 u) (by positivity)
  have hA := ((h0.add h1).add h2).add h3
  convert hA using 1
  simp only [id_eq]
  field_simp
  ring

private lemma hasDerivAt_H (u : ℝ) (hu : 0 < u) :
    HasDerivAt (fun u : ℝ => 1.314*u^2 + 0.092*u*log u + 60.883*u + 8.250*log u + 939.260)
      (2.628*u + 0.092*(log u + 1) + 60.883 + 8.250/u) u := by
  have hu' : u ≠ 0 := hu.ne'
  have hp0 : HasDerivAt (fun u : ℝ => u^2) (2*u) u := by simpa using hasDerivAt_pow 2 u
  have hp : HasDerivAt (fun u : ℝ => 1.314*u^2) ((1.314:ℝ) * (2*u)) u := hp0.const_mul (1.314:ℝ)
  have hm : HasDerivAt (fun u : ℝ => 0.092*u*log u) ((0.092:ℝ) * 1 * log u + (0.092:ℝ)*u * u⁻¹) u := by
    have hi : HasDerivAt (fun u : ℝ => (0.092:ℝ)*u) ((0.092:ℝ) * 1) u := (hasDerivAt_id u).const_mul (0.092:ℝ)
    exact hi.mul (hasDerivAt_log hu')
  have hl : HasDerivAt (fun u : ℝ => 60.883*u) ((60.883:ℝ) * 1) u := (hasDerivAt_id u).const_mul (60.883:ℝ)
  have hlg : HasDerivAt (fun u : ℝ => 8.250*log u) ((8.250:ℝ) * u⁻¹) u := (hasDerivAt_log hu').const_mul (8.250:ℝ)
  have hA := (((hp.add hm).add hl).add hlg).add_const 939.260
  convert hA using 1
  field_simp
  ring

/-- Derivative of the envelope `G` of `qG`: it is `exp (u/2) * P u + exp (u/4) * Q u`. -/
private lemma hasDerivAt_G (u : ℝ) (hu : 0 < u) :
    HasDerivAt (fun u : ℝ => exp (u/2) * (0.165*u + 12.683 + 254.980/u + 2607.854/u^2 + 11605.056/u^3)
      + exp (u/4) * (1.314*u^2 + 0.092*u*log u + 60.883*u + 8.250*log u + 939.260) - 237.934)
      (exp (u/2) * (0.0825*u + 6.5065 + 127.49/u + 1048.947/u^2 + 586.82/u^3 - 34815.168/u^4)
       + exp (u/4) * (0.3285*u^2 + 0.023*u*log u + 17.84875*u + 2.1545*log u + 295.79 + 8.25/u)) u := by
  have hh := hasDerivAt_h u hu
  have hH := hasDerivAt_H u hu
  have hid : HasDerivAt (fun u : ℝ => u) 1 u := hasDerivAt_id u
  have hc2 : HasDerivAt (fun u : ℝ => u/2) (1/2) u := by
    have := hid.div_const 2
    simpa using this
  have hc4 : HasDerivAt (fun u : ℝ => u/4) (1/4) u := by
    have := hid.div_const 4
    simpa using this
  have he2 : HasDerivAt (fun u : ℝ => exp (u/2)) (exp (u/2) * (1/2)) u := by
    have h := (Real.hasDerivAt_exp (u/2)).comp u hc2
    convert h using 1
    all_goals first | (funext x; rfl) | norm_num | ring
  have he4 : HasDerivAt (fun u : ℝ => exp (u/4)) (exp (u/4) * (1/4)) u := by
    have h := (Real.hasDerivAt_exp (u/4)).comp u hc4
    convert h using 1
    all_goals first | (funext x; rfl) | norm_num | ring
  have hA := (he2.mul hh).add (he4.mul hH)
  have hB := hA.sub_const 237.934
  convert hB using 1
  have hu' : u ≠ 0 := hu.ne'
  field_simp
  ring

/-- LEAF. Journal p. 1224, the last scalar comparison before display 13.
The whole error envelope increases on this ray. Antitonicity of qG alone is insufficient. -/
theorem error_envelope_mono (Y Z : ℝ) (hZ : 25 ≤ Z) (hZY : Z < Y) :
    qG Z * √Z * log Z ≤ qG Y * √Y * log Y := by
  have hZ1 : (1:ℝ) < Z := by linarith
  have hY1 : (1:ℝ) < Y := by linarith
  have hlogZ : 3.218 ≤ log Z := le_trans log_25_ge (log_le_log (by norm_num) hZ)
  have hlogZ0 : 0 < log Z := by linarith
  have hlt : log Z < log Y := log_lt_log (by linarith) hZY
  have hcont : ContinuousOn (fun t : ℝ => exp (t/2) * (0.165*t + 12.683 + 254.980/t + 2607.854/t^2 + 11605.056/t^3)
      + exp (t/4) * (1.314*t^2 + 0.092*t*log t + 60.883*t + 8.250*log t + 939.260) - 237.934) (Set.Icc (log Z) (log Y)) := by
    intro x hx
    exact ((hasDerivAt_G x (by linarith [hx.1])).continuousAt).continuousWithinAt
  have hdiff : DifferentiableOn ℝ (fun t : ℝ => exp (t/2) * (0.165*t + 12.683 + 254.980/t + 2607.854/t^2 + 11605.056/t^3)
      + exp (t/4) * (1.314*t^2 + 0.092*t*log t + 60.883*t + 8.250*log t + 939.260) - 237.934) (Set.Ioo (log Z) (log Y)) := by
    intro x hx
    exact ((hasDerivAt_G x (by linarith [hx.1])).differentiableAt).differentiableWithinAt
  obtain ⟨c, hc, hcd⟩ := exists_deriv_eq_slope (fun t : ℝ => exp (t/2) * (0.165*t + 12.683 + 254.980/t + 2607.854/t^2 + 11605.056/t^3)
      + exp (t/4) * (1.314*t^2 + 0.092*t*log t + 60.883*t + 8.250*log t + 939.260) - 237.934) hlt hcont hdiff
  have hc0 : 0 < c := by linarith [hc.1]
  have hc3 : 3.218 ≤ c := by linarith [hc.1]
  have hderivc : deriv (fun t : ℝ => exp (t/2) * (0.165*t + 12.683 + 254.980/t + 2607.854/t^2 + 11605.056/t^3)
      + exp (t/4) * (1.314*t^2 + 0.092*t*log t + 60.883*t + 8.250*log t + 939.260) - 237.934) c =
      exp (c/2) * (0.0825*c + 6.5065 + 127.49/c + 1048.947/c^2 + 586.82/c^3 - 34815.168/c^4) + exp (c/4) * (0.3285*c^2 + 0.023*c*log (c) + 17.84875*c + 2.1545*log (c) + 295.79 + 8.25/c) :=
    (hasDerivAt_G c hc0).deriv
  have hslope : 0 ≤ (exp (log Y/2) * (0.165*log Y + 12.683 + 254.980/log Y + 2607.854/log Y^2 + 11605.056/log Y^3)
      + exp (log Y/4) * (1.314*log Y^2 + 0.092*log Y*log (log Y) + 60.883*log Y + 8.250*log (log Y) + 939.260) - 237.934 - (exp (log Z/2) * (0.165*log Z + 12.683 + 254.980/log Z + 2607.854/log Z^2 + 11605.056/log Z^3)
      + exp (log Z/4) * (1.314*log Z^2 + 0.092*log Z*log (log Z) + 60.883*log Z + 8.250*log (log Z) + 939.260) - 237.934)) / (log Y - log Z) := by
    rw [← hcd, hderivc]
    exact env_deriv_nonneg c hc3
  have hpos : 0 < log Y - log Z := by linarith
  have hnn : 0 ≤ exp (log Y/2) * (0.165*log Y + 12.683 + 254.980/log Y + 2607.854/log Y^2 + 11605.056/log Y^3)
      + exp (log Y/4) * (1.314*log Y^2 + 0.092*log Y*log (log Y) + 60.883*log Y + 8.250*log (log Y) + 939.260) - 237.934 - (exp (log Z/2) * (0.165*log Z + 12.683 + 254.980/log Z + 2607.854/log Z^2 + 11605.056/log Z^3)
      + exp (log Z/4) * (1.314*log Z^2 + 0.092*log Z*log (log Z) + 60.883*log Z + 8.250*log (log Z) + 939.260) - 237.934) := by
    have hm := mul_nonneg hslope hpos.le
    rwa [div_mul_cancel₀ _ hpos.ne'] at hm
  rw [qG_eq_exp Z hZ1, qG_eq_exp Y hY1]
  linarith [hnn]


/-- Exact statement of Decomp148b.prime_character_bound from the three smaller steps.
CONDITIONAL ON prefix_bound, interval_boundary and error_envelope_mono. -/
theorem prime_character_bound (hG : GRH) (Y Z : ℝ) (r : ℕ)
    (hZ : 25 ≤ Z) (hZY : Z < Y) (hr : 3 ≤ r) (hrZ : (r : ℝ) ≤ √Z)
    (χ : DirichletCharacter ℂ r) (hχ : χ ≠ 1) :
    ‖∑ p ∈ pRange Y Z, χ p‖ ≤ 2 * r.totient * (1 + qG Y * √Y * log Y) := by
  have hy : 25 ≤ Y := hZ.trans hZY.le
  have hY := prefix_bound hG Y r hy hr (hrZ.trans (sqrt_le_sqrt hZY.le)) χ hχ
  have hZ' := prefix_bound hG Z r hZ hr hrZ χ hχ
  have hm := error_envelope_mono Y Z hZ hZY
  have he := interval_boundary Y Z r hZ hZY χ
  have ht := norm_sub_le (primePrefix Y χ) (primePrefix Z χ)
  have hi := norm_add_le
    ((∑ p ∈ pRange Y Z, χ p) - (primePrefix Y χ - primePrefix Z χ))
    (primePrefix Y χ - primePrefix Z χ)
  rw [sub_add_cancel] at hi
  have hφ : (1 : ℝ) ≤ r.totient := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < r)
  have hm' := mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ r.totient)
  calc
    _ ≤ 2 + r.totient * (qG Y * √Y * log Y) +
        r.totient * (qG Z * √Z * log Z) := by linarith
    _ ≤ 2 * r.totient * (1 + qG Y * √Y * log Y) := by nlinarith

end
end LeanLab.BS2022GRH.Decomp374b

#print axioms LeanLab.BS2022GRH.Decomp374b.prefix_bound
#print axioms LeanLab.BS2022GRH.Decomp374b.interval_boundary
#print axioms LeanLab.BS2022GRH.Decomp374b.error_envelope_mono
#print axioms LeanLab.BS2022GRH.Decomp374b.prime_character_bound
