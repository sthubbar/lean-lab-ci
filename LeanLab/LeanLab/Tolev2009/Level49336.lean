/-
AI wrote this Lean code. Codex task336.
Binary Goldbach is open.
Source context: Tolev 2009 pages 2 to 3, the four ninths level remark.
The Type I scalar component follows from Tolev 1999 page 86 display 65.
This does not prove the full well factorable extension or its Type II input.
-/
import LeanLab.Tolev2009.Decomp336b
import LeanLab.Tolev2009.WellFactorable

open Finset Real
namespace LeanLab.Tolev2009.Level49336
open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.Dyadic LeanLab.Tolev2009.Decomp286b
open LeanLab.Tolev2009.Decomp336a LeanLab.Tolev2009.WellFactorable
open LeanLab.Tolev2009.Decomp310a

/-- The extended cutoff contains the original third cutoff. -/
theorem cutoff3_le_level49 (B : ℝ) (N : ℕ) (hN : (1:ℝ) ≤ N) :
    cutoff3 B N ≤ ⌊level49 B N⌋₊ := by
  unfold cutoff3 level49
  apply Nat.floor_mono
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (Real.log_natCast_nonneg N) _)
  exact Real.rpow_le_rpow_of_exponent_le hN (by norm_num)

/-- The same Type I product cutoff bound at the extended four ninths level. -/
theorem shell_product_bound (A : ℝ) (N : ℕ) (x M H : ℝ)
    (hA : 10000 ≤ A) (hN : (1 : ℝ) ≤ N) (hL : 2 ≤ Real.log N)
    (hx : 0 < x) (hxN : x ≤ N) (hM : 0 < M) (hH : 0 < H)
    (hMH : M*H ≤ 2*x) (hHlo : x^((249:ℝ)/500) ≤ H) :
    let T := ⌊2*M⌋₊ * ⌊level49 (10000*A) N⌋₊
    (T : ℝ) ≤ 4*N*Real.log N^(-10000*A) ∧
    (T : ℝ) ≤ N ∧
    (T : ℝ) ≤ 4*N*Real.log N^(-20*A) := by
  dsimp only
  have hN0 : (0 : ℝ) < N := by linarith
  have hL0 : 0 < Real.log N := by linarith
  have hp : 0 < x^((249:ℝ)/500) := Real.rpow_pos_of_pos hx _
  have hmp : M*x^((249:ℝ)/500) ≤ 2*x :=
    (mul_le_mul_of_nonneg_left hHlo hM.le).trans hMH
  have hm : M ≤ 2*x^((251:ℝ)/500) := by
    have hh : M ≤ 2*x / x^((249:ℝ)/500) := (le_div_iff₀ hp).mpr hmp
    convert hh using 1
    rw [mul_div_assoc]
    congr 1
    simpa only [show (1:ℝ)-(249:ℝ)/500 = (251:ℝ)/500 by norm_num, Real.rpow_one] using Real.rpow_sub hx 1 ((249:ℝ)/500)
  have hmN : M ≤ 2*(N:ℝ)^((251:ℝ)/500) :=
    hm.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx.le hxN (by norm_num)) (by norm_num))
  have hf : (⌊2*M⌋₊ : ℝ) ≤ 2*M := Nat.floor_le (by positivity)
  have hk : (⌊level49 (10000*A) N⌋₊ : ℝ) ≤ (N:ℝ)^((4:ℝ)/9)*Real.log N^(-10000*A) :=
    by
      unfold level49
      have hh := Nat.floor_le (show 0 ≤ (N:ℝ)^((4:ℝ)/9)*Real.log N^(-(10000*A)) by positivity)
      simpa only [neg_mul] using hh
  have hfirst : ((⌊2*M⌋₊ * ⌊level49 (10000*A) N⌋₊ : ℕ) : ℝ) ≤
      4*(N:ℝ)*Real.log N^(-10000*A) := by
    push_cast
    calc
      _ ≤ (2*M)*((N:ℝ)^((4:ℝ)/9)*Real.log N^(-10000*A)) :=
        mul_le_mul hf hk (Nat.cast_nonneg _) (by positivity)
      _ ≤ (2*(2*(N:ℝ)^((251:ℝ)/500)))*((N:ℝ)^((4:ℝ)/9)*Real.log N^(-10000*A)) := by
        gcongr
      _ = 4*(N:ℝ)^((4259:ℝ)/4500)*Real.log N^(-10000*A) := by
        rw [show (4259:ℝ)/4500 = (251:ℝ)/500 + 4/9 by norm_num, Real.rpow_add hN0]
        ring
      _ ≤ _ := by
        have hh : (N:ℝ)^((4259:ℝ)/4500) ≤ N := by
          convert Real.rpow_le_rpow_of_exponent_le hN (show (4259:ℝ)/4500 ≤ 1 by norm_num) using 1 <;> simp
        gcongr
  have hs : Real.log N^(-10000*A) ≤ (1:ℝ)/4 := by
    calc
      _ ≤ Real.log N^(-2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith)
      _ ≤ (2:ℝ)^(-2:ℝ) := Real.rpow_le_rpow_of_nonpos (by norm_num) hL (by norm_num)
      _ = 1/4 := by norm_num
  refine ⟨hfirst, ?_, ?_⟩
  · calc
      _ ≤ 4*(N:ℝ)*Real.log N^(-10000*A) := hfirst
      _ ≤ 4*(N:ℝ)*(1/4) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by ring
  · apply hfirst.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by nlinarith)

/-- The scalar Type I phase estimate at level four ninths needs no factorability input. -/
theorem phase_average :
    ∀ A : ℝ, 10 ^ 4 ≤ A →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ α ∈ Set.Ioo (-1 / τof A N) (1 - 1 / τof A N),
          α ∉ majorArcs (Qof A N) (τof A N) →
        ∀ x M H : ℝ,
          (N : ℝ) * Real.log N ^ (-4 * A) ≤ x → x ≤ N → 2 < x →
          0 < M → 0 < H → x / 4 ≤ M * H → M * H ≤ 2 * x →
          x ^ ((249 : ℝ) / 500) ≤ H →
          ∑ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, (tau5 m : ℝ) *
            ∑ k ∈ Icc 1 (⌊level49 (10 ^ 4 * A) N⌋₊), phaseCap α x (m * k) ≤
              C * N * Real.log N ^ (328 - 4 * A) := by
  intro A hA
  obtain ⟨N₀, hN₀⟩ := eventual_minor_arc_parameters A (by linarith)
  refine ⟨(2 : ℝ)^30, N₀, by positivity, ?_⟩
  intro N hodd hNN α hα hminor x M H hxlo hxN hx hM hH hprodlo hprodhi hsize
  obtain ⟨hL, hτ⟩ := hN₀ N hNN
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hQ : 0 ≤ Qof A N := Real.rpow_nonneg (Real.log_natCast_nonneg _) _
  obtain ⟨a, q, hq, hqQ, hqτ, hcop, herr, herr2⟩ :=
    minor_arc_reduced_approximation (Qof A N) (τof A N) α hQ hτ
      (by linarith) hα hminor
  have hprod := shell_product_bound A N x M H (by norm_num at hA ⊢; exact hA)
    hN1 hL (by linarith) hxN hM hH hprodhi hsize
  have hTN : ⌊2*M⌋₊ * ⌊level49 (10000*A) N⌋₊ ≤ N := by exact_mod_cast hprod.2.1
  have hmass := phase_mass_from_approx A N (⌊2*M⌋₊ * ⌊level49 (10000*A) N⌋₊) q a α x
    (by linarith) hNpos hL (by linarith) hxN hTN hprod.2.2 hq hqQ hqτ hcop herr2
  have hres := rectangle_phase_of_mass A N α x ⌊M⌋₊ ⌊2*M⌋₊ (⌊level49 (10000*A) N⌋₊)
    (by norm_num at hA ⊢; exact hA) (by exact_mod_cast hNpos) hL
    (by linarith) hxN hTN hmass
  norm_num only [show (10 : ℝ)^4 = 10000 by norm_num] at *
  exact hres

/-- The constant row estimate at the extended four ninths cutoff.
The scalar phase average is proved with clean axioms. -/
theorem constant_rows :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ α ∈ Set.Ioo (-1 / τof A N) (1 - 1 / τof A N), α ∉ majorArcs (Qof A N) (τof A N) →
        ∀ x M M₁ H H₁ : ℝ,
          (N : ℝ) * Real.log N ^ (-4 * A) ≤ x → x ≤ N → 2 < x →
          0 < M → M ≤ M₁ → M₁ ≤ 2 * M →
          0 < H → H ≤ H₁ → H₁ ≤ 2 * H → x / 4 ≤ M * H → M * H ≤ 2 * x →
          x ^ ((249 : ℝ) / 500) ≤ H →
          ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊,
            ((tau5 m : ℝ) * Real.log N) *
              ‖row lam l₃ (⌊level49 (10 ^ 4 * A) N⌋₊) N α x H H₁ (fun _ => 1) m‖ ≤
                C * N * Real.log N ^ (330 - 4 * A) := by
  intro A hA l₃ hl₃
  obtain ⟨C, N₀, hC, hav⟩ := phase_average A hA
  refine ⟨C, max N₀ 3, hC, ?_⟩
  intro N hodd hN lam hlam α hα hminor x M M₁ H H₁
    hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hsize
  have hL : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by have := (le_max_right N₀ 3).trans hN; linarith)]
    exact Real.exp_one_lt_d9.le.trans (by have := (le_max_right N₀ 3).trans hN; linarith)
  have hL0 : 0 < Real.log N := by linarith
  let P : ℕ → ℝ := fun m => ∑ k ∈ Icc 1 (⌊level49 (10 ^ 4 * A) N⌋₊), phaseCap α x (m * k)
  have hP : ∀ m, 0 ≤ P m := fun m => sum_nonneg (fun k hk => phaseCap_nonneg α x (m * k) (by linarith))
  have hr : ∀ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊,
      ‖row lam l₃ (⌊level49 (10 ^ 4 * A) N⌋₊) N α x H H₁ (fun _ => 1) m‖ ≤ P m := by
    intro m hm
    apply row_norm_le_phase lam l₃ _ N m α x H H₁ hlam
      (by have := (mem_Ioc.mp hm).1; omega) (by linarith)
    intro k hk hc
    exact progression_bound l₃ k N m α x H H₁ (mem_Icc.mp hk).1
      (by have := (mem_Ioc.mp hm).1; omega) hc (by linarith)
  have hav' := hav N hodd ((le_max_left _ _).trans hN) α hα hminor x M H
    hxlo hxhi hx hM hH hprodlo hprodhi hsize
  have hsub : Ioc ⌊M⌋₊ ⌊M₁⌋₊ ⊆ Ioc ⌊M⌋₊ ⌊2 * M⌋₊ :=
    Ioc_subset_Ioc le_rfl (Nat.floor_mono hM₁)
  calc
    _ ≤ Real.log N * ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, (tau5 m : ℝ) * P m := by
      rw [mul_sum]
      apply sum_le_sum
      intro m hm
      have ht := mul_le_mul_of_nonneg_left (hr m hm)
        (show 0 ≤ (tau5 m : ℝ) * Real.log N by positivity)
      nlinarith
    _ ≤ Real.log N * ∑ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, (tau5 m : ℝ) * P m :=
      mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hsub (fun m hm hn => mul_nonneg (Nat.cast_nonneg _) (hP m))) hL0.le
    _ ≤ Real.log N * (C * N * Real.log N ^ (328 - 4 * A)) :=
      mul_le_mul_of_nonneg_left hav' hL0.le
    _ = C * N * Real.log N ^ (329 - 4 * A) := by
      rw [show (329 - 4 * A) = (1 : ℝ) + (328 - 4 * A) by ring,
        Real.rpow_add hL0, Real.rpow_one]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL (by linarith)) (by positivity)

/-- The logarithmic row estimate at the extended four ninths cutoff.
The scalar phase average is proved with clean axioms. -/
theorem logarithmic_rows :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ α ∈ Set.Ioo (-1 / τof A N) (1 - 1 / τof A N), α ∉ majorArcs (Qof A N) (τof A N) →
        ∀ x M M₁ H H₁ : ℝ,
          (N : ℝ) * Real.log N ^ (-4 * A) ≤ x → x ≤ N → 2 < x →
          0 < M → M ≤ M₁ → M₁ ≤ 2 * M →
          0 < H → H ≤ H₁ → H₁ ≤ 2 * H → x / 4 ≤ M * H → M * H ≤ 2 * x →
          x ^ ((249 : ℝ) / 500) ≤ H →
          ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊,
            ((tau5 m : ℝ) * Real.log N) *
              ‖row lam l₃ (⌊level49 (10 ^ 4 * A) N⌋₊) N α x H H₁ (fun l : ℕ => (Real.log l : ℂ)) m‖ ≤
                C * N * Real.log N ^ (330 - 4 * A) := by
  intro A hA l₃ hl₃
  obtain ⟨C, N₀, hC, hav⟩ := phase_average A hA
  refine ⟨8 * C, max N₀ 3, by positivity, ?_⟩
  intro N hodd hN lam hlam α hα hminor x M M₁ H H₁
    hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hsize
  have hN3 : (3 : ℝ) ≤ N := (le_max_right _ _).trans hN
  have hL : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  have hL0 : 0 < Real.log N := by linarith
  let P : ℕ → ℝ := fun m => ∑ k ∈ Icc 1 (⌊level49 (10 ^ 4 * A) N⌋₊), phaseCap α x (m * k)
  have hP : ∀ m, 0 ≤ P m := fun m => sum_nonneg (fun k hk => phaseCap_nonneg α x (m * k) (by linarith))
  have hav' := hav N hodd ((le_max_left _ _).trans hN) α hα hminor x M H
    hxlo hxhi hx hM hH hprodlo hprodhi hsize
  have hsub : Ioc ⌊M⌋₊ ⌊M₁⌋₊ ⊆ Ioc ⌊M⌋₊ ⌊2 * M⌋₊ :=
    Ioc_subset_Ioc le_rfl (Nat.floor_mono hM₁)
  calc
    _ ≤ (8 * Real.log N ^ 2) * ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, (tau5 m : ℝ) * P m := by
      rw [mul_sum]
      apply sum_le_sum
      intro m hm
      have ht := mul_le_mul_of_nonneg_left
        (logarithmic_row_norm_le_phase lam l₃ (⌊level49 (10 ^ 4 * A) N⌋₊) N m α x M M₁ H H₁ hlam
          hN3 (by linarith) hxhi hM hM₁ hH hHH₁ hH₁ hprodhi hm)
        (show 0 ≤ (tau5 m : ℝ) * Real.log N by positivity)
      nlinarith
    _ ≤ (8 * Real.log N ^ 2) * ∑ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, (tau5 m : ℝ) * P m :=
      mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hsub (fun m hm hn => mul_nonneg (Nat.cast_nonneg _) (hP m))) (by positivity)
    _ ≤ (8 * Real.log N ^ 2) * (C * N * Real.log N ^ (328 - 4 * A)) :=
      mul_le_mul_of_nonneg_left hav' (by positivity)
    _ = _ := by
      rw [show (330 - 4 * A) = (2 : ℝ) + (328 - 4 * A) by ring,
        Real.rpow_add hL0, Real.rpow_two]
      ring

/-- The Type I estimate at level four ninths from the two row cases.
No cited analytic input is retained. The original parent file remains unchanged. -/
theorem typeI_estimate :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ α ∈ Set.Ioo (-1 / τof A N) (1 - 1 / τof A N), α ∉ majorArcs (Qof A N) (τof A N) →
        ∀ x M M₁ H H₁ : ℝ,
          (N : ℝ) * Real.log N ^ (-4 * A) ≤ x → x ≤ N → 2 < x →
          0 < M → M ≤ M₁ → M₁ ≤ 2 * M →
          0 < H → H ≤ H₁ → H₁ ≤ 2 * H → x / 4 ≤ M * H → M * H ≤ 2 * x →
          x ^ ((249 : ℝ) / 500) ≤ H →
          ∀ a b : ℕ → ℂ,
            (∀ m, ‖a m‖ ≤ (tau5 m : ℝ) * Real.log N) →
            (b = (fun _ => 1) ∨ b = (fun l : ℕ => (Real.log l : ℂ))) →
            ‖bilinear lam l₃ (⌊level49 (10 ^ 4 * A) N⌋₊) N α x M M₁ H H₁ a b‖ ≤
              C * N * Real.log N ^ (330 - 4 * A) := by
  intro A hA l₃ hl₃
  obtain ⟨C₁, N₁, hC₁, h₁⟩ := LeanLab.Tolev2009.Level49336.constant_rows A hA l₃ hl₃
  obtain ⟨C₂, N₂, hC₂, h₂⟩ := LeanLab.Tolev2009.Level49336.logarithmic_rows A hA l₃ hl₃
  refine ⟨C₁ + C₂, max N₁ N₂, add_nonneg hC₁ hC₂, ?_⟩
  intro N hodd hN lam hlam α hα hminor x M M₁ H H₁
    hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hsize a b ha hb
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans hN
  have hN₂ : N₂ ≤ N := (le_max_right _ _).trans hN
  apply (bilinear_norm_le_rows lam l₃ _ N α x M M₁ H H₁ a b ha).trans
  rcases hb with rfl | rfl
  · apply (h₁ N hodd hN₁ lam hlam α hα hminor x M M₁ H H₁
      hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hsize).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC₂) (Nat.cast_nonneg N))
      (Real.rpow_nonneg (Real.log_natCast_nonneg N) _)
  · apply (h₂ N hodd hN₂ lam hlam α hα hminor x M M₁ H H₁
      hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hsize).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₁) (Nat.cast_nonneg N))
      (Real.rpow_nonneg (Real.log_natCast_nonneg N) _)

end LeanLab.Tolev2009.Level49336
