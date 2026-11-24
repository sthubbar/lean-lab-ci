/-
MMS https://arxiv.org/abs/1610.02017v2, pages 11 and 12.
Feed 1122 split of harman_fourier_reference_input in Decomp420d.
The page 12 unsmoothing argument: a smoothed Fourier estimate from Proposition 5.1,
a sieve upper bound for the two edge pieces, and an elementary edge count.
The bound on the reference mean is taken from the Decomp571b limit leaves.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp420d
import LeanLab.Ternary.Decomp571b

namespace LeanLab.Ternary.MMS.Task420
open Finset

/-- The smooth cutoff g of MMS page 12 second paragraph, transported to the
interval x minus x to the theta over three, x plus x to the theta of Hyp1.
It vanishes off that interval, equals one at distance at least eps x to the theta
from both ends, and its j th derivative is of size at most a constant
depending on eps and j times x to the minus j theta. Built from Mathlib
smoothTransition. This particular profile is our choice of the paper g. -/
noncomputable def edgeCutoff (ε θ x t : ℝ) : ℝ :=
  Real.smoothTransition ((t - (x - x ^ θ / 3)) / (ε * x ^ θ)) *
    Real.smoothTransition ((x + x ^ θ - t) / (ε * x ^ θ))

/-- The cutoff is nonnegative. Derived from Mathlib smoothTransition.nonneg. -/
theorem edgeCutoff_nonneg (ε θ x t : ℝ) : 0 ≤ edgeCutoff ε θ x t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

/-- The cutoff is at most one. Derived from Mathlib smoothTransition.le_one. -/
theorem edgeCutoff_le_one (ε θ x t : ℝ) : edgeCutoff ε θ x t ≤ 1 := by
  unfold edgeCutoff
  have h1 := Real.smoothTransition.le_one ((t - (x - x ^ θ / 3)) / (ε * x ^ θ))
  have h2 := Real.smoothTransition.le_one ((x + x ^ θ - t) / (ε * x ^ θ))
  have h3 := Real.smoothTransition.nonneg ((x + x ^ θ - t) / (ε * x ^ θ))
  nlinarith [Real.smoothTransition.nonneg ((t - (x - x ^ θ / 3)) / (ε * x ^ θ))]

/-- Proved step toward edge_sieve_upper, MMS page 12 second paragraph: the weight
one minus g vanishes at distance at least eps x to the theta from both ends, so only
the two edge pieces carry the sieve sum. From Mathlib smoothTransition.one_of_one_le. -/
theorem one_sub_edgeCutoff_eq_zero_of_inner (ε θ x t : ℝ) (hw : 0 < ε * x ^ θ)
    (h1 : ε * x ^ θ ≤ t - (x - x ^ θ / 3)) (h2 : ε * x ^ θ ≤ x + x ^ θ - t) :
    1 - edgeCutoff ε θ x t = 0 := by
  unfold edgeCutoff
  rw [Real.smoothTransition.one_of_one_le ((one_le_div hw).mpr h1),
    Real.smoothTransition.one_of_one_le ((one_le_div hw).mpr h2)]
  ring

/-- Proved step toward edge_sieve_upper, MMS page 12 second paragraph: the edge
weight one minus g lies between zero and one, so the edge sum is at most the
plain sieve sum over the two edge pieces. From edgeCutoff_nonneg and edgeCutoff_le_one. -/
theorem one_sub_edgeCutoff_mem_Icc (ε θ x t : ℝ) :
    0 ≤ 1 - edgeCutoff ε θ x t ∧ 1 - edgeCutoff ε θ x t ≤ 1 :=
  ⟨sub_nonneg.mpr (edgeCutoff_le_one ε θ x t),
    sub_le_self _ (edgeCutoff_nonneg ε θ x t)⟩

/-- LEAF: MMS page 12 second paragraph, the smoothed display obtained from
Proposition 5.1 of page 11 with d equal to W, together with the two cases q at least
log to the 5A and q below it, applied before unsmoothing. Class HARD for Codex.
Proposition 5.1 itself is proved in sections 5.1 to 5.3, pages 13 to 27.
The normalized long mean on the right is the paper ratio of the g1 weighted sum to
the zero Fourier coefficient of g1, multiplied by log x, so no limit is taken here. -/
theorem smoothed_fourier_reference (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ c : ℕ, Nat.Coprime c (wheel x) → ∀ γ : ℝ,
        ‖∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]),
            ((Task361.harmanMajorant x n * edgeCutoff ε θ x n : ℝ) : ℂ) * e (n * γ) -
          ((Task379.referenceMean x / Real.log x * (wheel x / (wheel x).totient) : ℝ) : ℂ) *
          ∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]),
            ((edgeCutoff ε θ x n : ℝ) : ℂ) * e (n * γ)‖ ≤
          η * x ^ θ / ((wheel x).totient * Real.log x) := by
  sorry

/-- LEAF: MMS page 12 second paragraph, the simple sieve upper bound showing that
the two edge pieces of length eps x to the theta contribute
O of eps x to the theta over phi W log x, uniformly in eps. Class MEDIUM for Open Math OS.
It needs an upper bound sieve for x to the quarter rough numbers and for the ordered
prime triple term of equation 5.1 in short intervals and in classes modulo W. -/
theorem edge_sieve_upper (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ c : ℕ, Nat.Coprime c (wheel x) →
        ∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]),
            Task361.harmanMajorant x n * (1 - edgeCutoff ε θ x n) ≤
          C * ε * x ^ θ / ((wheel x).totient * Real.log x) := by
  sorry

/-- Proved leaf, MMS page 12 second paragraph, replacing g by one in the main term.
The weight one minus g lives on two intervals of length eps x to the theta, and each
meets one class modulo W in at most eps x to the theta over W plus one integers.
Originally class EASY, now proved. -/
theorem edge_count_bound (θ : ℝ) (hθ : 0 < θ) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ c : ℕ, ∀ γ : ℝ,
      (wheel x : ℝ) *
        ‖∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]),
          ((1 - edgeCutoff ε θ x n : ℝ) : ℂ) * e (n * γ)‖ ≤ 8 * ε * x ^ θ := by
  intro ε hε hε1
  have hsmall := (isLittleO_log_rpow_atTop hθ).bound hε
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp
    (hsmall.and (Filter.eventually_ge_atTop (Real.exp 1)))
  refine ⟨X₀, fun x hx c γ => ?_⟩
  obtain ⟨hlog, hxe⟩ := hX₀ x hx
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hxe
  have hxθ : 0 < x ^ θ := Real.rpow_pos_of_pos hx0 _
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith [Real.add_one_le_exp (1 : ℝ)])
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlx, abs_of_pos hxθ] at hlog
  have hWlog := wheel_le_log hxe
  have hW1 : (1 : ℝ) ≤ wheel x := by exact_mod_cast wheel_pos x
  set δ := ε * x ^ θ with hδ
  have hδ0 : 0 < δ := mul_pos hε hxθ
  have hWδ : (wheel x : ℝ) ≤ δ := hWlog.trans hlog
  set S := (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]) with hS
  set S₁ := S.filter (fun n : ℕ => (n : ℝ) < x - x ^ θ / 3 + δ)
  set S₂ := S.filter (fun n : ℕ => x + x ^ θ - δ < (n : ℝ))
  have hmem : ∀ n ∈ S, x - x ^ θ / 3 ≤ n ∧ (n : ℝ) ≤ x + x ^ θ := by
    intro n hn
    obtain ⟨hlo, hhi⟩ := mem_Icc.mp (mem_filter.mp hn).1
    exact ⟨(Nat.le_ceil _).trans (by exact_mod_cast hlo),
      (show (n : ℝ) ≤ (⌊x + x ^ θ⌋₊ : ℝ) by exact_mod_cast hhi).trans
        (Nat.floor_le (by linarith))⟩
  have hcong : ∀ T ⊆ S, ∀ m ∈ T, ∀ m' ∈ T, (m : ℤ) ≡ (m' : ℤ) [ZMOD (wheel x)] := by
    intro T hT m hm m' hm'
    have h1 := (mem_filter.mp (hT hm)).2
    have h2 := (mem_filter.mp (hT hm')).2
    exact Int.natCast_modEq_iff.mpr (h1.trans h2.symm)
  have hc₁ : (S₁.card : ℝ) ≤ (δ + 1) / wheel x + 1 := by
    apply LeanLab.Halupczok2012.card_cong_le (x := x - x ^ θ / 3 - 1) (wheel_pos x)
      (by linarith) _ (hcong S₁ (filter_subset _ _))
    intro m hm
    obtain ⟨hmS, hm1⟩ := mem_filter.mp hm
    have := hmem m hmS
    constructor <;> linarith
  have hc₂ : (S₂.card : ℝ) ≤ δ / wheel x + 1 := by
    apply LeanLab.Halupczok2012.card_cong_le (x := x + x ^ θ - δ) (wheel_pos x)
      hδ0.le _ (hcong S₂ (filter_subset _ _))
    intro m hm
    obtain ⟨hmS, hm1⟩ := mem_filter.mp hm
    have := hmem m hmS
    constructor <;> linarith
  have hpt : ∀ n ∈ S, 1 - edgeCutoff ε θ x n ≤
      (if (n : ℝ) < x - x ^ θ / 3 + δ then 1 else 0) +
        (if x + x ^ θ - δ < (n : ℝ) then 1 else 0) := by
    intro n hn
    have hg0 := edgeCutoff_nonneg ε θ x n
    split_ifs with h1 h2 h2
    · linarith
    · linarith
    · linarith
    · push_neg at h1 h2
      have e1 : 1 ≤ ((n : ℝ) - (x - x ^ θ / 3)) / (ε * x ^ θ) :=
        (one_le_div hδ0).mpr (by linarith)
      have e2 : 1 ≤ (x + x ^ θ - (n : ℝ)) / (ε * x ^ θ) :=
        (one_le_div hδ0).mpr (by linarith)
      unfold edgeCutoff
      rw [Real.smoothTransition.one_of_one_le e1, Real.smoothTransition.one_of_one_le e2]
      norm_num
  have hnorm : ‖∑ n ∈ S, ((1 - edgeCutoff ε θ x n : ℝ) : ℂ) * e (n * γ)‖ ≤
      (S₁.card : ℝ) + S₂.card := by
    apply (norm_sum_le _ _).trans
    have hle : ∑ n ∈ S, ‖((1 - edgeCutoff ε θ x n : ℝ) : ℂ) * e (n * γ)‖ ≤
        ∑ n ∈ S, ((if (n : ℝ) < x - x ^ θ / 3 + δ then (1 : ℝ) else 0) +
          (if x + x ^ θ - δ < (n : ℝ) then 1 else 0)) := by
      apply sum_le_sum
      intro n hn
      rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [edgeCutoff_le_one ε θ x n])]
      exact hpt n hn
    refine hle.trans (le_of_eq ?_)
    rw [sum_add_distrib, ← sum_filter, ← sum_filter]
    simp [S₁, S₂]
  have hW0 : (0 : ℝ) < wheel x := by linarith
  calc
    _ ≤ (wheel x : ℝ) * ((δ + 1) / wheel x + 1 + (δ / wheel x + 1)) :=
      mul_le_mul_of_nonneg_left (hnorm.trans (add_le_add hc₁ hc₂)) hW0.le
    _ = 2 * δ + 1 + 2 * wheel x := by field_simp; ring
    _ ≤ 8 * ε * x ^ θ := by rw [hδ] at hWδ ⊢; nlinarith

/-- The reference mean is eventually bounded in absolute value.
MMS page 11 bottom display. CONDITIONAL ON Task571.roughReferenceMean_limit and
Task571.correctionReferenceMean_limit, through Task571.referenceMean_limit. -/
theorem referenceMean_eventually_bounded :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ X : ℝ, ∀ x : ℝ, X ≤ x → |Task379.referenceMean x| ≤ M := by
  obtain ⟨X, hX⟩ := Task571.referenceMean_limit 1 one_pos
  refine ⟨|4 * Task571.buchstabModel 4 + Task571.profileIntegral Task571.buchstabModel| + 1,
    by positivity, X, fun x hx => ?_⟩
  have h := hX x hx
  have h2 := abs_sub_abs_le_abs_sub (Task379.referenceMean x)
    (4 * Task571.buchstabModel 4 + Task571.profileIntegral Task571.buchstabModel)
  linarith

/-- The unsmoothing algebra of MMS page 12 for one class and one frequency.
Derived triangle inequality step. -/
theorem unsmoothing_norm_bound {s : Finset ℕ} (ρp g : ℕ → ℝ) (f : ℕ → ℂ) (m : ℝ)
    (hρ : ∀ n ∈ s, 0 ≤ ρp n) (_hg0 : ∀ n ∈ s, 0 ≤ g n) (hg1 : ∀ n ∈ s, g n ≤ 1)
    (hf : ∀ n ∈ s, ‖f n‖ = 1) :
    ‖∑ n ∈ s, ((ρp n : ℝ) : ℂ) * f n - (m : ℂ) * ∑ n ∈ s, f n‖ ≤
      ‖∑ n ∈ s, ((ρp n * g n : ℝ) : ℂ) * f n - (m : ℂ) * ∑ n ∈ s, ((g n : ℝ) : ℂ) * f n‖ +
        ∑ n ∈ s, ρp n * (1 - g n) +
        |m| * ‖∑ n ∈ s, ((1 - g n : ℝ) : ℂ) * f n‖ := by
  have he : ∑ n ∈ s, ((ρp n : ℝ) : ℂ) * f n - (m : ℂ) * ∑ n ∈ s, f n =
      (∑ n ∈ s, ((ρp n * g n : ℝ) : ℂ) * f n - (m : ℂ) * ∑ n ∈ s, ((g n : ℝ) : ℂ) * f n) +
        ∑ n ∈ s, ((ρp n * (1 - g n) : ℝ) : ℂ) * f n -
        (m : ℂ) * ∑ n ∈ s, ((1 - g n : ℝ) : ℂ) * f n := by
    have h1 : ∑ n ∈ s, ((ρp n : ℝ) : ℂ) * f n =
        ∑ n ∈ s, ((ρp n * g n : ℝ) : ℂ) * f n + ∑ n ∈ s, ((ρp n * (1 - g n) : ℝ) : ℂ) * f n := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro n _
      push_cast
      ring
    have h2 : ∑ n ∈ s, f n =
        ∑ n ∈ s, ((g n : ℝ) : ℂ) * f n + ∑ n ∈ s, ((1 - g n : ℝ) : ℂ) * f n := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro n _
      push_cast
      ring
    rw [h1, h2]
    ring
  have hB : ‖∑ n ∈ s, ((ρp n * (1 - g n) : ℝ) : ℂ) * f n‖ ≤ ∑ n ∈ s, ρp n * (1 - g n) := by
    apply (norm_sum_le _ _).trans
    apply le_of_eq
    apply sum_congr rfl
    intro n hn
    rw [norm_mul, hf n hn, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hρ n hn) (by linarith [hg1 n hn]))]
  rw [he]
  calc
    _ ≤ ‖(∑ n ∈ s, ((ρp n * g n : ℝ) : ℂ) * f n - (m : ℂ) * ∑ n ∈ s, ((g n : ℝ) : ℂ) * f n) +
          ∑ n ∈ s, ((ρp n * (1 - g n) : ℝ) : ℂ) * f n‖ +
        ‖(m : ℂ) * ∑ n ∈ s, ((1 - g n : ℝ) : ℂ) * f n‖ := norm_sub_le _ _
    _ ≤ _ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      linarith [norm_add_le
        (∑ n ∈ s, ((ρp n * g n : ℝ) : ℂ) * f n - (m : ℂ) * ∑ n ∈ s, ((g n : ℝ) : ℂ) * f n)
        (∑ n ∈ s, ((ρp n * (1 - g n) : ℝ) : ℂ) * f n)]

/-- The exact statement of harman_fourier_reference_input from the page 12 leaves.
MMS page 11 Proposition 5.1 and page 12 unsmoothing displays.
CONDITIONAL ON smoothed_fourier_reference, edge_sieve_upper, edge_count_bound,
Task571.roughReferenceMean_limit and Task571.correctionReferenceMean_limit. -/
theorem harman_fourier_reference_input_of_leaves (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1) :
    ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      Hyp1 θ x (Task379.referenceMean x) η (Task361.harmanMajorant x) := by
  intro η hη
  obtain ⟨C, hC, hE⟩ := edge_sieve_upper θ hθ hθ1
  obtain ⟨M, hM, XM, hXM⟩ := referenceMean_eventually_bounded
  set ε : ℝ := min (1 / 2) (η / (3 * (C + 8 * M + 1))) with hεdef
  have hden : 0 < 3 * (C + 8 * M + 1) := by positivity
  have hε : 0 < ε := lt_min (by norm_num) (div_pos hη hden)
  have hε1 : ε < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hεη : ε * (3 * (C + 8 * M + 1)) ≤ η :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  obtain ⟨X₁, hX₁⟩ := smoothed_fourier_reference θ hθ hθ1 ε hε hε1 (η / 3) (by linarith)
  obtain ⟨X₂, hX₂⟩ := hE ε hε hε1
  obtain ⟨X₃, hX₃⟩ := edge_count_bound θ (by linarith) ε hε hε1
  refine ⟨max (max X₁ X₂) (max X₃ (max XM 2)), fun x hx => ?_⟩
  have hx₁ : X₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx₂ : X₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx₃ : X₃ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxM : XM ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)) hx
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_right _ _)) hx
  intro c hc γ
  have hφ : (0 : ℝ) < (wheel x).totient := by
    exact_mod_cast Nat.totient_pos.mpr (wheel_pos x)
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hD : 0 < ((wheel x).totient : ℝ) * Real.log x := mul_pos hφ hL
  have hW : (0 : ℝ) < wheel x := by exact_mod_cast wheel_pos x
  have hxθ : 0 < x ^ θ := Real.rpow_pos_of_pos (by linarith) _
  have hmain := unsmoothing_norm_bound
    (s := (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]))
    (Task361.harmanMajorant x) (fun n => edgeCutoff ε θ x n) (fun n => e (n * γ))
    (Task379.referenceMean x / Real.log x * (wheel x / (wheel x).totient))
    (fun n _ => Task361.harmanMajorant_nonneg x n) (fun n _ => edgeCutoff_nonneg _ _ _ _)
    (fun n _ => edgeCutoff_le_one _ _ _ _) (fun n _ => norm_e _)
  have h1 := hX₁ x hx₁ c hc γ
  have h2 := hX₂ x hx₂ c hc
  have h3 := hX₃ x hx₃ c γ
  have hm := hXM x hxM
  set N := ‖∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]),
          ((1 - edgeCutoff ε θ x n : ℝ) : ℂ) * e (n * γ)‖ with hN
  have hmabs : |Task379.referenceMean x / Real.log x * (wheel x / (wheel x).totient)| * N =
      |Task379.referenceMean x| * ((wheel x : ℝ) * N) /
        (((wheel x).totient : ℝ) * Real.log x) := by
    rw [abs_mul, abs_div, abs_div, abs_of_pos hL, abs_of_pos hW, abs_of_pos hφ]
    field_simp
  have h3' : |Task379.referenceMean x| * ((wheel x : ℝ) * N) ≤ M * (8 * ε * x ^ θ) :=
    mul_le_mul hm h3 (by positivity) hM
  have hfin : η / 3 * x ^ θ + C * ε * x ^ θ + M * (8 * ε * x ^ θ) ≤ η * x ^ θ := by
    have : C * ε + 8 * M * ε ≤ 2 * η / 3 := by nlinarith
    nlinarith
  calc
    _ ≤ _ := hmain
    _ ≤ η / 3 * x ^ θ / (((wheel x).totient : ℝ) * Real.log x) +
          C * ε * x ^ θ / (((wheel x).totient : ℝ) * Real.log x) +
          M * (8 * ε * x ^ θ) / (((wheel x).totient : ℝ) * Real.log x) := by
      rw [hmabs]
      gcongr
    _ = (η / 3 * x ^ θ + C * ε * x ^ θ + M * (8 * ε * x ^ θ)) /
          (((wheel x).totient : ℝ) * Real.log x) := by ring
    _ ≤ η * x ^ θ / (((wheel x).totient : ℝ) * Real.log x) := by gcongr

/-! Pass 3 split of smoothed_fourier_reference, MMS pages 11 to 13 and 25. -/

/-- Dirichlet approximation with a reduced fraction, the step we may write gamma as
a over q plus lambda of MMS page 12. Derived from Mathlib exists_int_int_abs_mul_sub_le. -/
theorem dirichlet_reduced (γ : ℝ) {N : ℕ} (hN : 0 < N) :
    ∃ a : ℤ, ∃ q : ℕ, 0 < q ∧ q ≤ N ∧ Int.gcd a q = 1 ∧ |(q : ℝ) * γ - a| ≤ 1 / (N + 1) := by
  obtain ⟨j, k, hk0, hkN, h⟩ := Real.exists_int_int_abs_mul_sub_le γ hN
  set d := Int.gcd j k with hd
  have hdpos : 0 < d := Int.gcd_pos_of_ne_zero_right _ hk0.ne'
  have hdj : (d : ℤ) ∣ j := Int.gcd_dvd_left j k
  have hdk : (d : ℤ) ∣ k := Int.gcd_dvd_right j k
  obtain ⟨a, ha⟩ := hdj
  obtain ⟨q', hq'⟩ := hdk
  have hq'pos : 0 < q' := by
    rcases lt_trichotomy q' 0 with h | h | h
    · nlinarith [show (0:ℤ) < d by exact_mod_cast hdpos]
    · simp [h] at hq'; omega
    · exact h
  refine ⟨a, q'.toNat, by omega, ?_, ?_, ?_⟩
  · have : q' ≤ k := by
      rw [hq']; nlinarith [show (1:ℤ) ≤ d by exact_mod_cast hdpos]
    omega
  · have hg := Int.gcd_div_gcd_div_gcd (i := j) (j := k) hdpos
    have e1 : j / (d : ℤ) = a := by rw [ha]; exact Int.mul_ediv_cancel_left _ (by exact_mod_cast hdpos.ne')
    have e2 : k / (d : ℤ) = q' := by rw [hq']; exact Int.mul_ediv_cancel_left _ (by exact_mod_cast hdpos.ne')
    rw [← hd, e1, e2] at hg
    rw [show ((q'.toNat : ℕ) : ℤ) = q' by omega]
    exact hg
  · have hcast : ((q'.toNat : ℕ) : ℝ) = (q' : ℝ) := by exact_mod_cast (show ((q'.toNat : ℕ) : ℤ) = q' by omega)
    rw [hcast]
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hdpos
    have hk : (k : ℝ) * γ - j = d * ((q' : ℝ) * γ - a) := by
      rw [hq', ha]; push_cast; ring
    rw [hk, abs_mul, abs_of_pos (by linarith)] at h
    have := abs_nonneg ((q' : ℝ) * γ - a)
    nlinarith

/-- LEAF: MMS page 11 Proposition 5.1 moreover clause, proved as Lemma 5.6 on page 13,
with d equal to W, minor arc case q at least log to the 5A. The weighted side is
O of x to the theta over log to the A, here in the o of x to the theta over phi W log x
form used on page 12. Class HARD for Codex. -/
theorem minor_arc_weighted (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (A : ℝ) (hA : 1 ≤ A) :
    ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ c : ℕ, Nat.Coprime c (wheel x) → ∀ γ : ℝ, ∀ a : ℤ, ∀ q : ℕ, 0 < q →
        Int.gcd a q = 1 → Real.log x ^ (5 * A) ≤ q →
        (q : ℝ) ≤ x ^ (2 * θ - 1) / Real.log x ^ (5 * A) →
        |(q : ℝ) * γ - a| < 1 / (x ^ (2 * θ - 1) / Real.log x ^ (5 * A)) →
        ‖∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]),
            ((Task361.harmanMajorant x n * edgeCutoff ε θ x n : ℝ) : ℂ) * e (n * γ)‖ ≤
          η * x ^ θ / ((wheel x).totient * Real.log x) := by
  sorry

/-- LEAF: MMS page 12, if q is at least log to the 5A then all terms are
O of eta x to the theta over phi W log x, here the main term with W over phi W and no
coprimality to q, a smoothed exponential sum with frequency W gamma away from integers.
Class MEDIUM for Open Math OS. -/
theorem minor_arc_main (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (A : ℝ) (hA : 1 ≤ A) :
    ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ c : ℕ, Nat.Coprime c (wheel x) → ∀ γ : ℝ, ∀ a : ℤ, ∀ q : ℕ, 0 < q →
        Int.gcd a q = 1 → Real.log x ^ (5 * A) ≤ q →
        (q : ℝ) ≤ x ^ (2 * θ - 1) / Real.log x ^ (5 * A) →
        |(q : ℝ) * γ - a| < 1 / (x ^ (2 * θ - 1) / Real.log x ^ (5 * A)) →
        ‖((Task379.referenceMean x / Real.log x * (wheel x / (wheel x).totient) : ℝ) : ℂ) *
          ∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]),
            ((edgeCutoff ε θ x n : ℝ) : ℂ) * e (n * γ)‖ ≤
          η * x ^ θ / ((wheel x).totient * Real.log x) := by
  sorry

/-- LEAF: MMS Lemma 5.12 page 25, Proposition 5.1 on major arcs, with d equal to W,
q below log to the 5A, main term [W,q] over phi of [W,q] times the sum over n coprime
to q. The long g1 mean is referenceMean over log x as in smoothed_fourier_reference.
Class HARD for Codex. -/
theorem major_arc_prop51 (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (A : ℝ) (hA : 1 ≤ A) :
    ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ c : ℕ, Nat.Coprime c (wheel x) → ∀ γ : ℝ, ∀ a : ℤ, ∀ q : ℕ, 0 < q →
        Int.gcd a q = 1 → (q : ℝ) < Real.log x ^ (5 * A) →
        (q : ℝ) ≤ x ^ (2 * θ - 1) / Real.log x ^ (5 * A) →
        |(q : ℝ) * γ - a| < 1 / (x ^ (2 * θ - 1) / Real.log x ^ (5 * A)) →
        ‖∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]),
            ((Task361.harmanMajorant x n * edgeCutoff ε θ x n : ℝ) : ℂ) * e (n * γ) -
          ((Task379.referenceMean x / Real.log x *
              ((Nat.lcm (wheel x) q : ℝ) / (Nat.lcm (wheel x) q).totient) : ℝ) : ℂ) *
          ∑ n ∈ ((ints (x - x ^ θ / 3) (x + x ^ θ)).filter
              (fun n => n ≡ c [MOD wheel x])).filter (fun n => Nat.Coprime n q),
            ((edgeCutoff ε θ x n : ℝ) : ℂ) * e (n * γ)‖ ≤
          η * x ^ θ / ((wheel x).totient * Real.log x) := by
  sorry

/-- LEAF: MMS page 12 last paragraph, for q below log to the 5A one has [W,q] over
phi of [W,q] equal to 1 plus o of 1 times W over phi W, and the terms with n not
coprime to q contribute o of x to the theta over phi W log x. Class MEDIUM for Open Math OS. -/
theorem major_arc_reduction (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (A : ℝ) (hA : 1 ≤ A) :
    ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ c : ℕ, Nat.Coprime c (wheel x) → ∀ γ : ℝ, ∀ q : ℕ, 0 < q →
        (q : ℝ) < Real.log x ^ (5 * A) →
        ‖((Task379.referenceMean x / Real.log x *
              ((Nat.lcm (wheel x) q : ℝ) / (Nat.lcm (wheel x) q).totient) : ℝ) : ℂ) *
          ∑ n ∈ ((ints (x - x ^ θ / 3) (x + x ^ θ)).filter
              (fun n => n ≡ c [MOD wheel x])).filter (fun n => Nat.Coprime n q),
            ((edgeCutoff ε θ x n : ℝ) : ℂ) * e (n * γ) -
          ((Task379.referenceMean x / Real.log x * (wheel x / (wheel x).totient) : ℝ) : ℂ) *
          ∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]),
            ((edgeCutoff ε θ x n : ℝ) : ℂ) * e (n * γ)‖ ≤
          η * x ^ θ / ((wheel x).totient * Real.log x) := by
  sorry

/-- Eventually Q, the Dirichlet parameter of MMS page 11 with A equal to one, is at least two.
Derived from Mathlib isLittleO_log_rpow_rpow_atTop. -/
theorem dirichlet_Q_ge_two (θ : ℝ) (hθ : 11 / 20 < θ) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → 2 ≤ x ^ (2 * θ - 1) / Real.log x ^ (5 * (1 : ℝ)) := by
  have hs : 0 < 2 * θ - 1 := by linarith
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp
    (((isLittleO_log_rpow_rpow_atTop (5 * (1 : ℝ)) hs).bound (by norm_num : (0 : ℝ) < 1 / 2)).and
      (Filter.eventually_ge_atTop (3 : ℝ)))
  refine ⟨X₀, fun x hx => ?_⟩
  obtain ⟨h, hx3⟩ := hX₀ x hx
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hL5 : 0 < Real.log x ^ (5 * (1 : ℝ)) := Real.rpow_pos_of_pos hL _
  have hxs : 0 < x ^ (2 * θ - 1) := Real.rpow_pos_of_pos (by linarith) _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hL5, abs_of_pos hxs] at h
  rw [le_div_iff₀ hL5]
  have h' : 2 * Real.log x ^ (5 * (1 : ℝ)) ≤ x ^ (2 * θ - 1) := by
    have := mul_le_mul_of_nonneg_left h (by norm_num : (0 : ℝ) ≤ 2)
    calc _ ≤ 2 * (1 / 2 * x ^ (2 * θ - 1)) := this
      _ = _ := by ring
  simpa [mul_comm] using h'

/-- The statement of smoothed_fourier_reference from the finer page 11 to 12 leaves.
CONDITIONAL ON minor_arc_weighted, minor_arc_main, major_arc_prop51 and
major_arc_reduction, all at A equal to one. -/
theorem smoothed_fourier_reference_of_leaves (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) :
    ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ c : ℕ, Nat.Coprime c (wheel x) → ∀ γ : ℝ,
        ‖∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]),
            ((Task361.harmanMajorant x n * edgeCutoff ε θ x n : ℝ) : ℂ) * e (n * γ) -
          ((Task379.referenceMean x / Real.log x * (wheel x / (wheel x).totient) : ℝ) : ℂ) *
          ∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]),
            ((edgeCutoff ε θ x n : ℝ) : ℂ) * e (n * γ)‖ ≤
          η * x ^ θ / ((wheel x).totient * Real.log x) := by
  intro η hη
  have hη2 : 0 < η / 2 := by linarith
  obtain ⟨X₁, h₁⟩ := minor_arc_weighted θ hθ hθ1 ε hε hε1 1 le_rfl (η / 2) hη2
  obtain ⟨X₂, h₂⟩ := minor_arc_main θ hθ hθ1 ε hε hε1 1 le_rfl (η / 2) hη2
  obtain ⟨X₃, h₃⟩ := major_arc_prop51 θ hθ hθ1 ε hε hε1 1 le_rfl (η / 2) hη2
  obtain ⟨X₄, h₄⟩ := major_arc_reduction θ hθ hθ1 ε hε hε1 1 le_rfl (η / 2) hη2
  obtain ⟨X₅, h₅⟩ := dirichlet_Q_ge_two θ hθ
  refine ⟨max (max X₁ X₂) (max X₃ (max X₄ X₅)), fun x hx c hc γ => ?_⟩
  have hx₁ : X₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx₂ : X₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx₃ : X₃ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx₄ : X₄ ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)) hx
  have hx₅ : X₅ ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_right _ _)) hx
  set Q := x ^ (2 * θ - 1) / Real.log x ^ (5 * (1 : ℝ)) with hQ
  have hQ2 : 2 ≤ Q := h₅ x hx₅
  have hN : 0 < ⌊Q⌋₊ := Nat.floor_pos.mpr (by linarith)
  obtain ⟨a, q, hq0, hqN, hgcd, happ⟩ := dirichlet_reduced γ hN
  have hqQ : (q : ℝ) ≤ Q := le_trans (by exact_mod_cast hqN) (Nat.floor_le (by linarith))
  have happ' : |(q : ℝ) * γ - a| < 1 / Q := by
    refine lt_of_le_of_lt happ ?_
    apply one_div_lt_one_div_of_lt (by linarith)
    exact Nat.lt_floor_add_one Q
  have hsum : η / 2 * x ^ θ / ((wheel x).totient * Real.log x) +
      η / 2 * x ^ θ / ((wheel x).totient * Real.log x) =
      η * x ^ θ / ((wheel x).totient * Real.log x) := by ring
  rcases le_or_gt (Real.log x ^ (5 * (1 : ℝ))) (q : ℝ) with hbig | hsmall
  · have a1 := h₁ x hx₁ c hc γ a q hq0 hgcd hbig hqQ happ'
    have a2 := h₂ x hx₂ c hc γ a q hq0 hgcd hbig hqQ happ'
    rw [← hsum]
    exact (norm_sub_le _ _).trans (add_le_add a1 a2)
  · have a3 := h₃ x hx₃ c hc γ a q hq0 hgcd hsmall hqQ happ'
    have a4 := h₄ x hx₄ c hc γ q hq0 hsmall
    rw [← hsum]
    exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add a3 a4)

end LeanLab.Ternary.MMS.Task420
