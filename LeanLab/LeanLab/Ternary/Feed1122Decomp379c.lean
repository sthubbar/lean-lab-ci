/-
Feed split of harman_reference_mean from Decomp379c.
MMS https://arxiv.org/abs/1610.02017v2, page 11 equation 5.1 and the bottom
Buchstab display, page 12 first paragraph. The majorant of equation 5.1 is the
rough indicator at x to the 1/4 plus the triple prime correction, so the
reference mean splits into a Buchstab omega term and a triple integral term.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp379c
import LeanLab.Ternary.Decomp420d
import LeanLab.Ternary.MMSBohrSmoothing
import LeanLab.Halupczok2012.U1439Combin

namespace LeanLab.Ternary.MMS.Task379
open Finset MeasureTheory
open scoped Interval

/-- LEAF: MMS page 11 bottom display, first term, the rough number density, HARD for Codex.
By the prime number theorem and the Buchstab function, integers in the long
reference interval free of primes below x to the 1/4 have density 4 omega 4
over log x. Numerically 4 omega 4 is about 2.2458, recomputed in the notes. -/
theorem reference_rough_mean :
    ∃ α₁ : ℝ, 0 < α₁ ∧ α₁ < 2.25 ∧
      ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        |Real.log x *
            (∑ n ∈ ints x (x + referenceLength x),
              referenceWeight x n * Task361.roughIndicator n (x ^ (1 / 4 : ℝ))) /
            (∫ t in x..(x + referenceLength x), referenceWeight x t) - α₁| ≤ δ := by
  sorry

/-- LEAF: MMS page 11 bottom display, the triple Buchstab integral term, HARD for Codex.
The correction of equation 5.1 over primes x to the 1/10 below p1 below p2 below p3
below x to the 1/4 has density the triple integral of omega of the remaining
exponent over p1, divided by a1 squared a2 a3. Numerically about 0.566, see the notes. -/
theorem reference_triple_mean :
    ∃ α₂ : ℝ, 0 ≤ α₂ ∧ α₂ < 0.65 ∧
      ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        |Real.log x *
            (∑ n ∈ ints x (x + referenceLength x),
              referenceWeight x n * (Task361.harmanMajorant x n -
                Task361.roughIndicator n (x ^ (1 / 4 : ℝ)))) /
            (∫ t in x..(x + referenceLength x), referenceWeight x t) - α₂| ≤ δ := by
  sorry

/-- The reference mean is the sum of its rough and triple parts.
Derived from MMS page 11 equation 5.1 by linearity of the weighted sum. -/
theorem referenceMean_split (x : ℝ) :
    referenceMean x =
      Real.log x *
          (∑ n ∈ ints x (x + referenceLength x),
            referenceWeight x n * Task361.roughIndicator n (x ^ (1 / 4 : ℝ))) /
          (∫ t in x..(x + referenceLength x), referenceWeight x t) +
        Real.log x *
          (∑ n ∈ ints x (x + referenceLength x),
            referenceWeight x n * (Task361.harmanMajorant x n -
              Task361.roughIndicator n (x ^ (1 / 4 : ℝ)))) /
          (∫ t in x..(x + referenceLength x), referenceWeight x t) := by
  unfold referenceMean
  rw [← add_div, ← mul_add, ← sum_add_distrib]
  congr 2
  apply sum_congr rfl
  intro n _
  ring

/-- The exact reference mean leaf of Decomp379c from its two density parts.
MMS pages 11 and 12. CONDITIONAL ON reference_rough_mean and reference_triple_mean. -/
theorem harman_reference_mean_of_leaves :
    ∃ αp : ℝ, 0 < αp ∧ αp < 2.9 ∧
      ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        |referenceMean x - αp| ≤ δ := by
  obtain ⟨α₁, h1p, h1u, h1⟩ := reference_rough_mean
  obtain ⟨α₂, h2p, h2u, h2⟩ := reference_triple_mean
  refine ⟨α₁ + α₂, by linarith, by linarith, ?_⟩
  intro δ hδ
  obtain ⟨X₁, hX₁⟩ := h1 (δ / 2) (by linarith)
  obtain ⟨X₂, hX₂⟩ := h2 (δ / 2) (by linarith)
  refine ⟨max X₁ X₂, fun x hx => ?_⟩
  have a := hX₁ x ((le_max_left _ _).trans hx)
  have b := hX₂ x ((le_max_right _ _).trans hx)
  rw [referenceMean_split]
  have := abs_add_le
    (Real.log x *
        (∑ n ∈ ints x (x + referenceLength x),
          referenceWeight x n * Task361.roughIndicator n (x ^ (1 / 4 : ℝ))) /
        (∫ t in x..(x + referenceLength x), referenceWeight x t) - α₁)
    (Real.log x *
        (∑ n ∈ ints x (x + referenceLength x),
          referenceWeight x n * (Task361.harmanMajorant x n -
            Task361.roughIndicator n (x ^ (1 / 4 : ℝ)))) /
        (∫ t in x..(x + referenceLength x), referenceWeight x t) - α₂)
  calc _ = |(Real.log x *
        (∑ n ∈ ints x (x + referenceLength x),
          referenceWeight x n * Task361.roughIndicator n (x ^ (1 / 4 : ℝ))) /
        (∫ t in x..(x + referenceLength x), referenceWeight x t) - α₁) +
      (Real.log x *
        (∑ n ∈ ints x (x + referenceLength x),
          referenceWeight x n * (Task361.harmanMajorant x n -
            Task361.roughIndicator n (x ^ (1 / 4 : ℝ)))) /
        (∫ t in x..(x + referenceLength x), referenceWeight x t) - α₂)| := by
          congr 1; ring
    _ ≤ δ := by linarith

/-! ### Pass 2 split of harman_fourier_of_reference_mean, MMS page 12 unsmoothing.
The smooth cutoff, the two leaves and the edge count follow the reference text of
branch claude/Ternary-feed1122-Decomp420d, copied here, not imported. -/

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
          ((referenceMean x / Real.log x * (wheel x / (wheel x).totient) : ℝ) : ℂ) *
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
  have hWlog := Task420.wheel_le_log hxe
  have hW1 : (1 : ℝ) ≤ wheel x := by exact_mod_cast Task420.wheel_pos x
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
    apply LeanLab.Halupczok2012.card_cong_le (x := x - x ^ θ / 3 - 1) (Task420.wheel_pos x)
      (by linarith) _ (hcong S₁ (filter_subset _ _))
    intro m hm
    obtain ⟨hmS, hm1⟩ := mem_filter.mp hm
    have := hmem m hmS
    constructor <;> linarith
  have hc₂ : (S₂.card : ℝ) ≤ δ / wheel x + 1 := by
    apply LeanLab.Halupczok2012.card_cong_le (x := x + x ^ θ - δ) (Task420.wheel_pos x)
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


/-- The page 12 unsmoothing with the exact reference mean as the density.
MMS page 11 Proposition 5.1 and page 12 unsmoothing displays.
CONDITIONAL ON smoothed_fourier_reference and edge_sieve_upper, and on an eventual
bound for the reference mean, supplied below by the hypothesis hmean. -/
theorem fourier_referenceMean_of_leaves (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1)
    (hbd : ∃ M : ℝ, 0 ≤ M ∧ ∃ X : ℝ, ∀ x : ℝ, X ≤ x → |referenceMean x| ≤ M) :
    ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      Hyp1 θ x (referenceMean x) η (Task361.harmanMajorant x) := by
  intro η hη
  obtain ⟨C, hC, hE⟩ := edge_sieve_upper θ hθ hθ1
  obtain ⟨M, hM, XM, hXM⟩ := hbd
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
    exact_mod_cast Nat.totient_pos.mpr (Task420.wheel_pos x)
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hD : 0 < ((wheel x).totient : ℝ) * Real.log x := mul_pos hφ hL
  have hW : (0 : ℝ) < wheel x := by exact_mod_cast Task420.wheel_pos x
  have hxθ : 0 < x ^ θ := Real.rpow_pos_of_pos (by linarith) _
  have hmain := unsmoothing_norm_bound
    (s := (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]))
    (Task361.harmanMajorant x) (fun n => edgeCutoff ε θ x n) (fun n => e (n * γ))
    (referenceMean x / Real.log x * (wheel x / (wheel x).totient))
    (fun n _ => Task361.harmanMajorant_nonneg x n) (fun n _ => edgeCutoff_nonneg _ _ _ _)
    (fun n _ => edgeCutoff_le_one _ _ _ _) (fun n _ => norm_e _)
  have h1 := hX₁ x hx₁ c hc γ
  have h2 := hX₂ x hx₂ c hc
  have h3 := hX₃ x hx₃ c γ
  have hm := hXM x hxM
  set N := ‖∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]),
          ((1 - edgeCutoff ε θ x n : ℝ) : ℂ) * e (n * γ)‖ with hN
  have hmabs : |referenceMean x / Real.log x * (wheel x / (wheel x).totient)| * N =
      |referenceMean x| * ((wheel x : ℝ) * N) /
        (((wheel x).totient : ℝ) * Real.log x) := by
    rw [abs_mul, abs_div, abs_div, abs_of_pos hL, abs_of_pos hW, abs_of_pos hφ]
    field_simp
  have h3' : |referenceMean x| * ((wheel x : ℝ) * N) ≤ M * (8 * ε * x ^ θ) :=
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




/-- Changing the density in Hyp1 by at most eta over four costs at most half of eta.
Derived step of MMS page 12, the replacement of the reference mean by its limit
alpha plus, written there as alpha plus plus o of one. One class modulo W meets the
interval of length four thirds of x to the theta in at most that length over W plus
one integers, and W is at most log x, which is small against x to the theta. -/
theorem hyp1_mean_transfer (θ : ℝ) (hθ : 0 < θ) : ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
    ∀ (αp m η : ℝ) (ρp : ℕ → ℝ), 0 < η → |m - αp| ≤ η / 4 →
      Hyp1 θ x m (η / 2) ρp → Hyp1 θ x αp η ρp := by
  have hsmall := (isLittleO_log_rpow_atTop hθ).bound (by norm_num : (0 : ℝ) < 1 / 3)
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp
    (hsmall.and (Filter.eventually_ge_atTop (Real.exp 1)))
  refine ⟨X₀, fun x hx αp m η ρp hη hmα h0 c hc γ => ?_⟩
  obtain ⟨hlog, hxe⟩ := hX₀ x hx
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hxe
  have hxθ : 0 < x ^ θ := Real.rpow_pos_of_pos hx0 _
  have hL1 : 1 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) hxe
    simpa only [Real.log_exp] using h
  have hL : 0 < Real.log x := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hL, abs_of_pos hxθ] at hlog
  have hWlog := Task420.wheel_le_log hxe
  have hW : (0 : ℝ) < wheel x := by exact_mod_cast Task420.wheel_pos x
  have hφ : (0 : ℝ) < (wheel x).totient := by
    exact_mod_cast Nat.totient_pos.mpr (Task420.wheel_pos x)
  set S := (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]) with hS
  have hcard : (S.card : ℝ) ≤ (4 / 3 * x ^ θ + 1) / wheel x + 1 := by
    apply LeanLab.Halupczok2012.card_cong_le (x := x - x ^ θ / 3 - 1) (Task420.wheel_pos x)
      (by positivity)
    · intro n hn
      obtain ⟨hlo, hhi⟩ := mem_Icc.mp (mem_filter.mp hn).1
      have h1 : x - x ^ θ / 3 ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hlo)
      have h2 : (n : ℝ) ≤ x + x ^ θ :=
        (show (n : ℝ) ≤ (⌊x + x ^ θ⌋₊ : ℝ) by exact_mod_cast hhi).trans
          (Nat.floor_le (by linarith))
      constructor <;> linarith
    · intro m hm m' hm'
      exact Int.natCast_modEq_iff.mpr ((mem_filter.mp hm).2.trans (mem_filter.mp hm').2.symm)
  have hWcard : (wheel x : ℝ) * S.card ≤ 2 * x ^ θ := by
    have := mul_le_mul_of_nonneg_left hcard hW.le
    have he : (wheel x : ℝ) * ((4 / 3 * x ^ θ + 1) / wheel x + 1) =
        4 / 3 * x ^ θ + 1 + wheel x := by field_simp
    linarith
  have hE : ‖∑ n ∈ S, e (n * γ)‖ ≤ S.card := by
    apply (norm_sum_le _ _).trans
    simp [norm_e]
  have hsplit : ∑ n ∈ S, ((ρp n : ℂ) * e (n * γ)) -
      ((αp / Real.log x * (wheel x / (wheel x).totient) : ℝ) : ℂ) * ∑ n ∈ S, e (n * γ) =
      (∑ n ∈ S, ((ρp n : ℂ) * e (n * γ)) -
        ((m / Real.log x * (wheel x / (wheel x).totient) : ℝ) : ℂ) * ∑ n ∈ S, e (n * γ)) +
      (((m - αp) * (wheel x / ((wheel x).totient * Real.log x)) : ℝ) : ℂ) *
        ∑ n ∈ S, e (n * γ) := by
    have hreal : m / Real.log x * (wheel x / (wheel x).totient) -
        αp / Real.log x * (wheel x / (wheel x).totient) =
        (m - αp) * (wheel x / ((wheel x).totient * Real.log x)) := by
      field_simp
    rw [← hreal, Complex.ofReal_sub]
    ring
  have h1 := h0 c hc γ
  have hD : 0 < ((wheel x).totient : ℝ) * Real.log x := mul_pos hφ hL
  have hcoef : ‖(((m - αp) * (wheel x / ((wheel x).totient * Real.log x)) : ℝ) : ℂ)‖ =
      |m - αp| * (wheel x / ((wheel x).totient * Real.log x)) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (div_pos hW hD)]
  have h2 : ‖(((m - αp) * (wheel x / ((wheel x).totient * Real.log x)) : ℝ) : ℂ) *
      ∑ n ∈ S, e (n * γ)‖ ≤ η / 2 * x ^ θ / ((wheel x).totient * Real.log x) := by
    rw [norm_mul, hcoef]
    calc
      _ ≤ η / 4 * (wheel x / ((wheel x).totient * Real.log x)) * S.card := by
        gcongr
      _ = η / 4 * ((wheel x : ℝ) * S.card) / ((wheel x).totient * Real.log x) := by ring
      _ ≤ η / 4 * (2 * x ^ θ) / ((wheel x).totient * Real.log x) := by gcongr
      _ = η / 2 * x ^ θ / ((wheel x).totient * Real.log x) := by ring
  rw [hsplit]
  calc
    _ ≤ _ := norm_add_le _ _
    _ ≤ η / 2 * x ^ θ / ((wheel x).totient * Real.log x) +
          η / 2 * x ^ θ / ((wheel x).totient * Real.log x) := add_le_add h1 h2
    _ = η * x ^ θ / ((wheel x).totient * Real.log x) := by ring

/-- The exact statement of harman_fourier_of_reference_mean from the page 12 leaves.
MMS page 11 Proposition 5.1 and page 12 unsmoothing displays, with the limit
alpha plus of the reference mean taken from the hypothesis hmean.
CONDITIONAL ON smoothed_fourier_reference and edge_sieve_upper. -/
theorem harman_fourier_of_reference_mean_of_leaves (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1)
    (αp : ℝ)
    (hmean : ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |referenceMean x - αp| ≤ δ) :
    ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      Hyp1 θ x αp η (Task361.harmanMajorant x) := by
  intro η hη
  have hbd : ∃ M : ℝ, 0 ≤ M ∧ ∃ X : ℝ, ∀ x : ℝ, X ≤ x → |referenceMean x| ≤ M := by
    obtain ⟨X, hX⟩ := hmean 1 one_pos
    refine ⟨|αp| + 1, by positivity, X, fun x hx => ?_⟩
    have h := hX x hx
    have h2 := abs_sub_abs_le_abs_sub (referenceMean x) αp
    linarith
  obtain ⟨X₁, hX₁⟩ := fourier_referenceMean_of_leaves θ hθ hθ1 hbd (η / 2) (by linarith)
  obtain ⟨X₂, hX₂⟩ := hmean (η / 4) (by linarith)
  obtain ⟨X₃, hX₃⟩ := hyp1_mean_transfer θ (by linarith)
  refine ⟨max X₁ (max X₂ X₃), fun x hx => ?_⟩
  exact hX₃ x ((le_max_right _ _).trans ((le_max_right _ _).trans hx)) αp (referenceMean x) η
    (Task361.harmanMajorant x) hη (hX₂ x ((le_max_left _ _).trans ((le_max_right _ _).trans hx)))
    (hX₁ x ((le_max_left _ _).trans hx))

end LeanLab.Ternary.MMS.Task379
