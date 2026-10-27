/-
P0083 Perelli 1996, page 482, the named Weyl lemma and equations 6 through 8.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.VaughanInput
import LeanLab.Perelli1996.Linear88
import LeanLab.Perelli1996.Divisor103

namespace LeanLab.Perelli1996.Decomp103b
open Finset Real Polynomial
open LeanLab.Perelli1996.Section2
noncomputable section

/-- A uniform envelope for the linear interval sums in equation 6. -/
def linearEnvelope (H β : ℝ) : ℝ :=
  sSup {x | ∃ start len : ℕ, (len : ℝ) ≤ H + 1 ∧ x = ‖Kernel.T start len β‖}

/-- The normalized heavy or light contribution in equations 7 and 8. -/
def divisorCost (F : ℤ[X]) (c N H D α : ℝ) (heavy : Bool) : ℝ :=
  (∑ h ∈ (Icc 1 ⌊c * H ^ (F.natDegree - 1)⌋₊).filter
      (fun h => if heavy then Real.log N ^ D < (divisorCount F.natDegree h : ℝ)
        else (divisorCount F.natDegree h : ℝ) ≤ Real.log N ^ D),
    (divisorCount F.natDegree h : ℝ) * linearEnvelope H (α * h)) / H ^ F.natDegree

/-- The linear interval envelope is nonnegative. -/
theorem linearEnvelope_nonneg (H β : ℝ) : 0 ≤ linearEnvelope H β := by
  unfold linearEnvelope
  apply Real.sSup_nonneg
  rintro x ⟨start, len, hlen, rfl⟩
  exact norm_nonneg _

/-- Both divisor costs are nonnegative for positive H. -/
theorem divisorCost_nonneg (F : ℤ[X]) (c N H D α : ℝ) (heavy : Bool) (hH : 0 < H) :
    0 ≤ divisorCost F c N H D α heavy := by
  unfold divisorCost
  apply div_nonneg _ (by positivity)
  apply Finset.sum_nonneg
  intro h hh
  exact mul_nonneg (Nat.cast_nonneg _) (linearEnvelope_nonneg _ _)

/-- The linear envelope never exceeds the allowed length. -/
theorem linearEnvelope_le (H β : ℝ) (hH : 0 ≤ H + 1) : linearEnvelope H β ≤ H + 1 := by
  unfold linearEnvelope
  apply csSup_le
  · exact ⟨0, 0, 0, by simpa using hH, by simp [Kernel.T]⟩
  · rintro x ⟨start, len, hlen, rfl⟩
    exact (Kernel.norm_T_le start len β).trans hlen

/-- Every permitted linear interval sum is bounded by the envelope. -/
theorem norm_T_le_linearEnvelope (start len : ℕ) (H β : ℝ) (hlen : (len : ℝ) ≤ H + 1) :
    ‖Kernel.T start len β‖ ≤ linearEnvelope H β := by
  unfold linearEnvelope
  apply le_csSup
  · refine ⟨H + 1, ?_⟩
    rintro x ⟨a, m, hm, rfl⟩
    exact (Kernel.norm_T_le a m β).trans hm
  · exact ⟨start, len, hlen, rfl⟩

/-- The two divisor costs partition the full normalized divisor sum. -/
theorem divisorCost_partition (F : ℤ[X]) (c N H D α : ℝ) :
    divisorCost F c N H D α true + divisorCost F c N H D α false =
      (∑ h ∈ Icc 1 ⌊c * H ^ (F.natDegree - 1)⌋₊,
        (divisorCount F.natDegree h : ℝ) * linearEnvelope H (α * h)) / H ^ F.natDegree := by
  classical
  unfold divisorCost
  simp only [Bool.false_eq_true, ite_false, ite_true]
  rw [← add_div]
  congr 1
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hheavy : Real.log N ^ D < (divisorCount F.natDegree h : ℝ)
  · simp [hheavy, not_le.mpr hheavy]
  · simp [hheavy, le_of_not_gt hheavy]

/-- LEAF. Page 482 equation 6, after taking the K-th root.
Vaughan 1981 Lemma 2.4 is the published differencing input.
The two costs partition the divisor sum exactly. -/
theorem leaf_differencing (F : ℤ[X]) (hF : Admissible F) (hk : 2 ≤ F.natDegree) :
    ∃ c C N₀ : ℝ, 0 < c ∧ 0 < C ∧ 3 ≤ N₀ ∧
      ∀ N H D α : ℝ, N₀ ≤ N → 1 ≤ H → H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ‖polynomialKernel F N H α‖ ≤ C * H *
        (1 / H + divisorCost F c N H D α true + divisorCost F c N H D α false) ^
          (1 / weylExponent F) := by
  sorry

/-- The heavy cost is bounded by the truncated divisor second moment. -/
theorem heavyCost_le (F : ℤ[X]) (c N H D α : ℝ) (hH : 1 ≤ H)
    (hL : 0 < Real.log N) :
    divisorCost F c N H D α true ≤
      ((H + 1) / Real.log N ^ D *
        ∑ h ∈ Icc 1 ⌊c * H ^ (F.natDegree - 1)⌋₊, (divisorCount F.natDegree h : ℝ) ^ 2) /
          H ^ F.natDegree := by
  have hH0 : 0 < H := by linarith
  have hb := heavy_weight_cutoff (Icc 1 ⌊c * H ^ (F.natDegree - 1)⌋₊)
    (fun h => (divisorCount F.natDegree h : ℝ))
    (fun h => linearEnvelope H (α * h))
    (Real.rpow_pos_of_pos hL D) (show 0 ≤ H + 1 by linarith)
    (fun h _ => Nat.cast_nonneg _) (fun h _ => linearEnvelope_le H (α * h) (by linarith))
  unfold divisorCost
  simp only [Bool.true_eq, ite_true]
  exact div_le_div_of_nonneg_right hb (by positivity)

/-- LEAF. Page 482 equation 7, normalized by H to the k.
Vaughan 1981 page 120 supplies the divisor second moment. -/
theorem leaf_heavy (F : ℤ[X]) (hF : Admissible F) (hk : 2 ≤ F.natDegree)
    (c D : ℝ) (hc : 0 < c) (hD : 0 < D) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H α : ℝ, N₀ ≤ N →
      1 ≤ H → H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      divisorCost F c N H D α true ≤
        C * Real.log N ^ (-D + (F.natDegree : ℝ) ^ 2 - 1) := by
  let k := F.natDegree
  let l := k ^ 2 - 1
  let T := 2 + Real.log (c + 2)
  let C := 2 * (c + 2) * T ^ l
  have hk1 : 1 ≤ k := by dsimp [k]; omega
  have hc2 : 0 < c + 2 := by linarith
  have hT : 0 < T := by
    have : 0 ≤ Real.log (c + 2) := Real.log_nonneg (by linarith)
    dsimp [T]
    linarith
  obtain ⟨CM, hCM, hmom⟩ := Divisor103.divisorSecondMoment k hk1
  refine ⟨CM * C, max 3 (Real.exp 1), by positivity, le_max_left _ _, ?_⟩
  intro N H α hN hH hHu
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hN0 : 0 < N := by linarith
  have hL1 : 1 ≤ Real.log N := by
    have hh := Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hN)
    simpa using hh
  have hL : 0 < Real.log N := by linarith
  have hH0 : 0 < H := by linarith
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hHk : H ^ k ≤ N := by
    have hh := pow_le_pow_left₀ hH0.le hHu k
    change H ^ k ≤ (N ^ (1 / (k : ℝ))) ^ k at hh
    rw [← Real.rpow_natCast (N ^ (1 / (k : ℝ))) k, ← Real.rpow_mul hN0.le,
      show 1 / (k : ℝ) * k = 1 by field_simp, Real.rpow_one] at hh
    exact hh
  have hHpred : H ^ (k - 1) ≤ N := by
    exact (pow_le_pow_right₀ hH (show k - 1 ≤ k by omega)).trans hHk
  let x := (c + 2) * H ^ (k - 1)
  have hx : 2 ≤ x := by
    have hp : 1 ≤ H ^ (k - 1) := one_le_pow₀ hH
    dsimp [x]
    nlinarith
  have hsum : (∑ h ∈ Icc 1 ⌊c * H ^ (k - 1)⌋₊, (divisorCount k h : ℝ) ^ 2) ≤
      CM * x * Real.log (Real.exp 1 * x) ^ l := by
    apply le_trans _ (hmom x hx)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · apply Finset.Icc_subset_Icc le_rfl
      apply Nat.floor_le_floor
      dsimp [x]
      nlinarith [pow_pos hH0 (k - 1)]
    · intro h _ _; exact sq_nonneg _
  have hxN : x ≤ (c + 2) * N := mul_le_mul_of_nonneg_left hHpred hc2.le
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 ≤ Real.log (Real.exp 1 * x) := Real.log_nonneg (by
    have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    nlinarith)
  have hlogx : Real.log (Real.exp 1 * x) ≤ T * Real.log N := by
    calc
      _ = 1 + Real.log x := by rw [Real.log_mul (Real.exp_pos 1).ne' hx0.ne', Real.log_exp]
      _ ≤ 1 + Real.log ((c + 2) * N) := add_le_add le_rfl (Real.log_le_log hx0 hxN)
      _ = 1 + Real.log (c + 2) + Real.log N := by rw [Real.log_mul hc2.ne' hN0.ne']; ring
      _ ≤ _ := by
        have hcLog : 0 ≤ Real.log (c + 2) := Real.log_nonneg (by linarith)
        dsimp [T]
        nlinarith
  have hsum' : (∑ h ∈ Icc 1 ⌊c * H ^ (k - 1)⌋₊, (divisorCount k h : ℝ) ^ 2) ≤
      CM * (c + 2) * T ^ l * H ^ (k - 1) * Real.log N ^ l := by
    calc
      _ ≤ CM * x * (T * Real.log N) ^ l := hsum.trans (by gcongr)
      _ = _ := by dsimp [x]; rw [mul_pow]; ring
  have hb := heavyCost_le F c N H D α hH hL
  have hHrel : H ^ k = H ^ (k - 1) * H := by
    conv_lhs => rw [show k = k - 1 + 1 by omega, pow_succ]
  have hcoef : (H + 1) / H ≤ 2 := (div_le_iff₀ hH0).mpr (by linarith)
  calc
    _ ≤ ((H + 1) / Real.log N ^ D *
        (CM * (c + 2) * T ^ l * H ^ (k - 1) * Real.log N ^ l)) / H ^ k :=
      hb.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsum' (by positivity)) (by positivity))
    _ = CM * (c + 2) * T ^ l * ((H + 1) / H) * Real.log N ^ (-D + (k : ℝ) ^ 2 - 1) := by
      rw [hHrel]
      have hl : (l : ℝ) = (k : ℝ) ^ 2 - 1 := by
        dsimp [l]
        rw [Nat.cast_sub (by nlinarith : 1 ≤ k ^ 2)]
        push_cast
        ring
      rw [show -D + (k : ℝ) ^ 2 - 1 = -D + (l : ℝ) by rw [hl]; ring,
        Real.rpow_add hL, Real.rpow_neg hL.le, Real.rpow_natCast]
      field_simp
      <;> ring
    _ ≤ CM * (c + 2) * T ^ l * 2 * Real.log N ^ (-D + (k : ℝ) ^ 2 - 1) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoef (by positivity)) (by positivity)
    _ = _ := by dsimp [C]; ring



/-- LEAF. Page 482 equation 8, normalized by H to the k.
Vaughan 1981 Lemma 2.2 supplies the rational linear sum estimate. -/
theorem leaf_light (F : ℤ[X]) (hF : Admissible F) (hk : 2 ≤ F.natDegree)
    (c D : ℝ) (hc : 0 < c) (hD : 0 < D) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H α : ℝ, N₀ ≤ N →
      1 ≤ H → H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∀ a : ℤ, ∀ q : ℕ, 0 < q → Nat.Coprime a.natAbs q →
      |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 →
      1 / H + divisorCost F c N H D α false ≤
        C * (1 / (q : ℝ) + 1 / H + (q : ℝ) / H ^ F.natDegree) *
          Real.log N ^ (D + 1) := by
  sorry

/-- The light cost has a trivial logarithmic bound for every phase. -/
theorem lightCost_trivial (F : ℤ[X]) (hk : 1 ≤ F.natDegree)
    (c N H D α : ℝ) (hc : 0 ≤ c) (hH : 1 ≤ H) (hL : 0 < Real.log N) :
    divisorCost F c N H D α false ≤ 2 * c * Real.log N ^ D := by
  classical
  let k := F.natDegree
  let s := (Icc 1 ⌊c * H ^ (k - 1)⌋₊).filter
    (fun h => (divisorCount k h : ℝ) ≤ Real.log N ^ D)
  have hH0 : 0 < H := by linarith
  have hcard : (s.card : ℝ) ≤ c * H ^ (k - 1) := by
    calc
      _ ≤ ((Icc 1 ⌊c * H ^ (k - 1)⌋₊).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
      _ = (⌊c * H ^ (k - 1)⌋₊ : ℝ) := by simp
      _ ≤ _ := Nat.floor_le (by positivity)
  have hterm : ∀ h ∈ s, (divisorCount k h : ℝ) * linearEnvelope H (α * h) ≤
      Real.log N ^ D * (H + 1) := by
    intro h hh
    have ht := (Finset.mem_filter.mp hh).2
    exact mul_le_mul ht (linearEnvelope_le H (α * h) (by linarith))
      (linearEnvelope_nonneg _ _) (Real.rpow_nonneg hL.le _)
  have hsum : (∑ h ∈ s, (divisorCount k h : ℝ) * linearEnvelope H (α * h)) ≤
      c * H ^ (k - 1) * (Real.log N ^ D * (H + 1)) := by
    calc
      _ ≤ ∑ _h ∈ s, Real.log N ^ D * (H + 1) := Finset.sum_le_sum hterm
      _ = (s.card : ℝ) * (Real.log N ^ D * (H + 1)) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hcard (by positivity)
  have hrel : H ^ k = H ^ (k - 1) * H := by
    conv_lhs => rw [show k = k - 1 + 1 by dsimp [k]; omega, pow_succ]
  change (∑ h ∈ s, (divisorCount k h : ℝ) * linearEnvelope H (α * h)) / H ^ k ≤ _
  apply (div_le_iff₀ (pow_pos hH0 k)).mpr
  rw [hrel]
  have ht : 0 ≤ c * H ^ (k - 1) * Real.log N ^ D := by positivity
  nlinarith

/-- The light rational estimate is elementary whenever its rational factor is at least one. -/
theorem lightCost_of_large_factor (F : ℤ[X]) (hk : 1 ≤ F.natDegree)
    (c N H D α : ℝ) (hc : 0 ≤ c) (hH : 1 ≤ H) (hD : 0 < D) (hL : 1 ≤ Real.log N)
    (R : ℝ) (hR : 1 ≤ R) :
    1 / H + divisorCost F c N H D α false ≤
      (2 * c + 1) * R * Real.log N ^ (D + 1) := by
  have hL0 : 0 < Real.log N := by linarith
  have ht := lightCost_trivial F hk c N H D α hc hH hL0
  have hHp : 0 < H := by linarith
  have hHinv : 1 / H ≤ 1 := (div_le_one hHp).mpr hH
  have hpow : 1 ≤ Real.log N ^ D := Real.one_le_rpow hL hD.le
  have hpow' : Real.log N ^ D ≤ Real.log N ^ (D + 1) :=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  calc
    _ ≤ (2 * c + 1) * Real.log N ^ D := by nlinarith
    _ ≤ (2 * c + 1) * Real.log N ^ (D + 1) := mul_le_mul_of_nonneg_left hpow' (by positivity)
    _ ≤ _ := by
      have hh := mul_nonneg (sub_nonneg.mpr hR)
        (show 0 ≤ (2 * c + 1) * Real.log N ^ (D + 1) by positivity)
      nlinarith

/-- Denominators at least H to the k satisfy the light estimate by the trivial bound. -/
theorem lightCost_large_denominator (F : ℤ[X]) (hk : 1 ≤ F.natDegree)
    (c N H D α : ℝ) (hc : 0 ≤ c) (hH : 1 ≤ H) (hD : 0 < D) (hL : 1 ≤ Real.log N)
    (q : ℕ) (hq : H ^ F.natDegree ≤ (q : ℝ)) :
    1 / H + divisorCost F c N H D α false ≤
      (2 * c + 1) * (1 / (q : ℝ) + 1 / H + (q : ℝ) / H ^ F.natDegree) *
        Real.log N ^ (D + 1) := by
  apply lightCost_of_large_factor F hk c N H D α hc hH hD hL
  have hHp : 0 < H := by linarith
  have hratio : 1 ≤ (q : ℝ) / H ^ F.natDegree := (le_div_iff₀ (pow_pos hHp _)).mpr (by simpa using hq)
  have ha : 0 ≤ 1 / (q : ℝ) := by positivity
  have hb : 0 ≤ 1 / H := by positivity
  linarith

/-- The denominator one case of the light estimate requires no rational approximation. -/
theorem lightCost_denominator_one (F : ℤ[X]) (hk : 1 ≤ F.natDegree)
    (c N H D α : ℝ) (hc : 0 ≤ c) (hH : 1 ≤ H) (hD : 0 < D) (hL : 1 ≤ Real.log N) :
    1 / H + divisorCost F c N H D α false ≤
      (2 * c + 1) * (1 + 1 / H + 1 / H ^ F.natDegree) * Real.log N ^ (D + 1) := by
  apply lightCost_of_large_factor F hk c N H D α hc hH hD hL
  have h1 : 0 ≤ 1 / H := by positivity
  have h2 : 0 ≤ 1 / H ^ F.natDegree := by positivity
  linarith

/-- The existing rational separation estimate transfers to the linear envelope. -/
theorem linearEnvelope_scaled_rational (H α : ℝ) (hH : 1 ≤ H) (a : ℤ) (q h : ℕ)
    (hq : 0 < q) (hh : 0 < h) (hcop : Nat.Coprime a.natAbs q)
    (happ : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) :
    linearEnvelope H (α * h) ≤ 2 * h * ((H + 1) / q + q) := by
  unfold linearEnvelope
  apply csSup_le
  · exact ⟨0, 0, 0, by norm_num; linarith, by simp [Kernel.T]⟩
  · rintro x ⟨start, len, hlen, rfl⟩
    have hb := norm_T_le_scaled_rational start len h hh a q hq hcop happ
    rw [mul_comm α (h : ℝ)]
    exact hb.trans (by gcongr)

/-- Termwise rational separation gives this weaker light bound.
The sum of h loses a power and does not prove the required equation 8. -/
theorem lightCost_scaled_rational (F : ℤ[X]) (c N H D α : ℝ)
    (hH : 1 ≤ H) (hL : 0 < Real.log N) (a : ℤ) (q : ℕ) (hq : 0 < q)
    (hcop : Nat.Coprime a.natAbs q) (happ : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2) :
    divisorCost F c N H D α false ≤
      (Real.log N ^ D * 2 * ((H + 1) / q + q) *
        ∑ h ∈ Icc 1 ⌊c * H ^ (F.natDegree - 1)⌋₊, (h : ℝ)) / H ^ F.natDegree := by
  classical
  let s := Icc 1 ⌊c * H ^ (F.natDegree - 1)⌋₊
  have hH0 : 0 < H := by linarith
  unfold divisorCost
  simp only [Bool.false_eq_true, ite_false]
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    _ ≤ ∑ h ∈ s.filter (fun h => (divisorCount F.natDegree h : ℝ) ≤ Real.log N ^ D),
        Real.log N ^ D * (2 * h * ((H + 1) / q + q)) := by
      apply Finset.sum_le_sum
      intro h hh
      obtain ⟨hs, ht⟩ := Finset.mem_filter.mp hh
      have hh0 : 0 < h := (Finset.mem_Icc.mp hs).1
      exact mul_le_mul ht (linearEnvelope_scaled_rational H α hH a q h hq hh0 hcop happ)
        (linearEnvelope_nonneg _ _) (Real.rpow_nonneg hL.le _)
    _ ≤ ∑ h ∈ s, Real.log N ^ D * (2 * h * ((H + 1) / q + q)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => by positivity)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      ring

/-- Exactly the cited Weyl Prop, assembled from equations 6 through 8.
CONDITIONAL ON the three Vaughan leaves for degree at least two. -/
theorem weyl (F : ℤ[X]) : Section2.WeylLemma F := by
  intro hF
  by_cases hdeg : F.natDegree = 1
  · exact weyl_of_natDegree_one F hdeg hF
  have hk : 2 ≤ F.natDegree := by have := hF.1; omega
  intro D hD
  obtain ⟨c, C0, N0, hc, hC0, hN0, hdiff⟩ := leaf_differencing F hF hk
  obtain ⟨CH, NH, hCH, hNH, hheavy⟩ := leaf_heavy F hF hk c D hc hD
  obtain ⟨CL, NL, hCL, hNL, hlight⟩ := leaf_light F hF hk c D hc hD
  let K := weylExponent F
  have hK : 0 < K := by dsimp [K, weylExponent]; positivity
  refine ⟨C0 * (CH + CL) ^ (1 / K), max N0 (max NH NL), by positivity,
    hN0.trans (le_max_left _ _), ?_⟩
  intro N H α hN hH hHu a q hq hcop happ
  have hN0' := (le_max_left N0 (max NH NL)).trans hN
  have hNH' := (le_max_left NH NL).trans ((le_max_right N0 (max NH NL)).trans hN)
  have hNL' := (le_max_right NH NL).trans ((le_max_right N0 (max NH NL)).trans hN)
  have hN3 := hN0.trans hN0'
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hH0 : 0 < H := by linarith
  let R := 1 / (q : ℝ) + 1 / H + (q : ℝ) / H ^ F.natDegree
  let T := Real.log N ^ (-2 * D + (F.natDegree : ℝ) ^ 2 - 2)
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hT : 0 ≤ T := Real.rpow_nonneg hL.le _
  have hheavy' := hheavy N H α hNH' hH hHu
  have hlight' := hlight N H α hNL' hH hHu a q hq hcop happ
  have heq : Real.log N ^ (-D + (F.natDegree : ℝ) ^ 2 - 1) =
      T * Real.log N ^ (D + 1) := by
    dsimp [T]
    rw [← Real.rpow_add hL]
    congr 1
    ring
  rw [heq] at hheavy'
  have hcost : 1 / H + divisorCost F c N H D α true + divisorCost F c N H D α false ≤
      (CH + CL) * (R + T) * Real.log N ^ (D + 1) := by
    have hCHT : CH * T ≤ (CH + CL) * (R + T) - CL * R := by nlinarith
    have hLH : 0 ≤ Real.log N ^ (D + 1) := Real.rpow_nonneg hL.le _
    dsimp [R] at *
    nlinarith [mul_le_mul_of_nonneg_right hCHT hLH]
  have hnon : 0 ≤ 1 / H + divisorCost F c N H D α true + divisorCost F c N H D α false := by
    have := divisorCost_nonneg F c N H D α true hH0
    have := divisorCost_nonneg F c N H D α false hH0
    positivity
  have hroot := Real.rpow_le_rpow hnon hcost (show 0 ≤ 1 / K by positivity)
  have hd := hdiff N H D α hN0' hH hHu
  calc
    _ ≤ C0 * H * ((CH + CL) * (R + T) * Real.log N ^ (D + 1)) ^ (1 / K) := by
      exact hd.trans (mul_le_mul_of_nonneg_left hroot (by positivity))
    _ = _ := by
      rw [Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hL.le]
      dsimp [R, T, K]
      rw [div_eq_mul_inv]
      ring

end
end LeanLab.Perelli1996.Decomp103b
