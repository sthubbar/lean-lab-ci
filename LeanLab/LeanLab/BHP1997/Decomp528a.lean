/-
P0069, pages 24 to 27 and 32 to 33. CODEX task528.
Explicit endpoint taper for the auxiliary Section 4 family.
The taper preserves local arithmetic estimates. It does not supply them.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Sifted312
import LeanLab.BHP1997.Decomp312c
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

namespace LeanLab.BHP1997.Decomp528a
open Classical Filter DecompC165b Decomp312c
open scoped BigOperators

/-- Pages 24 to 27, auxiliary smooth cutoff in the normalized variable. -/
noncomputable def taper (x t : ℝ) : ℝ :=
  Real.smoothTransition (4 * (t / x) - 2) *
    Real.smoothTransition (4 - 2 * (t / x))

/-- Pages 24 to 27, the explicitly tapered auxiliary coefficient family. -/
noncomputable def tapered (a : ℝ → ℕ → ℝ) (x : ℝ) (k : ℕ) : ℝ :=
  taper x k * a x k

/-- Pages 24 to 27, the endpoint taper takes values between zero and one. -/
theorem taper_bounds (x t : ℝ) : 0 ≤ taper x t ∧ taper x t ≤ 1 := by
  constructor
  · exact mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)
  · exact (mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _)
      (Real.smoothTransition.nonneg _)).trans (by simpa using Real.smoothTransition.le_one (4 - 2 * (t / x)))

/-- Pages 24 to 27, the taper is infinitely differentiable in the real index. -/
theorem taper_contDiff (x : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (taper x) := by
  unfold taper
  apply ContDiff.mul
  · exact (Real.smoothTransition.contDiff : ContDiff ℝ (⊤ : ℕ∞) _).comp (by fun_prop)
  · exact (Real.smoothTransition.contDiff : ContDiff ℝ (⊤ : ℕ∞) _).comp (by fun_prop)

/-- Pages 24 to 27, the taper is one on its central plateau. -/
theorem taper_one {x t : ℝ} (hx : 0 < x)
    (hlo : 3 * x / 4 ≤ t) (hhi : t ≤ 3 * x / 2) : taper x t = 1 := by
  have hlo' : 3 / 4 ≤ t / x := (le_div_iff₀ hx).mpr (by linarith)
  have hhi' : t / x ≤ 3 / 2 := (div_le_iff₀ hx).mpr (by linarith)
  rw [taper, Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 4 * (t / x) - 2),
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 4 - 2 * (t / x)), one_mul]

/-- Pages 24 to 27, the taper vanishes at and beyond both polynomial endpoints. -/
theorem taper_zero {x t : ℝ} (hx : 0 < x) (ht : t ≤ x / 2 ∨ 2 * x ≤ t) :
    taper x t = 0 := by
  rcases ht with ht | ht
  · have h : t / x ≤ 1 / 2 := (div_le_iff₀ hx).mpr (by linarith)
    rw [taper, Real.smoothTransition.zero_of_nonpos (by linarith : 4 * (t / x) - 2 ≤ 0), zero_mul]
  · have h : 2 ≤ t / x := (le_div_iff₀ hx).mpr (by linarith)
    rw [taper, Real.smoothTransition.zero_of_nonpos (by linarith : 4 - 2 * (t / x) ≤ 0), mul_zero]

/-- Pages 24 to 27, tapering preserves the same uniform divisor bound. -/
theorem tapered_divisor_bound {a : ℝ → ℕ → ℝ} {B C : ℝ}
    (ha : ∀ x k, |a x k| ≤ C * (k.divisors.card : ℝ) ^ B) :
    ∀ x k, |tapered a x k| ≤ C * (k.divisors.card : ℝ) ^ B := by
  intro x k
  rw [tapered, abs_mul, abs_of_nonneg (taper_bounds x k).1]
  exact (mul_le_of_le_one_left (abs_nonneg _) (taper_bounds x k).2).trans (ha x k)

/-- Pages 24 and 33, the reference interval lies in the taper plateau.
The fixed threshold three is sufficient. -/
theorem referenceWidth_lt_quarter {x : ℝ} (hx : 3 ≤ x) :
    referenceWidth x < x / 4 := by
  have hx0 : 0 < x := by linarith
  have hl : 1 ≤ Real.log x := by
    apply (Real.le_log_iff_exp_le hx0).2
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  have hp : 1 ≤ Real.log x ^ (1 / 3 : ℝ) := Real.one_le_rpow hl (by norm_num)
  have he : (4 : ℝ) < Real.exp 3 := by
    have := Real.add_one_lt_exp (by norm_num : (3 : ℝ) ≠ 0)
    linarith
  have hn : Real.exp (-3) < 1 / 4 := by
    rw [Real.exp_neg]
    simpa only [one_div] using (inv_lt_inv₀ (Real.exp_pos 3) (by norm_num : (0 : ℝ) < 4)).mpr he
  have hf : Real.exp (-3 * Real.log x ^ (1 / 3 : ℝ)) < 1 / 4 :=
    (Real.exp_le_exp.mpr (by linarith)).trans_lt hn
  unfold referenceWidth
  nlinarith [mul_lt_mul_of_pos_left hf hx0]

/-- Pages 24 and 33, the taper equals one at every index of I1. -/
theorem taper_one_reference {x : ℝ} (hx : 3 ≤ x) {k : ℕ}
    (hk : k ∈ Finset.Ioc ⌊x - referenceWidth x⌋₊ ⌊x⌋₊) : taper x k = 1 := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hk
  have hk0 : k ≠ 0 := by omega
  have hlo' : x - referenceWidth x < (k : ℝ) := (Nat.floor_lt' hk0).mp hlo
  have hhi' : (k : ℝ) ≤ x := (Nat.cast_le.mpr hhi).trans (Nat.floor_le (by linarith))
  apply taper_one (by linarith)
  · linarith [referenceWidth_lt_quarter hx]
  · linarith

/-- Pages 24 and 33, tapering leaves the entire I1 character mean unchanged. -/
theorem referenceAverage_tapered (a : ℝ → ℕ → ℝ) {x : ℝ} (hx : 3 ≤ x)
    {q : ℕ} (χ : DirichletCharacter ℂ q) :
    referenceAverage (tapered a) x χ = referenceAverage a x χ := by
  unfold referenceAverage
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [tapered, taper_one_reference hx hk, one_mul]

/-- Pages 24 and 33, tapering preserves precisely the given reference density.
CONDITIONAL on the arithmetic reference estimate for the original family. -/
theorem referenceDensity_tapered {u : ℝ} {a : ℝ → ℕ → ℝ}
    (ha : ReferenceDensity u a) : ReferenceDensity u (tapered a) := by
  intro A hA
  obtain ⟨C, X, h⟩ := ha A hA
  refine ⟨C, max X 3, ?_⟩
  intro x hx q hq hqx χ
  rw [referenceAverage_tapered a ((le_max_right _ _).trans hx)]
  exact h x ((le_max_left _ _).trans hx) q hq hqx χ

/-- Pages 24 to 27, a sublinear short interval eventually lies in the plateau. -/
theorem short_width_eventually {ε : ℝ} (hε : ε < 9 / 20) :
    ∀ᶠ x : ℝ in atTop, 2 * x ^ (11 / 20 + ε) ≤ x / 4 := by
  have hp : 0 < (1 : ℝ) - (11 / 20 + ε) := by linarith
  have ht := (tendsto_rpow_neg_atTop hp).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 8))
  filter_upwards [ht, eventually_gt_atTop (0 : ℝ)] with x hx hx0
  have he : x ^ (11 / 20 + ε) = x * x ^ (-((1 : ℝ) - (11 / 20 + ε))) := by
    calc
      _ = x ^ ((1 : ℝ) + -((1 : ℝ) - (11 / 20 + ε))) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hx0, Real.rpow_one]
  rw [he]
  nlinarith [mul_lt_mul_of_pos_left hx hx0]

/-- Pages 24 to 27, the taper is one on every sufficiently large short window. -/
theorem taper_one_left {ε : ℝ} (hε : ε < 9 / 20) :
    ∀ᶠ x : ℝ in atTop, ∀ k ∈ leftInterval ε x, taper x k = 1 := by
  filter_upwards [short_width_eventually hε, eventually_gt_atTop (0 : ℝ)] with x hx hx0 k hk
  obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hk
  have hk0 : k ≠ 0 := by omega
  have hlo' : x - 2 * x ^ (11 / 20 + ε) < (k : ℝ) := (Nat.floor_lt' hk0).mp hlo
  have hhi' : (k : ℝ) ≤ x := (Nat.cast_le.mpr hhi).trans (Nat.floor_le hx0.le)
  exact taper_one hx0 (by linarith) (by linarith)

/-- Pages 26 and 27, the tapered family agrees exactly on I.
This is an elementary zero error estimate, independent of all arithmetic inputs. -/
theorem shortApproximation_tapered {ε : ℝ} (hε : ε < 9 / 20)
    (a : ℝ → ℕ → ℝ) : ShortApproximation ε a (tapered a) := by
  obtain ⟨X, hX⟩ := eventually_atTop.mp (taper_one_left hε)
  intro A hA
  refine ⟨0, X, ?_⟩
  intro x hx
  have hs : (∑ k ∈ leftInterval ε x, |a x k - tapered a x k|) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    rw [tapered, hX x hx k hk, one_mul, sub_self, abs_zero]
  rw [hs]
  simp

/-- Page 26, the truncated Mobius coefficient, indexed by divisors of n.
At zero it is extended by zero since the paper only defines positive indices. -/
noncomputable def truncatedRough (n : ℕ) (z γ : ℝ) : ℝ :=
  ∑ d ∈ n.divisors.filter (fun d : ℕ => d ∣ Thm2.primorialBelow z ∧ (d : ℝ) ≤ γ),
    (ArithmeticFunction.moebius d : ℝ)

/-- Page 26, display 4.7, a finite convolution on its exact factor support.
The last factor r is the sifted or truncated rough coefficient. -/
noncomputable def finiteConvolution (M N : ℝ) (a b r : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ m ∈ k.divisors, ∑ n ∈ k.divisors,
    if M < m ∧ (m : ℝ) ≤ 2 * M ∧ N < n ∧ (n : ℝ) ≤ 2 * N ∧ m * n ∣ k
    then a m * b n * r (k / (m * n)) else 0

/-- Pages 26 and 27, the explicit tapered Mobius truncated family.
Its arithmetic density and analytic mean value are not part of the definition. -/
noncomputable def auxiliaryConvolution (M N z γ : ℝ → ℝ)
    (a b : ℝ → ℕ → ℝ) : ℝ → ℕ → ℝ :=
  tapered (fun x k => finiteConvolution (M x) (N x) (a x) (b x)
    (fun n => truncatedRough n (z x) (γ x)) k)

/-- Page 26, the absolute truncated Mobius coefficient is at most the divisor count. -/
theorem truncatedRough_bound (n : ℕ) (z γ : ℝ) :
    |truncatedRough n z γ| ≤ (n.divisors.card : ℝ) := by
  unfold truncatedRough
  calc
    _ ≤ ∑ d ∈ n.divisors.filter (fun d : ℕ => d ∣ Thm2.primorialBelow z ∧ (d : ℝ) ≤ γ),
        |(ArithmeticFunction.moebius d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ n.divisors.filter (fun d : ℕ => d ∣ Thm2.primorialBelow z ∧ (d : ℝ) ≤ γ), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    _ ≤ (n.divisors.card : ℝ) := by
      simpa using (Nat.cast_le.mpr (Finset.card_filter_le n.divisors
        (fun d : ℕ => d ∣ Thm2.primorialBelow z ∧ (d : ℝ) ≤ γ)) :
        ((n.divisors.filter (fun d : ℕ => d ∣ Thm2.primorialBelow z ∧ (d : ℝ) ≤ γ)).card : ℝ) ≤ _)

/-- Page 26, bounded factor coefficients give a uniform cubic divisor bound.
The extension at zero is included through its empty divisor set. -/
theorem finiteConvolution_bound (M N : ℝ) (a b r : ℕ → ℝ)
    (ha : ∀ m, |a m| ≤ 1) (hb : ∀ n, |b n| ≤ 1)
    (hr : ∀ l, |r l| ≤ (l.divisors.card : ℝ)) (k : ℕ) :
    |finiteConvolution M N a b r k| ≤ (k.divisors.card : ℝ) ^ (3 : ℕ) := by
  let τ : ℝ := k.divisors.card
  have hterm (m n : ℕ) (hm : m ∈ k.divisors) :
      |if M < m ∧ (m : ℝ) ≤ 2 * M ∧ N < n ∧ (n : ℝ) ≤ 2 * N ∧ m * n ∣ k
        then a m * b n * r (k / (m * n)) else 0| ≤ τ := by
    split_ifs with h
    · have hk : k ≠ 0 := (Nat.mem_divisors.mp hm).2
      have hc : (((k / (m * n)).divisors.card : ℕ) : ℝ) ≤ τ := by
        dsimp [τ]
        exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hk
          (Nat.div_dvd_of_dvd h.2.2.2.2))
      rw [abs_mul, abs_mul]
      have hab : |a m| * |b n| ≤ 1 :=
        (mul_le_mul (ha m) (hb n) (abs_nonneg _) (by norm_num)).trans_eq (by ring)
      exact ((mul_le_mul_of_nonneg_right hab (abs_nonneg _)).trans
        (by simpa using (hr (k / (m * n))).trans hc))
    · simpa only [abs_zero] using (Nat.cast_nonneg k.divisors.card : (0 : ℝ) ≤ (k.divisors.card : ℝ))
  unfold finiteConvolution
  calc
    _ ≤ ∑ m ∈ k.divisors, |∑ n ∈ k.divisors,
        if M < m ∧ (m : ℝ) ≤ 2 * M ∧ N < n ∧ (n : ℝ) ≤ 2 * N ∧ m * n ∣ k
        then a m * b n * r (k / (m * n)) else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ k.divisors, ∑ n ∈ k.divisors,
        |if M < m ∧ (m : ℝ) ≤ 2 * M ∧ N < n ∧ (n : ℝ) ≤ 2 * N ∧ m * n ∣ k
        then a m * b n * r (k / (m * n)) else 0| :=
      Finset.sum_le_sum (fun m hm => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _m ∈ k.divisors, ∑ _n ∈ k.divisors, τ :=
      Finset.sum_le_sum (fun m hm => Finset.sum_le_sum (fun n hn => hterm m n hm))
    _ = _ := by simp [τ]; ring

/-- Pages 26 and 27, the actual tapered truncated convolution has divisor exponent three. -/
theorem auxiliaryConvolution_divisor_bound (M N z γ : ℝ → ℝ)
    (a b : ℝ → ℕ → ℝ) (ha : ∀ x m, |a x m| ≤ 1) (hb : ∀ x n, |b x n| ≤ 1) :
    ∀ x k, |auxiliaryConvolution M N z γ a b x k| ≤ (k.divisors.card : ℝ) ^ (3 : ℝ) := by
  have hc : ∀ x k, |finiteConvolution (M x) (N x) (a x) (b x)
      (fun n => truncatedRough n (z x) (γ x)) k| ≤ 1 * (k.divisors.card : ℝ) ^ (3 : ℝ) := by
    intro x k
    simpa only [one_mul, Real.rpow_ofNat] using
      finiteConvolution_bound (M x) (N x) (a x) (b x)
        (fun n => truncatedRough n (z x) (γ x)) (ha x) (hb x)
        (fun n => truncatedRough_bound n (z x) (γ x)) k
  simpa only [auxiliaryConvolution, one_mul] using tapered_divisor_bound hc

/-- Page 26, the intermediate divisor band remaining after Mobius truncation. -/
noncomputable def roughBand (n : ℕ) (z γ : ℝ) : ℝ :=
  (((Nat.gcd n (Thm2.primorialBelow z)).divisors.filter
    (fun d : ℕ => γ ≤ (d : ℝ) ∧ (d : ℝ) < γ * z)).card : ℝ)

/-- Pages 26 and 27, the nonnegative convolution majorant for the intermediate band. -/
noncomputable def bandConvolution (M N : ℝ) (a b : ℕ → ℝ) (z γ : ℝ) (k : ℕ) : ℝ :=
  finiteConvolution M N (fun m => |a m|) (fun n => |b n|) (fun l => roughBand l z γ) k

/-- Page 26, the common divisor indexing agrees with the squarefree gcd indexing. -/
theorem truncatedRough_eq_gcd {n : ℕ} (hn : n ≠ 0) (z γ : ℝ) :
    truncatedRough n z γ =
      ∑ d ∈ (Nat.gcd n (Thm2.primorialBelow z)).divisors.filter
        (fun d : ℕ => (d : ℝ) ≤ γ), (ArithmeticFunction.moebius d : ℝ) := by
  have hg : Nat.gcd n (Thm2.primorialBelow z) ≠ 0 := by
    intro h
    exact hn (Nat.gcd_eq_zero_iff.mp h).1
  have he : n.divisors.filter (fun d => d ∣ Thm2.primorialBelow z) =
      (Nat.gcd n (Thm2.primorialBelow z)).divisors := by
    ext d
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hd, hdp⟩
      exact Nat.mem_divisors.mpr ⟨Nat.dvd_gcd (Nat.mem_divisors.mp hd).1 hdp, hg⟩
    · intro hd
      have h := (Nat.mem_divisors.mp hd).1
      exact ⟨Nat.mem_divisors.mpr ⟨h.trans (Nat.gcd_dvd_left _ _), hn⟩,
        h.trans (Nat.gcd_dvd_right _ _)⟩
  rw [truncatedRough, ← Finset.filter_filter, he]

/-- Page 26, the elementary intermediate band estimate for the concrete truncated coefficient.
The Hildebrand estimate for its summed size is a separate input. -/
theorem rough_truncation_band {n : ℕ} (hn : n ≠ 0) (z : ℝ) {γ : ℝ} (hγ : 1 ≤ γ) :
    |siftedWeight n ⌈z⌉₊ - truncatedRough n z γ| ≤ roughBand n z γ := by
  have hgs : Squarefree (Nat.gcd n (Thm2.primorialBelow z)) :=
    Squarefree.squarefree_of_dvd (Nat.gcd_dvd_right _ _) (primorial_squarefree z)
  rw [sifted_weight_primorial, truncatedRough_eq_gcd hn]
  exact squarefree_mobius_truncation _ hgs hγ (fun p hp hpd =>
    prime_lt_of_dvd_primorial hp (hpd.trans (Nat.gcd_dvd_right _ _)))

/-- Page 26, the actual finite convolution has the stated intermediate band majorant. -/
theorem finiteConvolution_truncation (M N : ℝ) (a b : ℕ → ℝ) (z : ℝ)
    {γ : ℝ} (hγ : 1 ≤ γ) (k : ℕ) :
    |finiteConvolution M N a b (fun l => siftedWeight l ⌈z⌉₊) k -
      finiteConvolution M N a b (fun l => truncatedRough l z γ) k| ≤
      bandConvolution M N a b z γ k := by
  let P (m n : ℕ) : Prop := M < m ∧ (m : ℝ) ≤ 2 * M ∧ N < n ∧ (n : ℝ) ≤ 2 * N ∧ m * n ∣ k
  let f (m n : ℕ) : ℝ := if P m n then a m * b n *
    (siftedWeight (k / (m * n)) ⌈z⌉₊ - truncatedRough (k / (m * n)) z γ) else 0
  have he : finiteConvolution M N a b (fun l => siftedWeight l ⌈z⌉₊) k -
      finiteConvolution M N a b (fun l => truncatedRough l z γ) k =
      ∑ m ∈ k.divisors, ∑ n ∈ k.divisors, f m n := by
    unfold finiteConvolution
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases h : P m n <;> simp [f, P] at h ⊢ <;> split_ifs <;> simp_all [mul_sub]
  rw [he]
  calc
    _ ≤ ∑ m ∈ k.divisors, |∑ n ∈ k.divisors, f m n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ k.divisors, ∑ n ∈ k.divisors, |f m n| :=
      Finset.sum_le_sum (fun m hm => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ bandConvolution M N a b z γ k := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro n hn
      by_cases h : P m n
      · have hk : k ≠ 0 := (Nat.mem_divisors.mp hm).2
        have hmn : m * n ∣ k := h.2.2.2.2
        have hl : k / (m * n) ≠ 0 := by
          intro heq
          have hh := Nat.mul_div_cancel' hmn
          rw [heq, mul_zero] at hh
          exact hk hh.symm
        change |f m n| ≤ if P m n then _ else 0
        dsimp only [f]
        rw [ite_eq_left h, ite_eq_left h, abs_mul, abs_mul]
        exact mul_le_mul_of_nonneg_left (rough_truncation_band hl z hγ) (by positivity)
      · change |f m n| ≤ if P m n then _ else 0
        simp [f, h]

/-- Pages 26 and 27, short band estimates give the required approximation
for the explicit tapered convolution. CONDITIONAL on that analytic band estimate. -/
theorem auxiliaryConvolution_shortApproximation {ε : ℝ} (hε : ε < 9 / 20)
    (M N z γ : ℝ → ℝ) (a b : ℝ → ℕ → ℝ)
    (hγ : ∀ᶠ x : ℝ in atTop, 1 ≤ γ x)
    (hband : ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x →
      (∑ k ∈ leftInterval ε x, bandConvolution (M x) (N x) (a x) (b x) (z x) (γ x) k) ≤
        C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :
    ShortApproximation ε
      (fun x k => finiteConvolution (M x) (N x) (a x) (b x) (fun l => siftedWeight l ⌈z x⌉₊) k)
      (auxiliaryConvolution M N z γ a b) := by
  obtain ⟨Xγ, hγ⟩ := eventually_atTop.mp hγ
  obtain ⟨Xt, ht⟩ := eventually_atTop.mp (taper_one_left hε)
  intro A hA
  obtain ⟨C, X, hC⟩ := hband A hA
  refine ⟨C, max X (max Xγ Xt), ?_⟩
  intro x hx
  have hxγ : Xγ ≤ x := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hx
  have hxt : Xt ≤ x := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hx
  calc
    _ ≤ ∑ k ∈ leftInterval ε x, bandConvolution (M x) (N x) (a x) (b x) (z x) (γ x) k := by
      apply Finset.sum_le_sum
      intro k hk
      rw [auxiliaryConvolution, tapered, ht x hxt k hk, one_mul]
      exact finiteConvolution_truncation _ _ _ _ _ (hγ x hxγ) k
    _ ≤ _ := hC x ((le_max_left _ _).trans hx)

/-- Pages 24 and 33, absolute coefficient error bounds the normalized character mean error. -/
theorem referenceAverage_error_le (a b : ℝ → ℕ → ℝ) {x : ℝ} (hx : 0 < x)
    {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ‖referenceAverage a x χ - referenceAverage b x χ‖ ≤
      (∑ k ∈ Finset.Ioc ⌊x - referenceWidth x⌋₊ ⌊x⌋₊, |a x k - b x k|) / referenceWidth x := by
  have he : referenceAverage a x χ - referenceAverage b x χ =
      (∑ k ∈ Finset.Ioc ⌊x - referenceWidth x⌋₊ ⌊x⌋₊,
        ((a x k - b x k : ℝ) : ℂ) * χ (k : ZMod q)) / (referenceWidth x : ℂ) := by
    unfold referenceAverage
    rw [← sub_div, ← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    push_cast
    ring
  rw [he, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (referenceWidth_pos hx)]
  apply div_le_div_of_nonneg_right _ (referenceWidth_pos hx).le
  calc
    _ ≤ ∑ k ∈ Finset.Ioc ⌊x - referenceWidth x⌋₊ ⌊x⌋₊,
        ‖((a x k - b x k : ℝ) : ℂ) * χ (k : ZMod q)‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_of_le_one_right (abs_nonneg _) (χ.norm_le_one _)

/-- Page 33, reference density transfers through a normalized absolute reference error.
CONDITIONAL on the density and reference error estimates. -/
theorem referenceDensity_of_error {u : ℝ} {a b : ℝ → ℕ → ℝ}
    (ha : ReferenceDensity u a)
    (herr : ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x →
      (∑ k ∈ Finset.Ioc ⌊x - referenceWidth x⌋₊ ⌊x⌋₊, |a x k - b x k|) ≤
        C * referenceWidth x * Real.log x ^ (-A)) : ReferenceDensity u b := by
  intro A hA
  obtain ⟨Ca, Xa, ha⟩ := ha A hA
  obtain ⟨Ce, Xe, he⟩ := herr A hA
  refine ⟨Ca + Ce, max Xa (max Xe 1), ?_⟩
  intro x hx q hq hqx χ
  have hxa : Xa ≤ x := (le_max_left _ _).trans hx
  have hxe : Xe ≤ x := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hx
  have hx1 : 1 ≤ x := (le_trans (le_max_right _ _) (le_max_right _ _)).trans hx
  have hx0 : 0 < x := by linarith
  have hw : referenceWidth x ≠ 0 := (referenceWidth_pos hx0).ne'
  have hd : ‖referenceAverage a x χ - referenceAverage b x χ‖ ≤ Ce * Real.log x ^ (-A) := by
    apply (referenceAverage_error_le a b hx0 χ).trans
    calc
      _ ≤ (Ce * referenceWidth x * Real.log x ^ (-A)) / referenceWidth x :=
        div_le_div_of_nonneg_right (he x hxe) (referenceWidth_pos hx0).le
      _ = _ := by field_simp
  calc
    _ = ‖(referenceAverage a x χ - Thm2.delta χ * u / Real.log x) -
        (referenceAverage a x χ - referenceAverage b x χ)‖ := by congr 1; ring
    _ ≤ ‖referenceAverage a x χ - Thm2.delta χ * u / Real.log x‖ +
        ‖referenceAverage a x χ - referenceAverage b x χ‖ := norm_sub_le _ _
    _ ≤ Ca * Real.log x ^ (-A) + Ce * Real.log x ^ (-A) :=
      add_le_add (ha x hxa q hq hqx χ) hd
    _ = _ := by ring

/-- Pages 26, 27 and 33, the explicit tapered convolution inherits the page 33 density.
CONDITIONAL on the sifted convolution density and the reference band sum. -/
theorem auxiliaryConvolution_referenceDensity {u : ℝ}
    (M N z γ : ℝ → ℝ) (a b : ℝ → ℕ → ℝ)
    (hγ : ∀ᶠ x : ℝ in atTop, 1 ≤ γ x)
    (hd : ReferenceDensity u
      (fun x k => finiteConvolution (M x) (N x) (a x) (b x) (fun l => siftedWeight l ⌈z x⌉₊) k))
    (hband : ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x →
      (∑ k ∈ Finset.Ioc ⌊x - referenceWidth x⌋₊ ⌊x⌋₊,
        bandConvolution (M x) (N x) (a x) (b x) (z x) (γ x) k) ≤
        C * referenceWidth x * Real.log x ^ (-A)) :
    ReferenceDensity u (auxiliaryConvolution M N z γ a b) := by
  apply referenceDensity_tapered
  apply referenceDensity_of_error hd
  obtain ⟨Xγ, hγ⟩ := eventually_atTop.mp hγ
  intro A hA
  obtain ⟨C, X, hC⟩ := hband A hA
  refine ⟨C, max X Xγ, ?_⟩
  intro x hx
  calc
    _ ≤ ∑ k ∈ Finset.Ioc ⌊x - referenceWidth x⌋₊ ⌊x⌋₊,
        bandConvolution (M x) (N x) (a x) (b x) (z x) (γ x) k :=
      Finset.sum_le_sum (fun k hk => finiteConvolution_truncation _ _ _ _ _
        (hγ x ((le_max_right _ _).trans hx)) k)
    _ ≤ _ := hC x ((le_max_left _ _).trans hx)

/-- Page 26 and display 3.1, general divisor bounded factor coefficients.
Two factor bounds of exponent B produce exponent 2B plus 3. -/
theorem finiteConvolution_bound_general (M N : ℝ) (a b r : ℕ → ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (ha : ∀ m, |a m| ≤ (m.divisors.card : ℝ) ^ B)
    (hb : ∀ n, |b n| ≤ (n.divisors.card : ℝ) ^ B)
    (hr : ∀ l, |r l| ≤ (l.divisors.card : ℝ)) (k : ℕ) :
    |finiteConvolution M N a b r k| ≤ (k.divisors.card : ℝ) ^ (2 * B + 3) := by
  by_cases hk : k = 0
  · subst k
    simp [finiteConvolution, Real.zero_rpow (by linarith : 2 * B + 3 ≠ 0)]
  let τ : ℝ := k.divisors.card
  have hτ : 0 < τ := by
    dsimp [τ]
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hk⟩
  have hsub {d : ℕ} (hd : d ∣ k) : (d.divisors.card : ℝ) ≤ τ := by
    dsimp [τ]
    exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hk hd)
  have hterm (m n : ℕ) (hm : m ∈ k.divisors) (hn : n ∈ k.divisors) :
      |if M < m ∧ (m : ℝ) ≤ 2 * M ∧ N < n ∧ (n : ℝ) ≤ 2 * N ∧ m * n ∣ k
        then a m * b n * r (k / (m * n)) else 0| ≤ τ ^ B * τ ^ B * τ := by
    split_ifs with h
    · have ham : |a m| ≤ τ ^ B :=
        (ha m).trans (Real.rpow_le_rpow (Nat.cast_nonneg _) (hsub (Nat.mem_divisors.mp hm).1) hB)
      have hbn : |b n| ≤ τ ^ B :=
        (hb n).trans (Real.rpow_le_rpow (Nat.cast_nonneg _) (hsub (Nat.mem_divisors.mp hn).1) hB)
      have hrk : |r (k / (m * n))| ≤ τ :=
        (hr _).trans (hsub (Nat.div_dvd_of_dvd h.2.2.2.2))
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul ham hbn (abs_nonneg _) (Real.rpow_nonneg hτ.le _))
        hrk (abs_nonneg _) (mul_nonneg (Real.rpow_nonneg hτ.le _) (Real.rpow_nonneg hτ.le _))
    · simp only [abs_zero]
      positivity
  have he : τ ^ (2 * B + 3) = τ ^ B * τ ^ B * τ * τ * τ := by
    calc
      _ = τ ^ ((((B + B) + 1) + 1) + 1) := by congr 1; ring
      _ = _ := by simp only [Real.rpow_add hτ, Real.rpow_one]
  unfold finiteConvolution
  calc
    _ ≤ ∑ m ∈ k.divisors, |∑ n ∈ k.divisors,
        if M < m ∧ (m : ℝ) ≤ 2 * M ∧ N < n ∧ (n : ℝ) ≤ 2 * N ∧ m * n ∣ k
        then a m * b n * r (k / (m * n)) else 0| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ m ∈ k.divisors, ∑ n ∈ k.divisors,
        |if M < m ∧ (m : ℝ) ≤ 2 * M ∧ N < n ∧ (n : ℝ) ≤ 2 * N ∧ m * n ∣ k
        then a m * b n * r (k / (m * n)) else 0| :=
      Finset.sum_le_sum (fun m hm => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _m ∈ k.divisors, ∑ _n ∈ k.divisors, τ ^ B * τ ^ B * τ :=
      Finset.sum_le_sum (fun m hm => Finset.sum_le_sum (fun n hn => hterm m n hm hn))
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      change τ * (τ * (τ ^ B * τ ^ B * τ)) = τ ^ (2 * B + 3)
      rw [he]
      ring

/-- Pages 26 and 27, the concrete tapered family retains general divisor bounded factors. -/
theorem auxiliaryConvolution_divisor_bound_general (M N z γ : ℝ → ℝ)
    (a b : ℝ → ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (ha : ∀ x m, |a x m| ≤ (m.divisors.card : ℝ) ^ B)
    (hb : ∀ x n, |b x n| ≤ (n.divisors.card : ℝ) ^ B) :
    ∀ x k, |auxiliaryConvolution M N z γ a b x k| ≤ (k.divisors.card : ℝ) ^ (2 * B + 3) := by
  have hc : ∀ x k, |finiteConvolution (M x) (N x) (a x) (b x)
      (fun n => truncatedRough n (z x) (γ x)) k| ≤
        1 * (k.divisors.card : ℝ) ^ (2 * B + 3) := by
    intro x k
    simpa only [one_mul] using finiteConvolution_bound_general (M x) (N x) (a x) (b x)
      (fun n => truncatedRough n (z x) (γ x)) hB (ha x) (hb x)
      (fun n => truncatedRough_bound n (z x) (γ x)) k
  simpa only [auxiliaryConvolution, one_mul] using tapered_divisor_bound hc

/-- Pages 26 and 27, the concrete auxiliary block at the paper scales w and gamma. -/
noncomputable def section4Block (ε m n : ℝ) (a b : ℝ → ℕ → ℝ) : ℝ → ℕ → ℝ :=
  auxiliaryConvolution (fun x => x ^ m) (fun x => x ^ n)
    (fun x => Real.exp (Real.log x ^ (9 / 10 : ℝ))) (fun x => x ^ (ε / 12)) a b

/-- LEAF. P0069 page 24 display 4.1 and pages 26 and 27 display 4.7.
The mean value is only for the concrete smooth Mobius truncated block.
Use display 4.8 or the repaired grouping max m n at most 0.46,
as justified by Lemma1112.lemma12_339_ok, not the larger printed 4.9 range.
The factor coefficients obey the paper divisor bound 3.1 at fixed exponent B.
Both signs of height are retained. No density, band sum, minorant or
discarded region classification is asserted. OPEN. -/
theorem leaf_section4Block_mean_value (h4 : Thm4.Theorem4Paper) (B : ℝ) (hB : 0 ≤ B) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ m n : ℝ, 0 ≤ m → 0 ≤ n →
      (max (0.45 : ℝ) m + max (0.225 : ℝ) n ≤ 0.775 ∨ max m n ≤ 0.46) →
      ∀ a b : ℝ → ℕ → ℝ,
        (∀ x k, |a x k| ≤ (k.divisors.card : ℝ) ^ B) →
        (∀ x k, |b x k| ≤ (k.divisors.card : ℝ) ^ B) →
        MeanValue41 ε (section4Block ε m n a b) := by
  sorry

/-- Pages 26, 27 and 33, the concrete tapered block construction.
CONDITIONAL on leaf_section4Block_mean_value, the actual reference density
and the short and reference intermediate band sums.
The elementary divisor, taper and normalization steps are all proved.
This is a single block, not the lower Buchstab minorant construction. -/
theorem section4Block_supply (h4 : Thm4.Theorem4Paper) (B : ℝ) (hB : 0 ≤ B) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ m n : ℝ, 0 ≤ m → 0 ≤ n →
      (max (0.45 : ℝ) m + max (0.225 : ℝ) n ≤ 0.775 ∨ max m n ≤ 0.46) →
      ∀ a b : ℝ → ℕ → ℝ,
        (∀ x k, |a x k| ≤ (k.divisors.card : ℝ) ^ B) →
        (∀ x k, |b x k| ≤ (k.divisors.card : ℝ) ^ B) →
      ∀ u : ℝ,
        ReferenceDensity u (fun x k => finiteConvolution (x ^ m) (x ^ n) (a x) (b x)
          (fun l => siftedWeight l ⌈Real.exp (Real.log x ^ (9 / 10 : ℝ))⌉₊) k) →
        (∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x →
          (∑ k ∈ leftInterval ε x, bandConvolution (x ^ m) (x ^ n) (a x) (b x)
            (Real.exp (Real.log x ^ (9 / 10 : ℝ))) (x ^ (ε / 12)) k) ≤
            C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) →
        (∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x →
          (∑ k ∈ Finset.Ioc ⌊x - referenceWidth x⌋₊ ⌊x⌋₊,
            bandConvolution (x ^ m) (x ^ n) (a x) (b x)
              (Real.exp (Real.log x ^ (9 / 10 : ℝ))) (x ^ (ε / 12)) k) ≤
            C * referenceWidth x * Real.log x ^ (-A)) →
        (∀ x k, |section4Block ε m n a b x k| ≤ (k.divisors.card : ℝ) ^ (2 * B + 3)) ∧
        MeanValue41 ε (section4Block ε m n a b) ∧
        ReferenceDensity u (section4Block ε m n a b) ∧
        ShortApproximation ε
          (fun x k => finiteConvolution (x ^ m) (x ^ n) (a x) (b x)
            (fun l => siftedWeight l ⌈Real.exp (Real.log x ^ (9 / 10 : ℝ))⌉₊) k)
          (section4Block ε m n a b) := by
  obtain ⟨η, hη, hm⟩ := leaf_section4Block_mean_value h4 B hB
  refine ⟨min η (1 / 10), lt_min hη (by norm_num), ?_⟩
  intro ε hε hεη m n hm0 hn0 hgroup a b ha hb u hd hshort href
  have hεη' : ε < η := hεη.trans_le (min_le_left _ _)
  have hεsmall : ε < 9 / 20 := by
    have h := hεη.trans_le (min_le_right _ _)
    linarith
  have hγ : ∀ᶠ x : ℝ in atTop, 1 ≤ x ^ (ε / 12) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact Real.one_le_rpow hx (by positivity)
  refine ⟨auxiliaryConvolution_divisor_bound_general _ _ _ _ a b hB ha hb,
    hm ε hε hεη' m n hm0 hn0 hgroup a b ha hb, ?_, ?_⟩
  · exact auxiliaryConvolution_referenceDensity _ _ _ _ a b hγ hd href
  · exact auxiliaryConvolution_shortApproximation hεsmall _ _ _ _ a b hγ hshort

/-- Page 26, gamma equal to one retains precisely the unit Mobius divisor. -/
theorem truncatedRough_at_one {n : ℕ} (hn : n ≠ 0) (z : ℝ) :
    truncatedRough n z 1 = 1 := by
  have he : n.divisors.filter
      (fun d : ℕ => d ∣ Thm2.primorialBelow z ∧ (d : ℝ) ≤ 1) = {1} := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hd, hdp, hd1⟩
      have hpos := Nat.pos_of_mem_divisors hd
      have hle : d ≤ 1 := by exact_mod_cast hd1
      omega
    · intro hd
      subst d
      exact ⟨Nat.one_mem_divisors.mpr hn, one_dvd _, by norm_num⟩
  rw [truncatedRough, he]
  simp

/-- Pages 26 and 27, a concrete nonzero auxiliary coefficient and its zero extension.
Both factor ranges are nonempty. The taper equals one at the tested positive index. -/
theorem auxiliaryConvolution_nonzero_instance :
    auxiliaryConvolution (fun _ => 3 / 4) (fun _ => 3 / 4) (fun _ => 4) (fun _ => 1)
      (fun _ _ => 1) (fun _ _ => 1) 6 6 = 1 ∧
    auxiliaryConvolution (fun _ => 3 / 4) (fun _ => 3 / 4) (fun _ => 4) (fun _ => 1)
      (fun _ _ => 1) (fun _ _ => 1) 6 0 = 0 := by
  have hd : (6 : ℕ).divisors = {1, 2, 3, 6} := by decide
  have hf : finiteConvolution (3 / 4) (3 / 4) (fun _ => 1) (fun _ => 1)
      (fun n => truncatedRough n 4 1) 6 = 1 := by
    norm_num [finiteConvolution, hd, truncatedRough_at_one]
  constructor
  · have ht : taper 6 6 = 1 := taper_one (by norm_num) (by norm_num) (by norm_num)
    simpa [auxiliaryConvolution, tapered, ht] using hf
  · simp [auxiliaryConvolution, tapered, finiteConvolution]

/-- Page 26 display 4.7, a nonzero block at the actual paper scales.
This is a consistency instance, not an asymptotic density assertion. -/
theorem section4Block_nonzero_instance {ε : ℝ} (hε : 0 ≤ ε) :
    section4Block ε (1 / 4) (1 / 4) (fun _ _ => 1) (fun _ _ => 1) 16 12 = 2 := by
  have hr : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by norm_num
  have hγ : 1 ≤ (16 : ℝ) ^ (ε / 12) :=
    Real.one_le_rpow (by norm_num) (by positivity)
  have hone : truncatedRough 1 (Real.exp (Real.log 16 ^ (9 / 10 : ℝ)))
      ((16 : ℝ) ^ (ε / 12)) = 1 := by
    simp [truncatedRough, Finset.sum_filter, hγ]
  have hd : (12 : ℕ).divisors = {1, 2, 3, 4, 6, 12} := by decide
  have hf : finiteConvolution 2 2 (fun _ => 1) (fun _ => 1)
      (fun n => truncatedRough n (Real.exp (Real.log 16 ^ (9 / 10 : ℝ)))
        ((16 : ℝ) ^ (ε / 12))) 12 = 2 := by
    norm_num [finiteConvolution, hd, hone]
  have ht : taper 16 12 = 1 := taper_one (by norm_num) (by norm_num) (by norm_num)
  simpa only [section4Block, auxiliaryConvolution, tapered, hr, Nat.cast_ofNat, ht, one_mul] using hf

end LeanLab.BHP1997.Decomp528a
