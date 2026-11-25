/-
MMS https://arxiv.org/abs/1610.02017v2, page 12.
S144 split of minor_arc_main, major_arc_reduction and edge_sieve_upper from Feed1122Decomp420d.
minor_arc_main_of_leaves and major_arc_reduction_of_leaves are sorry free here, and
conditional only on the Task571 limit leaves through referenceMean_eventually_bounded.
The reference mean factor is removed with referenceMean_eventually_bounded, and
the q below log to the 5A reduction is split into the lcm ratio step, the count of
n not coprime to q, and the plain count of one class modulo W.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Feed1122Decomp420d

namespace LeanLab.Ternary.MMS.Task420
open Finset

/-- Abel summation identity for the partial summation step of MMS page 12. Derived. -/
theorem abel_identity (g : ℕ → ℂ) (z : ℂ) (K : ℕ) :
    (z - 1) * ∑ k ∈ range (K + 1), g k * z ^ k =
      g K * z ^ (K + 1) - g 0 - ∑ k ∈ range K, (g (k + 1) - g k) * z ^ (k + 1) := by
  induction K with
  | zero => simp; ring
  | succ K ih =>
    rw [sum_range_succ, mul_add, ih, sum_range_succ]
    ring

/-- Total variation of a monotone sequence telescopes. Derived from Mathlib sum_range_sub. -/
theorem tv_monotone (f : ℕ → ℝ) (hf : Monotone f) (K : ℕ) :
    ∑ k ∈ range K, |f (k + 1) - f k| = f K - f 0 := by
  rw [← sum_range_sub]
  apply sum_congr rfl
  intro k _
  exact abs_of_nonneg (sub_nonneg.mpr (hf (Nat.le_succ k)))

/-- Total variation of an antitone sequence telescopes. Derived from tv_monotone. -/
theorem tv_antitone (f : ℕ → ℝ) (hf : Antitone f) (K : ℕ) :
    ∑ k ∈ range K, |f (k + 1) - f k| = f 0 - f K := by
  have := tv_monotone (fun k => - f k) (fun a b h => neg_le_neg (hf h)) K
  rw [show f 0 - f K = -f K - -f 0 by ring, ← this]
  apply sum_congr rfl
  intro k _
  rw [← abs_neg]; congr 1; ring

/-- A monotone or antitone sequence with values in zero to one has total variation at most one. Derived. -/
theorem tv_mono_or_anti (f : ℕ → ℝ) (hf : Monotone f ∨ Antitone f)
    (h0 : ∀ k, 0 ≤ f k) (h1 : ∀ k, f k ≤ 1) (K : ℕ) :
    ∑ k ∈ range K, |f (k + 1) - f k| ≤ 1 := by
  rcases hf with hf | hf
  · rw [tv_monotone f hf]; linarith [h0 0, h1 K]
  · rw [tv_antitone f hf]; linarith [h0 K, h1 0]

/-- Total variation of a product of sequences with values in zero to one. Derived. -/
theorem tv_prod (f₁ f₂ : ℕ → ℝ) (h0 : ∀ k, 0 ≤ f₁ k) (h1 : ∀ k, f₁ k ≤ 1)
    (h0' : ∀ k, 0 ≤ f₂ k) (h1' : ∀ k, f₂ k ≤ 1) (K : ℕ) :
    ∑ k ∈ range K, |f₁ (k + 1) * f₂ (k + 1) - f₁ k * f₂ k| ≤
      ∑ k ∈ range K, |f₁ (k + 1) - f₁ k| + ∑ k ∈ range K, |f₂ (k + 1) - f₂ k| := by
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro k _
  have e : f₁ (k + 1) * f₂ (k + 1) - f₁ k * f₂ k =
      (f₁ (k + 1) - f₁ k) * f₂ (k + 1) + f₁ k * (f₂ (k + 1) - f₂ k) := by ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_nonneg (h0' _)]
    exact mul_le_of_le_one_right (abs_nonneg _) (h1' _)
  · rw [abs_mul, abs_of_nonneg (h0 _)]
    exact mul_le_of_le_one_left (abs_nonneg _) (h1 _)

/-- Partial summation bound used on MMS page 12: weights in zero to one with total variation at most two give a sum of size at most four over the norm of z minus one. Derived. -/
theorem abel_bound (g : ℕ → ℝ) (z : ℂ) (hz : ‖z‖ = 1) (K : ℕ)
    (h0 : ∀ k, 0 ≤ g k) (h1 : ∀ k, g k ≤ 1)
    (htv : ∑ k ∈ range K, |g (k + 1) - g k| ≤ 2) :
    ‖∑ k ∈ range (K + 1), ((g k : ℝ) : ℂ) * z ^ k‖ * ‖z - 1‖ ≤ 4 := by
  rw [mul_comm, ← norm_mul, abel_identity]
  refine (norm_sub_le _ _).trans ?_
  refine (add_le_add (norm_sub_le _ _) (norm_sum_le _ _)).trans ?_
  have hp : ∀ n : ℕ, ‖z ^ n‖ = 1 := fun n => by rw [norm_pow, hz, one_pow]
  have hs : ∑ k ∈ range K, ‖(((g (k + 1) : ℝ) : ℂ) - ((g k : ℝ) : ℂ)) * z ^ (k + 1)‖ =
      ∑ k ∈ range K, |g (k + 1) - g k| := by
    apply sum_congr rfl; intro k _
    rw [norm_mul, hp, mul_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [hs, norm_mul, hp, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (h0 _), abs_of_nonneg (h0 _)]
  linarith [h1 K, h1 0]

/-- Proved step, MMS page 12, case q at least log to the 5A, the partial summation step.
Writing n as n0 plus W k, multiplying the sum by e of W gamma minus one telescopes it
into two boundary terms and the differences of g, and g takes values in zero to one
and is a product of a monotone rise and a monotone fall, so its total variation is at
most two. Originally class MEDIUM, now proved from abel_bound. -/
theorem progression_partial_summation (ε θ x : ℝ) (c : ℕ) (γ : ℝ) :
    ‖∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]),
        ((edgeCutoff ε θ x n : ℝ) : ℂ) * e (n * γ)‖ * ‖e ((wheel x : ℝ) * γ) - 1‖ ≤ 4 := by
  set S := (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]) with hS
  set W := wheel x with hWdef
  have hW : 0 < W := wheel_pos x
  rcases S.eq_empty_or_nonempty with hE | hne
  · rw [hE, sum_empty, norm_zero, zero_mul]; norm_num
  set n0 := S.min' hne with hn0
  have hn0S : n0 ∈ S := S.min'_mem hne
  set M := ⌊x + x ^ θ⌋₊ with hM
  have hmemS : ∀ n, n ∈ S ↔ ⌈x - x ^ θ / 3⌉₊ ≤ n ∧ n ≤ M ∧ n ≡ c [MOD W] := by
    intro n
    simp only [hS, ints, mem_filter, mem_Icc, hM, hWdef, and_assoc]
  obtain ⟨hn0lo, hn0hi, hn0c⟩ := (hmemS n0).mp hn0S
  set K := (M - n0) / W with hK
  have hSimg : S = (range (K + 1)).image (fun k => n0 + W * k) := by
    ext n
    simp only [mem_image, mem_range]
    constructor
    · intro hn
      obtain ⟨hlo, hhi, hc⟩ := (hmemS n).mp hn
      have hge : n0 ≤ n := S.min'_le n hn
      have hmod : n0 % W = n % W := (hn0c.trans hc.symm)
      have hdvd : W ∣ n - n0 := (Nat.modEq_iff_dvd' hge).mp hmod
      obtain ⟨k, hk⟩ := hdvd
      refine ⟨k, ?_, by omega⟩
      have : W * k ≤ M - n0 := by omega
      have : k ≤ (M - n0) / W := (Nat.le_div_iff_mul_le hW).mpr (by linarith [mul_comm W k])
      omega
    · rintro ⟨k, hk, rfl⟩
      refine (hmemS _).mpr ⟨le_trans hn0lo (Nat.le_add_right _ _), ?_, ?_⟩
      · have h1 : W * k ≤ W * ((M - n0) / W) := Nat.mul_le_mul_left _ (by omega)
        have h2 : W * ((M - n0) / W) ≤ M - n0 := Nat.mul_div_le _ _
        omega
      · have : n0 + W * k ≡ n0 [MOD W] := by
          simp [Nat.ModEq, Nat.add_mul_mod_self_left]
        exact this.trans hn0c
  have hinj : Set.InjOn (fun k => n0 + W * k) (range (K + 1) : Set ℕ) := by
    intro i _ j _ hij
    have : W * i = W * j := by simpa using hij
    exact Nat.eq_of_mul_eq_mul_left hW this
  rw [hSimg, sum_image (fun i hi j hj h => hinj hi hj h)]
  have hek : ∀ k : ℕ, e (((n0 + W * k : ℕ) : ℝ) * γ) = e (n0 * γ) * e (W * γ) ^ k := by
    intro k; unfold e
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]; congr 1; push_cast; ring
  set d := ε * x ^ θ with hd
  set f₁ : ℕ → ℝ := fun k => Real.smoothTransition ((((n0 + W * k : ℕ) : ℝ) - (x - x ^ θ / 3)) / d)
  set f₂ : ℕ → ℝ := fun k => Real.smoothTransition ((x + x ^ θ - ((n0 + W * k : ℕ) : ℝ)) / d)
  have hg : ∀ k, edgeCutoff ε θ x ((n0 + W * k : ℕ) : ℝ) = f₁ k * f₂ k := fun k => rfl
  have hsum : ∑ k ∈ range (K + 1), ((edgeCutoff ε θ x ((n0 + W * k : ℕ) : ℝ) : ℝ) : ℂ) *
      e (((n0 + W * k : ℕ) : ℝ) * γ) =
      e (n0 * γ) * ∑ k ∈ range (K + 1), (((f₁ k * f₂ k : ℝ)) : ℂ) * e (W * γ) ^ k := by
    rw [mul_sum]; apply sum_congr rfl; intro k _; rw [hg, hek]; ring
  rw [hsum, norm_mul, norm_e, one_mul]
  have hcast : ∀ i j : ℕ, i ≤ j → (((n0 + W * i : ℕ) : ℝ)) ≤ ((n0 + W * j : ℕ) : ℝ) := by
    intro i j hij; exact_mod_cast Nat.add_le_add_left (Nat.mul_le_mul_left _ hij) _
  have hm₁ : Monotone f₁ ∨ Antitone f₁ := by
    rcases le_total 0 d with hd0 | hd0
    · left; intro i j hij
      exact Real.smoothTransition.monotone
        (div_le_div_of_nonneg_right (by linarith [hcast i j hij]) hd0)
    · right; intro i j hij
      exact Real.smoothTransition.monotone
        (div_le_div_of_nonpos_of_le hd0 (by linarith [hcast i j hij]))
  have hm₂ : Monotone f₂ ∨ Antitone f₂ := by
    rcases le_total 0 d with hd0 | hd0
    · right; intro i j hij
      exact Real.smoothTransition.monotone
        (div_le_div_of_nonneg_right (by linarith [hcast i j hij]) hd0)
    · left; intro i j hij
      exact Real.smoothTransition.monotone
        (div_le_div_of_nonpos_of_le hd0 (by linarith [hcast i j hij]))
  have a0 : ∀ k, 0 ≤ f₁ k := fun k => Real.smoothTransition.nonneg _
  have a1 : ∀ k, f₁ k ≤ 1 := fun k => Real.smoothTransition.le_one _
  have b0 : ∀ k, 0 ≤ f₂ k := fun k => Real.smoothTransition.nonneg _
  have b1 : ∀ k, f₂ k ≤ 1 := fun k => Real.smoothTransition.le_one _
  apply abel_bound (fun k => f₁ k * f₂ k) _ (norm_e _) K
    (fun k => mul_nonneg (a0 k) (b0 k))
    (fun k => (mul_le_mul (a1 k) (b1 k) (b0 k) zero_le_one).trans (by norm_num))
  refine (tv_prod f₁ f₂ a0 a1 b0 b1 K).trans ?_
  linarith [tv_mono_or_anti f₁ hm₁ a0 a1 K, tv_mono_or_anti f₂ hm₂ b0 b1 K]

/-- Proved step, MMS page 12: e of y minus one has size at least four times the
distance from y to an integer k within one half. From Mathlib
Complex.norm_exp_I_mul_ofReal_sub_one and the Jordan inequality Real.mul_le_sin. -/
theorem e_sub_one_lower (y : ℝ) (k : ℤ) (hk : |y - k| ≤ 1 / 2) :
    4 * |y - k| ≤ ‖e y - 1‖ := by
  have he : e y = Complex.exp (Complex.I * ((2 * Real.pi * y : ℝ) : ℂ)) := by
    unfold e; congr 1; push_cast; ring
  rw [he, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs]
  have hs : Real.sin (Real.pi * (y - k)) = (-1) ^ k * Real.sin (2 * Real.pi * y / 2) := by
    rw [show Real.pi * (y - k) = 2 * Real.pi * y / 2 - k * Real.pi by ring]
    exact Real.sin_sub_int_mul_pi _ _
  have hpm : |((-1 : ℝ) ^ k)| = 1 := by
    rw [abs_zpow, abs_neg, abs_one, one_zpow]
  have hs' : |Real.sin (2 * Real.pi * y / 2)| = |Real.sin (Real.pi * (y - k))| := by
    rw [hs, abs_mul, hpm, one_mul]
  rw [abs_mul, hs', abs_of_pos (by norm_num : (0:ℝ) < 2)]
  set t := y - (k : ℝ) with ht
  have hpi := Real.pi_pos
  have key : 2 * |t| ≤ |Real.sin (Real.pi * t)| := by
    have h1 : 0 ≤ Real.pi * |t| := by positivity
    have h2 : Real.pi * |t| ≤ Real.pi / 2 := by nlinarith
    have j := Real.mul_le_sin h1 h2
    have hj : 2 / Real.pi * (Real.pi * |t|) = 2 * |t| := by field_simp
    rw [hj] at j
    rcases le_or_gt 0 t with h | h
    · rw [abs_of_nonneg h] at j ⊢
      exact j.trans (le_abs_self _)
    · rw [abs_of_neg h] at j ⊢
      rw [show Real.pi * t = -(Real.pi * -t) by ring, Real.sin_neg, abs_neg]
      exact j.trans (le_abs_self _)
  linarith

/-- Proved step, MMS page 12, case q at least log to the 5A, the diophantine step.
Since q is at least log to the 5A and W is at most log x, the fraction W a over q
is not an integer and lies at distance at least one over q from the integers, and
the approximation error W times gamma minus a over q is at most W over q Q, so
e of W gamma minus one has size at least about one over q, while W q is at most
W x to the 2 theta minus 1, which is o of x to the theta as theta is below one.
Originally class MEDIUM, now proved from e_sub_one_lower and wheel_le_log. -/
theorem minor_arc_dioph (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1) (A : ℝ) (hA : 1 ≤ A) :
    ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ γ : ℝ, ∀ a : ℤ, ∀ q : ℕ, 0 < q →
        Int.gcd a q = 1 → Real.log x ^ (5 * A) ≤ q →
        (q : ℝ) ≤ x ^ (2 * θ - 1) / Real.log x ^ (5 * A) →
        |(q : ℝ) * γ - a| < 1 / (x ^ (2 * θ - 1) / Real.log x ^ (5 * A)) →
        4 * (wheel x : ℝ) ≤ η * x ^ θ * ‖e ((wheel x : ℝ) * γ) - 1‖ := by
  intro η hη
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp
    ((Real.tendsto_log_atTop.eventually_ge_atTop (max 2 (2 / η))).and
      (Filter.eventually_ge_atTop (Real.exp 1)))
  refine ⟨X₀, fun x hx γ a q hq0 hgcd hbig hqQ happ => ?_⟩
  obtain ⟨hLB, hxe⟩ := hX₀ x hx
  set L := Real.log x with hLdef
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hLB
  have hLη : 2 / η ≤ L := (le_max_right _ _).trans hLB
  have hx1 : 1 ≤ x := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hxe
  have hx0 : 0 < x := by linarith
  have hW := wheel_le_log hxe
  have hW0 : (0 : ℝ) < wheel x := by exact_mod_cast wheel_pos x
  have h5 : L ^ (5 : ℕ) ≤ L ^ (5 * A) := by
    have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ L)
      (by linarith : (5 : ℝ) ≤ 5 * A)
    simpa using this
  have hP : 0 < L ^ (5 * A) := Real.rpow_pos_of_pos (by linarith) _
  have hL5 : 16 * L ≤ L ^ (5 : ℕ) := by
    have : (2:ℝ) ^ 4 ≤ L ^ 4 := pow_le_pow_left₀ (by norm_num) hL2 4
    nlinarith
  set Q := x ^ (2 * θ - 1) / L ^ (5 * A) with hQ
  have hqL5 : L ^ (5 : ℕ) ≤ q := h5.trans hbig
  have hQq : L ^ (5 : ℕ) ≤ Q := hqL5.trans hqQ
  have hQ0 : 0 < Q := by nlinarith
  have hWq : (wheel x : ℝ) < q := by nlinarith
  -- the diophantine step
  set r := (wheel x : ℝ) * γ - (round ((wheel x : ℝ) * γ) : ℤ) with hr
  set k : ℤ := round ((wheel x : ℝ) * γ) with hk
  have hm0 : (wheel x : ℤ) * a - k * q ≠ 0 := by
    intro h0
    have hdvd : (q : ℤ) ∣ (wheel x : ℤ) * a := ⟨k, by linarith⟩
    have hg : Int.gcd (q : ℤ) a = 1 := by rw [Int.gcd_comm]; exact hgcd
    have h1 : (q : ℤ) ∣ (wheel x : ℤ) := Int.dvd_of_dvd_mul_left_of_gcd_one hdvd hg
    have h2 : q ∣ wheel x := Int.natCast_dvd_natCast.mp h1
    have h3 : q ≤ wheel x := Nat.le_of_dvd (wheel_pos x) h2
    have : (q : ℝ) ≤ wheel x := by exact_mod_cast h3
    linarith
  have hm1 : (1 : ℝ) ≤ |(((wheel x : ℤ) * a - k * q : ℤ) : ℝ)| := by
    have : (1 : ℤ) ≤ |(wheel x : ℤ) * a - k * q| := Int.one_le_abs hm0
    exact_mod_cast this
  have hident : (q : ℝ) * r = (wheel x : ℝ) * ((q : ℝ) * γ - a) +
      (((wheel x : ℤ) * a - k * q : ℤ) : ℝ) := by
    rw [hr]; push_cast; ring
  have hsmall : |(wheel x : ℝ) * ((q : ℝ) * γ - a)| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos hW0]
    have hlt : |(q : ℝ) * γ - a| ≤ 1 / Q := happ.le
    have h16 : (wheel x : ℝ) / Q ≤ 1 / 2 := by
      rw [div_le_iff₀ hQ0]; nlinarith
    calc (wheel x : ℝ) * |(q : ℝ) * γ - a| ≤ (wheel x : ℝ) * (1 / Q) :=
          mul_le_mul_of_nonneg_left hlt hW0.le
      _ = (wheel x : ℝ) / Q := by ring
      _ ≤ 1 / 2 := h16
  have hqr : 1 / 2 ≤ (q : ℝ) * |r| := by
    have hq0' : (0 : ℝ) ≤ q := by positivity
    rw [← abs_of_nonneg hq0', ← abs_mul, hident]
    have := abs_sub_abs_le_abs_sub (((wheel x : ℤ) * a - k * q : ℤ) : ℝ)
      (-((wheel x : ℝ) * ((q : ℝ) * γ - a)))
    rw [abs_neg, sub_neg_eq_add] at this
    rw [add_comm]
    linarith
  have hA' := e_sub_one_lower ((wheel x : ℝ) * γ) k (abs_sub_round _)
  -- the size step
  have hxpow : x ^ (2 * θ - 1) ≤ x ^ θ :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hxθ : 0 < x ^ θ := Real.rpow_pos_of_pos hx0 _
  have hqx : (q : ℝ) * L ^ (5 : ℕ) ≤ x ^ θ := by
    have : (q : ℝ) * L ^ (5 * A) ≤ x ^ (2 * θ - 1) := by
      rw [← le_div_iff₀ hP]; exact hqQ
    nlinarith [mul_le_mul_of_nonneg_left h5 (by positivity : (0:ℝ) ≤ q)]
  have hηL : 2 ≤ η * L := by
    have := (div_le_iff₀ hη).mp hLη; linarith
  have hL3' : (1 : ℝ) ≤ L ^ (3 : ℕ) := one_le_pow₀ (by linarith)
  have hηL4 : 2 ≤ η * L ^ (4 : ℕ) := by
    have h := mul_le_mul_of_nonneg_left hL3' (by linarith : (0 : ℝ) ≤ η * L)
    calc (2 : ℝ) ≤ η * L * 1 := by linarith
      _ ≤ η * L * L ^ (3 : ℕ) := h
      _ = η * L ^ (4 : ℕ) := by ring
  have hLq : 0 ≤ L * q := by positivity
  have hc : 2 * (L * q) ≤ η * (q * L ^ (5 : ℕ)) := by
    calc 2 * (L * q) ≤ (η * L ^ (4 : ℕ)) * (L * q) := mul_le_mul_of_nonneg_right hηL4 hLq
      _ = η * (q * L ^ (5 : ℕ)) := by ring
  have hWq2 : 2 * (wheel x : ℝ) * q ≤ η * x ^ θ := by
    have h1 : 2 * (wheel x : ℝ) * q ≤ 2 * (L * q) := by
      have := mul_le_mul_of_nonneg_right hW (by positivity : (0 : ℝ) ≤ q)
      linarith
    exact h1.trans (hc.trans (mul_le_mul_of_nonneg_left hqx hη.le))
  set E := ‖e ((wheel x : ℝ) * γ) - 1‖ with hEdef
  have hE0 : 0 ≤ E := norm_nonneg _
  have hE : 2 ≤ (q : ℝ) * E := by
    have h := mul_le_mul_of_nonneg_left hA' (by positivity : (0 : ℝ) ≤ q)
    rw [← hr] at h
    linarith
  calc 4 * (wheel x : ℝ) = 2 * (wheel x : ℝ) * 2 := by ring
    _ ≤ 2 * (wheel x : ℝ) * ((q : ℝ) * E) :=
        mul_le_mul_of_nonneg_left hE (by positivity)
    _ = (2 * (wheel x : ℝ) * q) * E := by ring
    _ ≤ (η * x ^ θ) * E := mul_le_mul_of_nonneg_right hWq2 hE0

/-- MMS page 12, case q at least log to the 5A, the smoothed exponential sum over one
class modulo W with frequency gamma is o of x to the theta over W. This is the sum in
the main term of minor_arc_main with the reference mean removed.
Proved from progression_partial_summation and minor_arc_dioph. -/
theorem minor_arc_main_sum_of_leaves (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1) (A : ℝ) (hA : 1 ≤ A) :
    ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ c : ℕ, Nat.Coprime c (wheel x) → ∀ γ : ℝ, ∀ a : ℤ, ∀ q : ℕ, 0 < q →
        Int.gcd a q = 1 → Real.log x ^ (5 * A) ≤ q →
        (q : ℝ) ≤ x ^ (2 * θ - 1) / Real.log x ^ (5 * A) →
        |(q : ℝ) * γ - a| < 1 / (x ^ (2 * θ - 1) / Real.log x ^ (5 * A)) →
        (wheel x : ℝ) *
          ‖∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]),
            ((edgeCutoff ε θ x n : ℝ) : ℂ) * e (n * γ)‖ ≤ η * x ^ θ := by
  intro η hη
  obtain ⟨X, hX⟩ := minor_arc_dioph θ hθ hθ1 A hA η hη
  refine ⟨X, fun x hx c _hc γ a q hq0 hgcd hbig hqQ happ => ?_⟩
  have hd := hX x hx γ a q hq0 hgcd hbig hqQ happ
  have hp := progression_partial_summation ε θ x c γ
  set N := ‖∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]),
        ((edgeCutoff ε θ x n : ℝ) : ℂ) * e (n * γ)‖ with hN
  set E := ‖e ((wheel x : ℝ) * γ) - 1‖ with hE
  have hW : (0 : ℝ) < wheel x := by exact_mod_cast wheel_pos x
  have hN0 : 0 ≤ N := norm_nonneg _
  have hE0 : 0 ≤ E := norm_nonneg _
  have hEpos : 0 < E := by
    rcases hE0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hd; nlinarith
  have key : ((wheel x : ℝ) * N) * E ≤ (η * x ^ θ) * E := by
    calc ((wheel x : ℝ) * N) * E = (wheel x : ℝ) * (N * E) := by ring
      _ ≤ (wheel x : ℝ) * 4 := mul_le_mul_of_nonneg_left hp hW.le
      _ = 4 * (wheel x : ℝ) := by ring
      _ ≤ _ := hd
  exact le_of_mul_le_mul_right key hEpos

/-- The statement of minor_arc_main from minor_arc_main_sum_of_leaves and the eventual
bound on the reference mean. MMS page 12. CONDITIONAL ON
Task571.roughReferenceMean_limit and Task571.correctionReferenceMean_limit. -/
theorem minor_arc_main_of_leaves (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1)
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
  intro η hη
  obtain ⟨M, hM, XM, hXM⟩ := referenceMean_eventually_bounded
  have hM1 : 0 < M + 1 := by linarith
  obtain ⟨X₁, hX₁⟩ := minor_arc_main_sum_of_leaves θ hθ hθ1 ε hε hε1 A hA (η / (M + 1)) (div_pos hη hM1)
  refine ⟨max X₁ (max XM 2), fun x hx c hc γ a q hq0 hgcd hbig hqQ happ => ?_⟩
  have hx₁ : X₁ ≤ x := le_trans (le_max_left _ _) hx
  have hxM : XM ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hφ : (0 : ℝ) < (wheel x).totient := by
    exact_mod_cast Nat.totient_pos.mpr (wheel_pos x)
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hW : (0 : ℝ) < wheel x := by exact_mod_cast wheel_pos x
  have hxθ : 0 < x ^ θ := Real.rpow_pos_of_pos (by linarith) _
  have h1 := hX₁ x hx₁ c hc γ a q hq0 hgcd hbig hqQ happ
  have hm := hXM x hxM
  set N := ‖∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]),
          ((edgeCutoff ε θ x n : ℝ) : ℂ) * e (n * γ)‖ with hN
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hmabs : |Task379.referenceMean x / Real.log x * (wheel x / (wheel x).totient)| * N =
      |Task379.referenceMean x| * ((wheel x : ℝ) * N) /
        (((wheel x).totient : ℝ) * Real.log x) := by
    rw [abs_mul, abs_div, abs_div, abs_of_pos hL, abs_of_pos hW, abs_of_pos hφ]
    field_simp
  rw [hmabs]
  have hD : 0 < ((wheel x).totient : ℝ) * Real.log x := mul_pos hφ hL
  apply div_le_div_of_nonneg_right _ hD.le
  have hWN : 0 ≤ (wheel x : ℝ) * N := mul_nonneg hW.le (norm_nonneg _)
  calc |Task379.referenceMean x| * ((wheel x : ℝ) * N)
      ≤ M * (η / (M + 1) * x ^ θ) := mul_le_mul hm h1 hWN hM
    _ = (M / (M + 1)) * (η * x ^ θ) := by ring
    _ ≤ 1 * (η * x ^ θ) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      rw [div_le_one hM1]; linarith
    _ = η * x ^ θ := one_mul _

/-- Euler product for the totient over the reals. From Mathlib Nat.totient_eq_mul_prod_factors. -/
theorem totient_real_eq (n : ℕ) :
    ((n.totient : ℕ) : ℝ) = n * ∏ p ∈ n.primeFactors, (1 - (p : ℝ)⁻¹) := by
  have h := Nat.totient_eq_mul_prod_factors n
  have h2 := congrArg (fun r : ℚ => (r : ℝ)) h
  simpa using h2

/-- Prime factors of [a,b] split as those of a and the primes of b not dividing a. Derived. -/
theorem primeFactors_lcm_eq (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (Nat.lcm a b).primeFactors =
      a.primeFactors ∪ b.primeFactors.filter (fun p => ¬ p ∣ a) := by
  have hl : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha hb
  ext p
  simp only [mem_union, mem_filter, Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp, hpd, -⟩
    have : p ∣ a * b := hpd.trans (Nat.lcm_dvd_mul a b)
    rcases (Nat.Prime.dvd_mul hp).mp this with h | h
    · exact Or.inl ⟨hp, h, ha⟩
    · by_cases hpa : p ∣ a
      · exact Or.inl ⟨hp, hpa, ha⟩
      · exact Or.inr ⟨⟨hp, h, hb⟩, hpa⟩
  · rintro (⟨hp, h, -⟩ | ⟨⟨hp, h, -⟩, -⟩)
    · exact ⟨hp, h.trans (Nat.dvd_lcm_left a b), hl⟩
    · exact ⟨hp, h.trans (Nat.dvd_lcm_right a b), hl⟩

/-- MMS page 12 last paragraph, [W,q] over phi of [W,q] equals W over phi W divided by the
product of 1 minus 1 over p over the primes p of q not dividing W. Derived from totient_real_eq. -/
theorem lcm_ratio_eq (W q : ℕ) (hW : 0 < W) (hq : 0 < q) :
    (Nat.lcm W q : ℝ) / (Nat.lcm W q).totient =
      ((W : ℝ) / W.totient) /
        ∏ p ∈ q.primeFactors.filter (fun p => ¬ p ∣ W), (1 - (p : ℝ)⁻¹) := by
  have hl : Nat.lcm W q ≠ 0 := Nat.lcm_ne_zero hW.ne' hq.ne'
  have hdisj : Disjoint W.primeFactors (q.primeFactors.filter (fun p => ¬ p ∣ W)) := by
    rw [disjoint_left]
    intro p hp hp'
    exact (mem_filter.mp hp').2 (Nat.dvd_of_mem_primeFactors hp)
  rw [totient_real_eq, totient_real_eq, primeFactors_lcm_eq W q hW.ne' hq.ne',
    prod_union hdisj]
  have hpos : ∀ s : Finset ℕ, (∀ p ∈ s, p.Prime) → 0 < ∏ p ∈ s, (1 - (p : ℝ)⁻¹) := by
    intro s hs
    apply prod_pos
    intro p hp
    have : (1 : ℝ) < p := by exact_mod_cast (hs p hp).one_lt
    have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ this
    linarith
  have h1 := hpos W.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
  have h2 := hpos (q.primeFactors.filter (fun p => ¬ p ∣ W))
    (fun p hp => Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1)
  have hW0 : (0 : ℝ) < W := by exact_mod_cast hW
  have hL0 : (0 : ℝ) < Nat.lcm W q := by exact_mod_cast Nat.pos_of_ne_zero hl
  field_simp

/-- A prime not dividing W exceeds the wheel cutoff, MMS page 12 definition of W.
Derived from the definition of primorial. -/
theorem prime_not_dvd_wheel_ge (x : ℝ) {p : ℕ} (hp : p.Prime) (hpW : ¬ p ∣ wheel x) :
    ⌊(0.1 : ℝ) * Real.log (Real.log x)⌋₊ + 1 ≤ p := by
  by_contra h
  apply hpW
  rw [wheel_eq_primorial]
  unfold primorial
  apply dvd_prod_of_mem
  rw [mem_filter, mem_range]
  exact ⟨by omega, hp⟩

/-- The product of 1 minus a i is at least 1 minus the sum of a i for a i in zero to one. Derived. -/
theorem prod_one_sub_ge (s : Finset ℕ) (a : ℕ → ℝ) (h0 : ∀ i ∈ s, 0 ≤ a i)
    (h1 : ∀ i ∈ s, a i ≤ 1) : 1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [prod_insert hj, sum_insert hj]
    have hih := ih (fun i hi => h0 i (mem_insert_of_mem hi)) (fun i hi => h1 i (mem_insert_of_mem hi))
    have ha0 := h0 j (mem_insert_self j s)
    have ha1 := h1 j (mem_insert_self j s)
    have hs0 : 0 ≤ ∑ i ∈ s, a i := sum_nonneg (fun i hi => h0 i (mem_insert_of_mem hi))
    have := mul_le_mul_of_nonneg_left hih (by linarith : 0 ≤ 1 - a j)
    nlinarith

/-- Proved step, MMS page 12 last paragraph, the count behind the o of 1 terms for q below
log to the 5A: the primes of q not dividing W all exceed the wheel cutoff
w equal to 0.1 log log x, so their number is at most 5A log log x over log w, which is
o of w. Proved: the product of these primes divides q, so w plus one to their number is
below log to the 5A, and log log x is below 10 w plus 10. -/
theorem big_prime_count (A : ℝ) (hA : 1 ≤ A) :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ, 0 < q →
      (q : ℝ) < Real.log x ^ (5 * A) →
      ((q.primeFactors.filter (fun p => ¬ p ∣ wheel x)).card : ℝ) ≤
        δ * (⌊(0.1 : ℝ) * Real.log (Real.log x)⌋₊ + 1) := by
  intro δ hδ
  set B := 50 * A / δ with hB
  have hB0 : 0 < B := by positivity
  refine ⟨Real.exp (Real.exp (10 * Real.exp B)), fun x hx q hq hqs => ?_⟩
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL : Real.exp (10 * Real.exp B) ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos _) hx
    rwa [Real.log_exp] at this
  set L := Real.log x with hLdef
  have hLpos : 0 < L := lt_of_lt_of_le (Real.exp_pos _) hL
  have hlL : 10 * Real.exp B ≤ Real.log L := by
    have := Real.log_le_log (Real.exp_pos _) hL
    rwa [Real.log_exp] at this
  set P := q.primeFactors.filter (fun p => ¬ p ∣ wheel x) with hP
  set w : ℝ := (⌊(0.1 : ℝ) * Real.log L⌋₊ : ℝ) + 1 with hw
  have hwgt : 0.1 * Real.log L < w := Nat.lt_floor_add_one _
  have hwB : Real.exp B ≤ w := by linarith
  have hw1 : 1 < w := by linarith [Real.add_one_le_exp B]
  have hlogw : B ≤ Real.log w := by
    have := Real.log_le_log (Real.exp_pos _) hwB
    rwa [Real.log_exp] at this
  have hpge : ∀ p ∈ P, w ≤ (p : ℝ) := by
    intro p hp
    obtain ⟨hpq, hpW⟩ := mem_filter.mp hp
    have := prime_not_dvd_wheel_ge x (Nat.prime_of_mem_primeFactors hpq) hpW
    rw [hw]; exact_mod_cast this
  have hprod_dvd : ∏ p ∈ P, p ∣ q :=
    (prod_dvd_prod_of_subset P q.primeFactors id (filter_subset _ _)).trans
      (Nat.prod_primeFactors_dvd q)
  have hprod_le : ((∏ p ∈ P, p : ℕ) : ℝ) ≤ q := by
    exact_mod_cast Nat.le_of_dvd hq hprod_dvd
  have hpow : w ^ P.card ≤ ((∏ p ∈ P, p : ℕ) : ℝ) := by
    push_cast
    rw [← prod_const]
    exact prod_le_prod₀ (fun _ _ => by linarith) hpge
  have hlt : w ^ P.card < L ^ (5 * A) := lt_of_le_of_lt (hpow.trans hprod_le) hqs
  have hlog : (P.card : ℝ) * Real.log w < 5 * A * Real.log L := by
    have := Real.log_lt_log (pow_pos (by linarith) _) hlt
    rwa [Real.log_pow, Real.log_rpow hLpos] at this
  have hlogL : Real.log L < 10 * w := by linarith
  have hcw : (P.card : ℝ) * B < 50 * A * w := by
    have h1 : (P.card : ℝ) * B ≤ (P.card : ℝ) * Real.log w :=
      mul_le_mul_of_nonneg_left hlogw (by positivity)
    nlinarith
  have : (P.card : ℝ) * B = (P.card : ℝ) * (50 * A) / δ := by rw [hB]; ring
  rw [this, div_lt_iff₀ hδ] at hcw
  have hA0 : 0 < 50 * A := by linarith
  have : (P.card : ℝ) * (50 * A) ≤ δ * w * (50 * A) := by nlinarith
  have := le_of_mul_le_mul_right this hA0
  exact this

/-- Proved step, MMS page 12 last paragraph, the o of 1 step in [W,q] over phi of [W,q] equal to
1 plus o of 1 times W over phi W. Every prime p of q not dividing W exceeds the wheel cutoff
0.1 log log x, and as q is below log to the 5A there are at most 5A log log x over log of
that cutoff of them, so the product of p over p minus 1 over them tends to one.
Originally class MEDIUM, now proved from big_prime_count. -/
theorem wheel_prime_product_close (A : ℝ) (hA : 1 ≤ A) :
    ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ, 0 < q →
      (q : ℝ) < Real.log x ^ (5 * A) →
      |(∏ p ∈ q.primeFactors.filter (fun p => ¬ p ∣ wheel x), (1 - (p : ℝ)⁻¹))⁻¹ - 1| ≤ η := by
  intro η hη
  set δ := min (1 / 2) (η / 2) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by linarith)
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδ2 : δ ≤ η / 2 := min_le_right _ _
  obtain ⟨X, hX⟩ := big_prime_count A hA δ hδ0
  refine ⟨X, fun x hx q hq hqs => ?_⟩
  have hc := hX x hx q hq hqs
  set P := q.primeFactors.filter (fun p => ¬ p ∣ wheel x) with hP
  set w : ℝ := (⌊(0.1 : ℝ) * Real.log (Real.log x)⌋₊ : ℝ) + 1 with hw
  have hw1 : 1 ≤ w := by rw [hw]; have := Nat.cast_nonneg (α := ℝ) ⌊(0.1 : ℝ) * Real.log (Real.log x)⌋₊; linarith
  have hpge : ∀ p ∈ P, w ≤ (p : ℝ) := by
    intro p hp
    obtain ⟨hpq, hpW⟩ := mem_filter.mp hp
    have := prime_not_dvd_wheel_ge x (Nat.prime_of_mem_primeFactors hpq) hpW
    rw [hw]; exact_mod_cast this
  have hinv0 : ∀ p ∈ P, 0 ≤ (p : ℝ)⁻¹ := fun p _ => by positivity
  have hinv1 : ∀ p ∈ P, (p : ℝ)⁻¹ ≤ w⁻¹ := fun p hp =>
    inv_anti₀ (by linarith) (hpge p hp)
  have hinvle1 : ∀ p ∈ P, (p : ℝ)⁻¹ ≤ 1 := fun p hp =>
    (hinv1 p hp).trans (inv_le_one_of_one_le₀ hw1)
  have hsum : ∑ p ∈ P, (p : ℝ)⁻¹ ≤ δ := by
    calc ∑ p ∈ P, (p : ℝ)⁻¹ ≤ ∑ p ∈ P, w⁻¹ := sum_le_sum hinv1
      _ = (P.card : ℝ) * w⁻¹ := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (δ * w) * w⁻¹ := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = δ := by field_simp
  have hlow := prod_one_sub_ge P (fun p => (p : ℝ)⁻¹) hinv0 hinvle1
  have hup : ∏ p ∈ P, (1 - (p : ℝ)⁻¹) ≤ 1 :=
    prod_le_one₀ (fun p hp => by linarith [hinvle1 p hp]) (fun p hp => by linarith [hinv0 p hp])
  set Pr := ∏ p ∈ P, (1 - (p : ℝ)⁻¹) with hPr
  have hPr0 : 1 / 2 ≤ Pr := by linarith
  have hpos : 0 < Pr := by linarith
  rw [abs_le]
  constructor
  · have : 1 ≤ Pr⁻¹ := one_le_inv₀ hpos |>.mpr hup
    linarith
  · rw [inv_eq_one_div, div_sub_one hpos.ne', div_le_iff₀ hpos]
    nlinarith

/-- Proved step, MMS page 12 last paragraph, for q below log to the 5A the ratio
[W,q] over phi of [W,q] is 1 plus o of 1 times W over phi W, because every prime
factor of q not dividing W exceeds the wheel cutoff 0.1 log log x and q has
O of log log x over log log log x such factors. Originally class MEDIUM, now
proved from wheel_prime_product_close through lcm_ratio_eq. -/
theorem lcm_ratio_close (A : ℝ) (hA : 1 ≤ A) :
    ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ, 0 < q →
      (q : ℝ) < Real.log x ^ (5 * A) →
      |(Nat.lcm (wheel x) q : ℝ) / (Nat.lcm (wheel x) q).totient -
          (wheel x : ℝ) / (wheel x).totient| ≤
        η * ((wheel x : ℝ) / (wheel x).totient) := by
  intro η hη
  obtain ⟨X, hX⟩ := wheel_prime_product_close A hA η hη
  refine ⟨X, fun x hx q hq hqs => ?_⟩
  have h := hX x hx q hq hqs
  rw [lcm_ratio_eq (wheel x) q (wheel_pos x) hq]
  have hb : 0 < (wheel x : ℝ) / (wheel x).totient := by
    apply div_pos
    · exact_mod_cast wheel_pos x
    · exact_mod_cast Nat.totient_pos.mpr (wheel_pos x)
  rw [div_eq_mul_inv, show (wheel x : ℝ) / (wheel x).totient *
      (∏ p ∈ q.primeFactors.filter (fun p => ¬ p ∣ wheel x), (1 - (p : ℝ)⁻¹))⁻¹ -
      (wheel x : ℝ) / (wheel x).totient = (wheel x : ℝ) / (wheel x).totient *
      ((∏ p ∈ q.primeFactors.filter (fun p => ¬ p ∣ wheel x), (1 - (p : ℝ)⁻¹))⁻¹ - 1) by ring,
    abs_mul, abs_of_pos hb, mul_comm η]
  exact mul_le_mul_of_nonneg_left h hb.le


/-- Proved step, MMS page 12 last paragraph, the o of 1 step for the terms with n not
coprime to q. Every prime p of q not dividing W exceeds the wheel cutoff
0.1 log log x, there are at most 5A log log x over log of that cutoff of them as q is
below log to the 5A, so the sum of 2 x to the theta over p plus W over them is
o of x to the theta. Originally class MEDIUM, now proved from big_prime_count. -/
theorem prime_factor_sum_small (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1) (A : ℝ) (hA : 1 ≤ A) :
    ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ, 0 < q →
      (q : ℝ) < Real.log x ^ (5 * A) →
      ∑ p ∈ q.primeFactors.filter (fun p => ¬ p ∣ wheel x),
          (2 * x ^ θ / p + wheel x) ≤ η * x ^ θ := by
  intro η hη
  have hθ0 : 0 < θ := by linarith
  obtain ⟨X₁, h₁⟩ := big_prime_count A hA (η / 3) (by linarith)
  obtain ⟨X₂, h₂⟩ := Filter.eventually_atTop.mp
    (((isLittleO_log_rpow_rpow_atTop (2 : ℝ) hθ0).bound (by norm_num : (0 : ℝ) < 1)).and
      (Filter.eventually_ge_atTop (Real.exp 1)))
  refine ⟨max X₁ X₂, fun x hx q hq hqs => ?_⟩
  have hc := h₁ x (le_trans (le_max_left _ _) hx) q hq hqs
  obtain ⟨hL2, hxe⟩ := h₂ x (le_trans (le_max_right _ _) hx)
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hxe
  have hxθ : 0 < x ^ θ := Real.rpow_pos_of_pos hx0 _
  have hlx1 : 1 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) hxe
    simpa only [Real.log_exp] using h
  have hLpos : 0 < Real.log x := by linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hLpos _),
    abs_of_pos hxθ, one_mul] at hL2
  have hL2' : Real.log x * Real.log x ≤ x ^ θ := by
    rw [Real.rpow_two] at hL2
    nlinarith
  have hW := wheel_le_log hxe
  set P := q.primeFactors.filter (fun p => ¬ p ∣ wheel x) with hP
  set w : ℝ := (⌊(0.1 : ℝ) * Real.log (Real.log x)⌋₊ : ℝ) + 1 with hw
  have hll : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hlx1
  have hwL : w ≤ Real.log x := by
    have hf := Nat.floor_le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 0.1) hll)
    have := Real.log_le_sub_one_of_pos hLpos
    rw [hw]; nlinarith
  have hw1 : 1 ≤ w := by rw [hw]; have := Nat.cast_nonneg (α := ℝ) ⌊(0.1 : ℝ) * Real.log (Real.log x)⌋₊; linarith
  have hpge : ∀ p ∈ P, w ≤ (p : ℝ) := by
    intro p hp
    obtain ⟨hpq, hpW⟩ := mem_filter.mp hp
    have := prime_not_dvd_wheel_ge x (Nat.prime_of_mem_primeFactors hpq) hpW
    rw [hw]; exact_mod_cast this
  calc ∑ p ∈ P, (2 * x ^ θ / p + wheel x)
      ≤ ∑ p ∈ P, (2 * x ^ θ / w + Real.log x) := by
        apply sum_le_sum; intro p hp
        have := div_le_div_of_nonneg_left (by positivity : 0 ≤ 2 * x ^ θ) (by linarith) (hpge p hp)
        linarith
    _ = (P.card : ℝ) * (2 * x ^ θ / w + Real.log x) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (η / 3 * w) * (2 * x ^ θ / w + Real.log x) :=
        mul_le_mul_of_nonneg_right hc (by positivity)
    _ = 2 * (η / 3) * x ^ θ + η / 3 * (w * Real.log x) := by field_simp
    _ ≤ 2 * (η / 3) * x ^ θ + η / 3 * x ^ θ := by
        have : w * Real.log x ≤ x ^ θ :=
          (mul_le_mul_of_nonneg_right hwL hLpos.le).trans hL2'
        nlinarith
    _ = η * x ^ θ := by ring

/-- Proved step, MMS page 12 last paragraph: for a prime p not dividing W, the n in one
class modulo W that are divisible by p lie in one class modulo W p, so W times their
number is at most 2 x to the theta over p plus W. From Halupczok2012.card_cong_le and
Mathlib Nat.modEq_and_modEq_iff_modEq_mul. -/
theorem per_prime_count (θ : ℝ) (hθ : 0 < θ) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ c p : ℕ, p.Prime → ¬ p ∣ wheel x →
      (wheel x : ℝ) *
        ((((ints (x - x ^ θ / 3) (x + x ^ θ)).filter
            (fun n => n ≡ c [MOD wheel x])).filter (fun n => p ∣ n)).card : ℝ) ≤
        2 * x ^ θ / p + wheel x := by
  have hsmall := (isLittleO_log_rpow_atTop hθ).bound (by norm_num : (0 : ℝ) < 1 / 3)
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp
    (hsmall.and (Filter.eventually_ge_atTop (Real.exp 1)))
  refine ⟨X₀, fun x hx c p hp hpW => ?_⟩
  obtain ⟨hlog, hxe⟩ := hX₀ x hx
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hxe
  have hxθ : 0 < x ^ θ := Real.rpow_pos_of_pos hx0 _
  have hlx1 : 1 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) hxe
    simpa only [Real.log_exp] using h
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith), abs_of_pos hxθ] at hlog
  have hW0 : (0 : ℝ) < wheel x := by exact_mod_cast wheel_pos x
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  set S := ((ints (x - x ^ θ / 3) (x + x ^ θ)).filter
      (fun n => n ≡ c [MOD wheel x])).filter (fun n => p ∣ n) with hS
  have hcop : Nat.Coprime (wheel x) p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpW).symm
  have hmem : ∀ n ∈ S, x - x ^ θ / 3 ≤ n ∧ (n : ℝ) ≤ x + x ^ θ ∧
      n ≡ c [MOD wheel x] ∧ p ∣ n := by
    intro n hn
    obtain ⟨hn1, hpn⟩ := mem_filter.mp hn
    obtain ⟨hn2, hc⟩ := mem_filter.mp hn1
    obtain ⟨hlo, hhi⟩ := mem_Icc.mp hn2
    exact ⟨(Nat.le_ceil _).trans (by exact_mod_cast hlo),
      (show (n : ℝ) ≤ (⌊x + x ^ θ⌋₊ : ℝ) by exact_mod_cast hhi).trans
        (Nat.floor_le (by linarith)), hc, hpn⟩
  have hc : (S.card : ℝ) ≤ (4 / 3 * x ^ θ + 1) / ((wheel x * p : ℕ) : ℝ) + 1 := by
    apply LeanLab.Halupczok2012.card_cong_le (x := x - x ^ θ / 3 - 1)
      (Nat.mul_pos (wheel_pos x) hp.pos) (by linarith)
    · intro m hm
      have := hmem m hm
      constructor <;> linarith [this.1, this.2.1]
    · intro m hm m' hm'
      obtain ⟨-, -, h1, h1p⟩ := hmem m hm
      obtain ⟨-, -, h2, h2p⟩ := hmem m' hm'
      have hW : m ≡ m' [MOD wheel x] := h1.trans h2.symm
      have hP : m ≡ m' [MOD p] :=
        ((Nat.modEq_zero_iff_dvd.mpr h1p).trans (Nat.modEq_zero_iff_dvd.mpr h2p).symm)
      exact Int.natCast_modEq_iff.mpr ((Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hW, hP⟩)
  push_cast at hc
  have h43 : 4 / 3 * x ^ θ + 1 ≤ 2 * x ^ θ := by nlinarith
  calc (wheel x : ℝ) * S.card
      ≤ (wheel x : ℝ) * ((4 / 3 * x ^ θ + 1) / ((wheel x : ℝ) * p) + 1) :=
        mul_le_mul_of_nonneg_left hc hW0.le
    _ = (4 / 3 * x ^ θ + 1) / p + wheel x := by field_simp
    _ ≤ 2 * x ^ θ / p + wheel x := by
        gcongr

/-- Proved step, MMS page 12 last paragraph, the terms with n not coprime to q
contribute o of x to the theta over phi W log x. Such n in one class modulo W
coprime to W are divisible by a prime p of q above the wheel cutoff, so their
number is at most the sum over those p of x to the theta over W p plus one.
Originally class MEDIUM, now proved from prime_factor_sum_small and per_prime_count. -/
theorem noncoprime_count (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1) (A : ℝ) (hA : 1 ≤ A) :
    ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ c : ℕ, Nat.Coprime c (wheel x) → ∀ q : ℕ, 0 < q →
        (q : ℝ) < Real.log x ^ (5 * A) →
        (wheel x : ℝ) *
          ((((ints (x - x ^ θ / 3) (x + x ^ θ)).filter
              (fun n => n ≡ c [MOD wheel x])).filter
              (fun n => ¬ Nat.Coprime n q)).card : ℝ) ≤ η * x ^ θ := by
  intro η hη
  obtain ⟨X₁, h₁⟩ := prime_factor_sum_small θ hθ hθ1 A hA η hη
  obtain ⟨X₂, h₂⟩ := per_prime_count θ (by linarith)
  refine ⟨max X₁ X₂, fun x hx c hc q hq hqs => ?_⟩
  have hs := h₁ x (le_trans (le_max_left _ _) hx) q hq hqs
  have hpp := h₂ x (le_trans (le_max_right _ _) hx) c
  set S := (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]) with hS
  set P := q.primeFactors.filter (fun p => ¬ p ∣ wheel x) with hP
  have hsub : S.filter (fun n => ¬ Nat.Coprime n q) ⊆ P.biUnion (fun p => S.filter (fun n => p ∣ n)) := by
    intro n hn
    obtain ⟨hnS, hnc⟩ := mem_filter.mp hn
    obtain ⟨p, hp, hpn, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    rw [mem_biUnion]
    refine ⟨p, mem_filter.mpr ⟨Nat.mem_primeFactors.mpr ⟨hp, hpq, hq.ne'⟩, ?_⟩,
      mem_filter.mpr ⟨hnS, hpn⟩⟩
    intro hpW
    have hmod : n ≡ c [MOD wheel x] := (mem_filter.mp hnS).2
    have hpc : p ∣ c := (Nat.ModEq.dvd_iff hmod hpW).mp hpn
    have h1 : p ∣ Nat.gcd c (wheel x) := Nat.dvd_gcd hpc hpW
    rw [Nat.Coprime.gcd_eq_one hc] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hcard : ((S.filter (fun n => ¬ Nat.Coprime n q)).card : ℝ) ≤
      ∑ p ∈ P, ((S.filter (fun n => p ∣ n)).card : ℝ) := by
    exact_mod_cast (card_le_card hsub).trans card_biUnion_le
  have hW0 : (0 : ℝ) ≤ wheel x := by positivity
  calc (wheel x : ℝ) * ((S.filter (fun n => ¬ Nat.Coprime n q)).card : ℝ)
      ≤ (wheel x : ℝ) * ∑ p ∈ P, ((S.filter (fun n => p ∣ n)).card : ℝ) :=
        mul_le_mul_of_nonneg_left hcard hW0
    _ = ∑ p ∈ P, (wheel x : ℝ) * ((S.filter (fun n => p ∣ n)).card : ℝ) := mul_sum _ _ _
    _ ≤ ∑ p ∈ P, (2 * x ^ θ / p + wheel x) := by
        apply sum_le_sum
        intro p hpP
        obtain ⟨hpq, hpW⟩ := mem_filter.mp hpP
        exact hpp p (Nat.prime_of_mem_primeFactors hpq) hpW
    _ ≤ η * x ^ θ := hs

/-- Proved step, MMS page 12, the interval x minus x to the theta over three to x plus
x to the theta has length four thirds x to the theta, so one class modulo W meets it
in at most four thirds x to the theta over W plus one integers. Proved from
Halupczok2012.card_cong_le and wheel_le_log. -/
theorem progression_count (θ : ℝ) (hθ : 0 < θ) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ c : ℕ,
      (wheel x : ℝ) *
        (((ints (x - x ^ θ / 3) (x + x ^ θ)).filter
            (fun n => n ≡ c [MOD wheel x])).card : ℝ) ≤ 2 * x ^ θ := by
  have hsmall := (isLittleO_log_rpow_atTop hθ).bound (by norm_num : (0 : ℝ) < 1 / 3)
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp
    (hsmall.and (Filter.eventually_ge_atTop (Real.exp 1)))
  refine ⟨X₀, fun x hx c => ?_⟩
  obtain ⟨hlog, hxe⟩ := hX₀ x hx
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hxe
  have hxθ : 0 < x ^ θ := Real.rpow_pos_of_pos hx0 _
  have hlx1 : 1 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) hxe
    simpa only [Real.log_exp] using h
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith), abs_of_pos hxθ] at hlog
  have hWlog := wheel_le_log hxe
  have hW0 : (0 : ℝ) < wheel x := by exact_mod_cast wheel_pos x
  set S := (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]) with hS
  have hmem : ∀ n ∈ S, x - x ^ θ / 3 ≤ n ∧ (n : ℝ) ≤ x + x ^ θ := by
    intro n hn
    obtain ⟨hlo, hhi⟩ := mem_Icc.mp (mem_filter.mp hn).1
    exact ⟨(Nat.le_ceil _).trans (by exact_mod_cast hlo),
      (show (n : ℝ) ≤ (⌊x + x ^ θ⌋₊ : ℝ) by exact_mod_cast hhi).trans
        (Nat.floor_le (by linarith))⟩
  have hc : (S.card : ℝ) ≤ (4 / 3 * x ^ θ + 1) / wheel x + 1 := by
    apply LeanLab.Halupczok2012.card_cong_le (x := x - x ^ θ / 3 - 1) (wheel_pos x)
      (by linarith)
    · intro m hm
      have := hmem m hm
      constructor <;> linarith
    · intro m hm m' hm'
      have h1 := (mem_filter.mp hm).2
      have h2 := (mem_filter.mp hm').2
      exact Int.natCast_modEq_iff.mpr (h1.trans h2.symm)
  calc (wheel x : ℝ) * S.card ≤ (wheel x : ℝ) * ((4 / 3 * x ^ θ + 1) / wheel x + 1) :=
        mul_le_mul_of_nonneg_left hc hW0.le
    _ = 4 / 3 * x ^ θ + 1 + wheel x := by field_simp
    _ ≤ 2 * x ^ θ := by nlinarith

/-- The statement of major_arc_reduction from lcm_ratio_close, noncoprime_count
and progression_count, all proved here. MMS page 12 last paragraph.
CONDITIONAL ON Task571.roughReferenceMean_limit and Task571.correctionReferenceMean_limit. -/
theorem major_arc_reduction_of_leaves (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1)
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
  intro η hη
  obtain ⟨M, hM, XM, hXM⟩ := referenceMean_eventually_bounded
  have hM1 : 0 < M + 1 := by linarith
  have hη1 : 0 < η / (4 * (M + 1)) := by positivity
  have hη2 : 0 < η / (2 * (M + 1)) := by positivity
  obtain ⟨X₁, hX₁⟩ := lcm_ratio_close A hA _ hη1
  obtain ⟨X₂, hX₂⟩ := noncoprime_count θ hθ hθ1 A hA _ hη2
  obtain ⟨X₃, hX₃⟩ := progression_count θ (by linarith)
  refine ⟨max (max X₁ X₂) (max X₃ (max XM 2)), fun x hx c hc γ q hq0 hqs => ?_⟩
  have hx₁ : X₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx₂ : X₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx₃ : X₃ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxM : XM ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)) hx
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_right _ _)) hx
  have hφ : (0 : ℝ) < (wheel x).totient := by
    exact_mod_cast Nat.totient_pos.mpr (wheel_pos x)
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hW : (0 : ℝ) < wheel x := by exact_mod_cast wheel_pos x
  have hxθ : 0 < x ^ θ := Real.rpow_pos_of_pos (by linarith) _
  have h1 := hX₁ x hx₁ q hq0 hqs
  have h2 := hX₂ x hx₂ c hc q hq0 hqs
  have h3 := hX₃ x hx₃ c
  have hm := hXM x hxM
  set S := (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]) with hS
  set T := S.filter (fun n => Nat.Coprime n q) with hT
  set D := S.filter (fun n => ¬ Nat.Coprime n q) with hD
  set f : ℕ → ℂ := fun n => ((edgeCutoff ε θ x n : ℝ) : ℂ) * e (n * γ) with hf
  have hfn : ∀ n, ‖f n‖ ≤ 1 := by
    intro n
    simp only [hf]
    rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (edgeCutoff_nonneg _ _ _ _)]
    exact edgeCutoff_le_one _ _ _ _
  have hsumle : ∀ U : Finset ℕ, ‖∑ n ∈ U, f n‖ ≤ U.card := by
    intro U
    apply (norm_sum_le _ _).trans
    calc ∑ n ∈ U, ‖f n‖ ≤ ∑ n ∈ U, (1 : ℝ) := sum_le_sum (fun n _ => hfn n)
      _ = U.card := by simp
  have hsplit : ∑ n ∈ S, f n = ∑ n ∈ T, f n + ∑ n ∈ D, f n :=
    (sum_filter_add_sum_filter_not S (fun n => Nat.Coprime n q) f).symm
  set m := Task379.referenceMean x / Real.log x with hmdef
  set a := (Nat.lcm (wheel x) q : ℝ) / (Nat.lcm (wheel x) q).totient with hadef
  set b := (wheel x : ℝ) / (wheel x).totient with hbdef
  have hb0 : 0 < b := div_pos hW hφ
  have hexpr : ((m * a : ℝ) : ℂ) * ∑ n ∈ T, f n - ((m * b : ℝ) : ℂ) * ∑ n ∈ S, f n =
      (m : ℂ) * (((a - b : ℝ) : ℂ) * ∑ n ∈ T, f n - (b : ℂ) * ∑ n ∈ D, f n) := by
    rw [hsplit]; push_cast; ring
  have hTS : (T.card : ℝ) ≤ S.card := by exact_mod_cast card_filter_le S _
  have hmabs : |m| ≤ M / Real.log x := by
    rw [hmdef, abs_div, abs_of_pos hL]
    exact div_le_div_of_nonneg_right hm hL.le
  have hinner : ‖((a - b : ℝ) : ℂ) * ∑ n ∈ T, f n - (b : ℂ) * ∑ n ∈ D, f n‖ ≤
      η / (4 * (M + 1)) * b * T.card + b * D.card := by
    apply (norm_sub_le _ _).trans
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos hb0]
    apply add_le_add
    · exact mul_le_mul h1 (hsumle T) (norm_nonneg _) (by positivity)
    · exact mul_le_mul_of_nonneg_left (hsumle D) hb0.le
  have hWS : (wheel x : ℝ) * T.card ≤ 2 * x ^ θ :=
    (mul_le_mul_of_nonneg_left hTS hW.le).trans h3
  have hbT : b * T.card ≤ 2 * x ^ θ / (wheel x).totient := by
    rw [hbdef, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right hWS hφ.le
  have hbD : b * D.card ≤ η / (2 * (M + 1)) * x ^ θ / (wheel x).totient := by
    rw [hbdef, div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right h2 hφ.le
  rw [hexpr, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hin0 : 0 ≤ η / (4 * (M + 1)) * b * T.card + b * D.card := by positivity
  have hbound : η / (4 * (M + 1)) * b * T.card + b * D.card ≤
      (η / (M + 1)) * x ^ θ / (wheel x).totient := by
    have e1 : η / (4 * (M + 1)) * b * T.card ≤
        η / (4 * (M + 1)) * (2 * x ^ θ / (wheel x).totient) := by
      rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hbT hη1.le
    have e2 : η / (4 * (M + 1)) * (2 * x ^ θ / (wheel x).totient) +
        η / (2 * (M + 1)) * x ^ θ / (wheel x).totient =
        (η / (M + 1)) * x ^ θ / (wheel x).totient := by
      field_simp; ring
    linarith
  calc |m| * ‖((a - b : ℝ) : ℂ) * ∑ n ∈ T, f n - (b : ℂ) * ∑ n ∈ D, f n‖
      ≤ (M / Real.log x) * ((η / (M + 1)) * x ^ θ / (wheel x).totient) :=
        mul_le_mul hmabs ((hinner).trans hbound) (norm_nonneg _) (by positivity)
    _ = (M / (M + 1)) * (η * x ^ θ / ((wheel x).totient * Real.log x)) := by
        field_simp
    _ ≤ 1 * (η * x ^ θ / ((wheel x).totient * Real.log x)) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        rw [div_le_one hM1]; linarith
    _ = _ := one_mul _


/-- LEAF: MMS page 12 second paragraph, the simple sieve upper bound: on any subinterval
of length eps x to the theta inside x minus x to the theta over three to x plus x to the
theta, and in one class modulo W coprime to W, the Harman majorant of equation 5.1 sums to
O of eps x to the theta over phi W log x, with the constant independent of eps. It needs an
upper bound sieve of Brun or Selberg type for x to the quarter rough numbers and for the
ordered prime triple term, in short intervals and in classes modulo W. Class MEDIUM. -/
theorem short_interval_sieve_upper (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ c : ℕ, Nat.Coprime c (wheel x) → ∀ y : ℝ, x - x ^ θ / 3 ≤ y →
        y + ε * x ^ θ ≤ x + x ^ θ →
        ∑ n ∈ (ints y (y + ε * x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]),
            Task361.harmanMajorant x n ≤
          C * ε * x ^ θ / ((wheel x).totient * Real.log x) := by
  sorry

/-- The statement of edge_sieve_upper from short_interval_sieve_upper, MMS page 12 second
paragraph: the weight one minus g lives on the two edge pieces of length eps x to the theta.
CONDITIONAL ON short_interval_sieve_upper. -/
theorem edge_sieve_upper_of_leaves (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ c : ℕ, Nat.Coprime c (wheel x) →
        ∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]),
            Task361.harmanMajorant x n * (1 - edgeCutoff ε θ x n) ≤
          C * ε * x ^ θ / ((wheel x).totient * Real.log x) := by
  obtain ⟨C, hC, hE⟩ := short_interval_sieve_upper θ hθ hθ1
  refine ⟨2 * C, by positivity, fun ε hε hε1 => ?_⟩
  obtain ⟨X, hX⟩ := hE ε hε hε1
  refine ⟨max X 1, fun x hx c hc => ?_⟩
  have hxX : X ≤ x := le_trans (le_max_left _ _) hx
  have hx0 : 0 < x := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hx)
  have hxθ : 0 < x ^ θ := Real.rpow_pos_of_pos hx0 _
  set δ := ε * x ^ θ with hδ
  have hδ0 : 0 < δ := mul_pos hε hxθ
  have hδ1 : δ ≤ x ^ θ := by
    rw [hδ]; nlinarith
  set lo := x - x ^ θ / 3 with hlo
  set hi := x + x ^ θ with hhi
  set S := (ints lo hi).filter (fun n => n ≡ c [MOD wheel x]) with hS
  set S₁ := S.filter (fun n : ℕ => (n : ℝ) < lo + δ)
  set S₂ := S.filter (fun n : ℕ => hi - δ < (n : ℝ))
  have hmem : ∀ n ∈ S, lo ≤ n ∧ (n : ℝ) ≤ hi := by
    intro n hn
    obtain ⟨hlo', hhi'⟩ := mem_Icc.mp (mem_filter.mp hn).1
    exact ⟨(Nat.le_ceil _).trans (by exact_mod_cast hlo'),
      (show (n : ℝ) ≤ (⌊hi⌋₊ : ℝ) by exact_mod_cast hhi').trans
        (Nat.floor_le (by rw [hhi]; linarith))⟩
  have hpt : ∀ n ∈ S, Task361.harmanMajorant x n * (1 - edgeCutoff ε θ x n) ≤
      (if (n : ℝ) < lo + δ then Task361.harmanMajorant x n else 0) +
        (if hi - δ < (n : ℝ) then Task361.harmanMajorant x n else 0) := by
    intro n hn
    have hρ := Task361.harmanMajorant_nonneg x n
    have hg0 := edgeCutoff_nonneg ε θ x n
    have hg1 := edgeCutoff_le_one ε θ x n
    have hle : Task361.harmanMajorant x n * (1 - edgeCutoff ε θ x n) ≤
        Task361.harmanMajorant x n := by nlinarith
    split_ifs with h1 h2 h2
    · linarith
    · linarith
    · linarith
    · push_neg at h1 h2
      rw [one_sub_edgeCutoff_eq_zero_of_inner ε θ x n hδ0 (by linarith) (by linarith)]
      simp
  have hsplit : ∑ n ∈ S, Task361.harmanMajorant x n * (1 - edgeCutoff ε θ x n) ≤
      ∑ n ∈ S₁, Task361.harmanMajorant x n + ∑ n ∈ S₂, Task361.harmanMajorant x n := by
    refine (sum_le_sum hpt).trans (le_of_eq ?_)
    rw [sum_add_distrib, ← sum_filter, ← sum_filter]
  have hsub₁ : S₁ ⊆ (ints lo (lo + δ)).filter (fun n => n ≡ c [MOD wheel x]) := by
    intro n hn
    obtain ⟨hnS, hn1⟩ := mem_filter.mp hn
    obtain ⟨hIcc, hc'⟩ := mem_filter.mp hnS
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hIcc).1, ?_⟩, hc'⟩
    exact Nat.le_floor hn1.le
  have hsub₂ : S₂ ⊆ (ints (hi - δ) (hi - δ + δ)).filter (fun n => n ≡ c [MOD wheel x]) := by
    intro n hn
    obtain ⟨hnS, hn1⟩ := mem_filter.mp hn
    obtain ⟨hIcc, hc'⟩ := mem_filter.mp hnS
    refine mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.ceil_le.mpr hn1.le, ?_⟩, hc'⟩
    rw [sub_add_cancel]; exact (mem_Icc.mp hIcc).2
  have hnn : ∀ n, 0 ≤ Task361.harmanMajorant x n := Task361.harmanMajorant_nonneg x
  have e₁ := hX x hxX c hc lo le_rfl (by linarith)
  have e₂ := hX x hxX c hc (hi - δ) (by linarith) (by linarith)
  calc _ ≤ _ := hsplit
    _ ≤ ∑ n ∈ (ints lo (lo + δ)).filter (fun n => n ≡ c [MOD wheel x]),
            Task361.harmanMajorant x n +
        ∑ n ∈ (ints (hi - δ) (hi - δ + δ)).filter (fun n => n ≡ c [MOD wheel x]),
            Task361.harmanMajorant x n :=
        add_le_add (sum_le_sum_of_subset_of_nonneg hsub₁ (fun n _ _ => hnn n))
          (sum_le_sum_of_subset_of_nonneg hsub₂ (fun n _ _ => hnn n))
    _ ≤ C * ε * x ^ θ / ((wheel x).totient * Real.log x) +
        C * ε * x ^ θ / ((wheel x).totient * Real.log x) := add_le_add e₁ e₂
    _ = 2 * C * ε * x ^ θ / ((wheel x).totient * Real.log x) := by ring
end LeanLab.Ternary.MMS.Task420
