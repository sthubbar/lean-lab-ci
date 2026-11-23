/-
S54 burst-20261122, wave 3. Kumchev and Liu 2007, P0088, arXiv 0801.0130.
Reduces the two HARD leaves block_rough_left_half and block_rough_right_half of
Split1122KLFirstRoughHalves to one cited leaf, Lemma 3.4 of page 11 in the case
M = 1, a_1 = 1, the case page 15 applies to the first sum of display 52 with
x = Y, y = H, (m, k) = (1, m) and z = z1.

The left half is Lemma 3.4 with x = Y/4: on [Y/4, Y/2] every square in (t, t + H]
lies in [Y/4, Y), so the square window filter is no restriction.
The right half is Lemma 3.4 with x = Y/2 on [Y/2, Y - 2H], where again the window
filter is no restriction, plus the last stretch [Y - 2H, Y] of length 2H, where
the short sum has at most 2H Y^(-1/2) terms, so that stretch contributes at most
8 H^3 / Y <= 8 H^2 P^(-4), with P = (log X)^B.
The hypotheses of Lemma 3.4 hold in the block range for X large: the exponent
margin is X^(eps (3/8 - eps/4)) against P^6.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Prep1121DKLRoughCut

namespace LeanLab.KumchevLiu2007.Split1122KLLemma34M1

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d Eq33RouteD
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF: P0088 page 11 Lemma 3.4 in the case M = 1, a_1 = 1, the case used on
page 15 for the first sum of display 52. Let A > 0, B >= B0(A), x^(1/2) <= y <= x
with x sufficiently large, alpha, a, q with display 41: L^B <= q <= y L^(-B),
(a, q) = 1, |alpha - a/q| < q^(-2), L = log x, and 2 <= z <= y x^(-1/2) L^(-2B).
Then the integral over [x, 2x] of the squared modulus of the sum over k with
t < k^2 <= t + y of Phi(k, z) e(alpha k^2) is << y^2 L^(-A). Phi(k, z) of page 4
display 10 is roughWeight z k. Every k with k^2 <= t + y <= 3x lies in
range (floor (sqrt (3x)) + 1), so the finite sum below is the whole sum of the
paper. The implied constant C depends on A and B. HARD, cited, its proof is the
three case Harman type argument of page 11 to 13 built on Lemmas 3.1 to 3.3. -/
theorem lemma34_unit_coefficient (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
      ∃ C x0 : ℝ, 0 < C ∧ ∀ x y : ℝ, x0 ≤ x → Real.sqrt x ≤ y → y ≤ x →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log x ^ B ≤ (q : ℝ) → (q : ℝ) ≤ y / Real.log x ^ B →
        |α - (a : ℝ) / (q : ℝ)| < 1 / (q : ℝ) ^ 2 →
        ∀ z : ℝ, 2 ≤ z → z ≤ y / Real.sqrt x / Real.log x ^ (2 * B) →
        (∫ t in x..2 * x,
          ‖∑ k ∈ (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
              (fun k : ℕ => t < (k : ℝ) ^ 2 ∧ (k : ℝ) ^ 2 ≤ t + y),
            roughWeight z k *
              fourier ((k ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
          C * y ^ 2 / Real.log x ^ A := by
  sorry

/-- PROVED. The summand of the short sum has modulus at most one: page 4
display 10, Phi is 0 or 1, and e(alpha m^2) has modulus one. -/
theorem summand_norm_le_one (z α : ℝ) (m : ℕ) :
    ‖roughWeight z m * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ≤ 1 := by
  rw [norm_mul]
  have h1 : ‖fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ = 1 := Circle.norm_coe _
  rw [h1, mul_one]
  exact roughWeight_norm_le_one z m

/-- PROVED. Counting squares in a short interval: for Y/4 <= t and 0 <= H the
number of m with t < m^2 <= t + H is at most H Y^(-1/2) + 1, since
sqrt (t + H) - sqrt t = H / (sqrt (t + H) + sqrt t) <= H / sqrt Y. -/
theorem card_short_squares_le (S : Finset ℕ) (Y t H : ℝ) (hY : 0 < Y)
    (ht : Y / 4 ≤ t) (hH : 0 ≤ H) :
    (((S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H)).card : ℕ) : ℝ) ≤
      H / Real.sqrt Y + 1 := by
  have ht0 : 0 < t := by linarith
  have hsub : S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H) ⊆
      Finset.Ioc ⌊Real.sqrt t⌋₊ ⌊Real.sqrt (t + H)⌋₊ := by
    intro m hm
    obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hm
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hlt : Real.sqrt t < m := by
      have := Real.sqrt_lt_sqrt ht0.le h1
      rwa [Real.sqrt_sq hm0] at this
    have hle : (m : ℝ) ≤ Real.sqrt (t + H) := Real.le_sqrt_of_sq_le h2
    refine Finset.mem_Ioc.mpr ⟨?_, ?_⟩
    · have := Nat.floor_le (Real.sqrt_nonneg t)
      exact_mod_cast (lt_of_le_of_lt this hlt)
    · exact Nat.le_floor hle
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Ioc] at hcard
  have hmono : ⌊Real.sqrt t⌋₊ ≤ ⌊Real.sqrt (t + H)⌋₊ :=
    Nat.floor_le_floor (Real.sqrt_le_sqrt (by linarith))
  have hcast : (((⌊Real.sqrt (t + H)⌋₊ - ⌊Real.sqrt t⌋₊ : ℕ)) : ℝ) ≤
      Real.sqrt (t + H) - Real.sqrt t + 1 := by
    rw [Nat.cast_sub hmono]
    have a1 := Nat.floor_le (Real.sqrt_nonneg (t + H))
    have a2 := Nat.lt_floor_add_one (Real.sqrt t)
    linarith
  have hst : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht0
  have hsY : Real.sqrt Y ≤ 2 * Real.sqrt t := by
    have : Real.sqrt Y = 2 * Real.sqrt (Y / 4) := by
      rw [Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4)]
      have : Real.sqrt 4 = 2 := by
        rw [show (4:ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
      rw [this]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ht) (by norm_num)
  have hdiff : Real.sqrt (t + H) - Real.sqrt t ≤ H / Real.sqrt Y := by
    have hsY0 : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY
    have hsH : Real.sqrt t ≤ Real.sqrt (t + H) := Real.sqrt_le_sqrt (by linarith)
    have hprod : (Real.sqrt (t + H) - Real.sqrt t) * (Real.sqrt (t + H) + Real.sqrt t) = H := by
      have e1 := Real.sq_sqrt (show (0:ℝ) ≤ t + H by linarith)
      have e2 := Real.sq_sqrt ht0.le
      nlinarith
    rw [le_div_iff₀ hsY0]
    have hd0 : 0 ≤ Real.sqrt (t + H) - Real.sqrt t := by linarith
    calc (Real.sqrt (t + H) - Real.sqrt t) * Real.sqrt Y
        ≤ (Real.sqrt (t + H) - Real.sqrt t) * (Real.sqrt (t + H) + Real.sqrt t) :=
          mul_le_mul_of_nonneg_left (by linarith) hd0
      _ = H := hprod
  have : ((S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H)).card : ℝ) ≤
      (((⌊Real.sqrt (t + H)⌋₊ - ⌊Real.sqrt t⌋₊ : ℕ)) : ℝ) := by exact_mod_cast hcard
  linarith

/-- PROVED. The squared modulus of the short sum is at most (H Y^(-1/2) + 1)^2
for Y/4 <= t: the trivial bound, term count times the bound one on each term. -/
theorem short_sum_sq_le (S : Finset ℕ) (z α Y t H : ℝ) (hY : 0 < Y)
    (ht : Y / 4 ≤ t) (hH : 0 ≤ H) :
    ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        roughWeight z m * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2 ≤
      (H / Real.sqrt Y + 1) ^ 2 := by
  have h1 : ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        roughWeight z m * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ≤
      H / Real.sqrt Y + 1 := by
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ 1 (fun m _ => summand_norm_le_one z α m)).trans ?_
    rw [nsmul_eq_mul, mul_one]
    exact card_short_squares_le S Y t H hY ht hH
  exact pow_le_pow_left₀ (norm_nonneg _) h1 2

/-- PROVED. P0088 page 15, the square window is no restriction away from the top:
for Y/4 <= x <= t <= 2x and t + H < Y, the m in the square window
[sqrt Y / 2, sqrt Y) with t < m^2 <= t + H are exactly the m <= sqrt (3x) with
t < m^2 <= t + H, provided H <= x. -/
theorem window_filter_eq (Y x t H : ℝ) (hx : Y / 4 ≤ x)
    (hxt : x ≤ t) (ht2 : t ≤ 2 * x) (hHx : H ≤ x) (htY : t + H < Y) :
    (squareWindow Y).filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H) =
      (Finset.range (⌊Real.sqrt (3 * x)⌋₊ + 1)).filter
        (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H) := by
  ext m
  simp only [squareWindow, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨⟨-, -, -⟩, h1, h2⟩
    refine ⟨Nat.lt_succ_of_le (Nat.le_floor (Real.le_sqrt_of_sq_le (by linarith))), h1, h2⟩
  · rintro ⟨-, h1, h2⟩
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hmY : (m : ℝ) < Real.sqrt Y := by
      rw [Real.lt_sqrt hm0]; linarith
    have hlo : Real.sqrt Y / 2 ≤ m := by
      have hs4 : Real.sqrt Y / 2 = Real.sqrt (Y / 4) := by
        rw [Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4)]
        have : Real.sqrt 4 = 2 := by
          rw [show (4:ℝ) = 2 ^ 2 by norm_num]; exact Real.sqrt_sq (by norm_num)
        rw [this]
      rw [hs4]
      have : Real.sqrt (Y / 4) ≤ Real.sqrt ((m : ℝ) ^ 2) := Real.sqrt_le_sqrt (by linarith)
      rwa [Real.sqrt_sq hm0] at this
    refine ⟨⟨Nat.lt_succ_of_le (Nat.le_floor hmY.le), hlo, hmY⟩, h1, h2⟩

/-- PROVED. The large X facts used to check the hypotheses of Lemma 3.4 in the
block range: log X >= 1, (log X)^B >= 2, (log X)^(6B) <= X^(eps (3/8 - eps/4)),
4 X^(1/2) <= X^(7/12) and x0 <= X^(7/12) / 4. -/
theorem block_large_X (B ε x0 : ℝ) (hB : 0 < B) (hε : 0 < ε) (hε' : ε ≤ 7 / 18) :
    ∃ X1 : ℝ, 2 ≤ X1 ∧ ∀ X : ℝ, X1 ≤ X →
      1 ≤ Real.log X ∧ 2 ≤ Real.log X ^ B ∧
      Real.log X ^ (6 * B) ≤ X ^ (ε * (3 / 8 - ε / 4)) ∧
      4 * X ^ (1 / 2 : ℝ) ≤ X ^ (7 / 12 : ℝ) ∧ x0 ≤ X ^ (7 / 12 : ℝ) / 4 := by
  have hδ : 0 < ε * (3 / 8 - ε / 4) := mul_pos hε (by linarith)
  have e1 : ∀ᶠ X : ℝ in Filter.atTop, 1 ≤ Real.log X :=
    Real.tendsto_log_atTop.eventually_ge_atTop 1
  have e2 : ∀ᶠ X : ℝ in Filter.atTop, 2 ≤ Real.log X ^ B :=
    ((tendsto_rpow_atTop hB).comp Real.tendsto_log_atTop).eventually_ge_atTop 2
  have e3 : ∀ᶠ X : ℝ in Filter.atTop,
      ‖Real.log X ^ (6 * B)‖ ≤ 1 * ‖X ^ (ε * (3 / 8 - ε / 4))‖ :=
    (isLittleO_log_rpow_rpow_atTop (6 * B) hδ).bound one_pos
  have e4 : ∀ᶠ X : ℝ in Filter.atTop, 4 ≤ X ^ (1 / 12 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 1 / 12)).eventually_ge_atTop 4
  have e5 : ∀ᶠ X : ℝ in Filter.atTop, 4 * x0 ≤ X ^ (7 / 12 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 7 / 12)).eventually_ge_atTop (4 * x0)
  have e6 : ∀ᶠ X : ℝ in Filter.atTop, (1 : ℝ) ≤ X := Filter.eventually_ge_atTop 1
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (e1.and (e2.and (e3.and (e4.and (e5.and e6)))))
  refine ⟨max N 2, le_max_right _ _, fun X hX => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hN X ((le_max_left _ _).trans hX)
  have hX0 : 0 ≤ X := by linarith
  refine ⟨h1, h2, ?_, ?_, by linarith⟩
  · have a : 0 ≤ Real.log X ^ (6 * B) := Real.rpow_nonneg (by linarith) _
    have b : 0 ≤ X ^ (ε * (3 / 8 - ε / 4)) := Real.rpow_nonneg hX0 _
    rwa [Real.norm_of_nonneg a, Real.norm_of_nonneg b, one_mul] at h3
  · have : X ^ (7 / 12 : ℝ) = X ^ (1 / 2 : ℝ) * X ^ (1 / 12 : ℝ) := by
      rw [← Real.rpow_add (by linarith)]; norm_num
    rw [this, mul_comm 4]
    exact mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg hX0 _)

/-- PROVED. P0088 display 41 from the minor arc data of page 15: q P <= H and
|q alpha - a| < P / H give |alpha - a/q| < q^(-2). -/
theorem dirichlet_close (P H α : ℝ) (q : ℕ) (a : ℤ) (hH0 : 0 < H)
    (hq0 : (0 : ℝ) < q) (hqP' : (q : ℝ) * P ≤ H)
    (hclose : |(q : ℝ) * α - a| < (H / P)⁻¹) :
    |α - (a : ℝ) / (q : ℝ)| < 1 / (q : ℝ) ^ 2 := by
  have e : α - (a : ℝ) / q = ((q : ℝ) * α - a) / q := by field_simp
  rw [e, abs_div, abs_of_pos hq0, div_lt_iff₀ hq0]
  have h2 : (H / P)⁻¹ ≤ 1 / (q : ℝ) ^ 2 * q := by
    rw [inv_div, show (1 : ℝ) / (q : ℝ) ^ 2 * q = 1 / q by field_simp,
      div_le_div_iff₀ hH0 hq0]
    linarith
  linarith

/-- PROVED. The hypotheses of Lemma 3.4 at x with Y/4 <= x <= Y, Y = windowY X eps,
y = H, z, in the block range of page 15, for X past block_large_X. Also returns
sqrt Y <= H, H <= Y/4, H P^4 <= Y with P = (log X)^B, and log X <= 2 log x. -/
theorem block_hyps (B ε X H x z α : ℝ) (q : ℕ) (a : ℤ) (hB : 0 < B) (hε : 0 < ε)
    (hε' : ε ≤ 7 / 18) (hX2 : 2 ≤ X)
    (hL1 : 1 ≤ Real.log X) (hP2 : 2 ≤ Real.log X ^ B)
    (hgap : Real.log X ^ (6 * B) ≤ X ^ (ε * (3 / 8 - ε / 4)))
    (hhalf : 4 * X ^ (1 / 2 : ℝ) ≤ X ^ (7 / 12 : ℝ))
    (hlo : X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H)
    (hhi : H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ))
    (hqP : Real.log X ^ B < (q : ℝ)) (hqQ : (q : ℝ) ≤ H / Real.log X ^ B)
    (hclose : |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹)
    (hz : z ≤ windowY X ε ^ (1 / 6 + ε / 2))
    (hx1 : windowY X ε / 4 ≤ x) (hx2 : x ≤ windowY X ε) :
    Real.sqrt x ≤ H ∧ H ≤ x ∧ Real.log x ^ B ≤ (q : ℝ) ∧ (q : ℝ) ≤ H / Real.log x ^ B ∧
      |α - (a : ℝ) / (q : ℝ)| < 1 / (q : ℝ) ^ 2 ∧
      z ≤ H / Real.sqrt x / Real.log x ^ (2 * B) ∧
      Real.sqrt (windowY X ε) ≤ H ∧ H ≤ windowY X ε / 4 ∧
      H * (Real.log X ^ B) ^ 4 ≤ windowY X ε ∧
      0 < Real.log x ∧ Real.log X ≤ 2 * Real.log x := by
  set L := Real.log X with hLdef
  set P := L ^ B with hPdef
  set Y := windowY X ε with hYdef
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hP0 : 0 < P := by linarith
  have hP4 : 0 < P ^ 4 := by positivity
  have hzpow : P ^ (-4 : ℤ) = (P ^ 4)⁻¹ := by
    rw [zpow_neg]; norm_cast
  rw [hzpow] at hlo hhi
  have hlo' : X ^ (7 / 18 + ε) ≤ H * P ^ 4 := by
    rw [← div_le_iff₀ hP4]; simpa [div_eq_mul_inv] using hlo
  have hhi' : H * P ^ 4 ≤ Y := by
    rw [← le_div_iff₀ hP4]; simpa [div_eq_mul_inv] using hhi
  -- P^6 = L^(6B)
  have hP6 : P ^ 6 = L ^ (6 * B) := by
    rw [hPdef, ← Real.rpow_natCast, ← Real.rpow_mul hL0]; norm_num; ring_nf
  have hP2' : P ^ 2 = L ^ (2 * B) := by
    rw [hPdef, ← Real.rpow_natCast, ← Real.rpow_mul hL0]; norm_num; ring_nf
  have hP6le : P ^ 6 ≤ X ^ (ε * (3 / 8 - ε / 4)) := hP6 ▸ hgap
  have hP4le6 : P ^ 4 ≤ P ^ 6 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hP4ge : 4 ≤ P ^ 4 := by
    have := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hP2 4
    norm_num at this; linarith
  -- Y facts
  have hYeq : Y = X ^ (7 / 12 + ε / 2) := rfl
  have hY712 : X ^ (7 / 12 : ℝ) ≤ Y :=
    Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
  have hYX : Y ≤ X := by
    have := Real.rpow_le_rpow_of_exponent_le hX1 (show 7 / 12 + ε / 2 ≤ (1:ℝ) by linarith)
    rwa [Real.rpow_one] at this
  have hsq0 : 0 < X ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hX0 _
  have hY0 : 0 < Y := by linarith
  have hx0 : 0 < x := by linarith
  have hxX : x ≤ X := hx2.trans hYX
  have hxhalf : X ^ (1 / 2 : ℝ) ≤ x := by linarith
  -- logs
  have hlogx : Real.log X ≤ 2 * Real.log x := by
    have := Real.log_le_log hsq0 hxhalf
    rw [Real.log_rpow hX0] at this
    linarith
  have hlogx0 : 0 < Real.log x := by linarith
  have hlogxL : Real.log x ≤ L := Real.log_le_log hx0 hxX
  have hlxB : Real.log x ^ B ≤ P := Real.rpow_le_rpow hlogx0.le hlogxL hB.le
  have hlxB0 : 0 < Real.log x ^ B := Real.rpow_pos_of_pos hlogx0 _
  have hlx2B : Real.log x ^ (2 * B) ≤ P ^ 2 := by
    rw [hP2']; exact Real.rpow_le_rpow hlogx0.le hlogxL (by linarith)
  have hlx2B0 : 0 < Real.log x ^ (2 * B) := Real.rpow_pos_of_pos hlogx0 _
  -- sqrt Y <= H
  have hsqY : Real.sqrt Y = X ^ ((7 / 12 + ε / 2) / 2) := by
    rw [Real.sqrt_eq_rpow, hYeq, ← Real.rpow_mul hX0.le]; ring_nf
  have hsqYH : Real.sqrt Y * P ^ 4 ≤ X ^ (7 / 18 + ε) := by
    calc Real.sqrt Y * P ^ 4 ≤ X ^ ((7 / 12 + ε / 2) / 2) * X ^ (ε * (3 / 8 - ε / 4)) := by
          rw [hsqY]
          exact mul_le_mul_of_nonneg_left (hP4le6.trans hP6le) (Real.rpow_nonneg hX0.le _)
      _ = X ^ ((7 / 12 + ε / 2) / 2 + ε * (3 / 8 - ε / 4)) := by
          rw [Real.rpow_add hX0]
      _ ≤ X ^ (7 / 18 + ε) := Real.rpow_le_rpow_of_exponent_le hX1 (by nlinarith)
  have hHY : Real.sqrt Y ≤ H := by
    have := hsqYH.trans hlo'
    exact le_of_mul_le_mul_right this hP4
  have hH0 : 0 < H := lt_of_lt_of_le (Real.sqrt_pos.mpr hY0) hHY
  have hHY4 : H ≤ Y / 4 := by
    rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
    nlinarith
  have hsqx : Real.sqrt x ≤ Real.sqrt Y := Real.sqrt_le_sqrt hx2
  have hsqx0 : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  -- q facts
  have hq1 : (1 : ℝ) ≤ q := by linarith
  have hq0 : (0 : ℝ) < q := by linarith
  have hqP' : (q : ℝ) * P ≤ H := by rwa [le_div_iff₀ hP0] at hqQ
  refine ⟨hsqx.trans hHY, hHY4.trans hx1, hlxB.trans hqP.le,
    hqQ.trans (div_le_div_of_nonneg_left hH0.le hlxB0 hlxB), ?_, ?_, hHY, hHY4, hhi',
    hlogx0, hlogx⟩
  · exact dirichlet_close P H α q a hH0 hq0 hqP' hclose
  · -- z <= H / sqrt x / (log x)^(2B)
    have hz' : z ≤ X ^ ((7 / 12 + ε / 2) * (1 / 6 + ε / 2)) := by
      rw [Real.rpow_mul hX0.le]; exact hz
    have key : X ^ ((7 / 12 + ε / 2) * (1 / 6 + ε / 2)) * (Real.sqrt Y * P ^ 6) ≤
        X ^ (7 / 18 + ε) := by
      calc X ^ ((7 / 12 + ε / 2) * (1 / 6 + ε / 2)) * (Real.sqrt Y * P ^ 6)
          ≤ X ^ ((7 / 12 + ε / 2) * (1 / 6 + ε / 2)) *
              (X ^ ((7 / 12 + ε / 2) / 2) * X ^ (ε * (3 / 8 - ε / 4))) := by
            rw [hsqY]
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hP6le (Real.rpow_nonneg hX0.le _))
              (Real.rpow_nonneg hX0.le _)
        _ = X ^ (7 / 18 + ε) := by
            rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]; ring_nf
    have hden : Real.sqrt x * Real.log x ^ (2 * B) ≤ Real.sqrt Y * P ^ 2 :=
      mul_le_mul hsqx hlx2B hlx2B0.le (Real.sqrt_nonneg _)
    rw [div_div, le_div_iff₀ (mul_pos hsqx0 hlx2B0)]
    have hz0 : 0 ≤ X ^ ((7 / 12 + ε / 2) * (1 / 6 + ε / 2)) := Real.rpow_nonneg hX0.le _
    have hzz : 0 ≤ z ∨ z < 0 := le_or_gt 0 z
    rcases hzz with hzn | hzn
    · calc z * (Real.sqrt x * Real.log x ^ (2 * B))
          ≤ X ^ ((7 / 12 + ε / 2) * (1 / 6 + ε / 2)) * (Real.sqrt Y * P ^ 2) :=
            mul_le_mul hz' hden (by positivity) hz0
        _ ≤ H := by
            have h6 : X ^ ((7 / 12 + ε / 2) * (1 / 6 + ε / 2)) * (Real.sqrt Y * P ^ 6) ≤
                H * P ^ 4 := key.trans hlo'
            have : X ^ ((7 / 12 + ε / 2) * (1 / 6 + ε / 2)) * (Real.sqrt Y * P ^ 6) =
                (X ^ ((7 / 12 + ε / 2) * (1 / 6 + ε / 2)) * (Real.sqrt Y * P ^ 2)) * P ^ 4 := by
              ring
            rw [this] at h6
            exact le_of_mul_le_mul_right h6 hP4
    · have : z * (Real.sqrt x * Real.log x ^ (2 * B)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hzn.le (by positivity)
      linarith

/-- PROVED. Page 15 bookkeeping: with log X <= 2 log x, the saving (log x)^(-A)
of Lemma 3.4 is at most 2^A (log X)^(-A). -/
theorem log_saving_conv (C H x L A : ℝ) (hC : 0 ≤ C) (hA : 0 < A) (hL : 0 < L)
    (_hlx0 : 0 < Real.log x) (hlogx : L ≤ 2 * Real.log x) :
    C * H ^ 2 / Real.log x ^ A ≤ C * 2 ^ A * H ^ 2 / L ^ A := by
  have h1 : (L / 2) ^ A ≤ Real.log x ^ A :=
    Real.rpow_le_rpow (by positivity) (by linarith) hA.le
  have h2 : (L / 2) ^ A = L ^ A / 2 ^ A := Real.div_rpow hL.le (by norm_num) A
  have hLA : 0 < L ^ A := Real.rpow_pos_of_pos hL A
  have h2A : 0 < (2 : ℝ) ^ A := Real.rpow_pos_of_pos (by norm_num) A
  calc C * H ^ 2 / Real.log x ^ A ≤ C * H ^ 2 / (L / 2) ^ A :=
        div_le_div_of_nonneg_left (by positivity) (by rw [h2]; positivity) h1
    _ = C * 2 ^ A * H ^ 2 / L ^ A := by
        rw [h2]; field_simp

/-- PROVED. The last stretch [Y - 2H, Y] of the right half: length 2H times the
trivial bound (H Y^(-1/2) + 1)^2 <= 4 H^2 / Y, then H P^4 <= Y and
P^4 = (log X)^(4B) >= (log X)^A for 4B >= A. -/
theorem tail_arith (H Y L A B : ℝ) (hY : 0 < Y) (hsY : Real.sqrt Y ≤ H)
    (hHP : H * (L ^ B) ^ 4 ≤ Y) (hL1 : 1 ≤ L) (hBA : A / 4 ≤ B) :
    (Y - (Y - 2 * H)) * (H / Real.sqrt Y + 1) ^ 2 ≤ 8 * H ^ 2 / L ^ A := by
  have hs0 : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY
  have hH0 : 0 < H := lt_of_lt_of_le hs0 hsY
  have hL0 : 0 ≤ L := by linarith
  have hone : 1 ≤ H / Real.sqrt Y := by rw [le_div_iff₀ hs0]; linarith
  have hb : H / Real.sqrt Y + 1 ≤ 2 * (H / Real.sqrt Y) := by linarith
  have hsq : (Real.sqrt Y) ^ 2 = Y := Real.sq_sqrt hY.le
  have hP4 : (L ^ B) ^ 4 = L ^ (4 * B) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL0]; norm_num; ring_nf
  have hLA : L ^ A ≤ (L ^ B) ^ 4 := by
    rw [hP4]; exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hLA0 : 0 < L ^ A := Real.rpow_pos_of_pos (by linarith) A
  have step1 : (Y - (Y - 2 * H)) * (H / Real.sqrt Y + 1) ^ 2 ≤ 8 * H ^ 3 / Y := by
    have : (H / Real.sqrt Y + 1) ^ 2 ≤ (2 * (H / Real.sqrt Y)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hb 2
    have e : (Y - (Y - 2 * H)) * (2 * (H / Real.sqrt Y)) ^ 2 = 8 * H ^ 3 / Y := by
      have h4 : (2 * (H / Real.sqrt Y)) ^ 2 = 4 * H ^ 2 / Y := by
        rw [mul_pow, div_pow, hsq]; ring
      rw [h4]; field_simp; ring
    calc (Y - (Y - 2 * H)) * (H / Real.sqrt Y + 1) ^ 2
        ≤ (Y - (Y - 2 * H)) * (2 * (H / Real.sqrt Y)) ^ 2 :=
          mul_le_mul_of_nonneg_left this (by linarith)
      _ = 8 * H ^ 3 / Y := e
  have step2 : 8 * H ^ 3 / Y ≤ 8 * H ^ 2 / L ^ A := by
    rw [div_le_div_iff₀ hY hLA0]
    have : H * L ^ A ≤ Y := (mul_le_mul_of_nonneg_left hLA hH0.le).trans hHP
    nlinarith [sq_nonneg H]
  exact step1.trans step2

/-- PROVED from lemma34_unit_coefficient. The exact statement of the leaf
Split1122KLFirstRoughHalves.block_rough_left_half: Lemma 3.4 with x = Y/4,
y = H, z, on [Y/4, Y/2], where the square window filter is no restriction. -/
theorem block_rough_left_half_of_lemma34 (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in windowY X ε / 4..windowY X ε / 2,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, hlem⟩ := lemma34_unit_coefficient A hA
  refine ⟨max B1 (A / 4), lt_max_of_lt_left hB1, fun B hB ε hε hε' => ?_⟩
  have hBB1 : B1 ≤ B := (le_max_left _ _).trans hB
  have hBpos : 0 < B := hB1.trans_le hBB1
  obtain ⟨C, x0, hC, hL⟩ := hlem B hBB1
  obtain ⟨X1, hX1, hbig⟩ := block_large_X B ε x0 hBpos hε hε'
  refine ⟨C * 2 ^ A, X1, by positivity, hX1, ?_⟩
  intro X H hX hlo hhi α q a hcop hqP hqQ hclose z hz2 hz
  obtain ⟨hL1, hP2, hgap, hhalf, hx0⟩ := hbig X hX
  have hX2 : 2 ≤ X := hX1.trans hX
  have hYge : X ^ (7 / 12 : ℝ) ≤ windowY X ε :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hY0 : 0 < windowY X ε := Real.rpow_pos_of_pos (by linarith) _
  obtain ⟨hsx, hHx, hq1, hq2, hdir, hzz, -, -, -, hlx0, hlogx⟩ :=
    block_hyps B ε X H (windowY X ε / 4) z α q a hBpos hε hε' hX2 hL1 hP2 hgap hhalf
      hlo hhi hqP hqQ hclose hz le_rfl (by linarith)
  have hmain := hL (windowY X ε / 4) H (by linarith) hsx hHx α q a hcop hq1 hq2 hdir
    z hz2.le hzz
  rw [show 2 * (windowY X ε / 4) = windowY X ε / 2 by ring] at hmain
  have hcongr : (∫ t in windowY X ε / 4..windowY X ε / 2,
      ‖∑ m ∈ (squareWindow (windowY X ε)).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        roughWeight z m * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) =
      ∫ t in windowY X ε / 4..windowY X ε / 2,
      ‖∑ m ∈ (Finset.range (⌊Real.sqrt (3 * (windowY X ε / 4))⌋₊ + 1)).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        roughWeight z m * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    simp only
    rw [window_filter_eq (windowY X ε) (windowY X ε / 4) t H le_rfl ht.1
      (by linarith [ht.2]) hHx (by linarith [ht.2])]
  rw [hcongr]
  exact hmain.trans (log_saving_conv C H _ _ A hC.le hA (by linarith) hlx0 hlogx)

/-- PROVED from lemma34_unit_coefficient. The exact statement of the leaf
Split1122KLFirstRoughHalves.block_rough_right_half: Lemma 3.4 with x = Y/2,
y = H, z, on [Y/2, Y - 2H], where the square window filter is no restriction,
plus the trivial bound on [Y - 2H, Y], at most 8 H^2 (log X)^(-A). -/
theorem block_rough_right_half_of_lemma34 (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in windowY X ε / 2..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, hlem⟩ := lemma34_unit_coefficient A hA
  refine ⟨max B1 (A / 4), lt_max_of_lt_left hB1, fun B hB ε hε hε' => ?_⟩
  have hBB1 : B1 ≤ B := (le_max_left _ _).trans hB
  have hBA : A / 4 ≤ B := (le_max_right _ _).trans hB
  have hBpos : 0 < B := hB1.trans_le hBB1
  obtain ⟨C, x0, hC, hL⟩ := hlem B hBB1
  obtain ⟨X1, hX1, hbig⟩ := block_large_X B ε x0 hBpos hε hε'
  refine ⟨C * 2 ^ A + 8, X1, by positivity, hX1, ?_⟩
  intro X H hX hlo hhi α q a hcop hqP hqQ hclose z hz2 hz
  obtain ⟨hL1, hP2, hgap, hhalf, hx0⟩ := hbig X hX
  have hX2 : 2 ≤ X := hX1.trans hX
  have hYge : X ^ (7 / 12 : ℝ) ≤ windowY X ε :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hY0 : 0 < windowY X ε := Real.rpow_pos_of_pos (by linarith) _
  obtain ⟨hsx, hHx, hq1, hq2, hdir, hzz, hsY, hH4, hHP, hlx0, hlogx⟩ :=
    block_hyps B ε X H (windowY X ε / 2) z α q a hBpos hε hε' hX2 hL1 hP2 hgap hhalf
      hlo hhi hqP hqQ hclose hz (by linarith) (by linarith)
  have hH0 : 0 < H := lt_of_lt_of_le (Real.sqrt_pos.mpr hY0) hsY
  have hmain := hL (windowY X ε / 2) H (by linarith) hsx hHx α q a hcop hq1 hq2 hdir
    z hz2.le hzz
  rw [show 2 * (windowY X ε / 2) = windowY X ε by ring] at hmain
  have hint := fun (S : Finset ℕ) (u v : ℝ) => short_sum_sq_intervalIntegrable S
      (fun m : ℕ => roughWeight z m *
        fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) H u v
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hint (squareWindow (windowY X ε)) (windowY X ε / 2) (windowY X ε - 2 * H))
    (hint (squareWindow (windowY X ε)) (windowY X ε - 2 * H) (windowY X ε))]
  have hcongr : (∫ t in windowY X ε / 2..windowY X ε - 2 * H,
      ‖∑ m ∈ (squareWindow (windowY X ε)).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        roughWeight z m * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) =
      ∫ t in windowY X ε / 2..windowY X ε - 2 * H,
      ‖∑ m ∈ (Finset.range (⌊Real.sqrt (3 * (windowY X ε / 2))⌋₊ + 1)).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        roughWeight z m * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by linarith)] at ht
    simp only
    rw [window_filter_eq (windowY X ε) (windowY X ε / 2) t H (by linarith) ht.1
      (by linarith [ht.2]) hHx (by linarith [ht.2])]
  have p1 : (∫ t in windowY X ε / 2..windowY X ε - 2 * H,
      ‖∑ m ∈ (squareWindow (windowY X ε)).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        roughWeight z m * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
      C * 2 ^ A * H ^ 2 / Real.log X ^ A := by
    rw [hcongr]
    refine le_trans ?_ (hmain.trans
      (log_saving_conv C H _ _ A hC.le hA (by linarith) hlx0 hlogx))
    exact intervalIntegral.integral_mono_interval le_rfl (by linarith) (by linarith)
      (Filter.Eventually.of_forall (fun t => by simp only [Pi.zero_apply]; positivity))
      (hint _ _ _)
  have p2 : (∫ t in windowY X ε - 2 * H..windowY X ε,
      ‖∑ m ∈ (squareWindow (windowY X ε)).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        roughWeight z m * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
      8 * H ^ 2 / Real.log X ^ A := by
    refine le_trans ?_ (tail_arith H (windowY X ε) (Real.log X) A B hY0 hsY hHP hL1 hBA)
    refine le_trans (intervalIntegral.integral_mono_on (by linarith) (hint _ _ _)
      intervalIntegrable_const (fun t ht => short_sum_sq_le _ z α (windowY X ε) t H hY0
        (by linarith [ht.1]) hH0.le)) ?_
    rw [intervalIntegral.integral_const, smul_eq_mul]
  have e : (C * 2 ^ A + 8) * H ^ 2 / Real.log X ^ A =
      C * 2 ^ A * H ^ 2 / Real.log X ^ A + 8 * H ^ 2 / Real.log X ^ A := by ring
  rw [e]
  exact add_le_add p1 p2

end LeanLab.KumchevLiu2007.Split1122KLLemma34M1

#print axioms LeanLab.KumchevLiu2007.Split1122KLLemma34M1.lemma34_unit_coefficient
#print axioms LeanLab.KumchevLiu2007.Split1122KLLemma34M1.summand_norm_le_one
#print axioms LeanLab.KumchevLiu2007.Split1122KLLemma34M1.card_short_squares_le
#print axioms LeanLab.KumchevLiu2007.Split1122KLLemma34M1.short_sum_sq_le
#print axioms LeanLab.KumchevLiu2007.Split1122KLLemma34M1.window_filter_eq
#print axioms LeanLab.KumchevLiu2007.Split1122KLLemma34M1.block_large_X
#print axioms LeanLab.KumchevLiu2007.Split1122KLLemma34M1.dirichlet_close
#print axioms LeanLab.KumchevLiu2007.Split1122KLLemma34M1.block_hyps
#print axioms LeanLab.KumchevLiu2007.Split1122KLLemma34M1.log_saving_conv
#print axioms LeanLab.KumchevLiu2007.Split1122KLLemma34M1.tail_arith
#print axioms LeanLab.KumchevLiu2007.Split1122KLLemma34M1.block_rough_left_half_of_lemma34
#print axioms LeanLab.KumchevLiu2007.Split1122KLLemma34M1.block_rough_right_half_of_lemma34
