/-
Kumchev and Liu 2007, P0088, arXiv 0801.0130. SPLIT of
`F2085.rough_a23_hyp_F2085`, DecompF2085.lean, ROUTE BURST S98 burst-20261122.

The target is hypothesis A2.3 of page 7 for the rough weight at the cutoff
z0 = Y^(1/4) P^(-2), P = (log X)^B, in the range Y^(2/3 + eta) at most H at most
Y over (log X)^A, with Y = windowY X eps. The proof of page 15 after display 52
is followed, with the intermediate cutoff z1 = Y^(1/6 + eta/2) chosen from eta,
so that z1 Y^(1/2) = Y^(2/3 + eta/2) is below H by the power Y^(eta/2), which is
the room Lemma 3.4 of page 11 needs for its factor L^(-2B).

* `leaf_first_sum_F2085`, Lemma 3.4 with x = Y, y = H, (m, k) = (1, m) and a
  sieve cutoff z at most z1. LEAF, HARD.
* `leaf_second_sum_F2085`, Lemma 3.4 with x = Y, y = H, (m, k) = (p, m / p),
  z = z1, summed over the primes p from z1 to z0. LEAF, HARD.
* `display52_identity_eta`, the Buchstab identity of display 52 with the cutoff
  z1 = Y^(1/6 + kappa/2) for any kappa at least 0. Proved, from
  `Eq33RouteD.buchstab_core`.
* `logPower_le_H_F2085`, Q = H / P is at least one in this range. Proved.
* Dirichlet's result `Eq33RouteD.minor_arc_dirichlet` and the difference
  bound `Eq33RouteD.short_sum_sub_mean_square_le` are reused.

The assembly `rough_a23_hyp_F2085_split` has no sorry of its own.
Because H is at most Y here, the QUESTION of Eq33RouteD about H above Y does
not arise in these two leaves.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.DecompF2085
import LeanLab.KumchevLiu2007.Eq33RouteD

namespace LeanLab.KumchevLiu2007.F2085

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d Task628
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF: P0088 page 11 Lemma 3.4, as applied on page 15 after display 52 to the
first sum of display 52, with x = Y, y = H and (m, k) = (1, m), in the range
Y^(2/3 + eta) at most H at most Y (log X)^(-A) of hypothesis A2.3 on page 7.
The sieve cutoff z is any real at most z1 = Y^(1/6 + eta/2); the lemma is
uniform in z, and z1 Y^(1/2) L^(2B) is at most H for large X. The hypothesis on
alpha is display 41 with y = H, P < q at most H / P and |q alpha - a| < P / H,
P = (log X)^B. Class HARD. -/
theorem leaf_first_sum_F2085 (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
      ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∀ η : ℝ, 0 < η →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ, X0 ≤ X →
        windowY X ε ^ (2 / 3 + η) ≤ H → H ≤ windowY X ε / Real.log X ^ A →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, z ≤ windowY X ε ^ (1 / 6 + η / 2) →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- LEAF: P0088 page 11 Lemma 3.4, as applied on page 15 after display 52 to the
second sum of display 52, with x = Y, y = H, (m, k) = (p, m / p) and
z = z1 = Y^(1/6 + eta/2), the primes p running from z1 up to the cutoff
z0 = Y^(1/4) P^(-2) of page 8 display 34, in the range of hypothesis A2.3 on
page 7. The paper splits the p range into O(log X) dyadic blocks M at most
x^(1/4) L^(-2B) and applies the lemma with A + 2 to each. The hypothesis on
alpha is display 41 with y = H. Class HARD. -/
theorem leaf_second_sum_F2085 (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
      ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∀ η : ℝ, 0 < η →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ, X0 ≤ X →
        windowY X ε ^ (2 / 3 + η) ≤ H → H ≤ windowY X ε / Real.log X ^ A →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ (Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + η / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m),
              roughWeight (windowY X ε ^ (1 / 6 + η / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- P0088 page 15 display 52, the Buchstab identity on the window I2, with the
intermediate cutoff z1 = Y^(1/6 + kappa/2) for any kappa at least 0. Same proof
as `Eq33RouteD.display52_identity`, which is the case kappa = eps. -/
theorem display52_identity_eta (B ε κ : ℝ) (hB : 0 < B) (hε : 0 < ε) (hκ : 0 ≤ κ) :
    ∃ X0 : ℝ, 2 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X →
      windowY X ε ^ (1 / 6 + κ / 2) ≤
        windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
      ∀ m ∈ squareWindow (windowY X ε),
        roughWeight (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) m =
          roughWeight (windowY X ε ^ (1 / 6 + κ / 2)) m -
            ∑ p ∈ (Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + κ / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m),
              roughWeight (windowY X ε ^ (1 / 6 + κ / 2)) (m / p) := by
  refine ⟨max 2 (Real.exp (2 ^ (1 / B))), le_max_left _ _, ?_⟩
  intro X hX hz m hm
  have hX2 : 2 ≤ X := (le_max_left _ _).trans hX
  have hXe : Real.exp (2 ^ (1 / B)) ≤ X := (le_max_right _ _).trans hX
  have hY1 : 1 ≤ windowY X ε := by
    unfold windowY
    exact Real.one_le_rpow (by linarith) (by positivity)
  have hY0 : 0 < windowY X ε := by linarith
  have hlog : (2 : ℝ) ^ (1 / B) ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact hXe
  have hP : 2 ≤ Real.log X ^ B := by
    have h := Real.rpow_le_rpow (by positivity) hlog hB.le
    rwa [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hB.ne', Real.rpow_one] at h
  have hmw := (Finset.mem_filter.mp hm).2
  have hsq0 : 0 < Real.sqrt (windowY X ε) := Real.sqrt_pos.mpr hY0
  apply Eq33RouteD.buchstab_core _ _ m (Real.rpow_nonneg hY0.le _) hz
  · have hpow : (windowY X ε ^ (1 / 6 + κ / 2)) ^ 3 =
        windowY X ε ^ ((1 / 6 + κ / 2) * 3) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hY0.le]
      norm_num
    have hs : Real.sqrt (windowY X ε) ≤ windowY X ε ^ ((1 / 6 + κ / 2) * 3) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
    linarith [hmw.2]
  · have h4 : 4 ≤ (Real.log X ^ B) ^ 2 := by nlinarith
    have hw : (Real.log X ^ B) ^ (-2 : ℤ) ≤ 1 / 4 := by
      rw [zpow_neg, zpow_ofNat, one_div]
      exact inv_anti₀ (by norm_num) h4
    have hw0 : 0 < (Real.log X ^ B) ^ (-2 : ℤ) := zpow_pos (by linarith) _
    have hYq : (windowY X ε ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt (windowY X ε) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hY0.le]
      norm_num
    rw [mul_pow, hYq]
    have hw2 : ((Real.log X ^ B) ^ (-2 : ℤ)) ^ 2 ≤ 1 / 2 := by nlinarith
    have hprod := mul_le_mul_of_nonneg_left hw2 hsq0.le
    linarith [hmw.1]
  · have hpos : (0 : ℝ) < m := lt_of_lt_of_le (half_pos hsq0) hmw.1
    exact_mod_cast hpos

/-- P0088 page 4 display 14 in the range of hypothesis A2.3: Q = H P^(-1) is at
least one, since Y^(2/3 + eta) is at least X^(7/18 + eps/3). -/
theorem logPower_le_H_F2085 (B ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ X0 : ℝ, 2 ≤ X0 ∧ ∀ X H : ℝ, X0 ≤ X → windowY X ε ^ (2 / 3 + η) ≤ H →
      Real.log X ^ B ≤ H := by
  obtain ⟨X0, hX0, k⟩ := Eq33RouteD.logPower_le_H B (ε / 3) (by positivity)
  refine ⟨X0, hX0, fun X H hX hH => k X H hX ?_⟩
  have hX1 : 1 ≤ X := by linarith
  refine le_trans ?_ hH
  unfold windowY
  rw [← Real.rpow_mul (by linarith)]
  exact Real.rpow_le_rpow_of_exponent_le hX1 (by nlinarith)

/-- Assembly. The exact statement of `F2085.rough_a23_hyp_F2085`, from the two
leaves above, with no sorry of its own. Off the major arcs Dirichlet's theorem
gives display 41; if z0 is at most z1 the first leaf applies with z = z0,
otherwise display 52 and the difference bound combine the two leaves. -/
theorem rough_a23_hyp_F2085_split : ∀ A : ℝ, 0 < A → ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B →
    ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 → ∀ η : ℝ, 0 < η →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ, X0 ≤ X →
        windowY X ε ^ (2 / 3 + η) ≤ H → H ≤ windowY X ε / Real.log X ^ A →
        ∀ α : ℝ, α ∉ majorArcs H (Real.log X ^ B) →
        (∫ t in (windowY X ε / 4)..windowY X ε,
          ‖roughShortSum (windowY X ε) (Real.log X ^ B) H α t‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  intro A hA
  obtain ⟨B1, hB1, h1⟩ := leaf_first_sum_F2085 A hA
  obtain ⟨B2, hB2, h2⟩ := leaf_second_sum_F2085 A hA
  refine ⟨max B1 B2, lt_max_of_lt_left hB1, fun B hB ε hε hε' η hη => ?_⟩
  have hBpos : 0 < B := (lt_max_of_lt_left hB1).trans_le hB
  obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B ((le_max_left _ _).trans hB) ε hε hε' η hη
  obtain ⟨C2, X2, hC2, hX2, k2⟩ := h2 B ((le_max_right _ _).trans hB) ε hε hε' η hη
  obtain ⟨X3, hX3, k3⟩ := display52_identity_eta B ε η hBpos hε hη.le
  obtain ⟨X4, hX4, k4⟩ := logPower_le_H_F2085 B ε η hε hη
  refine ⟨2 * C1 + 2 * C2, max X1 (max X2 (max X3 X4)), by positivity,
    hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hH hHX α hα
  have hXa : X1 ≤ X := (le_max_left _ _).trans hX
  have hXb : X2 ≤ X := ((le_max_left _ _).trans (le_max_right _ _)).trans hX
  have hXc : X3 ≤ X :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hX
  have hXd : X4 ≤ X :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hX
  have hX2' : 2 ≤ X := hX1.trans hXa
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hY : 0 < windowY X ε := by
    unfold windowY
    exact Real.rpow_pos_of_pos (by linarith) _
  have hq : 0 ≤ H ^ 2 / Real.log X ^ A := by positivity
  obtain ⟨q, a, hcop, hqP, hqQ, hclose⟩ :=
    Eq33RouteD.minor_arc_dirichlet (Real.rpow_pos_of_pos hL B) (k4 X H hXd hH) hα
  have e1 := k1 X H hXa hH hHX α q a hcop hqP hqQ hclose
  have e2 := k2 X H hXb hH hHX α q a hcop hqP hqQ hclose
  unfold roughShortSum
  by_cases hz : windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ≤
      windowY X ε ^ (1 / 6 + η / 2)
  · refine (e1 _ hz).trans ?_
    have hr : C1 * H ^ 2 / Real.log X ^ A = C1 * (H ^ 2 / Real.log X ^ A) := by ring
    have hr' : (2 * C1 + 2 * C2) * H ^ 2 / Real.log X ^ A =
        (2 * C1 + 2 * C2) * (H ^ 2 / Real.log X ^ A) := by ring
    rw [hr, hr']
    exact mul_le_mul_of_nonneg_right (by linarith) hq
  · have hid := k3 X hXc (not_le.mp hz).le
    refine (Eq33RouteD.short_sum_sub_mean_square_le (squareWindow (windowY X ε)) _ _ _
      (fun m : ℕ => (fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) : ℂ))
      H _ _ _ _ (by linarith) hid (e1 _ le_rfl) e2).trans ?_
    apply le_of_eq
    ring

/-- The split statement is character for character the sealed leaf. -/
example : type_of% @rough_a23_hyp_F2085 := rough_a23_hyp_F2085_split

end LeanLab.KumchevLiu2007.F2085
