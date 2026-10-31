/-
P0095 W. C. Lu 2010, Section 9: the minor arc sup bound from the cited estimate of [12, p. 107]
and Dirichlet's theorem. Unit U-6856, CLOUD MANUAL-M1, 2026-10-21, track T1.

p. 2391: "using a well-known result: if α = hq⁻¹ + θq⁻², (q, h) = 1, |θ| ≤ 1, 1 ≤ q ≤ x, then
Σ_{n≤x} Λ(n)e(nα) ≪_ε (x^{1/2}q^{1/2} + x^{9/10} + xq^{-1/2})x^ε, see [12, p. 107]". This is
`Bound12`, cited. Dirichlet's theorem with Q = N^{3/4} puts every α of the minor arcs, except the
endpoint 1 - 1/Q, within 1/(qQ) of a reduced h/q with P < q ≤ Q, `dirichlet_minor`; then
|S(N - td, N - td - d, α)| ≤ 6C N^{1-c/2+4·10^{-6}}, `minorSup_of_bound12`, which is the field
`minorSup` of `InputsS`. After this unit the Theorem is CONDITIONAL ON (84) or (85), (86) and the
cited [12, p. 107] bound, `lu_of_inputsL`.

AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
Binary Goldbach itself is OPEN.
-/
import Mathlib
import LeanLab.ExceptionalSet.Lu2010Minor

namespace LeanLab.ExceptionalSet.Lu2010Dirichlet
open Real Filter Topology Finset ArithmeticFunction MeasureTheory Complex
  LeanLab.ExceptionalSet LeanLab.ExceptionalSet.Lu2010Assembly LeanLab.ExceptionalSet.Lu2010Lemma1
  LeanLab.ExceptionalSet.Lu2010Orth LeanLab.ExceptionalSet.Lu2010Arcs LeanLab.ExceptionalSet.Lu2010Sec9
  LeanLab.ExceptionalSet.Lu2010Minor

/-- **Cited**, [12, p. 107] as Lu quotes it, p. 2391. -/
def Bound12 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x → ∀ (α : ℝ) (h : ℤ) (q : ℕ), 1 ≤ q →
    (q : ℝ) ≤ x → Int.gcd h q = 1 → |α - h / q| ≤ 1 / (q : ℝ) ^ 2 →
      ‖Ssum x 0 α‖ ≤ C * (x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) + x ^ (9 / 10 : ℝ) +
        x * (q : ℝ) ^ (-(1 / 2) : ℝ)) * x ^ ε

/-- `S(x, y, α) = S(x, 0, α) - S(y, 0, α)` for `0 ≤ y ≤ x`. -/
theorem Ssum_sub {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) (α : ℝ) :
    Ssum x y α = Ssum x 0 α - Ssum y 0 α := by
  have hK : x ≤ (⌊x⌋₊ : ℝ) + 1 := (Nat.lt_floor_add_one x).le
  rw [Ssum_eq_range (K := ⌊x⌋₊ + 1) (by push_cast; linarith),
    Ssum_eq_range (K := ⌊x⌋₊ + 1) (by push_cast; linarith),
    Ssum_eq_range (K := ⌊x⌋₊ + 1) (by push_cast; linarith), ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro n _
  by_cases h1 : y < n
  · by_cases h2 : (n : ℝ) ≤ x
    · have : ¬ (n : ℝ) ≤ y := not_le.mpr h1
      rw [if_pos ⟨h1, h2⟩, if_pos ⟨by linarith, h2⟩, if_neg (fun h => this h.2), sub_zero]
    · rw [if_neg (fun h => h2 h.2), if_neg (fun h => h2 h.2), if_neg (fun h => h2 (by linarith [h.2])), sub_zero]
  · push Not at h1
    rw [if_neg (fun h => not_lt.mpr h1 h.1)]
    by_cases h0 : (0 : ℝ) < n
    · rw [if_pos ⟨h0, by linarith⟩, if_pos ⟨h0, h1⟩, sub_self]
    · rw [if_neg (fun h => h0 h.1), if_neg (fun h => h0 h.1), sub_self]

/-- Dirichlet on the minor arcs: for `P + 1 ≤ Q`, every `α ∈ 𝔪`, `α ≠ 1 - 1/Q`, has a reduced
`h/q` with `P < q ≤ Q` and `|α - h/q| ≤ 1/(qQ)`. -/
theorem dirichlet_minor {N : ℕ} (hQ1 : 1 ≤ QQ N) (hPQ : PP N + 1 ≤ QQ N) (hP0 : 0 < PP N)
    {α : ℝ} (hα : α ∈ per N \ major N) (hαe : α ≠ 1 - 1 / QQ N) :
    ∃ (h : ℤ) (q : ℕ), 1 ≤ q ∧ PP N < q ∧ (q : ℝ) ≤ QQ N ∧ Int.gcd h q = 1 ∧
      |α - h / q| ≤ 1 / (q * QQ N) := by
  obtain ⟨hper, hmaj⟩ := hα
  simp only [per, Set.mem_Ioc] at hper
  obtain ⟨ha1, ha2⟩ := hper
  have hQ0 : 0 < QQ N := by linarith
  set n := ⌊QQ N⌋₊ with hn
  have hn1 : 0 < n := Nat.floor_pos.mpr hQ1
  obtain ⟨j, k, hk0, hkn, hjk⟩ := Real.exists_int_int_abs_mul_sub_le α hn1
  have hnQ : QQ N < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have hkQ : (k : ℝ) ≤ QQ N := by
    have : (k : ℝ) ≤ n := by exact_mod_cast hkn
    linarith [Nat.floor_le hQ0.le]
  have hjk' : |(k : ℝ) * α - j| ≤ 1 / QQ N :=
    hjk.trans (one_div_le_one_div_of_le hQ0 hnQ.le)
  -- reduce by g = gcd
  set g := Int.gcd j k with hg
  have hg0 : 0 < g := Int.gcd_pos_of_ne_zero_right _ hk0.ne'
  obtain ⟨h, hj⟩ : (g : ℤ) ∣ j := Int.gcd_dvd_left j k
  obtain ⟨qz, hq⟩ : (g : ℤ) ∣ k := Int.gcd_dvd_right j k
  have hqz0 : 0 < qz := by
    by_contra hc; push Not at hc
    have : k ≤ 0 := by rw [hq]; exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hc
    omega
  set q := qz.toNat with hqdef
  have hqq : (q : ℤ) = qz := Int.toNat_of_nonneg hqz0.le
  have hq1 : 1 ≤ q := by omega
  have hcop : Int.gcd h q = 1 := by
    rw [hqq]
    have := Int.gcd_div_gcd_div_gcd (i := j) (j := k) hg0
    have e1 : j / (g : ℤ) = h := by rw [hj]; exact Int.mul_ediv_cancel_left _ (by exact_mod_cast hg0.ne')
    have e2 : k / (g : ℤ) = qz := by rw [hq]; exact Int.mul_ediv_cancel_left _ (by exact_mod_cast hg0.ne')
    rwa [e1, e2] at this
  have hgr : (1 : ℝ) ≤ g := by exact_mod_cast hg0
  have hkr : (k : ℝ) = g * q := by rw [hq]; push_cast; rw [← hqq]; push_cast; ring
  have hjr : (j : ℝ) = g * h := by rw [hj]; push_cast; ring
  have hqr1 : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hqQ : (q : ℝ) ≤ QQ N := by
    have : (q : ℝ) ≤ k := by rw [hkr]; nlinarith
    linarith
  have hbound : |α - h / q| ≤ 1 / (q * QQ N) := by
    have e : (k : ℝ) * α - j = (g : ℝ) * (q : ℝ) * (α - h / q) := by rw [hkr, hjr]; field_simp
    rw [e, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (g : ℝ) * (q : ℝ))] at hjk'
    rw [le_div_iff₀ (by positivity)]
    have : (q : ℝ) * |α - h / q| ≤ (g : ℝ) * (q : ℝ) * |α - h / q| := by
      have := mul_le_mul_of_nonneg_right hgr (mul_nonneg (Nat.cast_nonneg q) (abs_nonneg (α - h / q)))
      calc (q : ℝ) * |α - h / q| = 1 * ((q : ℝ) * |α - h / q|) := (one_mul _).symm
        _ ≤ (g : ℝ) * ((q : ℝ) * |α - h / q|) := this
        _ = (g : ℝ) * (q : ℝ) * |α - h / q| := by ring
    have h2 : (q : ℝ) * |α - h / q| ≤ 1 / QQ N := le_trans this hjk'
    rw [le_div_iff₀ hQ0] at h2
    nlinarith [abs_nonneg (α - h / q)]
  refine ⟨h, q, hq1, ?_, hqQ, hcop, hbound⟩
  -- q > P, else α is on a major arc
  by_contra hqP; push Not at hqP
  have hab := abs_le.mp hbound
  have hqpos : (0 : ℝ) < q := by linarith
  have hiq : 1 / (q * QQ N) ≤ 1 / QQ N := by
    apply one_div_le_one_div_of_le hQ0; nlinarith
  rcases lt_or_ge h 0 with hneg | hnn
  · -- h ≤ -1 forces α ≤ -1/Q
    have hh : (h : ℝ) ≤ -1 := by exact_mod_cast (show h ≤ -1 by omega)
    have : α ≤ -1 / QQ N := by
      have e1 : (h : ℝ) / q ≤ -1 / q := div_le_div_of_nonneg_right hh hqpos.le
      have e2 : -1 / (q : ℝ) + 1 / ((q : ℝ) * QQ N) ≤ -1 / QQ N := by
        have key : -1 / (q : ℝ) + 1 / ((q : ℝ) * QQ N) - -1 / QQ N =
            ((q : ℝ) + 1 - QQ N) / ((q : ℝ) * QQ N) := by
          field_simp; ring
        have : ((q : ℝ) + 1 - QQ N) / ((q : ℝ) * QQ N) ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
        linarith
      have e3 := hab.2
      linarith
    linarith
  rcases lt_or_ge h q with hlt | hge
  · -- 0 ≤ h ≤ q - 1: α is on the arc of h/q
    apply hmaj
    simp only [major, Set.mem_iUnion, Finset.mem_Icc, Finset.mem_filter, Finset.mem_range]
    refine ⟨q, ⟨hq1, Nat.le_floor hqP⟩, h.toNat, ⟨by omega, ?_⟩, ?_⟩
    · have : Int.gcd ((h.toNat : ℕ) : ℤ) ((q : ℕ) : ℤ) = 1 := by
        rw [Int.toNat_of_nonneg hnn]; exact hcop
      rw [Int.gcd_natCast_natCast] at this
      exact this
    · have hcast : ((h.toNat : ℕ) : ℝ) = (h : ℝ) := by
        have : ((h.toNat : ℤ) : ℝ) = (h : ℝ) := by rw [Int.toNat_of_nonneg hnn]
        exact_mod_cast this
      rw [Set.mem_Icc, hcast]
      have e : 1 / ((q : ℝ) * QQ N) = 1 / (q * QQ N) := rfl
      constructor <;> linarith [hab.1, hab.2]
  · -- h ≥ q: α ≥ 1 - 1/(qQ), so α = 1 - 1/Q and q = 1
    have hhq : (q : ℝ) ≤ h := by exact_mod_cast hge
    have h1 : 1 ≤ (h : ℝ) / q := by rw [le_div_iff₀ hqpos]; linarith
    have hα1 : 1 - 1 / (q * QQ N) ≤ α := by linarith [hab.1]
    apply hαe
    have : 1 - 1 / QQ N ≤ α := by linarith
    linarith

/-- The [12] bound at one `z ≤ N` with `P < q ≤ Q`: at most `3C N^{1-c/2+ε}`. -/
theorem bound_at {N : ℕ} (hN : 1 ≤ N) {C ε z : ℝ} (hC : 0 ≤ C) (hε : 0 ≤ ε) (hz0 : 0 ≤ z)
    (hzN : z ≤ N) {q : ℕ} (hqP : PP N < q) (hqQ : (q : ℝ) ≤ QQ N) :
    C * (z ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) + z ^ (9 / 10 : ℝ) + z * (q : ℝ) ^ (-(1 / 2) : ℝ)) * z ^ ε
      ≤ 3 * C * (N : ℝ) ^ (1 - c / 2 + ε) := by
  have hc : c = 0.1215 := rfl
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hP0 : 0 < PP N := rpow_pos_of_pos hN0 _
  have hq0 : (0 : ℝ) < q := lt_trans hP0 hqP
  have mono : ∀ a b : ℝ, a ≤ b → (N : ℝ) ^ a ≤ (N : ℝ) ^ b := fun a b h => rpow_le_rpow_of_exponent_le hN1 h
  have t1 : z ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) ≤ (N : ℝ) ^ (1 - c / 2) := by
    have a1 : z ^ (1 / 2 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := rpow_le_rpow hz0 hzN (by norm_num)
    have a2 : (q : ℝ) ^ (1 / 2 : ℝ) ≤ (N : ℝ) ^ (3 / 8 : ℝ) := by
      calc (q : ℝ) ^ (1 / 2 : ℝ) ≤ (QQ N) ^ (1 / 2 : ℝ) := rpow_le_rpow hq0.le hqQ (by norm_num)
        _ = (N : ℝ) ^ (3 / 8 : ℝ) := by unfold QQ; rw [← rpow_mul hN0.le]; norm_num
    calc z ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ (3 / 8 : ℝ) :=
          mul_le_mul a1 a2 (by positivity) (by positivity)
      _ = (N : ℝ) ^ (7 / 8 : ℝ) := by rw [← rpow_add hN0]; norm_num
      _ ≤ (N : ℝ) ^ (1 - c / 2) := mono _ _ (by rw [hc]; norm_num)
  have t2 : z ^ (9 / 10 : ℝ) ≤ (N : ℝ) ^ (1 - c / 2) :=
    (rpow_le_rpow hz0 hzN (by norm_num)).trans (mono _ _ (by rw [hc]; norm_num))
  have t3 : z * (q : ℝ) ^ (-(1 / 2) : ℝ) ≤ (N : ℝ) ^ (1 - c / 2) := by
    have a3 : (q : ℝ) ^ (-(1 / 2) : ℝ) ≤ (PP N) ^ (-(1 / 2) : ℝ) :=
      rpow_le_rpow_of_nonpos hP0 hqP.le (by norm_num)
    have e : (PP N) ^ (-(1 / 2) : ℝ) = (N : ℝ) ^ (-(c / 2)) := by
      unfold PP; rw [← rpow_mul hN0.le]; ring_nf
    calc z * (q : ℝ) ^ (-(1 / 2) : ℝ) ≤ (N : ℝ) * (N : ℝ) ^ (-(c / 2)) :=
          mul_le_mul hzN (a3.trans e.le) (by positivity) hN0.le
      _ = (N : ℝ) ^ (1 - c / 2) := by
          rw [show (1 - c / 2) = 1 + -(c / 2) by ring, rpow_add hN0, rpow_one]
  have t4 : z ^ ε ≤ (N : ℝ) ^ ε := rpow_le_rpow hz0 hzN hε
  have hsplit : (N : ℝ) ^ (1 - c / 2 + ε) = (N : ℝ) ^ (1 - c / 2) * (N : ℝ) ^ ε := rpow_add hN0 _ _
  rw [hsplit]
  have hsum : z ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) + z ^ (9 / 10 : ℝ) + z * (q : ℝ) ^ (-(1 / 2) : ℝ)
      ≤ 3 * (N : ℝ) ^ (1 - c / 2) := by linarith
  have h0 : 0 ≤ z ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) + z ^ (9 / 10 : ℝ) + z * (q : ℝ) ^ (-(1 / 2) : ℝ) := by
    positivity
  calc C * (z ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) + z ^ (9 / 10 : ℝ) + z * (q : ℝ) ^ (-(1 / 2) : ℝ)) * z ^ ε
      ≤ C * (3 * (N : ℝ) ^ (1 - c / 2)) * (N : ℝ) ^ ε := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hsum hC) t4 (by positivity) (by positivity)
    _ = 3 * C * ((N : ℝ) ^ (1 - c / 2) * (N : ℝ) ^ ε) := by ring

/-- **The minor arc sup bound, CONDITIONAL ON [12, p. 107]**: eventually
`|S(N-td, N-td-d, α)| ≤ Cs N^{1-c/2+4·10^{-6}}` on the minor arcs except `1 - 1/Q`. -/
theorem minorSup_of_bound12 (h12 : Bound12) : ∃ N1 : ℕ, ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ N, N1 ≤ N →
    ∀ α ∈ per N \ major N, α ≠ 1 - 1 / QQ N → ∀ t ∈ Set.Icc (aa N) (bb N),
      ‖Ssum (N - t * dd N) (N - t * dd N - dd N) α‖ ≤ Cs * (N : ℝ) ^ (1 - c / 2 + 0.000004) := by
  obtain ⟨C, hC, hb⟩ := h12 0.000004 (by norm_num)
  have hc : c = 0.1215 := rfl
  have ht : Tendsto (fun x : ℝ => x ^ (0.0001 : ℝ)) atTop atTop := tendsto_rpow_atTop (by norm_num)
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp
    (tendsto_natCast_atTop_atTop.eventually (ht.eventually_ge_atTop 6))
  refine ⟨max N1 2, 6 * C, by positivity, fun N hN α hα hαe t htI => ?_⟩
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have h6 := hN1 N (le_trans (le_max_left _ _) hN)
  have hN' : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNr1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNr2 : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have mono : ∀ a b : ℝ, a ≤ b → (N : ℝ) ^ a ≤ (N : ℝ) ^ b := fun a b h => rpow_le_rpow_of_exponent_le hNr1 h
  -- the eventual inequalities
  have hd : dd N = (N : ℝ) ^ (0.9999 : ℝ) := rfl
  have hsplitN : (N : ℝ) = (N : ℝ) ^ (0.9999 : ℝ) * (N : ℝ) ^ (0.0001 : ℝ) := by
    rw [← rpow_add hN']; norm_num
  have hQ : QQ N = (N : ℝ) ^ (3 / 4 : ℝ) := rfl
  have hQd : QQ N ≤ dd N := by rw [hQ, hd]; exact mono _ _ (by norm_num)
  have hdpos : 0 < dd N := dd_pos (by omega)
  have hthird : 2 * dd N ≤ (N : ℝ) / 3 := by
    rw [hd]; nth_rewrite 2 [hsplitN]
    have : 0 ≤ (N : ℝ) ^ (0.9999 : ℝ) := by positivity
    nlinarith
  have hQ1 : 1 ≤ QQ N := by rw [hQ]; exact Real.one_le_rpow hNr1 (by norm_num)
  have hPQ : PP N + 1 ≤ QQ N := by
    have hP1 : 1 ≤ PP N := Real.one_le_rpow hNr1 (by rw [hc]; norm_num)
    have e : QQ N = PP N * (N : ℝ) ^ (3 / 4 - c) := by
      rw [hQ]; unfold PP; rw [← rpow_add hN']; ring_nf
    have h2 : 2 ≤ (N : ℝ) ^ (3 / 4 - c) := by
      have := mono 0.0001 (3 / 4 - c) (by rw [hc]; norm_num); linarith
    rw [e]; nlinarith
  have hP0 : 0 < PP N := rpow_pos_of_pos hN' _
  obtain ⟨h, q, hq1, hqP, hqQ, hcop, hapx⟩ := dirichlet_minor hQ1 hPQ hP0 hα hαe
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq1
  have hsq : |α - h / q| ≤ 1 / (q : ℝ) ^ 2 := by
    refine hapx.trans ?_
    apply one_div_le_one_div_of_le (by positivity)
    rw [sq]; exact mul_le_mul_of_nonneg_left hqQ hq0.le
  -- x = N - td and y = N - td - d
  obtain ⟨hta, htb⟩ := htI
  have ha0 : 0 ≤ aa N := by unfold aa; positivity
  have htd0 : 0 ≤ t * dd N := mul_nonneg (ha0.trans hta) hdpos.le
  have hbd : bb N * dd N = 2 * (N : ℝ) / 3 := by
    have h1 := bad_mul N (by omega)
    have h2 : aa N * dd N = (N : ℝ) / 3 := by
      unfold aa dd; rw [div_mul_eq_mul_div, ← rpow_add hN']; norm_num
    nlinarith
  have htd : t * dd N ≤ 2 * (N : ℝ) / 3 := by rw [← hbd]; exact mul_le_mul_of_nonneg_right htb hdpos.le
  set x := (N : ℝ) - t * dd N
  set y := (N : ℝ) - t * dd N - dd N
  have hy : QQ N ≤ y := by simp only [y]; linarith
  have hd6 : 6 ≤ dd N := le_trans h6 (by rw [hd]; exact mono _ _ (by norm_num))
  have hy2 : 2 ≤ y := by simp only [y]; linarith
  have hxN : x ≤ N := by simp only [x]; linarith
  have hyx : y ≤ x := by simp only [x, y]; linarith
  rw [Ssum_sub (by linarith) hyx]
  have bx := hb x (by linarith) α h q hq1 (by linarith) hcop hsq
  have hby := hb y hy2 α h q hq1 (by linarith) hcop hsq
  have cx := bound_at (N := N) (z := x) (ε := 0.000004) (by omega) hC (by norm_num) (by linarith) hxN hqP hqQ
  have cy := bound_at (N := N) (z := y) (ε := 0.000004) (by omega) hC (by norm_num) (by linarith) (by linarith) hqP hqQ
  calc ‖Ssum x 0 α - Ssum y 0 α‖ ≤ ‖Ssum x 0 α‖ + ‖Ssum y 0 α‖ := norm_sub_le _ _
    _ ≤ 3 * C * (N : ℝ) ^ (1 - c / 2 + 0.000004) + 3 * C * (N : ℝ) ^ (1 - c / 2 + 0.000004) :=
        add_le_add (bx.trans cx) (hby.trans cy)
    _ = 6 * C * (N : ℝ) ^ (1 - c / 2 + 0.000004) := by ring

/-- **Cited input**, the last bundle: (84) or (85) for Re D₁ and (86), with D₆ and 𝔖 ≥ 1
existential; the minor arcs are handled by `Bound12`. -/
structure InputsL where
  D6 : ℕ → ℕ → ℂ
  S : ℕ → ℝ
  S_ge : ∀ k, Even k → 1 ≤ S k
  N0 : ℕ
  Cerr : ℝ
  c1 : ℝ
  c1_pos : 0 < c1
  C86 : ℝ
  lower : ∀ N, N0 ≤ N →
    (∀ k ∈ Win N, Even k →
      S k * (bb N - aa N) * dd N *
        ((Real.log (Real.log (Real.log N)))⁻¹ - Cerr * (Real.log (Real.log N)) ^ (-(1 / 2) : ℝ))
        - ‖D6 N k‖ < (D1c N k).re) ∨
    (∀ k ∈ Win N, Even k →
      S k * (bb N - aa N) * dd N * c1 * PP N ^ (-0.00001 : ℝ) * Real.log (PP N) *
        (2 * c⁻¹ - Cerr * (Real.log (Real.log (Real.log N))) ^ (-0.1 : ℝ))
        - ‖D6 N k‖ ≤ (D1c N k).re)
  eq86 : ∀ N, N0 ≤ N →
    ∑ k ∈ Win N, ‖D6 N k‖ ^ 2 ≤ C86 * PP N ^ (-1 : ℝ) * dd N * (N : ℝ) ^ (2.0003 : ℝ)

/-- `InputsL` with [12, p. 107] gives `InputsS`. -/
noncomputable def InputsL.toInputsS (J : InputsL) (h12 : Bound12) : InputsS :=
  have hex := minorSup_of_bound12 h12
  { D6 := J.D6, S := J.S, S_ge := J.S_ge, N0 := max J.N0 hex.choose, Cerr := J.Cerr, c1 := J.c1,
    c1_pos := J.c1_pos, Cs := hex.choose_spec.choose, C86 := J.C86
    lower := fun N hN => J.lower N (le_trans (le_max_left _ _) hN)
    minorSup := fun N hN => hex.choose_spec.choose_spec.2 N (le_trans (le_max_right _ _) hN)
    eq86 := fun N hN => J.eq86 N (le_trans (le_max_left _ _) hN) }

/-- **Lu's Theorem**, `E(x) ≪ x^{0.879}`, CONDITIONAL ON (84) or (85), (86) and [12, p. 107]. -/
theorem lu_of_inputsL (J : InputsL) (h12 : Bound12) : PowerBound 0.879 :=
  lu_of_inputsS (J.toInputsS h12)

/-- `E X ≪ X^{0.8789126}`, CONDITIONAL ON the same. -/
theorem lu_sharp_of_inputsL (J : InputsL) (h12 : Bound12) : PowerBound θ :=
  lu_sharp_of_inputsS (J.toInputsS h12)

/-- Pintz's eventual form `E X < X^{0.879}`, CONDITIONAL ON the same. -/
theorem lu_eventually_of_inputsL (J : InputsL) (h12 : Bound12) : Lu2010.lu_eventually_stmt :=
  lu_eventually_of_inputsS (J.toInputsS h12)

end LeanLab.ExceptionalSet.Lu2010Dirichlet

#print axioms LeanLab.ExceptionalSet.Lu2010Dirichlet.Ssum_sub
#print axioms LeanLab.ExceptionalSet.Lu2010Dirichlet.dirichlet_minor
#print axioms LeanLab.ExceptionalSet.Lu2010Dirichlet.bound_at
#print axioms LeanLab.ExceptionalSet.Lu2010Dirichlet.minorSup_of_bound12
#print axioms LeanLab.ExceptionalSet.Lu2010Dirichlet.InputsL.toInputsS
#print axioms LeanLab.ExceptionalSet.Lu2010Dirichlet.lu_of_inputsL
#print axioms LeanLab.ExceptionalSet.Lu2010Dirichlet.lu_sharp_of_inputsL
#print axioms LeanLab.ExceptionalSet.Lu2010Dirichlet.lu_eventually_of_inputsL
