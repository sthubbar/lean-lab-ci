/-
Split of `lemma4` in ExceptionalSet/State1539.lean into smaller leaves.

The statement being split, verbatim after its name:

: Lemma4

`lemma4_split` below proves `Lemma4` from the leaves, with no `sorry` of its own and without
using the target theorem.  The leaves are the steps of Vinogradov's equidistribution
argument, in the order the assembly uses them:

1. `leaf_fejer_majorant` - the discrepancy of the count against `(z₁ - z₂)N/2` is controlled
   by the first `H` exponential sums `Σ e(hαF(n))`; no decay and no unknown constants.
2. `leaf_exp_sum_bound` - each of those sums is small, at frequency `h α` and on the index
   range `N/2 < n ≤ N` that the count runs over, uniformly in `h ≤ F(N)^C`.
3. `leaf_log_regime` - past a threshold, `⌈log N⌉` lies in the frequency range of step 2 and
   is at least 1.
4. `leaf_absorption` - the bookkeeping: the `4N/(⌈log N⌉+1)` term and the geometrically
   small sum are dominated by one term of the same shape with a smaller `κ`.
5. `leaf_small_N` - the finitely many `N` below the threshold, with a constant absorbing the
   `exp` factor there.

AI wrote the Lean code.  The leaves are open; the assembly is proved.
-/
import LeanLab.ExceptionalSet.State1539
import LeanLab.ExceptionalSet.Decomp547a
import LeanLab.ExceptionalSet.Selberg524

namespace LeanLab.ExceptionalSet.U1539

open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-! ### Pass 9 (20261121T0105Z): Erdős–Turán from the verified Beurling–Selberg majorant

`leaf_fejer_majorant` is the Erdős–Turán inequality for an interval indicator.  `Selberg524`
(five Mathlib-only files, zero `sorry`, zero `axiom`) already proves the one-sided
Beurling–Selberg majorant of a symmetric arc; the lemmas below turn it into Erdős–Turán and
hence into the leaf.  The only statement left open is the leaf's *unbounded* `H` quantifier:
for `H + 1 > 8 * (N / 2)` the first term `4N/(H+1)` no longer dominates the parity defect
`(z₁-z₂) * ((#s) - N/2) ≤ 1/2`, so the leaf then asserts a lower bound on the weighted
exponential sums, which is the converse of Erdős–Turán.  The assembly uses `H = ⌈log N⌉`,
for which `H + 1 ≤ 4N ≤ 8⌊N/2⌋` holds, so `l4_leaf_fejer_of_bound` covers it.
-/



private theorem l4_eC_add (a b : ℝ) : eC (a + b) = eC a * eC b := by
  unfold eC
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem l4_eC_intCast (k : ℤ) : eC (k : ℝ) = 1 := by
  unfold eC
  have h : 2 * Real.pi * Complex.I * (k : ℝ) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

private theorem l4_eC_frac (h : ℕ) (y : ℝ) : eC ((h : ℝ) * Int.fract y) = eC ((h : ℝ) * y) := by
  have hfr : Int.fract y = y - (⌊y⌋ : ℝ) := (Int.self_sub_floor y).symm
  rw [hfr]
  have hsplit : (h : ℝ) * (y - (⌊y⌋ : ℝ)) = (h : ℝ) * y + (-(((h : ℤ) * ⌊y⌋ : ℤ)) : ℝ) := by
    push_cast
    ring
  rw [hsplit, l4_eC_add,
    show (-(((h : ℤ) * ⌊y⌋ : ℤ)) : ℝ) = (((-((h : ℤ) * ⌊y⌋)) : ℤ) : ℝ) by push_cast; ring,
    l4_eC_intCast, mul_one]

private theorem l4_cos_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    |∑ n ∈ s, Real.cos (2 * Real.pi * f n)| ≤ ‖∑ n ∈ s, eC (f n)‖ := by
  have hpt : ∀ n : ι, (eC (f n)).re = Real.cos (2 * Real.pi * f n) := by
    intro n
    unfold eC
    rw [Complex.exp_re]
    have hre : (2 * Real.pi * Complex.I * (f n : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    have him : (2 * Real.pi * Complex.I * (f n : ℂ)).im = 2 * Real.pi * f n := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, him, Real.exp_zero, one_mul]
  have h1 : ∑ n ∈ s, Real.cos (2 * Real.pi * f n) = (∑ n ∈ s, eC (f n)).re := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun n _ => (hpt n).symm
  rw [h1]
  exact Complex.abs_re_le_norm _

/-- `cos (2π h (θ - k)) = cos (2π h θ)` for `k : ℤ`. -/
private theorem l4_cos_sub_intCast (h : ℕ) (θ : ℝ) (k : ℤ) :
    Real.cos (2 * Real.pi * ((h : ℝ) * (θ - (k : ℝ)))) =
      Real.cos (2 * Real.pi * ((h : ℝ) * θ)) := by
  have harg : 2 * Real.pi * ((h : ℝ) * (θ - (k : ℝ)))
      = 2 * Real.pi * ((h : ℝ) * θ) - (((h : ℤ) * k : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [harg, Real.cos_sub_int_mul_two_pi]

/-- The majorant sum factors out of the point sum. -/
private theorem l4_sum_majorant_eq {ι : Type*} (s : Finset ι) (v : ι → ℝ) (m : ℝ) (g : ℕ → ℝ)
    (H : ℕ) :
    ∑ i ∈ s, (m + ∑ h ∈ Finset.Icc 1 H, g h * Real.cos (2 * Real.pi * ((h : ℝ) * v i))) =
      (s.card : ℝ) * m +
        ∑ h ∈ Finset.Icc 1 H, g h * ∑ i ∈ s, Real.cos (2 * Real.pi * ((h : ℝ) * v i)) := by
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun h _ => by rw [Finset.mul_sum]

/-- Rotating the points multiplies the exponential sum by a unit, so the norms agree. -/
private theorem l4_norm_rot {ι : Type*} (s : Finset ι) (x : ι → ℝ) (h : ℕ) (c : ℝ) :
    ‖∑ i ∈ s, eC ((h : ℝ) * (x i - c))‖ = ‖∑ i ∈ s, eC ((h : ℝ) * x i)‖ := by
  have hpt : ∀ i : ι, eC ((h : ℝ) * (x i - c))
      = eC ((h : ℝ) * x i) * eC ((h : ℝ) * (-c)) := by
    intro i
    rw [← l4_eC_add]
    congr 1
    ring
  rw [Finset.sum_congr rfl fun i _ => hpt i, ← Finset.sum_mul, norm_mul,
    norm_eC, mul_one]

/-- **Erdős–Turán, upper half.**  A subset of the points that lies in the arc
`|x - c| ≤ w/2` (mod 1) is counted by the majorant's mean plus the coefficients against the
exponential sums. -/
private theorem l4_majorant_upper {ι : Type*} (s t : Finset ι) (x : ι → ℝ) (m : ℝ) (g : ℕ → ℝ)
    (H : ℕ) (c w : ℝ) (hw : 0 < w) (hg0 : ∀ h ∈ Finset.Icc 1 H, |g h| ≤ 4 / (h : ℝ))
    (hnn : ∀ θ, 0 ≤ m + ∑ h ∈ Finset.Icc 1 H, g h * Real.cos (2 * Real.pi * ((h : ℝ) * θ)))
    (hmaj : ∀ θ, |θ| ≤ w / 2 →
      1 ≤ m + ∑ h ∈ Finset.Icc 1 H, g h * Real.cos (2 * Real.pi * ((h : ℝ) * θ)))
    (hts : t ⊆ s)
    (harc : ∀ i ∈ t, ∃ k : ℤ, |x i - c - (k : ℝ)| ≤ w / 2) :
    (t.card : ℝ) ≤ (s.card : ℝ) * m +
      ∑ h ∈ Finset.Icc 1 H, (4 / (h : ℝ)) * ‖∑ i ∈ s, eC ((h : ℝ) * x i)‖ := by
  classical
  have hone : ∀ i ∈ t, 1 ≤ m + ∑ h ∈ Finset.Icc 1 H,
      g h * Real.cos (2 * Real.pi * ((h : ℝ) * (x i - c))) := by
    intro i hi
    obtain ⟨k, hk⟩ := harc i hi
    have hper : (∑ h ∈ Finset.Icc 1 H,
        g h * Real.cos (2 * Real.pi * ((h : ℝ) * (x i - c - (k : ℝ)))))
        = ∑ h ∈ Finset.Icc 1 H,
          g h * Real.cos (2 * Real.pi * ((h : ℝ) * (x i - c))) := by
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [l4_cos_sub_intCast h (x i - c) k]
    rw [← hper]
    exact hmaj _ hk
  have hstep : (t.card : ℝ) ≤ ∑ i ∈ s,
      (m + ∑ h ∈ Finset.Icc 1 H, g h * Real.cos (2 * Real.pi * ((h : ℝ) * (x i - c)))) := by
    calc (t.card : ℝ) = ∑ i ∈ t, (1 : ℝ) := by simp
      _ ≤ ∑ i ∈ t, (m + ∑ h ∈ Finset.Icc 1 H,
            g h * Real.cos (2 * Real.pi * ((h : ℝ) * (x i - c)))) :=
          Finset.sum_le_sum fun i hi => hone i hi
      _ ≤ ∑ i ∈ s, (m + ∑ h ∈ Finset.Icc 1 H,
            g h * Real.cos (2 * Real.pi * ((h : ℝ) * (x i - c)))) :=
          Finset.sum_le_sum_of_subset_of_nonneg hts (fun i _ _ => hnn _)
  have hsquare : ∑ h ∈ Finset.Icc 1 H,
      g h * ∑ i ∈ s, Real.cos (2 * Real.pi * ((h : ℝ) * (x i - c)))
      ≤ ∑ h ∈ Finset.Icc 1 H, (4 / (h : ℝ)) * ‖∑ i ∈ s, eC ((h : ℝ) * x i)‖ := by
    refine Finset.sum_le_sum fun h hh => ?_
    have hcos : |∑ i ∈ s, Real.cos (2 * Real.pi * ((h : ℝ) * (x i - c)))| ≤
        ‖∑ i ∈ s, eC ((h : ℝ) * x i)‖ := by
      have h1 := l4_cos_sum_le s (fun i => (h : ℝ) * (x i - c))
      have h2 : ‖∑ i ∈ s, eC ((h : ℝ) * (x i - c))‖ = ‖∑ i ∈ s, eC ((h : ℝ) * x i)‖ :=
        l4_norm_rot s x h c
      rw [h2] at h1
      exact h1
    have h2 : g h * ∑ i ∈ s, Real.cos (2 * Real.pi * ((h : ℝ) * (x i - c)))
        ≤ |g h| * |∑ i ∈ s, Real.cos (2 * Real.pi * ((h : ℝ) * (x i - c)))| := by
      calc g h * ∑ i ∈ s, Real.cos (2 * Real.pi * ((h : ℝ) * (x i - c)))
          ≤ |g h * ∑ i ∈ s, Real.cos (2 * Real.pi * ((h : ℝ) * (x i - c)))| :=
            le_abs_self _
        _ = |g h| * |∑ i ∈ s, Real.cos (2 * Real.pi * ((h : ℝ) * (x i - c)))| :=
            abs_mul _ _
    refine h2.trans ?_
    calc |g h| * |∑ i ∈ s, Real.cos (2 * Real.pi * ((h : ℝ) * (x i - c)))|
        ≤ (4 / (h : ℝ)) * ‖∑ i ∈ s, eC ((h : ℝ) * x i)‖ :=
          mul_le_mul (hg0 h hh) hcos (abs_nonneg _) (by
            have : (0 : ℝ) ≤ 4 / (h : ℝ) := by
              have h1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hh).1
              positivity
            exact this)
      _ = (4 / (h : ℝ)) * ‖∑ i ∈ s, eC ((h : ℝ) * x i)‖ := rfl
  rw [l4_sum_majorant_eq s (fun i => x i - c) m g H] at hstep
  linarith

/-! ### Arc facts for the point count -/

private theorem l4_arc_main {z₁ z₂ x : ℝ} (h1 : z₂ ≤ x) (h2 : x < z₁) :
    |x - (z₂ + z₁) / 2| ≤ (z₁ - z₂) / 2 := by
  rw [abs_le]
  constructor <;> linarith

private theorem l4_arc_high {z₁ z₂ x : ℝ} (hz₂ : 0 ≤ z₂) (h2 : z₁ ≤ x) (h3 : x ≤ 1) :
    |x - ((z₂ + z₁) / 2 + 1 / 2)| ≤ (1 - (z₁ - z₂)) / 2 := by
  rw [abs_le]
  constructor <;> linarith

private theorem l4_arc_low {z₁ z₂ x : ℝ} (hz₁ : z₁ ≤ 1) (h1 : 0 ≤ x) (h2 : x < z₂) :
    |x - ((z₂ + z₁) / 2 + 1 / 2) + 1| ≤ (1 - (z₁ - z₂)) / 2 := by
  rw [abs_le]
  constructor <;> linarith

private theorem l4_card_Ioc (N : ℕ) : (Finset.Ioc (N / 2) N).card = N - N / 2 :=
  Nat.card_Ioc ..

private theorem l4_parity (N : ℕ) :
    |(((Finset.Ioc (N / 2) N).card : ℕ) : ℝ) - (N : ℝ) / 2| ≤ 1 / 2 := by
  have hcard : (Finset.Ioc (N / 2) N).card = N - N / 2 := l4_card_Ioc N
  have hdec : (N : ℝ) = 2 * ((N / 2 : ℕ) : ℝ) + ((N % 2 : ℕ) : ℝ) := by
    have h : 2 * (N / 2) + N % 2 = N := Nat.div_add_mod N 2
    have hcast : ((2 * (N / 2) + N % 2 : ℕ) : ℝ) = (N : ℝ) := by rw [h]
    push_cast at hcast
    linarith
  have hmod : ((N % 2 : ℕ) : ℝ) = 0 ∨ ((N % 2 : ℕ) : ℝ) = 1 := by
    rcases Nat.mod_two_eq_zero_or_one N with h | h
    · left; rw [h]; norm_num
    · right; rw [h]; norm_num
  rw [hcard]
  rw [show ((N - N / 2 : ℕ) : ℝ) = (N : ℝ) - ((N / 2 : ℕ) : ℝ) by
    rw [Nat.cast_sub (Nat.div_le_self N 2)]]
  have hrew : (N : ℝ) - ((N / 2 : ℕ) : ℝ) - (N : ℝ) / 2
      = (2 * ((N : ℝ) - ((N / 2 : ℕ) : ℝ)) - (N : ℝ)) / 2 := by ring
  rw [hrew, abs_div]
  have hkey : 2 * ((N : ℝ) - ((N / 2 : ℕ) : ℝ)) - (N : ℝ) = (((N % 2 : ℕ)) : ℝ) := by
    rw [hdec]; ring
  rw [hkey]
  rcases hmod with h | h <;> rw [h] <;> norm_num

/-! ### Erdős–Turán for the interval indicator, from Selberg's majorant -/

set_option maxHeartbeats 4000000 in
/-- **Erdős–Turán with the true point count.**  The count in an interval is compared with
`w` times the *number of points* `M` (not with `w N/2`), so the parity defect of `M - N/2`
never enters and no restriction on `H` is needed.  Valid for `M ≥ 2`. -/
private theorem l4_ET_card (γ α z₁ z₂ : ℝ) (N H : ℕ)
    (hz₂ : 0 ≤ z₂) (hz1 : z₂ < z₁) (hz₁ : z₁ ≤ 1)
    (hM2 : 2 ≤ (Finset.Ioc (N / 2) N).card) :
    |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
        z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
      - (z₁ - z₂) * ((Finset.Ioc (N / 2) N).card : ℝ)| ≤
    4 * ((Finset.Ioc (N / 2) N).card : ℝ) / ((H : ℝ) + 1) +
      4 * ((Finset.Ioc (N / 2) N).card : ℝ) *
        ∑ h ∈ Finset.Icc 1 H,
          ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / ((h : ℝ) + 1) := by
  classical
  set s : Finset ℕ := Finset.Ioc (N / 2) N with hs
  set w : ℝ := z₁ - z₂ with hwdef
  set A : ℝ := 4 / ((H : ℝ) + 1) with hAdef
  set Sn : ℕ → ℝ := fun h => ‖∑ n ∈ s, eC (h * α * F γ n)‖ with hSn
  set Sg : ℝ := ∑ h ∈ Finset.Icc 1 H, Sn h / ((h : ℝ) + 1) with hSg
  set Cc : ℝ := ((s.filter (fun n : ℕ => z₂ ≤ Int.fract (α * F γ n) ∧
      Int.fract (α * F γ n) < z₁)).card : ℝ) with hCc
  set Mc : ℝ := (s.card : ℝ) with hMc
  have hMc2 : (2 : ℝ) ≤ Mc := by rw [hMc]; exact_mod_cast hM2
  have hMc0 : (0 : ℝ) ≤ Mc := by linarith
  have hw0 : 0 < w := by rw [hwdef]; linarith
  have hw1 : w ≤ 1 := by rw [hwdef]; linarith
  have hApos : 0 < A := by rw [hAdef]; positivity
  have hSg0 : 0 ≤ Sg := by
    rw [hSg]
    exact Finset.sum_nonneg fun h _ => div_nonneg (by rw [hSn]; positivity) (by positivity)
  have hCc0 : 0 ≤ Cc := by rw [hCc]; positivity
  have hCcM : Cc ≤ Mc := by
    rw [hCc, hMc]
    exact_mod_cast Finset.card_filter_le (p := fun n : ℕ => z₂ ≤ Int.fract (α * F γ n) ∧
      Int.fract (α * F γ n) < z₁) s
  -- the weight conversion `4/h ≤ 4 M/(h+1)`
  have hconv : ∑ h ∈ Finset.Icc 1 H, (4 / (h : ℝ)) * Sn h ≤ 4 * Mc * Sg := by
    rw [hSg, Finset.mul_sum]
    refine Finset.sum_le_sum fun h hh => ?_
    obtain ⟨hh1, -⟩ := Finset.mem_Icc.mp hh
    have hh1' : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh1
    have hhpos : (0 : ℝ) < (h : ℝ) := by linarith
    have hSn0 : 0 ≤ Sn h := by rw [hSn]; positivity
    have hcoef : 4 / (h : ℝ) ≤ 4 * Mc / ((h : ℝ) + 1) := by
      rw [div_le_div_iff₀ hhpos (by linarith : (0 : ℝ) < (h : ℝ) + 1)]
      nlinarith
    calc (4 / (h : ℝ)) * Sn h ≤ (4 * Mc / ((h : ℝ) + 1)) * Sn h :=
          mul_le_mul_of_nonneg_right hcoef hSn0
      _ = 4 * Mc * (Sn h / ((h : ℝ) + 1)) := by ring
  have hMAtarget : 4 * Mc / ((H : ℝ) + 1) = Mc * A := by rw [hAdef]; ring
  -- upper bound
  have hU : Cc - w * Mc ≤ Mc * A + 4 * Mc * Sg := by
    rcases lt_or_ge w (1 - A) with hlt | hge
    · have hwA : w + A < 1 := by linarith
      obtain ⟨m, g, hm, hg, hmaj⟩ :=
        LeanLab.ExceptionalSet.Selberg524.selberg_cosine_majorant524 w H hw0 hwA
      have hnn : ∀ θ : ℝ, 0 ≤ m + ∑ h ∈ Finset.Icc 1 H,
          g h * Real.cos (2 * Real.pi * ((h : ℝ) * θ)) := fun θ =>
        le_trans (by split_ifs <;> norm_num) (hmaj θ)
      have hmaj' : ∀ θ : ℝ, |θ| ≤ w / 2 → 1 ≤ m + ∑ h ∈ Finset.Icc 1 H,
          g h * Real.cos (2 * Real.pi * ((h : ℝ) * θ)) := by
        intro θ hθ
        have h := hmaj θ
        rwa [if_pos hθ] at h
      have hsub1 : (s.filter (fun n : ℕ => z₂ ≤ Int.fract (α * F γ n) ∧
            Int.fract (α * F γ n) < z₁)) ⊆
          s.filter (fun n : ℕ => |Int.fract (α * F γ n) - (z₂ + z₁) / 2| ≤ w / 2) := by
        intro n hn
        simp only [Finset.mem_filter] at hn ⊢
        exact ⟨hn.1, by rw [hwdef]; exact l4_arc_main hn.2.1 hn.2.2⟩
      have harc1 : ∀ n ∈ s.filter (fun n : ℕ =>
            |Int.fract (α * F γ n) - (z₂ + z₁) / 2| ≤ w / 2),
          ∃ k : ℤ, |Int.fract (α * F γ n) - (z₂ + z₁) / 2 - (k : ℝ)| ≤ w / 2 := by
        intro n hn
        simp only [Finset.mem_filter] at hn
        exact ⟨0, by simpa using hn.2⟩
      have hmain1 := l4_majorant_upper s (s.filter (fun n : ℕ =>
          |Int.fract (α * F γ n) - (z₂ + z₁) / 2| ≤ w / 2))
        (fun n => Int.fract (α * F γ n)) m g H ((z₂ + z₁) / 2) w hw0 hg hnn hmaj'
        (Finset.filter_subset _ _) harc1
      have hsumid : ∀ h : ℕ, ‖∑ n ∈ s, eC ((h : ℝ) * Int.fract (α * F γ n))‖ = Sn h := by
        intro h
        rw [hSn]
        congr 1
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [l4_eC_frac h (α * F γ n)]
        congr 1
        ring
      have hCt : Cc ≤ ((s.filter (fun n : ℕ =>
          |Int.fract (α * F γ n) - (z₂ + z₁) / 2| ≤ w / 2)).card : ℝ) := by
        rw [hCc]
        exact_mod_cast Finset.card_le_card hsub1
      have hsum_eq : ∑ h ∈ Finset.Icc 1 H,
            (4 / (h : ℝ)) * ‖∑ i ∈ s, eC ((h : ℝ) * Int.fract (α * F γ i))‖
          = ∑ h ∈ Finset.Icc 1 H, (4 / (h : ℝ)) * Sn h :=
        Finset.sum_congr rfl fun h _ => by rw [hsumid h]
      have hstep : Cc ≤ Mc * m + ∑ h ∈ Finset.Icc 1 H, (4 / (h : ℝ)) * Sn h := by
        refine hCt.trans ?_
        refine hmain1.trans ?_
        rw [hMc, hsum_eq]
      have hb1 : Mc * m ≤ Mc * (w + A) := by
        refine mul_le_mul_of_nonneg_left ?_ hMc0
        have : 4 / ((H : ℝ) + 1) = A := hAdef.symm
        rw [← this]; exact hm
      nlinarith [hstep, hconv, hb1]
    · nlinarith [hCcM, hge, hMc0]
  -- lower bound
  have hL : w * Mc - Cc ≤ Mc * A + 4 * Mc * Sg := by
    rcases eq_or_lt_of_le hw1 with hwEq | hwlt
    · have hws : z₁ - z₂ = 1 := by rw [← hwdef]; exact hwEq
      have hz2 : z₂ = 0 := by linarith
      have hz1' : z₁ = 1 := by linarith
      have hf : s.filter (fun n : ℕ => z₂ ≤ Int.fract (α * F γ n) ∧
          Int.fract (α * F γ n) < z₁) = s := by
        refine Finset.filter_true_of_mem ?_
        intro n _
        exact ⟨by rw [hz2]; exact Int.fract_nonneg _, by rw [hz1']; exact Int.fract_lt_one _⟩
      have hCeq : Cc = Mc := by rw [hCc, hMc, hf]
      rw [hwEq, hCeq]
      nlinarith [hApos, hMc0, hSg0]
    · rcases le_or_gt w A with hle | hgt
      · nlinarith [hCc0, hle, hMc0]
      · have hwA' : (1 - w) + A < 1 := by linarith
        obtain ⟨m', g', hm', hg', hmaj'⟩ :=
          LeanLab.ExceptionalSet.Selberg524.selberg_cosine_majorant524 (1 - w) H
            (by linarith) hwA'
        have hnn' : ∀ θ : ℝ, 0 ≤ m' + ∑ h ∈ Finset.Icc 1 H,
            g' h * Real.cos (2 * Real.pi * ((h : ℝ) * θ)) := fun θ =>
          le_trans (by split_ifs <;> norm_num) (hmaj' θ)
        have hmaj'' : ∀ θ : ℝ, |θ| ≤ (1 - w) / 2 → 1 ≤ m' + ∑ h ∈ Finset.Icc 1 H,
            g' h * Real.cos (2 * Real.pi * ((h : ℝ) * θ)) := by
          intro θ hθ
          have h := hmaj' θ
          rwa [if_pos hθ] at h
        have hsub2 : (s.filter (fun n : ℕ =>
              ¬(z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁))) ⊆
            s.filter (fun n : ℕ =>
              |Int.fract (α * F γ n) - ((z₂ + z₁) / 2 + 1 / 2)| ≤ (1 - w) / 2 ∨
              |Int.fract (α * F γ n) - ((z₂ + z₁) / 2 + 1 / 2) + 1| ≤ (1 - w) / 2) := by
          intro n hn
          simp only [Finset.mem_filter] at hn ⊢
          obtain ⟨hns, hnot⟩ := hn
          have hx0 : (0 : ℝ) ≤ Int.fract (α * F γ n) := Int.fract_nonneg _
          have hx1 : Int.fract (α * F γ n) < 1 := Int.fract_lt_one _
          rcases lt_or_ge (Int.fract (α * F γ n)) z₂ with hlo | hhi
          · exact ⟨hns, Or.inr (by rw [hwdef]; exact l4_arc_low hz₁ hx0 hlo)⟩
          · have hz₁x : z₁ ≤ Int.fract (α * F γ n) := by
              rcases lt_or_ge (Int.fract (α * F γ n)) z₁ with h' | h'
              · exact absurd ⟨hhi, h'⟩ hnot
              · exact h'
            exact ⟨hns, Or.inl (by rw [hwdef]; exact l4_arc_high hz₂ hz₁x hx1.le)⟩
        have harc2 : ∀ n ∈ s.filter (fun n : ℕ =>
              |Int.fract (α * F γ n) - ((z₂ + z₁) / 2 + 1 / 2)| ≤ (1 - w) / 2 ∨
              |Int.fract (α * F γ n) - ((z₂ + z₁) / 2 + 1 / 2) + 1| ≤ (1 - w) / 2),
            ∃ k : ℤ, |Int.fract (α * F γ n) - ((z₂ + z₁) / 2 + 1 / 2) - (k : ℝ)| ≤
              (1 - w) / 2 := by
          intro n hn
          simp only [Finset.mem_filter] at hn
          rcases hn.2 with h | h
          · exact ⟨0, by simpa using h⟩
          · exact ⟨-1, by push_cast; simpa using h⟩
        have hmain2 := l4_majorant_upper s (s.filter (fun n : ℕ =>
            |Int.fract (α * F γ n) - ((z₂ + z₁) / 2 + 1 / 2)| ≤ (1 - w) / 2 ∨
            |Int.fract (α * F γ n) - ((z₂ + z₁) / 2 + 1 / 2) + 1| ≤ (1 - w) / 2))
          (fun n => Int.fract (α * F γ n)) m' g' H ((z₂ + z₁) / 2 + 1 / 2) (1 - w)
          (by linarith) hg' hnn' hmaj'' (Finset.filter_subset _ _) harc2
        have hsumid : ∀ h : ℕ, ‖∑ n ∈ s, eC ((h : ℝ) * Int.fract (α * F γ n))‖ = Sn h := by
          intro h
          rw [hSn]
          congr 1
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [l4_eC_frac h (α * F γ n)]
          congr 1
          ring
        have hcompl : Mc - Cc = ((s.filter (fun n : ℕ =>
            ¬(z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁))).card : ℝ) := by
          have h1 : s.filter (fun n : ℕ => ¬(z₂ ≤ Int.fract (α * F γ n) ∧
              Int.fract (α * F γ n) < z₁))
              = s \ s.filter (fun n : ℕ => z₂ ≤ Int.fract (α * F γ n) ∧
                Int.fract (α * F γ n) < z₁) := by
            ext n
            simp only [Finset.mem_filter, Finset.mem_sdiff]
            tauto
          have h2 : ((s \ s.filter (fun n : ℕ => z₂ ≤ Int.fract (α * F γ n) ∧
              Int.fract (α * F γ n) < z₁)).card : ℝ)
              = (s.card : ℝ) - ((s.filter (fun n : ℕ => z₂ ≤ Int.fract (α * F γ n) ∧
                Int.fract (α * F γ n) < z₁)).card : ℝ) := by
            rw [Finset.card_sdiff,
              Finset.inter_eq_left.mpr (Finset.filter_subset (p := fun n : ℕ =>
                z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁) s),
              Nat.cast_sub (Finset.card_le_card (Finset.filter_subset (p := fun n : ℕ =>
                z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁) s))]
          rw [h1, h2, hMc, hCc]
        have hcard2 : ((s.filter (fun n : ℕ =>
              ¬(z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁))).card : ℝ)
            ≤ ((s.filter (fun n : ℕ =>
              |Int.fract (α * F γ n) - ((z₂ + z₁) / 2 + 1 / 2)| ≤ (1 - w) / 2 ∨
              |Int.fract (α * F γ n) - ((z₂ + z₁) / 2 + 1 / 2) + 1| ≤ (1 - w) / 2)).card : ℝ) :=
          by exact_mod_cast Finset.card_le_card hsub2
        have hsum_eq : ∑ h ∈ Finset.Icc 1 H,
              (4 / (h : ℝ)) * ‖∑ i ∈ s, eC ((h : ℝ) * Int.fract (α * F γ i))‖
            = ∑ h ∈ Finset.Icc 1 H, (4 / (h : ℝ)) * Sn h :=
          Finset.sum_congr rfl fun h _ => by rw [hsumid h]
        have hstep2 : Mc - Cc ≤ Mc * m' + ∑ h ∈ Finset.Icc 1 H, (4 / (h : ℝ)) * Sn h := by
          rw [hcompl]
          refine le_trans hcard2 ?_
          refine hmain2.trans ?_
          rw [hMc, hsum_eq]
        have hb1 : Mc * m' ≤ Mc * ((1 - w) + A) := by
          refine mul_le_mul_of_nonneg_left ?_ hMc0
          have : 4 / ((H : ℝ) + 1) = A := hAdef.symm
          rw [← this]; exact hm'
        have hMA2 : Mc * ((1 - w) + A) = Mc - w * Mc + Mc * A := by ring
        nlinarith [hstep2, hconv, hb1, hMA2]
  rw [abs_le, hMAtarget]
  constructor
  · linarith
  · linarith

set_option maxHeartbeats 4000000 in
private theorem l4_ET_core (γ α z₁ z₂ : ℝ) (N H : ℕ)
    (hz₂ : 0 ≤ z₂) (hz1 : z₂ < z₁) (hz₁ : z₁ ≤ 1)
    (hN2 : 2 ≤ N) (hHN : H + 1 ≤ 8 * (N / 2)) :
    |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
        z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
      - (z₁ - z₂) * (N : ℝ) / 2| ≤
    4 * (N : ℝ) / ((H : ℝ) + 1) +
      4 * (N : ℝ) * ∑ h ∈ Finset.Icc 1 H,
        ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / ((h : ℝ) + 1) := by
  classical
  set s : Finset ℕ := Finset.Ioc (N / 2) N with hs
  set w : ℝ := z₁ - z₂ with hwdef
  set A : ℝ := 4 / ((H : ℝ) + 1) with hAdef
  set Sn : ℕ → ℝ := fun h => ‖∑ n ∈ s, eC (h * α * F γ n)‖ with hSn
  set Sg : ℝ := ∑ h ∈ Finset.Icc 1 H, Sn h / ((h : ℝ) + 1) with hSg
  set Cc : ℝ := ((s.filter (fun n : ℕ => z₂ ≤ Int.fract (α * F γ n) ∧
      Int.fract (α * F γ n) < z₁)).card : ℝ) with hCc
  set Mc : ℝ := (s.card : ℝ) with hMc
  have hw0 : 0 < w := by rw [hwdef]; linarith
  have hw1 : w ≤ 1 := by rw [hwdef]; linarith
  have hApos : 0 < A := by rw [hAdef]; positivity
  have hNSg : (0 : ℝ) ≤ 4 * (N : ℝ) * Sg := by
    have h1 : (0 : ℝ) ≤ (N : ℝ) := by positivity
    have h2 : 0 ≤ Sg := by
      rw [hSg]
      exact Finset.sum_nonneg fun h _ => div_nonneg (by rw [hSn]; positivity) (by positivity)
    positivity
  have hSg0 : 0 ≤ Sg := by
    rw [hSg]
    exact Finset.sum_nonneg fun h _ => div_nonneg (by rw [hSn]; positivity) (by positivity)
  have hMcard : s.card = N - N / 2 := by rw [hs]; exact l4_card_Ioc N
  have hMle : Mc ≤ (N : ℝ) := by
    have h1 : s.card ≤ N := by rw [hs, l4_card_Ioc]; omega
    rw [hMc]
    exact_mod_cast h1
  -- the arithmetic of `Mc`, `N/2` and `N % 2`
  have hdec : (N : ℝ) = 2 * ((N / 2 : ℕ) : ℝ) + ((N % 2 : ℕ) : ℝ) := by
    have h : 2 * (N / 2) + N % 2 = N := Nat.div_add_mod N 2
    have hcast : ((2 * (N / 2) + N % 2 : ℕ) : ℝ) = (N : ℝ) := by rw [h]
    push_cast at hcast
    linarith
  have hMval : Mc = ((N - N / 2 : ℕ) : ℝ) := by rw [hMc, hMcard]
  have hMsub : ((N - N / 2 : ℕ) : ℝ) = (N : ℝ) - ((N / 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (Nat.div_le_self N 2)]
  have hPform : Mc - (N : ℝ) / 2 = ((N % 2 : ℕ) : ℝ) / 2 := by
    rw [hMval, hMsub]; linarith
  have hNsub : (N : ℝ) - Mc = ((N / 2 : ℕ) : ℝ) := by
    rw [hMval, hMsub]; ring
  have hP : Mc - (N : ℝ) / 2 = 0 ∨ Mc - (N : ℝ) / 2 = 1 / 2 := by
    rw [hPform]
    rcases Nat.mod_two_eq_zero_or_one N with h | h
    · left; rw [h]; norm_num
    · right; rw [h]; norm_num
  have hX : (0 : ℝ) ≤ Mc - (N : ℝ) / 2 := by rw [hPform]; positivity
  have hhalfpos : (0 : ℝ) < ((N / 2 : ℕ) : ℝ) := by
    have : 0 < N / 2 := by omega
    exact_mod_cast this
  -- `1/2 ≤ (N/2) A`, the content of `H + 1 ≤ 8 (N/2)`
  have hAn : (1 : ℝ) / 2 ≤ ((N / 2 : ℕ) : ℝ) * A := by
    have h1 : ((H : ℝ) + 1) ≤ 8 * ((N / 2 : ℕ) : ℝ) := by
      have hc : ((H + 1 : ℕ) : ℝ) ≤ ((8 * (N / 2) : ℕ) : ℝ) := by exact_mod_cast hHN
      push_cast at hc
      linarith
    rw [hAdef,
      show ((N / 2 : ℕ) : ℝ) * (4 / ((H : ℝ) + 1)) = (((N / 2 : ℕ) : ℝ) * 4) / ((H : ℝ) + 1)
        by ring,
      le_div_iff₀ (by positivity : (0 : ℝ) < (H : ℝ) + 1)]
    nlinarith
  have hbud1 : Mc * A + (Mc - (N : ℝ) / 2) ≤ (N : ℝ) * A := by
    have h1 : (N : ℝ) * A - Mc * A = ((N / 2 : ℕ) : ℝ) * A := by rw [← hNsub]; ring
    rcases hP with h | h <;> nlinarith [hAn]
  have hbud2 : Mc - (N : ℝ) / 2 ≤ ((N : ℝ) / 2) * A := by
    have h2 : ((N / 2 : ℕ) : ℝ) * A ≤ ((N : ℝ) / 2) * A := by
      refine mul_le_mul_of_nonneg_right ?_ hApos.le
      have h := Nat.div_mul_le_self N 2
      have hc : ((N / 2 : ℕ) : ℝ) * 2 ≤ (N : ℝ) := by exact_mod_cast h
      linarith
    rcases hP with h | h <;> rw [h] <;> nlinarith [hAn, h2]
  -- the sum conversion `4/h ≤ 4N/(h+1)`
  have hconv : ∑ h ∈ Finset.Icc 1 H, (4 / (h : ℝ)) * Sn h ≤ 4 * (N : ℝ) * Sg := by
    rw [hSg, Finset.mul_sum]
    refine Finset.sum_le_sum fun h hh => ?_
    obtain ⟨hh1, -⟩ := Finset.mem_Icc.mp hh
    have hh1' : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh1
    have hhpos : (0 : ℝ) < (h : ℝ) := by linarith
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have hSn0 : 0 ≤ Sn h := by rw [hSn]; positivity
    have hN2' : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
    have hNh : ((h : ℝ) + 1) ≤ (N : ℝ) * (h : ℝ) := by nlinarith
    have hcoef : 4 / (h : ℝ) ≤ 4 * (N : ℝ) / ((h : ℝ) + 1) := by
      rw [div_le_div_iff₀ hhpos (by linarith : (0 : ℝ) < (h : ℝ) + 1)]
      nlinarith [hNh]
    calc (4 / (h : ℝ)) * Sn h ≤ (4 * (N : ℝ) / ((h : ℝ) + 1)) * Sn h :=
          mul_le_mul_of_nonneg_right hcoef hSn0
      _ = 4 * (N : ℝ) * (Sn h / ((h : ℝ) + 1)) := by ring
  -- upper bounds
  have hU : Cc - w * (N : ℝ) / 2 ≤ 4 * (N : ℝ) / ((H : ℝ) + 1) + 4 * (N : ℝ) * Sg := by
    have hNA : 4 * (N : ℝ) / ((H : ℝ) + 1) = (N : ℝ) * A := by rw [hAdef]; ring
    rw [hNA]
    rcases lt_or_ge w (1 - A) with hlt | hge
    · -- arc majorant
      have hwA : w + A < 1 := by linarith
      obtain ⟨m, g, hm, hg, hmaj⟩ :=
        LeanLab.ExceptionalSet.Selberg524.selberg_cosine_majorant524 w H hw0 hwA
      have hnn : ∀ θ : ℝ, 0 ≤ m + ∑ h ∈ Finset.Icc 1 H,
          g h * Real.cos (2 * Real.pi * ((h : ℝ) * θ)) := fun θ =>
        le_trans (by split_ifs <;> norm_num) (hmaj θ)
      have hmaj' : ∀ θ : ℝ, |θ| ≤ w / 2 → 1 ≤ m + ∑ h ∈ Finset.Icc 1 H,
          g h * Real.cos (2 * Real.pi * ((h : ℝ) * θ)) := by
        intro θ hθ
        have h := hmaj θ
        rwa [if_pos hθ] at h
      have hsub1 : (s.filter (fun n : ℕ => z₂ ≤ Int.fract (α * F γ n) ∧
            Int.fract (α * F γ n) < z₁)) ⊆
          s.filter (fun n : ℕ => |Int.fract (α * F γ n) - (z₂ + z₁) / 2| ≤ w / 2) := by
        intro n hn
        simp only [Finset.mem_filter] at hn ⊢
        exact ⟨hn.1, by rw [hwdef]; exact l4_arc_main hn.2.1 hn.2.2⟩
      have harc1 : ∀ n ∈ s.filter (fun n : ℕ =>
            |Int.fract (α * F γ n) - (z₂ + z₁) / 2| ≤ w / 2),
          ∃ k : ℤ, |Int.fract (α * F γ n) - (z₂ + z₁) / 2 - (k : ℝ)| ≤ w / 2 := by
        intro n hn
        simp only [Finset.mem_filter] at hn
        exact ⟨0, by simpa using hn.2⟩
      have hmain1 := l4_majorant_upper s (s.filter (fun n : ℕ =>
          |Int.fract (α * F γ n) - (z₂ + z₁) / 2| ≤ w / 2))
        (fun n => Int.fract (α * F γ n)) m g H ((z₂ + z₁) / 2) w hw0 hg hnn hmaj'
        (Finset.filter_subset _ _) harc1
      have hsumid : ∀ h : ℕ, ‖∑ n ∈ s, eC ((h : ℝ) * Int.fract (α * F γ n))‖ = Sn h := by
        intro h
        rw [hSn]
        congr 1
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [l4_eC_frac h (α * F γ n)]
        congr 1
        ring
      have hCt : Cc ≤ ((s.filter (fun n : ℕ =>
          |Int.fract (α * F γ n) - (z₂ + z₁) / 2| ≤ w / 2)).card : ℝ) := by
        rw [hCc]
        exact_mod_cast Finset.card_le_card hsub1
      have hsum_eq : ∑ h ∈ Finset.Icc 1 H,
            (4 / (h : ℝ)) * ‖∑ i ∈ s, eC ((h : ℝ) * Int.fract (α * F γ i))‖
          = ∑ h ∈ Finset.Icc 1 H, (4 / (h : ℝ)) * Sn h :=
        Finset.sum_congr rfl fun h _ => by rw [hsumid h]
      have hstep : Cc ≤ Mc * m + ∑ h ∈ Finset.Icc 1 H, (4 / (h : ℝ)) * Sn h := by
        refine hCt.trans ?_
        refine hmain1.trans ?_
        rw [hMc, hsum_eq]
      have hb1 : Mc * m ≤ Mc * (w + A) := mul_le_mul_of_nonneg_left hm (by linarith)
      have hb2 : ∑ h ∈ Finset.Icc 1 H, (4 / (h : ℝ)) * Sn h ≤ 4 * (N : ℝ) * Sg := hconv
      have hfin : Cc ≤ Mc * (w + A) + 4 * (N : ℝ) * Sg := by linarith
      -- `w * (Mc - N/2) ≤ Mc - N/2`
      have hwx : w * (Mc - (N : ℝ) / 2) ≤ Mc - (N : ℝ) / 2 := by
        calc w * (Mc - (N : ℝ) / 2) ≤ 1 * (Mc - (N : ℝ) / 2) :=
              mul_le_mul_of_nonneg_right hw1 hX
          _ = Mc - (N : ℝ) / 2 := one_mul _
      nlinarith [hfin, hbud1, hwx]
    · -- `w` close to 1: crude upper bound
      have hwx : (1 - w) * (N : ℝ) / 2 ≤ A * (N : ℝ) / 2 := by
        have h1 : 1 - w ≤ A := by linarith
        have h2 : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
        nlinarith
      have hfin : Cc - w * (N : ℝ) / 2 ≤ (Mc - (N : ℝ) / 2) + A * (N : ℝ) / 2 := by
        have hCcM : Cc ≤ Mc := by
          rw [hCc, hMc]
          exact_mod_cast Finset.card_filter_le _ _
        nlinarith
      have hstep2 : (Mc - (N : ℝ) / 2) + A * (N : ℝ) / 2 ≤ (N : ℝ) * A := by
        have h1 : A * (N : ℝ) / 2 = ((N : ℝ) / 2) * A := by ring
        rw [h1]
        have h2 : ((N : ℝ) / 2) * A + ((N : ℝ) / 2) * A = (N : ℝ) * A := by ring
        linarith [hbud2]
      linarith [hfin, hstep2, hNSg]
  -- lower bounds
  have hL' : -(Cc - w * (N : ℝ) / 2) ≤ 4 * (N : ℝ) / ((H : ℝ) + 1) + 4 * (N : ℝ) * Sg := by
    have hNA : 4 * (N : ℝ) / ((H : ℝ) + 1) = (N : ℝ) * A := by rw [hAdef]; ring
    rw [hNA]
    rcases eq_or_lt_of_le hw1 with hwEq | hwlt
    · -- the full circle: every point is counted
      have hf : s.filter (fun n : ℕ => z₂ ≤ Int.fract (α * F γ n) ∧
          Int.fract (α * F γ n) < z₁) = s := by
        apply Finset.filter_true_of_mem
        intro n hn
        rw [hs] at hn
        simp only [Finset.mem_Ioc] at hn
        have hx0 : (0 : ℝ) ≤ Int.fract (α * F γ n) := Int.fract_nonneg _
        have hx1 : Int.fract (α * F γ n) < 1 := Int.fract_lt_one _
        constructor <;> [linarith [hz₂, show z₂ = 0 by linarith]; linarith]
      have hCeq : Cc = Mc := by rw [hCc, hMc, hf]
      rw [hCeq, hwEq]
      have hNApos : (0 : ℝ) < (N : ℝ) * A := by
        have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
        exact mul_pos this hApos
      linarith [hX, hNApos.le, hNSg]
    · rcases le_or_gt w (2 * A) with hle | hgt
      · -- crude lower bound
        have hCc0 : 0 ≤ Cc := by rw [hCc]; positivity
        have h1 : w * (N : ℝ) / 2 ≤ (N : ℝ) * A := by
          have h2 : w * ((N : ℝ) / 2) ≤ (2 * A) * ((N : ℝ) / 2) :=
            mul_le_mul_of_nonneg_right hle (by positivity)
          have h3 : (2 * A) * ((N : ℝ) / 2) = (N : ℝ) * A := by ring
          linarith
        linarith [hCc0, hNSg, h1]
      · -- complement majorant
        have hwA' : (1 - w) + A < 1 := by linarith
        obtain ⟨m', g', hm', hg', hmaj'⟩ :=
          LeanLab.ExceptionalSet.Selberg524.selberg_cosine_majorant524 (1 - w) H
            (by linarith) hwA'
        have hnn' : ∀ θ : ℝ, 0 ≤ m' + ∑ h ∈ Finset.Icc 1 H,
            g' h * Real.cos (2 * Real.pi * ((h : ℝ) * θ)) := fun θ =>
          le_trans (by split_ifs <;> norm_num) (hmaj' θ)
        have hmaj'' : ∀ θ : ℝ, |θ| ≤ (1 - w) / 2 → 1 ≤ m' + ∑ h ∈ Finset.Icc 1 H,
            g' h * Real.cos (2 * Real.pi * ((h : ℝ) * θ)) := by
          intro θ hθ
          have h := hmaj' θ
          rwa [if_pos hθ] at h
        have hsub2 : (s.filter (fun n : ℕ =>
              ¬(z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁))) ⊆
            s.filter (fun n : ℕ =>
              |Int.fract (α * F γ n) - ((z₂ + z₁) / 2 + 1 / 2)| ≤ (1 - w) / 2 ∨
              |Int.fract (α * F γ n) - ((z₂ + z₁) / 2 + 1 / 2) + 1| ≤ (1 - w) / 2) := by
          intro n hn
          simp only [Finset.mem_filter] at hn ⊢
          obtain ⟨hns, hnot⟩ := hn
          have hx0 : (0 : ℝ) ≤ Int.fract (α * F γ n) := Int.fract_nonneg _
          have hx1 : Int.fract (α * F γ n) < 1 := Int.fract_lt_one _
          rcases lt_or_ge (Int.fract (α * F γ n)) z₂ with hlo | hhi
          · exact ⟨hns, Or.inr (by rw [hwdef]; exact l4_arc_low hz₁ hx0 hlo)⟩
          · have hz₁x : z₁ ≤ Int.fract (α * F γ n) := by
              rcases lt_or_ge (Int.fract (α * F γ n)) z₁ with h' | h'
              · exact absurd ⟨hhi, h'⟩ hnot
              · exact h'
            exact ⟨hns, Or.inl (by rw [hwdef]; exact l4_arc_high hz₂ hz₁x hx1.le)⟩
        have harc2 : ∀ n ∈ s.filter (fun n : ℕ =>
              |Int.fract (α * F γ n) - ((z₂ + z₁) / 2 + 1 / 2)| ≤ (1 - w) / 2 ∨
              |Int.fract (α * F γ n) - ((z₂ + z₁) / 2 + 1 / 2) + 1| ≤ (1 - w) / 2),
            ∃ k : ℤ, |Int.fract (α * F γ n) - ((z₂ + z₁) / 2 + 1 / 2) - (k : ℝ)| ≤
              (1 - w) / 2 := by
          intro n hn
          simp only [Finset.mem_filter] at hn
          rcases hn.2 with h | h
          · exact ⟨0, by simpa using h⟩
          · exact ⟨-1, by push_cast; simpa using h⟩
        have hmain2 := l4_majorant_upper s (s.filter (fun n : ℕ =>
            |Int.fract (α * F γ n) - ((z₂ + z₁) / 2 + 1 / 2)| ≤ (1 - w) / 2 ∨
            |Int.fract (α * F γ n) - ((z₂ + z₁) / 2 + 1 / 2) + 1| ≤ (1 - w) / 2))
          (fun n => Int.fract (α * F γ n)) m' g' H ((z₂ + z₁) / 2 + 1 / 2) (1 - w)
          (by linarith) hg' hnn' hmaj'' (Finset.filter_subset _ _) harc2
        have hsumid : ∀ h : ℕ, ‖∑ n ∈ s, eC ((h : ℝ) * Int.fract (α * F γ n))‖ = Sn h := by
          intro h
          rw [hSn]
          congr 1
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [l4_eC_frac h (α * F γ n)]
          congr 1
          ring
        -- `M - C` is the complementary count
        have hcompl : Mc - Cc = ((s.filter (fun n : ℕ =>
            ¬(z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁))).card : ℝ) := by
          have h1 : s.filter (fun n : ℕ => ¬(z₂ ≤ Int.fract (α * F γ n) ∧
              Int.fract (α * F γ n) < z₁))
              = s \ s.filter (fun n : ℕ => z₂ ≤ Int.fract (α * F γ n) ∧
                Int.fract (α * F γ n) < z₁) := by
            ext n
            simp only [Finset.mem_filter, Finset.mem_sdiff]
            tauto
          have h2 : ((s \ s.filter (fun n : ℕ => z₂ ≤ Int.fract (α * F γ n) ∧
              Int.fract (α * F γ n) < z₁)).card : ℝ)
              = (s.card : ℝ) - ((s.filter (fun n : ℕ => z₂ ≤ Int.fract (α * F γ n) ∧
                Int.fract (α * F γ n) < z₁)).card : ℝ) := by
            rw [Finset.card_sdiff,
              Finset.inter_eq_left.mpr (Finset.filter_subset (p := fun n : ℕ =>
                z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁) s),
              Nat.cast_sub (Finset.card_le_card (Finset.filter_subset (p := fun n : ℕ =>
                z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁) s))]
          rw [h1, h2, hMc, hCc]
        have hcard2 : ((s.filter (fun n : ℕ =>
              ¬(z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁))).card : ℝ)
            ≤ ((s.filter (fun n : ℕ =>
              |Int.fract (α * F γ n) - ((z₂ + z₁) / 2 + 1 / 2)| ≤ (1 - w) / 2 ∨
              |Int.fract (α * F γ n) - ((z₂ + z₁) / 2 + 1 / 2) + 1| ≤ (1 - w) / 2)).card : ℝ) :=
          by exact_mod_cast Finset.card_le_card hsub2
        have hsum_eq : ∑ h ∈ Finset.Icc 1 H,
              (4 / (h : ℝ)) * ‖∑ i ∈ s, eC ((h : ℝ) * Int.fract (α * F γ i))‖
            = ∑ h ∈ Finset.Icc 1 H, (4 / (h : ℝ)) * Sn h :=
          Finset.sum_congr rfl fun h _ => by rw [hsumid h]
        have hstep2 : Mc - Cc ≤ Mc * m' + ∑ h ∈ Finset.Icc 1 H, (4 / (h : ℝ)) * Sn h := by
          rw [hcompl]
          refine le_trans hcard2 ?_
          refine hmain2.trans ?_
          rw [hMc, hsum_eq]
        have hb1 : Mc * m' ≤ Mc * ((1 - w) + A) := mul_le_mul_of_nonneg_left hm' (by linarith)
        have hfin : Mc - Cc ≤ Mc * ((1 - w) + A) + 4 * (N : ℝ) * Sg := by linarith
        -- conclude
        have hwx : w * (Mc - (N : ℝ) / 2) ≤ Mc - (N : ℝ) / 2 := by
          calc w * (Mc - (N : ℝ) / 2) ≤ 1 * (Mc - (N : ℝ) / 2) :=
                mul_le_mul_of_nonneg_right hw1 hX
            _ = Mc - (N : ℝ) / 2 := one_mul _
        nlinarith [hfin, hbud1, hwx]
  have hL : -(4 * (N : ℝ) / ((H : ℝ) + 1) + 4 * (N : ℝ) * Sg) ≤ Cc - w * (N : ℝ) / 2 := by
    have hNA : 4 * (N : ℝ) / ((H : ℝ) + 1) = (N : ℝ) * A := by rw [hAdef]; ring
    have h := hL'
    rw [hNA]
    linarith
  rw [abs_le]
  exact ⟨hL, hU⟩

/-! ### The leaf, in the range the assembly uses

`leaf_fejer_majorant` as cut quantifies over *every* `H`.  The proof below needs
`H + 1 ≤ 8 * (N / 2)`, which is exactly what the assembly's choice `H = ⌈log N⌉` and `N ≥ 2`
satisfy.  For `H` beyond that range the leaf asserts a *lower* bound on the weighted exponential
sums (the parity defect `w * (M - N/2)` is no longer dominated by `4N/(H+1)`), which is the
converse of Erdős–Turán; see the report.
-/

private theorem l4_leaf_fejer_of_bound (γ α z₁ z₂ : ℝ) (N H : ℕ)
    (hz₂ : 0 ≤ z₂) (hz1 : z₂ < z₁) (hz₁ : z₁ ≤ 1) (hHN : H + 1 ≤ 8 * (N / 2)) :
    |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
        z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
      - (z₁ - z₂) * (N : ℝ) / 2| ≤
    4 * (N : ℝ) / ((H : ℝ) + 1) +
      4 * (N : ℝ) * ∑ h ∈ Finset.Icc 1 H,
        ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / ((h : ℝ) + 1) := by
  classical
  rcases Nat.lt_or_ge N 2 with hN1 | hN2
  · -- `N ≤ 1`: at most one point
    interval_cases N
    · -- `N = 0`
      have hI : Finset.Ioc (0 : ℕ) 0 = (∅ : Finset ℕ) := by decide
      rw [hI, Finset.filter_empty, Finset.card_empty]
      push_cast
      simp
    · -- `N = 1`: one point, every exponential sum has norm one
      have hs1 : Finset.Ioc (0 : ℕ) 1 = ({1} : Finset ℕ) := by decide
      set Cc : ℝ := (((Finset.Ioc (0 : ℕ) 1).filter (fun n : ℕ =>
          z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ) with hCc
      have hC0 : 0 ≤ Cc := by rw [hCc]; positivity
      have hC1 : Cc ≤ 1 := by
        rw [hCc]
        have hle : ((Finset.Ioc (0 : ℕ) 1).filter (fun n : ℕ =>
            z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card ≤ 1 := by
          rw [hs1]
          refine Finset.card_le_one.mpr ?_
          intro a ha b hb
          simp only [Finset.mem_filter, Finset.mem_singleton] at ha hb
          rw [ha.1, hb.1]
        exact_mod_cast hle
      have hw0 : 0 ≤ z₁ - z₂ := by linarith
      have hw1 : z₁ - z₂ ≤ 1 := by linarith
      have hLHS : |Cc - (z₁ - z₂) * (1 : ℝ) / 2| ≤ 1 := by
        rw [abs_le]
        constructor <;> nlinarith
      have hsum : ∀ h ∈ Finset.Icc 1 H,
          ‖∑ n ∈ Finset.Ioc (0 : ℕ) 1, eC (h * α * F γ n)‖ = 1 := by
        intro h _
        rw [hs1, Finset.sum_singleton]
        exact norm_eC _
      have hterm : ∀ h ∈ Finset.Icc 1 H,
          ‖∑ n ∈ Finset.Ioc (0 : ℕ) 1, eC (h * α * F γ n)‖ / ((h : ℝ) + 1)
            = 1 / ((h : ℝ) + 1) := by
        intro h hh
        rw [hsum h hh, one_div]
      rw [Finset.sum_congr rfl hterm]
      rcases Nat.eq_zero_or_pos H with hH0 | hHpos
      · -- `H = 0`: the first term alone is `4`
        subst hH0
        have hIcc : Finset.Icc (1 : ℕ) 0 = (∅ : Finset ℕ) := by decide
        rw [hIcc, Finset.sum_empty, mul_zero, add_zero]
        push_cast
        linarith [hLHS]
      · have hge : (1 / 2 : ℝ) ≤ ∑ h ∈ Finset.Icc 1 H, 1 / ((h : ℝ) + 1) := by
          have hmem : 1 ∈ Finset.Icc 1 H := Finset.mem_Icc.mpr ⟨le_rfl, hHpos⟩
          have hsplit := Finset.single_le_sum (f := fun h : ℕ => 1 / ((h : ℝ) + 1))
            (fun i _ => by positivity) hmem
          have h2 : ((1 : ℕ) : ℝ) + 1 = 2 := by norm_num
          rw [h2] at hsplit
          linarith [hsplit]
        have h4 : (0 : ℝ) < 4 * (1 : ℝ) / ((H : ℝ) + 1) := by positivity
        nlinarith [hLHS, hge, h4]
  · exact l4_ET_core γ α z₁ z₂ N H hz₂ hz1 hz₁ hN2 hHN
/-- Pigeonhole on the circle: `M` points cannot occupy all `M + 1` half-open arcs of length
`1/(M+1)`, so one of them is empty. -/
private theorem l4_empty_arc (γ α : ℝ) (N : ℕ) :
    ∃ k : ℕ, (k : ℝ) ≤ ((Finset.Ioc (N / 2) N).card : ℝ) ∧
      ∀ n ∈ Finset.Ioc (N / 2) N,
        ¬((k : ℝ) / (((Finset.Ioc (N / 2) N).card : ℝ) + 1) ≤ Int.fract (α * F γ n) ∧
          Int.fract (α * F γ n) < ((k : ℝ) + 1) /
            (((Finset.Ioc (N / 2) N).card : ℝ) + 1)) := by
  classical
  set s : Finset ℕ := Finset.Ioc (N / 2) N with hs
  set M : ℕ := s.card with hM
  set D : ℝ := (M : ℝ) + 1 with hD
  have hDpos : 0 < D := by rw [hD]; positivity
  set f : ℕ → ℕ := fun n => ⌊D * Int.fract (α * F γ n)⌋.toNat with hf
  have hfmem : ∀ n ∈ s, f n ∈ Finset.range (M + 1) := by
    intro n _
    have h1 : (0 : ℝ) ≤ Int.fract (α * F γ n) := Int.fract_nonneg _
    have h2 : Int.fract (α * F γ n) < 1 := Int.fract_lt_one _
    have h3 : D * Int.fract (α * F γ n) < (M : ℝ) + 1 := by
      rw [hD]; nlinarith
    have h4 : (0 : ℝ) ≤ D * Int.fract (α * F γ n) := by positivity
    have h5 : ⌊D * Int.fract (α * F γ n)⌋ < (M : ℤ) + 1 := by
      rw [Int.floor_lt]
      have : (((M : ℤ) + 1 : ℤ) : ℝ) = (M : ℝ) + 1 := by push_cast; ring
      rw [this]; exact h3
    have h6 : (0 : ℤ) ≤ ⌊D * Int.fract (α * F γ n)⌋ := Int.floor_nonneg.mpr h4
    rw [hf]
    simp only [Finset.mem_range]
    omega
  have hcard : (s.image f).card < (Finset.range (M + 1)).card := by
    have h1 : (s.image f).card ≤ M := by
      have := Finset.card_image_le (s := s) (f := f)
      omega
    rw [Finset.card_range]
    omega
  obtain ⟨k, hkrange, hknot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  rw [Finset.mem_range] at hkrange
  have hMe : M = (Finset.Ioc (N / 2) N).card := by rw [hM, hs]
  have hkM : (k : ℝ) ≤ ((Finset.Ioc (N / 2) N).card : ℝ) := by
    rw [← hMe]
    exact_mod_cast (by omega : k ≤ M)
  refine ⟨k, hkM, ?_⟩
  intro n hn hc
  obtain ⟨hc1, hc2⟩ := hc
  have hne : f n ≠ k := by
    intro hnk
    exact hknot (Finset.mem_image.mpr ⟨n, hs.symm ▸ hn, hnk⟩)
  apply hne
  have h1 : (k : ℝ) ≤ D * Int.fract (α * F γ n) := by
    have h := (div_le_iff₀ hDpos).mp hc1
    linarith [h]
  have h2 : D * Int.fract (α * F γ n) < (k : ℝ) + 1 := by
    have h := (lt_div_iff₀ hDpos).mp hc2
    linarith [h]
  have h3 : ⌊D * Int.fract (α * F γ n)⌋ = (k : ℤ) := by
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
    · exact h1
    · have : (((k : ℤ) : ℝ) + 1) = (k : ℝ) + 1 := by push_cast; ring
      rw [this]; exact h2
  have h4 : (0 : ℤ) ≤ ⌊D * Int.fract (α * F γ n)⌋ := by rw [h3]; positivity
  rw [hf]
  simp only
  rw [h3, Int.toNat_natCast]

/-- The empty arc forces the weighted exponential sums to be bounded below. -/
private theorem l4_delta_of_empty_arc (γ α : ℝ) (N H k : ℕ)
    (hM2 : 2 ≤ (Finset.Ioc (N / 2) N).card)
    (hk0 : (0 : ℝ) ≤ (k : ℝ))
    (hk1 : (k : ℝ) ≤ ((Finset.Ioc (N / 2) N).card : ℝ))
    (hempty : ∀ n ∈ Finset.Ioc (N / 2) N,
      ¬((k : ℝ) / (((Finset.Ioc (N / 2) N).card : ℝ) + 1) ≤ Int.fract (α * F γ n) ∧
        Int.fract (α * F γ n) < ((k : ℝ) + 1) /
          (((Finset.Ioc (N / 2) N).card : ℝ) + 1))) :
    1 / (4 * (((Finset.Ioc (N / 2) N).card : ℝ) + 1)) - 1 / ((H : ℝ) + 1) ≤
      ∑ h ∈ Finset.Icc 1 H,
        ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / ((h : ℝ) + 1) := by
  classical
  set M : ℝ := ((Finset.Ioc (N / 2) N).card : ℝ) with hM
  have hMpos : 0 < M := by
    rw [hM]; have : (0 : ℝ) < ((Finset.Ioc (N / 2) N).card : ℝ) := by
      have : 0 < (Finset.Ioc (N / 2) N).card := by omega
      exact_mod_cast this
    exact this
  have hMpos' : 0 < M + 1 := by linarith
  set z₂ : ℝ := (k : ℝ) / (M + 1) with hz₂def
  set z₁ : ℝ := ((k : ℝ) + 1) / (M + 1) with hz₁def
  have hz₂ : 0 ≤ z₂ := by rw [hz₂def]; positivity
  have hz1 : z₂ < z₁ := by
    rw [hz₂def, hz₁def, div_lt_div_iff_of_pos_right hMpos']
    linarith
  have hz₁ : z₁ ≤ 1 := by
    rw [hz₁def, div_le_one hMpos']
    linarith
  have hE := l4_ET_card γ α z₁ z₂ N H hz₂ hz1 hz₁ hM2
  have hempty' : (Finset.Ioc (N / 2) N).filter (fun n : ℕ => z₂ ≤ Int.fract (α * F γ n) ∧
      Int.fract (α * F γ n) < z₁) = ∅ := by
    refine Finset.filter_false_of_mem ?_
    intro n hn
    exact hempty n hn
  rw [hempty', Finset.card_empty, Nat.cast_zero, zero_sub, abs_neg] at hE
  have hdiff : z₁ - z₂ = 1 / (M + 1) := by
    rw [hz₁def, hz₂def]
    field_simp
    ring
  rw [hdiff] at hE
  have hMcast : ((Finset.Ioc (N / 2) N).card : ℝ) = M := hM.symm
  rw [hMcast] at hE
  have hEq : (1 / (M + 1)) * M = M / (M + 1) := by ring
  rw [hEq, abs_of_nonneg (by positivity)] at hE
  have hT : (0 : ℝ) < (H : ℝ) + 1 := by positivity
  have hkey : (1 / (4 * (M + 1)) - 1 / ((H : ℝ) + 1)) * (4 * M) ≤
      (∑ h ∈ Finset.Icc 1 H,
        ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / ((h : ℝ) + 1)) * (4 * M) := by
    have hid : (1 / (4 * (M + 1)) - 1 / ((H : ℝ) + 1)) * (4 * M)
        = M / (M + 1) - 4 * M / ((H : ℝ) + 1) := by
      field_simp
    rw [hid]
    linarith [hE]
  exact le_of_mul_le_mul_right hkey (by positivity)

/-- The `h = 1` term of the harmonic sum. -/
private theorem l4_half_harmonic (H : ℕ) (hH : 1 ≤ H) :
    (1 : ℝ) / 2 ≤ ∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / ((h : ℝ) + 1) := by
  have hmem : 1 ∈ Finset.Icc 1 H := Finset.mem_Icc.mpr ⟨le_rfl, hH⟩
  have hs := Finset.single_le_sum (f := fun h : ℕ => (1 : ℝ) / ((h : ℝ) + 1))
    (fun i _ => by positivity) hmem
  have h1 : (1 : ℝ) / (((1 : ℕ) : ℝ) + 1) = 1 / 2 := by norm_num
  linarith [hs, h1]

/-! ### Leaves -/

/-- LEAF. Step 1, the counting inequality: for every `H`, the excess of the number of
`N/2 < n ≤ N` with `z₂ ≤ {αF(n)} < z₁` over `(z₁ - z₂)N/2` is at most `4N/(H+1)` plus the
first `H` exponential sums at the frequencies `hα`, each weighted by `4N/(h+1)`.  This is the
Fejér-kernel majorant for the indicator of an interval of fractional parts. -/
theorem leaf_fejer_majorant (γ α z₁ z₂ : ℝ) (N H : ℕ)
    (hz₂ : 0 ≤ z₂) (hz1 : z₂ < z₁) (hz₁ : z₁ ≤ 1) :
    |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
        z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
      - (z₁ - z₂) * N / 2| ≤
    4 * N / ((H : ℝ) + 1) +
      4 * N * ∑ h ∈ Finset.Icc 1 H,
        ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / ((h : ℝ) + 1) := by
  classical
  rcases Nat.lt_or_ge N 4 with hN4 | hN4
  · interval_cases N
    · -- N = 0
      have h0 : Finset.Ioc ((0:ℕ) / 2) 0 = (∅ : Finset ℕ) := by decide
      rw [h0]
      simp
    · -- N = 1
      push_cast
      have h1 : Finset.Ioc ((1:ℕ) / 2) 1 = ({1} : Finset ℕ) := by decide
      set dl : ℝ := ∑ h ∈ Finset.Icc 1 H,
        ‖∑ n ∈ Finset.Ioc ((1:ℕ) / 2) 1, eC (h * α * F γ n)‖ / ((h : ℝ) + 1) with hdldef
      have hnorm : ∀ h : ℕ, ‖∑ n ∈ Finset.Ioc ((1:ℕ) / 2) 1, eC (h * α * F γ n)‖ = 1 := by
        intro h
        rw [h1, Finset.sum_singleton]
        exact norm_eC _
      have hdl : dl = ∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / ((h : ℝ) + 1) :=
        Finset.sum_congr rfl fun h _ => by rw [hnorm h]
      have hC1 : (((Finset.Ioc ((1:ℕ) / 2) 1).filter (fun n : ℕ =>
          z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ) ≤ 1 := by
        have hc := Finset.card_filter_le (p := fun n : ℕ =>
          z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁) (Finset.Ioc ((1:ℕ) / 2) 1)
        have hcard : (Finset.Ioc ((1:ℕ) / 2) 1).card = 1 := by rw [h1]; simp
        rw [hcard] at hc
        exact_mod_cast hc
      have hLHS : |(((Finset.Ioc ((1:ℕ) / 2) 1).filter (fun n : ℕ =>
          z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
            - (z₁ - z₂) * 1 / 2| ≤ 1 := by
        rw [abs_le]
        constructor <;> nlinarith [hC1, hz₂, hz1, hz₁]
      rw [hdldef]
      rcases Nat.eq_zero_or_pos H with hH | hH
      · subst hH
        have hz : Finset.Icc (1:ℕ) 0 = (∅ : Finset ℕ) := by decide
        rw [hz, Finset.sum_empty, mul_zero, add_zero]
        have h4 : (4:ℝ) * 1 / (((0:ℕ):ℝ) + 1) = 4 * 1 := by norm_num
        rw [h4]
        linarith [hLHS]
      · have hhalf := l4_half_harmonic H hH
        have hTnn : (0:ℝ) ≤ 4/((H:ℝ)+1) := by positivity
        linarith [hLHS, hhalf, hTnn]
    · -- N = 2
      push_cast
      have h2 : Finset.Ioc ((2:ℕ) / 2) 2 = ({2} : Finset ℕ) := by decide
      set dl : ℝ := ∑ h ∈ Finset.Icc 1 H,
        ‖∑ n ∈ Finset.Ioc ((2:ℕ) / 2) 2, eC (h * α * F γ n)‖ / ((h : ℝ) + 1) with hdldef
      have hnorm : ∀ h : ℕ, ‖∑ n ∈ Finset.Ioc ((2:ℕ) / 2) 2, eC (h * α * F γ n)‖ = 1 := by
        intro h
        rw [h2, Finset.sum_singleton]
        exact norm_eC _
      have hdl : dl = ∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / ((h : ℝ) + 1) :=
        Finset.sum_congr rfl fun h _ => by rw [hnorm h]
      have hC1 : (((Finset.Ioc ((2:ℕ) / 2) 2).filter (fun n : ℕ =>
          z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ) ≤ 1 := by
        have hc := Finset.card_filter_le (p := fun n : ℕ =>
          z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁) (Finset.Ioc ((2:ℕ) / 2) 2)
        have hcard : (Finset.Ioc ((2:ℕ) / 2) 2).card = 1 := by rw [h2]; simp
        rw [hcard] at hc
        exact_mod_cast hc
      have hLHS : |(((Finset.Ioc ((2:ℕ) / 2) 2).filter (fun n : ℕ =>
          z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
            - (z₁ - z₂) * 2 / 2| ≤ 1 := by
        rw [abs_le]
        constructor <;> nlinarith [hC1, hz₂, hz1, hz₁]
      rw [hdldef]
      rcases Nat.eq_zero_or_pos H with hH | hH
      · subst hH
        have hz : Finset.Icc (1:ℕ) 0 = (∅ : Finset ℕ) := by decide
        rw [hz, Finset.sum_empty, mul_zero, add_zero]
        have h4 : (4:ℝ) * 2 / (((0:ℕ):ℝ) + 1) = 4 * 2 := by norm_num
        rw [h4]
        linarith [hLHS]
      · have hhalf := l4_half_harmonic H hH
        have hTnn : (0:ℝ) ≤ 4 * 2/((H:ℝ)+1) := by positivity
        linarith [hLHS, hhalf, hTnn]
    · -- N = 3
      push_cast
      have h3 : Finset.Ioc ((3:ℕ) / 2) 3 = ({2, 3} : Finset ℕ) := by decide
      have hM2 : 2 ≤ (Finset.Ioc ((3:ℕ) / 2) 3).card := by rw [h3]; simp
      set dl : ℝ := ∑ h ∈ Finset.Icc 1 H,
        ‖∑ n ∈ Finset.Ioc ((3:ℕ) / 2) 3, eC (h * α * F γ n)‖ / ((h : ℝ) + 1) with hdldef
      obtain ⟨k, hkM, hempty⟩ := l4_empty_arc γ α 3
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
      have hdel := l4_delta_of_empty_arc γ α 3 H k hM2 hk0 hkM hempty
      have hMcard : ((Finset.Ioc ((3:ℕ) / 2) 3).card : ℝ) = 2 := by rw [h3]; simp
      have hd : (1 : ℝ) / 12 - 1 / ((H : ℝ) + 1) ≤ dl := by
        rw [hdldef]
        rw [hMcard] at hdel
        have he : (1:ℝ) / (4 * (2 + 1)) = 1 / 12 := by norm_num
        rw [he] at hdel
        exact hdel
      have hET := l4_ET_card γ α z₁ z₂ 3 H hz₂ hz1 hz₁ hM2
      rw [hMcard] at hET
      have hET2 : |(((Finset.Ioc ((3:ℕ) / 2) 3).filter (fun n : ℕ =>
          z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
            - (z₁ - z₂) * 2| ≤ 4 * 2 / ((H : ℝ) + 1) + 4 * 2 * dl := by
        rw [hdldef]
        exact hET
      have hcn : ((Finset.Ioc ((3:ℕ) / 2) 3).filter (fun n : ℕ =>
          z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card ≤ 2 := by
        have hc := Finset.card_filter_le (p := fun n : ℕ =>
          z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁) (Finset.Ioc ((3:ℕ) / 2) 3)
        have hcard : (Finset.Ioc ((3:ℕ) / 2) 3).card = 2 := by rw [h3]; simp
        omega
      have hone : (1 : ℝ) ≤ 12 / ((H : ℝ) + 1) + 12 * dl := by
        have hm := mul_le_mul_of_nonneg_left hd (by norm_num : (0:ℝ) ≤ 12)
        have he : 12 * (1/12 - 1 / ((H : ℝ) + 1)) = 1 - 12 / ((H : ℝ) + 1) := by
          field_simp
        linarith [hm, he]
      have hnonneg : (0 : ℝ) ≤ 6 / ((H : ℝ) + 1) + 6 * dl := by
        have h3' : (0 : ℝ) ≤ dl + 1 / ((H : ℝ) + 1) := by linarith [hd]
        have he : (6:ℝ) / ((H : ℝ) + 1) + 6 * dl = 6 * (dl + 1 / ((H : ℝ) + 1)) := by
          field_simp
          ring
        rw [he]
        positivity
      have hh : (1 : ℝ) / 2 ≤ 6 / ((H : ℝ) + 1) + 6 * dl := by
        have hm := mul_le_mul_of_nonneg_left hd (by norm_num : (0:ℝ) ≤ 6)
        have he : 6 * (1/12 - 1 / ((H : ℝ) + 1)) = 1/2 - 6 / ((H : ℝ) + 1) := by
          field_simp
          ring
        linarith [hm, he]
      have hcases : ((Finset.Ioc ((3:ℕ) / 2) 3).filter (fun n : ℕ =>
          z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card = 0 ∨
          ((Finset.Ioc ((3:ℕ) / 2) 3).filter (fun n : ℕ =>
            z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card = 1 ∨
          ((Finset.Ioc ((3:ℕ) / 2) 3).filter (fun n : ℕ =>
            z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card = 2 := by omega
      rcases hcases with hc | hc | hc
      · rw [hc] at hET2 ⊢
        have hu : 2 * (z₁ - z₂) ≤ 8 / ((H : ℝ) + 1) + 8 * dl := by
          have h := (abs_le.mp hET2).1
          simp at h
          linarith [h]
        have h1 : 2*(z₁ - z₂)*(3/4) ≤ (8 / ((H : ℝ) + 1) + 8 * dl)*(3/4) :=
          mul_le_mul_of_nonneg_right hu (by norm_num)
        have he : (8 / ((H : ℝ) + 1) + 8 * dl)*(3/4)
            = 6 / ((H : ℝ) + 1) + 6 * dl := by field_simp; ring
        have he2 : (6:ℝ) / ((H : ℝ) + 1) + 6 * dl + (6 / ((H : ℝ) + 1) + 6 * dl)
            = 12 / ((H : ℝ) + 1) + 12 * dl := by ring
        rw [abs_le]
        constructor <;> linarith [h1, he, hnonneg, he2]
      · rw [hc] at hET2 ⊢
        have hu : (1:ℝ) - (z₁ - z₂) * 3 / 2 ≤ 1 := by nlinarith [hz1, hz₂]
        have hlb : -(1:ℝ) ≤ 1 - (z₁ - z₂) * 3 / 2 := by nlinarith [hz₂, hz1, hz₁]
        rw [abs_le]
        constructor <;> linarith [hu, hlb, hone]
      · rw [hc] at hET2 ⊢
        have hu2 : 2 * (1 - (z₁ - z₂)) ≤ 8 / ((H : ℝ) + 1) + 8 * dl := by
          have h := (abs_le.mp hET2).2
          linarith [h]
        have hlb : (0:ℝ) ≤ 2 - (z₁ - z₂) * 3 / 2 := by nlinarith [hz₁, hz₂]
        have e0 : 4 - 3*(z₁ - z₂) = (3/2)*(2*(1-(z₁ - z₂))) + 1 := by ring
        have e1 : (3/2)*(8/((H:ℝ)+1) + 8*dl) = 12/((H:ℝ)+1) + 12*dl := by ring
        have e2 : (24:ℝ)/((H:ℝ)+1) + 24*dl = 2*(12/((H:ℝ)+1) + 12*dl) := by ring
        have e3 : (4*3 : ℝ)/((H:ℝ)+1) + 4*3*dl = 12/((H:ℝ)+1) + 12*dl := by norm_num
        have e4 : (2:ℝ) - (z₁ - z₂)*3/2 = (4 - 3*(z₁ - z₂))/2 := by ring
        have hstep : 4 - 3*(z₁ - z₂) ≤ 24/((H:ℝ)+1) + 24*dl := by
          have h1 : (3/2)*(2*(1-(z₁ - z₂))) + 1
              ≤ (3/2)*(8/((H:ℝ)+1) + 8*dl) + 1 := by
            have h2 := mul_le_mul_of_nonneg_left hu2 (by norm_num : (0:ℝ) ≤ 3/2)
            linarith [h2]
          rw [e1] at h1
          linarith [h1, hone, e2]
        have hupper : 2 - (z₁ - z₂)*3/2 ≤ 4*3/((H:ℝ)+1) + 4*3*dl := by
          rw [e4, e3]
          linarith [hstep, e2]
        rw [abs_le]
        constructor
        · linarith [hone, hlb]
        · exact hupper
  · -- N ≥ 4
    set T : ℝ := (H : ℝ) + 1 with hTdef
    set dl : ℝ := ∑ h ∈ Finset.Icc 1 H,
      ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / ((h : ℝ) + 1) with hdldef
    set Cc : ℝ := (((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
        z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ) with hCcdef
    set Mc : ℝ := ((Finset.Ioc (N / 2) N).card : ℝ) with hMcdef
    have hTpos : 0 < T := by rw [hTdef]; positivity
    have hMc0 : (0 : ℝ) ≤ Mc := by rw [hMcdef]; positivity
    have hMc1 : 0 < Mc + 1 := by linarith
    have hM2 : 2 ≤ (Finset.Ioc (N / 2) N).card := by rw [l4_card_Ioc N]; omega
    have hp : |Mc - (N : ℝ) / 2| ≤ 1 / 2 := l4_parity N
    have hX : 0 ≤ Mc - (N : ℝ) / 2 := by
      have hMcv' : Mc = ((N - N / 2 : ℕ) : ℝ) := by rw [hMcdef, l4_card_Ioc N]
      have hsum : N / 2 + (N - N / 2) = N := by omega
      have hN : ((N / 2 : ℕ) : ℝ) + ((N - N / 2 : ℕ) : ℝ) = (N : ℝ) := by
        have hc : ((N / 2 + (N - N / 2) : ℕ) : ℝ) = (N : ℝ) := by rw [hsum]
        simpa using hc
      have h1 : N / 2 ≤ N - N / 2 := by omega
      have hc : ((N / 2 : ℕ) : ℝ) ≤ ((N - N / 2 : ℕ) : ℝ) := by exact_mod_cast h1
      rw [hMcv']
      linarith [hN, hc]
    have hY : Mc - (N : ℝ) / 2 ≤ 1 / 2 := (abs_le.mp hp).2
    have hwpos : 0 < z₁ - z₂ := by linarith
    have hwle : z₁ - z₂ ≤ 1 := by linarith
    have hET : |Cc - (z₁ - z₂) * Mc| ≤ 4 * Mc / T + 4 * Mc * dl :=
      l4_ET_card γ α z₁ z₂ N H hz₂ hz1 hz₁ hM2
    obtain ⟨k, hkM, hempty⟩ := l4_empty_arc γ α N
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have hdel : 1 / (4 * (Mc + 1)) - 1 / T ≤ dl :=
      l4_delta_of_empty_arc γ α N H k hM2 hk0 hkM hempty
    have hNMc : (N : ℝ) - Mc = ((N / 2 : ℕ) : ℝ) := by
      rw [hMcdef, l4_card_Ioc N]
      have hsum : N / 2 + (N - N / 2) = N := by omega
      have hc : ((N / 2 : ℕ) : ℝ) + ((N - N / 2 : ℕ) : ℝ) = (N : ℝ) := by exact_mod_cast hsum
      linarith
    have hMcv : Mc = ((N - N / 2 : ℕ) : ℝ) := by rw [hMcdef, l4_card_Ioc N]
    have hkey : (1 : ℝ) / 2 ≤ ((N : ℝ) - Mc) / (Mc + 1) := by
      have hcast : ((N - N / 2 : ℕ) : ℝ) + 1 ≤ 2 * ((N / 2 : ℕ) : ℝ) := by
        have h1 : (N - N / 2) + 1 ≤ 2 * (N / 2) := by omega
        exact_mod_cast h1
      rw [hNMc, hMcv, le_div_iff₀ (by linarith : (0 : ℝ) < ((N - N / 2 : ℕ) : ℝ) + 1)]
      linarith [hcast]
    have hkey' : (1 : ℝ) / 2 * (Mc + 1) ≤ (N : ℝ) - Mc := (le_div_iff₀ hMc1).mp hkey
    have hmul : ((N : ℝ) - Mc) / (Mc + 1) ≤ 4 * ((N : ℝ) - Mc) * dl + 4 * ((N : ℝ) - Mc) / T := by
      have h4 : (0 : ℝ) ≤ 4 * ((N : ℝ) - Mc) := by linarith
      have h := mul_le_mul_of_nonneg_left hdel h4
      have he : 4 * ((N : ℝ) - Mc) * (1 / (4 * (Mc + 1)) - 1 / T)
          = ((N : ℝ) - Mc) / (Mc + 1) - 4 * ((N : ℝ) - Mc) / T := by field_simp
      rw [he] at h
      linarith [h]
    have hpar : (z₁ - z₂) * (Mc - (N : ℝ) / 2) ≤ 1 / 2 := by
      have hle : (z₁ - z₂) * (Mc - (N : ℝ) / 2) ≤ 1 * (1 / 2) :=
        mul_le_mul hwle hY hX (by norm_num)
      linarith [hle]
    have hnonneg : 0 ≤ (z₁ - z₂) * (Mc - (N : ℝ) / 2) := mul_nonneg hwpos.le hX
    have hstep : |Cc - (z₁ - z₂) * (N : ℝ) / 2|
        ≤ 4 * Mc / T + 4 * Mc * dl + (z₁ - z₂) * (Mc - (N : ℝ) / 2) := by
      have hsplit : Cc - (z₁ - z₂) * (N : ℝ) / 2
          = (Cc - (z₁ - z₂) * Mc) + (z₁ - z₂) * (Mc - (N : ℝ) / 2) := by ring
      rw [hsplit]
      calc |(Cc - (z₁ - z₂) * Mc) + (z₁ - z₂) * (Mc - (N : ℝ) / 2)|
          ≤ |Cc - (z₁ - z₂) * Mc| + |(z₁ - z₂) * (Mc - (N : ℝ) / 2)| := abs_add_le _ _
        _ = |Cc - (z₁ - z₂) * Mc| + (z₁ - z₂) * (Mc - (N : ℝ) / 2) := by
            rw [abs_of_nonneg hnonneg]
        _ ≤ (4 * Mc / T + 4 * Mc * dl) + (z₁ - z₂) * (Mc - (N : ℝ) / 2) := by
            linarith [hET]
    have hlast : 4 * Mc / T + 4 * Mc * dl + (z₁ - z₂) * (Mc - (N : ℝ) / 2)
        ≤ 4 * (N : ℝ) / T + 4 * (N : ℝ) * dl := by
      have hN : 4 * (N : ℝ) / T = 4 * Mc / T + 4 * ((N : ℝ) - Mc) / T := by
        field_simp
        ring
      have hN2 : 4 * (N : ℝ) * dl = 4 * Mc * dl + 4 * ((N : ℝ) - Mc) * dl := by ring
      rw [hN, hN2]
      linarith [hmul, hpar, hkey]
    linarith [hstep, hlast]


/-- LEAF. Step 2, the exponential-sum input at the frequencies `hα`: it has the shape of the
sealed Theorem 2 of this unit at frequency `h α` and at the scale `N/2`, with `c = 1/2` and
the exponent `C`, summed over `N/2 < n ≤ N`. -/
theorem leaf_exp_sum_bound :
    ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ C : ℝ, 0 < C → C < γ - 1 →
      ∃ κ B : ℝ, 0 < κ ∧ 0 < B ∧ ∀ N : ℕ, 1 ≤ N → ∀ α : ℝ,
        F γ N ^ (-(1 / 2 : ℝ)) < |α| → |α| ≤ 1 → ∀ h : ℕ, 1 ≤ h →
        (h : ℝ) ≤ F γ N ^ C →
        ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ ≤
          B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := by
  intro γ h1 h2 C hC hCγ
  exact Decomp547a.integer_multiple_decay_full theorem2_via_karacuba γ h1 h2 C hC hCγ

/-- LEAF. Step 3, the regime: past a threshold, `N ≥ 3`, `log N ≥ 1`, `⌈log N⌉ ≥ 1`, and
`⌈log N⌉ ≤ F(N)^C` for every `C > 0`.  The last is what lets step 2 be applied at every
frequency `h ≤ ⌈log N⌉`. -/
theorem leaf_log_regime :
    ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ C : ℝ, 0 < C →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        3 ≤ N ∧ 1 ≤ Real.log N ∧ (1 : ℝ) ≤ (Nat.ceil (Real.log N) : ℝ) ∧
        (Nat.ceil (Real.log N) : ℝ) ≤ F γ N ^ C := by
  intro γ hγ1 hγ2 C hC
  have hδ : 0 < γ - 1 := by linarith
  have hδne : (γ - 1) ≠ 0 := ne_of_gt hδ
  set X : ℝ := (1 / C) ^ (1 / (γ - 1)) with hXdef
  have hX0 : 0 ≤ X := Real.rpow_nonneg (by positivity) _
  set L₀ : ℝ := max 1 (max (Real.exp 1) X) with hL₀def
  have hL₀1 : (1 : ℝ) ≤ L₀ := le_max_left _ _
  have hL₀e : Real.exp 1 ≤ L₀ := le_trans (le_max_left _ _) (le_max_right _ _)
  have hL₀X : X ≤ L₀ := le_trans (le_max_right _ _) (le_max_right _ _)
  have hexp1 : (3 : ℝ) ≤ Real.exp (Real.exp 1) := by
    have h1 : 2 * Real.exp 1 ≤ Real.exp (Real.exp 1) := Real.two_mul_le_exp
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    nlinarith
  refine ⟨Nat.ceil (Real.exp L₀) + 1, ?_⟩
  intro N hN
  have hNge : Real.exp L₀ ≤ (N : ℝ) := by
    have h1 : Real.exp L₀ ≤ (Nat.ceil (Real.exp L₀) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (Real.exp L₀) : ℝ) ≤ ((Nat.ceil (Real.exp L₀) + 1 : ℕ) : ℝ) := by
      push_cast; linarith
    linarith [h2.trans (by exact_mod_cast hN : ((Nat.ceil (Real.exp L₀) + 1 : ℕ) : ℝ) ≤ (N : ℝ))]
  have hL : L₀ ≤ Real.log (N : ℝ) :=
    (Real.le_log_iff_exp_le (by have h := Real.exp_pos L₀; linarith)).mpr hNge
  have hL1 : (1 : ℝ) ≤ Real.log (N : ℝ) := le_trans hL₀1 hL
  have hL3 : (3 : ℝ) ≤ (N : ℝ) := by
    have h1 : (3 : ℝ) ≤ Real.exp L₀ := le_trans hexp1 (Real.exp_le_exp.mpr hL₀e)
    linarith
  have hLpos : (0 : ℝ) < Real.log (N : ℝ) := by linarith
  set L := Real.log (N : ℝ) with hLdef
  -- the power bound
  have hXpow : X ^ (γ - 1) = 1 / C := by
    rw [hXdef, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ 1 / C)]
    have h1 : 1 / (γ - 1) * (γ - 1) = 1 := by field_simp
    rw [h1, Real.rpow_one]
  have hLδ : 1 / C ≤ L ^ (γ - 1) := by
    have h := Real.rpow_le_rpow hX0 (le_trans hL₀X hL) hδ.le
    rwa [hXpow] at h
  have hγsplit : L ^ γ = L * L ^ (γ - 1) := by
    have h : γ = (γ - 1) + 1 := by ring
    conv_lhs => rw [h]
    rw [Real.rpow_add hLpos, Real.rpow_one]
    ring
  have hmain : L + 1 ≤ Real.exp (C * L ^ γ) := by
    have h1 : C * L ^ γ = C * L * L ^ (γ - 1) := by rw [hγsplit]; ring
    have h3 : 2 * (C * L * L ^ (γ - 1)) ≤ Real.exp (C * L ^ γ) := by
      rw [h1]; exact Real.two_mul_le_exp
    have h4 : 2 * (C * L * L ^ (γ - 1)) ≥ 2 * L := by
      have hCL : (0 : ℝ) < C * L := by positivity
      have h6 : C * L * (1 / C) ≤ C * L * L ^ (γ - 1) :=
        mul_le_mul_of_nonneg_left hLδ hCL.le
      have h5 : C * L * (1 / C) = L := by
        field_simp
      linarith
    linarith
  have hγle : L ^ γ ≥ 0 := Real.rpow_nonneg hLpos.le _
  have hceil : (Nat.ceil L : ℝ) ≤ Real.exp (C * L ^ γ) := by
    have h1 : (Nat.ceil L : ℝ) < L + 1 := Nat.ceil_lt_add_one hLpos.le
    linarith
  have hceil1 : (1 : ℝ) ≤ (Nat.ceil L : ℝ) := le_trans hL1 (Nat.le_ceil L)
  have hF : F γ N ^ C = Real.exp (C * L ^ γ) := by
    have hpos : 0 < F γ N := Real.exp_pos _
    rw [Real.rpow_def_of_pos hpos]
    congr 1
    simp [F, hLdef, Real.log_exp, mul_comm]
  refine ⟨?_, hL1, hceil1, ?_⟩
  · exact_mod_cast hL3
  · rw [hF]; exact hceil

/-- LEAF. Step 4, the bookkeeping of the geometric decay: with `H = ⌈log N⌉`, the term
`4N/(H+1)` and the sum of the equally decaying terms weighted by `1/(h+1)` are both dominated
by `B N exp(-κ (log N)^{3-2γ})` for a strictly smaller `κ` and a large enough `B`, once
`N ≥ 3`. -/
theorem leaf_absorption :
    ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ κ₁ B₁ : ℝ, 0 < κ₁ → 0 < B₁ →
      ∃ κ B : ℝ, 0 < κ ∧ 1 ≤ B ∧ ∀ N : ℕ, 3 ≤ N →
        4 * N / ((Nat.ceil (Real.log N) : ℝ) + 1) +
          4 * N * (B₁ * N * Real.exp (-κ₁ * Real.log N ^ (3 - 2 * γ))
            * ∑ h ∈ Finset.Icc 1 (Nat.ceil (Real.log N)), 1 / ((h : ℝ) + 1))
          ≤ B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := by
  sorry

/-- LEAF. Step 5, the finitely many small `N`: below any fixed bound the trivial bound
`|count - (z₁ - z₂)N/2| ≤ N` is absorbed by a large constant times
`N exp(-κ (log N)^{3-2γ})`, since on that finite range the `exp` factor is bounded below. -/
theorem leaf_small_N :
    ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ κ : ℝ, 0 < κ → ∀ N₀ : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ N : ℕ, 1 ≤ N → N ≤ N₀ → ∀ α z₁ z₂ : ℝ, 0 ≤ z₂ → z₂ < z₁ → z₁ ≤ 1 →
        |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
            z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
          - (z₁ - z₂) * N / 2| ≤ B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := by
  intro γ hγ1 hγ2 κ hκ N₀
  refine ⟨Real.exp (κ * Real.log (N₀ : ℝ) ^ (3 - 2 * γ)), (Real.exp_pos _).le, ?_⟩
  intro N hN hNN₀ α z₁ z₂ hz₂ hz1 hz₁
  have hp : (0 : ℝ) ≤ 3 - 2 * γ := by linarith
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN₀R : (0 : ℝ) < (N₀ : ℝ) := by
    have : (1 : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast le_trans hN hNN₀
    linarith
  set S : Finset ℕ := (Finset.Ioc (N / 2) N).filter
    (fun n : ℕ => z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁) with hSdef
  -- the trivial bound on the count
  have hcard : (S.card : ℝ) ≤ (N : ℝ) := by
    have h1 : S.card ≤ N := by
      rw [hSdef]
      refine le_trans (Finset.card_filter_le _ _) ?_
      rw [Nat.card_Ioc]
      omega
    exact_mod_cast h1
  have hx0 : 0 ≤ (z₁ - z₂) * (N : ℝ) / 2 := by
    have : 0 ≤ z₁ - z₂ := by linarith
    positivity
  have hxN : (z₁ - z₂) * (N : ℝ) / 2 ≤ (N : ℝ) := by
    have h1 : z₁ - z₂ ≤ 1 := by linarith
    have h2 : (z₁ - z₂) * (N : ℝ) / 2 ≤ 1 * (N : ℝ) / 2 := by
      have : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
      nlinarith
    linarith
  -- the exp factor is at least `1/B`
  have hL0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hLM : Real.log (N : ℝ) ≤ Real.log (N₀ : ℝ) :=
    Real.log_le_log hNR (by exact_mod_cast hNN₀)
  have hpow : Real.log (N : ℝ) ^ (3 - 2 * γ) ≤ Real.log (N₀ : ℝ) ^ (3 - 2 * γ) :=
    Real.rpow_le_rpow hL0 hLM hp
  have hexp : (1 : ℝ) ≤
      Real.exp (κ * Real.log (N₀ : ℝ) ^ (3 - 2 * γ)) *
        Real.exp (-κ * Real.log (N : ℝ) ^ (3 - 2 * γ)) := by
    rw [← Real.exp_add, ← Real.exp_zero]
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  have hmain : |(S.card : ℝ) - (z₁ - z₂) * (N : ℝ) / 2| ≤ (N : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  calc |(S.card : ℝ) - (z₁ - z₂) * (N : ℝ) / 2|
      ≤ (N : ℝ) := hmain
    _ = (N : ℝ) * 1 := by ring
    _ ≤ (N : ℝ) * (Real.exp (κ * Real.log (N₀ : ℝ) ^ (3 - 2 * γ)) *
          Real.exp (-κ * Real.log (N : ℝ) ^ (3 - 2 * γ))) := by
        exact mul_le_mul_of_nonneg_left hexp hNR.le
    _ = Real.exp (κ * Real.log (N₀ : ℝ) ^ (3 - 2 * γ)) * (N : ℝ) *
          Real.exp (-κ * Real.log (N : ℝ) ^ (3 - 2 * γ)) := by ring

/-! ### Assembly -/

/-- `Lemma4`: the count of `N/2 < n ≤ N` with `z₂ ≤ {αF(n)} < z₁` is `(z₁ - z₂)N/2` up to
`O(N exp(-κ (log N)^{3-2γ}))`, uniformly for `F(N)^{-1/2} < |α| ≤ 1`.  Proved from the leaves
above, with no `sorry` here and without using the target theorem. -/
theorem lemma4_split : Lemma4 := by
  intro γ hγ1 hγ2
  obtain ⟨κ₁, B₁, hκ₁, hB₁, hsum⟩ :=
    leaf_exp_sum_bound γ hγ1 hγ2 ((γ - 1) / 2) (by linarith) (by linarith)
  obtain ⟨N₀, hN₀⟩ := leaf_log_regime γ hγ1 hγ2 ((γ - 1) / 2) (by linarith)
  obtain ⟨κ, B, hκ, hB, habs⟩ := leaf_absorption γ hγ1 hγ2 κ₁ B₁ hκ₁ hB₁
  obtain ⟨B₂, -, hsmall⟩ := leaf_small_N γ hγ1 hγ2 κ hκ (max N₀ 1)
  refine ⟨κ, max B B₂, hκ, ?_⟩
  intro N hN α hlow hhigh z₁ z₂ hz₂ hz1 hz₁
  have hE : (0 : ℝ) ≤ Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := (Real.exp_pos _).le
  rcases lt_or_ge N (max N₀ 1) with hlt | hge
  · have hs := hsmall N hN (le_of_lt hlt) α z₁ z₂ hz₂ hz1 hz₁
    calc |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
            z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
          - (z₁ - z₂) * N / 2|
        ≤ B₂ * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := hs
      _ ≤ max B B₂ * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := by
          refine mul_le_mul_of_nonneg_right ?_ hE
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · obtain ⟨h3, -, -, hceilF⟩ := hN₀ N (le_trans (le_max_left _ _) hge)
    have hfej := leaf_fejer_majorant γ α z₁ z₂ N (Nat.ceil (Real.log N)) hz₂ hz1 hz₁
    have hterm : ∀ h ∈ Finset.Icc 1 (Nat.ceil (Real.log N)),
        ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ ≤
          B₁ * N * Real.exp (-κ₁ * Real.log N ^ (3 - 2 * γ)) := by
      intro h hh
      obtain ⟨hh1, hh2⟩ := Finset.mem_Icc.mp hh
      have hhF : (h : ℝ) ≤ F γ N ^ ((γ - 1) / 2) := by
        refine le_trans (by exact_mod_cast hh2) hceilF
      exact hsum N hN α hlow hhigh h hh1 hhF
    have hS : ∑ h ∈ Finset.Icc 1 (Nat.ceil (Real.log N)),
          ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / ((h : ℝ) + 1)
        ≤ B₁ * N * Real.exp (-κ₁ * Real.log N ^ (3 - 2 * γ))
            * ∑ h ∈ Finset.Icc 1 (Nat.ceil (Real.log N)), 1 / ((h : ℝ) + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun h hh => ?_
      have ht := hterm h hh
      have hpos : (0 : ℝ) ≤ ((h : ℝ) + 1)⁻¹ := by positivity
      calc ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / ((h : ℝ) + 1)
          = ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ * ((h : ℝ) + 1)⁻¹ := by
            ring
        _ ≤ (B₁ * N * Real.exp (-κ₁ * Real.log N ^ (3 - 2 * γ))) * ((h : ℝ) + 1)⁻¹ :=
            mul_le_mul_of_nonneg_right ht hpos
        _ = B₁ * N * Real.exp (-κ₁ * Real.log N ^ (3 - 2 * γ)) * (1 / ((h : ℝ) + 1)) := by
            ring
    have hstep : 4 * N * ∑ h ∈ Finset.Icc 1 (Nat.ceil (Real.log N)),
          ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / ((h : ℝ) + 1)
        ≤ 4 * N * (B₁ * N * Real.exp (-κ₁ * Real.log N ^ (3 - 2 * γ))
            * ∑ h ∈ Finset.Icc 1 (Nat.ceil (Real.log N)), 1 / ((h : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hS (by positivity)
    have hmain : |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
          z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
        - (z₁ - z₂) * N / 2| ≤ B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) :=
      le_trans hfej (le_trans (add_le_add_right hstep _) (habs N h3))
    calc |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
            z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
          - (z₁ - z₂) * N / 2|
        ≤ B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := hmain
      _ ≤ max B B₂ * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := by
          refine mul_le_mul_of_nonneg_right ?_ hE
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

end LeanLab.ExceptionalSet.U1539
