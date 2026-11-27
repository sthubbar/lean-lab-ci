/-
Split of leaf306_lemma7 of Split306Theorem6.lean: BJS Lemma 7, page 7 of
Bordignon, Johnston and Starichkova, arXiv 2207.09452v6, papers/P0009.pdf, pages 6 to 7,
display 18 with c_n of Table 2, proved in Section 2.2 via displays 19, 20 and 21.
The twin leaf306_lemma7_twin is proved from
* the case n = 2 through display 19 and the numerical check c_2 = 0.33, both proved here;
* for 3 ≤ n ≤ 500, the grid certificate of Section 2.2, last paragraph: the bounds
  f_n(x_i) ≤ 2 e ^ 2 c_n ^ (n - 1) h(x_(i+1)) at the points x_i = 1 + i / 1000 for odd n and
  x_i = 2 + i / 1000 for even n, which the paper obtains from display 21 recursively;
* the facts used in that paragraph, proved here: f_n and h are decreasing, and f_n(t) = 0
  for t ≥ n + 2.
The Riemann sum inequality of display 21 is also proved here, as riemann21_1122.
LEAF sorries: lemma7_grid_odd1122 and lemma7_grid_even1122, the numerical certificate.
burst-20261124 S9: lemma7_grid_even1122 is proved from the LEAF lemma7_grid_cert_even1122e of
Split1122bGridCert.lean with Riemann step 1 / 10000; lemma7_grid_odd1122 is suspected false
at n = 33, i = 0, notes/burst-20261124/Cai2002-S9-12-grid-cert.md.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Split306Theorem6
import LeanLab.Cai2002.Split1122bGridCert

open Finset Real
noncomputable section
namespace LeanLab.Cai2002

/-- h of BJS display 7 is decreasing on [1, ∞), as used in Section 2.2, page 8. -/
theorem hSieve_antitone1122 : AntitoneOn LeanLab.ChenExplicit.hSieve (Set.Ici 1) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  have key : ∀ c : ℝ, 3 < b → exp (-b) ≤ c → 3 * b⁻¹ * exp (-b) ≤ c := by
    intro c hb3 hc
    have h3 : 3 * b⁻¹ ≤ 1 := by
      rw [mul_inv_le_iff₀ (by linarith)]; linarith
    nlinarith [exp_pos (-b)]
  unfold LeanLab.ChenExplicit.hSieve
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;>
    first
    | exact le_rfl
    | (exfalso; linarith)
    | exact exp_le_exp.mpr (by linarith)
    | exact key _ (by linarith) (exp_le_exp.mpr (by linarith))
    | (apply mul_le_mul (mul_le_mul_of_nonneg_left (inv_anti₀ (by linarith) hab) (by norm_num))
        (exp_le_exp.mpr (by linarith)) (exp_pos _).le
       have : 0 < a := by linarith
       positivity)

/-- f_n(t) = 0 for t ≥ n + 2, BJS Section 2.2, page 8, from displays 15 to 17. -/
theorem fn_support1122 (n : ℕ) (hn : 1 ≤ n) (s : ℝ) (hs : (n : ℝ) + 2 ≤ s) :
    bjsF306 n s = 0 := by
  induction n using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    match n, ih, hn, hs with
    | 0, _, h, _ => omega
    | 1, _, _, hs =>
      simp only [bjsF306]
      push_cast at hs
      split_ifs with h3
      · have : s = 3 := by linarith
        subst this; norm_num
      · rfl
    | m + 2, ih, _, hs =>
      push_cast at hs
      have hm0 : (0 : ℝ) ≤ m := m.cast_nonneg
      simp only [bjsF306]
      have hz : ∀ σ : ℝ, (m : ℝ) + 4 ≤ σ →
          (∫ t in Set.Ioi σ, bjsF306 (m + 1) (t - 1)) = 0 := by
        intro σ hσ
        rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
          (g := fun _ => (0 : ℝ)) (fun t ht => ?_)]
        · simp
        · have ht' : σ < t := ht
          exact ih (m + 1) (by omega) (by omega) (t - 1) (by push_cast; linarith)
      split_ifs with h
      · exfalso; linarith [h.2]
      · rw [hz s (by linarith)]; simp

/-- Integrability of t ↦ f_m(t - 1) on (σ, ∞), given that f_m is decreasing, from the
bounds of display 18 with c_1 = 1 and of Lemma 8, both proved in Split306Theorem6. -/
theorem integrableOn_shift1122 (m : ℕ) (hm : 1 ≤ m) (σ : ℝ) (hσ : 1 ≤ σ)
    (hdom : ∀ t, σ < t → (Odd m ∧ 1 ≤ t - 1) ∨ (Even m ∧ 2 ≤ t - 1))
    (hanti : ∀ a b : ℝ, ((Odd m ∧ 1 ≤ a) ∨ (Even m ∧ 2 ≤ a)) → a ≤ b →
      bjsF306 m b ≤ bjsF306 m a) :
    MeasureTheory.IntegrableOn (fun t => bjsF306 m (t - 1)) (Set.Ioi σ) := by
  obtain ⟨K, hK⟩ : ∃ K : ℝ, ∀ t, σ < t →
      bjsF306 m (t - 1) ≤ K * LeanLab.ChenExplicit.hSieve (t - 1) := by
    rcases Nat.lt_or_ge m 2 with h1 | h2
    · have : m = 1 := by omega
      subst this
      refine ⟨2 * exp 2 * bjsC306 1 ^ (1 - 1), fun t ht => ?_⟩
      exact display18_one306 (t - 1) (by rcases hdom t ht with h | h <;> linarith [h.2])
    · exact ⟨_, fun t ht => leaf306_lemma8 m h2 (t - 1) (hdom t ht)⟩
  have hmeas : AntitoneOn (fun t => bjsF306 m (t - 1)) (Set.Ioi σ) := by
    intro a ha b hb hab
    exact hanti (a - 1) (b - 1) (hdom a ha) (by linarith)
  refine ((leaf306_hshift_integrable σ hσ).const_mul K).mono'
    (aemeasurable_restrict_of_antitoneOn measurableSet_Ioi hmeas).aestronglyMeasurable ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs, abs_of_nonneg (leaf306_fn_nonneg m (t - 1) (hdom t ht))]
  exact hK t ht

/-- The tail integral of a nonnegative integrable function decreases in the lower limit. -/
theorem tail_mono1122 (g : ℝ → ℝ) (σ a b : ℝ) (hσa : σ ≤ a) (hab : a ≤ b)
    (hi : MeasureTheory.IntegrableOn g (Set.Ioi σ)) (h0 : ∀ t, σ < t → 0 ≤ g t) :
    ∫ t in Set.Ioi b, g t ≤ ∫ t in Set.Ioi a, g t := by
  refine MeasureTheory.setIntegral_mono_set (hi.mono_set (Set.Ioi_subset_Ioi hσa)) ?_
    (Filter.Eventually.of_forall (Set.Ioi_subset_Ioi hab))
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  exact h0 t (lt_of_le_of_lt hσa ht)

/-- f_n is decreasing in s, n odd and s ≥ 1 or n even and s ≥ 2, as stated in BJS
Section 2.2, page 8, before display 21. Proved by strong induction on n from displays 15
to 17. -/
theorem fn_antitone1122 (n : ℕ) (hn : 1 ≤ n) (a b : ℝ)
    (ha : (Odd n ∧ 1 ≤ a) ∨ (Even n ∧ 2 ≤ a)) (hab : a ≤ b) :
    bjsF306 n b ≤ bjsF306 n a := by
  induction n using Nat.strong_induction_on generalizing a b with
  | _ n ih =>
    match n, ih, hn, ha with
    | 0, _, h, _ => omega
    | 1, _, _, ha =>
      have ha1 : 1 ≤ a := by rcases ha with h | h <;> [exact h.2; exact absurd h.1 (by decide)]
      simp only [bjsF306]
      split_ifs with h1 h2 h2
      · rw [div_le_div_iff₀ (by linarith : (0:ℝ) < b) (by linarith : (0:ℝ) < a)]; nlinarith
      · exfalso; linarith
      · exact div_nonneg (by linarith) (by linarith)
      · exact le_rfl
    | m + 2, ih, _, ha =>
      have ha1 : 1 ≤ a := by rcases ha with h | h <;> linarith [h.2]
      have anti' : ∀ x y : ℝ, ((Odd (m + 1) ∧ 1 ≤ x) ∨ (Even (m + 1) ∧ 2 ≤ x)) → x ≤ y →
          bjsF306 (m + 1) y ≤ bjsF306 (m + 1) x :=
        fun x y hx hxy => ih (m + 1) (by omega) (by omega) x y hx hxy
      rcases Nat.even_or_odd (m + 2) with he | ho
      · -- n even, a ≥ 2, the integrand is f_(m+1) at t - 1 ≥ 1 with m + 1 odd
        have ha2 : 2 ≤ a := by
          rcases ha with h' | h'
          · exact absurd h'.1 (by rw [Nat.not_odd_iff_even]; exact he)
          · exact h'.2
        have hodd : Odd (m + 1) := by
          rcases Nat.even_or_odd (m + 1) with he' | ho'
          · exact absurd he (by rw [Nat.not_even_iff_odd]; exact he'.add_one)
          · exact ho'
        have hno : ¬ Odd (m + 2) := by rw [Nat.not_odd_iff_even]; exact he
        have hdom : ∀ t : ℝ, a < t → (Odd (m + 1) ∧ 1 ≤ t - 1) ∨ (Even (m + 1) ∧ 2 ≤ t - 1) :=
          fun t ht => Or.inl ⟨hodd, by linarith⟩
        have hi := integrableOn_shift1122 (m + 1) (by omega) a ha1 hdom anti'
        have h0 : ∀ t, a < t → 0 ≤ bjsF306 (m + 1) (t - 1) :=
          fun t ht => leaf306_fn_nonneg _ _ (hdom t ht)
        simp only [bjsF306, hno, false_and, ite_false]
        have hIb := tail_mono1122 _ a a b le_rfl hab hi h0
        have hIa : 0 ≤ ∫ t in Set.Ioi a, bjsF306 (m + 1) (t - 1) :=
          MeasureTheory.setIntegral_nonneg measurableSet_Ioi (fun t ht => h0 t ht)
        calc (∫ t in Set.Ioi b, bjsF306 (m + 1) (t - 1)) / b
            ≤ (∫ t in Set.Ioi a, bjsF306 (m + 1) (t - 1)) / b :=
              div_le_div_of_nonneg_right hIb (by linarith)
          _ ≤ (∫ t in Set.Ioi a, bjsF306 (m + 1) (t - 1)) / a :=
              div_le_div_of_nonneg_left hIa (by linarith) hab
      · -- n odd, a ≥ 1, the integrand is f_(m+1) at t - 1 ≥ 2 for t > 3, m + 1 even
        have hev : Even (m + 1) := by
          rcases Nat.even_or_odd (m + 1) with he' | ho'
          · exact he'
          · exact absurd ho (by rw [Nat.not_odd_iff_even]; exact ho'.add_one)
        have hdom : ∀ t : ℝ, 3 < t → (Odd (m + 1) ∧ 1 ≤ t - 1) ∨ (Even (m + 1) ∧ 2 ≤ t - 1) :=
          fun t ht => Or.inr ⟨hev, by linarith⟩
        have hi := integrableOn_shift1122 (m + 1) (by omega) 3 (by norm_num) hdom anti'
        have h0 : ∀ t : ℝ, 3 < t → 0 ≤ bjsF306 (m + 1) (t - 1) :=
          fun t ht => leaf306_fn_nonneg _ _ (hdom t ht)
        have hnn : ∀ σ, 3 ≤ σ → 0 ≤ ∫ t in Set.Ioi σ, bjsF306 (m + 1) (t - 1) := by
          intro σ hσ
          exact MeasureTheory.setIntegral_nonneg measurableSet_Ioi
            (fun t ht => h0 t (lt_of_le_of_lt hσ ht))
        simp only [bjsF306, ho, true_and]
        split_ifs with hb ha3 ha3
        · exact div_le_div_of_nonneg_left (hnn 3 le_rfl) (by linarith) hab
        · exfalso; linarith
        · calc (∫ t in Set.Ioi b, bjsF306 (m + 1) (t - 1)) / b
              ≤ (∫ t in Set.Ioi 3, bjsF306 (m + 1) (t - 1)) / b :=
                div_le_div_of_nonneg_right (tail_mono1122 _ 3 3 b le_rfl (by linarith) hi h0)
                  (by linarith)
            _ ≤ (∫ t in Set.Ioi 3, bjsF306 (m + 1) (t - 1)) / a :=
                div_le_div_of_nonneg_left (hnn 3 le_rfl) (by linarith) hab
        · calc (∫ t in Set.Ioi b, bjsF306 (m + 1) (t - 1)) / b
              ≤ (∫ t in Set.Ioi a, bjsF306 (m + 1) (t - 1)) / b :=
                div_le_div_of_nonneg_right
                  (tail_mono1122 _ 3 a b (by linarith) hab hi h0) (by linarith)
            _ ≤ (∫ t in Set.Ioi a, bjsF306 (m + 1) (t - 1)) / a :=
                div_le_div_of_nonneg_left (hnn a (by linarith)) (by linarith) hab

/-- The last paragraph of BJS Section 2.2, page 8: since f_n and h are decreasing, a bound
f_n(x_i) ≤ C h(x_(i+1)) at the grid points x_i = a + i / 1000 up to n + 2 gives
f_n(s) ≤ C h(s) for all s ≥ a, with f_n(s) = 0 for s ≥ n + 2. -/
theorem grid_to_display18_1122 (n : ℕ) (hn : 1 ≤ n) (a C : ℝ) (M : ℕ) (ha1 : 1 ≤ a)
    (hdom : ∀ s, a ≤ s → (Odd n ∧ 1 ≤ s) ∨ (Even n ∧ 2 ≤ s))
    (hM : (n : ℝ) + 2 ≤ a + M / 1000) (hC : 0 ≤ C)
    (hgrid : ∀ i : ℕ, i < M → bjsF306 n (a + i / 1000) ≤
      C * LeanLab.ChenExplicit.hSieve (a + (i + 1) / 1000))
    (s : ℝ) (hs : a ≤ s) : bjsF306 n s ≤ C * LeanLab.ChenExplicit.hSieve s := by
  by_cases hsup : (n : ℝ) + 2 ≤ s
  · rw [fn_support1122 n hn s hsup]
    exact mul_nonneg hC (hSieve_nonneg306 s (by linarith))
  · push Not at hsup
    set i := ⌊(s - a) * 1000⌋₊ with hi
    have hx0 : 0 ≤ (s - a) * 1000 := by nlinarith
    have hi1 : (i : ℝ) ≤ (s - a) * 1000 := Nat.floor_le hx0
    have hi2 : (s - a) * 1000 < (i : ℝ) + 1 := Nat.lt_floor_add_one _
    have hiM : i < M := by
      have : (i : ℝ) < M := by linarith
      exact_mod_cast this
    have hxi : a + (i : ℝ) / 1000 ≤ s := by linarith
    have hxi1 : s ≤ a + ((i : ℝ) + 1) / 1000 := by linarith
    have hi0 : (0 : ℝ) ≤ i := i.cast_nonneg
    calc bjsF306 n s ≤ bjsF306 n (a + (i : ℝ) / 1000) :=
          fn_antitone1122 n hn _ s (hdom _ (by linarith)) hxi
      _ ≤ C * LeanLab.ChenExplicit.hSieve (a + ((i : ℝ) + 1) / 1000) := hgrid i hiM
      _ ≤ C * LeanLab.ChenExplicit.hSieve s :=
          mul_le_mul_of_nonneg_left
            (hSieve_antitone1122 (Set.mem_Ici.mpr (by linarith))
              (Set.mem_Ici.mpr (by linarith)) hxi1) hC

/-- BJS display 19, page 7: s f_2(s) = s - 3 log(s - 1) + 3 log 3 - 4 for 2 ≤ s ≤ 4,
from display 16 with display 15: the integral of (4 - t) / (t - 1) over (s, 4), by the
fundamental theorem of calculus, with f_1(t - 1) = 0 for t > 4. -/
theorem lemma7_display19_1122 (s : ℝ) (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    s * bjsF306 2 s = s - 3 * log (s - 1) + 3 * log 3 - 4 := by
  have hfs : s * bjsF306 2 s = ∫ t in Set.Ioi s, bjsF306 1 (t - 1) := by
    simp only [bjsF306, show ¬ Odd (0 + 2) by decide, false_and, ite_false]
    field_simp
  rw [hfs]
  have hzero : ∀ t ∈ Set.Ioi (4 : ℝ), bjsF306 1 (t - 1) = 0 := by
    intro t ht
    have ht' : (4 : ℝ) < t := ht
    simp only [bjsF306]
    rw [if_neg (by linarith)]
  have hon : ∀ t ∈ Set.Icc s 4, bjsF306 1 (t - 1) = (4 - t) / (t - 1) := by
    intro t ht
    simp only [bjsF306]
    rw [if_pos (by linarith [ht.2])]
    ring_nf
  have hcont : ContinuousOn (fun t : ℝ => (4 - t) / (t - 1)) (Set.Icc s 4) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro t ht; linarith [ht.1]
  have hi1 : MeasureTheory.IntegrableOn (fun t => bjsF306 1 (t - 1)) (Set.Ioc s 4) := by
    refine ((hcont.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self).congr_fun ?_
      measurableSet_Ioc
    intro t ht
    exact (hon t (Set.Ioc_subset_Icc_self ht)).symm
  have hi2 : MeasureTheory.IntegrableOn (fun t => bjsF306 1 (t - 1)) (Set.Ioi 4) := by
    refine (MeasureTheory.integrableOn_zero).congr_fun (fun t ht => (hzero t ht).symm)
      measurableSet_Ioi
  rw [← Set.Ioc_union_Ioi_eq_Ioi hs4,
    MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hi1 hi2]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hzero, MeasureTheory.integral_zero,
    add_zero]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    (fun t ht => hon t (Set.Ioc_subset_Icc_self ht)), ← intervalIntegral.integral_of_le hs4]
  have hderiv : ∀ x ∈ Set.uIcc s 4,
      HasDerivAt (fun t : ℝ => 3 * log (t - 1) - t) ((4 - x) / (x - 1)) x := by
    intro x hx
    rw [Set.uIcc_of_le hs4] at hx
    have hx1 : x - 1 ≠ 0 := by linarith [hx.1]
    have := (((hasDerivAt_id x).sub_const 1).log hx1).const_mul 3 |>.sub (hasDerivAt_id x)
    convert this using 1
    · funext t; simp
    · simp only [id]
      rw [eq_sub_iff_add_eq, mul_one_div, div_add_one hx1, eq_div_iff hx1, div_mul_cancel₀ _ hx1]
      ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((hcont.mono (by rw [Set.uIcc_of_le hs4])).intervalIntegrable)]
  norm_num
  ring

/-- e ^ (-x) ≤ 1 - x + x ^ 2 / 2 for x ≥ 0, Taylor bound used for the check c_2 = 0.33. -/
theorem exp_neg_le_quad1122 (x : ℝ) (hx : 0 ≤ x) : exp (-x) ≤ 1 - x + x ^ 2 / 2 := by
  have hmono : Monotone (fun y : ℝ => 1 - y + y ^ 2 / 2 - exp (-y)) := by
    refine monotone_of_hasDerivAt_nonneg (f' := fun y => -1 + y + exp (-y)) (fun y => ?_) ?_
    · have := ((((hasDerivAt_id y).const_sub 1).add ((hasDerivAt_pow 2 y).div_const 2)).sub
        ((hasDerivAt_neg y).exp))
      convert this using 1
      · funext t; simp only [Pi.add_apply, Pi.sub_apply, id_eq]
      · norm_num
    · intro y
      have := one_sub_le_exp_neg y
      simp only [Pi.zero_apply]; linarith
  have := hmono hx
  simp at this
  linarith

/-- 1 - x + x ^ 2 / 2 - x ^ 3 / 6 ≤ e ^ (-x) for x ≥ 0, Taylor bound used for the check
c_2 = 0.33. -/
theorem cubic_le_exp_neg1122 (x : ℝ) (hx : 0 ≤ x) :
    1 - x + x ^ 2 / 2 - x ^ 3 / 6 ≤ exp (-x) := by
  have hmono : MonotoneOn (fun y : ℝ => exp (-y) - (1 - y + y ^ 2 / 2 - y ^ 3 / 6))
      (Set.Ici 0) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
      (f' := fun y => 1 - y + y ^ 2 / 2 - exp (-y)) (by fun_prop) (fun y _ => ?_) ?_
    · have := ((hasDerivAt_neg y).exp).sub ((((hasDerivAt_id y).const_sub 1).add
        ((hasDerivAt_pow 2 y).div_const 2)).sub ((hasDerivAt_pow 3 y).div_const 6))
      refine HasDerivAt.hasDerivWithinAt ?_
      convert this using 1
      · funext t; simp only [Pi.add_apply, Pi.sub_apply, id_eq]
      · norm_num; ring
    · intro y hy
      rw [interior_Ici] at hy
      have := exp_neg_le_quad1122 y (le_of_lt hy)
      linarith
  have := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hx) hx
  simp at this
  linarith

/-- BJS page 7, the sentence after display 19: from display 19 and the definition 7
of h, c_2 = 0.33 works in display 18, that is
(s - 3 log(s - 1) + 3 log 3 - 4) / s ≤ 2 e ^ 2 0.33 h(s) for 2 ≤ s ≤ 4.
Proved with log(1 + x) ≥ 2 x / (x + 2), the bounds of log 2 and log 3 in Mathlib, and the
cubic Taylor bound for e ^ (-x); the margin is about 2 percent at s = 2. -/
theorem lemma7_c2_1122 (s : ℝ) (hs2 : 2 ≤ s) (hs4 : s ≤ 4) :
    (s - 3 * log (s - 1) + 3 * log 3 - 4) / s ≤
      2 * exp 2 * 0.33 * LeanLab.ChenExplicit.hSieve s := by
  have hl3 := Real.log_three_lt_d9
  have hspos : 0 < s := by linarith
  unfold LeanLab.ChenExplicit.hSieve
  split_ifs with h2 h3
  · have : s = 2 := le_antisymm h2 hs2
    subst this
    rw [div_le_iff₀ hspos, mul_assoc (2 * exp 2), mul_comm (0.33 : ℝ), ← mul_assoc,
      mul_assoc 2, ← exp_add]
    norm_num
    linarith
  · set v := s - 2 with hv
    have hv0 : 0 ≤ v := by linarith
    have hv1 : v ≤ 1 := by linarith
    have hlog : 2 * v / (v + 2) ≤ log (s - 1) := by
      have := le_log_one_add_of_nonneg hv0
      rwa [show 1 + v = s - 1 by rw [hv]; ring] at this
    have hE := cubic_le_exp_neg1122 v hv0
    have hR : 2 * exp 2 * 0.33 * exp (-s) = 0.66 * exp (-v) := by
      rw [hv, show -(s - 2) = 2 + -s by ring, exp_add]; ring
    rw [hR, div_le_iff₀ hspos]
    have hq : 2 * v / (v + 2) * (v + 2) = 2 * v := div_mul_cancel₀ _ (by linarith)
    set q := 2 * v / (v + 2)
    have hpoly : (v - 2 + 3 * 1.0986122888) * (v + 2) - 6 * v ≤
        0.66 * (1 - v + v ^ 2 / 2 - v ^ 3 / 6) * (v + 2) ^ 2 := by
      nlinarith [mul_nonneg hv0 (sub_nonneg.2 hv1), mul_nonneg (mul_nonneg hv0 hv0) (sub_nonneg.2 hv1),
        mul_nonneg (mul_nonneg hv0 hv0) hv0, mul_nonneg (mul_nonneg (mul_nonneg hv0 hv0) hv0) hv0]
    have hq' : v - 2 + 3 * 1.0986122888 - 3 * q ≤ 0.66 * (1 - v + v ^ 2 / 2 - v ^ 3 / 6) * (v + 2) := by
      have hpos : 0 < v + 2 := by linarith
      rw [← mul_le_mul_iff_of_pos_right hpos]
      nlinarith
    have hs : s = v + 2 := by rw [hv]; ring
    rw [hs] at hlog ⊢
    have hEp : 0.66 * (1 - v + v ^ 2 / 2 - v ^ 3 / 6) * (v + 2) ≤ 0.66 * exp (-v) * (v + 2) := by
      have : 0 ≤ v + 2 := by linarith
      nlinarith
    linarith
  · set w := s - 3 with hw
    have hw0 : 0 ≤ w := by linarith
    have hw1 : w ≤ 1 := by linarith
    have hl2 := Real.log_two_gt_d9
    have hlog : log 2 + 2 * (w / 2) / (w / 2 + 2) ≤ log (s - 1) := by
      have := le_log_one_add_of_nonneg (show 0 ≤ w / 2 by linarith)
      have hsplit : log (s - 1) = log 2 + log (1 + w / 2) := by
        rw [← log_mul (by norm_num) (by linarith)]; congr 1; rw [hw]; ring
      rw [hsplit]; linarith
    have hE := cubic_le_exp_neg1122 w hw0
    have he1 := Real.exp_neg_one_gt_d9
    have hR : 2 * exp 2 * 0.33 * (3 * s⁻¹ * exp (-s)) = 1.98 * exp (-1) * exp (-w) / s := by
      have he : exp 2 * exp (-s) = exp (-1) * exp (-w) := by
        rw [← exp_add, ← exp_add, hw]; ring_nf
      rw [show 2 * exp 2 * 0.33 * (3 * s⁻¹ * exp (-s)) = 1.98 * (exp 2 * exp (-s)) / s by
        rw [div_eq_mul_inv]; ring, he]
      ring
    rw [hR, div_le_div_iff_of_pos_right hspos]
    have hq : 2 * (w / 2) / (w / 2 + 2) * (w / 2 + 2) = 2 * (w / 2) :=
      div_mul_cancel₀ _ (by linarith)
    set q := 2 * (w / 2) / (w / 2 + 2)
    have hq0 : 0 ≤ q := by positivity
    have hcub : 0 ≤ 1 - w + w ^ 2 / 2 - w ^ 3 / 6 := by
      nlinarith [mul_nonneg hw0 (sub_nonneg.2 hw1), mul_nonneg (mul_nonneg hw0 hw0) (sub_nonneg.2 hw1)]
    have hEp : 1.98 * 0.36787944116 * (1 - w + w ^ 2 / 2 - w ^ 3 / 6) ≤ 1.98 * exp (-1) * exp (-w) := by
      have := mul_le_mul he1.le hE hcub (exp_pos _).le
      linarith
    have hpoly : w - 1 + 3 * 1.0986122888 - 3 * (0.6931471803 + q) ≤
        1.98 * 0.36787944116 * (1 - w + w ^ 2 / 2 - w ^ 3 / 6) := by
      have hpos : 0 < w / 2 + 2 := by linarith
      rw [← mul_le_mul_iff_of_pos_right hpos]
      nlinarith [mul_nonneg hw0 (sub_nonneg.2 hw1), mul_nonneg (mul_nonneg hw0 hw0) (sub_nonneg.2 hw1),
        mul_nonneg (mul_nonneg hw0 hw0) hw0, mul_nonneg (mul_nonneg (mul_nonneg hw0 hw0) hw0) hw0]
    have hs : s = w + 3 := by rw [hw]; ring
    rw [hs] at hlog ⊢
    linarith

/-- BJS display 21, page 8: for g decreasing on [σ, ∞) and zero from σ + N / 1000 on,
the integral of g over (σ, ∞) is at most the left Riemann sum with step 1 / 1000.
This is the inequality the paper applies recursively to g(t) = f_(n-1)(t - 1) to produce
the grid bounds of lemma7_grid_odd1122 and lemma7_grid_even1122; it is not needed for the
assembly of the twin and is recorded as a proved piece of the paper's method. -/
theorem riemann21_1122 (g : ℝ → ℝ) (σ : ℝ) (N : ℕ) (hanti : AntitoneOn g (Set.Ici σ))
    (hzero : ∀ t, σ + (N : ℝ) / 1000 ≤ t → g t = 0) :
    ∫ t in Set.Ioi σ, g t ≤ ∑ i ∈ range N, g (σ + (i : ℝ) / 1000) / 1000 := by
  set b := σ + (N : ℝ) / 1000 with hb
  have hσb : σ ≤ b := by rw [hb]; have : (0 : ℝ) ≤ N := N.cast_nonneg; linarith
  have hI1 : MeasureTheory.IntegrableOn g (Set.Ioc σ b) :=
    ((hanti.mono Set.Icc_subset_Ici_self).integrableOn_isCompact isCompact_Icc).mono_set
      Set.Ioc_subset_Icc_self
  have hI2 : MeasureTheory.IntegrableOn g (Set.Ioi b) :=
    (MeasureTheory.integrableOn_zero).congr_fun (fun t ht => (hzero t (le_of_lt ht)).symm)
      measurableSet_Ioi
  rw [← Set.Ioc_union_Ioi_eq_Ioi hσb,
    MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hI1 hI2,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0 : ℝ))
      (fun t ht => hzero t (le_of_lt ht)), MeasureTheory.integral_zero, add_zero,
    ← intervalIntegral.integral_of_le hσb]
  have hcv := intervalIntegral.integral_comp_add_div (f := g) (a := 0) (b := (N : ℝ))
    (by norm_num : (1000 : ℝ) ≠ 0) σ
  rw [zero_div, add_zero] at hcv
  have hA : AntitoneOn (fun x : ℝ => g (σ + x / 1000)) (Set.Icc 0 (0 + (N : ℝ))) := by
    intro x hx y hy hxy
    refine hanti (Set.mem_Ici.mpr ?_) (Set.mem_Ici.mpr ?_) (by linarith)
    · have := hx.1; linarith [div_nonneg this (by norm_num : (0 : ℝ) ≤ 1000)]
    · have := hy.1; linarith [div_nonneg this (by norm_num : (0 : ℝ) ≤ 1000)]
  have hsum := hA.integral_le_sum
  simp only [zero_add] at hsum
  rw [hcv, smul_eq_mul] at hsum
  rw [← Finset.sum_div, le_div_iff₀ (by norm_num : (0 : ℝ) < 1000), mul_comm]
  exact hsum

/-- BJS display 21, page 8, for the functions f_m: with σ = max(3, s) or max(4, s) in the
paper, the integral of f_m(t - 1) over (σ, ∞) is at most the Riemann sum
of f_m(σ + i / 1000 - 1) / 1000 over i < N, once σ + N / 1000 ≥ m + 3, since f_m is decreasing
and vanishes from m + 2 on. -/
theorem riemann21_fn1122 (m : ℕ) (hm : 1 ≤ m) (σ : ℝ) (N : ℕ)
    (hdom : ∀ t, σ ≤ t → (Odd m ∧ 1 ≤ t - 1) ∨ (Even m ∧ 2 ≤ t - 1))
    (hN : (m : ℝ) + 3 ≤ σ + (N : ℝ) / 1000) :
    ∫ t in Set.Ioi σ, bjsF306 m (t - 1) ≤
      ∑ i ∈ range N, bjsF306 m (σ + (i : ℝ) / 1000 - 1) / 1000 := by
  refine riemann21_1122 (fun t => bjsF306 m (t - 1)) σ N ?_ ?_
  · intro x hx y hy hxy
    exact fn_antitone1122 m hm (x - 1) (y - 1) (hdom x hx) (by linarith)
  · intro t ht
    exact fn_support1122 m hm (t - 1) (by linarith)

/-- BJS display 21, page 8, with step 1 / 10000 in place of 1 / 1000: for g decreasing on [σ, ∞) and zero from σ + N / 10000 on,
the integral of g over (σ, ∞) is at most the left Riemann sum with step 1 / 10000.
This is the inequality the paper applies recursively to g(t) = f_(n-1)(t - 1) to produce
the grid bounds of lemma7_grid_odd1122 and lemma7_grid_even1122; it is not needed for the
assembly of the twin and is recorded as a proved piece of the paper's method. -/
theorem riemann21_fine1122e (g : ℝ → ℝ) (σ : ℝ) (N : ℕ) (hanti : AntitoneOn g (Set.Ici σ))
    (hzero : ∀ t, σ + (N : ℝ) / 10000 ≤ t → g t = 0) :
    ∫ t in Set.Ioi σ, g t ≤ ∑ i ∈ range N, g (σ + (i : ℝ) / 10000) / 10000 := by
  set b := σ + (N : ℝ) / 10000 with hb
  have hσb : σ ≤ b := by rw [hb]; have : (0 : ℝ) ≤ N := N.cast_nonneg; linarith
  have hI1 : MeasureTheory.IntegrableOn g (Set.Ioc σ b) :=
    ((hanti.mono Set.Icc_subset_Ici_self).integrableOn_isCompact isCompact_Icc).mono_set
      Set.Ioc_subset_Icc_self
  have hI2 : MeasureTheory.IntegrableOn g (Set.Ioi b) :=
    (MeasureTheory.integrableOn_zero).congr_fun (fun t ht => (hzero t (le_of_lt ht)).symm)
      measurableSet_Ioi
  rw [← Set.Ioc_union_Ioi_eq_Ioi hσb,
    MeasureTheory.setIntegral_union (Set.Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hI1 hI2,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0 : ℝ))
      (fun t ht => hzero t (le_of_lt ht)), MeasureTheory.integral_zero, add_zero,
    ← intervalIntegral.integral_of_le hσb]
  have hcv := intervalIntegral.integral_comp_add_div (f := g) (a := 0) (b := (N : ℝ))
    (by norm_num : (10000 : ℝ) ≠ 0) σ
  rw [zero_div, add_zero] at hcv
  have hA : AntitoneOn (fun x : ℝ => g (σ + x / 10000)) (Set.Icc 0 (0 + (N : ℝ))) := by
    intro x hx y hy hxy
    refine hanti (Set.mem_Ici.mpr ?_) (Set.mem_Ici.mpr ?_) (by linarith)
    · have := hx.1; linarith [div_nonneg this (by norm_num : (0 : ℝ) ≤ 10000)]
    · have := hy.1; linarith [div_nonneg this (by norm_num : (0 : ℝ) ≤ 10000)]
  have hsum := hA.integral_le_sum
  simp only [zero_add] at hsum
  rw [hcv, smul_eq_mul] at hsum
  rw [← Finset.sum_div, le_div_iff₀ (by norm_num : (0 : ℝ) < 10000), mul_comm]
  exact hsum

/-- BJS display 21, page 8, step 1 / 10000, for the functions f_m: with σ = max(3, s) or max(4, s) in the
paper, the integral of f_m(t - 1) over (σ, ∞) is at most the Riemann sum
of f_m(σ + i / 10000 - 1) / 10000 over i < N, once σ + N / 10000 ≥ m + 3, since f_m is decreasing
and vanishes from m + 2 on. -/
theorem riemann21_fn_fine1122e (m : ℕ) (hm : 1 ≤ m) (σ : ℝ) (N : ℕ)
    (hdom : ∀ t, σ ≤ t → (Odd m ∧ 1 ≤ t - 1) ∨ (Even m ∧ 2 ≤ t - 1))
    (hN : (m : ℝ) + 3 ≤ σ + (N : ℝ) / 10000) :
    ∫ t in Set.Ioi σ, bjsF306 m (t - 1) ≤
      ∑ i ∈ range N, bjsF306 m (σ + (i : ℝ) / 10000 - 1) / 10000 := by
  refine riemann21_fine1122e (fun t => bjsF306 m (t - 1)) σ N ?_ ?_
  · intro x hx y hy hxy
    exact fn_antitone1122 m hm (x - 1) (y - 1) (hdom x hx) (by linarith)
  · intro t ht
    exact fn_support1122 m hm (t - 1) (by linarith)

/-- Grid index form of the Riemann sum terms of display 21, step 1 / 10000. -/
theorem grid_term_fine1122e (m J i : ℕ) (hJ : 10000 ≤ J) :
    bjsF306 m ((J : ℝ) / 10000 + (i : ℝ) / 10000 - 1) / 10000 =
      bjsF306 m (((J + i - 10000 : ℕ) : ℝ) / 10000) / 10000 := by
  congr 2
  rw [Nat.cast_sub (by omega)]; push_cast; ring

/-- BJS Section 2.2, page 8: display 21 applied recursively, with step 1 / 10000. Any table U
satisfying the first three conditions of lemma7_grid_cert_even1122e bounds f_n on the grid
x = k / 10000, for odd n with x ≥ 1 and even n with x ≥ 2, n ≤ 500, by strong induction on n. -/
theorem grid_table_bound_fine1122e (U : ℕ → ℕ → ℝ) (h0 : ∀ n j, 0 ≤ U n j)
    (h1 : ∀ j : ℕ, 10000 ≤ j → j ≤ 30000 → (3 - (j : ℝ) / 10000) / ((j : ℝ) / 10000) ≤ U 1 j)
    (hrec : ∀ n, 2 ≤ n → n ≤ 500 → ∀ j : ℕ, ((Odd n ∧ 10000 ≤ j) ∨ (Even n ∧ 20000 ≤ j)) →
      j < 10000 * (n + 2) →
      (∑ i ∈ range (10000 * (n + 3)),
        U (n - 1) ((if Odd n then max j 30000 else j) + i - 10000)) / (j : ℝ) ≤ U n j) :
    ∀ n, 1 ≤ n → n ≤ 500 → ∀ j : ℕ, ((Odd n ∧ 10000 ≤ j) ∨ (Even n ∧ 20000 ≤ j)) →
      bjsF306 n ((j : ℝ) / 10000) ≤ U n j := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn1 hn j hj
  match n, ih, hn1, hn, hj with
  | 1, _, _, _, hj =>
    have hj1 : 10000 ≤ j := by rcases hj with h | h; exact h.2; exact absurd h.1 (by decide)
    simp only [bjsF306]
    split_ifs with h3
    · refine h1 j hj1 ?_
      have : (j : ℝ) ≤ 30000 := by linarith
      exact_mod_cast this
    · exact h0 1 j
  | m + 2, ih, _, hn, hj =>
    by_cases hbig : 10000 * (m + 2 + 2) ≤ j
    · rw [fn_support1122 (m + 2) (by omega) _ (by
        have : ((10000 * (m + 2 + 2) : ℕ) : ℝ) ≤ j := by exact_mod_cast hbig
        rw [le_div_iff₀ (by norm_num)]; push_cast at this ⊢; linarith)]
      exact h0 _ _
    push Not at hbig
    have hj1 : 10000 ≤ j := by rcases hj with h | h <;> omega
    have hjpos : (0 : ℝ) < j := by have : (10000 : ℝ) ≤ j := by exact_mod_cast hj1
                                   linarith
    have hR := hrec (m + 2) (by omega) hn j hj hbig
    simp only [show m + 2 - 1 = m + 1 by omega] at hR
    set J := (if Odd (m + 2) then max j 30000 else j) with hJdef
    have hJ1 : 10000 ≤ J := by rw [hJdef]; split_ifs <;> omega
    -- the IH on the shifted indices
    have hIH : ∀ i, bjsF306 (m + 1) (((J + i - 10000 : ℕ) : ℝ) / 10000) ≤ U (m + 1) (J + i - 10000) := by
      intro i
      refine ih (m + 1) (by omega) (by omega) (by omega) _ ?_
      rcases Nat.even_or_odd (m + 2) with he | ho
      · left
        refine ⟨by rcases he with ⟨r, hr⟩; exact ⟨r - 1, by omega⟩, ?_⟩
        rw [hJdef, if_neg (Nat.not_odd_iff_even.mpr he)]
        rcases hj with h | h
        · exact absurd h.1 (Nat.not_odd_iff_even.mpr he)
        · omega
      · right
        refine ⟨by rcases ho with ⟨r, hr⟩; exact ⟨r, by omega⟩, ?_⟩
        rw [hJdef, if_pos ho]; omega
    have hsum : bjsF306 (m + 2) ((j : ℝ) / 10000) ≤
        (∑ i ∈ range (10000 * (m + 2 + 3)), bjsF306 (m + 1) (((J + i - 10000 : ℕ) : ℝ) / 10000)) / j := by
      have hdom : ∀ t : ℝ, (J : ℝ) / 10000 ≤ t →
          (Odd (m + 1) ∧ 1 ≤ t - 1) ∨ (Even (m + 1) ∧ 2 ≤ t - 1) := by
        intro t ht
        rcases Nat.even_or_odd (m + 2) with he | ho
        · left
          refine ⟨by rcases he with ⟨r, hr⟩; exact ⟨r - 1, by omega⟩, ?_⟩
          have : (20000 : ℝ) ≤ J := by
            rw [hJdef, if_neg (Nat.not_odd_iff_even.mpr he)]
            rcases hj with h | h
            · exact absurd h.1 (Nat.not_odd_iff_even.mpr he)
            · exact_mod_cast h.2
          linarith
        · right
          refine ⟨by rcases ho with ⟨r, hr⟩; exact ⟨r, by omega⟩, ?_⟩
          have : (30000 : ℝ) ≤ J := by
            rw [hJdef, if_pos ho]; exact_mod_cast (le_max_right j 30000)
          linarith
      have hRm := riemann21_fn_fine1122e (m + 1) (by omega) ((J : ℝ) / 10000) (10000 * (m + 2 + 3)) hdom
        (by push_cast; have : (0 : ℝ) ≤ J / 10000 := by positivity
            linarith)
      simp only [grid_term_fine1122e _ J _ hJ1] at hRm
      rw [← Finset.sum_div] at hRm
      have hval : bjsF306 (m + 2) ((j : ℝ) / 10000) =
          (∫ t in Set.Ioi ((J : ℝ) / 10000), bjsF306 (m + 1) (t - 1)) / ((j : ℝ) / 10000) := by
        simp only [bjsF306]
        rcases Nat.even_or_odd (m + 2) with he | ho
        · have hno : ¬ Odd (m + 2) := Nat.not_odd_iff_even.mpr he
          rw [if_neg (fun h => hno h.1), hJdef, if_neg hno]
        · by_cases h3 : (j : ℝ) / 10000 ≤ 3
          · rw [if_pos ⟨ho, h3⟩, hJdef, if_pos ho]
            have : j ≤ 30000 := by
              have : (j : ℝ) ≤ 30000 := by linarith
              exact_mod_cast this
            rw [max_eq_right this]; norm_num
          · rw [if_neg (fun h => h3 h.2), hJdef, if_pos ho]
            have : 30000 ≤ j := by
              have : (30000 : ℝ) ≤ j := by push Not at h3; linarith
              exact_mod_cast this
            rw [max_eq_left this]
      rw [hval, div_le_iff₀ (by positivity)]
      rw [div_mul_eq_mul_div, le_div_iff₀ hjpos] at *
      calc (∫ t in Set.Ioi ((J : ℝ) / 10000), bjsF306 (m + 1) (t - 1)) * j
          ≤ ((∑ i ∈ range (10000 * (m + 2 + 3)), bjsF306 (m + 1) (((J + i - 10000 : ℕ) : ℝ) / 10000)) / 10000) * j :=
            mul_le_mul_of_nonneg_right hRm hjpos.le
        _ = _ := by ring
    refine hsum.trans (le_trans ?_ hR)
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => hIH i) hjpos.le

/-- At the candidate counterexample point `1001 / 1000`, the sieve function is in its first
piece, so `hSieve (1001 / 1000) = exp (-2)`. -/
theorem hSieve_at_1001_1122 :
    LeanLab.ChenExplicit.hSieve (1 + (1 : ℝ) / 1000) = exp (-2) := by
  unfold LeanLab.ChenExplicit.hSieve
  rw [if_pos (by norm_num)]

/-- The Table 2 value used at the candidate counterexample point `n = 33` is `0.69`. -/
theorem bjsC306_at_33_1122 : bjsC306 33 = 0.69 := by
  unfold bjsC306
  norm_num

/-- LEAF: QUESTION, suspected false at n = 33, i = 0, burst-20261124 S9: float upper and lower
Riemann tables with step 1 / 100000 give f_33(1) between 1.0034 and 1.0038 times the right side.
BJS Section 2.2, last paragraph, page 8, odd n: the computed grid bounds
f_n(x_i) ≤ 2 e ^ 2 c_n ^ (n - 1) h(x_(i+1)) with x_i = 1 + i / 1000, 0 ≤ i < 1000 (n + 1),
for odd 3 ≤ n ≤ 499, obtained from display 17 and the Riemann sums of display 21 applied
recursively with step 1 / 1000, c_n of Table 2.
Class HARD: the paper's numerical certificate, about 500 by 500000 grid values. -/
theorem lemma7_grid_odd1122 (n : ℕ) (hn3 : 3 ≤ n) (hn500 : n ≤ 500) (hodd : Odd n)
    (i : ℕ) (hi : i < 1000 * (n + 1)) :
    bjsF306 n (1 + (i : ℝ) / 1000) ≤
      2 * exp 2 * bjsC306 n ^ (n - 1) * LeanLab.ChenExplicit.hSieve (1 + ((i : ℝ) + 1) / 1000) := by
  sorry

/-- Formerly a LEAF, PROVED in burst-20261124 S9 from lemma7_grid_cert_even1122e and
grid_table_bound_fine1122e. BJS Section 2.2, last paragraph, page 8, even n: the computed grid bounds
f_n(x_i) ≤ 2 e ^ 2 c_n ^ (n - 1) h(x_(i+1)) with x_i = 2 + i / 1000, 0 ≤ i < 1000 n,
for even 4 ≤ n ≤ 500, obtained from displays 16 and 20 and the Riemann sums of display 21
applied recursively with step 1 / 1000, c_n of Table 2.
Class HARD: the paper's numerical certificate, about 500 by 500000 grid values. -/
theorem lemma7_grid_even1122 (n : ℕ) (hn4 : 4 ≤ n) (hn500 : n ≤ 500) (heven : Even n)
    (i : ℕ) (hi : i < 1000 * n) :
    bjsF306 n (2 + (i : ℝ) / 1000) ≤
      2 * exp 2 * bjsC306 n ^ (n - 1) * LeanLab.ChenExplicit.hSieve (2 + ((i : ℝ) + 1) / 1000) := by
  obtain ⟨U, h0, h1, hrec, htgt⟩ := lemma7_grid_cert_even1122e
  have hd : (Odd n ∧ 10000 ≤ 10 * (2000 + i)) ∨ (Even n ∧ 20000 ≤ 10 * (2000 + i)) :=
    Or.inr ⟨heven, by omega⟩
  have hb := grid_table_bound_fine1122e U h0 h1 hrec n (by omega) hn500 (10 * (2000 + i)) hd
  have ht := htgt n hn4 hn500 heven (2000 + i) (by omega) (by omega)
  have e1 : (((10 * (2000 + i) : ℕ) : ℝ)) / 10000 = 2 + (i : ℝ) / 1000 := by push_cast; ring
  have e2 : (((2000 + i : ℕ) : ℝ) + 1) / 1000 = 2 + ((i : ℝ) + 1) / 1000 := by push_cast; ring
  rw [e1] at hb; rw [e2] at ht
  exact hb.trans ht

/-- c_n of Table 2 is positive. -/
theorem bjsC_nonneg1122 (n : ℕ) : 0 ≤ bjsC306 n := (bjsC306_pos n).le

/-- BJS Lemma 7 for n = 2, from display 19 and c_2 = 0.33, page 7. -/
theorem lemma7_n2_1122 (s : ℝ) (hs : 2 ≤ s) :
    bjsF306 2 s ≤ 2 * exp 2 * bjsC306 2 ^ (2 - 1) * LeanLab.ChenExplicit.hSieve s := by
  have hc : bjsC306 2 = 0.33 := by unfold bjsC306; norm_num
  rw [hc, show 2 - 1 = 1 by rfl, pow_one]
  by_cases h4 : 4 ≤ s
  · rw [fn_support1122 2 (by norm_num) s (by norm_num; linarith)]
    exact mul_nonneg (by positivity) (hSieve_nonneg306 s (by linarith))
  · push Not at h4
    have h19 := lemma7_display19_1122 s hs h4.le
    have hf : bjsF306 2 s = (s - 3 * log (s - 1) + 3 * log 3 - 4) / s := by
      rw [eq_div_iff (by linarith), mul_comm]; exact h19
    rw [hf]
    exact lemma7_c2_1122 s hs h4.le

/-- Twin of leaf306_lemma7, BJS Lemma 7, page 7: display 18 holds with c_n of Table 2
for 2 ≤ n ≤ 500. Proved from the n = 2 case and the grid certificates of Section 2.2 with
grid_to_display18_1122. -/
theorem leaf306_lemma7_twin (n : ℕ) (hn2 : 2 ≤ n) (hn500 : n ≤ 500) (s : ℝ)
    (hs : (Odd n ∧ 1 ≤ s) ∨ (Even n ∧ 2 ≤ s)) :
    bjsF306 n s ≤ 2 * exp 2 * bjsC306 n ^ (n - 1) * LeanLab.ChenExplicit.hSieve s := by
  have hC : 0 ≤ 2 * exp 2 * bjsC306 n ^ (n - 1) :=
    mul_nonneg (by positivity) (pow_nonneg (bjsC_nonneg1122 n) _)
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · have : n = 2 := by omega
    subst this
    rcases hs with h | h
    · exact absurd h.1 (by decide)
    · exact lemma7_n2_1122 s h.2
  · rcases Nat.even_or_odd n with he | ho
    · have hs2 : 2 ≤ s := by
        rcases hs with h | h
        · exact absurd h.1 (by rw [Nat.not_odd_iff_even]; exact he)
        · exact h.2
      have hn4 : 4 ≤ n := by
        rcases Nat.lt_or_ge n 4 with h | h
        · have : n = 3 := by omega
          subst this; exact absurd he (by decide)
        · exact h
      refine grid_to_display18_1122 n (by omega) 2 _ (1000 * n) (by norm_num)
        (fun x hx => Or.inr ⟨he, hx⟩) ?_ hC ?_ s hs2
      · push_cast; linarith
      · intro i hi
        exact lemma7_grid_even1122 n hn4 hn500 he i hi
    · have hs1 : 1 ≤ s := by rcases hs with h | h <;> linarith [h.2]
      refine grid_to_display18_1122 n (by omega) 1 _ (1000 * (n + 1)) le_rfl
        (fun x hx => Or.inl ⟨ho, hx⟩) ?_ hC ?_ s hs1
      · push_cast; linarith
      · intro i hi
        exact lemma7_grid_odd1122 n h3 hn500 ho i hi

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.grid_table_bound_fine1122e
#print axioms LeanLab.Cai2002.lemma7_grid_even1122
#print axioms LeanLab.Cai2002.leaf306_lemma7_twin
