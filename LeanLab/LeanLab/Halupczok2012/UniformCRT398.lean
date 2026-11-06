import LeanLab.Halupczok2012.U1452MainTermMV

/-!
Halupczok page 344, the CRT main term step uniformly over residue choices.
This reuses the U1452 injective lcm reindexing with one residue for each q.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.UniformCRT398

open Finset
open scoped Classical

/-- Page 344, injective lcm reindexing with a residue chosen for each modulus. -/
theorem piece_le (X Y Q : ℝ) (a : ℕ → ℤ) (s b g : ℕ) (hs : 0 < s) (J : Finset ℕ)
    (hJ : ∀ q ∈ J, 1 ≤ q ∧ (q : ℝ) ≤ Q ∧ Int.gcd (a q) q = 1 ∧ b ∈ crtG (a q) q s ∧ Nat.gcd q s = g) :
    ∃ a' : ℕ → ℤ, (∀ q, Int.gcd (a' q) q = 1) ∧
      ∑ q ∈ J, crtErr X Y (a q) q s b ≤
        ∑ q ∈ Icc 1 ⌊Q * s⌋₊, |thetaAP X Y q (a' q) - Y / (q.totient : ℝ)| := by
  classical
  have hinj : ∀ q1 ∈ J, ∀ q2 ∈ J, Nat.lcm q1 s = Nat.lcm q2 s → q1 = q2 := by
    intro q1 h1 q2 h2 he
    have e1 := Nat.gcd_mul_lcm q1 s
    have e2 := Nat.gcd_mul_lcm q2 s
    rw [(hJ q1 h1).2.2.2.2, he] at e1
    rw [(hJ q2 h2).2.2.2.2] at e2
    have : q1 * s = q2 * s := by rw [← e1, ← e2]
    exact Nat.eq_of_mul_eq_mul_right hs this
  let a' : ℕ → ℤ := fun q' =>
    if h : ∃ q ∈ J, Nat.lcm q s = q' then crtX (a h.choose) h.choose s b else 1
  have ha'J : ∀ q ∈ J, a' (Nat.lcm q s) = crtX (a q) q s b := by
    intro q hq
    have h : ∃ q0 ∈ J, Nat.lcm q0 s = Nat.lcm q s := ⟨q, hq, rfl⟩
    simp only [a', dif_pos h]
    rw [hinj _ h.choose_spec.1 q hq h.choose_spec.2]
  refine ⟨a', ?_, ?_⟩
  · intro q'
    by_cases h : ∃ q ∈ J, Nat.lcm q s = q'
    · simp only [a', dif_pos h]
      obtain ⟨hq, hl⟩ := h.choose_spec
      have := gcd_crtX (hJ _ hq).2.2.1 (hJ _ hq).2.2.2.1
      rw [hl] at this; exact this
    · simp only [a', dif_neg h]; simp
  · calc ∑ q ∈ J, crtErr X Y (a q) q s b
        = ∑ q ∈ J, |thetaAP X Y (Nat.lcm q s) (a' (Nat.lcm q s)) -
            Y / ((Nat.lcm q s).totient : ℝ)| := by
          apply sum_congr rfl; intro q hq; rw [crtErr, ha'J q hq]
      _ = ∑ q' ∈ J.image (fun q => Nat.lcm q s),
            |thetaAP X Y q' (a' q') - Y / (q'.totient : ℝ)| :=
          (sum_image (f := fun q' => |thetaAP X Y q' (a' q') - Y / (q'.totient : ℝ)|)
            (fun x hx y hy h => hinj x hx y hy h)).symm
      _ ≤ _ := by
          apply sum_le_sum_of_subset_of_nonneg _ (fun _ _ _ => abs_nonneg _)
          intro q' hq'
          rw [mem_image] at hq'
          obtain ⟨q, hq, rfl⟩ := hq'
          obtain ⟨h1, hQ, -⟩ := hJ q hq
          rw [mem_Icc]
          refine ⟨Nat.lcm_pos (by omega) hs, Nat.le_floor ?_⟩
          have hle : Nat.lcm q s ≤ q * s :=
            Nat.le_of_dvd (Nat.mul_pos (by omega) hs) (Nat.lcm_dvd_mul q s)
          have hs0 : (0 : ℝ) ≤ s := Nat.cast_nonneg s
          calc ((Nat.lcm q s : ℕ) : ℝ) ≤ ((q * s : ℕ) : ℝ) := by exact_mod_cast hle
            _ = (q : ℝ) * s := by push_cast; ring
            _ ≤ Q * s := mul_le_mul_of_nonneg_right hQ hs0

/-- **The CRT step of the main term, CONDITIONAL ON `Theorem3` only.** For one modulus `s`
and an `s`-periodic weight `f` with `|f| ≤ M`, uniformly in `s`, `f`, `a`:
`∑_{q ≤ Q, (a,q)=1} |∑_{p ∈ (X, X+Y], p ≡ a (q)} log p f(p) - Y/φ([q,s]) ∑_{b ∈ G(a,q,s)} f(b)|
  ≤ s² M C Y L^{-A}` when `Q s ≤ c₂ Y X^{-1/2} (log X)^{-B}`, `s ≤ X`. -/
theorem crtStep (h3 : Theorem3) : ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ B : ℝ, 0 < B ∧
    ∀ c1 c2 : ℝ, 0 < c1 → 0 < c2 → ∃ C Y0 : ℝ,
    ∀ (n s : ℕ) (X Y Q M : ℝ) (a : ℕ → ℤ) (f : ℕ → ℝ),
    Y0 ≤ Y → Y ≤ X → c1 * X ^ (3 / 5 + ε) ≤ Y →
    Q * s ≤ c2 * Y * X ^ (-(1 / 2) : ℝ) * Real.log X ^ (-B) →
    0 < s → (s : ℝ) ≤ X → X + Y ≤ n → (∀ p, f p = f (p % s)) → (∀ b, |f b| ≤ M) →
    ∑ q ∈ (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => Int.gcd (a q) (q : ℤ) = 1),
      |∑ p ∈ P1 n X Y q (a q), Real.log p * f p -
        Y / (Nat.totient (Nat.lcm q s) : ℝ) * ∑ b ∈ crtG (a q) q s, f b| ≤
      (s : ℝ) ^ 2 * M * C * Y * Real.log Y ^ (-A) := by
  classical
  intro A ε hA hε
  obtain ⟨B, hB, h3'⟩ := h3 A ε hA hε
  refine ⟨B, hB, fun c1 c2 hc1 hc2 => ?_⟩
  obtain ⟨C, Y0, hC⟩ := h3' c1 c2 hc1 hc2
  refine ⟨C, Y0, fun n s X Y Q M a f hY0 hYX hc1Y hQs hs hsX hn hf hM => ?_⟩
  set Iq := (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => Int.gcd (a q) (q : ℤ) = 1) with hIq
  set K := C * Y * Real.log Y ^ (-A) with hKdef
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hK0 : 0 ≤ K := by
    have := hC X Y (Q * s) hY0 hYX hc1Y hQs (fun _ => 1) (fun _ => Int.gcd_one_left _)
    exact (sum_nonneg (fun _ _ => abs_nonneg _)).trans this
  have hpiece : ∀ b g : ℕ,
      ∑ q ∈ (Iq.filter (fun q => b ∈ crtG (a q) q s)).filter (fun q => Nat.gcd q s = g),
        crtErr X Y (a q) q s b ≤ K := by
    intro b g
    obtain ⟨a', ha', hle⟩ := piece_le X Y Q a s b g hs
      ((Iq.filter (fun q => b ∈ crtG (a q) q s)).filter (fun q => Nat.gcd q s = g)) (by
      intro q hq
      simp only [hIq, mem_filter, mem_Icc] at hq
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hq
      exact ⟨h1, (Nat.le_floor_iff' (by omega)).mp h2, h3, h4, h5⟩)
    exact hle.trans (hC X Y (Q * s) hY0 hYX hc1Y hQs a' ha')
  have hite : ∀ q, ∑ b ∈ crtG (a q) q s, crtErr X Y (a q) q s b =
      ∑ b ∈ range s, if b ∈ crtG (a q) q s then crtErr X Y (a q) q s b else 0 := by
    intro q
    rw [sum_ite_mem, inter_eq_right.mpr (crtG_subset (a q) q s)]
  have hfib : ∀ b, ∑ q ∈ Iq, (if b ∈ crtG (a q) q s then crtErr X Y (a q) q s b else 0) ≤
      (s.divisors.card : ℝ) * K := by
    intro b
    rw [← sum_filter, ← sum_fiberwise_of_maps_to (g := fun q => Nat.gcd q s) (t := s.divisors)
      (fun q _ => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right _ _, hs.ne'⟩)]
    calc _ ≤ ∑ g ∈ s.divisors, K := sum_le_sum (fun g _ => hpiece b g)
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  have hdiv : (s.divisors.card : ℝ) ≤ s := by exact_mod_cast Nat.card_divisors_le_self s
  calc _ ≤ ∑ q ∈ Iq, M * ∑ b ∈ crtG (a q) q s, crtErr X Y (a q) q s b :=
        sum_le_sum (fun q _ => perQ_abs_le f hs hf hn hsX hM)
    _ = M * ∑ b ∈ range s, ∑ q ∈ Iq,
          (if b ∈ crtG (a q) q s then crtErr X Y (a q) q s b else 0) := by
        rw [← mul_sum, sum_congr rfl (fun q _ => hite q), sum_comm]
    _ ≤ M * ∑ b ∈ range s, (s.divisors.card : ℝ) * K :=
        mul_le_mul_of_nonneg_left (sum_le_sum (fun b _ => hfib b)) hM0
    _ = M * s * ((s.divisors.card : ℝ) * K) := by rw [sum_const, card_range, nsmul_eq_mul]; ring
    _ ≤ M * s * (s * K) := by
        apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hdiv hK0)
        positivity
    _ = _ := by rw [hKdef]; ring

end LeanLab.Halupczok2012.UniformCRT398
