/-
Baker, Harman and Pintz 1997, page 21, display 3.35.
Derivative and finite difference bridges for the logarithmic phase.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.PortedVanDerCorput

namespace LeanLab.BakerHarmanPintz1997.LogPhase219
open PortedVanDerCorput

/-- Page 21. Differentiation commutes with the iterated differences on the positive half line. -/
theorem backwardDifferences_hasDerivAt (hs : List ℝ) (f g : ℝ → ℝ)
    (hfg : ∀ x, 0 < x → HasDerivAt f (g x) x)
    (hhs : ∀ h ∈ hs, 0 ≤ h) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (backwardDifferences hs f) (backwardDifferences hs g x) x := by
  induction hs generalizing x with
  | nil => exact hfg x hx
  | cons h hs ih =>
    have hh := hhs h (by simp)
    have htail : ∀ t ∈ hs, 0 ≤ t := fun t ht => hhs t (by simp [ht])
    exact (ih htail hx).sub (HasDerivAt.comp_add_const x h (ih htail (by linarith : 0 < x + h)))

/-- Page 21. Iterated differences equal a product of shifts times a derivative at an intermediate point. -/
theorem backwardDifferences_meanValue (F : ℕ → ℝ → ℝ)
    (hF : ∀ k x, 0 < x → HasDerivAt (F k) (F (k + 1) x) x)
    (hs : List ℝ) (hhs : ∀ h ∈ hs, 0 < h) (k : ℕ) {x : ℝ} (hx : 0 < x) :
    ∃ y : ℝ, x ≤ y ∧ y ≤ x + hs.sum ∧
      backwardDifferences hs (F k) x =
        (-1 : ℝ) ^ hs.length * hs.prod * F (k + hs.length) y := by
  induction hs generalizing k x with
  | nil => exact ⟨x, le_rfl, by simp, by simp [backwardDifferences]⟩
  | cons h hs ih =>
    have hh := hhs h (by simp)
    have htail : ∀ t ∈ hs, 0 < t := fun t ht => hhs t (by simp [ht])
    have hd : ∀ z, 0 < z → HasDerivAt (backwardDifferences hs (F k))
        (backwardDifferences hs (F (k + 1)) z) z :=
      fun z hz => backwardDifferences_hasDerivAt hs (F k) (F (k + 1)) (hF k)
        (fun t ht => (htail t ht).le) hz
    obtain ⟨c, hc, heq⟩ := exists_hasDerivAt_eq_slope
      (backwardDifferences hs (F k)) (backwardDifferences hs (F (k + 1)))
      (by linarith : x < x + h)
      (fun z hz => (hd z (by have := hz.1; linarith)).continuousAt.continuousWithinAt)
      (fun z hz => hd z (by have := hz.1; linarith))
    obtain ⟨y, hcy, hy, hval⟩ := ih htail (k + 1) (by have := hc.1; linarith : 0 < c)
    refine ⟨y, hc.1.le.trans hcy, ?_, ?_⟩
    · simp only [List.sum_cons]
      linarith [hc.2]
    · have hslope : backwardDifferences hs (F k) (x + h) -
          backwardDifferences hs (F k) x =
          h * backwardDifferences hs (F (k + 1)) c := by
        apply (eq_div_iff (by linarith : x + h - x ≠ 0)).mp at heq
        nlinarith [heq]
      simp only [backwardDifferences, List.length_cons, List.prod_cons, pow_succ]
      rw [show k + (hs.length + 1) = k + 1 + hs.length by omega]
      rw [hval] at hslope
      linear_combination -hslope

/-- Page 21. The derivatives of minus log on the positive half line. -/
noncomputable def logJet : ℕ → ℝ → ℝ
  | 0, x => -Real.log x
  | n + 1, x => (-1 : ℝ) ^ (n + 1) * n.factorial * x ^ (-((n + 1 : ℕ) : ℤ))

/-- Page 21. The explicit logarithmic derivative sequence differentiates to its next term. -/
theorem logJet_hasDerivAt (k : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (logJet k) (logJet (k + 1) x) x := by
  cases k with
  | zero =>
    have hf : logJet 0 = -Real.log := by funext z; rfl
    have hv : logJet (0 + 1) x = -x⁻¹ := by norm_num [logJet]
    rw [hf, hv]
    exact (Real.hasDerivAt_log hx.ne').neg
  | succ n =>
    have hd := (hasDerivAt_zpow (-((n + 1 : ℕ) : ℤ)) x (Or.inl hx.ne')).const_mul
      ((-1 : ℝ) ^ (n + 1) * n.factorial)
    have hf : logJet (n + 1) = fun z : ℝ =>
        (-1 : ℝ) ^ (n + 1) * n.factorial * z ^ (-((n + 1 : ℕ) : ℤ)) := by
      funext z; rfl
    rw [hf]
    convert hd using 1
    simp only [logJet, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      pow_succ, Int.cast_neg, Int.cast_natCast]
    rw [show -((n : ℤ) + 1) - 1 = -((n : ℤ) + 1 + 1) by ring]
    push_cast
    ring

/-- Page 21. A positive order logarithmic derivative is a signed factorial divided by a power. -/
theorem logJet_succ (k : ℕ) (x : ℝ) :
    logJet (k + 1) x = (-1 : ℝ) ^ (k + 1) * k.factorial / x ^ (k + 1) := by
  change (-1 : ℝ) ^ (k + 1) * k.factorial * x ^ (-((k + 1 : ℕ) : ℤ)) = _
  rw [zpow_neg, zpow_natCast, div_eq_mul_inv]

/-- Page 21. Every positive iterated difference of minus log is a positive factorial kernel. -/
theorem log_backwardDifferences_meanValue (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 < h) {k : ℕ} (hlen : hs.length = k + 1)
    {x : ℝ} (hx : 0 < x) :
    ∃ y : ℝ, x ≤ y ∧ y ≤ x + hs.sum ∧
      backwardDifferences hs (fun z => -Real.log z) x =
        hs.prod * k.factorial / y ^ (k + 1) := by
  obtain ⟨y, hy, hy', heq⟩ := backwardDifferences_meanValue logJet
    (fun k _ hx => logJet_hasDerivAt k hx) hs hhs 0 hx
  refine ⟨y, hy, hy', ?_⟩
  simp only [Nat.zero_add, hlen, logJet_succ] at heq
  change backwardDifferences hs (logJet 0) x = _
  rw [heq]
  have hsign : (-1 : ℝ) ^ (k + 1) * (-1 : ℝ) ^ (k + 1) = 1 := by
    rw [← mul_pow]; norm_num
  calc
    _ = ((-1 : ℝ) ^ (k + 1) * (-1 : ℝ) ^ (k + 1)) *
        (hs.prod * k.factorial / y ^ (k + 1)) := by ring
    _ = _ := by rw [hsign, one_mul]

/-- Page 21. Bounds for the positive logarithmic finite difference kernel. -/
theorem log_backwardDifferences_bounds (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 < h) {k : ℕ} (hlen : hs.length = k + 1)
    {x N M : ℝ} (hN : 0 < N) (hNx : N ≤ x) (hM : x + hs.sum ≤ M) :
    hs.prod * k.factorial / M ^ (k + 1) ≤
      backwardDifferences hs (fun z => -Real.log z) x ∧
    backwardDifferences hs (fun z => -Real.log z) x ≤
      hs.prod * k.factorial / N ^ (k + 1) := by
  obtain ⟨y, hy, hy', heq⟩ := log_backwardDifferences_meanValue hs hhs hlen (hN.trans_le hNx)
  rw [heq]
  have hy0 : 0 < y := hN.trans_le (hNx.trans hy)
  have hnum : 0 ≤ hs.prod * (k.factorial : ℝ) :=
    mul_nonneg (List.prod_pos hhs).le (Nat.cast_nonneg _)
  exact ⟨div_le_div_of_nonneg_left hnum (pow_pos hy0 _) (pow_le_pow_left₀ hy0.le (hy'.trans hM) _),
    div_le_div_of_nonneg_left hnum (pow_pos hN _) (pow_le_pow_left₀ hN.le (hNx.trans hy) _)⟩

/-- Page 21. Iterated differences commute with affine changes of variable. -/
theorem backwardDifferences_affine (hs : List ℝ) (f : ℝ → ℝ) (q r x : ℝ) :
    backwardDifferences hs (fun z => f (q * z + r)) x =
      backwardDifferences (hs.map (q * ·)) f (q * x + r) := by
  induction hs generalizing x with
  | nil => rfl
  | cons h hs ih =>
    simp only [backwardDifferences, List.map_cons, ih]
    congr 2
    ring

/-- Page 21. A constant scalar factors out of all differences. -/
theorem backwardDifferences_const_mul (hs : List ℝ) (f : ℝ → ℝ) (c x : ℝ) :
    backwardDifferences hs (fun z => c * f z) x = c * backwardDifferences hs f x := by
  induction hs generalizing x with
  | nil => rfl
  | cons h hs ih => simp only [backwardDifferences, ih]; ring

/-- Page 21. The discrete second derivative is two more backward differences. -/
theorem second_difference_eq (hs : List ℝ) (f : ℝ → ℝ) (x : ℝ) :
    (backwardDifferences hs f (x + 1 + 1) - backwardDifferences hs f (x + 1)) -
      (backwardDifferences hs f (x + 1) - backwardDifferences hs f x) =
        backwardDifferences (1 :: 1 :: hs) f x := by
  simp only [backwardDifferences]
  ring

/-- Page 21. Explicit bounds for the second differences of each differenced logarithmic phase. -/
theorem log_phase_second_difference_bounds (hs : List ℝ)
    (hhs : ∀ h ∈ hs, 0 < h) {a t r x N M : ℝ}
    (ha : 0 < a) (ht : 0 ≤ t) (hN : 0 < N) (hNx : N ≤ a * x + r)
    (hM : a * (x + 2 + hs.sum) + r ≤ M) :
    let g := backwardDifferences hs (fun z => t * (-Real.log (a * z + r)))
    let P := ((1 :: 1 :: hs).map (a * ·)).prod * (hs.length + 1).factorial
    t * P / M ^ (hs.length + 2) ≤ (g (x + 1 + 1) - g (x + 1)) - (g (x + 1) - g x) ∧
    (g (x + 1 + 1) - g (x + 1)) - (g (x + 1) - g x) ≤ t * P / N ^ (hs.length + 2) := by
  dsimp only
  rw [second_difference_eq, backwardDifferences_const_mul,
    backwardDifferences_affine (1 :: 1 :: hs) (fun z => -Real.log z) a r x]
  have hpos : ∀ h ∈ (1 :: 1 :: hs).map (a * ·), 0 < h := by
    intro h hh
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hh
    apply mul_pos ha
    rcases List.mem_cons.mp hz with rfl | hz
    · norm_num
    rcases List.mem_cons.mp hz with rfl | hz
    · norm_num
    exact hhs z hz
  have hlen : ((1 :: 1 :: hs).map (a * ·)).length = (hs.length + 1) + 1 := by simp
  have hupper : a * x + r + ((1 :: 1 :: hs).map (a * ·)).sum ≤ M := by
    have hsum : (hs.map (a * ·)).sum = a * hs.sum := by
      simpa using (List.sum_map_mul_left (l := hs) (r := a) (f := id))
    simp only [List.map_cons, List.sum_cons, mul_one]
    rw [hsum]
    nlinarith [hM]
  have hb := log_backwardDifferences_bounds _ hpos hlen hN hNx hupper
  have hlo := mul_le_mul_of_nonneg_left hb.1 ht
  have hhi := mul_le_mul_of_nonneg_left hb.2 ht
  simpa only [mul_div_assoc, mul_assoc, Nat.add_assoc] using And.intro hlo hhi

#print axioms log_phase_second_difference_bounds
#print axioms log_backwardDifferences_bounds
#print axioms backwardDifferences_affine
#print axioms backwardDifferences_const_mul
#print axioms second_difference_eq
#print axioms logJet_hasDerivAt
#print axioms logJet_succ
#print axioms log_backwardDifferences_meanValue
#print axioms backwardDifferences_hasDerivAt
#print axioms backwardDifferences_meanValue
end LeanLab.BakerHarmanPintz1997.LogPhase219
