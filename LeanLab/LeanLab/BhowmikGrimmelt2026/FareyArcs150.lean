/-
ROUTE BURST 5, 20261112. The Farey counting behind the arc tails of P0029, Bhowmik and Grimmelt
2026, page 12: the `O(N^{1/2+ε})` in the contribution of the arc around `a/q`, in the pointwise
form `|V(α)² - W(α)| ≪ X^{1+ε}` for the model `V = VX150 X` of MeanSquareCore150.lean and the
full model `W = WX150 X` of Coefficients150.lean.

The survey states the bound without proof. The proof here is the standard one:

* the kernel bound `|T(y)| ≤ 1/(2|y|)` for `|y| ≤ 1/2`, from the geometric sum and Jordan's
  inequality, and `|T| ≤ X`;
* Dirichlet's theorem: every `α` lies on some arc `arcSet150 X q0` with `q0 ≤ Q = ⌊X^{1/2}⌋`,
  and minimality of `q0` makes `a0/q0` reduced;
* then `V² - W` is minus the sum over the other pairs `(q, a)`, and each such fraction differs
  from `a0/q0` by `h/(q q0)` with `h ≠ 0`;
* pairs with `|h| ≥ 2` or `2q ≤ Q` contribute `≪ (q/φ(q))² q0²/h²`, and for fixed `h` the `q`
  lie in one residue class modulo `q0`; pairs with `|h| = 1` and `2q > Q` are Farey neighbours
  of `a0/q0`, spaced at least `1/Q²` apart, and the kernel sums over spaced points.

Copies, said plainly: `le_totient_mul_card_divisors_f150` and `totient_rpow_bound_f150` are
verbatim copies of the private lemmas `le_totient_mul_card_divisors_m150` and
`totient_rpow_bound_m150` of ModelL2_150.lean, themselves copies from SingularTail150.lean,
which cannot be used from here because they are private.  The kernel bound adapts
`kernel_far` and `two_abs_le_abs_sin` of PerelliPintz1992/Kernel.lean to `ee` and `TX150`.

AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.BhowmikGrimmelt2026.ArcTails150

namespace LeanLab.BhowmikGrimmelt2026

open ArithmeticFunction

/-! ### The kernel `T` -/

theorem ee_int_f150 (m : ℤ) : ee (m : ℝ) = 1 := by
  unfold ee
  rw [show 2 * (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ) = (m : ℂ) * (2 * Real.pi * Complex.I) by
    push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I m

/-- `T` has period `1`. PROVED. -/
theorem TX_sub_int_f150 (X : ℕ) (β : ℝ) (m : ℤ) : TX150 X (β - m) = TX150 X β := by
  unfold TX150
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [show (n : ℝ) * (β - m) = (n : ℝ) * β + ((-(n * m) : ℤ) : ℝ) by push_cast; ring,
    ee_add150, ee_int_f150, mul_one]

theorem ee_nat_mul_f150 (n : ℕ) (y : ℝ) : ee ((n : ℝ) * y) = ee y ^ n := by
  unfold ee
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem norm_ee_sub_one_f150 (y : ℝ) : ‖ee y - 1‖ = 2 * |Real.sin (Real.pi * y)| := by
  unfold ee
  rw [show (2 * Real.pi * Complex.I * y : ℂ) = Complex.I * ((2 * Real.pi * y : ℝ) : ℂ) by
    push_cast; ring, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs,
    Real.norm_eq_abs]
  rw [show 2 * Real.pi * y / 2 = Real.pi * y by ring]
  norm_num

/-- Jordan: `2 |t| ≤ |sin(π t)|` for `|t| ≤ 1/2`. Copy of `two_abs_le_abs_sin` of
PerelliPintz1992/Kernel.lean. PROVED. -/
theorem two_abs_le_abs_sin_f150 {t : ℝ} (ht : |t| ≤ 1 / 2) :
    2 * |t| ≤ |Real.sin (Real.pi * t)| := by
  have h0 : 0 ≤ Real.pi * |t| := mul_nonneg Real.pi_pos.le (abs_nonneg t)
  have h1 : Real.pi * |t| ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
  have hj := Real.mul_le_sin h0 h1
  have e1 : 2 / Real.pi * (Real.pi * |t|) = 2 * |t| := by field_simp
  rw [e1] at hj
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h] at hj ⊢
    exact hj.trans (le_abs_self _)
  · rw [abs_of_nonpos h] at hj ⊢
    have : Real.sin (Real.pi * -t) = - Real.sin (Real.pi * t) := by rw [mul_neg, Real.sin_neg]
    rw [this] at hj
    exact hj.trans (neg_le_abs _)

/-- The kernel bound `|T(y)| ≤ 1/(2|y|)` for `|y| ≤ 1/2`, in the form `4 y² |T(y)|² ≤ 1`.
PROVED. -/
theorem kernel_TX_f150 (X : ℕ) {y : ℝ} (hy : |y| ≤ 1 / 2) :
    4 * y ^ 2 * ‖TX150 X y‖ ^ 2 ≤ 1 := by
  set r : ℂ := ee y with hr
  have hgeom : TX150 X y * (r - 1) = r ^ (X + 1) - r ^ 1 := by
    have e : TX150 X y = ∑ i ∈ Finset.Ico 1 (X + 1), r ^ i := by
      unfold TX150
      have : Finset.Icc 1 X = Finset.Ico 1 (X + 1) := by ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
      rw [this]
      exact Finset.sum_congr rfl fun n _ => ee_nat_mul_f150 n y
    rw [e]
    exact geom_sum_Ico_mul r (by omega)
  have hnum : ‖r ^ (X + 1) - r ^ 1‖ ≤ 2 := by
    calc ‖r ^ (X + 1) - r ^ 1‖ ≤ ‖r ^ (X + 1)‖ + ‖r ^ 1‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_pow, hr, norm_ee150, one_pow, one_pow]; norm_num
  have hprod : ‖TX150 X y‖ * (2 * |Real.sin (Real.pi * y)|) ≤ 2 := by
    rw [← norm_ee_sub_one_f150, ← hr, ← norm_mul, hgeom]; exact hnum
  have hj := two_abs_le_abs_sin_f150 hy
  have hT0 := norm_nonneg (TX150 X y)
  have h1 : ‖TX150 X y‖ * (2 * |y|) ≤ 1 := by nlinarith [abs_nonneg y]
  have h2 : 0 ≤ ‖TX150 X y‖ * (2 * |y|) := by positivity
  have h3 : (‖TX150 X y‖ * (2 * |y|)) ^ 2 ≤ 1 := by nlinarith
  calc 4 * y ^ 2 * ‖TX150 X y‖ ^ 2 = (‖TX150 X y‖ * (2 * |y|)) ^ 2 := by
        rw [mul_pow, mul_pow, sq_abs]; ring
    _ ≤ 1 := h3

/-! ### The nearest integer -/

theorem abs_sub_nint_le_half_f150 (x : ℝ) : |x - nint150 x| ≤ 1 / 2 := by
  unfold nint150
  have h1 := Int.floor_le (x + 1 / 2)
  have h2 := Int.lt_floor_add_one (x + 1 / 2)
  rw [abs_le]; constructor <;> linarith

/-- `nint150` is a nearest integer. PROVED. -/
theorem abs_sub_nint_le_f150 (x : ℝ) (j : ℤ) : |x - nint150 x| ≤ |x - j| := by
  have hh := abs_sub_nint_le_half_f150 x
  rcases lt_trichotomy j (nint150 x) with hj | hj | hj
  · have hj' : (j : ℝ) + 1 ≤ nint150 x := by exact_mod_cast hj
    have : nint150 x ≤ x + 1 / 2 := by unfold nint150; exact Int.floor_le _
    rw [abs_le] at hh
    rw [abs_of_pos (by linarith : (0 : ℝ) < x - j)]
    rw [abs_le]; constructor <;> linarith
  · rw [hj]
  · have hj' : (nint150 x : ℝ) + 1 ≤ j := by exact_mod_cast hj
    have : x + 1 / 2 < nint150 x + 1 := by unfold nint150; exact Int.lt_floor_add_one _
    rw [abs_of_neg (by linarith : x - j < 0)]
    rw [abs_le]; constructor <;> linarith

/-! ### Sums over spaced points -/

/-- A sum over points `f i ≥ 0` spaced at least `d` apart of values `v i ≤ M` with
`v i f(i)² ≤ c`: at most `M + 2c/d²`. PROVED. -/
theorem sum_spaced_nonneg_f150 {ι : Type*} (s : Finset ι) (f v : ι → ℝ) {d M c : ℝ}
    (hd : 0 < d) (hM : 0 ≤ M) (hc : 0 ≤ c) (hf : ∀ i ∈ s, 0 ≤ f i)
    (hsp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → d ≤ |f i - f j|)
    (hvM : ∀ i ∈ s, v i ≤ M) (hvc : ∀ i ∈ s, f i ≠ 0 → v i * f i ^ 2 ≤ c) :
    ∑ i ∈ s, v i ≤ M + 2 * c / d ^ 2 := by
  set k : ι → ℕ := fun i => ⌊f i / d⌋₊ with hk
  set G : ℕ → ℝ := fun n => if n = 0 then M else c / d ^ 2 * ((n : ℝ) ^ 2)⁻¹ with hG
  have hG0 : ∀ n, 0 ≤ G n := by
    intro n; simp only [hG]; split_ifs <;> positivity
  have hinj : Set.InjOn k s := by
    intro i hi j hj hij
    by_contra hne
    have h1 := hsp i hi j hj hne
    have hi0 : 0 ≤ f i / d := div_nonneg (hf i hi) hd.le
    have hj0 : 0 ≤ f j / d := div_nonneg (hf j hj) hd.le
    have a1 := Nat.floor_le hi0
    have a2 := Nat.lt_floor_add_one (f i / d)
    have a3 := Nat.floor_le hj0
    have a4 := Nat.lt_floor_add_one (f j / d)
    simp only [hk] at hij
    rw [hij] at a1 a2
    have hlt : |f i / d - f j / d| < 1 := by rw [abs_lt]; constructor <;> linarith
    rw [← sub_div, abs_div, abs_of_pos hd, div_lt_one hd] at hlt
    linarith
  have hvG : ∀ i ∈ s, v i ≤ G (k i) := by
    intro i hi
    simp only [hG]
    split_ifs with h0
    · exact hvM i hi
    · have hk1 : (1 : ℝ) ≤ (k i : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr h0
      have hfl : (k i : ℝ) ≤ f i / d := Nat.floor_le (div_nonneg (hf i hi) hd.le)
      have hkd : (k i : ℝ) * d ≤ f i := by rwa [le_div_iff₀ hd] at hfl
      have hfpos : 0 < f i := by nlinarith
      have hv := hvc i hi hfpos.ne'
      have hv' : v i ≤ c / f i ^ 2 := by rw [le_div_iff₀ (by positivity)]; exact hv
      have hsq : ((k i : ℝ) * d) ^ 2 ≤ f i ^ 2 := pow_le_pow_left₀ (by positivity) hkd 2
      calc v i ≤ c / f i ^ 2 := hv'
        _ ≤ c / ((k i : ℝ) * d) ^ 2 := div_le_div_of_nonneg_left hc (by positivity) hsq
        _ = c / d ^ 2 * ((k i : ℝ) ^ 2)⁻¹ := by field_simp
  set T := s.image k with hT
  have hsum1 : ∑ i ∈ s, v i ≤ ∑ n ∈ T, G n := by
    rw [hT, Finset.sum_image hinj]
    exact Finset.sum_le_sum hvG
  rw [← Finset.sum_filter_add_sum_filter_not T (fun n => n = 0)] at hsum1
  have hA : ∑ n ∈ T.filter (fun n => n = 0), G n ≤ M := by
    calc ∑ n ∈ T.filter (fun n => n = 0), G n ≤ ∑ n ∈ ({0} : Finset ℕ), G n := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => hG0 n)
          intro n hn; simp only [Finset.mem_filter] at hn; simp [hn.2]
      _ = M := by simp [hG]
  set N := T.sup id with hN
  have hB : ∑ n ∈ T.filter (fun n => ¬ n = 0), G n ≤ 2 * c / d ^ 2 := by
    calc ∑ n ∈ T.filter (fun n => ¬ n = 0), G n
        = ∑ n ∈ T.filter (fun n => ¬ n = 0), c / d ^ 2 * ((n : ℝ) ^ 2)⁻¹ := by
          refine Finset.sum_congr rfl fun n hn => ?_
          simp only [Finset.mem_filter] at hn
          simp [hG, hn.2]
      _ ≤ ∑ n ∈ Finset.Ioo 0 (N + 1), c / d ^ 2 * ((n : ℝ) ^ 2)⁻¹ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => by positivity)
          intro n hn
          simp only [Finset.mem_filter] at hn
          have : n ≤ N := Finset.le_sup (f := id) hn.1
          simp only [Finset.mem_Ioo]; omega
      _ = c / d ^ 2 * ∑ n ∈ Finset.Ioo 0 (N + 1), ((n : ℝ) ^ 2)⁻¹ := by rw [Finset.mul_sum]
      _ ≤ c / d ^ 2 * (2 / ((0 : ℕ) + 1)) :=
          mul_le_mul_of_nonneg_left (sum_Ioo_inv_sq_le 0 (N + 1)) (by positivity)
      _ = 2 * c / d ^ 2 := by push_cast; ring
  linarith

/-- The two sided form: `Σ v ≤ 2M + 4c/d²` for points spaced at least `d` apart. PROVED. -/
theorem sum_spaced_f150 {ι : Type*} (s : Finset ι) (f v : ι → ℝ) {d M c : ℝ}
    (hd : 0 < d) (hM : 0 ≤ M) (hc : 0 ≤ c)
    (hsp : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → d ≤ |f i - f j|)
    (hvM : ∀ i ∈ s, v i ≤ M) (hvc : ∀ i ∈ s, f i ≠ 0 → v i * f i ^ 2 ≤ c) :
    ∑ i ∈ s, v i ≤ 2 * M + 4 * c / d ^ 2 := by
  rw [← Finset.sum_filter_add_sum_filter_not s (fun i => 0 ≤ f i)]
  have h1 := sum_spaced_nonneg_f150 (s.filter (fun i => 0 ≤ f i)) f v hd hM hc
    (fun i hi => (Finset.mem_filter.mp hi).2)
    (fun i hi j hj hij => hsp i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hij)
    (fun i hi => hvM i (Finset.mem_filter.mp hi).1)
    (fun i hi => hvc i (Finset.mem_filter.mp hi).1)
  have h2 := sum_spaced_nonneg_f150 (s.filter (fun i => ¬ 0 ≤ f i)) (fun i => - f i) v hd hM hc
    (fun i hi => by have := (Finset.mem_filter.mp hi).2; show 0 ≤ -f i; linarith)
    (fun i hi j hj hij => by
      have := hsp i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hij
      show d ≤ |-f i - -f j|
      rwa [show -f i - -f j = -(f i - f j) by ring, abs_neg])
    (fun i hi => hvM i (Finset.mem_filter.mp hi).1)
    (fun i hi hne => by
      have := hvc i (Finset.mem_filter.mp hi).1 (fun h => hne (by simp [h]))
      simpa using this)
  have e : 2 * M + 4 * c / d ^ 2 = (M + 2 * c / d ^ 2) + (M + 2 * c / d ^ 2) := by ring
  rw [e]
  exact add_le_add h1 h2

/-- `Σ_{h ∈ s} 1/h² ≤ 6` over any finite set of integers, `1/0 = 0`. PROVED. -/
theorem sum_inv_sq_int_f150 (s : Finset ℤ) : ∑ h ∈ s, ((h : ℝ) ^ 2)⁻¹ ≤ 6 := by
  have := sum_spaced_f150 s (fun h => (h : ℝ)) (fun h => ((h : ℝ) ^ 2)⁻¹)
    (d := 1) (M := 1) (c := 1) one_pos zero_le_one zero_le_one
    (fun i _ j _ hij => by
      have : (1 : ℤ) ≤ |i - j| := Int.one_le_abs (sub_ne_zero.mpr hij)
      show (1 : ℝ) ≤ |(i : ℝ) - j|; exact_mod_cast this)
    (fun i _ => by
      rcases eq_or_ne i 0 with h | h
      · simp [h]
      · have : (1 : ℝ) ≤ (i : ℝ) ^ 2 := by
          have h1 : (1 : ℤ) ≤ i ^ 2 := by nlinarith [Int.one_le_abs h, sq_abs i]
          exact_mod_cast h1
        exact inv_le_one_of_one_le₀ this)
    (fun i _ hne => by rw [inv_mul_cancel₀ (pow_ne_zero 2 hne)])
  linarith

/-! ### Counting in a residue class -/

/-- Integers `q ∈ [1, Q]` with `q0 ∣ a0 q - h`, `(a0, q0) = 1`, lie in one residue class modulo
`q0`, so there are at most `Q/q0 + 1` of them. PROVED. -/
theorem card_filter_dvd_f150 (Q q0 : ℕ) (a0 h : ℤ) (hcop : IsCoprime a0 (q0 : ℤ)) :
    ((Finset.Icc 1 Q).filter (fun q : ℕ => (q0 : ℤ) ∣ a0 * q - h)).card ≤ Q / q0 + 1 := by
  calc ((Finset.Icc 1 Q).filter (fun q : ℕ => (q0 : ℤ) ∣ a0 * q - h)).card
      ≤ (Finset.range (Q / q0 + 1)).card := by
        refine Finset.card_le_card_of_injOn (fun q => q / q0) ?_ ?_
        · intro q hq
          simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hq
          simp only [Finset.coe_range, Set.mem_Iio]
          exact Nat.lt_succ_of_le (Nat.div_le_div_right hq.1.2)
        · intro q1 h1 q2 h2 heq
          simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at h1 h2
          have hd : (q0 : ℤ) ∣ a0 * ((q1 : ℤ) - q2) := by
            have := dvd_sub h1.2 h2.2
            rwa [show a0 * (q1 : ℤ) - h - (a0 * q2 - h) = a0 * ((q1 : ℤ) - q2) by ring] at this
          have hd2 : (q0 : ℤ) ∣ (q1 : ℤ) - q2 := hcop.symm.dvd_of_dvd_mul_left hd
          have hmod : q2 ≡ q1 [MOD q0] := Nat.modEq_iff_dvd.mpr hd2
          · have e1 := Nat.div_add_mod q1 q0
            have e2 := Nat.div_add_mod q2 q0
            simp only at heq
            rw [heq] at e1
            have : q1 % q0 = q2 % q0 := hmod.symm
            omega
    _ = Q / q0 + 1 := Finset.card_range _

/-- Swapping the sum over pairs `(q, a)` to a sum over `h = H q a`: for fixed `q` the map
`a ↦ H q a` is injective and `q0 ∣ a0 q - H q a`, so each `h` is hit by at most `Q/q0 + 1`
denominators `q`. PROVED. -/
theorem sum_swap_f150 (Q q0 : ℕ) (a0 : ℤ) (hcop : IsCoprime a0 (q0 : ℤ)) (A : ℕ → Finset ℕ)
    (H : ℕ → ℕ → ℤ) (hinj : ∀ q ∈ Finset.Icc 1 Q, Set.InjOn (H q) (A q))
    (hdvd : ∀ q ∈ Finset.Icc 1 Q, ∀ a ∈ A q, (q0 : ℤ) ∣ a0 * q - H q a)
    (g : ℤ → ℝ) (hg : ∀ h, 0 ≤ g h) :
    ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ A q, g (H q a) ≤
      (((Q / q0 : ℕ) : ℝ) + 1) *
        ∑ h ∈ (Finset.Icc 1 Q).biUnion (fun q => (A q).image (H q)), g h := by
  set HS := (Finset.Icc 1 Q).biUnion (fun q => (A q).image (H q)) with hHS
  have step1 : ∀ q ∈ Finset.Icc 1 Q, ∑ a ∈ A q, g (H q a) ≤
      ∑ h ∈ HS, if (q0 : ℤ) ∣ a0 * q - h then g h else 0 := by
    intro q hq
    rw [← Finset.sum_image (hinj q hq), ← Finset.sum_filter]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun h _ _ => hg h)
    intro h hh
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hh
    refine Finset.mem_filter.mpr ⟨?_, hdvd q hq a ha⟩
    exact Finset.mem_biUnion.mpr ⟨q, hq, Finset.mem_image_of_mem _ ha⟩
  calc ∑ q ∈ Finset.Icc 1 Q, ∑ a ∈ A q, g (H q a)
      ≤ ∑ q ∈ Finset.Icc 1 Q, ∑ h ∈ HS, if (q0 : ℤ) ∣ a0 * q - h then g h else 0 :=
        Finset.sum_le_sum step1
    _ = ∑ h ∈ HS, ∑ q ∈ Finset.Icc 1 Q, if (q0 : ℤ) ∣ a0 * q - h then g h else 0 :=
        Finset.sum_comm
    _ = ∑ h ∈ HS, (((Finset.Icc 1 Q).filter (fun q : ℕ => (q0 : ℤ) ∣ a0 * q - h)).card : ℝ) *
          g h := by
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ h ∈ HS, (((Q / q0 : ℕ) : ℝ) + 1) * g h := by
        refine Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_right ?_ (hg h)
        exact_mod_cast card_filter_dvd_f150 Q q0 a0 h hcop
    _ = (((Q / q0 : ℕ) : ℝ) + 1) * ∑ h ∈ HS, g h := by rw [Finset.mul_sum]

/-! ### Dirichlet's theorem and the reduced centre -/

/-- Dirichlet: the arcs `arcSet150 X q`, `1 ≤ q ≤ Q`, cover `ℝ`. PROVED. -/
theorem exists_arc_f150 (X : ℕ) (hX : 1 ≤ X) (α : ℝ) :
    ∃ q0 ∈ Finset.Icc 1 (Nat.sqrt X), α ∈ arcSet150 X q0 := by
  classical
  set Q := Nat.sqrt X with hQ
  have hQ1 : 1 ≤ Q := Nat.le_sqrt.mpr (by simpa using hX)
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1
  obtain ⟨k, hk0, hkQ, hb⟩ := Real.exists_nat_abs_mul_sub_round_le α (n := Q) (by omega)
  have hP : ∃ k : ℕ, 1 ≤ k ∧ |(k : ℝ) * α - nint150 ((k : ℝ) * α)| ≤ 1 / (Q : ℝ) := by
    refine ⟨k, hk0, ?_⟩
    calc |(k : ℝ) * α - nint150 ((k : ℝ) * α)| ≤ |(k : ℝ) * α - round ((k : ℝ) * α)| :=
          abs_sub_nint_le_f150 _ _
      _ ≤ 1 / ((Q : ℝ) + 1) := hb
      _ ≤ 1 / (Q : ℝ) := one_div_le_one_div_of_le (by linarith) (by linarith)
  have hs := Nat.find_spec hP
  have hle : Nat.find hP ≤ k := Nat.find_min' hP ⟨hk0, by
    calc |(k : ℝ) * α - nint150 ((k : ℝ) * α)| ≤ |(k : ℝ) * α - round ((k : ℝ) * α)| :=
          abs_sub_nint_le_f150 _ _
      _ ≤ 1 / ((Q : ℝ) + 1) := hb
      _ ≤ 1 / (Q : ℝ) := one_div_le_one_div_of_le (by linarith) (by linarith)⟩
  refine ⟨Nat.find hP, Finset.mem_Icc.mpr ⟨hs.1, by omega⟩, ?_⟩
  simp only [arcSet150, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter]
  refine ⟨hs.2, fun j hj => ?_⟩
  obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
  have hmin := Nat.find_min hP hj2
  push Not at hmin
  exact hmin hj1

/-- Minimality of `q0` makes the centre `a0/q0`, `a0 = nint(q0 α)`, reduced. PROVED. -/
theorem isCoprime_nint_f150 (X q0 : ℕ) (hq0 : 1 ≤ q0) {α : ℝ} (hα : α ∈ arcSet150 X q0) :
    IsCoprime (nint150 ((q0 : ℝ) * α)) (q0 : ℤ) := by
  simp only [arcSet150, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iInter] at hα
  obtain ⟨hα1, hα2⟩ := hα
  set a0 := nint150 ((q0 : ℝ) * α) with ha0
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hne
  set d := Int.gcd a0 (q0 : ℤ) with hd
  have hdpos : 0 < d := Int.gcd_pos_of_ne_zero_right _ (by exact_mod_cast (by omega : q0 ≠ 0))
  have hd2 : 2 ≤ d := by omega
  have hdq : d ∣ q0 := by
    have := Int.gcd_dvd_right a0 (q0 : ℤ)
    exact_mod_cast this
  obtain ⟨k, hk⟩ := hdq
  obtain ⟨b, hb⟩ := Int.gcd_dvd_left a0 (q0 : ℤ)
  rw [← hd] at hb
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · rw [h] at hk; omega
    · exact h
  have hkq : k < q0 := by
    rw [hk]; nlinarith
  have hc := hα2 k (Finset.mem_Ico.mpr ⟨hk1, hkq⟩)
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd2
  have hq0R : (q0 : ℝ) = d * k := by exact_mod_cast hk
  have ha0R : (a0 : ℝ) = d * b := by exact_mod_cast hb
  have e : (k : ℝ) * α - b = ((q0 : ℝ) * α - a0) / d := by
    rw [hq0R, ha0R]; field_simp
  have h1 : |(k : ℝ) * α - nint150 ((k : ℝ) * α)| ≤ |(k : ℝ) * α - b| := abs_sub_nint_le_f150 _ _
  have h2 : |(k : ℝ) * α - b| ≤ |(q0 : ℝ) * α - a0| := by
    rw [e, abs_div, abs_of_pos (by linarith : (0 : ℝ) < d)]
    exact div_le_self (abs_nonneg _) (by linarith)
  linarith

/-! ### The pairs `(q, a)` relative to the centre `a0/q0` -/

/-- The representative `a' ≡ a mod q` with `α - a'/q ∈ [-1/2, 1/2]`.  Proof helper for the arc
tails of P0029 page 12, the fractions `a/q` of the Farey dissection of page 11 seen from `α`. -/
noncomputable def aRep150 (α : ℝ) (q a : ℕ) : ℤ := (a : ℤ) + q * nint150 (α - (a : ℝ) / q)

/-- `y = α - a'/q`, the signed distance from `α` to the fraction `a/q` modulo `1`, the argument
`α - a/q` of the main term of P0029 display 3.5, page 11. -/
noncomputable def yRep150 (α : ℝ) (q a : ℕ) : ℝ := α - (aRep150 α q a : ℝ) / q

/-- `h = a0 q - a' q0`, so that `a0/q0 - a'/q = h/(q q0)`, `a0 = nint(q0 α)`: the Farey spacing
numerator between two fractions of the dissection of P0029 page 11. -/
noncomputable def hRep150 (α : ℝ) (q0 q a : ℕ) : ℤ :=
  nint150 ((q0 : ℝ) * α) * q - aRep150 α q a * q0

theorem TX_yRep150 (X : ℕ) (α : ℝ) {q : ℕ} (hq : 1 ≤ q) (a : ℕ) :
    TX150 X (α - (a : ℝ) / q) = TX150 X (yRep150 α q a) := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have e : yRep150 α q a = (α - (a : ℝ) / q) - (nint150 (α - (a : ℝ) / q) : ℝ) := by
    unfold yRep150 aRep150; push_cast; field_simp; ring
  rw [e, TX_sub_int_f150]

theorem abs_yRep_le150 (α : ℝ) {q : ℕ} (hq : 1 ≤ q) (a : ℕ) : |yRep150 α q a| ≤ 1 / 2 := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  have e : yRep150 α q a = (α - (a : ℝ) / q) - (nint150 (α - (a : ℝ) / q) : ℝ) := by
    unfold yRep150 aRep150; push_cast; field_simp; ring
  rw [e]; exact abs_sub_nint_le_half_f150 _

theorem yRep_mul150 (α : ℝ) {q : ℕ} (hq : 1 ≤ q) (q0 a : ℕ) :
    yRep150 α q a * ((q : ℝ) * q0) =
      (q : ℝ) * ((q0 : ℝ) * α - nint150 ((q0 : ℝ) * α)) + (hRep150 α q0 q a : ℝ) := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  unfold yRep150 hRep150; push_cast; field_simp; ring

theorem dvd_hRep150 (α : ℝ) (q0 q a : ℕ) :
    (q0 : ℤ) ∣ nint150 ((q0 : ℝ) * α) * q - hRep150 α q0 q a := by
  unfold hRep150
  exact ⟨aRep150 α q a, by ring⟩

/-- For fixed `q`, distinct residues `a < q` give distinct `h`. PROVED. -/
theorem hRep_injOn150 (α : ℝ) {q0 q : ℕ} (hq0 : 1 ≤ q0) :
    Set.InjOn (hRep150 α q0 q) (Finset.range q : Set ℕ) := by
  intro a1 h1 a2 h2 heq
  simp only [Finset.coe_range, Set.mem_Iio] at h1 h2
  unfold hRep150 at heq
  have hq0Z : (q0 : ℤ) ≠ 0 := by exact_mod_cast (by omega : q0 ≠ 0)
  have e1 : aRep150 α q a1 = aRep150 α q a2 := by
    have : aRep150 α q a1 * q0 = aRep150 α q a2 * q0 := by linarith
    exact mul_right_cancel₀ hq0Z this
  unfold aRep150 at e1
  have m1 : ((a1 : ℤ) + q * nint150 (α - (a1 : ℝ) / q)) % q = a1 := by
    rw [Int.add_mul_emod_self_left]; exact Int.emod_eq_of_lt (by omega) (by omega)
  have m2 : ((a2 : ℤ) + q * nint150 (α - (a2 : ℝ) / q)) % q = a2 := by
    rw [Int.add_mul_emod_self_left]; exact Int.emod_eq_of_lt (by omega) (by omega)
  rw [e1] at m1
  rw [m1] at m2
  exact_mod_cast m2

/-- The excluded residue: `r0 = a0 mod q0`, the numerator of the arc centre `a0/q0` of `α` in the
dissection of P0029 page 11. -/
noncomputable def r0Rep150 (α : ℝ) (q0 : ℕ) : ℕ := (nint150 ((q0 : ℝ) * α) % (q0 : ℤ)).toNat

/-- Only the pair `(q0, a0 mod q0)` has `h = 0`. PROVED. -/
theorem hRep_ne_zero150 (α : ℝ) {q0 q a : ℕ} (hq0 : 1 ≤ q0) (hq : 1 ≤ q) (haq : a < q)
    (hcop : Nat.Coprime a q) (hc0 : IsCoprime (nint150 ((q0 : ℝ) * α)) (q0 : ℤ))
    (hex : ¬ (q = q0 ∧ a = r0Rep150 α q0)) : hRep150 α q0 q a ≠ 0 := by
  intro h0
  set a0 := nint150 ((q0 : ℝ) * α) with ha0
  set A := aRep150 α q a with hA
  have hAdef : A = (a : ℤ) + q * nint150 (α - (a : ℝ) / q) := rfl
  have hE : a0 * q = A * q0 := by unfold hRep150 at h0; linarith
  have hcA : IsCoprime A (q : ℤ) := by
    rw [hAdef]
    exact (Nat.isCoprime_iff_coprime.mpr hcop).add_mul_left_left _
  have hqd : (q : ℤ) ∣ q0 := by
    have : (q : ℤ) ∣ (q0 : ℤ) * A := ⟨a0, by rw [mul_comm (q0 : ℤ) A, ← hE]; ring⟩
    exact hcA.symm.dvd_of_dvd_mul_right this
  have hq0d : (q0 : ℤ) ∣ q := by
    have : (q0 : ℤ) ∣ (q : ℤ) * a0 := ⟨A, by rw [mul_comm (q : ℤ) a0, hE]; ring⟩
    exact hc0.symm.dvd_of_dvd_mul_right this
  have hqq : (q : ℤ) = q0 := Int.dvd_antisymm (by positivity) (by positivity) hqd hq0d
  have hqq' : q = q0 := by exact_mod_cast hqq
  apply hex
  refine ⟨hqq', ?_⟩
  have hq0Z : (q0 : ℤ) ≠ 0 := by exact_mod_cast (by omega : q0 ≠ 0)
  rw [hqq] at hE
  have hA0 : a0 = A := by
    have : a0 * q0 = A * q0 := hE
    exact mul_right_cancel₀ hq0Z this
  have hmod : ((a : ℤ) + q * nint150 (α - (a : ℝ) / q)) % (q0 : ℤ) = a := by
    rw [← hqq, Int.add_mul_emod_self_left]; exact Int.emod_eq_of_lt (by omega) (by omega)
  show a = (a0 % (q0 : ℤ)).toNat
  rw [hA0, hAdef, hmod]; simp

/-- Farey spacing: two pairs with the same `h ≠ 0` and different denominators `q1 ≠ q2`
give points `y` at least `1/(q1 q2)` apart. PROVED. -/
theorem yRep_spacing150 (α : ℝ) {q0 q1 q2 a1 a2 : ℕ} (hq1 : 1 ≤ q1) (hq2 : 1 ≤ q2)
    (hne : q1 ≠ q2) (h : hRep150 α q0 q1 a1 = hRep150 α q0 q2 a2) (h0 : hRep150 α q0 q1 a1 ≠ 0) :
    1 / ((q1 : ℝ) * q2) ≤ |yRep150 α q1 a1 - yRep150 α q2 a2| := by
  set A1 := aRep150 α q1 a1
  set A2 := aRep150 α q2 a2
  set a0 := nint150 ((q0 : ℝ) * α)
  set hh := hRep150 α q0 q1 a1 with hhh
  have e1 : a0 * q1 - A1 * q0 = hh := rfl
  have e2 : a0 * q2 - A2 * q0 = hh := by rw [h]; rfl
  have hN : (q0 : ℤ) * (A1 * q2 - A2 * q1) = hh * ((q1 : ℤ) - q2) := by
    linear_combination (-(q2 : ℤ)) * e1 + (q1 : ℤ) * e2
  have hN0 : A1 * q2 - A2 * q1 ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hN
    have : (q1 : ℤ) - q2 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne)
    exact (mul_ne_zero h0 this) hN.symm
  have hN1 : (1 : ℝ) ≤ |((A1 * q2 - A2 * q1 : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hN0
  have hq1R : (0 : ℝ) < q1 := by exact_mod_cast hq1
  have hq2R : (0 : ℝ) < q2 := by exact_mod_cast hq2
  have e : yRep150 α q1 a1 - yRep150 α q2 a2 = -((A1 * q2 - A2 * q1 : ℤ) : ℝ) / ((q1 : ℝ) * q2) := by
    unfold yRep150; push_cast; field_simp; ring
  rw [e, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < (q1 : ℝ) * q2)]
  exact div_le_div_of_nonneg_right hN1 (by positivity)

/-! ### `(q/φ(q))² ≪ X^ε`: copies from ModelL2_150.lean -/

/-- `n ≤ φ(n) d(n)`. Verbatim copy of the private lemma `le_totient_mul_card_divisors_m150`
of ModelL2_150.lean. -/
private lemma le_totient_mul_card_divisors_f150 (n : ℕ) :
    n ≤ Nat.totient n * n.divisors.card := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hid := Nat.totient_mul_prod_primeFactors n
  have h2 : ∏ p ∈ n.primeFactors, p ≤
      2 ^ n.primeFactors.card * ∏ p ∈ n.primeFactors, (p - 1) := by
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun p hp => ?_)
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have h3 : 2 ^ n.primeFactors.card ≤ n.divisors.card := by
    rw [Nat.card_divisors hn.ne', ← Finset.prod_const]
    refine Finset.prod_le_prod (fun p hp => ?_)
    have hp' : p ∈ n.factorization.support := by rwa [Nat.support_factorization]
    have : n.factorization p ≠ 0 := Finsupp.mem_support_iff.mp hp'
    omega
  have hQ : 0 < ∏ p ∈ n.primeFactors, (p - 1) := by
    refine Finset.prod_pos fun p hp => ?_
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have hmain : n * ∏ p ∈ n.primeFactors, (p - 1) ≤
      (Nat.totient n * n.divisors.card) * ∏ p ∈ n.primeFactors, (p - 1) := by
    calc n * ∏ p ∈ n.primeFactors, (p - 1)
        = Nat.totient n * ∏ p ∈ n.primeFactors, p := hid.symm
      _ ≤ Nat.totient n * (2 ^ n.primeFactors.card * ∏ p ∈ n.primeFactors, (p - 1)) :=
          Nat.mul_le_mul_left _ h2
      _ ≤ Nat.totient n * (n.divisors.card * ∏ p ∈ n.primeFactors, (p - 1)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h3)
      _ = (Nat.totient n * n.divisors.card) * ∏ p ∈ n.primeFactors, (p - 1) := by ring
  exact Nat.le_of_mul_le_mul_right hmain hQ

/-- `n ^ a / φ(n)² ≤ D² n ^ (a - 2 + 2/k)`. Verbatim copy of the private lemma of
ModelL2_150.lean, `totient_rpow_bound_m150`. -/
private lemma totient_rpow_bound_f150 (k : ℕ) (hk : 1 ≤ k) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ, 1 ≤ n → ∀ a : ℝ,
      (n : ℝ) ^ a / (Nat.totient n : ℝ) ^ 2 ≤ D ^ 2 * (n : ℝ) ^ (a - 2 + 2 * (k : ℝ)⁻¹) := by
  obtain ⟨D, hD, hDb⟩ := LeanLab.HeathBrown1985.card_divisors_le_rpow k hk
  refine ⟨D, hD, fun n hn a => ?_⟩
  set t : ℝ := (k : ℝ)⁻¹ with ht
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hφ : (0 : ℝ) < (Nat.totient n : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hn
  have h1 : (n : ℝ) ≤ (Nat.totient n : ℝ) * (D * (n : ℝ) ^ t) := by
    have h0 := le_totient_mul_card_divisors_f150 n
    have h' : (n : ℝ) ≤ (Nat.totient n : ℝ) * (n.divisors.card : ℝ) := by exact_mod_cast h0
    exact h'.trans (mul_le_mul_of_nonneg_left (hDb n hn) hφ.le)
  have hsplit : (n : ℝ) = (n : ℝ) ^ (1 - t) * (n : ℝ) ^ t := by
    rw [← Real.rpow_add hnR]; simp
  have hnt : 0 < (n : ℝ) ^ t := Real.rpow_pos_of_pos hnR t
  have h2 : (n : ℝ) ^ (1 - t) ≤ D * (Nat.totient n : ℝ) := by
    have h4 : (n : ℝ) ^ (1 - t) * (n : ℝ) ^ t ≤ (D * (Nat.totient n : ℝ)) * (n : ℝ) ^ t := by
      rw [← hsplit]; linarith [h1]
    exact le_of_mul_le_mul_right h4 hnt
  have h3 : (n : ℝ) ^ (2 - 2 * t) ≤ D ^ 2 * (Nat.totient n : ℝ) ^ 2 := by
    have e : (n : ℝ) ^ (2 - 2 * t) = ((n : ℝ) ^ (1 - t)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le]
      congr 1
      push_cast
      ring
    rw [e, ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) h2 2
  have e2 : (n : ℝ) ^ a = (n : ℝ) ^ (a - 2 + 2 * t) * (n : ℝ) ^ (2 - 2 * t) := by
    rw [← Real.rpow_add hnR]; congr 1; ring
  rw [e2, div_le_iff₀ (by positivity)]
  calc (n : ℝ) ^ (a - 2 + 2 * t) * (n : ℝ) ^ (2 - 2 * t)
      ≤ (n : ℝ) ^ (a - 2 + 2 * t) * (D ^ 2 * (Nat.totient n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = D ^ 2 * (n : ℝ) ^ (a - 2 + 2 * t) * (Nat.totient n : ℝ) ^ 2 := by ring

/-- `(q/φ(q))² ≪_ε X^ε` for `1 ≤ q ≤ X`. PROVED. -/
theorem sq_div_totient_le_f150 (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ X : ℕ, 1 ≤ X → ∀ q : ℕ, 1 ≤ q → q ≤ X →
      (q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 ≤ K * (X : ℝ) ^ ε := by
  set k : ℕ := ⌈2 / ε⌉₊ + 1 with hk
  have hk1 : 1 ≤ k := by omega
  have hkR : (2 / ε : ℝ) < k := by
    have := Nat.le_ceil (2 / ε)
    rw [hk]; push_cast; linarith
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  have hs : 2 * (k : ℝ)⁻¹ ≤ ε := by
    rw [mul_comm, ← div_eq_inv_mul, div_le_iff₀ hkpos]
    have := (div_lt_iff₀ hε).mp hkR
    linarith
  obtain ⟨D, hD, hDb⟩ := totient_rpow_bound_f150 k hk1
  refine ⟨D ^ 2, by positivity, fun X hX q hq hqX => ?_⟩
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hb := hDb q hq 2
  rw [Real.rpow_two, show (2 : ℝ) - 2 + 2 * (k : ℝ)⁻¹ = 2 * (k : ℝ)⁻¹ by ring] at hb
  calc (q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 ≤ D ^ 2 * (q : ℝ) ^ (2 * (k : ℝ)⁻¹) := hb
    _ ≤ D ^ 2 * (X : ℝ) ^ (2 * (k : ℝ)⁻¹) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact Real.rpow_le_rpow (by linarith) (by exact_mod_cast hqX) (by positivity)
    _ ≤ D ^ 2 * (X : ℝ) ^ ε :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hXR hs) (by positivity)

/-! ### One pair -/

/-- The bound for one pair away from the Farey neighbours: if `|h| ≥ 2` or `2q ≤ Q`, then
`|y| ≥ |h|/(2 q q0)` and the kernel bound gives `h² |T(y)|² ≤ q² q0²`. PROVED. -/
theorem pair_bound_f150 {q q0 Q e y h t : ℝ} (hq : 1 ≤ q) (hqQ : q ≤ Q) (he : |e| ≤ 1 / Q)
    (hy : y * (q * q0) = q * e + h) (hh : 1 ≤ |h|) (hcase : 2 ≤ |h| ∨ 2 * q ≤ Q)
    (ht : 4 * y ^ 2 * t ^ 2 ≤ 1) : h ^ 2 * t ^ 2 ≤ q ^ 2 * q0 ^ 2 := by
  have hQ : 0 < Q := by linarith
  have hqe : |q * e| ≤ q / Q := by
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < q), div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left he (by linarith)
  have hqQ1 : q / Q ≤ 1 := by rw [div_le_one hQ]; exact hqQ
  set u := y * (q * q0) with hu
  have htri : |h| ≤ |u| + |q * e| := by
    have : h = u - q * e := by rw [hy]; ring
    rw [this]; exact abs_sub _ _
  have hhu : |h| ≤ 2 * |u| := by
    rcases hcase with h2 | h2
    · linarith
    · have : q / Q ≤ 1 / 2 := by rw [div_le_iff₀ hQ]; linarith
      linarith
  have hsq : h ^ 2 ≤ 4 * u ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg h) hhu 2
    rw [sq_abs, mul_pow, sq_abs] at this; linarith
  have ht0 : 0 ≤ t ^ 2 := sq_nonneg t
  calc h ^ 2 * t ^ 2 ≤ 4 * u ^ 2 * t ^ 2 := mul_le_mul_of_nonneg_right hsq ht0
    _ = (4 * y ^ 2 * t ^ 2) * (q ^ 2 * q0 ^ 2) := by rw [hu]; ring
    _ ≤ 1 * (q ^ 2 * q0 ^ 2) := mul_le_mul_of_nonneg_right ht (by positivity)
    _ = q ^ 2 * q0 ^ 2 := one_mul _

/-! ### `V² - W` as a sum over the other pairs -/

/-- The pairs `(q, a)` of `W` other than the one of the arc of `α`: the arcs of P0029 page 12
whose main terms make up the tail `V² - W`. -/
noncomputable def pairsA150 (α : ℝ) (q0 q : ℕ) : Finset ℕ :=
  ((Finset.range q).filter (fun a => Nat.Coprime a q)).filter
    (fun a => ¬ (q = q0 ∧ a = r0Rep150 α q0))

/-- On the arc of `q0`, `V(α)² = μ(q0)²/φ(q0)² T(α - r0/q0)²` is the term of `W` at
`(q0, r0)`, `r0 = a0 mod q0`, so `|V² - W| ≤ Σ_{other pairs} φ(q)^{-2} |T(y)|²`. PROVED. -/
theorem norm_VW_le_pairs150 (X : ℕ) {α : ℝ} {q0 : ℕ} (hq0 : q0 ∈ Finset.Icc 1 (Nat.sqrt X))
    (hα : α ∈ arcSet150 X q0) :
    ‖VX150 X α ^ 2 - WX150 X α‖ ≤ ∑ q ∈ Finset.Icc 1 (Nat.sqrt X), ∑ a ∈ pairsA150 α q0 q,
      1 / (Nat.totient q : ℝ) ^ 2 * ‖TX150 X (yRep150 α q a)‖ ^ 2 := by
  have hq01 : 1 ≤ q0 := (Finset.mem_Icc.mp hq0).1
  have hq0Z : (0 : ℤ) < q0 := by exact_mod_cast hq01
  have hc0 := isCoprime_nint_f150 X q0 hq01 hα
  set a0 := nint150 ((q0 : ℝ) * α) with ha0
  set r0 := r0Rep150 α q0 with hr0def
  have hr0 : (r0 : ℤ) = a0 % q0 := Int.toNat_of_nonneg (Int.emod_nonneg _ hq0Z.ne')
  have hr0lt : r0 < q0 := by
    have : a0 % q0 < q0 := Int.emod_lt_of_pos _ hq0Z
    omega
  have hr0cop : Nat.Coprime r0 q0 := by
    rw [← Nat.isCoprime_iff_coprime, hr0]
    have := hc0.add_mul_left_left (-(a0 / q0))
    have e : a0 + (q0 : ℤ) * -(a0 / q0) = a0 % q0 := by
      have := Int.emod_add_mul_ediv a0 q0; linarith
    rwa [e] at this
  -- V
  have hV : VX150 X α = arcTerm150 X q0 α := by
    unfold VX150
    rw [Finset.sum_eq_single q0, Set.indicator_of_mem hα]
    · intro b hb hbne
      rw [Set.indicator_of_notMem]
      intro hbα
      exact arcSet_disjoint150 X hq01 (Finset.mem_Icc.mp hb).1 (Ne.symm hbne) hα hbα
    · intro h; exact absurd hq0 h
  have hT : TX150 X (α - (a0 : ℝ) / q0) = TX150 X (α - (r0 : ℝ) / q0) := by
    have e : α - (a0 : ℝ) / q0 = (α - (r0 : ℝ) / q0) - ((a0 / q0 : ℤ) : ℝ) := by
      have h1 : (a0 : ℝ) = (r0 : ℝ) + q0 * ((a0 / q0 : ℤ) : ℝ) := by
        have := Int.emod_add_mul_ediv a0 q0
        rw [← hr0] at this
        exact_mod_cast this.symm
      have hq0R : (q0 : ℝ) ≠ 0 := by exact_mod_cast (by omega : q0 ≠ 0)
      rw [h1]; field_simp; ring
    rw [e, TX_sub_int_f150]
  set F : ℕ → ℕ → ℂ := fun q a => wq150 q * TX150 X (α - (a : ℝ) / q) ^ 2 with hF
  have hV2 : VX150 X α ^ 2 = F q0 r0 := by
    rw [hV]; unfold arcTerm150; rw [← ha0, hT]; simp only [hF, wq150]; ring
  have hsplit : ∀ q ∈ Finset.Icc 1 (Nat.sqrt X),
      ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q), F q a =
        ∑ a ∈ pairsA150 α q0 q, F q a +
          ∑ a ∈ ((Finset.range q).filter (fun a => Nat.Coprime a q)).filter
            (fun a => q = q0 ∧ a = r0), F q a := by
    intro q _
    unfold pairsA150
    rw [add_comm, Finset.sum_filter_add_sum_filter_not]
  have hex : ∑ q ∈ Finset.Icc 1 (Nat.sqrt X),
      ∑ a ∈ ((Finset.range q).filter (fun a => Nat.Coprime a q)).filter
        (fun a => q = q0 ∧ a = r0), F q a = F q0 r0 := by
    rw [Finset.sum_eq_single q0]
    · rw [Finset.sum_eq_single r0]
      · intro b hb hbne; exact absurd (Finset.mem_filter.mp hb).2.2 hbne
      · intro h
        exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨Finset.mem_range.mpr hr0lt, hr0cop⟩, rfl, rfl⟩) h
    · intro b _ hbne
      exact Finset.sum_eq_zero fun a ha => absurd (Finset.mem_filter.mp ha).2.1 hbne
    · intro h; exact absurd hq0 h
  have hW : WX150 X α = ∑ q ∈ Finset.Icc 1 (Nat.sqrt X), ∑ a ∈ pairsA150 α q0 q, F q a +
      F q0 r0 := by
    unfold WX150
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, hex]
  rw [hV2, hW, show F q0 r0 - (∑ q ∈ Finset.Icc 1 (Nat.sqrt X), ∑ a ∈ pairsA150 α q0 q, F q a +
      F q0 r0) = -(∑ q ∈ Finset.Icc 1 (Nat.sqrt X), ∑ a ∈ pairsA150 α q0 q, F q a) by ring,
    norm_neg]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q hq => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hq).1
  simp only [hF]
  rw [norm_mul, norm_pow, TX_yRep150 X α hq1 a]
  exact mul_le_mul_of_nonneg_right norm_wq_le150 (by positivity)

/-! ### The two families of pairs -/

/-- The Farey neighbours of `a0/q0`: the pairs with `h = hi` fixed and `2q > Q`.  Their points
`y` are spaced at least `1/Q²` apart, each term is at most `φ(q)^{-2} min(X², 1/(4y²))` with
`φ(q)^{-2} ≤ 4K/Q²`, and the sum over spaced points is `≪ K X²/Q² + K Q²`. PROVED. -/
theorem farey_neighbours_sum150 (X : ℕ) (hX : 1 ≤ X) (α : ℝ) {q0 : ℕ} (hq01 : 1 ≤ q0)
    (hi : ℤ) (hi0 : hi ≠ 0) {Kx : ℝ}
    (hK : ∀ q ∈ Finset.Icc 1 (Nat.sqrt X), (q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 ≤ Kx) :
    ∑ q ∈ Finset.Icc 1 (Nat.sqrt X), ∑ a ∈ pairsA150 α q0 q,
      (if hRep150 α q0 q a = hi ∧ Nat.sqrt X < 2 * q then
        1 / (Nat.totient q : ℝ) ^ 2 * ‖TX150 X (yRep150 α q a)‖ ^ 2 else 0) ≤
      8 * Kx * (X : ℝ) ^ 2 / (Nat.sqrt X : ℝ) ^ 2 + 4 * Kx * (Nat.sqrt X : ℝ) ^ 2 := by
  set Q := Nat.sqrt X with hQ
  have hQ1 : 1 ≤ Q := Nat.le_sqrt.mpr (by simpa using hX)
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1
  have hKx : 0 ≤ Kx := (div_nonneg (by positivity) (by positivity)).trans (hK 1 (by simp; omega))
  rw [Finset.sum_sigma', ← Finset.sum_filter]
  set S := ((Finset.Icc 1 Q).sigma (pairsA150 α q0)).filter
    (fun p => hRep150 α q0 p.1 p.2 = hi ∧ Q < 2 * p.1) with hS
  have hmem : ∀ p ∈ S, (1 ≤ p.1 ∧ p.1 ≤ Q) ∧ p.2 ∈ pairsA150 α q0 p.1 ∧
      hRep150 α q0 p.1 p.2 = hi ∧ Q < 2 * p.1 := by
    intro p hp
    rw [hS, Finset.mem_filter, Finset.mem_sigma, Finset.mem_Icc] at hp
    exact ⟨hp.1.1, hp.1.2, hp.2⟩
  have hinv : ∀ p ∈ S, 1 / (Nat.totient p.1 : ℝ) ^ 2 ≤ 4 * Kx / (Q : ℝ) ^ 2 := by
    intro p hp
    obtain ⟨⟨h1, h2⟩, _, _, h4⟩ := hmem p hp
    have hqR : (1 : ℝ) ≤ p.1 := by exact_mod_cast h1
    have h4R : (Q : ℝ) < 2 * p.1 := by exact_mod_cast h4
    have hφ : (0 : ℝ) < Nat.totient p.1 := by exact_mod_cast Nat.totient_pos.mpr h1
    have hk := hK p.1 (Finset.mem_Icc.mpr ⟨h1, h2⟩)
    rw [div_le_iff₀ (by positivity)] at hk
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (Q : ℝ) ^ 2 ≤ 4 * (p.1 : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hsp := sum_spaced_f150 S (fun p => yRep150 α p.1 p.2)
    (fun p => 1 / (Nat.totient p.1 : ℝ) ^ 2 * ‖TX150 X (yRep150 α p.1 p.2)‖ ^ 2)
    (d := 1 / (Q : ℝ) ^ 2) (M := 4 * Kx / (Q : ℝ) ^ 2 * (X : ℝ) ^ 2) (c := Kx / (Q : ℝ) ^ 2)
    (by positivity) (by positivity) (by positivity) ?_ ?_ ?_
  · calc _ ≤ 2 * (4 * Kx / (Q : ℝ) ^ 2 * (X : ℝ) ^ 2) + 4 * (Kx / (Q : ℝ) ^ 2) /
          (1 / (Q : ℝ) ^ 2) ^ 2 := hsp
      _ = 8 * Kx * (X : ℝ) ^ 2 / (Q : ℝ) ^ 2 + 4 * Kx * (Q : ℝ) ^ 2 := by
          field_simp; ring
  · rintro ⟨q1, a1⟩ hp1 ⟨q2, a2⟩ hp2 hne
    obtain ⟨⟨h11, h12⟩, ha1, he1, _⟩ := hmem _ hp1
    obtain ⟨⟨h21, h22⟩, ha2, he2, _⟩ := hmem _ hp2
    simp only at h11 h12 ha1 he1 h21 h22 ha2 he2 ⊢
    have hq : q1 ≠ q2 := by
      intro hq
      subst hq
      apply hne
      have hr1 : a1 ∈ (Finset.range q1 : Set ℕ) := by
        unfold pairsA150 at ha1; simp only [Finset.mem_filter] at ha1
        exact Finset.mem_coe.mpr ha1.1.1
      have hr2 : a2 ∈ (Finset.range q1 : Set ℕ) := by
        unfold pairsA150 at ha2; simp only [Finset.mem_filter] at ha2
        exact Finset.mem_coe.mpr ha2.1.1
      have := hRep_injOn150 α (q := q1) hq01 hr1 hr2 (he1.trans he2.symm)
      rw [this]
    have hspc := yRep_spacing150 α h11 h21 hq (he1.trans he2.symm) (by rw [he1]; exact hi0)
    have hq1R : (1 : ℝ) ≤ q1 := by exact_mod_cast h11
    have hq2R : (1 : ℝ) ≤ q2 := by exact_mod_cast h21
    have hq1Q : (q1 : ℝ) ≤ Q := by exact_mod_cast h12
    have hq2Q : (q2 : ℝ) ≤ Q := by exact_mod_cast h22
    refine le_trans ?_ hspc
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  · intro p hp
    have h1 := hinv p hp
    have hT := norm_TX_le150 X (yRep150 α p.1 p.2)
    have hT2 : ‖TX150 X (yRep150 α p.1 p.2)‖ ^ 2 ≤ (X : ℝ) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hT 2
    exact mul_le_mul h1 hT2 (by positivity) (by positivity)
  · intro p hp _
    have h1 := hinv p hp
    obtain ⟨⟨hp1, _⟩, _, _, _⟩ := hmem p hp
    have hk := kernel_TX_f150 X (abs_yRep_le150 α hp1 p.2)
    have e : 1 / (Nat.totient p.1 : ℝ) ^ 2 * ‖TX150 X (yRep150 α p.1 p.2)‖ ^ 2 *
        yRep150 α p.1 p.2 ^ 2 = 1 / (Nat.totient p.1 : ℝ) ^ 2 / 4 *
          (4 * yRep150 α p.1 p.2 ^ 2 * ‖TX150 X (yRep150 α p.1 p.2)‖ ^ 2) := by ring
    rw [e]
    calc _ ≤ 1 / (Nat.totient p.1 : ℝ) ^ 2 / 4 * 1 :=
          mul_le_mul_of_nonneg_left hk (by positivity)
      _ ≤ 4 * Kx / (Q : ℝ) ^ 2 / 4 * 1 := by gcongr
      _ = Kx / (Q : ℝ) ^ 2 := by ring

/-- The pairs away from the Farey neighbours: `Σ (q/φ(q))² q0²/h² ≤ 6 K q0² (Q/q0 + 1)` by the
swap to `h` and `Σ 1/h² ≤ 6`. PROVED. -/
theorem far_pairs_sum150 (X : ℕ) (α : ℝ) {q0 : ℕ} (hq01 : 1 ≤ q0)
    (hc0 : IsCoprime (nint150 ((q0 : ℝ) * α)) (q0 : ℤ)) {Kx : ℝ} (hKx : 0 ≤ Kx) :
    ∑ q ∈ Finset.Icc 1 (Nat.sqrt X), ∑ a ∈ pairsA150 α q0 q,
      Kx * (q0 : ℝ) ^ 2 * ((hRep150 α q0 q a : ℝ) ^ 2)⁻¹ ≤
      Kx * (q0 : ℝ) ^ 2 * ((((Nat.sqrt X / q0 : ℕ) : ℝ) + 1) * 6) := by
  simp_rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hsw := sum_swap_f150 (Nat.sqrt X) q0 (nint150 ((q0 : ℝ) * α)) hc0 (pairsA150 α q0)
    (hRep150 α q0)
    (fun q _ => (hRep_injOn150 α (q := q) hq01).mono (by
      intro a ha
      have ha' := Finset.mem_coe.mp ha
      unfold pairsA150 at ha'
      simp only [Finset.mem_filter] at ha'
      exact Finset.mem_coe.mpr ha'.1.1))
    (fun q _ a _ => dvd_hRep150 α q0 q a) (fun h => ((h : ℝ) ^ 2)⁻¹) (fun h => by positivity)
  refine hsw.trans (mul_le_mul_of_nonneg_left (sum_inv_sq_int_f150 _) (by positivity))

/-! ### The arc tails, pointwise -/

/-- One pair: `φ(q)^{-2} |T(y)|² ≤ K q0²/h² + [h = 1, 2q > Q] + [h = -1, 2q > Q]`. PROVED. -/
theorem pair_split150 (X : ℕ) {α : ℝ} {q0 : ℕ} (hq0 : q0 ∈ Finset.Icc 1 (Nat.sqrt X))
    (hα : α ∈ arcSet150 X q0) (hc0 : IsCoprime (nint150 ((q0 : ℝ) * α)) (q0 : ℤ)) {Kx : ℝ}
    (hK : ∀ q ∈ Finset.Icc 1 (Nat.sqrt X), (q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 ≤ Kx)
    {q a : ℕ} (hq : q ∈ Finset.Icc 1 (Nat.sqrt X)) (ha : a ∈ pairsA150 α q0 q) :
    1 / (Nat.totient q : ℝ) ^ 2 * ‖TX150 X (yRep150 α q a)‖ ^ 2 ≤
      Kx * (q0 : ℝ) ^ 2 * ((hRep150 α q0 q a : ℝ) ^ 2)⁻¹ +
      ((if hRep150 α q0 q a = 1 ∧ Nat.sqrt X < 2 * q then
        1 / (Nat.totient q : ℝ) ^ 2 * ‖TX150 X (yRep150 α q a)‖ ^ 2 else 0) +
      (if hRep150 α q0 q a = -1 ∧ Nat.sqrt X < 2 * q then
        1 / (Nat.totient q : ℝ) ^ 2 * ‖TX150 X (yRep150 α q a)‖ ^ 2 else 0)) := by
  set Q := Nat.sqrt X with hQ
  obtain ⟨hq1, hqQ⟩ := Finset.mem_Icc.mp hq
  have hq01 := (Finset.mem_Icc.mp hq0).1
  unfold pairsA150 at ha
  simp only [Finset.mem_filter, Finset.mem_range] at ha
  obtain ⟨⟨haq, hcop⟩, hex⟩ := ha
  set h := hRep150 α q0 q a with hh
  set t := ‖TX150 X (yRep150 α q a)‖ with ht
  have hne : h ≠ 0 := hRep_ne_zero150 α hq01 hq1 haq hcop hc0 hex
  have hφ : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq1
  have hv0 : 0 ≤ 1 / (Nat.totient q : ℝ) ^ 2 * t ^ 2 := by positivity
  have hKx : 0 ≤ Kx := (div_nonneg (by positivity) (by positivity)).trans (hK q hq)
  have hA0 : 0 ≤ Kx * (q0 : ℝ) ^ 2 * ((h : ℝ) ^ 2)⁻¹ := by positivity
  by_cases hc : (h = 1 ∨ h = -1) ∧ Q < 2 * q
  · rcases hc with ⟨h1 | h1, h2⟩
    · rw [if_pos ⟨h1, h2⟩, if_neg (by rw [h1]; omega)]; linarith
    · rw [if_neg (by rw [h1]; omega), if_pos ⟨h1, h2⟩]; linarith
  · rw [if_neg (fun h' => hc ⟨Or.inl h'.1, h'.2⟩), if_neg (fun h' => hc ⟨Or.inr h'.1, h'.2⟩)]
    have hcase : 2 ≤ |(h : ℝ)| ∨ 2 * (q : ℝ) ≤ Q := by
      by_cases h1 : h = 1 ∨ h = -1
      · right
        have : ¬ Q < 2 * q := fun h2 => hc ⟨h1, h2⟩
        exact_mod_cast (by omega : 2 * q ≤ Q)
      · left
        have : (2 : ℤ) ≤ |h| := by
          rcases abs_cases h with ⟨e, _⟩ | ⟨e, _⟩ <;> omega
        rw [← Int.cast_abs]; exact_mod_cast this
    have hα1 : |(q0 : ℝ) * α - nint150 ((q0 : ℝ) * α)| ≤ 1 / (Q : ℝ) := by
      simp only [arcSet150, Set.mem_inter_iff, Set.mem_ofPred_eq] at hα
      exact hα.1
    have hpb := pair_bound_f150 (q := (q : ℝ)) (q0 := (q0 : ℝ)) (Q := (Q : ℝ))
      (by exact_mod_cast hq1) (by exact_mod_cast hqQ) hα1 (yRep_mul150 α hq1 q0 a)
      (by exact_mod_cast Int.one_le_abs hne) hcase
      (kernel_TX_f150 X (abs_yRep_le150 α hq1 a))
    have hh2 : (0 : ℝ) < (h : ℝ) ^ 2 := by
      have : (h : ℝ) ≠ 0 := by exact_mod_cast hne
      positivity
    have ht2 : t ^ 2 ≤ (q : ℝ) ^ 2 * (q0 : ℝ) ^ 2 / (h : ℝ) ^ 2 := by
      rw [le_div_iff₀ hh2]; linarith
    have hkq := hK q hq
    calc 1 / (Nat.totient q : ℝ) ^ 2 * t ^ 2
        ≤ 1 / (Nat.totient q : ℝ) ^ 2 * ((q : ℝ) ^ 2 * (q0 : ℝ) ^ 2 / (h : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left ht2 (by positivity)
      _ = (q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 * ((q0 : ℝ) ^ 2 * ((h : ℝ) ^ 2)⁻¹) := by
          field_simp
      _ ≤ Kx * ((q0 : ℝ) ^ 2 * ((h : ℝ) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_right hkq (by positivity)
      _ = Kx * (q0 : ℝ) ^ 2 * ((h : ℝ) ^ 2)⁻¹ + (0 + 0) := by ring

/-- P0029 page 12, the arc tails pointwise: `|V(α)² - W(α)| ≪_ε X^{1+ε}` on `[0, 1]`, the
`O(N^{1/2+ε})` of page 12 which the survey states without proof. PROVED. -/
theorem arc_tails_sup_f150 :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X → ∀ α ∈ Set.Icc (0 : ℝ) 1,
      ‖VX150 X α ^ 2 - WX150 X α‖ ≤ C * (X : ℝ) ^ (1 + ε) := by
  intro ε hε
  obtain ⟨K, hK0, hK⟩ := sq_div_totient_le_f150 ε hε
  refine ⟨84 * K, fun X hX α _ => ?_⟩
  set Q := Nat.sqrt X with hQ
  have hQ1 : 1 ≤ Q := Nat.le_sqrt.mpr (by simpa using hX)
  have hQR : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hQ2 : (Q : ℝ) ^ 2 ≤ X := by exact_mod_cast Nat.sqrt_le' X
  have hX4 : (X : ℝ) ≤ 4 * (Q : ℝ) ^ 2 := by
    have h1 : X < (Q + 1) ^ 2 := Nat.lt_succ_sqrt' X
    have h2 : ((X : ℕ) : ℝ) < ((Q : ℝ) + 1) ^ 2 := by exact_mod_cast h1
    nlinarith
  set Kx := K * (X : ℝ) ^ ε with hKxdef
  have hKx0 : 0 ≤ Kx := by positivity
  have hKq : ∀ q ∈ Finset.Icc 1 Q, (q : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2 ≤ Kx := by
    intro q hq
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hq
    exact hK X hX q h1 (h2.trans (Nat.sqrt_le_self X))
  obtain ⟨q0, hq0, hα⟩ := exists_arc_f150 X hX α
  have hq01 := (Finset.mem_Icc.mp hq0).1
  have hq0Q := (Finset.mem_Icc.mp hq0).2
  have hc0 := isCoprime_nint_f150 X q0 hq01 hα
  have hmain := norm_VW_le_pairs150 X hq0 hα
  have hsplit := Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun a ha =>
    pair_split150 X hq0 hα hc0 hKq hq ha
  simp only [Finset.sum_add_distrib] at hsplit
  have hA := far_pairs_sum150 X α hq01 hc0 hKx0
  have hB1 := farey_neighbours_sum150 X hX α hq01 1 one_ne_zero hKq
  have hB2 := farey_neighbours_sum150 X hX α hq01 (-1) (by norm_num) hKq
  -- the arithmetic
  have hq0R : (1 : ℝ) ≤ q0 := by exact_mod_cast hq01
  have hq0QR : (q0 : ℝ) ≤ Q := by exact_mod_cast hq0Q
  have hdiv : (((Q / q0 : ℕ) : ℝ)) ≤ (Q : ℝ) / q0 := Nat.cast_div_le
  have hAX : Kx * (q0 : ℝ) ^ 2 * ((((Q / q0 : ℕ) : ℝ) + 1) * 6) ≤ 12 * Kx * X := by
    have h1 : (q0 : ℝ) ^ 2 * (((Q / q0 : ℕ) : ℝ) + 1) ≤ (q0 : ℝ) * Q + (q0 : ℝ) ^ 2 := by
      have : (q0 : ℝ) ^ 2 * ((Q : ℝ) / q0) = q0 * Q := by field_simp
      nlinarith
    have h2 : (q0 : ℝ) * Q + (q0 : ℝ) ^ 2 ≤ 2 * X := by nlinarith
    have h3 : (q0 : ℝ) ^ 2 * (((Q / q0 : ℕ) : ℝ) + 1) ≤ 2 * X := h1.trans h2
    calc Kx * (q0 : ℝ) ^ 2 * ((((Q / q0 : ℕ) : ℝ) + 1) * 6)
        = 6 * Kx * ((q0 : ℝ) ^ 2 * (((Q / q0 : ℕ) : ℝ) + 1)) := by ring
      _ ≤ 6 * Kx * (2 * X) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 12 * Kx * X := by ring
  have hBX : 8 * Kx * (X : ℝ) ^ 2 / (Q : ℝ) ^ 2 + 4 * Kx * (Q : ℝ) ^ 2 ≤ 36 * Kx * X := by
    have hQpos : (0 : ℝ) < (Q : ℝ) ^ 2 := by positivity
    have h1 : (X : ℝ) ^ 2 / (Q : ℝ) ^ 2 ≤ 4 * X := by
      rw [div_le_iff₀ hQpos]; nlinarith
    have e : 8 * Kx * (X : ℝ) ^ 2 / (Q : ℝ) ^ 2 = 8 * Kx * ((X : ℝ) ^ 2 / (Q : ℝ) ^ 2) := by ring
    rw [e]
    have h2 : 8 * Kx * ((X : ℝ) ^ 2 / (Q : ℝ) ^ 2) ≤ 8 * Kx * (4 * X) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : 4 * Kx * (Q : ℝ) ^ 2 ≤ 4 * Kx * X := mul_le_mul_of_nonneg_left hQ2 (by positivity)
    linarith
  have hfin : Kx * (X : ℝ) = K * (X : ℝ) ^ (1 + ε) := by
    rw [hKxdef, Real.rpow_add (by linarith : (0 : ℝ) < X), Real.rpow_one]; ring
  calc ‖VX150 X α ^ 2 - WX150 X α‖ ≤ 12 * Kx * X + (36 * Kx * X + 36 * Kx * X) := by
        linarith
    _ = 84 * (Kx * X) := by ring
    _ = 84 * K * (X : ℝ) ^ (1 + ε) := by rw [hfin]; ring

end LeanLab.BhowmikGrimmelt2026
