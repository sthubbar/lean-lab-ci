/-
Independent Davenport chapter 19 leaves for the sealed integer formula.
The character contour port on main supplies every analytic leaf.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.PNTPort.ExplicitPsi1.CharHalfAssembly1122

namespace LeanLab.BhowmikGrimmelt2026.Davenport636

open Complex Filter Topology Set
open LeanLab.PNTPort.ExplicitPsi1
open LeanLab.PNTPort.ExplicitPsi1.CharHalfAssembly1122

/-- LEAF: Davenport chapter 17 pages 105 to 109 and chapter 19 page 116.
The half weighted integer sum differs from its truncated Perron integral by
an absolute constant times n log squared n over T plus log n. -/
theorem perron_half636 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (n : ℕ), 2 ≤ n → ∀ T : ℝ, 2 ≤ T →
    ‖((∑ m ∈ Finset.range n, (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) +
        (1 / 2 : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) -
      (1 / (2 * Real.pi) : ℂ) * (∫ t in (-T)..T,
        -(deriv (DirichletCharacter.LFunction χ)
            (((1 + 1 / Real.log n : ℝ) : ℂ) + t * I) /
          DirichletCharacter.LFunction χ (((1 + 1 / Real.log n : ℝ) : ℂ) + t * I)) *
        (n : ℂ) ^ (((1 + 1 / Real.log n : ℝ) : ℂ) + t * I) /
          (((1 + 1 / Real.log n : ℝ) : ℂ) + t * I))‖ ≤
      C * ((n : ℝ) * Real.log n ^ 2 / T + Real.log n) := by
  exact CharPerronHalf1122.char_perron_half1122

/-- LEAF: Davenport chapter 19 page 116, modified height estimate before display 4.
A height between T and T plus four avoids zeros and bounds both horizontal
logarithmic derivatives by an absolute constant times log squared of q max T 5. -/
theorem good_height636 : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q), χ.IsPrimitive → ∀ T : ℝ, 2 ≤ T → ∃ T' : ℝ,
      T ≤ T' ∧ T' ≤ T + 4 ∧ 5 ≤ T' ∧
      ∀ σ ∈ Icc (-1 / 2 : ℝ) 2, ∀ τ ∈ ({T', -T'} : Set ℝ),
        χ.LFunction (σ + τ * I) ≠ 0 ∧
        ‖deriv χ.LFunction (σ + τ * I) / χ.LFunction (σ + τ * I)‖ ≤
          C * Real.log ((q : ℝ) * max T 5) ^ 2 := by
  exact CharHalfAssembly1122.good_height_ge_two

/-- LEAF: Davenport chapter 19 page 117 display 4.
At a good height the shifted Perron contour includes the nontrivial zero
residues, the origin correction and the trivial zero sum with its edge error. -/
theorem contour636 : ∃ D : ℝ, 0 ≤ D ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → ∀ T' K : ℝ, 2 ≤ T' → 0 ≤ K →
      (∀ σ ∈ Icc (-1 / 2 : ℝ) 2, ∀ τ ∈ ({T', -T'} : Set ℝ),
        χ.LFunction (σ + τ * I) ≠ 0 ∧
        ‖deriv χ.LFunction (σ + τ * I) / χ.LFunction (σ + τ * I)‖ ≤ K) →
      ∀ b : ℂ, IsB χ b → ∀ n : ℕ, 2 ≤ n → ∀ Z' : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z' ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T') →
      ‖perronJ χ n T' +
          (∑ ρ ∈ Z', (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) *
            (n : ℂ) ^ ρ / ρ) + (zeroLog χ n : ℂ) + b - (trivSum χ n : ℂ)‖ ≤
        D * ((K + 1) * n / T' + Real.log ((q : ℝ) * T') / T' + Real.log n) := by
  exact CharHalfAssembly1122.contour_good_height_leaf

/-- LEAF: Davenport chapter 19 page 117 displays 4 and 6.
The zero sum in the strip from T to a good height at most T plus four has
norm at most an absolute constant times n over T times log of q T. -/
theorem window636 : ∃ A : ℝ, 0 ≤ A ∧ ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q), χ.IsPrimitive → χ ≠ 1 → ∀ T T' : ℝ, 2 ≤ T → T ≤ T' →
      T' ≤ T + 4 → ∀ n : ℕ, 2 ≤ n → ∀ W : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ W ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ T ≤ |ρ.im| ∧ |ρ.im| < T') →
      ‖∑ ρ ∈ W, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) *
          (n : ℂ) ^ ρ / ρ‖ ≤ A * ((n : ℝ) / T * Real.log ((q : ℝ) * T)) := by
  exact CharHalfAssembly1122.window_switch

/-- LEAF: Davenport chapter 19 page 118, formula for b after the high zero estimate.
The regularized constant plus the low reciprocal zero sum has norm at most
an absolute constant times log q. -/
theorem constant636 : ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    χ.IsPrimitive → χ ≠ 1 → ∀ b : ℂ,
      ((χ.Odd ∧ b = deriv (DirichletCharacter.LFunction χ) 0 /
          DirichletCharacter.LFunction χ 0) ∨
        (χ.Even ∧ Tendsto (fun s => deriv (DirichletCharacter.LFunction χ) s /
          DirichletCharacter.LFunction χ s - 1 / s) (𝓝[≠] 0) (𝓝 b))) →
      ∀ Z : Finset ℂ, (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1) →
      ‖b + ∑ ρ ∈ Z, (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / ρ‖ ≤
        C * Real.log q := by
  exact CharBRegroup1122.b_regroup

set_option maxHeartbeats 1000000 in
/-- Davenport chapter 19 page 117 displays 4 and 6 and page 118.
The independent assembly combines the five proved analytic leaves.
No hypothesis T at most n is used. -/
theorem formula636 :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
      χ.IsPrimitive → χ ≠ 1 → ∀ T : ℝ, 2 ≤ T → ∀ Z : Finset ℂ,
      (∀ ρ : ℂ, ρ ∈ Z ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
        0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T) →
      ∀ n : ℕ, 2 ≤ n →
      ‖((∑ m ∈ Finset.range n,
          (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) +
          (1 / 2 : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q)) +
        (∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < T),
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * (n : ℂ) ^ ρ / ρ) -
        ∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < 1),
          (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / ρ‖ ≤
        D * ((n : ℝ) / T * Real.log ((q : ℝ) * n * T) ^ 2 +
          Real.log q + Real.log n) := by
  obtain ⟨CP, hCP, hP⟩ := perron_half636
  obtain ⟨CG, hCG, hG⟩ := good_height636
  obtain ⟨DC, hDC, hC⟩ := contour636
  obtain ⟨AW, hAW, hW⟩ := window636
  obtain ⟨Cb, hCb, hB⟩ := constant636
  set a1 : ℝ := CP + DC * (4 * CG + 1) + AW with ha1
  set a2 : ℝ := Cb + DC with ha2
  set a3 : ℝ := CP + 3 * DC + 3 with ha3
  refine ⟨a1 + a2 + a3, by rw [ha1, ha2, ha3]; positivity, ?_⟩
  intro q _ χ hprim hχ T hT Z hZ n hn
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hnpos : 0 < n := by omega
  have hT0 : 0 < T := by linarith
  -- real facts
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log n := by
    have := Real.log_two_gt_d9
    have : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn2
    linarith
  have hlogq : 0 ≤ Real.log q := Real.log_nonneg hq1
  set L : ℝ := Real.log ((q : ℝ) * n * T) with hL
  have hqT2 : 2 ≤ (q : ℝ) * T := by nlinarith
  have hqnT' : (q : ℝ) * n * T = (n : ℝ) * ((q : ℝ) * T) := by ring
  have hqnT : 4 ≤ (q : ℝ) * n * T := by rw [hqnT']; nlinarith
  have hnqnT : (n : ℝ) ≤ (q : ℝ) * n * T := by rw [hqnT']; nlinarith
  have hqTqnT : (q : ℝ) * T ≤ (q : ℝ) * n * T := by rw [hqnT']; nlinarith
  have hL1 : 1 ≤ L := by
    rw [hL]
    have h4 : Real.log 4 ≤ Real.log ((q : ℝ) * n * T) := Real.log_le_log (by norm_num) hqnT
    have : (1 : ℝ) < Real.log 4 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      have := Real.log_two_gt_d9; push_cast; linarith
    linarith
  have hLL : L ≤ L ^ 2 := by nlinarith
  have hnL : Real.log n ≤ L := by
    rw [hL]; exact Real.log_le_log (by linarith) hnqnT
  have hqTL : Real.log ((q : ℝ) * T) ≤ L := by
    rw [hL]; exact Real.log_le_log (by positivity) hqTqnT
  have hqT0 : 0 ≤ Real.log ((q : ℝ) * T) := Real.log_nonneg (by linarith)
  have hmaxL : Real.log ((q : ℝ) * max T 5) ≤ 2 * L := by
    have hm : max T 5 ≤ 3 * T := max_le (by linarith) (by linarith)
    have hm' : (q : ℝ) * max T 5 ≤ (q : ℝ) * (3 * T) :=
      mul_le_mul_of_nonneg_left hm (by positivity)
    have h3 : Real.log ((q : ℝ) * max T 5) ≤ Real.log (3 * ((q : ℝ) * n * T)) :=
      Real.log_le_log (mul_pos (by positivity) (lt_of_lt_of_le (by norm_num) (le_max_right T 5)))
        (by have := hqTqnT; linarith)
    rw [Real.log_mul (x := 3) (y := (q : ℝ) * n * T) (by norm_num) (by positivity)] at h3
    have : Real.log 3 ≤ Real.log ((q : ℝ) * n * T) := Real.log_le_log (by norm_num) (by linarith)
    rw [hL]; linarith
  have hmax0 : 0 ≤ Real.log ((q : ℝ) * max T 5) := by
    have h5 : (5 : ℝ) ≤ max T 5 := le_max_right T 5
    exact Real.log_nonneg (one_le_mul_of_one_le_of_one_le hq1 (by linarith))
  have hK : CG * Real.log ((q : ℝ) * max T 5) ^ 2 ≤ 4 * CG * L ^ 2 := by
    have : Real.log ((q : ℝ) * max T 5) ^ 2 ≤ (2 * L) ^ 2 := by
      exact pow_le_pow_left₀ hmax0 hmaxL 2
    nlinarith
  set X : ℝ := (n : ℝ) / T * L ^ 2 with hX
  have hX0 : 0 ≤ X := by rw [hX]; positivity
  -- the good height
  obtain ⟨T', hTT', hT'4, hT'5, hgood⟩ := hG q χ hprim T hT
  -- the zeros up to height `T'`
  have hfin : {ρ : ℂ | DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T'}.Finite := by
    refine (CharRect1122.charZeros_rect_finite χ hχ 1 T').subset ?_
    rintro ρ ⟨h0, hr0, hr1, hi⟩
    refine ⟨Complex.mem_reProdIm.mpr ⟨?_, ?_⟩, h0⟩
    · show ρ.re ∈ uIcc (-1 / 2 : ℝ) 1
      rw [uIcc_of_le (by norm_num)]; exact ⟨by linarith, hr1.le⟩
    · show ρ.im ∈ uIcc (-T') T'
      rw [abs_lt] at hi
      rw [uIcc_of_le (by linarith)]; exact ⟨hi.1.le, hi.2.le⟩
  set Z' := hfin.toFinset with hZ'
  have hZ'mem : ∀ ρ : ℂ, ρ ∈ Z' ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T' := fun ρ => by
    rw [hZ', Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  set W := Z'.filter (fun ρ => ¬ |ρ.im| < T) with hWdef
  have hWmem : ∀ ρ : ℂ, ρ ∈ W ↔ DirichletCharacter.LFunction χ ρ = 0 ∧
      0 < ρ.re ∧ ρ.re < 1 ∧ T ≤ |ρ.im| ∧ |ρ.im| < T' := fun ρ => by
    rw [hWdef, Finset.mem_filter, hZ'mem, not_lt]
    tauto
  have hsplitZ : Z'.filter (fun ρ => |ρ.im| < T) = Z.filter (fun ρ => |ρ.im| < T) := by
    ext ρ
    rw [Finset.mem_filter, Finset.mem_filter, hZ'mem, hZ]
    constructor
    · rintro ⟨⟨h0, h1, h2, _⟩, h4⟩; exact ⟨⟨h0, h1, h2, h4.le⟩, h4⟩
    · rintro ⟨⟨h0, h1, h2, _⟩, h4⟩; exact ⟨⟨h0, h1, h2, by linarith⟩, h4⟩
  have hZ1mem : ∀ ρ : ℂ, ρ ∈ Z.filter (fun ρ => |ρ.im| < 1) ↔
      DirichletCharacter.LFunction χ ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < 1 := fun ρ => by
    rw [Finset.mem_filter, hZ]
    constructor
    · rintro ⟨⟨h0, h1, h2, _⟩, h4⟩; exact ⟨h0, h1, h2, h4⟩
    · rintro ⟨h0, h1, h2, h4⟩; exact ⟨⟨h0, h1, h2, by linarith⟩, h4⟩
  -- the constant `b(χ)`
  obtain ⟨b, hb⟩ := exists_isB hprim hχ
  -- notation
  set f : ℂ → ℂ := fun ρ =>
    (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) * (n : ℂ) ^ ρ / ρ with hf
  set P₀ : ℂ := (∑ m ∈ Finset.range n,
      (ArithmeticFunction.vonMangoldt m : ℂ) * χ (m : ZMod q)) +
      (1 / 2 : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod q) with hP₀
  set J : ℂ := perronJ χ n T' with hJ
  set SZ : ℂ := ∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < T), f ρ with hSZ
  set SW : ℂ := ∑ ρ ∈ W, f ρ with hSW
  set S1 : ℂ := ∑ ρ ∈ Z.filter (fun ρ => |ρ.im| < 1),
    (analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ : ℂ) / ρ with hS1
  change ‖P₀ + SZ - S1‖ ≤ (a1 + a2 + a3) * (X + Real.log q + Real.log n)
  have hsum : ∑ ρ ∈ Z', f ρ = SZ + SW := by
    rw [← Finset.sum_filter_add_sum_filter_not Z' (fun ρ => |ρ.im| < T), hsplitZ]
  -- the five bounds
  have hT'0 : 0 < T' := by linarith
  have hPer : ‖P₀ - J‖ ≤ CP * ((n : ℝ) * Real.log n ^ 2 / T' + Real.log n) :=
    hP q χ n hn T' (by linarith)
  have hK0 : 0 ≤ CG * Real.log ((q : ℝ) * max T 5) ^ 2 := by positivity
  have hCon : ‖J + (SZ + SW) + (zeroLog χ n : ℂ) + b - (trivSum χ n : ℂ)‖ ≤
      DC * ((CG * Real.log ((q : ℝ) * max T 5) ^ 2 + 1) * n / T' +
        Real.log ((q : ℝ) * T') / T' + Real.log n) := by
    have h := hC q χ hprim hχ T' _ (by linarith) hK0 hgood b hb n hn Z' hZ'mem
    rw [← hsum]
    exact h
  have hWb : ‖SW‖ ≤ AW * ((n : ℝ) / T * Real.log ((q : ℝ) * T)) :=
    hW q χ hprim hχ T T' hT hTT' hT'4 n hn W hWmem
  have hbb : ‖b + S1‖ ≤ Cb * Real.log q := hB q χ hprim hχ b hb _ hZ1mem
  have htriv := trivSum_bound χ hn
  have hzl := zeroLog_bound χ hn
  clear_value f P₀ J SZ SW S1
  -- the identity
  have hid : P₀ + SZ - S1 = (P₀ - J) + (J + (SZ + SW) + (zeroLog χ n : ℂ) + b -
      (trivSum χ n : ℂ)) - SW - (zeroLog χ n : ℂ) - (b + S1) + (trivSum χ n : ℂ) := by ring
  have hnT : (n : ℝ) / T' ≤ (n : ℝ) / T := div_le_div_of_nonneg_left (by positivity) hT0 hTT'
  -- bound 1: Perron
  have b1 : ‖P₀ - J‖ ≤ CP * X + CP * Real.log n := by
    refine hPer.trans ?_
    have : (n : ℝ) * Real.log n ^ 2 / T' ≤ X := by
      rw [hX, mul_div_right_comm]
      have h1 : Real.log n ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hlogn hnL 2
      have h2 : (n : ℝ) / T' * Real.log n ^ 2 ≤ (n : ℝ) / T * Real.log n ^ 2 :=
        mul_le_mul_of_nonneg_right hnT (by positivity)
      have h3 : (n : ℝ) / T * Real.log n ^ 2 ≤ (n : ℝ) / T * L ^ 2 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      linarith
    have := mul_le_mul_of_nonneg_left this hCP
    linarith
  -- bound 2: contour
  have b2 : ‖J + (SZ + SW) + (zeroLog χ n : ℂ) + b - (trivSum χ n : ℂ)‖ ≤
      DC * (4 * CG + 1) * X + DC * Real.log q + 3 * DC * Real.log n := by
    refine hCon.trans ?_
    have e1 : (CG * Real.log ((q : ℝ) * max T 5) ^ 2 + 1) * n / T' ≤ (4 * CG + 1) * X := by
      have hA : CG * Real.log ((q : ℝ) * max T 5) ^ 2 + 1 ≤ (4 * CG + 1) * L ^ 2 := by
        have hL2 : 1 ≤ L ^ 2 := by linarith
        linarith
      have := mul_le_mul hA hnT (by positivity) (by positivity)
      have e : (CG * Real.log ((q : ℝ) * max T 5) ^ 2 + 1) * n / T' =
          (CG * Real.log ((q : ℝ) * max T 5) ^ 2 + 1) * ((n : ℝ) / T') := by ring
      rw [e, hX]
      linarith
    have e2 : Real.log ((q : ℝ) * T') / T' ≤ Real.log q + 2 * Real.log n := by
      rw [Real.log_mul (by positivity) (by positivity), add_div]
      have h1 : Real.log q / T' ≤ Real.log q := div_le_self hlogq (by linarith)
      have h2 : Real.log T' / T' ≤ 1 := by
        rw [div_le_one hT'0]
        have := Real.log_le_sub_one_of_pos hT'0
        linarith
      linarith
    have := mul_le_mul_of_nonneg_left (add_le_add (add_le_add e1 e2) (le_refl (Real.log n))) hDC
    linarith
  -- bound 3: window
  have b3 : ‖SW‖ ≤ AW * X := by
    refine hWb.trans (mul_le_mul_of_nonneg_left ?_ hAW)
    rw [hX]
    exact mul_le_mul_of_nonneg_left (hqTL.trans hLL) (by positivity)
  -- bound 4, 5, 6
  have b4 : ‖(zeroLog χ n : ℂ)‖ ≤ Real.log n := by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hzl
  have b5 : ‖b + S1‖ ≤ Cb * Real.log q := hbb
  have b6 : ‖(trivSum χ n : ℂ)‖ ≤ 2 * Real.log n := by
    rw [Complex.norm_real, Real.norm_eq_abs]; linarith
  -- combine
  rw [hid]
  have htri : ‖(P₀ - J) + (J + (SZ + SW) + (zeroLog χ n : ℂ) + b -
      (trivSum χ n : ℂ)) - SW - (zeroLog χ n : ℂ) - (b + S1) + (trivSum χ n : ℂ)‖ ≤
      ‖P₀ - J‖ + ‖J + (SZ + SW) + (zeroLog χ n : ℂ) + b - (trivSum χ n : ℂ)‖ + ‖SW‖ +
        ‖(zeroLog χ n : ℂ)‖ + ‖b + S1‖ + ‖(trivSum χ n : ℂ)‖ := by
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
    exact norm_add_le _ _
  refine htri.trans ?_
  have hsum6 : ‖P₀ - J‖ + ‖J + (SZ + SW) + (zeroLog χ n : ℂ) + b - (trivSum χ n : ℂ)‖ +
      ‖SW‖ + ‖(zeroLog χ n : ℂ)‖ + ‖b + S1‖ + ‖(trivSum χ n : ℂ)‖ ≤
      a1 * X + a2 * Real.log q + a3 * Real.log n := by
    rw [ha1, ha2, ha3]; linarith
  refine hsum6.trans ?_
  have ha10 : 0 ≤ a1 := by rw [ha1]; positivity
  have ha20 : 0 ≤ a2 := by rw [ha2]; positivity
  have ha30 : 0 ≤ a3 := by rw [ha3]; positivity
  nlinarith [mul_nonneg ha10 hlogq, mul_nonneg ha10 hlogn, mul_nonneg ha20 hX0,
    mul_nonneg ha20 hlogn, mul_nonneg ha30 hX0, mul_nonneg ha30 hlogq]


end LeanLab.BhowmikGrimmelt2026.Davenport636

#print axioms LeanLab.BhowmikGrimmelt2026.Davenport636.perron_half636

#print axioms LeanLab.BhowmikGrimmelt2026.Davenport636.good_height636

#print axioms LeanLab.BhowmikGrimmelt2026.Davenport636.contour636

#print axioms LeanLab.BhowmikGrimmelt2026.Davenport636.window636

#print axioms LeanLab.BhowmikGrimmelt2026.Davenport636.constant636

#print axioms LeanLab.BhowmikGrimmelt2026.Davenport636.formula636
