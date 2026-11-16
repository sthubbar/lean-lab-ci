/-
P0069, Section 5, pages 50 and 51, displays 5.15 and 5.17.
The E4 integer quadrature is split into its four coordinate estimates.
Each coordinate estimate saves x to the power minus one over one hundred.
All four coordinate estimates are proved with only the allowed axioms.
The mesh lower cutoff saves x to the power minus eleven over two hundred,
so the stated rate leaves room for the boundary and logarithmic factors.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.FourExponentRemaining517

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d
open scoped BigOperators

/-- LEAF: P0069 page 51 display 5.17, the d coordinate of the E4 quadrature.
The full strict fibre estimate and three outer weight contractions prove
this coordinate replacement, including every boundary and the Buchstab jump.
The build and allowed axioms are recorded in build/codex-task629.log. -/
theorem leaf_four_exponent_coordinate_d (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x : ℝ, C ≤ x → ∀ m : ℕ,
      ⌊x ^ (11 / 20 + ε)⌋₊ < m → m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |fourExponentMixed ω ε x (Real.log (m : ℝ) / Real.log (scaleZ ε x)) 0 -
        fourExponentMixed ω ε x (Real.log (m : ℝ) / Real.log (scaleZ ε x)) 1| ≤
          C * x ^ (-(1/100) : ℝ) := by
  obtain ⟨Cs, hCs, hscale⟩ := four_exponent_scale_data hε hε8
  refine ⟨max Cs 6403200000, by linarith [le_max_right Cs 6403200000], fun x hx m hm1 hm2 => ?_⟩
  obtain ⟨hx1, hL, hLN, hZ, hlog1, hNZ, hlo, hhi, herr⟩ :=
    hscale x ((le_max_left Cs 6403200000).trans hx)
  let L := ⌊x ^ (11/200 : ℝ) / 2⌋₊
  let N := ⌊2*x ^ (11/20+ε)⌋₊
  let Z := scaleZ ε x
  let B := Finset.Icc 1 N
  let w := fun n : ℕ => 1 / ((n : ℝ)*Real.log Z)
  let e := expo ε x
  let s := Real.log (m : ℝ) / Real.log Z
  let E := (200100000 : ℝ) / ((L : ℝ)*Real.log Z)
  let F := fun a b c : ℕ => if b < a ∧ c < b then
    (∑ d ∈ B, if d < c then fourExponentKernel ω ε s (e a) (e b) (e c) (e d) * w d else 0) -
      ∫ d in lowerFourGridReal 0..lowerFourGridReal 128,
        fourExponentKernel ω ε s (e a) (e b) (e c) d
    else 0
  have hLp : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hlog : 0 < Real.log Z := Real.log_pos hZ
  have hE : 0 ≤ E := by positivity
  have hs := four_exponent_short_range hε hx1 hm1 hm2
  have hpt : ∀ a ∈ B, ∀ b ∈ B, ∀ c ∈ B, |F a b c| ≤ E := by
    intro a ha b hb c hc
    dsimp only [F]
    by_cases horder : b < a ∧ c < b
    · rw [if_pos horder]
      have h := four_exponent_kernel_strict_grid_d hω hz hε hε8 hs.1 hs.2 hZ
        (e a) (e b) L N c hL hLN hc hNZ hlo hhi
      simpa only [e, expo, w, mul_one_div] using h
    · rw [if_neg horder, abs_zero]
      exact hE
  have hw : ∀ n ∈ B, 0 ≤ w n := by
    intro n hn
    dsimp only [w]
    positivity
  have hW : ∑ n ∈ B, w n ≤ 2 := four_exponent_weight_mass hZ hlog1 N (by linarith)
  have contract : ∀ (G : ℕ → ℝ) (T : ℝ), 0 ≤ T → (∀ n ∈ B, |G n| ≤ T) →
      |∑ n ∈ B, w n * G n| ≤ 2*T := by
    intro G T hT hG
    calc _ ≤ ∑ n ∈ B, |w n * G n| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ B, w n * T := by
        apply Finset.sum_le_sum
        intro n hn
        rw [abs_mul, abs_of_nonneg (hw n hn)]
        exact mul_le_mul_of_nonneg_left (hG n hn) (hw n hn)
      _ = (∑ n ∈ B, w n)*T := (Finset.sum_mul _ _ _).symm
      _ ≤ 2*T := mul_le_mul_of_nonneg_right hW hT
  have hc : ∀ a ∈ B, ∀ b ∈ B, |∑ c ∈ B, w c * F a b c| ≤ 2*E := by
    intro a ha b hb
    exact contract (F a b) E hE (hpt a ha b hb)
  have hb : ∀ a ∈ B, |∑ b ∈ B, w b * (∑ c ∈ B, w c * F a b c)| ≤ 2*(2*E) := by
    intro a ha
    exact contract _ (2*E) (by positivity) (hc a ha)
  have ht := contract (fun a => ∑ b ∈ B, w b * (∑ c ∈ B, w c * F a b c))
    (2*(2*E)) (by positivity) hb
  have hdifference : fourExponentMixed ω ε x s 0 - fourExponentMixed ω ε x s 1 =
      ∑ a ∈ B, w a * (∑ b ∈ B, w b * (∑ c ∈ B, w c * F a b c)) := by
    rw [four_exponent_mixed_zero_fibres, four_exponent_mixed_one_fibres]
    dsimp only
    simp only [Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c hc
    dsimp only [F, B, N, w, e, Z]
    by_cases horder : b < a ∧ c < b <;> simp [horder] <;> ring
  change |fourExponentMixed ω ε x s 0 - fourExponentMixed ω ε x s 1| ≤ _
  rw [hdifference]
  calc _ ≤ 8*E := by nlinarith [ht]
    _ ≤ 6403200000*x ^ (-(11/200) : ℝ) := by
      have h := mul_le_mul_of_nonneg_left herr (by norm_num : (0 : ℝ) ≤ 8*200100000)
      dsimp only [E]
      convert h using 1 <;> ring
    _ ≤ 6403200000*x ^ (-(1/100) : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)) (by norm_num)
    _ ≤ max Cs 6403200000 * x ^ (-(1/100) : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_right Cs 6403200000) (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x) _)

/-- LEAF: P0069 page 51 display 5.17, the c coordinate of the E4 quadrature.
Replace the innermost remaining integer sum by its exponent integral.
Bound the smooth cells by the mesh estimates and the boundary cells by
four_region_jumps and the Buchstab jump hyperplane. PROVED. -/
theorem leaf_four_exponent_coordinate_c (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x : ℝ, C ≤ x → ∀ m : ℕ,
      ⌊x ^ (11 / 20 + ε)⌋₊ < m → m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |fourExponentMixed ω ε x (Real.log (m : ℝ) / Real.log (scaleZ ε x)) 1 -
        fourExponentMixed ω ε x (Real.log (m : ℝ) / Real.log (scaleZ ε x)) 2| ≤
          C * x ^ (-(1/100) : ℝ) := by
  obtain ⟨Cs, hCs, hscale⟩ := four_exponent_scale_data hε hε8
  refine ⟨max Cs 6403200000, by linarith [le_max_right Cs 6403200000], fun x hx m hm1 hm2 => ?_⟩
  obtain ⟨hx1, hL, hLN, hZ, hlog1, hNZ, hlo, hhi, herr⟩ :=
    hscale x ((le_max_left Cs 6403200000).trans hx)
  let L := ⌊x ^ (11/200 : ℝ) / 2⌋₊
  let N := ⌊2*x ^ (11/20+ε)⌋₊
  let Z := scaleZ ε x
  let B := Finset.Icc 1 N
  let w := fun n : ℕ => 1 / ((n : ℝ)*Real.log Z)
  let e := expo ε x
  let s := Real.log (m : ℝ) / Real.log Z
  let E := (200100000 : ℝ) / ((L : ℝ)*Real.log Z)
  have hLp : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hlog : 0 < Real.log Z := Real.log_pos hZ
  have hE : 0 ≤ E := by positivity
  let F := fun a b : ℕ => if b < a then
    (∑ c ∈ B, if c < b then fourExponentInnerOne ω ε s (e a) (e b) (e c)*w c else 0) -
      fourExponentInnerTwo ω ε s (e a) (e b) else 0
  have hpt : ∀ a ∈ B, ∀ b ∈ B, |F a b| ≤ E := by
    intro a ha b hb
    dsimp only [F]
    by_cases hba : b < a
    · rw [if_pos hba]
      have hq := four_exponent_function_strict_grid (fourExponentInnerOne ω ε s (e a) (e b))
        ((four_exponent_inner_one_props hω hz hε hε8 s).2 (e a) (e b))
        (fun l r => four_exponent_inner_one_integrable hω hz hε hε8 s (e a) (e b) l r)
        (four_exponent_inner_one_variation hω hz hε hε8 s (e a) (e b))
        (fun t ht => four_exponent_inner_one_support hε hε8 s (e a) (e b) t ht)
        hZ L N b hL hLN hb hNZ hlo hhi
        (fun t ht => four_exponent_inner_one_order ε s (e a) (e b) t ht)
      simpa only [w, mul_one_div, e, expo, fourExponentInnerTwo] using hq
    · rw [if_neg hba, abs_zero]
      exact hE
  have hw : ∀ n ∈ B, 0 ≤ w n := by intro n hn; dsimp only [w]; positivity
  have hW : ∑ n ∈ B, w n ≤ 2 := four_exponent_weight_mass hZ hlog1 N (by linarith)
  have hb : ∀ a ∈ B, |∑ b ∈ B, w b*F a b| ≤ 2*E := by
    intro a ha
    exact four_exponent_weight_contraction B w (F a) hE hw hW (hpt a ha)
  have ht := four_exponent_weight_contraction B w
    (fun a => ∑ b ∈ B, w b*F a b) (by positivity : 0 ≤ 2*E) hw hW hb
  have hdifference : fourExponentMixed ω ε x s 1-fourExponentMixed ω ε x s 2 =
      ∑ a ∈ B, w a*(∑ b ∈ B, w b*F a b) := four_exponent_mixed_c_difference ω ε x s
  change |fourExponentMixed ω ε x s 1-fourExponentMixed ω ε x s 2| ≤ _
  rw [hdifference]
  calc _ ≤ 8*E := by nlinarith [ht]
    _ ≤ 6403200000*x ^ (-(11/200) : ℝ) := by
      have h := mul_le_mul_of_nonneg_left herr (by norm_num : (0 : ℝ) ≤ 8*200100000)
      dsimp only [E]
      convert h using 1 <;> ring
    _ ≤ 6403200000*x ^ (-(1/100) : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)) (by norm_num)
    _ ≤ max Cs 6403200000 * x ^ (-(1/100) : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_right Cs 6403200000)
        (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x) _)

/-- LEAF: P0069 page 51 display 5.17, the b coordinate of the E4 quadrature.
Replace the innermost remaining integer sum by its exponent integral.
Bound the smooth cells by the mesh estimates and the boundary cells by
four_region_jumps and the Buchstab jump hyperplane. PROVED. -/
theorem leaf_four_exponent_coordinate_b (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x : ℝ, C ≤ x → ∀ m : ℕ,
      ⌊x ^ (11 / 20 + ε)⌋₊ < m → m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |fourExponentMixed ω ε x (Real.log (m : ℝ) / Real.log (scaleZ ε x)) 2 -
        fourExponentMixed ω ε x (Real.log (m : ℝ) / Real.log (scaleZ ε x)) 3| ≤
          C * x ^ (-(1/100) : ℝ) := by
  obtain ⟨Cs, hCs, hscale⟩ := four_exponent_scale_data hε hε8
  refine ⟨max Cs 6403200000, by linarith [le_max_right Cs 6403200000], fun x hx m hm1 hm2 => ?_⟩
  obtain ⟨hx1, hL, hLN, hZ, hlog1, hNZ, hlo, hhi, herr⟩ :=
    hscale x ((le_max_left Cs 6403200000).trans hx)
  let L := ⌊x ^ (11/200 : ℝ) / 2⌋₊
  let N := ⌊2*x ^ (11/20+ε)⌋₊
  let Z := scaleZ ε x
  let B := Finset.Icc 1 N
  let w := fun n : ℕ => 1 / ((n : ℝ)*Real.log Z)
  let e := expo ε x
  let s := Real.log (m : ℝ) / Real.log Z
  let E := (200100000 : ℝ) / ((L : ℝ)*Real.log Z)
  have hLp : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hlog : 0 < Real.log Z := Real.log_pos hZ
  have hE : 0 ≤ E := by positivity
  let F := fun a : ℕ =>
    (∑ b ∈ B, if b < a then fourExponentInnerTwo ω ε s (e a) (e b)*w b else 0) -
      fourExponentInnerThree ω ε s (e a)
  have hpt : ∀ a ∈ B, |F a| ≤ E := by
    intro a ha
    have hq := four_exponent_function_strict_grid (fourExponentInnerTwo ω ε s (e a))
      ((four_exponent_inner_two_props hω hz hε hε8 s).2 (e a))
      (fun l r => four_exponent_inner_two_integrable hω hz hε hε8 s (e a) l r)
      (four_exponent_inner_two_variation hω hz hε hε8 s (e a))
      (fun t ht => four_exponent_inner_two_support hε hε8 s (e a) t ht)
      hZ L N a hL hLN ha hNZ hlo hhi
      (fun t ht => four_exponent_inner_two_order ε s (e a) t ht)
    simpa only [F, w, mul_one_div, e, expo, fourExponentInnerThree] using hq
  have hw : ∀ n ∈ B, 0 ≤ w n := by intro n hn; dsimp only [w]; positivity
  have hW : ∑ n ∈ B, w n ≤ 2 := four_exponent_weight_mass hZ hlog1 N (by linarith)
  have ht := four_exponent_weight_contraction B w F hE hw hW hpt
  have hdifference : fourExponentMixed ω ε x s 2-fourExponentMixed ω ε x s 3 =
      ∑ a ∈ B, w a*F a := four_exponent_mixed_b_difference ω ε x s
  change |fourExponentMixed ω ε x s 2-fourExponentMixed ω ε x s 3| ≤ _
  rw [hdifference]
  calc _ ≤ 8*E := by nlinarith [ht]
    _ ≤ 6403200000*x ^ (-(11/200) : ℝ) := by
      have h := mul_le_mul_of_nonneg_left herr (by norm_num : (0 : ℝ) ≤ 8*200100000)
      dsimp only [E]
      convert h using 1 <;> ring
    _ ≤ 6403200000*x ^ (-(1/100) : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)) (by norm_num)
    _ ≤ max Cs 6403200000 * x ^ (-(1/100) : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_right Cs 6403200000)
        (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x) _)

/-- LEAF: P0069 page 51 display 5.17, the a coordinate of the E4 quadrature.
Replace the innermost remaining integer sum by its exponent integral.
Bound the smooth cells by the mesh estimates and the boundary cells by
four_region_jumps and the Buchstab jump hyperplane. PROVED. -/
theorem leaf_four_exponent_coordinate_a (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x : ℝ, C ≤ x → ∀ m : ℕ,
      ⌊x ^ (11 / 20 + ε)⌋₊ < m → m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |fourExponentMixed ω ε x (Real.log (m : ℝ) / Real.log (scaleZ ε x)) 3 -
        fourExponentMixed ω ε x (Real.log (m : ℝ) / Real.log (scaleZ ε x)) 4| ≤
          C * x ^ (-(1/100) : ℝ) := by
  obtain ⟨Cs, hCs, hscale⟩ := four_exponent_scale_data hε hε8
  refine ⟨max Cs 6403200000, by linarith [le_max_right Cs 6403200000], fun x hx m hm1 hm2 => ?_⟩
  obtain ⟨hx1, hL, hLN, hZ, hlog1, hNZ, hlo, hhi, herr⟩ :=
    hscale x ((le_max_left Cs 6403200000).trans hx)
  let L := ⌊x ^ (11/200 : ℝ) / 2⌋₊
  let N := ⌊2*x ^ (11/20+ε)⌋₊
  let Z := scaleZ ε x
  let B := Finset.Icc 1 N
  let w := fun n : ℕ => 1 / ((n : ℝ)*Real.log Z)
  let e := expo ε x
  let s := Real.log (m : ℝ) / Real.log Z
  let E := (200100000 : ℝ) / ((L : ℝ)*Real.log Z)
  have hLp : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hlog : 0 < Real.log Z := Real.log_pos hZ
  have hE : 0 ≤ E := by positivity
  have hq := four_exponent_function_full_grid (fourExponentInnerThree ω ε s)
    ((four_exponent_inner_three_props hω hz hε hε8 s).2)
    (fun l r => four_exponent_inner_three_integrable hω hz hε hε8 s l r)
    (four_exponent_inner_three_variation hω hz hε hε8 s)
    (fun t ht => four_exponent_inner_three_support hε hε8 s t ht)
    hZ L N hL hLN hNZ hlo hhi
  have hbound : |(∑ a ∈ B, fourExponentInnerThree ω ε s (e a)*w a) -
      ∫ a in lowerFourGridReal 0..lowerFourGridReal 128, fourExponentInnerThree ω ε s a| ≤ E := by
    have he := hq.trans (show 200000000 / ((L : ℝ)*Real.log Z) ≤ E from
      div_le_div_of_nonneg_right (by norm_num) (by positivity))
    simpa only [w, mul_one_div, e, expo] using he
  change |fourExponentMixed ω ε x s 3-fourExponentMixed ω ε x s 4| ≤ _
  rw [four_exponent_mixed_a_difference]
  calc _ ≤ 8*E := by nlinarith [hbound]
    _ ≤ 6403200000*x ^ (-(11/200) : ℝ) := by
      have h := mul_le_mul_of_nonneg_left herr (by norm_num : (0 : ℝ) ≤ 8*200100000)
      dsimp only [E]
      convert h using 1 <;> ring
    _ ≤ 6403200000*x ^ (-(1/100) : ℝ) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)) (by norm_num)
    _ ≤ max Cs 6403200000 * x ^ (-(1/100) : ℝ) :=
      mul_le_mul_of_nonneg_right (le_max_right Cs 6403200000)
        (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ x) _)

/-- Page 51 display 5.17. Four coordinate errors telescope.
All four coordinate leaves are proved. -/
theorem four_exponent_quadrature_power (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x : ℝ, C ≤ x → ∀ m : ℕ,
      ⌊x ^ (11 / 20 + ε)⌋₊ < m → m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |fourExponentMixed ω ε x (Real.log (m : ℝ) / Real.log (scaleZ ε x)) 0 -
        lowerFourDensityAt ω ε (Real.log (m : ℝ) / Real.log (scaleZ ε x))| ≤
          C * x ^ (-(1/100) : ℝ) := by
  obtain ⟨Cd, hCd, hd⟩ := leaf_four_exponent_coordinate_d ω hω hz hε hε8
  obtain ⟨Cc, hCc, hc⟩ := leaf_four_exponent_coordinate_c ω hω hz hε hε8
  obtain ⟨Cb, hCb, hb⟩ := leaf_four_exponent_coordinate_b ω hω hz hε hε8
  obtain ⟨Ca, hCa, ha⟩ := leaf_four_exponent_coordinate_a ω hω hz hε hε8
  refine ⟨Cd + Cc + Cb + Ca, by linarith, fun x hx m hm1 hm2 => ?_⟩
  have ed := hd x (by linarith) m hm1 hm2
  have ec := hc x (by linarith) m hm1 hm2
  have eb := hb x (by linarith) m hm1 hm2
  have ea := ha x (by linarith) m hm1 hm2
  have h4 : fourExponentMixed ω ε x (Real.log (m : ℝ) / Real.log (scaleZ ε x)) 4 =
      lowerFourDensityAt ω ε (Real.log (m : ℝ) / Real.log (scaleZ ε x)) := rfl
  rw [← h4]
  have telescope : ∀ q : ℕ → ℝ,
      |q 0 - q 4| ≤ |q 0 - q 1| + |q 1 - q 2| + |q 2 - q 3| + |q 3 - q 4| := by
    intro q
    linarith [abs_sub_le (q 0) (q 1) (q 4),
      abs_sub_le (q 1) (q 2) (q 4), abs_sub_le (q 2) (q 3) (q 4)]
  refine (telescope _).trans ?_
  calc _ ≤ Cd * x ^ (-(1/100) : ℝ) + Cc * x ^ (-(1/100) : ℝ) +
        Cb * x ^ (-(1/100) : ℝ) + Ca * x ^ (-(1/100) : ℝ) :=
          add_le_add (add_le_add (add_le_add ed ec) eb) ea
    _ = _ := by ring

#print axioms leaf_four_exponent_coordinate_d
#print axioms leaf_four_exponent_coordinate_c
#print axioms leaf_four_exponent_coordinate_b
#print axioms leaf_four_exponent_coordinate_a
#print axioms four_exponent_quadrature_power
end LeanLab.BHP1997.LowerShortC165
