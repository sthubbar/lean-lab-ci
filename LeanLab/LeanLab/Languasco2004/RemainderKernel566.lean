/-
Jia 1996 pages 271 to 273, polynomial minorants for the remainder of group 1.
Source https://doi.org/10.4064/aa-77-3-207-287.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.RemainderData566
import LeanLab.Languasco2004.Midpoint566

namespace LeanLab.Languasco2004.RemainderKernel566
open Real Set intervalIntegral RemainderData566 Numeric548 Numeric30_548 Midpoint566
noncomputable section
set_option maxHeartbeats 0

/-- Pages 271 to 273: rational midpoint centres for the three positive reciprocals. -/
def centres : Fin 25 → Fin 3 → ℚ :=
  ![![629/2052, 763/3762, 1729/3564],
    ![629/2052, 743/3078, 7393/16416],
    ![2635/8316, 713/3564, 149/308],
    ![2635/8316, 5315/22176, 1579/3564],
    ![409/1260, 829/4158, 184/385],
    ![409/1260, 823/3465, 3673/8316],
    ![73/220, 391/1980, 311/660],
    ![73/220, 229/990, 289/660],
    ![301/900, 13/66, 31/66],
    ![3361/9900, 101/528, 18581/39600],
    ![3361/9900, 6439/29700, 131/297],
    ![3361/9900, 25/108, 12703/29700],
    ![547/1584, 1783/9408, 13075/28224],
    ![341/976, 5003/26352, 1513/3294],
    ![341/976, 2027/8784, 91/216],
    ![1189/3294, 12184/80703, 1697/3528],
    ![1189/3294, 2461/13176, 4477/9882],
    ![1189/3294, 11083/49410, 3467/8235],
    ![1217/3240, 22609/158760, 101191/211680],
    ![1217/3240, 2363/12960, 289/648],
    ![36139/93960, 1771/12960, 9937/20880],
    ![36139/93960, 33101/187920, 5729/12960],
    ![610787/1519020, 8501/62640, 6549/14065],
    ![610787/1519020, 166183/995220, 525113/1190160],
    ![645319/1519020, 6929/52380, 23671/52380]]

/-- LEAF. Pages 271 to 273: every source point lies in the midpoint enclosure domain. -/
theorem enclosure_domain (i : Fin 25) (t u : ℝ)
    (htl : (data i 0 : ℝ) ≤ t) (htu : t ≤ (data i 1 : ℝ))
    (hul : (data i 2 : ℝ) * t + data i 3 ≤ u)
    (huu : u ≤ (data i 4 : ℝ) * t + data i 5) :
    0 < t ∧ 0 < u ∧ 0 < 1 - t - u ∧
      0 < (centres i 0 : ℝ) ∧ 0 < (centres i 1 : ℝ) ∧ 0 < (centres i 2 : ℝ) ∧
      t ≤ 2 * (centres i 0 : ℝ) ∧ u ≤ 2 * (centres i 1 : ℝ) ∧
      1 - t - u ≤ 2 * (centres i 2 : ℝ) ∧
      (data i 6 = 1 → 0 ≤ 1 - t - 3 * u) := by
  fin_cases i <;> norm_num [data, centres] at *
  all_goals
    repeat' apply And.intro
    all_goals linarith

/-- Pages 271 to 273: the polynomial lower kernel for each of the 25 source terms. -/
def polynomial (i : Fin 25) (t u : ℝ) : ℝ :=
  let pt := invPoly3 t (centres i 0 : ℝ)
  let pu := invPoly5 u (centres i 1 : ℝ)
  let pv := invPoly3 (1 - t - u) (centres i 2 : ℝ)
  let z := (1 - t - 3 * u) * pv
  let zh := (1 - t - 3 * u) * invPoly1 (1 - t - u) (centres i 2 : ℝ)
  if data i 6 = 2 then 0.5607 * pt * pu ^ 2
  else if data i 6 = 1 then pt * pu * pv * (1 + 2 * z + 2 / 3 * z ^ 3 + 2 / 5 * zh ^ 5 + 2 / 7 * zh ^ 7)
  else pt * pu * pv

/-- Pages 271 to 273: the polynomial double integral keeps the exact source endpoints. -/
def polynomialTerm (i : Fin 25) : ℝ :=
  ∫ t in (data i 0 : ℝ)..(data i 1 : ℝ),
    ∫ u in ((data i 2 : ℝ) * t + data i 3)..((data i 4 : ℝ) * t + data i 5), polynomial i t u

/-- LEAF. Pages 271 to 273: the pointwise comparison for all 25 source kernels. -/
theorem polynomial_le (i : Fin 25) (t u : ℝ)
    (htl : (data i 0 : ℝ) ≤ t) (htu : t ≤ (data i 1 : ℝ))
    (hul : (data i 2 : ℝ) * t + data i 3 ≤ u)
    (huu : u ≤ (data i 4 : ℝ) * t + data i 5) :
    polynomial i t u ≤ kernel i t u := by
  obtain ⟨ht, hu, hv, ct, cu, cv, htU, huU, hvU, hw⟩ := enclosure_domain i t u htl htu hul huu
  obtain ⟨pt0, pt⟩ := invPoly3_midpoint t (centres i 0 : ℝ) ht ct htU
  obtain ⟨pu0, pu⟩ := invPoly5_midpoint u (centres i 1 : ℝ) hu cu huU
  obtain ⟨pv0, pv⟩ := invPoly3_midpoint (1 - t - u) (centres i 2 : ℝ) hv cv hvU
  have hp := mul_le_mul (mul_le_mul pt pu pu0 (by positivity : (0 : ℝ) ≤ 1 / t))
    pv pv0 (by positivity : (0 : ℝ) ≤ 1 / t * (1 / u))
  unfold polynomial kernel
  dsimp only
  split_ifs with htwo hone
  · have hp2 : invPoly5 u (centres i 1 : ℝ)^2 ≤ (1 / u)^2 := by nlinarith
    have hm := mul_le_mul pt hp2 (sq_nonneg _) (by positivity : (0 : ℝ) ≤ 1 / t)
    have hm' := mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 0.5607)
    convert hm' using 1 <;> (try simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]) <;> ring
  · have hw0 := hw hone
    have hz := mul_le_mul_of_nonneg_left pv hw0
    have hz0 : 0 ≤ (1 - t - 3 * u) * invPoly3 (1 - t - u) (centres i 2 : ℝ) := mul_nonneg hw0 pv0
    have hz3 := pow_le_pow_left₀ hz0 hz 3
    obtain ⟨pl0, pl⟩ := invPoly1_midpoint (1 - t - u) (centres i 2 : ℝ) hv cv hvU
    have hzh := mul_le_mul_of_nonneg_left pl hw0
    have hzh0 : 0 ≤ (1 - t - 3 * u) * invPoly1 (1 - t - u) (centres i 2 : ℝ) := mul_nonneg hw0 pl0
    have hz5 := pow_le_pow_left₀ hzh0 hzh 5
    have hz7 := pow_le_pow_left₀ hzh0 hzh 7
    have hy : 1 ≤ (1 - t) / u - 2 := by
      apply (le_sub_iff_add_le).mpr
      apply (le_div_iff₀ hu).mpr
      linarith
    have he : (((1 - t) / u - 2) - 1) / (((1 - t) / u - 2) + 1) =
        (1 - t - 3 * u) * (1 / (1 - t - u)) := by
      have hd : (1 - t) / u - 2 + 1 ≠ 0 := by linarith
      apply (div_eq_iff hd).mpr
      field_simp [hu.ne', hv.ne']
      <;> ring
    have hl := log_odd_seven_lower ((1 - t) / u - 2) hy
    rw [he] at hl
    have hn : 1 + 2 * ((1 - t - 3 * u) * invPoly3 (1 - t - u) (centres i 2 : ℝ)) +
        2 / 3 * ((1 - t - 3 * u) * invPoly3 (1 - t - u) (centres i 2 : ℝ)) ^ 3 +
        2 / 5 * ((1 - t - 3 * u) * invPoly1 (1 - t - u) (centres i 2 : ℝ)) ^ 5 +
        2 / 7 * ((1 - t - 3 * u) * invPoly1 (1 - t - u) (centres i 2 : ℝ)) ^ 7 ≤
        1 + Real.log ((1 - t) / u - 2) := by linarith
    have hn0 : 0 ≤ 1 + 2 * ((1 - t - 3 * u) * invPoly3 (1 - t - u) (centres i 2 : ℝ)) +
        2 / 3 * ((1 - t - 3 * u) * invPoly3 (1 - t - u) (centres i 2 : ℝ)) ^ 3 +
        2 / 5 * ((1 - t - 3 * u) * invPoly1 (1 - t - u) (centres i 2 : ℝ)) ^ 5 +
        2 / 7 * ((1 - t - 3 * u) * invPoly1 (1 - t - u) (centres i 2 : ℝ)) ^ 7 := by positivity
    have hm := mul_le_mul hp hn hn0
      (by positivity : (0 : ℝ) ≤ 1 / t * (1 / u) * (1 / (1 - t - u)))
    convert hm using 1 <;> (try simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]) <;> ring
  · convert hp using 1 <;> (try simp only [one_div, mul_inv_rev, inv_pow]) <;> ring

#print axioms enclosure_domain
#print axioms polynomial_le
end
end LeanLab.Languasco2004.RemainderKernel566
