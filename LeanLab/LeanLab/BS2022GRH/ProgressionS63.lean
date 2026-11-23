/- AI wrote the Lean code, ROUTE BURST S63, burst-20261122, unit progression_at_endpoint.
Goldbach is open.

Split of `DecompC164a.progression_at_endpoint`, journal Lemma 3 p. 1216, into
* `ep2022_theorem1`, LEAF: Ernvall-Hytonen and Palojarvi, arXiv 2003.01925v4,
  Theorem 1 p. 2, in its published form and range, checked on the page image;
* `progression_at_endpoint_of_theorem1`, PROVED: the specialization q ≤ √x, which gives
  log q ≤ log x / 2 and φ(q) ≥ 2, turning the printed bound into qG x * √x * log x.
Theorem 1 needs x ≥ q; the journal statement has d ≤ √N with d ≥ 3, so N ≥ d ≥ q.
No range of N or d is left uncovered. -/
import LeanLab.BS2022GRH.ChenThresholdGRH
import LeanLab.BS2022GRH.ProgressionEPS70
import LeanLab.BS2022GRH.ProgressionWireS76
namespace LeanLab.BS2022GRH.ProgressionS63
open Real Finset Classical ChenThresholdGRH
noncomputable section

/-- Was a LEAF, split by S70 in ProgressionEPS70 along the paper's Section 4: journal Lemma 3 p. 1216, the cited input, Ernvall-Hytonen and Palojarvi 2022,
arXiv 2003.01925v4, Theorem 1 p. 2, in its published form and range: GRH, gcd(a, q) = 1,
q ≥ 3, real x ≥ q, strict bound with eight explicit terms. HARD, a citation proved in the
source from its Theorem 3 by partial summation. li is the principal value, `liPV`.
Natural a in place of integer a loses no residue class. -/
theorem ep2022_theorem1 (hG : GRH) (q a : ℕ) (x : ℝ)
    (ha : Nat.Coprime a q) (hq : 3 ≤ q) (hx : (q : ℝ) ≤ x) :
    |((((range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p % q = a % q)).card : ℕ) : ℝ)
        - liPV x / (q.totient : ℝ)| <
      (1 / (8 * π * (q.totient : ℝ)) + 1 / (6 * π)) * √x * log x
      + (0.184 * log q + 8.396) * √x
      + (6.05 * log q + 158.745) * √x / log x
      + (5.048 * log q ^ 2 + 152.085 * log q + 1731.270) * √x / log x ^ 2
      + (0.184 * log q + 8.250) * x ^ ((1 : ℝ) / 4) * log (log x)
      + (5.254 * log q ^ 2 + 121.765 * log q + 939.260) * x ^ ((1 : ℝ) / 4)
      + (80.768 * log q ^ 2 + 1753.168 * log q + 11605.056) * √x / log x ^ 3
      - 237.934 := by
  exact ProgressionWireS76.ep2022_theorem1_S76 hG q a x ha hq hx

set_option maxHeartbeats 1000000 in
/-- The specialization of journal Lemma 3 p. 1216: for 3 ≤ q ≤ √x the bound of
Theorem 1 is at most qG x * √x * log x. Uses log q ≤ log x / 2 and φ(q) ≥ 2. -/
theorem theorem1_bound_le_qG (q : ℕ) (x : ℝ) (hq : 3 ≤ q) (hqx : (q : ℝ) ≤ √x) :
      (1 / (8 * π * (q.totient : ℝ)) + 1 / (6 * π)) * √x * log x
      + (0.184 * log q + 8.396) * √x
      + (6.05 * log q + 158.745) * √x / log x
      + (5.048 * log q ^ 2 + 152.085 * log q + 1731.270) * √x / log x ^ 2
      + (0.184 * log q + 8.250) * x ^ ((1 : ℝ) / 4) * log (log x)
      + (5.254 * log q ^ 2 + 121.765 * log q + 939.260) * x ^ ((1 : ℝ) / 4)
      + (80.768 * log q ^ 2 + 1753.168 * log q + 11605.056) * √x / log x ^ 3
      - 237.934 ≤ qG x * √x * log x := by
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hs3 : (3 : ℝ) ≤ √x := hq3.trans hqx
  have hx0 : 0 < x := by
    by_contra h; push Not at h; rw [sqrt_eq_zero'.mpr h] at hs3; norm_num at hs3
  have hsx : √x * √x = x := mul_self_sqrt hx0.le
  have hx9 : 9 ≤ x := by nlinarith
  -- logarithms
  have hlog9 : (2 : ℝ) ≤ log 9 := by
    rw [le_log_iff_exp_le (by norm_num)]
    have h : exp (2 : ℝ) = exp 1 * exp 1 := by rw [← exp_add]; norm_num
    rw [h]
    nlinarith [exp_one_lt_d9, exp_pos (1 : ℝ)]
  set L := log x with hLdef
  have hL2 : 2 ≤ L := hlog9.trans (log_le_log (by norm_num) hx9)
  have hL0 : 0 < L := by linarith
  have hLL : 0 ≤ log L := log_nonneg (by linarith)
  set l := log (q : ℝ) with hldef
  have hl0 : 0 ≤ l := log_nonneg (by linarith)
  have hlL : l ≤ L / 2 := by
    have h1 : l ≤ log √x := log_le_log (by linarith) hqx
    have h2 : log √x = L / 2 := by rw [log_sqrt hx0.le]
    linarith
  -- totient
  have hphi : (2 : ℝ) ≤ (q.totient : ℝ) := by
    have he := Nat.totient_even (by omega : 2 < q)
    have hp := Nat.totient_pos.mpr (by omega : 0 < q)
    obtain ⟨k, hk⟩ := he
    have : 2 ≤ q.totient := by omega
    exact_mod_cast this
  have hpi := pi_gt_d2
  have hc1 : 1 / (8 * π * (q.totient : ℝ)) + 1 / (6 * π) ≤ 0.073 := by
    have h1 : 1 / (8 * π * (q.totient : ℝ)) ≤ 1 / (8 * π * 2) := by
      apply one_div_le_one_div_of_le (by positivity)
      have : 0 < 8 * π := by positivity
      nlinarith
    have h2 : 1 / (8 * π * 2) + 1 / (6 * π) = 11 / (48 * π) := by
      field_simp; ring
    have h3 : 11 / (48 * π) ≤ 0.073 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  -- powers
  set s := √x with hsdef
  set r := x ^ ((1 : ℝ) / 4) with hrdef
  have hr0 : 0 < r := rpow_pos_of_pos hx0 _
  have hsr : s = r * r := by
    rw [hsdef, hrdef, ← rpow_add hx0, sqrt_eq_rpow]; norm_num
  have hs0 : 0 < s := by linarith
  -- the expanded right side
  have key : qG x * s * L =
      0.165 * s * L + 12.683 * s + 254.980 * (s / L) + 2607.854 * (s / L ^ 2)
      + 11605.056 * (s / L ^ 3) + 1.314 * L ^ 2 * r + 0.092 * L * log L * r
      + 60.883 * L * r + 8.250 * log L * r + 939.260 * r - 237.934 := by
    unfold qG
    rw [← hLdef, ← hrdef, ← hsdef, hsr]
    field_simp
  rw [key]
  -- termwise comparisons
  set a1 := s / L with ha1
  set a2 := s / L ^ 2 with ha2
  set a3 := s / L ^ 3 with ha3
  clear_value a1 a2 a3 r s l L
  have ha1n : 0 ≤ a1 := by rw [ha1]; positivity
  have ha2n : 0 ≤ a2 := by rw [ha2]; positivity
  have ha3n : 0 ≤ a3 := by rw [ha3]; positivity
  have e1 : s = a1 * L := by rw [ha1]; field_simp
  have e2 : a1 = a2 * L := by rw [ha1, ha2]; field_simp
  have e3 : a2 = a3 * L := by rw [ha2, ha3]; field_simp
  have hdiv1 : (6.05 * l + 158.745) * s / L = 6.05 * l * a1 + 158.745 * a1 := by
    rw [ha1]; ring
  have hdiv2 : (5.048 * l ^ 2 + 152.085 * l + 1731.270) * s / L ^ 2
      = 5.048 * l ^ 2 * a2 + 152.085 * l * a2 + 1731.270 * a2 := by
    rw [ha2]; ring
  have hdiv3 : (80.768 * l ^ 2 + 1753.168 * l + 11605.056) * s / L ^ 3
      = 80.768 * l ^ 2 * a3 + 1753.168 * l * a3 + 11605.056 * a3 := by
    rw [ha3]; ring
  rw [hdiv1, hdiv2, hdiv3]
  have hll : l ^ 2 ≤ L ^ 2 / 4 := by nlinarith
  have t1 : (1 / (8 * π * (q.totient : ℝ)) + 1 / (6 * π)) * s * L ≤ 0.073 * s * L := by
    have : 0 ≤ s * L := by positivity
    nlinarith
  have t2 : l * s ≤ L / 2 * s := mul_le_mul_of_nonneg_right hlL hs0.le
  have t3 : l * a1 ≤ L / 2 * a1 := mul_le_mul_of_nonneg_right hlL ha1n
  have t4 : l ^ 2 * a2 ≤ L ^ 2 / 4 * a2 := mul_le_mul_of_nonneg_right hll ha2n
  have t5 : l * a2 ≤ L / 2 * a2 := mul_le_mul_of_nonneg_right hlL ha2n
  have t6 : l * (r * log L) ≤ L / 2 * (r * log L) :=
    mul_le_mul_of_nonneg_right hlL (by positivity)
  have t7 : l ^ 2 * r ≤ L ^ 2 / 4 * r := mul_le_mul_of_nonneg_right hll hr0.le
  have t8 : l * r ≤ L / 2 * r := mul_le_mul_of_nonneg_right hlL hr0.le
  have t9 : l ^ 2 * a3 ≤ L ^ 2 / 4 * a3 := mul_le_mul_of_nonneg_right hll ha3n
  have t10 : l * a3 ≤ L / 2 * a3 := mul_le_mul_of_nonneg_right hlL ha3n
  -- rewrite the L multiples back to the a's
  have u3 : L / 2 * a1 = s / 2 := by rw [e1]; ring
  have u4 : L ^ 2 / 4 * a2 = s / 4 := by rw [e1, e2]; ring
  have u5 : L / 2 * a2 = a1 / 2 := by rw [e2]; ring
  have u9 : L ^ 2 / 4 * a3 = a1 / 4 := by rw [e2, e3]; ring
  have u10 : L / 2 * a3 = a2 / 2 := by rw [e3]; ring
  have hLr : 0 ≤ L * r := by positivity
  have hL2r : 0 ≤ L ^ 2 * r := by positivity
  linear_combination t1 + 0.184 * t2 + 6.05 * t3 + 5.048 * t4 + 152.085 * t5 + 0.184 * t6
    + 5.254 * t7 + 121.765 * t8 + 80.768 * t9 + 1753.168 * t10 + 6.05 * u3 + 5.048 * u4
    + 152.085 * u5 + 80.768 * u9 + 1753.168 * u10 + 0.0005 * ha1n
    + 0.0005 * hLr + 0.0005 * hL2r

/-- The endpoint estimate of journal Lemma 3 p. 1216, CONDITIONAL ON the LEAF
`ep2022_theorem1`, with the statement of `DecompC164a.progression_at_endpoint`. -/
theorem progression_at_endpoint_of_theorem1 (hG : GRH) (d a : ℕ) (N : ℝ)
    (hd : 3 ≤ d) (hdN : (d : ℝ) ≤ √N) (ha : Nat.Coprime a d) :
    |((((range (⌊N⌋₊ + 1)).filter (fun p => p.Prime ∧ p % d = a % d)).card : ℕ) : ℝ)
        - liPV N / (d.totient : ℝ)| ≤ qG N * √N * log N := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hs3 : (3 : ℝ) ≤ √N := hd3.trans hdN
  have hN0 : 0 < N := by
    by_contra h; push Not at h; rw [sqrt_eq_zero'.mpr h] at hs3; norm_num at hs3
  have hsN : √N ≤ N := by
    have h := mul_self_sqrt hN0.le
    nlinarith
  have hdx : (d : ℝ) ≤ N := hdN.trans hsN
  exact (ep2022_theorem1 hG d a N ha hd hdx).le.trans (theorem1_bound_le_qG d N hd hdN)

end
end LeanLab.BS2022GRH.ProgressionS63
#print axioms LeanLab.BS2022GRH.ProgressionS63.theorem1_bound_le_qG
#print axioms LeanLab.BS2022GRH.ProgressionS63.progression_at_endpoint_of_theorem1
