import LeanLab.ChenDoubleSieve.Discretization
import LeanLab.ChenDoubleSieve.Xi2Signs
import LeanLab.ChenDoubleSieve.NormalizerPositive

/-!
Elementary inputs for Wu 2004 displays 3.21 and 3.22 and the last display of page 31.
Source: https://arxiv.org/abs/0705.1652, pages 9, 14, 15, 30 and 31.
Eighteen declarations moved from Burst8P2 with identical statements and proofs.
AI wrote the Lean code. Binary Goldbach is open.
-/
set_option maxHeartbeats 1000000
noncomputable section
open Real Set MeasureTheory
namespace LeanLab.ChenDoubleSieve.Burst8P2
open Wu04Functional
open Wu04Integral (sigma0)

/-- A summand `1_{[a,b]}(t) / D(t) · log G(t)` of Wu's kernels on page 14 is integrable on
`[1, 3]` when `D` and `G` are continuous and nonzero on the support. -/
theorem ind_log_integrable {a b : ℝ} {D G : ℝ → ℝ}
    (hD : ContinuousOn D (Icc a b ∩ Icc 1 3)) (hD0 : ∀ t ∈ Icc a b ∩ Icc 1 3, D t ≠ 0)
    (hG : ContinuousOn G (Icc a b ∩ Icc 1 3)) (hG0 : ∀ t ∈ Icc a b ∩ Icc 1 3, G t ≠ 0) :
    IntervalIntegrable (fun t => ind a b t / D t * log (G t)) volume 1 3 := by
  have he : (fun t => ind a b t / D t * log (G t)) =
      (Icc a b).indicator (fun t => log (G t) / D t) := by
    funext t
    by_cases h : a ≤ t ∧ t ≤ b
    · rw [ind, if_pos h, indicator_of_mem (show t ∈ Icc a b from h)]; ring
    · rw [ind, if_neg h, indicator_of_notMem (show t ∉ Icc a b from h)]; ring
  rw [he, intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num : (1 : ℝ) ≤ 3),
    IntegrableOn, integrable_indicator_iff measurableSet_Icc, IntegrableOn,
    Measure.restrict_restrict measurableSet_Icc]
  exact ((hG.log hG0).div hD hD0).integrableOn_compact (isCompact_Icc.inter isCompact_Icc)

/-- The `σ₀` summand of the kernels on page 14 is integrable on `[1, 3]`, since `σ₀` is
increasing there, `Wu04Integral.sigma0_mono`. -/
theorem sigma_term_integrable (c L : ℝ) (hc : 0 < c) :
    IntervalIntegrable (fun t => Wu04Integral.sigma0 t / (c * t) * L) volume 1 3 := by
  have hm : IntervalIntegrable Wu04Integral.sigma0 volume 1 3 := by
    apply MonotoneOn.intervalIntegrable
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)]
    exact Wu04Integral.sigma0_mono.mono (fun t ht => mem_Ici.2 ht.1)
  have hg : ContinuousOn (fun t : ℝ => L / (c * t)) (uIcc 1 3) := by
    apply continuousOn_const.div (continuousOn_const.mul continuousOn_id)
    intro t ht
    rw [uIcc_of_le (by norm_num : (1 : ℝ) ≤ 3)] at ht
    show c * t ≠ 0
    exact (mul_pos hc (show (0 : ℝ) < t by linarith [ht.1])).ne'
  have he : (fun t => Wu04Integral.sigma0 t / (c * t) * L) =
      fun t => Wu04Integral.sigma0 t * (L / (c * t)) := by
    funext t; ring
  rw [he]
  exact hm.mul_continuousOn hg

/-- `Ξ₁(·; s, s')` of display 3.21, page 14, is integrable on `[1, 3]` on the full parameter
range of Proposition 3. -/
theorem Xi1_integrable {s sp : ℝ} (hp : Admissible3 s sp) :
    IntervalIntegrable (Xi1 s sp) volume 1 3 := by
  obtain ⟨hs2, hs3, hsp3, hsp5, hss⟩ := hp
  have h1 := sigma_term_integrable 2 (log (16 / ((s - 1) * (sp - 1)))) (by norm_num)
  have h2 : IntervalIntegrable (fun t => ind (sp - 2) 3 t / (2 * t) *
      log ((t + 1) ^ 2 / ((s - 1) * (sp - 1)))) volume 1 3 := by
    apply ind_log_integrable
    · fun_prop
    · intro t ht; exact (show (0 : ℝ) < 2 * t by linarith [ht.2.1]).ne'
    · fun_prop
    · intro t ht
      have h0 : (0 : ℝ) < (s - 1) * (sp - 1) := mul_pos (by linarith) (by linarith)
      exact (div_pos (by nlinarith [ht.2.1]) h0).ne'
  have h3 : IntervalIntegrable (fun t => ind (sp - sp / s - 1) (sp - 2) t / (2 * t) *
      log ((t + 1) / ((s - 1) * (sp - 1 - t)))) volume 1 3 := by
    apply ind_log_integrable
    · fun_prop
    · intro t ht; exact (show (0 : ℝ) < 2 * t by linarith [ht.2.1]).ne'
    · apply ContinuousOn.div (by fun_prop) (by fun_prop)
      intro t ht
      exact (mul_pos (by linarith) (by linarith [ht.1.2])).ne'
    · intro t ht
      have h0 : (0 : ℝ) < (s - 1) * (sp - 1 - t) := mul_pos (by linarith) (by linarith [ht.1.2])
      exact (div_pos (by linarith [ht.2.1]) h0).ne'
  exact (h1.add h2).add h3

/-- The sign conditions of `Wu04Functional.tableXi2_log_signs`, which Wu 2004 obtains for the
four Table 1 rows: on each support interval of display 3.22 the denominator of the logarithm is
positive and at most its numerator. PROVED from `tableXi2_log_signs`, no new definition. -/
theorem tableParams_Xi2Signs (i : Fin 4) :
  ∀ t ∈ Icc (1 : ℝ) 3,
    let a := alpha (tableParams i)
    let P := ((tableParams i).s-1)*((tableParams i).sp-1)*((tableParams i).k1-1)*((tableParams i).k2-1)*((tableParams i).k3-1)
    ((a 1 ≤ t ∧ t ≤ 3) → 0 < P ∧ P ≤ (t+1)^5) ∧
    ((a 8 ≤ t ∧ t ≤ a 0) → 0 < ((tableParams i).k2-1)*((tableParams i).k1-1-t) ∧ ((tableParams i).k2-1)*((tableParams i).k1-1-t) ≤ t+1) ∧
    ((a 4 ≤ t ∧ t ≤ a 1) → 0 < ((tableParams i).k3-1)*((tableParams i).sp-1-t) ∧ ((tableParams i).k3-1)*((tableParams i).sp-1-t) ≤ t+1) ∧
    ((a 2 ≤ t ∧ t ≤ a 1) → 0 < ((tableParams i).s-1)*((tableParams i).sp-1-t) ∧ ((tableParams i).s-1)*((tableParams i).sp-1-t) ≤ t+1) ∧
    ((a 0 ≤ t ∧ t ≤ a 1) → 0 < ((tableParams i).k1-1)*((tableParams i).k2-1) ∧ ((tableParams i).k1-1)*((tableParams i).k2-1) ≤ (t+1)^2) ∧
    ((a 6 ≤ t ∧ t ≤ a 4) →
      0 < ((tableParams i).k1*(tableParams i).sp-(tableParams i).sp-(tableParams i).k1*t)*((tableParams i).k3*(tableParams i).sp-(tableParams i).sp-(tableParams i).k3*t) ∧
      ((tableParams i).k1*(tableParams i).sp-(tableParams i).sp-(tableParams i).k1*t)*((tableParams i).k3*(tableParams i).sp-(tableParams i).sp-(tableParams i).k3*t) ≤ (tableParams i).sp^2) ∧
    ((a 4 ≤ t ∧ t ≤ a 7) → 0 < (tableParams i).k1*(tableParams i).sp-(tableParams i).sp-(tableParams i).k1*t ∧
      (tableParams i).k1*(tableParams i).sp-(tableParams i).sp-(tableParams i).k1*t ≤ (tableParams i).sp*((tableParams i).sp-1-t)) ∧
    ((a 5 ≤ t ∧ t ≤ a 7) → 0 < (tableParams i).k2*(tableParams i).sp-(tableParams i).sp-(tableParams i).k2*t ∧
      (tableParams i).k2*(tableParams i).sp-(tableParams i).sp-(tableParams i).k2*t ≤ (tableParams i).sp) ∧
    ((a 7 ≤ t ∧ t ≤ a 1) → 0 < (1 : ℝ) ∧ 1 ≤ (tableParams i).sp-1-t) :=
  fun _ ht => tableXi2_log_signs i ht

/-- `Ξ₂(·; s, s', κ₁, κ₂, κ₃)` of display 3.22, page 15, is integrable on `[1, 3]` whenever
`3 < s'` and the logarithms have positive arguments on their supports. -/
theorem Xi2_integrable {p : Params} (hsp : 3 < p.sp) (hS :
  ∀ t ∈ Icc (1 : ℝ) 3,
    let a := alpha p
    let P := (p.s-1)*(p.sp-1)*(p.k1-1)*(p.k2-1)*(p.k3-1)
    ((a 1 ≤ t ∧ t ≤ 3) → 0 < P ∧ P ≤ (t+1)^5) ∧
    ((a 8 ≤ t ∧ t ≤ a 0) → 0 < (p.k2-1)*(p.k1-1-t) ∧ (p.k2-1)*(p.k1-1-t) ≤ t+1) ∧
    ((a 4 ≤ t ∧ t ≤ a 1) → 0 < (p.k3-1)*(p.sp-1-t) ∧ (p.k3-1)*(p.sp-1-t) ≤ t+1) ∧
    ((a 2 ≤ t ∧ t ≤ a 1) → 0 < (p.s-1)*(p.sp-1-t) ∧ (p.s-1)*(p.sp-1-t) ≤ t+1) ∧
    ((a 0 ≤ t ∧ t ≤ a 1) → 0 < (p.k1-1)*(p.k2-1) ∧ (p.k1-1)*(p.k2-1) ≤ (t+1)^2) ∧
    ((a 6 ≤ t ∧ t ≤ a 4) →
      0 < (p.k1*p.sp-p.sp-p.k1*t)*(p.k3*p.sp-p.sp-p.k3*t) ∧
      (p.k1*p.sp-p.sp-p.k1*t)*(p.k3*p.sp-p.sp-p.k3*t) ≤ p.sp^2) ∧
    ((a 4 ≤ t ∧ t ≤ a 7) → 0 < p.k1*p.sp-p.sp-p.k1*t ∧
      p.k1*p.sp-p.sp-p.k1*t ≤ p.sp*(p.sp-1-t)) ∧
    ((a 5 ≤ t ∧ t ≤ a 7) → 0 < p.k2*p.sp-p.sp-p.k2*t ∧
      p.k2*p.sp-p.sp-p.k2*t ≤ p.sp) ∧
    ((a 7 ≤ t ∧ t ≤ a 1) → 0 < (1 : ℝ) ∧ 1 ≤ p.sp-1-t)) :
    IntervalIntegrable (Xi2 p) volume 1 3 := by
  have hq : ∀ t ∈ Icc (1 : ℝ) 3, 5 * t * (1 - t / p.sp) ≠ 0 := by
    intro t ht
    have hsp0 : 0 < p.sp := by linarith
    have : t / p.sp < 1 := (div_lt_one hsp0).2 (by linarith [ht.2])
    exact (mul_pos (by linarith [ht.1]) (by linarith)).ne'
  have h5t : ∀ t ∈ Icc (1 : ℝ) 3, 5 * t ≠ 0 := fun t ht => by
    exact (show (0 : ℝ) < 5 * t by linarith [ht.1]).ne'
  have hspc : ContinuousOn (fun t : ℝ => 5 * t * (1 - t / p.sp)) univ := by fun_prop
  have h1 := sigma_term_integrable 5
    (log (1024 / ((p.s - 1) * (p.sp - 1) * (p.k1 - 1) * (p.k2 - 1) * (p.k3 - 1)))) (by norm_num)
  have h2 : IntervalIntegrable (fun t => ind (alpha p 1) 3 t / (5 * t) *
      log ((t + 1) ^ 5 / ((p.s - 1) * (p.sp - 1) * (p.k1 - 1) * (p.k2 - 1) * (p.k3 - 1))))
      volume 1 3 := by
    apply ind_log_integrable (by fun_prop) (fun t ht => h5t t ht.2) (by fun_prop)
    intro t ht
    have := ((hS t ht.2).1 ht.1).1
    exact (div_pos (pow_pos (by linarith [ht.2.1]) 5) this).ne'
  have h3 : IntervalIntegrable (fun t => ind (alpha p 8) (alpha p 0) t / (5 * t) *
      log ((t + 1) / ((p.k2 - 1) * (p.k1 - 1 - t)))) volume 1 3 := by
    have hd := fun t (ht : t ∈ Icc (alpha p 8) (alpha p 0) ∩ Icc 1 3) =>
      ((hS t ht.2).2.1 ht.1)
    apply ind_log_integrable (by fun_prop) (fun t ht => h5t t ht.2)
      (ContinuousOn.div (by fun_prop) (by fun_prop) (fun t ht => (hd t ht).1.ne'))
    intro t ht
    exact (div_pos (by linarith [ht.2.1]) (hd t ht).1).ne'
  have h4 : IntervalIntegrable (fun t => ind (alpha p 4) (alpha p 1) t / (5 * t) *
      log ((t + 1) / ((p.k3 - 1) * (p.sp - 1 - t)))) volume 1 3 := by
    have hd := fun t (ht : t ∈ Icc (alpha p 4) (alpha p 1) ∩ Icc 1 3) =>
      ((hS t ht.2).2.2.1 ht.1)
    apply ind_log_integrable (by fun_prop) (fun t ht => h5t t ht.2)
      (ContinuousOn.div (by fun_prop) (by fun_prop) (fun t ht => (hd t ht).1.ne'))
    intro t ht
    exact (div_pos (by linarith [ht.2.1]) (hd t ht).1).ne'
  have h5 : IntervalIntegrable (fun t => ind (alpha p 2) (alpha p 1) t / (5 * t) *
      log ((t + 1) / ((p.s - 1) * (p.sp - 1 - t)))) volume 1 3 := by
    have hd := fun t (ht : t ∈ Icc (alpha p 2) (alpha p 1) ∩ Icc 1 3) =>
      ((hS t ht.2).2.2.2.1 ht.1)
    apply ind_log_integrable (by fun_prop) (fun t ht => h5t t ht.2)
      (ContinuousOn.div (by fun_prop) (by fun_prop) (fun t ht => (hd t ht).1.ne'))
    intro t ht
    exact (div_pos (by linarith [ht.2.1]) (hd t ht).1).ne'
  have h6 : IntervalIntegrable (fun t => ind (alpha p 0) (alpha p 1) t / (5 * t) *
      log ((t + 1) ^ 2 / ((p.k1 - 1) * (p.k2 - 1)))) volume 1 3 := by
    have hd := fun t (ht : t ∈ Icc (alpha p 0) (alpha p 1) ∩ Icc 1 3) =>
      ((hS t ht.2).2.2.2.2.1 ht.1)
    apply ind_log_integrable (by fun_prop) (fun t ht => h5t t ht.2) (by fun_prop)
    intro t ht
    exact (div_pos (by nlinarith [ht.2.1]) (hd t ht).1).ne'
  have h7 : IntervalIntegrable (fun t => ind (alpha p 6) (alpha p 4) t /
      (5 * t * (1 - t / p.sp)) * log (p.sp ^ 2 /
      ((p.k1 * p.sp - p.sp - p.k1 * t) * (p.k3 * p.sp - p.sp - p.k3 * t)))) volume 1 3 := by
    have hd := fun t (ht : t ∈ Icc (alpha p 6) (alpha p 4) ∩ Icc 1 3) =>
      ((hS t ht.2).2.2.2.2.2.1 ht.1)
    apply ind_log_integrable (hspc.mono (subset_univ _)) (fun t ht => hq t ht.2)
      (ContinuousOn.div (by fun_prop) (by fun_prop) (fun t ht => (hd t ht).1.ne'))
    intro t ht
    exact (div_pos (by nlinarith) (hd t ht).1).ne'
  have h8 : IntervalIntegrable (fun t => ind (alpha p 4) (alpha p 7) t /
      (5 * t * (1 - t / p.sp)) * log (p.sp * (p.sp - 1 - t) /
      (p.k1 * p.sp - p.sp - p.k1 * t))) volume 1 3 := by
    have hd := fun t (ht : t ∈ Icc (alpha p 4) (alpha p 7) ∩ Icc 1 3) =>
      ((hS t ht.2).2.2.2.2.2.2.1 ht.1)
    apply ind_log_integrable (hspc.mono (subset_univ _)) (fun t ht => hq t ht.2)
      (ContinuousOn.div (by fun_prop) (by fun_prop) (fun t ht => (hd t ht).1.ne'))
    intro t ht
    exact (div_pos ((hd t ht).1.trans_le (hd t ht).2) (hd t ht).1).ne'
  have h9 : IntervalIntegrable (fun t => ind (alpha p 5) (alpha p 7) t /
      (5 * t * (1 - t / p.sp)) * log (p.sp / (p.k2 * p.sp - p.sp - p.k2 * t))) volume 1 3 := by
    have hd := fun t (ht : t ∈ Icc (alpha p 5) (alpha p 7) ∩ Icc 1 3) =>
      ((hS t ht.2).2.2.2.2.2.2.2.1 ht.1)
    apply ind_log_integrable (hspc.mono (subset_univ _)) (fun t ht => hq t ht.2)
      (ContinuousOn.div (by fun_prop) (by fun_prop) (fun t ht => (hd t ht).1.ne'))
    intro t ht
    exact (div_pos (by linarith) (hd t ht).1).ne'
  have h10 : IntervalIntegrable (fun t => ind (alpha p 7) (alpha p 1) t /
      (5 * t * (1 - t / p.sp)) * log (p.sp - 1 - t)) volume 1 3 := by
    have hd := fun t (ht : t ∈ Icc (alpha p 7) (alpha p 1) ∩ Icc 1 3) =>
      ((hS t ht.2).2.2.2.2.2.2.2.2 ht.1)
    apply ind_log_integrable (hspc.mono (subset_univ _)) (fun t ht => hq t ht.2) (by fun_prop)
    intro t ht
    exact (show (0 : ℝ) < p.sp - 1 - t by linarith [(hd t ht).2]).ne'
  exact (((((((((h1.add h2).add h3).add h4).add h5).add h6).add h7).add h8).add h9).add h10)

/-- **Leaf `table_kernel_integrable` PROVED.** Wu 2004 displays 7.1 and 7.2, page 30: each of
the nine Table 1 kernels is integrable on `[1, 3]`. Same statement as
`Burst4Split.table_kernel_integrable`. -/
theorem table_kernel_integrable :
    ∀ i : Fin 9, IntervalIntegrable (Wu04Table.tableKernel i) volume 1 3 := by
  intro i
  unfold Wu04Table.tableKernel
  split_ifs with hi
  · apply Xi2_integrable _ (tableParams_Xi2Signs ⟨i.val, hi⟩)
    have : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
    rcases this with h | h | h | h <;> simp [h, tableParams]  <;> norm_num
  · let j : Fin 5 := ⟨i.val - 4, by omega⟩
    have hp := tableSp_admissible j
    have he : (⟨j.val + 5, by omega⟩ : Fin 10) = ⟨i.val + 1, by omega⟩ := by
      ext; dsimp [j]; omega
    rw [he] at hp
    exact Xi1_integrable hp



/-- `A(s) = 1` for `1 ≤ s ≤ 3`, used in the proof of Corollary 1, page 13. For `s ≤ 2` this is
display 2.6; on `(2, 3]` the equation `(uF(u))' = f(u − 1)` with `f = 0` on `(0, 2]` keeps
`uF(u)` constant, by the mean value theorem. -/
theorem normalized_eq_one {F f : ℝ → ℝ} (hF : IsLinearSieve F f) {s : ℝ}
    (hs1 : 1 ≤ s) (hs3 : s ≤ 3) : Wu04.normalized F s = 1 := by
  obtain ⟨hFc, -, hlow, hder⟩ := hF
  have hE : 0 < 2 * exp eulerMascheroniConstant := by positivity
  have key : s * F s = 2 * exp eulerMascheroniConstant := by
    rcases le_or_gt s 2 with h2 | h2
    · rw [(hlow s (by linarith) h2).1]
      field_simp
    · obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope (fun v => v * F v)
        (fun v => f (v - 1)) h2
        (continuousOn_id.mul (hFc.mono fun x hx => mem_Ioi.2 (by linarith [hx.1])))
        (fun x hx => (hder x hx.1).1)
      have hf0 : f (c - 1) = 0 := (hlow (c - 1) (by linarith [hc.1]) (by linarith [hc.2])).2
      rw [hf0, eq_comm, div_eq_zero_iff] at hslope
      rcases hslope with h | h
      · have h2F : (2 : ℝ) * F 2 = 2 * exp eulerMascheroniConstant := by
          rw [(hlow 2 (by norm_num) le_rfl).1]; field_simp
        linarith
      · linarith
  unfold Wu04.normalized
  rw [key, div_self hE.ne']


/-- The empty prime tuple at an even `N ≥ 3`: it lies in `U_k(N)`, its `Φ` is nonnegative and
its `Θ` is positive. This is the witness that makes `H_{k,N₀}(s)` and `h_{k,N₀}(s)` finite. -/
theorem empty_witness {δ : ℝ} (hδ0 : 0 < δ) (hδ : δ < 1 / 2) (k N : ℕ) (hN : 3 ≤ N) (s : ℝ) :
    Wu04.UkData δ k N 0 Fin.elim0 (1 + 3 / 2 * (Real.log N)⁻¹ ^ 4) ∧
    0 ≤ Wu04.Phi δ N 0 Fin.elim0 (1 + 3 / 2 * (Real.log N)⁻¹ ^ 4) s ∧
    0 < Wu04.Theta δ N 0 Fin.elim0 (1 + 3 / 2 * (Real.log N)⁻¹ ^ 4) := by
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hl : 0 < Real.log N := Real.log_pos (by linarith)
  have hp : 0 < (Real.log N)⁻¹ ^ 4 := by positivity
  refine ⟨Wu04.empty_UkData δ k N (by linarith) (by linarith), ?_, ?_⟩
  · unfold Wu04.Phi
    exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  · unfold Wu04.Theta
    have hli : 0 < Wu04.li (N : ℝ) := Wu04.li_positive (by linarith)
    have hne : (Wu41.Tset N 0 Fin.elim0 (1 + 3 / 2 * (Real.log N)⁻¹ ^ 4)).Nonempty :=
      ⟨Fin.elim0, Fintype.mem_piFinset.2 fun j => j.elim0⟩
    refine mul_pos (mul_pos (by norm_num) hli) (Finset.sum_pos (fun t _ => ?_) hne)
    have hm : Wu04.modulus t = 1 := by simp [Wu04.modulus]
    have hQ : 0 < Real.log (Wu04.Q δ N) := by
      unfold Wu04.Q
      rw [Real.log_rpow (by linarith)]
      exact mul_pos (by linarith) hl
    rw [hm]
    simp only [Nat.cast_one, one_mul, div_one, Nat.totient_one]
    exact div_pos (CN_pos N) hQ

/-- An even number at least `max N₀ 3`. -/
theorem exists_even_ge (N₀ : ℕ) : ∃ N, Even N ∧ N₀ ≤ N ∧ 3 ≤ N :=
  ⟨2 * (N₀ + 2), even_two_mul _, by omega, by omega⟩


/-! ### Part H. The last display of page 31 -/

theorem Tset_zero (N : ℕ) (V : Fin 0 → ℝ) (Δ : ℝ) : Wu41.Tset N 0 V Δ = {Fin.elim0} := by
  rw [Finset.eq_singleton_iff_unique_mem]
  exact ⟨Fintype.mem_piFinset.2 fun j => j.elim0, fun x _ => funext fun j => j.elim0⟩

theorem modulus_zero (t : Fin 0 → ℕ) : Wu04.modulus t = 1 := by simp [Wu04.modulus]

/-- `Φ(N, {1}, s) = S(A; P(N), Q^{1/s})`, the case `σ = {1}` of the definition on page 9. -/
theorem Phi_empty (δ s : ℝ) (N : ℕ) (Δ : ℝ) :
    Wu04.Phi δ N 0 Fin.elim0 Δ s = Wu41.S (Wu04.A N) 1 N (Wu04.Q δ N ^ (1 / s)) := by
  unfold Wu04.Phi
  rw [Tset_zero, Finset.sum_singleton, modulus_zero]
  simp only [Nat.cast_one, one_mul, div_one]

/-- `Θ(N, {1}) = 4 li(N) C_N / log Q`, the case `σ = {1}` of the definition on page 10. -/
theorem Theta_empty (δ : ℝ) (N : ℕ) (Δ : ℝ) :
    Wu04.Theta δ N 0 Fin.elim0 Δ = 4 * Wu04.li N * (CN N / Real.log (Wu04.Q δ N)) := by
  unfold Wu04.Theta
  rw [Tset_zero, Finset.sum_singleton, modulus_zero]
  simp only [Nat.cast_one, one_mul, div_one, Nat.totient_one]

/-- Page 31: `D(N) ≤ S(A; P(N), z) + z + 1`. A Goldbach prime `N − p ≥ z` survives the sieve;
the primes `N − p < z` number at most `z + 1`. -/
theorem D_le_S (N : ℕ) {z : ℝ} (hz : 0 ≤ z) :
    (D N : ℝ) ≤ (Wu41.S (Wu04.A N) 1 N z : ℝ) + z + 1 := by
  classical
  have key : D N ≤ Wu41.S (Wu04.A N) 1 N z + ⌈z⌉₊ := by
    have hS : Wu41.S (Wu04.A N) 1 N z =
        (Finset.filter (fun a => 1 ∣ a ∧ Wu41.Sifted N z a) (Wu04.A N)).card := by
      unfold Wu41.S; congr
    rw [hS]
    unfold D
    refine (Finset.card_le_card_of_injOn (fun p => N - p)
      (t := Finset.filter (fun a => 1 ∣ a ∧ Wu41.Sifted N z a) (Wu04.A N) ∪
        Finset.range ⌈z⌉₊) ?_ ?_).trans ?_
    · intro p hp
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hp
      obtain ⟨hpN, hpp, hΩ⟩ := hp
      have hprime : (N - p).Prime := ArithmeticFunction.cardFactors_eq_one_iff_prime.1 hΩ
      simp only [Finset.coe_union, Finset.coe_filter, Finset.coe_range, Set.mem_union,
        Set.mem_setOf_eq, Set.mem_Iio]
      rcases lt_or_ge ((N - p : ℕ) : ℝ) z with h | h
      · exact Or.inr (Nat.lt_ceil.2 h)
      · left
        refine ⟨Finset.mem_image.2 ⟨p, Finset.mem_filter.2 ⟨Finset.mem_range.2 hpN, hpp⟩, rfl⟩,
          one_dvd _, fun q hq hqz _ hqa => ?_⟩
        have := (Nat.prime_dvd_prime_iff_eq hq hprime).1 hqa
        rw [this] at hqz
        linarith
    · intro p hp q hq hpq
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range] at hp hq
      simp only at hpq
      omega
    · exact (Finset.card_union_le _ _).trans (by rw [Finset.card_range])
  have h1 : (D N : ℝ) ≤ (Wu41.S (Wu04.A N) 1 N z : ℝ) + (⌈z⌉₊ : ℝ) := by exact_mod_cast key
  have h2 : (⌈z⌉₊ : ℝ) < z + 1 := Nat.ceil_lt_add_one hz
  linarith

/-- Display 3.3 of Lemma 3.2, page 9, at `k = 1`, `σ = {1}`, `s = 2.2`, page 31: every
`c < H(2.2)` satisfies `c < 1` and `Φ(N, {1}, 2.2) ≤ (A(2.2) − c) Θ(N, {1})` with
`A(2.2) = 1`, for all large even `N`. PROVED from the definitions of page 10. -/
theorem display33_empty {F f : ℝ → ℝ} (hF : IsLinearSieve F f) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ < 1 / 2) {H h : ℝ → ℝ} (hR : RepresentsCorrections F f δ H h) {c : ℝ}
    (hc : c < H 2.2) :
    c < 1 ∧ ∃ N₀ : ℕ, ∀ N, Even N → N₀ ≤ N → 3 ≤ N →
      Wu04.Phi δ N 0 Fin.elim0 (1 + 3 / 2 * (Real.log N)⁻¹ ^ 4) 2.2 ≤
        (1 - c) * Wu04.Theta δ N 0 Fin.elim0 (1 + 3 / 2 * (Real.log N)⁻¹ ^ 4) := by
  have hE : ((c : ℝ) : EReal) < Wu04.H F δ 2.2 := by
    rw [← (hR 2.2 ⟨by norm_num, by norm_num⟩).1]
    exact_mod_cast hc
  have h1 : Wu04.H F δ 2.2 ≤ Wu04.Hk F δ 1 2.2 := iInf_le (fun k => Wu04.Hk F δ (k + 1) 2.2) 0
  obtain ⟨N₀, hN₀⟩ := lt_iSup_iff.1 (hE.trans_le h1)
  obtain ⟨_, ⟨c', hc', rfl⟩, hlt⟩ := lt_sSup_iff.1 hN₀
  have hcc : c < c' := by exact_mod_cast (show ((c : ℝ) : EReal) < ((c' : ℝ) : EReal) from hlt)
  have hA : Wu04.normalized F 2.2 = 1 := normalized_eq_one hF (by norm_num) (by norm_num)
  have hc'1 : c' ≤ 1 := by
    obtain ⟨N, hEv, hN0, hN3⟩ := exists_even_ge N₀
    obtain ⟨hUk, hPhi, hTh⟩ := empty_witness hδ0 hδ 1 N hN3 2.2
    have := hc' N hN0 (by omega) hEv 0 Fin.elim0 _ hUk
    rw [hA] at this
    by_contra hcon
    have : (1 - c') * Wu04.Theta δ N 0 Fin.elim0 (1 + 3 / 2 * (Real.log N)⁻¹ ^ 4) < 0 :=
      mul_neg_of_neg_of_pos (by linarith) hTh
    linarith
  refine ⟨by linarith, N₀, fun N hEv hN0 hN3 => ?_⟩
  obtain ⟨hUk, hPhi, hTh⟩ := empty_witness hδ0 hδ 1 N hN3 2.2
  have := hc' N hN0 (by omega) hEv 0 Fin.elim0 _ hUk
  rw [hA] at this
  exact this.trans (mul_le_mul_of_nonneg_right (by linarith) hTh.le)

/-- `li(x) ≤ (1 + ε) x / log x` for large `x`, the form of `li(N) ∼ N / log N` used on page 31.
PROVED by splitting `∫₂ˣ dt/log t` at `x^r`. -/
theorem li_upper {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, Wu04.li x ≤ (1 + ε) * (x / Real.log x) := by
  set r : ℝ := (2 + ε) / (2 + 2 * ε) with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r < 1 := by rw [hr, div_lt_one (by positivity)]; linarith
  have hrinv : 1 / r ≤ 1 + ε / 2 := by
    rw [hr, one_div_div, div_le_iff₀ (by positivity)]; nlinarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- `log x ≤ (ε/2) log 2 · x^{1−r}` eventually
  have hlo := (isLittleO_log_rpow_atTop (show 0 < 1 - r by linarith)).bound
    (show 0 < ε / 2 * Real.log 2 by positivity)
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.1 hlo
  refine ⟨max x₁ (max 3 ((2 : ℝ) ^ (1 / r))), fun x hx => ?_⟩
  have hx1 : x₁ ≤ x := (le_max_left _ _).trans hx
  have hx3 : 3 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hx2r : (2 : ℝ) ^ (1 / r) ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  set y := x ^ r with hy
  have hy2 : 2 ≤ y := by
    have := Real.rpow_le_rpow (by positivity) hx2r hr0.le
    rwa [← Real.rpow_mul (by norm_num), one_div_mul_cancel hr0.ne', Real.rpow_one] at this
  have hyx : y ≤ x := by
    have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ x) hr1.le
    rwa [Real.rpow_one] at this
  have hly : Real.log y = r * Real.log x := Real.log_rpow hx0 r
  have hlyp : 0 < Real.log y := by rw [hly]; positivity
  have hcont : ∀ a b : ℝ, 2 ≤ a → a ≤ b →
      IntervalIntegrable (fun t => (Real.log t)⁻¹) MeasureTheory.volume a b := by
    intro a b ha hab
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀ (ContinuousOn.log continuousOn_id fun t ht => ?_) fun t ht => ?_
    · rw [uIcc_of_le hab] at ht; show t ≠ 0; exact (show (0 : ℝ) < t by linarith [ht.1]).ne'
    · rw [uIcc_of_le hab] at ht; show Real.log t ≠ 0; exact (Real.log_pos (by linarith [ht.1])).ne'
  have hsplit : Wu04.li x = (∫ t in (2 : ℝ)..y, (Real.log t)⁻¹) +
      ∫ t in y..x, (Real.log t)⁻¹ := by
    unfold Wu04.li
    rw [intervalIntegral.integral_add_adjacent_intervals (hcont 2 y le_rfl hy2)
      (hcont y x hy2 hyx)]
  have hA : (∫ t in (2 : ℝ)..y, (Real.log t)⁻¹) ≤ y / Real.log 2 := by
    have := intervalIntegral.integral_mono_on hy2 (hcont 2 y le_rfl hy2)
      (intervalIntegrable_const (c := (Real.log 2)⁻¹)) (fun t ht =>
        inv_anti₀ hl2 (Real.log_le_log (by norm_num) ht.1))
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    have : (y - 2) * (Real.log 2)⁻¹ ≤ y / Real.log 2 := by
      rw [div_eq_mul_inv]; exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hB : (∫ t in y..x, (Real.log t)⁻¹) ≤ x / (r * Real.log x) := by
    have := intervalIntegral.integral_mono_on hyx (hcont y x hy2 hyx)
      (intervalIntegrable_const (c := (Real.log y)⁻¹)) (fun t ht =>
        inv_anti₀ hlyp (Real.log_le_log (by linarith) ht.1))
    rw [intervalIntegral.integral_const, smul_eq_mul, hly] at this
    have : (x - y) * (r * Real.log x)⁻¹ ≤ x / (r * Real.log x) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    rw [hly] at hlyp
    linarith
  have hC : y / Real.log 2 ≤ ε / 2 * (x / Real.log x) := by
    have h := hx₁ x hx1
    rw [Real.norm_of_nonneg hlx.le, Real.norm_of_nonneg (by positivity)] at h
    -- `y · x^{1−r} = x`
    have hyx' : y * x ^ (1 - r) = x := by
      rw [hy, ← Real.rpow_add hx0, show r + (1 - r) = 1 by ring, Real.rpow_one]
    rw [div_le_iff₀ hl2]
    have : ε / 2 * (x / Real.log x) * Real.log 2 = ε / 2 * Real.log 2 * x / Real.log x := by
      ring
    rw [this, le_div_iff₀ hlx]
    calc y * Real.log x ≤ y * (ε / 2 * Real.log 2 * x ^ (1 - r)) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = ε / 2 * Real.log 2 * (y * x ^ (1 - r)) := by ring
      _ = ε / 2 * Real.log 2 * x := by rw [hyx']
  have hD : x / (r * Real.log x) ≤ (1 + ε / 2) * (x / Real.log x) := by
    rw [show x / (r * Real.log x) = 1 / r * (x / Real.log x) by field_simp]
    exact mul_le_mul_of_nonneg_right hrinv (by positivity)
  rw [hsplit]
  nlinarith

/-- `N^{1/4} + 1 ≤ κ N / log² N` for large `N`. -/
theorem small_term {κ : ℝ} (hκ : 0 < κ) :
    ∃ x₀ : ℝ, ∀ x ≥ x₀, x ^ (1 / 4 : ℝ) + 1 ≤ κ * (x / Real.log x ^ 2) := by
  have hlo := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 8 by norm_num)).bound one_pos
  obtain ⟨x₁, hx₁⟩ := Filter.eventually_atTop.1 hlo
  refine ⟨max x₁ (max 3 ((2 / κ) ^ 2)), fun x hx => ?_⟩
  have hx1 : x₁ ≤ x := (le_max_left _ _).trans hx
  have hx3 : 3 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hxk : (2 / κ) ^ 2 ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hx
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have h := hx₁ x hx1
  rw [Real.norm_of_nonneg hlx.le, Real.norm_of_nonneg (by positivity), one_mul] at h
  have e8 : (x ^ (1 / 8 : ℝ)) ^ 2 = x ^ (1 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have e4 : x ^ (1 / 4 : ℝ) * x ^ (1 / 4 : ℝ) = x ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hx0]; norm_num
  have e2 : x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x := by
    rw [← Real.rpow_add hx0]; norm_num
  have hq1 : 1 ≤ x ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hlog2 : Real.log x ^ 2 ≤ x ^ (1 / 4 : ℝ) := by
    rw [← e8]; exact pow_le_pow_left₀ hlx.le h 2
  have hs : 2 / κ ≤ x ^ (1 / 2 : ℝ) := by
    have := Real.sqrt_le_sqrt hxk
    rwa [Real.sqrt_sq (by positivity), Real.sqrt_eq_rpow] at this
  rw [mul_div_assoc', le_div_iff₀ (by positivity)]
  have h2 : 2 ≤ κ * x ^ (1 / 2 : ℝ) := by
    rw [div_le_iff₀ hκ] at hs; linarith
  calc (x ^ (1 / 4 : ℝ) + 1) * Real.log x ^ 2 ≤ (2 * x ^ (1 / 4 : ℝ)) * x ^ (1 / 4 : ℝ) :=
        mul_le_mul (by linarith) hlog2 (by positivity) (by positivity)
    _ = 2 * x ^ (1 / 2 : ℝ) := by rw [mul_assoc, e4]
    _ ≤ κ * x ^ (1 / 2 : ℝ) * x ^ (1 / 2 : ℝ) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = κ * x := by rw [mul_assoc, e2]

/-- **Leaf `theorem1_final_display` PROVED.** Wu 2004 page 31, last display: Lemma 3.2 with
`σ = {1}` and `s = 2.2`, `D(N) ≤ S(A; P(N), N^{(1/2−δ)/2.2}) = Φ(N, {1}, 2.2) ≤
{A(2.2) − H_{1,N₀}(2.2)} 4 C_N li(N)/log N^{1/2−δ}`, with `A(2.2) = 1` and `li(N) ∼ N/log N`.
Same statement as `Burst4Split.theorem1_final_display`. -/
theorem theorem1_final_display {F f : ℝ → ℝ} (hF : IsLinearSieve F f)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1 / 4) {H h : ℝ → ℝ}
    (hR : RepresentsCorrections F f δ H h) {c : ℝ} (hc : c < H 2.2) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, Even N → N₀ ≤ N →
      (D N : ℝ) ≤ (1 + ε) * (8 * (1 - c) / (1 - 2 * δ)) * Θ N := by
  obtain ⟨hc1, N₀, hN₀⟩ := display33_empty hF hδ0 (by linarith) hR hc
  set K := 8 * (1 - c) / (1 - 2 * δ) with hK
  have hK0 : 0 < K := div_pos (by linarith) (by linarith)
  have htw := LeanLab.ChenExplicit.twinC_pos
  obtain ⟨x₀, hx₀⟩ := li_upper (show 0 < ε / 2 by linarith)
  obtain ⟨x₁, hx₁⟩ := small_term (show 0 < ε / 2 * K * LeanLab.ChenExplicit.twinC by positivity)
  refine ⟨max N₀ (max 3 (max ⌈x₀⌉₊ ⌈x₁⌉₊)), fun N hEv hN => ?_⟩
  have hN0 : N₀ ≤ N := (le_max_left _ _).trans hN
  have hN3 : 3 ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hNx0 : x₀ ≤ N := (Nat.le_ceil x₀).trans (by exact_mod_cast
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hN)
  have hNx1 : x₁ ≤ N := (Nat.le_ceil x₁).trans (by exact_mod_cast
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hN)
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have hN0r : (0 : ℝ) < N := by linarith
  have hlN : 0 < Real.log N := Real.log_pos (by linarith)
  set Δ := 1 + 3 / 2 * (Real.log N)⁻¹ ^ 4
  set z := Wu04.Q δ N ^ (1 / (2.2 : ℝ)) with hz
  have hQ : Wu04.Q δ N = (N : ℝ) ^ (1 / 2 - δ) := rfl
  have hz0 : 0 ≤ z := Real.rpow_nonneg (Real.rpow_nonneg hN0r.le _) _
  have hz4 : z ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
    rw [hz, hQ, ← Real.rpow_mul hN0r.le]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num; linarith)
  have hlogQ : Real.log (Wu04.Q δ N) = (1 / 2 - δ) * Real.log N := by
    rw [hQ, Real.log_rpow hN0r]
  -- the chain of page 31
  have h1 := D_le_S N hz0
  rw [← Phi_empty δ 2.2 N Δ] at h1
  have h2 := hN₀ N hEv hN0 hN3
  rw [Theta_empty, hlogQ] at h2
  have hli := hx₀ N hNx0
  have hsm := hx₁ N hNx1
  have hCN : LeanLab.ChenExplicit.twinC ≤ CN N := by
    unfold CN; have := oddFactor_one_le N; nlinarith
  have hCN0 : 0 < CN N := CN_pos N
  have hΘ : Θ N = CN N * N / Real.log N ^ 2 := rfl
  -- the main term
  have hmain : (1 - c) * (4 * Wu04.li N * (CN N / ((1 / 2 - δ) * Real.log N))) ≤
      (1 + ε / 2) * K * Θ N := by
    have e : (1 - c) * (4 * Wu04.li N * (CN N / ((1 / 2 - δ) * Real.log N))) =
        K * CN N / Real.log N * Wu04.li N := by
      rw [hK]; field_simp; ring
    rw [e, hΘ]
    have hk : 0 ≤ K * CN N / Real.log N := by positivity
    calc K * CN N / Real.log N * Wu04.li N ≤
          K * CN N / Real.log N * ((1 + ε / 2) * (N / Real.log N)) :=
          mul_le_mul_of_nonneg_left hli hk
      _ = (1 + ε / 2) * K * (CN N * N / Real.log N ^ 2) := by field_simp
  -- the small term
  have hsmall : z + 1 ≤ ε / 2 * K * Θ N := by
    have : ε / 2 * K * LeanLab.ChenExplicit.twinC * (N / Real.log N ^ 2) ≤ ε / 2 * K * Θ N := by
      rw [hΘ, show ε / 2 * K * LeanLab.ChenExplicit.twinC * (N / Real.log N ^ 2) =
        ε / 2 * K * (LeanLab.ChenExplicit.twinC * N / Real.log N ^ 2) by ring]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCN hN0r.le) (by positivity)
    linarith
  have hfin : (1 + ε) * (8 * (1 - c) / (1 - 2 * δ)) * Θ N =
      (1 + ε / 2) * K * Θ N + ε / 2 * K * Θ N := by rw [hK]; ring
  rw [hfin]
  linarith

end LeanLab.ChenDoubleSieve.Burst8P2

#print axioms LeanLab.ChenDoubleSieve.Burst8P2.ind_log_integrable
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.sigma_term_integrable
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.Xi1_integrable
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.tableParams_Xi2Signs
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.Xi2_integrable
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.table_kernel_integrable
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.normalized_eq_one
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.empty_witness
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.exists_even_ge
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.Tset_zero
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.modulus_zero
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.Phi_empty
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.Theta_empty
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.D_le_S
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.display33_empty
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.li_upper
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.small_term
#print axioms LeanLab.ChenDoubleSieve.Burst8P2.theorem1_final_display
