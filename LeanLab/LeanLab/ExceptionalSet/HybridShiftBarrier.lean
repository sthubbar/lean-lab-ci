/- AI wrote the Lean code. Audit of the lab hybrid large sieve transcription.
Source context: Montgomery and Vaughan 1975 page 366 equation 7.1.
This is a counterexample to an unrestricted shift in the lab statement.
No paper error is claimed. Binary Goldbach is open. -/
import Mathlib
open Real Finset MeasureTheory
namespace LeanLab.ExceptionalSet.HybridShiftBarrier
attribute [local instance] Classical.propDecidable
lemma log_shift_bound {M N n : ℕ} (hM : 0 < M) (hmn : M ≤ n) (hn : n ≤ M+N) :
    0 ≤ Real.log (n:ℝ)-Real.log M ∧ Real.log (n:ℝ)-Real.log M ≤ (N:ℝ)/M := by
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  have hnr : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hmnR : (M:ℝ) ≤ n := by exact_mod_cast hmn
  have hnR : (n:ℝ) ≤ M+N := by exact_mod_cast hn
  refine ⟨sub_nonneg.mpr (Real.log_le_log hMr hmnR), ?_⟩
  have hh := Real.log_le_sub_one_of_pos (div_pos hnr hMr)
  rw [Real.log_div hnr.ne' hMr.ne'] at hh
  have he : (n:ℝ)/M-1=((n:ℝ)-M)/M := by field_simp
  rw [he] at hh
  exact hh.trans (div_le_div_of_nonneg_right (by linarith : (n:ℝ)-M ≤ N) hMr.le)

lemma normalized_cpow_close {u v : ℝ} (hu : 0 < u) (hv : 0 < v) (t : ℝ) :
    ‖(u:ℂ)^((t:ℂ)*Complex.I)*(v:ℂ)^(-((t:ℂ)*Complex.I))-1‖ ≤
      |t| *|Real.log u-Real.log v| := by
  have huC : (u:ℂ) ≠ 0 := by exact_mod_cast hu.ne'
  have hvC : (v:ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  have he : (u:ℂ)^((t:ℂ)*Complex.I)*(v:ℂ)^(-((t:ℂ)*Complex.I)) =
      Complex.exp (Complex.I*((t*(Real.log u-Real.log v):ℝ):ℂ)) := by
    rw [Complex.cpow_def_of_ne_zero huC,Complex.cpow_def_of_ne_zero hvC,
      ← Complex.ofReal_log hu.le,← Complex.ofReal_log hv.le,← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  simpa [Real.norm_eq_abs,abs_mul] using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := t*(Real.log u-Real.log v)))

lemma dirichlet_norm_lower (M N : ℕ) (hM : 0 < M) (t : ℝ)
    (hsmall : |t| *(N:ℝ) ≤ (M:ℝ)/2) :
    (N:ℝ)/2 ≤ ‖∑ n ∈ Icc (M+1) (M+N), (n:ℂ)^((t:ℂ)*Complex.I)‖ := by
  have hMr : (0:ℝ) < M := by exact_mod_cast hM
  let B := (M:ℂ)^(-((t:ℂ)*Complex.I))
  let S := ∑ n ∈ Icc (M+1) (M+N), (n:ℂ)^((t:ℂ)*Complex.I)
  have hB : ‖B‖=1 := by
    dsimp [B]
    have hh := Complex.norm_cpow_eq_rpow_re_of_pos hMr (-((t:ℂ)*Complex.I))
    simpa using hh
  have hcard : (Icc (M+1) (M+N)).card=N := by rw [Nat.card_Icc]; omega
  have hlocal (n : ℕ) (hn : n ∈ Icc (M+1) (M+N)) :
      ‖(n:ℂ)^((t:ℂ)*Complex.I)*B-1‖ ≤ |t| *((N:ℝ)/M) := by
    obtain ⟨hn1,hn2⟩ := mem_Icc.mp hn
    have hnr : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
    have hb := log_shift_bound hM (show M≤n by omega) hn2
    have hh := normalized_cpow_close hnr hMr t
    push_cast at hh
    rw [abs_of_nonneg hb.1] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hb.2 (abs_nonneg t))
  have hdiff : ‖S*B-(N:ℂ)‖ ≤ (N:ℝ)/2 := by
    have hone : (∑ _n ∈ Icc (M+1) (M+N), (1:ℂ)) = (N:ℂ) := by simp [hcard]
    dsimp only [S]
    rw [sum_mul,← hone,← sum_sub_distrib]
    calc ‖∑ n ∈ Icc (M+1) (M+N), ((n:ℂ)^((t:ℂ)*Complex.I)*B-1)‖
        ≤ ∑ n ∈ Icc (M+1) (M+N), ‖(n:ℂ)^((t:ℂ)*Complex.I)*B-1‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ Icc (M+1) (M+N), |t| *((N:ℝ)/M) := sum_le_sum hlocal
      _ = (N:ℝ)*(|t| *((N:ℝ)/M)) := by simp [hcard]
      _ ≤ _ := by
        have hh : |t| *(N:ℝ)/(M:ℝ) ≤ 1/2 := (div_le_iff₀ hMr).2 (by linarith)
        have hm := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg N : (0:ℝ) ≤ N)
        convert hm using 1 <;> ring
  have hh := norm_sub_norm_le (N:ℂ) (S*B)
  rw [Complex.norm_natCast,norm_mul,hB,mul_one,norm_sub_rev] at hh
  change (N:ℝ)/2 ≤ ‖S‖
  linarith

lemma shifted_integral_lower (N : ℕ) (hN : 1 ≤ N) :
    (N:ℝ)^3/2 ≤ ∫ t in -(N:ℝ)..N,
      ‖∑ n ∈ Icc (2*N^2+1 : ℕ) (2*N^2+N), (n:ℂ)^((t:ℂ)*Complex.I)‖^2 := by
  have hNr : (0:ℝ) < N := by exact_mod_cast (show 0<N by omega)
  have hM : 0 < 2*N^2 := by positivity
  let F : ℝ → ℝ := fun t => ‖∑ n ∈ Icc (2*N^2+1 : ℕ) (2*N^2+N), (n:ℂ)^((t:ℂ)*Complex.I)‖^2
  have hc : Continuous F := by
    dsimp [F]
    apply Continuous.pow
    apply Continuous.norm
    apply continuous_finsetSum
    intro n hn
    have hn0 : (n:ℂ) ≠ 0 := by
      exact_mod_cast (show n ≠ 0 by have := (mem_Icc.mp hn).1; omega)
    simp_rw [Complex.cpow_def_of_ne_zero hn0]
    fun_prop
  have hb (t : ℝ) (ht : t ∈ Set.Icc (-(N:ℝ)) N) : (N:ℝ)^2/4 ≤ F t := by
    have htabs : |t| ≤ (N:ℝ) := abs_le.mpr ht
    have hs : |t| * (N:ℝ) ≤ ((2*N^2:ℕ):ℝ)/2 := by
      push_cast
      nlinarith [mul_le_mul_of_nonneg_right htabs hNr.le]
    have hh := dirichlet_norm_lower (2*N^2) N hM t hs
    dsimp [F]
    nlinarith [sq_nonneg (‖∑ n ∈ Icc (2*N^2+1 : ℕ) (2*N^2+N), (n:ℂ)^((t:ℂ)*Complex.I)‖-(N:ℝ)/2)]
  have hi := intervalIntegral.integral_mono_on (show -(N:ℝ) ≤ N by linarith)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (N:ℝ)^2/4) volume (-(N:ℝ)) N)
    (hc.intervalIntegrable _ _) hb
  simp only [intervalIntegral.integral_const,smul_eq_mul] at hi
  have he : ((N:ℝ)-(-(N:ℝ)))*((N:ℝ)^2/4)=(N:ℝ)^3/2 := by ring
  rw [he] at hi
  exact hi

lemma no_shift_uniform_bound : ¬ ∃ C : ℝ, 0 < C ∧ ∀ M N : ℕ, 1 ≤ N →
    (∫ t in -(N:ℝ)..N,
      ‖∑ n ∈ Icc (M+1) (M+N), (n:ℂ)^((t:ℂ)*Complex.I)‖^2) ≤
      C*((N:ℝ)+N)*N := by
  rintro ⟨C,hC,h⟩
  obtain ⟨N,hN⟩ := exists_nat_gt (4*C+1)
  have hNpos : 0 < (N:ℝ) := by linarith
  have hN1 : 1 ≤ N := by exact_mod_cast (show (1:ℝ) ≤ N by linarith)
  have hl := shifted_integral_lower N hN1
  have hu := h (2*N^2) N hN1
  have hprod : 0 < ((N:ℝ)-4*C)*(N:ℝ)^2 := mul_pos (by linarith) (sq_pos_of_pos hNpos)
  nlinarith

theorem hybrid_large_sieve_not_valid : ¬ ∃ C : ℝ, 0 < C ∧ ∀ Q : ℕ, 1 ≤ Q → ∀ T : ℝ, 1 ≤ T →
    ∀ (M N : ℕ) (a : ℕ → ℂ),
      ∑ q ∈ Finset.Icc 1 Q, ∑ χ : DirichletCharacter ℂ q with χ.IsPrimitive,
        ∫ t in (-T)..T, ‖∑ n ∈ Finset.Icc (M + 1) (M + N),
          a n * χ (n : ZMod q) * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖ ^ 2 ≤
      C * (N + (Q : ℝ) ^ 2 * T) * ∑ n ∈ Finset.Icc (M + 1) (M + N), ‖a n‖ ^ 2 := by
  classical
  rintro ⟨C,hC,h⟩
  apply no_shift_uniform_bound
  refine ⟨C,hC,?_⟩
  intro M N hN
  have hNr : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hh := h 1 (by omega) (N:ℝ) hNr M N (fun _ => 1)
  have hχ (χ : DirichletCharacter ℂ 1) : χ=1 := by
    apply DFunLike.ext
    intro z
    have hz : z=(1:ZMod 1) := Subsingleton.elim _ _
    simp [hz]
  have hprim : (1 : DirichletCharacter ℂ 1).IsPrimitive := by
    simp [DirichletCharacter.isPrimitive_def,DirichletCharacter.conductor_one]
  have hset : (Finset.univ.filter (fun χ : DirichletCharacter ℂ 1 => χ.IsPrimitive)) = {1} := by
    ext χ
    rw [hχ χ]
    simp only [mem_filter,mem_univ,true_and,mem_singleton]
    exact iff_of_true hprim trivial
  have hval (n : ℕ) : (1 : DirichletCharacter ℂ 1) (n:ZMod 1)=1 := by
    have hn : (n:ZMod 1)=(1:ZMod 1) := Subsingleton.elim _ _
    simp [hn]
  have hcard : (Icc (M+1) (M+N)).card=N := by rw [Nat.card_Icc]; omega
  simpa only [Icc_self,sum_singleton,hset,hval,one_mul,norm_one,one_pow,
    sum_const,nsmul_eq_mul,smul_eq_mul,mul_one,Nat.cast_one,one_pow,one_mul,hcard] using hh

end LeanLab.ExceptionalSet.HybridShiftBarrier
