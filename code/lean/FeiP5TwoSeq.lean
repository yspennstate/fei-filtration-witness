import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The two-sequence inequality

Let A_k, B_k >= 0 for k < n, let delta = sum_k B_k > 0, and suppose that for some M >= 0

  (sum_{k >= K} A_k) * (sum_{k <= K} B_k) <= M * delta^2   for every K < n.

With Phi(a, b) = a log2((a+b)/a) + b log2((a+b)/b), the conclusion proved here is

  sum_k Phi(A_k, B_k) <= (4 / ln 2 + log2 (1 + 2M)) * delta.

The proof: a log((a+b)/a) <= b; for every r >= 1, b log(1 + a/b) <= b log r + a/r, applied with
r = (1+2M)/beta_k^2, beta_k the normalised prefix sum of B; the B-part telescopes against
F(x) = x - x log x on [0, 1], and the A-part, after exchanging the order of summation, is bounded
by the hypothesis.
-/

open Finset Real

namespace FeiP5

noncomputable def phi (a b : ℝ) : ℝ := a * log ((a + b) / a) + b * log ((a + b) / b)

noncomputable def Phi2 (a b : ℝ) : ℝ := phi a b / log 2

noncomputable def F (x : ℝ) : ℝ := x - x * log x

lemma log_le_sub_one' {x : ℝ} (hx : 0 < x) : log x ≤ x - 1 := by
  have h := Real.add_one_le_exp (log x)
  rw [Real.exp_log hx] at h
  linarith

lemma div_mono {a b c : ℝ} (h : a ≤ b) (hc : 0 < c) : a / c ≤ b / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right h (inv_nonneg.mpr hc.le)

lemma first_part (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : a * log ((a + b) / a) ≤ b := by
  rcases ha.eq_or_lt with h | h
  · rw [← h]; simp only [zero_mul]; exact hb
  · have h1 := log_le_sub_one' (div_pos (by linarith : 0 < a + b) h)
    have h2 := mul_le_mul_of_nonneg_left h1 h.le
    have ha0 : a ≠ 0 := h.ne'
    have e : a * ((a + b) / a - 1) = b := by
      field_simp
      ring
    nlinarith [h2, e]

/-- For r = c / beta^2 >= 1: b log((a+b)/b) <= b (log c - 2 log beta) + a beta^2 / c. -/
lemma tangent (a b β c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hc : 1 ≤ c)
    (hbβ : 0 < b → 0 < β) :
    b * log ((a + b) / b) ≤ b * (log c - 2 * log β) + a * β ^ 2 / c := by
  have hc0 : 0 < c := by linarith
  rcases hb.eq_or_lt with h | h
  · rw [← h]
    simp only [zero_mul, zero_add]
    exact div_nonneg (mul_nonneg ha (sq_nonneg β)) hc0.le
  · have hβ := hbβ h
    have hβ2 : 0 < β ^ 2 := pow_pos hβ 2
    have hβ2c : β ^ 2 ≤ c := by nlinarith [mul_le_mul_of_nonneg_left hβ1 hβ0]
    have hr : 0 < c / β ^ 2 := div_pos hc0 hβ2
    have hu : 0 < (a + b) / b := div_pos (by linarith) h
    have h1 := log_le_sub_one' (div_pos hu hr)
    have hlr : log (c / β ^ 2) = log c - 2 * log β := by
      rw [Real.log_div hc0.ne' hβ2.ne', Real.log_pow]
      push_cast
      ring
    rw [Real.log_div hu.ne' hr.ne', hlr] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 h.le
    have hb0 : b ≠ 0 := h.ne'
    have hβ0' : β ≠ 0 := hβ.ne'
    have hc0' : c ≠ 0 := hc0.ne'
    have e : b * ((a + b) / b / (c / β ^ 2) - 1) = a * β ^ 2 / c + b * (β ^ 2 / c - 1) := by
      field_simp
      ring
    have h3 : β ^ 2 / c ≤ 1 := (div_le_one hc0).mpr hβ2c
    have h4 : b * (β ^ 2 / c - 1) ≤ 0 := by nlinarith [mul_nonneg h.le (sub_nonneg.mpr h3)]
    nlinarith [h2, e, h4]

/-- One step of the Riemann sum of -log against its antiderivative F. -/
lemma fstep (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) :
    (v - u) * (-log v) ≤ F v - F u := by
  unfold F
  have key : u * (log v - log u) ≤ v - u := by
    rcases hu.eq_or_lt with h | h
    · rw [← h]; simp only [zero_mul, sub_zero]; linarith
    · have hv : 0 < v := lt_of_lt_of_le h huv
      have h1 := log_le_sub_one' (div_pos hv h)
      rw [Real.log_div hv.ne' h.ne'] at h1
      have h2 := mul_le_mul_of_nonneg_left h1 h.le
      have hu0 : u ≠ 0 := h.ne'
      have e : u * (v / u - 1) = v - u := by
        field_simp
      nlinarith [h2, e]
  have e : (v - v * log v) - (u - u * log u) - (v - u) * (-log v) = (v - u) - u * (log v - log u) := by
    ring
  nlinarith [key, e]

lemma tele (n : ℕ) (β : ℕ → ℝ) (h0 : β 0 = 0) (hn : β n = 1) (hmono : ∀ k < n, β k ≤ β (k + 1))
    (hnn : ∀ k ≤ n, 0 ≤ β k) :
    ∑ k ∈ range n, (β (k + 1) - β k) * (-log (β (k + 1))) ≤ 1 := by
  have h : ∀ k ∈ range n, (β (k + 1) - β k) * (-log (β (k + 1))) ≤ F (β (k + 1)) - F (β k) := by
    intro k hk
    have hk' := Finset.mem_range.mp hk
    exact fstep _ _ (hnn k hk'.le) (hmono k hk')
  calc ∑ k ∈ range n, (β (k + 1) - β k) * (-log (β (k + 1)))
      ≤ ∑ k ∈ range n, (F (β (k + 1)) - F (β k)) := Finset.sum_le_sum h
    _ = F (β n) - F (β 0) := Finset.sum_range_sub (fun j => F (β j)) n
    _ = 1 := by rw [hn, h0]; simp [F]

/-- Exchange of the order of summation used for the A-part. -/
lemma swap (A d : ℕ → ℝ) (n : ℕ) :
    ∑ k ∈ range n, A k * ∑ l ∈ range (k + 1), d l = ∑ l ∈ range n, d l * ∑ k ∈ Ico l n, A k := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ (fun k => A k * ∑ l ∈ range (k + 1), d l) n, ih,
      Finset.sum_range_succ (fun l => d l * ∑ k ∈ Ico l (n + 1), A k) n]
    have h1 : ∑ l ∈ range n, d l * ∑ k ∈ Ico l (n + 1), A k =
        ∑ l ∈ range n, d l * ∑ k ∈ Ico l n, A k + A n * ∑ l ∈ range n, d l := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun l hl => ?_)
      rw [Finset.sum_Ico_succ_top (Finset.mem_range.mp hl).le]
      ring
    rw [h1, Finset.sum_Ico_succ_top (le_refl n), Finset.Ico_self, Finset.sum_empty,
      Finset.sum_range_succ d n]
    ring

/-- The inequality in natural logarithms, with the normalised prefix sums beta as data. -/
theorem core (n : ℕ) (A B β : ℕ → ℝ) (δ M : ℝ) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hA : ∀ k, 0 ≤ A k) (hB : ∀ k, 0 ≤ B k)
    (h0 : β 0 = 0) (hn : β n = 1) (hmono : ∀ k < n, β k ≤ β (k + 1)) (hnn : ∀ k ≤ n, 0 ≤ β k)
    (hle : ∀ k ≤ n, β k ≤ 1)
    (hBβ : ∀ k, B k = δ * (β (k + 1) - β k))
    (hyp : ∀ l < n, (∑ k ∈ Ico l n, A k) * β (l + 1) ≤ M * δ) :
    ∑ k ∈ range n, phi (A k) (B k) ≤ (4 + log (1 + 2 * M)) * δ := by
  have hc1 : (1 : ℝ) ≤ 1 + 2 * M := by linarith
  have hc0 : (0 : ℝ) < 1 + 2 * M := by linarith
  have hsumB : ∑ k ∈ range n, B k = δ := by
    rw [Finset.sum_congr rfl (fun k _ => hBβ k), ← Finset.mul_sum, Finset.sum_range_sub β n, hn, h0]
    ring
  have hsplit : ∑ k ∈ range n, phi (A k) (B k) =
      ∑ k ∈ range n, A k * log ((A k + B k) / A k) + ∑ k ∈ range n, B k * log ((A k + B k) / B k) := by
    rw [← Finset.sum_add_distrib]
    rfl
  have h1 : ∑ k ∈ range n, A k * log ((A k + B k) / A k) ≤ δ := by
    rw [← hsumB]
    exact Finset.sum_le_sum (fun k _ => first_part _ _ (hA k) (hB k))
  have h2 : ∑ k ∈ range n, B k * log ((A k + B k) / B k) ≤
      ∑ k ∈ range n, (B k * (log (1 + 2 * M) - 2 * log (β (k + 1))) +
        A k * β (k + 1) ^ 2 / (1 + 2 * M)) := by
    apply Finset.sum_le_sum
    intro k hk
    have hk' := Finset.mem_range.mp hk
    refine tangent _ _ _ _ (hA k) (hB k) (hnn (k + 1) (Nat.succ_le_of_lt hk'))
      (hle (k + 1) (Nat.succ_le_of_lt hk')) hc1 ?_
    intro hbpos
    rw [hBβ k] at hbpos
    have hd : 0 < β (k + 1) - β k := by
      rcases le_or_gt (β (k + 1) - β k) 0 with h | h
      · exfalso
        have := mul_le_mul_of_nonneg_left h hδ.le
        rw [mul_zero] at this
        linarith
      · exact h
    linarith [hnn k hk'.le]
  have h3 : ∑ k ∈ range n, B k * (-log (β (k + 1))) ≤ δ := by
    have e : ∑ k ∈ range n, B k * (-log (β (k + 1))) =
        δ * ∑ k ∈ range n, (β (k + 1) - β k) * (-log (β (k + 1))) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by rw [hBβ k]; ring)
    rw [e]
    calc δ * ∑ k ∈ range n, (β (k + 1) - β k) * (-log (β (k + 1)))
        ≤ δ * 1 := mul_le_mul_of_nonneg_left (tele n β h0 hn hmono hnn) hδ.le
      _ = δ := mul_one δ
  have h4 : ∑ k ∈ range n, A k * β (k + 1) ^ 2 ≤ 2 * M * δ := by
    have e1 : ∀ k, β (k + 1) ^ 2 = ∑ l ∈ range (k + 1), (β (l + 1) ^ 2 - β l ^ 2) := by
      intro k
      rw [Finset.sum_range_sub (fun j => β j ^ 2) (k + 1)]
      simp [h0]
    have e2 : ∑ k ∈ range n, A k * β (k + 1) ^ 2 =
        ∑ l ∈ range n, (β (l + 1) ^ 2 - β l ^ 2) * ∑ k ∈ Ico l n, A k := by
      calc ∑ k ∈ range n, A k * β (k + 1) ^ 2
          = ∑ k ∈ range n, A k * ∑ l ∈ range (k + 1), (β (l + 1) ^ 2 - β l ^ 2) :=
            Finset.sum_congr rfl (fun k _ => by rw [← e1 k])
        _ = ∑ l ∈ range n, (β (l + 1) ^ 2 - β l ^ 2) * ∑ k ∈ Ico l n, A k :=
            swap A (fun l => β (l + 1) ^ 2 - β l ^ 2) n
    rw [e2]
    calc ∑ l ∈ range n, (β (l + 1) ^ 2 - β l ^ 2) * ∑ k ∈ Ico l n, A k
        ≤ ∑ l ∈ range n, (β (l + 1) - β l) * (2 * (M * δ)) := by
          apply Finset.sum_le_sum
          intro l hl
          have hl' := Finset.mem_range.mp hl
          have hΔ : 0 ≤ β (l + 1) - β l := by linarith [hmono l hl']
          have hT : 0 ≤ ∑ k ∈ Ico l n, A k := Finset.sum_nonneg (fun k _ => hA k)
          have hh := hyp l hl'
          have hm := mul_le_mul_of_nonneg_right (hmono l hl') hT
          calc (β (l + 1) ^ 2 - β l ^ 2) * ∑ k ∈ Ico l n, A k
              = (β (l + 1) - β l) * ((β (l + 1) + β l) * ∑ k ∈ Ico l n, A k) := by ring
            _ ≤ (β (l + 1) - β l) * (2 * ((∑ k ∈ Ico l n, A k) * β (l + 1))) := by
                refine mul_le_mul_of_nonneg_left ?_ hΔ
                nlinarith [hm]
            _ ≤ (β (l + 1) - β l) * (2 * (M * δ)) := by
                refine mul_le_mul_of_nonneg_left ?_ hΔ
                linarith [hh]
      _ = 2 * M * δ := by
          rw [← Finset.sum_mul, Finset.sum_range_sub β n, hn, h0]
          ring
  have e2 : ∑ k ∈ range n, (B k * (log (1 + 2 * M) - 2 * log (β (k + 1))) +
        A k * β (k + 1) ^ 2 / (1 + 2 * M)) =
      log (1 + 2 * M) * ∑ k ∈ range n, B k + 2 * ∑ k ∈ range n, B k * (-log (β (k + 1))) +
        (∑ k ∈ range n, A k * β (k + 1) ^ 2) / (1 + 2 * M) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  have h5 : (∑ k ∈ range n, A k * β (k + 1) ^ 2) / (1 + 2 * M) ≤ δ := by
    rw [div_le_iff₀ hc0]
    nlinarith [h4]
  rw [e2, hsumB] at h2
  rw [hsplit]
  have e3 : (4 + log (1 + 2 * M)) * δ = 4 * δ + log (1 + 2 * M) * δ := by ring
  rw [e3]
  nlinarith [h1, h2, h3, h5]

/-- The same inequality, natural logarithms, in the paper's notation. -/
theorem two_seq_nat (n : ℕ) (A B : ℕ → ℝ) (M : ℝ) (hA : ∀ k, 0 ≤ A k) (hB : ∀ k, 0 ≤ B k)
    (hM : 0 ≤ M) (hδ : 0 < ∑ k ∈ range n, B k)
    (hyp : ∀ K < n, (∑ k ∈ Ico K n, A k) * (∑ k ∈ range (K + 1), B k) ≤
      M * (∑ k ∈ range n, B k) ^ 2) :
    ∑ k ∈ range n, phi (A k) (B k) ≤ (4 + log (1 + 2 * M)) * ∑ k ∈ range n, B k := by
  have hδ' : (∑ k ∈ range n, B k) ≠ 0 := hδ.ne'
  have hP0 : ∀ j ≤ n, ∑ k ∈ range j, B k ≤ ∑ k ∈ range n, B k := by
    intro j hj
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => hB k)
    intro x hx
    simp only [Finset.mem_range] at hx ⊢
    omega
  refine core n A B (fun j => (∑ k ∈ range j, B k) / ∑ k ∈ range n, B k) (∑ k ∈ range n, B k) M
    hδ hM hA hB ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · simp
  · exact div_self hδ'
  · intro k _
    show (∑ i ∈ range k, B i) / _ ≤ (∑ i ∈ range (k + 1), B i) / _
    refine div_mono ?_ hδ
    rw [Finset.sum_range_succ]
    linarith [hB k]
  · intro k _
    exact div_nonneg (Finset.sum_nonneg (fun i _ => hB i)) hδ.le
  · intro k hk
    exact (div_le_one hδ).mpr (hP0 k hk)
  · intro k
    show B k = _ * ((∑ i ∈ range (k + 1), B i) / _ - (∑ i ∈ range k, B i) / _)
    rw [Finset.sum_range_succ]
    field_simp
    ring
  · intro l hl
    show (∑ k ∈ Ico l n, A k) * ((∑ k ∈ range (l + 1), B k) / _) ≤ _
    have h := hyp l hl
    rw [mul_div_assoc', div_le_iff₀ hδ]
    nlinarith [h]

/-- The two-sequence inequality in bits: sum Phi(A_k, B_k) <= (4 / ln 2 + log2 (1 + 2M)) delta. -/
theorem two_seq (n : ℕ) (A B : ℕ → ℝ) (M : ℝ) (hA : ∀ k, 0 ≤ A k) (hB : ∀ k, 0 ≤ B k)
    (hM : 0 ≤ M) (hδ : 0 < ∑ k ∈ range n, B k)
    (hyp : ∀ K < n, (∑ k ∈ Ico K n, A k) * (∑ k ∈ range (K + 1), B k) ≤
      M * (∑ k ∈ range n, B k) ^ 2) :
    ∑ k ∈ range n, Phi2 (A k) (B k) ≤ (4 / log 2 + logb 2 (1 + 2 * M)) * ∑ k ∈ range n, B k := by
  have hl2 : 0 < log 2 := Real.log_pos (by norm_num)
  have hl2' : log 2 ≠ 0 := hl2.ne'
  have h := two_seq_nat n A B M hA hB hM hδ hyp
  have e : ∑ k ∈ range n, Phi2 (A k) (B k) = (∑ k ∈ range n, phi (A k) (B k)) / log 2 := by
    rw [Finset.sum_div]
    rfl
  have e2 : (4 / log 2 + logb 2 (1 + 2 * M)) * ∑ k ∈ range n, B k =
      ((4 + log (1 + 2 * M)) * ∑ k ∈ range n, B k) / log 2 := by
    simp only [Real.logb]
    field_simp
  rw [e, e2]
  exact div_mono h hl2

end FeiP5

#print axioms FeiP5.two_seq
