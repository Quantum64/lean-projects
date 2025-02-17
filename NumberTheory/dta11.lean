import Mathlib
import Paperproof

open Nat
open PNat
open Finset

namespace Nat



theorem division_algorithm (a b : ℕ) (h : b > 0) : ∃ q r : ℕ, a = b * q + r ∧ r < b := by
  use a / b, a % b
  constructor
  · rw [Nat.div_add_mod]
  · exact Nat.mod_lt a h


def order (a p : ℕ) : ℕ :=
  if h : Prime p ∧ ¬p ∣ a then
    haveI hex : ∃ n : ℕ, n > 0 ∧ a ^ n ≡ 1 [MOD p] := by
      existsi p - 1
      unfold ModEq
      rw [← Int.ofNat_inj]
      simp
      constructor
      . exact Prime.one_lt h.left
      . refine Int.ModEq.pow_card_sub_one_eq_one h.left ?_
        rcases Nat.coprime_or_dvd_of_prime h.left a with (hp | hp)
        . apply IsCoprime.symm
          exact isCoprime_iff_coprime.mpr hp
        . simp_all
    Nat.find hex
  else 0

lemma order_one_mod_p {a p : ℕ} : a ^ a.order p ≡ 1 [MOD p] := by
  by_cases h : Prime p ∧ ¬p ∣ a
  . unfold order
    rw [dif_pos]
    simp
    generalize_proofs h
    exact (Nat.find_spec h).right
    exact h
  . unfold order
    rw [dif_neg]
    simp
    rfl
    exact h


lemma order_gt_zero {a p : ℕ} (ha : ¬p ∣ a) (hp : Prime p) : a.order p > 0 := by
  unfold order
  rw [dif_pos]
  simp
  exact ⟨hp, ha⟩


theorem order_div (a n p : ℕ) (hm : a ^ n ≡ 1 [MOD p]) (ha : ¬p ∣ a) (hn : n > 0) (hp : Prime p) : a.order p ∣ n := by
  obtain ⟨q, r, hqr, hr⟩ := division_algorithm n (a.order p) (order_gt_zero ha hp)
  have : 1 ≡ a ^ r [MOD p] := by
    calc 1
      _ ≡ a ^ n [MOD p] := by gcongr
      _ ≡ a ^ (a.order p * q + r) [MOD p] := by subst n; rfl
      _ ≡ (a ^ (a.order p)) ^ q * a ^ r [MOD p] := by rw [Nat.pow_add, Nat.pow_mul]
      _ ≡ 1 ^ q * a ^ r [MOD p] := by
        apply ModEq.mul
        clear hqr hr
        . induction' q with q hq
          . simp; rfl
          . repeat rw [Nat.pow_add]
            apply ModEq.mul
            exact hq
            simp [order_one_mod_p]
        . rfl
      _ ≡ a ^ r [MOD p] := by simp; rfl
  suffices : r = 0
  . simp [hqr, this]
  . by_contra rnz
    have : a.order p ≤ r := by
      unfold order
      rw [dif_pos]
      apply Nat.find_min'
      simp [Nat.pos_of_ne_zero rnz, ModEq.symm, this]
      exact ⟨hp, ha⟩
    linarith


--@[reducible] def PrimitiveRoot (g n : ℕ) : Prop :=
--  order g n = n - 1

def index (a n g : ℕ) : ℕ := Nat.findGreatest (λ i => g ^ i ≡ a [MOD n]) (n - 1)


#eval order 3 7
