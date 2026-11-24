import Mathlib

namespace PEqualNP.Outside.L_lib_119_aux

theorem geom (k : ℕ) : (∑ l ∈ Finset.range k, 2 ^ l) + 1 = 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, pow_succ]; omega

end PEqualNP.Outside.L_lib_119_aux

theorem PEqualNP.Outside.L_lib_119 : ∀ n : ℕ, 1 ≤ n → ∀ g : (Σ l : Fin (n - 1), List.Vector Bool l) → List.Vector Bool n, 2 ^ (n - 1) + 1 ≤ (Finset.univ.filter (fun y : List.Vector Bool n => ∀ x, g x ≠ y)).card := by
  intro n hn g
  have hdom : Fintype.card (Σ l : Fin (n - 1), List.Vector Bool l) + 1 = 2 ^ (n - 1) := by
    rw [Fintype.card_sigma]
    simp only [card_vector, Fintype.card_bool]
    rw [Fin.sum_univ_eq_sum_range (fun l => 2 ^ l)]
    exact PEqualNP.Outside.L_lib_119_aux.geom _
  have hfilt : Finset.univ.filter (fun y : List.Vector Bool n => ∀ x, g x ≠ y) = Finset.univ \ Finset.univ.image g := by
    ext y; simp [Sigma.forall]
  rw [hfilt, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, card_vector, Fintype.card_bool]
  have him : (Finset.univ.image g).card ≤ Fintype.card (Σ l : Fin (n - 1), List.Vector Bool l) :=
    Finset.card_image_le.trans (by simp)
  have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']; congr 1; omega
  omega
