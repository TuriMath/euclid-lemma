import Theorems.EuclidLemma.A

namespace TuriMath.EuclidLemma

/-- Euclid's lemma, via Bézout: if `p ∤ a` then `p` and `a` are coprime, so `p ∣ b`. -/
theorem main : A.Statement := by
  intro p hp a b h
  by_cases ha : (p : ℤ) ∣ a
  · exact Or.inl ha
  · right
    have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hcop : IsCoprime (p : ℤ) a :=
      (Irreducible.coprime_iff_not_dvd hpi.irreducible).mpr ha
    exact hcop.dvd_of_dvd_mul_left h

end TuriMath.EuclidLemma
