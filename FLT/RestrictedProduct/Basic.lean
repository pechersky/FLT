import Mathlib

section defs

variable (I : Type*) (G : I → Type*) {Ht : I → Type*} (H : ∀ i, Ht i) [∀ i, SetLike (Ht i) (G i)]

def RestrictedProduct := {x : ∀ i, G i // ∀ᶠ i : I in Filter.cofinite, x i ∈ (H i : Set (G i))}

end defs

section finite_adele_example

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K]

open IsDedekindDomain DedekindDomain

example : RestrictedProduct (HeightOneSpectrum R) (fun v ↦ v.adicCompletion K)
  (fun v ↦ v.adicCompletionIntegers K) = FiniteAdeleRing R K := rfl

end finite_adele_example

variable (I : Type*) (G : I → Type*)
-- {Ht : I → Type*} (H : ∀ i, Ht i) [∀ i, SetLike (Ht i) (G i)]

section monoid

variable [∀ i, Monoid (G i)] (H : ∀ i, Submonoid (G i))

instance : Monoid (RestrictedProduct I G H) where
  mul x y := ⟨fun i ↦ x.val i * y.val i, sorry⟩
  mul_assoc := sorry
  one := ⟨fun i ↦ 1, sorry⟩
  one_mul := sorry
  mul_one := sorry

end monoid

/-

Group, CommRing, TopologicalSpace (careful with this one, it's not the subspace topology of ∏ᵢ Gᵢ,
it's some kind of direct limit topology), TopologicalRing, etc

-/
