import Mathlib
/-!

# Restricted products

Basic idea: a (possibly infinite) collection of groups G_i all equipped with subgroups H_i.
The restricted product is the subset of ∏_i G_i consisting of elements which are in H_i
for all but finitely many i.

I've got some kind of general set-up below. Need some boilerplate.

I've got the type (G_i are types, H_i are subtypes).

Need; if G_i are groups and H_i are subgroups, the restricted product is a group
Same for CommRing.

More interestingly, if the G_i are topological spaces and the H_i are...what?
Then we get a topological space structure on the restricted product.

In my example, the H_i are compact open subspaces.

In my example, the G_i are abelian groups, and the H_i are compact open subgroups.

In this case, there's a short exact sequence

0 -> ∏_i H_i -> restricted product of G_i -> ⨁ (G_i / H_i) -> 0

The restricted product is topologised such that ∏_i H_i is open with the product topology
and you muddle on from that.




-/
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
