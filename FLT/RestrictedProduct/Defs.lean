import Mathlib

section AntiRingFilterBasis

variable {R : Type*} [Ring R] [TopologicalSpace R] [TopologicalRing R]

/- The point of `RingFilterBasis` is "if these subsets of a ring satisfy some axioms
then there's a topological ring structure such that these subsets are the
open neighbourhoods of 0".

The below lemmas are the converse to this.
-/

namespace TopologicalRing

open scoped Pointwise

lemma ringFilterBasis_add {U : Set R} (hUopen : IsOpen U) (hU0 : 0 ∈ U) :
    ∃ V : Set R, IsOpen V ∧ 0 ∈ V ∧ V + V ⊆ U := by
  sorry

lemma ringFilterBasis_neg {U : Set R} (hUopen : IsOpen U) (hU0 : 0 ∈ U) :
    ∃ V : Set R, IsOpen V ∧ 0 ∈ V ∧ V ⊆ (fun x ↦ -x) ⁻¹' U := by
  sorry

lemma ringFilterBasis_mul {U : Set R} (hUopen : IsOpen U) (hU0 : 0 ∈ U) :
    ∃ V : Set R, IsOpen V ∧ 0 ∈ V ∧ V * V ⊆ U := by
  sorry

lemma ringFilterBasis_mul_left (r : R) {U : Set R} (hUopen : IsOpen U) (hU0 : 0 ∈ U) :
    ∃ V : Set R, IsOpen V ∧ 0 ∈ V ∧ V ⊆ (fun x ↦ r * x) ⁻¹' U := by
  sorry

lemma ringFilterBasis_mul_right (r : R) {U : Set R} (hUopen : IsOpen U) (hU0 : 0 ∈ U) :
    ∃ V : Set R, IsOpen V ∧ 0 ∈ V ∧ V ⊆ (fun x ↦ x * r) ⁻¹' U := by
  sorry

end TopologicalRing

end AntiRingFilterBasis

variable {ι : Type*}

namespace Ring

variable (R : ι → Type*) [∀ i, Ring (R i)] (A : (i : ι) → Subring (R i))

def Subring.restrictedProduct : Subring ((i : ι) → R i) where
  carrier := {x : (i : ι) → R i | ∀ᶠ i in Filter.cofinite, x i ∈ A i}
  mul_mem' {x y} hx hy := by
    --simp only [Set.mem_setOf_eq] at hx hy ⊢
    exact sorry
  one_mem' := sorry
  add_mem' {x y} hx hy := sorry
  zero_mem' := sorry
  neg_mem' {x} hx := sorry

def RestrictedProduct : Type _ := Subring.restrictedProduct R A

instance : Ring (RestrictedProduct R A) := inferInstanceAs (Ring <| Subring.restrictedProduct R A)

namespace RestrictedProduct

def structureMap : (∀ i, A i) →+* (RestrictedProduct R A) where
  toFun x := ⟨fun i ↦ (x i).1, sorry⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' x y := rfl
  map_mul' x y := rfl

instance : Module (∀ i, A i) (RestrictedProduct R A) := (structureMap R A).toModule

section Topology

variable [∀ i, TopologicalSpace (R i)] [∀ i, TopologicalRing (R i)]
    (hAopen : ∀ i, IsOpen (A i : Set (R i)))

def ringFilterBasis : RingFilterBasis (RestrictedProduct R A) where
  sets := {U | ∃ V : Set (∀ i, A i), IsOpen V ∧ 0 ∈ V ∧ structureMap R A '' V = U}
  nonempty := ⟨_, ⊤, isOpen_univ, trivial, rfl⟩
  inter_sets := by
    rintro _ _ ⟨V, hVopen, hV0, rfl⟩ ⟨W, hWopen, hW0, rfl⟩
    exact ⟨structureMap R A '' (V ∩ W), ⟨V ∩ W, IsOpen.inter hVopen hWopen, Set.mem_inter hV0 hW0,
      rfl⟩, Set.image_inter_subset _ _ _⟩
  zero' {_} := by
    rintro ⟨V, hVopen, hV0, rfl⟩
    exact ⟨0, hV0, rfl⟩
  add' {_} := by
    rintro ⟨V, hVopen, hV0, rfl⟩
    obtain ⟨W, hWopen, hW0, hWadd⟩ := TopologicalRing.ringFilterBasis_add hVopen hV0
    refine ⟨_, ⟨W, hWopen, hW0, rfl⟩, ?_⟩
    rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨x + y, hWadd <| Set.add_mem_add hx hy, rfl⟩
  neg' {_} := by
    rintro ⟨V, hVopen, hV0, rfl⟩
    obtain ⟨W, hWopen, hW0, hWneg⟩ := TopologicalRing.ringFilterBasis_neg hVopen hV0
    refine ⟨_, ⟨W, hWopen, hW0, rfl⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨-x, hWneg hx, rfl⟩
  conj' r {_} := by
    rintro ⟨V, hVopen, hV0, rfl⟩
    refine ⟨_, ⟨V, hVopen, hV0, rfl⟩, ?_⟩
    simp
  mul' {_} := by
    rintro ⟨V, hVopen, hV0, rfl⟩
    obtain ⟨W, hWopen, hW0, hWmul⟩ := TopologicalRing.ringFilterBasis_mul hVopen hV0
    refine ⟨_, ⟨W, hWopen, hW0, rfl⟩, ?_⟩ -- wtong, need smaller V
    rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨x * y, hWmul <| Set.mul_mem_mul hx hy, rfl⟩
  mul_left' r {_} := by
    rintro ⟨V, hVopen, hV0, rfl⟩
    -- strat: shrink V to make it ∏ᵢ Vᵢ with Vᵢ open in Aᵢ and Vᵢ = Aᵢ for all but finitely many i.
    -- Now define Wᵢ open in Aᵢ thus. If Vᵢ = Aᵢ and rᵢ ∈ Aᵢ then set Wᵢ = Aᵢ (this happens for
    -- all but finitely many i). Now what about the bad i?
    -- For these, apply `ringFilterBasis_mul_left` to Rᵢ, rᵢ and the image of Vᵢ to get
    -- Wᵢ with rᵢWᵢ ⊆ Vᵢ. Then ∏ᵢ Wᵢ works.
    sorry
  mul_right' := sorry -- probably have to repeat the argument mutatis mutandis.

instance : TopologicalSpace (RestrictedProduct R A) := (ringFilterBasis R A).topology

-- instance : TopologicalRing (RestrictedProduct R A) := inferInstance

/-
RingSubgroupsBasis.hasBasis_nhds_zero.{u_1, u_2} {A : Type u_1} {ι : Type u_2} [Ring A] [Nonempty ι]
  {B : ι → AddSubgroup A} (hB : RingSubgroupsBasis B) : (𝓝 0).HasBasis (fun x ↦ True) fun i ↦ ↑(B i)
-/

-- PR and refactor `RingSubgroupsBasis.hasBasis_nhds_zero`
open Filter in
lemma _root_.RingFilterBasis.hasBasis_nhds_zero {A : Type*} [Ring A]
    (B : RingFilterBasis A) : HasBasis (@nhds A B.topology 0) (fun _ => True)
    fun (i : {S // S ∈ B.sets}) => i :=
  ⟨by
    intro s
    rw [B.toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff]
    constructor
    · rintro ⟨t, h0, hi⟩
      exact ⟨⟨t, h0⟩, trivial, hi⟩
    · rintro ⟨i, -, hi⟩
      exact ⟨i.1, i.2, hi⟩⟩

lemma continuous_structureMap : Continuous (structureMap R A) := by
  -- this must help
  have := RingFilterBasis.hasBasis_nhds_zero (ringFilterBasis R A)
  sorry

lemma isOpenMap_structureMap : IsOpenMap (structureMap R A) := by
  sorry

end Topology

end Ring.RestrictedProduct
